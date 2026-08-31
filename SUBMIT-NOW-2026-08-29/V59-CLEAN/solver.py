#!/usr/bin/env python3
"""EULER v5.9 given-clause candidate — SAIR Stage 2 single-file solver (Riemann Labs).

Austin/e-graph fusion (2026-08-30): greedy affine cover ordering, finite magma-extension
search, judge-aware infinite candidate portfolio, symbolic one-sided-shift
families, and a proof-supported parity/residue-ray model on Bool x Nat distilled
from the community S00023/M00010 construction family.

Path A candidate (2026-08-30): a general, proof-recording superposition loop
uses E-style age/weight given-clause selection.  It derives Lean lemma DAGs at
runtime; it contains no problem-keyed proof or verdict table.  The embedded
source is compressed only to keep this submission single-file and is audited by
SHA-256 beside the blob below.

Path FALSE candidate (2026-08-31): a seed-free finite-domain CSP grounds the
universal antecedent, searches operation tables with propagation and carrier-
symmetry-broken goal witnesses, and independently replays every table it finds.
Its readable, hash-pinned source is embedded by the same mechanical process;
there are no known-model seeds or pair-specific branches.

Deterministic-first certificate-emitting solver for magma-law implication
pairs, with a disclosed judge-feedback LLM fallback only after every runtime
prover tier fails in Solo.  TRUE -> anonymous Lean proof term of the judge Goal;
FALSE -> whitelist-clean finite-countermodel existential (arithmetic-free
nested-match op).  Stdlib only; no network, no subprocess.  Solo candidates
are checked by the judge proxy before acceptance; Marathon candidates are
written for the runner's later judge pass.
Never reads any answer/ground-truth field.
"""
import base64
import hashlib
import json
import os
import itertools
import random
import re
import sys
import threading
import time
import zlib

# The Solo proxy extracts this literal and fills the fully rendered prompt sent
# in each request's context.  Model choice/sampling remain proxy-controlled.
PROMPT = "{solver.rendered_prompt}"

# Conservative judge caps.  These match judge.verify's standalone defaults and
# are stricter than pipeline/config.json's tunable Solo values, so the same
# serialized answers are safe in both Solo and Marathon configurations.
MAX_CODE_BYTES = 50000
MAX_FALSE_CERT_BYTES = 10000

# Targeted to the organizer's 2026-08-30 announcement: Lean/Mathlib 4.33.1.


# ===== inlined: harness/laws.py =====

"""Magma-law term utilities (stdlib only).

A term is either a variable (str, e.g. 'x') or a tuple ('op', l, r).
A law is a pair (lhs, rhs) of terms over a single binary operation.
Nothing in this module reads answer keys; it is pure syntax + finite-model math.
"""

VARS = ("x", "y", "z", "w", "v", "u")  # a k-op side has k+1 leaves -> a 4-op law needs up to 6


# ---------- parsing / printing ----------

def parse(s):
    """Parse laws like 'x*(y*z) = (x*y)*z'.  '*' is the magma operation."""
    if "=" in s:
        l, r = s.split("=", 1)
        return (parse(l), parse(r))
    toks = list(s.replace(" ", ""))
    pos = [0]

    def atom():
        c = toks[pos[0]]
        if c == "(":
            pos[0] += 1
            t = expr()
            assert toks[pos[0]] == ")"
            pos[0] += 1
            return t
        pos[0] += 1
        return c

    def expr():
        t = atom()
        while pos[0] < len(toks) and toks[pos[0]] == "*":
            pos[0] += 1
            t = ("op", t, atom())
        return t

    t = expr()
    assert pos[0] == len(toks), s
    return t


def show(t):
    if isinstance(t, str):
        return t
    return "(" + show(t[1]) + "*" + show(t[2]) + ")"


def show_law(law):
    return show(law[0]) + " = " + show(law[1])


def lean_term(t):
    if isinstance(t, str):
        return t
    return "(op " + lean_term(t[1]) + " " + lean_term(t[2]) + ")"


# ---------- basic term ops ----------

def variables(t, acc=None):
    if acc is None:
        acc = []
    if isinstance(t, str):
        if t not in acc:
            acc.append(t)
    else:
        variables(t[1], acc)
        variables(t[2], acc)
    return acc


def law_vars(law):
    acc = variables(law[0])
    variables(law[1], acc)
    return acc


def size(t):
    if isinstance(t, str):
        return 0
    return 1 + size(t[1]) + size(t[2])


def subst(t, sigma):
    if isinstance(t, str):
        return sigma.get(t, t)
    return ("op", subst(t[1], sigma), subst(t[2], sigma))


def match(pat, t, sigma=None):
    """One-way matching: pattern variables bind to subterms of t."""
    if sigma is None:
        sigma = {}
    if isinstance(pat, str):
        if pat in sigma:
            return sigma if sigma[pat] == t else None
        s = dict(sigma)
        s[pat] = t
        return s
    if isinstance(t, str):
        return None
    s = match(pat[1], t[1], sigma)
    if s is None:
        return None
    return match(pat[2], t[2], s)


def positions(t, p=()):
    yield p
    if not isinstance(t, str):
        yield from positions(t[1], p + (1,))
        yield from positions(t[2], p + (2,))


def at(t, p):
    for i in p:
        t = t[i]
    return t


def replace(t, p, new):
    if not p:
        return new
    i = p[0]
    if i == 1:
        return ("op", replace(t[1], p[1:], new), t[2])
    return ("op", t[1], replace(t[2], p[1:], new))


def canon(law):
    """Canonical variable naming (first appearance order), for dedup."""
    names = law_vars(law)
    sigma = {v: VARS[i] for i, v in enumerate(names)}
    return (subst(law[0], sigma), subst(law[1], sigma))


# ---------- finite models ----------

def eval_term(t, table, n, env):
    if isinstance(t, str):
        return env[t]
    a = eval_term(t[1], table, n, env)
    b = eval_term(t[2], table, n, env)
    return table[a * n + b]


def holds(law, table, n, vs=None):
    """Does `law` hold in the magma given by row-major `table` of size n*n?"""
    vs = vs or law_vars(law)
    k = len(vs)
    env = {}
    for code in range(n ** k):
        c = code
        for v in vs:
            env[v] = c % n
            c //= n
        if eval_term(law[0], table, n, env) != eval_term(law[1], table, n, env):
            return False
    return True


# ---------- law enumeration (no ground truth involved) ----------

def enum_terms(nops, nvars):
    """All terms with exactly `nops` operations over the first nvars variables."""
    if nops == 0:
        return [VARS[i] for i in range(nvars)]
    out = []
    for k in range(nops):
        for l in enum_terms(k, nvars):
            for r in enum_terms(nops - 1 - k, nvars):
                out.append(("op", l, r))
    return out


def enum_laws(max_ops=2, max_vars=3):
    """Deterministic pool of small magma laws, canonicalised and deduped."""
    pool, seen = [], set()
    for nl in range(0, max_ops + 1):
        for nr in range(0, max_ops + 1):
            for l in enum_terms(nl, max_vars):
                for r in enum_terms(nr, max_vars):
                    if l == r:
                        continue
                    law = canon((l, r))
                    if len(law_vars(law)) > max_vars:
                        continue
                    key = (show(law[0]), show(law[1]))
                    rkey = (key[1], key[0])
                    if key in seen or rkey in seen:
                        continue
                    seen.add(key)
                    pool.append(law)
    return pool


def law_ops(law):
    """Total number of magma operations in a law (both sides)."""
    return size(law[0]) + size(law[1])


def canon_key(law):
    """Canonical key up to variable renaming AND side swap.

    `canon` only normalises first-appearance order, so `x*y = y*x` and
    `y*x = x*y` survive it as distinct entries.  This stronger key quotients by
    every variable permutation and by swapping the two sides, which is the
    equivalence the equational-theories law pool uses.  Returns a pair of
    printed terms (hashable, sortable).
    """
    import itertools
    vs = law_vars(law)
    best = None
    for perm in itertools.permutations(VARS[:len(vs)]):
        sigma = dict(zip(vs, perm))
        l, r = subst(law[0], sigma), subst(law[1], sigma)
        for a, b in ((l, r), (r, l)):
            key = (show(a), show(b))
            if best is None or key < best:
                best = key
    return best


def enum_laws_total(max_total_ops=4, max_vars=6):
    """The full law pool: every law with at most `max_total_ops` operations
    across BOTH sides, deduped up to variable renaming and side swap.

    This is the target pool of the SAIR Stage 2 / equational-theories task.
    A side with k operations has k+1 leaves, so a law with 4 operations can
    carry up to 6 distinct variables -- hence max_vars=6 by default.
    `enum_laws` above caps operations per SIDE instead and is left untouched so
    the existing bench sets keep reproducing byte-for-byte.  No ground truth is
    involved anywhere: this is pure syntax.

    Dedup is two-stage for speed: a cheap first-appearance canonical form
    (`canon`, min over side swap) to collapse the bulk, then the full
    permutation-quotient `canon_key` on the survivors.
    """
    rough = {}
    for nl in range(max_total_ops + 1):
        for nr in range(max_total_ops + 1 - nl):
            lts = enum_terms(nl, min(max_vars, nl + 1 + nr + 1))
            rts = enum_terms(nr, min(max_vars, nl + 1 + nr + 1))
            for l in lts:
                for r in rts:
                    if l == r:
                        continue
                    if len(variables(l) + [v for v in variables(r) if v not in variables(l)]) > max_vars:
                        continue
                    a, b = canon((l, r)), canon((r, l))
                    ka = (show(a[0]), show(a[1]))
                    kb = (show(b[0]), show(b[1]))
                    rough[min(ka, kb)] = None
    pool, seen = [], set()
    for key in sorted(rough):
        law = (parse(key[0]), parse(key[1]))
        ck = canon_key(law)
        if ck in seen:
            continue
        seen.add(ck)
        pool.append((parse(ck[0]), parse(ck[1])))
    return pool


# ===== inlined: harness/lean_verify.py (emitters/lint; compile half cut) =====

"""Lean 4 certificate verification for TRUE (implication) claims.

Fail-fast policy: if the pinned toolchain / judge is unavailable we raise
InfraError instead of degrading to a weaker check.
"""


TOOLCHAIN_FILE = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "lean-toolchain")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class InfraError(RuntimeError):
    pass


def toolchain():
    with open(TOOLCHAIN_FILE) as f:
        return f.read().strip()


def binder(law):
    vs = law_vars(law)
    return "∀ " + " ".join(vs) + " : G, " if vs else ""


# Official-judge alignment: statements use a `Magma G` instance (the judge's
# Goal shape) rather than an explicit `(op : G → G → G)` argument.  The class is
# defined in a trusted PREAMBLE the harness itself emits; `export Magma (op)`
# keeps every existing proof emitter (they reference `op`) working unchanged.
PREAMBLE = (
    "universe u\n"
    "class Magma (G : Type u) where\n"
    "  op : G → G → G\n"
    "export Magma (op)\n"
    "set_option maxHeartbeats 1600000\n\n"
)


def statement(law_a, law_b):
    """The exact Lean statement a TRUE certificate for A ⟹ B must prove.

    Named `submission` because the official judge's declaration whitelist
    allows exactly the root `submission` (+ `submission.*` auto-generated
    auxiliaries like match_1) — any other self-declared name (the old
    `euler_imp`) is rejected as a disallowed declaration.
    """
    return (
        "theorem submission {G : Type} [Magma G]\n"
        "    (hA : " + binder(law_a) + lean_term(law_a[0]) + " = " + lean_term(law_a[1]) + ") :\n"
        "    " + binder(law_b) + lean_term(law_b[0]) + " = " + lean_term(law_b[1])
    )


def refutation_statement(law_a, law_b):
    """The exact Lean statement a FALSE certificate must prove.

    Official judge shape: ∃ (G : Type) (_ : Magma G), A ∧ ¬B — the carrier may
    be finite (Fin n + decide) or infinite (a real proof); no JSON table is
    ever accepted, so every FALSE must compile this existential.
    """
    return (
        "theorem submission : ∃ (G : Type) (_ : Magma G),\n"
        "    (" + binder(law_a) + lean_term(law_a[0]) + " = " + lean_term(law_a[1]) + ")\n"
        "    ∧ ¬ (" + binder(law_b) + lean_term(law_b[0]) + " = " + lean_term(law_b[1]) + ")"
    )


def affine_params(n, table):
    """Return (a, b, c) with table[x*n+y] == (a*x + b*y + c) % n, or None."""
    c = table[0]
    a = (table[n] - c) % n          # x=1,y=0
    b = (table[1] - c) % n          # x=0,y=1
    for x in range(n):
        for y in range(n):
            if table[x * n + y] != (a * x + b * y + c) % n:
                return None
    return a, b, c


def finite_false_proof(law_a, law_b, n, table):
    """Proof body for the existential refutation from a finite countermodel.

    WHITELIST-CONFORMANT single template (parity run 28d29d87): the official
    judge rejects any proof whose declaration closure touches HAdd.hAdd,
    HMul.hMul, HMod.hMod or LT.lt — which killed BOTH old templates (affine
    arithmetic op, and List.getD index decode).  The op is therefore a pure
    nested match on x.val/y.val Nat literals (Fin., Nat., OfNat., inst*,
    of_decide_* are all whitelisted), which also works uniformly at every
    order and sidesteps the historic multi-digit finOpTable bug.  Match arm
    VALUES must be OfNat literals `(k : Fin n)` — NOT `⟨k, by decide⟩`
    (Fin.mk): the mk route puts a `decide`-proof of `k < n` in the
    submission's direct declaration closure, dragging in LT.lt/Nat.decLt,
    which the judge rejected in run 34ed695e (parity stuck at 0.259).  The
    final `| _, _ =>` arm is unreachable for valid Fin values (all n*n
    combinations are enumerated first) and exists only for Nat-pattern
    exhaustiveness; `decide` evaluates the real table entries.
    """
    arms = []
    for x in range(n):
        for y in range(n):
            arms.append("  | %d, %d => (%d : Fin %d)" % (x, y, table[x * n + y], n))
    arms.append("  | _, _ => (0 : Fin %d)" % n)
    op = "(fun x y =>\n  match x.val, y.val with\n" + "\n".join(arms) + ")"
    return "refine ⟨Fin %d, ⟨%s⟩, by decide, by decide⟩" % (n, op)


# Tokens the official judge's declaration whitelist forbids (or that indicate
# a non-conformant certificate shape).  Enforced locally on every certificate
# so replica-verified ⇒ judge-acceptable.  " + ", " % ", " * ", " < " catch
# arithmetic (HAdd/HMod/HMul/LT elaborations); auxiliary declarations are
# banned because only the root `submission` (+ submission.*) is whitelisted.
OFFICIAL_SOURCE_BANNED = (
    "sorry", "admit", "sorryAx", "mkSorry", "dbg_trace", "dbgTrace",
    "run_tac", "run_cmd", "run_elab", "initialize", "builtin_initialize",
    "@[init", "#eval", "#exit", "#reduce", "#synth", "#check_eval",
    "elab", "elab_rules", "macro", "macro_rules", "syntax",
    "notation", "notation3", "infix", "infixl", "infixr", "prefix",
    "postfix", "unsafe", "implemented_by", "extern", "skipKernelTC",
    "unsafeCast", "unsafeIO", "unsafePerformIO",
)

WHITELIST_BANNED = OFFICIAL_SOURCE_BANNED + (
    "euler_imp", "euler_not_imp", "HAdd", "HMul", "HMod", "LT.lt",
    " + ", " % ", " * ", " < ", "theorem ", "def ", "abbrev ",
    "instance ", "class ", "import ", "omega", "sorry", "admit",
    "axiom ", "native_decide", "implemented_by", "unsafe", "run_tac",
    "run_cmd", "run_elab", "#eval",
)

# Fin.mk with a decide-proof (e.g. `⟨3, by decide⟩`) drags LT.lt/Nat.decLt
# into the submission's declaration closure — judge-rejected. OfNat literals
# `(3 : Fin n)` are the conformant spelling.
_FIN_MK_DECIDE = re.compile(r"⟨\s*\d+\s*,\s*by decide\s*⟩")


def whitelist_lint(proof_body):
    """Return None if the proof body is whitelist-conformant, else the token."""
    for tok in WHITELIST_BANNED:
        if tok in proof_body:
            return tok
    if _FIN_MK_DECIDE.search(proof_body):
        return "Fin.mk-with-decide (use OfNat literal)"
    return None


# Infinite models often need ordinary library declarations (functions, Bool,
# order/arithmetic tactics).  The 4.33.1 judge treats declaration allowlisting
# as problem-configurable, so the finite-model legacy lint must not pre-reject
# every infinite certificate before the judge can inspect it.
_INFINITE_SOURCE_BANNED = OFFICIAL_SOURCE_BANNED + (
    "axiom ", "native_decide",
)

def infinite_lint(proof_body):
    for tok in _INFINITE_SOURCE_BANNED:
        if tok in proof_body:
            return tok
    return None

# Judge-rejected heuristic infinite families are skipped on subsequent Solo
# attempts.  The set is process-local (one problem per Solo subprocess).
INF_REJECTED = set()
SOLO_JUDGE_AVAILABLE = False


def verify(law_a, law_b, proof_body, timeout=90):
    # The packaged solver intentionally has no Lean subprocess.  Returning
    # success here would turn an unavailable verifier into a false green check.
    return (False, "no-local-Lean: use the Solo judge proxy or runner judge pass")


def verify_refutation(law_a, law_b, proof_body, timeout=90):
    # Retained for API compatibility only.  Without a local Lean subprocess this
    # function cannot verify a universal infinite-model claim.
    return (False, "no-local-Lean: use Solo judge proxy")


# ===== inlined: EQT02-S00021-infra-failfast.py (all tiers) =====


# Progress-line cadence for long silent searches (config-not-code).
HEARTBEAT_SECS = float(os.environ.get("EULER_HEARTBEAT_SECS", "30"))

CONF = {
    "model_n_max": int(os.environ.get("EULER_MODEL_N", "3")),
    "model_sample_n4": int(os.environ.get("EULER_MODEL_SAMPLE_N4", "4000")),
    "bfs_nodes": int(os.environ.get("EULER_BFS_NODES", "4000")),
    "bfs_depth": int(os.environ.get("EULER_BFS_DEPTH", "5")),
    # HARD wall-clock deadline for the chain tier, on top of the node budget:
    # a pathological law can blow the node budget slowly, and the tier must
    # yield to the next one (and ultimately to UNKNOWN) instead of hanging.
    "bfs_secs": float(os.environ.get("EULER_BFS_SECS", "5")),
    "size_slack": int(os.environ.get("EULER_SIZE_SLACK", "2")),
    "self_check": os.environ.get("EULER_SELF_CHECK", "1") == "1",
    "debug": os.environ.get("EULER_DEBUG", "1") == "1",
    # ordered (unfailing) Knuth-Bendix completion, used when the BFS exhausts
    "kbc": os.environ.get("EULER_KBC", "1") == "1",
    "kbc_secs": float(os.environ.get("EULER_KBC_SECS", "8")),
    "kbc_max_eqs": int(os.environ.get("EULER_KBC_MAX_EQS", "400")),
    "kbc_max_size": int(os.environ.get("EULER_KBC_MAX_SIZE", "9")),
    "kbc_goal_slack": int(os.environ.get("EULER_KBC_GOAL_SLACK", "4")),
    "kbc_norm_steps": int(os.environ.get("EULER_KBC_NORM_STEPS", "60")),
    "kbc_join_nodes": int(os.environ.get("EULER_KBC_JOIN_NODES", "6000")),
    "kbc_join_depth": int(os.environ.get("EULER_KBC_JOIN_DEPTH", "4")),
    "kbc_join_secs": float(os.environ.get("EULER_KBC_JOIN_SECS", "2")),
    # General proof-recording superposition.  Unlike the older round-based
    # completion, the passive set is selected mostly by equation weight with
    # every fifth selection by age, preventing both term explosion and deep-
    # lemma starvation.  This tier runs only after finite refutation and the
    # cheap rewrite prover fail; every emitted proof is still judge-checked.
    "gc": os.environ.get("EULER_GC", "1") == "1",
    "gc_secs": float(os.environ.get("EULER_GC_SECS", "8")),
    "gc_weight_cap": int(os.environ.get("EULER_GC_WEIGHT_CAP", "70")),
    "gc_max_from": int(os.environ.get("EULER_GC_MAX_FROM", "55")),
    "gc_fact_cap": int(os.environ.get("EULER_GC_FACT_CAP", "60000")),
    "gc_ratio": int(os.environ.get("EULER_GC_RATIO", "5")),
    # Path B: runtime LLM proof authoring, Solo only and judge-gated.  It never
    # supplies direction/cert data to deterministic search and never runs in the
    # local/Marathon stress harness.  Each rejected Lean diagnostic is fed into
    # the next bounded retry.
    "llm": os.environ.get("EULER_LLM", "1") == "1",
    "llm_rounds": int(os.environ.get("EULER_LLM_ROUNDS", "5")),
    "llm_round_min_secs": float(os.environ.get("EULER_LLM_ROUND_MIN_SECS", "35")),
    "llm_max_proof_bytes": int(os.environ.get("EULER_LLM_MAX_PROOF_BYTES", "45000")),
    "judge_call_max_secs": float(os.environ.get("EULER_JUDGE_CALL_MAX_SECS", "300")),
    # structured (parametric) countermodel families, tried only after the cheap
    # exhaustive small-order search fails.  Some pairs have no countermodel below
    # order 13 yet are refuted by e.g. ZMod 13 with x*y = 7x+7y, which no
    # enumeration at n<=4 can ever reach.
    "cm_families": os.environ.get("EULER_CM_FAMILIES", "1") == "1",
    "cm_order_max": int(os.environ.get("EULER_CM_ORDER_MAX", "13")),
    "cm_secs": float(os.environ.get("EULER_CM_SECS", "25")),
    "cm_probe": int(os.environ.get("EULER_CM_PROBE", "40")),
    # Magma-cohomology extension tier (B x F_p); derived from the public
    # parsimagma construction (Apache-2.0), reimplemented here against EULER ASTs.
    "cm_ext": os.environ.get("EULER_CM_EXT", "1") == "1",
    "cm_ext_secs": float(os.environ.get("EULER_CM_EXT_SECS", "12")),
    "cm_ext_max_carrier": int(os.environ.get("EULER_CM_EXT_MAX", "10")),
    # genuinely exhaustive order-4 search (constrained DFS with pruning), run
    # only on pairs the cheap tiers could not refute.  Closes the gap left by
    # the SAMPLED n=4 pass: without it, "no finite countermodel" is unproven.
    "cm_n4_exhaustive": os.environ.get("EULER_CM_N4", "1") == "1",
    "cm_n4_secs": float(os.environ.get("EULER_CM_N4_SECS", "30")),
    # exhaustive order-5, reached only when order 4 was genuinely EXHAUSTED
    # (never when it merely ran out of time), so it costs nothing on the
    # 99%-of-pairs cheap path.
    "cm_n5_exhaustive": os.environ.get("EULER_CM_N5", "1") == "1",
    "cm_n5_secs": float(os.environ.get("EULER_CM_N5_SECS", "15")),
    # Seed-free finite-domain CSP tail.  Existing tiers already cover n<=5;
    # this engine starts at n=6, fairly divides its bounded budget through n=8,
    # and returns only tables independently replayed against both laws.
    "cm_csp": os.environ.get("EULER_CM_CSP", "1") == "1",
    "cm_csp_n_lo": int(os.environ.get("EULER_CM_CSP_N_LO", "6")),
    "cm_csp_n_hi": int(os.environ.get("EULER_CM_CSP_N_HI", "8")),
    "cm_csp_secs": float(os.environ.get("EULER_CM_CSP_SECS", "30")),
    "cm_csp_nodes": int(os.environ.get("EULER_CM_CSP_NODES", "1000000")),
    "cm_csp_groundings": int(os.environ.get("EULER_CM_CSP_GROUNDINGS", "4096")),
    # infinite-carrier (Z) refutation tier, LAST: some pairs have no finite
    # countermodel at all yet are refuted on an infinite carrier.  The claim is
    # only ever made on the strength of a compiled Lean proof.
    "inf_cm": os.environ.get("EULER_INF_CM", "1") == "1",
    "inf_window": int(os.environ.get("EULER_INF_WINDOW", "4")),
    "inf_secs": float(os.environ.get("EULER_INF_SECS", "25")),
    "inf_coeff": int(os.environ.get("EULER_INF_COEFF", "2")),
    # ESCALATION tier: re-run the TRUE search with deep budgets ONLY when every
    # standard tier came up empty (reached by ~7/1500 bigu pairs, so the cheap
    # path is untouched).  Budgets replicate the e12b8521 residue attack that
    # converted 7/9 formerly-undecided pairs (chains of 14-91 steps), and stay
    # well inside the competition's 3600s/problem Solo allowance.
    "egraph": os.environ.get("EULER_EGRAPH", "1") == "1",
    "egraph_secs": float(os.environ.get("EULER_EGRAPH_SECS", "10")),
    "egraph_terms": int(os.environ.get("EULER_EGRAPH_TERMS", "18000")),
    "egraph_rounds": int(os.environ.get("EULER_EGRAPH_ROUNDS", "10")),
    "egraph_size_slack": int(os.environ.get("EULER_EGRAPH_SIZE_SLACK", "12")),
    "egraph_fillers": int(os.environ.get("EULER_EGRAPH_FILLERS", "12")),
    "egraph_inst_cap": int(os.environ.get("EULER_EGRAPH_INST_CAP", "72")),
    "esc": os.environ.get("EULER_ESCALATION", "1") == "1",
    "esc_bfs_secs": float(os.environ.get("EULER_ESC_BFS_SECS", "60")),
    "esc_bfs_nodes": int(os.environ.get("EULER_ESC_BFS_NODES", "200000")),
    "esc_kbc_secs": float(os.environ.get("EULER_ESC_KBC_SECS", "90")),
    "esc_kbc_max_eqs": int(os.environ.get("EULER_ESC_KBC_MAX_EQS", "2000")),
    # long exhaustive-n5 pass, fired only when n<=4 was EXHAUSTED and the
    # standard n5 pass merely ran out of time (bigu-0212 needed ~1629s).
    # Default 0 = off (the fast regression gate never pays for it).
    "esc_n5_secs": float(os.environ.get("EULER_N5_ESCALATION_SECS", "0")),
}

# ===== embedded: proof-recording age/weight given-clause prover =====
# Runtime algorithm, not a proof/certificate bank.  Canonical source:
# stress-eval/given_clause_prover.py (materialized below for review).
_GC_SOURCE_SHA256 = "95f2e104df3ab109d50c5e61e697520d7943e75ae8fca6ba2e373716e11c97b1"
_GC_SRC_B64 = (
    "eNq9XV9zG0dyf8enmINKpV0LgET67pICDVUomZRVR+sPxeTOoVnQYrEgVlzswrsL/jmfq/KWVB5Tqcp7Hu7j3IfwJ0n/umdmZxZL"
    "Uo6c0DYJ7M709PT09Py6p2f84DdPNlX5ZJbmT5L8Uq1v6mWRf9nr9/urNE+HJ1dJMlaRmhWbfJ7M1R/yTb0cPk/yeXo9rOqbLFFx"
    "mdZpHGXDdZSWKi5W6yyp0yJX9TKqVbJK66oXZVlxlaVVPayiRaKOkihXv1XrsigWlVoUpVpF56tIJT9sIlSNMpUSGaKKb9Wo1/vj"
    "N9+pk29evVcHf3r1/uR9b+j/9MCnCjb5IkqzND932AjRzHwTJ5U6fHP8x/3jr91mNAtXab1UyTWaTOtelqxWUaWGQxVlq6Kqqf/M"
    "8QfqZfyBHpZJNL8ZKfWqVnmSzCv18psXT+JoFmUDdbVM46WKykRFsyrJa1XkvXqZViTCaxXlc1UXhVom0eUNfVKzTZrNVTBPq4sn"
    "q2Q1jKm7dRmleTIfkGSjajkkFvMkpNbeF+oq6ZUJRJOsQLpeJuqLdJ5EX6h5UiclhqziwchuVJqrtzya415PqZ2RelOmptLyZl3Q"
    "34rYUtdqombpuVLU5UiVyRWNZ6LKDQ0tPx8+U9cjorA7Uu+jelNGNWlEmawT+jCndqrNOinXRSV1Kuov9SuJSAhoohwQa2V6iUHJ"
    "kyuiQz9mACoVGO1R0J4K3TxAVa5D+mZKqjgqif3KDAWPmxBDv1mOtXrz+ug7tSiL1VgtNnnMFaO1VSRVLIixMkuTUskYk4yL/Lzc"
    "L88HQmxU3axWAzWiMcjpLVEhjoITjB/9m1xHcU1dvoJmH2BkLpPyUaU+VOvVB1XVybpS8wKKQwPF9Oh9ukipI+Aky9TvVR2V50ld"
    "yezAWECDqIBWOijOzvBLK9WU5STE5kmyFhVK85tRSA+/HKm3YIIJnRckxtmNHkIIHE+OvnmPIcTHY/rImo7SRsI8aEI/KGi00gW/"
    "pv+K8obEk2XRukqgtiT7GiNJrfB0JeFlGPZ5WiYQSwgt+e1IHdCUVx/myYI6MVulVQXRj9VLsDeegMM0r8tCvVRTtdzTX746v4zK"
    "6tme+moZUX9GoxF9xnzDxw9kAQ5IlKTO6BaNhJUrWaJhXQzpDwjvX5PWBuD//f6rY/VxMz9PaHzE3oy+3B3tEpO9E2gMcRL0qc3+"
    "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"
)
_GC_NS = {}
try:
    _gc_raw = zlib.decompress(base64.b64decode(_GC_SRC_B64))
    if hashlib.sha256(_gc_raw).hexdigest() != _GC_SOURCE_SHA256:
        raise ValueError("given-clause source digest mismatch")
    exec(compile(_gc_raw.decode("utf-8"), "euler-v59-given-clause.py", "exec"), _GC_NS)
except Exception:
    _GC_NS = {}
_GC_LOCK = threading.Lock()


def _gc_prove(law_a, law_b):
    """Return an intro-stripped Lean proof body and telemetry, or (None, why).

    The embedded engine owns mutable fresh-name/deadline state, so concurrent
    callers serialize this bounded tier.  Marathon itself is sequential; the
    lock protects library/harness callers without changing proof search.
    """
    fn = _GC_NS.get("prove_gc")
    if fn is None:
        return None, "gc-engine-unavailable"
    try:
        with _GC_LOCK:
            _GC_NS["GC_TIME_CAP"] = CONF["gc_secs"]
            _GC_NS["GC_WEIGHT_CAP"] = CONF["gc_weight_cap"]
            _GC_NS["GC_MAX_FROM"] = CONF["gc_max_from"]
            _GC_NS["GC_FACT_CAP"] = CONF["gc_fact_cap"]
            _GC_NS["GC_RATIO"] = max(1, CONF["gc_ratio"])
            body, info = fn(show_law(law_a), show_law(law_b),
                            time_cap=CONF["gc_secs"])
    except Exception as exc:
        return None, "gc-error:" + type(exc).__name__
    if not body:
        return None, str(info or "gc-no-proof")
    lines = body.splitlines()
    prefix = "intro G _ h"
    if not lines or not lines[0].strip().startswith(prefix):
        return None, "gc-unexpected-intro"
    suffix = lines[0].strip()[len(prefix):].strip()
    if suffix:
        lines[0] = "intro " + suffix
    else:
        lines = lines[1:]
    # _compose_true already introduced the hypothesis as hA.
    body = re.sub(r"\bh\b", "hA", "\n".join(lines))
    banned = whitelist_lint(body)
    if banned is not None:
        return None, "gc-lint:" + banned.strip()
    return body, str(info or "gc-proof")


# ===== embedded: seed-free finite-domain CSP countermodel finder =====
# Runtime algorithm, not a model/certificate bank.  Canonical source:
# stress-eval/finite_csp_prover.py (materialized below for review).
_CSP_SOURCE_SHA256 = "38d4d0d1275292bed046b0665832cbe40896591abfcf7095aadf868ee77c7366"
_CSP_SRC_B64 = (
    "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"
)
_CSP_NS = {}
try:
    _csp_raw = zlib.decompress(base64.b64decode(_CSP_SRC_B64))
    if hashlib.sha256(_csp_raw).hexdigest() != _CSP_SOURCE_SHA256:
        raise ValueError("finite-CSP source digest mismatch")
    exec(compile(_csp_raw.decode("utf-8"), "euler-v59-finite-csp.py", "exec"),
         _CSP_NS)
except Exception:
    _CSP_NS = {}
_CSP_LOCK = threading.Lock()


def _csp_countermodel(law_a, law_b):
    """Run the bounded seed-free CSP and replay any returned finite model."""
    fn = _CSP_NS.get("find_countermodel")
    if fn is None:
        return None, {"result": "csp-engine-unavailable"}
    try:
        with _CSP_LOCK:
            model = fn(
                law_a, law_b,
                n_lo=max(2, CONF["cm_csp_n_lo"]),
                n_hi=min(8, CONF["cm_csp_n_hi"]),
                time_cap=max(0.0, CONF["cm_csp_secs"]),
                node_limit=max(1, CONF["cm_csp_nodes"]),
                grounding_cap=max(1, CONF["cm_csp_groundings"]),
            )
            info = dict(_CSP_NS.get("LAST_STATS") or {})
    except Exception as exc:
        return None, {"result": "csp-error:" + type(exc).__name__}
    if not isinstance(model, dict):
        return None, info
    n, table = model.get("n"), model.get("table")
    if (not isinstance(n, int) or not (2 <= n <= 8) or
            not isinstance(table, list) or len(table) != n * n or
            any(not isinstance(v, int) or v < 0 or v >= n for v in table)):
        return None, dict(info, result="malformed-model-rejected")
    # Defense in depth across the namespace boundary: the host evaluator
    # exhaustively checks both laws again before the model reaches Lean.
    if not holds(law_a, table, n) or holds(law_b, table, n):
        return None, dict(info, result="host-replay-rejected")
    return {"n": n, "table": table}, dict(info, result="host-verified-model")


# Per-solve telemetry.  These are PER-THREAD: the bench may run several pairs
# concurrently (Lean compiles dominate wall time), and process-global dicts
# would interleave one pair's statistics into another's certificate.
class _ThreadStats:
    """Mapping-like view of a dict that is private to the calling thread."""

    def __init__(self):
        self._local = threading.local()

    def _d(self):
        d = getattr(self._local, "d", None)
        if d is None:
            d = self._local.d = {}
        return d

    def clear(self):
        self._d().clear()

    def update(self, *a, **kw):
        self._d().update(*a, **kw)

    def get(self, k, default=None):
        return self._d().get(k, default)

    def keys(self):                      # lets dict(STATS) copy the thread's view
        return self._d().keys()

    def __getitem__(self, k):
        return self._d()[k]

    def __setitem__(self, k, v):
        self._d()[k] = v

    def __contains__(self, k):
        return k in self._d()

    def __repr__(self):
        return repr(self._d())


# Last completion run's telemetry (read by the harness/logs, never by scoring).
KBC_STATS = _ThreadStats()

# Last countermodel search's telemetry (diagnostics only, never scoring).
CM_STATS = _ThreadStats()


# ---------------- FALSE: countermodels ----------------

def _all_tables(n):
    total = n ** (n * n)
    for code in range(total):
        c, t = code, []
        for _ in range(n * n):
            t.append(c % n)
            c //= n
        yield t


# Greedy prefix from carlok/parsimagma (Apache-2.0).  These twenty affine
# models are ordered by set-cover yield over the ETP false implication graph.
# They are mathematical constructions, not answer data: every candidate is
# still checked exhaustively against the input equations before use.
_GREEDY_AFFINE_PRIORITY = [
    (2, 0, 0, 0), (2, 0, 1, 0), (2, 1, 0, 0), (2, 1, 1, 0),
    (3, 0, 2, 0), (3, 2, 0, 0), (3, 2, 2, 0),
    (7, 0, 2, 0), (7, 2, 0, 0),
    (5, 2, 4, 0), (5, 3, 3, 0), (5, 4, 2, 0),
    (4, 2, 3, 0), (4, 0, 2, 0), (4, 2, 0, 0), (4, 3, 2, 0), (4, 2, 2, 0),
    (13, 7, 7, 0), (11, 6, 6, 0), (5, 0, 2, 0),
]


def _affine_table(n, a, b, c=0):
    return [(a * x + b * y + c) % n for x in range(n) for y in range(n)]


def _family_tables(order_max):
    """Structured finite magmas in high-yield order.

    The greedy prefix is attempted before the full affine sweep.  This changes
    only search order, never soundness: survivors are exhaustively checked by
    holds() before a certificate is emitted.
    """
    seen = set()
    for n, a, b, c in _GREEDY_AFFINE_PRIORITY:
        if n <= order_max:
            seen.add((n, a, b, c))
            yield ("greedy-zmod%d-affine(%d,%d,%d)" % (n, a, b, c), n,
                   _affine_table(n, a, b, c))
    for n in range(2, order_max + 1):
        rng = range(n)
        for a in rng:
            for b in rng:
                for c in rng:
                    if (n, a, b, c) in seen:
                        continue
                    yield ("zmod%d-affine(%d,%d,%d)" % (n, a, b, c), n,
                           _affine_table(n, a, b, c))
        yield ("max%d" % n, n, [max(x, y) for x in rng for y in rng])
        yield ("min%d" % n, n, [min(x, y) for x in rng for y in rng])
        yield ("projL%d" % n, n, [x for x in rng for _ in rng])
        yield ("projR%d" % n, n, [y for _ in rng for y in rng])
        yield ("succR%d" % n, n, [(y + 1) % n for _ in rng for y in rng])
        yield ("succL%d" % n, n, [(x + 1) % n for x in rng for _ in rng])

def _probe_holds(law, table, n, vs, tries, rnd):
    """Cheap necessary condition: law survives `tries` random assignments.

    Only used to skip candidates fast; a survivor is always re-checked
    exhaustively with holds() before anything is claimed.
    """
    for _ in range(tries):
        env = {v: rnd.randrange(n) for v in vs}
        if eval_term(law[0], table, n, env) != eval_term(law[1], table, n, env):
            return False
    return True



# ---------------- FALSE: finite magma extensions (cohomology tier) ----------------

def _ext_table(base, nb, p, alpha, beta, coc):
    """Extension B x F_p with fibre law αu + βv + c(x,y)."""
    n = nb * p
    out = [0] * (n * n)
    for bx in range(nb):
        for by in range(nb):
            bz = base[bx * nb + by]
            cc = coc[bx * nb + by]
            for u in range(p):
                for v in range(p):
                    out[(bx * p + u) * n + (by * p + v)] = \
                        bz * p + (alpha * u + beta * v + cc) % p
    return out


def _ext_residual(law, base, nb, p, alpha, beta, coc):
    """Fibre residual on base assignments with zero fibre coordinates."""
    lhs, rhs = law
    vs = law_vars(law)
    n = nb * p
    table = _ext_table(base, nb, p, alpha, beta, coc)
    out = []
    for vals in itertools.product(range(nb), repeat=len(vs)):
        env = dict(zip(vs, (v * p for v in vals)))
        a = eval_term(lhs, table, n, env)
        b = eval_term(rhs, table, n, env)
        if a // p != b // p:
            return None
        out.append((b % p - a % p) % p)
    return out


def _solve_modp(rows, nv, p):
    """Affine solution space over F_p as (particular, basis), or None."""
    a = [r[:] for r in rows]
    piv, rr = [], 0
    for c in range(nv):
        pr = next((i for i in range(rr, len(a)) if a[i][c] % p), None)
        if pr is None:
            continue
        a[rr], a[pr] = a[pr], a[rr]
        inv = pow(a[rr][c], p - 2, p)
        a[rr] = [v * inv % p for v in a[rr]]
        for i in range(len(a)):
            if i != rr and a[i][c] % p:
                f = a[i][c] % p
                a[i] = [(x - f * y) % p for x, y in zip(a[i], a[rr])]
        piv.append(c)
        rr += 1
    if any(all(v % p == 0 for v in row[:nv]) and row[nv] % p for row in a):
        return None
    free = [c for c in range(nv) if c not in piv]
    def sol(fv):
        x = [0] * nv
        for k, c in enumerate(free):
            x[c] = fv[k] % p
        for i, c in enumerate(piv):
            x[c] = (a[i][nv] - sum(a[i][j] * x[j] for j in free)) % p
        return x
    part = sol([0] * len(free))
    basis = []
    for k in range(len(free)):
        fv = [0] * len(free); fv[k] = 1
        q = sol(fv)
        basis.append([(u - v) % p for u, v in zip(q, part)])
    return part, basis


def search_extension(law_a, law_b, deadline, max_carrier=10):
    """Find a finite extension satisfying law_a and violating law_b.

    For fixed base/fibre parameters, law_a is linear in the cocycle values, so
    Gaussian elimination replaces exponential cocycle enumeration.
    """
    primes = (2, 3, 5, 7)
    for nb in range(2, 6):
        for p in primes:
            n = nb * p
            if n > max_carrier:
                continue
            # Keep Lean's final `by decide` tractable on high-arity laws.
            if n ** max(len(law_vars(law_a)), len(law_vars(law_b))) > 250000:
                continue
            for ba in range(nb):
                for bb in range(nb):
                    if time.time() > deadline:
                        return None
                    base = _affine_table(nb, ba, bb, 0)
                    if not holds(law_a, base, nb):
                        continue
                    for alpha in range(p):
                        for beta in range(p):
                            fib = _affine_table(p, alpha, beta, 0)
                            if not holds(law_a, fib, p):
                                continue
                            nv = nb * nb
                            z = [0] * nv
                            r0 = _ext_residual(law_a, base, nb, p, alpha, beta, z)
                            if r0 is None:
                                continue
                            cols = []
                            ok = True
                            for j in range(nv):
                                e = z[:]; e[j] = 1
                                rj = _ext_residual(law_a, base, nb, p, alpha, beta, e)
                                if rj is None:
                                    ok = False; break
                                cols.append([(x - y) % p for x, y in zip(rj, r0)])
                            if not ok:
                                continue
                            rows = [[cols[j][i] for j in range(nv)] + [(-r0[i]) % p]
                                    for i in range(len(r0))]
                            got = _solve_modp(rows, nv, p)
                            if got is None:
                                continue
                            part, basis = got
                            cands = [part] + [[(x + y) % p for x, y in zip(part, b)]
                                               for b in basis]
                            for coc in cands:
                                rc = _ext_residual(law_b, base, nb, p, alpha, beta, coc)
                                if rc is None or any(v % p for v in rc):
                                    table = _ext_table(base, nb, p, alpha, beta, coc)
                                    if holds(law_a, table, n) and not holds(law_b, table, n):
                                        return {"n": n, "table": table,
                                                "label": "extension-B%d-F%d(%d,%d)" %
                                                         (nb, p, alpha, beta)}
    return None

def find_countermodel(law_a, law_b):
    """Search for a finite magma satisfying law_a and violating law_b.

    Tiers, cheapest first (so the 0.0s FALSE path is untouched):
      1. exhaustive over ALL tables of order <= model_n_max (default 3)
      2. random tables at order 4
      3. parametric algebraic families up to order cm_order_max (default 13)
    Records telemetry in CM_STATS so the bench can distinguish 'countermodel
    search exhausted' from 'prover gave up'.
    """
    CM_STATS.clear()
    CM_STATS["exhaustive_n"] = CONF["model_n_max"]
    for n in range(1, CONF["model_n_max"] + 1):
        for table in _all_tables(n):
            if holds(law_a, table, n) and not holds(law_b, table, n):
                CM_STATS["found"] = "exhaustive-n%d" % n
                return {"n": n, "table": table}
    n = 4
    rng = random.Random(12345)
    CM_STATS["sampled_n4"] = CONF["model_sample_n4"]
    for _ in range(CONF["model_sample_n4"]):
        table = [rng.randrange(n) for _ in range(n * n)]
        if holds(law_a, table, n) and not holds(law_b, table, n):
            CM_STATS["found"] = "sample-n4"
            return {"n": n, "table": table}
    reason = "exhaustive-n%d+sample-n4" % CONF["model_n_max"]
    if CONF["cm_families"]:
        va, vb = law_vars(law_a), law_vars(law_b)
        probe, rnd = CONF["cm_probe"], random.Random(777)
        deadline = time.time() + CONF["cm_secs"]
        tried, reached = 0, 0
        family_status = "exhausted"
        for label, m, table in _family_tables(CONF["cm_order_max"]):
            if time.time() > deadline:
                # Preserve the original latency contract: once this bounded
                # tier times out, yield immediately to the standard proof
                # engines.  Continuing into extensions/n4/n5 here can delay a
                # cheap GC proof by another minute on a private TRUE case.
                CM_STATS.update(families_tried=tried,
                                order_reached=reached,
                                families="deadline",
                                reason="family-time-budget")
                return None
            tried += 1
            reached = m
            # cheap probe, then the real exhaustive checks
            if not _probe_holds(law_a, table, m, va,
                                min(probe, m ** len(va)), rnd):
                continue
            if not holds(law_a, table, m, va):
                continue
            if holds(law_b, table, m, vb):
                continue
            CM_STATS.update(found=label, families_tried=tried,
                            order_reached=m, families=family_status)
            return {"n": m, "table": table}
        CM_STATS.update(families_tried=tried, order_reached=reached,
                        families=family_status)
        reason += "+families-" + family_status
    else:
        CM_STATS["families"] = "disabled"
        reason += "+families-disabled"
    if CONF.get("cm_ext"):
        ext = search_extension(law_a, law_b,
                               time.time() + CONF["cm_ext_secs"],
                               CONF["cm_ext_max_carrier"])
        if ext is not None:
            CM_STATS["found"] = ext.get("label", "magma-extension")
            return {"n": ext["n"], "table": ext["table"]}
        CM_STATS["extension"] = "exhausted-or-time"
        reason += "+extension-bounded"
    else:
        CM_STATS["extension"] = "disabled"
        reason += "+extension-disabled"
    return _n4_finish(law_a, law_b, reason)


def _n4_finish(law_a, law_b, reason):
    """Last finite tier: genuinely exhaustive order-4 search.

    Turns "no countermodel found at n=4" (sampling) into a real exhaustion
    result, which is the precondition for claiming a pair has no finite
    countermodel at all.
    """
    if not CONF["cm_n4_exhaustive"]:
        CM_STATS["reason"] = reason
        return None
    tbl, exhausted = _exhaustive_n(law_a, law_b, 4,
                                   time.time() + CONF["cm_n4_secs"])
    CM_STATS["n4_exhausted"] = bool(exhausted)
    if tbl is not None:
        CM_STATS["found"] = "exhaustive-n4"
        return {"n": 4, "table": tbl}
    if not exhausted:
        CM_STATS["reason"] = reason + "+n4-time-budget"
        return None
    reason += "+exhaustive-n4"
    if not CONF["cm_n5_exhaustive"]:
        CM_STATS["reason"] = reason
        return None
    tbl5, done5 = _exhaustive_n(law_a, law_b, 5,
                                time.time() + CONF["cm_n5_secs"])
    CM_STATS["n5_exhausted"] = bool(done5)
    if tbl5 is not None:
        CM_STATS["found"] = "exhaustive-n5"
        return {"n": 5, "table": tbl5}
    CM_STATS["reason"] = reason + ("+exhaustive-n5" if done5 else "+n5-time-budget")
    return None


def _partial_holds(law, tbl, n, vs):
    """False only when law is DEFINITELY violated by the partial table `tbl`.

    Cells not yet assigned are None; any assignment needing one is skipped, so
    this is a sound pruning test (never rejects a completable table).
    """
    def ev(t, env):
        if isinstance(t, str):
            return env[t]
        l, r = ev(t[1], env), ev(t[2], env)
        if l is None or r is None:
            return None
        return tbl[l * n + r]

    def rec(i, env):
        if i == len(vs):
            a, b = ev(law[0], env), ev(law[1], env)
            return (a is None) or (b is None) or (a == b)
        for val in range(n):
            env[vs[i]] = val
            if not rec(i + 1, env):
                return False
        return True

    return rec(0, {})


def _exhaustive_n(law_a, law_b, n, deadline, lnh=None):
    """Constrained DFS over all order-n magmas satisfying law_a.

    Returns (table or None, exhausted).  `exhausted` is False when the time
    budget cut the search short -- only a True means "no countermodel exists
    at this order", which is what the infinite-carrier tier is allowed to
    assume.  Pruning: after each cell assignment, reject partial tables that
    already violate law_a on a fully-determined assignment.

    Isomorphism reduction (`lnh`, the classic least-number heuristic from
    SEM/Mace4-style finite model finders): when assigning a cell, values above
    max(mentioned elements) + 1 are skipped, because the not-yet-mentioned
    elements are interchangeable under a carrier permutation -- any magma has
    an isomorphic copy reachable under this restriction, so both "found" and
    "exhausted, none exists" verdicts are preserved while the branching factor
    near the root drops from n to ~2.  Default: on for n >= 5 (the language
    has one binary op and no constants, so LNH is sound as-is).
    """
    if lnh is None:
        lnh = n >= 5 and os.environ.get("EULER_CM_LNH", "1") == "1"
    va, vb = law_vars(law_a), law_vars(law_b)
    tbl = [None] * (n * n)
    cells = n * n
    # Heartbeat: an exhaustive order-n DFS can run for many minutes with nothing
    # to print, and a totally silent stage gets killed by the runner's no-output
    # stall guard (this is what killed experiment dc5e91eb mid-probe).  Emit a
    # flushed progress line at most every HEARTBEAT_SECS so the stage is both
    # inspectable and guard-safe.  Cost is one clock read per node.
    hb = {"n_nodes": 0, "next": time.time() + HEARTBEAT_SECS}

    def rec(i, mm):
        now = time.time()
        hb["n_nodes"] += 1
        if now > hb["next"]:
            hb["next"] = now + HEARTBEAT_SECS
            sys.stderr.write("[cm-n%d] nodes=%d depth=%d/%d %.0fs left\n" % (
                n, hb["n_nodes"], i, cells, max(0.0, deadline - now)))
        if now > deadline:
            return None, False
        if i == cells:
            if holds(law_a, tbl, n, va) and not holds(law_b, tbl, n, vb):
                return list(tbl), True
            return None, True
        r, c = divmod(i, n)
        mm2 = max(mm, r, c)
        vmax = min(n - 1, mm2 + 1) if lnh else n - 1
        for v in range(vmax + 1):
            tbl[i] = v
            if _partial_holds(law_a, tbl, n, va):
                found, done = rec(i + 1, max(mm2, v))
                if found is not None:
                    return found, done
                if not done:
                    tbl[i] = None
                    return None, False
            tbl[i] = None
        return None, True

    got = rec(0, -1)
    _exhaustive_n.last_stats = {"n": n, "nodes": hb["n_nodes"], "lnh": lnh,
                                "exhausted": bool(got[1])}
    return got


# ---------------- FALSE: infinite (Z) carrier ----------------

def _z_ops(coeff):
    """Piecewise-affine magmas on Z: op x w = a_i * w + b_i, region i = sign(x).

    Left translations are then affine; a = -1 makes each an involution, which is
    exactly the family that has NO finite countermodel (in a finite magma the
    involutions collapse) yet still refutes on Z.
    """
    for a0 in (-1, 1):
        for a1 in (-1, 1):
            for b0 in range(-coeff, coeff + 1):
                for b1 in range(-coeff, coeff + 1):
                    if (a0, b0) == (a1, b1):
                        continue  # constant on both regions: a finite quotient exists
                    yield ("z-piecewise(%d,%d|%d,%d)" % (a0, b0, a1, b1), (a0, b0, a1, b1))


def _z_eval(t, env, prm):
    a0, b0, a1, b1 = prm
    if isinstance(t, str):
        return env[t]
    x, w = _z_eval(t[1], env, prm), _z_eval(t[2], env, prm)
    return (a0 * w + b0) if x >= 0 else (a1 * w + b1)


def _z_holds(law, vs, prm, window):
    def rec(i, env):
        if i == len(vs):
            return _z_eval(law[0], env, prm) == _z_eval(law[1], env, prm)
        for val in range(-window, window + 1):
            env[vs[i]] = val
            if not rec(i + 1, env):
                return False
        return True
    return rec(0, {})


def _z_violation(law, vs, prm, window):
    """First assignment in the window where `law` fails (the E2 witness)."""
    def rec(i, env):
        if i == len(vs):
            if _z_eval(law[0], env, prm) != _z_eval(law[1], env, prm):
                return dict(env)
            return None
        for val in range(-window, window + 1):
            env[vs[i]] = val
            got = rec(i + 1, env)
            if got is not None:
                return got
        return None
    return rec(0, {})


def _z_lean_branch(a, b):
    """Lean source for `a * w + b` with a in {1,-1}."""
    if a == 1:
        return "w" if b == 0 else ("w + %d" % b if b > 0 else "w - %d" % (-b))
    return "-w" if b == 0 else ("%d - w" % b if b > 0 else "-w - %d" % (-b))


def _z_lean_op(prm):
    a0, b0, a1, b1 = prm
    return "fun x w => if 0 ≤ x then %s else %s" % (
        _z_lean_branch(a0, b0), _z_lean_branch(a1, b1))


def _num(v):
    return str(v) if v >= 0 else "(%d)" % v


def _z_proof(law_a, law_b, prm, witness):
    """Proof body for the existential refutation statement.

    Both halves beta-reduce, split every `if`, then use Mathlib's kernel-checked
    `omega` tactic for Presburger arithmetic.  Solo sends these candidates to
    the real judge; a finite window is never treated as a proof.
    """
    va, vb = law_vars(law_a), law_vars(law_b)
    args = " ".join(_num(witness[v]) for v in vb)
    lines = ["refine ⟨Int, ⟨%s⟩, ?_, ?_⟩" % _z_lean_op(prm)]
    lines.append("· " + ("intro " + " ".join(va) if va else "skip"))
    lines += ["  dsimp only", "  repeat any_goals split", "  all_goals omega"]
    lines.append("· intro h")
    lines.append("  have h1 := h" + ((" " + args) if args else ""))
    lines += ["  dsimp only at h1", "  repeat any_goals split at h1", "  all_goals omega"]
    return "\n".join(lines)


def find_infinite_countermodel(law_a, law_b):
    """Return the next plausible Z-family candidate for Solo judge validation.

    `_z_holds` is deliberately only a filter over a finite window.  It does NOT
    establish the universal antecedent.  Soundness comes only from the external
    Lean judge.  Rejected family labels are blacklisted so retries make progress.
    Marathon, which has no interactive judge proxy, does not use this heuristic.
    """
    if not SOLO_JUDGE_AVAILABLE:
        return None, "heuristic-infinite-disabled-without-judge"
    va, vb = law_vars(law_a), law_vars(law_b)
    # Two windows drastically reduce false positives at negligible cost.
    windows = (CONF["inf_window"], max(CONF["inf_window"] + 3, 7))
    deadline = time.time() + CONF["inf_secs"]
    tried = 0
    for label, prm in _z_ops(CONF["inf_coeff"]):
        if label in INF_REJECTED:
            continue
        if time.time() > deadline:
            return None, "z-time-budget(tried=%d)" % tried
        tried += 1
        if any(not _z_holds(law_a, va, prm, w) for w in windows):
            continue
        witness = _z_violation(law_b, vb, prm, windows[-1])
        if witness is None:
            continue
        proof = _z_proof(law_a, law_b, prm, witness)
        return {"claim": "FALSE", "carrier": "infinite",
                "lean_imports": ["Mathlib.Tactic.Omega"],
                "lean_statement": refutation_statement(law_a, law_b),
                "lean_proof": proof,
                "method": "infinite-model:" + label,
                "stats": {"family": label, "witness": witness,
                          "windows": windows, "detail": "judge-required"}}, "candidate"
    return None, "z-families-exhausted(tried=%d)" % tried


# ---------------- FALSE: generic F2 one-sided-shift model ----------------
#
# Carrier: streams Nat -> F_2.  R is the right shift with zero fill and L is
# the left shift, so L(R x)=x but R(L x) need not equal x.  The magma is
#     x ◇ y = R x + L y   (over F_2).
# For any term and output coordinate n, evaluation is the XOR of finitely many
# variable coordinates.  We compute that support exactly as a symmetric-
# difference set, including all n=0 boundary effects.  Once n exceeds term
# depth there are no more boundaries, so checking n=0..depth is complete.

def _term_depth(t):
    if isinstance(t, str):
        return 0
    return 1 + max(_term_depth(t[1]), _term_depth(t[2]))


def _f2_support(t, n):
    """Exact XOR support of term t at coordinate n in the shift model."""
    if isinstance(t, str):
        return {(t, n)}
    left = set() if n == 0 else _f2_support(t[1], n - 1)
    right = _f2_support(t[2], n + 1)
    return left ^ right


def _f2_shift_holds(law):
    d = max(_term_depth(law[0]), _term_depth(law[1]))
    # n=d is already in the stable no-boundary region; d+1 is a cheap guard
    # against an implementation mistake in the boundary argument.
    return all(_f2_support(law[0], n) == _f2_support(law[1], n)
               for n in range(d + 2))


def _f2_shift_violation(law):
    d = max(_term_depth(law[0]), _term_depth(law[1]))
    for n in range(d + 2):
        diff = _f2_support(law[0], n) ^ _f2_support(law[1], n)
        if diff:
            # Setting exactly one differing stream coordinate to 1 makes the
            # two sides differ at n; all other variables/coordinates are zero.
            return n, sorted(diff)[0]
    return None


def _lean_nat_cases(var, depth, indent="  "):
    """Nested cases n=0,1,...,depth-1, then stable successor^depth branch."""
    if depth <= 0:
        return [indent + "simp [m] <;> ring"]
    out = [indent + "cases %s with" % var,
           indent + "| zero =>",
           indent + "    simp [m] <;> ring",
           indent + "| succ %s =>" % var]
    out += _lean_nat_cases(var, depth - 1, indent + "    ")
    return out


def _f2_shift_candidate(law_a, law_b):
    label = "f2-one-sided-shift"
    if not SOLO_JUDGE_AVAILABLE or label in INF_REJECTED:
        return None
    if not _f2_shift_holds(law_a):
        return None
    vio = _f2_shift_violation(law_b)
    if vio is None:
        return None
    coord, (hot_var, hot_idx) = vio
    va, vb = law_vars(law_a), law_vars(law_b)
    depth = max(_term_depth(law_a[0]), _term_depth(law_a[1]))
    lines = [
        "let m : Magma (Nat → ZMod 2) := ⟨fun x y n => "
        "(match n with | 0 => 0 | k + 1 => x k) + y (n + 1)⟩",
        "refine ⟨Nat → ZMod 2, m, ?_, ?_⟩",
        "· intro " + " ".join(va),
        "  funext n",
    ]
    lines += _lean_nat_cases("n", depth, "  ")
    lines += ["· intro h",
              "  let z0 : Nat → ZMod 2 := fun _ => 0",
              "  let e : Nat → ZMod 2 := fun n => if n = %d then 1 else 0" % hot_idx]
    args = ["e" if v == hot_var else "z0" for v in vb]
    lines += ["  have bad := congrFun (h %s) %d" % (" ".join(args), coord),
              "  norm_num [m, z0, e] at bad"]
    return {"claim": "FALSE", "carrier": "infinite",
            "lean_imports": ["Mathlib.Data.ZMod.Basic", "Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum"],
            "lean_statement": refutation_statement(law_a, law_b),
            "lean_proof": "\n".join(lines),
            "method": "infinite-model:" + label,
            "stats": {"family": label, "exact": True, "coord": coord,
                      "hot": [hot_var, hot_idx], "antecedent_depth": depth}}


# Dual orientation of the exact F2 shift model:
#     x ◇ y = L x + R y.
# The two orientations satisfy dual families of identities, so this closes a
# cheap symmetry hole in Austin/finite-only implication coverage.
def _f2_dual_support(t, n):
    if isinstance(t, str):
        return {(t, n)}
    left = _f2_dual_support(t[1], n + 1)
    right = set() if n == 0 else _f2_dual_support(t[2], n - 1)
    return left ^ right


def _f2_dual_holds(law):
    d = max(_term_depth(law[0]), _term_depth(law[1]))
    return all(_f2_dual_support(law[0], n) == _f2_dual_support(law[1], n)
               for n in range(d + 2))


def _f2_dual_violation(law):
    d = max(_term_depth(law[0]), _term_depth(law[1]))
    for n in range(d + 2):
        diff = _f2_dual_support(law[0], n) ^ _f2_dual_support(law[1], n)
        if diff:
            return n, sorted(diff)[0]
    return None


def _f2_dual_candidate(law_a, law_b):
    label = "f2-one-sided-shift-dual"
    if not SOLO_JUDGE_AVAILABLE or label in INF_REJECTED:
        return None
    if not _f2_dual_holds(law_a):
        return None
    vio = _f2_dual_violation(law_b)
    if vio is None:
        return None
    coord, (hot_var, hot_idx) = vio
    va, vb = law_vars(law_a), law_vars(law_b)
    depth = max(_term_depth(law_a[0]), _term_depth(law_a[1]))
    lines = [
        "let m : Magma (Nat → ZMod 2) := ⟨fun x y n => "
        "x (n + 1) + (match n with | 0 => 0 | k + 1 => y k)⟩",
        "refine ⟨Nat → ZMod 2, m, ?_, ?_⟩",
        "· intro " + " ".join(va),
        "  funext n",
    ]
    lines += _lean_nat_cases("n", depth, "  ")
    lines += ["· intro h",
              "  let z0 : Nat → ZMod 2 := fun _ => 0",
              "  let e : Nat → ZMod 2 := fun n => if n = %d then 1 else 0" % hot_idx]
    args = ["e" if v == hot_var else "z0" for v in vb]
    lines += ["  have bad := congrFun (h %s) %d" % (" ".join(args), coord),
              "  norm_num [m, z0, e] at bad"]
    return {"claim": "FALSE", "carrier": "infinite",
            "lean_imports": ["Mathlib.Data.ZMod.Basic", "Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum"],
            "lean_statement": refutation_statement(law_a, law_b),
            "lean_proof": "\n".join(lines),
            "method": "infinite-model:" + label,
            "stats": {"family": label, "exact": True, "coord": coord,
                      "hot": [hot_var, hot_idx], "antecedent_depth": depth}}


# ---------------- FALSE: parity/residue-ray infinite model ----------------
#
# Community-derived mechanism, distilled from EQT02-S00023 / EQT02-M00010:
# represent Nat as Bool x Nat (parity, quotient) and use an unbounded ray action
# corresponding numerically to
#
#     a ◇ x = x + 1                 when parity(a) = parity(x)
#             max(0, x - 1)         otherwise.
#
# On Bool x Nat this action is proof-friendly and every left translation is an
# involution whose control depends only on the Bool coordinate.  Consequently
# antecedents of the structural form
#
#     x = y ◇ ((z ◇ (y ◇ y)) ◇ x)
#
# (or the reversed equation) hold universally: z ◇ (y ◇ y) has the same Bool
# control coordinate as y, so the two nested left actions cancel.  We search a
# small exact prefix only for a GOAL assignment whose outputs have different
# parity; antecedent validity is *not* inferred from sampling and is discharged
# by the fixed Lean proof template below.


def _parity_ray_roles(law):
    """Recognize x = y*((z*(y*y))*x), up to variable names/orientation."""
    for reversed_eq, lone, body in ((False, law[0], law[1]),
                                    (True, law[1], law[0])):
        if not isinstance(lone, str) or isinstance(body, str) or body[0] != "op":
            continue
        x = lone
        y = body[1]
        tail = body[2]
        if not isinstance(y, str) or isinstance(tail, str) or tail[0] != "op" or tail[2] != x:
            continue
        middle = tail[1]
        if isinstance(middle, str) or middle[0] != "op":
            continue
        z = middle[1]
        square = middle[2]
        if (isinstance(z, str) and not isinstance(square, str) and square[0] == "op"
                and square[1] == y and square[2] == y
                and len({x, y, z}) == 3):
            return {"reversed": reversed_eq, "x": x, "y": y, "z": z}
    return None


def _parity_ray_op(a, x):
    return x + 1 if (a & 1) == (x & 1) else max(0, x - 1)


def _parity_ray_eval(t, env):
    if isinstance(t, str):
        return env[t]
    return _parity_ray_op(_parity_ray_eval(t[1], env),
                          _parity_ray_eval(t[2], env))


def _parity_ray_goal_witness(law, value_limit=5):
    """Find a small goal violation visible already in the parity coordinate."""
    vs = law_vars(law)
    # Different parity gives a tiny proof via congrArg Prod.fst / Bool.noConfusion.
    for vals in itertools.product(range(value_limit + 1), repeat=len(vs)):
        env = dict(zip(vs, vals))
        a = _parity_ray_eval(law[0], env)
        b = _parity_ray_eval(law[1], env)
        if a != b and (a & 1) != (b & 1):
            return env, a, b
    return None


def _lean_nat_lit(k):
    # Succ form avoids pulling numeral arithmetic into the proof's critical
    # contradiction and mirrors the community proof template.
    out = "Nat.zero"
    for _ in range(max(0, int(k))):
        out = "Nat.succ (%s)" % out
    return out


def _parity_pair_lit(k):
    return "(%s, %s)" % ("true" if int(k) & 1 else "false", _lean_nat_lit(int(k) // 2))


def _parity_ray_candidate(law_a, law_b):
    label = "parity-residue-ray"
    if not SOLO_JUDGE_AVAILABLE or label in INF_REJECTED:
        return None
    roles = _parity_ray_roles(law_a)
    if roles is None:
        return None
    # Keep this first-pass deterministic cost tiny.  These parity constructions
    # usually expose a target failure on {0,...,5}; larger search belongs in a
    # research/offline model-fingerprint pass rather than the contest hot path.
    got = _parity_ray_goal_witness(law_b, value_limit=5)
    if got is None:
        return None
    env, lhs_value, rhs_value = got
    va, vb = law_vars(law_a), law_vars(law_b)
    x, y, z = roles["x"], roles["y"], roles["z"]
    changed_h = "%s = op %s (op (op %s (op %s %s)) %s)" % (x, y, z, y, y, x)
    if roles["reversed"]:
        changed_h = "op %s (op (op %s (op %s %s)) %s) = %s" % (y, z, y, y, x, x)
    witness_args = " ".join(_parity_pair_lit(env[v]) for v in vb)
    lhs_literal = _parity_pair_lit(lhs_value)
    rhs_literal = _parity_pair_lit(rhs_value)
    # If lhs is false and rhs true use h; for true=false flip it.
    contradiction = ("Bool.noConfusion (congrArg Prod.fst bad)"
                     if (lhs_value & 1) == 0
                     else "Bool.noConfusion (Eq.symm (congrArg Prod.fst bad))")
    lines = [
        "let op : (Bool × Nat) → (Bool × Nat) → (Bool × Nat) :=",
        "  fun a x =>",
        "    match a.1, x.1 with",
        "    | false, q => (Bool.not q, x.2)",
        "    | true, false =>",
        "        Nat.rec (false, Nat.zero) (fun k _ => (true, k)) x.2",
        "    | true, true => (false, Nat.succ x.2)",
        "let model : Magma (Bool × Nat) := ⟨op⟩",
        "refine ⟨Bool × Nat, model, ?_, ?_⟩",
        "· intro " + " ".join(va),
        "  change " + changed_h,
    ]
    if roles["reversed"]:
        lines.append("  symm")
    lines += [
        "  have op_left_congr (a b x : Bool × Nat) (hab : a.1 = b.1) :",
        "      op a x = op b x := by",
        "    rcases a with ⟨qa, ka⟩",
        "    rcases b with ⟨qb, kb⟩",
        "    rcases x with ⟨qx, kx⟩",
        "    cases hab",
        "    rfl",
        "  have op_invol (a x : Bool × Nat) : op a (op a x) = x := by",
        "    rcases a with ⟨qa, ka⟩",
        "    rcases x with ⟨qx, kx⟩",
        "    cases qa",
        "    · cases qx <;> rfl",
        "    · cases qx",
        "      · exact Nat.rec (by rfl) (fun k _ => by rfl) kx",
        "      · rfl",
        "  have middle_key (z y : Bool × Nat) :",
        "      (op z (op y y)).1 = y.1 := by",
        "    rcases z with ⟨qz, kz⟩",
        "    rcases y with ⟨qy, ky⟩",
        "    cases qz <;> cases qy <;> rfl",
        "  rw [op_left_congr (op %s (op %s %s)) %s %s (middle_key %s %s)]" % (z, y, y, y, x, z, y),
        "  exact (op_invol %s %s).symm" % (y, x),
        "· intro goal_holds",
        "  have bad := goal_holds " + witness_args,
        "  change %s = %s at bad" % (lhs_literal, rhs_literal),
        "  exact " + contradiction,
    ]
    return {"claim": "FALSE", "carrier": "infinite",
            "lean_imports": [],
            "lean_statement": refutation_statement(law_a, law_b),
            "lean_proof": "\n".join(lines),
            "method": "infinite-model:" + label,
            "stats": {"family": label, "exact_antecedent": True,
                      "goal_search_bound": 5,
                      "witness": {v: env[v] for v in vb},
                      "goal_values": [lhs_value, rhs_value]}}


# ---------------- TRUE: rewrite search ----------------

def _rules(law_a):
    return [(law_a[0], law_a[1], False), (law_a[1], law_a[0], True)]


def _steps(t, law_a, goal_vars, limit):
    """One-step rewrites of t: yields (new_term, args, reversed_flag, position)."""
    a_vars = law_vars(law_a)
    out = []
    for lhs, rhs, rev in _rules(law_a):
        for p in positions(t):
            sub = t
            for i in p:
                sub = sub[i]
            sigma = match(lhs, sub, {})
            if sigma is None:
                continue
            missing = [v for v in variables(rhs) if v not in sigma]
            fillers = [[goal_vars[0] if goal_vars else "x"]] * len(missing)
            for v, f in zip(missing, fillers):
                sigma[v] = f[0]
            new_sub = subst(rhs, sigma)
            nt = replace(t, p, new_sub)
            if nt == t or size(nt) > limit:
                continue
            args = [sigma.get(v, goal_vars[0] if goal_vars else "x") for v in a_vars]
            out.append((nt, args, rev, p))
    return out


def _reconstruct(meet, fwd, bwd):
    """Build the term/step chain from lhsB to rhsB through the meeting point."""
    chain = []
    cur = meet
    while fwd[cur][0] is not None:
        prev, args, rev, pos = fwd[cur]
        chain.append((prev, cur, args, rev, pos))
        cur = prev
    chain.reverse()
    cur = meet
    while bwd[cur][0] is not None:
        nxt, args, rev, pos = bwd[cur]
        chain.append((cur, nxt, args, not rev, pos))
        cur = nxt
    return chain


def find_proof(law_a, law_b, deadline=None, nodes_cap=None):
    lhs, rhs = law_b
    goal_vars = law_vars(law_b) or ["x"]
    if lhs == rhs:
        return []
    limit = max(size(lhs), size(rhs)) + CONF["size_slack"]
    if deadline is None:
        deadline = time.time() + CONF["bfs_secs"]
    if nodes_cap is None:
        nodes_cap = CONF["bfs_nodes"]
    fwd = {lhs: (None, None, None, None)}
    bwd = {rhs: (None, None, None, None)}
    frontier_f, frontier_b = [lhs], [rhs]
    nodes = 0
    for _ in range(CONF["bfs_depth"]):
        if time.time() > deadline:
            return None
        for side in (0, 1):
            seen, other = (fwd, bwd) if side == 0 else (bwd, fwd)
            frontier = frontier_f if side == 0 else frontier_b
            new = []
            for t in frontier:
                if time.time() > deadline:
                    return None
                for nt, args, rev, pos in _steps(t, law_a, goal_vars, limit):
                    nodes += 1
                    if nodes > nodes_cap:
                        return None
                    if nt in seen:
                        continue
                    seen[nt] = (t, args, rev, pos)
                    new.append(nt)
                    if nt in other:
                        return _reconstruct(nt, fwd, bwd)
            if side == 0:
                frontier_f = new
            else:
                frontier_b = new
        if not frontier_f and not frontier_b:
            return None
    return None


def _step_valid(law_a, src, tgt, args, rev, pos):
    """Is `src -> tgt` really the law_a instance `args` applied at `pos`?

    Rebuilds the instantiated axiom from the recorded arguments and checks the
    subterm it replaces literally, i.e. the certificate is re-derived from the
    rule set rather than trusted.  `pos is None` (legacy tactic steps) means the
    position was not recorded, so any position that works is accepted.
    """
    a_vars = law_vars(law_a)
    if len(args) != len(a_vars):
        return False
    sigma = dict(zip(a_vars, args))
    src_pat = subst(law_a[1] if rev else law_a[0], sigma)
    tgt_pat = subst(law_a[0] if rev else law_a[1], sigma)
    cands = [pos] if pos is not None else list(positions(src))
    for p in cands:
        try:
            if at(src, p) != src_pat:
                continue
            if replace(src, p, tgt_pat) == tgt:
                return True
        except (IndexError, TypeError):
            continue
    return False


def rewalk(law_a, law_b, chain):
    """Independently re-verify a chain before it is serialized to Lean.

    Checks (a) endpoints are exactly law_b's two sides, (b) consecutive steps
    share their endpoint term, (c) every single step is a genuine law_a rewrite
    at its recorded position.  This is deliberately independent of the Lean
    self-check: an emitter or search bug is caught here, in our own semantics,
    before any claim is made.
    """
    if not chain:
        return law_b[0] == law_b[1]
    if chain[0][0] != law_b[0] or chain[-1][1] != law_b[1]:
        return False
    for i in range(len(chain) - 1):
        if chain[i][1] != chain[i + 1][0]:
            return False
    for src, tgt, args, rev, pos in chain:
        if not _step_valid(law_a, src, tgt, args, rev, pos):
            return False
    return True


def _step_tactic(args, rev):
    app = "hA" + ("".join(" " + lean_term(a) for a in args))
    prim = "rw [\u2190 %s]" % app if rev else "rw [%s]" % app
    alt = "rw [%s]" % app if rev else "rw [\u2190 %s]" % app
    return "by first | %s | %s | simp only [hA] | rfl" % (prim, alt)


def _step_term(src, args, rev, pos):
    """Position-aware term proof of `src = tgt` for the rewrite at `pos`.

    The instantiated hypothesis `hA args : lhsA[sigma] = rhsA[sigma]` proves the
    equality of the *subterms* at `pos` (reversed via `.symm` when the rule was
    applied right-to-left).  One `congrArg` per level of `pos` lifts it to the
    whole term, so -- unlike `rw`, which rewrites the first syntactic match --
    the emitted certificate rewrites exactly the position the search used.
    """
    app = "hA" + ("".join(" " + lean_term(a) for a in args))
    proof = "(%s).symm" % app if rev else app
    for k in range(len(pos), 0, -1):
        parent = at(src, pos[:k - 1])
        if pos[k - 1] == 1:
            f = "(fun _t => op _t %s)" % lean_term(parent[2])
        else:
            f = "(op %s)" % lean_term(parent[1])
        proof = "congrArg %s (%s)" % (f, proof)
    return proof


def emit_lean(law_b, chain, style="term"):
    """Serialize the rewrite chain as a Lean 4 proof body.

    style="term"  : position-aware congruence terms (lossless).
    style="tactic": legacy `first | rw [...] | ...` fallback for steps whose
                    position is unavailable.
    """
    vs = law_vars(law_b)
    body = []
    if vs:
        body.append("intro " + " ".join(vs))
    if not chain:
        body.append("rfl")
        return "\n".join(body)

    def just(step):
        src, _tgt, args, rev, pos = step
        if style == "term" and pos is not None:
            return _step_term(src, args, rev, pos)
        return _step_tactic(args, rev)

    lines = ["calc " + lean_term(chain[0][0]) + " = " + lean_term(chain[0][1]) + " := " + just(chain[0])]
    for step in chain[1:]:
        lines.append("  _ = " + lean_term(step[1]) + " := " + just(step))
    body.extend(lines)
    return "\n".join(body)


# ---------------- TRUE: proof-carrying equality saturation ----------------
#
# Distilled from the community M00010 e-graph idea, but deliberately kept
# small and compatible with EULER's existing chain certificate format.  The
# important upgrade over the ordinary BFS is *e-matching style instantiation*:
# when a rewrite direction contains variables not fixed by matching the
# selected subterm, those variables are filled from a bounded pool of useful
# goal/subterm representatives rather than all being collapsed to one variable.
# This lets the search make the large, structured expansions that hard TRUE
# implications often require.  Every discovered edge is still one literal
# instance of the hypothesis at one position; `rewalk` independently checks
# the whole returned chain before Lean emission.


def _sat_subterms(t, out=None):
    if out is None:
        out = []
    if t not in out:
        out.append(t)
    if not isinstance(t, str):
        _sat_subterms(t[1], out)
        _sat_subterms(t[2], out)
    return out


def _sat_seed_pool(law_a, law_b, cap):
    pool = []
    for t in (law_b[0], law_b[1], law_a[0], law_a[1]):
        for q in _sat_subterms(t, []):
            if q not in pool:
                pool.append(q)
    # Goal variables are especially useful fillers and are cheapest first.
    goal_vars = law_vars(law_b) or ["x"]
    ordered = []
    for v in goal_vars:
        if v not in ordered:
            ordered.append(v)
    for t in sorted(pool, key=lambda q: (size(q), show(q))):
        if t not in ordered:
            ordered.append(t)
    return ordered[:max(2, cap)]


def _sat_instantiations(missing, fillers, cap):
    if not missing:
        yield {}
        return
    # Cartesian products are the power source but also the blow-up risk.
    # Enumerate low-complexity tuples first and stop deterministically.
    ranked = sorted(fillers, key=lambda q: (size(q), show(q)))
    emitted = 0
    for vals in itertools.product(ranked, repeat=len(missing)):
        yield dict(zip(missing, vals))
        emitted += 1
        if emitted >= cap:
            return


def _sat_steps(t, law_a, goal_vars, fillers, size_limit, inst_cap):
    a_vars = law_vars(law_a)
    emitted = set()
    for lhs, rhs, rev in _rules(law_a):
        rhs_vars = variables(rhs, [])
        for p in positions(t):
            sub = at(t, p)
            sigma0 = match(lhs, sub, {})
            if sigma0 is None:
                continue
            missing = [v for v in rhs_vars if v not in sigma0]
            for extra in _sat_instantiations(missing, fillers, inst_cap):
                sigma = dict(sigma0)
                sigma.update(extra)
                # Any axiom variables irrelevant to this orientation can use a
                # cheap goal variable; they do not affect the replacement.
                fallback = goal_vars[0] if goal_vars else "x"
                args = [sigma.get(v, fallback) for v in a_vars]
                new_sub = subst(rhs, sigma)
                nt = replace(t, p, new_sub)
                if nt == t or size(nt) > size_limit:
                    continue
                key = (nt, tuple(map(show, args)), rev, p)
                if key in emitted:
                    continue
                emitted.add(key)
                yield nt, args, rev, p


def equality_saturation_proof(law_a, law_b, secs=None, terms_cap=None):
    """Bounded proof-carrying equality saturation for one-hypothesis goals.

    This is intentionally not a full egg implementation.  It preserves the
    high-value mechanism for this contest -- diverse e-matching substitutions
    and shared term representatives -- while returning EULER-native primitive
    rewrite edges.  Thus a win requires no new trusted Lean renderer.
    """
    if law_b[0] == law_b[1]:
        return []
    if secs is None:
        secs = CONF.get("egraph_secs", 10.0)
    if terms_cap is None:
        terms_cap = CONF.get("egraph_terms", 18000)
    deadline = time.time() + max(0.05, secs)
    goal_vars = law_vars(law_b) or ["x"]
    fillers = _sat_seed_pool(law_a, law_b, CONF.get("egraph_fillers", 12))
    limit = max(size(law_b[0]), size(law_b[1]), size(law_a[0]), size(law_a[1])) \
            + CONF.get("egraph_size_slack", 12)
    fwd = {law_b[0]: (None, None, None, None)}
    bwd = {law_b[1]: (None, None, None, None)}
    front_f, front_b = [law_b[0]], [law_b[1]]
    total = 2
    rounds = CONF.get("egraph_rounds", 10)
    inst_cap = CONF.get("egraph_inst_cap", 72)

    # Newly discovered representatives become candidate fillers.  This is the
    # e-graph-like feedback loop: useful composite terms discovered on one side
    # can instantiate missing variables in later rewrites on either side.
    for _round in range(rounds):
        if time.time() >= deadline or total >= terms_cap:
            break
        progressed = False
        for side in (0, 1):
            seen, other = (fwd, bwd) if side == 0 else (bwd, fwd)
            frontier = front_f if side == 0 else front_b
            fresh = []
            for t in frontier:
                if time.time() >= deadline or total >= terms_cap:
                    break
                for nt, args, rev, pos in _sat_steps(
                        t, law_a, goal_vars, fillers, limit, inst_cap):
                    if nt in seen:
                        continue
                    seen[nt] = (t, args, rev, pos)
                    fresh.append(nt)
                    total += 1
                    progressed = True
                    if nt not in fillers and len(fillers) < CONF.get("egraph_fillers", 12):
                        fillers.append(nt)
                    if nt in other:
                        chain = _reconstruct(nt, fwd, bwd)
                        if rewalk(law_a, law_b, chain):
                            return chain
                    if total >= terms_cap:
                        break
            if side == 0:
                front_f = fresh
            else:
                front_b = fresh
        if not progressed:
            break
    return None


# ---------------- TRUE: exact compact proof e-graph ----------------
# Faithful compact port of the community M00010 single-rule e-graph core.
# Internally it keeps M00010's tagged term representation; only the final
# primitive rewrite trace is converted into EULER's chain format.  This avoids
# changing the saturation semantics while preserving EULER's independent
# `rewalk` and Lean emitter as the certificate trust boundary.

class _XEggError(Exception): pass

def _xm(t):
    return ('var',t) if isinstance(t,str) else ('op',_xm(t[1]),_xm(t[2]))

def _xe(t):
    return t[1] if t[0]=='var' else ('op',_xe(t[1]),_xe(t[2]))

def _xs(t): return 1 if t[0]=='var' else _xs(t[1])+_xs(t[2])+1

def _xsub(t,sg):
    return sg[t[1]] if t[0]=='var' and t[1] in sg else (t if t[0]=='var' else ('op',_xsub(t[1],sg),_xsub(t[2],sg)))

def _xsubs(t,acc=None):
    if acc is None: acc=[]
    acc.append(t)
    if t[0]=='op': _xsubs(t[1],acc); _xsubs(t[2],acc)
    return acc

def _xpvars(t,acc=None):
    if acc is None: acc=set()
    if t[0]=='var': acc.add(t[1])
    else: _xpvars(t[1],acc); _xpvars(t[2],acc)
    return acc

class _XEgg:
    def __init__(self):
        self.parent=[]; self.size_rep=[]; self.enodes={}; self.witness={}
        self.term_class={}; self.class_repr={}; self.adj={}
    def find(self,a):
        while self.parent[a]!=a:
            self.parent[a]=self.parent[self.parent[a]]; a=self.parent[a]
        return a
    def canon(self,node):
        return ('op',self.find(node[1]),self.find(node[2])) if node[0]=='op' else node
    def _register(self,t,cid):
        if t not in self.term_class:self.term_class[t]=cid
        r=self.find(cid); best=self.class_repr.get(r)
        if best is None or _xs(t)<_xs(best):self.class_repr[r]=t
    def _add_edge(self,a,b,reason):
        self.adj.setdefault(a,[]).append((b,reason,False)); self.adj.setdefault(b,[]).append((a,reason,True))
    def add_term(self,t):
        known=self.term_class.get(t)
        if known is not None:return self.find(known)
        if t[0]=='var': key=t; sz=1
        else:
            a=self.add_term(t[1]); b=self.add_term(t[2]); key=('op',self.find(a),self.find(b)); sz=self.size_rep[self.find(a)]+self.size_rep[self.find(b)]+1
        ex=self.enodes.get(key)
        if ex is not None:
            cid=self.find(ex); self.size_rep[cid]=min(self.size_rep[cid],sz); w=self.witness.get(key)
            if w is not None and w!=t:self._add_edge(t,w,('congr',))
            self._register(t,cid); return cid
        cid=len(self.parent); self.parent.append(cid); self.size_rep.append(sz); self.enodes[key]=cid; self.witness[key]=t; self._register(t,cid); return cid
    def merge_terms(self,a_t,b_t,reason):
        a=self.find(self.term_class[a_t]); b=self.find(self.term_class[b_t])
        if a_t!=b_t:self._add_edge(a_t,b_t,reason)
        if a==b:return False
        self.parent[a]=b; self.size_rep[b]=min(self.size_rep[b],self.size_rep[a]); ra,rb=self.class_repr.get(a),self.class_repr.get(b)
        if ra is not None and (rb is None or _xs(ra)<_xs(rb)):self.class_repr[b]=ra
        return True
    def rebuild(self):
        changed=True
        while changed:
            changed=False; fresh={}; fw={}
            for node,cid in self.enodes.items():
                node2=self.canon(node); cid=self.find(cid); wit=self.witness.get(node); other=fresh.get(node2)
                if other is None:
                    fresh[node2]=cid
                    if wit is not None:fw[node2]=wit
                elif self.find(other)!=cid:
                    ow=fw.get(node2)
                    if wit is not None and ow is not None:self.merge_terms(ow,wit,('congr',))
                    else:self.parent[self.find(other)]=cid
                    changed=True
            self.enodes=fresh; self.witness=fw
    def class_of(self,t):return self.find(self.term_class[t])
    def _tree_path(self,s,t):
        if s==t:return []
        prev={s:(s,(),False)}; queue=[s]
        while queue:
            nxt=[]
            for u in queue:
                for v,reason,flipped in self.adj.get(u,()):
                    if v in prev:continue
                    prev[v]=(u,reason,flipped)
                    if v==t:
                        path=[]; cur=t
                        while cur!=s:
                            p,r,f=prev[cur]; path.append((p,cur,r,f)); cur=p
                        path.reverse(); return path
                    nxt.append(v)
            queue=nxt
        raise _XEggError('disconnected')
    def explain(self,s,t,depth=0,budget=None):
        if depth>300:raise _XEggError('depth')
        if budget is None:budget=[200000]
        steps=[]; cur=s
        for a,b,reason,flipped in self._tree_path(s,t):
            budget[0]-=1
            if budget[0]<0:raise _XEggError('budget')
            if reason and reason[0]=='rule': steps.append(((),dict(reason[1]),flipped)); cur=b
            elif reason and reason[0]=='congr':
                if a[0]!='op' or b[0]!='op':raise _XEggError('bad congr')
                for sub in self.explain(a[1],b[1],depth+1,budget):steps.append((('L',)+sub[0],sub[1],sub[2]))
                for sub in self.explain(a[2],b[2],depth+1,budget):steps.append((('R',)+sub[0],sub[1],sub[2]))
                cur=b
            else:raise _XEggError('reason')
        if cur!=t:raise _XEggError('endpoint')
        return steps

def _xematch(egg,pattern,cid,sg,by):
    cid=egg.find(cid)
    if pattern[0]=='var':
        v=pattern[1]; bound=sg.get(v)
        if bound is not None:
            if egg.find(bound)==cid:yield sg
            return
        s2=dict(sg); s2[v]=cid; yield s2; return
    for node in by.get(cid,()):
        if node[0]!='op':continue
        for s1 in _xematch(egg,pattern[1],node[1],sg,by):yield from _xematch(egg,pattern[2],node[2],s1,by)


def _xat(t,pos):
    for q in pos: t=t[1] if q=='L' else t[2]
    return t

def _xrep(t,pos,new):
    if not pos:return new
    if pos[0]=='L':return ('op',_xrep(t[1],pos[1:],new),t[2])
    return ('op',t[1],_xrep(t[2],pos[1:],new))

def _xdiff(a,b):
    if a==b:return None
    if a[0]=='op' and b[0]=='op':
        l=a[1]!=b[1]; r=a[2]!=b[2]
        if l and not r:
            sub=_xdiff(a[1],b[1]); return ('L',)+(sub if sub is not None else ())
        if r and not l:
            sub=_xdiff(a[2],b[2]); return ('R',)+(sub if sub is not None else ())
    return ()

def _xmatch(pat,t,sg=None):
    if sg is None:sg={}
    if pat[0]=='var':
        b=sg.get(pat[1])
        if b is None:
            z=dict(sg);z[pat[1]]=t;return z
        return sg if b==t else None
    if t[0]!='op':return None
    s1=_xmatch(pat[1],t[1],sg)
    return None if s1 is None else _xmatch(pat[2],t[2],s1)

def _xone(s,t,lhs,rhs):
    if s==t:return None
    pos=_xdiff(s,t)
    if pos is None:return None
    ss,tt=_xat(s,pos),_xat(t,pos)
    for symm,(frm,to) in ((False,(lhs,rhs)),(True,(rhs,lhs))):
        sg=_xmatch(frm,ss,{})
        if sg is None:continue
        sg2=_xmatch(to,tt,dict(sg))
        if sg2 is not None and _xsub(frm,sg2)==ss:return (pos,sg2,symm)
    return None

def _xshort(start,steps,lhs,rhs):
    kept=[]; states=[start]; index={start:0}; cur=start
    for pos,sg,symm in steps:
        frm=_xsub(rhs if symm else lhs,sg)
        try:
            if _xat(cur,pos)!=frm:return None
        except Exception:return None
        to=_xsub(lhs if symm else rhs,sg); nxt=_xrep(cur,pos,to); seen=index.get(nxt)
        if seen is not None:
            for t in states[seen+1:]:index.pop(t,None)
            del kept[seen:];del states[seen+1:]
        else:
            kept.append((pos,sg,symm));states.append(nxt);index[nxt]=len(states)-1
        cur=nxt
    return kept

def _xbridge(start,steps,lhs,rhs):
    states=[start];cur=start
    for pos,sg,symm in steps:
        cur=_xrep(cur,pos,_xsub(lhs if symm else rhs,sg));states.append(cur)
    out=[];i=0
    while i<len(states)-1:
        jumped=False
        for j in range(len(states)-1,i,-1):
            if j==i+1:break
            st=_xone(states[i],states[j],lhs,rhs)
            if st is not None:out.append(st);i=j;jumped=True;break
        if not jumped:
            if len(steps)!=len(states)-1:return None
            out.append(steps[i]);i+=1
    return out

def _xsteps_chain(law_a,law_b,steps):
    cur=law_b[0]; out=[]; av=law_vars(law_a); fallback=(law_vars(law_b) or ['x'])[0]
    for xpos,xsg,symm in steps:
        pos=tuple(1 if q=='L' else 2 for q in xpos); sg={k:_xe(v) for k,v in xsg.items()}; args=[sg.get(v,fallback) for v in av]
        frm=subst(law_a[1] if symm else law_a[0],sg); to=subst(law_a[0] if symm else law_a[1],sg)
        if at(cur,pos)!=frm:return None
        nxt=replace(cur,pos,to); out.append((cur,nxt,args,symm,pos)); cur=nxt
    return out if cur==law_b[1] else None

def exact_proof_egraph(law_a,law_b,secs=None):
    lhs_p,rhs_p=_xm(law_a[0]),_xm(law_a[1]); L,R=_xm(law_b[0]),_xm(law_b[1])
    if L==R:return []
    egg=_XEgg(); pool=[]
    for t in _xsubs(L,[])+_xsubs(R,[]):
        cid=egg.add_term(t)
        if cid not in pool:pool.append(cid)
    orientations=[]
    for symm,(a,b) in ((False,(lhs_p,rhs_p)),(True,(rhs_p,lhs_p))):orientations.append((a,b,sorted(_xpvars(b)-_xpvars(a)),symm))
    deadline=time.time()+(secs if secs is not None else CONF.get('egraph_secs',10.0)); done=set(); max_enodes=max(60000,CONF.get('egraph_terms',18000)); max_apps=200000
    proved=egg.class_of(L)==egg.class_of(R)
    for rnd in range(30):
        if proved or time.time()>=deadline or len(egg.enodes)>max_enodes:break
        expand=min(36,10+6*rnd); free_pool=min(18,8+2*rnd)
        cur_pool=sorted({egg.find(c) for c in pool},key=lambda c:egg.size_rep[c]); pool=cur_pool[:36]
        prods=[]
        for p in pool[:expand]:
            for q in pool[:expand]:prods.append(egg.add_term(('op',egg.class_repr[egg.find(p)],egg.class_repr[egg.find(q)])))
        for c in prods:
            c=egg.find(c)
            if c not in pool and len(pool)<36:pool.append(c)
        by={}
        for node,cid in egg.enodes.items():by.setdefault(egg.find(cid),[]).append(egg.canon(node))
        apps=[]; outtime=False
        for oi,(a,b,free,symm) in enumerate(orientations):
            classes=pool[:expand] if a[0]=='var' else list(by)
            for cid in classes:
                if time.time()>=deadline:outtime=True;break
                for sg in _xematch(egg,a,cid,{},by):
                    if len(apps)>=max_apps or time.time()>=deadline:outtime=True;break
                    key=(oi,egg.find(cid),tuple(sorted((v,egg.find(c)) for v,c in sg.items())))
                    if not free:
                        if key not in done:apps.append((0,key,a,b,sg,symm))
                    else:
                        for combo in itertools.product(pool[:free_pool],repeat=len(free)):
                            key2=key+(tuple(egg.find(c) for c in combo),)
                            if key2 in done:continue
                            s2=dict(sg); s2.update(zip(free,combo)); cost=sum(egg.size_rep[egg.find(c)] for c in s2.values()); apps.append((cost,key2,a,b,s2,symm))
                if outtime:break
            if outtime:break
        apps.sort(key=lambda x:x[0]); merged=False; capped=False; applied=0
        for cost,key,a,b,sgc,symm in apps:
            if applied>900 and cost>0:capped=True;break
            if time.time()>=deadline or len(egg.enodes)>max_enodes:capped=True;break
            if key in done:continue
            done.add(key); applied+=1; sg={v:egg.class_repr[egg.find(c)] for v,c in sgc.items()}; lt=_xsub(a,sg); rt=_xsub(b,sg); egg.add_term(lt); egg.add_term(rt); edge=(rt,lt) if symm else (lt,rt)
            if egg.merge_terms(edge[0],edge[1],('rule',tuple(sorted(sg.items())))):merged=True
            if egg.class_of(L)==egg.class_of(R):proved=True;break
        egg.rebuild(); proved=proved or egg.class_of(L)==egg.class_of(R)
        if proved or (not merged and not capped):break
    if egg.class_of(L)!=egg.class_of(R):return None
    try:steps=egg.explain(L,R)
    except (_XEggError,RecursionError):return None
    shortened=_xshort(L,steps,lhs_p,rhs_p)
    if shortened is None:return None
    for _ in range(4):
        before=len(shortened); bridged=_xbridge(L,shortened,lhs_p,rhs_p)
        if bridged is None:break
        cut=_xshort(L,bridged,lhs_p,rhs_p)
        if cut is None:break
        shortened=cut
        if len(shortened)>=before:break
    chain=_xsteps_chain(law_a,law_b,shortened)
    return chain if chain is not None and rewalk(law_a,law_b,chain) else None


# ---------------- TRUE: proof-recording ordered completion ----------------
#
# The BFS above only explores terms within a tight size window, so it misses
# implications whose proof detours through larger terms.  Ordered (unfailing)
# Knuth-Bendix completion of {law_a} closes that gap: critical pairs are added
# as equations, unorientable ones are kept and used via *ordered* rewriting.
#
# Every equation carries a PROOF: a flat chain of primitive law_a rewrite steps
# in exactly the format the position-aware emitter consumes,
#     (src_term, tgt_term, hA_args, reversed?, position)
# so a successful join replays as the same certificate the BFS path emits.
# Rewrite steps are closed under substitution and under context, which is what
# makes the chain algebra below (subst / context / reverse / concat) valid.

_KBC_VAR = "v"          # axiom variables; goal variables (x,y,z,w) are constants


def _is_var(t):
    return isinstance(t, str) and t.startswith(_KBC_VAR)


def _weight(t):
    return 1 if isinstance(t, str) else 1 + _weight(t[1]) + _weight(t[2])


def _vcount(t, acc=None):
    if acc is None:
        acc = {}
    if isinstance(t, str):
        if _is_var(t):
            acc[t] = acc.get(t, 0) + 1
    else:
        _vcount(t[1], acc)
        _vcount(t[2], acc)
    return acc


def kbo_gt(s, t):
    """Knuth-Bendix order (all symbols weight 1, precedence = name order).

    A reduction order: stable under substitution and context, well-founded.
    Total on ground terms, partial once axiom variables are involved.
    """
    vt = _vcount(t)
    if vt:
        vs = _vcount(s)
        for v, c in vt.items():
            if vs.get(v, 0) < c:
                return False
    ws, wt = _weight(s), _weight(t)
    if ws != wt:
        return ws > wt
    if isinstance(s, str) or isinstance(t, str):
        if isinstance(s, str) and isinstance(t, str):
            if _is_var(s) or _is_var(t):
                return False          # variables are comparable only to themselves
            return s > t              # constants: precedence by name
        return False                  # equal weight => both leaves or both ops
    if s[1] != t[1]:
        return kbo_gt(s[1], t[1])
    return kbo_gt(s[2], t[2])


def _occurs(v, t):
    if isinstance(t, str):
        return t == v
    return _occurs(v, t[1]) or _occurs(v, t[2])


def _apply(t, sigma):
    """Simultaneous one-pass substitution (sigma must be idempotent)."""
    if not sigma:
        return t
    if isinstance(t, str):
        return sigma.get(t, t) if _is_var(t) else t
    return ("op", _apply(t[1], sigma), _apply(t[2], sigma))


def _deref(t, sigma):
    seen = 0
    while _is_var(t) and t in sigma and seen < 200:
        nt = sigma[t]
        if nt == t:
            break
        t = nt
        seen += 1
    return t


def _resolve(sigma):
    """Turn a triangular unifier into an idempotent substitution."""
    out = dict(sigma)
    for _ in range(len(sigma) + 2):
        nxt = {v: _apply(t, out) for v, t in out.items()}
        if nxt == out:
            break
        out = nxt
    return {v: t for v, t in out.items() if t != v}


def _unify_tri(a, b, sigma):
    a, b = _deref(a, sigma), _deref(b, sigma)
    if a == b:
        return sigma
    if _is_var(a):
        if _occurs(a, _apply(b, _resolve(sigma))):
            return None
        s = dict(sigma)
        s[a] = b
        return s
    if _is_var(b):
        return _unify_tri(b, a, sigma)
    if isinstance(a, str) or isinstance(b, str):
        return None
    if not isinstance(a, tuple) or not isinstance(b, tuple):
        return None
    s = _unify_tri(a[1], b[1], sigma)
    if s is None:
        return None
    s = _unify_tri(a[2], b[2], s)
    if s is None:
        return None
    return s


def unify(a, b, sigma=None):
    """Syntactic unification; v-prefixed leaves are variables, others constants.

    Returns an idempotent substitution (so one-pass `_apply` is exact) or None.
    """
    s = _unify_tri(a, b, dict(sigma or {}))
    if s is None:
        return None
    s = _resolve(s)
    if _apply(a, s) != _apply(b, s):
        return None
    return s


# ---- chain algebra (all four operations preserve "chain of law_a steps") ----

def _chain_subst(chain, sigma):
    return [(_apply(src, sigma), _apply(tgt, sigma), [_apply(a, sigma) for a in args], rev, pos)
            for src, tgt, args, rev, pos in chain]


def _chain_ctx(chain, ctx, p):
    """Lift a chain proving `u = v` to one proving `ctx[u]_p = ctx[v]_p`."""
    return [(replace(ctx, p, src), replace(ctx, p, tgt), args, rev, tuple(p) + tuple(pos))
            for src, tgt, args, rev, pos in chain]


def _chain_rev(chain):
    return [(tgt, src, args, not rev, pos) for src, tgt, args, rev, pos in reversed(chain)]


def _chain_ok(chain):
    """Adjacency check: consecutive steps must share their endpoint term."""
    for i in range(len(chain) - 1):
        if chain[i][1] != chain[i + 1][0]:
            return False
    return True


def _ground_chain(chain, filler):
    """Instantiate any axiom variable left in intermediate steps by `filler`.

    Uniform substitution over the whole chain keeps it a valid chain; ground
    endpoints are untouched because they contain no axiom variables.
    """
    left = {}
    for src, tgt, args, _rev, _pos in chain:
        for t in [src, tgt] + list(args):
            for v in _vcount(t):
                left[v] = filler
    return _chain_subst(chain, left) if left else chain


# ---- equations ----

def _rename(eq, tag):
    l, r, ch = eq
    ren = {v: "%s%s_%d" % (_KBC_VAR, v[len(_KBC_VAR):], tag) for v in _vcount(("op", l, r))}
    return _apply(l, ren), _apply(r, ren), _chain_subst(ch, ren)


def _canon_key(l, r):
    ren = {}
    for t in (l, r):
        for v in _vcount(t):
            if v not in ren:
                ren[v] = "%s%d" % (_KBC_VAR, len(ren))
    a, b = show(_apply(l, ren)), show(_apply(r, ren))
    return (a, b) if a <= b else (b, a)


def _oriented(eqs):
    """Directions usable as *rewrite rules*: rhs variables covered by the lhs."""
    out = []
    for l, r, ch in eqs:
        vl, vr = set(_vcount(l)), set(_vcount(r))
        if l == r:
            continue
        if vr <= vl:
            out.append((l, r, ch))
        if vl <= vr:
            out.append((r, l, _chain_rev(ch)))
    return out


def _both_dirs(eqs):
    """Both directions of every equation, including extra-variable ones.

    An equation holds for *all* valuations, so using the direction that
    introduces a fresh variable is sound -- it just isn't a terminating rewrite
    rule, which is why it is excluded from `_oriented` (normalization) but kept
    for critical-pair generation and for the goal-joining search.
    """
    out = []
    for l, r, ch in eqs:
        if l == r:
            continue
        out.append((l, r, ch))
        out.append((r, l, _chain_rev(ch)))
    return out


def _eq_steps(t, rules, limit, filler):
    """One-step equational rewrites of ground term t (any direction)."""
    out = []
    for l, r, ch in rules:
        for p in positions(t):
            sub = at(t, p)
            sigma = match(l, sub, {})
            if sigma is None:
                continue
            for v in _vcount(r):
                sigma.setdefault(v, filler)
            nsub = subst(r, sigma)
            if nsub == sub:
                continue
            nt = replace(t, p, nsub)
            if size(nt) > limit:
                continue
            out.append((nt, _chain_ctx(_chain_subst(ch, sigma), t, p)))
    return out


def _assemble(meet, fwd, bwd):
    parts, cur = [], meet
    while fwd[cur][0] is not None:
        prev, seg = fwd[cur]
        parts.append(seg)
        cur = prev
    parts.reverse()
    chain = [st for seg in parts for st in seg]
    cur = meet
    while bwd[cur][0] is not None:
        nxt, seg = bwd[cur]
        chain.extend(_chain_rev(seg))
        cur = nxt
    return chain


def _join_bfs(gl, gr, rules, limit, filler, nodes_cap, depth, deadline):
    """Bidirectional search for a proof of gl = gr using the equation set."""
    if gl == gr:
        return []
    fwd = {gl: (None, None)}
    bwd = {gr: (None, None)}
    ff, fb, nodes = [gl], [gr], 0
    for _ in range(depth):
        for side in (0, 1):
            seen, other = (fwd, bwd) if side == 0 else (bwd, fwd)
            frontier = ff if side == 0 else fb
            new = []
            for t in frontier:
                if time.time() > deadline:
                    return None
                for nt, seg in _eq_steps(t, rules, limit, filler):
                    nodes += 1
                    if nodes > nodes_cap:
                        return None
                    if nt in seen:
                        continue
                    seen[nt] = (t, seg)
                    new.append(nt)
                    if nt in other:
                        return _assemble(nt, fwd, bwd)
            if side == 0:
                ff = new
            else:
                fb = new
        if not ff and not fb:
            return None
    return None


def _reduce_step(t, rules, maxsize):
    for l, r, ch in rules:
        for p in positions(t):
            sub = at(t, p)
            sigma = match(l, sub, {})
            if sigma is None:
                continue
            nsub = subst(r, sigma)
            if nsub == sub or not kbo_gt(sub, nsub):
                continue                      # ordered rewriting: must decrease
            nt = replace(t, p, nsub)
            if size(nt) > maxsize:
                continue
            return nt, _chain_ctx(_chain_subst(ch, sigma), t, p)
    return None


def _normalize(t, rules, maxsize, max_steps):
    chain = []
    for _ in range(max_steps):
        step = _reduce_step(t, rules, maxsize)
        if step is None:
            break
        t, steps = step
        chain.extend(steps)
    return t, chain


def _critical_pairs(e1, e2, maxsize):
    """Overlaps of oriented e1's lhs into non-variable subterms of e2's lhs."""
    l1, r1, ch1 = _rename(e1, 1)
    l2, r2, ch2 = _rename(e2, 2)
    out = []
    for p in positions(l2):
        sub = at(l2, p)
        if _is_var(sub):
            continue
        if p == () and (l1, r1) == (l2, r2):
            continue
        sigma = unify(l1, sub, {})
        if sigma is None:
            continue
        ctx = _apply(l2, sigma)
        u = _apply(replace(l2, p, r1), sigma)
        v = _apply(r2, sigma)
        if u == v or max(size(u), size(v)) > maxsize:
            continue
        # ctx -> u  (e1 at p)   and   ctx -> v  (e2 at root)
        chain = _chain_rev(_chain_ctx(_chain_subst(ch1, sigma), ctx, p)) + _chain_subst(ch2, sigma)
        if not _chain_ok(chain):
            continue
        out.append((u, v, chain))
    return out


def complete_and_join(law_a, law_b, secs=None, max_eqs=None):
    """Ordered completion of {law_a}; returns a primitive step chain for law_b.

    `secs` / `max_eqs` override the standard budgets (used by the escalation
    tier); default None keeps the standard-tier behaviour byte-identical.
    """
    a_vars = law_vars(law_a) or ["x"]
    ren = {v: "%s%d" % (_KBC_VAR, i) for i, v in enumerate(a_vars)}
    ax = (subst(law_a[0], ren), subst(law_a[1], ren))
    seed = [(ax[0], ax[1], [ren[v] for v in a_vars], False, ())]
    eqs = [(ax[0], ax[1], seed)]
    seen = {_canon_key(ax[0], ax[1])}

    goal_l, goal_r = law_b
    filler = (law_vars(law_b) or ["x"])[0]
    gmax = max(size(goal_l), size(goal_r)) + CONF["kbc_goal_slack"]
    emax = CONF["kbc_max_size"]
    nsteps = CONF["kbc_norm_steps"]
    if secs is None:
        secs = CONF["kbc_secs"]
    if max_eqs is None:
        max_eqs = CONF["kbc_max_eqs"]
    deadline = time.time() + secs
    stats = {"eqs": 1, "pairs": 0, "reason": ""}

    def attempt():
        chain = _join_bfs(goal_l, goal_r, _both_dirs(eqs), gmax, filler,
                          CONF["kbc_join_nodes"], CONF["kbc_join_depth"],
                          min(deadline, time.time() + CONF["kbc_join_secs"]))
        if chain is None:
            return None
        chain = _ground_chain(chain, filler)
        return chain if _chain_ok(chain) else None

    got = attempt()
    if got is not None:
        stats["reason"] = "joined-immediately"
        KBC_STATS.update(stats)
        return got

    i = 0
    while True:
        if i >= len(eqs):
            stats["reason"] = "saturated"
            break
        if time.time() > deadline:
            stats["reason"] = "time-budget"
            break
        if len(eqs) >= max_eqs:
            stats["reason"] = "eq-budget"
            break
        rules = _oriented(eqs)
        fresh = []
        for j in range(i + 1):
            for e1 in _both_dirs([eqs[i]]):
                for e2 in _both_dirs([eqs[j]]):
                    stats["pairs"] += 1
                    for u, v, ch in _critical_pairs(e1, e2, emax) + (
                            _critical_pairs(e2, e1, emax) if i != j else []):
                        nu, cu = _normalize(u, rules, emax, nsteps)
                        nv, cv = _normalize(v, rules, emax, nsteps)
                        if nu == nv:
                            continue                  # already joinable
                        full = _chain_rev(cu) + ch + cv
                        if not _chain_ok(full):
                            continue
                        key = _canon_key(nu, nv)
                        if key in seen:
                            continue
                        seen.add(key)
                        fresh.append((nu, nv, full))
        fresh.sort(key=lambda e: size(e[0]) + size(e[1]))
        for e in fresh:
            if len(eqs) >= max_eqs:
                break
            eqs.append(e)
            stats["eqs"] = len(eqs)
            got = attempt()
            if got is not None:
                stats["reason"] = "joined"
                KBC_STATS.update(stats)
                return got
        i += 1
    KBC_STATS.update(stats)
    return None


# ---------------- solver-side self-check ----------------

_VERIFY_CACHE = {}
_VERIFY_LOCK = threading.Lock()


def self_check(law_a, law_b, proof):
    """Ask the configured verifier to check a candidate certificate.

    This single-file build deliberately has no local Lean subprocess, so direct
    calls fail closed. Solo uses the judge proxy; Marathon is checked later by
    the runner. Cached per (statement, proof).

    Concurrency: the cache is guarded by a lock, but the check itself runs
    OUTSIDE the lock so N pairs can be verified in parallel.  Two threads racing
    on the same key just check twice and agree -- `verify` is a pure function
    of (statement, proof, toolchain), so the result is identical either way.
    """
    key = (statement(law_a, law_b), proof)
    with _VERIFY_LOCK:
        if key in _VERIFY_CACHE:
            return _VERIFY_CACHE[key]
    res = verify(law_a, law_b, proof)
    with _VERIFY_LOCK:
        _VERIFY_CACHE.setdefault(key, res)
        return _VERIFY_CACHE[key]


# ---------------- top level ----------------

def _checked_law(law, which):
    """Guard against raw-string inputs.

    A law is a parsed (lhs, rhs) term pair; handing in the source string makes
    every term a variable, which silently yields bogus derivations.  The harness
    always passes parsed laws -- this protects any new caller.
    """
    if isinstance(law, str):
        raise TypeError("law %s must be parsed (use laws.parse), got str %r" % (which, law))
    if not (isinstance(law, (tuple, list)) and len(law) == 2):
        raise TypeError("law %s must be a (lhs, rhs) pair, got %r" % (which, type(law)))
    return law


def solve(law_a, law_b):
    """Return a certificate dict for the claim 'law_a implies law_b'."""
    law_a, law_b = _checked_law(law_a, "a"), _checked_law(law_b, "b")
    # Exact symbolic infinite constructions before any finite search.  They
    # recognize arbitrary identities from term supports and derive witnesses;
    # no antecedent/target pair lookup is involved.
    f2 = _f2_shift_candidate(law_a, law_b)
    if f2 is not None:
        return f2
    f2d = _f2_dual_candidate(law_a, law_b)
    if f2d is not None:
        return f2d
    ray = _parity_ray_candidate(law_a, law_b)
    if ray is not None:
        return ray
    # Cheap TRUE pre-pass before finite-model search.  The old ordering spent
    # substantial time searching for impossible countermodels even on reflexive
    # and one/two-step consequences.  A tiny proof budget catches those while
    # adding negligible latency to genuinely false cases.
    pre = find_proof(law_a, law_b, deadline=time.time() + 0.08, nodes_cap=350)
    if pre is not None and rewalk(law_a, law_b, pre):
        style = "term" if all(st[4] is not None for st in pre) else "tactic"
        proof = emit_lean(law_b, pre, style=style)
        return {"claim": "TRUE", "lean_statement": statement(law_a, law_b),
                "lean_proof": proof,
                "method": "cheap-preproof-%s/%d" % (style, len(pre))}
    cm = find_countermodel(law_a, law_b)
    if cm is not None:
        return {"claim": "FALSE", "model": cm,
                "method": "finite-model:" + str(CM_STATS.get("found", "?")),
                "stats": dict(CM_STATS)}
    KBC_STATS.clear()
    chain = find_proof(law_a, law_b)
    search = "bidirectional-rewrite"
    # Path A: proof-recording superposition with E-style age/weight selection.
    # It is deliberately after finite refutation (FALSE remains cheap) and the
    # normal rewrite prover, but before the slower round-based completion and
    # deep escalation.  This is a general runtime derivation, never an ID/pair
    # lookup; _cert_to_answer and the Solo/runner judge remain the final gate.
    if chain is None and CONF["gc"]:
        gc_body, gc_info = _gc_prove(law_a, law_b)
        if CONF["debug"]:
            sys.stderr.write("[gc] %s |= %s -> %s\n" % (
                show_law(law_a), show_law(law_b), gc_info))
        if gc_body is not None:
            if not CONF["self_check"]:
                return {"claim": "TRUE", "lean_statement": statement(law_a, law_b),
                        "lean_proof": gc_body,
                        "method": "given-clause-superposition-term:" + gc_info}
            ok, detail = self_check(law_a, law_b, gc_body)
            if ok:
                return {"claim": "TRUE", "lean_statement": statement(law_a, law_b),
                        "lean_proof": gc_body,
                        "method": "given-clause-superposition-term:" + gc_info}
            if CONF["debug"]:
                sys.stderr.write("[gc self-check FAILED] %s\n" % str(detail)[:300])
    if chain is None and CONF["kbc"]:
        chain = complete_and_join(law_a, law_b)
        search = "ordered-completion"
        if CONF["debug"]:
            sys.stderr.write("[kbc] %s |= %s -> %s (eqs=%s pairs=%s)\n" % (
                show_law(law_a), show_law(law_b),
                "chain/%d" % len(chain) if chain is not None else "none",
                KBC_STATS.get("eqs"), KBC_STATS.get("pairs")))
    if chain is None and CONF.get("egraph", True):
        chain = exact_proof_egraph(law_a, law_b)
        search = "exact-proof-egraph"
        if chain is None:
            chain = equality_saturation_proof(law_a, law_b, secs=min(2.5, CONF.get("egraph_secs", 10.0)))
            search = "equality-saturation"
        if CONF["debug"]:
            sys.stderr.write("[egraph] %s |= %s -> %s\n" % (
                show_law(law_a), show_law(law_b),
                "chain/%d" % len(chain) if chain is not None else "none"))
    # Dual FALSE tail before the expensive TRUE escalation.  Keeping the CSP
    # after the cheap/standard proof engines is important: a collapse law
    # should reach its fast GC proof instead of paying a full
    # unsatisfiable finite-model window first.  Conversely, a nonlinear FALSE
    # case gets this general n=6..8 search before the 60/90-second deep prover.
    if chain is None and CONF["cm_csp"] and CONF["cm_csp_secs"] > 0:
        csp_model, csp_info = _csp_countermodel(law_a, law_b)
        CM_STATS["csp"] = csp_info
        if CONF["debug"]:
            sys.stderr.write("[csp] %s |= %s -> %s\n" % (
                show_law(law_a), show_law(law_b), csp_info))
        if csp_model is not None:
            n = csp_model["n"]
            CM_STATS["found"] = "finite-csp-n%d" % n
            return {"claim": "FALSE", "model": csp_model,
                    "method": "finite-model:finite-csp-n%d" % n,
                    "stats": dict(CM_STATS)}
    if chain is None and CONF["esc"]:
        # ESCALATION tier: deep-budget TRUE retry, reached only when every
        # standard tier failed (~7/1500 bigu pairs).  Same emitters, same
        # self-check: nothing counts without a verified certificate.
        chain = find_proof(law_a, law_b,
                           deadline=time.time() + CONF["esc_bfs_secs"],
                           nodes_cap=CONF["esc_bfs_nodes"])
        search = "bidirectional-rewrite-esc"
        if chain is None and CONF["kbc"]:
            chain = complete_and_join(law_a, law_b,
                                      secs=CONF["esc_kbc_secs"],
                                      max_eqs=CONF["esc_kbc_max_eqs"])
            search = "ordered-completion-esc"
            if CONF["debug"]:
                sys.stderr.write("[kbc-esc] %s |= %s -> %s (eqs=%s pairs=%s)\n" % (
                    show_law(law_a), show_law(law_b),
                    "chain/%d" % len(chain) if chain is not None else "none",
                    KBC_STATS.get("eqs"), KBC_STATS.get("pairs")))
    if chain is None and CONF["esc"] and CONF["esc_n5_secs"] > 0 \
            and CM_STATS.get("n4_exhausted") and not CM_STATS.get("n5_exhausted"):
        # Long exhaustive-n5 FALSE pass: only when n<=4 is provably exhausted
        # and the standard n5 pass merely timed out (bigu-0212 needed ~1629s).
        tbl5, done5 = _exhaustive_n(law_a, law_b, 5,
                                    time.time() + CONF["esc_n5_secs"])
        CM_STATS["n5_exhausted"] = bool(done5)
        if tbl5 is not None:
            CM_STATS["found"] = "exhaustive-n5-esc"
            return {"claim": "FALSE", "model": {"n": 5, "table": tbl5},
                    "method": "finite-model:exhaustive-n5-esc",
                    "stats": dict(CM_STATS)}
    if chain is None:
        # LAST tier: no finite countermodel was found and no proof either, so
        # try an infinite (Z) carrier.  Kept last so the 0.0s finite path and
        # the prover tiers are completely untouched.
        inf_reason = "off"
        if CONF["inf_cm"]:
            cert, inf_reason = find_infinite_countermodel(law_a, law_b)
            if cert is not None:
                cert["stats"] = dict(cert.get("stats") or {},
                                     cm=dict(CM_STATS), kbc=dict(KBC_STATS))
                return cert
        # statistics only (no behaviour change): lets the bench report how far
        # completion got before giving up, instead of just "no certificate".
        stats = dict(KBC_STATS)
        stats["cm"] = dict(CM_STATS)
        stats["inf_cm"] = inf_reason
        return {"claim": "UNKNOWN",
                "method": "no-certificate:cm=%s;prover=%s" % (
                    CM_STATS.get("reason") or "?", KBC_STATS.get("reason") or "bfs"),
                "stats": stats}
    if not rewalk(law_a, law_b, chain):
        # Independent of Lean: the chain does not re-derive from law_a, so it is
        # not a proof and must not be serialized as one.
        if CONF["debug"]:
            sys.stderr.write("[rewalk FAILED] %s |= %s (%s, %d steps)\n" % (
                show_law(law_a), show_law(law_b), search, len(chain)))
        return {"claim": "UNKNOWN", "method": "chain-rewalk-failed:" + search,
                "stats": dict(KBC_STATS)}
    stmt = statement(law_a, law_b)
    positioned = all(st[4] is not None for st in chain)
    styles = ["term", "tactic"] if positioned else ["tactic"]
    failures = []
    for style in styles:
        proof = emit_lean(law_b, chain, style=style)
        if not CONF["self_check"]:
            return {"claim": "TRUE", "lean_statement": stmt, "lean_proof": proof,
                    "method": "%s-%s/%d" % (search, style, len(chain))}
        ok, detail = self_check(law_a, law_b, proof)
        if ok:
            return {"claim": "TRUE", "lean_statement": stmt, "lean_proof": proof,
                    "method": "%s-%s/%d" % (search, style, len(chain))}
        failures.append((style, detail, proof))
    if CONF["debug"]:
        for style, detail, proof in failures:
            sys.stderr.write("[self-check FAILED %s] %s |= %s\n  %s\n  proof:\n%s\n" % (
                style, show_law(law_a), show_law(law_b), detail,
                "\n".join("    " + ln for ln in proof.split("\n"))))
    # A proof we cannot compile is not a certificate: downgrade instead of
    # shipping an unsound TRUE claim.
    return {"claim": "UNKNOWN", "method": "self-check-failed:" + ",".join(f[0] for f in failures),
            "stats": {"self_check_details": [f[1][:200] for f in failures]}}




# =====================================================================
# Solo / Marathon protocol front-end (JSON over stdin/stdout)
# =====================================================================

def _compose_true(law_a, law_b, proof_body):
    """Full judge submission for TRUE: anonymous proof of the judge Goal."""
    src = "import JudgeProblem\n"
    src += "export Magma (op)\n"
    src += "set_option maxHeartbeats 1600000\n"
    src += "def submission : Goal := by\n"
    src += "  intro G inst hA\n"
    src += "\n".join("  " + ln for ln in proof_body.strip("\n").split("\n")) + "\n"
    return src


def _compose_false(proof_body, extra_imports=None):
    """Full judge submission for FALSE from a refutation proof body."""
    src = ""
    for mod in (extra_imports or []):
        src += "import " + mod + "\n"
    src += "import JudgeProblem\n"
    src += "export Magma (op)\n"
    src += "set_option maxHeartbeats 1600000\n"
    src += "def submission : Goal := by\n"
    src += "\n".join("  " + ln for ln in proof_body.strip("\n").split("\n")) + "\n"
    return src


_LLM_TRUE_PROMPT = """\
You are writing a Lean 4 proof for one magma-law implication.  Deterministic
search has already failed, so build an explicit lemma DAG (often 10-40 `have`
lemmas) and let Lean check every step.

The judge has already introduced:
  G : Type
  inst : Magma G
  hA : {hypothesis}

Your remaining goal is:
  {goal}

Start by introducing exactly the goal variables: {goal_intro}

Use only kernel-transparent equality reasoning: `intro`, `exact`, `have`,
`calc`, `congrArg`, `Eq.trans`, `.trans`, `.symm`, function application, and
`rfl`.  Instantiate hA on large compound terms when necessary.  Every local
lemma must include its complete proof.  Do not use automation, arithmetic,
imports, new declarations, `sorry`, `admit`, axioms, or native_decide.

Good shapes:
  have L1 : ∀ a b : G, TERM1 = TERM2 := fun a b => ...
  exact (L1 ...).trans (...)
  calc
    lhs = mid := ...
    _ = rhs := ...

The magma operator is `◇`, never `*`.  The hypothesis name is `hA`.
Return ONLY one JSON object with a tactic body after `by`:
{{"proof":"intro x y\\nhave L1 : ... := ...\\nexact ..."}}

Runtime-search note: {search_note}
Previous Lean/preflight feedback: {feedback}
Retry round: {round_index}
"""


def _diamond_term(t):
    return show(t).replace("*", " ◇ ")


def _prompt_quantified(law):
    vs = law_vars(law)
    prefix = ("∀ " + " ".join(vs) + " : G, ") if vs else ""
    return prefix + _diamond_term(law[0]) + " = " + _diamond_term(law[1])


def _build_llm_true_prompt(law_a, law_b, feedback, round_index, search_note):
    gvars = law_vars(law_b)
    return _LLM_TRUE_PROMPT.format(
        hypothesis=_prompt_quantified(law_a),
        goal=_prompt_quantified(law_b),
        goal_intro=("`intro " + " ".join(gvars) + "`") if gvars else "no intro is needed",
        feedback=(feedback or "None")[:1600],
        round_index=round_index,
        search_note=(search_note or "no deterministic certificate")[:400],
    )


def _first_json_object(text):
    if isinstance(text, dict):
        return text
    src = str(text or "").strip()
    if src.startswith("```"):
        src = re.sub(r"^```(?:json)?\s*", "", src, count=1,
                     flags=re.IGNORECASE)
        src = re.sub(r"\s*```$", "", src, count=1)
    try:
        obj = json.loads(src)
        return obj if isinstance(obj, dict) else None
    except Exception:
        pass
    decoder = json.JSONDecoder()
    for match in re.finditer(r"\{", src):
        try:
            obj, _end = decoder.raw_decode(src[match.start():])
        except Exception:
            continue
        if isinstance(obj, dict):
            return obj
    return None


def _extract_llm_proof(response):
    """Return a lint-clean tactic body or (None, a specific repair reason)."""
    obj = _first_json_object(response)
    if obj is None:
        return None, "response was not one valid JSON object"
    proof = obj.get("proof") or obj.get("lean_proof")
    if not isinstance(proof, str):
        return None, "JSON must contain a string field named proof"
    proof = proof.strip()
    if proof.startswith("```"):
        proof = re.sub(r"^```(?:lean)?\s*", "", proof, count=1,
                       flags=re.IGNORECASE)
        proof = re.sub(r"\s*```$", "", proof, count=1).strip()
    proof = re.sub(r"^\s*by\s*(?:\n|$)", "", proof, count=1).strip()
    if not proof:
        return None, "proof body was empty"
    if len(proof.encode("utf-8")) > CONF["llm_max_proof_bytes"]:
        return None, "proof body exceeded the byte cap"
    banned = whitelist_lint(proof)
    if banned is not None:
        return None, "proof body contains banned token %r" % banned
    return proof, "ok"


def _judge_feedback(result):
    if not isinstance(result, dict):
        return "Judge returned no structured diagnostic; emit a smaller explicit calc proof."
    raw = "\n".join(str(result.get(k) or "") for k in
                    ("stderr", "message", "error", "detail", "judge_message"))
    compact = re.sub(r"\s+", " ", raw).strip()
    low = compact.lower()
    if "application type mismatch" in low or "function expected" in low:
        hint = "An hA/lemma application has the wrong arity or parentheses; supply every quantified argument explicitly. "
    elif "type mismatch" in low:
        hint = "Lean reports a type mismatch: inspect the failing equality direction and toggle `.symm` only there. "
    elif "unsolved goals" in low:
        hint = "Lean reports unsolved goals: extend the lemma chain until the exact target closes. "
    elif "unknown identifier" in low:
        hint = "A name is out of scope: use only hA, introduced variables, and your own preceding have lemmas. "
    elif "declaration" in low and "not allowed" in low:
        hint = "The judge rejected a declaration dependency; use only explicit equality combinators. "
    else:
        hint = "Repair the smallest fragment identified by Lean. "
    return (hint + (compact or "No text diagnostic was returned."))[:1600]


def _proxy_llm(prompt, round_index, feedback):
    sys.stdout.write(json.dumps({
        "call": "llm",
        "context": {
            "rendered_prompt": prompt,
            "round": str(round_index),
            "feedback": (feedback or "")[:1600],
        },
    }) + "\n")
    sys.stdout.flush()
    line = sys.stdin.readline()
    if not line:
        return {"error": "proxy-eof"}
    try:
        reply = json.loads(line)
    except Exception:
        return {"error": "unparsed-proxy-line"}
    return reply if isinstance(reply, dict) else {"error": "non-object-proxy-reply"}


def _llm_true_fallback(law_a, law_b, judge, deadline, attempted_codes,
                       initial_feedback="", search_note=""):
    """Bounded model-write -> lint -> judge -> diagnostic retry loop."""
    if not CONF["llm"]:
        return False
    feedback = initial_feedback or "No previous Lean attempt."
    for round_index in range(max(0, CONF["llm_rounds"])):
        if time.time() > deadline - CONF["llm_round_min_secs"]:
            break
        prompt = _build_llm_true_prompt(
            law_a, law_b, feedback, round_index, search_note)
        reply = _proxy_llm(prompt, round_index, feedback)
        if reply.get("error"):
            sys.stderr.write("[llm] proxy error: %s\n" % reply.get("error"))
            break
        payload = reply.get("response", reply)
        proof, reason = _extract_llm_proof(payload)
        if proof is None:
            feedback = "Preflight rejected the response: " + reason
            sys.stderr.write("[llm] round %d preflight: %s\n" %
                             (round_index, reason))
            continue
        code = _compose_true(law_a, law_b, proof)
        if len(code.encode("utf-8")) > MAX_CODE_BYTES:
            feedback = "Preflight rejected the proof: composed code exceeded the judge byte cap."
            continue
        key = ("true", code)
        if key in attempted_codes:
            feedback = "This exact proof was already rejected; produce a materially different lemma chain."
            continue
        attempted_codes.add(key)
        result = judge("true", code)
        if result.get("status") == "accepted":
            return True
        feedback = _judge_feedback(result)
        sys.stderr.write("[llm] round %d rejected: %s\n" %
                         (round_index, feedback[:260]))
    return False


def _cert_to_answer(law_a, law_b, cert):
    """(verdict, code) from a solver certificate, or (None, reason).

    whitelist_lint applies to the proof BODY only (the composed file
    legitimately contains exactly one `def submission`).
    """
    # Serialization is driven by the certificate payload, not a telemetry
    # substring.  Both term-style and tactic-style proof bodies are valid
    # judge inputs after the same source lint; requiring "term" in `method`
    # silently discarded cheap-preproof and other correctly emitted TRUEs.
    if cert.get("claim") == "TRUE" and cert.get("lean_proof"):
        body = cert["lean_proof"]
        tok = whitelist_lint(body)
        if tok is not None:
            return None, "lint:" + tok.strip()
        code = _compose_true(law_a, law_b, body)
        if len(code.encode("utf-8")) > MAX_CODE_BYTES:
            return None, "true-code-too-large"
        return "true", code
    if cert.get("claim") == "FALSE":
        if cert.get("carrier") == "infinite" and cert.get("lean_proof"):
            body = cert["lean_proof"]
        elif cert.get("model"):
            m = cert["model"]
            n, table = m.get("n"), m.get("table")
            if (not isinstance(n, int) or not (1 <= n <= 20) or
                    not isinstance(table, list) or len(table) != n * n or
                    any(not isinstance(v, int) or v < 0 or v >= n
                        for v in table)):
                return None, "invalid-model-shape"
            # Final finite-certificate trust boundary.  Re-run every universal
            # assignment even if the producing tier already validated it.
            try:
                if not holds(law_a, table, n) or holds(law_b, table, n):
                    return None, "invalid-model-replay"
            except Exception:
                return None, "invalid-model-replay-error"
            body = finite_false_proof(law_a, law_b, n, table)
        else:
            return None, "no-model"
        if body is None:
            return None, "emit-failed"
        is_inf = cert.get("carrier") == "infinite"
        tok = infinite_lint(body) if is_inf else whitelist_lint(body)
        if tok is not None:
            return None, "lint:" + tok.strip()
        code = _compose_false(body, cert.get("lean_imports") if is_inf else None)
        code_bytes = len(code.encode("utf-8"))
        if code_bytes > MAX_FALSE_CERT_BYTES or code_bytes > MAX_CODE_BYTES:
            return None, "false-code-too-large"
        return "false", code
    return None, "undecided:" + str(cert.get("method"))


def _parse_official(eq):
    return parse(eq.replace("\u25c7", "*"))


def _preflight():
    """Compose+lint self-test on a known-true and known-false shape."""
    a = parse("(x*y) = x")            # left projection
    tb = finite_false_proof(a, parse("(x*y) = y"), 2, [0, 0, 1, 1])
    assert tb is not None and whitelist_lint(tb) is None, "FALSE lint path broken"
    assert whitelist_lint("exact fun x => hA x x") is None, "TRUE lint path broken"


def solo_main():
    global SOLO_JUDGE_AVAILABLE
    SOLO_JUDGE_AVAILABLE = True
    line = sys.stdin.readline()
    msg = json.loads(line)
    prob = msg.get("problem", msg)
    budget = msg.get("budget", {}) or {}
    timeout = float(budget.get("timeout_seconds", 3600))
    t0 = time.time()
    # One shared Path-B deadline governs both the preceding heuristic infinite
    # portfolio and the LLM fallback itself.  Without this shared cutoff, the
    # portfolio could consume 82% of the wall clock even though Path B's own
    # deadline was 60%, leaving the fallback with zero runnable rounds.
    post_llm_reserve = max(120.0, min(1800.0, timeout * 0.4))
    llm_deadline = t0 + timeout - post_llm_reserve
    _preflight()
    law_a = _parse_official(prob["equation1"])
    law_b = _parse_official(prob["equation2"])
    CONF["self_check"] = False          # judge proxy is the verifier here
    # Path B must receive an actual runtime window.  The long n=5 escalation
    # can consume half of a Solo budget (and a later re-solve can repeat it), so
    # keep it out of the first deterministic pass when the judge-gated model
    # tier is enabled.  Its requested/automatic budget is restored after the
    # model window if no proof was accepted.
    requested_n5_secs = CONF["esc_n5_secs"]
    if CONF["llm"]:
        CONF["esc_n5_secs"] = 0.0
    elif timeout >= 2400 and CONF["esc_n5_secs"] <= 0:
        CONF["esc_n5_secs"] = min(1800.0, timeout * 0.5)

    judge_wall_max = [0.0]

    def judge(verdict, code):
        sys.stdout.write(json.dumps({"call": "judge", "verdict": verdict, "code": code}) + "\n")
        sys.stdout.flush()
        judge_started = time.time()
        resp = sys.stdin.readline()
        judge_wall_max[0] = max(judge_wall_max[0],
                                max(0.0, time.time() - judge_started))
        if not resp:
            return {"status": "proxy-eof"}
        try:
            return json.loads(resp)
        except Exception:
            return {"status": "unparsed-proxy-line"}

    cert = solve(law_a, law_b)
    verdict, code = _cert_to_answer(law_a, law_b, cert)
    rejected_codes = set()
    last_feedback = ""
    final_cert = cert
    if verdict is not None:
        r = judge(verdict, code)
        if r.get("status") == "accepted":
            return
        rejected_codes.add((verdict, code))
        last_feedback = _judge_feedback(r)
        if cert.get("carrier") == "infinite":
            fam = (cert.get("stats") or {}).get("family")
            if fam:
                INF_REJECTED.add(fam)
        sys.stderr.write("[solo] judge rejected first attempt: %s\n" % str(r)[:300])
    else:
        sys.stderr.write("[solo] no certificate: %s\n" % code)

    # If the first answer was an infinite candidate, do not rerun all finite and
    # TRUE tiers just to rediscover it.  Walk the remaining infinite portfolio,
    # blacklisting every judge rejection.  This converts the proxy into an
    # exact verifier rather than pretending a finite-window test is universal.
    if cert.get("carrier") == "infinite":
        for _ in range(7):
            # Preserve one complete LLM round plus the full configured judge
            # ceiling before launching the next heuristic model.  The observed
            # maximum is retained as a guard if the proxy ceiling is raised.
            judge_reserve = max(CONF["llm_round_min_secs"],
                                CONF["judge_call_max_secs"],
                                judge_wall_max[0])
            portfolio_cutoff = (
                llm_deadline - CONF["llm_round_min_secs"] - judge_reserve
                if CONF["llm"] else t0 + timeout * 0.82)
            if time.time() > portfolio_cutoff:
                break
            nxt, _why = find_infinite_countermodel(law_a, law_b)
            if nxt is None:
                break
            v, c = _cert_to_answer(law_a, law_b, nxt)
            if v is None or (v, c) in rejected_codes:
                fam = (nxt.get("stats") or {}).get("family")
                if fam:
                    INF_REJECTED.add(fam)
                continue
            rr = judge(v, c)
            if rr.get("status") == "accepted":
                return
            rejected_codes.add((v, c))
            last_feedback = _judge_feedback(rr)
            fam = (nxt.get("stats") or {}).get("family")
            if fam:
                INF_REJECTED.add(fam)
            sys.stderr.write("[solo] infinite candidate rejected: %s %s\n" %
                             (fam, str(rr)[:180]))
        # Every infinite candidate above is only a runtime-generated heuristic
        # until the Lean judge accepts it.  Reaching this line means none was
        # accepted, so it must not retain claim=FALSE and suppress the TRUE LLM
        # fallback.  Finite models are independently replayed and remain the
        # only rejected-cert shape that blocks proof authoring.
        final_cert = {
            "claim": "UNKNOWN",
            "method": "rejected-infinite-portfolio:" +
                      str(cert.get("method") or "infinite-model"),
            "stats": dict(cert.get("stats") or {}),
        }

    # Path B is a TRUE-proof author only.  A concrete deterministic FALSE
    # witness must not be contradicted by spending model calls on the opposite
    # verdict; UNKNOWN or a judge-rejected TRUE proof may escalate.  Every model
    # candidate is linted, deduplicated, and compiled by the same judge proxy.
    # Reserve 40% (at most 1800 s) for constructive FALSE / deep deterministic
    # work after the model attempts, rather than letting either tier starve the
    # other.
    if final_cert.get("claim") != "FALSE":
        if _llm_true_fallback(
                law_a, law_b, judge,
                deadline=llm_deadline,
                attempted_codes=rejected_codes,
                initial_feedback=last_feedback,
                search_note=str(final_cert.get("method") or "deterministic UNKNOWN")):
            return

    # One escalated re-solve if wall-clock remains.  Rejected infinite families
    # are now excluded, so this call cannot simply repeat the same bad witness.
    # Restore the n=5 budget only here, after Path B has had its bounded window.
    remaining = t0 + timeout - time.time()
    if remaining > 120.0:
        if timeout >= 2400:
            desired_n5 = (requested_n5_secs if requested_n5_secs > 0
                          else min(1800.0, timeout * 0.5))
            # Leave room for the raised BFS/KBC tiers that precede n=5 inside
            # solve(); the process-level Solo deadline remains the hard stop.
            CONF["esc_n5_secs"] = min(desired_n5,
                                       max(0.0, remaining - 360.0))
        else:
            CONF["esc_n5_secs"] = max(0.0, requested_n5_secs)
        CONF["esc_bfs_secs"] = max(CONF["esc_bfs_secs"], 120.0)
        CONF["esc_kbc_secs"] = max(CONF["esc_kbc_secs"], 180.0)
        cert2 = solve(law_a, law_b)
        final_cert = cert2
        verdict2, code2 = _cert_to_answer(law_a, law_b, cert2)
        if verdict2 is not None and (verdict2, code2) not in rejected_codes:
            rr = judge(verdict2, code2)
            if rr.get("status") == "accepted":
                return
            rejected_codes.add((verdict2, code2))
            last_feedback = _judge_feedback(rr)

    # Never resubmit a certificate that the deterministic judge already rejected.
    # A rejected answer is worth zero exactly like no answer, while avoiding it
    # keeps logs honest and leaves room for later runner-side handling.


def marathon_main(manifest_path):
    global SOLO_JUDGE_AVAILABLE
    SOLO_JUDGE_AVAILABLE = False
    out_path = os.environ.get("JUDGE_MARATHON_OUTPUT",
                              os.path.join(os.path.dirname(manifest_path) or ".", "answers.jsonl"))
    _preflight()
    problems = []
    with open(manifest_path) as f:
        for ln in f:
            ln = ln.strip()
            if ln:
                problems.append(json.loads(ln))
    n = len(problems)
    budget = float(os.environ.get("JUDGE_MARATHON_BUDGET_SECONDS", str(n * 300)))
    t0 = time.time()
    deadline = t0 + budget - 60.0
    CONF["self_check"] = False
    answered = set()

    def emit(pid, verdict, code):
        with open(out_path, "a") as f:
            f.write(json.dumps({"id": pid, "verdict": verdict, "code": code}) + "\n")
        answered.add(pid)

    # pass 1: standard tiers (cheap FALSE + normal TRUE), escalation off
    esc_saved = CONF["esc"]
    CONF["esc"] = False
    for p in problems:
        if time.time() > deadline:
            break
        try:
            a, b = _parse_official(p["equation1"]), _parse_official(p["equation2"])
            v, c = _cert_to_answer(a, b, solve(a, b))
            if v is not None:
                emit(p["id"], v, c)
        except Exception as e:
            sys.stderr.write("[marathon] %s pass1 error: %r\n" % (p.get("id"), e))
    # pass 2: escalation on the residue while budget remains
    CONF["esc"] = esc_saved
    residue = [p for p in problems if p["id"] not in answered]
    for i, p in enumerate(residue):
        rem = deadline - time.time()
        if rem <= 0:
            break
        CONF["esc_n5_secs"] = max(0.0, min(1800.0, rem / max(1, len(residue) - i) - 200.0))
        try:
            a, b = _parse_official(p["equation1"]), _parse_official(p["equation2"])
            v, c = _cert_to_answer(a, b, solve(a, b))
            if v is not None:
                emit(p["id"], v, c)
        except Exception as e:
            sys.stderr.write("[marathon] %s pass2 error: %r\n" % (p.get("id"), e))
    sys.stderr.write("[marathon] answered %d/%d in %.0fs\n"
                     % (len(answered), n, time.time() - t0))


if __name__ == "__main__":
    manifest = os.environ.get("JUDGE_MARATHON_MANIFEST")
    if manifest:
        marathon_main(manifest)
    else:
        solo_main()
