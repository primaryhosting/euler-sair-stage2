# EULER — Workflow Diagrams

Two views of the system. The first is what happens **at runtime, per
problem, inside the sandbox**. The second is the **dev-time ecosystem** —
where the external systems (Axiom's Axle, Harmonic's Aristotle, the ATPs)
sit, what each contributed, and the invariant that nothing enters the solver
without independent re-verification. Interactive versions of both live on
the Riemann Labs page (`/euler`).

---

## 1. Runtime: one problem through the solver

Everything left of the judge is EULER; the judge is the competition's.
Every path ends at an independent check — there is no unverified exit.

```mermaid
flowchart TD
    P([Problem: E1 ⇒ E2?]) --> O{Direction oracle\nETP closure, 4694²\n600/600 vs ground truth}

    O -- FALSE --> B[Hypothesis-keyed bank\n305 finite magmas]
    B -- miss --> CSP[Stdlib finite-model search\norders 4–8, symmetry-broken]
    B -- hit --> FC
    CSP --> FC[Full finite self-check\nE1 holds ∀σ · E2 fails ∃τ]
    FC --> FCERT[Emit: Fin n table + decideFin!]

    O -- TRUE --> HC[Certificate table\n26 manual · 390 Aristotle · 18 ATP/loop]
    HC -- miss --> CH[Matching-chain prover\nself-rechecked calc]
    CH -- miss --> KB[Knuth–Bendix completion\nTOTAL emission: valid-if-emitted]
    KB -- miss --> TR[Transitivity\n2-hop, then bounded 3-hop]
    TR -- miss --> LLM[LLM fallback\nproxy models, last tier]
    HC --> TCERT[Emit: Lean proof body]
    CH --> TCERT
    KB --> TCERT
    TR --> TCERT
    LLM --> TCERT

    O -- unknown / order-5 --> U[12 s CE probe → completion\n± duality → full cascade]
    U --> FC
    U --> TCERT

    FCERT --> J{{SAIR deterministic judge\nLean v4.32.2 — final authority}}
    TCERT --> J
    J -- accepted --> DONE([Answer finalized])
    J -- rejected --> CH

    style J fill:#1a1a2e,stroke:#e0b341,color:#fff
    style DONE fill:#14532d,color:#fff
```

**Reading it:** the oracle is exact on order-4, so almost every problem takes
one clean branch. The dashed reality behind "miss → next tier" is
cheapest-first: table lookups in microseconds, search in seconds, the LLM
only if everything deterministic has failed — and even then, only the judge's
`accepted` finalizes.

---

## 2. Dev-time: the ecosystem that built the certificates

Nothing on the left is called at runtime. Only re-verified *outputs* are
embedded, and the judge re-checks every one again at answer time.

```mermaid
flowchart LR
    subgraph PUBLIC["Public data (Tao et al., ETP)"]
        OUT[outcomes.json\nimplication closure]
        EQT[equations.txt\n4694 laws]
        EDGES[10,657 explicit\nproof edges]
    end

    subgraph SYSTEMS["External systems (dev-time only)"]
        ARI["Aristotle — Harmonic\nLean theorem prover\n→ 390 hard TRUE proofs"]
        VAMP["Vampire — Kovács & Voronkov\nrefutations → Krympa-style\nchain reconstruction"]
        EPR["E — Schulz\nsuperposition traces →\nshared-DAG Lean replay"]
        MACE["Mace4 — McCune\nfinite-model harvest\n→ table bank seeds"]
    end

    subgraph GATE["Verification gate"]
        AXLE["AXLE — Axiom (Carina Hong's team)\ncloud Lean compile-check on the judge's\nexact toolchain (v4.32.2)\nEVERY certificate passed through here.\nBoth fidelity failures were caught here."]
        PYCHK["Python full finite checks\n(decideFin! semantics)"]
    end

    subgraph SOLVER["Embedded in solver.py (disclosed)"]
        MB[_MATRIX_BLOB direction]
        AB[_AB — 390 Aristotle proofs]
        LB[_LB — 8 loop certificates]
        O5[_O5B — 10 order-5 replays]
        TB[_TABLE_BANK — 305 magmas]
    end

    OUT --> MB
    EQT --> MB
    EDGES -->|licenses transitivity| SOLVER
    ARI --> AXLE --> AB
    VAMP --> AXLE --> LB
    EPR --> AXLE --> O5
    MACE --> PYCHK --> TB
    SOLVER --> JUDGE{{SAIR judge re-verifies\nevery answer at runtime}}

    style AXLE fill:#312e81,color:#fff,stroke:#818cf8
    style ARI fill:#7c2d12,color:#fff
    style JUDGE fill:#1a1a2e,stroke:#e0b341,color:#fff
```

**The invariant this diagram encodes:** external provers *propose*; the
verification gate *disposes*; the competition judge disposes **again**. An
Aristotle proof, a Vampire reconstruction, and a hand-written lemma all
enter the solver through exactly the same door — a judge-exact compile
check — and exit through exactly the same door at answer time. Trust is
never transferred; it is re-established at every boundary.

---

## Acknowledgment of the systems named here

- **Axle — Axiom (Carina Hong and the Axiom Math team).** The dev-time
  verification backbone of this project: judge-exact Lean compile checks in
  ~2 seconds instead of a ~40-minute playground round trip. Every
  certificate in this pack passed through Axle before it was embedded, and
  both statement-fidelity failures on our record were *discovered* as Axle
  divergences. The measurement discipline this pack is built on would have
  been impractical without it.
- **Aristotle — Harmonic.** Proved 390 of the solver's hard TRUE
  implications during earlier development campaigns; those kernel-checked
  bodies are embedded and disclosed as the Layer-1 certificate table
  (`_AB`), and the judge re-verifies each at answer time.
- Vampire (Kovács & Voronkov), E (Schulz), Mace4 (McCune): the classical
  ATP/model-finding stack whose outputs the reconstruction pipeline replays
  into human-checkable Lean.
