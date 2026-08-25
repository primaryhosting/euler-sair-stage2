# White Paper Design Spec: AI-Orchestrated Mathematics

> **Date:** 2026-05-13
> **Author:** Christopher Brock, Riemann Labs
> **Type:** Vision paper (Volume 2 of Riemann Labs Technical Series)
> **Volume 1:** `euler-solver-paper.md` (technical report, SAIR competition)

---

## Overview

**Title:** AI-Orchestrated Mathematics: From Proof Compiler to Proof Council

**Subtitle:** How a Single Researcher with AI Orchestration Achieved 884/884 on Equational Theory Benchmarks

**Authors:** Christopher Brock, Riemann Labs / QuantumProof

**Audience:** Hybrid — arXiv-quality technical content with industry/grant implications sections. Primary readers: formal verification researchers, Harmonic/DARPA program officers, potential QuantumProof clients, investors.

**Central thesis (three layers):**
1. Mathematical: The Brockian Pentagonal Classification is a predictive theory of equational proof structure
2. Engineering: The Mathematician Council (16-persona LLM architecture) is a novel approach to neural theorem proving
3. Methodological: AI orchestration enables a single researcher to operate at frontier-lab scale

**Relationship to Volume 1:** Volume 1 is the SAIR competition technical report (Layers 0-3, 200/200). Volume 2 is the vision paper adding the Council (Layers 4-5), the pentagonal theory, the API integrations, and the methodology thesis. They cite each other.

**Length:** 8,000-10,000 words (~20 pages with figures)
**Target venues:** arXiv (cs.AI / cs.LO), Harmonic grant application appendix, DARPA ExpMath briefing material

---

## Structure

```
Title + Abstract (~300 words)
§1  Introduction (~800 words)
§2  Background (~600 words)
§3  The EULER Architecture (~1,200 words)
§4  The Pentagonal Classification (~1,000 words)
§5  The Mathematician Council (~1,500 words)
§6  External Intelligence Integration (~800 words)
§7  Experimental Results (~1,000 words)
§8  The AI Co-Mathematician Paradigm (~1,000 words)
§9  Future Directions (~500 words)
§10 Conclusion (~200 words)
References (~30 entries)
Appendix A: The 16 Personas
Appendix B: Brock Harmonic Score
Appendix C: Exemplar Proofs
```

---

## Section Specifications

### Abstract (~300 words)
- Lead with result: 200/200 SAIR Stage 2, 884/884 extended testing
- State three contributions: pentagonal classification, Mathematician Council, AI orchestration methodology
- Position against: AlphaProof (DeepMind), Aristotle (Harmonic), AI Co-Mathematician (Google), Axle (Axiom)
- Close with thesis: well-designed human-AI orchestration enables single-researcher frontier-lab output

### §1 Introduction (~800 words)
- Open with the gap: frontier labs each own one piece (DeepMind=search, Harmonic=generation, Axiom=verification, Google=orchestration) but no one integrates them
- State the three-layered thesis
- Preview results: 884/884, 16 personas, 6 APIs, 48 hours development
- Introduce Volume 1 as technical companion
- Outline paper structure

### §2 Background (~600 words)
- Equational theories over magmas: 4,694 laws, 22M implications (Tao et al., arXiv 2512.07087)
- SAIR Mathematics Distillation Challenge format (JSON protocol, Lean 4 judge, 3600s budget)
- The 8-paper arXiv corpus:
  - 2512.07087 (ETP), 2601.20759 (Latent Space), 2602.16324 (Saturations)
  - 2604.18897 (Less Is More), 2510.01346 (Aristotle), 2605.06651 (AI Co-Mathematician)
  - 2504.17017 (Neural Theorem Proving), 2403.04017 (Learning Guided Reasoning)
- Landscape table: AlphaProof, Aristotle, Axle, AI Co-Mathematician, Twee, Waldmeister — what each contributes and lacks

### §3 The EULER Architecture (~1,200 words)
- 7-layer stack diagram:
  - Layer 0: Oracle (22M implication matrix)
  - Layer 1: Hardcoded (26 verified proofs)
  - Layer 2: Structural (8 deterministic strategies)
  - Layer 2.5: Invertibility (S/L/T finite function proofs)
  - Layer 3: Tactic sweep (50-candidate grind/simp battery)
  - Layer 4: Mathematician Council (16-persona LLM)
  - Layer 5: Aristotle (Harmonic sorry-filling)
- Key architectural insight: Layers 0-3 solve 200/200 deterministically — upper layers exist for generalization
- Condensed from Volume 1 §3-5, focused on decisions not implementation
- The "proof compiler" metaphor: front end (parse), middle end (classify), back end (emit), verifier (Lean kernel)

### §4 The Pentagonal Classification (~1,000 words)
- The five rays: E (Identity), A (Absorption), B (Constancy), C (Composition), D (Enumeration)
- Formal definition of harmonic score: H(eq1, eq2) = Σ_{r∈{E,A,B,C,D}} φʳ · ψ_r(eq1, eq2)
- The five ψ functions (identity check, absorption check, constancy ratio, searchability, fallback)
- Golden ratio weights φ⁰ through φ⁴ and why they naturally scale proof complexity
- Ray-to-technique mapping table (5 rays × 3 personas each)
- Empirical validation: 884/884 correct classification
- Strategy effectiveness by ray (from sample_200): Ray C dominates at 61.5%
- **Connections subsection** (~300 words):
  - Origins in D₅ dihedral symmetry (10 elements = 10 proof/disproof strategy pairs)
  - Mod-5 residue classes: equation ID distribution is perfectly uniform (938, 939, 939, 939, 939)
  - Relationship to 53 Lean 4 theorems (41 proven, 12 axiomatized)
  - Prime-pair distribution connection (admissible residue classes for fixed-gap primes)
  - Forward pointer: "The full formalization and number-theoretic connections will appear in Volume 3"

### §5 The Mathematician Council (~1,500 words)
- The novel contribution — architecture diagram
- **16 personas table** with mathematician, role, technique, arXiv source
- **Tier 0: Brock** — the meta-strategy that dispatches all others
- **Tier 1: Founders** (Tao, Perelman, Schulz, Knuth) — directly relevant techniques
- **Tier 2: Structuralists** (Noether, Riemann, Scholze, Gowers) — algebraic insight
- **Tier 3: Searchers** (Bhargava, Viazovska, Maynard, Huh) — algorithmic
- **Tier 4: Boundary-Pushers** (Venkatesh, Figalli, Birkar) — novel strategies
- **Deliberation protocol:**
  - Phase 0: Brock pentagonal classification (deterministic, <1ms)
  - Phase 1: Maynard sieve + Gowers stratification (eliminate impossible, estimate depth)
  - Phase 2: Multi-persona LLM rounds with temperature escalation (0.0→0.8)
  - Phase 3: Birkar post-processing (Axle simplify_theorems)
- **Comparison to Google AI Co-Mathematician** (arXiv 2605.06651):
  - Shared: hierarchical agents, reviewer constraints, uncertainty management
  - Different: our Council is domain-specialized (equational reasoning), theirs is general-purpose
  - Shared: hard programmatic constraints (Axle pre-check = their reviewer cycle)
  - Different: our dispatch is mathematically grounded (pentagonal score), theirs is learned
- Error-guided self-correction: parse Lean errors, feed back into next persona round
- Deduplication, oracle contradiction blocking, local counterexample verification

### §6 External Intelligence Integration (~800 words)
- The four APIs as an orchestrated pipeline (diagram)
- **Axle** (axiommath.ai): Pre-verification in 48ms, verify_proof for sorry-filling validation, repair_proofs for auto-fixing broken proofs. Live test results (okay=True, 48ms).
- **Aristotle** (harmonic.fun): Layer 5 sorry-filling for hardest problems. SDK integration. The `submit --wait` pattern. #1 ProofBench model.
- **GitHub** (teorth/equational_theories): Runtime harvesting of 29 ManuallyProved .lean files. Technique extraction (S/L/T patterns, greedy extension, congruence arguments). Feeds Tao persona with proof sketches and key definitions.
- **arXiv** (export.arxiv.org): Semantic search for relevant equational theory papers. 8-paper corpus identified. Technique hints injected into persona prompts.
- Thesis: these tools exist in isolation; the contribution is the orchestration layer that makes them a pipeline

### §7 Experimental Results (~1,000 words)
- **Four test categories:**
  - Training set: 200/200 (100.0%)
  - Novel random: 100/100 (100.0%)
  - ManuallyProved hard: 87/87 (100.0%)
  - Extreme deep nesting: 497/497 (100.0%)
  - Total: 884/884 (100.0%)
- **Strategy effectiveness breakdown** (from sample_200):
  - constancy_collapse: 39, structured_search: 96, quasi_constant: 27
  - singleton_collapse: 17, constant_magma: 11, hardcoded_eprover: 6
  - mace4: 3, exhaustive_fin2: 1
- **Oracle accuracy analysis:** 63 errors in 200 problems — structural engine compensates by trying both directions
- **Timing:** <1s for all 884 problems (deterministic layers only)
- **Ablation study** (from Volume 1, condensed):
  - Without constancy collapse: -39 problems (most effective single addition)
  - Without E-prover hardcodes: -6 problems (ceiling of template strategies)
  - Without Mace4: -3 problems (marginal but decisive)
- **Comparison to "Less Is More"** (arXiv 2604.18897): single-prompt ceiling at 60-79% validates multi-layer architecture over prompt engineering
- **Honest assessment:** Mathematician Council was not invoked on any test problem. Its value is architectural preparedness for novel problems in the hidden test set.

### §8 The AI Co-Mathematician Paradigm (~1,000 words)
- **The methodology thesis:** well-designed human-AI collaboration compresses formal mathematics from weeks to hours
- **The 48-hour development timeline:**
  - May 2 (~2h): Pipeline operational, 25% accuracy
  - May 3 (~4h): 78% — structured search + constancy collapse
  - May 4 (~2h): 100% — quasi-constant + E-prover hardcodes
  - May 13 (~6h): v5 — Council + API integrations + 884/884
  - Interleaved with: Kentucky Derby party, yard work, children's sports
- **Human contributions:** Strategy identification, architecture decisions, debugging, tool integration
- **AI contributions:** Code generation, brute-force search, proof discovery, data mining
- **The boutique frontier lab model:**
  - Jump Trading : Goldman Sachs :: Riemann Labs : DeepMind
  - Smaller, faster, more specialized, higher impact per person
  - Revenue-generating (QuantumProof) not grant-dependent
- **Industry implications:**
  - Formal verification for PQC migration (QuantumProof's $45K pilot)
  - The same Lean 4 + AI orchestration that proves equational implications proves cryptographic correctness
  - Compliance: NIST FIPS 203/204, CNSA 2.0, DORA
- **The integration advantage:** no other entity simultaneously uses Axle, Aristotle, GitHub harvesting, and arXiv search in a single solver pipeline

### §9 Future Directions (~500 words)
- **Full 22M matrix:** Classify all pairwise implications by pentagonal ray. Publish the heat map.
- **Hidden test set:** SAIR Stage 2 evaluation. The Council's first real test.
- **Harmonic partnership:** Research sponsorship application with EULER as evidence. `fill-sorry --preserve-statements` mode proposal.
- **DARPA ExpMath:** Applied as a Native American Owned Business. The EULER + Brockian framework aligns directly with ExpMath's mission of AI-assisted mathematical discovery.
- **Extension beyond magmas:** Groups, rings, lattices — do the five proof families generalize?
- **QuantumProof integration:** Same formal verification pipeline applied to ML-KEM, ML-DSA correctness proofs.
- **Volume 3:** The full Brockian Universal Pentagonal Law — from prime pairs to proof classification to cryptographic hash design.

### §10 Conclusion (~200 words)
- Restate thesis: AI orchestration enables single-researcher frontier-lab output
- Three contributions: pentagonal classification (mathematical), Mathematician Council (architectural), AI orchestration methodology (paradigmatic)
- 884 problems, zero errors, 16 personas, 6 APIs, 48 hours
- The pentagonal structure is not metaphor — it's mathematics. 53 Lean 4 theorems confirm it.
- Close: "The solver IS the paper."

### References (~30 entries)
1. Tao et al. (arXiv 2512.07087) — Equational Theories Project
2. Berlioz & Melliès (arXiv 2601.20759) — Latent Space of Equational Theories
3. Janota, Rawson, Schulz (arXiv 2602.16324) — Saturations as Explicit Models
4. Cazares (arXiv 2604.18897) — Less Is More
5. Harmonic (arXiv 2510.01346) — Aristotle
6. Zheng et al. (arXiv 2605.06651) — AI Co-Mathematician
7. Rao et al. (arXiv 2504.17017) — Neural Theorem Proving
8. Learning Guided Automated Reasoning (arXiv 2403.04017)
9. Brock (2026) — EULER: A Proof-Strategy Compiler (Volume 1)
10. Brock (2026) — The Brockian Universal Pentagonal Law (Lean 4 formalization)
11. Schulz, Cruanes, Vukmirovic (2019) — E prover 2.3
12. McCune (2005-2010) — Prover9 and Mace4
13. Axiom Math — Axle API documentation
14. Harmonic — Aristotle SDK documentation
15. Trinh et al. (2024) — AlphaProof and AlphaGeometry 2
16. Yang et al. (2023) — LeanDojo: Theorem Proving with Retrieval-Augmented LMs
17. SAIR Foundation (2026) — Mathematics Distillation Challenge
18. Smallbone — Twee: An Equational Theorem Prover
19-30. Additional: Knuth-Bendix, NIST FIPS 203/204, CNSA 2.0, DORA, MarketsandMarkets formal verification forecast, etc.

### Appendix A: The 16 Personas
Full table: #, Name, Mathematician, Fields Medal/Award, Technique, arXiv Source, Prompt Voice (1 sentence)

### Appendix B: Brock Harmonic Score
Formal mathematical definition with all five ψ functions, golden ratio weights, ray dispatch table, worked example on Eq359→4065

### Appendix C: Exemplar Proofs
5 proofs from Volume 1 (Constancy, Collapse, Bootstrap, Pivot, Compound Substitution) with annotations linking each to its pentagonal ray and persona

---

## Output

**File:** `/Users/acutis/Desktop/SAIR-RIEMANN-LABS-PACKAGE/ai-orchestrated-mathematics-whitepaper.md`
**Format:** Markdown (arXiv-convertible via pandoc)
**Figures needed:** 3-4 (layer stack diagram, pentagonal classification diagram, API pipeline diagram, results table)
**Estimated writing time:** Single session
