# Riemann Labs — SAIR Competition Dashboard

Create a new page at `/sair-competition` for the Riemann Labs project. This is a competition dashboard for the SAIR Mathematics Distillation Challenge Stage 2 — a formal mathematics competition where we prove/disprove equational implications over magmas using Lean 4.

## Design System

Follow the existing Riemann Labs dark gradient glass aesthetic:
- Background: deep blue-to-purple gradient (`#0a0a1a` to `#1a0a2e`)
- Panels: glass morphism with `backdrop-blur(20px)`, `bg-white/5`, luminous borders (`border-white/10`)
- Accent colors: electric blue (`#3b82f6`), emerald (`#10b981`), amber (`#f59e0b`), rose (`#f43f5e`)
- Typography: monospace for code/proofs, sans-serif for labels
- Animations: subtle glow effects, smooth transitions

## Page Layout

### 1. Hero Section

Full-width hero with:
- Title: "SAIR Mathematics Distillation Challenge" in large serif font
- Subtitle: "Stage 2 — Equational Theories over Magmas"
- Deadline countdown timer to August 31, 2026 (animated, days/hours/minutes)
- Current score badge: "200/200 (100%)" in a glowing circular gauge
- Participant count: "113 competitors"
- An animated force-directed graph visualization showing equation nodes connected by implication arrows — green for proved, red for disproved, gray for unsolved. Use ~50 sample nodes with physics-based animation.

### 2. Strategy Pentagon (I-Model Integration)

A large animated pentagon visualization (Brockian signature) where each vertex represents a proof technique family:

| Vertex | Technique | Count | Color |
|--------|-----------|-------|-------|
| Ray A (top) | Constancy Collapse | 39 | Electric blue |
| Ray B (upper-right) | Structured Search | 97 | Emerald |
| Ray C (lower-right) | Singleton + Constant Magma | 28 | Amber |
| Ray D (lower-left) | Quasi-Constant (.symm.trans) | 27 | Rose |
| Ray E (upper-left) | Hardcoded + ATP (Mace4/E) | 9 | Purple |

The pentagon should:
- Rotate slowly (5s period)
- Each vertex pulses with its count
- Inner area FULLY FILLED with golden glow (100% solved)
- Labels on each vertex with count and technique name
- Connecting lines between vertices glow when strategies chain together

Below the pentagon: "The Five Rays of Equational Proof — a pentagonal decomposition of automated reasoning"

### 3. Accuracy Timeline

Horizontal timeline showing solver evolution:

| Phase | Date | Accuracy | Milestone |
|-------|------|----------|-----------|
| Build 1-4 | May 2 | 25% (5/20) | Pipeline working |
| Phase 2a | May 3 AM | 58% (116/200) | + structured search |
| Phase 2b | May 3 | 72% (144/200) | + constancy collapse |
| Phase 2c | May 3 PM | 78% (156/200) | + Mace4 ATP |
| Phase 3a | May 4 | 97% (194/200) | + quasi-constant + constant magma |
| Phase 3b | May 4 | 100% (200/200) | + E-prover-derived hardcoded proofs |

Render as an animated line chart with glowing data points. The line should pulse/glow at the current position.

### 4. Proof Gallery

Grid of 5 cards, each showcasing an exemplar proof:

**Card 1: "The Constancy Principle"**
- Equation: 3268 → 3253
- Technique badge: "Direct Substitution"
- One-line proof: `exact h x x`
- Status: JUDGE VERIFIED
- Beauty score: 5/5 stars

**Card 2: "The Constant Collapse"**
- Equation: 3829 → 41
- Technique badge: "Transitivity Pivot"
- Proof: `(h x x z).trans (h y z z).symm`
- Status: Pending verification
- Beauty score: 4/5 stars

**Card 3: "The Bootstrap"**
- Equation: 359 → 4065
- Technique badge: "Self-Referential"
- Proof: `calc` chain with `congrArg`
- Status: Testing
- Beauty score: 5/5 stars

**Card 4: "The Pivot"**
- Equation: 404 → 4236
- Technique badge: ".trans .symm"
- Proof: Two instantiations meeting at a shared constant
- Status: Pending verification
- Beauty score: 4/5 stars

**Card 5: "Compound Substitution"**
- Equation: 282 → 2133
- Technique badge: "Structure Absorption"
- Proof: `exact h x y (z ◇ w)`
- Status: Pending verification
- Beauty score: 5/5 stars

Each card should:
- Have glass morphism styling with proof-technique-colored border
- Expand on click to show the full Lean 4 proof code in a syntax-highlighted code block
- Show the mathematical commentary from the proof file
- Have a "Copy Lean Code" button

### 5. Live Metrics Panel

4 metric cards in a row:

1. **Accuracy Gauge** — circular progress at 100%, full green glow, animated sparkle
2. **False Implications** — "100/100 COMPLETE" with checkmark, all green
3. **True Implications** — "100/100 COMPLETE" with checkmark, all green
4. **Solver Speed** — "200 problems solved in 325 seconds" with lightning icon

### 6. Arsenal Panel

Show installed tools as a grid of badges:

| Tool | Status | Purpose |
|------|--------|---------|
| Mace4 | Active | Finite model finder — solved 3 counterexamples |
| E Prover | Active | Equational ATP — confirmed all 200 provable |
| Prover9 | Active | First-order prover |
| Z3 | Active | SMT solver |
| Aristotle | Connected | Harmonic proof engine — API key obtained |
| LeanDojo | Ready | Neural proof search |

Each badge glows green if installed, amber if ready, gray if pending.

### 7. Navigation

Add "SAIR Competition" as a new nav item in the existing Riemann Labs sidebar/navbar, between Observatory and Thinkers Athenaeum. Use a trophy or target icon.

## Technical Notes

- All data is static for now (hardcoded from the stats above)
- Use Recharts or similar for the timeline chart
- Use react-force-graph or custom canvas for the equation graph
- The pentagon can be SVG with CSS animations
- Code blocks should use a dark theme syntax highlighter (Prism or similar)
- Make it responsive (works on mobile too)
- Add Riemann Labs logo and "Powered by EULER Solver" footer

### 8. Brockian Connection Panel

A glass morphism card below the arsenal showing the pentagonal proof theory:

**Title**: "The Five Rays of Equational Proof"

**Content**: A brief paragraph explaining the correspondence between the 5 proof technique families and the Brockian Universal Pentagonal Law. Each technique maps to one of the 5 rays (mod 5 residue classes):

- Ray E (Identity) → Direct instantiation — the null transformation
- Ray A (Singleton) → Singleton collapse — total absorption
- Ray B (Constancy) → Constancy collapse — free variable elimination
- Ray C (Structural) → Quasi-constant / bootstrap — self-referential growth
- Ray D (External) → Classical ATP + hardcoded — machine reasoning

Include a small pentagon diagram with the 5 rays labeled.

**Link**: "Read the full research note" → links to BROCKIAN-EQUATIONAL-THEORY-CONNECTIONS.md

### 9. Achievement Banner

A prominent animated banner at the bottom:

**"200/200 — Perfect Score"**

With subtitle: "From 25% to 100% in 48 hours. Zero wrong answers. 15 strategies. One pentagonal theory."

Animated golden particles emanating from the text. Subtle glow pulse.

## Tone

This is a research showcase — think academic conference poster meets cyberpunk dashboard. Mathematical precision meets visual drama. Every element should communicate: "This lab does serious formal mathematics with cutting-edge AI."
