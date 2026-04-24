---
section: "1"
owner: worker
status: skeleton
last_updated: 2026-04-24
---

# 1. Introduction

*[WIP — Day 1 draft pending mathnotes 0018 integral reading.]*

## Planned structure (per Session B 0064 §3.2 + 0066 §7)

### 1.1 The Collatz conjecture and the cycle problem
- Definition of the Collatz map `T(n) = n/2` if `n` even, `(3n+1)/2` if `n` odd.
- The two open questions : no divergence, no non-trivial cycle.
- Scope of this paper : the cycle problem, conditional on three structural hypotheses.

### 1.2 Why v2, why now — pivot rationale
- Paper v1 (draft, tag `paper-v1-draft`) presented a 2-hypothesis conditional proof (BakerSeparation, BarinaVerification).
- Exploration (Session C, 2026-04-24) of 11 research branches demonstrated that every product-bound approach is structurally limited to `k ≲ 10^10` (see §5 Obstruction I, δ8).
- This forced an honest third hypothesis `ProductBoundThreshold`, and a paper v2 that documents both the proof and the obstruction.
- Explicit documentation of the obstruction is, in itself, a scientific contribution.

### 1.3 Contributions
Brief enumeration of five originals :
- **δ7** : alternative framing via a disjunction on the cycle denominator (§7).
- **δ8** : Product-Bound Impossibility Lemma — no product-bound argument alone can exceed `k ≲ 10^10` (§5).
- **δ8'** : extension of δ8 to the generalised bound families (§5).
- **δ9** : state-of-the-art mapping 1977-2026 with structural typology (§6).
- **6α** : formal Lean 4 formalization of the Phase58 conditional theorem plus continued-fraction infrastructure (Phase60/61/62) (§8).

### 1.4 Relation to the 2026 literature
- Santana 2026 (arXiv:2601.03297) : rigour gap identified — see §6 Obstruction II.
- Knight 2025 (Discrete Math. 349(3)) : restricted class elimination (parity vector = upper Christoffel word), does not extend to general cycles. See §6.
- Dhiman-Pandey 2026 (arXiv:2601.12772) : complementary framework — see §6.
- Rozier-Terracol 2026 (arXiv:2502.00948) : paradoxical sequences, uses Rhin heuristically — see §6.4.

### 1.5 Paper organisation
One paragraph mapping the 11 sections.

## Style notes

- Academic English, Journal of Integer Sequences / Acta Arithmetica register.
- Concise. Citable. No hype.
- Each claim backed by a cross-reference to the section, a theorem in the Lean repo, or a direct-verified citation.
- No fabricated citations (policy mailbox 0065).

## RT#1 checklist (to apply post-draft)

- [ ] Every claim has a citation or a forward cross-reference.
- [ ] No `[INDIRECT]` tag outside of §6.2 Knight formulation.
- [ ] Abstract-ready : is §1.1-§1.3 one-paragraphable?
- [ ] Honest framing : `ProductBoundThreshold` introduced *before* the word "proof".
- [ ] Scope disclosure : cycle-only (we do not address divergence).

## Blocked on

- Reading `mailbox/from_mathlib_prover/0018-MATHNOTES-PACKAGE-...` integrally for Session C's δ7/δ8/δ8'/δ9/6α precise formulations.
- Reading mathnotes `docs/BIBLE/mathnotes/` directory mirror.
