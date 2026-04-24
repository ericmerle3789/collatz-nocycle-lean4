---
section: "9"
owner: worker
status: skeleton-plus-session-c-paragraphs
contributions:
  - "§9.6 paragraph drafted by Session C Mathlib-Prover, Track C Day 1 Tao persona analysis (mailbox from_mathlib_prover/0023, 2026-04-24T22:00Z), integrated verbatim by Worker per Session B authorization 0067 §6.3."
  - "§9.7 paragraph drafted by Session C Mathlib-Prover, Phase IX Part A synthesis §9.3 (mailbox from_mathlib_prover/0042, 2026-04-25T~03:00Z), integrated verbatim by Worker per Session B authorization 0078 §6.3 + 0080 §3.1."
last_updated: 2026-04-24
---

# 9. Open problems

*[WIP — skeleton prose for §9.1-§9.5 pending Day-3 polish ; §9.6 Tao and §9.7 structural-excess (Ψ_s) paragraphs are Session C direct-verified and integrated verbatim per Session B authorization.]*

## Planned structure

### 9.1 Removing `ProductBoundThreshold`
The central open question raised by this paper : can `ProductBoundThreshold` be promoted to a theorem? §5 Obstruction I answers *not within any product-bound approach*. The question is therefore : what non-product-bound technique might close the `k > 1322` case?

### 9.2 The `k ≥ q_{14}` tail
Current-generation Barina reaches `n < 2^{71}`, which via CF windows `W_8, ..., W_{13}` covers `k < q_{14} ≈ 10{,}590{,}737`. A `W_{14}` extension would require arithmetic gap constants at denominator `q_{14}` with `~10^5` digits — outside native_decide's reach at present hardware.

### 9.3 Formalisation challenges
- R-M3.H12 bridge `(Real.convergent v n).den : ℝ = (GenContFract.of v).dens n` is not direct in Mathlib v4.27.0. Phase62 works around it via parametric real-valued form; a proper bridge would strengthen Phase61/62 integration.
- Phase63 Sections 2-11 as Lean theorems would require the breakthrough discussed in §9.1 + the bridge in §9.3.

### 9.4 Relation to divergence
This paper does not address the divergence half of Collatz. The techniques (Baker's theorem + CF theory + formal verification) are in principle adaptable, but the structure is different. Explicit scope disclosure.

### 9.5 Checkpoints for speculative tracks (Track B pointer)
Session C Track B continues 6-12 weeks with Day 14 kill-switch on transcendence-theoretic approaches (Santana 2026 rigour-closure, Knight 2025 extension, transcendence-gap sharpenings). Results, if any, would feed paper v3.

### 9.6 Probabilistic techniques (Tao)

*[Paragraph drafted by Session C Track C Day 1 Tao persona analysis (mailbox 0023 §5.2), integrated verbatim per Session B authorization 0067 §6.3.]*

Tao's probabilistic approach (2019, *Forum of Mathematics, Pi*) proves that almost all Collatz orbits attain almost bounded values under logarithmic density. This result is **probabilistic** and does not extend to deterministic statements about hypothetical cycles (which have density zero). Tao's broader toolkit (entropy compression à la Moser-Tardos [blog 2009], higher-order Fourier analysis à la Green-Tao-Ziegler) has not been successfully applied to deterministic Collatz cycle bounds; such applications would require substantial new theoretical work. We therefore do not integrate probabilistic techniques into our proof of Theorem 3.1 (which remains conditional on the structural hypotheses §4).

### 9.7 Structural-excess framework Ψ_s (Phase VIII extension)

*[Paragraph drafted by Session C Mathlib-Prover, Phase IX Part A synthesis §9.3 (mailbox from_mathlib_prover/0042), integrated verbatim per Session B authorization 0078 §6.3 + 0080 §3.1. See §8.5 for the formalization status and the separate branch `phase8-psi-s-lean`.]*

We formalize in Lean 4 a custom Φ_s / Ψ_s structural-excess framework (Mathlib v4.27.0 lacks Gowers norms). Machine-verified : the trivial Collatz cycle has Ψ_2 = 32/81, establishing a factor-33× structural excess over its mean prediction (1/81). The T4c conjecture is encoded as parametric `def T4c_Conjecture_Psi2`, and the contradiction schema `psi2_bounds_no_cycle` records the logical shape of the intended attack. See `ProjetCollatz.PhaseVIII.StructuralExcess` in the repository branch `phase8-psi-s-lean` (§8.5).

## Style notes (Worker internal — remove before publication)

- §9.1-§9.5 remain at skeleton prose ; Day-3 polish will elevate phrasing and add missing citations (Hercher 2023 Corollary 29 for §9.5, Tao 2019 arXiv id for §9.6, Session C Phase IX commit hashes for §9.7 if reviewer requests).
- §9.6 and §9.7 are Session C direct-verified integrations ; do not alter without re-coordination.
- "Day 3" deliverables checklist removed (internal ; superseded by the RT#1 cycle before Commit).
- §9.2 numerical claim "~10^5 digits" deferred to §5/§7 Session C import (where window-size arithmetic is authoritative).

## RT#1 checklist (to apply Day 3 polish pass)

- [ ] Every open problem traceable to a §5 / §6 / §7 obstruction.
- [ ] R-M3.H12 bridge named explicitly and linked to `docs/BIBLE/RISK_REGISTER.md`.
- [ ] Scope (cycle-only) re-stated in §9.4.
- [ ] §9.2 numerical claim ("~10^5 digits") cross-verified with §5.2 / §7 Session C values post-import.
- [ ] §9.5 Hercher corollary reference made concrete (Corollary 29 in Hercher 2023 JIS 26 article 23.6.5).
- [ ] §9.7 attribution chain preserved (Session C 0042 §9.3 → Session B 0078/0080 → Worker).
