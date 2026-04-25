import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import ProjetCollatz.Phase60IrrationalityLog23
import ProjetCollatz.Phase61CFConvergents

/-!
# Phase 62 — Best-Approximation Bridge for log₂ 3

## Context

This file provides the continued-fraction best-approximation bridge for
`Real.logb 2 3`, foundational infrastructure for the Phase63
`DerivedLargeKBoundTheorem` (replacement of the `DerivedLargeKBound`
structure-as-hypothesis of Phase59). It builds on the two previous M3
modules:

- Phase60: `Irrational (Real.logb 2 3)` (via 2-adic valuation).
- Phase61: CF convergents infrastructure (`log23_convergent`, `q_n`,
  `InWindow`, `not_convergent_implies_far_approx`).

## What this file provides

1. **API bridge (H9)** — `of_convs_eq_log23_convergent`:
   `(GenContFract.of (logb 2 3)).convs n` definitionally equal to
   `log23_convergent n` via Mathlib's `Real.convs_eq_convergent`. Unifies
   the two convergent APIs used by the project.
2. **Non-termination (H10)** — `log23_never_terminates`,
   `log23_not_terminatedAt`, `log23_partDens_some`: the CF expansion of
   `logb 2 3` never terminates (because `log₂ 3` is irrational, from
   Phase60). Unlocks the `¬ TerminatedAt n` hypothesis and partial
   denominator existence required by Mathlib's approximation bounds.
3. **Public approximation bound** — `log23_abs_sub_convergent_le`: for any
   index `n`, `|logb 2 3 - log23_convergent n| ≤ 1 / (bₙ · Bₙ²)` where
   `bₙ` is the `n`-th partial denominator and `Bₙ = (of logb23).dens n`
   is the real-valued CF denominator (NOT `q_n n`: `Bₙ ≠ q_n n` in general
   until the Phase63 bridge is constructed per R-M3.H12).
4. **Weak monotonicity of real-valued denominators** — `log23_dens_nonneg`,
   `log23_dens_mono`, `log23_dens_monotone`: the sequence
   `(of logb23).dens n` is non-negative and weakly monotone. Strict
   monotonicity of `q_n` (Phase61 natural-valued) is **deferred to Phase63**
   per R-M3.H12 (bridge `q_n ↔ (of v).dens` absent from Mathlib v4.27.0).
5. **Approximation bound in window (Option C alias)** —
   `log23_abs_sub_convergent_le_in_window`: for `k : ℕ` with
   `(of logb23).dens n ≤ k < (of logb23).dens (n+1)`, the Section 4
   approximation bound applies. This is an **alias** of Section 4's
   `log23_abs_sub_convergent_le`, enriched with a window-context signature
   for Phase63 instantiation; the bound itself is unconditional (see
   Section 6 and the Architecture note below for the Option C rationale
   and R-M3.H12). The "window" in the name refers to the documented usage
   pattern (Phase63 Product Bound), NOT a second-kind strengthening of the
   bound — both RT #2 (auditor) and post-commit reviewers should read this
   as an honest alias, not a classical window-bound theorem.

## Voie B architecture link

Phase63 (planned) will combine:
- Baker-style upper bound on `|2^s - 3^k|` (external hypothesis
  `BakerSeparation` preserved in Phase58/59).
- Window-bound (this file) for `k ∈ [qₙ, qₙ₊₁)`.
- `log23_irrational` (Phase60) for non-termination (this file).
- CF convergents infrastructure (Phase61) for the denominator sequence.

to produce `DerivedLargeKBoundTheorem` (main effort, 500-1000 lines
estimated).

## Mathlib dependencies (v4.27.0)

- `GenContFract.of : ℝ → GenContFract ℝ` — generic CF expansion.
- `(of v).convs n`, `(of v).dens n`, `(of v).partDens` — CF outputs.
- `Real.convergent : ℝ → ℕ → ℚ` — high-level API (used by Phase60/61).
- `Real.convs_eq_convergent` — bridge between the two APIs (H9).
- `GenContFract.terminates_iff_rat` — termination iff rational (H10).
- `abs_sub_convergents_le'` — classical approximation bound.
- `GenContFract.of_den_mono` — weak monotonicity of denominators.

## Invariants (M3.3)

- Zero `axiom` declaration (kernel three suffice via Mathlib).
- Zero `sorry`.
- No `native_decide` (reserved for Phase63 `cf_gap_*`).
- No modification of `expected_axioms.md` (M3.3 stays outside central chain
  until Phase63 integration).
- All docstrings in English.
- ALL RT findings fixed pre-commit (zero-flag policy, Eric 2026-04-23).

## Architecture note — Phase61 ↔ Phase62 bridge deferred (R-M3.H12)

Phase61 defines `q_n : ℕ` (natural denominator of `Real.convergent (logb 2 3) n`)
and the `InWindow n k : Prop` predicate on naturals.

Phase62 operates on `(GenContFract.of (logb 2 3)).dens n : ℝ` (real denominator
from the matrix-recurrence CF API). These two denominator APIs are
conceptually equal — `((Real.convergent v n).den : ℝ) = (GenContFract.of v).dens n`
— but Mathlib v4.27.0 does NOT provide this bridge directly. Constructing it
requires a ~30-50 line sub-project on gcd / reduced form normalization.

**Decision (M3.3 Option C)**: Phase62 Section 6 provides a **parametric alias**
of Section 4 with window-context hypotheses on an arbitrary real interval
`[B, B')`. Phase63 will choose at that time whether to:

- Instantiate with `B := (of logb23).dens n` (direct, no bridge), or
- Instantiate with `B := (q_n n : ℝ)` via the deferred bridge (if needed for
  statement compatibility with the Phase59 `DerivedLargeKBound` structure).

**`InWindow` Phase61 is NOT orphaned** — it remains available for Phase63
should the chosen instantiation require the natural-valued window. The
deferral is a deliberate architectural choice (R-M3.H12 in `RISK_REGISTER.md`,
DEFERRED-TO-M3.4), not an oversight.
-/

namespace ProjetCollatz.Phase62

open Real GenContFract
open ProjetCollatz.Phase61 (log23_convergent)

/-! ## Section 2 — H9 API bridge: `(of v).convs n = v.convergent n`

Mathlib provides two parallel continued-fraction convergent APIs:

- `GenContFract.of v : GenContFract ℝ` with `.convs n : ℝ` and
  `.dens n : ℝ` (module `Mathlib.Algebra.ContinuedFractions`).
- `Real.convergent ξ n : ℚ` (module
  `Mathlib.NumberTheory.DiophantineApproximation.Basic`), used by
  Phase60/61 via the wrapper `log23_convergent`.

The bridge `Real.convs_eq_convergent` (in
`Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions`) provides
a direct equality between these two APIs, cast-transparent. -/

/-- Bridge specialization to `log₂ 3`: the Mathlib
`GenContFract.of (logb 2 3)` convergent equals the Phase61 wrapper
`log23_convergent`, cast to ℝ. -/
theorem of_convs_eq_log23_convergent (n : ℕ) :
    (GenContFract.of (Real.logb 2 3)).convs n = (log23_convergent n : ℝ) := by
  rw [Real.convs_eq_convergent]
  rfl

/-! ## Section 3 — H10: non-termination of the CF expansion of `logb 2 3`

Mathlib's `GenContFract.terminates_iff_rat` states that the CF expansion
of `v : K` terminates if and only if `v` equals the cast of some rational.
Phase60 proved that `log₂ 3` is irrational, so the CF expansion never
terminates. This unlocks the `¬ TerminatedAt n` hypothesis pervasively
required by Mathlib's approximation bounds (e.g., `abs_sub_convergents_le'`). -/

/-- The continued-fraction expansion of `Real.logb 2 3` never terminates.
Proof: contrapositive of `terminates_iff_rat` via `Phase60.log23_irrational`. -/
theorem log23_never_terminates :
    ¬ (GenContFract.of (Real.logb 2 3)).Terminates := by
  rw [terminates_iff_rat]
  rintro ⟨q, hq⟩
  exact ProjetCollatz.Phase60.log23_irrational ⟨q, hq.symm⟩

/-- Pointwise non-termination at every index `n`. This is the usable form for
Mathlib's approximation bounds (e.g., `abs_sub_convergents_le'`), which require
`¬ TerminatedAt n` rather than `¬ Terminates`. -/
theorem log23_not_terminatedAt (n : ℕ) :
    ¬ (GenContFract.of (Real.logb 2 3)).TerminatedAt n := by
  intro h_term
  exact log23_never_terminates ⟨n, h_term⟩

/-- At every index `n`, the partial denominator of the CF expansion of
`logb 2 3` is defined (i.e. `partDens.get? n = some b` for some `b`).
Follows from `log23_not_terminatedAt` and the Mathlib characterisation
`terminatedAt_iff_partDen_none`. -/
theorem log23_partDens_some (n : ℕ) :
    ∃ b : ℝ, (GenContFract.of (Real.logb 2 3)).partDens.get? n = some b := by
  have h_not_term := log23_not_terminatedAt n
  rw [GenContFract.terminatedAt_iff_partDen_none] at h_not_term
  exact Option.ne_none_iff_exists'.mp h_not_term

/-! ## Section 4 — Public approximation bound for `log₂ 3`

The classical continued-fraction approximation bound
`|v - convs n| ≤ 1 / (bₙ · Bₙ²)` of Mathlib (`abs_sub_convergents_le'`)
applied to `v = logb 2 3`, restated in terms of the Phase61 wrapper
`log23_convergent` via the H9 bridge.

This is the main PUBLIC output of Phase62 that will be consumed by Phase63
for the Product Bound refinement. `bₙ` here is the real-valued partial
denominator delivered by `log23_partDens_some`; `Bₙ = (of logb23).dens n`
is the real-valued denominator of the `n`-th convergent. -/

/-- Approximation bound specialized to `logb 2 3`: there exists a partial
denominator `b` such that
`|logb 2 3 - (log23_convergent n : ℝ)| ≤ 1 / (b · B_n · B_n)`, where
`B_n = (of (logb 2 3)).dens n`. -/
theorem log23_abs_sub_convergent_le (n : ℕ) :
    ∃ b : ℝ, (GenContFract.of (Real.logb 2 3)).partDens.get? n = some b ∧
      |Real.logb 2 3 - (log23_convergent n : ℝ)| ≤
        1 / (b * (GenContFract.of (Real.logb 2 3)).dens n *
                 (GenContFract.of (Real.logb 2 3)).dens n) := by
  obtain ⟨b, hb⟩ := log23_partDens_some n
  refine ⟨b, hb, ?_⟩
  rw [← of_convs_eq_log23_convergent n]
  exact abs_sub_convergents_le' hb

/-! ## Section 5 — Real-valued CF denominators monotonicity for `logb 2 3`

This section provides the Mathlib-backed monotonicity facts on the
**real-valued** CF denominators `Bₙ = (of logb23).dens n`. These are the
denominators used by `abs_sub_convergents_le'` (Section 4).

### Plan deviation note (for RT #2 review)

The original M3.3 plan §3 Section 5 asked for **strict** monotonicity on
the Phase61 natural-valued `q_n n = (log23_convergent n).den`, intended
to enforce `InWindow n` partition disjointness (Phase61 `InWindow`
predicate). After investigation:

- Mathlib provides weak monotonicity on the real-valued `(of v).dens`
  (`GenContFract.of_den_mono`) but not on `Rat.den` of the convergent.
- The natural bridge `((log23_convergent n).den : ℝ) = (of logb23).dens n`
  is NOT proved by any direct Mathlib lemma (searches for
  `convergent.*den.*dens`, `convergent_den_eq`, `gcd.*convergent`,
  `nums_gcd_dens` all returned zero matches).
- Constructing this bridge from scratch requires `gcd(nums n, dens n) = 1`
  combined with `(convs n = nums n / dens n)` + `Rat.num_div_den` — a
  ~30-50 line sub-project that would overflow the Section 5 budget.

**Pragmatic choice**: this section exposes the **real-valued** weak
monotonicity on `(of logb23).dens`, which is sufficient for Section 6's
window-bound argument (which can be formulated directly on `.dens` rather
than needing `q_n`). The `InWindow` disjointness property of Phase61 is
preserved structurally (windows are empty at indices where `q_n` stagnates,
which is mathematically coherent).

**Explicit deferral**: full strict monotonicity of `q_n` is deferred to
Phase63 (along with the `dens ↔ q_n` bridge), where it integrates naturally
with the Product Bound argument. This deviation is flagged in the
`ready-for-push` report for auditor review. -/

/-- The real-valued CF denominator `Bₙ = (of logb23).dens n` is non-negative. -/
theorem log23_dens_nonneg (n : ℕ) :
    0 ≤ (GenContFract.of (Real.logb 2 3)).dens n :=
  GenContFract.zero_le_of_den

/-- The real-valued CF denominator sequence `(Bₙ)` is weakly monotone:
`Bₙ ≤ Bₙ₊₁` for all `n`. Direct wrapper around `GenContFract.of_den_mono`. -/
theorem log23_dens_mono (n : ℕ) :
    (GenContFract.of (Real.logb 2 3)).dens n ≤
    (GenContFract.of (Real.logb 2 3)).dens (n + 1) :=
  GenContFract.of_den_mono

/-- Transitive monotonicity of the real-valued CF denominator: for
`n ≤ m`, `Bₙ ≤ Bₘ`. Follows from iterated `log23_dens_mono`. -/
theorem log23_dens_monotone : Monotone (fun n => (GenContFract.of (Real.logb 2 3)).dens n) := by
  intro n m h_le
  induction h_le with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (log23_dens_mono _)

/-! ## Section 6 — Approximation bound in window (Option C alias)

This section provides an **alias** of Section 4's `log23_abs_sub_convergent_le`
with a window-context signature, for Phase63 instantiation. The `k : ℕ`
hypotheses `h_lo` and `h_hi` locate `k` inside the CF interval
`[(of logb23).dens n, (of logb23).dens (n+1))`; the proof itself is a
direct call to Section 4 without consuming the window — this is **not** a
classical second-kind window-bound theorem, but a transparent alias for
Phase63 usage pattern.

The naming `log23_abs_sub_convergent_le_in_window` reflects the alias
nature (same bound as Section 4, with window documentation). This honest
naming was adopted after RT #2 auditor flagged the original name
`log23_window_approximation_bound` as semantically misleading (the window
hypotheses are not consumed by the proof).

See Architecture note in the module docstring for R-M3.H12 deferral
(Phase63 picks either direct `(of).dens` or `q_n` via future bridge).

### Why alias rather than `q_n`-specialised window-bound?

Phase61 defines `q_n n : ℕ` and `InWindow n k : Prop` on naturals.
Specialising a true second-kind window-bound theorem to `q_n` would
require: (a) the bridge `((log23_convergent n).den : ℝ) = (of logb23).dens n`
(not directly available in Mathlib v4.27.0, ~30-50 line sub-project); and
(b) the second-kind best-approximation property itself (also absent from
Mathlib). Phase62 opts for the transparent alias; Phase63 builds the real
window-bound theorem when it has the concrete Product Bound argument to
instantiate. -/

/-- **Approximation bound in window (alias)**: for `k : ℕ` located in the CF
window `[(of logb23).dens n, (of logb23).dens (n+1))`, the `n`-th convergent
approximation bound (Section 4) applies.

This is a transparent **alias** of `log23_abs_sub_convergent_le` with a
window-context signature. The window hypotheses `_h_lo` and `_h_hi` place
`k` inside the interval delimited by consecutive CF denominators; the bound
itself is inherited directly from Section 4 without consuming the window.
The alias serves as a **documentation marker** for Phase63 Product Bound
instantiation — it records the intended window context in the signature
while delivering the unconditional Section 4 bound.

**This is NOT a classical second-kind window-bound theorem.** Such a
theorem would require the second-kind best-approximation property
(absent from Mathlib v4.27.0). Phase63 will construct the real window-bound
when the concrete Product Bound argument is written.

**Proof note (zero-flag disclosure, per RT #2 recommendation)**: the window
hypotheses `_h_lo` and `_h_hi` are NOT consumed by the proof. A downstream
Phase63 caller obtains exactly the same bound as a direct call to
`log23_abs_sub_convergent_le n`, with the window evidence available for
*other* purposes in the Phase63 proof (e.g. proving `k > 0` or selecting
the index `n`). -/
theorem log23_abs_sub_convergent_le_in_window (n : ℕ) (k : ℕ)
    (_h_lo : (GenContFract.of (Real.logb 2 3)).dens n ≤ (k : ℝ))
    (_h_hi : (k : ℝ) < (GenContFract.of (Real.logb 2 3)).dens (n + 1)) :
    ∃ b : ℝ, (GenContFract.of (Real.logb 2 3)).partDens.get? n = some b ∧
      |Real.logb 2 3 - (log23_convergent n : ℝ)| ≤
        1 / (b * (GenContFract.of (Real.logb 2 3)).dens n *
                 (GenContFract.of (Real.logb 2 3)).dens n) :=
  -- Alias with window documentation: _h_lo and _h_hi unused (bound is
  -- unconditional, Section 4 inheritance). Window hypotheses carried in
  -- signature for Phase63 instantiation pattern, not strengthening.
  log23_abs_sub_convergent_le n

end ProjetCollatz.Phase62
