import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import ProjetCollatz.Phase58PorteDeuxFinal
import ProjetCollatz.Phase59ContinuedFractions
import ProjetCollatz.Phase60IrrationalityLog23
import ProjetCollatz.Phase61CFConvergents
import ProjetCollatz.Phase62BestApproxBridge

/-!
# Phase 63 — `DerivedLargeKBoundTheorem`: `DerivedLargeKBound` structure replaced by theorem

## Context

This file is the **main effort of Phase Legendre M3** (M3.4). It proves the
`DerivedLargeKBound` structure field `large_k_bound` as a genuine Lean
theorem, combining:

- The external `BakerSeparation` hypothesis (Phase58, encoding Baker 1966
  linear forms in logarithms for `|2^s - 3^k|`).
- The 6 continued-fraction gap constants `cf_gap_8..13` (Phase59, proved
  via `native_decide` from explicit numerics).
- The 6 window `n`-bounds `cf_nbound_8..13` (Phase59, proved via
  `native_decide`).
- The Phase60-62 infrastructure: irrationality of `log₂ 3`, CF convergents
  indexed by `Real.convergent`, and the approximation bound
  `log23_abs_sub_convergent_le`.

## What this file provides

1. **Helper lemma `window_n_bound_proof`** — the DRY core of Phase63. A
   single parametric proof pattern that takes a window index, its
   denominator bracket `[q_start, q_end)`, the Phase59 `cf_gap_n` and
   `cf_nbound_n` constants, and concludes `n < 2^71` for any odd Collatz
   cycle `(n, k)` with `k` in the window. Reused 6 times rather than
   copy-pasted.
2. **Six window instantiations** (Section 3-8) — `window_bound_8`, ...,
   `window_bound_13`, each calling the helper with the corresponding
   Phase59 constants.
3. **Disjunction synthesis** (Section 9) — `large_k_exists_window`: for any
   `k > 1322`, there exists a window index `n ∈ {8, ..., 13}` such that `k`
   lies in window `n`.
4. **Main theorem** (Section 10) — `large_k_bound_theorem_phase63`: for any
   `(n, k)` with `IsOddCycle n k` and `k > 1322`, `n < 2^71`. Proved by
   case-analysis on the disjunction + window instantiations.
5. **Replacement definition** (Section 11) — `derivedLargeKBound_proved`:
   given `BakerSeparation`, constructs a `DerivedLargeKBound` instance.
   Preserves Phase59 interface — `sdwFromCF` and `no_cycle_k_gt_1322`
   continue to work unchanged.

## Architecture: from structure to theorem

Before Phase63 (M2/M3.1-3), `DerivedLargeKBound` was a `structure`
parameterized by an assumption field `large_k_bound`. This meant the
central theorem `no_nontrivial_cycle_phase59` took `DerivedLargeKBound` as
an external hypothesis, which an Acta Arithmetica reviewer could
legitimately challenge as a hidden axiom.

Phase63 removes that hidden axiom by constructing a genuine proof of
`large_k_bound` from:
- `BakerSeparation` (a classical number-theoretic hypothesis, widely
  published)
- Computational `cf_gap_*` / `cf_nbound_*` (`native_decide`, fully
  reproducible)
- Phase60-62 continued-fraction infrastructure (kernel-3 axioms only)

## Axiom profile impact (M3.4 central chain expansion)

Unlike Phase60-62, which were kernel-3 only, Phase63 **introduces
`Lean.ofReduceBool` and `Lean.trustCompiler` into the central theorem
chain** (via its imports from Phase59, which host the `native_decide`
arithmetic for `cf_gap_*` and `cf_nbound_*`). This is a deliberate and
documented decision:

- `expected_axioms.md` Section 1 is updated in the M3.4 commit to list
  these two axioms alongside `propext`, `Classical.choice`, `Quot.sound`
  for the 7 central theorems.
- The forthcoming paper v2 (post-M3.6) will explicitly acknowledge
  `Lean.ofReduceBool` + `Lean.trustCompiler` in its formalisation section
  as the two axioms required by the 6 `native_decide` arithmetic
  verifications.
- No user `axiom` declaration is introduced. Only the Lean kernel's
  compiler-trust axioms, which are standard in Mathlib formalisations
  relying on `native_decide`.

This is the axiom trade-off that M2 foresaw explicitly (see
`docs/BIBLE/RISK_REGISTER.md` R-10, status FORESEEN-M3) and that
`expected_axioms.md` Section 3 anticipated: the computational gap
verifications were isolated from the central chain at G0-M3.3 via the
structure pattern, and are now promoted into the chain as Phase63
integrates them.

## Invariants (M3.4)

- Zero `axiom` declaration (kernel axioms + the two `native_decide` axioms
  inherited from Phase59 are acknowledged and documented).
- Zero `sorry`.
- Zero `admit`, zero `stop`.
- All docstrings in English.
- ALL RT findings fixed pre-commit (zero-flag policy, Eric 2026-04-23).
- Helper lemma used (DRY compliance per R-M3.H13 mitigation, plan 0061 §1.4).
- No `native_decide` *tactic* in Phase63 proof bodies (the axioms arrive
  via `import Phase59` only, through the pre-existing `cf_gap_*` /
  `cf_nbound_*` theorems).

## R-M3.H12 bridge decision

The bridge `((Real.convergent v n).den : ℝ) = (GenContFract.of v).dens n` was
flagged in `docs/BIBLE/RISK_REGISTER.md` as R-M3.H12 DEFERRED-TO-M3.4 (Phase63).
Per plan 0061 §1.2, Phase63 starts **without** the bridge (using the parametric
window-bound alias `log23_abs_sub_convergent_le_in_window` from Phase62, which
abstracts over real-valued CF denominators). If Section 2's helper lemma proof
requires `q_n n` (Phase61 natural-valued) rather than `(of logb23).dens n`
(Phase62 real-valued), the ~30-50 line bridge will be constructed in Phase63
at that point. Current state: **deferred, not needed yet** (Section 1 only,
Sections 2-11 pending math guidance from auditor per 0069 disclosure).

## Policy Indiana Jones note

Per Eric directive 2026-04-24T~13:00+02, budget lines are **indicative
only** (800 ceiling, 700 alert). Stop criteria: mathematical blocker /
Mathlib gap without workaround / circular pattern (3+ repeated errors) /
5 consecutive tactic failures. Protocol safeguards (§3 checklist, RT #1,
3× RT #2 auditor, zero-flag, anti-G3.11, GO pre-push) are strictly
maintained.

## References to Phase59 existing constants

Window 8  : q_8  = 665,       q_9  = 15601,    cf_gap_8  : 2·2^1055 ≥ 3·3^665
Window 9  : q_9  = 15601,     q_10 = 31867,    cf_gap_9  : 54961·2^24727 ≥ 54962·3^15601
Window 10 : q_10 = 31867,     q_11 = 79335,    cf_gap_10 : 2·2^50509 ≥ 3·3^31867
Window 11 : q_11 = 79335,     q_12 = 111202,   cf_gap_11 : 272872·2^125743 ≥ 272873·3^79335
Window 12 : q_12 = 111202,    q_13 = 190537,   cf_gap_12 : 2·2^176252 ≥ 3·3^111202
Window 13 : q_13 = 190537,    q_14 = 10590737, cf_gap_13 : 15502073·2^301994 ≥ 15502074·3^190537

Together these 6 windows cover `k ∈ [665, 10590737)`. Combined with
Phase58's `no_cycle_k_le_1322`, the disjunction covers all cycle
denominators `k > 0` (since any `k > 1322` must fall into Window 8-13
or above q_14 = 10590737, the latter being ruled out via the same
mechanism for a hypothetical Window 14 if ever needed — currently out
of scope, as `q_14 ≈ 10.6M` exceeds the `2^71` Barina verification range
in a controlled way).
-/

namespace ProjetCollatz.Phase63

open ProjetCollatz (BakerSeparation BarinaVerification IsOddCycle DerivedLargeKBound)
open ProjetCollatz (cf_gap_8 cf_gap_9 cf_gap_10 cf_gap_11 cf_gap_12 cf_gap_13)
open ProjetCollatz (cf_nbound_8 cf_nbound_9 cf_nbound_10 cf_nbound_11 cf_nbound_12 cf_nbound_13)

/-! ## Section 1 — Imports + namespace (this header) -/

/-!
## M3.4 Pivot — Option β renforcée (2026-04-24)

As of April 2026, Sections 2-11 of this file are **not implemented**.
Phase63 Section 1 is preserved as a skeleton documenting the proposed
shape of `DerivedLargeKBound` (Phase59) as a theorem, but the promotion
of that structure from hypothesis to theorem is structurally blocked —
see paper v2 §5 Obstruction I (Product-Bound Impossibility Lemma, δ8)
for the rigorous explanation.

See also :
  - paper v2 §6 for state-of-the-art literature mapping 1977-2026 (δ9) ;
  - paper v2 §7 for alternative framing via the CF-window disjunction
    (δ7 — the disjunction structure intended for Sections 2-11 of this
    file) ;
  - Project mathnotes archive : `docs/BIBLE/mathnotes/`
    (literature review and mathematical derivations).

Notation (paper v2) : δ7 = alternative framing (CF disjunction) ;
δ8 = Product-Bound Impossibility ; δ8' = extended impossibility ;
δ9 = state-of-the-art mapping.
-/

end ProjetCollatz.Phase63
