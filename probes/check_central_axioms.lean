import ProjetCollatz

/-!
# probes/check_central_axioms.lean

Canonical probe for auditing axiom dependencies of the central and auxiliary
theorems of `collatz-nocycle-lean4`. Runs as part of `reproduce.sh` step [4/5].

Usage :
```bash
lake env lean probes/check_central_axioms.lean
```

Expected output (baseline as of 2026-04-22, commit d2fa81a) :

Section 1 — Central chain (7 theorems)
  propext, Classical.choice, Quot.sound       (3 fundamental Mathlib axioms)

Section 2 — Auxiliary native_decide lemmas (3 sampled)
  propext, Lean.ofReduceBool, Lean.trustCompiler  (isolated, NOT in central chain at G0)

Any deviation = axiom drift. `reproduce.sh` fails with EXIT 3.
Any occurrence of `sorryAx` anywhere in the output = BLOCKER (EXIT 4 via
`probes/check_sorry.lean` which is invoked separately).

Note : as of Phase Legendre (M3), `DerivedLargeKBound` will be promoted from a
`structure` to a proven theorem via `cf_gap_*` + Legendre 1798. At that point,
`Lean.ofReduceBool` and `Lean.trustCompiler` will enter the central chain of
`no_nontrivial_cycle_phase59`. `expected_axioms.md` must be updated at that
point before committing the M3 integration.
-/

-- ============================================================================
-- Section 1 — Central theorem chain
-- Expected : all 7 depend on [propext, Classical.choice, Quot.sound]
-- ============================================================================

-- Principal central theorem
#print axioms ProjetCollatz.no_nontrivial_cycle_phase59

-- Variants and alias forms
#print axioms ProjetCollatz.no_nontrivial_cycle_final
#print axioms ProjetCollatz.no_nontrivial_cycle_derived
#print axioms ProjetCollatz.no_nontrivial_cycle_full

-- Sub-branches of the central theorem
#print axioms ProjetCollatz.no_cycle_k_le_1322
#print axioms ProjetCollatz.no_cycle_k_gt_1322

-- Key conditional-derivation lemma
#print axioms ProjetCollatz.sdw_from_cf

-- ============================================================================
-- Section 2 — Auxiliary native_decide lemmas (sample)
-- Expected : [propext, Lean.ofReduceBool, Lean.trustCompiler]
-- These lemmas justify the `DerivedLargeKBound` content mathematically but
-- are NOT part of the central theorem's Lean chain at G0/G1/G2 (structure is
-- taken as parameter). They WILL enter the central chain in M3 (Phase Legendre).
-- ============================================================================

#print axioms ProjetCollatz.cf_gap_8
#print axioms ProjetCollatz.cf_gap_13
#print axioms ProjetCollatz.cf_nbound_8

-- ============================================================================
-- Section 3 — M3 Legendre foundational theorems (M3.1+)
-- Expected : [propext, Classical.choice, Quot.sound] (kernel 3 only)
-- These theorems are not yet integrated into the central chain ; they will
-- compose into no_nontrivial_cycle_phase59 at Phase63 (planned).
-- Tracked separately in reproduce.sh under M3_THEOREMS to make regressions
-- visible immediately, without waiting for Phase63 integration.
-- ============================================================================

#print axioms ProjetCollatz.Phase60.log23_irrational
#print axioms ProjetCollatz.Phase60.two_pow_ne_three_pow

-- Phase61 — CF convergents infrastructure (M3.2)
#print axioms ProjetCollatz.Phase61.log23_convergent
#print axioms ProjetCollatz.Phase61.logb23_pos
#print axioms ProjetCollatz.Phase61.q_n
#print axioms ProjetCollatz.Phase61.q_n_pos
#print axioms ProjetCollatz.Phase61.q_n_eq_den
#print axioms ProjetCollatz.Phase61.InWindow
#print axioms ProjetCollatz.Phase61.not_convergent_implies_far_approx
