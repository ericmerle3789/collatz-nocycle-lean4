import ProjetCollatz

/-!
# probes/check_sorry.lean

Dedicated probe that triggers Lean's own `sorryAx` detection across all central
and auxiliary theorems audited by G2 hardening. Stricter than textual `grep
sorry`, because `grep` misses `sorryAx` injected via macros, custom elaborators,
or imports.

Usage (invoked by `reproduce.sh` step [5/5]) :
```bash
lake env lean probes/check_sorry.lean
```

`reproduce.sh` greps the output for `sorryAx` and exits with code 4 if found.

Rationale : a `sorry` anywhere in the transitive dependency chain of ANY of
these theorems will surface as `sorryAx` in the `#print axioms` output —
regardless of how the sorry was introduced.

Post-RT mitigation M2 (2026-04-22) : coverage extended from 1 theorem
(`no_nontrivial_cycle_phase59` only) to all 10 audited theorems (7 central + 3
auxiliary), so a sorry in e.g. `no_cycle_k_le_1322` cannot slip through.
-/

-- Central chain (7)
#print axioms ProjetCollatz.no_nontrivial_cycle_phase59
#print axioms ProjetCollatz.no_nontrivial_cycle_final
#print axioms ProjetCollatz.no_nontrivial_cycle_derived
#print axioms ProjetCollatz.no_nontrivial_cycle_full
#print axioms ProjetCollatz.no_cycle_k_le_1322
#print axioms ProjetCollatz.no_cycle_k_gt_1322
#print axioms ProjetCollatz.sdw_from_cf

-- Auxiliary native_decide lemmas (3)
#print axioms ProjetCollatz.cf_gap_8
#print axioms ProjetCollatz.cf_gap_13
#print axioms ProjetCollatz.cf_nbound_8

-- M3 Legendre foundational theorems (2) — added 2026-04-23 M3.1
-- Any sorryAx introduced in Phase60-63 will surface here immediately.
#print axioms ProjetCollatz.Phase60.log23_irrational
#print axioms ProjetCollatz.Phase60.two_pow_ne_three_pow

-- Phase61 CF convergents (7) — added 2026-04-23 M3.2
#print axioms ProjetCollatz.Phase61.log23_convergent
#print axioms ProjetCollatz.Phase61.logb23_pos
#print axioms ProjetCollatz.Phase61.q_n
#print axioms ProjetCollatz.Phase61.q_n_pos
#print axioms ProjetCollatz.Phase61.q_n_eq_den
#print axioms ProjetCollatz.Phase61.InWindow
#print axioms ProjetCollatz.Phase61.not_convergent_implies_far_approx

-- Phase62 Best-Approximation Bridge (9) — added 2026-04-24 M3.3
#print axioms ProjetCollatz.Phase62.of_convs_eq_log23_convergent
#print axioms ProjetCollatz.Phase62.log23_never_terminates
#print axioms ProjetCollatz.Phase62.log23_not_terminatedAt
#print axioms ProjetCollatz.Phase62.log23_partDens_some
#print axioms ProjetCollatz.Phase62.log23_abs_sub_convergent_le
#print axioms ProjetCollatz.Phase62.log23_dens_nonneg
#print axioms ProjetCollatz.Phase62.log23_dens_mono
#print axioms ProjetCollatz.Phase62.log23_dens_monotone
#print axioms ProjetCollatz.Phase62.log23_abs_sub_convergent_le_in_window
