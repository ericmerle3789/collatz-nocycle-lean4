import ProjetCollatz.Phase61CFConvergents

/-!
# probes/check_phase61_axioms.lean

Dedicated axiom probe for Phase61 (M3.2 Continued-Fraction Convergents).

Expected output (baseline M3.2) :
  propext, Classical.choice, Quot.sound       (kernel 3, inherited via Mathlib)

Any deviation (e.g. `sorryAx`, `Lean.ofReduceBool`, new axiom) = BLOCKER.
-/

-- Wrapper + basics
#print axioms ProjetCollatz.Phase61.log23_convergent
#print axioms ProjetCollatz.Phase61.logb23_pos

-- H2 bridge (denominators)
#print axioms ProjetCollatz.Phase61.q_n
#print axioms ProjetCollatz.Phase61.q_n_pos
#print axioms ProjetCollatz.Phase61.q_n_eq_den
#print axioms ProjetCollatz.Phase61.q_n_real_pos

-- Abstract window frame
#print axioms ProjetCollatz.Phase61.InWindow
#print axioms ProjetCollatz.Phase61.InWindow.lower
#print axioms ProjetCollatz.Phase61.InWindow.upper
#print axioms ProjetCollatz.Phase61.InWindow.mk

-- H3 Legendre second-kind contrapositive
#print axioms ProjetCollatz.Phase61.not_convergent_implies_far_approx
