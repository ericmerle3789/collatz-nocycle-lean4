import ProjetCollatz.Phase60IrrationalityLog23

/-!
# probes/check_phase60_axioms.lean

Dedicated axiom probe for Phase60 (M3.1 Irrationality of log₂ 3).

Expected output (baseline M3.1) :
  propext, Classical.choice, Quot.sound       (kernel 3, inherited via Mathlib)

Any deviation (e.g. `sorryAx`, `Lean.ofReduceBool`, new axiom) = BLOCKER.
-/

-- Main theorem of Phase60
#print axioms ProjetCollatz.Phase60.log23_irrational

-- Auxiliary lemma used in the main proof
#print axioms ProjetCollatz.Phase60.two_pow_ne_three_pow
