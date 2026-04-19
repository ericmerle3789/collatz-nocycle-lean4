/-
# `test/TestCylinders.lean` — Tests Sprint 4a

Tests de cohérence pour `ProjetCollatz/PAdic/Cylinders.lean` :
1. Cohérence définitionnelle du cylindre (def unfold).
2. Appartenance via `toZModPow` (def unfold).
3. Théorème `wellDefinedDomain_measure` instancié pour L=1, 2, 3.

Note : la monotonie `wellDefinedDomain L ⊆ wellDefinedDomain (L+1)` est
mathématiquement vraie mais sa preuve Lean requiert `ker_toZModPow` +
`Ideal.span_singleton_le_span_singleton` (non-trivial). Reportée Sprint 4a-bis.
-/

import ProjetCollatz.PAdic.Cylinders

namespace ProjetCollatz.PAdic.Test

open ProjetCollatz.PAdic

/-! ## Test 1 : Cohérence définitionnelle du cylindre -/

example {k : ℕ} (r : ZMod (2^k)) :
    cylinder r = (PadicInt.toZModPow k) ⁻¹' {r} := cylinder_def r

example {k : ℕ} (r : ZMod (2^k)) (x : ZTwo) :
    x ∈ cylinder r ↔ PadicInt.toZModPow k x = r := mem_cylinder_iff r x

/-! ## Test 2 : Cohérence du domaine E_L

Appartenance à `wellDefinedDomain L` équivaut à la non-annulation dans
`ZMod(2^L)` du projeté de `3x+1`. Test par définition. -/

example (L : ℕ) (x : ZTwo) :
    x ∈ wellDefinedDomain L ↔ PadicInt.toZModPow L (3 * x + 1) ≠ 0 :=
  mem_wellDefinedDomain_iff L x

/-! ## Test 3 : Borne de mesure `μ((E_L)^c) ≤ 2^{-L}` (note v3 §1.3)

Via `wellDefinedDomain_measure_le` pour L = 1, 2, 3. -/

example : haarZTwo (wellDefinedDomain 1)ᶜ ≤ ((1 : ENNReal) / 2) ^ 1 :=
  wellDefinedDomain_measure_le 1

example : haarZTwo (wellDefinedDomain 2)ᶜ ≤ ((1 : ENNReal) / 2) ^ 2 :=
  wellDefinedDomain_measure_le 2

example : haarZTwo (wellDefinedDomain 3)ᶜ ≤ ((1 : ENNReal) / 2) ^ 3 :=
  wellDefinedDomain_measure_le 3

/-! ## Test 4 : Égalité stricte (plus forte que §1.3)

Notre formalisation donne l'**égalité** `μ((E_L)^c) = 2^{-L}`, via le fait
que E_L^c est EXACTEMENT un cylindre (pas juste inclus dans). -/

example : haarZTwo (wellDefinedDomain 5)ᶜ = ((1 : ENNReal) / 2) ^ 5 :=
  wellDefinedDomain_measure 5

end ProjetCollatz.PAdic.Test
