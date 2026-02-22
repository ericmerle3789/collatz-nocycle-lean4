import ProjetCollatz.CollatzCore

namespace CollatzOddInst

open CollatzCore

/-
Instanciation "odd→odd" paramétrée par `a : ℕ → ℕ` dans ℚ.
On fabrique une trajectoire Nrec qui satisfait l'équation de pas par définition,
donc `steps_up_to` est vrai "par simp".
-/

/-- Trajectoire en ℚ définie par la règle de transition, paramétrée par `a`. -/
def Nrec (n0 : ℚ) (a : ℕ → ℕ) : ℕ → ℚ
  | 0     => n0
  | k + 1 => (3 * Nrec n0 a k + 1) / ((2 : ℚ) ^ (a k))

/-- La relation `steps_up_to` est vraie pour Nrec/a (hk inutile). -/
theorem steps_up_to_Nrec (n0 : ℚ) (a : ℕ → ℕ) (K : ℕ) :
    steps_up_to (N := Nrec n0 a) (a := a) K := by
  intro k hk
  -- hk n'est pas utilisé : la relation vaut pour tout k
  simp [CollatzCore.step, Nrec]


/-- Application directe du noyau "dur" à l'instance Nrec/a. -/
theorem hard_lower_bound_inst (n0 : ℚ) (a : ℕ → ℕ) (K : ℕ) :
    Nrec n0 a K ≥
      Nrec n0 a 0 * (3 : ℚ)^K /
        ((2 : ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i))) := by
  -- `hard_lower_bound` demande seulement `steps_up_to`, qu'on a par définition.
  simpa using
    (CollatzCore.hard_lower_bound
      (N := Nrec n0 a) (a := a) K (steps_up_to_Nrec n0 a K))


/- Version "mean" : si la moyenne des paiements est bornée, on obtient la borne exponentielle. -/
theorem hard_lower_bound_mean_inst (n0 : ℚ) (a : ℕ → ℕ) (K t : ℕ)
    (hn0 : 0 ≤ n0)
    (hmean : (∑ i ∈ Finset.range K, (a i : ℚ)) ≤ (t : ℚ) * (K : ℚ)) :
    Nrec n0 a K ≥ Nrec n0 a 0 * ((3 : ℚ) / ((2 : ℚ) ^ t)) ^ K := by
  have hsteps : steps_up_to (N := Nrec n0 a) (a := a) K := steps_up_to_Nrec n0 a K
  have hN0 : 0 ≤ Nrec n0 a 0 := by
    simpa [Nrec] using hn0
  -- On réutilise le corollaire "mean" du noyau.
  simpa [Nrec] using
    (CollatzCore.hard_lower_bound_mean
      (N := Nrec n0 a) (a := a) (K := K) (t := t) hsteps hN0 hmean)

end CollatzOddInst
