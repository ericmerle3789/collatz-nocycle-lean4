/-
Copyright (c) 2026 Eric Merle. All rights reserved.

# `ProjetCollatz/CompactnessSyracuseLink.lean` — Sprint 4c

Interface entre `CompactnessDefs` (Sprint 4b) et `SyracuseDefs` (dynamique
Collatz existante du projet). Fournit les briques pour Sprint 4d
(théorème no-go T3, cf. `NOTE_2ADIC_REFRAMING_v3.md` §2.3).

## Contenu

* `h_mul_pow2 n k : h (n * 2^k) = h n` — les zéros trailing ne changent pas h.
* `h_div_pow2_v2Nat n : h n = h (n / 2^(v2Nat n))` — h invariant par division
  par la plus grande puissance de 2 dans n.
* `IsCompact_mul_pow2 k m n : IsCompact k (n * 2^m) ↔ IsCompact k n` —
  corollaire direct de h_mul_pow2.
* `h_syracuseNext n : h (syracuseNext n) = h (3 * n + 1)` — **bridge clé**
  reliant la dynamique Syracuse à la fonction de compacité.
* `IsCompact_syracuseNext_iff k n : IsCompact k (syracuseNext n) ↔ IsCompact k (3 * n + 1)`
  — corollaire de `h_syracuseNext`.

## Statut Sprint 4c

**GOLD** : 0 sorry, 0 axiome, 5 théorèmes prouvés.

## Convention

Namespace `ProjetCollatz.Compactness` (cohérent avec Sprint 4b).
Import `ProjetCollatz.SyracuseDefs` pour accéder à `v2Nat`, `v2_3n1`, `syracuseNext`.
-/

import ProjetCollatz.CompactnessDefs
import ProjetCollatz.SyracuseDefs

namespace ProjetCollatz.Compactness

open ProjetCollatz

/-! ## §1. `h` invariante par multiplication par une puissance de 2 -/

/-- Multiplier par `2^k` ne change pas `h` : les zéros trailing ne comptent pas. -/
theorem h_mul_pow2 (n k : ℕ) : h (n * 2^k) = h n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, mul_comm (n * 2^k) 2, h_two_mul]
    exact ih

/-! ## §2. `h` invariante par division par la partie paire -/

/-- `h n` égale `h` du "noyau impair" de `n`, obtenu par division par `2^(v2Nat n)`. -/
theorem h_div_pow2_v2Nat (n : ℕ) : h n = h (n / 2^(v2Nat n)) := by
  by_cases hn : n = 0
  · subst hn; simp
  · -- Soit m := n / 2^(v2Nat n) ; par pow2_v2Nat_dvd on a n = m * 2^(v2Nat n).
    -- Goal après `set` : h n = h m. On réécrit le LHS via hn_eq pour obtenir
    -- h (m * 2^(v2Nat n)) = h m, qui est exactement h_mul_pow2.
    have hdvd : 2^(v2Nat n) ∣ n := pow2_v2Nat_dvd n
    set m := n / 2^(v2Nat n) with hm_def
    have hn_eq : n = m * 2^(v2Nat n) := (Nat.div_mul_cancel hdvd).symm
    conv_lhs => rw [hn_eq]
    exact h_mul_pow2 m (v2Nat n)

/-! ## §3. IsCompact préservé par multiplication par puissance de 2 -/

/-- `IsCompact` est invariant par multiplication par `2^m` : doubler n'importe
combien de fois ne change pas la compacité. -/
theorem IsCompact_mul_pow2 (k m n : ℕ) : IsCompact k (n * 2^m) ↔ IsCompact k n := by
  unfold IsCompact
  rw [h_mul_pow2]

/-! ## §4. Bridge Syracuse : `h ∘ syracuseNext = h ∘ (3·+1)`

Lemme clé pour Sprint 4d. La carte Syracuse `syracuseNext n = (3n+1)/2^(v₂(3n+1))`
supprime la partie paire de `3n+1`, qui par `h_div_pow2_v2Nat` ne change pas `h`.
Donc `h ∘ syracuseNext = h ∘ (3·+1)`.

Conséquence : l'analyse du drift `Δh` sous Syracuse se réduit à l'analyse
de `h(3n+1) - h(n)`, sans avoir à tenir compte du « bruit » des divisions
par 2. -/
theorem h_syracuseNext (n : ℕ) : h (syracuseNext n) = h (3 * n + 1) := by
  simp only [syracuseNext, v2_3n1]
  exact (h_div_pow2_v2Nat (3 * n + 1)).symm

/-- Corollaire : si `n` est compact et `3n+1` reste compact au même seuil,
alors `syracuseNext n` l'est aussi. -/
theorem IsCompact_syracuseNext_iff (k n : ℕ) :
    IsCompact k (syracuseNext n) ↔ IsCompact k (3 * n + 1) := by
  unfold IsCompact
  rw [h_syracuseNext]

end ProjetCollatz.Compactness
