import ProjetCollatz.Phase9BinaryCascade

/-!
# Phase9CascadeInduction.lean — Preuve inductive de la cascade binaire

## Résultat principal

Lemme algébrique central : si n a au moins k trailing ones (k >= 3),
alors sN(n) a au moins k-1 trailing ones.

Corollaire : après k-3 pas, on atteint la classe 7 mod 8 avec exactement 3
trailing ones, permettant la transition vers classe 3 au pas suivant.

Date : 2026-02-15 (Phase 9 Sprint 2)
-/

namespace ProjetCollatz

noncomputable section

open ProjetCollatz

/-!
## Lemmes auxiliaires sur les puissances de 2
-/

theorem pow2_pos' (k : ℕ) : 0 < 2^k := Nat.pos_of_ne_zero (by positivity)

theorem pow2_ge1 (k : ℕ) : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)

theorem pow2_split (k : ℕ) (hk : 1 ≤ k) : 2^k = 2 * 2^(k-1) := by
  cases k with
  | zero => omega
  | succ n => simp [pow_succ, mul_comm]

theorem four_dvd_pow2 (k : ℕ) (hk : 2 ≤ k) : 4 ∣ 2^k := by
  have : (4 : ℕ) = 2^2 := by norm_num
  rw [this]
  exact Nat.pow_dvd_pow 2 hk

theorem four_le_pow2 (k : ℕ) (hk : 2 ≤ k) : 4 ≤ 2^k := by
  calc 4 = 2^2 := by norm_num
  _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk

/-!
## Lemme modulaire pour la forme 2^k·q + 2^k-1
-/

theorem mod4_eq3_of_form (k q : ℕ) (hk : 2 ≤ k) :
    (2^k * q + (2^k - 1)) % 4 = 3 := by
  have h4dvd := four_dvd_pow2 k hk
  obtain ⟨m, hm⟩ := h4dvd
  -- 2^k = 4*m, et m >= 1 car 2^k >= 4
  have hm_pos : 1 ≤ m := by
    have h4le := four_le_pow2 k hk
    omega
  rw [hm]
  -- Goal: (4 * m * q + (4 * m - 1)) % 4 = 3
  -- Stratégie : réécrire comme 4 * N + 3
  -- 4*m*q = (m*q)*4 et 4*m - 1 = (m-1)*4 + 3
  have h1 : 4 * m * q = m * q * 4 := by ring
  have h2 : 4 * m - 1 = (m - 1) * 4 + 3 := by omega
  rw [h1, h2]
  -- Goal: (m * q * 4 + ((m - 1) * 4 + 3)) % 4 = 3
  have h3 : m * q * 4 + ((m - 1) * 4 + 3) = (m * q + (m - 1)) * 4 + 3 := by ring
  rw [h3]
  -- Goal: ((m * q + (m - 1)) * 4 + 3) % 4 = 3
  -- pattern: (a * b + c) % b = c % b → Nat.add_mul_mod_self_right ou omega
  omega

/-!
## Formule Syracuse pour la cascade

Pour n = 2^k·q + 2^k - 1 (k >= 2) :
  3n + 1 = 3·2^k·q + 3·2^k - 2 = 2·(3·2^{k-1}·q + 3·2^{k-1} - 1)
  v2(3n+1) = 1 (car n % 4 = 3)
  sN(n) = (3n+1)/2 = 3·2^{k-1}·q + 3·2^{k-1} - 1
-/

theorem cascade_formula (k q : ℕ) (hk : 2 ≤ k) :
    syracuseNext (2^k * q + (2^k - 1)) = 3 * 2^(k-1) * q + (3 * 2^(k-1) - 1) := by
  have hmod4 := mod4_eq3_of_form k q hk
  have hv1 : v2_3n1 (2^k * q + (2^k - 1)) = 1 := v2_mod4_eq3_eq1 _ hmod4
  have hspec := syracuseNext_spec (2^k * q + (2^k - 1))
  rw [hv1] at hspec
  simp at hspec
  -- hspec : syracuseNext (...) * 2 = 3 * (2^k * q + (2^k - 1)) + 1
  have hge : 1 ≤ 2^k := pow2_ge1 k
  have hge1 : 1 ≤ 2^(k-1) := pow2_ge1 (k-1)
  have hpow := pow2_split k (by omega : 1 ≤ k)
  -- Multiplier le RHS par 2 et comparer
  -- RHS * 2 = (3 * 2^{k-1} * q + (3 * 2^{k-1} - 1)) * 2
  -- = 6 * 2^{k-1} * q + 6 * 2^{k-1} - 2
  -- = 3 * (2 * 2^{k-1}) * q + 3 * (2 * 2^{k-1}) - 2
  -- = 3 * 2^k * q + 3 * 2^k - 2
  -- = 3 * (2^k * q + (2^k - 1)) + 1 = LHS * 2
  suffices h : syracuseNext (2^k * q + (2^k - 1)) * 2 =
    (3 * 2^(k-1) * q + (3 * 2^(k-1) - 1)) * 2 by
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) h
  rw [hspec, hpow]
  ring_nf
  omega

/-!
## Corollaire central : réduction des trailing ones
-/

theorem cascade_reduces_trailing (n k : ℕ) (hk : 3 ≤ k)
    (hmod : n % 2^k = 2^k - 1) :
    syracuseNext n % 2^(k-1) = 2^(k-1) - 1 := by
  have hpk : 0 < 2^k := pow2_pos' k
  -- n = 2^k * (n / 2^k) + n % 2^k = 2^k * q + (2^k - 1)
  have hq_def : n = 2^k * (n / 2^k) + n % 2^k := (Nat.div_add_mod n (2^k)).symm
  rw [hmod] at hq_def
  set q := n / 2^k
  have hk2 : 2 ≤ k := by omega
  have hge1 : 1 ≤ 2^(k-1) := pow2_ge1 (k-1)
  -- Réécrire n dans le but
  conv_lhs => rw [hq_def]
  rw [cascade_formula k q hk2]
  -- Goal: (3 * 2^{k-1} * q + (3 * 2^{k-1} - 1)) % 2^{k-1} = 2^{k-1} - 1
  -- 3 * 2^{k-1} * q = 2^{k-1} * (3 * q)
  have hrewrite : 3 * 2^(k-1) * q = 2^(k-1) * (3 * q) := by ring
  rw [hrewrite]
  -- Goal: (2^{k-1} * (3*q) + (3*2^{k-1} - 1)) % 2^{k-1} = 2^{k-1} - 1
  -- Utiliser Nat.mul_add_mod_self_left : (a*b + c) % a = c % a
  rw [Nat.mul_add_mod_self_left]
  -- Goal: (3*2^{k-1} - 1) % 2^{k-1} = 2^{k-1} - 1
  -- 3*a - 1 = a*2 + (a-1), donc (a*2 + (a-1)) % a = (a-1) % a = a-1
  have hsplit : 3 * 2^(k-1) - 1 = 2^(k-1) * 2 + (2^(k-1) - 1) := by omega
  rw [hsplit, Nat.mul_add_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-!
## Théorème de cascade itéré

Chaque pas réduit les trailing ones de 1.
Après j pas (j ≤ k-3), on a au moins k-j trailing ones.
-/

theorem cascade_iterate (n : ℕ) :
    ∀ k j : ℕ, 3 ≤ k → j ≤ k - 3 →
    n % 2^k = 2^k - 1 →
    nSeq n j % 2^(k - j) = 2^(k - j) - 1 := by
  intro k j hk hj hmod
  induction j with
  | zero =>
    simp [nSeq]
    exact hmod
  | succ j' ih =>
    simp only [nSeq]
    have hj'_le : j' ≤ k - 3 := by omega
    have ih_result := ih hj'_le
    have hk_j' : 3 ≤ k - j' := by omega
    have hred := cascade_reduces_trailing (nSeq n j') (k - j') hk_j' ih_result
    have heq : k - (j' + 1) = k - j' - 1 := by omega
    rw [heq]
    exact hred

/--
**Théorème principal : après k-3 pas de cascade, on atteint la classe 7 mod 8.**

Si n a au moins k trailing ones (k >= 3),
alors nSeq(n, k-3) ≡ 7 mod 8.
-/
theorem cascade_reaches_class7 (n k : ℕ) (hk : 3 ≤ k)
    (hmod : n % 2^k = 2^k - 1) :
    nSeq n (k - 3) % 8 = 7 := by
  have hiter := cascade_iterate n k (k - 3) hk (by omega) hmod
  have heq : k - (k - 3) = 3 := by omega
  rw [heq] at hiter
  norm_num at hiter
  exact hiter

end

end ProjetCollatz
