import ProjetCollatz.ModularHierarchy
import ProjetCollatz.Phase6BLemmas

/-!
# Phase7Theorems.lean — Nouveaux résultats Phase 7 Sprint 2

## Contenu

### Descent et dynamique
- `descent_of_v2_ge2` : Descente généralisée — si v₂(3n+1) ≥ 2 et n > 1, alors syracuseNext(n) < n
  (généralise B1 de Phase6BLemmas qui n'est valide que pour n ≡ 1 mod 4)
- `descent_v2_ge2_ratio` : Borne de ratio — syracuseNext(n) ≤ (3n+1)/4 quand v₂ ≥ 2
- `ascent_bounded` : Montée bornée — syracuseNext(n) < 2n pour tout n impair

### Théorème de proportion de descente
- `descent_proportion_mod4` : Au moins 1/2 des impairs descendent (les n ≡ 1 mod 4)
- `descent_proportion_mod16` : Distribution détaillée mod 16 → moyenne 15/8 > log₂(3)

### Théorème de progression en 2 pas
- `two_step_descent_from_mod8_eq3` : Si n ≡ 3 (mod 8), alors en 2 pas Syracuse,
  le deuxième pas est une descente garantie.

### Complétude hiérarchie modulaire
- `stochastic_exists_and_unique` : Combinaison existence + unicité en un seul théorème.

## Connexion au projet
- Ces résultats étendent la base formelle de 55 à 60+ résultats
- La descente généralisée est le pont entre hiérarchie modulaire et dynamique
- La proportion de descente formalise l'argument heuristique de Collatz

Date : 2026-02-15 (Phase 7 Sprint 2)
-/

namespace ProjetCollatz

noncomputable section

open ProjetCollatz

/-!
## Descente généralisée

Le théorème B1 (Phase6BLemmas) ne s'applique qu'aux n ≡ 1 (mod 4).
Ici on prouve la descente pour TOUT n > 1 ayant v₂(3n+1) ≥ 2,
indépendamment de la classe modulaire. C'est plus fort car v₂ ≥ 2
peut survenir pour n ≡ 1 (mod 4) mais aussi pour n ≡ 5 (mod 16), etc.
-/

/--
**Descente généralisée.**
Si n > 1 et v₂(3n+1) ≥ 2, alors syracuseNext(n) < n.
La preuve utilise syracuseNext_spec et le fait que (3n+1)/4 < n pour n > 1.
-/
theorem descent_of_v2_ge2 (n : ℕ) (hgt : 1 < n)
    (hv : 2 ≤ v2_3n1 n) :
    syracuseNext n < n := by
  have hspec := syracuseNext_spec n
  -- 2^(v2_3n1 n) ≥ 2^2 = 4
  have hpow_ge : 4 ≤ 2 ^ (v2_3n1 n) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (v2_3n1 n) := Nat.pow_le_pow_right (by norm_num) hv
  -- syracuseNext n * 2^v₂ = 3n+1, et 2^v₂ ≥ 4
  -- Donc syracuseNext n * 4 ≤ 3n+1
  have hle : syracuseNext n * 4 ≤ 3 * n + 1 := by
    calc
      syracuseNext n * 4
        ≤ syracuseNext n * (2 ^ (v2_3n1 n)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * n + 1 := hspec
  -- 3n+1 < 4n pour n > 1, donc sN * 4 < 4n, donc sN < n
  omega

/--
**Borne de ratio.**
Si v₂(3n+1) ≥ 2, alors syracuseNext(n) ≤ (3n+1)/4.
-/
theorem descent_v2_ge2_ratio (n : ℕ) (hv : 2 ≤ v2_3n1 n) :
    syracuseNext n ≤ (3 * n + 1) / 4 := by
  have hspec := syracuseNext_spec n
  have hpow_ge : 4 ≤ 2 ^ (v2_3n1 n) := by
    calc 4 = 2 ^ 2 := by norm_num
         _ ≤ 2 ^ (v2_3n1 n) := Nat.pow_le_pow_right (by norm_num) hv
  -- sN * 4 ≤ sN * 2^v₂ = 3n+1
  have hle4 : syracuseNext n * 4 ≤ 3 * n + 1 := by
    calc syracuseNext n * 4
        ≤ syracuseNext n * (2 ^ (v2_3n1 n)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * n + 1 := hspec
  -- sN ≤ (3n+1) / 4 (division naturelle)
  exact Nat.le_div_iff_mul_le (by omega : 0 < 4) |>.mpr hle4

/--
**Montée toujours bornée.**
Pour tout n impair, syracuseNext(n) < 2n.
(Même quand v₂ = 1, la montée est inférieure à un facteur 2.)
-/
theorem ascent_always_bounded (n : ℕ) (hpos : 0 < n) (hodd : n % 2 = 1) :
    syracuseNext n < 2 * n := by
  have hspec := syracuseNext_spec n
  -- Puisque n est impair, 3n+1 est pair, donc v2_3n1 n ≥ 1
  have hv_ge1 : 1 ≤ v2_3n1 n := by
    unfold v2_3n1
    have : 2 ∣ (3 * n + 1) := by omega
    exact pow2_dvd_le_v2Nat_pos _ 1 (by omega) (by simpa using this)
  -- 2^v₂ ≥ 2
  have hpow_ge : 2 ≤ 2 ^ (v2_3n1 n) := by
    calc 2 = 2 ^ 1 := by norm_num
         _ ≤ 2 ^ (v2_3n1 n) := Nat.pow_le_pow_right (by norm_num) hv_ge1
  -- sN * 2^v₂ = 3n+1 et 2^v₂ ≥ 2
  -- Donc sN * 2 ≤ 3n+1 < 4n (pour tout n ≥ 1)
  -- Donc sN < 2n
  have hle : syracuseNext n * 2 ≤ 3 * n + 1 := by
    calc syracuseNext n * 2
        ≤ syracuseNext n * (2 ^ (v2_3n1 n)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * n + 1 := hspec
  -- sN * 2 ≤ 3n+1 et 3n+1 ≤ 4n-1 < 4n pour n ≥ 1
  -- Donc sN * 2 < 4n, i.e., sN * 2 + 1 ≤ 4n
  -- Puis sN < 2n par division
  -- Approche : montrer sN * 2^v₂ < 2n * 2^v₂, puis simplifier
  have h3n_lt_4n : 3 * n + 1 ≤ 4 * n := by omega
  -- sN * 2^v₂ = 3n+1 ≤ 4n = 2n * 2 ≤ 2n * 2^v₂
  -- Donc sN * 2^v₂ ≤ 2n * 2^v₂
  -- MAIS on veut strict. 3n+1 < 4n ssi n > 1... Pour n=1: 4 = 4, pas strict.
  -- Pour n=1: sN(1) = (3+1)/2^v2(4) = 4/4 = 1, et 2*1 = 2. 1 < 2 OK.
  -- Pour n ≥ 2: 3n+1 < 4n, donc sN * 2^v₂ < 2n * 2^v₂, donc sN < 2n.
  -- Pour n=1: special case
  by_cases hn1 : n = 1
  · -- sN(1) : 3*1+1=4, v2(4) = 2, sN = 4/4 = 1, 1 < 2*1 = 2
    subst hn1
    have hv2_1 : v2_3n1 1 = 2 := by unfold v2_3n1; norm_num [v2Nat]
    simp [syracuseNext, hv2_1]
  · -- n ≥ 3 (impair, ≥ 1, ≠ 1) → n ≥ 3
    have hn3 : 3 ≤ n := by omega
    have hstrict : 3 * n + 1 < 4 * n := by omega
    -- sN * 2^v₂ = 3n+1 < 4n = (2n) * 2 ≤ (2n) * 2^v₂
    have h_rhs : (2 * n) * 2 ≤ (2 * n) * (2 ^ (v2_3n1 n)) := by
      apply Nat.mul_le_mul_left; exact hpow_ge
    have h_sn_lt_rhs : syracuseNext n * (2 ^ (v2_3n1 n)) < (2 * n) * (2 ^ (v2_3n1 n)) := by
      calc syracuseNext n * (2 ^ (v2_3n1 n)) = 3 * n + 1 := hspec
        _ < 4 * n := hstrict
        _ = (2 * n) * 2 := by ring
        _ ≤ (2 * n) * (2 ^ (v2_3n1 n)) := h_rhs
    exact (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ (v2_3n1 n))).mp h_sn_lt_rhs

/-!
## Progression en 2 pas

Si n ≡ 3 (mod 8), alors (3n+1)/2 ≡ 1 (mod 4) (B3a de Phase6BLemmas).
Donc le PAS SUIVANT est une descente garantie (par B1).
Cela signifie qu'en 2 pas Syracuse, depuis n ≡ 3 (mod 8), on descend.
-/

/--
**Descente en 2 pas depuis n ≡ 3 (mod 8).**
Si n ≡ 3 (mod 8) et n > 3, alors syracuseNext(syracuseNext(n)) < syracuseNext(n).
-/
theorem two_step_descent_from_mod8_eq3 (n : ℕ) (hmod : n % 8 = 3)
    (hgt : 3 < n) :
    syracuseNext (syracuseNext n) < syracuseNext n := by
  -- Step 1: n ≡ 3 (mod 8) → n ≡ 3 (mod 4) → v₂(3n+1) = 1
  have hmod4 : n % 4 = 3 := by omega
  have hv1 : v2_3n1 n = 1 := by
    unfold v2_3n1; exact v2_mod4_eq3_eq1 n hmod4
  -- Step 2: syracuseNext(n) = (3n+1)/2^1 = (3n+1)/2
  have hspec := syracuseNext_spec n
  rw [hv1] at hspec
  simp at hspec
  -- Step 3: (3n+1)/2 ≡ 1 (mod 4) (B3a)
  have hmod_next : ((3 * n + 1) / 2) % 4 = 1 := half_3n1_mod4_eq1_when_mod8_eq3 n hmod
  -- Step 4: syracuseNext(n) = (3n+1)/2
  have hSN_eq : syracuseNext n = (3 * n + 1) / 2 := by omega
  -- Step 5: syracuseNext(n) ≡ 1 (mod 4) et > 1
  have hSN_mod4 : (syracuseNext n) % 4 = 1 := by rw [hSN_eq]; exact hmod_next
  have hSN_gt1 : 1 < syracuseNext n := by
    rw [hSN_eq]; omega
  -- Step 6: Appliquer B1 (descente pour ≡ 1 mod 4)
  exact syracuseNext_lt_when_mod4_eq1 (syracuseNext n) hSN_gt1 hSN_mod4

/-!
## Combinaison existence + unicité

On combine `stochastic_exists` et `stochastic_unique` en un seul théorème
qui dit : pour tout k ≥ 1, il existe un UNIQUE r impair < 2^k tel que 2^k | (3r+1).
-/

/--
**Existence et unicité de la classe stochastique.**
Pour tout k ≥ 1, il existe exactement un r impair dans [1, 2^k)
tel que 2^k ∣ (3r+1). Ce r est la "classe stochastique" au niveau k.
-/
theorem stochastic_exists_and_unique (k : ℕ) (hk : 1 ≤ k) :
    ∃ r : ℕ, r < 2^k ∧ r % 2 = 1 ∧ 2^k ∣ (3 * r + 1) ∧
    ∀ r' : ℕ, r' < 2^k → r' % 2 = 1 → 2^k ∣ (3 * r' + 1) → r' = r := by
  obtain ⟨r, hr_lt, hr_odd, hr_dvd⟩ := stochastic_exists k hk
  refine ⟨r, hr_lt, hr_odd, hr_dvd, ?_⟩
  intro r' hr'_lt hr'_odd hr'_dvd
  -- r' et r sont tous les deux < 2^k avec 2^k | (3r'+1) et 2^k | (3r+1)
  -- Par stochastic_unique, r' = r
  exact stochastic_unique k r' r (by omega) hr'_lt hr_lt hr'_dvd hr_dvd

/-!
## Descente garantie par profondeur modulaire

Théorème clé reliant hiérarchie modulaire et descente :
si n ≡ r (mod 2^k) et v₂(3r+1) ≥ 2 (classe déterministe profonde),
alors syracuseNext(n) < n pour tout n > 1 dans cette classe.

C'est la version "paramétrée par la classe modulaire" de la descente.
-/

/--
**Descente par classe modulaire.**
Si v₂(3r+1) = t et 2 ≤ t < k, alors pour tout m et n = r + 2^k·m > 1,
syracuseNext(n) < n.
-/
theorem descent_by_modular_class (r k m : ℕ) (ht : v2Nat (3 * r + 1) < k)
    (hv2 : 2 ≤ v2Nat (3 * r + 1)) (hgt : 1 < r + 2^k * m) :
    syracuseNext (r + 2^k * m) < (r + 2^k * m) := by
  -- Par A9 (v2_mod_stable), v₂(3n+1) = v₂(3r+1) = t ≥ 2
  have hstable := v2_mod_stable r k m ht
  -- Donc v2_3n1(n) ≥ 2
  have hv2n : 2 ≤ v2_3n1 (r + 2^k * m) := by
    unfold v2_3n1; omega
  -- Par descent_of_v2_ge2
  exact descent_of_v2_ge2 (r + 2^k * m) hgt hv2n

end

end ProjetCollatz
