import ProjetCollatz.SyracuseDefs

/-!
# ModularHierarchy.lean — D5: Hiérarchie modulaire de v₂(3n+1)

## Théorème principal (D5)

Pour n impair, si l'on fixe les k derniers bits (n ≡ r mod 2^k),
alors v₂(3n+1) est **entièrement déterminé** par r, SAUF pour une
unique classe résiduelle r_k (celle où 2^k | (3r+1)).

### Énoncés formalisés

- **A9** `v2_mod_stable` (Plancher déterministe) :
  Si r est impair, t = v2Nat(3r+1), et t < k, alors pour tout m :
    v2Nat(3*(r + 2^k*m) + 1) = t

- **A10** `unique_stochastic_k*` :
  Pour tout k ≥ 1, il existe un unique r impair dans [1, 2^k) tel que
  2^k ∣ (3r+1).  (C'est la seule classe non déterministe.)

### Connexion au projet
- Généralise A8 (dichotomie mod 4) : A8 est le cas k=2
- Base pour la distribution géométrique (D3)
- Clé pour comprendre pourquoi τ_256 prédit σ (la hiérarchie réduit le chaos)

### Méthodologie
- Preuve de A9 : purement arithmétique (divisibilité + contradiction)
- Preuve de A10 : par interval_cases (vérification finie pour k concrets)
- Preuve de bifurcation_dichotomy : extraction du quotient + parité (Phase 7)
-/

namespace ProjetCollatz

open ProjetCollatz

/-!
## Lemmes de calcul pour v₂ de petites valeurs
-/

-- v₂(10) = 1
private theorem v2Nat_10 : v2Nat 10 = 1 := by
  rw [v2Nat_eq_succ_of_mod2_eq0 10 (by decide) (by decide)]
  rw [v2Nat_eq_zero_of_mod2_ne0 5 (by decide)]

-- v₂(4) = 2
private theorem v2Nat_4 : v2Nat 4 = 2 := by
  rw [v2Nat_eq_succ_of_mod2_eq0 4 (by decide) (by decide)]
  rw [v2Nat_eq_succ_of_mod2_eq0 2 (by decide) (by decide)]
  rw [v2Nat_eq_zero_of_mod2_ne0 1 (by decide)]

/-!
## A9: Plancher déterministe (le cœur de D5)

Si r est impair et v₂(3r+1) = t < k, alors pour tout m,
  v₂(3(r + 2^k·m) + 1) = t

**Idée de preuve (par contradiction)** :

On montre (≥) : 2^t | (3r+1) et 2^t | 3·2^k·m, donc 2^t | (3n+1), donc v₂ ≥ t.

On montre (≤) par contradiction : si v₂(3n+1) > t, alors 2^(t+1) | (3n+1).
Or 2^(t+1) | 3·2^k·m (car t+1 ≤ k). Donc 2^(t+1) | (3n+1 - 3·2^k·m) = (3r+1).
Mais cela implique v₂(3r+1) ≥ t+1 > t, contradiction.
-/

/--
**Théorème A9 (Plancher déterministe).**
Si v₂(3r+1) < k, alors pour tout m ∈ ℕ,
  v₂(3(r + 2^k·m) + 1) = v₂(3r+1).

Autrement dit, les bits au-delà du k-ième n'affectent pas la valuation
2-adique. Le théorème est valide pour tout r ∈ ℕ (pas seulement les impairs).
Dans le contexte de Collatz, on l'applique aux r impairs uniquement.
-/
theorem v2_mod_stable (r k m : ℕ) (ht : v2Nat (3 * r + 1) < k) :
    v2Nat (3 * (r + 2^k * m) + 1) = v2Nat (3 * r + 1) := by
  set t := v2Nat (3 * r + 1) with ht_def
  -- Étape 1 : 3(r + 2^k·m) + 1 = (3r+1) + 3·2^k·m
  have hexpand : 3 * (r + 2^k * m) + 1 = (3 * r + 1) + 3 * 2^k * m := by ring
  -- Étape 2 : 2^t divise (3r+1) (par définition de v2Nat)
  have hdvd_r : 2^t ∣ (3 * r + 1) := pow2_v2Nat_dvd (3 * r + 1)
  -- Étape 3 : 2^t divise 3·2^k·m (car t ≤ k, donc 2^t | 2^k)
  have hdvd_m : 2^t ∣ (3 * 2^k * m) := by
    have hpow : 2^t ∣ 2^k := Nat.pow_dvd_pow 2 (by omega : t ≤ k)
    calc (2 : ℕ)^t ∣ 2^k := hpow
      _ ∣ 3 * 2^k := dvd_mul_left (2^k) 3
      _ ∣ 3 * 2^k * m := dvd_mul_right (3 * 2^k) m
  -- Étape 4 : Donc 2^t divise la somme, et v₂ ≥ t
  have hdvd_sum : 2^t ∣ (3 * (r + 2^k * m) + 1) := by
    rw [hexpand]; exact Nat.dvd_add hdvd_r hdvd_m
  have hge : t ≤ v2Nat (3 * (r + 2^k * m) + 1) := by
    exact pow2_dvd_le_v2Nat_pos _ _ (by omega) hdvd_sum
  -- Étape 5 : Montrer v₂ ≤ t (par contradiction)
  -- Si v₂ > t, alors 2^(t+1) | (3n+1), et 2^(t+1) | 3·2^k·m,
  -- donc 2^(t+1) | (3r+1), contradiction.
  by_contra hne
  push_neg at hne
  -- hne : v₂(3n+1) ≠ t, et hge : t ≤ v₂(3n+1), donc t+1 ≤ v₂(3n+1)
  have hgt : t + 1 ≤ v2Nat (3 * (r + 2^k * m) + 1) := by omega
  -- 2^(t+1) | (3n+1)
  have h_pow_dvd_n : 2^(t+1) ∣ (3 * (r + 2^k * m) + 1) := by
    have h_v2_dvd := pow2_v2Nat_dvd (3 * (r + 2^k * m) + 1)
    -- 2^(t+1) | 2^v₂(...) car t+1 ≤ v₂(...)
    have h_pow_le : 2^(t+1) ∣ 2^(v2Nat (3 * (r + 2^k * m) + 1)) :=
      Nat.pow_dvd_pow 2 hgt
    exact Nat.dvd_trans h_pow_le h_v2_dvd
  -- 2^(t+1) | 3·2^k·m  (car t+1 ≤ k)
  have h_pow_dvd_m : 2^(t+1) ∣ (3 * 2^k * m) := by
    have hpow : 2^(t+1) ∣ 2^k := Nat.pow_dvd_pow 2 (by omega : t + 1 ≤ k)
    calc (2 : ℕ)^(t+1) ∣ 2^k := hpow
      _ ∣ 3 * 2^k := dvd_mul_left (2^k) 3
      _ ∣ 3 * 2^k * m := dvd_mul_right (3 * 2^k) m
  -- Donc 2^(t+1) | (3r+1)
  -- On utilise Nat.dvd_sub : d | a → d | b → d | (a - b)
  -- Ici a = (3r+1) + 3·2^k·m, b = 3·2^k·m, a - b = (3r+1)
  have h_pow_dvd_r : 2^(t+1) ∣ (3 * r + 1) := by
    rw [hexpand] at h_pow_dvd_n
    -- Nat.dvd_sub : d | m → d | n → d | (m - n)  (soustraction tronquée ℕ)
    -- Puis (a + b) - b = a en ℕ (Nat.add_sub_cancel)
    have h_sub := Nat.dvd_sub h_pow_dvd_n h_pow_dvd_m
    rwa [Nat.add_sub_cancel] at h_sub
  -- Donc v₂(3r+1) ≥ t+1
  have hge_t1 : t + 1 ≤ v2Nat (3 * r + 1) := by
    exact pow2_dvd_le_v2Nat_pos _ _ (by omega) h_pow_dvd_r
  -- Contradiction : t+1 ≤ t
  omega


/-!
## A10: Unicité de la classe stochastique

Pour chaque k, il y a exactement un r impair dans [0, 2^k) tel que
2^k ∣ (3r+1). C'est le r pour lequel v₂(3r+1) ≥ k.

L'argument théorique est simple : 3 est inversible mod 2^k, donc
3r ≡ -1 (mod 2^k) a une solution unique mod 2^k.

On vérifie pour k=1 à 6 par interval_cases.
-/

-- k=1: r=1 est l'unique impair < 2 avec 2¹ | (3r+1)
theorem unique_stochastic_k1 :
    ∀ r : ℕ, r % 2 = 1 → r < 2 → (2^1 ∣ (3 * r + 1) ↔ r = 1) := by
  intro r hr hlt; constructor
  · intro _; omega
  · intro heq; subst heq; norm_num

-- k=2: r=1 est l'unique impair < 4 avec 2² | (3r+1)
theorem unique_stochastic_k2 :
    ∀ r : ℕ, r % 2 = 1 → r < 4 → (2^2 ∣ (3 * r + 1) ↔ r = 1) := by
  intro r hr hlt
  interval_cases r <;> simp_all

-- k=3: r=5 est l'unique impair < 8 avec 2³ | (3r+1)
theorem unique_stochastic_k3 :
    ∀ r : ℕ, r % 2 = 1 → r < 8 → (2^3 ∣ (3 * r + 1) ↔ r = 5) := by
  intro r hr hlt
  interval_cases r <;> simp_all

-- k=4: r=5 est l'unique impair < 16 avec 2⁴ | (3r+1)
theorem unique_stochastic_k4 :
    ∀ r : ℕ, r % 2 = 1 → r < 16 → (2^4 ∣ (3 * r + 1) ↔ r = 5) := by
  intro r hr hlt
  interval_cases r <;> simp_all

-- k=5: r=21 est l'unique impair < 32 avec 2⁵ | (3r+1)
theorem unique_stochastic_k5 :
    ∀ r : ℕ, r % 2 = 1 → r < 32 → (2^5 ∣ (3 * r + 1) ↔ r = 21) := by
  intro r hr hlt
  interval_cases r <;> simp_all

-- k=6: r=21 est l'unique impair < 64 avec 2⁶ | (3r+1)
theorem unique_stochastic_k6 :
    ∀ r : ℕ, r % 2 = 1 → r < 64 → (2^6 ∣ (3 * r + 1) ↔ r = 21) := by
  intro r hr hlt
  interval_cases r <;> simp_all


/-!
## A10 général : Unicité de la classe stochastique (∀ k)

L'argument théorique : 3 est inversible mod 2^k (car gcd(3,2)=1),
donc 3r ≡ -1 (mod 2^k) a au plus une solution mod 2^k.

### Unicité (théorème principal)
Si 2^k | (3a+1) et 2^k | (3b+1) et a,b < 2^k, alors a = b.

### Coprimarité
Nat.Coprime 3 (2^k) est le lemme clé, prouvé via gcd(3,2)=1 + coprime_pow_right_iff.
-/

-- 3 et 2^k sont copremiers pour tout k ≥ 1
theorem coprime_three_pow2 (k : ℕ) (hk : 0 < k) : Nat.Coprime 3 (2^k) := by
  rw [Nat.coprime_comm, Nat.coprime_pow_left_iff hk]
  decide

-- Unicité : si 2^k | (3a+1) et 2^k | (3b+1), avec a,b < 2^k, alors a = b
theorem stochastic_unique (k a b : ℕ) (hk : 0 < k)
    (ha_lt : a < 2^k) (hb_lt : b < 2^k)
    (ha_dvd : 2^k ∣ (3 * a + 1)) (hb_dvd : 2^k ∣ (3 * b + 1)) :
    a = b := by
  -- De 2^k | (3a+1) et 2^k | (3b+1), on tire 2^k | (3a+1 - (3b+1)) = 3(a-b)
  -- En ℕ, on distingue les cas a ≥ b et a < b.
  by_cases hab : a ≥ b
  · -- Cas a ≥ b : montrer a = b
    have h3 : 2^k ∣ (3 * a + 1 - (3 * b + 1)) := Nat.dvd_sub ha_dvd hb_dvd
    have h_simp : 3 * a + 1 - (3 * b + 1) = 3 * (a - b) := by omega
    rw [h_simp] at h3
    -- Coprimarité : gcd(2^k, 3) = 1, donc 2^k | (a - b)
    -- On utilise dvd_mul_left pour réécrire 3 * (a-b) = (a-b) * 3
    rw [show 3 * (a - b) = (a - b) * 3 from by ring] at h3
    have hcop : Nat.Coprime (2^k) 3 := (coprime_three_pow2 k hk).symm
    rw [hcop.dvd_mul_right] at h3
    -- a - b < 2^k et 2^k | (a-b), donc a - b = 0
    have h_zero : a - b = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega
  · -- Cas a < b : montrer b = a par symétrie
    push_neg at hab
    have h3 : 2^k ∣ (3 * b + 1 - (3 * a + 1)) := Nat.dvd_sub hb_dvd ha_dvd
    have h_simp : 3 * b + 1 - (3 * a + 1) = 3 * (b - a) := by omega
    rw [h_simp] at h3
    rw [show 3 * (b - a) = (b - a) * 3 from by ring] at h3
    have hcop : Nat.Coprime (2^k) 3 := (coprime_three_pow2 k hk).symm
    rw [hcop.dvd_mul_right] at h3
    have h_zero : b - a = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega


/-!
## Corollaire : A8 comme cas particulier de A9

Le théorème A8 (dichotomie mod 4) est le cas k=2 de A9.
On retrouve les deux parties de A8 directement depuis A9.
-/

-- n ≡ 3 (mod 4) → v₂(3n+1) = 1  (retrouvé par A9 avec r=3, k=2)
theorem v2_mod4_eq3_from_A9 (n : ℕ) (hmod : n % 4 = 3) :
    v2Nat (3 * n + 1) = 1 := by
  -- Division euclidienne : n = 4*(n/4) + n%4, puis n%4 = 3
  have hdiv := Nat.div_add_mod n 4
  set m := n / 4
  -- n = 4*m + 3 = 3 + 4*m (par commutativité)
  have hn : n = 3 + 4 * m := by omega
  rw [hn]
  -- v₂(3*3+1) = v₂(10) = 1 (par déroulage)
  have hbase : v2Nat (3 * 3 + 1) = 1 := by
    show v2Nat 10 = 1; exact v2Nat_10
  -- v₂(3*3+1) = 1 < 2 = k, donc A9 s'applique
  have hlt : v2Nat (3 * 3 + 1) < 2 := by omega
  -- A9 : v₂(3*(3 + 2^2*m) + 1) = v₂(3*3+1)
  have h := v2_mod_stable 3 2 m hlt
  simp only [show (2:ℕ)^2 = 4 from by norm_num] at h
  -- Chaîner : v₂(3*(3+4*m)+1) = v₂(3*3+1) = 1
  rw [h, hbase]

-- n ≡ 1 (mod 4) → v₂(3n+1) ≥ 2  (retrouvé par A9 : r=1 donne v₂(4)=2)
theorem v2_mod4_eq1_from_A9 (n : ℕ) (hmod : n % 4 = 1) :
    2 ≤ v2Nat (3 * n + 1) := by
  -- Division euclidienne : n = 4*(n/4) + n%4, puis n%4 = 1
  have hdiv := Nat.div_add_mod n 4
  set m := n / 4
  have hn : n = 1 + 4 * m := by omega
  rw [hn]
  -- Divisibilité directe : 4 | (3*(1 + 4*m) + 1) car 3 + 12m + 1 = 4 + 12m
  have h4dvd : 4 ∣ (3 * (1 + 4 * m) + 1) := by omega
  have h_ne : 3 * (1 + 4 * m) + 1 ≠ 0 := by omega
  have h2pow : 2^2 ∣ (3 * (1 + 4 * m) + 1) := by
    show 4 ∣ _; exact h4dvd
  exact pow2_dvd_le_v2Nat_pos _ 2 h_ne h2pow

/-!
## Lemme auxiliaire : maximalité stricte de v₂

Si v₂(n) = k, alors 2^(k+1) ne divise PAS n.
C'est la contraposée de pow2_dvd_le_v2Nat_pos.
Ce lemme est la clé technique pour fermer bifurcation_dichotomy.
-/

/-- Si v₂(n) = k, alors ¬(2^(k+1) ∣ n). -/
theorem not_pow_succ_dvd_of_v2_eq (n k : ℕ) (hn : n ≠ 0)
    (hv : v2Nat n = k) : ¬(2^(k+1) ∣ n) := by
  intro h
  have hle : k + 1 ≤ v2Nat n := pow2_dvd_le_v2Nat_pos n (k+1) hn h
  omega

/-!
## D3 : Lemme de bifurcation (base de la distribution géométrique)

Si 2^k | (3r+1), alors parmi les deux extensions mod 2^(k+1) :
- r₀ = r (inchangé) : 2^(k+1) | (3r₀+1) OU v₂(3r₀+1) = k
- r₁ = r + 2^k  : v₂(3r₁+1) = k OU 2^(k+1) | (3r₁+1)

Plus précisément, exactement l'une des deux satisfait 2^(k+1) | (3r+1)
(c'est la classe stochastique au niveau k+1) et l'autre a v₂ = k exactement
(c'est une classe déterministe au niveau k+1 avec valuation = k).

Ce lemme est le mécanisme qui crée la distribution géométrique P(v₂ = j) = 1/2.
-/

/--
**Lemme de bifurcation** : si 2^k | (3r+1), alors
  v₂(3(r + 2^k) + 1) ≥ k.
(C'est trivial car 3(r+2^k)+1 = (3r+1) + 3·2^k, et 2^k divise les deux termes.)

La partie non-triviale est que EXACTEMENT un des deux (r et r+2^k)
satisfait v₂ = k et l'autre v₂ ≥ k+1.
-/
theorem bifurcation_ge_k (r k : ℕ) (hdvd : 2^k ∣ (3 * r + 1)) :
    k ≤ v2Nat (3 * (r + 2^k) + 1) := by
  -- 3*(r + 2^k) + 1 = (3*r + 1) + 3 * 2^k
  have hexp : 3 * (r + 2^k) + 1 = (3 * r + 1) + 3 * 2^k := by ring
  -- 2^k divise les deux termes
  have hdvd2 : 2^k ∣ (3 * 2^k) := by
    exact dvd_mul_left (2^k) 3
  have hdvd_sum : 2^k ∣ (3 * (r + 2^k) + 1) := by
    rw [hexp]; exact Nat.dvd_add hdvd hdvd2
  -- Donc v₂ ≥ k
  exact pow2_dvd_le_v2Nat_pos _ _ (by omega) hdvd_sum

/--
**Lemme de dichotomie** : si 2^k | (3r+1), alors exactement l'un de
v₂(3r+1) = k ou v₂(3(r+2^k)+1) = k est vrai.

En d'autres termes, parmi les deux sous-classes mod 2^(k+1), une a v₂ = k
(classe déterministe) et l'autre a v₂ ≥ k+1 (reste stochastique).
-/
theorem bifurcation_dichotomy (r k : ℕ) (hdvd : 2^k ∣ (3 * r + 1))
    (hge_r : k ≤ v2Nat (3 * r + 1)) :
    (v2Nat (3 * r + 1) = k ∧ k + 1 ≤ v2Nat (3 * (r + 2^k) + 1)) ∨
    (k + 1 ≤ v2Nat (3 * r + 1) ∧ v2Nat (3 * (r + 2^k) + 1) = k) := by
  -- Cas 1 : v₂(3r+1) = k
  -- Cas 2 : v₂(3r+1) > k, i.e., v₂(3r+1) ≥ k+1
  by_cases h : v2Nat (3 * r + 1) = k
  · -- Cas v₂(3r+1) = k : montrer v₂(3(r+2^k)+1) ≥ k+1
    left; constructor
    · exact h
    · -- 2^(k+1) | (3(r+2^k)+1) ↔ 2^(k+1) | (3r+1) + 3*2^k
      -- On sait v₂(3r+1) = k, donc 2^k ∥ (3r+1) (divise exactement)
      -- 3(r+2^k)+1 = (3r+1) + 3·2^k
      -- 2^k | (3r+1) et 2^k | 3·2^k, mais 2^(k+1) ∤ (3r+1) (car v₂=k)
      -- Reste à montrer : 3·2^k a exactement v₂ = k (car 3 est impair)
      -- Donc (3r+1) + 3·2^k = 2^k·(q₁ + 3) avec q₁ impair
      -- q₁ + 3 est pair, donc 2^(k+1) | somme
      have hexp : 3 * (r + 2^k) + 1 = (3 * r + 1) + 3 * 2^k := by ring
      -- Stratégie : montrer 2^(k+1) | (3(r+2^k)+1) via v2_mod_stable-style
      -- On a v₂(3r+1) = k, donc 2^k | (3r+1) et ¬(2^(k+1) | (3r+1))
      -- Posons A = 3r+1, B = 3·2^k. On veut v₂(A+B) ≥ k+1.
      -- A = 2^k·q₁ (q₁ impair car v₂=k), B = 2^k·3 (3 impair)
      -- A+B = 2^k·(q₁+3), et q₁+3 est pair, donc 2^(k+1) | A+B
      set A := 3 * r + 1
      set q := A / 2^k
      -- 2^k > 0
      have hpow_pos : 0 < 2^k := Nat.pos_of_ne_zero (by positivity)
      -- A = 2^k * q (division exacte car 2^k | A)
      have hA_eq : A = 2^k * q := (Nat.mul_div_cancel' hdvd).symm
      -- q est impair : si q pair, alors 2^(k+1) | A, contradiction avec v₂(A) = k
      have hq_odd : q % 2 = 1 := by
        by_contra hq_even
        push_neg at hq_even
        have hq_mod := Nat.mod_two_eq_zero_or_one q
        have hq0 : q % 2 = 0 := by omega
        have h2q : 2 ∣ q := Nat.dvd_of_mod_eq_zero hq0
        obtain ⟨q', hq'⟩ := h2q
        have hA2 : A = 2^(k+1) * q' := by
          rw [hA_eq, hq']; ring
        have h_dvd_k1 : 2^(k+1) ∣ A := ⟨q', hA2⟩
        exact not_pow_succ_dvd_of_v2_eq A k (by omega) h h_dvd_k1
      -- 3(r+2^k)+1 = A + 3·2^k = 2^k·q + 2^k·3 = 2^k·(q+3)
      have hsum : 3 * (r + 2^k) + 1 = 2^k * (q + 3) := by
        rw [hexp, hA_eq]; ring
      -- q+3 est pair (car q impair + 3 impair = pair)
      have hqp_even : (q + 3) % 2 = 0 := by omega
      have h2_dvd_qp : 2 ∣ (q + 3) := Nat.dvd_of_mod_eq_zero hqp_even
      obtain ⟨s, hs⟩ := h2_dvd_qp
      -- Donc 2^(k+1) | 2^k·(q+3)
      have h_dvd : 2^(k+1) ∣ (3 * (r + 2^k) + 1) := by
        rw [hsum, hs]; ring_nf; exact ⟨s, by ring⟩
      exact pow2_dvd_le_v2Nat_pos _ _ (by omega) h_dvd
  · -- Cas v₂(3r+1) > k : montrer v₂(3(r+2^k)+1) = k
    right; constructor
    · omega
    · -- v₂(3r+1) ≥ k+1, donc 2^(k+1) | (3r+1)
      -- 3(r+2^k)+1 = (3r+1) + 3·2^k
      -- On veut montrer v₂(3(r+2^k)+1) = k, i.e., ≤ k ET ≥ k.
      -- ≥ k vient de bifurcation_ge_k. Pour ≤ k, on montre ¬(2^(k+1) | résultat).
      have hexp : 3 * (r + 2^k) + 1 = (3 * r + 1) + 3 * 2^k := by ring
      -- On a déjà k ≤ v₂(3(r+2^k)+1) par bifurcation_ge_k
      have hge_k := bifurcation_ge_k r k hdvd
      -- Montrons v₂ ≤ k par contradiction : si v₂ ≥ k+1, alors 2^(k+1) | somme
      by_contra hne
      push_neg at hne
      -- hne : v₂(...) ≠ k, combiné avec hge_k : k ≤ v₂(...), donne k+1 ≤ v₂(...)
      have hgt : k + 1 ≤ v2Nat (3 * (r + 2^k) + 1) := by omega
      -- Donc 2^(k+1) | 3(r+2^k)+1
      have h_dvd_sum : 2^(k+1) ∣ (3 * (r + 2^k) + 1) := by
        exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hgt) (pow2_v2Nat_dvd _)
      -- Et 2^(k+1) | (3r+1) car v₂(3r+1) ≥ k+1 (de h et hge_r, soit omega)
      have h_v2_ge : k + 1 ≤ v2Nat (3 * r + 1) := by omega
      have h_dvd_A : 2^(k+1) ∣ (3 * r + 1) := by
        exact Nat.dvd_trans (Nat.pow_dvd_pow 2 h_v2_ge) (pow2_v2Nat_dvd _)
      -- Donc 2^(k+1) | ((3r+1) + 3·2^k) - (3r+1) = 3·2^k
      rw [hexp] at h_dvd_sum
      have h_dvd_3pk : 2^(k+1) ∣ (3 * 2^k) := by
        have hsub := Nat.dvd_sub h_dvd_sum h_dvd_A
        have : (3 * r + 1 + 3 * 2 ^ k) - (3 * r + 1) = 3 * 2 ^ k := by omega
        rwa [this] at hsub
      -- Mais 2^(k+1) = 2·2^k, et 3·2^k = 2^k·3, avec 3 impair
      -- Donc 2^(k+1) | 3·2^k implique 2 | 3, contradiction
      have : 2 ∣ 3 := by
        have hpk1 : 2^(k+1) = 2^k * 2 := by ring
        rw [hpk1] at h_dvd_3pk
        have h3_comm : 3 * 2^k = 2^k * 3 := by ring
        rw [h3_comm] at h_dvd_3pk
        exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (by positivity))).mp h_dvd_3pk
      omega


/-!
## Existence de la classe stochastique (∀ k ≥ 1)

Pour tout k ≥ 1, il existe un r impair dans [1, 2^k) tel que 2^k ∣ (3r+1).

**Stratégie** : récurrence sur k en utilisant `bifurcation_dichotomy`.
- Base : k=1, témoin r=1 (impair, < 2, et 2 | 4 = 3·1+1)
- Pas : si on a r < 2^k impair avec 2^k | (3r+1), alors par
  `bifurcation_dichotomy`, soit 2^(k+1) | (3r+1) (témoin r),
  soit 2^(k+1) | (3(r+2^k)+1) (témoin r+2^k, impair car pair+impair).

Cette approche évite la formule close (2^(k+k%2)-1)/3 et sa
division par 3, et réutilise directement le théorème de bifurcation.
-/

/-- Lemme auxiliaire : r + 2^k est impair si r est impair et k ≥ 1. -/
theorem odd_add_pow2 (r k : ℕ) (hr : r % 2 = 1) (hk : 1 ≤ k) :
    (r + 2^k) % 2 = 1 := by
  have h2k : 2^k % 2 = 0 := by
    have h2dvd : (2 : ℕ) ∣ 2^k := by
      calc (2 : ℕ) = 2^1 := by norm_num
        _ ∣ 2^k := Nat.pow_dvd_pow 2 hk
    exact Nat.mod_eq_zero_of_dvd h2dvd
  omega

/--
**Théorème d'existence de la classe stochastique.**
Pour tout k ≥ 1, il existe r < 2^k impair tel que 2^k ∣ (3r+1).
Preuve par récurrence sur k, utilisant `bifurcation_dichotomy` au pas inductif.
-/
theorem stochastic_exists : ∀ k : ℕ, 1 ≤ k →
    ∃ r : ℕ, r < 2^k ∧ r % 2 = 1 ∧ 2^k ∣ (3 * r + 1) := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · -- Base : k = 1 (i.e., n = 0)
      subst hn
      exact ⟨1, by norm_num, by norm_num, ⟨2, by norm_num⟩⟩
    · -- Pas inductif : k = n+1, on a l'hypothèse pour n ≥ 1
      have hn_ge : 1 ≤ n := by omega
      obtain ⟨r, hr_lt, hr_odd, hr_dvd⟩ := ih hn_ge
      have hge_r : n ≤ v2Nat (3 * r + 1) :=
        pow2_dvd_le_v2Nat_pos _ _ (by omega) hr_dvd
      have hbif := bifurcation_dichotomy r n hr_dvd hge_r
      cases hbif with
      | inl h =>
        refine ⟨r + 2^n, ?_, ?_, ?_⟩
        · -- r + 2^n < 2^(n+1)
          have : 2^(n+1) = 2 * 2^n := by ring
          omega
        · exact odd_add_pow2 r n hr_odd hn_ge
        · exact Nat.dvd_trans (Nat.pow_dvd_pow 2 h.2) (pow2_v2Nat_dvd _)
      | inr h =>
        refine ⟨r, ?_, hr_odd, ?_⟩
        · have : 2^n ≤ 2^(n+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        · exact Nat.dvd_trans (Nat.pow_dvd_pow 2 h.1) (pow2_v2Nat_dvd _)

end ProjetCollatz
