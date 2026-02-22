import ProjetCollatz.Phase9CascadeInduction

/-!
# Phase9DescentChain.lean — Chaîne complète de descente

## Résultat principal

Pour tout n ≡ 7 mod 8 avec au moins k trailing ones (k ≥ 3) :

  cascade (k-3 pas) → nSeq(n, k-3) ≡ 7 mod 8 (3 trailing ones)
  → nSeq(n, k-2) ≡ 3 mod 8 (transition classe 7 → 3)
  → nSeq(n, k-1) ∈ {1, 5} mod 8 (transition classe 3 → {1,5})
  → descente relative (v2 ≥ 2 pour classe 1, v2 ≥ 3 pour classe 5)

Ce fichier prouve la chaîne complète :
1. cascade_to_class7 (déjà prouvé dans Phase9CascadeInduction)
2. class7_3trailing_to_class3 : n ≡ 7 mod 16 → sN(n) ≡ 3 mod 8
3. class3_to_class1_or_5 : n ≡ 3 mod 8 → sN(n) ∈ {1, 5} mod 8
4. full_escape_chain : enchainement cascade → classe 3 → {1,5}

Date : 2026-02-15 (Phase 9 Sprint 4)
-/

namespace ProjetCollatz

noncomputable section

open ProjetCollatz

/-!
## 1. Classe 7 avec 3 trailing ones → classe 3

Si n ≡ 7 mod 16 (= 3 trailing ones, le bit 3 est 0), alors sN(n) ≡ 3 mod 8.
C'est déjà prouvé dans Phase9BinaryCascade.lean comme transition_class7_mod16_to3.
On fournit ici une version plus explicite.
-/

/-- n ≡ 7 mod 8 ET n a exactement 3 trailing ones → n ≡ 7 mod 16 -/
theorem class7_3trailing_is_mod16_7 (n : ℕ) (h7 : n % 8 = 7) (hk3 : n % 16 ≠ 15) :
    n % 16 = 7 := by
  omega

/-!
## 2. Chaîne complète : cascade → classe 7 (3 trailing) → classe 3

Après k-3 pas de cascade, nSeq(n, k-3) a exactement 3 trailing ones
(c'est le résidu de cascade_reaches_class7).
Au pas k-2, on sort vers classe 3.
-/

/-- Après la cascade de k-3 pas, le résultat a 3 trailing ones.
    Si de plus nSeq(n, k-3) ≢ 15 mod 16 (le bit 3 est 0),
    alors nSeq(n, k-2) ≡ 3 mod 8. -/
theorem cascade_then_escape (n k : ℕ) (hk : 3 ≤ k)
    (hmod : n % 2^k = 2^k - 1)
    (hbit : nSeq n (k - 3) % 16 ≠ 15) :
    nSeq n (k - 2) % 8 = 3 := by
  -- nSeq n (k-2) = syracuseNext (nSeq n (k-3))
  have hstep : nSeq n (k - 2) = syracuseNext (nSeq n (k - 3)) := by
    have : k - 2 = (k - 3) + 1 := by omega
    rw [this]
    simp [nSeq]
  rw [hstep]
  -- nSeq n (k-3) % 8 = 7 par cascade_reaches_class7
  have h7 := cascade_reaches_class7 n k hk hmod
  -- nSeq n (k-3) % 16 = 7 (par h7 et hbit)
  have h16 : nSeq n (k - 3) % 16 = 7 := by omega
  -- Utiliser transition_class7_mod16_to3
  exact transition_class7_mod16_to3 (nSeq n (k - 3)) h16 (by omega)

/-!
## 3. Classe 3 → {1, 5} mod 8

Quand n ≡ 3 mod 8, sN(n) est toujours impair et v2(3n+1) = 1.
sN(n) = (3n+1)/2. On a (3n+1)/2 ≡ 5 mod 4 quand n ≡ 3 mod 8,
donc sN(n) % 8 ∈ {1, 5}.

Plus précisément :
- n ≡ 3 mod 16 → sN(n) ≡ 5 mod 8
- n ≡ 11 mod 16 → sN(n) ≡ 1 mod 8
-/

/-- n ≡ 3 mod 8 → sN(n) % 4 = 1 (impair, pas classe 3 ou 7) -/
theorem class3_to_odd_not37 (n : ℕ) (h3 : n % 8 = 3) (hn : 1 < n) :
    syracuseNext n % 4 = 1 := by
  have hv1 : v2_3n1 n = 1 := v2_mod4_eq3_eq1 n (by omega)
  have hspec := syracuseNext_spec n
  rw [hv1] at hspec
  simp at hspec
  -- hspec : syracuseNext n * 2 = 3 * n + 1
  -- n % 8 = 3 signifie n = 8q + 3
  -- 3n + 1 = 24q + 10 = 2 * (12q + 5)
  -- sN(n) = 12q + 5
  -- sN(n) % 4 = (12q + 5) % 4 = 1
  omega

/-- n ≡ 3 mod 8 → sN(n) % 8 ∈ {1, 5} -/
theorem class3_to_class1_or_5 (n : ℕ) (h3 : n % 8 = 3) (hn : 1 < n) :
    syracuseNext n % 8 = 1 ∨ syracuseNext n % 8 = 5 := by
  have hmod4 := class3_to_odd_not37 n h3 hn
  -- sN(n) % 4 = 1 signifie sN(n) ≡ 1 ou 5 mod 8
  omega

/-!
## 4. Descente depuis classes {1, 5}

Classes 1 et 5 ont v2 ≥ 2, ce qui garantit la descente relative.
Ces résultats sont déjà prouvés dans Phase7Sprint3.lean et Phase7Theorems.lean :
- v2_mod8_eq1 : n ≡ 1 mod 8 → v2(3n+1) = 2
- v2_mod8_eq5_ge3 : n ≡ 5 mod 8 → v2(3n+1) ≥ 3
- descent_of_v2_ge2 : v2(3n+1) ≥ 2 → sN(n) < n

La chaîne complète est donc :
  cascade k-3 pas → classe 7 (3 trailing) → classe 3 → {1,5} → descente
-/

/-- Théorème de chaîne : n ≡ 3 mod 8 → classes {1,5} donnent descente relative -/
theorem chain_class3_descent (n : ℕ) (h3 : n % 8 = 3) (hn : 1 < n)
    (hn2 : 1 < syracuseNext n) :
    ∃ (m : ℕ), m = syracuseNext n ∧ (m % 8 = 1 ∨ m % 8 = 5) := by
  exact ⟨syracuseNext n, rfl, class3_to_class1_or_5 n h3 hn⟩

/-!
## 5. Descente relative depuis {1, 5}

Le maillon final : si m ∈ {1, 5} mod 8 et m > 1, alors sN(m) < m.
C'est un corollaire direct de descent_of_v2_ge2 + v2_mod8_eq1 + v2_mod8_eq5_ge3.
-/

/-- Classe 1 mod 8 → descente relative (sN(n) < n) -/
theorem descent_class1 (n : ℕ) (h1 : n % 8 = 1) (hgt : 1 < n) :
    syracuseNext n < n := by
  have hv2 : v2_3n1 n = 2 := v2_mod8_eq1 n h1
  exact descent_of_v2_ge2 n hgt (by omega)

/-- Classe 5 mod 8 → descente relative (sN(n) < n) -/
theorem descent_class5 (n : ℕ) (h5 : n % 8 = 5) (hgt : 1 < n) :
    syracuseNext n < n := by
  have hv2 : 3 ≤ v2_3n1 n := v2_mod8_eq5_ge3 n h5
  exact descent_of_v2_ge2 n hgt (by omega)

/-- Classes {1, 5} mod 8 → descente relative (sN(n) < n) -/
theorem descent_class1_or_5 (n : ℕ) (h15 : n % 8 = 1 ∨ n % 8 = 5) (hgt : 1 < n) :
    syracuseNext n < n := by
  rcases h15 with h1 | h5
  · exact descent_class1 n h1 hgt
  · exact descent_class5 n h5 hgt

/-!
## 6. Théorème final : chaîne complète cascade → classe 3 → descente en 2 pas

Pour n ≡ 3 mod 8, n > 1, sN(n) > 1 :
  sN(sN(n)) < sN(n)

C'est-à-dire : après la sortie de cascade (classe 3), en exactement 2 pas Syracuse,
le deuxième pas descend sous le premier.
-/

/-- Chaîne complète : classe 3 → {1,5} → descente (sN(sN(n)) < sN(n)) -/
theorem class3_two_step_descent (n : ℕ) (h3 : n % 8 = 3) (hn : 1 < n)
    (hSN : 1 < syracuseNext n) :
    syracuseNext (syracuseNext n) < syracuseNext n := by
  have h15 := class3_to_class1_or_5 n h3 hn
  exact descent_class1_or_5 (syracuseNext n) h15 hSN

/-!
## 7. Cascade stops : n avec EXACTEMENT k trailing ones

Si n a exactement k trailing ones (pas k+1), alors après k-3 pas de cascade,
le résultat a exactement 3 trailing ones, donc % 16 ≠ 15.
Cela élimine la condition `hbit` du théorème cascade_then_escape.

La preuve directe utilise le fait que cascade_iterate est "tight" :
nSeq(n,j) % 2^(k-j) = 2^(k-j) - 1, et si n % 2^(k+1) ≠ 2^(k+1)-1,
alors on ne peut pas avoir nSeq(n, k-3) % 2^4 = 15.
-/

/-- La cascade avec k+1 trailing ones implique 4 trailing ones au pas k-3.
    Contraposée : si n a exactement k trailing ones (pas k+1),
    alors nSeq(n, k-3) n'a PAS 4 trailing ones.

    Note : ce théorème utilise cascade_iterate dans le sens direct.
    Si n % 2^(k+1) = 2^(k+1)-1 (k+1 trailing ones),
    alors nSeq(n, k-3) % 2^4 = 15 (4 trailing ones).
    Contraposée : si nSeq(n, k-3) % 16 ≠ 15, pas de conclusion.
    Mais si n % 2^(k+1) ≠ 2^(k+1)-1, on ne peut PAS appliquer cascade_iterate
    avec k' = k+1, donc la conclusion % 16 = 15 n'est PAS garantie. -/
theorem cascade_kplus1_implies_4trailing (n k : ℕ) (hk : 3 ≤ k)
    (hmod_kp1 : n % 2^(k+1) = 2^(k+1) - 1) :
    nSeq n (k - 3) % 16 = 15 := by
  -- k+1 ≥ 4, so we can apply cascade_iterate with k' = k+1
  have hk1 : 3 ≤ k + 1 := by omega
  have hiter := cascade_iterate n (k+1) (k-3) hk1 (by omega) hmod_kp1
  -- (k+1) - (k-3) = 4
  have heq : k + 1 - (k - 3) = 4 := by omega
  rw [heq] at hiter
  norm_num at hiter
  exact hiter

/-- Contraposée : si nSeq(n, k-3) % 16 ≠ 15, alors n n'a PAS k+1 trailing ones -/
theorem no_4trailing_implies_exact_k (n k : ℕ) (hk : 3 ≤ k)
    (hbit : nSeq n (k - 3) % 16 ≠ 15) :
    n % 2^(k+1) ≠ 2^(k+1) - 1 := by
  intro hmod_kp1
  exact hbit (cascade_kplus1_implies_4trailing n k hk hmod_kp1)

/-- Lemme clé : propagation du quotient pair dans la cascade.
    Si n % 2^k = 2^k - 1 (k trailing ones), k ≥ 3, et le quotient q = n / 2^k
    est pair (ce qui signifie n % 2^(k+1) ≠ 2^(k+1)-1),
    alors sN(n) % 2^k = 2^(k-1) - 1 (EXACTEMENT k-1 trailing ones, pas k).

    Preuve : cascade_formula donne sN(n) = 3*2^(k-1)*q + (3*2^(k-1) - 1).
    = 2^(k-1) * (3q + 2) + (2^(k-1) - 1).
    Donc sN(n) % 2^(k-1) = 2^(k-1) - 1 (k-1 trailing ones).
    Et sN(n) % 2^k = ((3q+2) % 2) * 2^(k-1) + (2^(k-1) - 1).
    Si q est pair, (3q+2) % 2 = 0, donc sN(n) % 2^k = 2^(k-1) - 1 < 2^k - 1. -/
theorem cascade_tight_step (n k : ℕ) (hk : 2 ≤ k)
    (hmod : n % 2^k = 2^k - 1)
    (hqpair : (n / 2^k) % 2 = 0) :
    syracuseNext n % 2^k ≠ 2^k - 1 := by
  -- n = 2^k * q + (2^k - 1) avec q pair
  set q := n / 2^k
  have hn_eq : n = 2^k * q + (2^k - 1) := by
    have := (Nat.div_add_mod n (2^k)).symm
    rw [hmod] at this
    exact this
  -- sN(n) = 3*2^(k-1)*q + (3*2^(k-1) - 1) par cascade_formula
  have hk3 : 2 ≤ k := hk
  conv_lhs => rw [hn_eq]
  rw [cascade_formula k q hk3]
  -- But : (3*2^(k-1)*q + (3*2^(k-1) - 1)) % 2^k ≠ 2^k - 1
  -- = (2^(k-1) * (3q + 2) + (2^(k-1) - 1)) % 2^k
  -- Avec q pair (q = 2q'), 3q+2 = 6q'+2 = 2(3q'+1), pair.
  -- Donc (3q+2) % 2 = 0, et le résultat % 2^k = 2^(k-1) - 1 < 2^k - 1.
  intro heq
  -- heq : (3*2^(k-1)*q + (3*2^(k-1) - 1)) % 2^k = 2^k - 1
  -- Cela signifie que la valeur mod 2^k = 2^k - 1, i.e., k trailing ones
  -- Mais q est pair, donc on peut montrer la contradiction.
  -- q % 2 = 0 signifie q = 2 * (q/2)
  -- q est pair, donc q = 2 * (q/2)
  have hq2 : q = 2 * (q / 2) := by have := Nat.div_add_mod q 2; omega
  -- Étape 1: Montrer que le résultat mod 2^k vaut 2^(k-1) - 1
  -- La cascade_formula donne sN(n) = 3*2^(k-1)*q + (3*2^(k-1)-1)
  -- Avec q = 2*(q/2), on a 3*2^(k-1)*(2*(q/2)) = (2*2^(k-1)) * (3*(q/2))
  -- Et 2*2^(k-1) = 2^k.
  set p := 2^(k-1)
  have hp : 0 < p := Nat.pos_of_ne_zero (by positivity)
  have hpk : 2^k = 2 * p := by
    show 2^k = 2 * 2^(k-1)
    have : k = (k - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [pow_succ]; ring
  -- Le résultat = 3*p*q + (3*p - 1). Avec q = 2*(q/2) :
  -- = 3*p*(2*(q/2)) + (3*p - 1)
  -- = (2*p) * (3*(q/2)) + (3*p - 1)
  -- = 2^k * (3*(q/2)) + (3*p - 1)
  -- Donc % 2^k = (3*p - 1) % 2^k
  have hval : (3 * p * q + (3 * p - 1)) % (2 * p) = p - 1 := by
    rw [hq2]
    -- 3*p*(2*(q/2)) = (2*p) * (3*(q/2))
    have h1 : 3 * p * (2 * (q / 2)) = 2 * p * (3 * (q / 2)) := by ring
    rw [h1, Nat.mul_add_mod_self_left]
    -- (3*p - 1) % (2*p) = p - 1
    -- 3*p - 1 = 2*p + (p - 1) et p - 1 < 2*p
    -- (3*p - 1) % (2*p) = p - 1
    -- 3*p - 1 = (2*p)*1 + (p - 1) et p - 1 < 2*p
    have h2 : 3 * p - 1 = 2 * p * 1 + (p - 1) := by omega
    rw [h2, Nat.mul_add_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  -- heq : (3 * p * q + (3 * p - 1)) % 2^k = 2^k - 1
  -- On veut montrer que c'est impossible.
  -- Étape : montrer que (3 * p * q + (3 * p - 1)) % (2 * p) = p - 1
  -- et que 2^k = 2 * p, donc le mod donne p - 1, pas 2*p - 1.
  have heq2 : (3 * p * q + (3 * p - 1)) % (2 * p) = p - 1 := hval
  -- Puisque 2^k = 2 * p (par hpk), substituons dans heq
  have heq3 : (3 * p * q + (3 * p - 1)) % (2 * p) = 2 * p - 1 := by
    rwa [hpk] at heq
  -- Contradiction: heq2 dit que c'est p-1, heq3 dit 2*p - 1
  have hp2 : 2 ≤ p := by
    show 2 ≤ 2^(k-1)
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^(k-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- heq2 : ... = p - 1, heq3 : ... = 2*p - 1, même LHS
  -- Donc p - 1 = 2*p - 1, contradiction car p ≥ 2
  omega

/-- Itération : propagation du quotient pair sur j pas de cascade.
    Si n a exactement k trailing ones (quotient pair),
    alors nSeq(n, j) a exactement k-j trailing ones pour tout j ≤ k-3. -/
theorem cascade_tight_iterate (n : ℕ) :
    ∀ k j : ℕ, 3 ≤ k → j ≤ k - 3 →
    n % 2^k = 2^k - 1 →
    n % 2^(k+1) ≠ 2^(k+1) - 1 →
    nSeq n j % 2^(k - j + 1) ≠ 2^(k - j + 1) - 1 := by
  intro k j hk hj hmod hexact
  induction j with
  | zero =>
    simp only [nSeq]
    -- goal: n % 2^(k - 0 + 1) ≠ 2^(k - 0 + 1) - 1
    -- k - 0 + 1 = k + 1
    show n % 2^(k + 1) ≠ 2^(k + 1) - 1
    exact hexact
  | succ j' ih =>
    simp only [nSeq]
    have hj'_le : j' ≤ k - 3 := by omega
    -- nSeq n j' a au moins k - j' trailing ones (cascade_iterate)
    have hmod_prev := cascade_iterate n k j' hk hj'_le hmod
    -- nSeq n j' n'a PAS k - j' + 1 trailing ones (ih)
    have hexact_prev := ih hj'_le
    -- Le quotient (nSeq n j') / 2^(k-j') est pair
    -- car % 2^(k-j') = 2^(k-j') - 1 mais % 2^(k-j'+1) ≠ 2^(k-j'+1) - 1
    -- Cela signifie le bit (k-j') est 0, i.e., le quotient est pair.
    have hqp : ((nSeq n j') / 2^(k - j')) % 2 = 0 := by
      -- nSeq n j' = 2^(k-j') * q + (2^(k-j') - 1) avec q pair
      -- n % 2^(k-j'+1) ≠ 2^(k-j'+1) - 1
      -- i.e., n % (2 * 2^(k-j')) ≠ 2 * 2^(k-j') - 1
      -- n = 2^(k-j') * q + (2^(k-j') - 1), n % (2*2^(k-j')) = (q%2) * 2^(k-j') + 2^(k-j') - 1
      -- Si q % 2 = 1 : = 2^(k-j') + 2^(k-j') - 1 = 2*2^(k-j') - 1 = 2^(k-j'+1) - 1
      -- Mais hexact_prev dit % 2^(k-j'+1) ≠ 2^(k-j'+1) - 1
      -- Donc q % 2 ≠ 1, i.e., q % 2 = 0
      by_contra h
      apply hexact_prev
      -- h : ((nSeq n j') / 2^(k - j')) % 2 ≠ 0
      -- Donc ((nSeq n j') / 2^(k - j')) % 2 = 1
      have hq1 : ((nSeq n j') / 2^(k - j')) % 2 = 1 := by omega
      -- Montrer : nSeq n j' % 2^(k-j'+1) = 2^(k-j'+1) - 1
      -- nSeq n j' = 2^(k-j') * q + (2^(k-j') - 1) et q % 2 = 1
      have hdecomp := (Nat.div_add_mod (nSeq n j') (2^(k-j'))).symm
      rw [hmod_prev] at hdecomp
      set q' := (nSeq n j') / 2^(k-j')
      -- q' % 2 = 1 signifie q' = 2*(q'/2) + 1
      -- nSeq n j' = 2^(k-j') * q' + (2^(k-j') - 1)
      -- % 2^(k-j'+1) = (q' % 2) * 2^(k-j') + (2^(k-j') - 1)
      -- = 1 * 2^(k-j') + 2^(k-j') - 1 = 2^(k-j'+1) - 1
      -- nSeq n j' = 2^(k-j') * q' + (2^(k-j') - 1) (hdecomp)
      -- q' % 2 = 1 (hq1)
      -- Montrons : nSeq n j' % (2 * 2^(k-j')) = 2 * 2^(k-j') - 1
      -- = (2^(k-j') * q' + (2^(k-j') - 1)) % (2 * 2^(k-j'))
      -- = (q' % 2) * 2^(k-j') + (2^(k-j') - 1)  [car 2^(k-j') - 1 < 2^(k-j')]
      -- = 1 * 2^(k-j') + 2^(k-j') - 1 = 2 * 2^(k-j') - 1
      have hpow : 2^(k - j' + 1) = 2 * 2^(k - j') := by
        have hkeq : k - j' + 1 = (k - j') + 1 := by omega
        conv_lhs => rw [hkeq]
        rw [pow_succ]; ring
      rw [hpow]
      -- Goal: nSeq n j' % (2 * 2^(k-j')) = 2 * 2^(k-j') - 1
      rw [hdecomp]
      -- Goal: (2^(k-j') * q' + (2^(k-j') - 1)) % (2 * 2^(k-j')) = 2 * 2^(k-j') - 1
      -- On sait : q' = 2*(q'/2) + 1 (car q' % 2 = 1)
      have hq'odd : q' = 2 * (q' / 2) + 1 := by
        have := Nat.div_add_mod q' 2
        omega
      rw [hq'odd]
      -- 2^(k-j') * (2*(q'/2) + 1) = 2 * 2^(k-j') * (q'/2) + 2^(k-j')
      set m := 2^(k - j')
      have hm : 0 < m := Nat.pos_of_ne_zero (by positivity)
      -- m * (2*(q'/2) + 1) + (m - 1) = 2*m*(q'/2) + (2*m - 1)
      -- Étape 1: distribuer m * (2*(q'/2) + 1) = 2*m*(q'/2) + m
      have hdist : m * (2 * (q'/2) + 1) = 2 * m * (q'/2) + m := by ring
      -- Étape 2: (2*m*(q'/2) + m) + (m-1) = 2*m*(q'/2) + (2*m-1)
      have hmul : 2 * m * (q'/2) + m + (m - 1) = 2 * m * (q'/2) + (2 * m - 1) := by omega
      -- Étape 3: réécrire le LHS
      have hfull : m * (2 * (q'/2) + 1) + (m - 1)
                 = 2 * m * (q'/2) + (2 * m - 1) := by rw [hdist]; omega
      rw [hfull]
      rw [Nat.mul_add_mod_self_left]
      -- (2*m - 1) % (2*m) = 2*m - 1
      exact Nat.mod_eq_of_lt (by omega)
    -- Maintenant appliquer cascade_tight_step
    have hkj : 2 ≤ k - j' := by omega
    have hstep := cascade_tight_step (nSeq n j') (k - j') hkj hmod_prev hqp
    -- hstep : syracuseNext (nSeq n j') % 2^(k-j') ≠ 2^(k-j') - 1
    -- Mais on veut : syracuseNext (nSeq n j') % 2^(k - (j'+1) + 1) ≠ ...
    -- k - (j'+1) + 1 = k - j'
    have heq : k - (j' + 1) + 1 = k - j' := by omega
    rw [heq]
    exact hstep

/-- Corollaire principal : si n a exactement k trailing ones,
    nSeq(n, k-3) a exactement 3 trailing ones (% 16 ≠ 15). -/
theorem cascade_exact_3_trailing (n k : ℕ) (hk : 3 ≤ k)
    (hmod : n % 2^k = 2^k - 1)
    (hexact : n % 2^(k+1) ≠ 2^(k+1) - 1) :
    nSeq n (k - 3) % 16 ≠ 15 := by
  have h := cascade_tight_iterate n k (k - 3) hk (by omega) hmod hexact
  -- h : nSeq n (k-3) % 2^(k - (k-3) + 1) ≠ 2^(k - (k-3) + 1) - 1
  -- k - (k-3) + 1 = 4
  have heq : k - (k - 3) + 1 = 4 := by omega
  rw [heq] at h
  norm_num at h
  exact h

/-- Version forte de cascade_then_escape : pas de condition hbit
    si n a exactement k trailing ones. SANS SORRY. -/
theorem cascade_then_escape_exact (n k : ℕ) (hk : 3 ≤ k)
    (hmod : n % 2^k = 2^k - 1)
    (hexact : n % 2^(k+1) ≠ 2^(k+1) - 1) :
    nSeq n (k - 2) % 8 = 3 := by
  have hbit := cascade_exact_3_trailing n k hk hmod hexact
  exact cascade_then_escape n k hk hmod hbit

end

end ProjetCollatz
