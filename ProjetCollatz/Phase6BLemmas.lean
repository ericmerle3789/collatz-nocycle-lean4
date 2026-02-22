import ProjetCollatz.SyracuseDefs
import ProjetCollatz.Phase6Lemmas

/-!
# Phase6BLemmas.lean — Lemmes avancés Phase 6 (Sprint P6-B)

Lemmes recommandés par Gemini 2.5 Pro (auditeur scientifique) lors de la
certification du Sprint P6-A (2026-02-15).

## Contenu
- B1: `syracuseNext_lt_when_mod4_eq1` — Descente explicite: n≡1(mod4) ∧ n>1 → next < n
- B2: `half_3n1_odd_when_mod4_eq3` — Composition: n≡3(mod4) → (3n+1)/2 est impair
- B3: `half_3n1_mod8_dichotomy` — Raffinage mod 8: la dynamique entre les classes
- B4: `tauPrefix` definition — Moyenne des paiements 2-adiques sur L pas

## Signification pour la conjecture
- B1 montre que la moitié des impairs (ceux ≡1 mod4) DESCENDENT toujours.
- B2 + B3 montrent que quand on ne descend pas (n≡3 mod4), le prochain
  pas PEUT descendre (50% de chance de tomber en ≡1 mod4).
- B4 formalise τ_prefix, la métrique centrale du projet.

## Méthodologie
- Aucun `sorry` — tout est prouvé formellement.
- Les preuves utilisent uniquement SyracuseDefs.lean et Phase6Lemmas.lean.
- Zéro axiome utilisateur.
-/

namespace ProjetCollatz

noncomputable section

/-!
## B1: Descente explicite pour n ≡ 1 (mod 4)

C'est le lemme le plus puissant du sprint P6-B. Il dit:
si n est impair, n > 1, et n ≡ 1 (mod 4), alors syracuseNext(n) < n.

Intuition: pour n ≡ 1 (mod 4), on a 3n+1 ≡ 0 (mod 4), donc v₂(3n+1) ≥ 2.
On divise par au moins 4, donc next ≤ (3n+1)/4 < n pour n > 1.
-/

-- Main theorem B1: Descent for n ≡ 1 (mod 4), n > 1
theorem syracuseNext_lt_when_mod4_eq1 (n : ℕ) (hgt : 1 < n) (hmod : n % 4 = 1) :
    syracuseNext n < n := by
  -- Step 1: v₂(3n+1) ≥ 2 from Phase 6-A dichotomy
  have hv : 2 ≤ v2_3n1 n := by
    unfold v2_3n1
    exact v2_mod4_eq1_ge2 n hmod
  -- Step 2: From syracuseNext_spec, syracuseNext n * 2^(v2_3n1 n) = 3n+1
  have hspec := syracuseNext_spec n
  -- Step 3: Since v₂ ≥ 2, 2^v₂ ≥ 4
  have hpow_ge : 4 ≤ 2 ^ (v2_3n1 n) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (v2_3n1 n) := Nat.pow_le_pow_right (by norm_num) hv
  -- Step 4: syracuseNext n * 2^v₂ = 3n+1, and 2^v₂ ≥ 4
  -- So syracuseNext n ≤ (3n+1)/4  (since sN * 2^v₂ = 3n+1, and 2^v₂ ≥ 4 means sN ≤ (3n+1)/4)
  -- And (3n+1)/4 < n when n > 1 (since 3n+1 < 4n ⟺ 1 < n)
  -- Combining: syracuseNext n < n
  have h3n1 : 3 * n + 1 = syracuseNext n * (2 ^ (v2_3n1 n)) := hspec.symm
  -- syracuseNext n * 4 ≤ syracuseNext n * 2^v₂ = 3n+1
  have hle : syracuseNext n * 4 ≤ 3 * n + 1 := by
    calc
      syracuseNext n * 4
        ≤ syracuseNext n * (2 ^ (v2_3n1 n)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * n + 1 := hspec
  -- From syracuseNext n * 4 ≤ 3n+1 and 3n+1 < 4n (for n>1), we get sN < n
  omega

/-!
## B2: Composition — (3n+1)/2 est impair quand n ≡ 3 (mod 4)

Quand n ≡ 3 (mod 4), v₂(3n+1) = 1, donc syracuseNext(n) = (3n+1)/2.
Ce résultat est impair.
-/

-- B2: (3n+1)/2 is odd when n ≡ 3 (mod 4)
theorem half_3n1_odd_when_mod4_eq3 (n : ℕ) (hmod : n % 4 = 3) :
    ((3 * n + 1) / 2) % 2 = 1 := by
  -- n = 4k + 3, so 3n+1 = 12k + 10 = 2(6k+5), and 6k+5 is odd
  omega

/-!
## B3: Raffinage mod 8 — la dynamique entre classes

Quand n ≡ 3 (mod 4), le prochain impair est (3n+1)/2. La classe mod 4 du
résultat dépend de n mod 8:

- n ≡ 3 (mod 8): next ≡ 1 (mod 4) → DESCENTE GARANTIE au pas suivant!
- n ≡ 7 (mod 8): next ≡ 3 (mod 4) → on reste en "montée"

C'est la base de l'argument probabiliste de la conjecture.
-/

-- B3a: n ≡ 3 (mod 8) → (3n+1)/2 ≡ 1 (mod 4) → descente garantie au pas suivant
theorem half_3n1_mod4_eq1_when_mod8_eq3 (n : ℕ) (hmod : n % 8 = 3) :
    ((3 * n + 1) / 2) % 4 = 1 := by
  omega

-- B3b: n ≡ 7 (mod 8) → (3n+1)/2 ≡ 3 (mod 4) → reste en "montée"
theorem half_3n1_mod4_eq3_when_mod8_eq7 (n : ℕ) (hmod : n % 8 = 7) :
    ((3 * n + 1) / 2) % 4 = 3 := by
  omega

-- B3c: Complétude — tout n ≡ 3 (mod 4) est soit ≡ 3 soit ≡ 7 (mod 8)
theorem mod8_dichotomy_of_mod4_eq3 (n : ℕ) (hmod : n % 4 = 3) :
    n % 8 = 3 ∨ n % 8 = 7 := by
  omega

-- B3d: Corollaire complet — après montée, on va soit en descente, soit on reste
theorem composition_step_dichotomy (n : ℕ) (hmod : n % 4 = 3) :
    ((3 * n + 1) / 2) % 4 = 1 ∨ ((3 * n + 1) / 2) % 4 = 3 := by
  have h := mod8_dichotomy_of_mod4_eq3 n hmod
  cases h with
  | inl h3 => left; exact half_3n1_mod4_eq1_when_mod8_eq3 n h3
  | inr h7 => right; exact half_3n1_mod4_eq3_when_mod8_eq7 n h7

/-!
## B4: Définition formelle de τ_prefix

τ_prefix(n, L) est la **moyenne des paiements 2-adiques** sur L pas de la
trajectoire Syracuse odd→odd à partir de n.

Formellement: τ_prefix(n, L) = (1/L) × Σᵢ₌₀^{L-1} v₂(3·nSeq(n,i)+1)

On utilise aSeq (défini dans SyracuseDefs.lean) qui donne v₂(3·nSeq(n,k)+1).
-/

-- Definition of tau_prefix as a rational number
def tauPrefix (start_n : ℕ) (L : ℕ) : ℚ :=
  if L = 0 then 0
  else (∑ i ∈ Finset.range L, (aSeq start_n i : ℚ)) / (L : ℚ)

-- B4a: τ_prefix is non-negative
theorem tauPrefix_nonneg (start_n L : ℕ) : 0 ≤ tauPrefix start_n L := by
  simp only [tauPrefix]
  split
  · exact le_refl 0
  · exact div_nonneg
      (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
      (Nat.cast_nonneg _)

-- B4b: τ_prefix at the fixed point equals 2
-- When start_n = 1, every step gives v₂(3·1+1) = v₂(4) = 2, so average = 2
theorem tauPrefix_at_one (L : ℕ) (hL : 0 < L) :
    tauPrefix 1 L = 2 := by
  simp only [tauPrefix]
  -- L ≠ 0 since 0 < L
  have hLne : L ≠ 0 := by omega
  rw [if_neg hLne]
  -- Each aSeq 1 i = v2_3n1 (nSeq 1 i) = v2_3n1 1 = v2Nat 4 = 2
  have haSeq : ∀ i, i ∈ Finset.range L → (aSeq 1 i : ℚ) = 2 := by
    intro i _
    simp [aSeq, nSeq_stays_at_one, v2_3n1]
    simp [v2Nat]
  rw [Finset.sum_congr rfl haSeq]
  simp [Finset.sum_const, Finset.card_range]
  field_simp

/-!
## B5: Montée bornée — quand v₂ = 1, le facteur est < 2

syracuseNext(n) = (3n+1)/2 < 2n pour tout n > 0 quand v₂(3n+1) = 1.
Cela signifie que les montées ne dépassent jamais un facteur 2.
-/

-- Montée bornée: quand v₂ = 1, syracuseNext(n) < 2n
theorem syracuseNext_lt_2n_when_v2_eq1 (n : ℕ) (hpos : 0 < n)
    (hv : v2_3n1 n = 1) :
    syracuseNext n < 2 * n := by
  have hspec := syracuseNext_spec n
  rw [hv] at hspec
  -- hspec : syracuseNext n * 2^1 = 3*n + 1
  -- Since 2^1 = 2, this is: syracuseNext n * 2 = 3*n + 1
  -- We need syracuseNext n < 2n, i.e. syracuseNext n * 2 < 4n
  -- From hspec: syracuseNext n * 2 = 3n+1 < 4n iff 1 < n
  -- For n=1: syracuseNext 1 * 2 = 3+1 = 4 = 2*2, so sN 1 = 2... wait no.
  -- Let's use nlinarith or compute via the spec
  have h2pow : (2 : ℕ) ^ 1 = 2 := by norm_num
  rw [h2pow] at hspec
  -- hspec : syracuseNext n * 2 = 3 * n + 1
  -- Need : syracuseNext n < 2 * n
  -- ⟺ syracuseNext n * 2 < 4 * n (multiply both sides by 2)
  -- From hspec: 3*n+1 < 4*n ⟺ 1 < n, which may fail for n=1
  -- n=1: syracuseNext 1 * 2 = 4, 2*1*2 = 4, so sN 1 = 2, and 2 < 2*1 = 2 fails!
  -- Actually sN 1 = 1 (from syracuseNext_one_eq_one), but with v2_3n1 1 = 2, not 1.
  -- If v2_3n1 n = 1, then n ≡ 3 (mod 4), so n ≥ 3.
  -- When n ≡ 3 (mod 4), n ∈ {3, 7, 11, ...}, so n ≥ 3.
  have hn_ge3 : 3 ≤ n := by
    -- v2_3n1 n = 1 implies n % 4 = 3 (from v2_mod4_eq3_eq1 and v2_mod4_eq1_ge2)
    -- which implies n ≥ 3
    -- Actually, let's just use the fact that n > 0 and v2 = 1
    -- If n = 1, v2_3n1 1 = v2Nat 4 = 2 ≠ 1, contradiction
    -- If n = 2, n is even, not odd (but we don't assume odd here)
    -- Actually we just need n * 4 > 3 * n + 1, so n > 1
    -- Let's check: if n = 1, v2_3n1 1 = 2 ≠ 1
    by_contra h
    push_neg at h
    -- n ≤ 2, and n > 0
    interval_cases n <;> simp_all [v2_3n1, v2Nat]
  nlinarith

/-!
## B6: Prédiction de v₂ par les résidus modulaires (descentes profondes)

C'est le lemme qui déverrouille P6-C. Il montre que la profondeur de descente
est DÉTERMINÉE par le résidu modulaire de n.

Exemples concrets:
- n ≡ 5 (mod 16)  → 3n+1 = 48k+16 = 16(3k+1) → v₂(3n+1) ≥ 4
- n ≡ 1 (mod 16)  → 3n+1 = 48k+4  = 4(12k+1)  → v₂(3n+1) = 2
- n ≡ 13 (mod 16) → 3n+1 = 48k+40 = 8(6k+5)   → v₂(3n+1) = 3
- n ≡ 9 (mod 16)  → 3n+1 = 48k+28 = 4(12k+7)   → v₂(3n+1) = 2

Chaque classe mod 2^k a un v₂ prédictible. C'est le "code-barres binaire"
qui détermine la trajectoire.
-/

-- B6a: n ≡ 5 (mod 16) → v₂(3n+1) ≥ 4 (descente très profonde)
theorem v2_mod16_eq5_ge4 (n : ℕ) (hmod : n % 16 = 5) :
    4 ≤ v2Nat (3 * n + 1) := by
  -- n = 16k+5, so 3n+1 = 48k+16 = 16(3k+1), divisible by 16 = 2^4
  have h16dvd : 16 ∣ (3 * n + 1) := by omega
  have h3n1_ne : 3 * n + 1 ≠ 0 := by omega
  have h2pow : (2 ^ 4) ∣ (3 * n + 1) := by
    show 16 ∣ (3 * n + 1)
    exact h16dvd
  exact pow2_dvd_le_v2Nat_pos (3 * n + 1) 4 h3n1_ne h2pow

-- B6b: n ≡ 13 (mod 16) → v₂(3n+1) = 3 (descente profonde)
theorem v2_mod16_eq13_eq3 (n : ℕ) (hmod : n % 16 = 13) :
    v2Nat (3 * n + 1) = 3 := by
  -- n = 16k+13, so 3n+1 = 48k+40 = 8(6k+5), and 6k+5 is odd
  have h3n1_ne : 3 * n + 1 ≠ 0 := by omega
  -- Unfold step by step
  have h_even1 : (3 * n + 1) % 2 = 0 := by omega
  have hv1 := v2Nat_eq_succ_of_mod2_eq0 (3 * n + 1) h3n1_ne h_even1
  -- (3n+1)/2 = 24k+20
  have h_half_ne : (3 * n + 1) / 2 ≠ 0 := by omega
  have h_even2 : ((3 * n + 1) / 2) % 2 = 0 := by omega
  have hv2 := v2Nat_eq_succ_of_mod2_eq0 ((3 * n + 1) / 2) h_half_ne h_even2
  -- (3n+1)/4 = 12k+10
  have h_quarter_ne : (3 * n + 1) / 2 / 2 ≠ 0 := by omega
  have h_even3 : ((3 * n + 1) / 2 / 2) % 2 = 0 := by omega
  have hv3 := v2Nat_eq_succ_of_mod2_eq0 ((3 * n + 1) / 2 / 2) h_quarter_ne h_even3
  -- (3n+1)/8 = 6k+5, which is odd
  have h_odd4 : ((3 * n + 1) / 2 / 2 / 2) % 2 = 1 := by omega
  have hv4 := v2Nat_eq_zero_of_mod2_ne0 ((3 * n + 1) / 2 / 2 / 2) (by omega)
  omega

-- B6c: n ≡ 9 (mod 16) → v₂(3n+1) = 2 (descente faible, comme mod4=1)
theorem v2_mod16_eq9_eq2 (n : ℕ) (hmod : n % 16 = 9) :
    v2Nat (3 * n + 1) = 2 := by
  -- n = 16k+9, so 3n+1 = 48k+28 = 4(12k+7), and 12k+7 is odd
  have h3n1_ne : 3 * n + 1 ≠ 0 := by omega
  have h_even1 : (3 * n + 1) % 2 = 0 := by omega
  have hv1 := v2Nat_eq_succ_of_mod2_eq0 (3 * n + 1) h3n1_ne h_even1
  have h_half_ne : (3 * n + 1) / 2 ≠ 0 := by omega
  have h_even2 : ((3 * n + 1) / 2) % 2 = 0 := by omega
  have hv2 := v2Nat_eq_succ_of_mod2_eq0 ((3 * n + 1) / 2) h_half_ne h_even2
  have h_odd3 : ((3 * n + 1) / 2 / 2) % 2 = 1 := by omega
  have hv3 := v2Nat_eq_zero_of_mod2_ne0 ((3 * n + 1) / 2 / 2) (by omega)
  omega

-- B6d: n ≡ 1 (mod 16) → v₂(3n+1) = 2 (descente faible)
theorem v2_mod16_eq1_eq2 (n : ℕ) (hmod : n % 16 = 1) :
    v2Nat (3 * n + 1) = 2 := by
  have h3n1_ne : 3 * n + 1 ≠ 0 := by omega
  have h_even1 : (3 * n + 1) % 2 = 0 := by omega
  have hv1 := v2Nat_eq_succ_of_mod2_eq0 (3 * n + 1) h3n1_ne h_even1
  have h_half_ne : (3 * n + 1) / 2 ≠ 0 := by omega
  have h_even2 : ((3 * n + 1) / 2) % 2 = 0 := by omega
  have hv2 := v2Nat_eq_succ_of_mod2_eq0 ((3 * n + 1) / 2) h_half_ne h_even2
  have h_odd3 : ((3 * n + 1) / 2 / 2) % 2 = 1 := by omega
  have hv3 := v2Nat_eq_zero_of_mod2_ne0 ((3 * n + 1) / 2 / 2) (by omega)
  omega

/-!
## B7: Tableau complet mod 16 pour impairs

Pour tout n impair, n mod 16 ∈ {1, 3, 5, 7, 9, 11, 13, 15}.
On donne v₂(3n+1) pour chacun:

| n mod 16 | n mod 8 | n mod 4 | v₂(3n+1) | Type     |
|----------|---------|---------|----------|----------|
| 1        | 1       | 1       | 2        | Descente |
| 3        | 3       | 3       | 1        | Montée   |
| 5        | 5       | 1       | ≥4       | SUPER descente |
| 7        | 7       | 3       | 1        | Montée   |
| 9        | 1       | 1       | 2        | Descente |
| 11       | 3       | 3       | 1        | Montée   |
| 13       | 5       | 1       | 3        | Descente profonde |
| 15       | 7       | 3       | 1        | Montée   |

Distribution : 4 montées (v₂=1) + 2 descentes faibles (v₂=2) +
               1 descente profonde (v₂=3) + 1 super descente (v₂≥4)

Moyenne pondérée: (4×1 + 2×2 + 1×3 + 1×4) / 8 = 15/8 = 1.875
C'est > log₂(3) ≈ 1.585 → la trajectoire descend EN MOYENNE !
C'est l'essence de l'argument heuristique de la conjecture.
-/

-- v₂(3n+1) = 1 pour n ≡ 11 (mod 16) (comme mod4=3)
theorem v2_mod16_eq11_eq1 (n : ℕ) (hmod : n % 16 = 11) :
    v2Nat (3 * n + 1) = 1 := by
  exact v2_mod4_eq3_eq1 n (by omega)

-- v₂(3n+1) = 1 pour n ≡ 15 (mod 16) (comme mod4=3)
theorem v2_mod16_eq15_eq1 (n : ℕ) (hmod : n % 16 = 15) :
    v2Nat (3 * n + 1) = 1 := by
  exact v2_mod4_eq3_eq1 n (by omega)

end

end ProjetCollatz
