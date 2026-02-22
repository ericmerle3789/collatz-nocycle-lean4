import ProjetCollatz.Phase30GlobalDescent

/-!
# Phase32CarryChain.lean — v₂ Structure and Descent Mechanics

## Purpose

Formalize the structural relationship between modular classes and
the 2-adic valuation v₂(3n+1), which governs Syracuse dynamics.

## Key Results

1. **Mod-4 dichotomy**: n ≡ 1 mod 4 ⟹ v₂ ≥ 2 (descent),
   n ≡ 3 mod 4 ⟹ v₂ = 1 (ascent).

2. **Descent from v₂ ≥ 2**: syracuseNext(n) < n for n > 1.

3. **Immediate Descends for mod-4 class 1**: one Syracuse step suffices.

4. **Two-step bound**: For n ≡ 3 mod 8, sN ≡ 1 mod 4 (guaranteed descent
   at step 2). For n ≡ 7 mod 8, sN ≡ 3 mod 4 (no guarantee).

5. **Mersenne worst case**: v₂(2^t - 1) = 1 always.

## Note on the Directive

The directive suggested: "trailing 1s ⟹ v₂ ≥ t+1". This is FALSE.
Counterexample: n=3 (trailing 11), v₂(10)=1. Mersenne numbers 2^t-1
(all 1s) always give v₂=1. The v₂ value is determined by the modular
class, not by trailing bits.

## Date: 2026-02-18 (Cycle 110)
-/

namespace ProjetCollatz

/-!
## Part 1: Mod-4 dichotomy
-/

/-- Every odd n is in exactly one of two mod-4 classes. -/
theorem odd_mod4_cases (n : ℕ) (hodd : n % 2 = 1) :
    n % 4 = 1 ∨ n % 4 = 3 := by
  omega

/-- If n ≡ 1 mod 4, then v₂(3n+1) ≥ 2. This is the descent condition. -/
theorem v2_ge2_of_mod4_eq1 (n : ℕ) (hmod : n % 4 = 1) :
    2 ≤ v2_3n1 n := by
  unfold v2_3n1
  exact v2_mod4_eq1_ge2 n hmod

/-- If n ≡ 3 mod 4, then v₂(3n+1) = 1. This is the ascent case. -/
theorem v2_eq1_of_mod4_eq3 (n : ℕ) (hmod : n % 4 = 3) :
    v2_3n1 n = 1 := by
  unfold v2_3n1
  exact v2_mod4_eq3_eq1 n hmod

/-!
## Part 2: Descent from v₂ ≥ 2
-/

/-- If v₂(3n+1) ≥ 2 and n > 1, then syracuseNext(n) < n.
    Proof: sN * 2^a = 3n+1 with a ≥ 2, so sN ≤ (3n+1)/4 < n. -/
theorem syracuseNext_lt_of_v2_ge2 (n : ℕ) (hn : n > 1) (hv : 2 ≤ v2_3n1 n) :
    syracuseNext n < n := by
  have hspec := syracuseNext_spec n
  have hpow : 4 ≤ 2 ^ v2_3n1 n := by
    calc 4 = 2 ^ 2 := by norm_num
         _ ≤ 2 ^ v2_3n1 n := Nat.pow_le_pow_right (by norm_num) hv
  have h_le : syracuseNext n * 4 ≤ 3 * n + 1 := by
    calc syracuseNext n * 4
        ≤ syracuseNext n * 2 ^ v2_3n1 n := Nat.mul_le_mul_left _ hpow
      _ = 3 * n + 1 := hspec
  omega

/-- One-step descent for n ≡ 1 mod 4 with n > 1. -/
theorem descent_mod4_eq1 (n : ℕ) (hn : n > 1) (hmod : n % 4 = 1) :
    syracuseNext n < n :=
  syracuseNext_lt_of_v2_ge2 n hn (v2_ge2_of_mod4_eq1 n hmod)

/-- Descends for all n ≡ 1 mod 4 with n > 1. -/
theorem descends_of_mod4_eq1 (n : ℕ) (hn : n > 1) (hmod : n % 4 = 1) :
    Descends n :=
  ⟨1, by omega, by simp [nSeq]; exact descent_mod4_eq1 n hn hmod⟩

/-!
## Part 3: v₂ = 1 dynamics

When v₂(3n+1) = 1, syracuseNext(n) = (3n+1)/2.
The successor's mod-4 class depends on n mod 8:
- n ≡ 3 mod 8: sN = (3n+1)/2 ≡ 5 mod 4 ≡ 1 mod 4 (descent guaranteed)
- n ≡ 7 mod 8: sN = (3n+1)/2 ≡ 11 mod 4 ≡ 3 mod 4 (another ascent)
-/

/-- When v₂ = 1, syracuseNext(n) * 2 = 3n+1. -/
theorem syracuseNext_of_v2_eq1 (n : ℕ) (hv : v2_3n1 n = 1) :
    syracuseNext n * 2 = 3 * n + 1 := by
  have := syracuseNext_spec n
  rw [hv] at this
  simpa using this

/-- For n ≡ 3 mod 8: v₂ = 1 and successor ≡ 1 mod 4 (guaranteed descent next). -/
theorem successor_mod4_of_mod8_eq3 (n : ℕ) (hmod : n % 8 = 3) :
    syracuseNext n % 4 = 1 := by
  have hmod4 : n % 4 = 3 := by omega
  have hv := v2_eq1_of_mod4_eq3 n hmod4
  have hspec := syracuseNext_of_v2_eq1 n hv
  -- sN * 2 = 3n+1 ⟹ sN = (3n+1) / 2
  have hsN_eq : syracuseNext n = (3 * n + 1) / 2 := by
    have := hspec -- sN * 2 = 3n+1
    omega
  rw [hsN_eq]
  omega

/-- For n ≡ 7 mod 8: v₂ = 1 and successor ≡ 3 mod 4 (another ascent). -/
theorem successor_mod4_of_mod8_eq7 (n : ℕ) (hmod : n % 8 = 7) :
    syracuseNext n % 4 = 3 := by
  have hmod4 : n % 4 = 3 := by omega
  have hv := v2_eq1_of_mod4_eq3 n hmod4
  have hspec := syracuseNext_of_v2_eq1 n hv
  -- sN * 2 = 3n+1 ⟹ sN = (3n+1) / 2
  have hsN_eq : syracuseNext n = (3 * n + 1) / 2 := by
    have := hspec -- sN * 2 = 3n+1
    omega
  rw [hsN_eq]
  omega

/-!
## Part 4: Two-step descent for class 3 mod 8

For n ≡ 3 mod 8 with n > 1:
- Step 1: ascent, sN₁ = (3n+1)/2, and sN₁ ≡ 1 mod 4
- Step 2: descent (since v₂ ≥ 2), sN₂ < sN₁

Combined: nSeq n 2 < (3n+1)/2, which is < n when... well, sN₁ > n
(since 3n+1 > 2n), but sN₂ < sN₁. We need sN₂ < n.

Bound: sN₂ * 4 ≤ 3*sN₁ + 1 = 3*(3n+1)/2 + 1 = (9n+5)/2
So sN₂ ≤ (9n+5)/8 < n when n ≥ 5. For n=3: sN₂ = 1 < 3. ✓
-/

/-- **Two-step bound for class 3 mod 8**: nSeq n 2 * 8 ≤ 9n + 5.
    The ratio 9/8 > 1 means two steps do NOT guarantee descent below n.
    (Counterexample: n=11, nSeq 11 2 = 13 > 11.)
    Deeper modular analysis is needed for true descent certificates. -/
theorem two_step_bound_mod8_eq3 (n : ℕ) (hmod : n % 8 = 3) :
    nSeq n 2 * 8 ≤ 9 * n + 5 := by
  have hmod4 : n % 4 = 3 := by omega
  have hv1 := v2_eq1_of_mod4_eq3 n hmod4
  have h1 := syracuseNext_of_v2_eq1 n hv1
  have h_succ_mod := successor_mod4_of_mod8_eq3 n hmod
  have hv2 := v2_ge2_of_mod4_eq1 (syracuseNext n) h_succ_mod
  have hspec2 := syracuseNext_spec (syracuseNext n)
  have hpow : 4 ≤ 2 ^ v2_3n1 (syracuseNext n) :=
    Nat.le_of_eq (by norm_num : 4 = 2 ^ 2) |>.trans (Nat.pow_le_pow_right (by norm_num) hv2)
  have h_nseq2 : nSeq n 2 = syracuseNext (syracuseNext n) := by simp [nSeq]
  rw [h_nseq2]
  have h2_4 : syracuseNext (syracuseNext n) * 4 ≤ 3 * syracuseNext n + 1 :=
    calc syracuseNext (syracuseNext n) * 4
        ≤ syracuseNext (syracuseNext n) * 2 ^ v2_3n1 (syracuseNext n) :=
          Nat.mul_le_mul_left _ hpow
      _ = 3 * syracuseNext n + 1 := hspec2
  have h_8 : syracuseNext (syracuseNext n) * 8 ≤ 6 * syracuseNext n + 2 := by linarith
  have h_6sn : 6 * syracuseNext n = 3 * (3 * n + 1) := by linarith [h1]
  linarith

/-!
## Part 5: Mersenne worst case
-/

/-- For Mersenne numbers 2^t - 1 (t ≥ 2), v₂(3n+1) = 1. -/
theorem mersenne_v2_eq1 (t : ℕ) (ht : t ≥ 2) :
    v2_3n1 (2 ^ t - 1) = 1 := by
  have hmod : (2 ^ t - 1) % 4 = 3 := by
    have h4dvd : (2 ^ 2) ∣ 2 ^ t := Nat.pow_dvd_pow 2 ht
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4]
    obtain ⟨q, hq⟩ := h4dvd
    have hq_pos : q ≥ 1 := by
      by_contra h; push_neg at h
      simp at h; rw [h] at hq; simp at hq
    rw [show 2 ^ t = 2 ^ 2 * q from hq]
    rw [show 2 ^ 2 * q - 1 = 2 ^ 2 * (q - 1) + 3 from by omega]
    simp
  exact v2_eq1_of_mod4_eq3 (2 ^ t - 1) hmod

/-!
## Part 6: Summary of v₂ structure

The mod-4 dichotomy partitions all odd n into:
- **Class 1 mod 4** (50%): immediate descent (1 step). These are the "easy" cases.
- **Class 3 mod 4** (50%): ascent (v₂=1). Need further subclass analysis.

Class 3 mod 4 subdivides by mod 8:
- **Class 3 mod 8** (25%): sN ≡ 1 mod 4, so step 2 descends.
  But two-step ratio is 9/8, so descent below n is NOT guaranteed
  without deeper analysis of v₂ at step 2.
- **Class 7 mod 8** (25%): sN ≡ 3 mod 4, so step 2 is another ascent.
  Need mod 16/32/... analysis.

This recursive structure is exactly why our certificate system works:
finite modular information determines v₂ values, which determine
descent behavior. Deeper certificates handle deeper subclasses.
-/

end ProjetCollatz
