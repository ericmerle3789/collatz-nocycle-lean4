import ProjetCollatz.Phase9FirstReturnMap
import ProjetCollatz.Phase54EmpiricalHypotheses

/-!
# Phase9ErgodicDescent.lean — Partial EventualDescent & Ergodic Axioms

## Sprint P7-B/C: Partial proofs of EventualDescent

For classes 1, 3, 5 mod 8, we can prove EventualDescent directly
(these classes always descend in 1-2 steps).

For class 7 mod 8, we axiomatize the empirical observation and
derive consequences.

Date: 2026-02-15 (Phase 9 Sprint P7)
-/

namespace ProjetCollatz

noncomputable section

open ProjetCollatz

/-!
## 1. EventualDescent for class 1: one step suffices

For n ≡ 1 mod 8, n > 1: syracuseNext n < n (already proved).
So nSeq n 1 < n.
-/

/-- syracuseNext n > 0 for any n, via the spec: sN(n) * 2^a = 3n+1 -/
theorem syracuseNext_pos (n : ℕ) : syracuseNext n > 0 := by
  by_contra h
  push_neg at h
  have h0 : syracuseNext n = 0 := by omega
  have hspec := syracuseNext_spec n
  rw [h0, Nat.zero_mul] at hspec
  omega

/-- EventualDescent holds for all n ≡ 1 mod 8 -/
theorem eventual_descent_class1 (n : ℕ) (h1 : n % 8 = 1) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  exact ⟨1, descent_class1 n h1 hn, syracuseNext_pos n⟩

/-- EventualDescent holds for all n ≡ 5 mod 8 -/
theorem eventual_descent_class5 (n : ℕ) (h5 : n % 8 = 5) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  exact ⟨1, descent_class5 n h5 hn, syracuseNext_pos n⟩

/-!
## 2. EventualDescent for class 3: two steps suffice

For n ≡ 3 mod 8, n > 1:
  - syracuseNext n ≡ 1 or 5 mod 8 (proved)
  - syracuseNext (syracuseNext n) < syracuseNext n (proved for class 1 and 5)
  - But we need: ∃ step, nSeq n step < n
  - Problem: syracuseNext n might be > n! (3n+1 divided by only 2)
  - However: nSeq n 2 = syracuseNext(syracuseNext n) < syracuseNext n
  - We need: syracuseNext(syracuseNext n) < n
  - This is NOT always true for class 3 (counter: n=3, sN(3)=5, sN(5)=1 < 3 ✓)
  - Actually for n ≡ 3 mod 8: v2(3n+1) = v2(3·(8m+3)+1) = v2(24m+10) = v2(2(12m+5)) = 1
  - So syracuseNext n = (3n+1)/2 > n for n > 1
  - Then we need sN(sN(n)) < n
  - sN(n) = (3n+1)/2, class 1 or 5
  - For class 1: sN(sN(n)) = (3·(3n+1)/2 + 1) / 2^v2(...)
  - This is complex. Let's just state what we CAN prove.
-/

/-- For n ≡ 3 mod 8, n > 1: the two-step result lands in class {1,5} -/
theorem class3_two_step_class (n : ℕ) (h3 : n % 8 = 3) (hn : 1 < n) :
    syracuseNext n % 8 = 1 ∨ syracuseNext n % 8 = 5 :=
  class3_to_class1_or_5 n h3 hn

/-- For n ≡ 3 mod 8, n > 1: after two steps we are strictly below
    the intermediate value (but not necessarily below n) -/
theorem class3_two_step_local_descent (n : ℕ) (h3 : n % 8 = 3) (hn : 1 < n)
    (hsn_gt : syracuseNext n > 1) :
    nSeq n 2 < syracuseNext n := by
  show syracuseNext (nSeq n 1) < syracuseNext n
  simp [nSeq]
  have h15 := class3_to_class1_or_5 n h3 hn
  exact transit_class1or5_descent (syracuseNext n) h15 hsn_gt

/-!
## 2b. The Salmon Trap: mod 16 refinement of the class 3 split

The class 3 → {1, 5} transition is determined by bit 4 (the 16s position):
- n ≡ 3 mod 16 → sN(n) ≡ 5 mod 8 → ABYSS (v₂ ≥ 3, deep compression)
- n ≡ 11 mod 16 → sN(n) ≡ 1 mod 8 → gentle descent (v₂ = 2)

This is the "salmon trap": the salmon (class 7 number) must pass through
class 3, where bit 4 determines if it falls into the abyss. The split
is exactly 50/50 among class 3 numbers.

Sprint P8 — Salmon Hypothesis (Eric Merle's intuition)
-/

/-- Salmon Trap part 1: n ≡ 3 mod 16 → sN(n) ≡ 5 mod 8 (ABYSS) -/
theorem salmon_trap_abyss (n : ℕ) (h : n % 16 = 3) :
    syracuseNext n % 8 = 5 := by
  have h8 : n % 8 = 3 := by omega
  have hv2 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  simp [syracuseNext, hv2]
  omega

/-- Salmon Trap part 2: n ≡ 11 mod 16 → sN(n) ≡ 1 mod 8 (gentle passage) -/
theorem salmon_trap_passage (n : ℕ) (h : n % 16 = 11) :
    syracuseNext n % 8 = 1 := by
  have h8 : n % 8 = 3 := by omega
  have hv2 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  simp [syracuseNext, hv2]
  omega

/-- The class 3 split is exactly determined by bit 4:
    every n ≡ 3 mod 8 is either ≡ 3 mod 16 or ≡ 11 mod 16 -/
theorem class3_bit4_dichotomy (n : ℕ) (h : n % 8 = 3) :
    n % 16 = 3 ∨ n % 16 = 11 := by
  omega

/-!
## 2c. EventualDescent for n ≡ 3 mod 16 (ABYSS descent in 2 steps)

For n ≡ 3 mod 16:
  - v₂(3n+1) = 1, so sN(n) × 2 = 3n+1 (one division by 2)
  - sN(n) ≡ 5 mod 8 (salmon_trap_abyss), so v₂ ≥ 3
  - nSeq n 2 × 2^v = 3·sN(n)+1, with 2^v ≥ 8
  - Bound: nSeq n 2 × 16 ≤ 9n+5 < 16n for n ≥ 1

Sprint mod16_eq3 — +12.5% modulaire coverage (57.8% → 70.3%).
PURE THEOREM — no axiom needed.
-/

/-- EventualDescent for n ≡ 3 mod 16: descent in exactly 2 steps.
    Chain: n ≡ 3 mod 16 (class 3) → sN(n) ≡ 5 mod 8 (ABYSS) → descent.
    v₂ = [1, ≥3]. Cumulative: 3²/2^(1+3) = 9/16 < 1. -/
theorem eventual_descent_mod16_eq3 (n : ℕ) (hmod : n % 16 = 3) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 3 mod 8), so sN(n) × 2 = 3n+1
  have h8 : n % 8 = 3 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- hspec1 : syracuseNext n * 2 = 3 * n + 1
  -- Step 2: sN(n) ≡ 5 mod 8 (abyss), v₂ ≥ 3
  have h_sn_class5 : syracuseNext n % 8 = 5 := salmon_trap_abyss n hmod
  have h_sn_gt1 : syracuseNext n > 1 := by omega
  have hv2 : 3 ≤ v2_3n1 (syracuseNext n) := v2_mod8_eq5_ge3 _ h_sn_class5
  have hspec2 := syracuseNext_spec (syracuseNext n)
  -- 2^v₂ ≥ 8
  have hpow_ge : 8 ≤ 2 ^ v2_3n1 (syracuseNext n) := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ v2_3n1 (syracuseNext n) := Nat.pow_le_pow_right (by norm_num) hv2
  -- sN₂ × 8 ≤ 3·sN + 1
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have hle8 : s2 * 8 ≤ 3 * s1 + 1 := by
    calc s2 * 8
        ≤ s2 * 2 ^ v2_3n1 s1 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s1 + 1 := hspec2
  -- Eliminate s1 to get bound on s2 in terms of n
  -- s1 * 2 = 3n+1, so 6*s1 = 3*(3n+1) = 9n+3
  have h_6s1 : 6 * s1 = 9 * n + 3 := by linarith [hspec1]
  -- s2 * 16 ≤ 2*(3*s1+1) = 6*s1+2 = 9n+5
  have h_s2_16 : s2 * 16 ≤ 9 * n + 5 := by linarith [hle8]
  -- 9n+5 < 16n for n ≥ 1 (n ≡ 3 mod 16 → n ≥ 3)
  have h_n_ge : n ≥ 3 := by omega
  have hs2_lt : s2 < n := by omega
  have hs2_pos : s2 > 0 := syracuseNext_pos s1
  exact ⟨2, hs2_lt, hs2_pos⟩

/-!
## 2d. EventualDescent for n ≡ 11 mod 64 (PASSAGE → CLASS 1 → ABYSS in 3 steps)

For n ≡ 11 mod 64:
  - v₂(3n+1) = 1 (n ≡ 3 mod 8), so sN(n) × 2 = 3n+1
  - sN(n) ≡ 1 mod 8 (salmon_trap_passage), so v₂ = 2, sN₂ × 4 = 3·sN+1
  - sN₂ ≡ 5 mod 8 (arithmetic: sN₂ × 8 = 9n+5, n ≡ 11 mod 64)
  - v₂(3·sN₂+1) ≥ 3 (class 5 abyss), so sN₃ × 8 ≤ 3·sN₂+1
  - Bound: sN₃ × 64 ≤ 27n+23 < 64n for n ≥ 1

Cumulative ratio: 3³/2^(1+2+3) = 27/64 ≈ 0.422 < 1.
Sprint mod64_eq11 — this is a sub-case of GAP #4 (mod16=11).
-/

/-- EventualDescent for n ≡ 11 mod 64: descent in exactly 3 steps.
    Chain: n ≡ 11 mod 64 (class 3) → sN ≡ 1 mod 8 (passage)
    → sN₂ ≡ 5 mod 8 (abyss) → descent.
    v₂ = [1, 2, ≥3]. Cumulative: 3³/2^(1+2+3) = 27/64 < 1. -/
theorem eventual_descent_mod64_eq11 (n : ℕ) (hmod : n % 64 = 11) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 3 mod 8)
  have h8 : n % 8 = 3 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- hspec1 : syracuseNext n * 2 = 3 * n + 1
  -- Step 2: sN ≡ 1 mod 8 (passage), v₂ = 2
  have h16 : n % 16 = 11 := by omega
  have h_sn_class1 : syracuseNext n % 8 = 1 := salmon_trap_passage n h16
  have hv2 : v2_3n1 (syracuseNext n) = 2 := v2_mod8_eq1 _ h_sn_class1
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- hspec2 : syracuseNext (syracuseNext n) * 4 = 3 * syracuseNext n + 1
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  -- Key identity: s2 * 8 = 9n + 5
  have h_s2_8 : s2 * 8 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: sN₂ ≡ 5 mod 8 (abyss from arithmetic)
  have h_s2_class5 : s2 % 8 = 5 := by omega
  have hv3 : 3 ≤ v2_3n1 s2 := v2_mod8_eq5_ge3 _ h_s2_class5
  have hspec3 := syracuseNext_spec s2
  -- 2^v₃ ≥ 8
  have hpow_ge : 8 ≤ 2 ^ v2_3n1 s2 := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ v2_3n1 s2 := Nat.pow_le_pow_right (by norm_num) hv3
  set s3 := syracuseNext s2
  -- s3 * 8 ≤ 3 * s2 + 1
  have hle8 : s3 * 8 ≤ 3 * s2 + 1 := by
    calc s3 * 8
        ≤ s3 * 2 ^ v2_3n1 s2 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s2 + 1 := hspec3
  -- s3 * 64 ≤ 27n + 23
  have h_s3_64 : s3 * 64 ≤ 27 * n + 23 := by linarith [hle8, h_s2_8]
  -- 27n + 23 < 64n for n ≥ 11 (n ≡ 11 mod 64 → n ≥ 11)
  have h_n_ge : n ≥ 11 := by omega
  have hs3_lt : s3 < n := by omega
  have hs3_pos : s3 > 0 := syracuseNext_pos s2
  exact ⟨3, hs3_lt, hs3_pos⟩

/-!
## 2e. EventualDescent for n ≡ 59 mod 128 (4 steps via class 3 → ABYSS)

For n ≡ 59 mod 128:
  - Steps 1-2 same as mod16=11: v₂=[1,2], giving s2*8 = 9n+5
  - s2 ≡ 3 mod 16 (arithmetic), so salmon_trap_abyss applies: s3 ≡ 5 mod 8
  - v₂(s2)=1 (class 3): s3*2 = 3*s2+1 → s3*16 = 27n+23
  - v₂(s3)≥3 (class 5 ABYSS): s4*8 ≤ 3*s3+1
  - Bound: s4*128 ≤ 81n+85 < 128n for n ≥ 2

Cumulative ratio: 3⁴/2^(1+2+1+3) = 81/128 ≈ 0.633 < 1.
-/

/-- EventualDescent for n ≡ 59 mod 128: descent in 4 steps.
    Chain: n (class 3) → sN (class 1, passage) → sN₂ (class 3, mod16=3)
    → sN₃ (class 5, ABYSS) → descent.
    v₂ = [1, 2, 1, ≥3]. Cumulative: 3⁴/2^7 = 81/128 < 1. -/
theorem eventual_descent_mod128_eq59 (n : ℕ) (hmod : n % 128 = 59) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 3 mod 8)
  have h8 : n % 8 = 3 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: sN ≡ 1 mod 8 (passage), v₂ = 2
  have h16 : n % 16 = 11 := by omega
  have h_sn_class1 : syracuseNext n % 8 = 1 := salmon_trap_passage n h16
  have hv2 : v2_3n1 (syracuseNext n) = 2 := v2_mod8_eq1 _ h_sn_class1
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_8 : s2 * 8 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 3 mod 16 → salmon_trap_abyss → s3 ≡ 5 mod 8
  have h_s2_mod16 : s2 % 16 = 3 := by omega
  have h_s2_mod8 : s2 % 8 = 3 := by omega
  have hv3 : v2_3n1 s2 = 1 := v2_mod8_eq3 s2 h_s2_mod8
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  -- s3 * 16 = 27n + 23
  have h_s3_16 : s3 * 16 = 27 * n + 23 := by linarith [hspec3, h_s2_8]
  -- s3 ≡ 5 mod 8 (abyss) — from salmon_trap_abyss on s2
  have h_s3_class5 : s3 % 8 = 5 := salmon_trap_abyss s2 h_s2_mod16
  -- Step 4: v₂ ≥ 3 (class 5)
  have hv4 : 3 ≤ v2_3n1 s3 := v2_mod8_eq5_ge3 _ h_s3_class5
  have hspec4 := syracuseNext_spec s3
  have hpow_ge : 8 ≤ 2 ^ v2_3n1 s3 := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ v2_3n1 s3 := Nat.pow_le_pow_right (by norm_num) hv4
  set s4 := syracuseNext s3
  have hle8 : s4 * 8 ≤ 3 * s3 + 1 := by
    calc s4 * 8
        ≤ s4 * 2 ^ v2_3n1 s3 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s3 + 1 := hspec4
  -- s4 * 128 ≤ 81n + 85
  have h_s4_128 : s4 * 128 ≤ 81 * n + 85 := by linarith [hle8, h_s3_16]
  have h_n_ge : n ≥ 59 := by omega
  have hs4_lt : s4 < n := by omega
  have hs4_pos : s4 > 0 := syracuseNext_pos s3
  exact ⟨4, hs4_lt, hs4_pos⟩

/-!
## 2f. EventualDescent for n ≡ 43 mod 256 (4 steps via class 1 → ABYSS)

For n ≡ 43 mod 256:
  - Steps 1-2 same as mod16=11: v₂=[1,2], giving s2*8 = 9n+5
  - s2 ≡ 1 mod 8 (class 1, v₂=2): s3*4 = 3*s2+1 → s3*32 = 27n+23
  - s3 ≡ 5 mod 8 (arithmetic: s3*32=27n+23, n%256=43)
  - v₂(s3)≥3 (class 5 ABYSS): s4*8 ≤ 3*s3+1
  - Bound: s4*256 ≤ 81n+101 < 256n for n ≥ 1

Cumulative ratio: 3⁴/2^(1+2+2+3) = 81/256 ≈ 0.316 < 1.
-/

/-- EventualDescent for n ≡ 43 mod 256: descent in 4 steps.
    Chain: n (class 3) → sN (class 1, passage) → sN₂ (class 1)
    → sN₃ (class 5, ABYSS) → descent.
    v₂ = [1, 2, 2, ≥3]. Cumulative: 3⁴/2^8 = 81/256 < 1. -/
theorem eventual_descent_mod256_eq43 (n : ℕ) (hmod : n % 256 = 43) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 3 mod 8)
  have h8 : n % 8 = 3 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: sN ≡ 1 mod 8 (passage), v₂ = 2
  have h16 : n % 16 = 11 := by omega
  have h_sn_class1 : syracuseNext n % 8 = 1 := salmon_trap_passage n h16
  have hv2 : v2_3n1 (syracuseNext n) = 2 := v2_mod8_eq1 _ h_sn_class1
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_8 : s2 * 8 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 1 mod 8 (class 1), v₂ = 2
  have h_s2_class1 : s2 % 8 = 1 := by omega
  have hv3 : v2_3n1 s2 = 2 := v2_mod8_eq1 s2 h_s2_class1
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  -- s3 * 32 = 27n + 23
  have h_s3_32 : s3 * 32 = 27 * n + 23 := by linarith [hspec3, h_s2_8]
  -- s3 ≡ 5 mod 8 (abyss)
  have h_s3_class5 : s3 % 8 = 5 := by omega
  -- Step 4: v₂ ≥ 3 (class 5)
  have hv4 : 3 ≤ v2_3n1 s3 := v2_mod8_eq5_ge3 _ h_s3_class5
  have hspec4 := syracuseNext_spec s3
  have hpow_ge : 8 ≤ 2 ^ v2_3n1 s3 := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ v2_3n1 s3 := Nat.pow_le_pow_right (by norm_num) hv4
  set s4 := syracuseNext s3
  have hle8 : s4 * 8 ≤ 3 * s3 + 1 := by
    calc s4 * 8
        ≤ s4 * 2 ^ v2_3n1 s3 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s3 + 1 := hspec4
  -- s4 * 256 ≤ 81n + 101
  have h_s4_256 : s4 * 256 ≤ 81 * n + 101 := by linarith [hle8, h_s3_32]
  have h_n_ge : n ≥ 43 := by omega
  have hs4_lt : s4 < n := by omega
  have hs4_pos : s4 > 0 := syracuseNext_pos s3
  exact ⟨4, hs4_lt, hs4_pos⟩

/-- **Descent for n ≡ 43 mod 64** in exactly 3 steps (generalization of mod256=43).
    v₂ pattern: [1, 2, 2]. Cumulative ratio: 3³/2⁵ = 27/32 < 1.
    Chain: n (class 3) →[v₂=1] s1 (class 1) →[v₂=2] s2 (class 1) →[v₂=2] s3
    Algebraic: n=64q+43, s1=96q+65, s2=72q+49, s3=54q+37.
    Covers ALL 16 residues ≡ 43 mod 64, including 12 previously uncovered. -/
theorem eventual_descent_mod64_eq43 (n : ℕ) (hmod : n % 64 = 43) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 3 mod 8)
  have h8 : n % 8 = 3 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: s1 ≡ 1 mod 8 (passage), v₂ = 2
  have h16 : n % 16 = 11 := by omega
  have h_s1_class1 : syracuseNext n % 8 = 1 := salmon_trap_passage n h16
  have hv2 : v2_3n1 (syracuseNext n) = 2 := v2_mod8_eq1 _ h_s1_class1
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_8 : s2 * 8 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 1 mod 8 (class 1), v₂ = 2
  have h_s2_class1 : s2 % 8 = 1 := by omega
  have hv3 : v2_3n1 s2 = 2 := v2_mod8_eq1 _ h_s2_class1
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_32 : s3 * 32 = 27 * n + 23 := by linarith [hspec3, h_s2_8]
  have h_n_ge : n ≥ 43 := by omega
  have hs3_lt : s3 < n := by omega
  have hs3_pos : s3 > 0 := syracuseNext_pos s2
  exact ⟨3, hs3_lt, hs3_pos⟩

/-- **Descent for n ≡ 123 mod 256** in at most 5 steps.
    v₂ pattern: [1, 2, 1, 2, ≥2]. Cumulative ratio: 3⁵/2⁸ = 243/256 < 1.
    Chain: n (mod8=3) → s1 (mod8=1) → s2 (mod8=3) → s3 (mod8=1) → s4 (mod4=1) → s5.
    Algebraic: s4*64 = 81n+85, then s5*256 ≤ 243n+319 < 256n.
    Covers 4 previously uncovered residues: {123, 379, 635, 891} mod 1024. -/
theorem eventual_descent_mod256_eq123 (n : ℕ) (hmod : n % 256 = 123) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 3 mod 8)
  have h8 : n % 8 = 3 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: s1 ≡ 1 mod 8 (passage), v₂ = 2
  have h16 : n % 16 = 11 := by omega
  have h_s1_class1 : syracuseNext n % 8 = 1 := salmon_trap_passage n h16
  have hv2 : v2_3n1 (syracuseNext n) = 2 := v2_mod8_eq1 _ h_s1_class1
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_8 : s2 * 8 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 3 mod 8, v₂ = 1
  have h_s2_class3 : s2 % 8 = 3 := by omega
  have hv3 : v2_3n1 s2 = 1 := v2_mod8_eq3 _ h_s2_class3
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_16 : s3 * 16 = 27 * n + 23 := by linarith [hspec3, h_s2_8]
  -- Step 4: s3 ≡ 1 mod 8, v₂ = 2
  have h_s3_class1 : s3 % 8 = 1 := by omega
  have hv4 : v2_3n1 s3 = 2 := v2_mod8_eq1 _ h_s3_class1
  have hspec4 := syracuseNext_spec s3
  rw [hv4] at hspec4; simp at hspec4
  set s4 := syracuseNext s3
  have h_s4_64 : s4 * 64 = 81 * n + 85 := by linarith [hspec4, h_s3_16]
  -- Step 5: s4 ≡ 1 mod 4, v₂ ≥ 2 → s5*4 ≤ 3*s4+1
  have h_s4_mod4 : s4 % 4 = 1 := by omega
  have hv5 : 2 ≤ v2_3n1 s4 := v2_mod4_eq1_ge2 _ h_s4_mod4
  set s5 := syracuseNext s4
  have h_s5_bound : s5 * 4 ≤ 3 * s4 + 1 := by
    have := descent_v2_ge2_ratio s4 hv5
    omega
  have h_s5_256 : s5 * 256 ≤ 243 * n + 319 := by
    nlinarith [h_s5_bound, h_s4_64]
  have h_n_ge : n ≥ 123 := by omega
  have hs5_lt : s5 < n := by nlinarith
  have hs5_pos : s5 > 0 := syracuseNext_pos s4
  exact ⟨5, hs5_lt, hs5_pos⟩

/-- **Descent for n ≡ 219 mod 256** in at most 5 steps.
    v₂ pattern: [1, 2, 1, 1, ≥3]. Cumulative divisions: ≥ 8.
    Chain: n (mod8=3) → s1 (mod8=1) → s2 (mod8=7) → s3 (mod8=3) → s4 (mod8=5) → s5.
    Algebraic: s4*32 = 81n+85, s4≡5 mod 8 → v₂(3s4+1) ≥ 3 → s5*256 ≤ 243n+287 < 256n.
    Covers 4 previously uncovered residues: {219, 475, 731, 987} mod 1024. -/
theorem eventual_descent_mod256_eq219 (n : ℕ) (hmod : n % 256 = 219) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 3 mod 8)
  have h8 : n % 8 = 3 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: s1 ≡ 1 mod 8 (salmon passage), v₂ = 2
  have h16 : n % 16 = 11 := by omega
  have h_s1_class1 : syracuseNext n % 8 = 1 := salmon_trap_passage n h16
  have hv2 : v2_3n1 (syracuseNext n) = 2 := v2_mod8_eq1 _ h_s1_class1
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_8 : s2 * 8 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 7 mod 8, v₂ = 1
  have h_s2_mod8 : s2 % 8 = 7 := by omega
  have hv3 : v2_3n1 s2 = 1 := v2_mod8_eq7 _ h_s2_mod8
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_16 : s3 * 16 = 27 * n + 23 := by linarith [hspec3, h_s2_8]
  -- Step 4: s3 ≡ 3 mod 8, v₂ = 1
  have h_s3_mod8 : s3 % 8 = 3 := by omega
  have hv4 : v2_3n1 s3 = 1 := v2_mod8_eq3 _ h_s3_mod8
  have hspec4 := syracuseNext_spec s3
  rw [hv4] at hspec4; simp at hspec4
  set s4 := syracuseNext s3
  have h_s4_32 : s4 * 32 = 81 * n + 85 := by linarith [hspec4, h_s3_16]
  -- Step 5: s4 ≡ 5 mod 8 → v₂(3s4+1) ≥ 3 → s5*8 ≤ 3*s4+1
  have h_s4_mod8 : s4 % 8 = 5 := by omega
  have hv5 : 3 ≤ v2_3n1 s4 := v2_mod8_eq5_ge3 _ h_s4_mod8
  set s5 := syracuseNext s4
  have h_s5_bound : s5 * 8 ≤ 3 * s4 + 1 := by
    have hspec5 := syracuseNext_spec s4
    have hpow_ge : 8 ≤ 2 ^ (v2_3n1 s4) := by
      calc 8 = 2 ^ 3 := by norm_num
           _ ≤ 2 ^ (v2_3n1 s4) := Nat.pow_le_pow_right (by norm_num) hv5
    calc s5 * 8 ≤ s5 * (2 ^ (v2_3n1 s4)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
         _ = 3 * s4 + 1 := hspec5
  -- Final bound: s5*256 ≤ 243*n + 287 < 256*n
  have h_s5_256 : s5 * 256 ≤ 243 * n + 287 := by nlinarith [h_s5_bound, h_s4_32]
  have h_n_ge : n ≥ 219 := by omega
  have hs5_lt : s5 < n := by nlinarith
  have hs5_pos : s5 > 0 := syracuseNext_pos s4
  exact ⟨5, hs5_lt, hs5_pos⟩

/-!
## 2g. Cycle 107 — Near-Perfect Tier 1 Descent (9 theorems, mod 1024)

All 9 residues below have 6-step descent chains with ratio 729/1024 < 1.
The first 5 steps are deterministic (exact v₂ values), and the 6th step
uses a v₂ lower bound (≥3, ≥4, or ≥5) based on the modular class of s5.
Together they cover 9 new residues mod 1024, raising coverage from 439 to 448/512.
-/

/-- **Descent for n ≡ 347 mod 1024** in at most 6 steps.
    v₂ pattern: [1,2,1,1,2,≥3]. Final divisor: 1024 = 128·8.
    s5·128 = 243n+287, s6·1024 ≤ 729n+989 < 1024n for n≥347. -/
theorem eventual_descent_mod1024_eq347 (n : ℕ) (hmod : n % 1024 = 347) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 3 mod 8)
  have h8 : n % 8 = 3 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: salmon passage (n ≡ 11 mod 16 → s1 ≡ 1 mod 8), v₂ = 2
  have h16 : n % 16 = 11 := by omega
  have h_s1_class1 : syracuseNext n % 8 = 1 := salmon_trap_passage n h16
  have hv2 : v2_3n1 (syracuseNext n) = 2 := v2_mod8_eq1 _ h_s1_class1
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_8 : s2 * 8 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 7 mod 8, v₂ = 1
  have h_s2_mod8 : s2 % 8 = 7 := by omega
  have hv3 : v2_3n1 s2 = 1 := v2_mod8_eq7 _ h_s2_mod8
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_16 : s3 * 16 = 27 * n + 23 := by linarith [hspec3, h_s2_8]
  -- Step 4: s3 ≡ 3 mod 8, v₂ = 1
  have h_s3_mod8 : s3 % 8 = 3 := by omega
  have hv4 : v2_3n1 s3 = 1 := v2_mod8_eq3 _ h_s3_mod8
  have hspec4 := syracuseNext_spec s3
  rw [hv4] at hspec4; simp at hspec4
  set s4 := syracuseNext s3
  have h_s4_32 : s4 * 32 = 81 * n + 85 := by linarith [hspec4, h_s3_16]
  -- Step 5: s4 ≡ 1 mod 8, v₂ = 2
  have h_s4_mod8 : s4 % 8 = 1 := by omega
  have hv5 : v2_3n1 s4 = 2 := v2_mod8_eq1 _ h_s4_mod8
  have hspec5 := syracuseNext_spec s4
  rw [hv5] at hspec5; simp at hspec5
  set s5 := syracuseNext s4
  have h_s5_128 : s5 * 128 = 243 * n + 287 := by linarith [hspec5, h_s4_32]
  -- Step 6: s5 % 8 = 5, v₂(3s5+1) ≥ 3
  have h_s5_mod8 : s5 % 8 = 5 := by omega
  have hv6 : 3 ≤ v2_3n1 s5 := v2_mod8_eq5_ge3 _ h_s5_mod8
  set s6 := syracuseNext s5
  have h_s6_bound : s6 * 8 ≤ 3 * s5 + 1 := by
    have hspec6 := syracuseNext_spec s5
    have hpow_ge : 8 ≤ 2 ^ (v2_3n1 s5) := by
      calc 8 = 2 ^ 3 := by norm_num
           _ ≤ 2 ^ (v2_3n1 s5) := Nat.pow_le_pow_right (by norm_num) hv6
    calc s6 * 8 ≤ s6 * (2 ^ (v2_3n1 s5)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
         _ = 3 * s5 + 1 := hspec6
  -- Final: s6·1024 ≤ 729n+989 < 1024n for n≥347
  have h_final : s6 * 1024 ≤ 729 * n + 989 := by nlinarith [h_s6_bound, h_s5_128]
  have h_n_ge : n ≥ 347 := by omega
  have hs6_lt : s6 < n := by nlinarith
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  exact ⟨6, hs6_lt, hs6_pos⟩

/-- **Descent for n ≡ 507 mod 1024** in at most 6 steps.
    v₂ pattern: [1,2,1,2,1,≥3]. Final divisor: 1024 = 128·8.
    s5·128 = 243n+319, s6·1024 ≤ 729n+1085 < 1024n for n≥507. -/
theorem eventual_descent_mod1024_eq507 (n : ℕ) (hmod : n % 1024 = 507) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 3 mod 8)
  have h8 : n % 8 = 3 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: salmon passage (n ≡ 11 mod 16 → s1 ≡ 1 mod 8), v₂ = 2
  have h16 : n % 16 = 11 := by omega
  have h_s1_class1 : syracuseNext n % 8 = 1 := salmon_trap_passage n h16
  have hv2 : v2_3n1 (syracuseNext n) = 2 := v2_mod8_eq1 _ h_s1_class1
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_8 : s2 * 8 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 3 mod 8, v₂ = 1
  have h_s2_mod8 : s2 % 8 = 3 := by omega
  have hv3 : v2_3n1 s2 = 1 := v2_mod8_eq3 _ h_s2_mod8
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_16 : s3 * 16 = 27 * n + 23 := by linarith [hspec3, h_s2_8]
  -- Step 4: s3 ≡ 1 mod 8, v₂ = 2
  have h_s3_mod8 : s3 % 8 = 1 := by omega
  have hv4 : v2_3n1 s3 = 2 := v2_mod8_eq1 _ h_s3_mod8
  have hspec4 := syracuseNext_spec s3
  rw [hv4] at hspec4; simp at hspec4
  set s4 := syracuseNext s3
  have h_s4_64 : s4 * 64 = 81 * n + 85 := by linarith [hspec4, h_s3_16]
  -- Step 5: s4 ≡ 3 mod 8, v₂ = 1
  have h_s4_mod8 : s4 % 8 = 3 := by omega
  have hv5 : v2_3n1 s4 = 1 := v2_mod8_eq3 _ h_s4_mod8
  have hspec5 := syracuseNext_spec s4
  rw [hv5] at hspec5; simp at hspec5
  set s5 := syracuseNext s4
  have h_s5_128 : s5 * 128 = 243 * n + 319 := by linarith [hspec5, h_s4_64]
  -- Step 6: s5 % 8 = 5, v₂(3s5+1) ≥ 3
  have h_s5_mod8 : s5 % 8 = 5 := by omega
  have hv6 : 3 ≤ v2_3n1 s5 := v2_mod8_eq5_ge3 _ h_s5_mod8
  set s6 := syracuseNext s5
  have h_s6_bound : s6 * 8 ≤ 3 * s5 + 1 := by
    have hspec6 := syracuseNext_spec s5
    have hpow_ge : 8 ≤ 2 ^ (v2_3n1 s5) := by
      calc 8 = 2 ^ 3 := by norm_num
           _ ≤ 2 ^ (v2_3n1 s5) := Nat.pow_le_pow_right (by norm_num) hv6
    calc s6 * 8 ≤ s6 * (2 ^ (v2_3n1 s5)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
         _ = 3 * s5 + 1 := hspec6
  -- Final: s6·1024 ≤ 729n+1085 < 1024n for n≥507
  have h_final : s6 * 1024 ≤ 729 * n + 1085 := by nlinarith [h_s6_bound, h_s5_128]
  have h_n_ge : n ≥ 507 := by omega
  have hs6_lt : s6 < n := by nlinarith
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  exact ⟨6, hs6_lt, hs6_pos⟩

/-- **Descent for n ≡ 923 mod 1024** in at most 6 steps.
    v₂ pattern: [1,2,1,1,1,≥4]. Final divisor: 1024 = 64·16.
    s5·64 = 243n+287, s6·1024 ≤ 729n+925 < 1024n for n≥923. -/
theorem eventual_descent_mod1024_eq923 (n : ℕ) (hmod : n % 1024 = 923) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 3 mod 8)
  have h8 : n % 8 = 3 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq3 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: salmon passage (n ≡ 11 mod 16 → s1 ≡ 1 mod 8), v₂ = 2
  have h16 : n % 16 = 11 := by omega
  have h_s1_class1 : syracuseNext n % 8 = 1 := salmon_trap_passage n h16
  have hv2 : v2_3n1 (syracuseNext n) = 2 := v2_mod8_eq1 _ h_s1_class1
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_8 : s2 * 8 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 7 mod 8, v₂ = 1
  have h_s2_mod8 : s2 % 8 = 7 := by omega
  have hv3 : v2_3n1 s2 = 1 := v2_mod8_eq7 _ h_s2_mod8
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_16 : s3 * 16 = 27 * n + 23 := by linarith [hspec3, h_s2_8]
  -- Step 4: s3 ≡ 7 mod 8, v₂ = 1
  have h_s3_mod8 : s3 % 8 = 7 := by omega
  have hv4 : v2_3n1 s3 = 1 := v2_mod8_eq7 _ h_s3_mod8
  have hspec4 := syracuseNext_spec s3
  rw [hv4] at hspec4; simp at hspec4
  set s4 := syracuseNext s3
  have h_s4_32 : s4 * 32 = 81 * n + 85 := by linarith [hspec4, h_s3_16]
  -- Step 5: s4 ≡ 3 mod 8, v₂ = 1
  have h_s4_mod8 : s4 % 8 = 3 := by omega
  have hv5 : v2_3n1 s4 = 1 := v2_mod8_eq3 _ h_s4_mod8
  have hspec5 := syracuseNext_spec s4
  rw [hv5] at hspec5; simp at hspec5
  set s5 := syracuseNext s4
  have h_s5_64 : s5 * 64 = 243 * n + 287 := by linarith [hspec5, h_s4_32]
  -- Step 6: s5 % 16 = 5, v₂(3s5+1) ≥ 4
  have h_s5_mod16 : s5 % 16 = 5 := by omega
  have hv6 : 4 ≤ v2_3n1 s5 := v2_mod16_eq5_ge4 _ h_s5_mod16
  set s6 := syracuseNext s5
  have h_s6_bound : s6 * 16 ≤ 3 * s5 + 1 := by
    have hspec6 := syracuseNext_spec s5
    have hpow_ge : 16 ≤ 2 ^ (v2_3n1 s5) := by
      calc 16 = 2 ^ 4 := by norm_num
           _ ≤ 2 ^ (v2_3n1 s5) := Nat.pow_le_pow_right (by norm_num) hv6
    calc s6 * 16 ≤ s6 * (2 ^ (v2_3n1 s5)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
         _ = 3 * s5 + 1 := hspec6
  -- Final: s6·1024 ≤ 729n+925 < 1024n for n≥923
  have h_final : s6 * 1024 ≤ 729 * n + 925 := by nlinarith [h_s6_bound, h_s5_64]
  have h_n_ge : n ≥ 923 := by omega
  have hs6_lt : s6 < n := by nlinarith
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  exact ⟨6, hs6_lt, hs6_pos⟩

/-- **Descent for n ≡ 423 mod 1024** in at most 6 steps.
    v₂ pattern: [1,1,2,1,2,≥3]. Final divisor: 1024 = 128·8.
    s5·128 = 243n+251, s6·1024 ≤ 729n+881 < 1024n for n≥423. -/
theorem eventual_descent_mod1024_eq423 (n : ℕ) (hmod : n % 1024 = 423) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 7 mod 8)
  have h8 : n % 8 = 7 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: s1 ≡ 3 mod 8, v₂ = 1
  have h_sn1_mod8 : syracuseNext n % 8 = 3 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn1_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_4 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 1 mod 8, v₂ = 2
  have h_s2_mod8 : s2 % 8 = 1 := by omega
  have hv3 : v2_3n1 s2 = 2 := v2_mod8_eq1 _ h_s2_mod8
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_16 : s3 * 16 = 27 * n + 19 := by linarith [hspec3, h_s2_4]
  -- Step 4: s3 ≡ 3 mod 8, v₂ = 1
  have h_s3_mod8 : s3 % 8 = 3 := by omega
  have hv4 : v2_3n1 s3 = 1 := v2_mod8_eq3 _ h_s3_mod8
  have hspec4 := syracuseNext_spec s3
  rw [hv4] at hspec4; simp at hspec4
  set s4 := syracuseNext s3
  have h_s4_32 : s4 * 32 = 81 * n + 73 := by linarith [hspec4, h_s3_16]
  -- Step 5: s4 ≡ 1 mod 8, v₂ = 2
  have h_s4_mod8 : s4 % 8 = 1 := by omega
  have hv5 : v2_3n1 s4 = 2 := v2_mod8_eq1 _ h_s4_mod8
  have hspec5 := syracuseNext_spec s4
  rw [hv5] at hspec5; simp at hspec5
  set s5 := syracuseNext s4
  have h_s5_128 : s5 * 128 = 243 * n + 251 := by linarith [hspec5, h_s4_32]
  -- Step 6: s5 % 8 = 5, v₂(3s5+1) ≥ 3
  have h_s5_mod8 : s5 % 8 = 5 := by omega
  have hv6 : 3 ≤ v2_3n1 s5 := v2_mod8_eq5_ge3 _ h_s5_mod8
  set s6 := syracuseNext s5
  have h_s6_bound : s6 * 8 ≤ 3 * s5 + 1 := by
    have hspec6 := syracuseNext_spec s5
    have hpow_ge : 8 ≤ 2 ^ (v2_3n1 s5) := by
      calc 8 = 2 ^ 3 := by norm_num
           _ ≤ 2 ^ (v2_3n1 s5) := Nat.pow_le_pow_right (by norm_num) hv6
    calc s6 * 8 ≤ s6 * (2 ^ (v2_3n1 s5)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
         _ = 3 * s5 + 1 := hspec6
  -- Final: s6·1024 ≤ 729n+881 < 1024n for n≥423
  have h_final : s6 * 1024 ≤ 729 * n + 881 := by nlinarith [h_s6_bound, h_s5_128]
  have h_n_ge : n ≥ 423 := by omega
  have hs6_lt : s6 < n := by nlinarith
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  exact ⟨6, hs6_lt, hs6_pos⟩

/-- **Descent for n ≡ 583 mod 1024** in at most 6 steps.
    v₂ pattern: [1,1,2,2,1,≥3]. Final divisor: 1024 = 128·8.
    s5·128 = 243n+283, s6·1024 ≤ 729n+977 < 1024n for n≥583. -/
theorem eventual_descent_mod1024_eq583 (n : ℕ) (hmod : n % 1024 = 583) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 7 mod 8)
  have h8 : n % 8 = 7 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: s1 ≡ 3 mod 8, v₂ = 1
  have h_sn1_mod8 : syracuseNext n % 8 = 3 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn1_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_4 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 1 mod 8, v₂ = 2
  have h_s2_mod8 : s2 % 8 = 1 := by omega
  have hv3 : v2_3n1 s2 = 2 := v2_mod8_eq1 _ h_s2_mod8
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_16 : s3 * 16 = 27 * n + 19 := by linarith [hspec3, h_s2_4]
  -- Step 4: s3 ≡ 1 mod 8, v₂ = 2
  have h_s3_mod8 : s3 % 8 = 1 := by omega
  have hv4 : v2_3n1 s3 = 2 := v2_mod8_eq1 _ h_s3_mod8
  have hspec4 := syracuseNext_spec s3
  rw [hv4] at hspec4; simp at hspec4
  set s4 := syracuseNext s3
  have h_s4_64 : s4 * 64 = 81 * n + 73 := by linarith [hspec4, h_s3_16]
  -- Step 5: s4 ≡ 3 mod 8, v₂ = 1
  have h_s4_mod8 : s4 % 8 = 3 := by omega
  have hv5 : v2_3n1 s4 = 1 := v2_mod8_eq3 _ h_s4_mod8
  have hspec5 := syracuseNext_spec s4
  rw [hv5] at hspec5; simp at hspec5
  set s5 := syracuseNext s4
  have h_s5_128 : s5 * 128 = 243 * n + 283 := by linarith [hspec5, h_s4_64]
  -- Step 6: s5 % 8 = 5, v₂(3s5+1) ≥ 3
  have h_s5_mod8 : s5 % 8 = 5 := by omega
  have hv6 : 3 ≤ v2_3n1 s5 := v2_mod8_eq5_ge3 _ h_s5_mod8
  set s6 := syracuseNext s5
  have h_s6_bound : s6 * 8 ≤ 3 * s5 + 1 := by
    have hspec6 := syracuseNext_spec s5
    have hpow_ge : 8 ≤ 2 ^ (v2_3n1 s5) := by
      calc 8 = 2 ^ 3 := by norm_num
           _ ≤ 2 ^ (v2_3n1 s5) := Nat.pow_le_pow_right (by norm_num) hv6
    calc s6 * 8 ≤ s6 * (2 ^ (v2_3n1 s5)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
         _ = 3 * s5 + 1 := hspec6
  -- Final: s6·1024 ≤ 729n+977 < 1024n for n≥583
  have h_final : s6 * 1024 ≤ 729 * n + 977 := by nlinarith [h_s6_bound, h_s5_128]
  have h_n_ge : n ≥ 583 := by omega
  have hs6_lt : s6 < n := by nlinarith
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  exact ⟨6, hs6_lt, hs6_pos⟩

/-- **Descent for n ≡ 735 mod 1024** in at most 6 steps.
    v₂ pattern: [1,1,1,1,3,≥3]. Final divisor: 1024 = 128·8.
    s5·128 = 243n+211, s6·1024 ≤ 729n+761 < 1024n for n≥735. -/
theorem eventual_descent_mod1024_eq735 (n : ℕ) (hmod : n % 1024 = 735) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 7 mod 8)
  have h8 : n % 8 = 7 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: s1 ≡ 7 mod 8, v₂ = 1
  have h_sn1_mod8 : syracuseNext n % 8 = 7 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq7 _ h_sn1_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_4 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 7 mod 8, v₂ = 1
  have h_s2_mod8 : s2 % 8 = 7 := by omega
  have hv3 : v2_3n1 s2 = 1 := v2_mod8_eq7 _ h_s2_mod8
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_8 : s3 * 8 = 27 * n + 19 := by linarith [hspec3, h_s2_4]
  -- Step 4: s3 ≡ 3 mod 8, v₂ = 1
  have h_s3_mod8 : s3 % 8 = 3 := by omega
  have hv4 : v2_3n1 s3 = 1 := v2_mod8_eq3 _ h_s3_mod8
  have hspec4 := syracuseNext_spec s3
  rw [hv4] at hspec4; simp at hspec4
  set s4 := syracuseNext s3
  have h_s4_16 : s4 * 16 = 81 * n + 65 := by linarith [hspec4, h_s3_8]
  -- Step 5: s4 ≡ 13 mod 16, v₂ = 3 (exact, via v2_mod16_eq13_eq3)
  have h_s4_mod16 : s4 % 16 = 13 := by omega
  have hv5 : v2_3n1 s4 = 3 := v2_mod16_eq13_eq3 _ h_s4_mod16
  have hspec5 := syracuseNext_spec s4
  rw [hv5] at hspec5; simp at hspec5
  set s5 := syracuseNext s4
  have h_s5_128 : s5 * 128 = 243 * n + 211 := by linarith [hspec5, h_s4_16]
  -- Step 6: s5 % 8 = 5, v₂(3s5+1) ≥ 3
  have h_s5_mod8 : s5 % 8 = 5 := by omega
  have hv6 : 3 ≤ v2_3n1 s5 := v2_mod8_eq5_ge3 _ h_s5_mod8
  set s6 := syracuseNext s5
  have h_s6_bound : s6 * 8 ≤ 3 * s5 + 1 := by
    have hspec6 := syracuseNext_spec s5
    have hpow_ge : 8 ≤ 2 ^ (v2_3n1 s5) := by
      calc 8 = 2 ^ 3 := by norm_num
           _ ≤ 2 ^ (v2_3n1 s5) := Nat.pow_le_pow_right (by norm_num) hv6
    calc s6 * 8 ≤ s6 * (2 ^ (v2_3n1 s5)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
         _ = 3 * s5 + 1 := hspec6
  -- Final: s6·1024 ≤ 729n+761 < 1024n for n≥735
  have h_final : s6 * 1024 ≤ 729 * n + 761 := by nlinarith [h_s6_bound, h_s5_128]
  have h_n_ge : n ≥ 735 := by omega
  have hs6_lt : s6 < n := by nlinarith
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  exact ⟨6, hs6_lt, hs6_pos⟩

/-- **Descent for n ≡ 367 mod 1024** in at most 6 steps.
    v₂ pattern: [1,1,1,2,1,≥4]. Final divisor: 1024 = 64·16.
    s5·64 = 243n+227, s6·1024 ≤ 729n+745 < 1024n for n≥367. -/
theorem eventual_descent_mod1024_eq367 (n : ℕ) (hmod : n % 1024 = 367) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 7 mod 8)
  have h8 : n % 8 = 7 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: s1 ≡ 7 mod 8, v₂ = 1
  have h_sn1_mod8 : syracuseNext n % 8 = 7 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq7 _ h_sn1_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_4 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 3 mod 8, v₂ = 1
  have h_s2_mod8 : s2 % 8 = 3 := by omega
  have hv3 : v2_3n1 s2 = 1 := v2_mod8_eq3 _ h_s2_mod8
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_8 : s3 * 8 = 27 * n + 19 := by linarith [hspec3, h_s2_4]
  -- Step 4: s3 ≡ 1 mod 8, v₂ = 2
  have h_s3_mod8 : s3 % 8 = 1 := by omega
  have hv4 : v2_3n1 s3 = 2 := v2_mod8_eq1 _ h_s3_mod8
  have hspec4 := syracuseNext_spec s3
  rw [hv4] at hspec4; simp at hspec4
  set s4 := syracuseNext s3
  have h_s4_32 : s4 * 32 = 81 * n + 65 := by linarith [hspec4, h_s3_8]
  -- Step 5: s4 ≡ 3 mod 8, v₂ = 1
  have h_s4_mod8 : s4 % 8 = 3 := by omega
  have hv5 : v2_3n1 s4 = 1 := v2_mod8_eq3 _ h_s4_mod8
  have hspec5 := syracuseNext_spec s4
  rw [hv5] at hspec5; simp at hspec5
  set s5 := syracuseNext s4
  have h_s5_64 : s5 * 64 = 243 * n + 227 := by linarith [hspec5, h_s4_32]
  -- Step 6: s5 % 16 = 5, v₂(3s5+1) ≥ 4
  have h_s5_mod16 : s5 % 16 = 5 := by omega
  have hv6 : 4 ≤ v2_3n1 s5 := v2_mod16_eq5_ge4 _ h_s5_mod16
  set s6 := syracuseNext s5
  have h_s6_bound : s6 * 16 ≤ 3 * s5 + 1 := by
    have hspec6 := syracuseNext_spec s5
    have hpow_ge : 16 ≤ 2 ^ (v2_3n1 s5) := by
      calc 16 = 2 ^ 4 := by norm_num
           _ ≤ 2 ^ (v2_3n1 s5) := Nat.pow_le_pow_right (by norm_num) hv6
    calc s6 * 16 ≤ s6 * (2 ^ (v2_3n1 s5)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
         _ = 3 * s5 + 1 := hspec6
  -- Final: s6·1024 ≤ 729n+745 < 1024n for n≥367
  have h_final : s6 * 1024 ≤ 729 * n + 745 := by nlinarith [h_s6_bound, h_s5_64]
  have h_n_ge : n ≥ 367 := by omega
  have hs6_lt : s6 < n := by nlinarith
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  exact ⟨6, hs6_lt, hs6_pos⟩

/-- **Descent for n ≡ 999 mod 1024** in at most 6 steps.
    v₂ pattern: [1,1,2,1,1,≥4]. Final divisor: 1024 = 64·16.
    s5·64 = 243n+251, s6·1024 ≤ 729n+817 < 1024n for n≥999. -/
theorem eventual_descent_mod1024_eq999 (n : ℕ) (hmod : n % 1024 = 999) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 7 mod 8)
  have h8 : n % 8 = 7 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: s1 ≡ 3 mod 8, v₂ = 1
  have h_sn1_mod8 : syracuseNext n % 8 = 3 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn1_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_4 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 1 mod 8, v₂ = 2
  have h_s2_mod8 : s2 % 8 = 1 := by omega
  have hv3 : v2_3n1 s2 = 2 := v2_mod8_eq1 _ h_s2_mod8
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_16 : s3 * 16 = 27 * n + 19 := by linarith [hspec3, h_s2_4]
  -- Step 4: s3 ≡ 7 mod 8, v₂ = 1
  have h_s3_mod8 : s3 % 8 = 7 := by omega
  have hv4 : v2_3n1 s3 = 1 := v2_mod8_eq7 _ h_s3_mod8
  have hspec4 := syracuseNext_spec s3
  rw [hv4] at hspec4; simp at hspec4
  set s4 := syracuseNext s3
  have h_s4_32 : s4 * 32 = 81 * n + 73 := by linarith [hspec4, h_s3_16]
  -- Step 5: s4 ≡ 3 mod 8, v₂ = 1
  have h_s4_mod8 : s4 % 8 = 3 := by omega
  have hv5 : v2_3n1 s4 = 1 := v2_mod8_eq3 _ h_s4_mod8
  have hspec5 := syracuseNext_spec s4
  rw [hv5] at hspec5; simp at hspec5
  set s5 := syracuseNext s4
  have h_s5_64 : s5 * 64 = 243 * n + 251 := by linarith [hspec5, h_s4_32]
  -- Step 6: s5 % 16 = 5, v₂(3s5+1) ≥ 4
  have h_s5_mod16 : s5 % 16 = 5 := by omega
  have hv6 : 4 ≤ v2_3n1 s5 := v2_mod16_eq5_ge4 _ h_s5_mod16
  set s6 := syracuseNext s5
  have h_s6_bound : s6 * 16 ≤ 3 * s5 + 1 := by
    have hspec6 := syracuseNext_spec s5
    have hpow_ge : 16 ≤ 2 ^ (v2_3n1 s5) := by
      calc 16 = 2 ^ 4 := by norm_num
           _ ≤ 2 ^ (v2_3n1 s5) := Nat.pow_le_pow_right (by norm_num) hv6
    calc s6 * 16 ≤ s6 * (2 ^ (v2_3n1 s5)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
         _ = 3 * s5 + 1 := hspec6
  -- Final: s6·1024 ≤ 729n+817 < 1024n for n≥999
  have h_final : s6 * 1024 ≤ 729 * n + 817 := by nlinarith [h_s6_bound, h_s5_64]
  have h_n_ge : n ≥ 999 := by omega
  have hs6_lt : s6 < n := by nlinarith
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  exact ⟨6, hs6_lt, hs6_pos⟩

/-- **Descent for n ≡ 575 mod 1024** in at most 6 steps.
    v₂ pattern: [1,1,1,1,1,≥5]. Final divisor: 1024 = 32·32.
    s5·32 = 243n+211, s6·1024 ≤ 729n+665 < 1024n for n≥575. -/
theorem eventual_descent_mod1024_eq575 (n : ℕ) (hmod : n % 1024 = 575) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: v₂ = 1 (n ≡ 7 mod 8)
  have h8 : n % 8 = 7 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: s1 ≡ 7 mod 8, v₂ = 1
  have h_sn1_mod8 : syracuseNext n % 8 = 7 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq7 _ h_sn1_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  have h_s2_4 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- Step 3: s2 ≡ 7 mod 8, v₂ = 1
  have h_s2_mod8 : s2 % 8 = 7 := by omega
  have hv3 : v2_3n1 s2 = 1 := v2_mod8_eq7 _ h_s2_mod8
  have hspec3 := syracuseNext_spec s2
  rw [hv3] at hspec3; simp at hspec3
  set s3 := syracuseNext s2
  have h_s3_8 : s3 * 8 = 27 * n + 19 := by linarith [hspec3, h_s2_4]
  -- Step 4: s3 ≡ 7 mod 8, v₂ = 1
  have h_s3_mod8 : s3 % 8 = 7 := by omega
  have hv4 : v2_3n1 s3 = 1 := v2_mod8_eq7 _ h_s3_mod8
  have hspec4 := syracuseNext_spec s3
  rw [hv4] at hspec4; simp at hspec4
  set s4 := syracuseNext s3
  have h_s4_16 : s4 * 16 = 81 * n + 65 := by linarith [hspec4, h_s3_8]
  -- Step 5: s4 ≡ 3 mod 8, v₂ = 1
  have h_s4_mod8 : s4 % 8 = 3 := by omega
  have hv5 : v2_3n1 s4 = 1 := v2_mod8_eq3 _ h_s4_mod8
  have hspec5 := syracuseNext_spec s4
  rw [hv5] at hspec5; simp at hspec5
  set s5 := syracuseNext s4
  have h_s5_32 : s5 * 32 = 243 * n + 211 := by linarith [hspec5, h_s4_16]
  -- Step 6: s5 % 32 = 21, v₂(3s5+1) ≥ 5
  have h_s5_mod32 : s5 % 32 = 21 := by omega
  have hv6 : 5 ≤ v2_3n1 s5 := v2_mod32_eq21_ge5 _ h_s5_mod32
  set s6 := syracuseNext s5
  have h_s6_bound : s6 * 32 ≤ 3 * s5 + 1 := by
    have hspec6 := syracuseNext_spec s5
    have hpow_ge : 32 ≤ 2 ^ (v2_3n1 s5) := by
      calc 32 = 2 ^ 5 := by norm_num
           _ ≤ 2 ^ (v2_3n1 s5) := Nat.pow_le_pow_right (by norm_num) hv6
    calc s6 * 32 ≤ s6 * (2 ^ (v2_3n1 s5)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
         _ = 3 * s5 + 1 := hspec6
  -- Final: s6·1024 ≤ 729n+665 < 1024n for n≥575
  have h_final : s6 * 1024 ≤ 729 * n + 665 := by nlinarith [h_s6_bound, h_s5_32]
  have h_n_ge : n ≥ 575 := by omega
  have hs6_lt : s6 < n := by nlinarith
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  exact ⟨6, hs6_lt, hs6_pos⟩

/-!
## 3. The Salmon Conditional Theorem

### The Bit4 Ergodic Hypothesis

The "Salmon Hypothesis" (Eric Merle, Feb 2026) reduces the Collatz conjecture
to a single property: every trajectory eventually visits a number ≡ 3 mod 16.

When this happens, by `salmon_trap_abyss`, the next step lands in class 5 mod 8,
and by `descent_class5`, class 5 numbers always descend strictly.

### Axiom Hierarchy (Sprint P8+, corrected Cycle 63)

We distinguish two versions of the hypothesis:

**SalmonVisitsAbyss** (WEAK, empirically verified up to n=100000):
  ∀ n > 1, ∃ t, nSeq n t % 8 = 5 ∧ nSeq n t > 0
  "Every trajectory visits class 5 at some positive value."
  Implied by Collatz (since the predecessor of 1 in Syracuse
  is always class 5, except 1 itself).
  Defined in EmpiricalAxioms.lean.

**BoundedSalmon** (STRONG, empirically FALSE for some small n):
  ∀ n > 1, ∃ t, nSeq n t % 8 = 5 ∧ 0 < nSeq n t ∧ nSeq n t ≤ n
  "Every trajectory visits class 5 at a value ≤ starting point."
  COUNTEREXAMPLE: n=3, trajectory [3, 5, 1]. Only class-5 visit is 5 > 3.
  Also false for n=2,4,75,151,227,... (26 failures in [2, 100000]).

**Status**: BoundedSalmon → EventualDescent is trivially provable (done below),
but the axiom itself is false. SalmonVisitsAbyss is true but
SalmonVisitsAbyss → EventualDescent is an open problem (class-5 values
along a trajectory are NOT monotonically decreasing).

### Correct reduction chain
  EventualDescent ↔ Collatz conjecture (proved: conditional_convergence)
  Collatz → SalmonVisitsAbyss (true: predecessor of 1 is always class 5)
  SalmonVisitsAbyss → EventualDescent (OPEN — non-trivial)
-/

/-- Lemma: class 5 numbers > 1 descend AND the result is positive -/
theorem class5_descent_with_pos (m : ℕ) (h5 : m % 8 = 5) (hm : m > 1) :
    syracuseNext m < m ∧ syracuseNext m > 0 :=
  ⟨descent_class5 m h5 hm, syracuseNext_pos m⟩

/-- Class 5 values are never 1 (since 1 % 8 = 1 ≠ 5) -/
theorem class5_ne_one (m : ℕ) (h5 : m % 8 = 5) : m ≠ 1 := by omega

/-- CONDITIONAL THEOREM: BoundedSalmon → EventualDescent

    If every trajectory visits class 5 at a value ≤ n (BoundedSalmon),
    then EventualDescent follows trivially.

    NOTE: BoundedSalmon is empirically FALSE for some n (e.g., n=3).
    This theorem is kept for documentation: it shows the proof technique
    works IF the hypothesis holds. The real challenge is proving
    SalmonVisitsAbyss → EventualDescent (open problem).

    Proof: Given n > 1, by hypothesis, ∃ t such that:
    - nSeq n t ≡ 5 mod 8 (class 5)
    - 0 < nSeq n t ≤ n
    Since 5 ≠ 1 mod 8, nSeq n t ≠ 1, so nSeq n t > 1.
    By descent_class5: sN(nSeq n t) < nSeq n t ≤ n.
    By syracuseNext_pos: sN(nSeq n t) > 0.
    So step = t + 1 witnesses EventualDescent. -/
theorem bounded_salmon_implies_descent
    (hS : ∀ n : ℕ, n > 1 →
      ∃ t : ℕ, nSeq n t % 8 = 5 ∧ 0 < nSeq n t ∧ nSeq n t ≤ n) :
    EventualDescent := by
  intro n hn
  obtain ⟨t, h5, hpos, hle⟩ := hS n hn
  have hgt1 : nSeq n t > 1 := by omega
  have hdesc : nSeq n (t + 1) < nSeq n t := by
    show syracuseNext (nSeq n t) < nSeq n t
    exact descent_class5 (nSeq n t) h5 hgt1
  have hpos' : nSeq n (t + 1) > 0 := by
    show syracuseNext (nSeq n t) > 0
    exact syracuseNext_pos (nSeq n t)
  exact ⟨t + 1, by omega, hpos'⟩

/-- CONDITIONAL THEOREM: BoundedSalmon → Collatz conjecture

    The full reduction chain (conditional on BoundedSalmon):
    BoundedSalmon → EventualDescent → ∀ n > 0, ∃ k, nSeq n k = 1

    NOTE: BoundedSalmon is empirically FALSE, so this chain has
    limited mathematical value. See SalmonVisitsAbyss for the
    correct (but harder) formulation. -/
theorem bounded_salmon_implies_collatz :
    (∀ n : ℕ, n > 1 →
      ∃ t : ℕ, nSeq n t % 8 = 5 ∧ 0 < nSeq n t ∧ nSeq n t ≤ n) →
    ∀ n : ℕ, n > 0 → ∃ k : ℕ, nSeq n k = 1 := by
  intro hS n hn
  exact conditional_convergence (bounded_salmon_implies_descent hS) n hn

/-!
## 3b. SalmonVisitsAbyss — The correct (weak) hypothesis

SalmonVisitsAbyss states: every trajectory from n > 1 eventually
visits a number ≡ 5 mod 8 (class 5) with value > 0.

This is empirically verified for all n up to 100,000, and is
implied by the Collatz conjecture (since the predecessor of 1
in the Syracuse function is always class 5, except 1→1).

The OPEN QUESTION is: does SalmonVisitsAbyss imply EventualDescent?
The naive well-founded induction argument FAILS because class-5
values along a trajectory are NOT monotonically decreasing.
Example: n=10, class-5 values: [445, 2429, 3077, 325, 61, 53, 5]
(note 445 → 2429 → 3077 is increasing).
-/

-- SalmonVisitsAbyss is now a field of EmpiricalHypotheses (Phase 54 refactor)

/-- Local descent from SalmonVisitsAbyss: at the class-5 visit,
    the NEXT step descends strictly below that value.

    This is a weaker result than EventualDescent: it shows
    sN(m) < m at the class-5 visit, but m might be > n.

    **Conditional** on `EmpiricalHypotheses`. -/
theorem salmon_local_descent (hyp : EmpiricalHypotheses) (n : ℕ) (hn : n > 1) :
    ∃ t : ℕ, nSeq n (t + 1) < nSeq n t ∧ nSeq n (t + 1) > 0 := by
  obtain ⟨t, h5, hpos⟩ := hyp.salmon_visits_abyss n hn
  have hgt1 : nSeq n t > 1 := by omega
  have hdesc : nSeq n (t + 1) < nSeq n t := by
    show syracuseNext (nSeq n t) < nSeq n t
    exact descent_class5 (nSeq n t) h5 hgt1
  have hpos' : nSeq n (t + 1) > 0 := by
    show syracuseNext (nSeq n t) > 0
    exact syracuseNext_pos (nSeq n t)
  exact ⟨t, hdesc, hpos'⟩

/-!
## 3c. EventualDescent for sub-class n ≡ 23 mod 32

For n ≡ 23 mod 32 (a sub-class of class 7 mod 8), we can prove
EventualDescent in exactly 3 steps, WITHOUT any axiom.

The chain:
  n ≡ 23 mod 32 (class 7)
  → sN(n) = (3n+1)/2 ≡ 35 mod 48 ≡ 3 mod 16 (class 3, ABYSS)
  → sN²(n) = (3·sN(n)+1)/2 ≡ 5 mod 8 (class 5)
  → sN³(n) = (3·sN²(n)+1)/2^v2 ≤ (27n+20)/8 < n

The key bound: sN³(n) ≤ (27n+20)/8 < n for all n ≡ 23 mod 32, n > 1.
-/

/-- Helper: for n ≡ 23 mod 32, syracuseNext n has v2 = 1 and
    value = (3n+1)/2. More precisely: sN(n) * 2 = 3n+1. -/
theorem sN_mod32_eq23_spec (n : ℕ) (hmod : n % 32 = 23) :
    v2_3n1 n = 1 ∧ syracuseNext n * 2 = 3 * n + 1 := by
  have h8 : n % 8 = 7 := by omega
  have hv : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec := syracuseNext_spec n
  rw [hv] at hspec
  simp at hspec
  exact ⟨hv, hspec⟩

/-- Helper: for n ≡ 23 mod 32, sN(n) ≡ 3 mod 16 (triggers abyss). -/
theorem sN_mod32_eq23_class (n : ℕ) (hmod : n % 32 = 23) :
    syracuseNext n % 16 = 3 := by
  obtain ⟨hv, hspec⟩ := sN_mod32_eq23_spec n hmod
  -- sN(n) * 2 = 3n+1, so sN(n) = (3n+1)/2
  -- n = 32k+23, so 3n+1 = 96k+70, sN(n) = 48k+35
  -- 48k+35 mod 16 = 3 (since 48k mod 16 = 0, 35 mod 16 = 3)
  omega

/-- EventualDescent for n ≡ 23 mod 32: descent in 3 steps.

    This is a PURE THEOREM — no axiom needed.
    Proof: sN(n) ∈ class 3 mod 16 (abyss), sN²(n) ∈ class 5,
    sN³(n) ≤ (27n+20)/8 < n. -/
theorem eventual_descent_mod32_eq23 (n : ℕ) (hmod : n % 32 = 23) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Step 1: sN(n) ≡ 3 mod 16, which means sN(n) ≡ 3 mod 8
  have h_sn_mod16 := sN_mod32_eq23_class n hmod
  have h_sn_mod8 : syracuseNext n % 8 = 3 := by omega
  -- Step 2: sN²(n) ∈ class 5 (by salmon_trap_abyss on sN(n))
  have h_sn2_class5 : syracuseNext (syracuseNext n) % 8 = 5 :=
    salmon_trap_abyss (syracuseNext n) h_sn_mod16
  -- sN²(n) > 1 (class 5 means ≠ 1, and sN²(n) > 0)
  have h_sn2_pos : syracuseNext (syracuseNext n) > 0 :=
    syracuseNext_pos (syracuseNext n)
  have h_sn2_gt1 : syracuseNext (syracuseNext n) > 1 := by omega
  -- Step 3: sN³(n) < sN²(n) (descent_class5)
  have h_sn3_lt_sn2 : syracuseNext (syracuseNext (syracuseNext n)) <
      syracuseNext (syracuseNext n) :=
    descent_class5 _ h_sn2_class5 h_sn2_gt1
  -- Now bound sN²(n) ≤ (9n+5)/4 and sN³(n) ≤ (27n+20)/8
  -- Actually we need sN³(n) < n. Use the spec chain:
  -- sN(n) * 2 = 3n+1 (from v2=1)
  obtain ⟨_, hspec1⟩ := sN_mod32_eq23_spec n hmod
  -- sN²(n) * 2 = 3·sN(n)+1 (since sN(n) ≡ 3 mod 8, v2=1)
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2
  simp at hspec2
  -- sN³(n) * 2^v ≤ 3·sN²(n)+1 where v ≥ 3 (class 5)
  have hv3 : 3 ≤ v2_3n1 (syracuseNext (syracuseNext n)) :=
    v2_mod8_eq5_ge3 _ h_sn2_class5
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  -- 2^v ≥ 8
  have hpow_ge : 8 ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext n)) := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext n)) :=
             Nat.pow_le_pow_right (by norm_num) hv3
  -- sN³ * 8 ≤ sN³ * 2^v = 3·sN²+1
  have hle8 : syracuseNext (syracuseNext (syracuseNext n)) * 8 ≤
      3 * syracuseNext (syracuseNext n) + 1 := by
    calc syracuseNext (syracuseNext (syracuseNext n)) * 8
        ≤ syracuseNext (syracuseNext (syracuseNext n)) *
          2 ^ v2_3n1 (syracuseNext (syracuseNext n)) := by
            apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * syracuseNext (syracuseNext n) + 1 := hspec3
  -- From hspec1: sN * 2 = 3n+1, so sN = (3n+1)/2
  -- From hspec2: sN² * 2 = 3·sN+1
  -- Substituting: sN² * 2 = 3·(3n+1)/2 + 1 ... but Nat division is tricky
  -- Instead, work with the product chain:
  -- sN³ * 8 ≤ 3·sN² + 1
  -- sN² * 2 = 3·sN + 1
  -- sN * 2 = 3n + 1
  -- So: sN² = (3·sN+1)/2, and sN = (3n+1)/2
  -- sN³ * 8 ≤ 3·(3·(3n+1)/2+1)/2 + 1
  -- = 3·(9n+3+2)/4 + 1 = 3·(9n+5)/4 + 1 = (27n+15)/4 + 1 = (27n+19)/4
  -- Wait, let's use omega on the multiplied versions:
  -- sN³ * 8 ≤ 3·sN² + 1
  -- sN² * 2 = 3·sN + 1  → 3·sN² = 3·(3·sN+1)/2 ... Nat arithmetic
  -- Better: multiply everything out.
  -- From hspec2: sN² * 2 = 3*sN + 1 → 3*sN² + 1 = 3*(3*sN+1)/2 + 1
  -- Hmm, let's just use omega on all three equations:
  -- sN * 2 = 3n + 1
  -- sN² * 2 = 3*sN + 1
  -- sN³ * 8 ≤ 3*sN² + 1
  -- From first two: sN² * 4 = 2*(3*sN+1) = 6*sN+2 = 3*(3n+1)+2 = 9n+5
  -- Actually sN² * 2 = 3*sN+1 and sN*2 = 3n+1
  -- so sN² * 4 = 2*(3*sN+1) = 6*sN + 2
  -- and 6*sN = 3*(3n+1) = 9n+3
  -- so sN² * 4 = 9n+5
  -- sN³ * 8 ≤ 3*sN² + 1
  -- sN³ * 32 ≤ 4*(3*sN² + 1) = 12*sN² + 4
  -- 12*sN² = 3*(sN²*4) = 3*(9n+5) = 27n+15
  -- sN³ * 32 ≤ 27n+15+4 = 27n+19
  -- Need: sN³ < n, i.e., sN³ * 32 < 32n
  -- 27n+19 < 32n iff 19 < 5n iff n > 3 (true since n ≡ 23 mod 32 → n ≥ 23)
  -- So: sN³ * 32 ≤ 27n+19 < 32n → sN³ < n ✓
  -- Use omega with the three equations
  -- Let's name the variables for omega
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  -- We have: s1 * 2 = 3*n+1, s2 * 2 = 3*s1+1, s3 * 8 ≤ 3*s2+1
  -- Need: s3 < n
  -- Let's derive: s3 * 32 ≤ 4*(3*s2+1) = 12*s2+4
  -- and 4*s2 = 2*(3*s1+1) = 6*s1+2, so 12*s2 = 3*(6*s1+2) = 18*s1+6
  -- wait this is getting complex. Let's try omega directly with all facts.
  -- omega should handle this if we give it the key linear inequalities
  have h_n_ge : n ≥ 23 := by omega
  -- Eliminate intermediate variables to get linear bound on s3 in terms of n
  have h_s2_4 : s2 * 4 = 6 * s1 + 2 := by linarith [hspec2]
  have h_6s1 : 6 * s1 = 9 * n + 3 := by linarith [hspec1]
  have h_s2_bound : s2 * 4 = 9 * n + 5 := by linarith
  have h_s3_32 : s3 * 32 ≤ 12 * s2 + 4 := by linarith [hle8]
  have h_s3_bound : s3 * 32 ≤ 27 * n + 19 := by linarith
  have hs3_pos : s3 > 0 := syracuseNext_pos s2
  have hs3_lt : s3 < n := by omega
  exact ⟨3, hs3_lt, hs3_pos⟩

/-- EventualDescent for n ≡ 7 mod 16, n ≡ 23 mod 32 sub-case.
    This covers half of all class-7 numbers mod 16. -/
theorem eventual_descent_class7_sub23 (n : ℕ) (h7 : n % 8 = 7)
    (h23 : n % 32 = 23) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 :=
  eventual_descent_mod32_eq23 n h23 hn

/-!
## 3e. EventualDescent for n ≡ 7 mod 128 (Sprint P9)

The PASSAGE chain: for n ≡ 7 mod 32 with sN(n) ≡ 11 mod 16,
the trajectory goes through class 3 (passage) → class 1 → class 5 → descent.

We split n ≡ 7 mod 128 into two sub-cases mod 256:
- n ≡ 7 mod 256: exact v2=[1,1,2,3], sN⁴ = (162k+5) < n
- n ≡ 135 mod 256: v2=[1,1,2,≥4], sN⁴ ≤ (81k+43) < n
-/

/-- For n ≡ 7 mod 128, sN(n) ≡ 11 mod 16 (class 3, PASSAGE route). -/
theorem sN_mod128_eq7_class (n : ℕ) (hmod : n % 128 = 7) :
    syracuseNext n % 16 = 11 := by
  have h8 : n % 8 = 7 := by omega
  have hv : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec := syracuseNext_spec n
  rw [hv] at hspec
  simp at hspec
  -- sN(n) * 2 = 3n+1, n = 128k+7, 3n+1 = 384k+22
  -- sN(n) = (384k+22)/2 = 192k+11, mod 16 = 11
  omega

/-- For n ≡ 7 mod 128, sN(n) ≡ 3 mod 8 and sN²(n) ≡ 1 mod 8. -/
theorem sN2_mod128_eq7_class (n : ℕ) (hmod : n % 128 = 7) :
    syracuseNext (syracuseNext n) % 16 = 1 := by
  have h8 : n % 8 = 7 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- sN(n) % 8 = 3, so v2(3·sN+1) = 1
  have h_sn_mod8 : syracuseNext n % 8 = 3 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- sN²(n) * 2 = 3·sN(n)+1, and sN(n)*2 = 3n+1
  -- sN²*4 = 2*(3·sN+1) = 6·sN+2, and sN*2 = 3n+1
  -- sN²*4 = 3*(3n+1)+2 = 9n+5
  -- n = 128k+7, sN²*4 = 1152k+68 → sN² = 288k+17
  -- 288k+17 mod 16 = 1 (since 288 = 18·16)
  omega

/-- For n ≡ 7 mod 256, sN³(n) ≡ 13 mod 16 (class 5, v2=3 exactly). -/
theorem sN3_mod256_eq7_class (n : ℕ) (hmod : n % 256 = 7) :
    syracuseNext (syracuseNext (syracuseNext n)) % 16 = 13 := by
  have h128 : n % 128 = 7 := by omega
  have h8 : n % 8 = 7 := by omega
  -- Step 1: sN(n) * 2 = 3n+1
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: sN(n) % 8 = 3, v2 = 1
  have h_sn_mod8 : syracuseNext n % 8 = 3 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- Step 3: sN²(n) % 16 = 1, v2 = 2
  have h_sn2_mod16 : syracuseNext (syracuseNext n) % 16 = 1 :=
    sN2_mod128_eq7_class n h128
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn2_mod16
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³*4 = 3·sN²+1, sN²*2 = 3·sN+1, sN*2 = 3n+1
  -- n = 256k+7: sN³*4*2*2 = chain → sN³ = 432k+13
  -- 432k+13 mod 16 = 13
  omega

/-- EventualDescent for n ≡ 7 mod 256: descent in 4 steps.
    Chain: class 7 → class 3 (passage) → class 1 (v2=2) → class 5 (v2=3) → descent.
    Exact: sN⁴(n) * 8 = 3·sN³(n)+1, total product gives sN⁴ * 256 = 81n+65.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod256_eq7 (n : ℕ) (hmod : n % 256 = 7) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h128 : n % 128 = 7 := by omega
  have h8 : n % 8 = 7 := by omega
  -- Build the 4-step chain
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  have h_sn_mod8 : syracuseNext n % 8 = 3 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  have h_sn2_mod16 : syracuseNext (syracuseNext n) % 16 = 1 :=
    sN2_mod128_eq7_class n h128
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn2_mod16
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³ ≡ 13 mod 16, so v2 = 3 exactly
  have h_sn3_mod16 := sN3_mod256_eq7_class n hmod
  have hv4 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) = 3 :=
    v2_mod16_eq13_eq3 _ h_sn3_mod16
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  rw [hv4] at hspec4; simp at hspec4
  -- Chain: s1*2 = 3n+1, s2*2 = 3s1+1, s3*4 = 3s2+1, s4*8 = 3s3+1
  -- Combined: s4*8*4*2*2 = 81n+65, i.e., s4*256 = 81n+65
  -- For n ≡ 7 mod 256: 81n+65 = 81·(256k+7)+65 = 20736k+632 = 256·(81k+2) + 56+8 ...
  -- Actually: need s4 < n, and s4 > 0
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  have h_n_ge : n ≥ 7 := by omega
  -- s4 > 0
  have hs4_pos : s4 > 0 := syracuseNext_pos s3
  -- s4 < n: from the chain equations, omega should derive this
  have hs4_lt : s4 < n := by omega
  exact ⟨4, hs4_lt, hs4_pos⟩

/-- For n ≡ 135 mod 256, sN³(n) ≡ 5 mod 16 (class 5, v2 ≥ 4). -/
theorem sN3_mod256_eq135_class (n : ℕ) (hmod : n % 256 = 135) :
    syracuseNext (syracuseNext (syracuseNext n)) % 16 = 5 := by
  have h128 : n % 128 = 7 := by omega
  have h8 : n % 8 = 7 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  have h_sn_mod8 : syracuseNext n % 8 = 3 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  have h_sn2_mod16 : syracuseNext (syracuseNext n) % 16 = 1 :=
    sN2_mod128_eq7_class n h128
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn2_mod16
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- n = 256k+135: sN³ = 432k+229, 229 mod 16 = 5
  omega

/-- EventualDescent for n ≡ 135 mod 256: descent in 4 steps.
    Chain: class 7 → class 3 (passage) → class 1 (v2=2) → class 5 (v2≥4) → descent.
    Bound: sN⁴ * 128 ≤ 81n+65, and 81n+65 < 128n for n ≥ 2.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod256_eq135 (n : ℕ) (hmod : n % 256 = 135) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h128 : n % 128 = 7 := by omega
  have h8 : n % 8 = 7 := by omega
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  have h_sn_mod8 : syracuseNext n % 8 = 3 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  have h_sn2_mod16 : syracuseNext (syracuseNext n) % 16 = 1 :=
    sN2_mod128_eq7_class n h128
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn2_mod16
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³ ≡ 5 mod 16 → v2 ≥ 4
  have h_sn3_mod16 := sN3_mod256_eq135_class n hmod
  have hv4 : 4 ≤ v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) :=
    v2_mod16_eq5_ge4 _ h_sn3_mod16
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  -- 2^v4 ≥ 16
  have hpow_ge : 16 ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) := by
    calc 16 = 2 ^ 4 := by norm_num
         _ ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) :=
             Nat.pow_le_pow_right (by norm_num) hv4
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  have hs4_pos : s4 > 0 := syracuseNext_pos s3
  -- s4 * 16 ≤ s4 * 2^v4 = 3*s3+1
  have hle16 : s4 * 16 ≤ 3 * s3 + 1 := by
    calc s4 * 16
        ≤ s4 * 2 ^ v2_3n1 s3 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s3 + 1 := hspec4
  -- Eliminate intermediate variables to get linear bound in n
  have h_n_ge : n ≥ 135 := by omega
  -- s1*2=3n+1, s2*2=3*s1+1 => s2*4=9n+5
  have h_elim_s1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  -- s3*4=3*s2+1 => s3*16=12*s2+4=27n+19
  have h_elim_s2 : s3 * 16 = 27 * n + 19 := by linarith [hspec3]
  -- s4*16≤3*s3+1 => s4*256≤48*s3+16=81n+73
  have h_elim_s3 : s4 * 256 ≤ 81 * n + 73 := by linarith [hle16]
  -- 81n+73 < 256n when n ≥ 1
  have hs4_lt : s4 < n := by omega
  exact ⟨4, hs4_lt, hs4_pos⟩

/-- EventualDescent for all n ≡ 7 mod 128: descent in 4 steps.
    Combines n ≡ 7 mod 256 and n ≡ 135 mod 256.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod128_eq7 (n : ℕ) (hmod : n % 128 = 7) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  -- Split: n % 256 = 7 or n % 256 = 135
  have h256 : n % 256 = 7 ∨ n % 256 = 135 := by omega
  rcases h256 with h7 | h135
  · exact eventual_descent_mod256_eq7 n h7 hn
  · exact eventual_descent_mod256_eq135 n h135 hn

/-!
## 3f. EventualDescent for n ≡ 15 mod 128 (Sprint P9)

For n ≡ 15 mod 128: sN(n) = (3n+1)/2 ≡ 23 mod 32.
Then the existing mod32_eq23 theorem gives descent in 3 more steps.
Total: 4 steps.

Proof: sN(n) ≡ 23 mod 32, then nSeq n 4 = nSeq (sN(n)) 3 < sN(n) < ... < n?
No! sN(n) > n (it's a class 7 → v2=1 step). But nSeq n 4 < n directly.
We need: sN⁴(n) * 128 ≤ 81n + 65 < 128n for n ≥ 2.
-/

/-- For n ≡ 15 mod 128, sN(n) ≡ 23 mod 32. -/
theorem sN_mod128_eq15_class (n : ℕ) (hmod : n % 128 = 15) :
    syracuseNext n % 32 = 23 := by
  have h8 : n % 8 = 7 := by omega
  have hv : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec := syracuseNext_spec n
  rw [hv] at hspec; simp at hspec
  -- sN * 2 = 3n+1, n = 128k+15, sN = (384k+46)/2 = 192k+23
  -- 192k+23 mod 32 = 23 (since 192 = 6·32)
  omega

/-- EventualDescent for n ≡ 15 mod 128: descent in 4 steps.
    Chain: sN(n) ≡ 23 mod 32 → apply mod32_eq23 chain for 3 more steps.
    Combined bound: sN⁴(n) * 128 ≤ 81n + 65 < 128n for n ≥ 2.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod128_eq15 (n : ℕ) (hmod : n % 128 = 15) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h8 : n % 8 = 7 := by omega
  -- Step 1: sN(n) ≡ 23 mod 32
  have h_sn_mod32 := sN_mod128_eq15_class n hmod
  have h_sn_mod8 : syracuseNext n % 8 = 7 := by omega
  -- sN(n) specs
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- Step 2: sN²(n) ≡ 3 mod 16 (from mod32_eq23 chain on sN(n))
  have h_sn2_mod16 : syracuseNext (syracuseNext n) % 16 = 3 :=
    sN_mod32_eq23_class (syracuseNext n) h_sn_mod32
  have h_sn2_mod8 : syracuseNext (syracuseNext n) % 8 = 3 := by omega
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq7 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- Step 3: sN³(n) ≡ 5 mod 8 (salmon_trap_abyss on sN²(n))
  have h_sn3_class5 : syracuseNext (syracuseNext (syracuseNext n)) % 8 = 5 :=
    salmon_trap_abyss (syracuseNext (syracuseNext n)) h_sn2_mod16
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 1 :=
    v2_mod8_eq3 _ h_sn2_mod8
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- Step 4: sN³ ≡ 5 mod 16 (from chain of equalities), so v2 ≥ 4
  have h_sn3_mod16 : syracuseNext (syracuseNext (syracuseNext n)) % 16 = 5 := by omega
  have hv4 : 4 ≤ v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) :=
    v2_mod16_eq5_ge4 _ h_sn3_mod16
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  have hpow_ge : 16 ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) := by
    calc 16 = 2 ^ 4 := by norm_num
         _ ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) :=
             Nat.pow_le_pow_right (by norm_num) hv4
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  have hs4_pos : s4 > 0 := syracuseNext_pos s3
  have hle16 : s4 * 16 ≤ 3 * s3 + 1 := by
    calc s4 * 16
        ≤ s4 * 2 ^ v2_3n1 s3 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s3 + 1 := hspec4
  have h_n_ge : n ≥ 15 := by omega
  -- Eliminate: s2*4=9n+5, s3*8=27n+19, s4*128≤81n+65
  have h_elim_s1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  have h_elim_s2 : s3 * 8 = 27 * n + 19 := by linarith [hspec3]
  have h_elim_s3 : s4 * 128 ≤ 81 * n + 65 := by linarith [hle16]
  have hs4_lt : s4 < n := by omega
  exact ⟨4, hs4_lt, hs4_pos⟩

/-!
## 3g. Coverage summary (Sprint P9)

For class 7 (n ≡ 7 mod 8), EventualDescent is now proved for:

| Sub-class mod 128 | Steps | Theorem | Ratio bound |
|---|---|---|---|
| n ≡ 23 mod 32 (4 classes) | 3 | eventual_descent_mod32_eq23 | ≤ 27/32 |
| n ≡ 7 mod 128 | 4 | eventual_descent_mod128_eq7 | ≤ 162/256 |
| n ≡ 15 mod 128 | 4 | eventual_descent_mod128_eq15 | ≤ 81/128 |

Coverage: 6/16 residues mod 128 → 37.5% of all class-7 numbers.
(Compared to 25% before Sprint P9.)
-/

/-!
## 3h. EventualDescent for 5-step sub-classes (Sprint P9 continued)

Three more sub-classes of class 7 descend in exactly 5 steps:
- n ≡ 39 mod 256: v2=[1,1,2,1,≥3], ratio ≤ 243/256 ≈ 0.949
- n ≡ 95 mod 256: v2=[1,1,1,1,≥4], ratio ≤ 243/256 ≈ 0.949
- n ≡ 175 mod 256: v2=[1,1,1,2,≥3], ratio ≤ 243/256 ≈ 0.949

Common pattern: s4 ≡ 5 mod 8, so v2 ≥ 3 at step 5.
For n≡95 mod 256: s4 ≡ 5 mod 16, giving the stronger v2 ≥ 4.
-/

/-- For n ≡ 39 mod 256: sN(n) ≡ 11 mod 16 (class 3, passage). -/
theorem sN_mod256_eq39_chain (n : ℕ) (hmod : n % 256 = 39) :
    syracuseNext n % 16 = 11 := by
  have h8 : n % 8 = 7 := by omega
  have hv : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec := syracuseNext_spec n
  rw [hv] at hspec; simp at hspec
  omega

/-- EventualDescent for n ≡ 39 mod 256: descent in 5 steps.
    Chain: class 7 → class 3 (passage) → class 1 → class 3 (abyss) → class 5 → descent.
    v2 = [1, 1, 2, 1, ≥3], combined bound: s5*8 ≤ 3·s4+1, s4*32=81n+73.
    Need: 243k+38 < 256k+39, true for k ≥ 0.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod256_eq39 (n : ℕ) (hmod : n % 256 = 39) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h8 : n % 8 = 7 := by omega
  -- Step 1: v2 = 1 (class 7)
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- sN(n) ≡ 3 mod 8 (11 mod 16, passage)
  have h_sn_mod8 : syracuseNext n % 8 = 3 := by omega
  -- Step 2: v2 = 1 (class 3, mod 16 = 11)
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- sN²(n) ≡ 1 mod 8 (mod 16 = 9)
  have h_sn2_mod16 : syracuseNext (syracuseNext n) % 16 = 9 := by omega
  -- Step 3: v2 = 2 (class 1, mod 16 = 9)
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 2 :=
    v2_mod16_eq9_eq2 _ h_sn2_mod16
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³(n) ≡ 3 mod 8 (mod 16 = 3, ABYSS)
  have h_sn3_mod8 : syracuseNext (syracuseNext (syracuseNext n)) % 8 = 3 := by omega
  -- Step 4: v2 = 1 (class 3)
  have hv4 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) = 1 :=
    v2_mod8_eq3 _ h_sn3_mod8
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  rw [hv4] at hspec4; simp at hspec4
  -- sN⁴(n) ≡ 5 mod 8
  have h_sn4_mod8 : syracuseNext (syracuseNext (syracuseNext (syracuseNext n))) % 8 = 5 := by omega
  -- Step 5: v2 ≥ 3 (class 5)
  have hv5 : 3 ≤ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) :=
    v2_mod8_eq5_ge3 _ h_sn4_mod8
  have hspec5 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext (syracuseNext n))))
  have hpow_ge : 8 ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) :=
             Nat.pow_le_pow_right (by norm_num) hv5
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  set s5 := syracuseNext s4
  have hs5_pos : s5 > 0 := syracuseNext_pos s4
  have hle8 : s5 * 8 ≤ 3 * s4 + 1 := by
    calc s5 * 8
        ≤ s5 * 2 ^ v2_3n1 s4 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s4 + 1 := hspec5
  have h_n_ge : n ≥ 39 := by omega
  -- Eliminate: s1*2=3n+1, s2*2=3*s1+1, s3*4=3*s2+1, s4*2=3*s3+1, s5*8≤3*s4+1
  have h_e1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  have h_e2 : s3 * 16 = 27 * n + 19 := by linarith [hspec3]
  have h_e3 : s4 * 32 = 81 * n + 73 := by linarith [hspec4]
  have h_e4 : s5 * 256 ≤ 243 * n + 251 := by linarith [hle8]
  have hs5_lt : s5 < n := by omega
  exact ⟨5, hs5_lt, hs5_pos⟩

/-- EventualDescent for n ≡ 95 mod 256: descent in 5 steps.
    Chain: class 7 → class 7 (mod32=15) → class 7 (mod32=23) → class 3 (abyss) →
    class 5 (mod16=5, v2≥4) → descent.
    Bound: s5*16 ≤ 3·s4+1, s4*16=81n+65, giving s5 ≤ 243k+91 < 256k+95.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod256_eq95 (n : ℕ) (hmod : n % 256 = 95) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h8 : n % 8 = 7 := by omega
  -- Step 1: v2 = 1 (class 7)
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- sN(n) ≡ 7 mod 8 (still class 7, mod 16 = 15)
  have h_sn_mod8 : syracuseNext n % 8 = 7 := by omega
  -- Step 2: v2 = 1 (class 7, mod 16 = 15)
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq7 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- sN²(n) ≡ 7 mod 8 (class 7, mod 32 = 23!)
  have h_sn2_mod8 : syracuseNext (syracuseNext n) % 8 = 7 := by omega
  have h_sn2_mod32 : syracuseNext (syracuseNext n) % 32 = 23 := by omega
  -- Step 3: v2 = 1 (class 7, mod 32 = 23, this is the ABYSS entry)
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 1 :=
    v2_mod8_eq7 _ h_sn2_mod8
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³(n) ≡ 3 mod 16 (by sN_mod32_eq23_class on sN²)
  have h_sn3_mod16 : syracuseNext (syracuseNext (syracuseNext n)) % 16 = 3 :=
    sN_mod32_eq23_class (syracuseNext (syracuseNext n)) h_sn2_mod32
  have h_sn3_mod8 : syracuseNext (syracuseNext (syracuseNext n)) % 8 = 3 := by omega
  -- Step 4: v2 = 1 (class 3, mod 16 = 3)
  have hv4 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) = 1 :=
    v2_mod8_eq3 _ h_sn3_mod8
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  rw [hv4] at hspec4; simp at hspec4
  -- sN⁴(n) ≡ 5 mod 16 (abyss result)
  have h_sn4_mod16 : syracuseNext (syracuseNext (syracuseNext (syracuseNext n))) % 16 = 5 := by omega
  -- Step 5: v2 ≥ 4 (class 5 mod 16 = 5)
  have hv5 : 4 ≤ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) :=
    v2_mod16_eq5_ge4 _ h_sn4_mod16
  have hspec5 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext (syracuseNext n))))
  have hpow_ge : 16 ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) := by
    calc 16 = 2 ^ 4 := by norm_num
         _ ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) :=
             Nat.pow_le_pow_right (by norm_num) hv5
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  set s5 := syracuseNext s4
  have hs5_pos : s5 > 0 := syracuseNext_pos s4
  have hle16 : s5 * 16 ≤ 3 * s4 + 1 := by
    calc s5 * 16
        ≤ s5 * 2 ^ v2_3n1 s4 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s4 + 1 := hspec5
  have h_n_ge : n ≥ 95 := by omega
  -- Eliminate: s1*2=3n+1, s2*2=3*s1+1, s3*2=3*s2+1, s4*2=3*s3+1, s5*16≤3*s4+1
  have h_e1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  have h_e2 : s3 * 8 = 27 * n + 19 := by linarith [hspec3]
  have h_e3 : s4 * 16 = 81 * n + 65 := by linarith [hspec4]
  have h_e4 : s5 * 256 ≤ 243 * n + 211 := by linarith [hle16]
  have hs5_lt : s5 < n := by omega
  exact ⟨5, hs5_lt, hs5_pos⟩

/-- EventualDescent for n ≡ 175 mod 256: descent in 5 steps.
    Chain: class 7 (mod128=7) → class 3 (passage) → class 1 → class 5 → descent.
    But v2 at step 4 is only 2, not ≥3, so descent below sN needs one more step.
    v2 = [1, 1, 1, 2, ≥3], bound: s5 ≤ 243k+167 < 256k+175.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod256_eq175 (n : ℕ) (hmod : n % 256 = 175) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h8 : n % 8 = 7 := by omega
  -- Step 1: v2 = 1 (class 7)
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- sN(n) ≡ 7 mod 8
  have h_sn_mod8 : syracuseNext n % 8 = 7 := by omega
  -- Step 2: v2 = 1 (class 7)
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq7 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- sN²(n) ≡ 3 mod 8 (mod 16 = 11, passage)
  have h_sn2_mod8 : syracuseNext (syracuseNext n) % 8 = 3 := by omega
  -- Step 3: v2 = 1 (class 3, passage)
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 1 :=
    v2_mod8_eq3 _ h_sn2_mod8
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³(n) ≡ 1 mod 8 (mod 16 = 1)
  have h_sn3_mod16 : syracuseNext (syracuseNext (syracuseNext n)) % 16 = 1 := by omega
  -- Step 4: v2 = 2 (class 1, mod 16 = 1)
  have hv4 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn3_mod16
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  rw [hv4] at hspec4; simp at hspec4
  -- sN⁴(n) ≡ 5 mod 8
  have h_sn4_mod8 : syracuseNext (syracuseNext (syracuseNext (syracuseNext n))) % 8 = 5 := by omega
  -- Step 5: v2 ≥ 3 (class 5)
  have hv5 : 3 ≤ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) :=
    v2_mod8_eq5_ge3 _ h_sn4_mod8
  have hspec5 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext (syracuseNext n))))
  have hpow_ge : 8 ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) :=
             Nat.pow_le_pow_right (by norm_num) hv5
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  set s5 := syracuseNext s4
  have hs5_pos : s5 > 0 := syracuseNext_pos s4
  have hle8 : s5 * 8 ≤ 3 * s4 + 1 := by
    calc s5 * 8
        ≤ s5 * 2 ^ v2_3n1 s4 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s4 + 1 := hspec5
  have h_n_ge : n ≥ 175 := by omega
  -- Eliminate: s1*2=3n+1, s2*2=3*s1+1, s3*2=3*s2+1, s4*4=3*s3+1, s5*8≤3*s4+1
  have h_e1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  have h_e2 : s3 * 8 = 27 * n + 19 := by linarith [hspec3]
  have h_e3 : s4 * 32 = 81 * n + 65 := by linarith [hspec4]
  have h_e4 : s5 * 256 ≤ 243 * n + 227 := by linarith [hle8]
  have hs5_lt : s5 < n := by omega
  exact ⟨5, hs5_lt, hs5_pos⟩

/-!
## 3j. EventualDescent for mod 512 sub-classes (Sprint P9 continued)

The sub-classes n ≡ 79 mod 256 and n ≡ 199 mod 256 have s4 that alternates
between class 5 and class 1 depending on n mod 512. We split each:

- n ≡ 79 mod 512: v2=[1,1,1,3,≥3], s4 ≡ 5 mod 8 → v2≥3
- n ≡ 335 mod 512: v2=[1,1,1,3,2], s4 ≡ 1 mod 8 → v2=2 (exact)
- n ≡ 199 mod 512: v2=[1,1,2,2,≥3], s4 ≡ 5 mod 8 → v2≥3
- n ≡ 455 mod 512: v2=[1,1,2,2,2], s4 ≡ 1 mod 8 → v2=2 (exact)

All give descent in 5 steps.
-/

/-- EventualDescent for n ≡ 79 mod 512: descent in 5 steps.
    Chain: class 7 → class 7 → class 3 (abyss, mod16=3) → class 5 (mod16=13, v2=3)
    → class 5 (mod8=5, v2≥3) → descent.
    v2 = [1, 1, 1, 3, ≥3].
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod512_eq79 (n : ℕ) (hmod : n % 512 = 79) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h8 : n % 8 = 7 := by omega
  -- Step 1: v2 = 1 (class 7)
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- sN(n) = 768k+119, mod 8 = 7 (still class 7)
  have h_sn_mod8 : syracuseNext n % 8 = 7 := by omega
  -- Step 2: v2 = 1 (class 7)
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq7 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- sN²(n) = 1152k+179, mod 8 = 3 (class 3, abyss: mod 16 = 3)
  have h_sn2_mod8 : syracuseNext (syracuseNext n) % 8 = 3 := by omega
  -- Step 3: v2 = 1 (class 3)
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 1 :=
    v2_mod8_eq3 _ h_sn2_mod8
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³(n) = 1728k+269, mod 16 = 13 (class 5, v2=3 exactly)
  have h_sn3_mod16 : syracuseNext (syracuseNext (syracuseNext n)) % 16 = 13 := by omega
  -- Step 4: v2 = 3 (mod16=13 → v2=3)
  have hv4 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) = 3 :=
    v2_mod16_eq13_eq3 _ h_sn3_mod16
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  rw [hv4] at hspec4; simp at hspec4
  -- sN⁴(n) = 648k+101, mod 8 = 5 (class 5)
  have h_sn4_mod8 : syracuseNext (syracuseNext (syracuseNext (syracuseNext n))) % 8 = 5 := by omega
  -- Step 5: v2 ≥ 3 (class 5)
  have hv5 : 3 ≤ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) :=
    v2_mod8_eq5_ge3 _ h_sn4_mod8
  have hspec5 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext (syracuseNext n))))
  have hpow_ge : 8 ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) :=
             Nat.pow_le_pow_right (by norm_num) hv5
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  set s5 := syracuseNext s4
  have hs5_pos : s5 > 0 := syracuseNext_pos s4
  have hle8 : s5 * 8 ≤ 3 * s4 + 1 := by
    calc s5 * 8
        ≤ s5 * 2 ^ v2_3n1 s4 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s4 + 1 := hspec5
  have h_n_ge : n ≥ 79 := by omega
  -- Eliminate: s1*2=3n+1, s2*2=3*s1+1, s3*2=3*s2+1, s4*8=3*s3+1, s5*8≤3*s4+1
  have h_e1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  have h_e2 : s3 * 8 = 27 * n + 19 := by linarith [hspec3]
  have h_e3 : s4 * 64 = 81 * n + 65 := by linarith [hspec4]
  have h_e4 : s5 * 512 ≤ 243 * n + 259 := by linarith [hle8]
  have hs5_lt : s5 < n := by omega
  exact ⟨5, hs5_lt, hs5_pos⟩

/-- EventualDescent for n ≡ 335 mod 512: descent in 5 steps.
    Chain: class 7 → class 7 → class 3 (abyss, mod16=3) → class 5 (mod16=13, v2=3)
    → class 1 (mod8=1, v2=2) → descent.
    v2 = [1, 1, 1, 3, 2]. Exact: s5 = 486k+319 < 512k+335.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod512_eq335 (n : ℕ) (hmod : n % 512 = 335) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h8 : n % 8 = 7 := by omega
  -- Step 1: v2 = 1 (class 7)
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- sN(n) = 768k+503, mod 8 = 7
  have h_sn_mod8 : syracuseNext n % 8 = 7 := by omega
  -- Step 2: v2 = 1 (class 7)
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq7 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- sN²(n) = 1152k+755, mod 8 = 3 (class 3, abyss: mod 16 = 3)
  have h_sn2_mod8 : syracuseNext (syracuseNext n) % 8 = 3 := by omega
  -- Step 3: v2 = 1 (class 3)
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 1 :=
    v2_mod8_eq3 _ h_sn2_mod8
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³(n) = 1728k+1133, mod 16 = 13 (class 5, v2=3)
  have h_sn3_mod16 : syracuseNext (syracuseNext (syracuseNext n)) % 16 = 13 := by omega
  -- Step 4: v2 = 3 (mod16=13 → v2=3)
  have hv4 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) = 3 :=
    v2_mod16_eq13_eq3 _ h_sn3_mod16
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  rw [hv4] at hspec4; simp at hspec4
  -- sN⁴(n) = 648k+425, mod 8 = 1 (class 1), mod 16 alternates 9/1
  -- Both mod16=1 and mod16=9 give v2=2
  -- Split on s4 % 16
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  have h_s4_mod8 : s4 % 8 = 1 := by omega
  have h_s4_mod16 : s4 % 16 = 1 ∨ s4 % 16 = 9 := by omega
  -- In both cases, v2 = 2
  have hv5 : v2_3n1 s4 = 2 := by
    rcases h_s4_mod16 with h1 | h9
    · exact v2_mod16_eq1_eq2 s4 h1
    · exact v2_mod16_eq9_eq2 s4 h9
  have hspec5 := syracuseNext_spec s4
  rw [hv5] at hspec5; simp at hspec5
  set s5 := syracuseNext s4
  have hs5_pos : s5 > 0 := syracuseNext_pos s4
  -- s5*4 = 3*s4+1, combined with chain: s5 = 486k+319 < 512k+335 = n
  have h_n_ge : n ≥ 335 := by omega
  -- Eliminate: s1*2=3n+1, s2*2=3*s1+1, s3*2=3*s2+1, s4*8=3*s3+1, s5*4=3*s4+1
  have h_e1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  have h_e2 : s3 * 8 = 27 * n + 19 := by linarith [hspec3]
  have h_e3 : s4 * 64 = 81 * n + 65 := by linarith [hspec4]
  have h_e4 : s5 * 256 = 243 * n + 259 := by linarith [hspec5]
  have hs5_lt : s5 < n := by omega
  exact ⟨5, hs5_lt, hs5_pos⟩

/-- EventualDescent for n ≡ 79 mod 256: combines mod512 eq79 and eq335.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod256_eq79 (n : ℕ) (hmod : n % 256 = 79) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h512 : n % 512 = 79 ∨ n % 512 = 335 := by omega
  rcases h512 with h79 | h335
  · exact eventual_descent_mod512_eq79 n h79 hn
  · exact eventual_descent_mod512_eq335 n h335 hn

/-- EventualDescent for n ≡ 199 mod 512: descent in 5 steps.
    Chain: class 7 → class 3 (passage, mod16=11) → class 1 (mod16=1, v2=2)
    → class 1 (mod16=1, v2=2) → class 5 (mod8=5, v2≥3) → descent.
    v2 = [1, 1, 2, 2, ≥3].
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod512_eq199 (n : ℕ) (hmod : n % 512 = 199) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h8 : n % 8 = 7 := by omega
  -- Step 1: v2 = 1 (class 7)
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- sN(n) = 768k+299, mod 8 = 3, mod 16 = 11 (passage)
  have h_sn_mod8 : syracuseNext n % 8 = 3 := by omega
  -- Step 2: v2 = 1 (class 3, passage)
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- sN²(n) = 1152k+449, mod 16 = 1 (class 1)
  have h_sn2_mod16 : syracuseNext (syracuseNext n) % 16 = 1 := by omega
  -- Step 3: v2 = 2 (mod16=1 → v2=2)
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn2_mod16
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³(n) = 864k+337, mod 16 = 1 (class 1)
  have h_sn3_mod16 : syracuseNext (syracuseNext (syracuseNext n)) % 16 = 1 := by omega
  -- Step 4: v2 = 2 (mod16=1 → v2=2)
  have hv4 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn3_mod16
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  rw [hv4] at hspec4; simp at hspec4
  -- sN⁴(n) = 648k+253, mod 8 = 5 (class 5)
  have h_sn4_mod8 : syracuseNext (syracuseNext (syracuseNext (syracuseNext n))) % 8 = 5 := by omega
  -- Step 5: v2 ≥ 3 (class 5)
  have hv5 : 3 ≤ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) :=
    v2_mod8_eq5_ge3 _ h_sn4_mod8
  have hspec5 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext (syracuseNext n))))
  have hpow_ge : 8 ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) :=
             Nat.pow_le_pow_right (by norm_num) hv5
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  set s5 := syracuseNext s4
  have hs5_pos : s5 > 0 := syracuseNext_pos s4
  have hle8 : s5 * 8 ≤ 3 * s4 + 1 := by
    calc s5 * 8
        ≤ s5 * 2 ^ v2_3n1 s4 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s4 + 1 := hspec5
  have h_n_ge : n ≥ 199 := by omega
  -- Eliminate: s1*2=3n+1, s2*2=3*s1+1, s3*4=3*s2+1, s4*4=3*s3+1, s5*8≤3*s4+1
  have h_e1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  have h_e2 : s3 * 16 = 27 * n + 19 := by linarith [hspec3]
  have h_e3 : s4 * 64 = 81 * n + 73 := by linarith [hspec4]
  have h_e4 : s5 * 512 ≤ 243 * n + 283 := by linarith [hle8]
  have hs5_lt : s5 < n := by omega
  exact ⟨5, hs5_lt, hs5_pos⟩

/-- EventualDescent for n ≡ 455 mod 512: descent in 5 steps.
    Chain: class 7 → class 3 (passage, mod16=11) → class 1 (mod16=1, v2=2)
    → class 1 (mod16=1, v2=2) → class 1 (mod8=1, v2=2) → descent.
    v2 = [1, 1, 2, 2, 2]. Exact: s5 = 486k+433 < 512k+455.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod512_eq455 (n : ℕ) (hmod : n % 512 = 455) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h8 : n % 8 = 7 := by omega
  -- Step 1: v2 = 1 (class 7)
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- sN(n) = 768k+683, mod 8 = 3, mod 16 = 11 (passage)
  have h_sn_mod8 : syracuseNext n % 8 = 3 := by omega
  -- Step 2: v2 = 1 (class 3, passage)
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq3 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- sN²(n) = 1152k+1025, mod 16 = 1 (class 1)
  have h_sn2_mod16 : syracuseNext (syracuseNext n) % 16 = 1 := by omega
  -- Step 3: v2 = 2 (mod16=1 → v2=2)
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn2_mod16
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³(n) = 864k+769, mod 16 = 1 (class 1)
  have h_sn3_mod16 : syracuseNext (syracuseNext (syracuseNext n)) % 16 = 1 := by omega
  -- Step 4: v2 = 2 (mod16=1 → v2=2)
  have hv4 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn3_mod16
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  rw [hv4] at hspec4; simp at hspec4
  -- sN⁴(n) = 648k+577, mod 8 = 1, mod 16 alternates 1/9
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  have h_s4_mod8 : s4 % 8 = 1 := by omega
  have h_s4_mod16 : s4 % 16 = 1 ∨ s4 % 16 = 9 := by omega
  -- In both cases, v2 = 2
  have hv5 : v2_3n1 s4 = 2 := by
    rcases h_s4_mod16 with h1 | h9
    · exact v2_mod16_eq1_eq2 s4 h1
    · exact v2_mod16_eq9_eq2 s4 h9
  have hspec5 := syracuseNext_spec s4
  rw [hv5] at hspec5; simp at hspec5
  set s5 := syracuseNext s4
  have hs5_pos : s5 > 0 := syracuseNext_pos s4
  -- s5*4 = 3*s4+1, combined: s5 = 486k+433 < 512k+455 = n
  have h_n_ge : n ≥ 455 := by omega
  -- Eliminate: s1*2=3n+1, s2*2=3*s1+1, s3*4=3*s2+1, s4*4=3*s3+1, s5*4=3*s4+1
  have h_e1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  have h_e2 : s3 * 16 = 27 * n + 19 := by linarith [hspec3]
  have h_e3 : s4 * 64 = 81 * n + 73 := by linarith [hspec4]
  have h_e4 : s5 * 256 = 243 * n + 283 := by linarith [hspec5]
  have hs5_lt : s5 < n := by omega
  exact ⟨5, hs5_lt, hs5_pos⟩

/-- EventualDescent for n ≡ 199 mod 256: combines mod512 eq199 and eq455.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod256_eq199 (n : ℕ) (hmod : n % 256 = 199) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h512 : n % 512 = 199 ∨ n % 512 = 455 := by omega
  rcases h512 with h199 | h455
  · exact eventual_descent_mod512_eq199 n h199 hn
  · exact eventual_descent_mod512_eq455 n h455 hn

/-!
## 3l. Sprint P10 — mod 1024 proofs (6-step descent)

At mod 1024, three sub-classes admit 6-step descent proofs:
- n ≡ 287 mod 1024: v2=[1,1,1,1,2,≥4], chain 7→7→7→3→1→5→5
- n ≡ 815 mod 1024: v2=[1,1,1,2,2,3], chain 7→7→3→1→1→5→5
- n ≡ 975 mod 1024: v2=[1,1,1,3,1,3], chain 7→7→3→5→3→5→7

Each covers 1/128 of class 7. Combined with Sprint P9:
17/32 + 3/128 = 71/128 ≈ 55.47% of class 7.
-/

/-- EventualDescent for n ≡ 287 mod 1024: descent in 6 steps.
    Chain: class 7 → class 7 (mod16=15) → class 7 (mod16=7) → class 3 (mod16=11)
    → class 1 (mod16=1, v2=2) → class 5 (mod16=5, v2≥4) → descent.
    v2 = [1, 1, 1, 1, 2, ≥4]. Cumulative 3^6/2^(1+1+1+1+2+4) = 729/1024 < 1.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod1024_eq287 (n : ℕ) (hmod : n % 1024 = 287) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h8 : n % 8 = 7 := by omega
  -- Step 1: v2 = 1 (class 7, mod16=15)
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- sN(n) = 1536k+431, mod 8 = 7, mod 16 = 15
  have h_sn_mod8 : syracuseNext n % 8 = 7 := by omega
  -- Step 2: v2 = 1 (class 7, mod16=15)
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq7 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- sN²(n) = 2304k+647, mod 8 = 7, mod 16 = 7
  have h_sn2_mod8 : syracuseNext (syracuseNext n) % 8 = 7 := by omega
  -- Step 3: v2 = 1 (class 7, mod16=7)
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 1 :=
    v2_mod8_eq7 _ h_sn2_mod8
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³(n) = 3456k+971, mod 8 = 3, mod 16 = 11
  have h_sn3_mod8 : syracuseNext (syracuseNext (syracuseNext n)) % 8 = 3 := by omega
  -- Step 4: v2 = 1 (class 3, mod16=11)
  have hv4 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) = 1 :=
    v2_mod8_eq3 _ h_sn3_mod8
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  rw [hv4] at hspec4; simp at hspec4
  -- sN⁴(n) = 5184k+1457, mod 8 = 1, mod 16 = 1
  have h_sn4_mod16 : syracuseNext (syracuseNext (syracuseNext (syracuseNext n))) % 16 = 1 := by omega
  -- Step 5: v2 = 2 (mod16=1 → v2=2)
  have hv5 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn4_mod16
  have hspec5 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext (syracuseNext n))))
  rw [hv5] at hspec5; simp at hspec5
  -- sN⁵(n) = 3888k+1093, mod 8 = 5, mod 16 = 5
  have h_sn5_mod16 : syracuseNext (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) % 16 = 5 := by omega
  -- Step 6: v2 ≥ 4 (mod16=5 → v2≥4)
  have hv6 : 4 ≤ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext (syracuseNext n))))) :=
    v2_mod16_eq5_ge4 _ h_sn5_mod16
  have hspec6 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))))
  have hpow_ge : 16 ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext (syracuseNext n))))) := by
    calc 16 = 2 ^ 4 := by norm_num
         _ ≤ 2 ^ v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext (syracuseNext n))))) :=
             Nat.pow_le_pow_right (by norm_num) hv6
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  set s5 := syracuseNext s4
  set s6 := syracuseNext s5
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  have hle16 : s6 * 16 ≤ 3 * s5 + 1 := by
    calc s6 * 16
        ≤ s6 * 2 ^ v2_3n1 s5 := by apply Nat.mul_le_mul_left; exact hpow_ge
      _ = 3 * s5 + 1 := hspec6
  -- Eliminate: s1*2=3n+1, s2*2=3*s1+1, s3*2=3*s2+1, s4*2=3*s3+1, s5*4=3*s4+1, s6*16≤3*s5+1
  have h_n_ge : n ≥ 287 := by omega
  have h_e1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  have h_e2 : s3 * 8 = 27 * n + 19 := by linarith [hspec3]
  have h_e3 : s4 * 16 = 81 * n + 65 := by linarith [hspec4]
  have h_e4 : s5 * 64 = 243 * n + 211 := by linarith [hspec5]
  have h_e5 : s6 * 1024 ≤ 729 * n + 697 := by linarith [hle16]
  have hs6_lt : s6 < n := by omega
  exact ⟨6, hs6_lt, hs6_pos⟩

/-- EventualDescent for n ≡ 815 mod 1024: descent in 6 steps.
    Chain: class 7 (mod16=15) → class 7 (mod16=7) → class 3 (mod16=11)
    → class 1 (mod16=1, v2=2) → class 1 (mod16=1, v2=2) → class 5 (mod16=13, v2=3)
    → descent.
    v2 = [1, 1, 1, 2, 2, 3]. Cumulative 3^6/2^(1+1+1+2+2+3) = 729/1024 < 1.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod1024_eq815 (n : ℕ) (hmod : n % 1024 = 815) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h8 : n % 8 = 7 := by omega
  -- Step 1: v2 = 1 (class 7, mod16=15)
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- sN(n) = 1536k+1223, mod 8 = 7
  have h_sn_mod8 : syracuseNext n % 8 = 7 := by omega
  -- Step 2: v2 = 1 (class 7, mod16=7)
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq7 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- sN²(n) = 2304k+1835, mod 8 = 3
  have h_sn2_mod8 : syracuseNext (syracuseNext n) % 8 = 3 := by omega
  -- Step 3: v2 = 1 (class 3, mod16=11)
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 1 :=
    v2_mod8_eq3 _ h_sn2_mod8
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³(n) = 3456k+2753, mod 16 = 1
  have h_sn3_mod16 : syracuseNext (syracuseNext (syracuseNext n)) % 16 = 1 := by omega
  -- Step 4: v2 = 2 (mod16=1 → v2=2)
  have hv4 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn3_mod16
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  rw [hv4] at hspec4; simp at hspec4
  -- sN⁴(n) = 2592k+2065, mod 16 = 1
  have h_sn4_mod16 : syracuseNext (syracuseNext (syracuseNext (syracuseNext n))) % 16 = 1 := by omega
  -- Step 5: v2 = 2 (mod16=1 → v2=2)
  have hv5 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) = 2 :=
    v2_mod16_eq1_eq2 _ h_sn4_mod16
  have hspec5 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext (syracuseNext n))))
  rw [hv5] at hspec5; simp at hspec5
  -- Introduce set names early to help with mod computation
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  set s5 := syracuseNext s4
  -- Derive s5 in terms of n via elimination chain
  have h_e1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  have h_e2 : s3 * 8 = 27 * n + 19 := by linarith [hspec3]
  have h_e3 : s4 * 32 = 81 * n + 65 := by linarith [hspec4]
  have h_e4 : s5 * 128 = 243 * n + 227 := by linarith [hspec5]
  -- sN⁵(n) % 16 is either 13 or 5 (depends on n mod 2048)
  have h_sn5_mod : s5 % 16 = 13 ∨ s5 % 16 = 5 := by
    obtain ⟨k, hk⟩ : ∃ k, n = 1024 * k + 815 := ⟨n / 1024, by omega⟩
    have hs5 : s5 = 1944 * k + 1549 := by omega
    omega
  have h_sn5_mod8 : s5 % 8 = 5 := by omega
  have h_n_ge : n ≥ 815 := by omega
  -- Step 6: v2 ≥ 3 (class 5, mod8=5). Both mod16 cases give descent.
  have hv6 : 3 ≤ v2_3n1 s5 := v2_mod8_eq5_ge3 _ h_sn5_mod8
  have hspec6 := syracuseNext_spec s5
  have hpow_ge6 : 8 ≤ 2 ^ v2_3n1 s5 := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ v2_3n1 s5 := Nat.pow_le_pow_right (by norm_num) hv6
  set s6 := syracuseNext s5
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  have hle8_6 : s6 * 8 ≤ 3 * s5 + 1 := by
    calc s6 * 8
        ≤ s6 * 2 ^ v2_3n1 s5 := by apply Nat.mul_le_mul_left; exact hpow_ge6
      _ = 3 * s5 + 1 := hspec6
  -- s6*1024 ≤ 729n+809
  have h_e5 : s6 * 1024 ≤ 729 * n + 809 := by linarith [hle8_6]
  have hs6_lt : s6 < n := by omega
  exact ⟨6, hs6_lt, hs6_pos⟩

/-- EventualDescent for n ≡ 975 mod 1024: descent in 6 steps.
    Chain: class 7 (mod16=15) → class 7 (mod16=7) → class 3 (mod16=3)
    → class 5 (mod16=13, v2=3) → class 3 (mod16=3, v2=1)
    → class 5 (mod16=13, v2=3) → descent.
    v2 = [1, 1, 1, 3, 1, 3]. Cumulative 3^6/2^(1+1+1+3+1+3) = 729/1024 < 1.
    PURE THEOREM — no axiom needed. -/
theorem eventual_descent_mod1024_eq975 (n : ℕ) (hmod : n % 1024 = 975) (hn : n > 1) :
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  have h8 : n % 8 = 7 := by omega
  -- Step 1: v2 = 1 (class 7, mod16=15)
  have hv1 : v2_3n1 n = 1 := v2_mod8_eq7 n h8
  have hspec1 := syracuseNext_spec n
  rw [hv1] at hspec1; simp at hspec1
  -- sN(n) = 1536k+1463, mod 8 = 7
  have h_sn_mod8 : syracuseNext n % 8 = 7 := by omega
  -- Step 2: v2 = 1 (class 7, mod16=7)
  have hv2 : v2_3n1 (syracuseNext n) = 1 := v2_mod8_eq7 _ h_sn_mod8
  have hspec2 := syracuseNext_spec (syracuseNext n)
  rw [hv2] at hspec2; simp at hspec2
  -- sN²(n) = 2304k+2195, mod 8 = 3
  have h_sn2_mod8 : syracuseNext (syracuseNext n) % 8 = 3 := by omega
  -- Step 3: v2 = 1 (class 3, mod16=3)
  have hv3 : v2_3n1 (syracuseNext (syracuseNext n)) = 1 :=
    v2_mod8_eq3 _ h_sn2_mod8
  have hspec3 := syracuseNext_spec (syracuseNext (syracuseNext n))
  rw [hv3] at hspec3; simp at hspec3
  -- sN³(n) = 3456k+3293, mod 16 = 13
  have h_sn3_mod16 : syracuseNext (syracuseNext (syracuseNext n)) % 16 = 13 := by omega
  -- Step 4: v2 = 3 (mod16=13 → v2=3)
  have hv4 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext n))) = 3 :=
    v2_mod16_eq13_eq3 _ h_sn3_mod16
  have hspec4 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext n)))
  rw [hv4] at hspec4; simp at hspec4
  -- sN⁴(n) = 1296k+1235, mod 8 = 3
  have h_sn4_mod8 : syracuseNext (syracuseNext (syracuseNext (syracuseNext n))) % 8 = 3 := by omega
  -- Step 5: v2 = 1 (class 3, mod16=3)
  have hv5 : v2_3n1 (syracuseNext (syracuseNext (syracuseNext (syracuseNext n)))) = 1 :=
    v2_mod8_eq3 _ h_sn4_mod8
  have hspec5 := syracuseNext_spec (syracuseNext (syracuseNext (syracuseNext (syracuseNext n))))
  rw [hv5] at hspec5; simp at hspec5
  -- Introduce set names early to help with mod computation
  set s1 := syracuseNext n
  set s2 := syracuseNext s1
  set s3 := syracuseNext s2
  set s4 := syracuseNext s3
  set s5 := syracuseNext s4
  -- Derive s5 in terms of n via elimination chain
  have h_e1 : s2 * 4 = 9 * n + 5 := by linarith [hspec1, hspec2]
  have h_e2 : s3 * 8 = 27 * n + 19 := by linarith [hspec3]
  have h_e3 : s4 * 64 = 81 * n + 65 := by linarith [hspec4]
  have h_e4 : s5 * 128 = 243 * n + 259 := by linarith [hspec5]
  -- sN⁵(n) % 16 is either 13 or 5 (depends on n mod 2048)
  have h_sn5_mod : s5 % 16 = 13 ∨ s5 % 16 = 5 := by
    obtain ⟨k, hk⟩ : ∃ k, n = 1024 * k + 975 := ⟨n / 1024, by omega⟩
    have hs5 : s5 = 1944 * k + 1853 := by omega
    omega
  have h_sn5_mod8 : s5 % 8 = 5 := by omega
  have h_n_ge : n ≥ 975 := by omega
  -- Step 6: v2 ≥ 3 (class 5, mod8=5). Both mod16 cases give descent.
  have hv6 : 3 ≤ v2_3n1 s5 := v2_mod8_eq5_ge3 _ h_sn5_mod8
  have hspec6 := syracuseNext_spec s5
  have hpow_ge6 : 8 ≤ 2 ^ v2_3n1 s5 := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ v2_3n1 s5 := Nat.pow_le_pow_right (by norm_num) hv6
  set s6 := syracuseNext s5
  have hs6_pos : s6 > 0 := syracuseNext_pos s5
  have hle8_6 : s6 * 8 ≤ 3 * s5 + 1 := by
    calc s6 * 8
        ≤ s6 * 2 ^ v2_3n1 s5 := by apply Nat.mul_le_mul_left; exact hpow_ge6
      _ = 3 * s5 + 1 := hspec6
  -- s6*1024 ≤ 729n+905
  have h_e5 : s6 * 1024 ≤ 729 * n + 905 := by linarith [hle8_6]
  have hs6_lt : s6 < n := by omega
  exact ⟨6, hs6_lt, hs6_pos⟩

/-!
## 3m. Updated coverage (Sprint P10)

| Sub-class | Steps | Theorem | Density |
|---|---|---|---|
| n ≡ 23 mod 32 (8/32) | 3 | eventual_descent_mod32_eq23 | 25.0% |
| n ≡ 7 mod 128 (2/32) | 4 | eventual_descent_mod128_eq7 | 6.25% |
| n ≡ 15 mod 128 (2/32) | 4 | eventual_descent_mod128_eq15 | 6.25% |
| n ≡ 39 mod 256 (1/32) | 5 | eventual_descent_mod256_eq39 | 3.125% |
| n ≡ 95 mod 256 (1/32) | 5 | eventual_descent_mod256_eq95 | 3.125% |
| n ≡ 175 mod 256 (1/32) | 5 | eventual_descent_mod256_eq175 | 3.125% |
| n ≡ 79 mod 256 (2/64) | 5 | eventual_descent_mod256_eq79 | 3.125% |
| n ≡ 199 mod 256 (2/64) | 5 | eventual_descent_mod256_eq199 | 3.125% |
| n ≡ 287 mod 1024 (1/128) | 6 | eventual_descent_mod1024_eq287 | 0.781% |
| n ≡ 815 mod 1024 (1/128) | 6 | eventual_descent_mod1024_eq815 | 0.781% |
| n ≡ 975 mod 1024 (1/128) | 6 | eventual_descent_mod1024_eq975 | 0.781% |
| **TOTAL PROVED** | | | **55.47%** |
| OPEN | | | 44.53% |

Coverage: 17/32 + 3/128 = 71/128 of class-7 residues → 55.47%.
Sprint P10: first mod-1024 proofs with 6-step chains!
-/

/-!
## 3d. Ergodic axioms (legacy)

We axiomatize the key empirical observations as Lean axioms.
These are EMPIRICAL HYPOTHESES, clearly marked as such.
-/

-- barina_verified (2^71), evt_bounded_tail, geometric_k_distribution
-- are all defined in Phase54EmpiricalHypotheses.lean (upgraded Phase 57)

/-!
## 4. Combining empirical axioms with formal results

Using barina_verified, we get EventualDescent for n < 2^71.
Combined with conditional_convergence, this gives convergence for n < 2^71.
-/

/-- EventualDescent holds for all n < 2^71 (from Barina verification).
    **Conditional** on `EmpiricalHypotheses`.
    Updated Phase 57: Barina 2025 (J. Supercomputing 81) verified up to 2^71. -/
theorem eventual_descent_below_2_71 (hyp : EmpiricalHypotheses) :
    ∀ n : ℕ, n > 1 → n < 2^71 →
      ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0 := by
  intro n hn1 hn71
  -- n reaches 1, so it passes through values < n
  obtain ⟨k, hk⟩ := hyp.barina_verified n (by omega) hn71
  -- nSeq n k = 1 < n (since n > 1)
  exact ⟨k, by omega, by omega⟩

/-- Convergence for all n < 2^71 (from Barina verification).
    **Conditional** on `EmpiricalHypotheses`.
    Updated Phase 57: Barina 2025 (J. Supercomputing 81) verified up to 2^71. -/
theorem convergence_below_2_71 (hyp : EmpiricalHypotheses) :
    ∀ n : ℕ, n > 0 → n < 2^71 →
      ∃ k : ℕ, nSeq n k = 1 := by
  intro n hn hn71
  exact hyp.barina_verified n hn hn71

/-!
## 5. Summary (Sprint P10, Cycle 64)

PROVED (0 sorry, 0 axiom) — Sprint P9/P10 additions marked with [P9]/[P10]:
  - syracuseNext_pos: sN(n) > 0 for all n
  - eventual_descent_class1: class 1 always descends in 1 step
  - eventual_descent_class5: class 5 always descends in 1 step
  - class3_two_step_class: class 3 reaches {1,5} in 1 step
  - class3_two_step_local_descent: class 3 descends locally in 2 steps
  - salmon_trap_abyss: n ≡ 3 mod 16 → sN(n) ≡ 5 mod 8 (ABYSS)
  - salmon_trap_passage: n ≡ 11 mod 16 → sN(n) ≡ 1 mod 8 (gentle)
  - class3_bit4_dichotomy: n ≡ 3 mod 8 → n ≡ 3 or 11 mod 16
  - class5_descent_with_pos: class 5, m > 1 → sN(m) < m ∧ sN(m) > 0
  - class5_ne_one: m ≡ 5 mod 8 → m ≠ 1
  - sN_mod32_eq23_spec: n ≡ 23 mod 32 → v2=1 ∧ sN(n)*2=3n+1
  - sN_mod32_eq23_class: n ≡ 23 mod 32 → sN(n) ≡ 3 mod 16 (ABYSS)
  - eventual_descent_mod32_eq23: n ≡ 23 mod 32 → descent in 3 steps
  - eventual_descent_class7_sub23: class 7 sub-class 23 mod 32 → descent
  - [P9] sN_mod128_eq7_class: n ≡ 7 mod 128 → sN(n) ≡ 11 mod 16 (PASSAGE)
  - [P9] sN2_mod128_eq7_class: n ≡ 7 mod 128 → sN²(n) ≡ 1 mod 16
  - [P9] sN3_mod256_eq7_class: n ≡ 7 mod 256 → sN³(n) ≡ 13 mod 16
  - [P9] sN3_mod256_eq135_class: n ≡ 135 mod 256 → sN³(n) ≡ 5 mod 16
  - [P9] eventual_descent_mod256_eq7: n ≡ 7 mod 256 → descent in 4 steps
  - [P9] eventual_descent_mod256_eq135: n ≡ 135 mod 256 → descent in 4 steps
  - [P9] eventual_descent_mod128_eq7: n ≡ 7 mod 128 → descent in 4 steps
  - [P9] sN_mod128_eq15_class: n ≡ 15 mod 128 → sN(n) ≡ 23 mod 32
  - [P9] eventual_descent_mod128_eq15: n ≡ 15 mod 128 → descent in 4 steps
  - [P9] sN_mod256_eq39_chain: n ≡ 39 mod 256 → sN(n) ≡ 11 mod 16
  - [P9] eventual_descent_mod256_eq39: n ≡ 39 mod 256 → descent in 5 steps
  - [P9] eventual_descent_mod256_eq95: n ≡ 95 mod 256 → descent in 5 steps
  - [P9] eventual_descent_mod256_eq175: n ≡ 175 mod 256 → descent in 5 steps
  - [P9] eventual_descent_mod512_eq79: n ≡ 79 mod 512 → descent in 5 steps
  - [P9] eventual_descent_mod512_eq335: n ≡ 335 mod 512 → descent in 5 steps
  - [P9] eventual_descent_mod256_eq79: n ≡ 79 mod 256 → descent in 5 steps
  - [P9] eventual_descent_mod512_eq199: n ≡ 199 mod 512 → descent in 5 steps
  - [P9] eventual_descent_mod512_eq455: n ≡ 455 mod 512 → descent in 5 steps
  - [P9] eventual_descent_mod256_eq199: n ≡ 199 mod 256 → descent in 5 steps
  - [P10] eventual_descent_mod1024_eq287: n ≡ 287 mod 1024 → descent in 6 steps
  - [P10] eventual_descent_mod1024_eq815: n ≡ 815 mod 1024 → descent in 6 steps
  - [P10] eventual_descent_mod1024_eq975: n ≡ 975 mod 1024 → descent in 6 steps

PROVED (conditional, from axiom/hypothesis):
  - bounded_salmon_implies_descent: BoundedSalmon → EventualDescent
  - bounded_salmon_implies_collatz: BoundedSalmon → Collatz
  - salmon_local_descent: SalmonVisitsAbyss → local descent at class 5
  - eventual_descent_below_2_71: all n < 2^71 descend (from Barina 2025)
  - convergence_below_2_71: all n < 2^71 converge to 1 (from Barina 2025)

CLASS 7 COVERAGE (Sprint P10):
  | Sub-class               | Steps | Density  |
  |-------------------------|-------|----------|
  | n ≡ 23 mod 32 (8/32)    | 3     | 25.0%    |
  | n ≡ 7 mod 128 (2/32)    | 4     | 6.25%    |
  | n ≡ 15 mod 128 (2/32)   | 4     | 6.25%    |
  | n ≡ 39 mod 256 (1/32)   | 5     | 3.125%   |
  | n ≡ 95 mod 256 (1/32)   | 5     | 3.125%   |
  | n ≡ 175 mod 256 (1/32)  | 5     | 3.125%   |
  | n ≡ 79 mod 256 (1/16)   | 5     | 3.125%   |
  | n ≡ 199 mod 256 (1/16)  | 5     | 3.125%   |
  | n ≡ 287 mod 1024 (1/128)| 6     | 0.781%   |
  | n ≡ 815 mod 1024 (1/128)| 6     | 0.781%   |
  | n ≡ 975 mod 1024 (1/128)| 6     | 0.781%   |
  | TOTAL: 71/128            |       | 55.47%   |
  | OPEN: 57/128             |       | 44.53%   |

AXIOMS (empirical, isolated in EmpiricalAxioms.lean):
  - SalmonVisitsAbyss (empirically verified up to n=100000)
  - barina_verified (published: Barina 2025, J. Supercomputing 81, verified to 2^71)
  - evt_bounded_tail (empirically verified up to 2^40)
  - geometric_k_distribution (placeholder, empirical)
-/

end

end ProjetCollatz
