import ProjetCollatz.Phase47NoCycle

/-!
# Phase50CycleEquation.lean — Algebraic Constraints on Hypothetical Cycles

## Purpose

Derive algebraic constraints on any hypothetical non-trivial cycle
of the Syracuse (odd-to-odd Collatz) map. If nSeq n k = n, then
the sum S = aSumSeq n k is tightly constrained.

## Key Results

1. `cycle_pow2_gt_pow3`: 2^S > 3^k (strict, using Phase 47)
2. `cycle_sum_upper`: S ≤ 2k
3. `cycle_nSeq_periodic`: nSeq is periodic

## Date: 2026-02-19 (Phase 50)
-/

namespace ProjetCollatz

open scoped BigOperators

/-- A k-cycle of odd numbers starting at n.
    n > 1, n is odd, k ≥ 1, and the k-th Syracuse iterate returns to n. -/
def IsOddCycle (n : ℕ) (k : ℕ) : Prop :=
  n > 1 ∧ n % 2 = 1 ∧ k ≥ 1 ∧ nSeq n k = n

noncomputable section

/-!
## Part 1: Periodicity of nSeq under a cycle
-/

/-- If nSeq n k = n, then nSeq n (j + k) = nSeq n j. -/
theorem cycle_nSeq_periodic (n k : ℕ) (hcyc : nSeq n k = n) :
    ∀ j : ℕ, nSeq n (j + k) = nSeq n j := by
  intro j
  rw [show j + k = k + j from by ring, nSeq_add, hcyc]

/-- If nSeq n k = n, then nSeq n (m * k) = n for all m. -/
theorem cycle_nSeq_multiples (n k : ℕ) (hcyc : nSeq n k = n) :
    ∀ m : ℕ, nSeq n (m * k) = n := by
  intro m
  induction m with
  | zero => simp [nSeq_zero]
  | succ m ih =>
    rw [show (m + 1) * k = m * k + k from by ring]
    rw [nSeq_add, ih, hcyc]

/-- All elements on the cycle are > 0 (since n > 1). -/
theorem cycle_all_pos (n : ℕ) (hn : n > 1) (j : ℕ) :
    nSeq n j > 0 :=
  nSeq_pos n (by omega) j

/-!
## Part 2: Lower bound — 3^k ≤ 2^S, then strict
-/

/-- From a cycle, 3^k ≤ 2^S where S = aSumSeq n k. -/
theorem cycle_pow3_le_pow2 (n k : ℕ) (hcyc : IsOddCycle n k) :
    3^k ≤ 2^(aSumSeq n k) := by
  have hn1 : n ≥ 1 := by obtain ⟨h1, _, _, _⟩ := hcyc; omega
  have hnk : nSeq n k = n := hcyc.2.2.2
  -- From sandwich lower bound: (n : ℚ) * 3^k / 2^S ≤ (nSeq n k : ℚ)
  have hsand := (syracuse_sandwich n k hn1).1
  rw [hnk] at hsand
  -- (n : ℚ) * 3^k / 2^S ≤ (n : ℚ)
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have h2S_pos : (0 : ℚ) < (2 : ℚ)^(aSumSeq n k) := by positivity
  -- Multiply both sides by 2^S: n * 3^k ≤ n * 2^S
  have h1 : (n : ℚ) * (3 : ℚ)^k ≤ (n : ℚ) * (2 : ℚ)^(aSumSeq n k) := by
    have := mul_le_mul_of_nonneg_right hsand (le_of_lt h2S_pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt h2S_pos)] at this
  -- Divide by n: 3^k ≤ 2^S
  have h2 : (3 : ℚ)^k ≤ (2 : ℚ)^(aSumSeq n k) :=
    le_of_mul_le_mul_left h1 hn_pos
  exact_mod_cast h2

/-- The sum S is positive: aSumSeq n k ≥ 1 for a cycle. -/
theorem cycle_sum_pos (n k : ℕ) (hcyc : IsOddCycle n k) :
    aSumSeq n k ≥ 1 := by
  have hk1 := hcyc.2.2.1
  have hodd := hcyc.2.1
  -- aSumSeq n k = Σ_{i<k} aSeq n i ≥ aSeq n 0 ≥ 1
  unfold aSumSeq aSum
  have hk_pos : k ≥ 1 := hk1
  have h0mem : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hge : aSeq n 0 ≤ Finset.sum (Finset.range k) (fun i => aSeq n i) :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0mem
  have hv1 : aSeq n 0 ≥ 1 := by
    simp only [aSeq, nSeq]
    unfold v2_3n1
    have h3n1_ne : 3 * n + 1 ≠ 0 := by omega
    have h2dvd : (2^1) ∣ (3 * n + 1) := by simp; omega
    exact pow2_dvd_le_v2Nat_pos _ _ h3n1_ne h2dvd
  omega

/-- Strict inequality: 2^S > 3^k (since 2^S ≠ 3^k by parity). -/
theorem cycle_pow2_gt_pow3 (n k : ℕ) (hcyc : IsOddCycle n k) :
    2^(aSumSeq n k) > 3^k := by
  have hle := cycle_pow3_le_pow2 n k hcyc
  have hk1 := hcyc.2.2.1
  have hS1 := cycle_sum_pos n k hcyc
  have hne := pow3_ne_pow2 k (aSumSeq n k) hk1 hS1
  omega

/-!
## Part 3: Upper bound — S ≤ 2k
-/

/-- From a cycle, S ≤ 2k where S = aSumSeq n k. -/
theorem cycle_sum_upper (n k : ℕ) (hcyc : IsOddCycle n k) :
    aSumSeq n k ≤ 2 * k := by
  have hn1 : n ≥ 1 := by obtain ⟨h1, _, _, _⟩ := hcyc; omega
  have hnk : nSeq n k = n := hcyc.2.2.2
  -- From sandwich upper bound: (nSeq n k : ℚ) ≤ (n : ℚ) * 4^k / 2^S
  have hsand := (syracuse_sandwich n k hn1).2
  rw [hnk] at hsand
  -- (n : ℚ) ≤ (n : ℚ) * 4^k / 2^S
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have h2S_pos : (0 : ℚ) < (2 : ℚ)^(aSumSeq n k) := by positivity
  -- Multiply both sides by 2^S: n * 2^S ≤ n * 4^k
  have h1 : (n : ℚ) * (2 : ℚ)^(aSumSeq n k) ≤ (n : ℚ) * (4 : ℚ)^k := by
    have := mul_le_mul_of_nonneg_right hsand (le_of_lt h2S_pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt h2S_pos)] at this
  -- Divide by n: 2^S ≤ 4^k = 2^(2k)
  have h2 : (2 : ℚ)^(aSumSeq n k) ≤ (4 : ℚ)^k :=
    le_of_mul_le_mul_left h1 hn_pos
  -- 4^k = 2^(2k)
  have h4 : (4 : ℚ)^k = (2 : ℚ)^(2 * k) := by
    rw [show (4 : ℚ) = (2 : ℚ)^2 from by norm_num, ← pow_mul]
  rw [h4] at h2
  -- 2^S ≤ 2^(2k) in ℚ ⟹ S ≤ 2k (since base 2 > 1)
  have h3 : (2 : ℕ)^(aSumSeq n k) ≤ (2 : ℕ)^(2 * k) := by exact_mod_cast h2
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3

/-!
## Part 4: Minimum cycle length

A 1-cycle is impossible for n > 1: if nSeq n 1 = n, then syracuseNext n = n,
so n · 2^a = 3n+1 where a = v₂(3n+1). This equation has no solution with n > 1.
-/

/-- **Any non-trivial odd cycle has k ≥ 2** (a 1-cycle is impossible for n > 1).

Proof: if k = 1 then nSeq n 1 = n, i.e., syracuseNext n = n.
By syracuseNext_spec: n · 2^a = 3n+1 where a = v₂(3n+1).
- If a ≤ 1: n · 2^a ≤ 2n < 3n+1 (for n ≥ 1).
- If a ≥ 2: n · 2^a ≥ 4n > 3n+1 (for n > 1).
Both cases contradict n · 2^a = 3n+1. -/
theorem cycle_k_ge_two (n k : ℕ) (hcyc : IsOddCycle n k) : k ≥ 2 := by
  by_contra h
  push_neg at h
  have hk1 := hcyc.2.2.1  -- k ≥ 1
  have hk_eq : k = 1 := by omega
  subst hk_eq
  -- nSeq n 1 = n, i.e., syracuseNext n = n
  have heq := hcyc.2.2.2
  simp only [nSeq] at heq
  -- syracuseNext_spec: syracuseNext n * 2^(v2_3n1 n) = 3*n+1
  have hspec := syracuseNext_spec n
  rw [heq] at hspec
  -- hspec: n * 2^(v2_3n1 n) = 3*n+1, impossible for n > 1
  have hn : n > 1 := hcyc.1
  set a := v2_3n1 n
  by_cases ha : a ≤ 1
  · -- 2^a ≤ 2 → n*2^a ≤ 2n < 3n+1
    have h2a : 2 ^ a ≤ 2 := by interval_cases a <;> norm_num
    nlinarith [Nat.mul_le_mul_left n h2a]
  · -- a ≥ 2 → 2^a ≥ 4 → n*2^a ≥ 4n > 3n+1
    push_neg at ha
    have h2a : 4 ≤ 2 ^ a := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith [Nat.mul_le_mul_left n h2a]

/-!
## Summary

| Theorem | Statement |
|---------|-----------|
| `cycle_nSeq_periodic` | nSeq n (j+k) = nSeq n j |
| `cycle_nSeq_multiples` | nSeq n (m·k) = n |
| `cycle_pow3_le_pow2` | 3^k ≤ 2^S |
| `cycle_pow2_gt_pow3` | 2^S > 3^k (strict) |
| `cycle_sum_upper` | S ≤ 2k |
| `cycle_k_ge_two` | k ≥ 2 (1-cycle impossible) |
-/

end

end ProjetCollatz
