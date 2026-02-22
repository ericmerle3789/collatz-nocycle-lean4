import ProjetCollatz.HardLowerBoundPaper

/-!
# Phase45UpperBound.lean — The Hard UPPER Bound (dual of R7)

## Purpose

R7 (CollatzCore) proves a LOWER bound: N(K) ≥ N(0) × 3^K / 2^(Σaᵢ).
This file proves the complementary UPPER bound: N(K) ≤ N(0) × 4^K / 2^(Σaᵢ),
valid when all intermediate values N(k) ≥ 1.

## Key Result

**Theorem (hard_upper_bound)**: For any Syracuse trajectory starting at N(0) ≥ 1,
after K odd-to-odd steps with valuations a₀, ..., a_{K-1}:

    N(K) ≤ N(0) × 4^K / 2^(Σᵢ aᵢ)

**Corollary (descent_of_large_sum)**: If Σᵢ aᵢ > 2K, then N(K) < N(0).

This is the missing piece connecting E[v₂] = 2 to descent:
- E[v₂] = 2 means the expected sum is 2K
- When the sum exceeds 2K, the trajectory has descended below its starting point

## Date: 2026-02-19 (Phase 45)
-/

namespace CollatzCore

open scoped BigOperators

variable (N : ℕ → ℚ) (a : ℕ → ℕ)

/-!
## Part 1: The Hard Upper Bound

Each step satisfies N(k+1) = (3N(k)+1)/2^(a_k).
Since 3N(k)+1 ≤ 4N(k) when N(k) ≥ 1, we get N(k+1) ≤ 4N(k)/2^(a_k).
Iterating: N(K) ≤ N(0) × 4^K / 2^(Σaᵢ).
-/

/-- Hypothesis: all intermediate trajectory values are ≥ 1. -/
def all_ge_one (K : ℕ) : Prop := ∀ k, k < K → N k ≥ 1

/-- One-step upper bound: if N(k) ≥ 1 and the step equation holds,
    then N(k+1) ≤ 4 * N(k) / 2^(a_k). -/
theorem step_upper_bound (k : ℕ) (hstep : step N a k) (hge : N k ≥ 1) :
    N (k + 1) ≤ 4 * N k / (2 : ℚ) ^ (a k) := by
  -- From step: N(k+1) = (3*N(k)+1) / 2^(a_k)
  rw [step] at hstep
  rw [hstep]
  -- Need: (3*N(k)+1) / 2^(a_k) ≤ 4*N(k) / 2^(a_k)
  -- Since 2^(a_k) > 0, this reduces to 3*N(k)+1 ≤ 4*N(k)
  have hden_pos : (0 : ℚ) < (2 : ℚ) ^ (a k) := by positivity
  rw [div_le_div_iff_of_pos_right hden_pos]
  -- Need: 3*N(k)+1 ≤ 4*N(k)
  linarith

/-- The hard upper bound: N(K) ≤ N(0) × 4^K / 2^(Σaᵢ). -/
theorem hard_upper_bound (K : ℕ)
    (h : steps_up_to N a K)
    (hge : all_ge_one N K) :
    N K ≤ N 0 * (4 : ℚ)^K / ((2 : ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i))) := by
  induction K with
  | zero => simp
  | succ K ih =>
    -- Induction hypothesis
    have hprev : steps_up_to N a K := fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hge_prev : all_ge_one N K := fun k hk => hge k (Nat.lt_succ_of_lt hk)
    have ihK := ih hprev hge_prev
    -- Step at k = K
    have hstep := h K (Nat.lt_succ_self K)
    have hge_K : N K ≥ 1 := hge K (Nat.lt_succ_self K)
    -- Upper bound at step K
    have hstep_ub := step_upper_bound N a K hstep hge_K
    -- Denominator positivity
    have hden_pos : (0 : ℚ) < (2 : ℚ) ^ (a K) := by positivity
    have hden_sum_pos : (0 : ℚ) < (2 : ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i)) := by
      positivity
    -- Chain: N(K+1) ≤ 4*N(K)/2^(a_K) ≤ 4*(N(0)*4^K/2^S_K)/2^(a_K)
    calc N (K + 1)
        ≤ 4 * N K / (2 : ℚ) ^ (a K) := hstep_ub
      _ ≤ 4 * (N 0 * (4 : ℚ) ^ K / (2 : ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i))) /
            (2 : ℚ) ^ (a K) := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left ihK (by norm_num : (0:ℚ) ≤ 4)
          · exact le_of_lt hden_pos
      _ = N 0 * (4 : ℚ) ^ (K + 1) /
            ((2 : ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i)) * (2 : ℚ) ^ (a K)) := by
          have h1 : ((2 : ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i))) ≠ 0 := by positivity
          have h2 : ((2 : ℚ) ^ (a K)) ≠ 0 := by positivity
          field_simp
          ring
      _ = N 0 * (4 : ℚ) ^ (K + 1) /
            (2 : ℚ) ^ (Finset.sum (Finset.range (K + 1)) (fun i => a i)) := by
          congr 1
          rw [Finset.sum_range_succ, pow_add]

end CollatzCore

/-!
## Part 2: Descent theorems in the ProjetCollatz namespace
-/

namespace ProjetCollatz

open scoped BigOperators

noncomputable section

/-!
### Syracuse specialization

We connect the abstract upper bound to actual Syracuse trajectories.
-/

/-- All values in a Syracuse odd-to-odd trajectory starting at n ≥ 1 are ≥ 1.
    (Since syracuseNext always produces an odd number, and odd numbers are ≥ 1.) -/
theorem nSeq_ge_one (n : ℕ) (hn : n ≥ 1) (k : ℕ) : (nSeq n k : ℚ) ≥ 1 := by
  induction k with
  | zero =>
    simp [nSeq]
    exact_mod_cast hn
  | succ k _ =>
    simp [nSeq]
    have hodd := syracuseNext_odd (nSeq n k)
    have hge1 : syracuseNext (nSeq n k) ≥ 1 := by omega
    exact_mod_cast hge1

/-- Bridge: NrecSyr equals nSeq cast to ℚ. -/
theorem NrecSyr_eq_nSeq_cast (n : ℕ) : ∀ k : ℕ,
    NrecSyr n k = (nSeq n k : ℚ) := by
  intro k
  induction k with
  | zero =>
    simp [NrecSyr, CollatzOddInst.Nrec, x0_of_start, nSeq]
  | succ k ih =>
    -- NrecSyr n (k+1) = Nrec (n:ℚ) (aSeq n) (k+1)
    --                  = (3 * Nrec (n:ℚ) (aSeq n) k + 1) / 2^(aSeq n k)
    -- By IH: Nrec ... k = (nSeq n k : ℚ)
    -- nSeq n (k+1) = syracuseNext(nSeq n k)
    -- syracuseNext_spec: syracuseNext m * 2^(v2_3n1 m) = 3m+1
    -- So: syracuseNext m = (3m+1) / 2^(v2_3n1 m)
    -- And aSeq n k = v2_3n1 (nSeq n k)
    unfold NrecSyr at ih ⊢
    simp only [CollatzOddInst.Nrec] at ih ⊢
    rw [ih]
    simp only [nSeq, aSeq, v2_3n1]
    -- Goal: (3 * ↑(nSeq n k) + 1) / 2^v₂ = ↑(syracuseNext (nSeq n k))
    have hspec := syracuseNext_spec (nSeq n k)
    -- hspec: syracuseNext(nSeq n k) * 2^(v2_3n1(nSeq n k)) = 3*(nSeq n k)+1
    have hden_ne : ((2:ℚ) ^ (v2Nat (3 * nSeq n k + 1))) ≠ 0 := by positivity
    rw [div_eq_iff hden_ne]
    -- Goal: ↑(syracuseNext(nSeq n k)) * 2^v₂ = 3*↑(nSeq n k)+1
    have : (syracuseNext (nSeq n k) : ℚ) * ((2:ℚ) ^ (v2Nat (3 * nSeq n k + 1))) =
        ((3 * nSeq n k + 1 : ℕ) : ℚ) := by
      unfold v2_3n1 at hspec
      exact_mod_cast hspec
    push_cast at this ⊢
    linarith

/-- The hard upper bound for Syracuse trajectories:
    nSeq(n, K) ≤ n × 4^K / 2^(Σ v₂ᵢ). -/
theorem syracuse_hard_upper_bound (n K : ℕ) (hn : n ≥ 1) :
    (nSeq n K : ℚ) ≤ (n : ℚ) * (4 : ℚ)^K /
      ((2 : ℚ) ^ (aSumSeq n K)) := by
  rw [← NrecSyr_eq_nSeq_cast]
  -- NrecSyr n 0 = (n : ℚ)
  have h0 : NrecSyr n 0 = (n : ℚ) := by simp [NrecSyr, CollatzOddInst.Nrec, x0_of_start]
  rw [← h0]
  -- Apply the abstract upper bound
  have hsteps := steps_up_to_NrecSyr n K
  have hge : CollatzCore.all_ge_one (fun k => NrecSyr n k) K := by
    intro k hk
    simp only
    rw [NrecSyr_eq_nSeq_cast]
    exact nSeq_ge_one n hn k
  have hub := CollatzCore.hard_upper_bound (fun k => NrecSyr n k) (aSeq n) K hsteps hge
  exact hub

/-- **THE DESCENT THEOREM**: If the sum of v₂ values exceeds 2K,
    then the trajectory has descended below its starting point.

    This is the key result connecting E[v₂] = 2 to the Collatz conjecture:
    since E[v₂] = 2, we expect Σ v₂ᵢ ≈ 2K, and when Σ v₂ᵢ > 2K,
    descent is guaranteed. -/
theorem descent_of_large_v2_sum (n K : ℕ) (hn : n ≥ 2)
    (hsum : aSumSeq n K > 2 * K) :
    (nSeq n K : ℚ) < (n : ℚ) := by
  have hn1 : n ≥ 1 := by omega
  have hub := syracuse_hard_upper_bound n K hn1
  -- hub: nSeq n K ≤ n * 4^K / 2^(aSumSeq n K)
  -- 4^K = 2^(2K), so n * 4^K / 2^S = n * 2^(2K) / 2^S = n * 2^(2K-S)
  -- Since S > 2K, 2^(2K-S) < 1, so n * 2^(2K-S) < n
  -- More precisely: 4^K / 2^S = 4^K / 2^S ≤ 4^K / 2^(2K+1) = 2^(2K) / 2^(2K+1) = 1/2
  calc (nSeq n K : ℚ)
      ≤ (n : ℚ) * (4 : ℚ)^K / ((2 : ℚ) ^ (aSumSeq n K)) := hub
    _ < (n : ℚ) := by
        -- Need: n * 4^K / 2^S < n, i.e., 4^K / 2^S < 1
        -- i.e., 4^K < 2^S, i.e., 2^(2K) < 2^S, i.e., 2K < S
        rw [div_lt_iff₀ (by positivity : (0:ℚ) < (2:ℚ) ^ (aSumSeq n K))]
        -- Goal: n * 4^K < n * 2^S
        have h4eq : (4:ℚ)^K = (2:ℚ)^(2*K) := by
          rw [show (4:ℚ) = (2:ℚ)^2 from by norm_num, ← pow_mul]
        rw [h4eq]
        -- n * 2^(2K) < n * 2^S when 2K < S and n > 0
        apply mul_lt_mul_of_pos_left
        · exact pow_lt_pow_right₀ (by norm_num : (1:ℚ) < 2) (by omega)
        · exact_mod_cast (show (0:ℕ) < n by omega)

/-!
### Part 3: The Sandwich Theorem

Combining R7's lower bound with Phase 45's upper bound:

    n × 3^K / 2^S  ≤  nSeq(n, K)  ≤  n × 4^K / 2^S

where S = Σᵢ v₂(3·nSeq(n,i)+1).

This gives tight control over trajectory behavior:
- If S < K·log₂(3) ≈ 1.585·K: trajectory grows (lower bound > n)
- If S > 2K: trajectory descends (upper bound < n)
- Since E[v₂] = 2 > 2: descent happens on average
-/

/-- **THE SANDWICH THEOREM**: Syracuse trajectories are trapped between
    n × 3^K / 2^S and n × 4^K / 2^S. -/
theorem syracuse_sandwich (n K : ℕ) (hn : n ≥ 1) :
    (n : ℚ) * (3 : ℚ)^K / ((2 : ℚ) ^ (aSumSeq n K)) ≤ (nSeq n K : ℚ) ∧
    (nSeq n K : ℚ) ≤ (n : ℚ) * (4 : ℚ)^K / ((2 : ℚ) ^ (aSumSeq n K)) := by
  constructor
  · -- Lower bound from R7
    have hlb := syracuse_hard_lower_bound_inst n K
    rw [NrecSyr_eq_nSeq_cast] at hlb
    have h0 : NrecSyr n 0 = (n : ℚ) := by simp [NrecSyr, CollatzOddInst.Nrec, x0_of_start]
    rw [h0] at hlb
    exact hlb
  · -- Upper bound from Phase 45
    exact syracuse_hard_upper_bound n K hn

end

end ProjetCollatz
