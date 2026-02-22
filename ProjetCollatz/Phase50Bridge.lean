import ProjetCollatz.Phase50CycleEquation

/-!
# Phase50Bridge.lean — Cycle Prevents Reaching One

## Purpose

Prove that if `n` is on a non-trivial odd cycle (IsOddCycle n k),
then `¬ reaches_one n`. This bridges cycle existence to Barina's
computational verification.

## Key Results

1. `cycle_nSeq_ne_one`: no Syracuse iterate on a cycle equals 1
2. `collatz_iter_one_le_four`: the 1→4→2 loop stays ≤ 4
3. `nSeq_reachable_pos`: Collatz time to reach nSeq n m is > 0 for m ≥ 1
4. `cycle_prevents_reaching_one`: IsOddCycle n k → ¬ reaches_one n

## Date: 2026-02-19 (Phase 50)
-/

namespace ProjetCollatz

noncomputable section

/-!
## Part 1: No cycle element equals 1
-/

/-- On a non-trivial cycle, no Syracuse iterate equals 1. -/
theorem cycle_nSeq_ne_one (n k : ℕ) (hcyc : IsOddCycle n k) (j : ℕ) :
    nSeq n j ≠ 1 := by
  intro heq
  have hk1 := hcyc.2.2.1
  have hn1 := hcyc.1
  have hnk := hcyc.2.2.2
  -- nSeq n (j + m) = nSeq 1 m = 1 for all m
  have hstay : ∀ m : ℕ, nSeq n (j + m) = 1 := by
    intro m; rw [nSeq_add, heq, nSeq_stays_at_one]
  -- j * k = j + j * (k - 1), so nSeq n (j * k) = 1
  have hjk : nSeq n (j * k) = 1 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [show j * (k' + 1) = j + j * k' from by ring]
    exact hstay _
  -- But cycle_nSeq_multiples gives nSeq n (j * k) = n > 1
  have := cycle_nSeq_multiples n k hnk j
  omega

/-!
## Part 2: The 1-4-2 loop
-/

/-- `collatz_iter 1 m ≤ 4` for all m (the trajectory is 1,4,2,1,4,2,...) -/
theorem collatz_iter_one_le_four (m : ℕ) : collatz_iter 1 m ≤ 4 := by
  suffices h : ∀ m, collatz_iter 1 m = 1 ∨ collatz_iter 1 m = 2 ∨ collatz_iter 1 m = 4 by
    rcases h m with h | h | h <;> omega
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => left; simp [collatz_iter]
    | 1 =>
      right; right
      simp [collatz_iter, collatz]
    | 2 =>
      right; left
      simp [collatz_iter, collatz]
    | 3 =>
      left
      simp [collatz_iter, collatz]
    | m + 4 =>
      have h3 : collatz_iter 1 3 = 1 := by simp [collatz_iter, collatz]
      have heq : collatz_iter 1 (m + 4) = collatz_iter 1 (m + 1) := by
        rw [show m + 4 = 3 + (m + 1) from by omega, collatz_iter_add, h3]
      rw [heq]; exact ih (m + 1) (by omega)

/-- The odd values in the 1-4-2 loop are exactly 1. -/
theorem collatz_iter_one_odd_eq_one (m : ℕ) (hodd : collatz_iter 1 m % 2 = 1) :
    collatz_iter 1 m = 1 := by
  -- Prove the stronger: collatz_iter 1 m ∈ {1, 2, 4}
  suffices hsuf : ∀ m, collatz_iter 1 m = 1 ∨ collatz_iter 1 m = 2 ∨ collatz_iter 1 m = 4 by
    rcases hsuf m with h | h | h
    · exact h
    · rw [h] at hodd; simp at hodd
    · rw [h] at hodd; simp at hodd
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => left; simp [collatz_iter]
    | 1 => right; right; simp [collatz_iter, collatz]
    | 2 => right; left; simp [collatz_iter, collatz]
    | 3 => left; simp [collatz_iter, collatz]
    | m + 4 =>
      have h3 : collatz_iter 1 3 = 1 := by simp [collatz_iter, collatz]
      have heq : collatz_iter 1 (m + 4) = collatz_iter 1 (m + 1) := by
        rw [show m + 4 = 3 + (m + 1) from by omega, collatz_iter_add, h3]
      rw [heq]; exact ih (m + 1) (by omega)

/-!
## Part 3: Positive Collatz reachability time
-/

/-- For m ≥ 1, the Collatz time to reach nSeq n m is positive. -/
theorem nSeq_reachable_pos (n : ℕ) (hodd : n % 2 = 1) (m : ℕ) (hm : m ≥ 1) :
    ∃ s : ℕ, s > 0 ∧ collatz_iter n s = nSeq n m := by
  -- For m = 1, use syracuseNext_reachable
  -- For m > 1, build on m = 1
  cases m with
  | zero => omega
  | succ m =>
    -- nSeq n (m + 1) is reachable in positive time
    -- First reach nSeq n m, then do one more Syracuse step
    obtain ⟨s₁, hs₁⟩ := nSeq_reachable n hodd m
    have h_odd_m : nSeq n m % 2 = 1 := nSeq_odd n m hodd
    obtain ⟨s₂, hs₂_pos, hs₂⟩ := syracuseNext_reachable (nSeq n m) h_odd_m
    refine ⟨s₁ + s₂, by omega, ?_⟩
    rw [collatz_iter_add, hs₁, hs₂]
    simp [nSeq]

/-!
## Part 4: The Bridge Theorem
-/

/-- **Bridge Theorem**: A non-trivial cycle prevents reaching 1.

If `reaches_one n` holds (∃ s, collatz_iter n s = 1) and
`collatz_iter n s₁ = n` with s₁ > 0, then by well-founded descent
on s, we derive that `n ∈ {1, 2, 4}`, contradicting n > 1 and n odd. -/
theorem cycle_prevents_reaching_one (n k : ℕ) (hcyc : IsOddCycle n k) :
    ¬ reaches_one n := by
  intro ⟨s, hs⟩
  have hn1 := hcyc.1
  have hodd := hcyc.2.1
  have hnk := hcyc.2.2.2
  have hk1 := hcyc.2.2.1
  -- Get positive Collatz time returning to n
  obtain ⟨s₁, hs₁_pos, hs₁⟩ := nSeq_reachable_pos n hodd k hk1
  rw [hnk] at hs₁
  -- Now: collatz_iter n s = 1 and collatz_iter n s₁ = n with s₁ > 0
  -- By well-founded descent on s, derive False
  revert s hs
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro hs
    by_cases hle : s < s₁
    · -- Case: s < s₁
      -- collatz_iter n s₁ = collatz_iter (collatz_iter n s) (s₁ - s)
      have : s₁ = s + (s₁ - s) := by omega
      rw [this, collatz_iter_add, hs] at hs₁
      -- collatz_iter 1 (s₁ - s) = n, but only odd value reachable from 1 is 1
      have hodd_step := collatz_iter_one_odd_eq_one (s₁ - s) (by rw [hs₁]; exact hodd)
      -- n = 1, contradicting n > 1
      omega
    · -- Case: s ≥ s₁. Reduce s to s - s₁.
      have : s = s₁ + (s - s₁) := by omega
      rw [this, collatz_iter_add, hs₁] at hs
      -- collatz_iter n (s - s₁) = 1 with s - s₁ < s
      exact ih (s - s₁) (by omega) hs

/-!
## Summary

| Theorem | Statement |
|---------|-----------|
| `cycle_nSeq_ne_one` | nSeq n j ≠ 1 for all j on a cycle |
| `collatz_iter_one_le_four` | trajectory from 1 stays ≤ 4 |
| `nSeq_reachable_pos` | positive Collatz time for m ≥ 1 |
| `cycle_prevents_reaching_one` | IsOddCycle n k → ¬ reaches_one n |
-/

end

end ProjetCollatz
