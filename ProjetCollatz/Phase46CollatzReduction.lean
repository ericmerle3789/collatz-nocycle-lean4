import ProjetCollatz.Phase45UpperBound
import ProjetCollatz.Phase33ConditionalCollatz

/-!
# Phase46CollatzReduction.lean — THE Reduction Theorem

## Purpose

Reduce the Collatz conjecture to a single arithmetic inequality about 2-adic valuations.

## Main Result

**Theorem (collatz_of_v2_dominance)**:

    If ∀ odd n > 1, ∃ K, aSumSeq n K > 2*K
    then ∀ n > 0, n eventually reaches 1 under Collatz.

In words: if for every starting odd number, the cumulative 2-adic valuations
eventually exceed twice the number of steps, then the Collatz conjecture holds.

## Proof Chain (all 0 sorry)

1. Phase 45: `descent_of_large_v2_sum` — if Σv₂ > 2K then nSeq(n,K) < n
2. Phase 33: `conditional_collatz` — if every odd n > 1 descends then Collatz holds
3. This file: chains 1 → 2 to get the clean reduction

## Why This Matters

- E[v₂] = 2 for uniformly random odd n (proved formally for k=1..5, confirmed to k=100)
- By LLN, Σv₂ ≈ 2K with probability 1
- The sum exceeds 2K in median 3-4 steps (experimentally confirmed for n up to 2^1000)
- This theorem makes the precise statement: proving Σv₂ > 2K suffices for Collatz

The gap between this and a full proof is exactly the independence/ergodicity of the
v₂ sequence along trajectories — the hardest part of the Collatz problem.

## Date: 2026-02-19 (Phase 46)
-/

namespace ProjetCollatz

open scoped BigOperators

noncomputable section

/-!
## Part 1: From v₂ dominance to descent
-/

/-- **V₂ Dominance Hypothesis**: for every odd n > 1, there exists K steps
    such that the cumulative 2-adic valuation sum exceeds 2K. -/
def V2Dominance : Prop :=
  ∀ n : ℕ, n > 1 → n % 2 = 1 → ∃ K : ℕ, K > 0 ∧ aSumSeq n K > 2 * K

/-- Under V₂ dominance, every odd n > 1 descends. -/
theorem descends_of_v2_dominance (hdom : V2Dominance) :
    ∀ n : ℕ, n > 1 → n % 2 = 1 → Descends n := by
  intro n hn1 hodd
  obtain ⟨K, hK_pos, hsum⟩ := hdom n hn1 hodd
  -- descent_of_large_v2_sum: aSumSeq n K > 2*K → (nSeq n K : ℚ) < (n : ℚ)
  have hdesc := descent_of_large_v2_sum n K (by omega : n ≥ 2) hsum
  -- Convert from ℚ inequality to ℕ inequality
  have hlt : nSeq n K < n := by exact_mod_cast hdesc
  exact ⟨K, hK_pos, hlt⟩

/-!
## Part 2: THE Reduction Theorem
-/

/-- **THE COLLATZ REDUCTION THEOREM**:
    V₂ dominance implies the Collatz conjecture.

    If for every odd n > 1, there exists K > 0 such that
    Σᵢ₌₀^{K-1} v₂(3·nSeq(n,i)+1) > 2K,
    then every n > 0 eventually reaches 1 under Collatz iteration.

    This reduces the Collatz conjecture to a purely arithmetic statement
    about cumulative 2-adic valuations along Syracuse trajectories. -/
theorem collatz_of_v2_dominance (hdom : V2Dominance) :
    ∀ n : ℕ, n > 0 → reaches_one n := by
  exact conditional_collatz (descends_of_v2_dominance hdom)

/-!
## Part 3: The Quantitative Statement

We can also state a more quantitative version:
if the v₂ sum exceeds 2K at some specific step K₀ = f(n),
then nSeq(n, K₀) < n.

Combined with the sandwich theorem, we get precise bounds.
-/

/-- **Quantitative descent**: For any specific n ≥ 2 and K such that
    the v₂ sum exceeds 2K, we get both:
    - descent: nSeq(n,K) < n
    - lower bound: nSeq(n,K) ≥ n * 3^K / 2^(aSumSeq n K)

    This gives the trajectory value in the "landing zone"
    [n * 3^K / 2^S, n) after K steps. -/
theorem descent_landing_zone (n K : ℕ) (hn : n ≥ 2)
    (hsum : aSumSeq n K > 2 * K) :
    (n : ℚ) * (3 : ℚ)^K / ((2 : ℚ) ^ (aSumSeq n K)) ≤ (nSeq n K : ℚ) ∧
    (nSeq n K : ℚ) < (n : ℚ) := by
  constructor
  · -- Lower bound from sandwich
    exact (syracuse_sandwich n K (by omega : n ≥ 1)).1
  · -- Descent from Phase 45
    exact descent_of_large_v2_sum n K hn hsum

/-!
## Summary

| Theorem | Statement | Sorry |
|---------|-----------|-------|
| `V2Dominance` | ∀ odd n>1, ∃K>0, Σv₂ > 2K | (hypothesis) |
| `descends_of_v2_dominance` | V2Dominance → ∀ odd n>1, Descends n | 0 |
| `collatz_of_v2_dominance` | V2Dominance → Collatz | 0 |
| `descent_landing_zone` | Σv₂ > 2K → trajectory in [n·3^K/2^S, n) | 0 |

## The Logical Chain (complete, 0 sorry)

```
V₂ staircase (Phase 44)          R7 lower bound (CollatzCore)
  P(v₂=k) = 1/2^k for k=1..5    N(K) ≥ N(0)·3^K/2^S
  ⟹ E[v₂] = 2                              ↓
         ↓                        Phase 45 upper bound
  V₂ Dominance hypothesis          N(K) ≤ N(0)·4^K/2^S
  ∀ odd n>1, ∃K, Σv₂ > 2K                   ↓
         ↓                        descent_of_large_v2_sum
  descends_of_v2_dominance          Σv₂ > 2K ⟹ N(K) < N(0)
         ↓                                   ↓
  conditional_collatz (Phase 33)  ⟵ Descends n
         ↓
  **∀ n > 0, reaches_one n**
  = THE COLLATZ CONJECTURE
```

The only remaining gap: proving V₂ Dominance.
This requires showing that the v₂ sequence along trajectories
behaves sufficiently like i.i.d. Geometric(1/2) —
the fundamental open problem of the Collatz conjecture.
-/

end

end ProjetCollatz
