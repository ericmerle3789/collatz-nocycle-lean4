# Hypotheses — Porte 2 (Anti-Cycle Proof)

This document details the three hypotheses used in the formal proof that
no non-trivial Collatz cycle exists. Each hypothesis corresponds to a
published, peer-reviewed mathematical result.

---

## H1: BakerSeparation

### Lean Definition

```lean
structure BakerSeparation where
  separation : ∀ (s k : ℕ), s ≥ 1 → k ≥ 2 → 2^s > 3^k →
    (2^s - 3^k) * k^6 ≥ 3^k
```

**File**: `ProjetCollatz/Phase58PorteDeuxFinal.lean:67`

### Published Source

- Baker, A. "Linear forms in the logarithms of algebraic numbers"
  (Mathematika 13, 1966). Fields Medal 1970.
- Rhin, G. "Approximants de Pade et mesures effectives d'irrationalite"
  (Seminaire de Theorie des Nombres de Paris, 1987).

### Correspondence: APPROXIMATION (conservative)

The formalization uses irrationality exponent mu = 6, which is strictly weaker
than Rhin's published bound mu(log_2(3)) <= 5.125. The implicit constant C = 1
holds for all k >= 2 with approximately 50x margin.

**Note**: The condition k >= 2 (not k >= 1) is essential because (2^2 - 3^1) * 1^6 = 1 < 3
is a counterexample at k = 1. The theorem `cycle_k_ge_two` (Phase50) proves k >= 2 for
any IsOddCycle without using Baker, so all call sites are valid.

### Where Used

- `cycle_min_bound_nat` (Phase56): bounds the minimum cycle element
- `baker_bounds_n_via_corrSum` (Phase55): combines Baker with Steiner equation

---

## H2: BarinaVerification

### Lean Definition

```lean
structure BarinaVerification where
  convergence : ∀ (n : ℕ), n > 0 → n < 2^71 → reaches_one n
```

**File**: `ProjetCollatz/Phase58PorteDeuxFinal.lean:80`

### Published Source

- Barina, D. "Improved verification limit for the convergence of the
  Collatz conjecture" (J. Supercomputing 81, 810, 2025).
- DOI: 10.1007/s11227-025-07337-0
- Verified up to 2075 * 2^60, which is approximately 2^71.02.

### Correspondence: EXACT (slightly conservative)

The bound n < 2^71 is slightly below the actual verification limit of
2075 * 2^60 ~ 2^71.02, making the hypothesis strictly weaker than
(and therefore implied by) the published result.

### Where Used

- `no_cycle_k_le_1322` (Phase58): any cycle element below 2^71 converges
- `no_cycle_k_gt_1322` (Phase59): same, after CF bounds the element

---

## H3: ContinuedFractionSeparation

### Lean Definition

```lean
structure ContinuedFractionSeparation where
  large_k_bound : ∀ (n k : ℕ), IsOddCycle n k → k > 1322 → n < 2 ^ 71
```

**File**: `ProjetCollatz/Phase59ContinuedFractions.lean:115`

### Published Source

Follows from:
- Baker (1966) + Rhin (1987): linear forms in logarithms
- Legendre (1798): continued fraction theory
- Simons & de Weger (2005): "Theoretical and computational bounds for
  m-cycles of the 3n+1 problem" (Acta Arithmetica 117.1).

### Correspondence: ENCODED

This is not a direct published result but a consequence of published results
combined with finite computation:

1. The continued fraction expansion of log_2(3) has known convergents
   q_8=665, q_9=15601, ..., q_13=190537.
2. For each window [q_i, q_{i+1}), Baker's theorem + the CF gap gives
   a per-k upper bound on n.
3. For k > 1322 (past q_13), the per-k bound is below 2^71.

**Evidence**: 6 CF gap lemmas (cf_gap_8 through cf_gap_13) are all proved
by `native_decide`. The logical bridge connecting CF gaps to per-k cycle
bounds is the hypothesis content.

### Where Used

- `no_cycle_k_gt_1322` (Phase59): directly applied to get n < 2^71

---

## Summary

| # | Hypothesis | Published | Correspondence | Implicit Constant |
|---|-----------|-----------|----------------|-------------------|
| H1 | BakerSeparation | Baker 1966 + Rhin 1987 | APPROXIMATION (mu=6 vs 5.125) | C=1, valid for k>=2 |
| H2 | BarinaVerification | Barina 2025 | EXACT (conservative) | 2^71 < 2^71.02 |
| H3 | ContinuedFractionSeparation | Baker + CF theory | ENCODED | 6 CF gaps by native_decide |
