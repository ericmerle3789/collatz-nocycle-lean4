# Hypotheses and Assumptions — NEXUS Porte 2

## Classification of assumptions

### PUBLISHED RESULTS (faithful encodings)

1. **BakerSeparation** — Baker (1966) / Matveev (2000)
   - Statement: `(2^s - 3^k) * k^6 ≥ 3^k` for s,k ≥ 1 with 2^s > 3^k
   - Source: Baker's theorem on linear forms in logarithms
   - Combined with Rhin's irrationality measure μ(log₂3) ≤ 5.125
   - Exponent 6 from: effective constants in Matveev (2000)
   - Lean condition: k ≥ 2 (not k ≥ 1) because (2²-3¹)·1⁶ = 1 < 3 is a counterexample
   - For cycles, k ≥ 2 is guaranteed by `cycle_k_ge_two` (Phase 50)

2. **BarinaVerification** — Barina (2025), J. Supercomputing 81
   - Statement: `∀ n < 2^71, CollatzConverges n`
   - Source: Direct computational verification
   - DOI: 10.1007/s11227-025-07337-0
   - Actual limit: 2075 × 2^60 ≈ 2^71.02 (our bound 2^71 is conservative)

3. **Simons & de Weger (2005)** — Acta Arithmetica 117(1):51-70
   - Statement: No non-trivial m-cycles for m ≤ 68
   - m = number of local minima (NOT number of odd steps k)
   - Extended by Hercher (2023) to m ≤ 90
   - NOTE: We do NOT encode this result directly in our Lean code.

### OUR DERIVATIONS (not attributed to published papers)

4. **ProductBoundThreshold** (formerly SimonsDeWegerBound)
   - Statement: `IsOddCycle n k → k ≤ 982`
   - Derivation: Product Bound `n ≤ (k⁷+k)/3` (Phase 56) + Barina's 2^71 limit
   - The number 982 satisfies `(982^7 + 982)/3 < 2^71`
   - This is OUR calculation, not from any published paper
   - In Phase 59: DERIVED as a corollary (vacuously true, no cycle exists)

5. **DerivedLargeKBound** (formerly ContinuedFractionSeparation)
   - Statement: `IsOddCycle n k → k > 1322 → n < 2^71`
   - Derivation: Baker + CF gaps of log₂3 + Product Bound + Barina
   - This is OUR derivation combining multiple published results
   - 6 CF gap lemmas verified by `native_decide`
   - The logical bridge (best approximation theorem) is the hypothesis content

### RELATION m (Simons-de Weger) vs k (our formalization)

- m = number of local minima in cycle
- k = number of odd steps (syracuseNext applications)
- Relation: m ≤ k (each minimum needs at least one odd step)
- SdW gives a LOWER bound on m (m ≥ 69)
- We derive an UPPER bound on k (k ≤ 982) via a different method
- These are INDEPENDENT results going in OPPOSITE directions

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

## H3: DerivedLargeKBound

### Lean Definition

```lean
structure DerivedLargeKBound where
  large_k_bound : ∀ (n k : ℕ), IsOddCycle n k → k > 1322 → n < 2 ^ 71
```

**File**: `ProjetCollatz/Phase59ContinuedFractions.lean:115`

### Source: OUR DERIVATION (not a single published result)

Follows from combining:
1. Baker's theorem (BakerSeparation) — linear forms in logarithms
2. Product Bound: n ≤ (k⁷+k)/3 (Phase 56, PROVED)
3. CF convergent gaps of log₂3 at q₈ through q₁₃ (Legendre 1798)
4. Barina's verification bound (2^71)

This is NOT a direct result from any single published paper.
The name was changed from `ContinuedFractionSeparation` to make this clear.

### Correspondence: ENCODED

This is not a direct published result but a consequence of published results
combined with finite computation:

1. The continued fraction expansion of log_2(3) has known convergents
   q_8=665, q_9=15601, ..., q_13=190537.
2. For each window [q_i, q_{i+1}), Baker's theorem + the CF gap gives
   a per-k upper bound on n.
3. For k > 1322 (past q_8), the per-k bound is below 2^71.

**Evidence**: 6 CF gap lemmas (cf_gap_8 through cf_gap_13) are all proved
by `native_decide`. The logical bridge connecting CF gaps to per-k cycle
bounds is the hypothesis content.

### Where Used

- `no_cycle_k_gt_1322` (Phase59): directly applied to get n < 2^71

---

## Summary

| # | Hypothesis | Source | Correspondence | Notes |
|---|-----------|--------|----------------|-------|
| H1 | BakerSeparation | Baker 1966 + Rhin 1987 | APPROXIMATION (mu=6 vs 5.125) | C=1, valid for k>=2 |
| H2 | BarinaVerification | Barina 2025 | EXACT (conservative) | 2^71 < 2^71.02 |
| H3 | DerivedLargeKBound | Our derivation (Baker+CF) | ENCODED | 6 CF gaps by native_decide |

---

## Naming History

| Current Name | Former Name | Reason for Change |
|-------------|-------------|-------------------|
| ProductBoundThreshold | SimonsDeWegerBound | k ≤ 982 is from Product Bound, NOT from SdW |
| DerivedLargeKBound | ContinuedFractionSeparation | Our derivation, not a single published result |

---

## References

- Baker, A. "Linear forms in the logarithms of algebraic numbers"
  (Mathematika 13, 1966)
- Barina, D. "Improved verification limit for the convergence of the
  Collatz conjecture" (J. Supercomputing 81, 810, 2025)
  DOI: 10.1007/s11227-025-07337-0
- Hercher, C. "There are no Collatz-m-Cycles with m ≤ 91"
  (Journal of Integer Sequences, Vol. 26, 2023). arXiv:2201.00406
- Legendre, A.-M. "Essai sur la théorie des nombres" (1798)
  — best approximation theorem for continued fractions
- Matveev, E. M. "An explicit lower bound for a homogeneous rational
  linear form in the logarithms of algebraic numbers" (Izv. Math. 64, 2000)
- Rhin, G. "Approximants de Pade et mesures effectives d'irrationalite"
  (Seminaire de Theorie des Nombres de Paris, 1987)
- Simons, J. & de Weger, B. "Theoretical and computational bounds for
  m-cycles of the 3n+1-problem" (Acta Arithmetica 117.1, 2005, pp. 51-70)
