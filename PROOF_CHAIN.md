# Proof Chain — Porte 2 (Anti-Cycle)

## Date: 2026-02-22
## Auditor: Claude Code (Opus 4.6)

---

## Final Theorem

- **File**: `ProjetCollatz/Phase59ContinuedFractions.lean`
- **Name**: `no_nontrivial_cycle_phase59`
- **Signature**:
  ```lean
  theorem no_nontrivial_cycle_phase59
      (baker : BakerSeparation) (barina : BarinaVerification)
      (cf : DerivedLargeKBound)
      (n k : ℕ) (hcyc : IsOddCycle n k) : False
  ```
- **Parameters**: 3 hypothesis structures + 2 naturals + 1 proposition
- **Content**: Under Baker + Barina + CF, no non-trivial Collatz cycle exists

---

## Dependency Tree

```
Phase59ContinuedFractions.lean  <-- THE MAIN THEOREM
  │
  ├── no_nontrivial_cycle_phase59 (Baker+Barina+CF → False)
  │     ├── CASE k ≤ 1322: no_cycle_k_le_1322 (Phase58)
  │     │     ├── cycle_has_min (Phase56) → finds minimum m
  │     │     ├── cycle_min_bound_nat (Phase56, uses Baker) → m ≤ (k⁷+k)/3
  │     │     │     ├── product_bound (Phase56) → 2^S·n^k ≤ (3n+1)^k
  │     │     │     ├── bernoulli_upper_nat (Phase56) → (a+b)^k·(a-kb) ≤ a^k·a
  │     │     │     └── BakerSeparation.separation (k≥2)
  │     │     ├── k1322_bound_implies_n_bound (Phase58) → m < 2^71
  │     │     ├── BarinaVerification.convergence → reaches_one m
  │     │     └── cycle_prevents_reaching_one (Phase50) → contradiction
  │     │
  │     └── CASE k > 1322: no_cycle_k_gt_1322 (Phase59)
  │           ├── DerivedLargeKBound.large_k_bound → n < 2^71
  │           ├── BarinaVerification.convergence → reaches_one n
  │           └── cycle_prevents_reaching_one (Phase50) → contradiction
  │
  ├── cf_gap_8..13 (6 native_decide arithmetic proofs)
  ├── cf_nbound_8..13 (6 native_decide bound proofs)
  └── sdw_from_cf (ProductBoundThreshold derived as corollary)

Phase58PorteDeuxFinal.lean
  ├── BakerSeparation (hypothesis structure, k≥2)
  ├── BarinaVerification (hypothesis structure)
  ├── ProductBoundThreshold (hypothesis structure, DERIVED in Phase59)
  └── hercher_derived (k ≥ 92 is PROVED from Baker+Barina)

Phase56Bloc18Complete.lean
  ├── partial_product_bound (induction on m)
  ├── product_bound (specialization at m=k)
  ├── bernoulli_upper_nat (induction on k)
  ├── cycle_min_bound_nat (two cases: k≥3n and k<3n)
  ├── cycle_has_min (via Finset.min')
  └── no_nontrivial_cycle_derived (uses ExternalCycleHypothesesDerived)

Phase55CycleBound.lean
  ├── IsCycleMin (structure)
  ├── per_step_ineq ((3m+1)n ≤ (3n+1)m when n≤m)
  └── baker_bounds_n_via_corrSum (n·3^k ≤ corrSum·k^6)

Phase52SteinerEquation.lean
  └── nSeq_step_mul (Syracuse multiplicative step)

Phase50CycleEquation.lean
  ├── IsOddCycle (definition)
  ├── cycle_k_ge_two (k ≥ 2 for any cycle, proved)
  ├── cycle_pow2_gt_pow3 (2^S > 3^k, strict)
  └── cycle_sum_pos (S ≥ 1)

Phase50Bridge.lean
  ├── cycle_nSeq_ne_one (no orbit element = 1)
  ├── collatz_iter_one_le_four (1→4→2 loop)
  └── cycle_prevents_reaching_one (IsOddCycle → ¬reaches_one)

Phase33ConditionalCollatz.lean
  ├── collatz, collatz_iter, reaches_one
  ├── syracuseNext_reachable (odd→odd reachable in positive time)
  └── nSeq_reachable (nSeq reachable via collatz_iter)

SyracuseDefs.lean
  ├── v2Nat, v2_3n1 (2-adic valuation)
  ├── syracuseNext ((3n+1)/2^v₂)
  └── nSeq, aSeq (Syracuse sequences)
```

---

## What is PROVED vs ASSUMED

| Result | Status | File |
|--------|--------|------|
| Product Bound (2^S·n^k ≤ (3n+1)^k) | **PROVED** | Phase56 |
| Bernoulli upper bound | **PROVED** | Phase56 |
| cycle_has_min (minimum exists) | **PROVED** | Phase56 |
| cycle_prevents_reaching_one | **PROVED** | Phase50 |
| cycle_pow2_gt_pow3 (2^S > 3^k) | **PROVED** | Phase50 |
| cycle_k_ge_two (k ≥ 2) | **PROVED** | Phase50 |
| Steiner equation | **PROVED** | Phase52 |
| n ≤ (k⁷+k)/3 for cycle minimum | **PROVED** | Phase56 |
| k ≥ 92 (Hercher) | **PROVED** from Baker+Barina | Phase58 |
| ProductBoundThreshold (k ≤ 982) | **PROVED** from Baker+Barina+CF | Phase59 |
| Baker separation | **ASSUMED** (hypothesis) | Phase58 |
| Barina verification | **ASSUMED** (hypothesis) | Phase58 |
| CF separation for k > 1322 | **ASSUMED** (hypothesis) | Phase59 |

---

## Axioms: 0 | Sorry: 0 | Hypotheses: 3
