---
section: "4"
owner: session_c
status: placeholder
source: mathnotes_0018_section_C
last_updated: 2026-04-24
---

# 4. The three structural hypotheses

**Owner** : Session C Mathlib-Prover, via mathnotes package 0018 §C.

**Status** : awaiting import from mathnotes 0018.

## Expected subsections (per 0064 §3.2)

### 4.1 BakerSeparation
Origin : Baker 1966 *Mathematika* "Linear forms in logarithms". Rhin 1987 effective μ=5.125 refinement. Matveev 2000 effective constants.
Statement in project form : `(2^s - 3^k) · k^6 ≥ 3^k` when `2^s > 3^k`, `s ≥ 1`, `k ≥ 2`.

### 4.2 BarinaVerification
Origin : Barina 2023 (*J. Supercomp.*) large-scale computation `n ≤ 2^71`.
Statement in project form : no non-trivial cycle with `n ≤ 2^71`.

### 4.3 ProductBoundThreshold
Origin : this project. See §5 for the rigorous derivation and the obstruction that forces it to be a hypothesis rather than a theorem.
Statement in project form : for every odd cycle `(n, k)` with `k > 1322`, `n < 2^71`.

## Integration note

When importing Session C draft, preserve :
- Explicit citation of Baker 1966, Rhin 1987, Matveev 2000 for §4.1.
- Explicit citation of Barina 2023 for §4.2 (with DOI).
- §4.3 must forward-reference §5 honestly, not hide the obstruction.
