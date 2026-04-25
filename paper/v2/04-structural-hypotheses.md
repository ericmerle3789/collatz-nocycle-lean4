---
section: "4"
owner: session_c
status: imported-session-c-section-C
contributions:
  - "§4 content drafted by Session C Mathlib-Prover, mathnotes package 0018 §C (mailbox from_mathlib_prover/0018, 2026-04-24T19:40:00Z). Integrated by Worker per Session B authorization 0083 §5.3 + 0101 §5, with cross-reference adjustments to §2.3 (already-committed Phase58 structures verbatim) and §5 (Obstruction I)."
source: mailbox/from_mathlib_prover/0018 §C
last_updated: 2026-04-24
---

# 4. The three structural hypotheses

The conditional theorem of §3 depends on three hypothesis-structures
declared in `ProjetCollatz/Phase58PorteDeuxFinal.lean`. The Lean
signatures are shown verbatim in §2.3 (`BakerSeparation` lines 67-69,
`BarinaVerification` lines 80-81, `ProductBoundThreshold` lines
296-297) ; this section provides the mathematical and bibliographic
context for each.

## 4.1 BakerSeparation (Baker 1966)

```lean
structure BakerSeparation where
  separation : ∀ (s k : ℕ), s ≥ 1 → k ≥ 2 → 2^s > 3^k →
    (2^s - 3^k) * k^6 ≥ 3^k
```

**Source.** Baker, A. (1966), « Linear forms in the logarithms of
algebraic numbers », *Mathematika* 13, pp. 204-216. Refined by Matveev
(2000) and Rhin (1987). Fields Medal 1970.

**Scope.** It is standard in the Collatz cycle literature to adopt
Baker as an external hypothesis ; Steiner (1977), Simons-de Weger
(2005), and Hercher (2023) all use variants. Formalizing Baker's
theorem in Lean would require ~10000 lines of transcendence theory
(Feldman-Nesterenko-Shorey-Tijdeman framework).

**Effective constant.** The formalization uses the irrationality-measure
exponent `μ = 6`, strictly weaker than Rhin's bound
`μ(log_2 3) ≤ 5.125` ; the constant `C = 1` holds with ~50× safety
margin for `k ≥ 2`.

## 4.2 BarinaVerification (Barina 2025)

```lean
structure BarinaVerification where
  convergence : ∀ (n : ℕ), n > 0 → n < 2^71 → reaches_one n
```

**Source.** Barina, D. (2025), « Improved verification limit for the
convergence of the Collatz conjecture », *Journal of Supercomputing*
81:810. DOI: 10.1007/s11227-025-07337-0.

**Actual limit.** `2075 · 2^60 ≈ 2^71.02` ; the bound `n < 2^71` used
in the formalization is slightly conservative.

**Reproducibility.** Barina's code is open-source ; the computational
verification relies on modular sieving and is reproducible (though it
requires ~months of CPU time).

## 4.3 ProductBoundThreshold (project-derived, documented)

```lean
structure ProductBoundThreshold where
  cycle_length_bound : ∀ (n k : ℕ), IsOddCycle n k → k ≤ 982
```

**Origin.** This hypothesis is **not a direct result from any single
published paper** (see `ProjetCollatz/HYPOTHESES.md` in the
accompanying repository). It is a **cycle-complexity bound** whose
explicit threshold `k ≤ 982` derives from :

1. The Product Bound lemma (`ProjetCollatz/Phase56*.lean`, proved
   algebraically from Baker + Bernoulli) : `n ≤ (k⁷ + k) / 3`.
2. Barina's verification limit `2⁷¹`.
3. The arithmetic fact `(982⁷ + 982)/3 < 2⁷¹`, verified by
   `native_decide` in `k982_bound` (`Phase56Bloc18Complete.lean` line
   249).

**Status.** For hypothetical cycles, `k ≤ 982` is **vacuously true**
assuming the Collatz no-cycle conjecture. It is **stronger** than
Hercher's (2023) lower bound `K > 1.375 · 10¹¹`, but this apparent
contradiction is resolved because both claims are vacuous on the
(conjectured) empty set of non-trivial cycles.

**Why it remains a hypothesis.** Even though `ProductBoundThreshold`
is not a direct citation, it encapsulates the Product Bound + Barina
chain in a cycle-complexity framing that is natural to formalize and
explicit about what is assumed. The structural obstruction that
prevents promoting it from hypothesis to theorem — together with the
resulting gap in the unconditional argument — is the subject of §5
(Obstruction I).

