---
section: "10"
owner: worker
status: drafted
last_updated: 2026-04-25
---

# 10. Conclusion

This paper presents a machine-checked conditional non-existence result
for non-trivial Collatz cycles, three named hypotheses on which it
rests, two impossibility lemmas explaining why the third hypothesis
cannot be discharged within the standard Diophantine framework, and a
literature mapping documenting the structural gap that makes the
conditionality necessary. The Lean 4 formalization is reproducible
under Mathlib v4.27.0 with an isolated and documented axiom profile.

## 10.1 What this paper establishes

The five contributions of §1.3 are realized as follows :

- **6α (formal verification, §3 + §8).** The conditional theorem
  `no_nontrivial_cycle_final` (`ProjetCollatz/Phase58PorteDeuxFinal.lean`
  line 339) is declared parametrically with the three structures of §4
  and is machine-verified. Its kernel-3 axiom profile
  (`propext`, `Classical.choice`, `Quot.sound`) is exhibited verbatim
  in §3.3 and §8.6, and reproducibility is encoded in `reproduce.sh`
  against the `expected_axioms.md` baseline (§8.7).

- **δ7 (alternative framing, §7).** Theorem 7.1 restates the central
  result equivalently as the disjunction « `k ≤ 982` or `n > 2⁷¹` »
  (§7.1), establishing a one-sentence bridge from the conditional
  theorem to Hercher's (2023) lower-bound `K > 1.375 · 10¹¹` (§7.2).
  A finer-grained continued-fraction refinement at the cycle-length
  scale `k > 1322` is documented as a Phase63 Lean skeleton (§8) ;
  its non-completion meets the obstruction of §5.

- **δ8 (Product-Bound Impossibility Lemma, §5.1).** Lemma 5.1
  formalizes a meta-mathematical obstruction : every uniform algebraic
  bound `F(k)` with `F(k) < 2⁷¹` derived through the Product Bound
  derivation forces an irrationality-measure constraint on `log_2 3`
  that contradicts irrationality. The lemma is a publication-only
  argument about the structural limits of the Baker + continued-
  fraction framework, not a Lean theorem.

- **δ8' (extended impossibility, §5.2).** Corollary 5.2 extends δ8 to
  Baker-type inequalities composed with Steiner's cycle equation.
  Window-by-window numerical corroboration via Khinchin's best-
  second-kind characterization closes `k ≤ 982` (Baker `μ = 6`),
  `k ≤ 3695` (Rhin `μ = 5.125`), and `k ≤ ~3 · 10¹⁰` (Khinchin
  per-window) — all below Hercher's lower bound `K > 1.375 · 10¹¹`.

- **δ9 (state-of-the-art mapping, §6).** Section 6 catalogues the
  1977-2026 Collatz cycle literature in five categories :
  historical lower bounds (§6.1), structural-class eliminations
  (§6.2), meta-impossibilities (§6.3), recent reformulation attempts
  (§6.4), and probabilistic / density results (§6.5). The mapping
  documents, to the best of our literature review, the absence of any
  peer-reviewed deterministic upper bound on cycle length `k` for
  general Collatz cycles (§6.6).

## 10.2 What this paper does not claim

- We do **not** prove the Collatz conjecture. The third hypothesis,
  `ProductBoundThreshold` (§4.3), remains a hypothesis ; the paper
  is *about* why it cannot be discharged within the standard framework.

- We do **not** address the divergence half of the Collatz conjecture
  (§1.1). The cycle problem and the divergence problem are
  disjoint ; this paper concerns only the former.

- We do **not** dismiss or subsume Santana (2026), Knight (2025),
  Dhiman-Pandey (2026), or Rozier-Terracol (2026). Each is situated
  in §6.4 as either complementary (different methodological framework)
  or restricted-class (does not extend to general cycles), with the
  documented gaps and indirect-source flags clearly attributed.

- We do **not** claim that the obstruction of §5 is final. The
  obstruction is structural under the *Baker + CF + Product Bound*
  paradigm ; methodological frameworks outside that paradigm — for
  instance a deterministic upper bound on cycle length derived from
  ergodic, density-theoretic, or yet-uncatalogued techniques — would
  immediately discharge `ProductBoundThreshold` and upgrade Theorem
  3.1 from conditional to unconditional.

## 10.3 Modular invitation for future work

The paper's structure is deliberately additive : conditional theorem
+ documented obstructions + machine-verifiable formalization. A
future contribution that resolves any of the three following lines
of work would, without further editorial intervention, upgrade the
conditional theorem :

1. **Discharge `ProductBoundThreshold`** (§4.3). Any deterministic
   proof that hypothetical cycles satisfy `k ≤ K` for some explicit
   `K` (whether `K = 982` or larger) would replace the structure
   field with a Lean theorem.

2. **Close the δ9 gap** (§6.6). A peer-reviewed deterministic upper
   bound on `k` for general cycles, by any methodological framework,
   would supersede the project-specific encoding.

3. **Refine or supersede δ8** (§5). A novel argument framework not
   bound by the Baker + CF + Product Bound family of inequalities
   could in principle bypass the obstruction, with corresponding
   refinement of the conditional theorem.

Speculative tracks documented in §9 (open problems) — including the
Phase VIII Ψ_s structural-excess framework (§9.7) and the Phase X
upper-bound complement attempt (§9.X) — are presented as ongoing
work not integrated into the central conditional theorem of §3 ; we
list them for transparency and as invitations rather than as
results.

The Lean 4 formalization is intended as a stable substrate for such
future work : the conditional theorem, the three hypothesis
structures, and the axiom profile are all parametric, so additive
contributions need not re-formalize the existing argument.

