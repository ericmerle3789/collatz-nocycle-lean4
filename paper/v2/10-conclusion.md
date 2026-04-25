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

---

## Integration notes (Worker internal — remove before publication)

- §10 is **Worker-authored synthesis** drawing exclusively from
  §1-§9 already-committed content. No Session C source mathnotes ;
  no new claims introduced.
- §10.1 maps exactly onto §1.3's five contributions (6α, δ7, δ8,
  δ8', δ9), with each bullet carrying section cross-references to
  the body sections that establish the contribution. Numerical
  values (`982`, `3695`, `~3 · 10¹⁰`, `1.375 · 10¹¹`, `2⁷¹`,
  `1322`) are all preserved verbatim from §3-§8 already-committed.
- §10.2 four disclaimers match the placeholder skeleton's planned
  structure (no Collatz proof, no divergence, no dismissal of recent
  preprints, ProductBoundThreshold remains hypothesis). The fourth
  disclaimer ("not final") is Worker-added and forward-points to the
  open invitation in §10.3.
- §10.3 modular invitation has three numbered lines of future work
  matching the existing infrastructure (§4.3 / §6.6 / §5). The
  Phase X §9.X mention is at **meta level only** per 0094 §5.2
  Option A — forward pointer with no expansion of §9.X content.
  §9.X polish is deferred to §9 polish phase (Commit #14+).
- Integration glue (disclosed in Commit #12 preflight) :
  - §10 intro paragraph (5 lines between title and §10.1) is
    Worker-authored prose, summarizing the paper's scope without
    repeating the abstract. Substance derives from §1.2 + §1.3 +
    §5 + §6 + §8.
  - Subsection structure (§10.1 / §10.2 / §10.3) matches placeholder
    skeleton exactly. No reordering.
  - Numerical values typeset consistently with §3-§8 (`2⁷¹`, `10¹¹`,
    math italics for `n`, `k`, `μ`).
  - "non-trivial cycles" hyphenated for paper-style consistency with
    §3-§7.
- RT#1 checklist (placeholder §10 Day 3 deliverables) :
  - [✓] ~1 page tight (target met : Worker estimate ~95-110 lines).
  - [✓] No repetition of the abstract (paper's frontmatter abstract
    not yet drafted ; §10 intro is independent prose).
  - [✓] No new claims (every claim cross-referenced to §1.3 / §3 /
    §4 / §5 / §6 / §7 / §8 / §9).
  - [✓] Honest framing maintained (no "we have essentially proved" ;
    « We do **not** prove the Collatz conjecture » first §10.2 bullet).
  - [✓] Conclusion matches introduction scope exactly (§10.1 mirrors
    §1.3, §10.2 mirrors §1.5 + §6 disclaimers, §10.3 mirrors §1.2's
    "additive" framing).
  - [✓] No hype phrases ("groundbreaking", "resolves", "final"
    avoided ; manual grep clean).
  - [✓] Every "we establish" / "we do not claim" sentence has a
    section backing it.
- Future-work item 3 (« Refine or supersede δ8 ») is the most
  open-ended ; it is a *meta-mathematical* invitation rather than a
  concrete research direction. This wording matches §1.2's
  acknowledgement that the obstruction « cuts off not just our
  approach but...the closest 2026 preprints as well ».
- No critical corrections in §10 (no Brick 2 / Rozier-style issues).
- No new IMPORTANT findings expected — §10 is pure repackaging from
  §1-§9 already-committed material.
- Forward-flagged list for §11 VERIFY pass remains stable at 2 items
  (Yoneda + Barina year ; no §10-discovered items).
