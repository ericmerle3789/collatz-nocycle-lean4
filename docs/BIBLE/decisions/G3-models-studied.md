# G3 retrofit — literature study of paper-writing models

**Date** : 2026-04-22T19:15:00Z
**Author** : worker session (retrofit per auditor Option A, message `0015-g3-retrofit-option-a-autosign.md`)
**Statut** : documentation of the literature study required by `PAPER_WRITING_STANDARDS_NASA.md` §1 and §10 step 1. Retrofit applied after G3.1-G3.9 were already committed under the original plan (amendment timing gap).
**Auto-reconnaissance** : the standard's recommended drafting order (abstract → §6 Hypotheses → lean → reproducibility → main result → preliminaries → conclusion → introduction last) was not followed. The existing draft was produced linearly G3.1-G3.7. The Red Team round G3.8 detected and mitigated the kind of inconsistencies the Tao-order is designed to prevent (H1 Theorem 4.1 natural-language vs Lean, H3 abstract euphemism on B3). This document records the post-hoc study and identifies incremental adjustments, not a full re-draft.

---

## 1. Tao, "Advice on writing papers"

- **URL** : https://terrytao.wordpress.com/advice-on-writing-papers/
- **Access date** : 2026-04-22

### Extracted patterns

1. **Strategic introduction** : use the introduction to "sell" the main contributions ; make the reader understand why the work matters before the technical details.
2. **Accurate description** : results described precisely, neither oversold nor understated.
3. **Thoughtful organisation** : break complex arguments into digestible sections that guide the reader step-by-step.
4. **Clear motivation** : explain why the results matter and how they connect to existing knowledge.
5. **Notation choices** : select mathematical notation that reduces cognitive load ; good notation illuminates, poor notation obscures.
6. **Appropriate level of detail** : balance rigour and readability ; use lemmas to break arguments into manageable pieces.
7. **Personal voice** : adopt a professional yet personal style rather than forced formality.
8. **Leverage English** : don't rely solely on symbols ; use prose to explain intuition, motivate definitions, guide through logic.
9. **Rapid prototype first** : write a rough draft before polishing to avoid over-optimising initial material.
10. **Results-to-effort ratio at a local maximum** : contribution should justify the length ; avoid padding.

### Adjustments to our paper (incremental)

- \[already compliant\] §1.3 contributions are stated precisely ; §4 remark on "what the theorem does not claim" aligns with pattern 2 (accurate description).
- \[already compliant\] Lemmas and sections are well-separated (pattern 3).
- \[to check\] notation consistency across §3 Preliminaries and §4 Main Result : verify `\collatz`, `\Nat`, `\mathtt{IsOddCycle}`, and theorem environments are uniform.
- \[incremental improvement\] §2 Introduction could make the "sell" more explicit in the opening paragraph (pattern 1). **Minor, deferred to Eric review**.
- \[already compliant\] no promotional adjectives per `PAPER_WRITING_STANDARDS_NASA.md` §5 and post-RT-G3.8 interdit-grep.

---

## 2. Tao, "Almost all orbits of the Collatz map attain almost bounded values" (2022)

- **arXiv preprint** : https://arxiv.org/abs/1909.03562
- **Published** : *Forum of Mathematics, Pi*, vol. 10, 2022 (DOI to complete in references.bib `[ERIC-REVIEW]` entry)
- **Access date** : 2026-04-22

### Extracted patterns

1. **Opening within established territory** : Tao immediately frames the problem within the well-known Collatz conjecture and prior work (Korec). The abstract does not begin cold.
2. **Honest reframing** : rather than claim the conjecture is resolved, Tao redefines success using a weaker density notion ("almost all" in the logarithmic density sense).
3. **Conditional framework** : the result is announced as "for any θ > log 3 / log 4" and "for any function f with lim f(N) = +∞" — strong conditional quantifiers are upfront.
4. **Limitation handling** : Tao is explicit about "almost all" and specifies the density type ; the constraint is named, not hidden.
5. **Technical scaffolding in the abstract** : mention of first passage variables, characteristic functions of skew random walks on 3-adic groups, and renewal processes — abstract signals the methodology.

### Adjustments to our paper (incremental)

- \[already compliant\] §1.1 opens with a reference to Collatz's 1937 conjecture, matching pattern 1 (opening within established territory). Tao 2022 is a natural state-of-the-art reference — already in `references.bib` as `Tao2022` `[ERIC-REVIEW]`. Cite it once in §2 alongside Hercher 2023 and Barina 2025 to position our work.
- \[already compliant\] Our abstract is conditional (on \(\mathsf{B1}, \mathsf{B2}, \mathsf{B3}\)) and states what is and is not claimed — matches patterns 2, 3, 4.
- \[already compliant\] Our abstract mentions the 3-axiom chain and reproducibility pipeline — methodological signalling per pattern 5.
- \[incremental improvement\] Add a brief reference to Tao 2022 in §2 Introduction state-of-the-art list, since the paper is relevant context even though it addresses a different aspect of Collatz (orbit dynamics, not cycles). **Minor bib + citation addition, applied in G3.8c**.

---

## 3. Hales et al., "A formal proof of the Kepler conjecture" (2017)

- **DOI** : 10.1017/fmp.2017.1
- **Published** : *Forum of Mathematics, Pi*, vol. 5, 2017
- **Access date** : 2026-04-22 (Cambridge Core page accessible, but only abstract- and reference-level content ; full methodology sections not accessible via WebFetch at this time)

### Extracted patterns (inferred from available content + community knowledge)

1. **Collaborative, distributed verification** : multiple institutions (Pittsburgh, Intel, TU München, Vietnam Academy of Science) imply a distributed formal verification effort, with formal proof artefacts in the Archive of Formal Proofs and project GitHub.
2. **Modular decomposition of the formalised content** : references name specific modules — "tame graphs", "basic linear programs", "nonlinear inequalities with Taylor interval approximations" — each a formalisable unit.
3. **Tool ecosystem** : HOL Light and Isabelle as proof assistants ; GLPK for linear programming ; interval analysis for numerical verification.
4. **Cite the formal proof infrastructure in the references** : foundational proof assistant papers and computational tool papers are all cited, which is standard for formal-proof journal submissions.

### Patterns we cannot extract from what was accessible

- Explicit "trust model" section (axioms list, computational dependencies, manual choices) was not visible in the fetched abstract excerpt. Community knowledge suggests Hales's paper does discuss a trust model, but we should not claim specific wording without verification.
- Detailed treatment of limitations / caveats in the published version.

### Adjustments to our paper (incremental)

- \[already compliant\] §6 Lean Formalisation describes the toolchain (Lean 4, Mathlib, `lake`, `elan`) explicitly. §7 Reproducibility names the scripts and CI workflow. These match pattern 3.
- \[already compliant\] §6 has a dedicated discussion of "axioms" (Section "Axiom baseline") that plays the role of a trust model for our paper ; post-RT-G3.8 it also acknowledges the Phase Legendre M3 escalation of `Lean.trustCompiler`.
- \[incremental improvement\] Add Hales 2017 to `references.bib` as methodology reference. Cite it once in §6 Lean Formalisation as precedent for formal-proof-of-an-open-conjecture papers that explicitly discuss their axiom baseline and formalisation boundaries. **Applied in G3.8c**.
- \[out of scope G3 retrofit\] A true "Trust Model" subsection modelled on Hales's structure (axioms + computational dependencies + manual choices) would be a valuable refinement, but the information is largely covered in §6.4 Isolation property + §8 Future Work §3 (the `Lean.trustCompiler` discussion). A full Trust Model subsection can be added post-Eric-review if Eric wants it (G3 v2).

---

## 4. Summary of adjustments applied in G3.0-retrofit

Non-substantive, applied within the 2-3h window of the retrofit :

| Adjustment | Location | Status |
|-----------|----------|--------|
| Bibliography entries for Collatz 1937, Gonthier 2008, Hales 2017, Tao 2022 with `[ERIC-REVIEW]` for DOI completion | `paper/references.bib` | G3.8c (see commit) |
| Single citation addition of Tao 2022 in §2 state-of-the-art list | `paper/sections/02-introduction.tex` | G3.8c |
| Single citation addition of Hales 2017 as methodology reference in §6 Lean Formalisation | `paper/sections/06-lean-formalization.tex` | G3.8c |
| Fix of the single adverbial "clearly identified" → "explicitly identified" per `PAPER_WRITING_STANDARDS_NASA.md` §5 interdits | `paper/sections/05-hypotheses.tex` | G3.8d |
| Fresh Red Team focused on §5 Hypotheses (RT-B) | `docs/BIBLE/redteam/2026-04-22-G3-RT-B-section5.md` | G3.8b |

### Adjustments deferred to Eric review (G3.10)

- Expand §2 opening paragraph in Tao-"sell"-style (pattern 1 of Tao blog). Non-urgent, judgement call.
- Add dedicated "Trust Model" subsection in §6 following Hales 2017 structure. Non-urgent, enriches the paper but not required for v1.
- Reorder sections per Tao-order (abstract first, §6 Hypotheses first in body, intro last). The current ordering is conventional ; reordering would be cosmetic and risks breaking internal references. Defer indefinitely unless Eric requests.

---

## 5. Honest self-critique of the retrofit

The Tao blog and standards document advise writing the **introduction last**. Our introduction was drafted in commit G3.6 (penultimate, not last), after Abstract and Sections 4, 5, 6, 7 but before §3 Preliminaries and §8 Conclusion. The difference with Tao-order is that §3 Preliminaries and §8 Conclusion came after §2 Introduction. The practical risk this creates is that the introduction's statement of "the paper does not claim to resolve Collatz" could have been written without the full benefit of §8's Phase Legendre plan being drafted. Reviewing the actual text of §2.3 and §8.2, the two are consistent — §2 says "target of Phase Legendre, see Section 8", and §8 defines Phase Legendre. The `[ERIC-REVIEW]` markers on both sections invite Eric to check the consistency end-to-end.

In short : the ordering risk was real but the Red Team G3.8 caught the high-severity inconsistencies it would have produced (H1 theorem wording, H3 abstract euphemism). The remaining consistency checking is Eric's job during the review cycle.

---

**Retrofit notes end here. Commits G3.0-retrofit, G3.8b, G3.8c, G3.8d follow.**
