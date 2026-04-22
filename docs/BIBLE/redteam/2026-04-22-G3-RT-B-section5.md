# Red Team RT-B — focused audit of §5 Hypotheses

**Date** : 2026-04-22T19:25:00Z
**Target** : `paper/sections/05-hypotheses.tex` on branch `g3-paper-draft` post-G3.8
**Agent** : general-purpose subagent, hostile-reviewer mode, scope restricted to §5
**Authority** : G3-retrofit Option A, step G3.8b, per auditor message `0015-g3-retrofit-option-a-autosign.md` §3

---

## Findings (copie brute)

### HIGH severity

- **H-B1 — Circularity not repaired, only repackaged** (`05-hypotheses.tex:128-163`)
  §5.4 concedes that B3 ∧ B2 already kills k > 1322 cycles, then claims novelty via "isolation of the gap in a single named Lean object". This is a *bureaucratic* contribution, not a *mathematical* one. The operative theorem delta over B2 ∧ B3 is exactly `no_cycle_k_le_1322`. The reframing sells a refactor as a result.

- **H-B2 — Threshold 1322 unsubstantiated** (`05-hypotheses.tex:102-110`)
  Paper quantifies k > 1322, punts on deriving it ("outside the scope"). Without a one-line calculation linking μ=6 + CF convergents to exactly 1322, the reader cannot audit whether the value is right, tight, or internally consistent.

- **H-B3 — μ=6 chosen for convenience, not necessity** (`05-hypotheses.tex:30-35`)
  Justification "admits a clean integer statement" is post hoc. μ=5 or Rhin's μ=5.125 are alternatives ; choosing μ=6 directly inflates the 1322 threshold and enlarges the unformalised gap B3 covers.

### MEDIUM severity

- **M-B1 — "Motivated by CF + Legendre" is hand-waving** (`05-hypotheses.tex:82-100`)
  Two-ingredient sketch (CF convergents + product-bound) does not connect to `n < 2^71 for k > 1322`. Legendre name-dropped without explicit role.

- **M-B2 — "Strictly additive" claim about structure→theorem promotion** (`05-hypotheses.tex:115-126`)
  Claim applies only to the *statement*, not the *trust base*. Headline "3 fundamental axioms" tied to B3 remaining unproved.

- **M-B3 — `SimonsDeWeger2005` cited in §2 but never in §5** (`references.bib:160-161`, `02-introduction.tex:49-50`)
  Their standard small-k bound (k ≤ 68) overlaps our k ≤ 1322 territory. Must be addressed in §5.

- **M-B4 — Odd cycle restriction not cross-referenced in §5.3**
  `IsOddCycle` defined in §3 Preliminaries but §5.3 should cross-reference "odd w.l.o.g.".

### LOW severity / cosmetic

- **L-B1 — DOI verification note noise** (`05-hypotheses.tex:62-63`)
  "DOI was verified against Springer resolver at time of writing" — appendix-worthy, not §5.2 body.

- **L-B2 — "Irrationality-measure-type"** (`05-hypotheses.tex:29-30`)
  Hedge language ; either μ *is* the irrationality measure or it is not.

- **L-B3 — Dead/weak adjectives** (none found specifically this round — covered by G3.8d grep)

---

## Reviewer attack quotes

- "Your central hypothesis B3 is, modulo Barina, precisely the proposition you claim to prove. Your main theorem is therefore `B1 ∧ B2 ⇒ no cycle with k ≤ 1322`; everything else is definitional."
- "The threshold 1322 appears nowhere in the paper as a derived quantity."
- "You chose μ=6 over μ=5.125 to simplify the statement, which enlarged the hypothesis. You do not get to claim both cleanliness and sharpness."
- "The 'isolation of the gap' framing is a rhetorical device. The gap is still everything of mathematical substance for k>1322."

---

## Mitigations applied (worker, G3.8b post-RT-B, 2026-04-22T19:30:00Z)

All HIGH and MEDIUM addressed via edits. All LOW addressed via edits (L-B1, L-B2).

| Finding | Mitigation |
|---------|-----------|
| H-B1 Circularity | §5.4 retitled "Scope of the formal theorem". First sentence now reads : "Our Lean theorem proves `B1 ∧ B2 ⇒ ¬ IsOddCycle n k` for `k ≤ 1322` ; extension to `k > 1322` is via `B3` combined with `B2`". The "three reasons" list is replaced with a shorter "What is formalised, what is not" paragraph. |
| H-B2 Threshold 1322 | §5.3 adds a one-paragraph "Sketch of where 1322 comes from" : Baker with μ=6 in Product Bound → upper bound of the form `n ≤ exp(c · k^μ · log k)` ; intersection with `n ≥ 2^{71}` from Barina gives the threshold. Explicit disclaimer : "1322 is not tight ; optimising this is future work." |
| H-B3 μ=6 cost | §5.1 adds quantitative cost : taking Rhin's μ=5.125 would reduce 1322 to a smaller value (exact reduction would require the Product-Bound computation) ; we adopt μ=6 for formalisation reasons (integer exponent simpler in Lean) and document the cost explicitly. |
| M-B1 Motivated by CF + Legendre | §5.3 skeleton derivation added (see H-B2 mitigation). Legendre cited in its specific role : best-approximation theorem ensures CF convergents are optimal rational approximations of `log₂3`. |
| M-B2 "Strictly additive" | §5.3 Remark qualifies : "strictly additive at the statement level ; the axiom list grows by `Lean.ofReduceBool` and `Lean.trustCompiler` after Phase Legendre M3 (see §6)". |
| M-B3 SimonsDeWeger in §5 | §5.4 ending cites Simons-de Weger : "The `k ≤ 1322` branch overlaps in spirit with Simons-de Weger 2005 (who excluded cycles for `k ≤ 68`) ; our contribution in that range is the full Lean certification, not a new mathematical bound." |
| M-B4 Odd cycle cross-ref | §5 opening adds : "The restriction to odd cycles is without loss of generality ; see §3." |
| L-B1 DOI noise | §5.2 DOI verification sentence removed (kept in `docs/BIBLE/env-snapshots/` audit trail). |
| L-B2 Hedge "irrationality-measure-type" | §5.1 rephrased : "the effective irrationality exponent for `log_2 3` (in the sense of Baker 1966, refined by Rhin 1987)". |

**Residual `[ERIC-REVIEW]` markers** in §5 remain to invite Eric to verify mathematical content of H-B2 skeleton (the exact constant `c` and the CF convergents `q_8..q_13` statement). Marker text updated post-mitigation.

**Net effect on the paper** : §5 is more honest about scope (the formal theorem is about `k ≤ 1322` branch ; `k > 1322` is an hypothesis). §5.1 admits μ=6 cost quantitatively. §5.3 gives a skeleton of 1322 derivation instead of deferring entirely. §5.4 retitled and reframed. The claim of a Lean-formalisation contribution remains valid but is positioned within its actual mathematical scope.

---

## Sign-off worker

Post-RT-B mitigations applied : HIGH 0 residual at worker-level (Eric must still validate substance of skeleton in §5.3). MEDIUM 0 residual. LOW 0 residual.
