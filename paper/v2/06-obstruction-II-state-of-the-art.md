---
section: "6"
owner: session_c
status: imported-session-c-section-E-with-two-critical-readings
contributions:
  - "§6 content drafted by Session C Mathlib-Prover, mathnotes package 0018 §E (mailbox from_mathlib_prover/0018, lines 217-263). Integrated by Worker per Session B authorization 0083 §5.3 + 0091 §5, with two substantive critical-reading additions disclosed in-band : (1) Knight 2025 [INDIRECT] source flag (footnote †) per Session C verification mailbox from_mathlib_prover/0020 (HAL/ScienceDirect access blocked, verdict based on search snippets + Explore agent + cross-referenced Christoffel-word combinatorics) ; (2) Santana 2026 critical-reading paragraph (footnote ‡) disclosing the 3 structural gaps identified by Session C in mailbox from_mathlib_prover/0019 (boundedness assumption non-justified, finiteness ≠ uniqueness, author self-disclaim Remark 17). The §6.4 Rozier-Terracol mention preserved as legitimate citation (Theorem 1.1 + Rhin Proposition 6.3), distinct from §5.3's fabrication removal."
source: mailbox/from_mathlib_prover/0018 §E
critical_readings:
  - "Knight 2025 [INDIRECT] flag per from_mathlib_prover/0020 §3"
  - "Santana 2026 3 structural gaps per from_mathlib_prover/0019 §2"
last_updated: 2026-04-24
---

# 6. Obstruction II: state of the art (δ9)

We document the state of the art on Collatz cycle non-existence as of
2026, identifying a structural gap (« δ9 ») : no published peer-
reviewed result provides a deterministic upper bound on `k` (the
number of odd steps) for general Collatz cycles. Our
`ProductBoundThreshold` hypothesis (§4.3) is therefore a project-
specific encoding rather than a citation, and §5's δ8 / δ8'
impossibility lemmas explain why this gap is structural rather than
incidental.

## 6.1 Historical lower bounds on k for hypothetical cycles

| Author | Year | Method | Bound |
|--------|------|--------|-------|
| Crandall | 1978 | CF + n₀ bound | `k > (3/2) · min(q_j, 2n₀/(q_j + q_{j+1}))` |
| Steiner | 1977 | Baker effective + CF | Circuits → only trivial cycle |
| Yoneda | ~1985 | Computational `n₀ > 2⁴⁰` | `k > 275 000` |
| Simons-de Weger | 2005 | LFL + CF iterations | `m > 68` minima |
| Applegate-Lagarias | 1995 | Density bounds | `γ > 0.81` (density) |
| Hercher-Puchert | 2018 | Refined CF iteration | `k > 7.2 · 10¹⁰` |
| Barina | 2025 | Computational `X₀ = 704 · 2⁶⁰` | Provides bound for above |
| **Hercher** | **2023** | **Iterative refinement (post-SdW)** | ***K > 1.375 · 10¹¹*** (SOTA) |

These are all *lower* bounds on `k` : they assume hypothetical cycles
exist and place arithmetic constraints on their parameters. None
bounds `k` from above.

## 6.2 Structural class eliminations (restricted classes of cycles)

- **Steiner** (1977) : circuits (cycles with one positive-to-maximum
  segment + one maximum-to-minimum descent) → only trivial cycle.
- **Knight** (2025, *Discrete Mathematics* 349(3)) : « high cycles »
  whose parity vector is the upper Christoffel word → do not exist. †

Neither extends to general m-cycles with `m ≥ 2`. Iterating
restricted-class eliminations to cover all parity patterns faces
combinatorial explosion.

† **Indirect-source flag (Worker integration).** The Knight 2025
paper was not directly accessible to Session C during verification
(HAL hal-04261183 returned an Anubis security block ; the
ScienceDirect article was paywalled). The formulation above
(« high cycles whose parity vector is the upper Christoffel word »)
is the project-validated `[INDIRECT]` framing per mailbox
`from_mathlib_prover/0020 §3` : verdict based on Google Scholar
search snippets + ScienceDirect abstract + Hacker News discussion
thread + cross-referenced memory of Christoffel-word combinatorics.
The result is sound (analogous to Steiner's restricted-class
elimination), but readers seeking the precise theorem statement
should consult the published paper directly. This `[INDIRECT]`
disclosure follows the same protocol as the Phase IX
`[SOURCE-INACCESSIBLE-MEMORY-BASED]` flag (mailbox 0044 §0).

## 6.3 Meta-impossibility results

- **Our δ8 + δ8'** (this paper §5) : Baker + CF approaches yield
  *lower* bounds on `k`, never uniform upper bounds.
- **Dhiman-Pandey** (2026, arXiv:2601.12772) : Presburger / 2-adic
  approaches are impossible (orthogonal framework, see §5.3).

## 6.4 Recent reformulation attempts (insufficient alone)

- **Santana** (2026, arXiv:2601.03297v4) : topological / ergodic
  reformulation. Proves conditional finiteness (Theorem B) under a
  boundedness hypothesis on continuous integrable potentials that is
  not justified in the proof. Does **not** prove uniqueness (Lemma 16
  is a reformulation, not a proof ; Remark 17 explicitly disclaims
  this : « In Lemma 16 we address an alternative approach of the
  conjecture, rather than a proof of it. »). No quantitative bounds
  on `n₀` or `k`. The framework is *complementary* to our Baker + CF
  approach but cannot substitute for the `ProductBoundThreshold`
  hypothesis. ‡
- **Honarvar** (2026, arXiv:2601.04289) : near-conjugacy to circle
  rotation. The author explicitly states « any resolution of the
  Collatz conjecture would require additional arithmetic arguments ».
- **Rozier-Terracol** (2026, arXiv:2502.00948) : paradoxical
  sequences approach (Theorem 1.1), uses Rhin Proposition 6.3
  heuristically. The framework is independent of our Baker + CF
  approach. (Cf. §5.3 footnote ‡ for an unrelated citation-integrity
  disclosure that does *not* affect the legitimate Theorem 1.1 + Rhin
  citation here.)

‡ **Critical-reading note (Worker integration).** Three structural
gaps in Santana 2026 are documented per Session C's direct WebFetch
verification of arXiv:2601.03297v4 (mailbox
`from_mathlib_prover/0019 §2`) :

> (i) **Boundedness assumption non-justified.** The Theorem B proof
>   constructs a convex combination `μ = Σ aᵢ · δᵢ` of ergodic
>   measures and claims `∫φ dμ < ∞` for any continuous integrable
>   potential φ. The proof assumes without justification that the
>   sequence `{∫φ dδᵢ}` is bounded as `i → ∞` ; no demonstration
>   that the integral remains finite is provided.
> (ii) **Finiteness ≠ uniqueness.** Lemma 14 (finiteness via
>   *unbounded* integrable potentials, e.g. `φ(n) = #𝒪(n) · Σ_{i ∈
>   𝒪(n)} i`) and Lemma 16 (uniqueness via *bounded* continuous
>   potentials) are not equivalent. The topology 𝒯 used by Santana
>   is strictly coarser than the discrete topology and does not give
>   uniqueness from finiteness without an Alexandroff compactification.
> (iii) **Author self-disclaim (Remark 17).** Verbatim : « In
>   Lemma 16 we address an alternative approach of the conjecture,
>   rather than a proof of it. » This is the author's explicit
>   disclaimer that Lemma 16 does *not* constitute a proof.

The « complementary, not closing » framing in the bullet above
incorporates all three observations. See Session C 0019 §2 for the
Lemma / Remark quotes verbatim.

## 6.5 Probabilistic / density results (not deterministic)

- **Terras** (1976) : almost all integers have finite stopping time.
- **Tao** (2019/2020) : almost all Collatz orbits attain almost
  bounded values (cf. Tao, *Almost all orbits of the Collatz map
  attain almost bounded values*, *Forum of Mathematics, Pi* 8, e5).

These are probabilistic / density-theoretic results : they do not
provide deterministic statements about every cycle. See §9.6 for
Tao's explicit framing of the cycle problem as still open.

## 6.6 Gap identified (δ9)

To the best of our literature review (17 peer-reviewed papers
consulted + 5 recent preprints, as of April 2026) :

> **No peer-reviewed result provides a deterministic upper bound on
> `k` (the number of odd steps) for general Collatz cycles.**

The `ProductBoundThreshold` hypothesis of §4.3 is therefore a
**project-specific encoding** of the Product Bound + Barina chain,
rather than a direct citation of any published theorem. This
transparency is maintained throughout our paper to avoid
misattribution to peer-reviewed results. See §5 for the structural
reason (δ8 / δ8') why this gap is unlikely to close via standard
Diophantine refinements.

