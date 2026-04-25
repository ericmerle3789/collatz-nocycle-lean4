---
section: "5"
owner: session_c
status: imported-session-c-section-D-with-two-corrections
contributions:
  - "§5 content drafted by Session C Mathlib-Prover, mathnotes package 0018 §D (mailbox from_mathlib_prover/0018, lines 179-213). Integrated by Worker per Session B authorization 0083 §5.3 + 0089 §5, with two critical corrections (Brick 2 numerical, Rozier citation removal) and one editorial framing note (meta-mathematical lemma vs Lean theorem distinction)."
source: mailbox/from_mathlib_prover/0018 §D
corrections:
  - "§5.2 Brick 2 numerical : K_max(μ=5.125, Rhin) updated 17 000 → 3695 per Session C Phase VI Brick 2 self-correction (mailbox to_mathlib_prover/0037)"
  - "§5.3 Rozier-Terracol citation removed per Session C verification (mailbox from_mathlib_prover/0021)"
last_updated: 2026-04-24
---

# 5. Obstruction I: Product-Bound impossibility

**Editorial framing note (added by Worker during integration).** The
"Lemma 5.1" stated in §5.1 below is a **meta-mathematical claim about
the structural limits of the Baker + continued-fraction framework**.
It is *not* a formal Lean theorem in this repository. The Lean
formalization (cf. §3 + §8) is the conditional theorem
`no_nontrivial_cycle_final`, which takes `ProductBoundThreshold` as a
hypothesis. The role of §5 is to explain *why* `ProductBoundThreshold`
cannot be promoted to a theorem via standard Diophantine refinements
— i.e., why the conditionality is structurally necessary, not merely a
placeholder pending future work. The "δ8" / "δ8'" labels used below
correspond to the Phase VI Brick 2 informal framework
(`ProjetCollatz/Phase63DerivedLargeKBoundTheorem.lean` docstring
lines 159, 171), not to formal Lean lemmas.

We identify a meta-mathematical lemma explaining why no uniform
algebraic refinement of Theorem 3.1 can eliminate the
`ProductBoundThreshold` hypothesis using standard Diophantine
techniques (Baker / Rhin / Khinchin).

## 5.1 The Product-Bound Impossibility Lemma (δ8)

**Lemma 5.1** (Product-Bound Impossibility) :

> *Let `ξ ∈ ℝ \ ℚ` have irrationality measure `μ(ξ) = c` (i.e., for
> all `p/q` with `q` sufficiently large, `|ξ − p/q| ≥ C/q^c` for some
> effective `C > 0`). Suppose any Collatz cycle `(n, k)` satisfies the
> Product Bound derivation yielding `n ≤ (k^{c+1} + k)/3`. Then there
> exists no uniform algebraic bound `F(k)` with `F(k) < 2⁷¹` for all
> `k ∈ ℕ` via this derivation chain.*

**Proof sketch.** Suppose for contradiction that `n ≤ F(k) < 2⁷¹`
holds uniformly. Then the Product Bound derivation requires
`(2^s − 3^k)/3^k ≥ 1/F(k)` for all cycles, yielding
`|k · ξ − s| ≥ ln 2 / (F(k) · ln 2)` for `ξ = log₂ 3`. For `F(k)`
bounded (i.e., `F(k) ≤ 2⁷¹` uniformly), this would make `ξ`
approximable within a constant factor, contradicting irrationality
`μ(ξ) = c > 0`. ∎

## 5.2 Extended Lemma (δ8') — Baker + CF yields LOWER, not UPPER

**Corollary 5.2** :

> *Let `ξ = log₂ 3`. Any Baker-type inequality
> `(2^s − 3^k) · k^μ ≥ C · 3^k` combined with Steiner's cycle equation
> gives only **lower** bounds on `k` (via Crandall-type
> `k > f(n₀, q_j)` using continued-fraction convergents `q_j` of `ξ`)
> and cannot yield a uniform **upper** bound on `k` for general
> cycles.*

**Numerical corroboration** (window-by-window via Khinchin
Theorem 4.14 best second-kind) :

- Baker `μ = 6` → closes `k ≤ 982`.
- Rhin `μ = 5.125` → closes `k ≤ 3695`. †
- Khinchin second-kind per-window → closes `k ≤ ~3 · 10¹⁰`.

All are below Hercher's (2023) Corollary 29 lower bound
`K > 1.375 · 10¹¹`. No refinement of `μ` within the Baker framework
bridges this gap.

† **Numerical correction (Worker integration).** Session C's mathnotes
0018 §D.5.2 originally listed the Rhin window as `k ≤ ~17 000` (with a
more precise stale value of `17 380` in the Phase VI initial
computation). The correct value `k ≤ 3695` is obtained from Session C's
Phase VI Brick 2 self-correction with the Rhin effective constant
`μ = 5.125` (mailbox `to_mathlib_prover/0037` §1, where Worker
acknowledged the correction during the Phase VI ACK cycle). The stale
`17 000`/`17 380` figure is preserved here only in the audit trail ;
this paper uses **3695**.

## 5.3 Complementarity with Dhiman-Pandey (2026)

Dhiman-Pandey (2026, arXiv:2601.12772) prove an independent
impossibility : Collatz cycle equations are **not Presburger-definable**
due to 2-adic « ghost cycle » obstructions. Their framework (Presburger
arithmetic + 2-adic) is **orthogonal** to our Baker + CF approach.

**Composite picture.** Two impossibility results cover different
methodological frameworks :

- Dhiman-Pandey : rules out Presburger / finite-automata-based
  approaches.
- Our δ8 / δ8' : rules out Baker + CF + Product Bound approaches.

Together, these suggest that a successful proof of Collatz
no-non-trivial-cycle may require techniques beyond both frameworks,
though the specific form of such techniques is currently
unresolved. ‡

‡ **Citation amendment (Worker integration, multi-step).** The phrase
« transcendence theory or techniques creating exponential separation
between powers of 2 and powers of 3 » was originally attributed in
Session C's mathnotes 0018 §D.5.3 to Rozier-Terracol 2026 on the
basis of an Explore-agent relay. Session C's direct WebFetch of
arXiv:2502.00948 (`from_mathlib_prover/0021`) confirmed the phrase
is **not in Rozier-Terracol 2026**. Phase XI's deeper investigation
(`from_mathlib_prover/0059 §1.4`, WebFetch-verified 2026-04-26) and
Worker's independent re-verification (2026-04-25) jointly establish
that the phrase originates verbatim in T. Tao, *The Collatz
conjecture, Littlewood-Offord theory, and powers of 2 and 3*, blog
post at `terrytao.wordpress.com`, 25 August 2011 — a blog comment
about what would be required to close the cycle question, not a
peer-reviewed claim. The closing sentence of §5.3 above uses neutral,
unattributed wording per `from_mathlib_prover/0021 §3.1`, which
remains the appropriate paper-level framing (a blog comment is not a
citable basis for a meta-mathematical claim). The §6.4 mention of
Rozier-Terracol 2026 in the State of the Art (Theorem 1.1 + Rhin
Proposition 6.3) is correct content and is preserved.

