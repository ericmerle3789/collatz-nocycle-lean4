---
section: "1"
owner: worker
status: draft-day1
last_updated: 2026-04-24
---

# 1. Introduction

## 1.1 The Collatz conjecture and the cycle problem

For each positive integer `n`, the Collatz map `T : ℕ → ℕ` is defined by
`T(n) = n/2` if `n` is even and `T(n) = (3n+1)/2` if `n` is odd. The Collatz
conjecture asserts that, for every starting value, iterating `T` eventually
reaches `1`. Equivalently, it makes two negative claims : (i) no trajectory
diverges to infinity, and (ii) no non-trivial periodic orbit exists — where
*non-trivial* means distinct from the fixed orbit `1 → 1`. The present paper
addresses (ii) only; the divergence half of the conjecture is outside our
scope.

We find it convenient to work with the *odd iterate* `T_odd`, which
compresses runs of halvings and advances the index by one only on a
`3n+1` step. A pair `(n, k)` with `n` odd, `k ≥ 1` and `T_odd^k(n) = n`
is called an **odd Collatz cycle** of length `k`. The trivial cycle
`(1, 2)` gives the trivial period `1 → 1`. Our central question is whether
any pair `(n, k)` with `n > 1` is an odd Collatz cycle.

## 1.2 Why v2, and why now

An earlier draft of this work (tagged `paper-v1-draft` in the accompanying
Lean 4 repository) closed the cycle problem conditionally on two published
hypotheses : Baker's 1966 theorem on linear forms in logarithms of algebraic
numbers, and Barina's 2025 computational verification that every integer
below `2^71` ultimately reaches `1`. In early 2026 we set out to remove the
second of these, or at least to reduce the verification range substantially,
by promoting an intermediate structural hypothesis of our formalization
to a Lean theorem. A deliberately exhaustive exploration of the available
methodology, across eleven research sub-branches, returned a single
structural verdict : every product-bound approach known to the literature
is limited to cycle length at most of order `10^10`, and any successful
bridge from Baker's theorem through the continued-fraction theory of
`log_2 3` to the cycle-length bound we require would have to surmount an
obstruction we formulate here as the **Product-Bound Impossibility Lemma**
(§5, Lemma 5.1).

The obstruction is not a gap in our own effort alone ; it is a consequence
of the irrationality measure of `log_2 3` and is shared by every argument
in the same family. It is also non-trivially honest to document : the
obstruction cuts off not just our approach but, as we detail in §6, the
closest 2026 preprints as well. Paper v2 therefore (a) states the
conditional theorem cleanly, (b) records the three structural hypotheses
that it rests on, and (c) explains the obstruction and the state of the
art that make the third hypothesis necessary. The third hypothesis is named
**ProductBoundThreshold** and is made explicit in §4.3.

## 1.3 Contributions

The paper contains five originals, each with a rigorous statement later in
the text :

- **δ7 (alternative framing, §7).** A logically equivalent restatement of
  the central theorem as a disjunction over a finite list of
  continued-fraction windows of `log_2 3`. The framing is illuminating for
  connecting our conditional bound to Hercher's (2023) lower-bound
  methodology, without claiming it closes the cycle problem.

- **δ8 (Product-Bound Impossibility Lemma, §5.1).** A meta-mathematical
  lemma : any argument that bounds a hypothetical cycle minimum `m` by a
  polynomial-over-cycle-length `F(k)` with `F(k) < 2^{71}` uniformly in `k`
  forces `log_2 3` to be rationally approximable within a constant factor,
  contradicting its irrationality. The lemma explains why no refinement of
  Baker's effective exponent within the standard framework can discharge
  our third hypothesis.

- **δ8' (extended impossibility, §5.2).** A corollary of δ8 extending the
  obstruction to the family of bound schemes obtained by composing
  Baker-type inequalities with Steiner's cycle equation and the
  continued-fraction convergents `p_j / q_j` of `log_2 3`. Numerical
  corroboration is given window by window, connecting with Khinchin's
  best-second-kind characterization of convergents.

- **δ9 (state-of-the-art mapping, §6).** A typology of the 1977-2026
  Collatz cycle literature distinguishing lower bounds on cycle length,
  structural-class eliminations (Steiner 1977 circuits ; Knight 2025
  high cycles), probabilistic density results (Terras 1976 ; Tao 2019),
  and recent reformulation attempts (Santana 2026 ; Dhiman-Pandey 2026 ;
  Rozier-Terracol 2026). The typology makes explicit, to the best of our
  literature review, that no published result supplies the deterministic
  upper bound on cycle length that our third hypothesis encodes.

- **6α (formal verification, §8).** The central theorem and its immediate
  dependencies are formalized in Lean 4 under Mathlib v4.27.0, with zero
  user-declared axioms, zero `sorry`, and an axiom profile whose central
  chain consists of the three Mathlib kernel axioms (`propext`,
  `Classical.choice`, `Quot.sound`). Arithmetic gap constants used
  auxiliarily are isolated from the central chain through a structural
  parameter, so that the two Lean compiler axioms required by
  `native_decide` remain outside it at the present formalization state.

## 1.4 Relation to the 2026 literature

Four recent contributions deserve explicit situation with respect to our
conditional theorem.

- **Santana (2026, arXiv:2601.03297v4)** proposes a topological and ergodic
  reformulation of the cycle problem. We directly consulted the full
  preprint. The argument for Theorem B (finiteness) relies on an
  un-justified boundedness assumption for a sequence of integrals over
  atomic invariant measures, and Lemma 16, which would extend finiteness
  to uniqueness, is labelled by the author (Remark 17) as "an alternative
  approach [...] rather than a proof". The framework therefore does not
  discharge our third hypothesis, although it is complementary (§6.4).

- **Knight (2025, *Discrete Math.* 349(3))** proves that no Collatz cycle
  whose parity vector coincides with an upper Christoffel word exists. This
  is a restricted-class elimination in the tradition of Steiner's (1977)
  circuits result ; it does not extend, without substantial further work,
  to general parity patterns (§6.2). Access to the full text was blocked
  at the time of writing ; we therefore rely on the abstract-level
  formulation validated by our upstream survey and flag the claim as such.

- **Dhiman-Pandey (2026, arXiv:2601.12772)** prove, by a 2-adic
  "ghost-cycle" construction, that cycle equations cannot be characterized
  in Presburger arithmetic. This is methodologically orthogonal to our
  Baker-plus-continued-fractions approach : the two results rule out
  different proof families (§5.3).

- **Rozier-Terracol (2026, arXiv:2502.00948, to appear *Discrete Math.*)**
  enumerate so-called *paradoxical sequences* and use Rhin's effective
  irrationality bound heuristically. Their finiteness statement for
  paradoxical sequences is independent of our third hypothesis (§6.4).

## 1.5 Paper organisation

Section 2 fixes notation and restates the three hypothesis-structures as
they appear in the Lean 4 formalization. Section 3 gives the central
conditional theorem. Section 4 discusses the mathematical origin and the
published support of each of the three hypotheses. Section 5 proves the
Product-Bound Impossibility Lemma (δ8) and its extension (δ8'). Section 6
presents the literature mapping (δ9). Section 7 gives the disjunction
framing (δ7). Section 8 describes the Lean 4 formalization (6α), including
its axiom profile and its reproducibility contract. Section 9 lists open
problems and connects with ongoing speculative tracks not integrated here.
Section 10 concludes. Section 11 is the reference list.

