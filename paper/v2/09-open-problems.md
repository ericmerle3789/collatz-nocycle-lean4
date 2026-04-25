---
section: "9"
owner: worker
status: drafted-with-section-9-x-expansion
contributions:
  - "§9.6 paragraph drafted by Session C Mathlib-Prover, Track C Day 1 Tao persona analysis (mailbox from_mathlib_prover/0023, 2026-04-24T22:00Z), integrated verbatim by Worker per Session B authorization 0067 §6.3."
  - "§9.7 paragraph drafted by Session C Mathlib-Prover, Phase IX Part A synthesis §9.3 (mailbox from_mathlib_prover/0042, 2026-04-25T~03:00Z), integrated verbatim by Worker per Session B authorization 0078 §6.3 + 0080 §3.1."
  - "§9.X (8 subsections) drafted by Worker integrating Session C Phase X mathnotes 0049-0054 (set-theoretic schema + Wall DNA Theorem + META-ROADMAP THEOREM + Lean infrastructure 43d622b) and Phase XI mathnotes 0057-0061 (Theorem 9.X.1 Rhin + Hercher closure + Conjecture 9.X.2 refined rigidity + Phase XII research-program framing), per Session B authorization 0098 §5 + 0098 §9."
last_updated: 2026-04-25
---

# 9. Open problems

*[WIP — skeleton prose for §9.1-§9.5 pending Day-3 polish ; §9.6 Tao and §9.7 structural-excess (Ψ_s) paragraphs are Session C direct-verified and integrated verbatim per Session B authorization.]*

## Planned structure

### 9.1 Removing `ProductBoundThreshold`
The central open question raised by this paper : can `ProductBoundThreshold` be promoted to a theorem? §5 Obstruction I answers *not within any product-bound approach*. The question is therefore : what non-product-bound technique might close the `k > 1322` case?

### 9.2 The `k ≥ q_{14}` tail
Current-generation Barina reaches `n < 2^{71}`, which via CF windows `W_8, ..., W_{13}` covers `k < q_{14} ≈ 10{,}590{,}737`. A `W_{14}` extension would require arithmetic gap constants at denominator `q_{14}` with `~10^5` digits — outside native_decide's reach at present hardware.

### 9.3 Formalisation challenges
- R-M3.H12 bridge `(Real.convergent v n).den : ℝ = (GenContFract.of v).dens n` is not direct in Mathlib v4.27.0. Phase62 works around it via parametric real-valued form; a proper bridge would strengthen Phase61/62 integration.
- Phase63 Sections 2-11 as Lean theorems would require the breakthrough discussed in §9.1 + the bridge in §9.3.

### 9.4 Relation to divergence
This paper does not address the divergence half of Collatz. The techniques (Baker's theorem + CF theory + formal verification) are in principle adaptable, but the structure is different. Explicit scope disclosure.

### 9.5 Checkpoints for speculative tracks (Track B pointer)
Session C Track B continues 6-12 weeks with Day 14 kill-switch on transcendence-theoretic approaches (Santana 2026 rigour-closure, Knight 2025 extension, transcendence-gap sharpenings). Results, if any, would feed paper v3.

### 9.6 Probabilistic techniques (Tao)

*[Paragraph drafted by Session C Track C Day 1 Tao persona analysis (mailbox 0023 §5.2), integrated verbatim per Session B authorization 0067 §6.3.]*

Tao's probabilistic approach (2019, *Forum of Mathematics, Pi*) proves that almost all Collatz orbits attain almost bounded values under logarithmic density. This result is **probabilistic** and does not extend to deterministic statements about hypothetical cycles (which have density zero). Tao's broader toolkit (entropy compression à la Moser-Tardos [blog 2009], higher-order Fourier analysis à la Green-Tao-Ziegler) has not been successfully applied to deterministic Collatz cycle bounds; such applications would require substantial new theoretical work. We therefore do not integrate probabilistic techniques into our proof of Theorem 3.1 (which remains conditional on the structural hypotheses §4).

### 9.7 Structural-excess framework Ψ_s (Phase VIII extension)

*[Paragraph drafted by Session C Mathlib-Prover, Phase IX Part A synthesis §9.3 (mailbox from_mathlib_prover/0042), integrated verbatim per Session B authorization 0078 §6.3 + 0080 §3.1. See §8.5 for the formalization status and the separate branch `phase8-psi-s-lean`.]*

We formalize in Lean 4 a custom Φ_s / Ψ_s structural-excess framework (Mathlib v4.27.0 lacks Gowers norms). Machine-verified : the trivial Collatz cycle has Ψ_2 = 32/81, establishing a factor-33× structural excess over its mean prediction (1/81). The T4c conjecture is encoded as parametric `def T4c_Conjecture_Psi2`, and the contradiction schema `psi2_bounds_no_cycle` records the logical shape of the intended attack. See `ProjetCollatz.PhaseVIII.StructuralExcess` in the repository branch `phase8-psi-s-lean` (§8.5).

### 9.X Set-theoretic obstructions via Gowers nilsequences and MRDP × Kolmogorov compressibility (Phase X + Phase XI)

*[Section §9.X drafted by Worker integrating Session C Phase X mathnotes 0049-0054 (set-theoretic schema + Wall DNA Theorem + META-ROADMAP THEOREM + Lean infrastructure) and Phase XI mathnotes 0057-0061 (Theorem 0060.1 Rhin + Hercher closure + Conjecture 0060.2 refined rigidity + Phase XII research-program framing). Per Session B authorization 0098 §5 + 0098 §9.]*

#### 9.X.1 Set-theoretic schema

For non-trivial Collatz cycle parity vector `v_cycle` of period `T`, following Phase X mathnote 0050 §1.3 :

> `S_{cycle} ⊂ S_{Steiner-tuples} ∩ S_{Ψ-large} ∩ S_{K-bounded} \ S_{Hercher}`

with `S_{Ψ-large} = {v : ψ_2(v) ≥ ε}` (Phase VIII T4c, §8.5) and `S_{K-bounded} = {v : K(v | Hercher, Steiner) ≤ f(T)}` (`C10` MRDP × Kolmogorov compressibility). Cycle non-existence requires intersection emptiness modulo Hercher.

#### 9.X.2 Counting argument insufficient

Among classical mechanisms for cycle structural constraint, the conjunction of Phase VIII T4c (Gowers nilsequence compressibility) and `C10` (MRDP Diophantine compactness) provides correlated rather than independent constraints, yielding `|S_{Ψ-large} ∩ S_{K-bounded}| ≈ poly(T)` under conditional Kolmogorov on (Hercher, Steiner) (Phase X 0051 §2.7 + 0053 §3.3).

#### 9.X.3 Wall DNA Theorem and META-ROADMAP THEOREM

The structural Wall reduces to three independent bricks : `W1` (`T` binary, exploited), `W2` (Steiner rigidity, OPEN), `W3` (Hercher, exploited). Bricks `W4` (Gowers) and `W5` (MRDP) reduce to compressibility-class redundancy. `W2` is necessary AND sufficient (modulo `W1+W3`) (Phase X 0053 §3 Wall DNA Theorem).

Among classical mechanisms tested in Session C Phase X (Gowers nilsequences, MRDP × Kolmogorov, Schmidt subspace variants, Tao 2019 entropy compression, Lagarias `T_∞` analysis), Steiner rigidity is the unique remaining path identified for unifying Phase VIII T4c with the `C10*` set-theoretic obstruction (Phase X 0051 §4.2 + 0052 §4.3 META-ROADMAP THEOREM).

#### 9.X.4 Mechanism boundary search

Phase X mathnote 0052 verified the following mechanism boundaries :

- **Schmidt subspace theorem and variants** : require `α` algebraic ; `log 2`, `log 3` are transcendental, so the technique does not extend to Collatz beyond Baker's existing exploitation (§4.1).
- **Tao 2019 entropy compression** : 3-adic random walk for typical orbits in logarithmic density, no discussion of cycles or fixed points (verified via arXiv:1909.03562 abstract ; cf. §6.5 + §9.6).
- **Lagarias `T_∞` Galton-Watson** : `T_∞` rooted at `1` contains all predecessors of `1` by definition, so non-trivial cycles are disjoint from `T_∞` and do not fall under the Galton-Watson framework.

#### 9.X.5 Lean infrastructure (43d622b)

A 200-line Lean 4 prototype `ProjetCollatz/PhaseX/MRDPCollatz.lean` (repository commit `43d622b`) formalizes the META-ROADMAP THEOREM as a `theorem ... := sorry` with hypothesis structure (`hSteinerRigidity`, `hCycle`, `hPsiLarge`, `hKBounded`, `hHercher`). The trivial Collatz cycle's `ψ_2 = 32/81` is machine-verified via `native_decide` reusing the Phase VIII framework (§8.5). Mathlib `NumberTheory.Dioph` (Carneiro 2018, formalising Matiyasevich's theorem) provides the foundation for completing the Diophantine encoding. Zero new user axioms introduced (`#print axioms` audit).

#### 9.X.6 Theorem 9.X.1 — Rhin 1987 + Hercher 2023 close Conjecture 0059.2

Phase XI mathnote 0060 establishes :

**Theorem 9.X.1 (Phase XI consequence of Rhin 1987 + Hercher 2023).**
*For all admissible Collatz cycle parameters `(a, k)` with*
*`a > 1.375 · 10¹¹`,*
> *`q := 2^a − 3^k > 2.836^k`.*

The proof combines Rhin's effective irrationality bound `μ(log_2 3) ≤ 5.125` with Hercher's lower bound `T > 1.375 · 10¹¹` (§6.1) by straightforward rearrangement (Phase XI 0060 §2.4, eight-step proof sketch). Theorem 9.X.1 closes Phase XI Conjecture 0059.2 (`q >> 2.836^k`) modulo the two source results.

#### 9.X.7 Conjecture 9.X.2 — refined central rigidity question (OPEN)

The actual structural question that Theorem 9.X.1 *does not* answer is the σ-level uniform distribution of `R_K(σ) := Σ 3^{K−1−i} · 2^{σ(i)}` modulo `q` :

**Conjecture 9.X.2 (Phase XI 0060, central rigidity).**
*For admissible `(T, K)` with `T > 1.375 · 10¹¹`, the values*
*`{R_K(σ) (mod q) : σ : {0,…,K−1} → {0,…,T−1} increasing}` are*
*approximately uniformly distributed modulo `q`.*

This refines the « Steiner rigidity » open question identified in §9.X.3 (META-ROADMAP THEOREM, Wall brick `W2`) : a positive resolution of Conjecture 9.X.2 would, combined with Theorem 9.X.1, complete the σ-level rigidity argument. Heuristic plausibility is supported by orbit-cover arguments (Phase XI 0060 §4.4) ; no obstruction is currently known.

#### 9.X.8 Three challenges and Phase XII research-program framing

Phase XI mathnote 0061 documents three substantive technical challenges to a direct attack on Conjecture 9.X.2 via Kloosterman + Weil + Vinogradov sums :

1. ***q* composite obstruction.** The Weil bound `|Σ e(α 2^t / q)| = O(√q)` requires `q` prime (with Kloosterman-pair structure). For `q = 2^T − 3^K` composite, generalised Weil (Estermann + Hensel) yields `O(q^{1/2 + ε})` heuristically for square-free `q`, but rigorously verifying favourable factorisation for every admissible `q` is open.
2. **Increasing subset constraint.** `S_K(c)` sums over increasing `K`-tuples, not arbitrary tuples. Cauchy-Schwarz / inclusion-exclusion decompositions yield cross-terms with rank-dependent coefficients that standard analytic-number-theory techniques do not directly handle.
3. **Mixed exponential 3-adic + 2-adic structure.** `R_K(σ)` mixes powers of 3 (deterministic coefficient) and 2 (`σ`-dependent), so the standard Kloosterman-sum framework over a single multiplicative group does not directly apply. Decoupling absorbs the 3-power into a constant `α_i = c · 3^{K−1−i} (mod q)` whose orbit under multiplication by 3 covers most residues — challenge 3 resolves conditional on challenges 1 and 2.

The path forward (Phase XII research program) is one of three options : (a) develop new analytic techniques for composite-modulus exponential sums with increasing-subset constraints ; (b) restrict to admissible `(T, K)` with favourable factorisation of `q` ; or (c) accept a partial bound and identify the specific obstruction to closing the remaining gap. Each option defines a distinct sub-line of investigation outside the present paper's scope.

