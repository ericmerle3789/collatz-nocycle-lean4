---
section: "6"
owner: session_c
status: placeholder
source: mathnotes_0018_section_E_plus_0019_0020
last_updated: 2026-04-24
---

# 6. Obstruction II: state of the art (δ9)

**Owner** : Session C Mathlib-Prover, via mathnotes package 0018 §E + supplementary analyses 0019 (Santana), 0020 (Knight), 0021 (Rozier-verification).

**Status** : awaiting import.

## Expected subsections

### 6.1 Structural classification of 1977-2026 results
Typology proposed by Session C for the cycle-elimination literature : positive vs restricted-class, published vs preprint, direct-verified vs inference-only.

### 6.2 Structural class eliminations (restricted classes of cycles)
Safe-to-use Session C formulation for Knight 2025 :

> - Steiner (1977): no non-trivial circuits (verified via Lagarias 1985 §2.6).
> - Knight (2025, Discrete Math. 349(3)): no high cycles (parity vector = upper Christoffel word).
>
> These results eliminate specific restricted classes of hypothetical cycles via combinatorial + Diophantine analysis. Neither extends to the general class of cycles with arbitrary parity vectors. Iterating restricted-class eliminations to cover all parity patterns faces combinatorial explosion.

Knight 2025 access : blocked (HAL Anubis 403, ScienceDirect paywall). Formulation above is the project-validated `[INDIRECT]` framing per mailbox 0065 §6.5.

### 6.3 Density and probabilistic approaches
- Applegate-Lagarias 1995 : density.
- Tao 2019 : almost-all results.
- Framing : these do not close the cycle problem.

### 6.4 Recent reformulation attempts (insufficient alone)
Direct-verified by Session C :
- Santana (2026, arXiv:2601.03297v4) : rigour gap identified — see mailbox 0019.
- Dhiman-Pandey (2026, arXiv:2601.12772) : complementary framework, not a closing proof.
- Rozier-Terracol (2026, arXiv:2502.00948, to appear *Discrete Math.*) : paradoxical sequences, uses Rhin heuristically.

### 6.5 Synthesis
The state-of-the-art as of 2026 does not contain a complete proof; the published and preprint results are either restricted-class, probabilistic, or use conditional hypotheses comparable to our `ProductBoundThreshold`.

## Integration note

When importing Session C draft :
- Keep the Knight 2025 formulation in §6.2 verbatim from mailbox 0065 §6.5.
- Cite Santana 2026 with the rigour-gap footnote per mailbox 0019.
- Cite Rozier-Terracol 2026 correctly per mailbox 0065 §5 (not the fabricated paraphrase).
