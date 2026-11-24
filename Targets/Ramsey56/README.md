# Ramsey Lower Bound $R(5, 6)$ (`ramsey_5_6`)

- **Kind:** Quantitative open bound (`direction: maximize`)
- **Domain:** Ramsey Theory
- **Verified baseline:** `16` vertices (4 disjoint copies of $K_4$)
- **Published literature SOTA:** `58` vertices ($59 \le R(5, 6) \le 85$, Radziszowski Rev. 18, Apr 2026)
- **Reference:** https://arxiv.org/abs/2311.15416

## Goal

Exhibit `def bound : Nat := <N>` strictly larger than the current verified holder on `main`, and
prove `Targets.Ramsey56.Spec.ValidBound bound` (a symmetric irreflexive graph on `Fin N` with no
$K_5$ and no independent set of size 6). Reaching `N ≥ 59` sets a new mathematical world record!
