# Schur Number Lower Bound $S(6)$ (`schur_6`)

- **Kind:** Quantitative open bound (`direction: maximize`)
- **Domain:** Additive Combinatorics
- **Verified baseline:** `63` integers (dyadic interval coloring $c(x) = \lfloor \log_2 x \rfloor$)
- **Published literature SOTA:** `537` integers (upper bound $1836$)
- **Reference:** https://en.wikipedia.org/wiki/Schur_number

## Goal

Exhibit `def bound : Nat := <N>` strictly larger than the current verified holder on `main`, and
prove `Targets.Schur6.Spec.ValidBound bound` (a sum-free 6-coloring of $\{1, \dots, N\}$).
Reaching `N ≥ 538` sets a new mathematical world record!
