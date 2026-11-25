# Frankl Union-Closed Density Bound (`frankl_density_bound`)

- **Kind:** Quantitative open bound (`direction: maximize`)
- **Domain:** Combinatorics
- **Verified baseline:** `0` (the trivial bound; any kernel-verified `P > 0` is the first record, in `1e-5` units)
- **Published literature SOTA:** `38234` (`0.38234`, Cambie / Yu / Sawin / Chase–Lovett improvements on Gilmer's entropy method)
- **Reference:** https://en.wikipedia.org/wiki/Union-closed_sets_conjecture

## Goal

Exhibit `def bound : Nat := <P>` strictly larger than the current verified holder on `main`, and
prove `Targets.FranklDensity.Spec.ValidBound bound` (for every non-trivial finite union-closed
family `F`, some element belongs to at least `P / 100000` of the sets in `F`). Reaching
`P ≥ 38235` sets a new mathematical world record, and reaching `P = 50000` settles Frankl's
conjecture!
