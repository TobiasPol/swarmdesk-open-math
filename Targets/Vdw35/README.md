# van der Waerden Lower Bound $W(3, 5)$ (`vdw_3_5`)

- **Kind:** Quantitative open bound (`direction: maximize`)
- **Domain:** Ramsey Theory
- **Verified baseline:** `12` integers (three 4-element color blocks)
- **Published literature SOTA:** `2173` integers ($W(3, 5) > 2173$)
- **Reference:** https://en.wikipedia.org/wiki/Van_der_Waerden_number

## Goal

Exhibit `def bound : Nat := <N>` strictly larger than the current verified holder on `main`, and
prove `Targets.Vdw35.Spec.ValidBound bound` (a 3-coloring of $\{0, \dots, N - 1\}$ avoiding any
monochromatic 5-term arithmetic progression). Reaching `N ≥ 2174` sets a new world record!
