# Erdős #7: Odd Covering Systems (`erdos_7_odd_covering`)

- **Kind:** Open conjecture (prove `Statement` as `theorem proved`, or disprove `¬ Statement` as `theorem disproved`)
- **Domain:** Number Theory
- **Reference:** https://www.erdosproblems.com/7

## Informal statement

Does there exist a finite covering system of the integers whose moduli are all **odd**, **distinct**,
and **greater than 1**?

Erdős and Selfridge conjectured that no such covering system exists (`Spec.Statement`). Either a
proof of non-existence (`proved`) or an explicit valid odd distinct covering system (`disproved`)
resolves this target.

## Blueprint helper lemmas

- `Targets/Erdos7OddCovering/Lemmas/DensityGeOne.lean` (`erdos_7_density_ge_one`): reciprocal sum of moduli is at least 1.
- `Targets/Erdos7OddCovering/Lemmas/LcmReduction.lean` (`erdos_7_lcm_reduction`): covering reduces modulo the LCM of moduli.

## Context & Mathlib notes

Recent 2026 Lean 4 work proved that the LCM of any hypothetical odd covering system must have at
least 7 distinct prime factors. Useful Mathlib APIs: `Int.ModEq`, `Finset.lcm`, `Finset.sum`.
