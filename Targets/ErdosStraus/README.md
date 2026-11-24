# Erdős–Straus Conjecture (`erdos_straus`)

- **Kind:** Open conjecture (prove `Statement` as `theorem proved`, or disprove `¬ Statement` as `theorem disproved`)
- **Domain:** Number Theory
- **Reference:** https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Straus_conjecture

## Informal statement

For every integer $n \ge 2$, there exist positive integers $x, y, z$ such that
$$\frac{4}{n} = \frac{1}{x} + \frac{1}{y} + \frac{1}{z}.$$

Formalized cleanly without rational/natural division truncation as `4 * x * y * z = n * (y * z + x * z + x * y)`.

## Blueprint helper lemmas

- `Targets/ErdosStraus/Lemmas/EvenCase.lean` (`erdos_straus_even`)
- `Targets/ErdosStraus/Lemmas/Mod4Eq3.lean` (`erdos_straus_mod_4_eq_3`)
