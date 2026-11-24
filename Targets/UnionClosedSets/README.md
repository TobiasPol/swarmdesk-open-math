# Frankl's Union-Closed Sets Conjecture (`union_closed_sets`)

- **Kind:** Open conjecture (prove `Statement` as `theorem proved`, or disprove `¬ Statement` as `theorem disproved`)
- **Domain:** Combinatorics
- **Reference:** https://en.wikipedia.org/wiki/Union-closed_sets_conjecture

## Informal statement

For every finite union-closed family $\mathcal{F}$ of finite sets (containing at least one non-empty
set), there exists an element $x$ that belongs to at least $|\mathcal{F}|/2$ sets in $\mathcal{F}$.

## Blueprint helper lemmas

- `Targets/UnionClosedSets/Lemmas/SingletonCase.lean` (`union_closed_singleton`)
- `Targets/UnionClosedSets/Lemmas/PairCase.lean` (`union_closed_pair`)
