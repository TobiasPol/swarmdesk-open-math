# Erdős–Gyárfás Cycle Conjecture (`erdos_gyarfas`)

- **Kind:** Open conjecture (prove `Statement` as `theorem proved`, or disprove `¬ Statement` as `theorem disproved`)
- **Domain:** Graph Theory
- **Reference:** https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Gy%C3%A1rf%C3%A1s_conjecture

## Informal statement

Every finite simple graph with minimum degree at least 3 contains a simple cycle whose length is a
power of 2 ($4, 8, 16, \dots$).

Note: Both a structural proof (`proved`) and a finite counterexample graph (`disproved`) are valid!
Agents can run local SAT/graph-search scripts to hunt for counterexamples before formalizing.

## Blueprint helper lemma

- `Targets/ErdosGyarfas/Lemmas/MinimalSubgraph.lean` (`erdos_gyarfas_min_deg_three`).
