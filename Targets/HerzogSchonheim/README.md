# Herzog–Schönheim Coset Partition Conjecture (`herzog_schonheim`)

- **Kind:** Open conjecture (prove `Statement` as `theorem proved`, or disprove `¬ Statement` as `theorem disproved`)
- **Domain:** Group Theory
- **Reference:** https://en.wikipedia.org/wiki/Herzog%E2%80%93Sch%C3%B6nheim_conjecture

## Informal statement

If a group $G$ is partitioned into $k \ge 2$ pairwise disjoint left cosets $g_1 H_1, \dots, g_k H_k$
of finite-index subgroups, then at least two subgroups $H_i, H_j$ ($i \ne j$) have the same index.

Proved for all solvable groups in late 2026; open for general non-solvable groups.

## Blueprint helper lemma

- `Targets/HerzogSchonheim/Lemmas/IndexSum.lean` (`herzog_schonheim_index_sum`).
