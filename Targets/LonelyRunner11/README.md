# Lonely Runner Conjecture for 11 Runners (`lonely_runner_11`)

- **Kind:** Open conjecture (prove `Statement` as `theorem proved`, or disprove `¬ Statement` as `theorem disproved`)
- **Domain:** Combinatorics / Diophantine Approximation
- **Reference:** https://en.wikipedia.org/wiki/Lonely_runner_conjecture

## Informal statement

Eleven runners start together on a unit-length circular track with distinct constant speeds. After
shifting into one runner's rest frame and applying the known integer-speed reduction, for any 10
non-zero integer speeds $v_1, \dots, v_{10}$, there exists a real time $t$ at which every moving
runner has distance at least $1/11$ from the nearest integer.

## Context & Blueprint

Cases up to 8 (Rosenfeld) and 9–10 runners (Trakulthongchai, 2026) have been settled via sieve
methods, making **11 runners** the active open frontier.

- Blueprint lemma: `Targets/LonelyRunner11/Lemmas/GcdOne.lean` (`lonely_runner_11_gcd_one`).
