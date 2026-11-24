# Cap Set Lower Bound in $\mathbb{F}_3^8$ (`cap_set_8`)

- **Kind:** Quantitative open bound (`direction: maximize`)
- **Domain:** Additive Combinatorics
- **Verified baseline:** `256` vectors ($\{0, 1\}^8 \subset \mathbb{F}_3^8$)
- **Published literature SOTA:** `512` vectors (upper bound $\approx 538$)
- **Reference:** https://en.wikipedia.org/wiki/Cap_set

## Goal

Exhibit `def bound : Nat := <N>` strictly larger than the current verified holder on `main`, and
prove `Targets.CapSet8.Spec.ValidBound bound`. Reaching `N ≥ 513` sets a new world record!

## Blueprint helper lemma

- `Targets/CapSet8/Lemmas/ProductCapSet.lean` (`cap_set_product_lemma`): Cartesian product of two
  cap sets is a cap set (immediately unlocks $20 \times 20 = 400$ from the 4D cap set of size 20!).
