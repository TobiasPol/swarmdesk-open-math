import Mathlib

namespace Targets.HerzogSchonheim.Spec

/-- A finite partition of a group `G` into `k ≥ 2` pairwise disjoint left cosets `g_i • H_i`. -/
def IsCosetPartition {G : Type} [Group G] {k : ℕ}
    (g : Fin k → G) (H : Fin k → Subgroup G) : Prop :=
  2 ≤ k ∧
  (∀ i : Fin k, 0 < (H i).index) ∧
  (∀ x : G, ∃! i : Fin k, x ∈ Set.image (g i * ·) (H i : Set G))

/-- Herzog-Schönheim Conjecture: at least two subgroups in a finite coset partition share the same index. -/
def Statement : Prop :=
  ∀ (G : Type) [Group G] (k : ℕ) (g : Fin k → G) (H : Fin k → Subgroup G),
    IsCosetPartition g H → ∃ i j : Fin k, i ≠ j ∧ (H i).index = (H j).index

/-- Blueprint Lemma: The reciprocal indices of a finite coset partition sum to 1. -/
def LemmaIndexSum : Prop :=
  ∀ (G : Type) [Group G] (k : ℕ) (g : Fin k → G) (H : Fin k → Subgroup G),
    IsCosetPartition g H → ∑ i : Fin k, (1 : ℚ) / ((H i).index : ℚ) = 1

end Targets.HerzogSchonheim.Spec
