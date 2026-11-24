import Mathlib

namespace Targets.UnionClosedSets.Spec

/-- A finite family of finite sets over `ℕ` is union-closed and contains at least one non-empty set. -/
def IsUnionClosedNonTrivial (F : Finset (Finset ℕ)) : Prop :=
  (∃ A ∈ F, A.Nonempty) ∧ ∀ A ∈ F, ∀ B ∈ F, (A ∪ B) ∈ F

/-- Frankl's Union-Closed Sets Conjecture: some element belongs to at least half of all sets in `F`. -/
def Statement : Prop :=
  ∀ F : Finset (Finset ℕ), IsUnionClosedNonTrivial F →
    ∃ x : ℕ, F.card ≤ 2 * (F.filter (fun A => x ∈ A)).card

/-- Blueprint Lemma 1: If `F` contains a singleton `{x}`, then `x` belongs to at least half the sets. -/
def LemmaSingletonCase : Prop :=
  ∀ (F : Finset (Finset ℕ)) (x : ℕ), IsUnionClosedNonTrivial F → {x} ∈ F →
    F.card ≤ 2 * (F.filter (fun A => x ∈ A)).card

/-- Blueprint Lemma 2: If `F` contains a 2-element set `{x, y}`, then `x` or `y` belongs to at least half. -/
def LemmaPairCase : Prop :=
  ∀ (F : Finset (Finset ℕ)) (x y : ℕ), IsUnionClosedNonTrivial F → x ≠ y → ({x, y} : Finset ℕ) ∈ F →
    F.card ≤ 2 * (F.filter (fun A => x ∈ A)).card ∨
    F.card ≤ 2 * (F.filter (fun A => y ∈ A)).card

end Targets.UnionClosedSets.Spec
