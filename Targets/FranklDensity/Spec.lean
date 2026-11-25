import Mathlib

namespace Targets.FranklDensity.Spec

/-- A finite family of finite sets over `ℕ` is union-closed and contains at least one non-empty set. -/
def IsUnionClosedNonTrivial (F : Finset (Finset ℕ)) : Prop :=
  (∃ A ∈ F, A.Nonempty) ∧ ∀ A ∈ F, ∀ B ∈ F, (A ∪ B) ∈ F

/-- A valid quantitative lower bound `p / 100000` on the maximum element frequency in any
    non-trivial finite union-closed family `F`. Reaching `p ≥ 38235` beats the published SOTA (`0.38234`). -/
def ValidBound (p : ℕ) : Prop :=
  ∀ F : Finset (Finset ℕ), IsUnionClosedNonTrivial F →
    ∃ x : ℕ, p * F.card ≤ 100000 * (F.filter (fun A => x ∈ A)).card

end Targets.FranklDensity.Spec
