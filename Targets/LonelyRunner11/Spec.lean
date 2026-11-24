import Mathlib

namespace Targets.LonelyRunner11.Spec

/-- Distance from a real number `x` to the nearest integer, in `[0, 1/2]`. -/
noncomputable def distToInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- Lonely Runner property for `k` moving runners (total `k + 1` runners including the stationary one). -/
def LonelyFor (v : Fin 10 → ℤ) : Prop :=
  ∃ t : ℝ, ∀ i : Fin 10, (1 : ℝ) / 11 ≤ distToInt (t * (v i : ℝ))

/-- Lonely Runner Conjecture for 11 runners (the next open frontier after 9 and 10 runners fell in 2026). -/
def Statement : Prop :=
  ∀ v : Fin 10 → ℤ, (∀ i, v i ≠ 0) → LonelyFor v

/-- Blueprint Lemma: Scaling all speeds by a common non-zero integer factor preserves lonesomeness. -/
def LemmaGcdOne : Prop :=
  (∀ v : Fin 10 → ℤ, (∀ i, v i ≠ 0) →
      (∀ d : ℕ, 1 < d → ¬ ∀ i, (d : ℤ) ∣ v i) → LonelyFor v) →
    Statement

end Targets.LonelyRunner11.Spec
