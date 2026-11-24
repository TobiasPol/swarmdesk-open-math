import Mathlib

namespace Targets.Schur6.Spec

/-- A valid witness proving `S(6) ≥ n`: a 6-coloring of `{1, ..., n}` (indexed by `Fin n` via `i + 1`)
    with no monochromatic solution to `(x + 1) + (y + 1) = (z + 1)`. -/
def ValidBound (n : ℕ) : Prop :=
  ∃ color : Fin n → Fin 6,
    ∀ x y z : Fin n, (x.val + 1) + (y.val + 1) = z.val + 1 →
      ¬ (color x = color y ∧ color y = color z)

end Targets.Schur6.Spec
