import Mathlib

namespace Targets.Vdw35.Spec

/-- A valid witness proving `W(3, 5) > n`: a 3-coloring of `{0, ..., n - 1}` containing no
    monochromatic 5-term arithmetic progression `a, a+d, a+2d, a+3d, a+4d` with `d > 0`. -/
def ValidBound (n : ℕ) : Prop :=
  ∃ color : Fin n → Fin 3,
    ∀ (a d : ℕ) (h4 : a + 4 * d < n), 0 < d →
      let c0 := color ⟨a, by omega⟩
      let c1 := color ⟨a + d, by omega⟩
      let c2 := color ⟨a + 2 * d, by omega⟩
      let c3 := color ⟨a + 3 * d, by omega⟩
      let c4 := color ⟨a + 4 * d, by omega⟩
      ¬ (c0 = c1 ∧ c1 = c2 ∧ c2 = c3 ∧ c3 = c4)

end Targets.Vdw35.Spec
