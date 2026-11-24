import Mathlib

namespace Targets.Ramsey56.Spec

/-- A valid witness proving `R(5, 6) > n`: a symmetric irreflexive graph on `Fin n` containing
    no 5-clique and no 6-element independent set. -/
def ValidBound (n : ℕ) : Prop :=
  ∃ adj : Fin n → Fin n → Bool,
    (∀ u, adj u u = false) ∧
    (∀ u v, adj u v = adj v u) ∧
    (¬ ∃ f : Fin 5 → Fin n, Function.Injective f ∧ ∀ i j, i ≠ j → adj (f i) (f j) = true) ∧
    (¬ ∃ f : Fin 6 → Fin n, Function.Injective f ∧ ∀ i j, i ≠ j → adj (f i) (f j) = false)

end Targets.Ramsey56.Spec
