import Mathlib

namespace Targets.CapSet8.Spec

/-- A subset `A` of `F_3^d` is a cap set if it contains no 3 distinct vectors summing to 0. -/
def IsCapSet {d : ℕ} (A : Finset (Fin d → ZMod 3)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y ∧ y = z

/-- A valid witness proving `cap(8) ≥ n`: a cap set in `F_3^8` of cardinality at least `n`. -/
def ValidBound (n : ℕ) : Prop :=
  ∃ A : Finset (Fin 8 → ZMod 3), IsCapSet A ∧ n ≤ A.card

/-- Blueprint Lemma: The Cartesian product of cap sets in `F_3^a` and `F_3^b` is a cap set in `F_3^(a+b)`. -/
def LemmaProductCapSet : Prop :=
  ∀ (a b : ℕ) (A : Finset (Fin a → ZMod 3)) (B : Finset (Fin b → ZMod 3)),
    IsCapSet A → IsCapSet B →
    ∃ C : Finset (Fin (a + b) → ZMod 3), IsCapSet C ∧ C.card = A.card * B.card

end Targets.CapSet8.Spec
