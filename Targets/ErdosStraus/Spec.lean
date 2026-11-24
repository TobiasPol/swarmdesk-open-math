import Mathlib

namespace Targets.ErdosStraus.Spec

/-- Division-free representation of `4/n = 1/x + 1/y + 1/z` with positive integers `x, y, z`. -/
def HasUnitSum (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ 4 * x * y * z = n * (y * z + x * z + x * y)

/-- Erdős-Straus Conjecture: `4/n = 1/x + 1/y + 1/z` holds for every integer `n ≥ 2`. -/
def Statement : Prop :=
  ∀ n : ℕ, 2 ≤ n → HasUnitSum n

/-- Blueprint Lemma 1: Erdős-Straus holds for every even integer `n ≥ 2`. -/
def LemmaEvenCase : Prop :=
  ∀ n : ℕ, 2 ≤ n → n % 2 = 0 → HasUnitSum n

/-- Blueprint Lemma 2: Erdős-Straus holds for every integer `n ≥ 2` with `n ≡ 3 (mod 4)`. -/
def LemmaMod4Eq3 : Prop :=
  ∀ n : ℕ, 2 ≤ n → n % 4 = 3 → HasUnitSum n

end Targets.ErdosStraus.Spec
