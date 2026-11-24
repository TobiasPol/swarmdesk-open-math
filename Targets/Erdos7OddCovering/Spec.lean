import Mathlib

namespace Targets.Erdos7OddCovering.Spec

/-- A finite family of congruences `x ≡ a (mod m)` with `m > 0` covering every integer `x : ℤ`. -/
def IsCovering (S : Finset (ℤ × ℕ)) : Prop :=
  (∀ p ∈ S, 0 < p.2) ∧ ∀ x : ℤ, ∃ p ∈ S, x ≡ p.1 [ZMOD (p.2 : ℤ)]

/-- All moduli in the covering system are odd, distinct, and strictly greater than 1. -/
def IsOddDistinctCovering (S : Finset (ℤ × ℕ)) : Prop :=
  IsCovering S ∧
  (∀ p ∈ S, 1 < p.2 ∧ p.2 % 2 = 1) ∧
  (∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q)

/-- Erdős Problem #7 (Erdős-Selfridge): No finite odd distinct covering system of ℤ exists. -/
def Statement : Prop :=
  ¬ ∃ S : Finset (ℤ × ℕ), IsOddDistinctCovering S

/-- Blueprint Lemma 1: The reciprocal moduli of any finite covering system sum to at least 1. -/
def LemmaDensityGeOne : Prop :=
  ∀ S : Finset (ℤ × ℕ), IsCovering S → (1 : ℚ) ≤ ∑ p ∈ S, (1 : ℚ) / (p.2 : ℚ)

/-- Blueprint Lemma 2: Covering all of ℤ is equivalent to covering every residue modulo the LCM of moduli. -/
def LemmaLcmReduction : Prop :=
  ∀ S : Finset (ℤ × ℕ), (∀ p ∈ S, 0 < p.2) →
    (∀ x : ℤ, ∃ p ∈ S, x ≡ p.1 [ZMOD (p.2 : ℤ)]) ↔
    (∀ r : ℕ, r < S.lcm Prod.snd → ∃ p ∈ S, (r : ℤ) ≡ p.1 [ZMOD (p.2 : ℤ)])

end Targets.Erdos7OddCovering.Spec
