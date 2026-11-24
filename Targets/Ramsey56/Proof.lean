import Targets.Ramsey56.Spec
import Targets.Ramsey56.Helpers

namespace Targets.Ramsey56.Proof

def bound : Nat := 16

private def fourK4 (u v : Fin 16) : Bool :=
  decide (u ≠ v ∧ u.val / 4 = v.val / 4)

theorem proved : Targets.Ramsey56.Spec.ValidBound bound := by
  dsimp only [bound]
  refine ⟨fourK4, ?_, ?_, ?_, ?_⟩
  · intro u
    simp [fourK4]
  · intro u v
    by_cases h : u = v
    · subst h
      simp [fourK4]
    · have hne : v ≠ u := Ne.symm h
      simp [fourK4, h, hne, eq_comm]
  · rintro ⟨f, hinj, hclique⟩
    have hsame : ∀ i : Fin 5, (f i).val / 4 = (f 0).val / 4 := by
      intro i
      by_cases hi : i = 0
      · subst hi
        rfl
      · have hadj := hclique i 0 hi
        simp [fourK4] at hadj
        exact hadj.2
    have hmap : Function.Injective (fun i : Fin 5 => (⟨(f i).val % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4)) := by
      intro a b hab
      have hmod : (f a).val % 4 = (f b).val % 4 := congrArg Fin.val hab
      have hdiv : (f a).val / 4 = (f b).val / 4 := (hsame a).trans (hsame b).symm
      have hval : (f a).val = (f b).val := by omega
      exact hinj (Fin.ext hval)
    have hcard := Fintype.card_le_of_injective _ hmap
    simp at hcard
  · rintro ⟨f, hinj, hind⟩
    have hmap : Function.Injective (fun i : Fin 6 => (⟨(f i).val / 4, by omega⟩ : Fin 4)) := by
      intro a b hab
      by_cases h : a = b
      · exact h
      · exfalso
        have hadj := hind a b h
        have hfv : f a ≠ f b := fun heq => h (hinj heq)
        have hdiv : (f a).val / 4 = (f b).val / 4 := congrArg Fin.val hab
        simp [fourK4, hfv, hdiv] at hadj
    have hcard := Fintype.card_le_of_injective _ hmap
    simp at hcard

end Targets.Ramsey56.Proof
