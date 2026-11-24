import Targets.CapSet8.Spec
import Targets.CapSet8.Helpers

namespace Targets.CapSet8.Proof

def bound : Nat := 256

private def boolToZMod3 (b : Bool) : ZMod 3 :=
  if b then 1 else 0

private def embed (f : Fin 8 → Bool) : Fin 8 → ZMod 3 :=
  fun i => boolToZMod3 (f i)

private lemma embed_inj : Function.Injective embed := by
  intro f g h
  funext i
  have hi := congrFun h i
  cases hf : f i <;> cases hg : g i <;>
    simp [embed, boolToZMod3, hf, hg] at hi ⊢ <;>
    exact absurd hi (by decide)

theorem proved : Targets.CapSet8.Spec.ValidBound bound := by
  refine ⟨Finset.univ.image embed, ?_, ?_⟩
  · intro x hx y hy z hz hsum
    rcases Finset.mem_image.mp hx with ⟨fx, _, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨fy, _, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨fz, _, rfl⟩
    have hcoord : ∀ i : Fin 8, fx i = fy i ∧ fy i = fz i := by
      intro i
      have hi := congrFun hsum i
      cases h1 : fx i <;> cases h2 : fy i <;> cases h3 : fz i <;>
        simp [embed, boolToZMod3, h1, h2, h3] at hi ⊢ <;>
        exact absurd hi (by decide)
    constructor
    · funext i
      simp [embed, (hcoord i).1]
    · funext i
      simp [embed, (hcoord i).2]
  · rw [Finset.card_image_of_injective _ embed_inj]
    simp [bound] <;> decide

end Targets.CapSet8.Proof
