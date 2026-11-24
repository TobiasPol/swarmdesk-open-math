import Targets.Vdw35.Spec
import Targets.Vdw35.Helpers

namespace Targets.Vdw35.Proof

def bound : Nat := 12

private def blockColor (i : Fin 12) : Fin 3 :=
  ⟨i.val / 4, by omega⟩

theorem proved : Targets.Vdw35.Spec.ValidBound bound := by
  dsimp only [bound]
  refine ⟨blockColor, ?_⟩
  intro a d h4 hd ⟨h01, h12, h23, h34⟩
  have h04 : a / 4 = (a + 4 * d) / 4 := by
    have e01 : a / 4 = (a + d) / 4 := congrArg Fin.val h01
    have e12 : (a + d) / 4 = (a + 2 * d) / 4 := congrArg Fin.val h12
    have e23 : (a + 2 * d) / 4 = (a + 3 * d) / 4 := congrArg Fin.val h23
    have e34 : (a + 3 * d) / 4 = (a + 4 * d) / 4 := congrArg Fin.val h34
    omega
  omega

end Targets.Vdw35.Proof
