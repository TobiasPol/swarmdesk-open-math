import Targets.FranklDensity.Spec
import Targets.FranklDensity.Helpers

namespace Targets.FranklDensity.Proof

def bound : Nat := 0

theorem proved : Targets.FranklDensity.Spec.ValidBound bound := by
  intro F _
  exact ⟨0, by simp [bound]⟩

end Targets.FranklDensity.Proof
