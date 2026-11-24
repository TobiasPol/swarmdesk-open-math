import Targets.Schur6.Spec
import Targets.Schur6.Helpers

namespace Targets.Schur6.Proof

def bound : Nat := 63

private def logColor (x : Fin 63) : Fin 6 :=
  ⟨Nat.log 2 (x.val + 1), by
    have hlt : x.val + 1 < 2 ^ 6 := by omega
    exact Nat.log_lt_of_lt_pow (by omega) hlt⟩

theorem proved : Targets.Schur6.Spec.ValidBound bound := by
  dsimp only [bound]
  refine ⟨logColor, ?_⟩
  intro x y z hsum ⟨hxy, hyz⟩
  have h1 : Nat.log 2 (x.val + 1) = Nat.log 2 (y.val + 1) := congrArg Fin.val hxy
  have h2 : Nat.log 2 (y.val + 1) = Nat.log 2 (z.val + 1) := congrArg Fin.val hyz
  have hxlo : 2 ^ Nat.log 2 (y.val + 1) ≤ x.val + 1 := by
    rw [← h1]
    exact Nat.pow_log_le_self 2 (by omega)
  have hylo : 2 ^ Nat.log 2 (y.val + 1) ≤ y.val + 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have hzlt : z.val + 1 < 2 ^ (Nat.log 2 (y.val + 1) + 1) := by
    rw [h2]
    exact Nat.lt_pow_succ_log_self (by decide) (z.val + 1)
  have hpow :
      2 ^ (Nat.log 2 (y.val + 1) + 1) =
        2 ^ Nat.log 2 (y.val + 1) + 2 ^ Nat.log 2 (y.val + 1) := by
    rw [Nat.pow_succ]
    omega
  omega

end Targets.Schur6.Proof
