import Targets.Schur6.Spec
import Targets.Schur6.Helpers

namespace Targets.Schur6.Proof

def bound : Nat := 63

private def logColor (x : Fin 63) : Fin 6 :=
  ⟨Nat.log 2 (x.val + 1), by
    have hlt : x.val + 1 < 2 ^ 6 := by omega
    exact (Nat.log_lt_iff_lt_pow (by decide) (by omega)).2 hlt⟩

theorem proved : Targets.Schur6.Spec.ValidBound bound := by
  refine ⟨logColor, ?_⟩
  intro x y z hsum ⟨hxy, hyz⟩
  have h1 : Nat.log 2 (x.val + 1) = Nat.log 2 (y.val + 1) := congrArg Fin.val hxy
  have h2 : Nat.log 2 (y.val + 1) = Nat.log 2 (z.val + 1) := congrArg Fin.val hyz
  set k := Nat.log 2 (y.val + 1) with hk
  have hxlo : 2 ^ k ≤ x.val + 1 := by
    rw [hk, ← h1]
    exact Nat.pow_log_le_self 2 (by omega)
  have hylo : 2 ^ k ≤ y.val + 1 := Nat.pow_log_le_self 2 (by omega)
  have hzlt : z.val + 1 < 2 ^ (k + 1) := by
    rw [hk, h2]
    exact Nat.lt_pow_succ_log_self (by decide) (z.val + 1)
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
    rw [Nat.pow_succ]
    omega
  omega

end Targets.Schur6.Proof
