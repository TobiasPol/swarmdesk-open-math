import Targets.FranklDensity.Spec
import Targets.FranklDensity.Helpers

namespace Targets.FranklDensity.Proof

def bound : Nat := 20000

private structure BoxEntry where
  v0n : Nat
  v0d : Nat
  v1n : Nat
  v1d : Nat
  u0n : Nat
  u0d : Nat
  u1n : Nat
  u1d : Nat
  rx : Nat
  r1x : Nat
  ru : Nat
  r1u : Nat
  rv : Nat
  r1v : Nat
  deriving DecidableEq

private def pow64 (a : Nat) : Nat :=
  let a2 := a * a
  let a4 := a2 * a2
  let a8 := a4 * a4
  let a16 := a8 * a8
  let a32 := a16 * a16
  a32 * a32

private def ten64 : Nat := pow64 100000

private def checkBox (b : BoxEntry) : Bool :=
  let xn := b.u1n * b.v1n
  let xd := b.u1d * b.v1d
  let m := 100000
  decide (
    0 < b.v0n ∧ b.v0n < b.v0d ∧ b.v1n < b.v1d ∧
    0 < b.u0n ∧ b.u0n < b.u0d ∧ b.u1n < b.u1d ∧
    0 < xn ∧ xn < xd ∧
    m < b.rx ∧ m < b.r1x ∧ m ≤ b.ru ∧ m ≤ b.r1u ∧ m ≤ b.rv ∧ m ≤ b.r1v ∧
    pow64 b.rx * xn ≤ xd * ten64 ∧
    pow64 b.r1x * (xd - xn) ≤ xd * ten64 ∧
    b.u0d * ten64 ≤ pow64 b.ru * b.u0n ∧
    b.u0d * ten64 ≤ pow64 b.r1u * (b.u0d - b.u0n) ∧
    b.v0d * ten64 ≤ pow64 b.rv * b.v0n ∧
    b.v0d * ten64 ≤ pow64 b.r1v * (b.v0d - b.v0n) ∧
    8 * 64 * ((b.rx - m) * b.r1x * xn + (xd - xn) * (b.r1x - m) * b.rx) * m * b.u0n * b.v0n ≥
      5 * 64 * ((b.u0n * (b.ru - m) + (b.u0d - b.u0n) * (b.r1u - m)) * b.v0n +
              (b.v0n * (b.rv - m) + (b.v0d - b.v0n) * (b.r1v - m)) * b.u0n) * b.rx * b.r1x * xn
  )

private def gridBoxes : List BoxEntry := [
  ⟨1, 8, 1, 6, 1, 8, 1, 6, 105758, 100044, 103303, 100209, 103303, 100209⟩,
  ⟨1, 8, 1, 6, 1, 6, 2, 9, 105284, 100058, 102840, 100286, 103303, 100209⟩,
  ⟨1, 8, 1, 6, 2, 9, 3, 10, 104792, 100080, 102378, 100394, 103303, 100209⟩,
  ⟨1, 8, 1, 6, 3, 10, 2, 5, 104322, 100107, 101900, 100559, 103303, 100209⟩,
  ⟨1, 8, 1, 6, 2, 5, 1, 2, 103959, 100136, 101443, 100802, 103303, 100209⟩,
  ⟨1, 8, 1, 6, 1, 2, 3, 5, 103663, 100164, 101089, 101089, 103303, 100209⟩,
  ⟨1, 8, 1, 6, 3, 5, 2, 3, 103492, 100184, 100802, 101443, 103303, 100209⟩,
  ⟨1, 8, 1, 6, 2, 3, 3, 4, 103302, 100208, 100636, 101732, 103303, 100209⟩,
  ⟨1, 8, 1, 6, 3, 4, 4, 5, 103198, 100223, 100451, 102190, 103303, 100209⟩,
  ⟨1, 8, 1, 6, 4, 5, 5, 6, 103132, 100233, 100350, 102547, 103303, 100209⟩,
  ⟨1, 8, 1, 6, 5, 6, 7, 8, 103053, 100246, 100286, 102840, 103303, 100209⟩,
  ⟨1, 6, 2, 9, 1, 6, 2, 9, 104812, 100079, 102840, 100286, 102840, 100286⟩,
  ⟨1, 6, 2, 9, 2, 9, 3, 10, 104322, 100107, 102378, 100394, 102840, 100286⟩,
  ⟨1, 6, 2, 9, 3, 10, 2, 5, 103854, 100145, 101900, 100559, 102840, 100286⟩,
  ⟨1, 6, 2, 9, 2, 5, 1, 2, 103492, 100184, 101443, 100802, 102840, 100286⟩,
  ⟨1, 6, 2, 9, 1, 2, 3, 5, 103198, 100223, 101089, 101089, 102840, 100286⟩,
  ⟨1, 6, 2, 9, 3, 5, 2, 3, 103028, 100250, 100802, 101443, 102840, 100286⟩,
  ⟨1, 6, 2, 9, 2, 3, 3, 4, 102839, 100285, 100636, 101732, 102840, 100286⟩,
  ⟨1, 6, 2, 9, 3, 4, 4, 5, 102735, 100306, 100451, 102190, 102840, 100286⟩,
  ⟨1, 6, 2, 9, 4, 5, 5, 6, 102670, 100320, 100350, 102547, 102840, 100286⟩,
  ⟨1, 6, 2, 9, 5, 6, 7, 8, 102591, 100338, 100286, 102840, 102840, 100286⟩,
  ⟨2, 9, 3, 10, 2, 9, 3, 10, 103834, 100147, 102378, 100394, 102378, 100394⟩,
  ⟨2, 9, 3, 10, 3, 10, 2, 5, 103368, 100199, 101900, 100559, 102378, 100394⟩,
  ⟨2, 9, 3, 10, 2, 5, 1, 2, 103008, 100254, 101443, 100802, 102378, 100394⟩,
  ⟨2, 9, 3, 10, 1, 2, 3, 5, 102715, 100310, 101089, 101089, 102378, 100394⟩,
  ⟨2, 9, 3, 10, 3, 5, 2, 3, 102546, 100349, 100802, 101443, 102378, 100394⟩,
  ⟨2, 9, 3, 10, 2, 3, 3, 4, 102358, 100399, 100636, 101732, 102378, 100394⟩,
  ⟨2, 9, 3, 10, 3, 4, 4, 5, 102254, 100429, 100451, 102190, 102378, 100394⟩,
  ⟨2, 9, 3, 10, 4, 5, 5, 6, 102189, 100450, 100350, 102547, 102378, 100394⟩,
  ⟨2, 9, 3, 10, 5, 6, 7, 8, 102111, 100476, 100286, 102840, 102378, 100394⟩,
  ⟨3, 10, 2, 5, 3, 10, 2, 5, 102904, 100272, 101900, 100559, 101900, 100559⟩,
  ⟨3, 10, 2, 5, 2, 5, 1, 2, 102546, 100349, 101443, 100802, 101900, 100559⟩,
  ⟨3, 10, 2, 5, 1, 2, 3, 5, 102254, 100429, 101089, 101089, 101900, 100559⟩,
  ⟨3, 10, 2, 5, 3, 5, 2, 3, 102086, 100485, 100802, 101443, 101900, 100559⟩,
  ⟨3, 10, 2, 5, 2, 3, 3, 4, 101899, 100558, 100636, 101732, 101900, 100559⟩,
  ⟨3, 10, 2, 5, 3, 4, 4, 5, 101796, 100604, 100451, 102190, 101900, 100559⟩,
  ⟨3, 10, 2, 5, 4, 5, 5, 6, 101731, 100635, 100350, 102547, 101900, 100559⟩,
  ⟨3, 10, 2, 5, 5, 6, 7, 8, 101653, 100675, 100286, 102840, 101900, 100559⟩,
  ⟨2, 5, 1, 2, 2, 5, 1, 2, 102189, 100450, 101443, 100802, 101443, 100802⟩,
  ⟨2, 5, 1, 2, 1, 2, 3, 5, 101899, 100558, 101089, 101089, 101443, 100802⟩,
  ⟨2, 5, 1, 2, 3, 5, 2, 3, 101731, 100635, 100802, 101443, 101443, 100802⟩,
  ⟨2, 5, 1, 2, 2, 3, 3, 4, 101544, 100737, 100636, 101732, 101443, 100802⟩,
  ⟨2, 5, 1, 2, 3, 4, 4, 5, 101442, 100801, 100451, 102190, 101443, 100802⟩,
  ⟨2, 5, 1, 2, 4, 5, 5, 6, 101377, 100845, 100350, 102547, 101443, 100802⟩,
  ⟨2, 5, 1, 2, 5, 6, 7, 8, 101300, 100903, 100286, 102840, 101443, 100802⟩,
  ⟨1, 2, 3, 5, 1, 2, 3, 5, 101609, 100699, 101089, 101089, 101089, 101089⟩,
  ⟨1, 2, 3, 5, 3, 5, 2, 3, 101442, 100801, 100802, 101443, 101089, 101089⟩,
  ⟨1, 2, 3, 5, 2, 3, 3, 4, 101255, 100938, 100636, 101732, 101089, 101089⟩,
  ⟨1, 2, 3, 5, 3, 4, 4, 5, 101153, 101026, 100451, 102190, 101089, 101089⟩,
  ⟨1, 2, 3, 5, 4, 5, 5, 6, 101088, 101088, 100350, 102547, 101089, 101089⟩,
  ⟨1, 2, 3, 5, 5, 6, 7, 8, 101011, 101169, 100286, 102840, 101089, 101089⟩,
  ⟨3, 5, 2, 3, 3, 5, 2, 3, 101275, 100922, 100802, 101443, 100802, 101443⟩,
  ⟨3, 5, 2, 3, 2, 3, 3, 4, 101088, 101088, 100636, 101732, 100802, 101443⟩,
  ⟨3, 5, 2, 3, 3, 4, 4, 5, 100987, 101197, 100451, 102190, 100802, 101443⟩,
  ⟨3, 5, 2, 3, 4, 5, 5, 6, 100922, 101275, 100350, 102547, 100802, 101443⟩,
  ⟨3, 5, 2, 3, 5, 6, 7, 8, 100845, 101377, 100286, 102840, 100802, 101443⟩,
  ⟨2, 3, 3, 4, 2, 3, 3, 4, 100903, 101300, 100636, 101732, 100636, 101732⟩,
  ⟨2, 3, 3, 4, 3, 4, 4, 5, 100801, 101442, 100451, 102190, 100636, 101732⟩,
  ⟨2, 3, 3, 4, 4, 5, 5, 6, 100737, 101544, 100350, 102547, 100636, 101732⟩,
  ⟨2, 3, 3, 4, 5, 6, 7, 8, 100660, 101682, 100286, 102840, 100636, 101732⟩,
  ⟨3, 4, 4, 5, 3, 4, 4, 5, 100699, 101609, 100451, 102190, 100451, 102190⟩,
  ⟨3, 4, 4, 5, 4, 5, 5, 6, 100635, 101731, 100350, 102547, 100451, 102190⟩,
  ⟨3, 4, 4, 5, 5, 6, 7, 8, 100558, 101899, 100286, 102840, 100451, 102190⟩,
  ⟨4, 5, 5, 6, 4, 5, 5, 6, 100571, 101869, 100350, 102547, 100350, 102547⟩,
  ⟨4, 5, 5, 6, 5, 6, 7, 8, 100494, 102061, 100286, 102840, 100350, 102547⟩,
  ⟨5, 6, 7, 8, 5, 6, 7, 8, 100418, 102292, 100286, 102840, 100286, 102840⟩,
  ⟨3, 4, 25, 32, 7, 8, 29, 32, 100540, 101942, 100209, 103303, 100451, 102190⟩,
  ⟨3, 4, 25, 32, 29, 32, 15, 16, 100487, 102081, 100154, 103768, 100451, 102190⟩,
  ⟨25, 32, 13, 16, 7, 8, 29, 32, 100479, 102104, 100209, 103303, 100387, 102404⟩,
  ⟨25, 32, 13, 16, 29, 32, 15, 16, 100426, 102266, 100154, 103768, 100387, 102404⟩,
  ⟨13, 16, 27, 32, 7, 8, 29, 32, 100420, 102286, 100209, 103303, 100325, 102651⟩,
  ⟨13, 16, 27, 32, 29, 32, 15, 16, 100366, 102476, 100154, 103768, 100325, 102651⟩,
  ⟨27, 32, 7, 8, 7, 8, 29, 32, 100363, 102491, 100209, 103303, 100266, 102943⟩,
  ⟨27, 32, 7, 8, 29, 32, 15, 16, 100309, 102718, 100154, 103768, 100266, 102943⟩
]

private def pts1 : List (Nat × Nat) :=
  [(1,8),(1,6),(2,9),(3,10),(2,5),(1,2),(3,5),(2,3),(3,4),(4,5),(5,6),(7,8)]

private def ptsV : List (Nat × Nat) :=
  [(3,4),(25,32),(13,16),(27,32),(7,8)]

private def ptsU : List (Nat × Nat) :=
  [(7,8),(29,32),(15,16)]

private def adjPairs {α : Type} : List α → List (α × α)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: adjPairs (b :: rest)

private def withIdx {α : Type} (k : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (k, x) :: withIdx (k + 1) xs

private def hasBox (boxes : List BoxEntry) (v0 v1 u0 u1 : Nat × Nat) : Bool :=
  boxes.any (fun b =>
    decide (b.v0n = v0.1 ∧ b.v0d = v0.2 ∧ b.v1n = v1.1 ∧ b.v1d = v1.2 ∧
            b.u0n = u0.1 ∧ b.u0d = u0.2 ∧ b.u1n = u1.1 ∧ b.u1d = u1.2))

private def checkTri (boxes : List BoxEntry) (ps : List (Nat × Nat)) : Bool :=
  let pairs := withIdx 0 (adjPairs ps)
  pairs.all (fun iv =>
    pairs.all (fun ju =>
      if iv.1 ≤ ju.1 then hasBox boxes iv.2.1 iv.2.2 ju.2.1 ju.2.2 else true))

private def checkRect (boxes : List BoxEntry) (vs us : List (Nat × Nat)) : Bool :=
  (adjPairs vs).all (fun v =>
    (adjPairs us).all (fun u => hasBox boxes v.1 v.2 u.1 u.2))

private def isSortedPts : List (Nat × Nat) → Bool
  | [] => true
  | [p] => decide (0 < p.2)
  | p :: q :: rest => decide (0 < p.2 ∧ p.1 * q.2 < q.1 * p.2) && isSortedPts (q :: rest)

private theorem gridOk :
    (gridBoxes.all checkBox && checkTri gridBoxes pts1 && checkRect gridBoxes ptsV ptsU &&
     isSortedPts pts1 && isSortedPts ptsV && isSortedPts ptsU) = true := by
  decide

private theorem extra34_ok :
    (pow64 100450 * 3 ≤ 4 * ten64 ∧ pow64 102189 * 1 ≤ 4 * ten64 ∧
     8 * ten64 ≤ pow64 100209 * 7 ∧ 8 * ten64 ≤ pow64 103303 * 1 ∧
     pow64 100208 * 7 ≤ 8 * ten64 ∧ pow64 103302 * 1 ≤ 8 * ten64 ∧
     16 * ten64 ≤ pow64 100101 * 15 ∧ 16 * ten64 ≤ pow64 104428 * 1) := by
  decide

private theorem list_all_iff {α : Type} (p : α → Bool) :
    ∀ xs : List α, xs.all p = true ↔ ∀ x ∈ xs, p x = true
  | [] => by simp
  | x :: xs => by
    simp only [List.all_cons, Bool.and_eq_true, List.mem_cons]
    constructor
    · rintro ⟨hx, hxs⟩ y (rfl | hy)
      · exact hx
      · exact (list_all_iff p xs).mp hxs y hy
    · intro h
      exact ⟨h x (Or.inl rfl), (list_all_iff p xs).mpr (fun y hy => h y (Or.inr hy))⟩

private theorem list_any_iff {α : Type} (p : α → Bool) :
    ∀ xs : List α, xs.any p = true ↔ ∃ x ∈ xs, p x = true
  | [] => by simp
  | x :: xs => by
    simp only [List.any_cons, Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro (hx | hxs)
      · exact ⟨x, Or.inl rfl, hx⟩
      · obtain ⟨y, hy, hpy⟩ := (list_any_iff p xs).mp hxs
        exact ⟨y, Or.inr hy, hpy⟩
    · rintro ⟨y, rfl | hy, hpy⟩
      · exact Or.inl hpy
      · exact Or.inr ((list_any_iff p xs).mpr ⟨y, hy, hpy⟩)

private theorem withIdx_mem_snd {α : Type} :
    ∀ (k : Nat) (xs : List α) (i : Nat) (x : α), (i, x) ∈ withIdx k xs → x ∈ xs
  | _, [], _, _, h => by simp [withIdx] at h
  | k, hd :: tl, i, x, h => by
    simp only [withIdx, List.mem_cons] at h
    rcases h with heq | htl
    · injection heq with _ hx
      subst hx
      exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (withIdx_mem_snd (k + 1) tl i x htl))

private lemma pow64_eq (a : Nat) : pow64 a = a ^ 64 := by
  simp only [pow64]
  ring

private lemma pow_le_pow_nat {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := pow_le_pow_nat ha hab n
    have hb : 0 ≤ b := le_trans ha hab
    have hpow : 0 ≤ a ^ n := pow_nonneg ha n
    nlinarith

private noncomputable def negMulLog (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else -x * Real.log x

private noncomputable def binEnt (p : ℝ) : ℝ :=
  negMulLog p + negMulLog (1 - p)

private noncomputable def entRatio (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else binEnt x / x

private lemma negMulLog_zero : negMulLog 0 = 0 := by
  simp [negMulLog]

private lemma negMulLog_one : negMulLog 1 = 0 := by
  simp [negMulLog]

private lemma negMulLog_pos_eq {x : ℝ} (hx : 0 < x) : negMulLog x = -x * Real.log x := by
  simp [negMulLog, not_le.mpr hx]

private lemma negMulLog_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ negMulLog x := by
  by_cases h : x ≤ 0
  · simp [negMulLog, h]
  · have hxpos : 0 < x := lt_of_not_ge h
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hx0 hx1
    rw [negMulLog_pos_eq hxpos]
    nlinarith

private lemma binEnt_zero : binEnt 0 = 0 := by
  simp [binEnt, negMulLog_zero, negMulLog_one]

private lemma binEnt_one : binEnt 1 = 0 := by
  simp [binEnt, negMulLog_zero, negMulLog_one]

private lemma binEnt_symm (p : ℝ) : binEnt (1 - p) = binEnt p := by
  simp [binEnt, sub_sub_cancel, add_comm]

private lemma binEnt_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binEnt p :=
  add_nonneg (negMulLog_nonneg hp0 hp1) (negMulLog_nonneg (by linarith) (by linarith))

private lemma negMulLog_le_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    negMulLog x ≤ 1 - x := by
  by_cases h : x ≤ 0
  · have : x = 0 := le_antisymm h hx0
    subst this
    simp [negMulLog_zero]
  · have hxpos : 0 < x := lt_of_not_ge h
    rw [negMulLog_pos_eq hxpos]
    have hinv : Real.log x⁻¹ ≤ x⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hxpos)
    rw [Real.log_inv] at hinv
    have hmul := mul_le_mul_of_nonneg_left hinv hx0
    have hxx : x * x⁻¹ = 1 := by field_simp [ne_of_gt hxpos]
    nlinarith

private lemma entRatio_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    entRatio y ≤ entRatio x := by
  by_cases hy1 : y = 1
  · subst hy1
    simp only [entRatio, not_le.mpr (by norm_num : (0 : ℝ) < 1), not_le.mpr hx, ↓reduceIte,
      binEnt_one, zero_div]
    exact div_nonneg (binEnt_nonneg hx.le hy) hx.le
  · have hy_lt : y < 1 := lt_of_le_of_ne hy hy1
    have hypos : 0 < y := lt_of_lt_of_le hx hxy
    have h1x : 0 < 1 - x := by linarith
    have h1y : 0 < 1 - y := by linarith
    simp only [entRatio, not_le.mpr hx, not_le.mpr hypos, ↓reduceIte]
    have hle : y * binEnt x ≥ x * binEnt y := by
      simp only [binEnt, negMulLog_pos_eq hx, negMulLog_pos_eq hypos,
        negMulLog_pos_eq h1x, negMulLog_pos_eq h1y]
      have hlog1 : Real.log (x / y) ≤ x / y - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hx hypos)
      rw [Real.log_div (ne_of_gt hx) (ne_of_gt hypos)] at hlog1
      have hxy_mul : x * y * (Real.log x - Real.log y) ≤ x * y * (x / y - 1) :=
        mul_le_mul_of_nonneg_left hlog1 (mul_pos hx hypos).le
      have hxy_id : x * y * (x / y - 1) = x * (x - y) := by
        field_simp [ne_of_gt hypos]
        ring
      rw [hxy_id] at hxy_mul
      have hlog2 : Real.log ((1 - x) / (1 - y)) ≤ (1 - x) / (1 - y) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos h1x h1y)
      rw [Real.log_div (ne_of_gt h1x) (ne_of_gt h1y)] at hlog2
      have h1xy_mul : x * (1 - y) * (Real.log (1 - x) - Real.log (1 - y)) ≤
          x * (1 - y) * ((1 - x) / (1 - y) - 1) :=
        mul_le_mul_of_nonneg_left hlog2 (mul_pos hx h1y).le
      have h1xy_id : x * (1 - y) * ((1 - x) / (1 - y) - 1) = x * (y - x) := by
        field_simp [ne_of_gt h1y]
        ring
      rw [h1xy_id] at h1xy_mul
      have hlog1x : Real.log (1 - x) ≤ 0 := Real.log_nonpos h1x.le (by linarith)
      have h3 : 0 ≤ (y - x) * (-Real.log (1 - x)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    rw [← sub_nonneg]
    have hid : binEnt x / x - binEnt y / y = (y * binEnt x - x * binEnt y) / (x * y) := by
      field_simp [ne_of_gt hx, ne_of_gt hypos]
      ring
    rw [hid]
    exact div_nonneg (sub_nonneg.mpr hle) (mul_pos hx hypos).le

private lemma exp_one_gt : (25 / 10 : ℝ) < Real.exp 1 := by
  have h1 : (9 / 8 : ℝ) < Real.exp (1 / 8) := by
    have h := Real.add_one_lt_exp (by norm_num : (1 / 8 : ℝ) ≠ 0)
    linarith
  have h2 : (9 / 8 : ℝ) ^ 2 < Real.exp (1 / 4) := by
    have he : Real.exp (1 / 4 : ℝ) = Real.exp (1 / 8) * Real.exp (1 / 8) := by
      rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith
  have h4 : (9 / 8 : ℝ) ^ 4 < Real.exp (1 / 2) := by
    have he : Real.exp (1 / 2 : ℝ) = Real.exp (1 / 4) * Real.exp (1 / 4) := by
      rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 9 / 8) 2]
  have h8 : (9 / 8 : ℝ) ^ 8 < Real.exp 1 := by
    have he : Real.exp (1 : ℝ) = Real.exp (1 / 2) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 9 / 8) 4]
  linarith [show (25 / 10 : ℝ) < (9 / 8 : ℝ) ^ 8 by norm_num]

private lemma exp_one_lt : Real.exp 1 < (282 / 100 : ℝ) := by
  have h1 : (15 / 16 : ℝ) < Real.exp (-1 / 16) := by
    have h := Real.add_one_lt_exp (by norm_num : (-1 / 16 : ℝ) ≠ 0)
    linarith
  have h2 : (15 / 16 : ℝ) ^ 2 < Real.exp (-1 / 8) := by
    have he : Real.exp (-1 / 8 : ℝ) = Real.exp (-1 / 16) * Real.exp (-1 / 16) := by
      rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith
  have h4 : (15 / 16 : ℝ) ^ 4 < Real.exp (-1 / 4) := by
    have he : Real.exp (-1 / 4 : ℝ) = Real.exp (-1 / 8) * Real.exp (-1 / 8) := by
      rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 15 / 16) 2]
  have h8 : (15 / 16 : ℝ) ^ 8 < Real.exp (-1 / 2) := by
    have he : Real.exp (-1 / 2 : ℝ) = Real.exp (-1 / 4) * Real.exp (-1 / 4) := by
      rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 15 / 16) 4]
  have h16 : (15 / 16 : ℝ) ^ 16 < Real.exp (-1) := by
    have he : Real.exp (-1 : ℝ) = Real.exp (-1 / 2) * Real.exp (-1 / 2) := by
      rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 15 / 16) 8]
  have hlow : (100 / 282 : ℝ) < (Real.exp 1)⁻¹ := by
    rw [← Real.exp_neg]
    linarith [show (100 / 282 : ℝ) < (15 / 16 : ℝ) ^ 16 by norm_num]
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  have hmul := mul_lt_mul_of_pos_right hlow hexp
  have hid : (Real.exp 1)⁻¹ * Real.exp 1 = 1 := by field_simp [ne_of_gt hexp]
  rw [hid] at hmul
  linarith

private lemma two_le_log_eight : (2 : ℝ) ≤ Real.log 8 := by
  have hexp : Real.exp 2 < 8 := by
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he]
    have h1 := exp_one_lt
    have h0 : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith
  calc
    (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
    _ ≤ Real.log 8 := Real.log_le_log (Real.exp_pos 2) hexp.le

private lemma boppana_small_v {u v : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hv0 : 0 < v) (hv8 : v ≤ 1 / 8) :
    (5 / 8 : ℝ) * (u * binEnt v + v * binEnt u) ≤ binEnt (u * v) := by
  have huv0 : 0 < u * v := mul_pos hu0 hv0
  have huv1 : u * v < 1 := by nlinarith
  have hv1 : v < 1 := by linarith
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  have h1uv : 0 < 1 - u * v := by linarith
  simp only [binEnt, negMulLog_pos_eq hu0, negMulLog_pos_eq hv0, negMulLog_pos_eq huv0,
    negMulLog_pos_eq h1u, negMulLog_pos_eq h1v, negMulLog_pos_eq h1uv]
  rw [Real.log_mul (ne_of_gt hu0) (ne_of_gt hv0)]
  have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1.le
  have hlogv : Real.log v ≤ -Real.log 8 := by
    have hle : v ≤ (8 : ℝ)⁻¹ := by linarith
    calc
      Real.log v ≤ Real.log (8⁻¹) := Real.log_le_log hv0 hle
      _ = -Real.log 8 := Real.log_inv 8
  have hv_log : (2 : ℝ) ≤ -Real.log v := by linarith [two_le_log_eight]
  have hrem : (7 / 8 : ℝ) * (u * v) ≤ -(1 - u * v) * Real.log (1 - u * v) := by
    have hlog1uv : Real.log (1 - u * v) ≤ -u * v := by
      have h := Real.log_le_sub_one_of_pos h1uv
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlog1uv h1uv.le
    have h78 : (7 / 8 : ℝ) ≤ 1 - u * v := by nlinarith
    nlinarith
  have hgu : -(1 - u) * Real.log (1 - u) ≤ u := by
    have h := negMulLog_le_sub h1u.le hu1.le
    rw [negMulLog_pos_eq h1u] at h
    linarith
  have hgv : -(1 - v) * Real.log (1 - v) ≤ v := by
    have h := negMulLog_le_sub h1v.le hv1.le
    rw [negMulLog_pos_eq h1v] at h
    linarith
  have hlogv_sum : (3 / 8 : ℝ) * (u * v) * 2 ≤ (3 / 8 : ℝ) * (u * v) * (-Real.log v) :=
    mul_le_mul_of_nonneg_left hv_log (by positivity)
  have hlogu_nn : 0 ≤ (3 / 8 : ℝ) * (u * v) * (-Real.log u) :=
    mul_nonneg (by positivity) (by linarith)
  have hgu_mul : (5 / 8 : ℝ) * v * (-(1 - u) * Real.log (1 - u)) ≤ (5 / 8 : ℝ) * v * u :=
    mul_le_mul_of_nonneg_left hgu (by positivity)
  have hgv_mul : (5 / 8 : ℝ) * u * (-(1 - v) * Real.log (1 - v)) ≤ (5 / 8 : ℝ) * u * v :=
    mul_le_mul_of_nonneg_left hgv (by positivity)
  linarith

private lemma negMulLog_le_exp_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    -a * Real.log a ≤ -a * Real.log b + (2 / 5 : ℝ) * b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have he1 : 0 < Real.exp 1 := Real.exp_pos 1
  have hdiv : Real.log (b / (a * Real.exp 1)) ≤ b / (a * Real.exp 1) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hb (mul_pos ha he1))
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt (mul_pos ha he1)),
      Real.log_mul (ne_of_gt ha) (ne_of_gt he1), Real.log_exp] at hdiv
  have hmul : a * (Real.log b - Real.log a) ≤ b / Real.exp 1 := by
    have hm := mul_le_mul_of_nonneg_left hdiv ha.le
    have hid : a * (b / (a * Real.exp 1)) = b / Real.exp 1 := by
      field_simp [ne_of_gt ha, ne_of_gt he1]
    nlinarith
  have hexp : b / Real.exp 1 ≤ (2 / 5 : ℝ) * b := by
    have h25 := exp_one_gt
    have hid : (2 / 5 : ℝ) * b - b / Real.exp 1 = b * (2 * Real.exp 1 - 5) / (5 * Real.exp 1) := by
      field_simp [ne_of_gt he1]
      ring
    have hpos : 0 ≤ b * (2 * Real.exp 1 - 5) / (5 * Real.exp 1) :=
      div_nonneg (mul_nonneg hb.le (by linarith)) (by positivity)
    linarith
  nlinarith

private lemma log_one_add_bound {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + t) * Real.log (1 + t) ≤ (3 / 2 : ℝ) * t := by
  let s1 := Real.sqrt (1 + t)
  let s2 := Real.sqrt s1
  let s3 := Real.sqrt s2
  have hs1_pos : 0 < s1 := Real.sqrt_pos.mpr (by linarith)
  have hs2_pos : 0 < s2 := Real.sqrt_pos.mpr hs1_pos
  have hs3_pos : 0 < s3 := Real.sqrt_pos.mpr hs2_pos
  have hs1_sq : s1 ^ 2 = 1 + t := Real.sq_sqrt (by linarith)
  have hs2_sq : s2 ^ 2 = s1 := Real.sq_sqrt hs1_pos.le
  have hs3_sq : s3 ^ 2 = s2 := Real.sq_sqrt hs2_pos.le
  have hs3_pow : s3 ^ 8 = 1 + t := by
    calc
      s3 ^ 8 = ((s3 ^ 2) ^ 2) ^ 2 := by ring
      _ = (s2 ^ 2) ^ 2 := by rw [hs3_sq]
      _ = s1 ^ 2 := by rw [hs2_sq]
      _ = 1 + t := hs1_sq
  have hs3_ge1 : 1 ≤ s3 := by
    by_contra hlt
    have hlt' : s3 < 1 := lt_of_not_ge hlt
    have hs2_lt : s3 ^ 2 < 1 := by nlinarith
    have hs4_lt : s3 ^ 4 < 1 := by nlinarith
    have hs8_lt : s3 ^ 8 < 1 := by nlinarith
    linarith
  have hs3_le2 : s3 ^ 8 ≤ 2 := by linarith
  have hlog : Real.log (1 + t) ≤ 8 * (s3 - 1) := by
    rw [← hs3_pow, Real.log_pow]
    have h := Real.log_le_sub_one_of_pos hs3_pos
    norm_num at *
    linarith
  have hpoly : 16 * s3 ^ 8 ≤
      3 * (1 + s3 + s3 ^ 2 + s3 ^ 3 + s3 ^ 4 + s3 ^ 5 + s3 ^ 6 + s3 ^ 7) := by
    by_cases h1 : s3 ≤ 104 / 100
    · have hp : s3 ^ 8 ≤ (104 / 100 : ℝ) ^ 8 := pow_le_pow_nat hs3_pos.le h1 8
      have hnum : 16 * (104 / 100 : ℝ) ^ 8 ≤ 24 := by norm_num
      have p2 : 1 ≤ s3 ^ 2 := by have h := pow_le_pow_nat zero_le_one hs3_ge1 2; simpa using h
      have p3 : 1 ≤ s3 ^ 3 := by have h := pow_le_pow_nat zero_le_one hs3_ge1 3; simpa using h
      have p4 : 1 ≤ s3 ^ 4 := by have h := pow_le_pow_nat zero_le_one hs3_ge1 4; simpa using h
      have p5 : 1 ≤ s3 ^ 5 := by have h := pow_le_pow_nat zero_le_one hs3_ge1 5; simpa using h
      have p6 : 1 ≤ s3 ^ 6 := by have h := pow_le_pow_nat zero_le_one hs3_ge1 6; simpa using h
      have p7 : 1 ≤ s3 ^ 7 := by have h := pow_le_pow_nat zero_le_one hs3_ge1 7; simpa using h
      linarith
    · by_cases h2 : s3 ≤ 1085 / 1000
      · have hgt : (104 / 100 : ℝ) ≤ s3 := le_of_not_ge h1
        have hp : s3 ^ 8 ≤ (1085 / 1000 : ℝ) ^ 8 := pow_le_pow_nat hs3_pos.le h2 8
        have p1 : (104 / 100 : ℝ) ≤ s3 := hgt
        have p2 : (104 / 100 : ℝ) ^ 2 ≤ s3 ^ 2 := pow_le_pow_nat (by norm_num) hgt 2
        have p3 : (104 / 100 : ℝ) ^ 3 ≤ s3 ^ 3 := pow_le_pow_nat (by norm_num) hgt 3
        have p4 : (104 / 100 : ℝ) ^ 4 ≤ s3 ^ 4 := pow_le_pow_nat (by norm_num) hgt 4
        have p5 : (104 / 100 : ℝ) ^ 5 ≤ s3 ^ 5 := pow_le_pow_nat (by norm_num) hgt 5
        have p6 : (104 / 100 : ℝ) ^ 6 ≤ s3 ^ 6 := pow_le_pow_nat (by norm_num) hgt 6
        have p7 : (104 / 100 : ℝ) ^ 7 ≤ s3 ^ 7 := pow_le_pow_nat (by norm_num) hgt 7
        norm_num at *
        linarith
      · have hgt : (1085 / 1000 : ℝ) ≤ s3 := le_of_not_ge h2
        have p1 : (1085 / 1000 : ℝ) ≤ s3 := hgt
        have p2 : (1085 / 1000 : ℝ) ^ 2 ≤ s3 ^ 2 := pow_le_pow_nat (by norm_num) hgt 2
        have p3 : (1085 / 1000 : ℝ) ^ 3 ≤ s3 ^ 3 := pow_le_pow_nat (by norm_num) hgt 3
        have p4 : (1085 / 1000 : ℝ) ^ 4 ≤ s3 ^ 4 := pow_le_pow_nat (by norm_num) hgt 4
        have p5 : (1085 / 1000 : ℝ) ^ 5 ≤ s3 ^ 5 := pow_le_pow_nat (by norm_num) hgt 5
        have p6 : (1085 / 1000 : ℝ) ^ 6 ≤ s3 ^ 6 := pow_le_pow_nat (by norm_num) hgt 6
        have p7 : (1085 / 1000 : ℝ) ^ 7 ≤ s3 ^ 7 := pow_le_pow_nat (by norm_num) hgt 7
        norm_num at *
        linarith
  have hmul_s : 16 * s3 ^ 8 * (s3 - 1) ≤ 3 * (s3 ^ 8 - 1) := by
    have hfac : (s3 - 1) * (1 + s3 + s3 ^ 2 + s3 ^ 3 + s3 ^ 4 + s3 ^ 5 + s3 ^ 6 + s3 ^ 7) =
        s3 ^ 8 - 1 := by ring
    have hs3_sub : 0 ≤ s3 - 1 := by linarith
    have hm := mul_le_mul_of_nonneg_left hpoly hs3_sub
    nlinarith
  have h16 : (1 + t) * 8 * (s3 - 1) ≤ (3 / 2 : ℝ) * t := by
    rw [← hs3_pow]
    linarith
  have hm := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 1 + t)
  linarith

private lemma boppana_large_uv {u v : ℝ} (hv : 7 / 8 ≤ v) (hvu : v ≤ u) (hu1 : u < 1) :
    (5 / 8 : ℝ) * (u * binEnt v + v * binEnt u) ≤ binEnt (u * v) := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have huv0 : 0 < u * v := mul_pos hu0 hv0
  have huv1 : u * v < 1 := by nlinarith
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  have h1uv : 0 < 1 - u * v := by linarith
  let a := 1 - u
  let b := 1 - v
  have ha0 : 0 < a := h1u
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hb8 : b ≤ 1 / 8 := by dsimp [b]; linarith
  have h1uv_eq : 1 - u * v = b + a * u := by dsimp [a, b]; ring
  have ht0 : 0 ≤ a * u / b := div_nonneg (mul_nonneg ha0.le hu0.le) h1v.le
  have ht1 : a * u / b ≤ 1 := by
    have hid : 1 - a * u / b = (b - a * u) / b := by field_simp [ne_of_gt h1v]
    have hnonneg : 0 ≤ (b - a * u) / b := div_nonneg (by nlinarith) h1v.le
    linarith
  have hlog_add : (b + a * u) * Real.log (1 + a * u / b) ≤ (3 / 2 : ℝ) * (a * u) := by
    have hb_pos : 0 < b := h1v
    have h := log_one_add_bound ht0 ht1
    have hm := mul_le_mul_of_nonneg_left h hb_pos.le
    have hid1 : b * (1 + a * u / b) = b + a * u := by field_simp [ne_of_gt hb_pos]
    have hid2 : b * ((3 / 2 : ℝ) * (a * u / b)) = (3 / 2 : ℝ) * (a * u) := by
      field_simp [ne_of_gt hb_pos]
    nlinarith
  have hlog_1uv : (b + a * u) * Real.log (b + a * u) =
      (b + a * u) * Real.log b + (b + a * u) * Real.log (1 + a * u / b) := by
    have hb_pos : 0 < b := h1v
    have h1t : 0 < 1 + a * u / b := by linarith
    have heq : b + a * u = b * (1 + a * u / b) := by field_simp [ne_of_gt hb_pos]
    rw [heq, Real.log_mul (ne_of_gt hb_pos) (ne_of_gt h1t)]
    ring
  have hga : -a * Real.log a ≤ -a * Real.log b + (2 / 5 : ℝ) * b :=
    negMulLog_le_exp_bound ha0 hab
  have hlogb : (2 : ℝ) ≤ -Real.log b := by
    have hle : b ≤ (8 : ℝ)⁻¹ := by linarith
    have h := Real.log_le_log h1v hle
    rw [Real.log_inv] at h
    linarith [two_le_log_eight]
  have hlogu_lb : a ≤ -Real.log u := by
    have h := Real.log_le_sub_one_of_pos hu0
    dsimp [a]
    linarith
  have hlogv_lb : b ≤ -Real.log v := by
    have h := Real.log_le_sub_one_of_pos hv0
    dsimp [b]
    linarith
  simp only [binEnt, negMulLog_pos_eq hu0, negMulLog_pos_eq hv0, negMulLog_pos_eq huv0,
    negMulLog_pos_eq h1u, negMulLog_pos_eq h1v, negMulLog_pos_eq h1uv]
  rw [Real.log_mul (ne_of_gt hu0) (ne_of_gt hv0), h1uv_eq]
  change (5 / 8 : ℝ) * (u * (-v * Real.log v + -b * Real.log b) +
      v * (-u * Real.log u + -a * Real.log a)) ≤
    -(u * v) * (Real.log u + Real.log v) + -(b + a * u) * Real.log (b + a * u)
  have hcoeff : (0 : ℝ) ≤ b + a * u - (5 / 8 : ℝ) * u * b - (5 / 8 : ℝ) * v * a := by
    have huv_eq : u = 1 - a := by dsimp [a]; ring
    have hvv_eq : v = 1 - b := by dsimp [b]; ring
    nlinarith
  have huv_ge : (49 / 64 : ℝ) ≤ u * v := by nlinarith
  have hcoeff_mul : 2 * (b + a * u - (5 / 8 : ℝ) * u * b - (5 / 8 : ℝ) * v * a) ≤
      (-Real.log b) * (b + a * u - (5 / 8 : ℝ) * u * b - (5 / 8 : ℝ) * v * a) :=
    mul_le_mul_of_nonneg_right hlogb hcoeff
  have hga_mul : (5 / 8 : ℝ) * v * (-a * Real.log a) ≤
      (5 / 8 : ℝ) * v * (-a * Real.log b + (2 / 5 : ℝ) * b) :=
    mul_le_mul_of_nonneg_left hga (by positivity)
  have hrem_ab : (147 / 512 : ℝ) * (a + b) ≤ (3 / 8 : ℝ) * (u * v) * (-Real.log u - Real.log v) := by
    have h1 : (a + b) ≤ -Real.log u - Real.log v := by linarith
    have h2 : (147 / 512 : ℝ) ≤ (3 / 8 : ℝ) * (u * v) := by linarith
    nlinarith
  have hquad : 2 * (b + a * u - (5 / 8 : ℝ) * u * b - (5 / 8 : ℝ) * v * a) +
      (147 / 512 : ℝ) * (a + b) - (3 / 2 : ℝ) * (a * u) - (5 / 8 : ℝ) * v * ((2 / 5 : ℝ) * b) ≥ 0 := by
    have huv_eq : u = 1 - a := by dsimp [a]; ring
    have hvv_eq : v = 1 - b := by dsimp [b]; ring
    rw [huv_eq, hvv_eq]
    nlinarith
  linarith

private lemma log_lo_of_pow64 {n d r : Nat} (hn : 0 < n) (hd : 0 < d) (hr : 100000 < r)
    (hpow : pow64 r * d ≤ n * ten64) :
    (64 : ℝ) * ((r : ℝ) - 100000) / (r : ℝ) ≤ Real.log ((n : ℝ) / (d : ℝ)) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
  have hdpos : (0 : ℝ) < (d : ℝ) := by positivity
  have hdiv : ((r : ℝ) / 100000) ^ 64 ≤ (n : ℝ) / (d : ℝ) := by
    have hnat : ((r ^ 64 * d : Nat) : ℝ) ≤ ((n * 100000 ^ 64 : Nat) : ℝ) := by
      exact_mod_cast (by simpa [pow64_eq, ten64] using hpow)
    push_cast at hnat
    have hid : (n : ℝ) / (d : ℝ) - ((r : ℝ) / 100000) ^ 64 =
        ((n : ℝ) * (100000 : ℝ) ^ 64 - (r : ℝ) ^ 64 * (d : ℝ)) / ((d : ℝ) * (100000 : ℝ) ^ 64) := by
      field_simp [ne_of_gt hdpos]
      ring
    have hnonneg : 0 ≤ ((n : ℝ) * (100000 : ℝ) ^ 64 - (r : ℝ) ^ 64 * (d : ℝ)) /
        ((d : ℝ) * (100000 : ℝ) ^ 64) :=
      div_nonneg (sub_nonneg.mpr hnat) (by positivity)
    linarith
  have hlog : (64 : ℝ) * Real.log ((r : ℝ) / 100000) ≤ Real.log ((n : ℝ) / (d : ℝ)) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (pow_pos (by positivity) 64) hdiv
  have hsub : ((r : ℝ) - 100000) / (r : ℝ) ≤ Real.log ((r : ℝ) / 100000) := by
    have hinv := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 100000 / (r : ℝ))
    have hleq : Real.log ((100000 : ℝ) / (r : ℝ)) = -Real.log ((r : ℝ) / 100000) := by
      rw [Real.log_div (by norm_num) (ne_of_gt hrpos),
          Real.log_div (ne_of_gt hrpos) (by norm_num)]
      ring
    rw [hleq] at hinv
    have hmul := mul_le_mul_of_nonneg_left hinv hrpos.le
    have hdiv_id : (r : ℝ) * ((100000 : ℝ) / (r : ℝ) - 1) = 100000 - (r : ℝ) := by
      field_simp [ne_of_gt hrpos]
    rw [hdiv_id] at hmul
    have hid2 : Real.log ((r : ℝ) / 100000) - ((r : ℝ) - 100000) / (r : ℝ) =
        ((r : ℝ) * Real.log ((r : ℝ) / 100000) - ((r : ℝ) - 100000)) / (r : ℝ) := by
      field_simp [ne_of_gt hrpos]
    have hnn : 0 ≤ ((r : ℝ) * Real.log ((r : ℝ) / 100000) - ((r : ℝ) - 100000)) / (r : ℝ) :=
      div_nonneg (by linarith) hrpos.le
    linarith
  linarith

private lemma log_hi_of_pow64 {n d r : Nat} (hn : 0 < n) (hd : 0 < d) (hr : 100000 ≤ r)
    (hpow : n * ten64 ≤ pow64 r * d) :
    Real.log ((n : ℝ) / (d : ℝ)) ≤ (64 : ℝ) * ((r : ℝ) - 100000) / 100000 := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hdiv : (n : ℝ) / (d : ℝ) ≤ ((r : ℝ) / 100000) ^ 64 := by
    have hnat : ((n * 100000 ^ 64 : Nat) : ℝ) ≤ ((r ^ 64 * d : Nat) : ℝ) := by
      exact_mod_cast (by simpa [pow64_eq, ten64] using hpow)
    push_cast at hnat
    have hid : ((r : ℝ) / 100000) ^ 64 - (n : ℝ) / (d : ℝ) =
        ((r : ℝ) ^ 64 * (d : ℝ) - (n : ℝ) * (100000 : ℝ) ^ 64) / ((d : ℝ) * (100000 : ℝ) ^ 64) := by
      field_simp [ne_of_gt hdpos]
      ring
    have hnonneg : 0 ≤ ((r : ℝ) ^ 64 * (d : ℝ) - (n : ℝ) * (100000 : ℝ) ^ 64) /
        ((d : ℝ) * (100000 : ℝ) ^ 64) :=
      div_nonneg (sub_nonneg.mpr hnat) (by positivity)
    linarith
  have hlog : Real.log ((n : ℝ) / (d : ℝ)) ≤ (64 : ℝ) * Real.log ((r : ℝ) / 100000) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (div_pos hnpos hdpos) hdiv
  have hsub := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (r : ℝ) / 100000)
  have hmul : (64 : ℝ) * Real.log ((r : ℝ) / 100000) ≤
      (64 : ℝ) * ((r : ℝ) - 100000) / 100000 := by
    linarith
  exact hlog.trans hmul

private lemma entRatio_rat_eq {n d : Nat} (hn : 0 < n) (hnd : n < d) :
    entRatio ((n : ℝ) / (d : ℝ)) =
      Real.log ((d : ℝ) / (n : ℝ)) +
        (((d - n : Nat) : ℝ) / (n : ℝ)) * Real.log ((d : ℝ) / ((d - n : Nat) : ℝ)) := by
  have hd : 0 < d := lt_trans hn hnd
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hdR : (0 : ℝ) < (d : ℝ) := by positivity
  have hdn : 0 < d - n := Nat.sub_pos_of_lt hnd
  have hdnR : (0 : ℝ) < ((d - n : Nat) : ℝ) := by positivity
  have hsub : (1 : ℝ) - (n : ℝ) / (d : ℝ) = ((d - n : Nat) : ℝ) / (d : ℝ) := by
    rw [Nat.cast_sub hnd.le]
    field_simp [ne_of_gt hdR]
  have hx : (0 : ℝ) < (n : ℝ) / (d : ℝ) := div_pos hnR hdR
  have h1x : (0 : ℝ) < 1 - (n : ℝ) / (d : ℝ) := by rw [hsub]; exact div_pos hdnR hdR
  simp only [entRatio, not_le.mpr hx, ↓reduceIte, binEnt, negMulLog_pos_eq hx,
    negMulLog_pos_eq h1x]
  rw [hsub, Real.log_div (ne_of_gt hnR) (ne_of_gt hdR),
      Real.log_div (ne_of_gt hdR) (ne_of_gt hnR),
      Real.log_div (ne_of_gt hdnR) (ne_of_gt hdR),
      Real.log_div (ne_of_gt hdR) (ne_of_gt hdnR)]
  field_simp [ne_of_gt hnR, ne_of_gt hdR, ne_of_gt hdnR]
  ring

private lemma boppana_box (b : BoxEntry) (hb : checkBox b = true)
    {u v : ℝ} (hv0 : (b.v0n : ℝ) / b.v0d ≤ v) (hv1 : v ≤ (b.v1n : ℝ) / b.v1d)
    (hu0 : (b.u0n : ℝ) / b.u0d ≤ u) (hu1 : u ≤ (b.u1n : ℝ) / b.u1d) :
    (5 / 8 : ℝ) * (entRatio u + entRatio v) ≤ entRatio (u * v) := by
  simp only [checkBox, decide_eq_true_eq] at hb
  rcases hb with ⟨hv0n, hv0d, hv1d, hu0n, hu0d, hu1d, hxn, hxd,
    hrx, hr1x, hru, hr1u, hrv, hr1v, hpx, hp1x, hpu, hp1u, hpv, hp1v, hmain⟩
  have hv1n : 0 < b.v1n := Nat.pos_of_mul_pos_left hxn
  have hu1n : 0 < b.u1n := Nat.pos_of_mul_pos_right hxn
  have hv0d_pos : 0 < b.v0d := lt_trans hv0n hv0d
  have hv1d_pos : 0 < b.v1d := lt_trans hv1n hv1d
  have hu0d_pos : 0 < b.u0d := lt_trans hu0n hu0d
  have hu1d_pos : 0 < b.u1d := lt_trans hu1n hu1d
  have hv0_pos : (0 : ℝ) < (b.v0n : ℝ) / b.v0d := by positivity
  have hu0_pos : (0 : ℝ) < (b.u0n : ℝ) / b.u0d := by positivity
  have hv1_lt1 : (b.v1n : ℝ) / b.v1d ≤ 1 := by
    have hid : 1 - (b.v1n : ℝ) / b.v1d = ((b.v1d : ℝ) - b.v1n) / b.v1d := by
      field_simp [show (b.v1d : ℝ) ≠ 0 by positivity]
    have hle : (b.v1n : ℝ) ≤ b.v1d := by exact_mod_cast hv1d.le
    have hnn : 0 ≤ ((b.v1d : ℝ) - b.v1n) / b.v1d := div_nonneg (by linarith) (by positivity)
    linarith
  have hu1_lt1 : (b.u1n : ℝ) / b.u1d ≤ 1 := by
    have hid : 1 - (b.u1n : ℝ) / b.u1d = ((b.u1d : ℝ) - b.u1n) / b.u1d := by
      field_simp [show (b.u1d : ℝ) ≠ 0 by positivity]
    have hle : (b.u1n : ℝ) ≤ b.u1d := by exact_mod_cast hu1d.le
    have hnn : 0 ≤ ((b.u1d : ℝ) - b.u1n) / b.u1d := div_nonneg (by linarith) (by positivity)
    linarith
  have hv_pos : 0 < v := lt_of_lt_of_le hv0_pos hv0
  have hu_pos : 0 < u := lt_of_lt_of_le hu0_pos hu0
  have huv_pos : 0 < u * v := mul_pos hu_pos hv_pos
  have huv_le : u * v ≤ ((b.u1n * b.v1n : Nat) : ℝ) / ((b.u1d * b.v1d : Nat) : ℝ) := by
    push_cast
    rw [mul_div_mul_comm]
    exact mul_le_mul hu1 hv1 hv_pos.le (by positivity)
  have hprod_le1 : ((b.u1n * b.v1n : Nat) : ℝ) / ((b.u1d * b.v1d : Nat) : ℝ) ≤ 1 := by
    have hle : ((b.u1n * b.v1n : Nat) : ℝ) ≤ ((b.u1d * b.v1d : Nat) : ℝ) := by
      exact_mod_cast hxd.le
    have hden : (0 : ℝ) < ((b.u1d * b.v1d : Nat) : ℝ) := by positivity
    have hid : 1 - ((b.u1n * b.v1n : Nat) : ℝ) / ((b.u1d * b.v1d : Nat) : ℝ) =
        (((b.u1d * b.v1d : Nat) : ℝ) - ((b.u1n * b.v1n : Nat) : ℝ)) /
          ((b.u1d * b.v1d : Nat) : ℝ) := by
      field_simp [ne_of_gt hden]
    have hnn : 0 ≤ (((b.u1d * b.v1d : Nat) : ℝ) - ((b.u1n * b.v1n : Nat) : ℝ)) /
        ((b.u1d * b.v1d : Nat) : ℝ) := div_nonneg (by linarith) hden.le
    linarith
  have hf_uv : entRatio (((b.u1n * b.v1n : Nat) : ℝ) / ((b.u1d * b.v1d : Nat) : ℝ)) ≤
      entRatio (u * v) :=
    entRatio_antitone huv_pos huv_le hprod_le1
  have hf_u : entRatio u ≤ entRatio ((b.u0n : ℝ) / b.u0d) :=
    entRatio_antitone hu0_pos hu0 (hu1.trans hu1_lt1)
  have hf_v : entRatio v ≤ entRatio ((b.v0n : ℝ) / b.v0d) :=
    entRatio_antitone hv0_pos hv0 (hv1.trans hv1_lt1)
  let xn := b.u1n * b.v1n
  let xd := b.u1d * b.v1d
  have hxd_pos : 0 < xd := Nat.pos_of_lt hxd
  have hxd_sub : 0 < xd - xn := Nat.sub_pos_of_lt hxd
  have hlx := log_lo_of_pow64 hxd_pos hxn hrx hpx
  have hl1x := log_lo_of_pow64 hxd_pos hxd_sub hr1x hp1x
  have hlu := log_hi_of_pow64 hu0d_pos hu0n hru hpu
  have hl1u := log_hi_of_pow64 hu0d_pos (Nat.sub_pos_of_lt hu0d) hr1u hp1u
  have hlv := log_hi_of_pow64 hv0d_pos hv0n hrv hpv
  have hl1v := log_hi_of_pow64 hv0d_pos (Nat.sub_pos_of_lt hv0d) hr1v hp1v
  rw [entRatio_rat_eq hxn hxd] at hf_uv
  rw [entRatio_rat_eq hu0n hu0d] at hf_u
  rw [entRatio_rat_eq hv0n hv0d] at hf_v
  have hflo_lb : (64 : ℝ) * (((b.rx : ℝ) - 100000) * (b.r1x : ℝ) * (xn : ℝ) +
      ((xd - xn : Nat) : ℝ) * ((b.r1x : ℝ) - 100000) * (b.rx : ℝ)) /
      ((b.rx : ℝ) * (b.r1x : ℝ) * (xn : ℝ)) ≤
      Real.log ((xd : ℝ) / (xn : ℝ)) +
      (((xd - xn : Nat) : ℝ) / (xn : ℝ)) * Real.log ((xd : ℝ) / ((xd - xn : Nat) : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hl1x (div_nonneg (by positivity) (by positivity))
    have hadd := add_le_add hlx hmul
    have hid : (64 : ℝ) * (((b.rx : ℝ) - 100000) * (b.r1x : ℝ) * (xn : ℝ) +
        ((xd - xn : Nat) : ℝ) * ((b.r1x : ℝ) - 100000) * (b.rx : ℝ)) /
        ((b.rx : ℝ) * (b.r1x : ℝ) * (xn : ℝ)) =
        (64 : ℝ) * ((b.rx : ℝ) - 100000) / (b.rx : ℝ) +
        (((xd - xn : Nat) : ℝ) / (xn : ℝ)) *
          ((64 : ℝ) * ((b.r1x : ℝ) - 100000) / (b.r1x : ℝ)) := by
      field_simp [show (b.rx : ℝ) ≠ 0 by positivity,
        show (b.r1x : ℝ) ≠ 0 by positivity, show (xn : ℝ) ≠ 0 by positivity]
      ring
    linarith
  have hfhiu_ub : Real.log ((b.u0d : ℝ) / (b.u0n : ℝ)) +
      (((b.u0d - b.u0n : Nat) : ℝ) / (b.u0n : ℝ)) *
        Real.log ((b.u0d : ℝ) / ((b.u0d - b.u0n : Nat) : ℝ)) ≤
      (64 : ℝ) * ((b.u0n : ℝ) * ((b.ru : ℝ) - 100000) +
        ((b.u0d - b.u0n : Nat) : ℝ) * ((b.r1u : ℝ) - 100000)) /
        (100000 * (b.u0n : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hl1u (div_nonneg (by positivity) (by positivity))
    have hadd := add_le_add hlu hmul
    have hid : (64 : ℝ) * ((b.u0n : ℝ) * ((b.ru : ℝ) - 100000) +
        ((b.u0d - b.u0n : Nat) : ℝ) * ((b.r1u : ℝ) - 100000)) /
        (100000 * (b.u0n : ℝ)) =
        (64 : ℝ) * ((b.ru : ℝ) - 100000) / 100000 +
        (((b.u0d - b.u0n : Nat) : ℝ) / (b.u0n : ℝ)) *
          ((64 : ℝ) * ((b.r1u : ℝ) - 100000) / 100000) := by
      field_simp [show (b.u0n : ℝ) ≠ 0 by positivity]
      ring
    linarith
  have hfhiv_ub : Real.log ((b.v0d : ℝ) / (b.v0n : ℝ)) +
      (((b.v0d - b.v0n : Nat) : ℝ) / (b.v0n : ℝ)) *
        Real.log ((b.v0d : ℝ) / ((b.v0d - b.v0n : Nat) : ℝ)) ≤
      (64 : ℝ) * ((b.v0n : ℝ) * ((b.rv : ℝ) - 100000) +
        ((b.v0d - b.v0n : Nat) : ℝ) * ((b.r1v : ℝ) - 100000)) /
        (100000 * (b.v0n : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hl1v (div_nonneg (by positivity) (by positivity))
    have hadd := add_le_add hlv hmul
    have hid : (64 : ℝ) * ((b.v0n : ℝ) * ((b.rv : ℝ) - 100000) +
        ((b.v0d - b.v0n : Nat) : ℝ) * ((b.r1v : ℝ) - 100000)) /
        (100000 * (b.v0n : ℝ)) =
        (64 : ℝ) * ((b.rv : ℝ) - 100000) / 100000 +
        (((b.v0d - b.v0n : Nat) : ℝ) / (b.v0n : ℝ)) *
          ((64 : ℝ) * ((b.r1v : ℝ) - 100000) / 100000) := by
      field_simp [show (b.v0n : ℝ) ≠ 0 by positivity]
      ring
    linarith
  have hmainR : (5 : ℝ) * 64 * (((b.u0n : ℝ) * ((b.ru : ℝ) - 100000) +
      ((b.u0d - b.u0n : Nat) : ℝ) * ((b.r1u : ℝ) - 100000)) * (b.v0n : ℝ) +
      ((b.v0n : ℝ) * ((b.rv : ℝ) - 100000) +
      ((b.v0d - b.v0n : Nat) : ℝ) * ((b.r1v : ℝ) - 100000)) * (b.u0n : ℝ)) *
      (b.rx : ℝ) * (b.r1x : ℝ) * (xn : ℝ) ≤
      8 * 64 * (((b.rx : ℝ) - 100000) * (b.r1x : ℝ) * (xn : ℝ) +
      ((xd - xn : Nat) : ℝ) * ((b.r1x : ℝ) - 100000) * (b.rx : ℝ)) *
      100000 * (b.u0n : ℝ) * (b.v0n : ℝ) := by
    have hnat : ((5 * 64 * ((b.u0n * (b.ru - 100000) + (b.u0d - b.u0n) * (b.r1u - 100000)) * b.v0n +
        (b.v0n * (b.rv - 100000) + (b.v0d - b.v0n) * (b.r1v - 100000)) * b.u0n) *
        b.rx * b.r1x * xn : Nat) : ℝ) ≤
        ((8 * 64 * ((b.rx - 100000) * b.r1x * xn + (xd - xn) * (b.r1x - 100000) * b.rx) *
        100000 * b.u0n * b.v0n : Nat) : ℝ) := by exact_mod_cast hmain
    have c1 : ((b.rx - 100000 : Nat) : ℝ) = (b.rx : ℝ) - 100000 := by rw [Nat.cast_sub hrx.le]; norm_num
    have c2 : ((b.r1x - 100000 : Nat) : ℝ) = (b.r1x : ℝ) - 100000 := by rw [Nat.cast_sub hr1x.le]; norm_num
    have c3 : ((b.ru - 100000 : Nat) : ℝ) = (b.ru : ℝ) - 100000 := by rw [Nat.cast_sub hru]; norm_num
    have c4 : ((b.r1u - 100000 : Nat) : ℝ) = (b.r1u : ℝ) - 100000 := by rw [Nat.cast_sub hr1u]; norm_num
    have c5 : ((b.rv - 100000 : Nat) : ℝ) = (b.rv : ℝ) - 100000 := by rw [Nat.cast_sub hrv]; norm_num
    have c6 : ((b.r1v - 100000 : Nat) : ℝ) = (b.r1v : ℝ) - 100000 := by rw [Nat.cast_sub hr1v]; norm_num
    have c7 : ((b.u0d - b.u0n : Nat) : ℝ) = (b.u0d : ℝ) - (b.u0n : ℝ) := Nat.cast_sub hu0d.le
    have c8 : ((b.v0d - b.v0n : Nat) : ℝ) = (b.v0d : ℝ) - (b.v0n : ℝ) := Nat.cast_sub hv0d.le
    have c9 : ((xd - xn : Nat) : ℝ) = (xd : ℝ) - (xn : ℝ) := Nat.cast_sub hxd.le
    push_cast at hnat
    rw [c1, c2, c3, c4, c5, c6, c7, c8, c9] at hnat
    rw [c7, c8, c9]
    linarith
  have hcomb : (5 / 8 : ℝ) * (
      (64 : ℝ) * ((b.u0n : ℝ) * ((b.ru : ℝ) - 100000) +
        ((b.u0d - b.u0n : Nat) : ℝ) * ((b.r1u : ℝ) - 100000)) / (100000 * (b.u0n : ℝ)) +
      (64 : ℝ) * ((b.v0n : ℝ) * ((b.rv : ℝ) - 100000) +
        ((b.v0d - b.v0n : Nat) : ℝ) * ((b.r1v : ℝ) - 100000)) / (100000 * (b.v0n : ℝ))) ≤
      (64 : ℝ) * (((b.rx : ℝ) - 100000) * (b.r1x : ℝ) * (xn : ℝ) +
        ((xd - xn : Nat) : ℝ) * ((b.r1x : ℝ) - 100000) * (b.rx : ℝ)) /
        ((b.rx : ℝ) * (b.r1x : ℝ) * (xn : ℝ)) := by
    rw [← sub_nonneg]
    have hfrac : (64 : ℝ) * (((b.rx : ℝ) - 100000) * (b.r1x : ℝ) * (xn : ℝ) +
          ((xd - xn : Nat) : ℝ) * ((b.r1x : ℝ) - 100000) * (b.rx : ℝ)) /
          ((b.rx : ℝ) * (b.r1x : ℝ) * (xn : ℝ)) -
        (5 / 8 : ℝ) * (
          (64 : ℝ) * ((b.u0n : ℝ) * ((b.ru : ℝ) - 100000) +
            ((b.u0d - b.u0n : Nat) : ℝ) * ((b.r1u : ℝ) - 100000)) / (100000 * (b.u0n : ℝ)) +
          (64 : ℝ) * ((b.v0n : ℝ) * ((b.rv : ℝ) - 100000) +
            ((b.v0d - b.v0n : Nat) : ℝ) * ((b.r1v : ℝ) - 100000)) / (100000 * (b.v0n : ℝ))) =
        (8 * 64 * (((b.rx : ℝ) - 100000) * (b.r1x : ℝ) * (xn : ℝ) +
          ((xd - xn : Nat) : ℝ) * ((b.r1x : ℝ) - 100000) * (b.rx : ℝ)) *
          100000 * (b.u0n : ℝ) * (b.v0n : ℝ) -
          5 * 64 * (((b.u0n : ℝ) * ((b.ru : ℝ) - 100000) +
          ((b.u0d - b.u0n : Nat) : ℝ) * ((b.r1u : ℝ) - 100000)) * (b.v0n : ℝ) +
          ((b.v0n : ℝ) * ((b.rv : ℝ) - 100000) +
          ((b.v0d - b.v0n : Nat) : ℝ) * ((b.r1v : ℝ) - 100000)) * (b.u0n : ℝ)) *
          (b.rx : ℝ) * (b.r1x : ℝ) * (xn : ℝ)) /
        (8 * ((b.rx : ℝ) * (b.r1x : ℝ) * (xn : ℝ) * 100000 * (b.u0n : ℝ) * (b.v0n : ℝ))) := by
      field_simp [show (b.rx : ℝ) ≠ 0 by positivity, show (b.r1x : ℝ) ≠ 0 by positivity,
        show (xn : ℝ) ≠ 0 by positivity, show (b.u0n : ℝ) ≠ 0 by positivity,
        show (b.v0n : ℝ) ≠ 0 by positivity]
      ring
    rw [hfrac]
    exact div_nonneg (sub_nonneg.mpr hmainR) (by positivity)
  linarith

private lemma find_interval_idx :
    ∀ (k : Nat) (ps : List (Nat × Nat)),
      2 ≤ ps.length → isSortedPts ps = true →
      ∀ (x : ℝ) (a0 alast : Nat × Nat),
        ps.head? = some a0 → ps.getLast? = some alast →
        (a0.1 : ℝ) / a0.2 ≤ x → x ≤ (alast.1 : ℝ) / alast.2 →
        ∃ idx p, (idx, p) ∈ withIdx k (adjPairs ps) ∧
          (p.1.1 : ℝ) / p.1.2 ≤ x ∧ x ≤ (p.2.1 : ℝ) / p.2.2 ∧
          (∀ j p', (j, p') ∈ withIdx k (adjPairs ps) → j < idx →
            (p'.2.1 : ℝ) / p'.2.2 < x)
  | _, [], hlen, _, _, _, _, _, _, _, _ => by simp at hlen
  | _, [_], hlen, _, _, _, _, _, _, _, _ => by simp at hlen
  | k, a :: b :: rest, _, hs, x, a0, alast, hh, hl, hax, hxl => by
    simp only [List.head?, Option.some.injEq] at hh
    subst hh
    by_cases hxb : x ≤ (b.1 : ℝ) / b.2
    · refine ⟨k, (a, b), ?_, hax, hxb, ?_⟩
      · simp [adjPairs, withIdx]
      · intro j p' hj hlt
        simp only [adjPairs, withIdx, List.mem_cons] at hj
        rcases hj with heq | hj
        · injection heq with hjk; omega
        · have : k + 1 ≤ j := by
            clear hlt hax hxb hs hl hxl
            induction (adjPairs (b :: rest)) generalizing k j p' with
            | nil => simp [withIdx] at hj
            | cons hd tl ih =>
              simp only [withIdx, List.mem_cons] at hj
              rcases hj with heq | hj2
              · injection heq with hjk; omega
              · exact Nat.le_of_succ_le (ih (k + 1) hj2)
          omega
    · have hbx : (b.1 : ℝ) / b.2 ≤ x := le_of_not_ge hxb
      have hxb_strict : (b.1 : ℝ) / b.2 < x := lt_of_not_ge hxb
      have hlen2 : 2 ≤ (b :: rest).length := by
        cases rest with
        | nil =>
          simp only [List.getLast?, Option.some.injEq] at hl
          subst hl
          exfalso
          exact hxb hxl
        | cons _ _ => simp
      simp only [isSortedPts, Bool.and_eq_true] at hs
      obtain ⟨idx, p, hp, hp1, hp2, hstrict⟩ :=
        find_interval_idx (k + 1) (b :: rest) hlen2 hs.2 x b alast rfl hl hbx hxl
      refine ⟨idx, p, by simp [adjPairs, withIdx, hp], hp1, hp2, ?_⟩
      intro j p' hj hlt
      simp only [adjPairs, withIdx, List.mem_cons] at hj
      rcases hj with heq | hj2
      · injection heq with hjk hp'
        rw [← hp']
        exact hxb_strict
      · exact hstrict j p' hj2 hlt

private lemma boppana_pts1 {u v : ℝ} (hv : 1 / 8 ≤ v) (hvu : v ≤ u) (hu : u ≤ 7 / 8) :
    (5 / 8 : ℝ) * (entRatio u + entRatio v) ≤ entRatio (u * v) := by
  have hok := gridOk
  simp only [Bool.and_eq_true] at hok
  rcases hok with ⟨⟨⟨⟨⟨hall, htri⟩, _⟩, hs1⟩, _⟩, _⟩
  obtain ⟨iv, pv, hiv, hv0, hv1, hvstrict⟩ :=
    find_interval_idx 0 pts1 (by decide) hs1 v (1, 8) (7, 8) rfl rfl (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨ju, pu, hju, hu0, hu1, _⟩ :=
    find_interval_idx 0 pts1 (by decide) hs1 u (1, 8) (7, 8) rfl rfl (by norm_num; linarith) (by norm_num; linarith)
  have hij : iv ≤ ju := by
    by_contra hlt
    have hgt : ju < iv := lt_of_not_ge hlt
    have hltv : (pu.2.1 : ℝ) / pu.2.2 < v := hvstrict ju pu hju hgt
    linarith
  have hcheckTri := (list_all_iff _ _).mp htri (iv, pv) hiv
  have hhas := (list_all_iff _ _).mp hcheckTri (ju, pu) hju
  simp only [hij, ↓reduceIte, hasBox, list_any_iff, decide_eq_true_eq] at hhas
  rcases hhas with ⟨b, hbmem, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hbcheck : checkBox b = true := (list_all_iff _ _).mp hall b hbmem
  rw [← h1, ← h2] at hv0
  rw [← h3, ← h4] at hv1
  rw [← h5, ← h6] at hu0
  rw [← h7, ← h8] at hu1
  exact boppana_box b hbcheck hv0 hv1 hu0 hu1

private lemma boppana_rect {u v : ℝ} (hv0 : 3 / 4 ≤ v) (hv1 : v ≤ 7 / 8)
    (hu0 : 7 / 8 ≤ u) (hu1 : u ≤ 15 / 16) :
    (5 / 8 : ℝ) * (entRatio u + entRatio v) ≤ entRatio (u * v) := by
  have hok := gridOk
  simp only [Bool.and_eq_true] at hok
  rcases hok with ⟨⟨⟨⟨⟨hall, _⟩, hrect⟩, _⟩, hsV⟩, hsU⟩
  obtain ⟨_, pv, hpv, hvlo, hvhi, _⟩ :=
    find_interval_idx 0 ptsV (by decide) hsV v (3, 4) (7, 8) rfl rfl (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨_, pu, hpu, hulo, huhi, _⟩ :=
    find_interval_idx 0 ptsU (by decide) hsU u (7, 8) (15, 16) rfl rfl (by norm_num; linarith) (by norm_num; linarith)
  have hpv' : pv ∈ adjPairs ptsV := withIdx_mem_snd 0 (adjPairs ptsV) _ pv hpv
  have hpu' : pu ∈ adjPairs ptsU := withIdx_mem_snd 0 (adjPairs ptsU) _ pu hpu
  have hcheckRect := (list_all_iff _ _).mp hrect pv hpv'
  have hhas := (list_all_iff _ _).mp hcheckRect pu hpu'
  simp only [hasBox, list_any_iff, decide_eq_true_eq] at hhas
  rcases hhas with ⟨b, hbmem, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hbcheck : checkBox b = true := (list_all_iff _ _).mp hall b hbmem
  rw [← h1, ← h2] at hvlo
  rw [← h3, ← h4] at hvhi
  rw [← h5, ← h6] at hulo
  rw [← h7, ← h8] at huhi
  exact boppana_box b hbcheck hvlo hvhi hulo huhi

private lemma entRatio_34_78 : (5 : ℝ) * entRatio (7 / 8) ≤ 3 * entRatio (3 / 4) := by
  rcases extra34_ok with ⟨h34a, h34b, h78a, h78b, _, _, _, _⟩
  have l1 := log_lo_of_pow64 (by norm_num) (by norm_num) (by norm_num) h34a
  have l2 := log_lo_of_pow64 (by norm_num) (by norm_num) (by norm_num) h34b
  have l3 := log_hi_of_pow64 (by norm_num) (by norm_num) (by norm_num) h78a
  have l4 := log_hi_of_pow64 (by norm_num) (by norm_num) (by norm_num) h78b
  have e34 : entRatio (3 / 4) = Real.log (4 / 3) + (1 / 3 : ℝ) * Real.log 4 := by
    have h := entRatio_rat_eq (n := 3) (d := 4) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have e78 : entRatio (7 / 8) = Real.log (8 / 7) + (1 / 7 : ℝ) * Real.log 8 := by
    have h := entRatio_rat_eq (n := 7) (d := 8) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  rw [e34, e78]
  norm_num at l1 l2 l3 l4
  linarith

private lemma entRatio_78_1516 : (5 : ℝ) * entRatio (15 / 16) ≤ 3 * entRatio (7 / 8) := by
  rcases extra34_ok with ⟨_, _, _, _, h78a, h78b, h15a, h15b⟩
  have l1 := log_lo_of_pow64 (by norm_num) (by norm_num) (by norm_num) h78a
  have l2 := log_lo_of_pow64 (by norm_num) (by norm_num) (by norm_num) h78b
  have l3 := log_hi_of_pow64 (by norm_num) (by norm_num) (by norm_num) h15a
  have l4 := log_hi_of_pow64 (by norm_num) (by norm_num) (by norm_num) h15b
  have e78 : entRatio (7 / 8) = Real.log (8 / 7) + (1 / 7 : ℝ) * Real.log 8 := by
    have h := entRatio_rat_eq (n := 7) (d := 8) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have e15 : entRatio (15 / 16) = Real.log (16 / 15) + (1 / 15 : ℝ) * Real.log 16 := by
    have h := entRatio_rat_eq (n := 15) (d := 16) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  rw [e78, e15]
  norm_num at l1 l2 l3 l4
  linarith

private lemma boppana_ordered {u v : ℝ} (hv0 : 0 ≤ v) (hvu : v ≤ u) (hu1 : u ≤ 1) :
    (5 / 8 : ℝ) * (u * binEnt v + v * binEnt u) ≤ binEnt (u * v) := by
  by_cases hvz : v = 0
  · subst hvz; simp [binEnt_zero]
  have hvpos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hvz)
  have hupos : 0 < u := lt_of_lt_of_le hvpos hvu
  by_cases huone : u = 1
  · subst huone
    simp only [binEnt_one, mul_zero, add_zero, one_mul, mul_one]
    have hnn := binEnt_nonneg hv0 (by linarith)
    linarith
  have hult : u < 1 := lt_of_le_of_ne hu1 huone
  by_cases hv8 : v ≤ 1 / 8
  · exact boppana_small_v hupos hult hvpos hv8
  have hv_gt8 : 1 / 8 < v := lt_of_not_ge hv8
  by_cases hv78 : 7 / 8 ≤ v
  · exact boppana_large_uv hv78 hvu hult
  have hv_lt78 : v < 7 / 8 := lt_of_not_ge hv78
  suffices hratio : (5 / 8 : ℝ) * (entRatio u + entRatio v) ≤ entRatio (u * v) by
    have huvpos : 0 < u * v := mul_pos hupos hvpos
    have hmul := mul_le_mul_of_nonneg_left hratio huvpos.le
    have hid1 : (u * v) * entRatio (u * v) = binEnt (u * v) := by
      simp only [entRatio, not_le.mpr huvpos, ↓reduceIte]
      field_simp [ne_of_gt huvpos]
    have hid2 : (u * v) * ((5 / 8 : ℝ) * (entRatio u + entRatio v)) =
        (5 / 8 : ℝ) * (u * binEnt v + v * binEnt u) := by
      simp only [entRatio, not_le.mpr hupos, not_le.mpr hvpos, ↓reduceIte]
      field_simp [ne_of_gt hupos, ne_of_gt hvpos]
      ring
    linarith
  by_cases hu78 : u ≤ 7 / 8
  · exact boppana_pts1 hv_gt8.le hvu hu78
  have hu_gt78 : 7 / 8 < u := lt_of_not_ge hu78
  have huv_pos : 0 < u * v := mul_pos hupos hvpos
  have hf_uv : entRatio v ≤ entRatio (u * v) :=
    entRatio_antitone huv_pos (by nlinarith) hv_lt78.le
  by_cases hv34 : v ≤ 3 / 4
  · have hfv : entRatio (3 / 4) ≤ entRatio v := entRatio_antitone hvpos hv34 (by norm_num)
    have hfu : entRatio u ≤ entRatio (7 / 8) := entRatio_antitone (by norm_num) hu_gt78.le hult.le
    linarith [entRatio_34_78]
  have hv_gt34 : 3 / 4 < v := lt_of_not_ge hv34
  by_cases hu15 : u ≤ 15 / 16
  · exact boppana_rect hv_gt34.le hv_lt78.le hu_gt78.le hu15
  have hu_gt15 : 15 / 16 < u := lt_of_not_ge hu15
  have hfv : entRatio (7 / 8) ≤ entRatio v := entRatio_antitone hvpos hv_lt78.le (by norm_num)
  have hfu : entRatio u ≤ entRatio (15 / 16) := entRatio_antitone (by norm_num) hu_gt15.le hult.le
  linarith [entRatio_78_1516]

private lemma boppana_ineq {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (5 / 8 : ℝ) * (u * binEnt v + v * binEnt u) ≤ binEnt (u * v) := by
  by_cases hvu : v ≤ u
  · exact boppana_ordered hv0 hvu hu1
  · have huv : u ≤ v := le_of_not_ge hvu
    have h := boppana_ordered hu0 huv hv1
    rw [mul_comm v u] at h
    linarith

private lemma binEnt_tangent {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y < 1) :
    binEnt x ≤ binEnt y + (y - x) * (Real.log y - Real.log (1 - y)) := by
  have h1y : 0 < 1 - y := by linarith
  by_cases hxz : x = 0
  · subst hxz
    simp only [binEnt, negMulLog_zero, negMulLog_one, zero_add,
      negMulLog_pos_eq hy0, negMulLog_pos_eq h1y, sub_zero]
    have hlog : Real.log (1 - y) ≤ 0 := Real.log_nonpos h1y.le (by linarith)
    linarith
  by_cases hxone : x = 1
  · subst hxone
    simp only [binEnt, negMulLog_one, negMulLog_zero, sub_self, add_zero,
      negMulLog_pos_eq hy0, negMulLog_pos_eq h1y]
    have hlog : Real.log y ≤ 0 := Real.log_nonpos hy0.le hy1.le
    linarith
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxz)
  have hxlt : x < 1 := lt_of_le_of_ne hx1 hxone
  have h1x : 0 < 1 - x := by linarith
  simp only [binEnt, negMulLog_pos_eq hxpos, negMulLog_pos_eq h1x,
    negMulLog_pos_eq hy0, negMulLog_pos_eq h1y]
  have h1 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hxpos)
  rw [Real.log_div (ne_of_gt hy0) (ne_of_gt hxpos)] at h1
  have hm1 : x * (Real.log y - Real.log x) ≤ y - x := by
    have hm := mul_le_mul_of_nonneg_left h1 hxpos.le
    have hid : x * (y / x - 1) = y - x := by field_simp [ne_of_gt hxpos]
    linarith
  have h2 : Real.log ((1 - y) / (1 - x)) ≤ (1 - y) / (1 - x) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos h1y h1x)
  rw [Real.log_div (ne_of_gt h1y) (ne_of_gt h1x)] at h2
  have hm2 : (1 - x) * (Real.log (1 - y) - Real.log (1 - x)) ≤ x - y := by
    have hm := mul_le_mul_of_nonneg_left h2 h1x.le
    have hid : (1 - x) * ((1 - y) / (1 - x) - 1) = x - y := by field_simp [ne_of_gt h1x]; ring
    linarith
  linarith

private lemma binEnt_jensen {ι : Type} (s : Finset ι) (w p : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    (hW : 0 < ∑ i ∈ s, w i) :
    ∑ i ∈ s, w i * binEnt (p i) ≤
      (∑ i ∈ s, w i) * binEnt ((∑ i ∈ s, w i * p i) / (∑ i ∈ s, w i)) := by
  let W := ∑ i ∈ s, w i
  let P := ∑ i ∈ s, w i * p i
  let pbar := P / W
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (hp0 i hi))
  have hPW : P ≤ W := by
    apply Finset.sum_le_sum
    intro i hi
    have hm := mul_le_mul_of_nonneg_left (hp1 i hi) (hw i hi)
    linarith
  have hpbar0 : 0 ≤ pbar := div_nonneg hP0 hW.le
  have hpbar1 : pbar ≤ 1 := by
    have hid : 1 - P / W = (W - P) / W := by field_simp [ne_of_gt hW]
    have hnn : 0 ≤ (W - P) / W := div_nonneg (by linarith) hW.le
    linarith
  by_cases hpz : pbar = 0
  · have hPz : P = 0 := by
      have hid : W * pbar = P := by dsimp [pbar]; field_simp [ne_of_gt hW]
      rw [hpz, mul_zero] at hid
      exact hid.symm
    have hzero : ∀ i ∈ s, w i * binEnt (p i) = 0 := by
      intro i hi
      by_cases hwi : w i = 0
      · simp [hwi]
      · have hwpos : 0 < w i := lt_of_le_of_ne (hw i hi) (Ne.symm hwi)
        have hpi0 : w i * p i = 0 := by
          have hmem : w i * p i ≤ P :=
            Finset.single_le_sum (fun j hj => mul_nonneg (hw j hj) (hp0 j hj)) hi
          have hnn : 0 ≤ w i * p i := mul_nonneg (hw i hi) (hp0 i hi)
          linarith
        have hpi : p i = 0 := (mul_eq_zero.mp hpi0).resolve_left hwi
        simp [hpi, binEnt_zero]
    rw [Finset.sum_eq_zero hzero, hpz, binEnt_zero, mul_zero]
  by_cases hpone : pbar = 1
  · have hPW_eq : P = W := by
      have hid : W * pbar = P := by dsimp [pbar]; field_simp [ne_of_gt hW]
      rw [hpone, mul_one] at hid
      exact hid.symm
    have hdiff_zero : ∑ i ∈ s, w i * (1 - p i) = 0 := by
      have hid : ∑ i ∈ s, w i * (1 - p i) = W - P := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      linarith
    have hzero : ∀ i ∈ s, w i * binEnt (p i) = 0 := by
      intro i hi
      by_cases hwi : w i = 0
      · simp [hwi]
      · have hwi_nn : w i * (1 - p i) = 0 := by
          have hmem : w i * (1 - p i) ≤ ∑ j ∈ s, w j * (1 - p j) :=
            Finset.single_le_sum (fun j hj => mul_nonneg (hw j hj) (by linarith [hp1 j hj])) hi
          have hnn : 0 ≤ w i * (1 - p i) := mul_nonneg (hw i hi) (by linarith [hp1 i hi])
          linarith
        have hpi : 1 - p i = 0 := (mul_eq_zero.mp hwi_nn).resolve_left hwi
        have hp1i : p i = 1 := by linarith
        simp [hp1i, binEnt_one]
    rw [Finset.sum_eq_zero hzero, hpone, binEnt_one, mul_zero]
  have hy0 : 0 < pbar := lt_of_le_of_ne hpbar0 (Ne.symm hpz)
  have hy1 : pbar < 1 := lt_of_le_of_ne hpbar1 hpone
  calc
    ∑ i ∈ s, w i * binEnt (p i)
        ≤ ∑ i ∈ s, w i * (binEnt pbar + (pbar - p i) * (Real.log pbar - Real.log (1 - pbar))) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (binEnt_tangent (hp0 i hi) (hp1 i hi) hy0 hy1) (hw i hi)
    _ = W * binEnt pbar + (W * pbar - P) * (Real.log pbar - Real.log (1 - pbar)) := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
          have h1 : ∑ i ∈ s, w i * ((pbar - p i) * (Real.log pbar - Real.log (1 - pbar))) =
              (∑ i ∈ s, (w i * pbar - w i * p i)) * (Real.log pbar - Real.log (1 - pbar)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun i _ => by ring)
          rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ = W * binEnt pbar := by
          have hid : W * pbar = P := by dsimp [pbar]; field_simp [ne_of_gt hW]
          rw [hid, sub_self, zero_mul, add_zero]

private noncomputable def projEnt {α : Type} [DecidableEq α]
    (Ω : Finset α) (π : α → Finset ℕ) : ℝ :=
  ∑ T ∈ Ω.image π, negMulLog (((Ω.filter (fun ω => π ω = T)).card : ℝ) / (Ω.card : ℝ))

private lemma projEnt_empty {α : Type} [DecidableEq α] (Ω : Finset α) (hΩ : Ω.Nonempty) :
    projEnt Ω (fun _ => ∅) = 0 := by
  have himg : Ω.image (fun _ => (∅ : Finset ℕ)) = {∅} := by
    ext T
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨_, _, rfl⟩; rfl
    · intro hT; subst hT; obtain ⟨ω, hω⟩ := hΩ; exact ⟨ω, hω, rfl⟩
  have hfilt : Ω.filter (fun _ : α => (∅ : Finset ℕ) = ∅) = Ω := by
    ext ω; simp
  simp only [projEnt, himg, Finset.sum_singleton, hfilt]
  have hpos : (Ω.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hΩ).ne'
  rw [div_self hpos, negMulLog_one]

private lemma card_filter_split {α : Type} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  have hdisj : Disjoint (s.filter p) (s.filter (fun x => ¬ p x)) :=
    Finset.disjoint_left.mpr (fun x hx1 hx2 =>
      (Finset.mem_filter.mp hx2).2 (Finset.mem_filter.mp hx1).2)
  have hunion : s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx; by_cases hp : p x <;> [exact Or.inl ⟨hx, hp⟩; exact Or.inr ⟨hx, hp⟩]
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

private lemma negMulLog_split_eq {c c0 c1 m : ℝ} (hm : 0 < m) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hsum : c = c0 + c1) :
    negMulLog (c0 / m) + negMulLog (c1 / m) - negMulLog (c / m) =
      if c ≤ 0 then 0 else (c / m) * binEnt (c1 / c) := by
  by_cases hc : c ≤ 0
  · have hc0z : c0 = 0 := by linarith
    have hc1z : c1 = 0 := by linarith
    have hcz : c = 0 := by linarith
    simp [hc, hc0z, hc1z, hcz, negMulLog_zero]
  · have hcpos : 0 < c := lt_of_not_ge hc
    simp only [hc, ↓reduceIte]
    have hsub : 1 - c1 / c = c0 / c := by
      field_simp [ne_of_gt hcpos]; linarith
    rw [binEnt, hsub]
    by_cases h0z : c0 = 0
    · have hc1_eq : c1 = c := by linarith
      subst h0z
      rw [hc1_eq, zero_div, div_self (ne_of_gt hcpos), negMulLog_zero, negMulLog_zero, zero_add,
          add_zero, sub_self, mul_zero]
    · by_cases h1z : c1 = 0
      · have hc0_eq : c0 = c := by linarith
        subst h1z
        rw [hc0_eq, zero_div, div_self (ne_of_gt hcpos), negMulLog_zero, negMulLog_zero, add_zero,
            zero_add, sub_self, mul_zero]
      · have hc0pos : 0 < c0 := lt_of_le_of_ne hc0 (Ne.symm h0z)
        have hc1pos : 0 < c1 := lt_of_le_of_ne hc1 (Ne.symm h1z)
        rw [negMulLog_pos_eq (div_pos hc0pos hm), negMulLog_pos_eq (div_pos hc1pos hm),
            negMulLog_pos_eq (div_pos hcpos hm), negMulLog_pos_eq (div_pos hc1pos hcpos),
            negMulLog_pos_eq (div_pos hc0pos hcpos),
            Real.log_div (ne_of_gt hc0pos) (ne_of_gt hm),
            Real.log_div (ne_of_gt hc1pos) (ne_of_gt hm),
            Real.log_div (ne_of_gt hcpos) (ne_of_gt hm),
            Real.log_div (ne_of_gt hc1pos) (ne_of_gt hcpos),
            Real.log_div (ne_of_gt hc0pos) (ne_of_gt hcpos)]
        field_simp [ne_of_gt hm, ne_of_gt hcpos]
        nlinarith

private lemma projEnt_insert {α : Type} [DecidableEq α]
    (Ω : Finset α) (hΩ : Ω.Nonempty) (f : α → Finset ℕ) (S : Finset ℕ) (x : ℕ) (hxS : x ∉ S) :
    projEnt Ω (fun ω => f ω ∩ insert x S) - projEnt Ω (fun ω => f ω ∩ S) =
      ∑ T ∈ Ω.image (fun ω => f ω ∩ S),
        (((Ω.filter (fun ω => f ω ∩ S = T)).card : ℝ) / (Ω.card : ℝ)) *
          binEnt ((((Ω.filter (fun ω => f ω ∩ S = T)).filter (fun ω => x ∈ f ω)).card : ℝ) /
            ((Ω.filter (fun ω => f ω ∩ S = T)).card : ℝ)) := by
  let π := fun ω => f ω ∩ S
  let π' := fun ω => f ω ∩ insert x S
  let I := Ω.image π
  let I' := Ω.image π'
  have hm : (0 : ℝ) < (Ω.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hΩ
  have hx_not_mem : ∀ T ∈ I, x ∉ T := by
    intro T hT
    obtain ⟨ω, _, rfl⟩ := Finset.mem_image.mp hT
    intro hmem
    exact hxS (Finset.mem_inter.mp hmem).2
  have hsub : I' ⊆ I ∪ I.image (insert x) := by
    intro T' hT'
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.mp hT'
    have hTmem : f ω ∩ S ∈ I := Finset.mem_image.mpr ⟨ω, hω, rfl⟩
    by_cases hxω : x ∈ f ω
    · have heq : f ω ∩ insert x S = insert x (f ω ∩ S) := by
        ext y; simp only [Finset.mem_inter, Finset.mem_insert]; constructor
        · rintro ⟨hy1, rfl | hy2⟩ <;> [exact Or.inl rfl; exact Or.inr ⟨hy1, hy2⟩]
        · rintro (rfl | ⟨hy1, hy2⟩) <;> [exact ⟨hxω, Or.inl rfl⟩; exact ⟨hy1, Or.inr hy2⟩]
      rw [heq]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨f ω ∩ S, hTmem, rfl⟩))
    · have heq : f ω ∩ insert x S = f ω ∩ S := by
        ext y; simp only [Finset.mem_inter, Finset.mem_insert]; constructor
        · rintro ⟨hy1, rfl | hy2⟩
          · exact absurd hy1 hxω
          · exact ⟨hy1, hy2⟩
        · rintro ⟨hy1, hy2⟩; exact ⟨hy1, Or.inr hy2⟩
      rw [heq]
      exact Finset.mem_union.mpr (Or.inl hTmem)
  have hproj' : projEnt Ω π' =
      ∑ T' ∈ I ∪ I.image (insert x), negMulLog (((Ω.filter (fun ω => π' ω = T')).card : ℝ) / (Ω.card : ℝ)) := by
    apply Finset.sum_subset hsub
    intro T' _ hT'not
    have hfilt : Ω.filter (fun ω => π' ω = T') = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ω hω
      have hω' := Finset.mem_filter.mp hω
      exact hT'not (Finset.mem_image.mpr ⟨ω, hω'.1, hω'.2⟩)
    simp [hfilt, negMulLog_zero]
  have hdisj : Disjoint I (I.image (insert x)) := by
    refine Finset.disjoint_left.mpr ?_
    intro T hT1 hT2
    obtain ⟨T₀, _, rfl⟩ := Finset.mem_image.mp hT2
    exact hx_not_mem (insert x T₀) hT1 (Finset.mem_insert_self x T₀)
  have hinj : Set.InjOn (insert x) I := by
    intro T₁ hT₁ T₂ hT₂ heq
    have h1 := hx_not_mem T₁ hT₁
    have h2 := hx_not_mem T₂ hT₂
    ext y
    have hy := congrArg (fun s => y ∈ s) heq
    simp only [Finset.mem_insert] at hy
    by_cases hyx : y = x
    · subst hyx; exact iff_of_false h1 h2
    · simpa [hyx] using hy
  rw [hproj', Finset.sum_union hdisj, Finset.sum_image hinj]
  change (∑ T ∈ I, negMulLog (((Ω.filter (fun ω => π' ω = T)).card : ℝ) / (Ω.card : ℝ)) +
      ∑ T ∈ I, negMulLog (((Ω.filter (fun ω => π' ω = insert x T)).card : ℝ) / (Ω.card : ℝ))) -
      ∑ T ∈ I, negMulLog (((Ω.filter (fun ω => π ω = T)).card : ℝ) / (Ω.card : ℝ)) = _
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro T hT
  have hxT : x ∉ T := hx_not_mem T hT
  have hfilt0 : Ω.filter (fun ω => π' ω = T) = (Ω.filter (fun ω => π ω = T)).filter (fun ω => x ∉ f ω) := by
    ext ω
    simp only [Finset.mem_filter, π, π']
    constructor
    · rintro ⟨hω, heq⟩
      have hsubT : f ω ∩ S = T := by
        ext y
        have hy := congrArg (fun s => y ∈ s) heq
        simp only [Finset.mem_inter, Finset.mem_insert] at hy
        constructor
        · rintro ⟨h1, h2⟩; exact hy.mp ⟨h1, Or.inr h2⟩
        · intro hyT
          have hy' := hy.mpr hyT
          rcases hy'.2 with rfl | h2
          · exact absurd hyT hxT
          · exact ⟨hy'.1, h2⟩
      have hxnot : x ∉ f ω := by
        intro hxf
        have hxmem : x ∈ f ω ∩ insert x S := Finset.mem_inter.mpr ⟨hxf, Finset.mem_insert_self x S⟩
        rw [heq] at hxmem
        exact hxT hxmem
      exact ⟨⟨hω, hsubT⟩, hxnot⟩
    · rintro ⟨⟨hω, heq⟩, hxnot⟩
      refine ⟨hω, ?_⟩
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨h1, rfl | h2⟩
        · exact absurd h1 hxnot
        · exact heq ▸ Finset.mem_inter.mpr ⟨h1, h2⟩
      · intro hyT
        have hyS := Finset.mem_inter.mp (heq ▸ hyT)
        exact ⟨hyS.1, Or.inr hyS.2⟩
  have hfilt1 : Ω.filter (fun ω => π' ω = insert x T) =
      (Ω.filter (fun ω => π ω = T)).filter (fun ω => x ∈ f ω) := by
    ext ω
    simp only [Finset.mem_filter, π, π']
    constructor
    · rintro ⟨hω, heq⟩
      have hxmem : x ∈ f ω ∩ insert x S := heq ▸ Finset.mem_insert_self x T
      have hxf : x ∈ f ω := (Finset.mem_inter.mp hxmem).1
      have hsubT : f ω ∩ S = T := by
        ext y
        have hy := congrArg (fun s => y ∈ s) heq
        simp only [Finset.mem_inter, Finset.mem_insert] at hy
        by_cases hyx : y = x
        · subst hyx
          exact iff_of_false (fun h => hxS (Finset.mem_inter.mp h).2) hxT
        · simpa [hyx] using hy
      exact ⟨⟨hω, hsubT⟩, hxf⟩
    · rintro ⟨⟨hω, heq⟩, hxf⟩
      refine ⟨hω, ?_⟩
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert]
      by_cases hyx : y = x
      · subst hyx
        exact iff_of_true ⟨hxf, Or.inl rfl⟩ (Or.inl rfl)
      · have hy := congrArg (fun s => y ∈ s) heq
        simp only [Finset.mem_inter] at hy
        simpa [hyx] using hy
  rw [hfilt0, hfilt1]
  have hcard_sum : ((Ω.filter (fun ω => π ω = T)).filter (fun ω => x ∉ f ω)).card +
      ((Ω.filter (fun ω => π ω = T)).filter (fun ω => x ∈ f ω)).card =
      (Ω.filter (fun ω => π ω = T)).card := by
    have h := card_filter_split (Ω.filter (fun ω => π ω = T)) (fun ω => x ∈ f ω)
    omega
  have hcard_sumR : ((Ω.filter (fun ω => π ω = T)).card : ℝ) =
      (((Ω.filter (fun ω => π ω = T)).filter (fun ω => x ∉ f ω)).card : ℝ) +
      (((Ω.filter (fun ω => π ω = T)).filter (fun ω => x ∈ f ω)).card : ℝ) := by
    exact_mod_cast hcard_sum.symm
  have hsplit := negMulLog_split_eq hm
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hcard_sumR
  have hcpos : 0 < (Ω.filter (fun ω => π ω = T)).card := by
    obtain ⟨ω, hω, hωT⟩ := Finset.mem_image.mp hT
    exact Finset.card_pos.mpr ⟨ω, Finset.mem_filter.mpr ⟨hω, hωT⟩⟩
  have hcposR : ¬ ((Ω.filter (fun ω => π ω = T)).card : ℝ) ≤ 0 := by
    exact not_le.mpr (by exact_mod_cast hcpos)
  rw [hsplit]
  simp [hcposR]

private lemma projEnt_union_step (F : Finset (Finset ℕ)) (hF : F.Nonempty) (S : Finset ℕ) (x : ℕ)
    (hxS : x ∉ S) :
    (5 / 4 : ℝ) * (1 - ((F.filter (fun A => x ∈ A)).card : ℝ) / (F.card : ℝ)) *
      (projEnt F (fun A => A ∩ insert x S) - projEnt F (fun A => A ∩ S)) ≤
      projEnt (F ×ˢ F) (fun ab => (ab.1 ∪ ab.2) ∩ insert x S) -
        projEnt (F ×ˢ F) (fun ab => (ab.1 ∪ ab.2) ∩ S) := by
  have hFF : (F ×ˢ F).Nonempty := by
    obtain ⟨A, hA⟩ := hF
    exact ⟨(A, A), Finset.mem_product.mpr ⟨hA, hA⟩⟩
  rw [projEnt_insert F hF id S x hxS, projEnt_insert (F ×ˢ F) hFF (fun ab => ab.1 ∪ ab.2) S x hxS]
  let m : ℝ := (F.card : ℝ)
  have hm : 0 < m := by exact_mod_cast Finset.card_pos.mpr hF
  have hm2 : ((F ×ˢ F).card : ℝ) = m ^ 2 := by
    rw [Finset.card_product]
    push_cast
    ring
  let I := F.image (fun A => A ∩ S)
  let IU := (F ×ˢ F).image (fun ab => (ab.1 ∪ ab.2) ∩ S)
  let c : Finset ℕ → ℝ := fun T => ((F.filter (fun A => A ∩ S = T)).card : ℝ)
  let c1 : Finset ℕ → ℝ := fun T => (((F.filter (fun A => A ∩ S = T)).filter (fun A => x ∈ A)).card : ℝ)
  let c0 : Finset ℕ → ℝ := fun T => (((F.filter (fun A => A ∩ S = T)).filter (fun A => x ∉ A)).card : ℝ)
  let p : Finset ℕ → ℝ := fun T => c1 T / c T
  let q : Finset ℕ → ℝ := fun T => 1 - p T
  have hc_pos : ∀ T ∈ I, 0 < c T := by
    intro T hT
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hT
    exact_mod_cast Finset.card_pos.mpr ⟨A, Finset.mem_filter.mpr ⟨hA, rfl⟩⟩
  have hcsplit : ∀ T : Finset ℕ, c0 T + c1 T = c T := by
    intro T
    have h := card_filter_split (F.filter (fun A => A ∩ S = T)) (fun A => x ∈ A)
    exact_mod_cast (by simpa [c0, c1, c] using (by omega :
      ((F.filter (fun A => A ∩ S = T)).filter (fun A => x ∉ A)).card +
      ((F.filter (fun A => A ∩ S = T)).filter (fun A => x ∈ A)).card =
      (F.filter (fun A => A ∩ S = T)).card))
  have hp_bounds : ∀ T ∈ I, 0 ≤ p T ∧ p T ≤ 1 := by
    intro T hT
    have hcpos := hc_pos T hT
    refine ⟨div_nonneg (Nat.cast_nonneg _) hcpos.le, ?_⟩
    rw [div_le_one hcpos]
    have := hcsplit T
    have hc0nn : 0 ≤ c0 T := Nat.cast_nonneg _
    linarith
  have hq_bounds : ∀ T ∈ I, 0 ≤ q T ∧ q T ≤ 1 := by
    intro T hT
    have hp := hp_bounds T hT
    exact ⟨by dsimp [q]; linarith, by dsimp [q]; linarith⟩
  have hfiber : ∀ T ∈ IU,
      let KT := (I ×ˢ I).filter (fun pr => pr.1 ∪ pr.2 = T)
      let FF := (F ×ˢ F).filter (fun ab => (ab.1 ∪ ab.2) ∩ S = T)
      (0 : ℝ) < (FF.card : ℝ) ∧
      (FF.card : ℝ) = ∑ pr ∈ KT, c pr.1 * c pr.2 ∧
      ((FF.filter (fun ab => x ∈ ab.1 ∪ ab.2)).card : ℝ) =
        ∑ pr ∈ KT, (c pr.1 * c pr.2) * (1 - q pr.1 * q pr.2) := by
    intro T hT
    dsimp only
    let KT := (I ×ˢ I).filter (fun pr => pr.1 ∪ pr.2 = T)
    let FF := (F ×ˢ F).filter (fun ab => (ab.1 ∪ ab.2) ∩ S = T)
    have hFF_pos : 0 < (FF.card : ℝ) := by
      obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hT
      exact_mod_cast Finset.card_pos.mpr ⟨ab, Finset.mem_filter.mpr ⟨hab, rfl⟩⟩
    let cell : Finset ℕ × Finset ℕ → Finset (Finset ℕ × Finset ℕ) :=
      fun pr => (F.filter (fun A => A ∩ S = pr.1)) ×ˢ (F.filter (fun B => B ∩ S = pr.2))
    have hdisj : (KT : Set (Finset ℕ × Finset ℕ)).PairwiseDisjoint cell := by
      intro pr1 _ pr2 _ hne
      refine Finset.disjoint_left.mpr ?_
      intro ab hab1 hab2
      simp only [cell, Finset.mem_product, Finset.mem_filter] at hab1 hab2
      apply hne
      exact Prod.ext (hab1.1.2.symm.trans hab2.1.2) (hab1.2.2.symm.trans hab2.2.2)
    have hbiU : KT.biUnion cell = FF := by
      ext ab
      simp only [Finset.mem_biUnion, KT, cell, Finset.mem_filter, Finset.mem_product, FF]
      constructor
      · rintro ⟨⟨T1, T2⟩, ⟨_, hU⟩, ⟨⟨hA, hAS⟩, ⟨hB, hBS⟩⟩⟩
        refine ⟨⟨hA, hB⟩, ?_⟩
        rw [Finset.union_inter_distrib_right, hAS, hBS, hU]
      · rintro ⟨⟨hA, hB⟩, hU⟩
        refine ⟨(ab.1 ∩ S, ab.2 ∩ S), ⟨⟨Finset.mem_image.mpr ⟨ab.1, hA, rfl⟩,
          Finset.mem_image.mpr ⟨ab.2, hB, rfl⟩⟩, ?_⟩, ⟨⟨hA, rfl⟩, ⟨hB, rfl⟩⟩⟩
        rw [← Finset.union_inter_distrib_right, hU]
    have hcard_eq : (FF.card : ℝ) = ∑ pr ∈ KT, c pr.1 * c pr.2 := by
      rw [← hbiU, Finset.card_biUnion hdisj]
      push_cast
      refine Finset.sum_congr rfl (fun pr _ => ?_)
      simp only [cell, Finset.card_product, c]
      push_cast
      rfl
    let cell1 : Finset ℕ × Finset ℕ → Finset (Finset ℕ × Finset ℕ) :=
      fun pr => (cell pr).filter (fun ab => x ∈ ab.1 ∪ ab.2)
    have hdisj1 : (KT : Set (Finset ℕ × Finset ℕ)).PairwiseDisjoint cell1 := by
      intro pr1 h1 pr2 h2 hne
      exact Finset.disjoint_left.mpr (fun ab hab1 hab2 =>
        Finset.disjoint_left.mp (hdisj h1 h2 hne)
          (Finset.mem_filter.mp hab1).1 (Finset.mem_filter.mp hab2).1)
    have hbiU1 : KT.biUnion cell1 = FF.filter (fun ab => x ∈ ab.1 ∪ ab.2) := by
      ext ab
      simp only [Finset.mem_biUnion, cell1, Finset.mem_filter]
      constructor
      · rintro ⟨pr, hpr, hab, hmem⟩
        exact ⟨hbiU ▸ Finset.mem_biUnion.mpr ⟨pr, hpr, hab⟩, hmem⟩
      · rintro ⟨hab, hmem⟩
        obtain ⟨pr, hpr, habc⟩ := Finset.mem_biUnion.mp (hbiU.symm ▸ hab)
        exact ⟨pr, hpr, habc, hmem⟩
    have hcard1_eq : ((FF.filter (fun ab => x ∈ ab.1 ∪ ab.2)).card : ℝ) =
        ∑ pr ∈ KT, (c pr.1 * c pr.2) * (1 - q pr.1 * q pr.2) := by
      rw [← hbiU1, Finset.card_biUnion hdisj1]
      push_cast
      refine Finset.sum_congr rfl (fun pr hpr => ?_)
      have hprI : pr.1 ∈ I ∧ pr.2 ∈ I := by
        simpa [KT, Finset.mem_filter, Finset.mem_product] using hpr
      have hc1_pos : 0 < c pr.1 := hc_pos pr.1 hprI.1
      have hc2_pos : 0 < c pr.2 := hc_pos pr.2 hprI.2
      have hsplit_cell := card_filter_split (cell pr) (fun ab => x ∈ ab.1 ∪ ab.2)
      have hnot_eq : (cell pr).filter (fun ab => x ∉ ab.1 ∪ ab.2) =
          ((F.filter (fun A => A ∩ S = pr.1)).filter (fun A => x ∉ A)) ×ˢ
          ((F.filter (fun B => B ∩ S = pr.2)).filter (fun B => x ∉ B)) := by
        ext ab
        simp [cell, Finset.mem_filter, Finset.mem_product, Finset.mem_union, not_or]
      have hcard_not : ((cell pr).filter (fun ab => x ∉ ab.1 ∪ ab.2)).card =
          ((F.filter (fun A => A ∩ S = pr.1)).filter (fun A => x ∉ A)).card *
          ((F.filter (fun B => B ∩ S = pr.2)).filter (fun B => x ∉ B)).card := by
        rw [hnot_eq, Finset.card_product]
      have hcard_cell : (cell pr).card =
          (F.filter (fun A => A ∩ S = pr.1)).card * (F.filter (fun B => B ∩ S = pr.2)).card := by
        simp [cell, Finset.card_product]
      have hsub_nat : (cell1 pr).card + ((cell pr).filter (fun ab => x ∉ ab.1 ∪ ab.2)).card =
          (cell pr).card := hsplit_cell
      have hR : ((cell1 pr).card : ℝ) = c pr.1 * c pr.2 - c0 pr.1 * c0 pr.2 := by
        have hnat : (cell1 pr).card +
            ((F.filter (fun A => A ∩ S = pr.1)).filter (fun A => x ∉ A)).card *
            ((F.filter (fun B => B ∩ S = pr.2)).filter (fun B => x ∉ B)).card =
            (F.filter (fun A => A ∩ S = pr.1)).card * (F.filter (fun B => B ∩ S = pr.2)).card := by
          rw [hcard_not, hcard_cell] at hsub_nat
          exact hsub_nat
        have hnatR : ((cell1 pr).card : ℝ) + c0 pr.1 * c0 pr.2 = c pr.1 * c pr.2 := by
          exact_mod_cast hnat
        linarith
      rw [hR]
      have hq1 : q pr.1 = c0 pr.1 / c pr.1 := by
        dsimp [q, p]
        have := hcsplit pr.1
        field_simp [ne_of_gt hc1_pos]; linarith
      have hq2 : q pr.2 = c0 pr.2 / c pr.2 := by
        dsimp [q, p]
        have := hcsplit pr.2
        field_simp [ne_of_gt hc2_pos]; linarith
      rw [hq1, hq2]
      field_simp [ne_of_gt hc1_pos, ne_of_gt hc2_pos]
      ring
    exact ⟨hFF_pos, hcard_eq, hcard1_eq⟩
  have hjensen_sum : ∑ T ∈ IU, ∑ pr ∈ (I ×ˢ I).filter (fun pr => pr.1 ∪ pr.2 = T),
      (c pr.1 * c pr.2 / m ^ 2) * binEnt (1 - q pr.1 * q pr.2) ≤
      ∑ T ∈ IU, ((((F ×ˢ F).filter (fun ab => (ab.1 ∪ ab.2) ∩ S = T)).card : ℝ) / ((F ×ˢ F).card : ℝ)) *
        binEnt (((((F ×ˢ F).filter (fun ab => (ab.1 ∪ ab.2) ∩ S = T)).filter
          (fun ab => x ∈ ab.1 ∪ ab.2)).card : ℝ) /
          (((F ×ˢ F).filter (fun ab => (ab.1 ∪ ab.2) ∩ S = T)).card : ℝ)) := by
    apply Finset.sum_le_sum
    intro T hT
    rcases hfiber T hT with ⟨hFF_pos, hcard_eq, hcard1_eq⟩
    let KT := (I ×ˢ I).filter (fun pr => pr.1 ∪ pr.2 = T)
    have hWpos : 0 < ∑ pr ∈ KT, (c pr.1 * c pr.2 / m ^ 2) := by
      rw [← Finset.sum_div, ← hcard_eq]
      exact div_pos hFF_pos (by positivity)
    have hj := binEnt_jensen KT (fun pr => c pr.1 * c pr.2 / m ^ 2)
      (fun pr => 1 - q pr.1 * q pr.2)
      (fun pr _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity))
      (fun pr hpr => by
        have hmem : pr.1 ∈ I ∧ pr.2 ∈ I := by
          simpa [KT, Finset.mem_filter, Finset.mem_product] using hpr
        have h1 := hq_bounds pr.1 hmem.1
        have h2 := hq_bounds pr.2 hmem.2
        nlinarith)
      (fun pr hpr => by
        have hmem : pr.1 ∈ I ∧ pr.2 ∈ I := by
          simpa [KT, Finset.mem_filter, Finset.mem_product] using hpr
        have h1 := hq_bounds pr.1 hmem.1
        have h2 := hq_bounds pr.2 hmem.2
        nlinarith)
      hWpos
    have hW_eq : ∑ pr ∈ KT, (c pr.1 * c pr.2 / m ^ 2) =
        (((F ×ˢ F).filter (fun ab => (ab.1 ∪ ab.2) ∩ S = T)).card : ℝ) / ((F ×ˢ F).card : ℝ) := by
      rw [← Finset.sum_div, ← hcard_eq, hm2]
    have hP_eq : (∑ pr ∈ KT, (c pr.1 * c pr.2 / m ^ 2) * (1 - q pr.1 * q pr.2)) /
        (∑ pr ∈ KT, (c pr.1 * c pr.2 / m ^ 2)) =
        (((((F ×ˢ F).filter (fun ab => (ab.1 ∪ ab.2) ∩ S = T)).filter
          (fun ab => x ∈ ab.1 ∪ ab.2)).card : ℝ) /
          (((F ×ˢ F).filter (fun ab => (ab.1 ∪ ab.2) ∩ S = T)).card : ℝ)) := by
      have hnum : ∑ pr ∈ KT, (c pr.1 * c pr.2 / m ^ 2) * (1 - q pr.1 * q pr.2) =
          ((((F ×ˢ F).filter (fun ab => (ab.1 ∪ ab.2) ∩ S = T)).filter
            (fun ab => x ∈ ab.1 ∪ ab.2)).card : ℝ) / m ^ 2 := by
        rw [hcard1_eq, Finset.sum_div]
        refine Finset.sum_congr rfl (fun pr _ => by ring)
      rw [hnum, hW_eq, hm2]
      field_simp [ne_of_gt hm]
    rw [hW_eq, hP_eq] at hj
    exact hj
  have hpart_II : ∑ T ∈ IU, ∑ pr ∈ (I ×ˢ I).filter (fun pr => pr.1 ∪ pr.2 = T),
      (c pr.1 * c pr.2 / m ^ 2) * binEnt (1 - q pr.1 * q pr.2) =
      ∑ T1 ∈ I, ∑ T2 ∈ I, (c T1 * c T2 / m ^ 2) * binEnt (q T1 * q T2) := by
    have hbiU_II : IU.biUnion (fun T => (I ×ˢ I).filter (fun pr => pr.1 ∪ pr.2 = T)) = I ×ˢ I := by
      ext pr
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, IU]
      constructor
      · rintro ⟨_, _, h1, _⟩; exact h1
      · rintro ⟨h1, h2⟩
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp h2
        refine ⟨(A ∪ B) ∩ S, Finset.mem_image.mpr ⟨(A, B), Finset.mem_product.mpr ⟨hA, hB⟩, rfl⟩,
          ⟨h1, h2⟩, ?_⟩
        rw [Finset.union_inter_distrib_right]
    have hdisj_II : (IU : Set (Finset ℕ)).PairwiseDisjoint
        (fun T => (I ×ˢ I).filter (fun pr => pr.1 ∪ pr.2 = T)) := by
      intro T1 _ T2 _ hne
      refine Finset.disjoint_left.mpr ?_
      intro pr hp1 hp2
      simp only [Finset.mem_filter] at hp1 hp2
      exact hne (hp1.2.symm.trans hp2.2)
    rw [← Finset.sum_biUnion hdisj_II, hbiU_II, Finset.sum_product]
    refine Finset.sum_congr rfl (fun T1 _ => Finset.sum_congr rfl (fun T2 _ => ?_))
    rw [binEnt_symm]
  have hbopp_sum : (5 / 8 : ℝ) * ∑ T1 ∈ I, ∑ T2 ∈ I, (c T1 * c T2 / m ^ 2) *
      (q T1 * binEnt (q T2) + q T2 * binEnt (q T1)) ≤
      ∑ T1 ∈ I, ∑ T2 ∈ I, (c T1 * c T2 / m ^ 2) * binEnt (q T1 * q T2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro T1 hT1
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro T2 hT2
    have hq1 := hq_bounds T1 hT1
    have hq2 := hq_bounds T2 hT2
    have hw : 0 ≤ c T1 * c T2 / m ^ 2 := by positivity
    have hb := boppana_ineq hq1.1 hq1.2 hq2.1 hq2.2
    nlinarith
  have hsum_c : ∑ T ∈ I, c T = m := by
    have hdisj : (I : Set (Finset ℕ)).PairwiseDisjoint (fun T => F.filter (fun A => A ∩ S = T)) := by
      intro T1 _ T2 _ hne
      refine Finset.disjoint_left.mpr ?_
      intro A h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hbiU : I.biUnion (fun T => F.filter (fun A => A ∩ S = T)) = F := by
      ext A
      simp only [Finset.mem_biUnion, Finset.mem_filter, I, Finset.mem_image]
      constructor
      · rintro ⟨_, _, hA, _⟩; exact hA
      · intro hA; exact ⟨A ∩ S, ⟨A, hA, rfl⟩, hA, rfl⟩
    have hnat : ∑ T ∈ I, (F.filter (fun A => A ∩ S = T)).card = F.card := by
      rw [← Finset.card_biUnion hdisj, hbiU]
    exact_mod_cast hnat
  have hsum_c0 : ∑ T ∈ I, c0 T = ((F.filter (fun A => x ∉ A)).card : ℝ) := by
    have hdisj : (I : Set (Finset ℕ)).PairwiseDisjoint
        (fun T => (F.filter (fun A => A ∩ S = T)).filter (fun A => x ∉ A)) := by
      intro T1 _ T2 _ hne
      refine Finset.disjoint_left.mpr ?_
      intro A h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hne (h1.1.2.symm.trans h2.1.2)
    have hbiU : I.biUnion (fun T => (F.filter (fun A => A ∩ S = T)).filter (fun A => x ∉ A)) =
        F.filter (fun A => x ∉ A) := by
      ext A
      simp only [Finset.mem_biUnion, Finset.mem_filter, I, Finset.mem_image]
      constructor
      · rintro ⟨_, _, ⟨hA, _⟩, hxA⟩; exact ⟨hA, hxA⟩
      · rintro ⟨hA, hxA⟩; exact ⟨A ∩ S, ⟨A, hA, rfl⟩, ⟨hA, rfl⟩, hxA⟩
    have hnat : ∑ T ∈ I, ((F.filter (fun A => A ∩ S = T)).filter (fun A => x ∉ A)).card =
        (F.filter (fun A => x ∉ A)).card := by
      rw [← Finset.card_biUnion hdisj, hbiU]
    exact_mod_cast hnat
  have hsum_q : ∑ T ∈ I, (c T / m) * q T = 1 - ((F.filter (fun A => x ∈ A)).card : ℝ) / m := by
    have hq_simp : ∀ T ∈ I, (c T / m) * q T = c0 T / m := by
      intro T hT
      have hcpos := hc_pos T hT
      have hcs := hcsplit T
      dsimp [q, p]
      field_simp [ne_of_gt hcpos, ne_of_gt hm]
      linarith
    rw [Finset.sum_congr rfl hq_simp, ← Finset.sum_div, hsum_c0]
    have hfs := card_filter_split F (fun A => x ∈ A)
    have hfsR : ((F.filter (fun A => x ∉ A)).card : ℝ) =
        m - ((F.filter (fun A => x ∈ A)).card : ℝ) := by
      have hn : ((F.filter (fun A => x ∈ A)).card : ℝ) +
          ((F.filter (fun A => x ∉ A)).card : ℝ) = m := by exact_mod_cast hfs
      linarith
    rw [hfsR]
    field_simp [ne_of_gt hm]
  have hsum_ent : ∑ T ∈ I, (c T / m) * binEnt (q T) =
      ∑ T ∈ I, (c T / m) * binEnt (p T) := by
    refine Finset.sum_congr rfl (fun T _ => ?_)
    dsimp [q]
    rw [binEnt_symm]
  have hfact : ∑ T1 ∈ I, ∑ T2 ∈ I, (c T1 * c T2 / m ^ 2) *
      (q T1 * binEnt (q T2) + q T2 * binEnt (q T1)) =
      2 * (1 - ((F.filter (fun A => x ∈ A)).card : ℝ) / m) *
        ∑ T ∈ I, (c T / m) * binEnt (p T) := by
    have hsplit : ∀ T1 T2, (c T1 * c T2 / m ^ 2) * (q T1 * binEnt (q T2) + q T2 * binEnt (q T1)) =
        ((c T1 / m) * q T1) * ((c T2 / m) * binEnt (q T2)) +
        ((c T1 / m) * binEnt (q T1)) * ((c T2 / m) * q T2) := by
      intro T1 T2; ring
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      hsum_q, hsum_ent]
    ring
  rw [hpart_II, hfact] at hjensen_sum
  have hcomb := le_trans (by linarith [hbopp_sum]) hjensen_sum
  linarith

private lemma projEnt_ge_zero {α : Type} [DecidableEq α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (π : α → Finset ℕ) : 0 ≤ projEnt Ω π := by
  apply Finset.sum_nonneg
  intro T hT
  have hm : (0 : ℝ) < (Ω.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hΩ
  apply negMulLog_nonneg
  · exact div_nonneg (Nat.cast_nonneg _) hm.le
  · rw [div_le_one hm]
    exact_mod_cast Finset.card_filter_le Ω (fun ω => π ω = T)

private lemma projEnt_step_nonneg (F : Finset (Finset ℕ)) (hF : F.Nonempty)
    (S : Finset ℕ) (x : ℕ) (hxS : x ∉ S) :
    0 ≤ projEnt F (fun A => A ∩ insert x S) - projEnt F (fun A => A ∩ S) := by
  rw [projEnt_insert F hF id S x hxS]
  apply Finset.sum_nonneg
  intro T hT
  have hm : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hF
  have hc : 0 < (F.filter (fun A => A ∩ S = T)).card := by
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.card_pos.mpr ⟨A, Finset.mem_filter.mpr ⟨hA, rfl⟩⟩
  have hcR : (0 : ℝ) < ((F.filter (fun A => A ∩ S = T)).card : ℝ) := by exact_mod_cast hc
  apply mul_nonneg (div_nonneg hcR.le hm.le)
  apply binEnt_nonneg (div_nonneg (Nat.cast_nonneg _) hcR.le)
  rw [div_le_one hcR]
  exact_mod_cast Finset.card_filter_le _ _

private lemma projEnt_union_le_log (F : Finset (Finset ℕ)) (hF : F.Nonempty)
    (hclosed : ∀ A ∈ F, ∀ B ∈ F, (A ∪ B) ∈ F) (U : Finset ℕ) (hU : ∀ A ∈ F, A ⊆ U) :
    projEnt (F ×ˢ F) (fun ab => (ab.1 ∪ ab.2) ∩ U) ≤ Real.log (F.card : ℝ) := by
  let Ω := F ×ˢ F
  let π := fun ab : Finset ℕ × Finset ℕ => (ab.1 ∪ ab.2) ∩ U
  let I := Ω.image π
  have hΩ : Ω.Nonempty := by
    obtain ⟨A, hA⟩ := hF
    exact ⟨(A, A), Finset.mem_product.mpr ⟨hA, hA⟩⟩
  have hm : (0 : ℝ) < (Ω.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hΩ
  have hFpos : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hF
  have hI_sub : I ⊆ F := by
    intro T hT
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hT
    have habm := Finset.mem_product.mp hab
    have hun : ab.1 ∪ ab.2 ∈ F := hclosed ab.1 habm.1 ab.2 habm.2
    have hsub : (ab.1 ∪ ab.2) ∩ U = ab.1 ∪ ab.2 := Finset.inter_eq_left.mpr (hU _ hun)
    simpa [π, hsub] using hun
  have hI_card : (I.card : ℝ) ≤ (F.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hI_sub
  let w : Finset ℕ → ℝ := fun T => ((Ω.filter (fun ab => π ab = T)).card : ℝ) / (Ω.card : ℝ)
  have hw_pos : ∀ T ∈ I, 0 < w T := by
    intro T hT
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hT
    have hc : 0 < (Ω.filter (fun x => π x = π ab)).card :=
      Finset.card_pos.mpr ⟨ab, Finset.mem_filter.mpr ⟨hab, rfl⟩⟩
    exact div_pos (by exact_mod_cast hc) hm
  have hw_sum : ∑ T ∈ I, w T = 1 := by
    have hdisj : (I : Set (Finset ℕ)).PairwiseDisjoint (fun T => Ω.filter (fun ab => π ab = T)) := by
      intro T1 _ T2 _ hne
      refine Finset.disjoint_left.mpr ?_
      intro ab h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hbiU : I.biUnion (fun T => Ω.filter (fun ab => π ab = T)) = Ω := by
      ext ab
      simp only [Finset.mem_biUnion, Finset.mem_filter, I, Finset.mem_image]
      constructor
      · rintro ⟨_, _, hab, _⟩; exact hab
      · intro hab; exact ⟨π ab, ⟨ab, hab, rfl⟩, hab, rfl⟩
    have hnat : ∑ T ∈ I, (Ω.filter (fun ab => π ab = T)).card = Ω.card := by
      rw [← Finset.card_biUnion hdisj, hbiU]
    have hnatR : ∑ T ∈ I, ((Ω.filter (fun ab => π ab = T)).card : ℝ) = (Ω.card : ℝ) := by
      exact_mod_cast hnat
    rw [← Finset.sum_div, hnatR, div_self (ne_of_gt hm)]
  have hgibbs : ∑ T ∈ I, w T * (Real.log (1 / (w T * (F.card : ℝ)))) ≤
      ∑ T ∈ I, w T * (1 / (w T * (F.card : ℝ)) - 1) := by
    apply Finset.sum_le_sum
    intro T hT
    have hwT := hw_pos T hT
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos one_pos (mul_pos hwT hFpos))) hwT.le
  have hlhs : ∑ T ∈ I, w T * Real.log (1 / (w T * (F.card : ℝ))) =
      projEnt Ω π - Real.log (F.card : ℝ) := by
    have hterm : ∀ T ∈ I, w T * Real.log (1 / (w T * (F.card : ℝ))) =
        negMulLog (w T) - w T * Real.log (F.card : ℝ) := by
      intro T hT
      have hwT := hw_pos T hT
      rw [negMulLog_pos_eq hwT, Real.log_div one_ne_zero (ne_of_gt (mul_pos hwT hFpos)),
          Real.log_one, Real.log_mul (ne_of_gt hwT) (ne_of_gt hFpos)]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum, one_mul]
    rfl
  have hrhs : ∑ T ∈ I, w T * (1 / (w T * (F.card : ℝ)) - 1) ≤ 0 := by
    have hterm : ∀ T ∈ I, w T * (1 / (w T * (F.card : ℝ)) - 1) =
        1 / (F.card : ℝ) - w T := by
      intro T hT
      have hwT := hw_pos T hT
      field_simp [ne_of_gt hwT, ne_of_gt hFpos]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        hw_sum]
    have hdiv : (I.card : ℝ) * (1 / (F.card : ℝ)) ≤ 1 := by
      have hid : (I.card : ℝ) * (1 / (F.card : ℝ)) = (I.card : ℝ) / (F.card : ℝ) := by ring
      rw [hid, div_le_one hFpos]
      exact hI_card
    linarith
  linarith

private lemma projEnt_self_eq_log (F : Finset (Finset ℕ)) (hF : F.Nonempty)
    (U : Finset ℕ) (hU : ∀ A ∈ F, A ⊆ U) :
    projEnt F (fun A => A ∩ U) = Real.log (F.card : ℝ) := by
  let π := fun A : Finset ℕ => A ∩ U
  have himg : F.image π = F := by
    ext A
    simp only [Finset.mem_image, π]
    constructor
    · rintro ⟨B, hB, rfl⟩
      rwa [Finset.inter_eq_left.mpr (hU B hB)]
    · intro hA
      exact ⟨A, hA, Finset.inter_eq_left.mpr (hU A hA)⟩
  have hm : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hF
  simp only [projEnt, himg]
  have hterm : ∀ A ∈ F, negMulLog (((F.filter (fun B => π B = A)).card : ℝ) / (F.card : ℝ)) =
      Real.log (F.card : ℝ) / (F.card : ℝ) := by
    intro A hA
    have hfilt : F.filter (fun B => π B = A) = {A} := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_singleton, π]
      constructor
      · rintro ⟨hB, heq⟩
        rwa [Finset.inter_eq_left.mpr (hU B hB)] at heq
      · intro hB; subst hB; exact ⟨hA, Finset.inter_eq_left.mpr (hU A hA)⟩
    rw [hfilt, Finset.card_singleton, Nat.cast_one,
        negMulLog_pos_eq (div_pos one_pos hm),
        Real.log_div one_ne_zero (ne_of_gt hm), Real.log_one]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  field_simp [ne_of_gt hm]

theorem proved : Targets.FranklDensity.Spec.ValidBound bound := by
  dsimp only [bound]
  intro F hF
  rcases hF with ⟨⟨A₀, hA₀, x₀, hx₀⟩, hclosed⟩
  have hFne : F.Nonempty := ⟨A₀, hA₀⟩
  by_cases hle5 : F.card ≤ 5
  · refine ⟨x₀, ?_⟩
    have hmem : A₀ ∈ F.filter (fun A => x₀ ∈ A) := Finset.mem_filter.mpr ⟨hA₀, hx₀⟩
    have hc : 1 ≤ (F.filter (fun A => x₀ ∈ A)).card := Finset.card_pos.mpr ⟨A₀, hmem⟩
    omega
  have hcard6 : 6 ≤ F.card := by omega
  by_contra hno
  push_neg at hno
  have hfreq : ∀ x : ℕ, 5 * (F.filter (fun A => x ∈ A)).card < F.card := by
    intro x
    have hx := hno x
    omega
  let U := F.biUnion id
  have hU : ∀ A ∈ F, A ⊆ U := by
    intro A hA a ha
    exact Finset.mem_biUnion.mpr ⟨A, hA, ha⟩
  have hind : ∀ S : Finset ℕ,
      projEnt F (fun A => A ∩ S) ≤ projEnt (F ×ˢ F) (fun ab => (ab.1 ∪ ab.2) ∩ S) ∧
      (0 < projEnt F (fun A => A ∩ S) →
        projEnt F (fun A => A ∩ S) < projEnt (F ×ˢ F) (fun ab => (ab.1 ∪ ab.2) ∩ S)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have hFF : (F ×ˢ F).Nonempty := ⟨(A₀, A₀), Finset.mem_product.mpr ⟨hA₀, hA₀⟩⟩
      have h1 : projEnt F (fun A => A ∩ ∅) = 0 := by
        simpa [Finset.inter_empty] using projEnt_empty F hFne
      have h2 : projEnt (F ×ˢ F) (fun ab => (ab.1 ∪ ab.2) ∩ ∅) = 0 := by
        simpa [Finset.inter_empty] using projEnt_empty (F ×ˢ F) hFF
      rw [h1, h2]
      exact ⟨le_rfl, fun h => absurd h (lt_irrefl 0)⟩
    | @insert x S hxS ih =>
      have hstep := projEnt_union_step F hFne S x hxS
      have hdH := projEnt_step_nonneg F hFne S x hxS
      have hfx : 1 < (5 / 4 : ℝ) * (1 - ((F.filter (fun A => x ∈ A)).card : ℝ) / (F.card : ℝ)) := by
        have hfR : (5 : ℝ) * ((F.filter (fun A => x ∈ A)).card : ℝ) < (F.card : ℝ) := by
          exact_mod_cast hfreq x
        have hm : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hFne
        have hid : (5 / 4 : ℝ) * (1 - ((F.filter (fun A => x ∈ A)).card : ℝ) / (F.card : ℝ)) - 1 =
            ((F.card : ℝ) - 5 * ((F.filter (fun A => x ∈ A)).card : ℝ)) / (4 * (F.card : ℝ)) := by
          field_simp [ne_of_gt hm]
          ring
        have hpos : 0 < ((F.card : ℝ) - 5 * ((F.filter (fun A => x ∈ A)).card : ℝ)) / (4 * (F.card : ℝ)) :=
          div_pos (by linarith) (by positivity)
        linarith
      have hle_step : projEnt F (fun A => A ∩ insert x S) - projEnt F (fun A => A ∩ S) ≤
          projEnt (F ×ˢ F) (fun ab => (ab.1 ∪ ab.2) ∩ insert x S) -
            projEnt (F ×ˢ F) (fun ab => (ab.1 ∪ ab.2) ∩ S) := by
        have hmul : projEnt F (fun A => A ∩ insert x S) - projEnt F (fun A => A ∩ S) ≤
            (5 / 4 : ℝ) * (1 - ((F.filter (fun A => x ∈ A)).card : ℝ) / (F.card : ℝ)) *
              (projEnt F (fun A => A ∩ insert x S) - projEnt F (fun A => A ∩ S)) := by
          nlinarith
        linarith
      refine ⟨by linarith [ih.1], ?_⟩
      intro hpos
      by_cases hSpos : 0 < projEnt F (fun A => A ∩ S)
      · linarith [ih.2 hSpos]
      · have hS0 : projEnt F (fun A => A ∩ S) = 0 :=
          le_antisymm (le_of_not_gt hSpos) (projEnt_ge_zero F hFne _)
        have hdH_pos : 0 < projEnt F (fun A => A ∩ insert x S) - projEnt F (fun A => A ∩ S) := by
          linarith
        have hstrict : projEnt F (fun A => A ∩ insert x S) - projEnt F (fun A => A ∩ S) <
            (5 / 4 : ℝ) * (1 - ((F.filter (fun A => x ∈ A)).card : ℝ) / (F.card : ℝ)) *
              (projEnt F (fun A => A ∩ insert x S) - projEnt F (fun A => A ∩ S)) := by
          nlinarith
        linarith [ih.1]
  have hlog_pos : 0 < Real.log (F.card : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < F.card)
  have hFU := projEnt_self_eq_log F hFne U hU
  have hstrict := (hind U).2 (by linarith)
  have hupper := projEnt_union_le_log F hFne hclosed U hU
  linarith

end Targets.FranklDensity.Proof
