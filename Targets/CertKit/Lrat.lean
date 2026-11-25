namespace Targets.CertKit.Lrat

/-- A propositional literal: variable index `var` with polarity `pos` (`true` = positive, `false` = negated). -/
structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, BEq, Repr

/-- Negation of a literal, flipping its polarity. -/
def Lit.neg (l : Lit) : Lit :=
  ⟨l.var, !l.pos⟩

/-- Disjunctive clause of literals. -/
abbrev Clause := List Lit

/-- Conjunctive normal form formula: list of clauses. -/
abbrev Cnf := List Clause

/-- Evaluate a literal under a Boolean valuation `σ`. -/
def evalLit (σ : Nat → Bool) (l : Lit) : Bool :=
  (σ l.var) == l.pos

/-- Evaluate a clause (disjunction of its literals). -/
def evalClause (σ : Nat → Bool) (c : Clause) : Bool :=
  c.any (evalLit σ)

/-- Evaluate a CNF formula (conjunction of its clauses). -/
def evalCnf (σ : Nat → Bool) (f : Cnf) : Bool :=
  f.all (evalClause σ)

/-- Semantic unsatisfiability of a CNF formula. -/
def Unsat (f : Cnf) : Prop :=
  ∀ σ : Nat → Bool, evalCnf σ f = false

/-- Check whether literal `l` occurs in `trail`. -/
def hasLit (trail : List Lit) (l : Lit) : Bool :=
  trail.any (fun x => decide (x = l))

/-- Check whether `trail` contains both a literal and its negation. -/
def hasContradiction (trail : List Lit) : Bool :=
  trail.any (fun l => hasLit trail l.neg)

/-- Check whether every literal of `c` is falsified by `trail`. -/
def isFalsified (trail : List Lit) (c : Clause) : Bool :=
  c.all (fun l => hasLit trail l.neg)

/-- Return `some u` if clause `c` is not already satisfied by `trail` and has exactly one
    non-falsified literal `u`; otherwise `none`. -/
def isUnit (trail : List Lit) (c : Clause) : Option Lit :=
  if c.any (fun l => hasLit trail l) then
    none
  else
    match c.filter (fun l => !(hasLit trail l.neg)) with
    | [u] => some u
    | _ => none

private def rupLoop (f : Cnf) (trail : List Lit) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if f.any (isFalsified trail) then
      true
    else
      let units := f.filterMap (isUnit trail)
      if units.isEmpty then
        false
      else
        let trail' := units ++ trail
        if hasContradiction trail' then
          true
        else
          rupLoop f trail' fuel

/-- Verify that clause `c` is a Reverse Unit Propagation (RUP) consequence of `f`. -/
def rupStep (f : Cnf) (c : Clause) : Bool :=
  let trail := c.map Lit.neg
  hasContradiction trail || rupLoop f trail (f.length + 1)

private def verifyRupAux (f : Cnf) : List Clause → Bool
  | [] => false
  | [c] => c.isEmpty && rupStep f c
  | c :: d :: rest => rupStep f c && verifyRupAux (c :: f) (d :: rest)

/-- Verify a complete RUP refutation proof ending at the empty clause `[]`. -/
def verifyRup (f : Cnf) (proof : List Clause) : Bool :=
  verifyRupAux f proof

private def nthClause : Cnf → Nat → Option Clause
  | [], _ => none
  | c :: _, 0 => some c
  | _ :: cs, n + 1 => nthClause cs n

private def rupStepLratAux (f : Cnf) (trail : List Lit) : List Nat → Bool
  | [] => false
  | idx :: rest =>
    match nthClause f idx with
    | none => false
    | some cl =>
      if isFalsified trail cl then
        true
      else
        match isUnit trail cl with
        | some u => rupStepLratAux f (u :: trail) rest
        | none => false

/-- Verify a hint-indexed LRAT RUP derivation step for clause `c` using clause indices `hints`. -/
def rupStepLrat (f : Cnf) (c : Clause) (hints : List Nat) : Bool :=
  let trail := c.map Lit.neg
  hasContradiction trail || rupStepLratAux f trail hints

private def verifyLratAux (f : Cnf) : List (Clause × List Nat) → Bool
  | [] => false
  | [(c, hints)] => c.isEmpty && rupStepLrat f c hints
  | (c, hints) :: d :: rest => rupStepLrat f c hints && verifyLratAux (c :: f) (d :: rest)

/-- Verify a complete hint-indexed LRAT refutation ending at the empty clause `[]`. -/
def verifyLrat (f : Cnf) (steps : List (Clause × List Nat)) : Bool :=
  verifyLratAux f steps

private theorem evalLit_neg (σ : Nat → Bool) (l : Lit) :
    evalLit σ l.neg = !(evalLit σ l) := by
  simp only [evalLit, Lit.neg]
  cases σ l.var <;> cases l.pos <;> rfl

private theorem any_eq_true_iff {α : Type} (p : α → Bool) :
    ∀ xs : List α, xs.any p = true ↔ ∃ x ∈ xs, p x = true
  | [] => by simp
  | x :: xs => by
    simp only [List.any_cons, Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro (hx | hxs)
      · exact ⟨x, Or.inl rfl, hx⟩
      · obtain ⟨y, hy, hpy⟩ := (any_eq_true_iff p xs).mp hxs
        exact ⟨y, Or.inr hy, hpy⟩
    · rintro ⟨y, rfl | hy, hpy⟩
      · exact Or.inl hpy
      · exact Or.inr ((any_eq_true_iff p xs).mpr ⟨y, hy, hpy⟩)

private theorem all_eq_true_iff {α : Type} (p : α → Bool) :
    ∀ xs : List α, xs.all p = true ↔ ∀ x ∈ xs, p x = true
  | [] => by simp
  | x :: xs => by
    simp only [List.all_cons, Bool.and_eq_true, List.mem_cons]
    constructor
    · rintro ⟨hx, hxs⟩ y (rfl | hy)
      · exact hx
      · exact (all_eq_true_iff p xs).mp hxs y hy
    · intro h
      exact ⟨h x (Or.inl rfl), (all_eq_true_iff p xs).mpr (fun y hy => h y (Or.inr hy))⟩

private def SatTrail (σ : Nat → Bool) (trail : List Lit) : Prop :=
  ∀ l ∈ trail, evalLit σ l = true

private theorem hasLit_sound {σ : Nat → Bool} {trail : List Lit} {l : Lit}
    (ht : SatTrail σ trail) (hl : hasLit trail l = true) : evalLit σ l = true := by
  obtain ⟨x, hx, hxeq⟩ := (any_eq_true_iff (fun x => decide (x = l)) trail).mp hl
  have heq : x = l := of_decide_eq_true hxeq
  subst heq
  exact ht x hx

private theorem hasContradiction_sound {σ : Nat → Bool} {trail : List Lit}
    (ht : SatTrail σ trail) (hc : hasContradiction trail = true) : False := by
  obtain ⟨l, hl, hneg⟩ := (any_eq_true_iff (fun l => hasLit trail l.neg) trail).mp hc
  have h1 : evalLit σ l = true := ht l hl
  have h2 : evalLit σ l.neg = true := hasLit_sound ht hneg
  rw [evalLit_neg, h1] at h2
  cases h2

private theorem isFalsified_sound {σ : Nat → Bool} {trail : List Lit} {c : Clause}
    (ht : SatTrail σ trail) (hf : isFalsified trail c = true) : evalClause σ c = false := by
  cases hc : evalClause σ c with
  | false => rfl
  | true =>
    obtain ⟨l, hl, hval⟩ := (any_eq_true_iff (evalLit σ) c).mp hc
    have hneg : hasLit trail l.neg = true :=
      (all_eq_true_iff (fun x => hasLit trail x.neg) c).mp hf l hl
    have h2 : evalLit σ l.neg = true := hasLit_sound ht hneg
    rw [evalLit_neg, hval] at h2
    cases h2

private theorem mem_filter_iff {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (y : α), y ∈ xs.filter p ↔ y ∈ xs ∧ p y = true
  | [], y => by simp
  | x :: xs, y => by
    cases hpx : p x <;> simp only [List.filter, hpx, List.mem_cons]
    · constructor
      · intro hy
        obtain ⟨hy1, hy2⟩ := (mem_filter_iff p xs y).mp hy
        exact ⟨Or.inr hy1, hy2⟩
      · rintro ⟨rfl | hy1, hy2⟩
        · rw [hpx] at hy2; cases hy2
        · exact (mem_filter_iff p xs y).mpr ⟨hy1, hy2⟩
    · constructor
      · rintro (rfl | hy)
        · exact ⟨Or.inl rfl, hpx⟩
        · obtain ⟨hy1, hy2⟩ := (mem_filter_iff p xs y).mp hy
          exact ⟨Or.inr hy1, hy2⟩
      · rintro ⟨rfl | hy1, hy2⟩
        · exact Or.inl rfl
        · exact Or.inr ((mem_filter_iff p xs y).mpr ⟨hy1, hy2⟩)

private theorem isUnit_sound {σ : Nat → Bool} {trail : List Lit} {c : Clause} {u : Lit}
    (ht : SatTrail σ trail) (hc : evalClause σ c = true) (hu : isUnit trail c = some u) :
    evalLit σ u = true := by
  unfold isUnit at hu
  cases hsat : c.any (fun l => hasLit trail l)
  · rw [hsat] at hu
    dsimp only at hu
    cases hfilt : c.filter (fun l => !(hasLit trail l.neg)) with
    | nil => rw [hfilt] at hu; cases hu
    | cons a rest =>
      cases rest with
      | nil =>
        rw [hfilt] at hu
        injection hu with hau
        subst hau
        obtain ⟨l, hl, hval⟩ := (any_eq_true_iff (evalLit σ) c).mp hc
        cases hneg : hasLit trail l.neg with
        | true =>
          have h2 : evalLit σ l.neg = true := hasLit_sound ht hneg
          rw [evalLit_neg, hval] at h2
          cases h2
        | false =>
          have hmem : l ∈ c.filter (fun x => !(hasLit trail x.neg)) :=
            (mem_filter_iff _ c l).mpr ⟨hl, by simp [hneg]⟩
          rw [hfilt] at hmem
          simp only [List.mem_singleton] at hmem
          subst hmem
          exact hval
      | cons b rest' => rw [hfilt] at hu; cases hu
  · rw [hsat] at hu; cases hu

private theorem mem_filterMap_iff {α β : Type} (g : α → Option β) :
    ∀ (xs : List α) (y : β), y ∈ xs.filterMap g ↔ ∃ x ∈ xs, g x = some y
  | [], y => by simp
  | x :: xs, y => by
    cases hgx : g x <;> simp only [List.filterMap, hgx, List.mem_cons]
    · constructor
      · intro hy
        obtain ⟨a, ha, hga⟩ := (mem_filterMap_iff g xs y).mp hy
        exact ⟨a, Or.inr ha, hga⟩
      · rintro ⟨a, rfl | ha, hga⟩
        · rw [hgx] at hga; cases hga
        · exact (mem_filterMap_iff g xs y).mpr ⟨a, ha, hga⟩
    · constructor
      · rintro (rfl | hy)
        · exact ⟨x, Or.inl rfl, hgx⟩
        · obtain ⟨a, ha, hga⟩ := (mem_filterMap_iff g xs y).mp hy
          exact ⟨a, Or.inr ha, hga⟩
      · rintro ⟨a, rfl | ha, hga⟩
        · rw [hgx] at hga; injection hga with hba; exact Or.inl hba.symm
        · exact Or.inr ((mem_filterMap_iff g xs y).mpr ⟨a, ha, hga⟩)

private theorem rupLoop_sound {σ : Nat → Bool} {f : Cnf} (hf : evalCnf σ f = true) :
    ∀ (fuel : Nat) (trail : List Lit), SatTrail σ trail → rupLoop f trail fuel = true → False
  | 0, _, _, h => by simp [rupLoop] at h
  | fuel + 1, trail, ht, h => by
    unfold rupLoop at h
    cases hconf : f.any (isFalsified trail)
    · rw [hconf] at h
      dsimp only at h
      cases hemp : (f.filterMap (isUnit trail)).isEmpty
      · rw [hemp] at h
        dsimp only at h
        have ht' : SatTrail σ (f.filterMap (isUnit trail) ++ trail) := by
          intro l hl
          simp only [List.mem_append] at hl
          cases hl with
          | inl hlu =>
            obtain ⟨cl, hclf, hunit⟩ := (mem_filterMap_iff (isUnit trail) f l).mp hlu
            have hcl : evalClause σ cl = true := (all_eq_true_iff (evalClause σ) f).mp hf cl hclf
            exact isUnit_sound ht hcl hunit
          | inr hlt => exact ht l hlt
        cases hcontra : hasContradiction (f.filterMap (isUnit trail) ++ trail)
        · rw [hcontra] at h
          exact rupLoop_sound hf fuel (f.filterMap (isUnit trail) ++ trail) ht' h
        · exact hasContradiction_sound ht' hcontra
      · rw [hemp] at h; cases h
    · obtain ⟨cl, hclf, hfal⟩ := (any_eq_true_iff (isFalsified trail) f).mp hconf
      have hcl : evalClause σ cl = true := (all_eq_true_iff (evalClause σ) f).mp hf cl hclf
      have hfalse := isFalsified_sound ht hfal
      rw [hcl] at hfalse
      cases hfalse

/-- Soundness of `rupStep`: if `rupStep f c = true`, every satisfying assignment of `f` satisfies `c`. -/
theorem rupStep_sound (f : Cnf) (c : Clause) (h : rupStep f c = true) :
    ∀ σ : Nat → Bool, evalCnf σ f = true → evalClause σ c = true := by
  intro σ hf
  cases hc : evalClause σ c with
  | true => rfl
  | false =>
    exfalso
    have ht : SatTrail σ (c.map Lit.neg) := by
      intro l hl
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      have hxval : evalLit σ x = false := by
        cases hxv : evalLit σ x with
        | false => rfl
        | true =>
          have htrue : evalClause σ c = true := (any_eq_true_iff (evalLit σ) c).mpr ⟨x, hx, hxv⟩
          rw [hc] at htrue
          cases htrue
      rw [evalLit_neg, hxval]
      rfl
    unfold rupStep at h
    cases hcontra : hasContradiction (c.map Lit.neg)
    · rw [hcontra] at h
      exact rupLoop_sound hf (f.length + 1) (c.map Lit.neg) ht h
    · exact hasContradiction_sound ht hcontra

private theorem verifyRupAux_sound :
    ∀ (f : Cnf) (proof : List Clause),
      verifyRupAux f proof = true → ∀ σ : Nat → Bool, evalCnf σ f = false
  | _, [], h, _ => by simp [verifyRupAux] at h
  | f, [c], h, σ => by
    simp only [verifyRupAux, Bool.and_eq_true] at h
    cases hf : evalCnf σ f with
    | false => rfl
    | true =>
      cases c with
      | nil =>
        have hsat : evalClause σ [] = true := rupStep_sound f [] h.2 σ hf
        simp [evalClause] at hsat
      | cons _ _ =>
        cases h.1
  | f, c :: d :: rest, h, σ => by
    simp only [verifyRupAux, Bool.and_eq_true] at h
    cases hf : evalCnf σ f with
    | false => rfl
    | true =>
      have hcsat : evalClause σ c = true := rupStep_sound f c h.1 σ hf
      have hcf : evalCnf σ (c :: f) = true := by
        simp only [evalCnf, List.all_cons, Bool.and_eq_true]
        exact ⟨hcsat, hf⟩
      have hfalse := verifyRupAux_sound (c :: f) (d :: rest) h.2 σ
      rw [hcf] at hfalse
      cases hfalse

/-- Soundness of `verifyRup`: a valid RUP refutation certifies unsatisfiability with zero axioms. -/
theorem verifyRup_sound (f : Cnf) (proof : List Clause) (h : verifyRup f proof = true) : Unsat f :=
  verifyRupAux_sound f proof h

private theorem nthClause_mem :
    ∀ (f : Cnf) (idx : Nat) (cl : Clause), nthClause f idx = some cl → cl ∈ f
  | [], _, _, h => by cases h
  | c :: _, 0, cl, h => by injection h with hcl; subst hcl; exact List.mem_cons.mpr (Or.inl rfl)
  | _ :: cs, n + 1, cl, h => List.mem_cons.mpr (Or.inr (nthClause_mem cs n cl h))

private theorem rupStepLratAux_sound {σ : Nat → Bool} {f : Cnf} (hf : evalCnf σ f = true) :
    ∀ (hints : List Nat) (trail : List Lit),
      SatTrail σ trail → rupStepLratAux f trail hints = true → False
  | [], _, _, h => by simp [rupStepLratAux] at h
  | idx :: rest, trail, ht, h => by
    unfold rupStepLratAux at h
    cases hnth : nthClause f idx with
    | none => rw [hnth] at h; cases h
    | some cl =>
      rw [hnth] at h
      have hclf : cl ∈ f := nthClause_mem f idx cl hnth
      have hcl : evalClause σ cl = true := (all_eq_true_iff (evalClause σ) f).mp hf cl hclf
      cases hfal : isFalsified trail cl
      · rw [hfal] at h
        dsimp only at h
        cases hunit : isUnit trail cl with
        | none => rw [hunit] at h; cases h
        | some u =>
          rw [hunit] at h
          have ht' : SatTrail σ (u :: trail) := by
            intro l hl
            simp only [List.mem_cons] at hl
            cases hl with
            | inl hlu => subst hlu; exact isUnit_sound ht hcl hunit
            | inr hlt => exact ht l hlt
          exact rupStepLratAux_sound hf rest (u :: trail) ht' h
      · have hfalse := isFalsified_sound ht hfal
        rw [hcl] at hfalse
        cases hfalse

/-- Soundness of `rupStepLrat`: if `rupStepLrat f c hints = true`, `f` implies `c`. -/
theorem rupStepLrat_sound (f : Cnf) (c : Clause) (hints : List Nat)
    (h : rupStepLrat f c hints = true) :
    ∀ σ : Nat → Bool, evalCnf σ f = true → evalClause σ c = true := by
  intro σ hf
  cases hc : evalClause σ c with
  | true => rfl
  | false =>
    exfalso
    have ht : SatTrail σ (c.map Lit.neg) := by
      intro l hl
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      have hxval : evalLit σ x = false := by
        cases hxv : evalLit σ x with
        | false => rfl
        | true =>
          have htrue : evalClause σ c = true := (any_eq_true_iff (evalLit σ) c).mpr ⟨x, hx, hxv⟩
          rw [hc] at htrue
          cases htrue
      rw [evalLit_neg, hxval]
      rfl
    unfold rupStepLrat at h
    cases hcontra : hasContradiction (c.map Lit.neg)
    · rw [hcontra] at h
      exact rupStepLratAux_sound hf hints (c.map Lit.neg) ht h
    · exact hasContradiction_sound ht hcontra

private theorem verifyLratAux_sound :
    ∀ (f : Cnf) (steps : List (Clause × List Nat)),
      verifyLratAux f steps = true → ∀ σ : Nat → Bool, evalCnf σ f = false
  | _, [], h, _ => by simp [verifyLratAux] at h
  | f, [(c, hints)], h, σ => by
    simp only [verifyLratAux, Bool.and_eq_true] at h
    cases hf : evalCnf σ f with
    | false => rfl
    | true =>
      cases c with
      | nil =>
        have hsat : evalClause σ [] = true := rupStepLrat_sound f [] hints h.2 σ hf
        simp [evalClause] at hsat
      | cons _ _ =>
        cases h.1
  | f, (c, hints) :: d :: rest, h, σ => by
    simp only [verifyLratAux, Bool.and_eq_true] at h
    cases hf : evalCnf σ f with
    | false => rfl
    | true =>
      have hcsat : evalClause σ c = true := rupStepLrat_sound f c hints h.1 σ hf
      have hcf : evalCnf σ (c :: f) = true := by
        simp only [evalCnf, List.all_cons, Bool.and_eq_true]
        exact ⟨hcsat, hf⟩
      have hfalse := verifyLratAux_sound (c :: f) (d :: rest) h.2 σ
      rw [hcf] at hfalse
      cases hfalse

/-- Soundness of `verifyLrat`: a valid hint-indexed LRAT refutation certifies unsatisfiability with zero axioms. -/
theorem verifyLrat_sound (f : Cnf) (steps : List (Clause × List Nat))
    (h : verifyLrat f steps = true) : Unsat f :=
  verifyLratAux_sound f steps h

end Targets.CertKit.Lrat
