import Lean

/-!
Independent kernel-replay verifier for `swarmdesk-open-math`.
Inspired by Lean's `lean4checker` and `SafeVerify`:
1. Loads the trusted `Spec` module independently and records its exact `ConstantInfo`.
2. Replays every new declaration introduced by the compiled submission `.olean` through the Lean 4
   C++ kernel (`Environment.replay`), defeating elaborator `addDeclWithoutChecking` exploits.
3. Checks exact kernel `Expr` identity against the target specification:
   - `conjecture`: either `proved : Spec.Statement` or `disproved : ¬ Spec.Statement` (never `P ∨ ¬P`
     and never `Classical.propDecidable`). Rejects proving both as `FAULT`.
   - `lemma`: `proved : Spec.Lemma<Name>`.
   - `bound`: `def bound : Nat` with ZERO axioms (no `Classical.choice`) reducing to a concrete
     literal strictly improving on `holderBound`, plus `theorem proved : Spec.ValidBound bound`.
4. Audits transitive axioms of the target theorem to be a subset of
   `{propext, Classical.choice, Quot.sound}`.
-/

open Lean

private def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

private partial def collectTransitiveAxiomsLoop
    (env : Environment) (work : List Name) (seen axioms : NameSet) : NameSet :=
  match work with
  | [] => axioms
  | n :: rest =>
    if seen.contains n then
      collectTransitiveAxiomsLoop env rest seen axioms
    else
      let seen' := seen.insert n
      match env.find? n with
      | none => collectTransitiveAxiomsLoop env rest seen' axioms
      | some (.axiomInfo _) => collectTransitiveAxiomsLoop env rest seen' (axioms.insert n)
      | some info =>
        let deps := info.getUsedConstantsAsSet.toList
        collectTransitiveAxiomsLoop env (deps ++ rest) seen' axioms

private def collectTransitiveAxioms (env : Environment) (root : Name) : NameSet :=
  collectTransitiveAxiomsLoop env [root] {} {}

private def checkAxioms (env : Environment) (decl : Name) (allowed : List Name) : Except String Unit := do
  let used := collectTransitiveAxioms env decl
  let bad := used.toList.filter fun a => !allowed.contains a
  if !bad.isEmpty then
    throw s!"unpermitted axioms used by {decl}: {bad}"

private def decodeNatLit : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .app (.app (.app (.const ``OfNat.ofNat _) (.const ``Nat _)) (.lit (.natVal n)))
      (.app (.const ``instOfNatNat _) (.lit (.natVal m))) =>
    if n == m then some n else none
  | _ => none

private def extractNatLit (env : Environment) (decl : Name) : Except String Nat := do
  checkAxioms env decl []
  let some info := env.find? decl
    | throw s!"missing bound definition {decl}"
  if !info.levelParams.isEmpty then
    throw s!"bound definition {decl} must not be universe-polymorphic"
  let some val := info.value?
    | throw s!"bound definition {decl} has no transparent value"
  match decodeNatLit val with
  | some n => pure n
  | none => throw s!"bound definition {decl} must be a concrete Nat literal"

private def checkTypeExact (env : Environment) (decl : Name) (expected : Expr) : Except String Unit := do
  let some info := env.find? decl
    | throw s!"missing theorem {decl}"
  if !info.levelParams.isEmpty then
    throw s!"theorem {decl} must not be universe-polymorphic"
  if info.type != expected then
    throw s!"type mismatch for {decl}: expected exact kernel term {expected}, got {info.type}"

private def verifySpecPreserved (specEnv candEnv : Environment) (specDecl : Name) : Except String Unit := do
  let some sInfo := specEnv.find? specDecl
    | throw s!"trusted Spec missing {specDecl}"
  let some cInfo := candEnv.find? specDecl
    | throw s!"candidate environment missing {specDecl}"
  if sInfo.type != cInfo.type || sInfo.value? != cInfo.value? then
    throw s!"Spec declaration {specDecl} was altered"

private def replayCandidate (specMod candMod : Name) : IO (Environment × Environment) := do
  initSearchPath (← findSysroot)
  let specEnv ← importModules #[{ module := specMod }] {} (trustLevel := 0)
  let candEnv ← importModules #[{ module := candMod }] {} (trustLevel := 0)
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  for i in [:candEnv.header.moduleNames.size] do
    if (specEnv.getModuleIdx? candEnv.header.moduleNames[i]!).isNone then
      for info in candEnv.header.moduleData[i]!.constants do
        if !specEnv.contains info.name then
          newConsts := newConsts.insert info.name info
  -- Replay all new constants through the Lean kernel inside a fresh environment.
  let replayed ← specEnv.replay newConsts
  pure (specEnv, replayed)

private def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" " "

private def emitVerdict (verdict resolution reason : String) (metric holder : Option Nat := none) : IO Unit := do
  let mStr := match metric with | some n => s!"{n}" | none => "null"
  let hStr := match holder with | some n => s!"{n}" | none => "null"
  IO.println s!"\{\"verdict\":\"{verdict}\",\"resolution\":\"{resolution}\",\"reason\":\"{jsonEscape reason}\",\"metric_value\":{mStr},\"holder_value\":{hStr}}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [kind, specModStr, candModStr, specDeclStr, direction, holderBoundStr] =>
    let specMod := specModStr.toName
    let candMod := candModStr.toName
    let specDecl := specDeclStr.toName
    try
      let (specEnv, env) ← replayCandidate specMod candMod
      match verifySpecPreserved specEnv env specDecl with
      | .error msg =>
        emitVerdict "REJECTED" "" msg
        return 1
      | .ok () => pure ()

      let provedName := candMod ++ `proved
      let disprovedName := candMod ++ `disproved
      let specConst := Expr.const specDecl []
      let notSpec := Expr.app (Expr.const ``Not []) specConst

      if kind == "conjecture" then
        let hasProved := env.contains provedName
        let hasDisproved := env.contains disprovedName
        if hasProved && hasDisproved then
          emitVerdict "FAULT" "" "submission proved both Statement and ¬Statement"
          return 1
        if hasProved then
          match checkTypeExact env provedName specConst *> checkAxioms env provedName allowedAxioms with
          | .ok () => emitVerdict "ACCEPTED" "proved" ""; return 0
          | .error msg => emitVerdict "REJECTED" "" msg; return 1
        else if hasDisproved then
          match checkTypeExact env disprovedName notSpec *> checkAxioms env disprovedName allowedAxioms with
          | .ok () => emitVerdict "ACCEPTED" "disproved" ""; return 0
          | .error msg => emitVerdict "REJECTED" "" msg; return 1
        else
          emitVerdict "REJECTED" "" s!"must define {provedName} or {disprovedName}"
          return 1
      else if kind == "lemma" then
        match checkTypeExact env provedName specConst *> checkAxioms env provedName allowedAxioms with
        | .ok () => emitVerdict "ACCEPTED" "proved" ""; return 0
        | .error msg => emitVerdict "REJECTED" "" msg; return 1
      else if kind == "bound" then
        let boundName := candMod ++ `bound
        let some holderVal := holderBoundStr.toNat?
          | do emitVerdict "FAULT" "" s!"invalid holder bound {holderBoundStr}"; return 1
        match extractNatLit env boundName with
        | .error msg => emitVerdict "REJECTED" "" msg; return 1
        | .ok candVal =>
          let expected := Expr.app specConst (Expr.const boundName [])
          let expectedLit := Expr.app specConst (Expr.lit (.natVal candVal))
          let typeOk :=
            match checkTypeExact env provedName expected with
            | .ok () => .ok ()
            | .error _ => checkTypeExact env provedName expectedLit
          match typeOk *> checkAxioms env provedName allowedAxioms with
          | .error msg => emitVerdict "REJECTED" "" msg (some candVal) (some holderVal); return 1
          | .ok () =>
            let better := if direction == "minimize" then candVal < holderVal else candVal > holderVal
            if !better then
              emitVerdict "REJECTED" "" s!"bound {candVal} does not improve on current holder {holderVal}" (some candVal) (some holderVal)
              return 1
            emitVerdict "ACCEPTED" "improved" "" (some candVal) (some holderVal)
            return 0
      else
        emitVerdict "FAULT" "" s!"unknown target kind {kind}"
        return 1
    catch e =>
      emitVerdict "REJECTED" "" s!"kernel replay error: {e}"
      return 1
  | _ =>
    IO.eprintln "usage: sdlean_verify <kind> <SpecModule> <CandModule> <SpecDecl> <direction> <holderBound>"
    return 2
