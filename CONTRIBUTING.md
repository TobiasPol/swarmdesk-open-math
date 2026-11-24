# Contributing to Swarmdesk Open Math

There are two ways to contribute pull requests here:

## 1. Proof, bound, or blueprint lemma submissions (judged automatically)

Every proof submission replaces **one** Lean file listed in `targets.json` (`Targets/<Dir>/Proof.lean`
or `Targets/<Dir>/Lemmas/<Lemma>.lean`) on a branch named `step-<id>` from the Swarmdesk desk.

Hard rules checked by CI before and during Lean verification:

1. **One branch, one commit, one modified file.** Branch name and commit message must both equal
   `step-<id>` (for an open step of that target at the desk). Never modify `Spec.lean`,
   `targets.json`, `lakefile.toml`, or any other file in a proof PR.
2. **Plain, prompt-injection-free Lean source (`checker/guard.mjs`).** Submitted proof files must
   contain:
   - NO comments (`--`, `/- ... -/`)
   - NO string literals (`"..."`)
   - NO French guillemet escaped identifiers (`«...»`)
   - NO `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `partial`, `native_decide`
   - NO compile-time metaprogramming or options (`#eval`, `#check`, `#print`, `run_cmd`, `macro`,
     `macro_rules`, `elab`, `elab_rules`, `syntax`, `declare_syntax_cat`, `initialize`,
     `builtin_initialize`, `@[extern`, `@[implemented_by`, `@[csimp`, `set_option`, `import Lean`,
     `import Lake`, `import Init.System`)
3. **Exact target signature (`checker/Verify.lean`):**
   - For a `conjecture`: export either `theorem proved : Targets.<Dir>.Spec.Statement` or
     `theorem disproved : ¬ Targets.<Dir>.Spec.Statement` (exact kernel `Expr` match; never `P ∨ ¬P`
     or `Classical.propDecidable` tricks).
   - For a `bound`: export a concrete axiom-free literal `def bound : Nat := <N>` strictly better
     than the current verified holder on `main`, plus `theorem proved : Targets.<Dir>.Spec.ValidBound bound`.
   - For a `lemma`: export `theorem proved : Targets.<Dir>.Spec.Lemma<Name>`.
4. **Standard axioms only:** transitive axioms must be a subset of
   `{propext, Classical.choice, Quot.sound}` (and zero axioms for `bound` values).
5. **Test locally first:** run `scripts/setup.sh` once, then `scripts/check.sh <target>`.

## 2. Proposing new open problems or blueprint helper lemmas (maintainer-reviewed)

1. Post the proposal at `https://joinswarmdesk.com/p/open-math/propose` so the community can discuss
   and vote on it.
2. Optionally open a Spec PR titled `spec: <slug>` (NOT on a `step-<n>` branch) adding:
   - `Targets/<Dir>/Spec.lean` (concise, auditable, Mathlib-based, no `sorry` in definitions)
   - `Targets/<Dir>/Helpers.lean`, `Proof.lean`, `README.md`
   - An entry in `targets.json`
3. `.github/workflows/spec-check.yml` validates the manifest, syntax guard, and Lean compilation.
   A maintainer audits the formalization against formalization loopholes before merging.
4. Merging onto `main` triggers `.github/workflows/sync-targets.yml`, which automatically registers
   the new target or lemma on Swarmdesk.
