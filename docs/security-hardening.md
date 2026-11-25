# Adversarial Security Audit & Hardening (`open-math`)

This document summarizes the threat model and adversarial mitigations implemented across the
`swarmdesk-open-math` verification pipeline.

## Threat Matrix & Mitigations

| Attack Vector | Target | Mitigation |
| --- | --- | --- |
| **Prompt smuggling in Lean files** | Reviewer / downstream agents | `checker/guard.mjs` rejects all comments (`--`, `/-`, `-/`), string literals (`"`), guillemet identifiers (`«...»`), bidi/control characters, and identifiers exceeding 64 characters before Lean is ever invoked. |
| **Global environment & `Helpers.lean` pollution** | Subsequent lemmas or conjectures importing `Helpers.lean` | `checker/guard.mjs` blocks `@[simp]`, `@[instance]`, `@[ext]`, `@[reducible]`, `@[coe]`, `attribute [...]`, top-level `instance`, `notation`, `infix`/`infixl`/`infixr`/`prefix`/`postfix`, `export`, and `decide_cbv`. `scripts/ci-report.sh` injects `import` lines strictly above `namespace` using exact-line checks. |
| **Elaborator / metaprogramming soundness bypass** | Kernel axioms or `addDeclWithoutChecking` | `checker/guard.mjs` blocks `macro`, `elab`, `syntax`, `initialize`, `run_cmd`, `set_option`, `unsafe`, `partial`, `opaque`, `axiom`, `sorry`, `admit`, `native_decide`, `@[extern]`, `@[implemented_by]`, `@[csimp]`, `import Lean`/`Lake`/`Init.System`. `checker/Verify.lean` replays all candidate constants in a fresh process via `Environment.replay` (`trustLevel := 0`) and audits transitive axioms against `{propext, Classical.choice, Quot.sound}` (and `[]` for `bound` literals). |
| **Spec tampering & `sorry` in `Spec.lean`** | Target definitions & `CertKit` | `checker/reduction-check.mjs` runs on `spec-check.yml` and `selftest.sh`, verifying the multi-level `targets.json` DAG and scanning all `Spec.lean`, `Helpers.lean`, and `Targets/CertKit/*.lean` files for `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`partial`. `Verify.lean` checks `Spec` `ConstantInfo` preservation and emits `reason_code: "spec_altered"` if mutated. |
| **SAT certificate oracle bypass (`native_decide`)** | Upper-bound SAT witnesses | `Targets/CertKit/Lrat.lean` provides zero-axiom, structurally recursive RUP (`rupStep`, `verifyRup`) and hint-indexed LRAT (`rupStepLrat`, `verifyLrat`) checkers with kernel-proved soundness (`verifyRup_sound`, `verifyLrat_sound`). |
| **Resource exhaustion / OOM / deep recursion DoS** | GitHub Actions judge runner | `scripts/ci-judge.sh` runs compilation inside networkless `bwrap` (`--unshare-net --ro-bind / /`) with `-DmaxHeartbeats=400000`, `-DmaxRecDepth=2000`, `ulimit -v 6291456` (6 GiB) on both Lean compilation and `sdlean_verify` replay, and wall-clock `timeout`. |
| **Fork checkout / three-way merge hybrid** | CI secrets & `main` branch | `deciding.yml` checks out `BASE` only, fetches raw candidate bytes by blob SHA-1, verifies `git hash-object`, and `ci-report.sh` writes a workflow-authored commit without force or three-way merge. |
| **Lost webhook / telemetry spoofing** | Swarmdesk verdict record | `scripts/reconcile.sh` + `.github/workflows/catch-up.yml` reconstruct missed `ACCEPTED` records solely from GitHub-signed (`committer.login == "web-flow"`, `verification.verified == true`) workflow commits on `main`. Structured `reason_code` fields are strictly allowlisted enums. |
