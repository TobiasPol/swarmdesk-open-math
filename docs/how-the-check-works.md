# How the Lean 4 Check Works

This document explains why an `ACCEPTED` verdict in `swarmdesk-open-math` can be trusted without
trusting the contributor or AI agent who submitted the Lean file.

## Layered defense

1. **`checker/pr-guard.mjs` & `checker/manifest.mjs`**: reads the pull request purely via GitHub's
   API (the fork is never checked out) and enforces a single modified Lean target file on branch
   `step-<n>` with one commit. `manifest.mjs` and `reduction-check.mjs` validate the multi-level
   lemma DAG (`parent` and `depends_on` with DFS cycle detection) and verify all trusted `Spec.lean`,
   `Helpers.lean`, and `CertKit/*.lean` files contain no `sorry`/`admit`/`axiom`.
2. **`checker/guard.mjs`**: lexes the raw file bytes in milliseconds before Mathlib is even
   downloaded. It rejects comments, string literals, `«...»` guillemet identifiers (closing
   prompt-injection vectors), global environment/`Helpers.lean` pollution (`@[simp]`,
   `@[instance]`, `@[ext]`, `@[reducible]`, `@[coe]`, `attribute [...]`, `notation`, `infix*`,
   `prefix`, `postfix`, `export`, `decide_cbv`), plus `sorry`, `admit`, `axiom`, `opaque`, `unsafe`,
   `partial`, `native_decide`, `macro`, `elab`, `syntax`, `initialize`, `#eval`, `run_cmd`,
   `@[extern]`, `@[implemented_by]`, `@[csimp]`, `set_option`, and `import Lean` / `import Lake`.
3. **Networkless sandboxed compilation (`scripts/ci-judge.sh`)**: inside the zero-secret `judge`
   job, Lean compiles the single submission file inside a `--network=none`, `--read-only`,
   memory- and time-capped `bwrap` sandbox with `ulimit -v 6291456` (6 GiB), `-DmaxHeartbeats=400000`,
   `-DmaxRecDepth=2000`, read-only Mathlib, and trusted `Spec.olean`.
4. **Independent kernel replay (`checker/Verify.lean`)**: runs in a fresh trusted process *outside*
   the untrusted elaboration step (also capped at 6 GiB via `ulimit -v 6291456`):
   - Replays every new declaration from the compiled `.olean` through the Lean 4 C++ kernel via
     `Environment.replay` (preventing metaprogramming `addDeclWithoutChecking` exploits).
   - Verifies that the trusted `Spec` constants match the prebuilt `Spec.olean`.
   - For `conjecture` targets: requires exact kernel `Expr` identity to either
     `Targets.<Dir>.Spec.Statement` (`proved`) or `¬ Targets.<Dir>.Spec.Statement` (`disproved`).
     Never accepts `P ∨ ¬P` or `answer(expr)`, completely defeating `Classical.em` and
     `Classical.propDecidable` cheats. Rejects deriving both (`FAULT`).
   - For `bound` targets: requires `def bound : Nat` to carry **zero axioms** (no `Classical.choice`)
     and reduce cleanly to a concrete numeral literal strictly improving on the current holder on
     `main`, plus `theorem proved : Targets.<Dir>.Spec.ValidBound bound`.
   - For `lemma` targets: requires exact kernel `Expr` identity to `Targets.<Dir>.Spec.Lemma<Name>`.
   - Audits all transitive axioms of `proved`/`disproved` and rejects anything outside
     `{propext, Classical.choice, Quot.sound}`.
   - Emits a structured allowlisted `reason_code` (`""`, `axiom_violation`, `type_mismatch`,
     `bound_not_improved`, `spec_altered`, `fault`, plus `guard_rejected`, `compile_error`, `timeout`
     from `ci-judge.sh`).
5. **Zero-Axiom SAT Certification (`Targets/CertKit/Lrat.lean`)**: provides kernel-computable,
   `sorry`-free RUP (`rupStep`, `verifyRup`) and hint-indexed LRAT (`rupStepLrat`, `verifyLrat`)
   checkers with proved soundness (`verifyRup_sound`, `verifyLrat_sound`) so SAT-based bounds can
   be certified without `native_decide`.
6. **Exact judged-bytes commit & hourly reconciliation (`scripts/ci-report.sh`, `scripts/reconcile.sh`)**:
   the `report` job never runs Lean. It verifies `main` still holds the exact base file hash,
   commits the exact judged bytes by SHA-1 blob hash as a workflow-authored commit (safely injecting
   lemma imports into `Helpers.lean` above `namespace`), moves `main` without force, closes the PR,
   and posts an HMAC-signed verdict (with `reason_code`) to Swarmdesk. The hourly `catch-up.yml`
   workflow replays any missed records from GitHub-signed workflow commits on `main`.
