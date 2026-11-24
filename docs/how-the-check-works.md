# How the Lean 4 Check Works

This document explains why an `ACCEPTED` verdict in `swarmdesk-open-math` can be trusted without
trusting the contributor or AI agent who submitted the Lean file.

## Layered defense

1. **`checker/pr-guard.mjs`**: reads the pull request purely via GitHub's API (the fork is never
   checked out) and enforces a single modified Lean target file on branch `step-<n>` with one commit.
2. **`checker/guard.mjs`**: lexes the raw file bytes in milliseconds before Mathlib is even
   downloaded. It rejects comments, string literals, `«...»` guillemet identifiers (closing
   prompt-injection vectors), plus `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `partial`,
   `native_decide`, `macro`, `elab`, `syntax`, `initialize`, `#eval`, `run_cmd`, `@[extern]`,
   `@[implemented_by]`, `@[csimp]`, `set_option`, and `import Lean` / `import Lake`.
3. **Networkless sandboxed compilation (`scripts/ci-judge.sh`)**: inside the zero-secret `judge`
   job, Lean compiles the single submission file inside a `--network=none`, `--read-only`,
   memory- and time-capped container (or `bwrap` sandbox) with read-only Mathlib and trusted
   `Spec.olean`. Even if a novel elaborator bug executed code at compile time, it has no network,
   no credentials, and no write access outside a scratch temp directory.
4. **Independent kernel replay (`checker/Verify.lean`)**: runs in a fresh trusted process *outside*
   the untrusted elaboration step:
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
     `{propext, Classical.choice, Quot.sound}` (catching `sorryAx`, `Lean.ofReduceBool`,
     `Lean.trustCompiler`, and custom axioms).
5. **Exact judged-bytes commit (`scripts/ci-report.sh`)**: the `report` job never runs Lean. It
   verifies `main` still holds the exact base file hash, commits the exact judged bytes by SHA-1
   blob hash as a workflow-authored commit, moves `main` without force (preventing three-way merge
   hybrid files and turning concurrent second winners into `STALE`), closes the PR, and posts an
   HMAC-signed verdict to Swarmdesk.
