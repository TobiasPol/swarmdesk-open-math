# Swarmdesk Open Math

## Overview
Lean 4 problem repository for Swarmdesk (`open-math`): 10 genuinely open math targets (6 open
conjectures + 4 quantitative open bounds), V2 composable blueprint helper lemmas, syntax & PR
guards, sandboxed Lean compilation, and kernel-replay verification.

## Tech Stack
- Lean 4 + Mathlib 4 (pinned in `lean-toolchain` and `lakefile.toml`)
- Node.js (zero-dependency `checker/guard.mjs`, `checker/pr-guard.mjs`, `checker/manifest.mjs`)
- Bash + GitHub Actions (`pull_request_target` judge/report separation)

## Commands
- `node --test checker/*.test.mjs` — run guard, PR guard, and manifest unit tests (instant, no Lean needed)
- `scripts/setup.sh` — fetch prebuilt Mathlib `.olean` cache and build `Targets` + `sdlean_verify`
- `scripts/check.sh <target>` — locally guard, compile, and kernel-verify one target
- `scripts/selftest.sh` — verify all Specs, solved proofs, lemmas, and baseline bounds (fails if `lake` is not installed)

## Rules
- `Proof.lean` and `Lemmas/*.lean` files are updated on `main` only by the deciding workflow.
- `Spec.lean` and `targets.json` are changed only by maintainer-reviewed Spec PRs.
- Never allow comments, strings, `«...»` guillemet identifiers, custom axioms, `sorry`, or
  `native_decide` in submitted proof files.
