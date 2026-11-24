#!/usr/bin/env bash
# Sets up the local Lean 4 environment with prebuilt Mathlib .olean files (no compiling Mathlib!).
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null || { echo "Install elan first: https://github.com/leanprover/elan"; exit 1; }
echo "Fetching prebuilt Mathlib cache..."
lake exe cache get
echo "Building trusted Specs and sdlean_verify..."
lake build Targets sdlean_verify
echo "Ready. Run scripts/check.sh <target> to judge a local Lean proof."
