#!/usr/bin/env bash
# Locally checks one target file (conjecture, bound, or blueprint lemma) with the exact same
# syntax guard and Lean 4 kernel-replay verifier that CI runs.
#
#   scripts/check.sh <target-slug> [candidate-file.lean]
set -euo pipefail
cd "$(dirname "$0")/.."
target="${1:?usage: scripts/check.sh <target-slug> [candidate.lean]}"
entry=$(jq -c --arg t "$target" '.targets[] | select(.name == $t)' targets.json)
[ -n "$entry" ] || { echo "REJECTED (unknown target: $target)"; exit 1; }

file_path=$(jq -r .file_path <<<"$entry")
kind=$(jq -r .kind <<<"$entry")
spec_mod=$(jq -r .spec_module <<<"$entry")
proof_mod=$(jq -r .proof_module <<<"$entry")
stmt_decl=$(jq -r .statement_decl <<<"$entry")
direction=$(jq -r '.direction // "maximize"' <<<"$entry")
candidate="${2:-$file_path}"

guard_out=$(node checker/guard.mjs "$candidate") || {
  echo "REJECTED ($(jq -r .refused <<<"$guard_out"))"
  exit 1
}

holder_bound=0
if [ "$kind" = "bound" ]; then
  # Extract current verified holder bound literal from HEAD (or baseline_value if uncommitted).
  base_src=$(git show "HEAD:$file_path" 2>/dev/null || cat "$file_path")
  holder_bound=$(printf '%s\n' "$base_src" | sed -nE 's/^def[[:space:]]+bound[[:space:]]*:[[:space:]]*Nat[[:space:]]*:=[[:space:]]*([0-9]+).*/\1/p' | head -n1)
  holder_bound="${holder_bound:-$(jq -r '.baseline_value // 0' <<<"$entry")}"
fi

if [ "$candidate" != "$file_path" ]; then
  cp "$candidate" "$file_path"
fi

helpers_mod="${spec_mod%.Spec}.Helpers"
lake build "$spec_mod" "$helpers_mod" sdlean_verify >/dev/null
olean=".lake/build/lib/lean/${proof_mod//.//}.olean"
mkdir -p "$(dirname "$olean")"
lake env lean -R . -DmaxHeartbeats=400000 -o "$olean" "$file_path"
verdict=$(lake exe sdlean_verify "$kind" "$spec_mod" "$proof_mod" "$stmt_decl" "$direction" "$holder_bound")
echo "$verdict"
[ "$(jq -r .verdict <<<"$verdict")" = "ACCEPTED" ]
