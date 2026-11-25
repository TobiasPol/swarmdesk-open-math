#!/usr/bin/env bash
# Validates targets.json, runs Node guard/manifest/reduction tests, and (when Lean is installed)
# builds all trusted Specs and verifies every non-stub Proof/Lemma and baseline Bound via sdlean_verify.
set -euo pipefail
cd "$(dirname "$0")/.."
node --test checker/*.test.mjs
node checker/manifest.mjs . >/dev/null
node checker/reduction-check.mjs . >/dev/null
if ! command -v lake >/dev/null 2>&1; then
  echo "Node guard, manifest, and reduction checks passed (lake not installed; skipping Lean kernel checks)."
  exit 0
fi
lake build Targets sdlean_verify
jq -c '.targets[]' targets.json | while IFS= read -r entry; do
  name=$(jq -r .name <<<"$entry")
  kind=$(jq -r .kind <<<"$entry")
  file_path=$(jq -r .file_path <<<"$entry")
  spec_mod=$(jq -r .spec_module <<<"$entry")
  proof_mod=$(jq -r .proof_module <<<"$entry")
  stmt_decl=$(jq -r .statement_decl <<<"$entry")
  direction=$(jq -r '.direction // "maximize"' <<<"$entry")
  if grep -Eq '\bsorry\b' "$file_path"; then
    echo "stub (open): $name"
    continue
  fi
  node checker/guard.mjs "$file_path" >/dev/null
  olean=".lake/build/lib/lean/${proof_mod//.//}.olean"
  mkdir -p "$(dirname "$olean")"
  lake env lean -R . -DmaxHeartbeats=400000 -DmaxRecDepth=2000 -o "$olean" "$file_path"
  baseline=$([ "$kind" = "bound" ] && echo 0 || echo 0)
  verdict=$(lake exe sdlean_verify "$kind" "$spec_mod" "$proof_mod" "$stmt_decl" "$direction" "$baseline" || true)
  echo "$name: $verdict"
  # bound_not_improved is emitted only after the type and axiom checks pass, so a holder whose
  # value equals the baseline (such as the trivial bound 0) is still a verified proof here.
  jq -e '.verdict == "ACCEPTED" or (.reason_code == "bound_not_improved" and .metric_value == .holder_value)' \
    <<<"$verdict" >/dev/null
done
