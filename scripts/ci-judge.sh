#!/usr/bin/env bash
# Judges one Lean 4 pull request from a clean checkout of BASE. Never checks out the fork.
# Fetches ONLY the raw bytes of the single modified Lean file by blob SHA, runs guard.mjs,
# compiles in an isolated networkless sandbox (bwrap when available) with bounded memory/recursion,
# and replays the .olean through the Lean 4 kernel via sdlean_verify.
set -euo pipefail
: "${PR:?}" "${REPO:?}" "${DEFAULT_BRANCH:?}" "${GH_TOKEN:?}" "${OUT:?}" "${RUN_URL:?}"
API=https://api.github.com
PROBLEM="${PROBLEM:-open-math}"
mkdir -p "$OUT/api"

printf '%s' "$PR" | grep -Eqx '[1-9][0-9]{0,6}' || { echo "bad pull request number"; exit 1; }

# write <verdict> <reason> [json object with more fields] [reason_code]
write() {
  local code="fault"
  if [ "$#" -ge 4 ] && [ -n "$4" ]; then
    code="$4"
  elif [ "$1" = "REJECTED" ]; then
    code="guard_rejected"
  fi
  jq -n --arg verdict "$1" --arg reason "$2" --arg reason_code "$code" \
    --argjson pr "$PR" --arg run_url "$RUN_URL" --argjson more "${3:-{\}}" \
    '$more + {verdict: $verdict, reason: $reason, reason_code: ($more.reason_code // $reason_code), pr: $pr, run_url: $run_url}' \
    > "$OUT/final.json"
  echo "$1 ($2)"
}
write FAULT "the check stopped before it reached a verdict" '{}' fault

get() {
  curl -sSf --proto '=https' --max-redirs 0 --max-filesize 20000000 \
    -H "Authorization: Bearer $GH_TOKEN" -H "Accept: ${3:-application/vnd.github+json}" \
    -H "X-GitHub-Api-Version: 2022-11-28" -o "$2" "$API/repos/$REPO/$1"
}

get "pulls/$PR" "$OUT/api/pr.json"
get "pulls/$PR/files?per_page=100" "$OUT/api/files.json"
head=$(jq -r '.head.sha // ""' "$OUT/api/pr.json")
printf '%s' "$head" | grep -Eqx '[0-9a-f]{40}' || { write REJECTED "the pull request has no head commit" '{}' guard_rejected; exit 0; }
get "git/trees/$head?recursive=1" "$OUT/api/tree.json"
get "pulls/$PR/commits?per_page=5" "$OUT/api/commits.json"

if ! guard=$(node checker/pr-guard.mjs pr "$OUT/api/pr.json" "$OUT/api/files.json" \
  "$OUT/api/tree.json" "$OUT/api/commits.json" targets.json "$REPO" "$DEFAULT_BRANCH"); then
  write REJECTED "$(jq -r '.refused // "the pull request was refused"' <<<"$guard")" '{}' guard_rejected
  exit 0
fi

target=$(jq -r .target <<<"$guard")
kind=$(jq -r .kind <<<"$guard")
file_path=$(jq -r .file_path <<<"$guard")
step=$(jq -r .step <<<"$guard")
blob=$(jq -r .blob <<<"$guard")
author=$(jq -r .author <<<"$guard")
holder_blob=$(git hash-object "$file_path")

entry=$(jq -c --arg t "$target" '.targets[] | select(.name == $t)' targets.json)
spec_mod=$(jq -r .spec_module <<<"$entry")
proof_mod=$(jq -r .proof_module <<<"$entry")
stmt_decl=$(jq -r .statement_decl <<<"$entry")
direction=$(jq -r '.direction // "maximize"' <<<"$entry")

meta=$(jq -c --arg holder "$holder_blob" --arg proof_mod "$proof_mod" \
  '{target, kind, file_path, proof_module: $proof_mod, step, head_sha: .head, author, candidate_blob: .blob, holder_blob: $holder}' <<<"$guard")

# Rate limits per author & PR (exact speed-race pattern).
curl -sSf --proto '=https' --max-redirs 0 --max-filesize 2000000 \
  -H "Authorization: Bearer $GH_TOKEN" -H "Accept: application/vnd.github+json" \
  -H "X-GitHub-Api-Version: 2022-11-28" -o "$OUT/api/mine.json" \
  "$API/search/issues?q=repo:$REPO+is:pr+is:open+author:$author&per_page=1"
total=$(jq -r '.comments // 0 | if type == "number" then . else 0 end' "$OUT/api/pr.json")
last=$(( (total + 99) / 100 )); [ "$last" -ge 1 ] || last=1
first=$(( last > 10 ? last - 9 : 1 ))
pages=()
for page in $(seq "$first" "$last"); do
  get "issues/$PR/comments?per_page=100&page=$page" "$OUT/api/comments-$page.json"
  pages+=("$OUT/api/comments-$page.json")
done
jq -s add "${pages[@]}" > "$OUT/api/comments.json"
if ! limits=$(node checker/pr-guard.mjs limits "$OUT/api/mine.json" "$OUT/api/comments.json"); then
  write REJECTED "$(jq -r '.refused // "the pull request was refused"' <<<"$limits")" "$meta" guard_rejected
  exit 0
fi

# Verify step is open at the Swarmdesk desk.
if [ -n "${SWARMDESK_URL:-}" ]; then
  printf '%s' "$SWARMDESK_URL" | grep -Eqx 'https://[a-z0-9.-]+' || { write FAULT "bad desk address" "$meta" fault; exit 0; }
  if ! curl -sSf --proto '=https' --max-time 20 -o "$OUT/api/steps.json" "$SWARMDESK_URL/p/$PROBLEM/steps.json"; then
    write FAULT "the desk could not be reached" "$meta" fault; exit 0
  fi
  if ! open=$(node checker/pr-guard.mjs step "$OUT/api/steps.json" "$step" "$target"); then
    write REJECTED "$(jq -r '.refused // "the step was refused"' <<<"$open")" "$meta" guard_rejected; exit 0
  fi
fi

# Fetch raw candidate bytes by SHA and run fast syntax/security guard BEFORE touching Lean.
get "git/blobs/$blob" "$OUT/candidate.lean" "application/vnd.github.raw"
if [ "$(git hash-object "$OUT/candidate.lean")" != "$blob" ]; then
  write FAULT "the file that arrived is not the file of the pull request" "$meta" fault; exit 0
fi
if ! src_guard=$(node checker/guard.mjs "$OUT/candidate.lean"); then
  write REJECTED "$(jq -r '.refused // "guard failed"' <<<"$src_guard")" "$meta" guard_rejected; exit 0
fi
proof_lines=$(jq -r '.lines // 0' <<<"$src_guard")

# Determine current verified bound for quantitative targets before overwriting working copy.
holder_bound=0
if [ "$kind" = "bound" ]; then
  holder_bound=$(sed -nE 's/^def[[:space:]]+bound[[:space:]]*:[[:space:]]*Nat[[:space:]]*:=[[:space:]]*([0-9]+).*/\1/p' "$file_path" | head -n1)
  holder_bound="${holder_bound:-$(jq -r '.baseline_value // 0' <<<"$entry")}"
fi

# Build trusted Specs, Helpers, CertKit, and verifier cleanly BEFORE compiling untrusted candidate bytes.
helpers_mod="${spec_mod%.Spec}.Helpers"
build_mods=("$spec_mod" "$helpers_mod" sdlean_verify)
if [ -f Targets/CertKit/Lrat.lean ]; then
  build_mods+=(Targets.CertKit.Lrat)
fi
lake build "${build_mods[@]}"

olean_rel=".lake/build/lib/lean/${proof_mod//.//}.olean"
mkdir -p "$(dirname "$olean_rel")"
cp "$OUT/candidate.lean" "$file_path"

# Compile candidate with zero credentials, stripped env, networkless sandbox when bwrap exists,
# hard wall-clock timeout (10 minutes), 6 GiB virtual memory cap, bounded heartbeats & recursion depth.
set +e
if command -v bwrap >/dev/null 2>&1; then
  (
    ulimit -v 6291456
    timeout 600 env -i PATH="$PATH" HOME="$HOME" \
      bwrap --unshare-net --ro-bind / / --dev /dev --proc /proc \
        --bind "$PWD/.lake/build" "$PWD/.lake/build" --tmpfs /tmp \
        lake env lean -R . -DmaxHeartbeats=400000 -DmaxRecDepth=2000 -o "$olean_rel" "$file_path"
  ) > "$OUT/lean.log" 2>&1
  build_rc=$?
else
  (
    ulimit -v 6291456
    timeout 600 env -u GH_TOKEN \
      lake env lean -R . -DmaxHeartbeats=400000 -DmaxRecDepth=2000 -o "$olean_rel" "$file_path"
  ) > "$OUT/lean.log" 2>&1
  build_rc=$?
fi
set -e

if [ "$build_rc" -ne 0 ]; then
  err=$(head -n 3 "$OUT/lean.log" | tr '\n' ' ' | tr -cd '[:alnum:] .,:()<>_/`-' | cut -c1-180)
  if [ "$build_rc" -eq 124 ]; then
    write REJECTED "Lean compilation timed out: ${err:-timeout}" "$meta" timeout
  else
    write REJECTED "Lean compilation failed: ${err:-error}" "$meta" compile_error
  fi
  exit 0
fi

# Fresh trusted kernel-replay verification OUTSIDE the untrusted compile step, capped at 6 GiB.
set +e
(
  ulimit -v 6291456
  timeout 300 env -u GH_TOKEN \
    lake exe sdlean_verify "$kind" "$spec_mod" "$proof_mod" "$stmt_decl" "$direction" "$holder_bound"
) > "$OUT/verdict.json" 2> "$OUT/verify.err"
verify_rc=$?
set -e

if [ ! -s "$OUT/verdict.json" ]; then
  if [ "$verify_rc" -eq 124 ]; then
    write FAULT "sdlean_verify timed out" "$meta" timeout
  else
    write FAULT "sdlean_verify produced no verdict" "$meta" fault
  fi
  exit 0
fi

jq -c --argjson meta "$meta" --argjson pr "$PR" --arg run_url "$RUN_URL" --argjson lines "$proof_lines" \
  '. + $meta + {pr: $pr, run_url: $run_url, proof_lines: $lines, reason_code: (.reason_code // "")}' \
  "$OUT/verdict.json" > "$OUT/final.json"
