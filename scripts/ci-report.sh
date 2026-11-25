#!/usr/bin/env bash
# Report job for swarmdesk-open-math: never executes submitted Lean code.
# On ACCEPTED, commits the exact judged bytes by SHA-1 hash onto main (and for blueprint lemmas,
# safely adds its `import` line to Helpers.lean above `namespace` in the same workflow commit),
# closes the PR, comments, and sends the HMAC-signed verdict (including reason_code) to Swarmdesk.
set -euo pipefail
: "${PR:?}" "${REPO:?}" "${GH_TOKEN:?}" "${DEFAULT_BRANCH:?}"
file="${1:?usage: ci-report.sh <final.json>}"
here=$(cd "$(dirname "$0")" && pwd)
PROBLEM="${PROBLEM:-open-math}"
printf '%s' "$PR" | grep -Eqx '[1-9][0-9]{0,6}' || { echo "bad pull request number"; exit 1; }
[ -s "$file" ] || { mkdir -p "$(dirname "$file")"; echo '{"verdict":"FAULT","reason":"the check produced no verdict","reason_code":"fault"}' > "$file"; }

field() { jq -r --arg k "$1" '.[$k] // "" | tostring' "$file"; }
pick() { field "$1" | grep -Ex "$2" || true; }
verdict=$(pick verdict 'ACCEPTED|REJECTED|FAULT')
verdict=${verdict:-FAULT}
reason=$(field reason | tr -cd '[:alnum:] .,:()<>_/`-' | cut -c1-200)
reason_code=$(pick reason_code 'wrong_answer|margin_too_small|timeout|out_of_fuel|trapped|compile_error|guard_rejected|axiom_violation|type_mismatch|bound_not_improved|spec_altered|stale|fault|other|')
head=$(pick head_sha '[0-9a-f]{40}')
target=$(pick target '[a-z0-9_]{3,48}')
kind=$(pick kind 'conjecture|bound|lemma')
file_path=$(pick file_path 'Targets/[A-Za-z0-9_]+(/Lemmas/[A-Za-z0-9_]+|/Proof)\.lean')
proof_mod=$(pick proof_module 'Targets\.[A-Za-z0-9_.]+')
step=$(pick step '[1-9][0-9]{0,8}')
author=$(pick author '[A-Za-z0-9][A-Za-z0-9-]{0,38}')
resolution=$(pick resolution 'proved|disproved|improved')
metric_val=$(jq -r '.metric_value // "null"' "$file")
holder_val=$(jq -r '.holder_value // "null"' "$file")
proof_lines=$(pick proof_lines '[0-9]{1,6}')
candidate_blob=$(pick candidate_blob '[0-9a-f]{40}')
holder_blob=$(pick holder_blob '[0-9a-f]{40}')
bytes="$(dirname "$file")/candidate.lean"
run_url=$(pick run_url "https://github\.com/$REPO/actions/runs/[0-9]+")

merged=false
repeat=false
record_sha=""
api() { gh api -H "X-GitHub-Api-Version: 2022-11-28" "$@"; }
blob_at() { api "repos/$REPO/contents/$2?ref=$1" --jq .sha 2>/dev/null; }

inject_helpers_import() {
  local raw="$1"
  local mod="$2"
  local mod_re="${mod//./\\.}"
  raw="${raw//$'\r'/}"
  if printf '%s\n' "$raw" | grep -Eq "^[[:space:]]*import[[:space:]]+${mod_re}[[:space:]]*$"; then
    return 1
  fi
  awk -v imp="import $mod" '
    { lines[NR] = $0 }
    /^[[:space:]]*import[[:space:]]/ && !seen_ns { last_imp = NR }
    /^[[:space:]]*namespace[[:space:]]/ { seen_ns = 1 }
    END {
      if (last_imp > 0) {
        for (i = 1; i <= NR; i++) {
          print lines[i]
          if (i == last_imp) print imp
        }
      } else {
        print imp
        for (i = 1; i <= NR; i++) print lines[i]
      }
    }
  ' <<<"$raw"
}

write_record() {
  local main now last blob tree new commit message tree_items helpers_path helpers_raw updated_helpers helpers_blob
  message="step-$step: verified Lean $kind $target ($resolution) by $author"$'\n\n'
  if [ "$kind" = "bound" ]; then
    message+="Verified bound $metric_val (previous: $holder_val). Lines: ${proof_lines:-0}."$'\n'
  else
    message+="Resolution: $resolution. Standard axioms only. Lines: ${proof_lines:-0}."$'\n'
  fi
  message+="Pull request #$PR, commit $head."
  for _ in 1 2 3 4; do
    main=$(api "repos/$REPO/git/ref/heads/$DEFAULT_BRANCH" --jq .object.sha) || return 2
    now=$(blob_at "$main" "$file_path") || return 2
    if [ "$now" = "$candidate_blob" ]; then
      last=$(api "repos/$REPO/commits?sha=$main&path=$file_path&per_page=1" \
        --jq '.[0].commit.message' | sed -n 4p) || return 2
      [ "$last" = "Pull request #$PR, commit $head." ] || return 1
      repeat=true
      return 0
    fi
    [ "$now" = "$holder_blob" ] || return 1
    base64 -w0 "$bytes" > "$bytes.b64"
    blob=$(jq -n --rawfile content "$bytes.b64" '{content: $content, encoding: "base64"}' \
      | api -X POST "repos/$REPO/git/blobs" --input - --jq .sha) || return 2
    [ "$blob" = "$candidate_blob" ] || return 2
    tree=$(api "repos/$REPO/git/commits/$main" --jq .tree.sha) || return 2
    tree_items=$(jq -cn --arg path "$file_path" --arg sha "$blob" \
      '[{path: $path, mode: "100644", type: "blob", sha: $sha}]')

    # For V2 blueprint helper lemmas, safely re-export the proved lemma in Helpers.lean above namespace.
    if [ "$kind" = "lemma" ] && [ -n "$proof_mod" ]; then
      helpers_path="$(dirname "$(dirname "$file_path")")/Helpers.lean"
      helpers_raw=$(api "repos/$REPO/contents/$helpers_path?ref=$main" --jq '.content' | tr -d '\n' | base64 -d) || return 2
      if updated_helpers=$(inject_helpers_import "$helpers_raw" "$proof_mod"); then
        helpers_blob=$(jq -n --arg content "${updated_helpers}"$'\n' '{content: $content, encoding: "utf-8"}' \
          | api -X POST "repos/$REPO/git/blobs" --input - --jq .sha) || return 2
        tree_items=$(jq -cn --argjson cur "$tree_items" --arg path "$helpers_path" --arg sha "$helpers_blob" \
          '$cur + [{path: $path, mode: "100644", type: "blob", sha: $sha}]')
      fi
    fi

    new=$(jq -n --arg base "$tree" --argjson items "$tree_items" \
      '{base_tree: $base, tree: $items}' \
      | api -X POST "repos/$REPO/git/trees" --input - --jq .sha) || return 2
    commit=$(jq -n --arg message "$message" --arg tree "$new" --arg parent "$main" \
      '{message: $message, tree: $tree, parents: [$parent]}' \
      | api -X POST "repos/$REPO/git/commits" --input - --jq .sha) || return 2
    if jq -n --arg sha "$commit" '{sha: $sha, force: false}' \
      | api -X PATCH "repos/$REPO/git/refs/heads/$DEFAULT_BRANCH" --input - >/dev/null 2>&1; then
      [ "$(blob_at "$commit" "$file_path")" = "$candidate_blob" ] || return 2
      record_sha="$commit"
      return 0
    fi
  done
  return 1
}

if [ "$verdict" = ACCEPTED ] && [ -n "$head" ] && [ -n "$target" ] && [ -n "$file_path" ] && [ -n "$step" ] && [ -n "$author" ]; then
  reason_code=""
  outcome=2
  if [ -n "$candidate_blob" ] && [ -n "$holder_blob" ] && [ -s "$bytes" ]; then
    write_record && outcome=0 || outcome=$?
  fi
  case "$outcome" in
    0) merged=true ;;
    1)
      verdict=STALE
      reason="this target moved while your proof was checked"
      reason_code="stale"
      ;;
    *)
      verdict=FAULT
      reason="the verified proof could not be written to main"
      reason_code="fault"
      ;;
  esac
fi

line="**$verdict**"
[ -n "$reason" ] && line="$line ($reason)"
body="$line"
[ -n "$target" ] && body="$body"$'\n\n'"Target \`$target\` ($kind), step-$step."
[ -n "$resolution" ] && body="$body"$'\n'"Resolution: \`$resolution\` (standard Lean 4 axioms only)."
if [ "$kind" = "bound" ] && [ "$metric_val" != "null" ]; then
  body="$body"$'\n'"Verified bound: \`$metric_val\` (previous: \`$holder_val\`)."
fi
if [ "$merged" = true ]; then
  body="$body"$'\n\n'"This verified Lean file is now on \`$DEFAULT_BRANCH\` (commit $record_sha). Pull request closed without three-way merge."
fi
[ -n "$run_url" ] && body="$body"$'\n\n'"[The run]($run_url)"
[ "$repeat" = true ] || gh api -X POST "repos/$REPO/issues/$PR/comments" -f body="$body" >/dev/null
[ "$merged" = true ] && api -X PATCH "repos/$REPO/pulls/$PR" -f state=closed >/dev/null 2>&1 || true
[ -n "$record_sha" ] && [ -n "${GITHUB_OUTPUT:-}" ] && echo "recorded=true" >> "$GITHUB_OUTPUT"
echo "$line"

if [ -n "${SWARMDESK_URL:-}" ] && [ -n "${VERDICT_SECRET:-}" ] && [ -n "$author" ] && [ -n "$head" ]; then
  payload=$(mktemp)
  jq -cn --arg problem "$PROBLEM" --argjson pr "$PR" --arg head_sha "$head" --arg author "$author" \
    --arg step "$step" --arg target "$target" --arg verdict "$verdict" --arg reason "$reason" \
    --arg reason_code "$reason_code" --arg resolution "$resolution" \
    --argjson metric "$metric_val" --argjson holder "$holder_val" \
    --arg lines "${proof_lines:-0}" --argjson merged "$merged" --arg run_url "$run_url" \
    '{problem: $problem, pr: $pr, head_sha: $head_sha, author: $author, step: ($step | tonumber? // null),
      target: $target, verdict: $verdict, reason: $reason, reason_code: $reason_code,
      resolution: $resolution, metric_value: $metric, holder_value: $holder,
      proof_lines: ($lines | tonumber? // 0), merged: $merged, run_url: $run_url}' > "$payload"
  "$here/send-verdict.sh" "$payload"
fi
