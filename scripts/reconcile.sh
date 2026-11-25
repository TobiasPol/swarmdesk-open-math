#!/usr/bin/env bash
# Catches the site up. Re-sends the verdict of every recent verified Lean commit on main,
# rebuilt from GitHub-signed workflow commits written by ci-report.sh.
# Swarmdesk records each verdict idempotently by head_sha/step, so re-sending is safe.
#
#   scripts/reconcile.sh        (LIMIT=<n> inspects the n most recent commits on main)
set -euo pipefail
: "${REPO:?}" "${GH_TOKEN:?}" "${DEFAULT_BRANCH:?}" "${SWARMDESK_URL:?}" "${VERDICT_SECRET:?}"
here=$(cd "$(dirname "$0")" && pwd)
PROBLEM="${PROBLEM:-open-math}"
LIMIT="${LIMIT:-30}"
printf '%s' "$LIMIT" | grep -Eqx '[1-9][0-9]?' || { echo "LIMIT must be 1 to 99"; exit 2; }
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

sent=0
failed=0
LOGIN='^[A-Za-z0-9][A-Za-z0-9-]{0,38}$'
WHEN='^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$'
TITLE='^step-([0-9]+): verified Lean (conjecture|bound|lemma) ([a-z0-9_]{3,48}) \((proved|disproved|improved)\) by ([A-Za-z0-9][A-Za-z0-9-]{0,38})$'
BOUND_LINE='^Verified bound ([0-9]{1,18}) \(previous: ([0-9]{1,18})\)\. Lines: ([0-9]{1,6})\.$'
RES_LINE='^Resolution: (proved|disproved)\. Standard axioms only\. Lines: ([0-9]{1,6})\.$'
FROM_LINE='^Pull request #([1-9][0-9]{0,6}), commit ([0-9a-f]{40})\.$'

# send <pr> <head> <author> <step> <target> <resolution> <metric> <holder> <lines> <merged_at>
send() {
  jq -cn --arg problem "$PROBLEM" --argjson pr "$1" --arg head_sha "$2" --arg author "$3" \
    --argjson step "$4" --arg target "$5" --arg resolution "$6" \
    --argjson metric "$7" --argjson holder "$8" --argjson lines "$9" --arg merged_at "${10}" \
    '{problem: $problem, pr: $pr, head_sha: $head_sha, author: $author, step: $step, target: $target,
      verdict: "ACCEPTED", reason: "", reason_code: "", resolution: $resolution,
      metric_value: $metric, holder_value: $holder, proof_lines: $lines,
      merged: true, merged_at: $merged_at, run_url: ""}' > "$work/payload.json"
  echo "pull request $1 (step-$4, $5):"
  if "$here/send-verdict.sh" "$work/payload.json"; then sent=$((sent + 1)); else failed=$((failed + 1)); fi
}

gh api "repos/$REPO/commits?sha=$DEFAULT_BRANCH&per_page=$LIMIT" \
  --jq '.[] | select((.parents | length) == 1) | .sha' | tac > "$work/single.txt"

while read -r sha; do
  [[ "$sha" =~ ^[0-9a-f]{40}$ ]] || continue
  gh api "repos/$REPO/commits/$sha" > "$work/commit.json" 2>/dev/null || continue
  proof=$(jq -r '[
      .author.login == "github-actions[bot]",
      .committer.login == "web-flow",
      .commit.verification.verified == true,
      (.parents | length) == 1,
      ((.files | length) == 1 or (.files | length) == 2)
    ] | all' "$work/commit.json")
  [ "$proof" = true ] || continue

  target_file=""
  helpers_ok=true
  while IFS= read -r fjson; do
    fname=$(jq -r '.filename' <<<"$fjson")
    fstatus=$(jq -r '.status' <<<"$fjson")
    if [[ "$fname" =~ ^Targets/[A-Za-z0-9_]+(/Lemmas/[A-Za-z0-9_]+|/Proof)\.lean$ ]] && [ "$fstatus" = "modified" ]; then
      [ -z "$target_file" ] && target_file="$fname" || { helpers_ok=false; break; }
    elif [[ "$fname" =~ ^Targets/[A-Za-z0-9_]+/Helpers\.lean$ ]] && [ "$fstatus" = "modified" ]; then
      :
    else
      helpers_ok=false
      break
    fi
  done < <(jq -c '.files[]' "$work/commit.json")
  [ "$helpers_ok" = true ] && [ -n "$target_file" ] || continue

  merged_at=$(jq -r '.commit.committer.date' "$work/commit.json")
  [[ "$merged_at" =~ $WHEN ]] || continue

  title=$(jq -r '.commit.message' "$work/commit.json" | sed -n 1p)
  detail=$(jq -r '.commit.message' "$work/commit.json" | sed -n 3p)
  from=$(jq -r '.commit.message' "$work/commit.json" | sed -n 4p)
  [[ "$title" =~ $TITLE ]] || continue
  step="${BASH_REMATCH[1]}"
  kind="${BASH_REMATCH[2]}"
  target="${BASH_REMATCH[3]}"
  resolution="${BASH_REMATCH[4]}"
  author="${BASH_REMATCH[5]}"

  [[ "$step" =~ ^[1-9][0-9]{0,8}$ && "$author" =~ $LOGIN ]] || continue
  expected_path=$(jq -r --arg t "$target" --arg k "$kind" \
    '.targets[] | select(.name == $t and .kind == $k) | .file_path // ""' "$here/../targets.json")
  [ "$expected_path" = "$target_file" ] || continue

  [[ "$from" =~ $FROM_LINE ]] || continue
  pr="${BASH_REMATCH[1]}"
  head="${BASH_REMATCH[2]}"

  metric="null"
  holder="null"
  lines="0"
  if [ "$kind" = "bound" ]; then
    [[ "$detail" =~ $BOUND_LINE ]] || continue
    metric="${BASH_REMATCH[1]}"
    holder="${BASH_REMATCH[2]}"
    lines="${BASH_REMATCH[3]}"
  else
    [[ "$detail" =~ $RES_LINE ]] || continue
    [ "${BASH_REMATCH[1]}" = "$resolution" ] || continue
    lines="${BASH_REMATCH[2]}"
  fi

  send "$pr" "$head" "$author" "$step" "$target" "$resolution" "$metric" "$holder" "$lines" "$merged_at"
done < "$work/single.txt"

echo "records sent: $sent, not delivered: $failed"
[ "$failed" = 0 ]
