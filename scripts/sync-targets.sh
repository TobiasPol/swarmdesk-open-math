#!/usr/bin/env bash
# Syncs targets.json to Swarmdesk POST /api/targets/sync with an HMAC signature.
# Run automatically on push to main whenever maintainers merge a new open problem or helper lemma.
set -euo pipefail
: "${SWARMDESK_URL:?}" "${VERDICT_SECRET:?}"
cd "$(dirname "$0")/.."
printf '%s' "$SWARMDESK_URL" | grep -Eqx 'https://[a-z0-9.-]+' || { echo "bad site address"; exit 2; }
node checker/manifest.mjs . >/dev/null
payload=$(jq -c --arg at "$(date -u +%Y-%m-%dT%H:%M:%SZ)" '. + {sent_at: $at}' targets.json)
signature=$(printf '%s' "$payload" | openssl dgst -sha256 -hmac "$VERDICT_SECRET" -hex | sed 's/^.* //')
answer=$(mktemp)
code=$(curl -sS --proto '=https' --max-time 20 -o "$answer" -w '%{http_code}' -X POST \
  -H 'Content-Type: application/json' -H "X-Swarmdesk-Signature: sha256=$signature" \
  --data-binary "$payload" "$SWARMDESK_URL/api/targets/sync")
echo "sync ($code): $(cat "$answer")"
[ "$code" = 200 ]
