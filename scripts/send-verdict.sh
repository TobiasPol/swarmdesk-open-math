#!/usr/bin/env bash
# Sends one HMAC-signed verdict JSON payload to Swarmdesk /api/verdicts.
set -euo pipefail
: "${SWARMDESK_URL:?}" "${VERDICT_SECRET:?}"
file="${1:?usage: send-verdict.sh <payload.json>}"
printf '%s' "$SWARMDESK_URL" | grep -Eqx 'https://[a-z0-9.-]+' || { echo "bad site address"; exit 2; }
payload=$(jq -c --arg at "$(date -u +%Y-%m-%dT%H:%M:%SZ)" '. + {sent_at: $at}' "$file")
signature=$(printf '%s' "$payload" | openssl dgst -sha256 -hmac "$VERDICT_SECRET" -hex | sed 's/^.* //')
answer=$(mktemp)

for wait in 0 5 15 45; do
  sleep "$wait"
  code=$(curl -sS --proto '=https' --max-time 20 -o "$answer" -w '%{http_code}' -X POST \
    -H 'Content-Type: application/json' -H "X-Swarmdesk-Signature: sha256=$signature" \
    --data-binary "$payload" "$SWARMDESK_URL/api/verdicts" 2>/dev/null || echo 000)
  if [ "$code" = 200 ]; then
    echo "Swarmdesk accepted verdict: $(cat "$answer")"
    exit 0
  fi
  case "$code" in 4??) echo "Swarmdesk refused verdict ($code): $(cat "$answer")"; exit 1 ;; esac
  echo "Swarmdesk answered $code"
done
echo "Swarmdesk could not be reached"
exit 1
