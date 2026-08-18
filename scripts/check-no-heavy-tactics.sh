#!/usr/bin/env bash
set -euo pipefail

failed=0
for f in "$@"; do
  if grep -nE '\b(aesop|grind|omega)\b' "$f" 2>/dev/null; then
    echo "ERROR: banned tactic (aesop/grind/omega) found in $f" >&2
    failed=1
  fi
done

exit $failed
