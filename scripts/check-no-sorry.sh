#!/usr/bin/env bash
set -euo pipefail

failed=0
for f in "$@"; do
  if grep -nE '\b(sorry|admit)\b' "$f" 2>/dev/null; then
    echo "ERROR: sorry/admit found in $f" >&2
    failed=1
  fi
done

exit $failed
