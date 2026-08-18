#!/usr/bin/env bash
set -euo pipefail

if [ "${CI:-false}" = "true" ] || [ "${GITHUB_ACTIONS:-false}" = "true" ]; then
  exit 0
fi

if [ ! -f .claude/verification-stamp ]; then
  echo "ERROR: .claude/verification-stamp is missing." >&2
  echo "Run: bash .claude/hooks/stamp-verification.sh" >&2
  exit 1
fi

current="$(git ls-files -z --cached --others --exclude-standard | xargs -0 sha256sum | sha256sum | cut -d' ' -f1)"
stamped="$(tr -d '[:space:]' < .claude/verification-stamp)"

if [ "$current" != "$stamped" ]; then
  echo "ERROR: Working tree modified after verification stamp." >&2
  echo "Please re-run: bash .claude/hooks/stamp-verification.sh" >&2
  exit 1
fi
