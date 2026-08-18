#!/usr/bin/env bash
# Run by the verification subagent (CLAUDE.md workflow step 7) after its
# checklist passes. Hard-gates: no sorry/admit in Lean sources, `lake build`
# succeeds, no warnings in the build log. On success writes
# .claude/verification-stamp = sha256 over all tracked+untracked files;
# the git-commit hook then refuses commits unless this stamp matches.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"

if git ls-files -z --cached --others --exclude-standard -- '*.lean' \
    | xargs -0 grep -lE '\b(sorry|admit)\b' 2>/dev/null | grep -q .; then
  echo "STAMP REFUSED: sorry/admit present in Lean sources:" >&2
  git ls-files -z --cached --others --exclude-standard -- '*.lean' \
    | xargs -0 grep -nE '\b(sorry|admit)\b' 2>/dev/null || true
  exit 1
fi

log="$(mktemp)"
if ! lake build >"$log" 2>&1; then
  echo "STAMP REFUSED: lake build failed:" >&2
  tail -50 "$log" >&2
  rm -f "$log"
  exit 1
fi
if grep -qE '^warning:' "$log"; then
  echo "STAMP REFUSED: lake build emitted warnings:" >&2
  grep -E '^warning:' "$log" >&2
  rm -f "$log"
  exit 1
fi
rm -f "$log"

hash="$(git ls-files -z --cached --others --exclude-standard \
  | xargs -0 sha256sum | sha256sum | cut -d' ' -f1)"
printf '%s\n' "$hash" > .claude/verification-stamp
echo "STAMP OK: .claude/verification-stamp = $hash"
