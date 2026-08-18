#!/usr/bin/env bash
# PreToolUse hook for Bash (git commands): if the command invokes `git commit`
# and .lean files are changed, require a fresh verification stamp
# (.claude/verification-stamp, written by stamp-verification.sh after the
# verification subagent passes) and no sorry/admit in the changed files.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"

input="$(cat)"
command="$(printf '%s' "$input" | jq -r '.tool_input.command // empty')"

if ! printf '%s' "$command" | grep -qE '(^|[;&|]\s*)git\s+commit(\s|$|-)'; then
  exit 0
fi

lean_changes="$( { git diff --cached --name-only -- '*.lean'; \
  git diff --name-only -- '*.lean'; \
  git ls-files --others --exclude-standard -- '*.lean'; } | sort -u )"

if [ -z "$lean_changes" ]; then
  exit 0
fi

if printf '%s\n' "$lean_changes" | xargs grep -nE '\b(sorry|admit)\b' 2>/dev/null | grep -q .; then
  jq -n '{hookSpecificOutput: {hookEventName: "PreToolUse", permissionDecision: "deny", permissionDecisionReason: "Blocked: sorry/admit present in changed Lean files — fix before committing."}}'
  exit 0
fi

stamp=".claude/verification-stamp"
if [ ! -f "$stamp" ]; then
  jq -n '{hookSpecificOutput: {hookEventName: "PreToolUse", permissionDecision: "deny", permissionDecisionReason: "Blocked: no verification stamp. Run the verification subagent (CLAUDE.md workflow step 7) and have it execute: bash .claude/hooks/stamp-verification.sh"}}'
  exit 0
fi

current="$(git ls-files -z --cached --others --exclude-standard \
  | xargs -0 sha256sum | sha256sum | cut -d' ' -f1)"
stamped="$(tr -d '[:space:]' < "$stamp")"
if [ "$current" != "$stamped" ]; then
  jq -n '{hookSpecificOutput: {hookEventName: "PreToolUse", permissionDecision: "deny", permissionDecisionReason: "Blocked: files changed after the verification stamp. Re-run the verification subagent and stamp again (bash .claude/hooks/stamp-verification.sh)."}}'
  exit 0
fi

exit 0
