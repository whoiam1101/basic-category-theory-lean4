#!/usr/bin/env bash
# PreToolUse hook for Edit|Write:
#  1) deny any edit outside the project (exception: the Claude memory dir)
#  2) deny introducing sorry/admit or heavy automation tactics
#     (aesop/grind/omega) into .lean files
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"

input="$(cat)"
file_path="$(printf '%s' "$input" | jq -r '.tool_input.file_path // empty')"
[ -n "$file_path" ] || exit 0

case "$file_path" in
  /*) abs="$file_path" ;;
  '~'*) abs="$HOME/${file_path#'~'/}" ;;
  *) abs="$ROOT/$file_path" ;;
esac
# Canonicalize with symlink resolution (readlink -f resolves the final
# component too when it exists; the parent-dir fallback covers paths whose
# last component does not exist yet — nonexistent components cannot be
# symlinks, so a plain prefix check is sound there).
if canon="$(readlink -f "$abs" 2>/dev/null)"; then
  abs="$canon"
else
  dir="$(dirname "$abs")"
  abs="$(realpath "$dir" 2>/dev/null || printf '%s' "$dir")/$(basename "$abs")"
fi

case "$abs" in
  "$ROOT"/*) ;;
  "$HOME"/.claude/projects/*) ;;
  *)
    jq -n --arg p "$file_path" \
      '{hookSpecificOutput: {hookEventName: "PreToolUse", permissionDecision: "deny", permissionDecisionReason: ("Blocked: editing outside the project is forbidden (" + $p + "). Only the project and the Claude memory directory may be edited.")}}'
    exit 0
    ;;
esac

case "$file_path" in
  *.lean) ;;
  *) exit 0 ;;
esac

content="$(printf '%s' "$input" | jq -r '.tool_input.new_string // .tool_input.content // empty')"
[ -n "$content" ] || exit 0

# In scratch files (.claude/scratch/) `sorry`/`admit` are allowed: they are
# gitignored, never built by the project, and must be removed before the
# code is integrated into the real section file.
case "$abs" in
  "$ROOT"/.claude/scratch/*)
    if printf '%s' "$content" | grep -qE '\b(aesop|grind|omega)\b'; then
      forbidden="$(printf '%s' "$content" | grep -oE '\b(aesop|grind|omega)\b' | sort -u | tr '\n' ' ')"
      jq -n --arg m "$forbidden" \
        '{hookSpecificOutput: {hookEventName: "PreToolUse", permissionDecision: "deny", permissionDecisionReason: ("Blocked: Lean code contains heavy tactics: " + $m + "— project rules forbid aesop/grind/omega even in scratch files.")}}'
      exit 0
    fi
    exit 0
    ;;
esac

if printf '%s' "$content" | grep -qE '\b(sorry|admit|aesop|grind|omega)\b'; then
  forbidden="$(printf '%s' "$content" | grep -oE '\b(sorry|admit|aesop|grind|omega)\b' | sort -u | tr '\n' ' ')"
  jq -n --arg m "$forbidden" \
    '{hookSpecificOutput: {hookEventName: "PreToolUse", permissionDecision: "deny", permissionDecisionReason: ("Blocked: Lean code contains forbidden terms: " + $m + "— project rules forbid sorry/admit and heavy tactics (aesop/grind/omega); rewrite the proof.")}}'
  exit 0
fi

exit 0
