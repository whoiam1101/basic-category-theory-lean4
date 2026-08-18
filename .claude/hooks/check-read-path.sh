#!/usr/bin/env bash
# PreToolUse hook for Read: deny reading anything outside the project except
# Lean-related locations (elan toolchain, local loogle checkout), the session
# scratch dir /tmp, and the Claude memory directory.
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
  "$ROOT"/*) exit 0 ;;
  /tmp/*) exit 0 ;;
  "$HOME"/.elan/*) exit 0 ;;
  "$HOME"/Documents/loogle/*) exit 0 ;;
  "$HOME"/.claude/projects/*) exit 0 ;;
  *)
    jq -n --arg p "$file_path" \
      '{hookSpecificOutput: {hookEventName: "PreToolUse", permissionDecision: "deny", permissionDecisionReason: ("Blocked: reading outside the project is forbidden (" + $p + "). Allowed outside the project: Lean toolchain (~/.elan), the local loogle checkout, /tmp scratch, and the Claude memory directory.")}}'
    exit 0
    ;;
esac
