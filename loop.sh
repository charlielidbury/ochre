#!/usr/bin/env bash
set -euo pipefail

# Infinite loop of Claude Code agents working on Och.
#
# Each iteration gets a fresh Claude Code session with a unique ID.
# You can resume any agent later with: claude --resume <session-name>
#
# Usage:
#   ./loop.sh              # run with defaults
#   ./loop.sh 10           # pause for review every N iterations
#
# Environment variables:
#   MAX_TURNS=50           # max turns per agent (default 50)
#
# To stop: Ctrl-C

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROMPT_FILE="$SCRIPT_DIR/AGENT_PROMPT.md"
MAX_TURNS="${MAX_TURNS:-50}"
PAUSE_EVERY="${1:-0}"
ITERATION=0

if [ ! -f "$PROMPT_FILE" ]; then
  echo "Error: $PROMPT_FILE not found"
  exit 1
fi

echo "Starting Och agent loop"
echo "  Max turns per iteration: $MAX_TURNS"
echo "  Pause every: ${PAUSE_EVERY:-never} iterations"
echo "  Press Ctrl-C to stop"
echo ""

while true; do
  ITERATION=$((ITERATION + 1))
  SESSION_ID="$(uuidgen | tr '[:upper:]' '[:lower:]')"
  SESSION_NAME="och-agent-$(date +%Y%m%d-%H%M%S)"

  echo "=========================================="
  echo "  Iteration $ITERATION"
  echo "  Session: $SESSION_NAME"
  echo "  ID:      $SESSION_ID"
  echo "  Resume:  claude --resume $SESSION_NAME"
  echo "  $(date)"
  echo "=========================================="

  # Substitute $AGENT_ID into the prompt (use session name as the agent ID)
  PROMPT="$(sed "s/\$AGENT_ID/$SESSION_NAME/g" "$PROMPT_FILE")"

  # Run Claude Code with a named, resumable session
  claude --print \
    --dangerously-skip-permissions \
    --session-id "$SESSION_ID" \
    --name "$SESSION_NAME" \
    --max-turns "$MAX_TURNS" \
    -p "$PROMPT" || true

  echo ""
  echo "Agent $SESSION_NAME finished"
  echo "  Resume with: claude --resume $SESSION_NAME"
  echo "Last commit:"
  git -C "$SCRIPT_DIR" log --oneline -1
  echo ""

  # Optional pause for human review
  if [ "$PAUSE_EVERY" -gt 0 ] && [ $((ITERATION % PAUSE_EVERY)) -eq 0 ]; then
    echo ">>> Paused for review (iteration $ITERATION). Press Enter to continue, Ctrl-C to stop."
    read -r
  fi

  sleep 2
done
