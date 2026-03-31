#!/usr/bin/env bash
set -euo pipefail

# Infinite loop of Claude Code agents working on Och.
#
# Each iteration gets a fresh agent with a unique ID. The agent reads git
# history to understand prior progress, works until it runs out of turns,
# commits (with its ID in the message), and exits.
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
  AGENT_ID="agent-$(date +%Y%m%d-%H%M%S)-$(openssl rand -hex 3)"

  echo "=========================================="
  echo "  Iteration $ITERATION — $AGENT_ID"
  echo "  $(date)"
  echo "=========================================="

  # Substitute $AGENT_ID into the prompt
  PROMPT="$(sed "s/\$AGENT_ID/$AGENT_ID/g" "$PROMPT_FILE")"

  # Run Claude Code
  claude --print \
    --max-turns "$MAX_TURNS" \
    --allowedTools "Edit,Write,Read,Glob,Grep,Bash" \
    -p "$PROMPT" || true

  echo ""
  echo "Agent $AGENT_ID finished"
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
