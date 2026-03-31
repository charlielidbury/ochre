#!/usr/bin/env bash
set -euo pipefail

# Infinite loop of Claude Code agents working on Och.
#
# Each iteration launches an interactive Claude Code session in tmux.
# You can:
#   - Watch live:    tmux attach -t <session-name>
#   - Resume later:  claude --resume <session-name>
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
MAX_TURNS="${MAX_TURNS:-50}"
PAUSE_EVERY="${1:-0}"
ITERATION=0

echo "Starting Och agent loop"
echo "  Max turns per iteration: $MAX_TURNS"
echo "  Pause every: ${PAUSE_EVERY:-never} iterations"
echo "  Press Ctrl-C to stop"
echo ""

while true; do
  ITERATION=$((ITERATION + 1))
  SESSION_NAME="och-agent-$(date +%Y%m%d-%H%M%S)"

  echo "=========================================="
  echo "  Iteration $ITERATION"
  echo "  Session: $SESSION_NAME"
  echo "  Attach:  tmux attach -t $SESSION_NAME"
  echo "  Resume:  claude --resume $SESSION_NAME"
  echo "  $(date)"
  echo "=========================================="

  # Launch claude interactively in a tmux session
  tmux new-session -d -s "$SESSION_NAME" -x 200 -y 50 \
    "cd '$SCRIPT_DIR' && claude --dangerously-skip-permissions --name '$SESSION_NAME' --max-turns $MAX_TURNS"

  # Wait for claude to start up
  sleep 5

  # Enable remote control, then send the initial message
  tmux send-keys -t "$SESSION_NAME" "/remote-control" Enter
  sleep 3
  tmux send-keys -t "$SESSION_NAME" \
    "Your agent ID is $SESSION_NAME. Read and follow AGENT_PROMPT.md" Enter

  echo "  Agent started. Waiting for it to finish..."

  # Wait for the tmux session to end
  while tmux has-session -t "$SESSION_NAME" 2>/dev/null; do
    sleep 10
  done

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
