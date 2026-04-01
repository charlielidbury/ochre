#!/usr/bin/env bash
set -euo pipefail

# Infinite loop of Claude Code agents working on Och.
#
# Each iteration launches Claude Code interactively with remote control,
# so you can connect via the web URL printed in the logs.
# When the agent finishes (idle prompt detected), /exit is sent automatically.
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

# Get a fingerprint of the pane content (md5 hash).
pane_fingerprint() {
  local session="$1"
  tmux capture-pane -t "$session" -p 2>/dev/null | md5sum | cut -d' ' -f1
}

echo "Starting Och agent loop"
echo "  Max turns per iteration: $MAX_TURNS"
echo "  Pause every: ${PAUSE_EVERY:-never} iterations"
echo "  Press Ctrl-C to stop"
echo ""

while true; do
  ITERATION=$((ITERATION + 1))
  REPO_NAME="$(basename "$SCRIPT_DIR")"
  SESSION_NAME="${REPO_NAME}-$(date +%Y%m%d-%H%M%S)"
  PROMPT="Your agent ID is $SESSION_NAME. Read and follow AGENT_PROMPT.md"

  echo "=========================================="
  echo "  Iteration $ITERATION"
  echo "  Session: $SESSION_NAME"
  echo "  $(date)"
  echo "=========================================="

  # Launch claude interactively with remote control in a tmux session
  tmux new-session -d -s "$SESSION_NAME" -x 200 -y 50 \
    "cd '$SCRIPT_DIR' && claude --rc --dangerously-skip-permissions --max-turns $MAX_TURNS --verbose --name '$SESSION_NAME'"

  # Wait for the TUI to render and remote control to activate
  sleep 8

  # Extract and display the remote URL
  PANE_CONTENT="$(tmux capture-pane -t "$SESSION_NAME" -p 2>/dev/null)"
  REMOTE_URL="$(echo "$PANE_CONTENT" | grep -oP 'https://claude\.ai/code/\S+' || echo "(no URL found)")"
  echo "  Remote URL: $REMOTE_URL"
  echo "  Attach locally: tmux attach -t $SESSION_NAME"

  # Send the prompt
  tmux send-keys -t "$SESSION_NAME" "$PROMPT" Enter

  echo "  Agent started. Waiting for it to finish..."

  # Wait a bit, then capture pane to verify the agent is processing
  sleep 15
  echo "  --- Post-prompt pane snapshot (15s) ---"
  tmux capture-pane -t "$SESSION_NAME" -p 2>/dev/null | head -10
  echo "  --- end snapshot ---"

  # Wait for the agent to finish by detecting when the pane stops changing.
  # First wait for the prompt to be ingested, then poll until stable.
  sleep 15
  PREV_HASH=""
  STABLE_COUNT=0
  while tmux has-session -t "$SESSION_NAME" 2>/dev/null; do
    CURR_HASH="$(pane_fingerprint "$SESSION_NAME")"
    if [ "$CURR_HASH" = "$PREV_HASH" ]; then
      STABLE_COUNT=$((STABLE_COUNT + 1))
      if [ $STABLE_COUNT -ge 3 ]; then
        echo "  Agent idle (pane stable for 30s) — sending /exit"
        tmux send-keys -t "$SESSION_NAME" "/exit" Enter
        sleep 3
        break
      fi
    else
      STABLE_COUNT=0
    fi
    PREV_HASH="$CURR_HASH"
    sleep 10
  done

  # Ensure tmux session is cleaned up
  tmux kill-session -t "$SESSION_NAME" 2>/dev/null || true

  echo ""
  echo "Agent $SESSION_NAME finished"
  echo ""

  # Optional pause for human review
  if [ "$PAUSE_EVERY" -gt 0 ] && [ $((ITERATION % PAUSE_EVERY)) -eq 0 ]; then
    echo ">>> Paused for review (iteration $ITERATION). Press Enter to continue, Ctrl-C to stop."
    read -r
  fi

  sleep 2
done
