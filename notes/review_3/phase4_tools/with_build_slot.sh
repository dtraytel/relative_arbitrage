#!/usr/bin/env bash
# Run a command while holding one of two build slots (at most two Isabelle builds
# at once on this 15 GB machine).  Usage: with_build_slot.sh CMD ARGS...
L=/tmp/claude-0/-home-user-relative-arbitrage/b298b4d9-283e-5a1e-9ff1-6c1924a698bb/scratchpad/tools
exec 8>"$L/slot1.lock" 9>"$L/slot2.lock"
if flock -n 8; then exec 9>&-; elif flock -n 9; then exec 8>&-; else
  while :; do flock -n 8 && { exec 9>&-; break; }; flock -n 9 && { exec 8>&-; break; }; sleep 5; done
fi
"$@"
