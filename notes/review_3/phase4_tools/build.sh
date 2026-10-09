#!/usr/bin/env bash
# build.sh GROUP [SESSION...]
# Builds the sessions of the worktree $SP/p4/GROUP with its own Isabelle home
# (default: every session of the repository, -D .).  Only sessions whose sources
# changed (and their descendants) are rebuilt.  Prints the error messages of every
# failed session and "BUILD: OK" or "BUILD: FAILED".  At most two Isabelle builds
# run at once on this machine (a shared slot lock), so it may wait.
SP=/tmp/claude-0/-home-user-relative-arbitrage/b298b4d9-283e-5a1e-9ff1-6c1924a698bb/scratchpad
G="$1"; shift
WT="$SP/p4/$G"; export HOME="$SP/p4/home-$G"
cd "$WT" || exit 2
LOG="$SP/p4/build-$G.log"
if [ $# -gt 0 ]; then SEL="$*"; else SEL="-D ."; fi
"$SP/tools/with_build_slot.sh" isabelle build -b -o threads=2 -o timeout=1800 -d . $SEL > "$LOG" 2>&1
RC=$?
grep -E '^(Finished|Building) |FAILED' "$LOG" | grep -v document
for s in $(grep ' FAILED' "$LOG" | awk '{print $1}'); do
  echo "=== errors in $s"
  timeout 300 isabelle build_log -H Error "$s" 2>/dev/null | grep -v '^###' | head -60
done
if [ $RC -eq 0 ]; then echo "BUILD: OK"; else echo "BUILD: FAILED (rc=$RC)"; fi
