#!/usr/bin/env bash
# Batch replacement for PIDE: check one theory file as a throwaway session.
#   check_thy.sh /abs/path/My_Theory.thy [BASE_SESSION]
# The theory may import any theory of the repository's sessions (session-qualified,
# e.g. "Relative_Arbitrage.Comparison_Two_Domain"); BASE defaults to
# Relative_Arbitrage_Statement, whose heap holds all of them.  Prints the build's
# error/warning messages and "RESULT: OK" or "RESULT: FAILED".  Runs with
# threads=2 and a 600 s timeout; a looping proof shows up as a timeout.
# SHOW_MSGS=1 also prints all messages (writeln output of thm, find_theorems,
# sledgehammer, ...).  At most two builds run at once (with_build_slot.sh).
set -uo pipefail
THY="$1"; BASE="${2:-Relative_Arbitrage_Statement}"
REPO=/home/user/relative_arbitrage
# Inside a phase-4 group (HOME=.../p4/home-GX), use that group's worktree, whose
# sources match the group's heaps.
case "${HOME:-}" in
  */p4/home-G[0-9]) REPO="${HOME%/home-G*}/$(basename "$HOME" | sed 's/^home-//')" ;;
esac
NAME="$(basename "$THY" .thy)"
DIR="$(mktemp -d /tmp/claude-0/-home-user-relative-arbitrage/b298b4d9-283e-5a1e-9ff1-6c1924a698bb/scratchpad/checks/${NAME}_XXXX 2>/dev/null || mktemp -d)"
cp "$THY" "$DIR/"
SESS="Check_${NAME}_$(basename "$DIR" | tr -c 'A-Za-z0-9_' '_')"
cat > "$DIR/ROOT" <<ROOTEOF
session "$SESS" = "$BASE" +
  options [document = false, timeout = 600]
  sessions
    Second_Order_Viscosity_Analysis Continuous_Time_Martingales Wiener_Measure
    Continuous_Path_Spaces Relative_Arbitrage Symmetric_Matrix_Spectra
    Semicontinuous_Analysis
  theories
    "$NAME"
ROOTEOF
cd "$REPO"
"$(dirname "$0")/with_build_slot.sh" isabelle build -d . -d "$DIR" -o threads=2 "$SESS" > "$DIR/build.out" 2>&1
RC=$?
grep -vE '^### Version mismatch|^Building |^Running |^Finished |^[0-9:]+ elapsed' "$DIR/build.out" | head -150
echo "SESSION: $SESS   (all messages, e.g. find_theorems/thm output: isabelle build_log -v -U $SESS)"
if [ "${SHOW_MSGS:-0}" = 1 ]; then isabelle build_log -v -U "$SESS" 2>/dev/null | tail -300; fi
if [ $RC -eq 0 ]; then
  isabelle build_log -H Warning "$SESS" 2>/dev/null | grep -iE 'warning|sorry' | head -20
  echo "RESULT: OK"
else
  echo "RESULT: FAILED (rc=$RC)"
fi
