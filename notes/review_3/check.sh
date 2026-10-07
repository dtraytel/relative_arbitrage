#!/usr/bin/env bash
# Re-run the measurements of notes/REVIEW_3.md and PLAN_RESTRUCTURING_3.md section 5.
#   notes/review_3/check.sh [OUTDIR]
# 1. builds every session of the repository (not only the Statement chain);
# 2. runs Review_Analysis.thy (oracles, closure of roots.txt, clones) in a
#    build of the throwaway session Review_3_Analysis (notes/review_3/ROOT);
# 3. post-processes with the Python scripts beside this file.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
OUT="${1:-/tmp/review_3_out}"
mkdir -p "$OUT"
LOG="$OUT/build.log"

cd "$REPO"
isabelle build -b -v -d . -D . -o threads="${THREADS:-3}" -o timeout=1800 2>&1 | tee "$LOG"

# The analysis theory writes to the directory named in its 'outdir' (default
# /tmp/review_3_out/); keep OUT and that value in sync.
isabelle build -d . -d notes/review_3 -o timeout=3600 Review_3_Analysis 2>&1 | tail -5

python3 "$HERE/dead.py" "$OUT"
python3 "$HERE/actual_imports.py" "$OUT"
python3 "$HERE/critpath.py" "$OUT" "$LOG"
echo "lines per session:"
for d in $(cat ROOTS); do printf '  %-34s %7d\n' "$d" "$(cat "$d"/*.thy | wc -l)"; done
echo "@{theory Session.X} antiquotations: $(grep -rhoE '@\{theory [A-Za-z_-]+\.[A-Za-z_]+\}' --include=*.thy . | wc -l)"
echo "'lives in' pointer texts: $(grep -rhc 'lives in' --include=*.thy . | paste -sd+ | bc)"
