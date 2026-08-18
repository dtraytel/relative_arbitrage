# Measurements behind `notes/PLAN_RESTRUCTURING_2.md`

| file | what it is |
|---|---|
| `thy_parse.py` | a theory-file parser: top-level declarations with their name, line range, enclosing locale, statement and proof text. Nothing Isabelle-aware beyond lexing |
| `probes.py` | the seven probes the plan quotes. `python3 probes.py` runs all of them; `python3 probes.py probe4` runs one |
| `dispositions.tsv` | one row per top-level statement in the repository (2 754), with its disposition, target theory, and the rule that produced the row |

Run from this directory (or set `REPO` to the repository root):

```bash
python3 probes.py
python3 probes.py probe0        # the self-check; must print 0 mismatches
```

## Read `probe0` before believing anything else

Isabelle's `(*v)` — the matrix-vector product as a bare operator — opens a
comment for any stripper that does not know it is inside a string literal. With
that bug the parser reported 1 lemma in `Doubling_Of_Variables` (there are 141)
and 93 in `Matrix_Algebra` (there are 147), and every derived number was wrong
in a way that looked plausible. `thy_parse.scan` tracks string literals and
cartouches; `probe0` compares the parse against a plain `grep` and must print
`mismatched theories: 0`.

## Columns of `dispositions.tsv`

```
session  theory  name  line  lines  disposition  target  rule
```

`disposition` is one of `STAY`, `MOVE`, `SPLIT`, `STAY-OR-UPSTREAM`, with a
`/UNUSED?` suffix when no other statement, proof or comment names the lemma.
`rule` records how the row was derived; §4 of the plan says which rules are
reliable as instructions and which only as permissions.

Regenerate after each phase: the plan's progress metrics (§7.2) are these
numbers.
