# GroupoidCorr

A short note (`note/note.tex`) and a Lean 4 library (`GroupoidCorr/`) kept in one-to-one correspondence. Together they formalize the structural part of the theta-chain account of GRH:

- finite groupoids and local systems;
- integral pushforward over fibres;
- base change and composition of correspondences;
- additivity of divisibility along chains.

```
lake exe cache get && lake build
python3 scripts/check_sync.py --axioms
cd note && latexmk -pdf note.tex
```

See `CLAUDE.md` for the sync convention and the task list.
