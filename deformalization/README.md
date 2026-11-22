# GroupoidCorr

A short note (`note/note.tex`) and a Lean 4 library (`GroupoidCorr/`) kept in one-to-one correspondence. Together they formalize the structural part of the theta-chain account of GRH:

- finite groupoids and local systems;
- integral pushforward over fibres;
- base change and composition of correspondences;
- additivity of divisibility along chains;
- denominators of the Lubin–Tate exponential and divisibility of jets at inert primes;
- the one-step minor lemma behind each unit of divisibility;
- the factorial identity relating the prime sum to the inert factorial ideal;
- integrality of divided periods over a Dedekind domain;
- the content of the period map, and Claim A from (the consequence of) Hypothesis J.

```
lake exe cache get && lake build
python3 scripts/check_sync.py --axioms
cd note && latexmk -pdf note.tex
```

See `CLAUDE.md` for the sync convention and the task list.
