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
- the content of the period map, and Claim A from (the consequence of) Hypothesis J;
- trace duality, duals of modifications, and the rank-one norm map.

Toolchain: Lean `v4.36.0` with Mathlib `v4.36.0`. Every file uses the module system (`module`, `public import`, `@[expose] public section`).

## Build and check

```
lake exe cache get                 # download Mathlib's build files; never compile Mathlib
lake build                         # builds GroupoidCorr only (a few minutes)
python3 scripts/check_sync.py --axioms
cd note && latexmk -pdf note.tex
```

If `lake build` starts compiling Mathlib files, stop it: the cache is not being used. Running `lake env .lake/packages/mathlib/.lake/build/bin/cache unpack!` re-extracts every downloaded cache file over any stale local ones. `lake build --no-build` lists what would be rebuilt without building anything.

## The challenge

`Challenge.lean` and `Challenge/*.lean` state everything the library proves, importing only Mathlib. They are the library with every theorem's proof replaced by `sorry` and the definitions copied verbatim. They are generated, so do not edit them by hand:

```
python3 scripts/make_challenge.py  # writes Challenge.lean, Challenge/*.lean, comparator.json
lake build Challenge Solution
lake comparator                    # reads comparator.json
```

`lake comparator` (built into Lean since v4.35, needs `bwrap`) checks every theorem listed in `comparator.json`. Each must be proved by the library (`Solution.lean` imports `GroupoidCorr`) with exactly the same statement. Each proof may use only `propext`, `Quot.sound` and `Classical.choice`. The kernel must accept the proofs. It also requires every definition the statements use to be identical in challenge and solution. That is why the challenge mirrors the library's module structure file by file: Lean names auxiliary proof lemmas per module.

See `CLAUDE.md` for the sync convention and the task list.
