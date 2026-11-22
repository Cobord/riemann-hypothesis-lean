# GroupoidCorr — note and Lean kept in sync

This folder formalizes the *structural* part of the theta-chain account of GRH:

- integral pushforward along maps of finite groupoids;
- composition of correspondences;
- the fact that divisibility orders add along a chain.

It has two halves that must always say the same thing:

- `note/note.tex`: a short, standard math note (amsart).
- `GroupoidCorr/*.lean`: Lean 4 + Mathlib.

The main exposition this is extracted from is `context/GRH_Theta_Chain_Conceptual_Account.tex` (PDF alongside), Sections 2, 3 and 8.6. The note is a self-contained excerpt; keep it short.

## Where this sits

This folder is the `deformalization/` subproject of the fork `Cobord/riemann-hypothesis-lean`. The rest of the repository is an unmodified mirror of Alpöge's archive (`../src/`). This subproject is a separate Lake package with its own `lakefile.toml`; do not edit the mirror.

Archive files referred to below are under `../src/`. For example, the archive's `ChainIntM` is in `../src/Formalism/ThetaLiftIndependence/Statement.lean`.

Run all commands from this folder (`cd deformalization`).

## Toolchain

- `lean-toolchain` is `leanprover/lean4:v4.33.1`.
- Mathlib is pinned to `0df444a360eaa60ab8c11dca51a86af692955474`.
- Both are the same as the Alpöge archive's `lean/`, so a shared cache works.
- First time: `lake exe cache get` and then `lake build`.

## The sync convention (enforced by `scripts/check_sync.py`)

In the note:
- Every `definition / lemma / proposition / theorem / corollary` has a `\label{KEY}`.
- A formalized item lists its Lean declarations: `\lean{GroupoidCorr.foo, GroupoidCorr.bar}`.
- An item not yet formalized says `\notready` instead.
- Add `\leanok` to an item **only** when all its listed declarations build with no `sorry` and only standard axioms.

In Lean:
- Each declaration that realizes a note item has a docstring containing `[note: KEY]`.
- Helper declarations without a tag are fine; they are not checked.

Run before every commit:

```
lake build
python3 scripts/check_sync.py            # structural check
python3 scripts/check_sync.py --axioms   # also #print axioms for \leanok items
```

Both must exit 0.

## Rules for changing things

1. Change a statement in one place, change it in the other in the same commit. Lean statements and note statements must match in content: same hypotheses, same conclusion. Proofs may differ in route, but each note proof should be one a reader can match to the Lean proof's structure.
2. Never weaken a Lean statement to make it compile without weakening the note to match.
3. No new axioms, no `sorry` in `\leanok` items, no `native_decide`.
4. Prefer Mathlib's existing notions (`CategoryTheory.Groupoid`, `ModuleCat`, `Representation`, `Finset.sum`). If a notion has to be built by hand, say so in the note.
5. Keep the conventions of the main account:
   - every tensor product names its base ring;
   - every dual names its target;
   - kernels of correspondences point from `src^*` to `tgt^*`;
   - pushforward sums, never averages.

## Current status

`lake build` is clean, with no `sorry`. Every note item that has Lean declarations is `\leanok`, and `check_sync.py --axioms` passes using only `propext`, `Classical.choice` and `Quot.sound`. The items done: `lem:norm-map`, `def:local-system`, `def:section`, `def:fibre`, `lem:summand-wd`, `def:pushforward`, `prop:push-section`, `def:chain`, `thm:orders-add`, `cor:divisible-values`.

`prop:push-section` goes through the helpers `FibrePair.postcomp`, `Fibre.postcompEquiv` (the fibre bijection, with inverse from `inv g`) and `summand_postcomp`. `pushVal` picks its `Fintype` instance with `Fintype.ofFinite`, so proofs that unfold it should bring the same instance into scope (`let _ : ∀ z, Fintype (Fibre f z) := fun z => Fintype.ofFinite _`). Rewriting under `pushVal` with `rw` trips over `Fibre` vs `Quotient`; use `refine`/`exact` instead.

Next tasks, in order:

1. Formalize `prop:base-change`: define the 2-fibre product groupoid and the fibre bijection.
2. `def:correspondence` and `prop:composition`.
3. `prop:adjoint`: groupoid cardinality, orbit–stabilizer.

After that, natural extensions from the main account:
- the reduction of `thm:orders-add` from linear maps to kernels on iterated fibre products;
- Theorems 8.3–8.4, the Lubin–Tate exponential bound and the divisibility of jets. These are elementary power-series statements.

## Context

- The main account explains why this part matters. It is not a mirror of the archive's formal proof, whose organization it deliberately departs from.
- The archive has lattices in a fixed space, chosen representatives and averaging. Here: groupoids, fibres and summation.
- The archive's abstract lemma `ChainIntM` corresponds to `thm:orders-add` but is unused on its main route.
