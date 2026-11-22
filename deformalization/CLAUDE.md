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

`lake build` is clean, with no `sorry`. All 39 note items are `\leanok`, and `check_sync.py --axioms` passes using only `propext`, `Classical.choice` and `Quot.sound`.

Files:
- `NormMap.lean`: Section 1.
- `Pushforward.lean`: local systems, sections, fibres, pushforward.
- `BaseChange.lean`: the 2-fibre product, which is Mathlib's `Comma f g` with a hand-built `Groupoid` instance, and base change.
- `Functoriality.lean`: `Sec.pull`, `Sec.map`, naturality of pushforward, and `(k ⋙ h)_! = h_! k_!` for faithful `h`.
- `Correspondence.lean`: `Corr` (apex `C` is a parameter), `Corr.op`, `Corr.comp`, `Corr.op_comp`.
- `Adjoint.lean`: `FinGroupoid`, the pairing `ginner`, and `ginner_push`, proved by double counting.
- `Divisibility.lean`: chains of linear maps.
- `Chain.lean`: kernel scaling (`Corr.smul`), the identity correspondence, and bundled correspondences `BCorr` with the apex as a field, all in one universe `Type u`. Also chains `chain` and `thm:orders-add-corr` (`chain_eq_pow_smul`). This is the kernel-level version of `thm:orders-add`.
- `OneStep.lean`: Section 5 of the note, which is Section 8.3 of the main account (`lem:minor`, `lem:covector`). The proofs work in `B ⧸ (ϖ)`, which is either the zero ring or of characteristic `p`.
- `Factorial.lean`: Section 6 of the note, which is Section 8.5 of the main account. `QuadChar d` records the properties of `χ_{-d}` that are used; `χ_{-d}` itself and the splitting of primes are not formalized. `askFlat_eq` is Proposition 8.9, by reindexing the `Λ`-sum over prime powers with `Finset.sum_bij_ne_zero`. `factorial_gain` is Corollary 8.10; its proof writes the even-`k` part of Legendre's sum as Legendre's sum in base `p²` (`legendre_base`), which avoids geometric series.
- `Divided.lean`: Section 7 of the note, which is Corollary 8.12 of the main account. Over a Dedekind domain, divisibility by each `𝔭^e` gives divisibility by `𝔞 = ∏ 𝔭^e` (`IsDedekindDomain.inf_pow_eq_prod_of_prime`), and `𝔞⁻¹ 𝔞 = 1` for fractional ideals. The local-to-global step is `mem_pow_of_local` (`lem:local-global`): `𝔭^e` is primary, so `𝔭^e R_𝔭 ∩ R = 𝔭^e` (`IsLocalization.under_map_of_isPrimary_disjoint`). `divided_integral_of_local` takes the local form directly.
- `QuadCharJacobi.lean`: `χ_{-d}(n) = (n/d)` for a prime `d ≡ 3 mod 4` (`chiNeg`), an instance of `QuadChar` (`quadCharOf`), and the splitting criteria via quadratic reciprocity (`prop:chi-split`). That these criteria describe splitting in `ℚ(√-d)` is not formalized.
- `Content.lean`: `def:content` and `prop:content`. `VanishesMod per I` (values reduce to 0 in `R/I`) stands for `per ⊗ R/I = 0`. The content is the span of the values, and `ordP` is the exponent of `𝔭` in it (`Associates.count`).
- `ClaimA.lean`: `lem:norm-bound` and `thm:claimA`, over `𝓞 E` for a number field `E`. Primes above `p` are indexed by `Above E T = Σ p : T, (span {p}).primesOver (𝓞 E)`. The `Fintype` instance on `primesOver` needs `[Fact p.Prime]`, so `T`'s primality is the instance argument `[∀ p : T, Fact (p : ℕ).Prime]`. Hypothesis J is replaced by its per-step consequence. Uses the new ramification API (`Ideal.ramificationIdx`, `Ideal.inertiaDeg`, `absNorm_pow_inertiaDeg`, `sum_ramification_inertia_eq_finrank`), not the primed one.
- `LubinTate.lean`: Section 4 of the note, which is Section 8.2 of the main account. `LTData` bundles the hypotheses; `[p]_F(exp Z) = exp(pZ)` is an assumption, used in coefficient form. Bounds are integral: `ϖ ^ (n-1) * c_n ∈ O` with `ϖ ^ (q-1) = p`, which stands for `ord_p(c_n) ≥ -(n-1)/(q-1)`. Proof via the scaled series `G(Z) = ϖ⁻¹ E(ϖ Z)`. `cor:height` is an exact integer identity from Mathlib's Legendre formula (`sub_one_mul_padicValNat_factorial`).

Mathematical point. The original note dropped the main account's hypothesis that `tgt` is faithful. That hypothesis is needed for composition: functoriality of the unweighted pushforward fails for non-faithful `h`. The note now records this, with a counterexample. Pushforward and base change need no faithfulness.

Lean gotchas:
- `Fibre` and `FibrePair` are `abbrev`s. Without that, `rw` under `pushVal` trips over `Fibre` vs `Quotient`.
- Proofs that unfold `pushVal` should bring the same instance into scope: `let _ : ∀ z, Fintype (Fibre f z) := fun z => Fintype.ofFinite _`.
- Use `h.map_id`, not `Functor.map_id`: with `open CategoryTheory` the latter resolves to the monad lemma.
- `Comma.homMk` does not exist at this Mathlib commit. Build `CommaMorphism` structures directly.
- To prove two `BCorr`s with the same apex equal, `show` both as `⟨C, T⟩` and rewrite in `T`. For `Corr` equality, use `unfold …; congr 1; ext`.
- Inside `namespace LTData`, a bare `mk` resolves to `LTData.mk`; write `PowerSeries.mk`.
- `push_cast` turns `padicValNat` into `padicValRat`; cast with `exact_mod_cast` and `Nat.cast_sub` instead.
- With `open ArithmeticFunction`, the notation `Λ` is ambiguous; write `vonMangoldt n`.
- When destructuring `Quotient.exact`, give the witness type explicitly (`obtain ⟨γ, hγ⟩ : ∃ γ : a ⟶ b, … := Quotient.exact h`).

Natural extensions from the main account (not started):
- The equality `log Nm cont = Σ ord_𝔭 f_𝔭 log p` (only the inequality `lem:norm-bound` is done).
- §8.6 is covered by `thm:orders-add-corr`, `cor:divisible-values`, `lem:local-global` and `cor:divided`.
- Linking `prop:chi-split` to the actual splitting of primes in `𝓞_{ℚ(√-d)}` (Dedekind–Kummer); the case `d = 2`.
- Building a Lubin–Tate formal group and its exponential, so that `LTData.hE` is a theorem rather than a hypothesis.

## Context

- The main account explains why this part matters. It is not a mirror of the archive's formal proof, whose organization it deliberately departs from.
- The archive has lattices in a fixed space, chosen representatives and averaging. Here: groupoids, fibres and summation.
- The archive's abstract lemma `ChainIntM` corresponds to `thm:orders-add` but is unused on its main route.
