module

public import Mathlib

/-!
# The norm map: invariants against coinvariants

Mirrors `note/note.tex`, Section 1 (Lemma `lem:norm-map`).

For a finite group `G` acting linearly on an `R`-module `V`, the norm
`v ↦ ∑ g, ρ g v` multiplies invariant vectors by `|G|`, and `|G| • v` always
differs from the norm of `v` by an element of the span of `v - ρ g v`
(the kernel of the projection to coinvariants). These two identities are the
whole content of "the norm map from coinvariants to invariants has kernel and
cokernel killed by `|G|`".
-/

@[expose] public section

namespace GroupoidCorr

open scoped BigOperators

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- [note: lem:norm-map] On invariant vectors the norm is multiplication by `|G|`. -/
theorem norm_of_invariant (ρ : Representation R G V) (v : V) (hv : ∀ g, ρ g v = v) :
    ∑ g, ρ g v = Fintype.card G • v := by
  simp [hv, Finset.sum_const, Finset.card_univ]

/-- [note: lem:norm-map] `|G| • v` is the norm of `v` plus a sum of elements `v - ρ g v`. -/
theorem card_smul_eq_norm_add (ρ : Representation R G V) (v : V) :
    Fintype.card G • v = (∑ g, (v - ρ g v)) + ∑ g, ρ g v := by
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_const, Finset.card_univ]

/-- [note: lem:norm-map] If the norm of `v` vanishes, `|G| • v` lies in the span of the
`v - ρ g v`, i.e. `v` is `|G|`-torsion in the coinvariants. -/
theorem card_smul_mem_span_of_norm_eq_zero (ρ : Representation R G V) (v : V)
    (hv : ∑ g, ρ g v = 0) :
    Fintype.card G • v ∈ Submodule.span R (Set.range fun g : G => v - ρ g v) := by
  rw [card_smul_eq_norm_add ρ v, hv, add_zero]
  exact Submodule.sum_mem _ fun g _ => Submodule.subset_span ⟨g, rfl⟩

end GroupoidCorr
