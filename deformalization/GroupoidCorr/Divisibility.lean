module

public import Mathlib

/-!
# Divisibility adds along chains

Mirrors `note/note.tex`, Section 3 (`def:chain`, `thm:orders-add`, `cor:divisible-values`).

This is the linear-algebra core of "orders add along compositions of correspondences":
once each step's operator is `ϖ ^ rᵢ` times an integral operator, the composite is
`ϖ ^ (∑ rᵢ)` times the composite of the integral operators. The groupoid-level statement
(kernels on iterated fibre products) reduces to this because pullback and pushforward are
`R`-linear; that reduction is item `prop:composition` in the note (not yet formalized).
-/

@[expose] public section

namespace GroupoidCorr

open scoped BigOperators

variable {R : Type*} [CommRing R]
variable {M : ℕ → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- [note: def:chain] The composite `K (n-1) ∘ ⋯ ∘ K 0 : M 0 → M n` of a chain of linear maps. -/
def chainComp (K : ∀ i, M i →ₗ[R] M (i + 1)) : ∀ n, M 0 →ₗ[R] M n
  | 0 => LinearMap.id
  | n + 1 => (K n).comp (chainComp K n)

/-- [note: thm:orders-add] If each step is `ϖ ^ r i` times an integral map `K' i`, the composite
of the first `n` steps is `ϖ ^ (∑_{i<n} r i)` times the composite of the `K' i`. -/
theorem chainComp_eq_pow_smul (K K' : ∀ i, M i →ₗ[R] M (i + 1)) (ϖ : R) (r : ℕ → ℕ)
    (h : ∀ i, K i = ϖ ^ r i • K' i) (n : ℕ) :
    chainComp K n = ϖ ^ (∑ i ∈ Finset.range n, r i) • chainComp K' n := by
  induction n with
  | zero => simp [chainComp]
  | succ n ih =>
    simp only [chainComp]
    rw [h n, ih, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
      Finset.sum_range_succ, pow_add, mul_comm]

/-- [note: cor:divisible-values] If a bilinear period pairing is `ϖ ^ S` times an integral one,
all of its values lie in the ideal `(ϖ ^ S)`. Combined with `thm:orders-add` this gives
divisibility of the periods of a chain. -/
theorem values_mem_span_pow {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] (per per' : N →ₗ[R] P →ₗ[R] R) (ϖ : R) (S : ℕ) (h : per = ϖ ^ S • per')
    (x : N) (y : P) : per x y ∈ Ideal.span {ϖ ^ S} := by
  rw [h, Ideal.mem_span_singleton]
  exact ⟨per' x y, by simp⟩

end GroupoidCorr
