import Mathlib

/-!
# Divided periods are integral

Mirrors `note/note.tex`, Section 7 (`cor:divided`); this is Corollary 8.12 of the main account.

Over a Dedekind domain `R` with fraction field `K`: if every value of a period pairing lies in
`𝔭 ^ e(𝔭)` for each prime `𝔭` of a finite set of distinct primes (the local output of
`thm:orders-add-corr` and `cor:divisible-values` at `𝔭`), then every value lies in
`𝔞 = ∏ 𝔭 ^ e(𝔭)`, and dividing by `𝔞` keeps the values integral: for `α ∈ 𝔞⁻¹`,
`α · per(v)(w) ∈ R`. Here `per(α v) = α · per(v)` is the `K`-linear extension.
-/

open scoped nonZeroDivisors

namespace GroupoidCorr

open scoped BigOperators

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- [note: cor:divided] Local divisibility at each prime gives `cont(per) ⊆ 𝔞`. -/
theorem values_mem_prod {ι : Type*} (s : Finset ι) (𝔭 : ι → Ideal R) (e : ι → ℕ)
    (hprime : ∀ i ∈ s, Prime (𝔭 i)) (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 𝔭 i ≠ 𝔭 j)
    (per : N →ₗ[R] P →ₗ[R] R) (h : ∀ i ∈ s, ∀ v w, per v w ∈ 𝔭 i ^ e i) (v : N) (w : P) :
    per v w ∈ ∏ i ∈ s, 𝔭 i ^ e i := by
  rw [← IsDedekindDomain.inf_pow_eq_prod_of_prime s 𝔭 e hprime hdist]
  rw [Finset.inf_eq_iInf]
  simp only [Submodule.mem_iInf]
  exact fun i hi => h i hi v w

/-- [note: cor:divided] Divided periods are integral: for `α ∈ 𝔞⁻¹`, `α · per(v)(w) ∈ R`. -/
theorem divided_integral {ι : Type*} (s : Finset ι) (𝔭 : ι → Ideal R) (e : ι → ℕ)
    (hprime : ∀ i ∈ s, Prime (𝔭 i)) (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 𝔭 i ≠ 𝔭 j)
    (per : N →ₗ[R] P →ₗ[R] R) (h : ∀ i ∈ s, ∀ v w, per v w ∈ 𝔭 i ^ e i) (v : N) (w : P)
    (α : K) (hα : α ∈ ((∏ i ∈ s, 𝔭 i ^ e i : Ideal R) : FractionalIdeal R⁰ K)⁻¹) :
    ∃ y : R, algebraMap R K y = α * algebraMap R K (per v w) := by
  set 𝔞 : Ideal R := ∏ i ∈ s, 𝔭 i ^ e i
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot, Ne, Finset.prod_eq_zero_iff, not_exists]
    rintro i ⟨hi, h0⟩
    exact (hprime i hi).ne_zero (pow_eq_zero_iff'.mp h0).1
  have hx : algebraMap R K (per v w) ∈ (𝔞 : FractionalIdeal R⁰ K) :=
    (FractionalIdeal.mem_coeIdeal R⁰).mpr ⟨_, values_mem_prod s 𝔭 e hprime hdist per h v w, rfl⟩
  have hmem := FractionalIdeal.mul_mem_mul hα hx
  rw [inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔞)] at hmem
  exact FractionalIdeal.mem_one_iff R⁰ |>.mp hmem

end GroupoidCorr
