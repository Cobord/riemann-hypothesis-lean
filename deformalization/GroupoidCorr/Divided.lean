module

public import Mathlib

/-!
# Divided periods are integral

Mirrors `note/note.tex`, Section 7 (`cor:divided`); this is Corollary 8.12 of the main account.

Over a Dedekind domain `R` with fraction field `K`: if every value of a period pairing lies in
`𝔭 ^ e(𝔭)` for each prime `𝔭` of a finite set of distinct primes (the local output of
`thm:orders-add-corr` and `cor:divisible-values` at `𝔭`), then every value lies in
`𝔞 = ∏ 𝔭 ^ e(𝔭)`, and dividing by `𝔞` keeps the values integral: for `α ∈ 𝔞⁻¹`,
`α · per(v)(w) ∈ R`. Here `per(α v) = α · per(v)` is the `K`-linear extension.
-/

@[expose] public section

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

/-- [note: lem:local-global] If `x ∈ R` becomes divisible by `ϖ ^ e` in `R_𝔭` for some `ϖ ∈ 𝔭`,
then `x ∈ 𝔭 ^ e`: the power `𝔭 ^ e` of a nonzero prime is `𝔭`-primary, so it is recovered from
its localization. -/
theorem mem_pow_of_local (𝔭 : Ideal R) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (e : ℕ) (ϖ : R) (hϖ : ϖ ∈ 𝔭)
    (x : R) (y : Localization.AtPrime 𝔭)
    (h : algebraMap R (Localization.AtPrime 𝔭) x =
      algebraMap R (Localization.AtPrime 𝔭) ϖ ^ e * y) :
    x ∈ 𝔭 ^ e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  have hmax : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔭
  have hprim : (𝔭 ^ e).IsPrimary := by
    apply Ideal.isPrimary_of_isMaximal_radical
    rw [Ideal.radical_pow (I := 𝔭) he.ne', Ideal.IsPrime.radical inferInstance]
    exact hmax
  have hdisj : Disjoint (𝔭.primeCompl : Set R) ((𝔭 ^ e : Ideal R) : Set R) := by
    rw [Set.disjoint_left]
    intro a ha ha'
    exact ha (Ideal.pow_le_self he.ne' ha')
  rw [← IsLocalization.under_map_of_isPrimary_disjoint 𝔭.primeCompl (Localization.AtPrime 𝔭) hprim hdisj]
  change algebraMap R (Localization.AtPrime 𝔭) x ∈
    Ideal.map (algebraMap R (Localization.AtPrime 𝔭)) (𝔭 ^ e)
  rw [h, ← map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hϖ e))

/-- [note: cor:divided] The same, with the local hypothesis in the form produced by
`thm:orders-add-corr` and `cor:divisible-values` over `R_𝔭`: every value becomes `ϖᵢ ^ eᵢ` times
an element of `R_{𝔭ᵢ}`, for some `ϖᵢ ∈ 𝔭ᵢ`. -/
theorem divided_integral_of_local {ι : Type*} (s : Finset ι) (𝔭 : ι → Ideal R)
    [∀ i, (𝔭 i).IsPrime] (hne : ∀ i ∈ s, 𝔭 i ≠ ⊥) (e : ι → ℕ)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 𝔭 i ≠ 𝔭 j) (ϖ : ι → R) (hϖ : ∀ i, ϖ i ∈ 𝔭 i)
    (per : N →ₗ[R] P →ₗ[R] R)
    (h : ∀ i ∈ s, ∀ v w, ∃ y : Localization.AtPrime (𝔭 i),
      algebraMap R _ (per v w) = algebraMap R _ (ϖ i) ^ e i * y) (v : N) (w : P)
    (α : K) (hα : α ∈ ((∏ i ∈ s, 𝔭 i ^ e i : Ideal R) : FractionalIdeal R⁰ K)⁻¹) :
    ∃ y : R, algebraMap R K y = α * algebraMap R K (per v w) := by
  refine divided_integral s 𝔭 e (fun i hi => Ideal.prime_of_isPrime (hne i hi) inferInstance)
    hdist per (fun i hi v w => ?_) v w α hα
  obtain ⟨y, hy⟩ := h i hi v w
  exact mem_pow_of_local (𝔭 i) (hne i hi) (e i) (ϖ i) (hϖ i) _ y hy

end GroupoidCorr
