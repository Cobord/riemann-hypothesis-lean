import Mathlib

/-!
# Content of a period map

Mirrors `note/note.tex`, Section 7 (`def:content`, `prop:content`); this is Section 7 of the
main account (Definition 7.3, Proposition 7.4).

For a bilinear period pairing `per : N × P → R`, "`per ⊗ R/I = 0` as a map
`N ⊗ R/I → Hom(P, R/I)`" is equivalent, by tensor–hom adjunction (the target is an
`R/I`-module), to "every value of `per` reduces to `0` in `R/I`"; we take the latter as the
definition (`VanishesMod`). The content is the ideal spanned by the values.
-/

open IsDedekindDomain

namespace GroupoidCorr

variable {R : Type*} [CommRing R]
variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- [note: def:content] The content of `per`: the ideal spanned by its values, i.e. the image of
the evaluation map `N ⊗ P → R`. -/
def content (per : N →ₗ[R] P →ₗ[R] R) : Ideal R :=
  Ideal.span {x | ∃ v w, per v w = x}

/-- [note: def:content] `per` vanishes modulo `I`: every value reduces to `0` in `R/I`. -/
def VanishesMod (per : N →ₗ[R] P →ₗ[R] R) (I : Ideal R) : Prop :=
  ∀ v w, Ideal.Quotient.mk I (per v w) = 0

/-- [note: prop:content] (a) `per` vanishes modulo `I` iff its content lies in `I`. -/
theorem vanishesMod_iff (per : N →ₗ[R] P →ₗ[R] R) (I : Ideal R) :
    VanishesMod per I ↔ content per ≤ I := by
  constructor
  · intro h
    rw [content, Ideal.span_le]
    rintro x ⟨v, w, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mp (h v w)
  · intro h v w
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h (Ideal.subset_span ⟨v, w, rfl⟩))

/-- [note: prop:content] (b) Vanishing modulo `I` survives composition with linear maps on
either side. -/
theorem VanishesMod.comp {per : N →ₗ[R] P →ₗ[R] R} {I : Ideal R} (h : VanishesMod per I)
    {N' P' : Type*} [AddCommGroup N'] [Module R N'] [AddCommGroup P'] [Module R P']
    (f : N' →ₗ[R] N) (g : P' →ₗ[R] P) : VanishesMod (per.compl₁₂ f g) I :=
  fun v w => h (f v) (g w)

/-- [note: prop:content] (b) Vanishing modulo `I` survives any base change `R → S` killing `I`. -/
theorem VanishesMod.map {per : N →ₗ[R] P →ₗ[R] R} {I : Ideal R} (h : VanishesMod per I)
    {S : Type*} [CommRing S] (φ : R →+* S) (hφ : I ≤ RingHom.ker φ) (v : N) (w : P) :
    φ (per v w) = 0 :=
  hφ (Ideal.Quotient.eq_zero_iff_mem.mp (h v w))

section Dedekind

variable [IsDedekindDomain R]

/-- [note: def:content] `ord_𝔭(per)`: the exponent of `𝔭` in the content. -/
noncomputable def ordP (v : HeightOneSpectrum R) (per : N →ₗ[R] P →ₗ[R] R) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (content per)).factors

/-- [note: prop:content] (a) For nonzero content, `ord_𝔭(per)` is the largest `r` such that `per`
vanishes modulo `𝔭 ^ r`. -/
theorem le_ordP_iff (v : HeightOneSpectrum R) (per : N →ₗ[R] P →ₗ[R] R)
    (hC : content per ≠ ⊥) (r : ℕ) : r ≤ ordP v per ↔ VanishesMod per (v.asIdeal ^ r) := by
  rw [vanishesMod_iff, ← Ideal.dvd_iff_le, ← Associates.mk_dvd_mk, Associates.mk_pow]
  simp only [Associates.dvd_eq_le]
  rw [Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hC) v.associates_irreducible]
  rfl

/-- [note: prop:content] (a) The content is `∏_𝔭 𝔭 ^ ord_𝔭(per)`. -/
theorem content_factorization (per : N →ₗ[R] P →ₗ[R] R) (hC : content per ≠ ⊥) :
    ∏ᶠ v : HeightOneSpectrum R, v.asIdeal ^ ordP v per = content per :=
  Ideal.finprod_heightOneSpectrum_factorization hC

end Dedekind

end GroupoidCorr
