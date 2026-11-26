module

public import Mathlib

/-!
# The one-step lemma

Mirrors `note/note.tex`, Section 5 (`lem:minor`, `lem:covector`); these are Lemmas 8.6–8.7 of
the main account, the conceptual content of the archive's `key_minor_dvd` and `key_pow_dvd`.

All statements are proved after reduction modulo `ϖ`, where `p = ϖ²` vanishes and `x ↦ x ^ p^e`
is additive. If `B ⧸ (ϖ)` is the zero ring there is nothing to prove; otherwise it has
characteristic `p`.
-/

@[expose] public section

open Matrix

namespace GroupoidCorr

open scoped BigOperators

variable {B : Type*} [CommRing B] (p : ℕ) [hp : Fact p.Prime] (ϖ : B)

/-- Reduction modulo `ϖ`. -/
abbrev red (ϖ : B) : B →+* B ⧸ Ideal.span {ϖ} := Ideal.Quotient.mk _

theorem dvd_of_mk_eq_zero {x : B} (h : Ideal.Quotient.mk (Ideal.span {ϖ}) x = 0) : ϖ ∣ x :=
  Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)

theorem mk_eq_zero_of_dvd {x : B} (h : ϖ ∣ x) : Ideal.Quotient.mk (Ideal.span {ϖ}) x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)

/-- A nonzero quotient `B ⧸ (ϖ)` with `ϖ² = p` has characteristic `p`. -/
theorem charP_quot (hϖ : ϖ ^ 2 = p) [Nontrivial (B ⧸ Ideal.span {ϖ})] :
    CharP (B ⧸ Ideal.span {ϖ}) p := by
  rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk _), ← hϖ, map_pow,
    mk_eq_zero_of_dvd ϖ (dvd_refl ϖ), zero_pow two_ne_zero]

variable {p ϖ}

/-- Modulo `ϖ`, a row `(v ⬝ M)^(p^e)` is `v₀^(p^e)` times row `0` of `M'`. -/
theorem frob_row (hϖ : ϖ ^ 2 = p) [Nontrivial (B ⧸ Ideal.span {ϖ})] {n e : ℕ}
    {M M' : Matrix (Fin (n + 1)) (Fin (n + 1)) B} (hM : ∀ i j, (p : B) ∣ M i j ^ (p ^ e) - M' i j)
    {v : Fin (n + 1) → B} (hv : ∀ i, i ≠ 0 → ϖ ∣ v i) (c : Fin (n + 1)) :
    red ϖ ((v ᵥ* M) c ^ (p ^ e)) = red ϖ (v 0) ^ (p ^ e) * red ϖ (M' 0 c) := by
  have := charP_quot p ϖ hϖ
  have hM' : red ϖ (M 0 c) ^ (p ^ e) = red ϖ (M' 0 c) := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub]
    apply mk_eq_zero_of_dvd
    obtain ⟨d, hd⟩ := hM 0 c
    exact ⟨ϖ * d, by rw [hd, ← hϖ]; ring⟩
  rw [show (v ᵥ* M) c = ∑ i, v i * M i c from rfl, map_pow, map_sum, sum_pow_char_pow,
    Fintype.sum_eq_single (0 : Fin (n + 1)), map_mul, mul_pow, hM']
  intro i hi
  rw [map_mul, mk_eq_zero_of_dvd ϖ (hv i hi), zero_mul, zero_pow (pow_pos hp.out.pos e).ne']

/-- Modulo `ϖ`, a row `v' ⬝ M'` is `v'₀` times row `0` of `M'`. -/
theorem lin_row {n : ℕ} {M' : Matrix (Fin (n + 1)) (Fin (n + 1)) B} {v' : Fin (n + 1) → B}
    (hv' : ∀ i, i ≠ 0 → ϖ ∣ v' i) (c : Fin (n + 1)) :
    red ϖ ((v' ᵥ* M') c) = red ϖ (v' 0) * red ϖ (M' 0 c) := by
  rw [show (v' ᵥ* M') c = ∑ i, v' i * M' i c from rfl, map_sum, Fintype.sum_eq_single (0 : Fin (n + 1)), map_mul]
  intro i hi
  rw [map_mul, mk_eq_zero_of_dvd ϖ (hv' i hi), zero_mul]

/-- [note: lem:minor] With `ϖ² = p`, `M^(p^e) ≡ M' (mod p)` entrywise, and row vectors `v, v'`
whose coordinates of index `≥ 1` are divisible by `ϖ`, every `2 × 2` minor of the matrix with
rows `(v ⬝ M)^(p^e)` and `v' ⬝ M'` is divisible by `ϖ`. -/
theorem minor_dvd (hϖ : ϖ ^ 2 = p) {n e : ℕ} (M M' : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hM : ∀ i j, (p : B) ∣ M i j ^ (p ^ e) - M' i j) (v v' : Fin (n + 1) → B)
    (hv : ∀ i, i ≠ 0 → ϖ ∣ v i) (hv' : ∀ i, i ≠ 0 → ϖ ∣ v' i) (a b : Fin (n + 1)) :
    ϖ ∣ (v ᵥ* M) a ^ (p ^ e) * (v' ᵥ* M') b - (v ᵥ* M) b ^ (p ^ e) * (v' ᵥ* M') a := by
  apply dvd_of_mk_eq_zero
  rcases subsingleton_or_nontrivial (B ⧸ Ideal.span {ϖ}) with hQ | hQ
  · exact Subsingleton.elim _ _
  rw [map_sub, map_mul, map_mul, frob_row hϖ hM hv, frob_row hϖ hM hv, lin_row hv',
    lin_row hv']
  ring

/-- [note: lem:covector] In the setting of `lem:minor`, if `M' M'' = 1` and the column vector
`w` has `w₀` divisible by `ϖ`, then `∑ₐ ((v ⬝ M)ₐ)^(p^e) (M'' w)ₐ ≡ 0 (mod ϖ)`. -/
theorem covector_dvd (hϖ : ϖ ^ 2 = p) {n e : ℕ} (M M' M'' : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hM : ∀ i j, (p : B) ∣ M i j ^ (p ^ e) - M' i j) (hinv : M' * M'' = 1)
    (v : Fin (n + 1) → B) (hv : ∀ i, i ≠ 0 → ϖ ∣ v i) (w : Fin (n + 1) → B) (hw : ϖ ∣ w 0) :
    ϖ ∣ ∑ a, (v ᵥ* M) a ^ (p ^ e) * (M'' *ᵥ w) a := by
  apply dvd_of_mk_eq_zero
  rcases subsingleton_or_nontrivial (B ⧸ Ideal.span {ϖ}) with hQ | hQ
  · exact Subsingleton.elim _ _
  have hcol : ∑ a, M' 0 a * (M'' *ᵥ w) a = w 0 := by
    have := congrFun (Matrix.mulVec_mulVec w M' M'') 0
    rw [hinv, Matrix.one_mulVec] at this
    rw [← this]; rfl
  calc red ϖ (∑ a, (v ᵥ* M) a ^ (p ^ e) * (M'' *ᵥ w) a)
      = red ϖ (v 0) ^ (p ^ e) * red ϖ (∑ a, M' 0 a * (M'' *ᵥ w) a) := by
        rw [map_sum, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_mul, frob_row hϖ hM hv, map_mul]; ring
    _ = 0 := by rw [hcol, mk_eq_zero_of_dvd ϖ hw, mul_zero]

end GroupoidCorr
