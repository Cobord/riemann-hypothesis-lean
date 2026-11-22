import GroupoidCorr.Factorial

/-!
# The quadratic character of `ℚ(√-d)`

Mirrors `note/note.tex`, Section 6 (`def:chi-neg-d`, `prop:chi-split`).

For a prime `d ≡ 3 (mod 4)`, the character of `ℚ(√-d)` is `χ_{-d}(n) = (n / d)`, the Legendre
symbol (a Jacobi symbol in Mathlib). It satisfies the axioms `QuadChar d`. By quadratic
reciprocity, at an odd prime `p ≠ d` it equals `(-d / p)`, so `χ_{-d}(p) = 1` exactly when `-d` is
a square mod `p`; and `χ_{-d}(2) = 1` exactly when `d ≡ 7 (mod 8)`. These are the classical
criteria for `p` to split in `ℚ(√-d)`; the link to splitting itself is not formalized.
-/

namespace GroupoidCorr

/-- [note: def:chi-neg-d] `χ_{-d}(n) = (n / d)`. -/
def chiNeg (d : ℕ) (n : ℕ) : ℤ := jacobiSym n d

/-- [note: def:chi-neg-d] `χ_{-d}` satisfies the axioms of `def:quad-char`. -/
def quadCharOf (d : ℕ) (hd : d.Prime) : QuadChar d where
  χ := chiNeg d
  hd := hd
  map_one := by simp [chiNeg, jacobiSym.one_left]
  map_mul m n := by simp [chiNeg, jacobiSym.mul_left]
  at_prime p hp hpd := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hp hd).mpr hpd
  at_d := by
    rw [chiNeg, jacobiSym.eq_zero_iff, Int.gcd_natCast_natCast, Nat.gcd_self]
    exact ⟨hd.ne_zero, hd.one_lt.ne'⟩

/-- [note: prop:chi-split] At an odd prime `p`, `χ_{-d}(p) = (-d / p)` (quadratic reciprocity,
using `d ≡ 3 mod 4`). -/
theorem chiNeg_eq_legendreSym (d : ℕ) (h3 : d % 4 = 3) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) : chiNeg d p = legendreSym p (-d) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.legendreSym.to_jacobiSym, neg_eq_neg_one_mul, jacobiSym.mul_left,
    jacobiSym.at_neg_one hpodd, chiNeg]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpodd) with h1 | h1
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 hdodd, ZMod.χ₄_nat_one_mod_four h1,
      one_mul]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four h1 h3, ZMod.χ₄_nat_three_mod_four h1,
      neg_one_mul]

/-- [note: prop:chi-split] At an odd prime `p ≠ d`, `χ_{-d}(p) = 1` iff `-d` is a square mod `p`. -/
theorem chiNeg_eq_one_iff (d : ℕ) (hd : d.Prime) (h3 : d % 4 = 3) (p : ℕ) [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hpd : p ≠ d) : chiNeg d p = 1 ↔ IsSquare ((-d : ℤ) : ZMod p) := by
  rw [chiNeg_eq_legendreSym d h3 p hp2]
  apply legendreSym.eq_one_iff
  intro h
  have h' : ((d : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_neg, neg_eq_zero] at h; exact h
  rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h'
  exact hpd ((Nat.prime_dvd_prime_iff_eq hp.out hd).mp h')

/-- [note: prop:chi-split] `χ_{-d}(2) = 1` iff `d ≡ 7 (mod 8)`. -/
theorem chiNeg_two_eq_one_iff (d : ℕ) (h3 : d % 4 = 3) : chiNeg d 2 = 1 ↔ d % 8 = 7 := by
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  rw [chiNeg, Nat.cast_ofNat, jacobiSym.at_two hdodd, ZMod.χ₈_nat_eq_if_mod_eight]
  have : d % 8 = 3 ∨ d % 8 = 7 := by omega
  rcases this with h | h <;> simp [h, show d % 2 = 1 by omega]

end GroupoidCorr
