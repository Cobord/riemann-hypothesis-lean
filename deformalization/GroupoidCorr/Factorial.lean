module

public import Mathlib

/-!
# The prime sum is the norm of a factorial ideal

Mirrors `note/note.tex`, Section 6 (`def:quad-char`, `prop:factorial`, `cor:factorial-gain`);
this is Section 8.5 of the main account.

The quadratic character `χ_{-d}` enters only through the properties recorded in `QuadChar`:
complete multiplicativity, values `±1` at primes `p ≠ d` (`+1` split, `-1` inert) and `0` at the
ramified prime `d`.
-/

@[expose] public section

open Finset ArithmeticFunction Real

namespace GroupoidCorr

open scoped BigOperators

/-- [note: def:quad-char] The properties of the quadratic character `χ_{-d}` that are used. -/
structure QuadChar (d : ℕ) where
  /-- the character -/
  χ : ℕ → ℤ
  hd : d.Prime
  map_one : χ 1 = 1
  map_mul : ∀ m n, χ (m * n) = χ m * χ n
  at_prime : ∀ p, p.Prime → p ≠ d → χ p = 1 ∨ χ p = -1
  at_d : χ d = 0

namespace QuadChar

variable {d : ℕ} (Q : QuadChar d)

theorem map_pow (p k : ℕ) : Q.χ (p ^ k) = Q.χ p ^ k := by
  induction k with
  | zero => simp [Q.map_one]
  | succ k ih => rw [pow_succ, Q.map_mul, ih, pow_succ]

end QuadChar

/-- `∑_{k odd} ⌊a / p^k⌋`. -/
def oddSum (p a : ℕ) : ℝ := ∑ k ∈ (Icc 1 a).filter Odd, ((a / p ^ k : ℕ) : ℝ)

/-- [note: def:quad-char] The primes `p ≤ a` with `χ(p) = -1`, i.e. inert in `K`. -/
def inertPrimes (χ : ℕ → ℤ) (a : ℕ) : Finset ℕ :=
  ((range (a + 1)).filter Nat.Prime).filter (fun p => χ p = -1)

/-- [note: def:quad-char] `ASK^♭(a) = ∑_n Λ(n) (1 - χ(n)) ⌊a/n⌋`. -/
noncomputable def askFlat (χ : ℕ → ℤ) (a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), vonMangoldt n * ((1 - (χ n : ℝ)) * ((a / n : ℕ) : ℝ))

/-- Sums against `Λ` are sums over prime powers. -/
theorem sum_vonMangoldt (a : ℕ) (G : ℕ → ℝ) (hG : ∀ n, a < n → G n = 0) :
    ∑ n ∈ range (a + 1), vonMangoldt n * G n =
      ∑ p ∈ (range (a + 1)).filter Nat.Prime, ∑ k ∈ Icc 1 a, Real.log p * G (p ^ k) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1 ^ x.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hx hne
    simp only [mem_product, mem_filter, mem_range, mem_Icc] at hx
    rw [mem_range]
    by_contra h
    simp only at h hne
    exact hne (by rw [hG _ (by omega), mul_zero])
  · rintro ⟨p, k⟩ hx _ ⟨p', k'⟩ hx' _ h
    simp only [mem_product, mem_filter, mem_range, mem_Icc] at hx hx'
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj' hx.1.2 hx'.1.2 (by omega) (by omega) h
    exact Prod.ext h1 h2
  · intro n hn hne
    have hΛ : vonMangoldt n ≠ 0 := left_ne_zero_of_mul hne
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hn' := mem_range.mp hn
    have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hk' : k < p ^ k := Nat.lt_pow_self hp.one_lt
    refine ⟨⟨p, k⟩, ?_, ?_, rfl⟩
    · simp only [mem_product, mem_filter, mem_range, mem_Icc]
      exact ⟨⟨by omega, hp⟩, by omega, by omega⟩
    · dsimp only
      rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp] at hne
      exact hne
  · rintro ⟨p, k⟩ hx _
    simp only [mem_product, mem_filter, mem_range, mem_Icc] at hx
    simp only
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hx.1.2]

/-- Legendre's formula with the sum over `1 ≤ k ≤ a`. -/
theorem padicValNat_factorial_Icc (p : ℕ) [Fact p.Prime] (a : ℕ) :
    padicValNat p a.factorial = ∑ k ∈ Icc 1 a, a / p ^ k := by
  rw [Nat.padicValNat_def, multiplicity_factorial (b := a + 1) (Nat.lt_succ_of_le (Nat.log_le_self p a))]
  rfl

/-- [note: prop:factorial] The factorial identity:
`ASK^♭(a) = ∑_{p inert} 2 log p ∑_{k odd} ⌊a/p^k⌋ + log d · ord_d(a!)`. -/
theorem askFlat_eq {d : ℕ} (Q : QuadChar d) (a : ℕ) :
    askFlat Q.χ a = ∑ p ∈ inertPrimes Q.χ a, 2 * Real.log p * oddSum p a +
      Real.log d * padicValNat d a.factorial := by
  have := Fact.mk Q.hd
  unfold askFlat
  rw [sum_vonMangoldt a _ (fun n hn => by rw [Nat.div_eq_of_lt hn]; simp)]
  -- the contribution of one prime
  set h : ℕ → ℝ := fun p =>
    ∑ k ∈ Icc 1 a, Real.log p * ((1 - (Q.χ (p ^ k) : ℝ)) * ((a / p ^ k : ℕ) : ℝ)) with hh
  have h_inert : ∀ p, Q.χ p = -1 → h p = 2 * Real.log p * oddSum p a := by
    intro p hp
    simp only [hh, oddSum, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Q.map_pow, hp]
    rcases Nat.even_or_odd k with he | ho
    · rw [ite_eq_right (Nat.not_odd_iff_even.mpr he)]; push_cast; rw [he.neg_one_pow]; ring
    · rw [ite_eq_left ho]; push_cast; rw [ho.neg_one_pow]; ring
  have h_split : ∀ p, Q.χ p = 1 → h p = 0 := by
    intro p hp
    simp only [hh]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Q.map_pow, hp, one_pow]; simp
  have h_d : h d = Real.log d * padicValNat d a.factorial := by
    simp only [hh]
    rw [padicValNat_factorial_Icc, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Q.map_pow, Q.at_d, zero_pow (by have := (mem_Icc.mp hk).1; omega)]; simp
  change ∑ p ∈ (range (a + 1)).filter Nat.Prime, h p = _
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => Q.χ p = -1)]
  congr 1
  · exact Finset.sum_congr rfl fun p hp => h_inert p (mem_filter.mp hp).2
  · rw [← h_d]
    refine Finset.sum_eq_single d (fun p hp hpd => ?_) (fun hd => ?_)
    · simp only [mem_filter, mem_range] at hp
      rcases Q.at_prime p hp.1.2 hpd with h1 | h1
      · exact h_split p h1
      · exact absurd h1 hp.2
    · -- `d > a`: every term vanishes
      simp only [hh]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk1 := (mem_Icc.mp hk).1
      have hda : a < d := by
        by_contra hda
        apply hd
        simp only [mem_filter, mem_range, Q.at_d]
        exact ⟨⟨by omega, Q.hd⟩, by norm_num⟩
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hda (Nat.le_self_pow (by omega) d))]
      simp

/-! ### The gain at inert primes -/

/-- The even part of Legendre's sum is Legendre's sum in base `p²`. -/
theorem even_sum_eq (p a : ℕ) (hp : 1 < p) :
    ∑ k ∈ (Icc 1 a).filter (fun k => ¬ Odd k), a / p ^ k = ∑ j ∈ Icc 1 a, a / (p ^ 2) ^ j := by
  symm
  refine Finset.sum_bij_ne_zero (fun j _ _ => 2 * j) ?_ ?_ ?_ ?_
  · intro j hj hne
    simp only [mem_Icc] at hj
    have h1 : (p ^ 2) ^ j ≤ a := by
      by_contra h; exact hne (Nat.div_eq_of_lt (by omega))
    have h2 : 2 * j < p ^ (2 * j) := Nat.lt_pow_self hp
    rw [← pow_mul] at h1
    simp only [mem_filter, mem_Icc, Nat.not_odd_iff_even]
    exact ⟨⟨by omega, by omega⟩, even_two_mul j⟩
  · intro j _ _ j' _ _ h; omega
  · intro k hk hne
    simp only [mem_filter, mem_Icc, Nat.not_odd_iff_even] at hk
    obtain ⟨j, hj⟩ := hk.2
    exact ⟨j, by simp only [mem_Icc]; omega, by rw [← pow_mul]; convert hne using 3; omega,
      by omega⟩
  · intro j _ _
    rw [← pow_mul]

/-- Legendre's sum in an arbitrary base `q ≥ 2`: `(q-1) ∑_{1 ≤ j ≤ a} ⌊a/q^j⌋ = a - s_q(a)`. -/
theorem legendre_base (q a : ℕ) (hq : 1 < q) :
    (q - 1) * ∑ j ∈ Icc 1 a, a / q ^ j = a - (q.digits a).sum := by
  rw [← Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]
  congr 1
  symm
  refine Finset.sum_bij_ne_zero (fun i _ _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi hne
    simp only [Nat.succ_eq_add_one] at hne
    have h1 : q ^ (i + 1) ≤ a := by
      by_contra h; exact hne (Nat.div_eq_of_lt (by omega))
    have h2 : i + 1 < q ^ (i + 1) := Nat.lt_pow_self hq
    simp only [mem_Icc]; omega
  · intro i _ _ i' _ _ h; omega
  · intro j hj hne
    simp only [mem_Icc] at hj
    have h1 : q ^ j ≤ a := by
      by_contra h; exact hne (Nat.div_eq_of_lt (by omega))
    have h2 := Nat.le_log_of_pow_le hq h1
    exact ⟨j - 1, by simp only [mem_range]; omega, by rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hj.1]; exact hne,
      by omega⟩
  · intro i _ _; rfl

/-- The base-`q` digit sum is at most `(q-1)(log_q a + 1)`. -/
theorem digit_sum_le_log (q a : ℕ) (hq : 1 < q) (ha : a ≠ 0) :
    (q.digits a).sum ≤ (q - 1) * (Nat.log q a + 1) := by
  have := List.sum_le_length_nsmul (q.digits a) (q - 1)
    (fun x hx => Nat.le_sub_one_of_lt (Nat.digits_lt_base hq hx))
  rw [Nat.length_digits q a hq ha, smul_eq_mul] at this
  linarith

/-- [note: cor:factorial-gain] The lower bound `g_p(a) = ord_p(a!) - (a-1)/(p²-1)` from
`thm:jet-gain` and `cor:height` at an inert prime. -/
noncomputable def jetBound (p a : ℕ) : ℝ :=
  (padicValNat p a.factorial : ℝ) - ((a : ℝ) - 1) / ((p : ℝ) ^ 2 - 1)

/-- `g_p(a) ≥ ∑_{k odd} ⌊a/p^k⌋ - (log_p a + 1)`. -/
theorem jetBound_ge (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (ha : 1 ≤ a) :
    oddSum p a - ((Nat.log p a : ℝ) + 1) ≤ jetBound p a := by
  have hp1 := hp.out.one_lt
  set q := p ^ 2 with hqdef
  have hq : 1 < q := by rw [hqdef]; nlinarith
  have hq' : ((q - 1 : ℕ) : ℝ) = (p : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by omega), hqdef]; push_cast; ring
  have hqpos : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
    nlinarith
  -- split Legendre's sum into odd and even parts
  have hsplit : (padicValNat p a.factorial : ℝ) =
      oddSum p a + ((∑ j ∈ Icc 1 a, a / q ^ j : ℕ) : ℝ) := by
    rw [padicValNat_factorial_Icc, ← sum_filter_add_sum_filter_not _ Odd, even_sum_eq p a hp1]
    push_cast; rfl
  have hleg := legendre_base q a hq
  have hs := Nat.digit_sum_le q a
  have hleg' : ((q - 1 : ℕ) : ℝ) * ((∑ j ∈ Icc 1 a, a / q ^ j : ℕ) : ℝ) =
      (a : ℝ) - ((q.digits a).sum : ℝ) := by
    rw [← Nat.cast_sub hs, ← Nat.cast_mul, hleg]
  rw [hq'] at hleg'
  have hdig := digit_sum_le_log q a hq (by omega)
  have hlog : Nat.log q a ≤ Nat.log p a := Nat.log_anti_left hp1 (by rw [hqdef]; nlinarith)
  have hdig' : ((q.digits a).sum : ℝ) ≤ ((p : ℝ) ^ 2 - 1) * ((Nat.log p a : ℝ) + 1) := by
    rw [← hq']
    have : (q.digits a).sum ≤ (q - 1) * (Nat.log p a + 1) :=
      hdig.trans (Nat.mul_le_mul_left _ (by omega))
    exact_mod_cast this
  unfold jetBound
  rw [hsplit]
  set E := ((∑ j ∈ Icc 1 a, a / q ^ j : ℕ) : ℝ)
  have hE : E = ((a : ℝ) - ((q.digits a).sum : ℝ)) / ((p : ℝ) ^ 2 - 1) := by
    rw [eq_div_iff hqpos.ne', mul_comm, hleg']
  rw [hE]
  have : ((a : ℝ) - (q.digits a).sum) / ((p : ℝ) ^ 2 - 1) - ((a : ℝ) - 1) / ((p : ℝ) ^ 2 - 1) ≥
      -((Nat.log p a : ℝ) + 1) := by
    rw [← sub_div, ge_iff_le, le_div_iff₀ hqpos]
    nlinarith
  linarith

/-- `log p · (log_p a + 1) ≤ 2 log a` for a prime `p ≤ a`. -/
theorem log_mul_le (p a : ℕ) (hp : p.Prime) (hpa : p ≤ a) :
    Real.log p * ((Nat.log p a : ℝ) + 1) ≤ 2 * Real.log a := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ha0 : a ≠ 0 := by have := hp.pos; omega
  have h1 : (Nat.log p a : ℝ) * Real.log p ≤ Real.log a := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.pow_log_le_self p ha0
  have h2 : Real.log p ≤ Real.log a := Real.log_le_log hp0 (by exact_mod_cast hpa)
  nlinarith

/-- [note: cor:factorial-gain] If jets of order `a` are divisible by `p^{g_p(a)}` at each inert
`p ≤ a` (`thm:jet-gain`), the resulting ideal `𝔤(a)` has
`log Nm 𝔤(a) = ∑_{p inert, p ≤ a} 2 log p · g_p(a) ≥ ASK^♭(a) - a log d/(d-1) - 4 π(a) log a`. -/
theorem factorial_gain {d : ℕ} (Q : QuadChar d) (a : ℕ) (ha : 1 ≤ a) :
    askFlat Q.χ a - a * Real.log d / (d - 1) - 4 * Nat.primeCounting a * Real.log a ≤
      ∑ p ∈ inertPrimes Q.χ a, 2 * Real.log p * jetBound p a := by
  have hd := Q.hd
  have := Fact.mk hd
  have hloga : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
  -- each inert prime loses at most `4 log a`
  have hterm : ∀ p ∈ inertPrimes Q.χ a,
      2 * Real.log p * oddSum p a - 4 * Real.log a ≤ 2 * Real.log p * jetBound p a := by
    intro p hp
    simp only [inertPrimes, mem_filter, mem_range] at hp
    have := Fact.mk hp.1.2
    have h1 := jetBound_ge p a ha
    have h2 := log_mul_le p a hp.1.2 (by omega)
    have h3 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.1.2.one_lt.le)
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  -- at most `π(a)` inert primes
  have hcard : ((inertPrimes Q.χ a).card : ℝ) ≤ Nat.primeCounting a := by
    have : (inertPrimes Q.χ a).card ≤ (Nat.primesBelow (a + 1)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Nat.primesBelow_card_eq_primeCounting'] at this
    exact_mod_cast this
  -- the ramified prime contributes at most `a log d / (d-1)`
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd.one_lt
  have hram : Real.log d * padicValNat d a.factorial ≤ a * Real.log d / (d - 1) := by
    have h : (d - 1) * padicValNat d a.factorial = a - (d.digits a).sum := by
      rw [Nat.padicValNat_def]; exact hd.sub_one_mul_multiplicity_factorial
    have hle : (d - 1) * padicValNat d a.factorial ≤ a := by rw [h]; omega
    have hle' : ((d : ℝ) - 1) * padicValNat d a.factorial ≤ a := by
      have := (Nat.cast_le (α := ℝ)).mpr hle
      rwa [Nat.cast_mul, Nat.cast_sub hd.one_lt.le, Nat.cast_one] at this
    rw [le_div_iff₀ (by linarith)]
    have : 0 ≤ Real.log d := Real.log_nonneg hd1.le
    nlinarith
  rw [askFlat_eq Q a]
  nlinarith

end GroupoidCorr
