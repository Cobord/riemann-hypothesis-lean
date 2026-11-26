module

public import Mathlib

/-!
# Denominators of the Lubin–Tate exponential and divisibility of jets

Mirrors `note/note.tex`, Section 4 (`thm:LT-exp`, `thm:jet-gain`, `cor:height`).

The formal group enters only through one identity, `[p]_F(exp_F Z) = exp_F(p Z)`, used here in
coefficient form. Valuations are replaced by an integral statement: with `ϖ ^ (q-1) = p` in a
subring `O` of a field `K`, the bound `ord_p(c_n) ≥ -(n-1)/(q-1)` says that `ϖ ^ (n-1) * c_n ∈ O`.
The unramified hypothesis enters only as the invertibility of `p ^ m - 1` in `O` for `m ≥ 1`.

The proof scales the exponential: `G(Z) = ϖ⁻¹ exp_F(ϖ Z)` has coefficients `ϖ ^ (n-1) c_n`,
and the functional equation shows by strong induction that these are integral.
-/

@[expose] public section

open PowerSeries

namespace GroupoidCorr

open scoped BigOperators

variable {K : Type*} [Field K]

/-- If the coefficients of `G` below `n` are integral, so are those of every power. -/
theorem coeff_pow_mem_of_lt (O : Subring K) (G : K⟦X⟧) (n : ℕ) (hG : ∀ m < n, coeff m G ∈ O) :
    ∀ k, ∀ m < n, coeff m (G ^ k) ∈ O := by
  intro k
  induction k with
  | zero =>
    intro m _
    rw [pow_zero, coeff_one]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  | succ k ih =>
    intro m hm
    rw [pow_succ, coeff_mul]
    refine O.sum_mem fun x hx => O.mul_mem (ih _ ?_) (hG _ ?_)
    · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega
    · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega

/-- For `k ≥ 2` and `G` without constant term, the `n`-th coefficient of `G ^ k` only involves
coefficients of `G` below `n`. -/
theorem coeff_pow_mem (O : Subring K) (G : K⟦X⟧) (n : ℕ) (h0 : coeff 0 G = 0)
    (hG : ∀ m < n, coeff m G ∈ O) (k : ℕ) (hk : 2 ≤ k) : coeff n (G ^ k) ∈ O := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [pow_succ, coeff_mul]
  refine O.sum_mem fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  by_cases h1 : x.2 = 0
  · rw [h1, h0, mul_zero]; exact O.zero_mem
  by_cases h2 : x.1 = 0
  · rw [h2, coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply, h0,
      zero_pow (by omega), zero_mul]
    exact O.zero_mem
  exact O.mul_mem (coeff_pow_mem_of_lt O G n hG _ _ (by omega)) (hG _ (by omega))

/-- [note: thm:LT-exp] The data of the Lubin–Tate setting. `O` is a subring of a field `K`,
containing `ϖ` with `ϖ ^ (q-1) = p`. The coefficients `e k` of `[p]_F(T) = p T + ∑_{k ≥ 2} e_k T^k`
are integral, and divisible by `p` for `k ≠ q` (the congruence `[p]_F ≡ T^q mod p`). `E` is the
exponential `exp_F`, normalized by `c_0 = 0`, `c_1 = 1`, and `hE` is the coefficient of `Z^n` in
`[p]_F(exp_F Z) = exp_F(p Z)`. -/
structure LTData (K : Type*) [Field K] where
  /-- the ring of integers (enlarged to contain `ϖ`) -/
  O : Subring K
  /-- the prime -/
  p : K
  /-- a `(q-1)`-th root of `p` -/
  ϖ : K
  /-- the size of the residue field -/
  q : ℕ
  hq : 2 ≤ q
  hϖ : ϖ ∈ O
  hpϖ : ϖ ^ (q - 1) = p
  hp : p ≠ 0
  /-- unramified: `p ^ m - 1` is a unit of `O` for `m ≥ 1` -/
  hunit : ∀ m, 1 ≤ m → ∃ u ∈ O, u * (p ^ m - 1) = 1
  /-- the coefficients of `[p]_F` in degrees `≥ 2` -/
  e : ℕ → K
  he : ∀ k, e k ∈ O
  hep : ∀ k, k ≠ q → e k / p ∈ O
  /-- the exponential -/
  E : K⟦X⟧
  hE0 : coeff 0 E = 0
  hE1 : coeff 1 E = 1
  hE : ∀ n, p ^ n * coeff n E = p * coeff n E + ∑ k ∈ Finset.Icc 2 n, e k * coeff n (E ^ k)

namespace LTData

variable (D : LTData K)

theorem ϖ_ne_zero : D.ϖ ≠ 0 := by
  intro h
  apply D.hp
  rw [← D.hpϖ, h, zero_pow (by have := D.hq; omega)]

/-- The scaled exponential `G(Z) = ϖ⁻¹ exp_F(ϖ Z)`, with coefficients `ϖ ^ (n-1) c_n`. -/
noncomputable def G : K⟦X⟧ := PowerSeries.mk fun n => D.ϖ ^ (n - 1) * coeff n D.E

theorem coeff_G (n : ℕ) : coeff n D.G = D.ϖ ^ (n - 1) * coeff n D.E := coeff_mk _ _

theorem coeff_G_zero : coeff 0 D.G = 0 := by rw [coeff_G, D.hE0, mul_zero]

theorem E_eq : D.E = C D.ϖ * rescale D.ϖ⁻¹ D.G := by
  ext n
  rw [coeff_C_mul, coeff_rescale, coeff_G]
  rcases n with _ | m
  · rw [D.hE0, mul_zero, mul_zero, mul_zero]
  · have := D.ϖ_ne_zero
    rw [inv_pow, Nat.add_sub_cancel]
    field_simp
    ring

theorem coeff_E_pow (k n : ℕ) :
    coeff n (D.E ^ k) = D.ϖ ^ k * D.ϖ⁻¹ ^ n * coeff n (D.G ^ k) := by
  rw [E_eq, mul_pow, ← map_pow, ← map_pow, coeff_C_mul, coeff_rescale, mul_assoc]

/-- All coefficients of the scaled exponential are integral. -/
theorem coeff_G_mem (n : ℕ) : coeff n D.G ∈ D.O := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [coeff_G_zero]; exact D.O.zero_mem
    · rw [coeff_G, D.hE1, pow_zero, mul_one]; exact D.O.one_mem
  have hϖ0 := D.ϖ_ne_zero
  have hGk : ∀ k ∈ Finset.Icc 2 n, coeff n (D.G ^ k) ∈ D.O := fun k hk =>
    coeff_pow_mem D.O D.G n D.coeff_G_zero IH k (Finset.mem_Icc.mp hk).1
  -- the functional equation, multiplied by `ϖ ^ (n-1)`
  have key : coeff n D.G * ((D.p ^ (n - 1) - 1) * D.p) =
      ∑ k ∈ Finset.Icc 2 n, D.e k * D.ϖ ^ (k - 1) * coeff n (D.G ^ k) := by
    have h1 : (D.p ^ n - D.p) * coeff n D.E =
        ∑ k ∈ Finset.Icc 2 n, D.e k * coeff n (D.E ^ k) := by
      rw [sub_mul, D.hE n]; ring
    have hpn : (D.p ^ (n - 1) - 1) * D.p = D.p ^ n - D.p := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]; ring
    rw [hpn, coeff_G, mul_assoc, mul_comm (coeff n D.E), h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk2 := (Finset.mem_Icc.mp hk).1
    rw [coeff_E_pow]
    obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel, inv_pow]
    field_simp
    ring
  obtain ⟨u, hu, hu1⟩ := D.hunit (n - 1) (by omega)
  have hne : D.p ^ (n - 1) - 1 ≠ 0 := by
    intro h; rw [h, mul_zero] at hu1; exact zero_ne_one hu1
  have hrepr : coeff n D.G =
      u * ∑ k ∈ Finset.Icc 2 n, (D.e k * D.ϖ ^ (k - 1) / D.p) * coeff n (D.G ^ k) := by
    have hS : ∑ k ∈ Finset.Icc 2 n, (D.e k * D.ϖ ^ (k - 1) / D.p) * coeff n (D.G ^ k) =
        (∑ k ∈ Finset.Icc 2 n, D.e k * D.ϖ ^ (k - 1) * coeff n (D.G ^ k)) / D.p := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hS, ← key, eq_inv_of_mul_eq_one_left hu1]
    have := D.hp
    field_simp
  rw [hrepr]
  refine D.O.mul_mem hu (D.O.sum_mem fun k hk => D.O.mul_mem ?_ (hGk k hk))
  by_cases hkq : k = D.q
  · rw [hkq, D.hpϖ, mul_div_assoc, div_self D.hp, mul_one]; exact D.he _
  · rw [mul_div_right_comm]; exact D.O.mul_mem (D.hep k hkq) (D.O.pow_mem D.hϖ _)

/-- [note: thm:LT-exp] Denominators of the Lubin–Tate exponential: `ϖ ^ (n-1) c_n` is integral
for `n ≥ 1`, i.e. `ord_p(c_n) ≥ -(n-1)/(q-1)`. -/
theorem exp_coeff_mem (n : ℕ) : D.ϖ ^ (n - 1) * coeff n D.E ∈ D.O := by
  rw [← coeff_G]; exact D.coeff_G_mem n

/-- [note: thm:jet-gain] For integral `f = ∑ f_m T^m`, the coefficient
`b_a = [Z^a] f(exp_F Z) = ∑_{m ≤ a} f_m [Z^a] exp_F(Z)^m` satisfies `ϖ ^ (a-1) b_a ∈ O` for
`a ≥ 1`, i.e. `ord_p(b_a) ≥ -(a-1)/(q-1)`. -/
theorem jet_coeff_mem (f : ℕ → K) (hf : ∀ m, f m ∈ D.O) (a : ℕ) (ha : 1 ≤ a) :
    D.ϖ ^ (a - 1) * ∑ m ∈ Finset.range (a + 1), f m * coeff a (D.E ^ m) ∈ D.O := by
  have hϖ0 := D.ϖ_ne_zero
  have hGall : ∀ k, coeff a (D.G ^ k) ∈ D.O := fun k =>
    coeff_pow_mem_of_lt D.O D.G (a + 1) (fun m _ => D.coeff_G_mem m) k a (by omega)
  rw [Finset.sum_range_succ', pow_zero, coeff_one, ite_eq_right (by omega), mul_zero, add_zero,
    Finset.mul_sum]
  refine D.O.sum_mem fun m _ => ?_
  have : D.ϖ ^ (a - 1) * (f (m + 1) * coeff a (D.E ^ (m + 1))) =
      f (m + 1) * D.ϖ ^ m * coeff a (D.G ^ (m + 1)) := by
    rw [coeff_E_pow]
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel, inv_pow]
    field_simp
    ring
  rw [this]
  exact D.O.mul_mem (D.O.mul_mem (hf _) (D.O.pow_mem D.hϖ _)) (hGall _)

/-- [note: thm:jet-gain] Hence `(∂^a f)(0) = a! b_a` satisfies
`ord_p((∂^a f)(0)) ≥ ord_p(a!) - (a-1)/(q-1)`: `ϖ ^ (a-1) a! b_a` is `a!` times an integral
element. -/
theorem jet_factorial_mem (f : ℕ → K) (hf : ∀ m, f m ∈ D.O) (a : ℕ) (ha : 1 ≤ a) :
    ∃ x ∈ D.O, D.ϖ ^ (a - 1) *
      ((a.factorial : K) * ∑ m ∈ Finset.range (a + 1), f m * coeff a (D.E ^ m)) =
      a.factorial * x :=
  ⟨_, D.jet_coeff_mem f hf a ha, by ring⟩

end LTData

/-- [note: cor:height] Split primes (`q = p`): with `s = s_p(a)`,
`(p-1) (ord_p(a!) - (a-1)/(p-1)) = 1 - s ≤ 0` for `a ≥ 1`. -/
theorem height_split (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (ha : 1 ≤ a) :
    ((p : ℤ) - 1) * padicValNat p a.factorial - ((a : ℤ) - 1) = 1 - ((p.digits a).sum : ℤ) ∧
      1 ≤ (p.digits a).sum := by
  have h : (p - 1) * padicValNat p a.factorial = a - (p.digits a).sum := by
    rw [Nat.padicValNat_def]; exact hp.out.sub_one_mul_multiplicity_factorial
  have hs := Nat.digit_sum_le p a
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  refine ⟨?_, ?_⟩
  · have h' : ((p : ℤ) - 1) * padicValNat p a.factorial = a - (p.digits a).sum := by
      have : (((p - 1 : ℕ) : ℤ)) * (padicValNat p a.factorial : ℤ) =
          ((a - (p.digits a).sum : ℕ) : ℤ) := by exact_mod_cast h
      rw [Nat.cast_sub hp1, Nat.cast_sub hs, Nat.cast_one] at this
      exact this
    rw [h']; ring
  · have hne : p.digits a ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    have hl := Nat.getLast_digit_ne_zero p (by omega : a ≠ 0)
    have := List.le_sum_of_mem (List.getLast_mem hne)
    omega

/-- [note: cor:height] Inert primes (`q = p²`): with `s = s_p(a)`,
`(p²-1) (ord_p(a!) - (a-1)/(p²-1)) = a p - (p+1) s + 1`. -/
theorem height_inert (p : ℕ) [hp : Fact p.Prime] (a : ℕ) :
    ((p : ℤ) ^ 2 - 1) * padicValNat p a.factorial - ((a : ℤ) - 1) =
      a * p - (p + 1) * (p.digits a).sum + 1 := by
  have h : (p - 1) * padicValNat p a.factorial = a - (p.digits a).sum := by
    rw [Nat.padicValNat_def]; exact hp.out.sub_one_mul_multiplicity_factorial
  have hs := Nat.digit_sum_le p a
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have h' : ((p : ℤ) - 1) * padicValNat p a.factorial = a - (p.digits a).sum := by
    have : (((p - 1 : ℕ) : ℤ)) * (padicValNat p a.factorial : ℤ) =
        ((a - (p.digits a).sum : ℕ) : ℤ) := by exact_mod_cast h
    rw [Nat.cast_sub hp1, Nat.cast_sub hs, Nat.cast_one] at this
    exact this
  linear_combination ((p : ℤ) + 1) * h'

end GroupoidCorr
