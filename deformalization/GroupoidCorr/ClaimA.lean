import GroupoidCorr.Content
import GroupoidCorr.Factorial

/-!
# Claim A from Hypothesis J

Mirrors `note/note.tex`, Section 8 (`lem:norm-bound`, `thm:claimA`); this is Theorem 8.13 of the
main account.

`E` is a number field and the period map is `𝓞_E`-bilinear. Hypothesis J (jets at inert places)
is about formal groups and is not formalized; we assume its consequence for each step: at every
prime `𝔮` of `𝓞_E` above an inert `p ≤ aᵢ`, step `i` is divisible by `𝔮 ^ mᵢ` with
`mᵢ ≥ e(𝔮|p) g_p(aᵢ)` (`thm:jet-gain`), and orders add (`thm:orders-add-corr`), so the content
lies in `𝔮 ^ (∑ᵢ mᵢ)`.
-/

open NumberField Finset

namespace GroupoidCorr

open scoped BigOperators

variable {E : Type*} [Field E] [NumberField E]

/-- Primes of `𝓞_E` above `p`, indexed over a finite set of rational primes. -/
abbrev Above (E : Type*) [Field E] [NumberField E] (T : Finset ℕ) : Type _ :=
  Σ p : T, (Ideal.span {((p : ℕ) : ℤ)}).primesOver (𝓞 E)

theorem above_injective (T : Finset ℕ) (x y : Above E T) (h : x.2.1 = y.2.1) : x = y := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := x
  obtain ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ := y
  simp only at h
  subst h
  have h1 : Ideal.span {(p : ℤ)} = Ideal.span {(p' : ℤ)} := hq.2.over.trans hq'.2.over.symm
  rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff] at h1
  have : p = p' := by omega
  subst this
  rfl

/-- [note: prop:content] (c) `log Nm cont(per) = ∑_𝔭 ord_𝔭(per) · log Nm 𝔭`, where
`Nm 𝔭 = p ^ f(𝔭|p)`. -/
theorem log_absNorm_content {N P : Type*} [AddCommGroup N] [Module (𝓞 E) N] [AddCommGroup P]
    [Module (𝓞 E) P] (per : N →ₗ[𝓞 E] P →ₗ[𝓞 E] 𝓞 E) (hC : content per ≠ ⊥) :
    Real.log (Ideal.absNorm (content per)) =
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
        (ordP v per : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
  classical
  have hfin := Ideal.hasFiniteMulSupport (R := 𝓞 E) hC
  set s := hfin.toFinset
  have hsub : Function.mulSupport
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) => v.asIdeal ^ ordP v per) ⊆ s := by
    intro v hv; exact hfin.mem_toFinset.mpr hv
  have hprod : content per = ∏ v ∈ s, v.asIdeal ^ ordP v per := by
    conv_lhs => rw [← content_factorization per hC]
    exact finprod_eq_prod_of_mulSupport_subset _ hsub
  have hne : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Ideal.absNorm v.asIdeal ≠ 0 :=
    fun v h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  rw [finsum_eq_sum_of_support_subset _ (s := s) ?_, hprod, map_prod, Nat.cast_prod,
    Real.log_prod]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_pow, Nat.cast_pow, Real.log_pow]
  · intro v _
    rw [map_pow, Nat.cast_pow]
    exact pow_ne_zero _ (by exact_mod_cast hne v)
  · intro v hv
    apply hsub
    intro h1
    simp only at h1
    apply hv
    have h0 : ordP v per = 0 := by
      by_contra h0
      have : v.asIdeal ^ ordP v per ≤ v.asIdeal := Ideal.pow_le_self h0
      rw [h1, Ideal.one_eq_top, top_le_iff] at this
      exact v.isPrime.ne_top this
    simp [h0]

/-- [note: lem:norm-bound] If `C ≤ 𝔮 ^ n(𝔮)` for every prime `𝔮` above the primes in `T`, then
`∑ n(𝔮) f(𝔮|p) log p ≤ log Nm C`. -/
theorem log_absNorm_ge (C : Ideal (𝓞 E)) (hC : C ≠ ⊥) (T : Finset ℕ)
    [hT' : ∀ p : T, Fact (p : ℕ).Prime] (n : Above E T → ℕ) (hn : ∀ x, C ≤ x.2.1 ^ n x) :
    ∑ x : Above E T, ((n x * x.2.1.inertiaDeg ℤ : ℕ) : ℝ) * Real.log (x.1 : ℕ) ≤
      Real.log (Ideal.absNorm C) := by
  classical
  have hT : ∀ p ∈ T, p.Prime := fun p hp => (hT' ⟨p, hp⟩).out
  have hprime : ∀ x : Above E T, Prime x.2.1 := by
    intro x
    have hpT := hT _ x.1.2
    have := x.2.2.1
    have := x.2.2.2
    refine Ideal.prime_of_isPrime ?_ x.2.2.1
    intro hbot
    have h := x.2.2.2.over
    rw [hbot, Ideal.under_bot, Ideal.span_singleton_eq_bot] at h
    exact hpT.ne_zero (by exact_mod_cast h)
  have hle : C ≤ ∏ x : Above E T, x.2.1 ^ n x := by
    rw [← IsDedekindDomain.inf_pow_eq_prod_of_prime univ (fun x : Above E T => x.2.1) n
      (fun x _ => hprime x) (fun x _ y _ hxy h => hxy (above_injective T x y h))]
    rw [Finset.inf_eq_iInf]
    simp only [Submodule.mem_iInf, IsConcreteLE.le_iff]
    exact fun a ha x _ => hn x ha
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hCpos : 0 < Ideal.absNorm C :=
    Nat.pos_of_ne_zero (fun h => hC (Ideal.absNorm_eq_zero_iff.mp h))
  have hnorm : ∀ x : Above E T, Ideal.absNorm x.2.1 = (x.1 : ℕ) ^ x.2.1.inertiaDeg ℤ := by
    intro x
    have := x.2.2.1
    have := x.2.2.2
    rw [← Ideal.absNorm_pow_inertiaDeg (Ideal.span {((x.1 : ℕ) : ℤ)}) x.2.1]
    simp
  rw [map_prod] at hdvd
  have hle' := Nat.le_of_dvd hCpos hdvd
  have hpos : ∀ x : Above E T, (0 : ℝ) < ((x.1 : ℕ) : ℝ) := fun x => by
    exact_mod_cast (hT _ x.1.2).pos
  calc ∑ x : Above E T, ((n x * x.2.1.inertiaDeg ℤ : ℕ) : ℝ) * Real.log (x.1 : ℕ)
      = Real.log ((∏ x : Above E T, Ideal.absNorm (x.2.1 ^ n x) : ℕ) : ℝ) := by
        rw [Nat.cast_prod, Real.log_prod]
        · refine Finset.sum_congr rfl fun x _ => ?_
          rw [map_pow, hnorm, ← pow_mul, Nat.cast_pow, Real.log_pow, mul_comm (n x)]
        · intro x _
          rw [map_pow, hnorm]
          exact_mod_cast (pow_pos (pow_pos (hT _ x.1.2).pos _) _).ne'
    _ ≤ Real.log (Ideal.absNorm C) := by
        apply Real.log_le_log
        · rw [Nat.cast_pos]
          exact Finset.prod_pos fun x _ => by
            rw [map_pow, hnorm]; exact pow_pos (pow_pos (hT _ x.1.2).pos _) _
        · exact_mod_cast hle'

/-- The fundamental identity `∑_{𝔮 | p} e f = [E : ℚ]`. -/
theorem sum_ef (p : ℕ) [hp : Fact p.Prime] :
    ∑ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ =
      Module.finrank ℚ E := by
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp.out)
  rw [Ideal.sum_ramification_inertia_eq_finrank, RingOfIntegers.rank]

/-- [note: thm:claimA] The core estimate: if at every prime `𝔮` above `p ∈ T` the content lies in
`𝔮 ^ m` with `m ≥ e(𝔮|p) G(p)`, then `[E:ℚ] ∑_{p ∈ T} log p · G(p) ≤ log Nm C`. -/
theorem claimA_core (C : Ideal (𝓞 E)) (hC : C ≠ ⊥) (T : Finset ℕ)
    [hT' : ∀ p : T, Fact (p : ℕ).Prime] (G : ℕ → ℝ)
    (hJ : ∀ x : Above E T, ∃ m : ℕ, (x.2.1.ramificationIdx ℤ : ℝ) * G x.1 ≤ m ∧ C ≤ x.2.1 ^ m) :
    (Module.finrank ℚ E : ℝ) * ∑ p ∈ T, Real.log p * G p ≤ Real.log (Ideal.absNorm C) := by
  have hT : ∀ p ∈ T, p.Prime := fun p hp => (hT' ⟨p, hp⟩).out
  choose n hn1 hn2 using hJ
  refine le_trans ?_ (log_absNorm_ge C hC T n hn2)
  have hterm : ∀ x : Above E T,
      ((x.2.1.ramificationIdx ℤ * x.2.1.inertiaDeg ℤ : ℕ) : ℝ) * (Real.log (x.1 : ℕ) * G x.1) ≤
        ((n x * x.2.1.inertiaDeg ℤ : ℕ) : ℝ) * Real.log (x.1 : ℕ) := by
    intro x
    have hlog : 0 ≤ Real.log (x.1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (hT _ x.1.2).one_lt.le)
    have hf : (0 : ℝ) ≤ x.2.1.inertiaDeg ℤ := Nat.cast_nonneg _
    push_cast
    have := mul_le_mul_of_nonneg_right (hn1 x) (mul_nonneg hf hlog)
    nlinarith
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun x _ => hterm x)
  rw [Fintype.sum_sigma, Finset.mul_sum, ← Finset.sum_coe_sort T]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := hT' p
  simp only
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_ef]

/-- [note: thm:claimA] Claim A from Hypothesis J. Let `a : Fin ℓ → ℕ` be the jet orders of the
steps, all `≤ A`. Assume that for every prime `𝔮` of `𝓞_E` above an inert `p ≤ A`, step `i` is
divisible by `𝔮 ^ mᵢ` with `mᵢ ≥ e(𝔮|p) g_p(aᵢ)` whenever `p ≤ aᵢ`, and that the content of the
period map lies in `𝔮 ^ (∑ᵢ mᵢ)`. Then
`log Nm cont(per) ≥ [E:ℚ]/2 · ∑ᵢ (ASK^♭(aᵢ) - aᵢ log d/(d-1) - 4 π(aᵢ) log aᵢ)`. -/
theorem claimA {d : ℕ} (Q : QuadChar d) {N P : Type*} [AddCommGroup N] [Module (𝓞 E) N]
    [AddCommGroup P] [Module (𝓞 E) P] (per : N →ₗ[𝓞 E] P →ₗ[𝓞 E] 𝓞 E) (hC : content per ≠ ⊥)
    {ℓ : ℕ} (a : Fin ℓ → ℕ) (ha : ∀ i, 1 ≤ a i) (A : ℕ) (hA : ∀ i, a i ≤ A)
    (hJ : ∀ x : Above E (inertPrimes Q.χ A), ∃ m : Fin ℓ → ℕ,
      (∀ i, (x.1 : ℕ) ≤ a i → (x.2.1.ramificationIdx ℤ : ℝ) * jetBound x.1 (a i) ≤ m i) ∧
      VanishesMod per (x.2.1 ^ ∑ i, m i)) :
    (Module.finrank ℚ E : ℝ) / 2 *
        ∑ i, (askFlat Q.χ (a i) - a i * Real.log d / (d - 1) -
          4 * Nat.primeCounting (a i) * Real.log (a i)) ≤
      Real.log (Ideal.absNorm (content per)) := by
  set T := inertPrimes Q.χ A
  have hT : ∀ p ∈ T, p.Prime := fun p hp => by
    simp only [T, inertPrimes, mem_filter] at hp; exact hp.1.2
  have hTf : ∀ p : T, Fact (p : ℕ).Prime := fun p => ⟨hT _ p.2⟩
  set G : ℕ → ℝ := fun p => ∑ i, if p ≤ a i then jetBound p (a i) else 0
  have hcore := claimA_core (content per) hC T G (fun x => by
    obtain ⟨m, hm1, hm2⟩ := hJ x
    refine ⟨∑ i, m i, ?_, (vanishesMod_iff _ _).mp hm2⟩
    simp only [G, Finset.mul_sum]
    push_cast
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with h
    · exact hm1 i h
    · simp)
  refine le_trans ?_ hcore
  -- per step, `cor:factorial-gain`; then exchange the sums
  have hfilter : ∀ i, inertPrimes Q.χ (a i) = T.filter (fun p => p ≤ a i) := by
    intro i
    ext p
    simp only [T, inertPrimes, mem_filter, mem_range]
    have := hA i
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨by omega, h2⟩, h3⟩, by omega⟩
    · rintro ⟨⟨⟨_, h2⟩, h3⟩, h4⟩; exact ⟨⟨by omega, h2⟩, h3⟩
  have hstep : ∀ i, askFlat Q.χ (a i) - a i * Real.log d / (d - 1) -
      4 * Nat.primeCounting (a i) * Real.log (a i) ≤
      2 * ∑ p ∈ T, Real.log p * (if p ≤ a i then jetBound p (a i) else 0) := by
    intro i
    refine le_trans (factorial_gain Q (a i) (ha i)) (le_of_eq ?_)
    rw [hfilter i, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  have hE : (0 : ℝ) ≤ Module.finrank ℚ E / 2 := by positivity
  calc (Module.finrank ℚ E : ℝ) / 2 * ∑ i, (askFlat Q.χ (a i) - a i * Real.log d / (d - 1) -
          4 * Nat.primeCounting (a i) * Real.log (a i))
      ≤ (Module.finrank ℚ E : ℝ) / 2 *
          ∑ i, 2 * ∑ p ∈ T, Real.log p * (if p ≤ a i then jetBound p (a i) else 0) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hstep i) hE
    _ = (Module.finrank ℚ E : ℝ) * ∑ p ∈ T, Real.log p * G p := by
        simp only [G, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => ?_
        ring

end GroupoidCorr
