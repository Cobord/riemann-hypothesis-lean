module

public import GroupoidCorr.Adjoint
public import GroupoidCorr.Correspondence

/-!
# Adjoints of correspondences and the doubled correspondence

Mirrors `note/note.tex`, Section 10 (`def:scalar-corr`, `prop:corr-adjoint`, `thm:doubling`,
`lem:pairing-pos`, `cor:gram-kernel`).

This is the structural core of the lower bound from the Rallis inner product formula. For a
correspondence `C` between finite groupoids with both legs faithful and a scalar kernel `K`, the
adjoint of its operator for the mass pairing is the operator of the transposed correspondence
(legs swapped, kernel conjugated). Hence the Gram operator `T_C† T_C` is the operator of the
*doubled* correspondence `Cᵗ ∘ C` on the 2-fibre product `C ×_{X'} C`, with kernel
`K(c₁) conj K(c₂)` (`prop:composition`); this is the groupoid form of the seesaw / doubling step.
The mass pairing is positive definite, so `T_C a = 0` exactly when `⟨a, T_{Cᵗ ∘ C} a⟩ = 0`.

What is not formalized: the Rallis inner product formula, which identifies the action of the
doubled correspondence on Hecke-isotypic components with special `L`-values.
-/

@[expose] public section

open CategoryTheory ComplexConjugate

namespace GroupoidCorr

open scoped BigOperators

universe u₀ v₀ u₁ v₁ u₂ v₂

/-- Multiplication by `z` on `ℂ`, as an endomorphism in `ModuleCat ℂ`. -/
noncomputable def mulHom (z : ℂ) : ModuleCat.of ℂ ℂ ⟶ ModuleCat.of ℂ ℂ :=
  ModuleCat.ofHom (z • LinearMap.id)

theorem mulHom_apply (z w : ℂ) : (mulHom z).hom w = z * w := rfl

section

variable {X : Type u₁} [Groupoid.{v₁} X] {X' : Type u₂} [Groupoid.{v₂} X']
  {C : Type u₀} [Groupoid.{v₀} C]

/-- [note: def:scalar-corr] The kernel `src^* ℂ ⟶ tgt^* ℂ` given by a function `K : C → ℂ`
constant on isomorphism classes: multiplication by `K c` at `c`. -/
noncomputable def scalarKernel (src : C ⥤ X) (tgt : C ⥤ X') (K : C → ℂ)
    (hK : ∀ {c c' : C} (_ : c ⟶ c'), K c = K c') : src ⋙ cst X ⟶ tgt ⋙ cst X' where
  app c := mulHom (K c)
  naturality c c' h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp [mulHom, hK h]

/-- [note: def:scalar-corr] The correspondence with legs `src`, `tgt` and scalar kernel `K`, from
`(X, ℂ)` to `(X', ℂ)`. -/
noncomputable def scalarCorr [FinGroupoid C] [FinGroupoid X'] (src : C ⥤ X) (tgt : C ⥤ X')
    [tgt.Faithful] (K : C → ℂ) (hK : ∀ {c c' : C} (_ : c ⟶ c'), K c = K c') :
    Corr (cst X) (cst X') C where
  src := src
  tgt := tgt
  faithful := inferInstance
  finite := fun _ => inferInstance
  K := scalarKernel src tgt K hK

theorem conj_invariant {K : C → ℂ} (hK : ∀ {c c' : C} (_ : c ⟶ c'), K c = K c') :
    ∀ {c c' : C} (_ : c ⟶ c'), conj (K c) = conj (K c') :=
  fun h => by rw [hK h]

/-- [note: def:scalar-corr] The transposed correspondence: legs swapped, kernel conjugated. -/
noncomputable def scalarCorrT [FinGroupoid C] [FinGroupoid X] (src : C ⥤ X) (tgt : C ⥤ X')
    [src.Faithful] (K : C → ℂ) (hK : ∀ {c c' : C} (_ : c ⟶ c'), K c = K c') :
    Corr (cst X') (cst X) C :=
  scalarCorr tgt src (fun c => conj (K c)) (conj_invariant hK)

end

/-- [note: lem:pairing-pos] Conjugate symmetry of the mass pairing. -/
theorem ginner_comm {X : Type u₁} [Groupoid.{v₁} X] [FinGroupoid X] (a b : X → ℂ) :
    ginner b a = conj (ginner a b) := by
  unfold ginner
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_div₀, map_mul, Complex.conj_conj, map_natCast, mul_comm]

section adjoint

variable {X : Type u₁} [Groupoid.{v₁} X] {X' : Type u₂} [Groupoid.{v₂} X']
  {C : Type u₀} [Groupoid.{v₀} C] [FinGroupoid X] [FinGroupoid X'] [FinGroupoid C]
  (src : C ⥤ X) (tgt : C ⥤ X') [src.Faithful] [tgt.Faithful] (K : C → ℂ)
  (hK : ∀ {c c' : C} (_ : c ⟶ c'), K c = K c')

/-- [note: prop:corr-adjoint] Adjointness: for the mass pairings, the operator of the
transposed correspondence is the adjoint of the operator of the correspondence:
`⟨T_C a, b⟩_{X'} = ⟨a, T_{Cᵗ} b⟩_X`. -/
theorem scalarCorr_adjoint (s : Sec (cst X)) (t : Sec (cst X')) :
    ginner (bval ((scalarCorr src tgt K hK).op s)) (bval t) =
      ginner (bval s) (bval ((scalarCorrT src tgt K hK).op t)) := by
  -- both sides are `∑_{[c]} K(c) s(src c) conj t(tgt c) / |Aut c|`
  have h1 := ginner_push tgt (Sec.map (scalarKernel src tgt K hK) (Sec.pull src s)) t
  have h2 := ginner_push src
    (Sec.map (scalarKernel tgt src (fun c => conj (K c)) (conj_invariant hK)) (Sec.pull tgt t)) s
  change ginner (pval tgt (Sec.map (scalarKernel src tgt K hK) (Sec.pull src s))) (bval t) =
    ginner (bval s) (pval src
      (Sec.map (scalarKernel tgt src (fun c => conj (K c)) (conj_invariant hK)) (Sec.pull tgt t)))
  rw [h1, ginner_comm _ (bval s), h2, ← ginner_comm]
  unfold ginner
  refine Finset.sum_congr rfl fun q _ => ?_
  change K _ * bval s (src.obj _) * conj (bval t (tgt.obj _)) / _ =
    bval s (src.obj _) * conj (conj (K _) * bval t (tgt.obj _)) / _
  simp only [map_mul, Complex.conj_conj]
  ring

end adjoint

section doubling

variable {X : Type u₁} [Groupoid.{v₁} X] {X' : Type u₂} [Groupoid.{v₂} X']
  {C : Type u₀} [Groupoid.{v₀} C] [FinGroupoid X] [FinGroupoid X'] [FinGroupoid C]
  (src : C ⥤ X) (tgt : C ⥤ X') [src.Faithful] [tgt.Faithful] (K : C → ℂ)
  (hK : ∀ {c c' : C} (_ : c ⟶ c'), K c = K c')

/-- [note: thm:doubling] The kernel of the doubled correspondence `Cᵗ ∘ C` on
`C ×_{X'} C = Comma tgt tgt`: at `(c₁, c₂, γ)` it is multiplication by `K(c₁) conj K(c₂)`. -/
theorem doubled_kernel (a : Comma tgt tgt) :
    ((scalarCorr src tgt K hK).comp (scalarCorrT src tgt K hK)).K.app a =
      mulHom (K a.left * conj (K a.right)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp [Corr.comp, Corr.compKernel, scalarCorr, scalarCorrT, scalarKernel, mulHom, mul_comm]

/-- [note: thm:doubling] Doubling: the Gram operator of the correspondence is the operator of the
doubled correspondence, `⟨T_C a, T_C b⟩_{X'} = ⟨a, T_{Cᵗ ∘ C} b⟩_X`. -/
theorem gram_eq_doubled (s s' : Sec (cst X)) :
    ginner (bval ((scalarCorr src tgt K hK).op s)) (bval ((scalarCorr src tgt K hK).op s')) =
      ginner (bval s)
        (bval (((scalarCorr src tgt K hK).comp (scalarCorrT src tgt K hK)).op s')) := by
  rw [scalarCorr_adjoint, Corr.op_comp]

end doubling

section positivity

variable {X : Type u₁} [Groupoid.{v₁} X] [FinGroupoid X]

/-- [note: lem:pairing-pos] The mass pairing is positive: `⟨a, a⟩ = ∑_{[x]} |a(x)|² / |Aut x|`. -/
theorem ginner_self (a : X → ℂ) :
    haveI := Fintype.ofFinite (Pi0 X)
    ginner a a = ((∑ q : Pi0 X, Complex.normSq (a (Quotient.out q)) /
      Nat.card (Quotient.out q ⟶ Quotient.out q) : ℝ) : ℂ) := by
  unfold ginner
  push_cast
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Complex.mul_conj]

/-- [note: lem:pairing-pos] The mass pairing is definite on functions constant on isomorphism
classes: `⟨a, a⟩ = 0` only for `a = 0`. -/
theorem ginner_self_eq_zero (a : X → ℂ) (ha : ∀ {x y : X} (_ : x ⟶ y), a x = a y)
    (h : ginner a a = 0) : a = 0 := by
  classical
  let _ := Fintype.ofFinite (Pi0 X)
  rw [ginner_self] at h
  have h' : ∑ q : Pi0 X, Complex.normSq (a (Quotient.out q)) /
      (Nat.card (Quotient.out q ⟶ Quotient.out q) : ℝ) = 0 := by exact_mod_cast h
  have hpos : ∀ q : Pi0 X, 0 ≤ Complex.normSq (a (Quotient.out q)) /
      (Nat.card (Quotient.out q ⟶ Quotient.out q) : ℝ) := fun q =>
    div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)
  have hq := (Finset.sum_eq_zero_iff_of_nonneg fun q _ => hpos q).mp h'
  funext x
  obtain ⟨i⟩ := out_hom x
  have hx := hq (Quotient.mk _ x) (Finset.mem_univ _)
  have hcard : (Nat.card (Quotient.out (Quotient.mk (isIsomorphicSetoid X) x) ⟶
      Quotient.out (Quotient.mk (isIsomorphicSetoid X) x)) : ℝ) ≠ 0 := by
    have := card_aut_ne_zero (Quotient.out (Quotient.mk (isIsomorphicSetoid X) x))
    exact_mod_cast this
  rw [div_eq_zero_iff, or_iff_left hcard, Complex.normSq_eq_zero] at hx
  rw [← ha i, hx, Pi.zero_apply]

end positivity

section gramKernel

variable {X : Type u₁} [Groupoid.{v₁} X] {X' : Type u₂} [Groupoid.{v₂} X']
  {C : Type u₀} [Groupoid.{v₀} C] [FinGroupoid X] [FinGroupoid X'] [FinGroupoid C]
  (src : C ⥤ X) (tgt : C ⥤ X') [src.Faithful] [tgt.Faithful] (K : C → ℂ)
  (hK : ∀ {c c' : C} (_ : c ⟶ c'), K c = K c')

/-- [note: cor:gram-kernel] The kernel of `T_C` is detected by the doubled correspondence:
`T_C a = 0` if and only if `⟨a, T_{Cᵗ ∘ C} a⟩ = 0`. -/
theorem op_eq_zero_iff_doubled (s : Sec (cst X)) :
    bval ((scalarCorr src tgt K hK).op s) = 0 ↔
      ginner (bval s)
        (bval (((scalarCorr src tgt K hK).comp (scalarCorrT src tgt K hK)).op s)) = 0 := by
  rw [← gram_eq_doubled]
  constructor
  · intro h
    rw [h]
    unfold ginner
    simp
  · intro h
    exact ginner_self_eq_zero _ (fun g => ((scalarCorr src tgt K hK).op s).compat g) h

end gramKernel

end GroupoidCorr
