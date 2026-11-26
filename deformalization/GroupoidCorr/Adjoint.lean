module

public import GroupoidCorr.Pushforward

/-!
# Groupoid cardinality and adjointness

Mirrors `note/note.tex`, Section 2 (`def:finite-groupoid`, `prop:adjoint`).

Functions on isomorphism classes are sections of the constant local system `ℂ`. The pairing
`⟨a, b⟩_X = ∑_{[x]} a(x) conj(b(x)) / |Aut x|` is computed on chosen representatives of
isomorphism classes. For faithful `f`, `⟨f_! a, b⟩_Y = ⟨a, f^* b⟩_X`.

Proof: double counting of triples `([x], [y], α : f x ⟶ y)` of chosen representatives.
Each class in the fibre of `f` over `y` is hit `|Aut x|` times (faithfulness), and
`|Hom(f x, y)|` is `|Aut y|` if `f x ≅ y` and `0` otherwise.
-/

@[expose] public section

open CategoryTheory ComplexConjugate

namespace GroupoidCorr

universe u₁ v₁ u₂ v₂

/-- Isomorphism classes of objects. -/
abbrev Pi0 (X : Type u₁) [Groupoid.{v₁} X] : Type u₁ := Quotient (isIsomorphicSetoid X)

/-- [note: def:finite-groupoid] A finite groupoid: finitely many isomorphism classes and finite
automorphism groups. -/
class FinGroupoid (X : Type u₁) [Groupoid.{v₁} X] : Prop where
  finite_classes : Finite (Pi0 X)
  finite_aut : ∀ x : X, Finite (x ⟶ x)

variable {X : Type u₁} [Groupoid.{v₁} X] {Y : Type u₂} [Groupoid.{v₂} Y]

instance [FinGroupoid X] : Finite (Pi0 X) := FinGroupoid.finite_classes

/-- [note: def:finite-groupoid] In a finite groupoid all hom-sets are finite. -/
instance finite_hom [FinGroupoid X] (x y : X) : Finite (x ⟶ y) := by
  by_cases h : Nonempty (x ⟶ y)
  · obtain ⟨i⟩ := h
    have := FinGroupoid.finite_aut y
    exact Finite.of_equiv _ (Iso.homCongr (asIso i).symm (Iso.refl y))
  · have := not_nonempty_iff.mp h
    infer_instance

/-- `|Hom(x, y)| = |Aut y|` when `x ≅ y`. -/
theorem card_hom_eq (x y : X) (i : x ⟶ y) : Nat.card (x ⟶ y) = Nat.card (y ⟶ y) :=
  Nat.card_congr (Iso.homCongr (asIso i) (Iso.refl y))

theorem card_aut_eq (x y : X) (i : x ⟶ y) : Nat.card (x ⟶ x) = Nat.card (y ⟶ y) :=
  Nat.card_congr (Iso.homCongr (asIso i) (asIso i))

theorem card_aut_ne_zero [FinGroupoid X] (x : X) : (Nat.card (x ⟶ x) : ℂ) ≠ 0 := by
  have : Nonempty (x ⟶ x) := ⟨𝟙 x⟩
  exact_mod_cast (Nat.card_pos (α := x ⟶ x)).ne'

/-- The representative of a class is isomorphic to any member. -/
theorem out_hom (x : X) : Nonempty (Quotient.out (Quotient.mk (isIsomorphicSetoid X) x) ⟶ x) := by
  have h := Quotient.exact (Quotient.out_eq (Quotient.mk (isIsomorphicSetoid X) x))
  obtain ⟨i⟩ := h
  exact ⟨i.hom⟩

/-- The constant local system `ℂ`. -/
abbrev cst (X : Type u₁) [Groupoid.{v₁} X] : LocalSystem ℂ X :=
  (Functor.const X).obj (ModuleCat.of ℂ ℂ)

/-- The value of a section of `f^* ℂ`, as a complex number. -/
abbrev cval (f : X ⥤ Y) (a : Sec (f ⋙ cst Y)) (x : X) : ℂ := a.val x

/-- The value of a section of `ℂ`, as a complex number. -/
abbrev bval (b : Sec (cst Y)) (y : Y) : ℂ := b.val y

/-- The pushforward of a section of `f^* ℂ`, as a function to `ℂ`. -/
noncomputable abbrev pval (f : X ⥤ Y) [∀ y, Finite (Fibre f y)] (a : Sec (f ⋙ cst Y)) (y : Y) :
    ℂ :=
  pushVal f (cst Y) a y

theorem cst_compat (f : X ⥤ Y) (a : Sec (f ⋙ cst Y)) {x x' : X} (g : x ⟶ x') :
    cval f a x = cval f a x' :=
  a.compat g

/-- [note: def:finite-groupoid] The pairing `⟨a, b⟩ = ∑_{[x]} a(x) conj(b(x)) / |Aut x|`, on chosen
representatives of the isomorphism classes. -/
noncomputable def ginner [FinGroupoid X] (a b : X → ℂ) : ℂ :=
  haveI := Fintype.ofFinite (Pi0 X)
  ∑ q : Pi0 X, a (Quotient.out q) * conj (b (Quotient.out q)) / Nat.card (Quotient.out q ⟶ Quotient.out q)

section

variable (f : X ⥤ Y)

/-- `(qx, α) ↦ [(x, α)]`, with `x` the chosen representative of `qx`. -/
noncomputable def toFibre (y : Y) (t : Σ qx : Pi0 X, (f.obj (Quotient.out qx) ⟶ y)) : Fibre f y :=
  Quotient.mk _ ⟨Quotient.out t.1, t.2⟩

theorem toFibre_surjective (y : Y) : Function.Surjective (toFibre f y) := by
  intro p
  induction p using Quotient.inductionOn with
  | h p =>
    obtain ⟨i⟩ := out_hom p.1
    exact ⟨⟨Quotient.mk _ p.1, f.map i ≫ p.2⟩, Quotient.sound ⟨i, rfl⟩⟩

/-- [note: def:finite-groupoid] Fibres of a functor between finite groupoids are finite. -/
instance finite_fibre_of_fin [FinGroupoid X] [FinGroupoid Y] (y : Y) : Finite (Fibre f y) :=
  Finite.of_surjective _ (toFibre_surjective f y)

/-- Each class `[(x', α')]` in the fibre is hit `|Aut x'|` times by `toFibre`. -/
theorem card_toFibre_preimage [f.Faithful] [FinGroupoid X] [FinGroupoid Y] (y : Y)
    (p : FibrePair f y) :
    Nat.card {t // toFibre f y t = Quotient.mk _ p} = Nat.card (p.1 ⟶ p.1) := by
  let q0 : Pi0 X := Quotient.mk _ p.1
  obtain ⟨i⟩ := out_hom p.1
  rw [← card_hom_eq _ _ i]
  symm
  refine Nat.card_eq_of_bijective
    (fun β : Quotient.out q0 ⟶ p.1 => ⟨⟨q0, f.map β ≫ p.2⟩, Quotient.sound ⟨β, rfl⟩⟩) ⟨?_, ?_⟩
  · intro β β' h
    obtain ⟨-, h'⟩ := Sigma.mk.inj_iff.mp (congrArg Subtype.val h)
    exact f.map_injective ((cancel_mono p.2).1 (eq_of_heq h'))
  · rintro ⟨⟨qx, α⟩, ht⟩
    change Quotient.mk _ ⟨Quotient.out qx, α⟩ = Quotient.mk _ p at ht
    obtain ⟨γ, hγ⟩ : ∃ γ : Quotient.out qx ⟶ p.1, f.map γ ≫ p.2 = α := Quotient.exact ht
    have hq : qx = q0 := by
      rw [← Quotient.out_eq qx]
      exact Quotient.sound ⟨asIso γ⟩
    subst hq
    exact ⟨γ, by simp [hγ]⟩

/-- The pushforward of a function, as a sum over triples. -/
theorem pushVal_cst [f.Faithful] [FinGroupoid X] [FinGroupoid Y] (a : Sec (f ⋙ cst Y)) (y : Y) :
    haveI := Fintype.ofFinite (Pi0 X)
    haveI := fun qx : Pi0 X => Fintype.ofFinite (f.obj (Quotient.out qx) ⟶ y)
    pval f a y =
      ∑ t : (Σ qx : Pi0 X, (f.obj (Quotient.out qx) ⟶ y)),
        cval f a (Quotient.out t.1) / Nat.card (Quotient.out t.1 ⟶ Quotient.out t.1) := by
  classical
  let _ := Fintype.ofFinite (Pi0 X)
  let _ := fun qx : Pi0 X => Fintype.ofFinite (f.obj (Quotient.out qx) ⟶ y)
  let _ : ∀ y, Fintype (Fibre f y) := fun y => Fintype.ofFinite _
  unfold pval pushVal
  rw [← Fintype.sum_fiberwise (toFibre f y)]
  refine Finset.sum_congr rfl fun p _ => ?_
  induction p using Quotient.inductionOn with
  | h p =>
    have hconst : ∀ t : {t // toFibre f y t = Quotient.mk _ p},
        cval f a (Quotient.out t.1.1) / Nat.card (Quotient.out t.1.1 ⟶ Quotient.out t.1.1) =
          cval f a p.1 / Nat.card (p.1 ⟶ p.1) := by
      rintro ⟨⟨qx, α⟩, ht⟩
      change Quotient.mk _ ⟨Quotient.out qx, α⟩ = Quotient.mk _ p at ht
      obtain ⟨γ, -⟩ : ∃ γ : Quotient.out qx ⟶ p.1, f.map γ ≫ p.2 = α := Quotient.exact ht
      rw [cst_compat f a γ, card_aut_eq _ _ γ]
    rw [Finset.sum_congr rfl fun t _ => hconst t, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, card_toFibre_preimage, nsmul_eq_mul]
    change cval f a p.1 = _
    field_simp [card_aut_ne_zero p.1]

/-- [note: prop:adjoint] For faithful `f` between finite groupoids, `⟨f_! a, b⟩_Y = ⟨a, f^* b⟩_X`. -/
theorem ginner_push [f.Faithful] [FinGroupoid X] [FinGroupoid Y] (a : Sec (f ⋙ cst Y))
    (b : Sec (cst Y)) :
    ginner (pval f a) (bval b) = ginner (cval f a) (fun x => bval b (f.obj x)) := by
  classical
  let _ := Fintype.ofFinite (Pi0 X)
  let _ := Fintype.ofFinite (Pi0 Y)
  let _ : ∀ (u : Y) (v : Y), Fintype (u ⟶ v) := fun u v => Fintype.ofFinite _
  unfold ginner
  simp only [pushVal_cst, Fintype.sum_sigma, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun qx _ => ?_
  set x := Quotient.out qx
  let qy0 : Pi0 Y := Quotient.mk _ (f.obj x)
  rw [Finset.sum_eq_single qy0]
  · -- the class of `f x`
    obtain ⟨j⟩ := out_hom (f.obj x)
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
      ← card_hom_eq _ _ (Groupoid.inv j)]
    have hb : bval b (Quotient.out qy0) = bval b (f.obj x) := b.compat j
    rw [hb]
    have h1 := card_aut_ne_zero (Quotient.out qy0)
    rw [card_hom_eq _ _ (Groupoid.inv j)] at *
    field_simp
  · -- other classes contribute nothing
    intro qy _ hne
    have : IsEmpty (f.obj x ⟶ Quotient.out qy) := by
      refine ⟨fun α => hne ?_⟩
      rw [← Quotient.out_eq qy]
      exact Quotient.sound ⟨(asIso α).symm⟩
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

end

end GroupoidCorr
