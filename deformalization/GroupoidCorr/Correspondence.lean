import GroupoidCorr.BaseChange
import GroupoidCorr.Functoriality

/-!
# Correspondences and their composition

Mirrors `note/note.tex`, Section 3 (`def:correspondence`, `prop:composition`).

A correspondence from `(X, F)` to `(X', F')` with apex groupoid `C` (a parameter here) consists of
legs `src : C ⥤ X`, `tgt : C ⥤ X'` with `tgt` faithful and with finite fibres, and a kernel
`K : src^* F ⟶ tgt^* F'`. Its operator is `tgt_! ∘ K ∘ src^*`. Two correspondences compose
through the 2-fibre product `Comma tgt₁ src₂` of their apexes.
-/

open CategoryTheory

namespace GroupoidCorr

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ w

variable {R : Type w} [CommRing R]

/-- [note: def:correspondence] A correspondence from `(X, F)` to `(X', F')` with apex `C`. -/
structure Corr {X : Type u₁} [Groupoid.{v₁} X] {X' : Type u₂} [Groupoid.{v₂} X']
    (F : LocalSystem R X) (F' : LocalSystem R X') (C : Type u₀) [Groupoid.{v₀} C] where
  /-- the source leg -/
  src : C ⥤ X
  /-- the target leg -/
  tgt : C ⥤ X'
  /-- the target leg is faithful -/
  faithful : tgt.Faithful
  /-- the fibres of the target leg are finite -/
  finite : ∀ x', Finite (Fibre tgt x')
  /-- the kernel, from `src^* F` to `tgt^* F'` -/
  K : src ⋙ F ⟶ tgt ⋙ F'

namespace Corr

variable {X : Type u₁} [Groupoid.{v₁} X] {X' : Type u₂} [Groupoid.{v₂} X']
  {X'' : Type u₃} [Groupoid.{v₃} X'']
  {F : LocalSystem R X} {F' : LocalSystem R X'} {F'' : LocalSystem R X''}
  {C₁ : Type u₀} [Groupoid.{v₀} C₁] {C₂ : Type u₄} [Groupoid.{v₄} C₂]

/-- [note: def:correspondence] The operator `T_C = tgt_! ∘ K ∘ src^*` on sections. -/
noncomputable def op {C : Type u₀} [Groupoid.{v₀} C] (T : Corr F F' C) (s : Sec F) : Sec F' :=
  haveI := T.finite
  push T.tgt F' (Sec.map T.K (Sec.pull T.src s))

/-- [note: def:fibre-product] The second projection of `Comma f g` is faithful when `f` is. -/
theorem snd_faithful {Y : Type u₂} [Groupoid.{v₂} Y] {A : Type u₁} [Groupoid.{v₁} A]
    {B : Type u₃} [Groupoid.{v₃} B] (f : A ⥤ Y) (g : B ⥤ Y) [f.Faithful] :
    (Comma.snd f g).Faithful where
  map_injective {a b} e e' he := by
    have hr : e.right = e'.right := he
    have hl : f.map e.left = f.map e'.left := by
      have h1 := e.w
      have h2 := e'.w
      rw [hr] at h1
      exact (cancel_mono b.hom).1 (h1.trans h2.symm)
    exact CommaMorphism.ext (f.map_injective hl) hr

/-- The composite kernel on the 2-fibre product: at `(c₁, c₂, γ)` it is
`K₂(c₂) ∘ F'(γ) ∘ K₁(c₁)`. -/
def compKernel (T₁ : Corr F F' C₁) (T₂ : Corr F' F'' C₂) :
    (Comma.fst T₁.tgt T₂.src ⋙ T₁.src) ⋙ F ⟶ (Comma.snd T₁.tgt T₂.src ⋙ T₂.tgt) ⋙ F'' where
  app a := T₁.K.app a.left ≫ F'.map a.hom ≫ T₂.K.app a.right
  naturality a b e := by
    have h1 := T₁.K.naturality e.left
    have h2 := T₂.K.naturality e.right
    have h3 : F'.map (T₁.tgt.map e.left) ≫ F'.map b.hom =
        F'.map a.hom ≫ F'.map (T₂.src.map e.right) := by
      rw [← F'.map_comp, ← F'.map_comp, e.w]
    dsimp at h1 h2 ⊢
    simp only [Category.assoc, Comma.fst_map, Comma.snd_map]
    rw [reassoc_of% h1, reassoc_of% h3, h2]

/-- [note: prop:composition] The composite correspondence on the 2-fibre product
`Comma tgt₁ src₂`, with legs `fst ⋙ src₁`, `snd ⋙ tgt₂` and the composite kernel. -/
noncomputable def comp (T₁ : Corr F F' C₁) (T₂ : Corr F' F'' C₂) :
    Corr F F'' (Comma T₁.tgt T₂.src) where
  src := Comma.fst T₁.tgt T₂.src ⋙ T₁.src
  tgt := Comma.snd T₁.tgt T₂.src ⋙ T₂.tgt
  faithful := by
    have := T₁.faithful; have := T₂.faithful; have := snd_faithful T₁.tgt T₂.src
    infer_instance
  finite := by
    have := T₁.finite; have := T₂.finite
    infer_instance
  K := compKernel T₁ T₂

/-- [note: prop:composition] The operator of the composite is the composite of the operators:
`T_{C₂} ∘ T_{C₁} = T_{C₂ ∘ C₁}`. -/
theorem op_comp (T₁ : Corr F F' C₁) (T₂ : Corr F' F'' C₂) (s : Sec F) :
    T₂.op (T₁.op s) = (T₁.comp T₂).op s := by
  have := T₁.finite; have := T₂.finite; have := T₂.faithful
  let u : Sec (T₁.tgt ⋙ F') := Sec.map T₁.K (Sec.pull T₁.src s)
  -- base change, then move `K₂` inside the pushforward along `snd`
  have hstep : Sec.map T₂.K (Sec.pull T₂.src (push T₁.tgt F' u)) =
      push (Comma.snd T₁.tgt T₂.src) (T₂.tgt ⋙ F'')
        (Sec.map (Functor.whiskerLeft (Comma.snd T₁.tgt T₂.src) T₂.K)
          (baseChangeSec T₁.tgt T₂.src F' u)) := by
    refine Sec.ext' fun c₂ => ?_
    change (T₂.K.app c₂).hom (pushVal T₁.tgt F' u (T₂.src.obj c₂)) = _
    rw [← pushVal_baseChange T₁.tgt T₂.src F' u c₂, pushVal_map]
    rfl
  refine Sec.ext' fun x'' => ?_
  change pushVal T₂.tgt F'' (Sec.map T₂.K (Sec.pull T₂.src (push T₁.tgt F' u))) x'' = _
  rw [hstep, ← pushVal_comp]
  rfl

end Corr

end GroupoidCorr
