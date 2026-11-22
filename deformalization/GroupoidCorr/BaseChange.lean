import GroupoidCorr.Pushforward

/-!
# Base change for pushforward

Mirrors `note/note.tex`, Section 2 (`def:fibre-product`, `prop:base-change`).

For functors of groupoids `f : X ⥤ Y` and `g : Z ⥤ Y`, the 2-fibre product `X ×_Y Z` is
Mathlib's comma category `Comma f g`: objects are triples `(x, z, γ : f x ⟶ g z)`, morphisms
are pairs `(β, δ)` with `f β ≫ γ' = γ ≫ g δ`. Mathlib does not record that it is a groupoid
when `X` and `Z` are; we supply that by hand. The projections are `Comma.fst f g` (to `X`,
the note's `g'`) and `Comma.snd f g` (to `Z`, the note's `f'`).
-/

open CategoryTheory

namespace GroupoidCorr

universe u₁ v₁ u₂ v₂ u₃ v₃ w

variable {R : Type w} [CommRing R]
variable {X : Type u₁} [Groupoid.{v₁} X] {Y : Type u₂} [Groupoid.{v₂} Y]
  {Z : Type u₃} [Groupoid.{v₃} Z]

/-- Every morphism of the comma category of two functors out of groupoids is invertible. -/
theorem comma_isIso (f : X ⥤ Y) (g : Z ⥤ Y) {a b : Comma f g} (e : a ⟶ b) : IsIso e := by
  have h : e = (Comma.isoMk (asIso e.left) (asIso e.right) e.w).hom := by
    ext <;> rfl
  rw [h]
  infer_instance

/-- [note: def:fibre-product] The 2-fibre product `X ×_Y Z` of groupoids is a groupoid: it is
the comma category `Comma f g`, all of whose morphisms are invertible. -/
noncomputable instance commaGroupoid (f : X ⥤ Y) (g : Z ⥤ Y) : Groupoid (Comma f g) :=
  Groupoid.ofIsIso (comma_isIso f g)

/-- [note: prop:base-change] Part (1). The pullback `g'^* s` of a section of `f^* F`, read as a section of
`f'^* (g^* F)` through the 2-cell `γ : f x ⟶ g z`: its value at `(x, z, γ)` is `F(γ)(s x)`. -/
def baseChangeSec (f : X ⥤ Y) (g : Z ⥤ Y) (F : LocalSystem R Y) (s : Sec (f ⋙ F)) :
    Sec (Comma.snd f g ⋙ g ⋙ F) where
  val a := (F.map a.hom).hom (s.val a.left)
  compat {a b} e := by
    change (F.map (g.map e.right)).hom ((F.map a.hom).hom (s.val a.left)) =
      (F.map b.hom).hom (s.val b.left)
    rw [← s.compat e.left]
    change _ = (F.map b.hom).hom ((F.map (f.map e.left)).hom (s.val a.left))
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← F.map_comp, ← F.map_comp, e.w]

/-- The map of fibres `[(a, δ)] ↦ [(a.left, a.hom ≫ g δ)]`, on pairs. -/
def bcPair (f : X ⥤ Y) (g : Z ⥤ Y) (z : Z) (p : FibrePair (Comma.snd f g) z) :
    FibrePair f (g.obj z) :=
  ⟨p.1.left, p.1.hom ≫ g.map p.2⟩

/-- The inverse map `[(x, α)] ↦ [((x, z, α), 𝟙 z)]`, on pairs. -/
def bcPairInv (f : X ⥤ Y) (g : Z ⥤ Y) (z : Z) (p : FibrePair f (g.obj z)) :
    FibrePair (Comma.snd f g) z :=
  ⟨⟨p.1, z, p.2⟩, 𝟙 z⟩

theorem bcPair_rel (f : X ⥤ Y) (g : Z ⥤ Y) (z : Z) (a b : FibrePair (Comma.snd f g) z)
    (hab : (fibreSetoid (Comma.snd f g) z).r a b) :
    (fibreSetoid f (g.obj z)).r (bcPair f g z a) (bcPair f g z b) := by
  obtain ⟨e, h⟩ := hab
  refine ⟨e.left, ?_⟩
  change f.map e.left ≫ b.1.hom ≫ g.map b.2 = a.1.hom ≫ g.map a.2
  rw [← Category.assoc, e.w, Category.assoc, ← g.map_comp]
  congr 2

theorem bcPairInv_rel (f : X ⥤ Y) (g : Z ⥤ Y) (z : Z) (a b : FibrePair f (g.obj z))
    (hab : (fibreSetoid f (g.obj z)).r a b) :
    (fibreSetoid (Comma.snd f g) z).r (bcPairInv f g z a) (bcPairInv f g z b) := by
  obtain ⟨β, h⟩ := hab
  let e : (bcPairInv f g z a).1 ⟶ (bcPairInv f g z b).1 :=
    { left := β
      right := 𝟙 z
      w := by simp [bcPairInv, h] }
  refine ⟨e, ?_⟩
  change (𝟙 z : z ⟶ z) ≫ 𝟙 z = 𝟙 z
  simp

/-- [note: prop:base-change] Part (2). The fibre of `f' : X ×_Y Z → Z` over `z` is in bijection with the
fibre of `f` over `g z`. -/
noncomputable def bcFibreEquiv (f : X ⥤ Y) (g : Z ⥤ Y) (z : Z) :
    Fibre (Comma.snd f g) z ≃ Fibre f (g.obj z) where
  toFun := Quotient.map (bcPair f g z) (bcPair_rel f g z)
  invFun := Quotient.map (bcPairInv f g z) (bcPairInv_rel f g z)
  left_inv := fun q => by
    induction q using Quotient.inductionOn with
    | h p =>
      show Quotient.mk _ (bcPairInv f g z (bcPair f g z p)) = Quotient.mk _ p
      let e : (bcPairInv f g z (bcPair f g z p)).1 ⟶ p.1 :=
        { left := 𝟙 _
          right := Groupoid.inv p.2
          w := by
            simp only [bcPair, bcPairInv, Category.assoc, ← g.map_comp, Groupoid.comp_inv]
            erw [f.map_id, g.map_id, Category.id_comp, Category.comp_id] }
      refine Quotient.sound ⟨e, ?_⟩
      change Groupoid.inv p.2 ≫ p.2 = 𝟙 z
      exact Groupoid.inv_comp _
  right_inv := fun q => by
    induction q using Quotient.inductionOn with
    | h p =>
      show Quotient.mk _ (bcPair f g z (bcPairInv f g z p)) = Quotient.mk _ p
      simp [bcPair, bcPairInv]
      rfl

instance finite_fibre_snd (f : X ⥤ Y) (g : Z ⥤ Y) [∀ y, Finite (Fibre f y)] (z : Z) :
    Finite (Fibre (Comma.snd f g) z) :=
  Finite.of_equiv _ (bcFibreEquiv f g z).symm

/-- The bijection of fibres carries summands to summands. -/
theorem summand_bcPair (f : X ⥤ Y) (g : Z ⥤ Y) (F : LocalSystem R Y) (s : Sec (f ⋙ F)) (z : Z)
    (p : FibrePair (Comma.snd f g) z) :
    summand (Comma.snd f g) (g ⋙ F) (baseChangeSec f g F s) z p =
      summand f F s (g.obj z) (bcPair f g z p) := by
  change (F.map (g.map p.2)).hom ((F.map p.1.hom).hom (s.val p.1.left)) =
    (F.map (p.1.hom ≫ g.map p.2)).hom (s.val p.1.left)
  rw [F.map_comp, ModuleCat.comp_apply]

/-- [note: prop:base-change] Part (3). Base change: `g^* f_! = f'_! g'^*`. For every `z : Z`, the
pushforward along `f' : X ×_Y Z → Z` of the base-changed section, evaluated at `z`, is the
pushforward along `f` of `s`, evaluated at `g z`. -/
theorem pushVal_baseChange (f : X ⥤ Y) (g : Z ⥤ Y) [∀ y, Finite (Fibre f y)]
    (F : LocalSystem R Y) (s : Sec (f ⋙ F)) (z : Z) :
    pushVal (Comma.snd f g) (g ⋙ F) (baseChangeSec f g F s) z = pushVal f F s (g.obj z) := by
  classical
  let _ : ∀ y, Fintype (Fibre f y) := fun y => Fintype.ofFinite _
  let _ : ∀ z, Fintype (Fibre (Comma.snd f g) z) := fun z => Fintype.ofFinite _
  unfold pushVal
  refine Fintype.sum_equiv (bcFibreEquiv f g z) _ _ fun q => ?_
  induction q using Quotient.inductionOn with
  | h p => exact summand_bcPair f g F s z p

end GroupoidCorr
