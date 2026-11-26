module

public import GroupoidCorr.Pushforward

/-!
# Functoriality of pushforward

Mirrors `note/note.tex`, Section 2 (`def:pull-map`, `lem:push-natural`, `lem:push-comp`).

* `Sec.pull f s`  — pullback of a section along a functor;
* `Sec.map K s`   — a morphism of local systems applied to a section;
* `pushVal_map`   — pushforward commutes with morphisms of local systems;
* `pushVal_comp`  — `(k ⋙ h)_! = h_! k_!` when `h` is faithful.

Faithfulness of `h` is needed in `pushVal_comp`: for `k : pt → BG`, `h : BG → pt` and a constant
local system, `h_! k_!` is multiplication by `|G|` while `(k ⋙ h)_!` is the identity.
-/

@[expose] public section

open CategoryTheory

namespace GroupoidCorr

universe u₁ v₁ u₂ v₂ u₃ v₃ w

variable {R : Type w} [CommRing R]
variable {A : Type u₁} [Groupoid.{v₁} A] {B : Type u₂} [Groupoid.{v₂} B]
  {C : Type u₃} [Groupoid.{v₃} C]

theorem Sec.ext' {F : LocalSystem R A} {s t : Sec F} (h : ∀ a, s.val a = t.val a) : s = t := by
  cases s; cases t; congr; funext a; exact h a

/-- [note: def:pull-map] The pullback `f^* s` of a section along a functor. -/
def Sec.pull (f : A ⥤ B) {F : LocalSystem R B} (s : Sec F) : Sec (f ⋙ F) where
  val a := s.val (f.obj a)
  compat g := s.compat (f.map g)

/-- [note: def:pull-map] A morphism of local systems applied to a section. -/
def Sec.map {F G : LocalSystem R A} (K : F ⟶ G) (s : Sec F) : Sec G where
  val a := (K.app a).hom (s.val a)
  compat {a b} g := by
    rw [← s.compat g, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, K.naturality]

/-- [note: lem:push-natural] Pushforward commutes with morphisms of local systems:
`K ∘ k_! = k_! ∘ (k^* K)`. -/
theorem pushVal_map (k : A ⥤ B) [∀ b, Finite (Fibre k b)] {G G' : LocalSystem R B} (K : G ⟶ G')
    (s : Sec (k ⋙ G)) (b : B) :
    (K.app b).hom (pushVal k G s b) = pushVal k G' (Sec.map (Functor.whiskerLeft k K) s) b := by
  classical
  let _ : ∀ b, Fintype (Fibre k b) := fun b => Fintype.ofFinite _
  unfold pushVal
  refine (map_sum (K.app b).hom _ _).trans (Finset.sum_congr rfl fun q _ => ?_)
  induction q using Quotient.inductionOn with
  | h p =>
    change (K.app b).hom ((G.map p.2).hom (s.val p.1)) =
      (G'.map p.2).hom ((K.app (k.obj p.1)).hom (s.val p.1))
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, K.naturality]

section comp

variable (k : A ⥤ B) (h : B ⥤ C)

/-- On pairs: `(a, β) ↦ (a, h β ≫ α)`, where `(b, α)` is the chosen representative of `q`. -/
noncomputable def compPair (c : C) (q : Fibre h c) (p : FibrePair k (Quotient.out q).1) :
    FibrePair (k ⋙ h) c :=
  ⟨p.1, h.map p.2 ≫ (Quotient.out q).2⟩

theorem compPair_rel (c : C) (q : Fibre h c) (a b : FibrePair k (Quotient.out q).1)
    (hab : (fibreSetoid k _).r a b) :
    (fibreSetoid (k ⋙ h) c).r (compPair k h c q a) (compPair k h c q b) := by
  obtain ⟨γ, hγ⟩ := hab
  refine ⟨γ, ?_⟩
  change h.map (k.map γ) ≫ h.map b.2 ≫ _ = h.map a.2 ≫ _
  rw [← Category.assoc, ← h.map_comp, hγ]

/-- The map `(q, [(a, β)]) ↦ [(a, h β ≫ α)]`, where `(b, α)` is the chosen representative of
`q` in the fibre of `h` and `[(a, β)]` lies in the fibre of `k` over `b`. -/
noncomputable def compFibreMap (c : C) :
    (Σ q : Fibre h c, Fibre k (Quotient.out q).1) → Fibre (k ⋙ h) c :=
  fun x => Quotient.map (compPair k h c x.1) (compPair_rel k h c x.1) x.2

theorem compFibreMap_surjective (c : C) : Function.Surjective (compFibreMap k h c) := by
  intro p
  induction p using Quotient.inductionOn with
  | h p =>
    let q : Fibre h c := Quotient.mk (fibreSetoid h c) ⟨k.obj p.1, p.2⟩
    obtain ⟨β, hβ⟩ : (fibreSetoid h c).r ⟨k.obj p.1, p.2⟩ (Quotient.out q) :=
      Quotient.exact (Quotient.out_eq q).symm
    refine ⟨⟨q, Quotient.mk _ ⟨p.1, β⟩⟩, ?_⟩
    show Quotient.mk _ (compPair k h c q ⟨p.1, β⟩) = Quotient.mk _ p
    apply Quotient.sound
    refine ⟨𝟙 _, ?_⟩
    change h.map (k.map (𝟙 _)) ≫ p.2 = h.map β ≫ (Quotient.out q).2
    rw [hβ]; simp

theorem compFibreMap_injective [h.Faithful] (c : C) : Function.Injective (compFibreMap k h c) := by
  rintro ⟨q, r⟩ ⟨q', r'⟩ hqr
  induction r using Quotient.inductionOn with
  | h r =>
  induction r' using Quotient.inductionOn with
  | h r' =>
  change Quotient.mk _ (compPair k h c q r) = Quotient.mk _ (compPair k h c q' r') at hqr
  obtain ⟨γ, hγ⟩ : ∃ γ : r.1 ⟶ r'.1, h.map (k.map γ) ≫ h.map r'.2 ≫ (Quotient.out q').2 =
      h.map r.2 ≫ (Quotient.out q).2 := Quotient.exact hqr
  -- the two classes in the fibre of `h` agree
  have hq : q = q' := by
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    apply Quotient.sound
    refine ⟨Groupoid.inv r.2 ≫ k.map γ ≫ r'.2, ?_⟩
    simp only [Functor.map_comp, Category.assoc]
    rw [hγ, ← Category.assoc, ← Functor.map_comp, Groupoid.inv_comp, h.map_id,
      Category.id_comp]
  subst hq
  congr 1
  apply Quotient.sound
  refine ⟨γ, h.map_injective ?_⟩
  have h2 : (h.map (k.map γ) ≫ h.map r'.2) ≫ (Quotient.out q).2 =
      h.map r.2 ≫ (Quotient.out q).2 := by
    rw [Category.assoc]; exact hγ
  rw [h.map_comp]
  exact (cancel_mono _).1 h2

/-- Composite fibres are finite when the fibres of both factors are. -/
instance finite_fibre_comp [∀ b, Finite (Fibre k b)] [∀ c, Finite (Fibre h c)] (c : C) :
    Finite (Fibre (k ⋙ h) c) :=
  Finite.of_surjective _ (compFibreMap_surjective k h c)

/-- [note: lem:push-comp] Pushforward is functorial along a faithful second factor:
`(k ⋙ h)_! = h_! k_!`. -/
theorem pushVal_comp [h.Faithful] [∀ b, Finite (Fibre k b)] [∀ c, Finite (Fibre h c)]
    (F : LocalSystem R C) (s : Sec ((k ⋙ h) ⋙ F)) (c : C) :
    pushVal (k ⋙ h) F s c = pushVal h F (push k (h ⋙ F) s) c := by
  classical
  let _ : ∀ b, Fintype (Fibre k b) := fun b => Fintype.ofFinite _
  let _ : ∀ c, Fintype (Fibre h c) := fun c => Fintype.ofFinite _
  let _ : ∀ c, Fintype (Fibre (k ⋙ h) c) := fun c => Fintype.ofFinite _
  unfold pushVal
  rw [← Fintype.sum_bijective _ ⟨compFibreMap_injective k h c, compFibreMap_surjective k h c⟩
    (fun x => _) _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun q _ => ?_
  -- evaluate the outer summand at the chosen representative of `q`
  conv_rhs => rw [← Quotient.out_eq q]
  change _ = (F.map (Quotient.out q).2).hom (pushVal k (h ⋙ F) s (Quotient.out q).1)
  unfold pushVal
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  induction r using Quotient.inductionOn with
  | h r =>
    change (F.map (h.map r.2 ≫ (Quotient.out q).2)).hom (s.val r.1) =
      (F.map (Quotient.out q).2).hom ((F.map (h.map r.2)).hom (s.val r.1))
    rw [F.map_comp, ModuleCat.comp_apply]

end comp

end GroupoidCorr
