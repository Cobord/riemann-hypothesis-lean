import Mathlib

/-!
# Local systems on groupoids and pushforward by summation over fibres

Mirrors `note/note.tex`, Section 2.

* `LocalSystem R X`   — functors from a groupoid to `R`-modules (`def:local-system`);
* `Sec F`             — compatible families of elements (`def:section`);
* `Fibre f y`         — isomorphism classes of pairs `(x, α : f x ⟶ y)` (`def:fibre`);
* `pushVal f F s y`   — the sum over the fibre of `F(α)(s x)` (`def:pushforward`);
* `push f F s`        — the same, as a section of `F` (`prop:push-section`).

Nothing here divides: pushforward is a finite sum with integer coefficients.
-/

open CategoryTheory

namespace GroupoidCorr

open scoped BigOperators

universe u v w

/-- [note: def:local-system] A local system of `R`-modules on a groupoid `X`. -/
abbrev LocalSystem (R : Type w) [CommRing R] (X : Type u) [Groupoid.{v} X] : Type _ :=
  X ⥤ ModuleCat.{w} R

variable {R : Type w} [CommRing R]

/-- [note: def:section] A section of a local system: a family of elements, compatible with
every morphism of the groupoid. -/
structure Sec {X : Type u} [Groupoid.{v} X] (F : LocalSystem R X) where
  /-- the value at each object -/
  val : ∀ x : X, F.obj x
  /-- compatibility with morphisms -/
  compat : ∀ {x y : X} (g : x ⟶ y), (F.map g).hom (val x) = val y

variable {X : Type u} [Groupoid.{v} X] {Y : Type u} [Groupoid.{v} Y]

/-- Pairs `(x, α)` with `α : f x ⟶ y`. -/
def FibrePair (f : X ⥤ Y) (y : Y) : Type _ := Σ x : X, (f.obj x ⟶ y)

/-- [note: def:fibre] Two pairs are identified when a morphism `β : x ⟶ x'` carries one to the
other: `f β ≫ α' = α`. -/
def fibreSetoid (f : X ⥤ Y) (y : Y) : Setoid (FibrePair f y) where
  r a b := ∃ β : a.1 ⟶ b.1, f.map β ≫ b.2 = a.2
  iseqv :=
    { refl := fun a => ⟨𝟙 _, by simp⟩
      symm := fun {a b} ⟨β, h⟩ => ⟨Groupoid.inv β, by
        rw [← h, ← Category.assoc, ← Functor.map_comp]
        simp⟩
      trans := fun {a b c} ⟨β, h⟩ ⟨γ, h'⟩ => ⟨β ≫ γ, by
        rw [Functor.map_comp, Category.assoc, h', h]⟩ }

/-- [note: def:fibre] The fibre of `f` over `y`: isomorphism classes of pairs `(x, α)`. -/
def Fibre (f : X ⥤ Y) (y : Y) : Type _ := Quotient (fibreSetoid f y)

/-- The summand `F(α)(s x)` attached to a pair `(x, α)`. -/
def summand (f : X ⥤ Y) (F : LocalSystem R Y) (s : Sec (f ⋙ F)) (y : Y)
    (p : FibrePair f y) : F.obj y :=
  (F.map p.2).hom (s.val p.1)

/-- [note: lem:summand-wd] The summand only depends on the isomorphism class of the pair. -/
theorem summand_wd (f : X ⥤ Y) (F : LocalSystem R Y) (s : Sec (f ⋙ F)) (y : Y)
    (a b : FibrePair f y) (hab : (fibreSetoid f y).r a b) :
    summand f F s y a = summand f F s y b := by
  obtain ⟨β, h⟩ := hab
  simp only [summand]
  rw [← s.compat β, ← h, Functor.map_comp]
  rfl

/-- [note: def:pushforward] Pushforward along `f`: the sum over the fibre of `F(α)(s x)`.
Requires the fibres to be finite. -/
noncomputable def pushVal (f : X ⥤ Y) [∀ y, Finite (Fibre f y)] (F : LocalSystem R Y)
    (s : Sec (f ⋙ F)) (y : Y) : F.obj y := by
  classical
  haveI : Fintype (Fibre f y) := Fintype.ofFinite _
  exact ∑ q : Fibre f y,
    Quotient.lift (s := fibreSetoid f y) (summand f F s y) (summand_wd f F s y) q

/-- [note: prop:push-section] The pushforward is compatible with the morphisms of `Y`.
Proof idea (note): post-composition with `g : y ⟶ y'` is a bijection between the fibres
over `y` and `y'`, and it carries summands to summands. -/
theorem pushVal_compat (f : X ⥤ Y) [∀ y, Finite (Fibre f y)] (F : LocalSystem R Y)
    (s : Sec (f ⋙ F)) {y y' : Y} (g : y ⟶ y') :
    (F.map g).hom (pushVal f F s y) = pushVal f F s y' := by
  sorry

/-- [note: prop:push-section] The pushforward as a section of `F`. -/
noncomputable def push (f : X ⥤ Y) [∀ y, Finite (Fibre f y)] (F : LocalSystem R Y)
    (s : Sec (f ⋙ F)) : Sec F where
  val := pushVal f F s
  compat := fun g => pushVal_compat f F s g

end GroupoidCorr
