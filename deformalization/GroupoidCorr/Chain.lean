import GroupoidCorr.Correspondence
import GroupoidCorr.Divisibility

/-!
# Orders add along chains of correspondences

Mirrors `note/note.tex`, Section 3 (`lem:corr-smul`, `def:corr-id`, `def:corr-chain`,
`thm:orders-add-corr`).

This lifts `thm:orders-add` from linear maps to kernels. Scaling a kernel by `c` scales the
operator by `c`, and composition multiplies the scalars. A chain of correspondences
is composed by iterated 2-fibre products, starting from the identity correspondence. If the
`i`-th kernel is `ϖ ^ rᵢ` times an integral one, the composite kernel is `ϖ ^ ∑ rᵢ` times the
composite of the integral kernels.

Apexes change along a chain, so chains use bundled correspondences `BCorr` whose apex is a field.
To stay in one universe, all groupoids here live in `Type u` with morphisms in `Type u`;
`Comma` preserves this.
-/

open CategoryTheory

namespace GroupoidCorr

open scoped BigOperators

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u w

variable {R : Type w} [CommRing R]

namespace Corr

section scalars

variable {X : Type u₁} [Groupoid.{v₁} X] {X' : Type u₂} [Groupoid.{v₂} X']
  {X'' : Type u₃} [Groupoid.{v₃} X'']
  {F : LocalSystem R X} {F' : LocalSystem R X'} {F'' : LocalSystem R X''}
  {C : Type u₀} [Groupoid.{v₀} C] {C₂ : Type u₄} [Groupoid.{v₄} C₂]

/-- [note: lem:corr-smul] The same correspondence with its kernel multiplied by `c`. -/
def smul (c : R) (T : Corr F F' C) : Corr F F' C :=
  { T with K := c • T.K }

/-- [note: lem:corr-smul] Scaling the kernel by `c` scales the operator by `c`. -/
theorem op_smul (c : R) (T : Corr F F' C) (s : Sec F) (x' : X') :
    ((T.smul c).op s).val x' = c • (T.op s).val x' := by
  classical
  have := T.finite
  let _ : ∀ y, Fintype (Fibre T.tgt y) := fun y => Fintype.ofFinite _
  change pushVal T.tgt F' _ x' = c • pushVal T.tgt F' _ x'
  unfold pushVal
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  induction q using Quotient.inductionOn with
  | h p =>
    change (F'.map p.2).hom (((c • T.K).app p.1).hom (s.val (T.src.obj p.1))) =
      c • (F'.map p.2).hom ((T.K.app p.1).hom (s.val (T.src.obj p.1)))
    rw [NatTrans.app_smul, ModuleCat.hom_smul, LinearMap.smul_apply, map_smul]

/-- [note: lem:corr-smul] Composition multiplies the scalars of the kernels. -/
theorem comp_smul (c d : R) (T₁ : Corr F F' C) (T₂ : Corr F' F'' C₂) :
    (T₁.smul c).comp (T₂.smul d) = (T₁.comp T₂).smul (c * d) := by
  unfold comp smul
  congr 1
  ext a
  simp only [compKernel, NatTrans.app_smul, Linear.smul_comp, Linear.comp_smul, smul_smul,
    mul_comm d c]

theorem smul_one (T : Corr F F' C) : T.smul 1 = T := by
  cases T
  simp [smul]

end scalars

section identity

variable {X : Type u₁} [Groupoid.{v₁} X]

instance subsingleton_fibre_id (x : X) : Subsingleton (Fibre (𝟭 X) x) := by
  constructor
  intro p p'
  induction p using Quotient.inductionOn with
  | h p =>
  induction p' using Quotient.inductionOn with
  | h p' =>
  exact Quotient.sound ⟨p.2 ≫ Groupoid.inv p'.2, by simp⟩

/-- [note: def:corr-id] The identity correspondence: apex `X`, both legs the identity, kernel
the identity. -/
def id (F : LocalSystem R X) : Corr F F X where
  src := 𝟭 X
  tgt := 𝟭 X
  faithful := inferInstance
  finite := fun _ => Finite.of_subsingleton
  K := 𝟙 _

/-- [note: def:corr-id] The operator of the identity correspondence is the identity. -/
theorem op_id (F : LocalSystem R X) (s : Sec F) : (Corr.id F).op s = s := by
  classical
  refine Sec.ext' fun x => ?_
  let _ : ∀ y, Fintype (Fibre (𝟭 X) y) := fun y => Fintype.ofFinite _
  change pushVal (𝟭 X) F _ x = s.val x
  unfold pushVal
  rw [Fintype.sum_subsingleton _ (Quotient.mk _ ⟨x, 𝟙 x⟩)]
  change (F.map (𝟙 x)).hom ((𝟙 F : F ⟶ F).app x |>.hom (s.val x)) = s.val x
  simp

end identity

end Corr

/-- A correspondence bundled with its apex. -/
structure BCorr {X : Type u} [Groupoid.{u} X] {X' : Type u} [Groupoid.{u} X']
    (F : LocalSystem R X) (F' : LocalSystem R X') where
  /-- the apex -/
  C : Type u
  /-- its groupoid structure -/
  [grp : Groupoid.{u} C]
  /-- the correspondence -/
  T : Corr F F' C

attribute [instance] BCorr.grp

namespace BCorr

variable {X : Type u} [Groupoid.{u} X] {X' : Type u} [Groupoid.{u} X']
  {X'' : Type u} [Groupoid.{u} X'']
  {F : LocalSystem R X} {F' : LocalSystem R X'} {F'' : LocalSystem R X''}

/-- The operator of a bundled correspondence. -/
noncomputable def op (B : BCorr F F') (s : Sec F) : Sec F' := B.T.op s

/-- Composition, through the 2-fibre product of the apexes. -/
noncomputable def comp (B₁ : BCorr F F') (B₂ : BCorr F' F'') : BCorr F F'' :=
  ⟨Comma B₁.T.tgt B₂.T.src, B₁.T.comp B₂.T⟩

/-- Scaling the kernel. -/
def smul (c : R) (B : BCorr F F') : BCorr F F' := ⟨B.C, B.T.smul c⟩

theorem comp_smul (c d : R) (B₁ : BCorr F F') (B₂ : BCorr F' F'') :
    (B₁.smul c).comp (B₂.smul d) = (B₁.comp B₂).smul (c * d) := by
  show (⟨Comma B₁.T.tgt B₂.T.src, (B₁.T.smul c).comp (B₂.T.smul d)⟩ : BCorr F F'') =
    ⟨Comma B₁.T.tgt B₂.T.src, (B₁.T.comp B₂.T).smul (c * d)⟩
  rw [Corr.comp_smul]
  rfl

theorem op_smul (c : R) (B : BCorr F F') (s : Sec F) (x' : X') :
    ((B.smul c).op s).val x' = c • (B.op s).val x' :=
  Corr.op_smul c B.T s x'

end BCorr

section chain

variable {X : ℕ → Type u} [∀ i, Groupoid.{u} (X i)] {F : ∀ i, LocalSystem R (X i)}

/-- [note: def:corr-chain] The composite `C_{n-1} ∘ ⋯ ∘ C_0` of a chain of correspondences
`C_i` from `(X i, F i)` to `(X (i+1), F (i+1))`. The empty composite is the identity
correspondence. -/
noncomputable def chain (T : ∀ i, BCorr (F i) (F (i + 1))) : ∀ n, BCorr (F 0) (F n)
  | 0 => ⟨X 0, Corr.id (F 0)⟩
  | n + 1 => (chain T n).comp (T n)

/-- [note: def:corr-chain] The operator of the empty chain is the identity. -/
theorem chain_op_zero (T : ∀ i, BCorr (F i) (F (i + 1))) (s : Sec (F 0)) :
    (chain T 0).op s = s :=
  Corr.op_id (F 0) s

/-- [note: def:corr-chain] The operator of a chain is the composite of the step operators. -/
theorem chain_op_succ (T : ∀ i, BCorr (F i) (F (i + 1))) (n : ℕ) (s : Sec (F 0)) :
    (chain T (n + 1)).op s = (T n).op ((chain T n).op s) :=
  (Corr.op_comp (chain T n).T (T n).T s).symm

theorem chain_smul (T : ∀ i, BCorr (F i) (F (i + 1))) (c : ℕ → R) (n : ℕ) :
    chain (fun i => (T i).smul (c i)) n = (chain T n).smul (∏ i ∈ Finset.range n, c i) := by
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.prod_empty]
    show (⟨X 0, Corr.id (F 0)⟩ : BCorr (F 0) (F 0)) = ⟨X 0, (Corr.id (F 0)).smul 1⟩
    rw [Corr.smul_one]
  | succ n ih =>
    rw [chain, ih, BCorr.comp_smul, Finset.prod_range_succ]
    rfl

/-- [note: thm:orders-add-corr] Orders add along a chain of correspondences: if the `i`-th
correspondence is the `i`-th integral one with kernel scaled by `ϖ ^ r i`, the composite of the
first `n` is the composite of the integral ones with kernel scaled by `ϖ ^ ∑_{i<n} r i`. -/
theorem chain_eq_pow_smul (T T' : ∀ i, BCorr (F i) (F (i + 1))) (ϖ : R) (r : ℕ → ℕ)
    (h : ∀ i, T i = (T' i).smul (ϖ ^ r i)) (n : ℕ) :
    chain T n = (chain T' n).smul (ϖ ^ ∑ i ∈ Finset.range n, r i) := by
  obtain rfl : T = fun i => (T' i).smul (ϖ ^ r i) := funext h
  rw [chain_smul, Finset.prod_pow_eq_pow_sum]

/-- [note: thm:orders-add-corr] Consequently the operator of the chain is `ϖ ^ ∑_{i<n} r i`
times the operator of the integral chain. -/
theorem chain_op_eq_pow_smul (T T' : ∀ i, BCorr (F i) (F (i + 1))) (ϖ : R) (r : ℕ → ℕ)
    (h : ∀ i, T i = (T' i).smul (ϖ ^ r i)) (n : ℕ) (s : Sec (F 0)) (x : X n) :
    ((chain T n).op s).val x = ϖ ^ (∑ i ∈ Finset.range n, r i) • ((chain T' n).op s).val x := by
  rw [chain_eq_pow_smul T T' ϖ r h n, BCorr.op_smul]

end chain

end GroupoidCorr
