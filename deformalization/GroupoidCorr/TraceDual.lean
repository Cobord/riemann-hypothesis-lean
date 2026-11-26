import Mathlib

/-!
# Trace duality

Mirrors `note/note.tex`, Section 9 (`lem:trace-dual`); this is Lemma 2.1 of the main account.

Setting: `A ⊆ K` and `B ⊆ L` (in the application `𝒪_{E⁺} ⊆ E⁺` and `𝒪_E ⊆ E`), with `L/K` finite
separable and `B` free over `A` on a basis that is also a `K`-basis of `L`. The inverse different
`𝔇⁻¹` is Mathlib's `Submodule.traceDual A K 1 = {y ∈ L | Tr(y B) ⊆ A}`.

For every `B`-module `M`, composition with the trace is a bijection between `B`-linear maps
`M → 𝔇⁻¹` and `A`-linear maps `M → A`. The case `M = B` is a dual-basis computation; the general
case reduces to it.
-/

open Algebra

namespace GroupoidCorr

open scoped BigOperators

variable (A K : Type*) {B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The inverse different `𝔇⁻¹ = {y ∈ L | Tr(y B) ⊆ A}`. -/
noncomputable abbrev invDiff : Submodule B L := Submodule.traceDual A K (1 : Submodule B L)

variable {A K}
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (bB : Module.Basis ι A B) (b : Module.Basis ι K L)
  (hbb : ∀ i, b i = algebraMap B L (bB i))
include hbb

/-- [note: lem:trace-dual] The case `M = B`: every `A`-linear `f : B → A` is `c ↦ Tr(y c)` for a
unique `y ∈ 𝔇⁻¹`. -/
theorem trace_dual_self (f : B →ₗ[A] A) :
    ∃! y : L, y ∈ invDiff A K (B := B) ∧
      ∀ c : B, Algebra.trace K L (y * algebraMap B L c) = algebraMap A K (f c) := by
  have nd := traceForm_nondegenerate K L
  set bd := (traceForm K L).dualBasis nd b
  set y : L := ∑ i, algebraMap A K (f (bB i)) • bd i with hydef
  -- `c ↦ Tr(y c)` and `c ↦ f c` agree on the basis, hence everywhere
  have key : ∀ c : B, Algebra.trace K L (y * algebraMap B L c) = algebraMap A K (f c) := by
    let g₁ : B →ₗ[A] K := ((traceForm K L y).restrictScalars A).comp
      (IsScalarTower.toAlgHom A B L).toLinearMap
    let g₂ : B →ₗ[A] K := (Algebra.linearMap A K).comp f
    have : g₁ = g₂ := by
      refine bB.ext fun j => ?_
      simp only [g₁, g₂, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', Algebra.linearMap_apply]
      rw [← hbb j, hydef, map_sum, LinearMap.sum_apply]
      simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
      simp only [bd, LinearMap.BilinForm.apply_dualBasis_left, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    intro c
    have := congrArg (fun g => g c) this
    simpa [g₁, g₂, traceForm_apply] using this
  refine ⟨y, ⟨?_, key⟩, ?_⟩
  · rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_one.mp ha
    rw [traceForm_apply, key]
    exact ⟨_, rfl⟩
  · rintro y' ⟨-, hy'⟩
    have hzero : ∀ z : L, traceForm K L (y' - y) z = 0 := by
      have : traceForm K L (y' - y) = 0 := b.ext fun j => by
        rw [map_sub, LinearMap.sub_apply, traceForm_apply, traceForm_apply, hbb j, hy', key,
          sub_self, LinearMap.zero_apply]
      intro z; rw [this, LinearMap.zero_apply]
    exact sub_eq_zero.mp (nd.1 _ hzero)

/-- [note: lem:trace-dual] Trace duality: for a `B`-module `M`, every `A`-linear `h : M → A` is
`Tr ∘ g` for a unique `B`-linear `g : M → L` with values in `𝔇⁻¹`. -/
theorem trace_dual {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (h : M →ₗ[A] A) :
    ∃! g : M →ₗ[B] L, (∀ m, g m ∈ invDiff A K (B := B)) ∧
      ∀ m, Algebra.trace K L (g m) = algebraMap A K (h m) := by
  -- the functional `c ↦ h(c • m)` and its dual element
  let fm : M → (B →ₗ[A] A) := fun m => h ∘ₗ (LinearMap.toSpanSingleton B M m).restrictScalars A
  have hfm : ∀ m c, fm m c = h (c • m) := fun m c => rfl
  choose y hy huniq using fun m => trace_dual_self bB b hbb (fm m)
  have ychar : ∀ m (z : L), z ∈ invDiff A K (B := B) →
      (∀ c : B, Algebra.trace K L (z * algebraMap B L c) = algebraMap A K (h (c • m))) →
      z = y m := fun m z hz hc => huniq m z ⟨hz, hc⟩
  let g : M →ₗ[B] L :=
    { toFun := y
      map_add' := fun m₁ m₂ => (ychar (m₁ + m₂) _ (Submodule.add_mem _ (hy m₁).1 (hy m₂).1)
          (fun c => by
            rw [add_mul, map_add, (hy m₁).2, (hy m₂).2, smul_add, map_add, map_add]; rfl)).symm
      map_smul' := fun a m => by
        refine (ychar (a • m) _ (Submodule.smul_mem _ a (hy m).1) (fun c => ?_)).symm
        rw [Algebra.smul_def, mul_assoc, mul_left_comm, ← map_mul, (hy m).2, hfm, smul_smul, mul_comm a c] }
  refine ⟨g, ⟨fun m => (hy m).1, fun m => ?_⟩, ?_⟩
  · have := (hy m).2 1
    rwa [map_one, mul_one, hfm, one_smul] at this
  · rintro g' ⟨hg'1, hg'2⟩
    ext m
    refine ychar m _ (hg'1 m) (fun c => ?_)
    rw [mul_comm, ← Algebra.smul_def, ← g'.map_smul, hg'2]

end GroupoidCorr
