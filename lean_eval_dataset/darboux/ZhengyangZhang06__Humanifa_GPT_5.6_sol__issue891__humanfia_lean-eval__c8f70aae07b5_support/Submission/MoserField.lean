import Submission.RadialPrimitive
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Compactness.Compact

open Set Function Matrix MeasureTheory Metric
open scoped ContDiff Interval

namespace Submission.MoserField

noncomputable section

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A two-form, curried as the continuous linear map `v ↦ ω(v, ·)`. -/
def flat (form : V [⋀^Fin 2]→L[ℝ] ℝ) : V →L[ℝ] (V →L[ℝ] ℝ) :=
  let uncurry : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  uncurry.comp form.curryLeft

omit [FiniteDimensional ℝ V] in
@[simp] theorem flat_apply (form : V [⋀^Fin 2]→L[ℝ] ℝ) (v w : V) :
    flat form v w = form ![v, w] := by
  exact Submission.RadialPrimitive.contract_apply form v w

/-- The contraction map, identified with an endomorphism by the real Riesz equivalence. -/
def rieszFlat (form : V [⋀^Fin 2]→L[ℝ] ℝ) : V →L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (flat form)

omit [FiniteDimensional ℝ V] in theorem flat_injective (form : V [⋀^Fin 2]→L[ℝ] ℝ)
    (hform : ∀ v, v ≠ 0 → ∃ w, form ![v, w] ≠ 0) : Function.Injective (flat form) := by
  intro v₁ v₂ h
  apply sub_eq_zero.mp
  by_contra hv
  obtain ⟨w, hw⟩ := hform (v₁ - v₂) hv
  apply hw
  rw [← flat_apply]
  rw [map_sub, h, sub_self]
  exact zero_apply w

theorem rieszFlat_injective (form : V [⋀^Fin 2]→L[ℝ] ℝ)
    (hform : ∀ v, v ≠ 0 → ∃ w, form ![v, w] ≠ 0) : Function.Injective (rieszFlat form) :=
  (InnerProductSpace.toDual ℝ V).symm.injective.comp (flat_injective form hform)

theorem rieszFlat_isUnit (form : V [⋀^Fin 2]→L[ℝ] ℝ)
    (hform : ∀ v, v ≠ 0 → ∃ w, form ![v, w] ≠ 0) : IsUnit (rieszFlat form) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hinj := rieszFlat_injective form hform
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

theorem flat_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (form : X → V [⋀^Fin 2]→L[ℝ] ℝ) (hform : ContDiff ℝ ∞ form) :
    ContDiff ℝ ∞ fun x => flat (form x) := by
  rw [contDiff_clm_apply_iff]
  intro v
  exact Submission.RadialPrimitive.contract_contDiff hform contDiff_const

theorem rieszFlat_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (form : X → V [⋀^Fin 2]→L[ℝ] ℝ) (hform : ContDiff ℝ ∞ form) :
    ContDiff ℝ ∞ fun x => rieszFlat (form x) := by
  rw [contDiff_clm_apply_iff]
  intro v
  unfold rieszFlat
  exact (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.contDiff.comp
    ((flat_contDiff form hform).clm_apply contDiff_const)

/-- The affine path `ω₀ + t(ω₁ - ω₀)`, with `δ = ω₁ - ω₀`. -/
def formPath (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (p : ℝ × V) : V [⋀^Fin 2]→L[ℝ] ℝ :=
  ω₀ + p.1 • δ p.2

omit [FiniteDimensional ℝ V] in theorem formPath_contDiff (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ) :
    ContDiff ℝ ∞ (formPath ω₀ δ) := by
  unfold formPath
  fun_prop

omit [FiniteDimensional ℝ V] in
@[simp] theorem formPath_zero (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ0 : δ 0 = 0) (t : ℝ) :
    formPath ω₀ δ (t, 0) = ω₀ := by
  simp [formPath, hδ0]

def endPath (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (p : ℝ × V) : V →L[ℝ] V :=
  rieszFlat (formPath ω₀ δ p)

theorem endPath_contDiff (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ) :
    ContDiff ℝ ∞ (endPath ω₀ δ) :=
  rieszFlat_contDiff (formPath ω₀ δ) (formPath_contDiff ω₀ δ hδ)

def invertibleLocus (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) : Set (ℝ × V) :=
  {p | IsUnit (endPath ω₀ δ p)}

theorem isOpen_invertibleLocus (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ) :
    IsOpen (invertibleLocus ω₀ δ) :=
  Units.isOpen.preimage (endPath_contDiff ω₀ δ hδ).continuous

theorem exists_open_prod_invertible (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (hω₀ : ∀ v, v ≠ 0 → ∃ w, ω₀ ![v, w] ≠ 0)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ) (hδ0 : δ 0 = 0) :
    ∃ T : Set ℝ, ∃ Z : Set V,
      IsOpen T ∧ IsOpen Z ∧ Icc (0 : ℝ) 1 ⊆ T ∧ 0 ∈ Z ∧
        T ×ˢ Z ⊆ invertibleLocus ω₀ δ := by
  have haxis : Icc (0 : ℝ) 1 ×ˢ ({0} : Set V) ⊆ invertibleLocus ω₀ δ := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    simp only [mem_singleton_iff] at hz
    subst z
    change IsUnit (rieszFlat (formPath ω₀ δ (t, 0)))
    rw [formPath_zero ω₀ δ hδ0]
    exact rieszFlat_isUnit ω₀ hω₀
  obtain ⟨T, Z, hT, hZ, hIT, h0Z, hTZ⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton
      (isOpen_invertibleLocus ω₀ δ hδ) haxis
  exact ⟨T, Z, hT, hZ, hIT, h0Z (mem_singleton 0), hTZ⟩

/-- The time-dependent Moser field solving `ι_X ω_t = -β`. -/
def moserField (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (p : ℝ × V) : V :=
  Ring.inverse (endPath ω₀ δ p)
    ((InnerProductSpace.toDual ℝ V).symm (-Submission.RadialPrimitive.radialPrimitive δ p.2))

@[simp]
theorem moserField_zero (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (t : ℝ) :
    moserField ω₀ δ (t, 0) = 0 := by
  simp [moserField]

theorem moserField_contDiffOn (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ) :
    ContDiffOn ℝ ∞ (moserField ω₀ δ) (invertibleLocus ω₀ δ) := by
  intro p hp
  have hEnd := endPath_contDiff ω₀ δ hδ
  rcases hp with ⟨a, ha⟩
  have hinv : ContDiffAt ℝ ∞
      (fun q => Ring.inverse (endPath ω₀ δ q)) p := by
    have hbase : ContDiffAt ℝ ∞ Ring.inverse (endPath ω₀ δ p) := by
      rw [← ha]
      exact contDiffAt_ringInverse ℝ a
    exact hbase.comp p hEnd.contDiffAt
  have hrhs : ContDiff ℝ ∞ fun q : ℝ × V =>
      (InnerProductSpace.toDual ℝ V).symm
        (-Submission.RadialPrimitive.radialPrimitive δ q.2) := by
    exact (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.contDiff.comp
      ((Submission.RadialPrimitive.radialPrimitive_contDiff δ hδ).comp contDiff_snd).neg
  exact (hinv.clm_apply hrhs.contDiffAt).contDiffWithinAt

theorem moserField_equation (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (p : ℝ × V)
    (hp : p ∈ invertibleLocus ω₀ δ) :
    flat (formPath ω₀ δ p) (moserField ω₀ δ p) =
      -Submission.RadialPrimitive.radialPrimitive δ p.2 := by
  change IsUnit (endPath ω₀ δ p) at hp
  have hsolve : endPath ω₀ δ p (moserField ω₀ δ p) =
      (InnerProductSpace.toDual ℝ V).symm
        (-Submission.RadialPrimitive.radialPrimitive δ p.2) := by
    unfold moserField
    have hmul := Ring.mul_inverse_cancel (endPath ω₀ δ p) hp
    have happ := congrArg (fun f : V →L[ℝ] V =>
      f ((InnerProductSpace.toDual ℝ V).symm
        (-Submission.RadialPrimitive.radialPrimitive δ p.2))) hmul
    simpa using happ
  apply (InnerProductSpace.toDual ℝ V).symm.injective
  change rieszFlat (formPath ω₀ δ p) (moserField ω₀ δ p) = _
  exact hsolve

end

end Submission.MoserField
