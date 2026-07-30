import Submission.OddOrder.PF.Section02.ClassSupportProperties

/-!
# The global Dade support

This is the support block following Peterfalvi 2.4.  The global support is
the union of the first Dade supports indexed by `A`.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.MathlibSupport
open scoped Pointwise

universe u

variable {Γ : Type u} [Group Γ]

/-- The union of the first Dade supports indexed by `A`. -/
def Dade_support
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) : Set Γ :=
  {x | ∃ a ∈ A, x ∈ Dade_support1 ddA a}

/-- The identity does not belong to the global Dade support. -/
theorem not_support_Dade_1
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    (1 : Γ) ∉ Dade_support ddA := by
  rintro ⟨a, haA, hOne⟩
  change
    ∃ z ∈ ((DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ)),
      ∃ g ∈ G, g⁻¹ * z * g = 1 at hOne
  rcases hOne with ⟨z, hz, g, _hg, hconj⟩
  have hzOne : z = 1 := by
    calc
      z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [hconj]; simp
  rcases Set.mem_mul.mp hz with ⟨h, hh, b, hb, rfl⟩
  rw [Set.mem_singleton_iff] at hb
  subst b
  have haH : a ∈ DadeSignalizer ddA a := by
    have haInv : a = h⁻¹ := by
      calc
        a = 1 * a := by simp
        _ = (h⁻¹ * h) * a := by simp
        _ = h⁻¹ * (h * a) := by group
        _ = h⁻¹ := by rw [hzOne]; simp
    convert (DadeSignalizer ddA a).inv_mem hh using 1
  have haCL :
      a ∈ centralizerWithin L (Subgroup.zpowers a) := by
    refine ⟨ddA.1.1 haA, ?_⟩
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.refl a).zpow_left n).eq
  have hsd := Dade_sdprod ddA haA
  let C := centralizerWithin G (Subgroup.zpowers a)
  let aC : C := ⟨a, hsd.1 haH⟩
  have haCOne : aC = 1 :=
    Subgroup.disjoint_def.mp hsd.2.2.2.disjoint
      (show aC ∈ (DadeSignalizer ddA a).subgroupOf C from haH)
      (show aC ∈
        (centralizerWithin L (Subgroup.zpowers a)).subgroupOf C from haCL)
  have haOne : a = 1 := congrArg Subtype.val haCOne
  exact ddA.2.2.1 (haOne ▸ haA)

/-- The global Dade support is contained in `G`. -/
theorem Dade_support_sub
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    Dade_support ddA ⊆ (G : Set Γ) := by
  rintro x ⟨a, haA, hxa⟩
  apply classSupportWithin_subset (G := G) (S :=
    (DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ)) at hxa
  · exact hxa
  · rintro y ⟨h, hh, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst b
    exact G.mul_mem (Dade_signalizer_sub ddA a hh)
      (ddA.2.1 (ddA.1.1 haA))

/-- The ambient subgroup normalizes the global Dade support. -/
theorem Dade_support_norm
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    G ≤ Subgroup.normalizer (Dade_support ddA) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff'']
  intro x
  constructor
  · rintro ⟨a, haA, hxa⟩
    refine ⟨a, haA, ?_⟩
    exact (classSupportWithin_rightConj_iff
      (G := G) (S :=
        (DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ)) hg).2 hxa
  · rintro ⟨a, haA, hxa⟩
    refine ⟨a, haA, ?_⟩
    exact (classSupportWithin_rightConj_iff
      (G := G) (S :=
        (DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ)) hg).1 hxa

/-- The global Dade support is a normal subset of `G`. -/
theorem Dade_support_normal
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    Dade_support ddA ⊆ (G : Set Γ) ∧
      G ≤ Subgroup.normalizer (Dade_support ddA) :=
  ⟨Dade_support_sub ddA, Dade_support_norm ddA⟩

/-- The global Dade support is contained in the nonidentity elements of
`G`. -/
theorem Dade_support_subD1
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    Dade_support ddA ⊆ (G : Set Γ) \ ({1} : Set Γ) := by
  intro x hx
  refine ⟨Dade_support_sub ddA hx, ?_⟩
  intro hxOne
  rw [Set.mem_singleton_iff] at hxOne
  subst x
  exact not_support_Dade_1 ddA hx

end Submission.OddOrder.PF
