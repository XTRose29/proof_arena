import Submission.OddOrder.PF.Section02.DadeGlobalSupport
import Submission.OddOrder.PF.Section02.DadeSupportTI
import Submission.OddOrder.PF.Section01.ClassFunction

/-!
# Peterfalvi Definition 2.5: the Dade map

The value on the global Dade support is obtained by choosing an index whose
first support contains the argument.  The choice need not be canonical:
Peterfalvi 2.4(b) shows that any two possible indices are conjugate in `L`,
so every class function on `L` gives the same value.  The map vanishes off
the global support.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical Pointwise

universe u v

variable {Γ : Type u} [Group Γ]

private noncomputable def dadeRepresentative
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : G)
    (hx : (x : Γ) ∈ Dade_support ddA) : Γ :=
  Classical.choose hx

private theorem dadeRepresentative_mem_A
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : G)
    (hx : (x : Γ) ∈ Dade_support ddA) :
    dadeRepresentative ddA x hx ∈ A :=
  (Classical.choose_spec hx).1

private theorem mem_support1_dadeRepresentative
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : G)
    (hx : (x : Γ) ∈ Dade_support ddA) :
    (x : Γ) ∈ Dade_support1 ddA (dadeRepresentative ddA x hx) :=
  (Classical.choose_spec hx).2

private noncomputable def dadeRepresentativeInL
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : G)
    (hx : (x : Γ) ∈ Dade_support ddA) : L :=
  ⟨dadeRepresentative ddA x hx,
    ddA.1.1 (dadeRepresentative_mem_A ddA x hx)⟩

private theorem classFunction_eq_of_support1_overlap
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    {a b z : Γ} (ha : a ∈ A) (hb : b ∈ A)
    (hza : z ∈ Dade_support1 ddA a)
    (hzb : z ∈ Dade_support1 ddA b) :
    alpha ⟨b, ddA.1.1 hb⟩ = alpha ⟨a, ddA.1.1 ha⟩ := by
  rcases Dade_support1_TI ddA ha hb ⟨z, hza, hzb⟩ with
    ⟨x, hxL, hba⟩
  let xL : L := ⟨x, hxL⟩
  let aL : L := ⟨a, ddA.1.1 ha⟩
  let bL : L := ⟨b, ddA.1.1 hb⟩
  have hbConj : bL = xL⁻¹ * aL * xL := by
    apply Subtype.ext
    exact hba
  calc
    alpha ⟨b, ddA.1.1 hb⟩ = alpha bL := rfl
    _ = alpha (xL⁻¹ * aL * xL) := congrArg alpha hbConj
    _ = alpha aL := by
      simpa using ClassFunction.conj_apply alpha xL⁻¹ aL
    _ = alpha ⟨a, ddA.1.1 ha⟩ := rfl

private noncomputable def dadeValue
    {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (x : G) : k :=
  if hx : (x : Γ) ∈ Dade_support ddA then
    alpha (dadeRepresentativeInL ddA x hx)
  else
    0

private theorem dadeValue_eq_of_mem
    {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (x : G) (hx : (x : Γ) ∈ Dade_support ddA) :
    dadeValue ddA alpha x =
      alpha (dadeRepresentativeInL ddA x hx) := by
  simp only [dadeValue, dif_pos hx]

private theorem dadeValue_eq_zero_of_not_mem
    {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (x : G) (hx : (x : Γ) ∉ Dade_support ddA) :
    dadeValue ddA alpha x = 0 := by
  simp only [dadeValue, dif_neg hx]

private theorem dadeValue_conj
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (x y : G) :
    dadeValue ddA alpha (x * y * x⁻¹) = dadeValue ddA alpha y := by
  have hmem :
      ((x * y * x⁻¹ : G) : Γ) ∈ Dade_support ddA ↔
        (y : Γ) ∈ Dade_support ddA := by
    have hnorm := Subgroup.mem_set_normalizer_iff.mp
      (Dade_support_norm ddA x.property) (y : Γ)
    simpa using hnorm.symm
  by_cases hy : (y : Γ) ∈ Dade_support ddA
  · have hxy : ((x * y * x⁻¹ : G) : Γ) ∈ Dade_support ddA :=
      hmem.mpr hy
    have hxyRep := mem_support1_dadeRepresentative ddA
      (x * y * x⁻¹) hxy
    have hyRep := mem_support1_dadeRepresentative ddA y hy
    have hyInLeft :
        (y : Γ) ∈ Dade_support1 ddA
          (dadeRepresentative ddA (x * y * x⁻¹) hxy) := by
      have hiff :
          ((x : Γ)⁻¹)⁻¹ * (y : Γ) * (x : Γ)⁻¹ ∈
              Dade_support1 ddA
                (dadeRepresentative ddA (x * y * x⁻¹) hxy) ↔
            (y : Γ) ∈ Dade_support1 ddA
              (dadeRepresentative ddA (x * y * x⁻¹) hxy) := by
        exact classSupportWithin_rightConj_iff
          (G := G)
          (S :=
            (DadeSignalizer ddA
                (dadeRepresentative ddA (x * y * x⁻¹) hxy) : Set Γ) *
              ({dadeRepresentative ddA (x * y * x⁻¹) hxy} : Set Γ))
          (x := (y : Γ)) (g := (x : Γ)⁻¹)
          (G.inv_mem x.property)
      apply hiff.mp
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using hxyRep
    calc
      dadeValue ddA alpha (x * y * x⁻¹) =
          alpha (dadeRepresentativeInL ddA (x * y * x⁻¹) hxy) :=
        dadeValue_eq_of_mem ddA alpha (x * y * x⁻¹) hxy
      _ = alpha (dadeRepresentativeInL ddA y hy) := by
        simpa [dadeRepresentativeInL] using
          (classFunction_eq_of_support1_overlap ddA alpha
            (dadeRepresentative_mem_A ddA y hy)
            (dadeRepresentative_mem_A ddA (x * y * x⁻¹) hxy)
            hyRep hyInLeft)
      _ = dadeValue ddA alpha y :=
        (dadeValue_eq_of_mem ddA alpha y hy).symm
  · have hxy : ((x * y * x⁻¹ : G) : Γ) ∉ Dade_support ddA :=
      fun h ↦ hy (hmem.mp h)
    rw [dadeValue_eq_zero_of_not_mem ddA alpha (x * y * x⁻¹) hxy,
      dadeValue_eq_zero_of_not_mem ddA alpha y hy]

/-- Peterfalvi Definition 2.5: extend a class function on `L` to `G` via
the global Dade support, with value zero off that support. -/
noncomputable def Dade
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) :
    ClassFunction L k →ₗ[k] ClassFunction G k where
  toFun alpha :=
    ⟨dadeValue ddA alpha, dadeValue_conj ddA alpha⟩
  map_add' alpha beta := by
    apply ClassFunction.ext
    intro x
    change dadeValue ddA (alpha + beta) x =
      dadeValue ddA alpha x + dadeValue ddA beta x
    by_cases hx : (x : Γ) ∈ Dade_support ddA <;>
      simp [dadeValue, hx]
  map_smul' c alpha := by
    apply ClassFunction.ext
    intro x
    change dadeValue ddA (c • alpha) x = c • dadeValue ddA alpha x
    by_cases hx : (x : Γ) ∈ Dade_support ddA <;>
      simp [dadeValue, hx]

/-- The Dade map evaluates on the first support over `a` as the original
class function evaluates at `a`. -/
theorem DadeE
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A)
    (alpha : ClassFunction L k) {a : Γ} (ha : a ∈ A)
    (u : G) (hu : (u : Γ) ∈ Dade_support1 ddA a) :
    Dade ddA alpha u = alpha ⟨a, ddA.1.1 ha⟩ := by
  change dadeValue ddA alpha u = alpha ⟨a, ddA.1.1 ha⟩
  have huGlobal : (u : Γ) ∈ Dade_support ddA := ⟨a, ha, hu⟩
  rw [dadeValue_eq_of_mem ddA alpha u huGlobal]
  simpa [dadeRepresentativeInL] using
    classFunction_eq_of_support1_overlap ddA alpha ha
      (dadeRepresentative_mem_A ddA u huGlobal) hu
      (mem_support1_dadeRepresentative ddA u huGlobal)

end

end Submission.OddOrder.PF
