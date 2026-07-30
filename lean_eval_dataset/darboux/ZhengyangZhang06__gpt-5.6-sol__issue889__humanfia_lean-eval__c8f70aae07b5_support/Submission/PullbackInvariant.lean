import Submission.MoserDiffeomorph
import Mathlib.Analysis.Calculus.DifferentialForm.VectorField

open Set Function Matrix Metric Filter
open scoped ContDiff NNReal Topology

namespace Submission.PullbackInvariant

noncomputable section

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in theorem fderiv_formPath_contract
    (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ)
    (X : V → V) (hX : ContDiff ℝ ∞ X) (t : ℝ) (q a w : V) :
    fderiv ℝ (fun z => Submission.MoserField.formPath ω₀ δ (t, z) ![X z, w]) q a =
      t * fderiv ℝ δ q a ![X q, w] +
        Submission.MoserField.formPath ω₀ δ (t, q) ![fderiv ℝ X q a, w] := by
  let form : V → V [⋀^Fin 2]→L[ℝ] ℝ := fun z =>
    Submission.MoserField.formPath ω₀ δ (t, z)
  let args : Fin 2 → V → V := fun i z => ![X z, w] i
  have hform : DifferentiableAt ℝ form q := by
    exact (Submission.MoserField.formPath_contDiff ω₀ δ hδ).differentiable
      (by simp) (t, q) |>.comp q (hasFDerivAt_prodMk_right t q).differentiableAt
  have hargs : ∀ i, DifferentiableAt ℝ (args i) q := by
    intro i
    fin_cases i
    · change DifferentiableAt ℝ X q
      exact hX.differentiable (by simp) q
    · change DifferentiableAt ℝ (fun _ : V => w) q
      exact differentiableAt_const (c := w)
  rw [fderiv_continuousAlternatingMap_apply_apply hform hargs a]
  have hformDeriv : fderiv ℝ form q = t • fderiv ℝ δ q := by
    have hδq := (hδ.differentiable (by simp) q).hasFDerivAt.const_smul t
    have hsum := hδq.const_add ω₀
    exact hsum.fderiv
  rw [hformDeriv]
  simp only [Fin.sum_univ_two]
  have hargs0 : fderiv ℝ (args 0) q = fderiv ℝ X q := by
    congr
  have hargs1 : fderiv ℝ (args 1) q = 0 := by
    change fderiv ℝ (fun _ : V => w) q = 0
    exact (hasFDerivAt_const (𝕜 := ℝ) w q).fderiv
  rw [hargs0, hargs1]
  simp [form, args]
  have hupdate :
      Function.update (fun i : Fin 2 => ![X q, w] i) 0 (fderiv ℝ X q a) =
        ![fderiv ℝ X q a, w] := by
    funext i
    fin_cases i <;> simp
  exact congrArg
    (fun v : Fin 2 → V => Submission.MoserField.formPath ω₀ δ (t, q) v) hupdate

theorem radialPrimitive_derivative_identity
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ)
    (q a b : V)
    (hclosed : ∀ s ∈ Icc (0 : ℝ) 1, extDeriv δ (s • q) = 0) :
    fderiv ℝ (fun z => Submission.RadialPrimitive.radialPrimitive δ z b) q a -
      fderiv ℝ (fun z => Submission.RadialPrimitive.radialPrimitive δ z a) q b =
        δ q ![a, b] := by
  have hd := Submission.RadialPrimitive.extDeriv_radialPrimitiveForm_apply_of_closed_segment
    δ hδ q a b hclosed
  rw [extDeriv_apply
    (((Submission.RadialPrimitive.radialPrimitiveForm_contDiff δ hδ).differentiable
      (by simp)) q) (![a, b])] at hd
  simp only [Fin.sum_univ_succ] at hd
  simp at hd
  have hremove : (1 : Fin 2).removeNth ![a, b] = ![a] := by
    funext i
    fin_cases i
    rfl
  rw [hremove] at hd
  exact hd

theorem moser_coordinate_identity
    (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ)
    (X : V → V) (hX : ContDiff ℝ ∞ X)
    (t : ℝ) (q a b : V)
    (hclosed : ∀ s ∈ Icc (0 : ℝ) 1, extDeriv δ (s • q) = 0)
    (heq : ∀ w : V,
      (fun z => Submission.MoserField.formPath ω₀ δ (t, z) ![X z, w]) =ᶠ[𝓝 q]
        fun z => -Submission.RadialPrimitive.radialPrimitive δ z w) :
    δ q ![a, b] + t * fderiv ℝ δ q (X q) ![a, b] +
        Submission.MoserField.formPath ω₀ δ (t, q) ![fderiv ℝ X q a, b] +
        Submission.MoserField.formPath ω₀ δ (t, q) ![a, fderiv ℝ X q b] = 0 := by
  have ha : fderiv ℝ
      (fun z => Submission.MoserField.formPath ω₀ δ (t, z) ![X z, b]) q =
        fderiv ℝ (fun z => -Submission.RadialPrimitive.radialPrimitive δ z b) q :=
    (heq b).fderiv_eq
  have hb : fderiv ℝ
      (fun z => Submission.MoserField.formPath ω₀ δ (t, z) ![X z, a]) q =
        fderiv ℝ (fun z => -Submission.RadialPrimitive.radialPrimitive δ z a) q :=
    (heq a).fderiv_eq
  have hprim : ContDiff ℝ ∞ (Submission.RadialPrimitive.radialPrimitive δ) :=
    Submission.RadialPrimitive.radialPrimitive_contDiff δ hδ
  have ha' : t * fderiv ℝ δ q a ![X q, b] +
      Submission.MoserField.formPath ω₀ δ (t, q) ![fderiv ℝ X q a, b] =
        -fderiv ℝ (fun z => Submission.RadialPrimitive.radialPrimitive δ z b) q a := by
    have happ := congrArg (fun D : V →L[ℝ] ℝ => D a) ha
    rw [fderiv_formPath_contract ω₀ δ hδ X hX t q a b] at happ
    have hright : fderiv ℝ
        (fun z => -Submission.RadialPrimitive.radialPrimitive δ z b) q a =
        -fderiv ℝ (fun z => Submission.RadialPrimitive.radialPrimitive δ z b) q a := by
      have hscalar : ContDiff ℝ ∞
          (fun z => Submission.RadialPrimitive.radialPrimitive δ z b) :=
        hprim.clm_apply contDiff_const
      have hderiv : fderiv ℝ
          (fun z => -Submission.RadialPrimitive.radialPrimitive δ z b) q =
            -fderiv ℝ (fun z => Submission.RadialPrimitive.radialPrimitive δ z b) q :=
        (hscalar.differentiable (by simp) q).hasFDerivAt.neg.fderiv
      exact congrArg (fun D : V →L[ℝ] ℝ => D a) hderiv
    exact happ.trans hright
  have hb' : t * fderiv ℝ δ q b ![X q, a] +
      Submission.MoserField.formPath ω₀ δ (t, q) ![fderiv ℝ X q b, a] =
        -fderiv ℝ (fun z => Submission.RadialPrimitive.radialPrimitive δ z a) q b := by
    have happ := congrArg (fun D : V →L[ℝ] ℝ => D b) hb
    rw [fderiv_formPath_contract ω₀ δ hδ X hX t q b a] at happ
    have hright : fderiv ℝ
        (fun z => -Submission.RadialPrimitive.radialPrimitive δ z a) q b =
        -fderiv ℝ (fun z => Submission.RadialPrimitive.radialPrimitive δ z a) q b := by
      have hscalar : ContDiff ℝ ∞
          (fun z => Submission.RadialPrimitive.radialPrimitive δ z a) :=
        hprim.clm_apply contDiff_const
      have hderiv : fderiv ℝ
          (fun z => -Submission.RadialPrimitive.radialPrimitive δ z a) q =
            -fderiv ℝ (fun z => Submission.RadialPrimitive.radialPrimitive δ z a) q :=
        (hscalar.differentiable (by simp) q).hasFDerivAt.neg.fderiv
      exact congrArg (fun D : V →L[ℝ] ℝ => D b) hderiv
    exact happ.trans hright
  have halt := (Submission.MoserField.formPath ω₀ δ (t, q)).map_swap
    (v := ![a, fderiv ℝ X q b]) (by decide : (0 : Fin 2) ≠ 1)
  have hswap : ![a, fderiv ℝ X q b] ∘ Equiv.swap (0 : Fin 2) 1 =
      ![fderiv ℝ X q b, a] := by
    funext i
    fin_cases i <;> rfl
  rw [hswap] at halt
  change Submission.MoserField.formPath ω₀ δ (t, q) ![fderiv ℝ X q b, a] =
      -Submission.MoserField.formPath ω₀ δ (t, q) ![a, fderiv ℝ X q b] at halt
  have halt' : Submission.MoserField.formPath ω₀ δ (t, q)
      ![a, fderiv ℝ X q b] =
        -Submission.MoserField.formPath ω₀ δ (t, q) ![fderiv ℝ X q b, a] := by
    calc
      _ = -(-Submission.MoserField.formPath ω₀ δ (t, q)
          ![a, fderiv ℝ X q b]) := by simp
      _ = -Submission.MoserField.formPath ω₀ δ (t, q)
          ![fderiv ℝ X q b, a] := by rw [← halt]
  rw [halt']
  have hclosedq : extDeriv δ q = 0 := by
    simpa using hclosed 1 (by constructor <;> norm_num)
  have hδclosed := Submission.RadialPrimitive.closed_fderiv_identity
    δ hδ q (X q) a b hclosedq
  have htδclosed :
      t * fderiv ℝ δ q a ![X q, b] - t * fderiv ℝ δ q b ![X q, a] =
        t * fderiv ℝ δ q (X q) ![a, b] := by
    calc
      _ = t * (fderiv ℝ δ q a ![X q, b] -
          fderiv ℝ δ q b ![X q, a]) := by ring
      _ = _ := by rw [hδclosed]
  have hβ := radialPrimitive_derivative_identity δ hδ q a b hclosed
  linarith [ha', hb', htδclosed, hβ]

end

end Submission.PullbackInvariant
