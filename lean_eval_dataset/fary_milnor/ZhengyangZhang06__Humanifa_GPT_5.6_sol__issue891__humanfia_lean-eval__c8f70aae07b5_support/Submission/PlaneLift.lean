import Submission.FramePath

open LeanEval.Geometry.FaryMilnorProblem
open Set
open scoped Real
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def frameScale (d : Space) (s : ℝ) : ℝ :=
  (1 - s) * ‖d‖ + s

@[simp] theorem frameScale_zero (d : Space) : frameScale d 0 = ‖d‖ := by
  simp [frameScale]

@[simp] theorem frameScale_one (d : Space) : frameScale d 1 = 1 := by
  simp [frameScale]

theorem frameScale_pos {d : Space} (hd : d ≠ 0) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 < frameScale d s := by
  have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  unfold frameScale
  rcases hs.2.eq_or_lt with rfl | hslt
  · norm_num
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr hslt) hnorm) hs.1

theorem norm_smul_normalizedDirection {d : Space} (hd : d ≠ 0) :
    ‖d‖ • normalizedDirection d = d := by
  rw [normalizedDirection, smul_smul]
  rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hd), one_smul]

noncomputable def framedPlaneUnknot (u d : Space) (R : ℝ → ℝ → Space)
    (t s : ℝ) : Space :=
  frameRotation u (normalizedDirection d) s
    (frameEmbedding u (normalizedDirection d) (frameScale d s) (R t s))

set_option maxHeartbeats 1000000 in
theorem contDiff_framedPlaneUnknot (u d : Space) {R : ℝ → ℝ → Space}
    (hR : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2)) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => framedPlaneUnknot u d R p.1 p.2) := by
  have hR0 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2 0) :=
    (spaceCoordinateCLM 0).contDiff.comp hR
  have hR1 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2 1) :=
    (spaceCoordinateCLM 1).contDiff.comp hR
  have hR2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2 2) :=
    (spaceCoordinateCLM 2).contDiff.comp hR
  have hscale : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => frameScale d p.2) := by
    unfold frameScale
    fun_prop
  have hleft : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2 0 • u) :=
    hR0.smul (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => u))
  have hmiddle : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      (frameScale d p.2 * R p.1 p.2 1) • normalizedDirection d) :=
    (hscale.mul hR1).smul
      (contDiff_const : ContDiff ℝ ⊤
        (fun _ : ℝ × ℝ => normalizedDirection d))
  have hright : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      R p.1 p.2 2 • frameNormal u (normalizedDirection d)) :=
    hR2.smul
      (contDiff_const : ContDiff ℝ ⊤
        (fun _ : ℝ × ℝ => frameNormal u (normalizedDirection d)))
  have hemb : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      frameEmbedding u (normalizedDirection d) (frameScale d p.2) (R p.1 p.2)) := by
    change ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      R p.1 p.2 0 • u +
        (frameScale d p.2 * R p.1 p.2 1) • normalizedDirection d +
          R p.1 p.2 2 • frameNormal u (normalizedDirection d))
    exact (hleft.add hmiddle).add hright
  have hpair : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      (frameEmbedding u (normalizedDirection d) (frameScale d p.2) (R p.1 p.2),
        p.2)) := hemb.prodMk contDiff_snd
  have hcomp := (contDiff_frameRotation u (normalizedDirection d)).comp hpair
  change ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
    frameRotation u (normalizedDirection d) p.2
      (frameEmbedding u (normalizedDirection d) (frameScale d p.2) (R p.1 p.2)))
  exact hcomp

theorem framedPlaneUnknot_zero {p : ℝ → Space} {u d : Space} (hd : d ≠ 0)
    (hplanar : ∀ t, p t 2 = 0) (R : ℝ → ℝ → Space)
    (hR0 : ∀ t, R t 0 = p t) (t : ℝ) :
    framedPlaneUnknot u d R t 0 = liftPlanarCurveAlong u p (fun _ => d) t := by
  rw [framedPlaneUnknot, frameRotation_zero, hR0]
  unfold frameEmbedding liftPlanarCurveAlong
  rw [frameScale_zero, hplanar, zero_smul, add_zero]
  have hscaled : (‖d‖ * p t 1) • normalizedDirection d = p t 1 • d := by
    rw [mul_comm, mul_smul, norm_smul_normalizedDirection hd]
  rw [hscaled]

theorem framedPlaneUnknot_one {u d : Space} (hu : ‖u‖ = 1) (hd : d ≠ 0)
    (hud : inner ℝ u d = 0) (R : ℝ → ℝ → Space)
    (hR1 : ∀ t, R t 1 = standardCircle t) (t : ℝ) :
    framedPlaneUnknot u d R t 1 = standardCircle t := by
  let e := normalizedDirection d
  have he : ‖e‖ = 1 := norm_normalizedDirection hd
  have hue : inner ℝ u e = 0 := by
    dsimp [e, normalizedDirection]
    rw [real_inner_smul_right, hud, mul_zero]
  rw [framedPlaneUnknot, hR1, frameScale_one]
  have hemb : frameEmbedding u e 1 (standardCircle t) =
      Real.cos t • u + Real.sin t • e := by
    ext i
    fin_cases i <;> simp [frameEmbedding, standardCircle, e]
  rw [hemb, frameRotation_add, frameRotation_smul, frameRotation_smul,
    frameRotation_end_left hu, frameRotation_end_right hu he hue]
  ext i
  fin_cases i <;> simp [standardCircle]

theorem isUnknotted_liftPlanarCurveAlong_of_planar
    {p : ℝ → Space} (hplanar : ∀ t, p t 2 = 0) (hp : IsUnknotted p)
    {u d : Space} (hu : ‖u‖ = 1) (hd : d ≠ 0) (hud : inner ℝ u d = 0) :
    IsUnknotted (liftPlanarCurveAlong u p (fun _ => d)) := by
  rcases hp with ⟨R, hRsmooth, hR0, hR1, hRknot⟩
  refine ⟨framedPlaneUnknot u d R,
    contDiff_framedPlaneUnknot u d hRsmooth, ?_, ?_, ?_⟩
  · exact framedPlaneUnknot_zero hd hplanar R hR0
  · exact framedPlaneUnknot_one hu hd hud R hR1
  · intro s hs
    let e := normalizedDirection d
    have he : ‖e‖ = 1 := norm_normalizedDirection hd
    have hue : inner ℝ u e = 0 := by
      dsimp [e, normalizedDirection]
      rw [real_inner_smul_right, hud, mul_zero]
    have hbase : IsSmoothKnot (fun t =>
        frameEmbedding u e (frameScale d s) (R t s)) :=
      isSmoothKnot_frameEmbedding (hRknot s hs) hu he hue
        (ne_of_gt (frameScale_pos hd hs))
    have hrot := isSmoothKnot_frameRotation (d := e) hbase hu s
    simpa [framedPlaneUnknot, e] using hrot

end Submission.Helpers
