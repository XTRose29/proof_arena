import Submission.Cone

namespace Submission.Helpers

open Function Set
open MeasureTheory
open scoped ContDiff

noncomputable section

/-- Sphere-valued data on a nonempty compact subset of a strict linear
subspace extends sphere-valuedly over that subspace.  The codimension-one
case is the relative zero-avoidance lemma used below; allowing an arbitrary
strict subspace costs nothing extra.

The proof first extends the data vector-valuedly and smooths that extension.
The image of the strict subspace under the smooth map has Haar measure zero,
so a small translation makes the smoothed map nonvanishing there.  A bounded
Tietze correction, supported where this translated map is uniformly away
from zero, restores the prescribed values exactly. -/
theorem exists_sphere_extension_of_compact_subset_submodule (d : ℕ)
    (P : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hP : P ≠ ⊤)
    (s : Set (EuclideanSpace ℝ (Fin d))) (hs : IsCompact s)
    (hsP : s ⊆ (P : Set (EuclideanSpace ℝ (Fin d))))
    (h : C(s, Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :
    ∃ H : C(P, Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
      ∀ x : s, H ⟨x, hsP x.2⟩ = h x := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let hE : C(s, E) :=
    { toFun := fun x ↦ (h x : E)
      continuous_toFun := continuous_subtype_val.comp h.continuous }
  obtain ⟨F, hF⟩ :=
    hE.exists_extension hs.isClosed.isClosedEmbedding_subtypeVal
  obtain ⟨g, hg, hgclose, _hgsupport⟩ :=
    F.continuous.exists_contDiff_approx ⊤
      (continuous_const : Continuous fun _ : E ↦ (1 / 16 : ℝ))
      (fun _ ↦ by norm_num)
  have hgdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hPzero : volume (P : Set E) = 0 :=
    MeasureTheory.Measure.addHaar_submodule volume P hP
  have hImageZero : volume (g '' (P : Set E)) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      volume hgdiff.differentiableOn hPzero
  have hDense : Dense ((g '' (P : Set E))ᶜ) := by
    rw [dense_iff_closure_eq, closure_compl,
      MeasureTheory.Measure.interior_eq_empty_of_null hImageZero]
    simp
  obtain ⟨a, haImage, haBall⟩ := hDense.exists_mem_open
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : E) (1 / 16)))
    (Metric.nonempty_ball.mpr (by norm_num))
  have haNorm : ‖a‖ < 1 / 16 := by
    simpa [Metric.mem_ball, dist_zero_right] using haBall
  let v : E → E := fun x ↦ g x - a
  have hvCont : Continuous v := hg.continuous.sub continuous_const
  have hvP (x : P) : v x ≠ 0 := by
    intro hx
    apply haImage
    refine ⟨x, x.2, ?_⟩
    dsimp [v] at hx
    exact sub_eq_zero.mp hx
  have hvClose (x : s) : ‖v x - (h x : E)‖ < 1 / 8 := by
    calc
      ‖v x - (h x : E)‖ = ‖(g x - F x) - a‖ := by
        have hFx : F x = (h x : E) := DFunLike.congr_fun hF x
        change ‖(g x - a) - (h x : E)‖ = _
        rw [hFx]
        simp only [sub_sub]
        rw [add_comm a (h x : E)]
      _ ≤ ‖g x - F x‖ + ‖a‖ := norm_sub_le _ _
      _ < 1 / 16 + 1 / 16 := by
        gcongr
        simpa [dist_eq_norm] using hgclose x
      _ = 1 / 8 := by norm_num
  have hvNorm (x : s) : 1 / 2 < ‖v x‖ := by
    have hhNorm : ‖(h x : E)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp (h x).2
    have htriangle : 1 ≤ ‖(h x : E) - v x‖ + ‖v x‖ := by
      calc
        (1 : ℝ) = ‖(h x : E)‖ := hhNorm.symm
        _ = ‖((h x : E) - v x) + v x‖ := by
          congr 1
          abel
        _ ≤ ‖(h x : E) - v x‖ + ‖v x‖ := norm_add_le _ _
    have hclose' : ‖(h x : E) - v x‖ < 1 / 8 := by
      rw [norm_sub_rev]
      exact hvClose x
    linarith
  let correction : C(s, E) :=
    { toFun := fun x ↦ (h x : E) - v x
      continuous_toFun :=
        (continuous_subtype_val.comp h.continuous).sub
          (hvCont.comp continuous_subtype_val) }
  obtain ⟨C, hC⟩ :=
    correction.exists_extension hs.isClosed.isClosedEmbedding_subtypeVal
  have hCNorm (x : s) : ‖C x‖ < 1 / 4 := by
    have hCx : C x = correction x := DFunLike.congr_fun hC x
    rw [hCx]
    change ‖(h x : E) - v x‖ < 1 / 4
    rw [norm_sub_rev]
    exact (hvClose x).trans (by norm_num)
  let O : Set E := {x | 1 / 2 < ‖v x‖} ∩ {x | ‖C x‖ < 1 / 4}
  have hOOpen : IsOpen O :=
    (isOpen_lt continuous_const hvCont.norm).inter
      (isOpen_lt C.continuous.norm continuous_const)
  have hsO : s ⊆ O := fun x hx ↦
    ⟨hvNorm ⟨x, hx⟩, hCNorm ⟨x, hx⟩⟩
  have hdisjoint : Disjoint Oᶜ s :=
    disjoint_compl_left_iff_subset.mpr hsO
  obtain ⟨φ, hφ0, hφ1, hφrange⟩ :=
    exists_continuous_zero_one_of_isClosed hOOpen.isClosed_compl
      hs.isClosed hdisjoint
  let w : P → E := fun x ↦ v x + φ x • C x
  have hwCont : Continuous w := by
    exact (hvCont.comp continuous_subtype_val).add
      ((φ.continuous.comp continuous_subtype_val).smul
        (C.continuous.comp continuous_subtype_val))
  have hwNe (x : P) : w x ≠ 0 := by
    by_cases hxO : (x : E) ∈ O
    · intro hw
      have hφnonneg : 0 ≤ φ x := (hφrange x).1
      have hφle : φ x ≤ 1 := (hφrange x).2
      have hvLarge : 1 / 2 < ‖v x‖ := hxO.1
      have hCnorm : ‖C x‖ ≤ 1 / 4 := hxO.2.le
      have hvEq : v x = -φ x • C x := by
        dsimp [w] at hw
        calc
          v x = (v x + φ x • C x) - φ x • C x := by abel
          _ = -φ x • C x := by rw [hw, zero_sub, neg_smul]
      have hvLe : ‖v x‖ ≤ 1 / 4 := by
        rw [hvEq, norm_smul, Real.norm_eq_abs,
          abs_of_nonpos (neg_nonpos.mpr hφnonneg), neg_neg]
        calc
          φ x * ‖C x‖ ≤ 1 * ‖C x‖ :=
            mul_le_mul_of_nonneg_right hφle (norm_nonneg _)
          _ ≤ 1 / 4 := by simpa using hCnorm
      exact (not_le_of_gt hvLarge) (hvLe.trans (by norm_num))
    · have hφ0x : φ x = 0 := hφ0 hxO
      simpa [w, hφ0x] using hvP x
  let H : C(P, Metric.sphere (0 : E) 1) :=
    { toFun := fun x ↦ ⟨NormedSpace.normalize (w x), by
        rw [mem_sphere_zero_iff_norm]
        exact NormedSpace.norm_normalize (hwNe x)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        change Continuous (fun x ↦ ‖w x‖⁻¹ • w x)
        exact (hwCont.norm.inv₀ fun x ↦
          norm_ne_zero_iff.mpr (hwNe x)).smul hwCont }
  refine ⟨H, ?_⟩
  intro x
  apply Subtype.ext
  have hφx : φ x = 1 := hφ1 x.2
  have hCx : C x = correction x := DFunLike.congr_fun hC x
  have hwx : w ⟨x, hsP x.2⟩ = (h x : E) := by
    change v x + φ x • C x = (h x : E)
    rw [hφx, one_smul, hCx]
    dsimp [correction]
    abel
  change NormedSpace.normalize (w ⟨x, hsP x.2⟩) = (h x : E)
  rw [hwx]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (mem_sphere_zero_iff_norm.mp (h x).2)

end

end Submission.Helpers
