import Submission.SphereLocalLinearization
import Submission.SphereTransverse

open scoped ContDiff unitInterval Topology

noncomputable section

namespace Submission.SphereSingleton

open Set
open Submission.SphereRegularApprox

variable {m : ℕ}

private theorem matrixOfFDeriv_apply
    (f : Domain m → Domain m) (c v : Domain m) :
    let b := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
    let A := LinearMap.toMatrix b b
      (fderiv ℝ f c).toLinearMap
    A.toEuclideanLin v = fderiv ℝ f c v := by
  dsimp
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.toLin_toMatrix]
  rfl

private theorem matrixOfFDeriv_det
    (f : Domain m → Domain m) (c : Domain m) :
    let b := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
    let A := LinearMap.toMatrix b b
      (fderiv ℝ f c).toLinearMap
    A.det = (fderiv ℝ f c).det := by
  dsimp
  change
    (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
      (fderiv ℝ f c).toLinearMap).det =
      LinearMap.det (fderiv ℝ f c).toLinearMap
  exact LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis _

private theorem localCoordinates_mem_ambient_ball
    (d : SphereBubble.LocalDatum m)
    {t : Fin (m + 1) → I}
    (ht : ‖SphereBubble.localCoordinates d t‖ ≤ 1) :
    ‖cubeDomain m t - cubeDomain m d.center‖ ≤ d.scale := by
  rw [SphereBubble.norm_cubeDomain_sub_center]
  exact mul_le_of_le_one_right d.scale_pos.le ht

/-- A transverse singleton antipode fiber represents the canonical sphere
generator or its inverse. -/
theorem class_eq_or_eq_inverse_of_singleton_transverse
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (hfinite :
      {t | p t =
        -(SphereGenerator.canonicalBasepoint m)}.Finite)
    (hcard : hfinite.toFinset.card = 1)
    (hp : SphereTransverse.Transverse p) :
    (Quotient.mk' p :
        HomotopyGroup.Pi (m + 1) (UnitSphere m)
          (SphereGenerator.canonicalBasepoint m)) =
        SphereGenerator.canonicalGeneratorClass m ∨
      (Quotient.mk' p :
        HomotopyGroup.Pi (m + 1) (UnitSphere m)
          (SphereGenerator.canonicalBasepoint m)) =
        (SphereGenerator.canonicalGeneratorClass m)⁻¹ := by
  classical
  obtain ⟨t₀, hfiberFinset⟩ :=
    Finset.card_eq_one.mp hcard
  have ht₀mem : t₀ ∈ hfinite.toFinset := by
    rw [hfiberFinset]
    simp
  have ht₀ :
      p t₀ = -(SphereGenerator.canonicalBasepoint m) := by
    simpa using ht₀mem
  have ht₀unique :
      ∀ t, p t = -(SphereGenerator.canonicalBasepoint m) → t = t₀ := by
    intro t ht
    have htmem : t ∈ hfinite.toFinset := by
      simpa using ht
    rw [hfiberFinset] at htmem
    simpa using htmem
  obtain ⟨hregular⟩ := hp t₀ ht₀
  obtain ⟨F, hFdiff, hFnorm, hagree, hdet⟩ := hregular
  let ψ : Domain m → Domain m :=
    fun v => horizontal m (F v)
  let c : Domain m := cubeDomain m t₀
  have hagree₀ :
      (p t₀ : Target m) = F c :=
    hagree.self_of_nhds
  have hFc :
      F c =
        (-(SphereGenerator.canonicalBasepoint m) : UnitSphere m) := by
    rw [← hagree₀]
    exact congrArg Subtype.val ht₀
  have hψc : ψ c = 0 := by
    dsimp only [ψ]
    rw [hFc]
    exact SphereUpperChart.horizontal_antipode
  have hvertc : vertical m (F c) = 1 := by
    rw [hFc]
    simp [vertical, coe_canonicalBasepoint]
  have hψdiff : ContDiff ℝ ∞ ψ :=
    (contDiff_horizontal m).comp hFdiff
  let b := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
  let A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    LinearMap.toMatrix b b (fderiv ℝ ψ c).toLinearMap
  have hAapply : ∀ v, A.toEuclideanLin v = fderiv ℝ ψ c v :=
    matrixOfFDeriv_apply ψ c
  have hA : A.det ≠ 0 := by
    rw [matrixOfFDeriv_det ψ c]
    exact hdet
  obtain ⟨K₀, hK₀one, hK₀boundary, hK₀all⟩ :=
    RealMatrixComponents.exists_uniform_scale A hA
  have hK₀pos : 0 < K₀ := zero_lt_one.trans_le hK₀one
  have hε : 0 < (1 / (2 * K₀) : ℝ) := by
    positivity
  obtain ⟨Rder, hRder, hder⟩ :
      ∃ Rder > 0,
        ∀ v ∈ Metric.ball c Rder,
          ‖ψ v - ψ c - fderiv ℝ ψ c (v - c)‖ ≤
            (1 / (2 * K₀)) * ‖v - c‖ :=
    Metric.eventually_nhds_iff_ball.mp <|
      ((hψdiff.differentiable
        (by norm_num)).differentiableAt).hasFDerivAt
        |>.isLittleO.bound hε
  have hopenVertical :
      IsOpen {v : Domain m | 0 < vertical m (F v)} :=
    isOpen_lt continuous_const <|
      (contDiff_vertical m).continuous.comp hFdiff.continuous
  have hcVertical :
      c ∈ {v : Domain m | 0 < vertical m (F v)} := by
    change 0 < vertical m (F c)
    rw [hvertc]
    norm_num
  obtain ⟨Rvert, hRvert, hvert⟩ :
      ∃ Rvert > 0,
        Metric.ball c Rvert ⊆
          {v : Domain m | 0 < vertical m (F v)} := by
    exact Metric.isOpen_iff.mp hopenVertical c hcVertical
  obtain ⟨Ragree, hRagree, hagreeBall⟩ :
      ∃ Ragree > 0,
        ∀ t ∈ Metric.ball t₀ Ragree,
          (p t : Target m) = F (cubeDomain m t) :=
    Metric.eventually_nhds_iff_ball.mp hagree
  let R : ℝ := min Rder (min Rvert Ragree)
  have hR : 0 < R := by
    dsimp only [R]
    exact lt_min hRder (lt_min hRvert hRagree)
  have ht₀notBoundary :
      t₀ ∉ Cube.boundary (Fin (m + 1)) := by
    intro htBoundary
    have := p.property t₀ htBoundary
    exact canonicalBasepoint_ne_neg m (this.symm.trans ht₀)
  have ht₀interior :
      ∀ i, 0 < (t₀ i : ℝ) ∧ (t₀ i : ℝ) < 1 :=
    cube_coordinate_strict_of_not_mem_boundary t₀
      ht₀notBoundary
  obtain ⟨d, hdcenter, hdscale⟩ :=
    SphereBubble.exists_localDatum_centered_lt
      t₀ ht₀interior hR
  have hdRder : d.scale < Rder :=
    hdscale.trans_le (min_le_left _ _)
  have hdRvert : d.scale < Rvert :=
    hdscale.trans_le <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hdRagree : d.scale < Ragree :=
    hdscale.trans_le <|
      (min_le_right _ _).trans (min_le_right _ _)
  let U : Set (Fin (m + 1) → I) :=
    {t | ‖SphereBubble.localCoordinates d t‖ < 1}
  have hU : IsOpen U :=
    isOpen_lt (SphereBubble.continuous_localCoordinates d).norm
      continuous_const
  have ht₀U : t₀ ∈ U := by
    change ‖SphereBubble.localCoordinates d t₀‖ < 1
    rw [← hdcenter]
    simp [SphereBubble.localCoordinates]
  have hfiberU :
      {t | p t = -(SphereGenerator.canonicalBasepoint m)} ⊆ U := by
    intro t ht
    rw [ht₀unique t ht]
    exact ht₀U
  have hδ : 0 < d.scale / (2 * K₀) := by
    exact div_pos d.scale_pos (mul_pos (by norm_num) hK₀pos)
  obtain ⟨e, hepos, hescale, hpe, heoutside⟩ :=
    SphereUpperChart.exists_genLoop_constant_off_scale_lt
      p hU hfiberU hδ
  let φ : (Fin (m + 1) → I) → Domain m :=
    fun t => SphereUpperChart.coordinate e (p t)
  have hφ : Continuous φ :=
    (SphereUpperChart.continuous_coordinate e).comp p.1.continuous
  let K : ℝ := d.scale / SphereUpperChart.scale e
  have hescalePos : 0 < SphereUpperChart.scale e :=
    SphereUpperChart.scale_pos e hepos
  have hKpos : 0 < K := div_pos d.scale_pos hescalePos
  have hK₀ltK : 2 * K₀ < K := by
    dsimp only [K]
    rw [lt_div_iff₀ hescalePos]
    have := mul_lt_mul_of_pos_left hescale
      (show 0 < 2 * K₀ by positivity)
    field_simp [hK₀pos.ne'] at this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hKone : 1 ≤ K :=
    (show (1 : ℝ) ≤ 2 * K₀ by nlinarith [hK₀one]).trans
      hK₀ltK.le
  have hK₀leK : K₀ ≤ K := by
    nlinarith [hK₀ltK, hK₀pos]
  have hK :
      ∀ v : Domain m, 1 ≤ ‖v‖ →
        1 ≤ ‖K • A.toEuclideanLin v‖ := by
    intro v hv
    have h₀ := hK₀boundary v hv
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hK₀pos] at h₀
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hKpos]
    exact h₀.trans <|
      mul_le_mul_of_nonneg_right
        hK₀leK (norm_nonneg _)
  have hinsideAmbient :
      ∀ t, ‖SphereBubble.localCoordinates d t‖ ≤ 1 →
        (p t : Target m) = F (cubeDomain m t) ∧
        0 < vertical m (F (cubeDomain m t)) := by
    intro t ht
    have hdist :
        ‖cubeDomain m t - c‖ ≤ d.scale := by
      simpa only [c, hdcenter] using
        localCoordinates_mem_ambient_ball d ht
    have hderBall :
        cubeDomain m t ∈ Metric.ball c Rder := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hdist.trans_lt hdRder
    have hvertBall :
        cubeDomain m t ∈ Metric.ball c Rvert := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hdist.trans_lt hdRvert
    have hagreeMetric :
        t ∈ Metric.ball t₀ Ragree := by
      rw [Metric.mem_ball]
      calc
        dist t t₀ ≤
            ‖cubeDomain m t - cubeDomain m t₀‖ :=
          dist_cube_le_norm_cubeDomain_sub m t t₀
        _ = ‖cubeDomain m t - c‖ := by rfl
        _ < Ragree := hdist.trans_lt hdRagree
    exact ⟨hagreeBall t hagreeMetric, hvert hvertBall⟩
  have hinside :
      ∀ t, ‖SphereBubble.localCoordinates d t‖ ≤ 1 →
        SphereUpperChart.genLoop e hepos p t =
          SphereBubble.map m (φ t) := by
    intro t ht
    obtain ⟨hagree', hvert'⟩ := hinsideAmbient t ht
    change SphereUpperChart.map e (p t) =
      SphereBubble.map m (SphereUpperChart.coordinate e (p t))
    rw [SphereUpperChart.map, if_pos]
    rw [congrArg (vertical m) hagree']
    exact hvert'.le
  have houtside :
      ∀ t, 1 ≤ ‖SphereBubble.localCoordinates d t‖ →
        SphereUpperChart.genLoop e hepos p t =
          SphereGenerator.canonicalBasepoint m := by
    intro t ht
    apply heoutside t
    exact not_lt.mpr ht
  have hwall :
      ∀ (s : I) (t : Fin (m + 1) → I),
        ‖SphereBubble.localCoordinates d t‖ = 1 →
          1 ≤
            ‖SphereLocalLinearization.interpolation
              φ d A K (s, t)‖ := by
    intro s t ht
    have htLe :
        ‖SphereBubble.localCoordinates d t‖ ≤ 1 := ht.le
    obtain ⟨hagree', _⟩ := hinsideAmbient t htLe
    let u := SphereBubble.localCoordinates d t
    let v := cubeDomain m t
    have hsub : v - c = d.scale • u := by
      simpa only [v, c, u, hdcenter] using
        (SphereBubble.scale_smul_localCoordinates d t).symm
    have hvBall : v ∈ Metric.ball c Rder := by
      rw [Metric.mem_ball, dist_eq_norm, hsub, norm_smul,
        Real.norm_eq_abs, abs_of_pos d.scale_pos, ht, mul_one]
      exact hdRder
    have happ := hder v hvBall
    rw [hψc, sub_zero] at happ
    have hφeq :
        φ t = (SphereUpperChart.scale e)⁻¹ • ψ v := by
      dsimp only [φ, ψ, v, SphereUpperChart.coordinate]
      rw [congrArg (horizontal m) hagree']
    have hlinear :
        K • A.toEuclideanLin u =
          (SphereUpperChart.scale e)⁻¹ •
            fderiv ℝ ψ c (v - c) := by
      rw [hAapply, hsub, map_smul, smul_smul]
      dsimp only [K]
      field_simp [hescalePos.ne', d.scale_pos.ne']
    have herror :
        ‖φ t - K • A.toEuclideanLin u‖ ≤
          K / (2 * K₀) := by
      rw [hφeq, hlinear, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hescalePos)]
      calc
        (SphereUpperChart.scale e)⁻¹ *
              ‖ψ v - fderiv ℝ ψ c (v - c)‖ ≤
            (SphereUpperChart.scale e)⁻¹ *
              ((1 / (2 * K₀)) * ‖v - c‖) :=
          mul_le_mul_of_nonneg_left happ
            (inv_pos.mpr hescalePos).le
        _ = K / (2 * K₀) := by
          rw [hsub, norm_smul, Real.norm_eq_abs,
            abs_of_pos d.scale_pos, ht, mul_one]
          dsimp only [K]
          field_simp [hescalePos.ne', hK₀pos.ne']
    have hlinearLower :
        K / K₀ ≤ ‖K • A.toEuclideanLin u‖ := by
      have h₀ := hK₀all u
      rw [ht] at h₀
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hK₀pos] at h₀
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hKpos]
      have hratio : 0 ≤ K / K₀ := (div_pos hKpos hK₀pos).le
      calc
        K / K₀ = (K / K₀) * 1 := by ring
        _ ≤ (K / K₀) *
            (K₀ * ‖A.toEuclideanLin u‖) :=
          mul_le_mul_of_nonneg_left h₀ hratio
        _ = K * ‖A.toEuclideanLin u‖ := by
          field_simp [hK₀pos.ne']
    have hratioTwo : 2 < K / K₀ := by
      rw [lt_div_iff₀ hK₀pos]
      exact hK₀ltK
    have hinterpolation :
        SphereLocalLinearization.interpolation
            φ d A K (s, t) =
          K • A.toEuclideanLin u +
            (1 - (s : ℝ)) •
              (φ t - K • A.toEuclideanLin u) := by
      dsimp only [SphereLocalLinearization.interpolation, u]
      module
    have hperturb :
        ‖(1 - (s : ℝ)) •
            (φ t - K • A.toEuclideanLin u)‖ ≤
          K / (2 * K₀) := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr s.property.2)]
      calc
        (1 - (s : ℝ)) *
              ‖φ t - K • A.toEuclideanLin u‖ ≤
            1 * ‖φ t - K • A.toEuclideanLin u‖ :=
          mul_le_mul_of_nonneg_right
            (by linarith [s.property.1])
            (norm_nonneg _)
        _ ≤ K / (2 * K₀) := by simpa using herror
    rw [hinterpolation]
    have htriangle :=
      norm_sub_le
        (K • A.toEuclideanLin u +
          (1 - (s : ℝ)) •
            (φ t - K • A.toEuclideanLin u))
        ((1 - (s : ℝ)) •
          (φ t - K • A.toEuclideanLin u))
    rw [add_sub_cancel_right] at htriangle
    have hdouble :
        K / K₀ = 2 * (K / (2 * K₀)) := by
      field_simp [hK₀pos.ne']
    have hhalf : 1 < K / (2 * K₀) := by
      linarith [hratioTwo, hdouble]
    have hsumLower :
        K / (2 * K₀) ≤
          ‖K • A.toEuclideanLin u +
            (1 - (s : ℝ)) •
              (φ t - K • A.toEuclideanLin u)‖ := by
      linarith [hlinearLower, hperturb, htriangle, hdouble]
    exact hhalf.le.trans hsumLower
  have hcollapsed :=
    SphereLocalLinearization.class_eq_or_eq_inverse
      (SphereUpperChart.genLoop e hepos p)
      φ hφ d A hA K hKone hK hinside houtside hwall
  have hclass :
      (Quotient.mk' p :
          HomotopyGroup.Pi (m + 1) (UnitSphere m)
            (SphereGenerator.canonicalBasepoint m)) =
        Quotient.mk' (SphereUpperChart.genLoop e hepos p) :=
    Quotient.sound hpe
  rcases hcollapsed with hcollapsed | hcollapsed
  · exact Or.inl (hclass.trans hcollapsed)
  · exact Or.inr (hclass.trans hcollapsed)

end Submission.SphereSingleton
