import Submission.KernelExpansion
import Submission.PlaneTopology
import Submission.Runge

open Set
open scoped ContDiff Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- On a compact set avoiding zero, higher powers can cancel prescribed
linear and quadratic terms while leaving those two terms unchanged in the
Taylor expansion at zero.

The connected-complement hypothesis is used only to approximate the
rational function `-m₀ / ζ² + m₁ / ζ` by polynomials. -/
theorem exists_higherPower_moment_regularization
    (L : Set ℂ) (hL : IsCompact L) (hLc : IsConnected (Lᶜ))
    (h0 : 0 ∉ L) (m₀ m₁ : ℂ) (e : ℝ) (he : 0 < e) :
    ∃ P : ℂ[X], ∀ ζ ∈ L,
      ‖m₀ * ζ - m₁ * ζ ^ 2 + ζ ^ 3 * P.eval ζ‖ < e := by
  let F : ℂ → ℂ := fun ζ ↦ (-m₀ + m₁ * ζ) / ζ ^ 2
  have hF : ContinuousOn F L := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro ζ hζ
      exact pow_ne_zero 2 fun hζ0 ↦ h0 (hζ0 ▸ hζ)
  letI : CompactSpace L :=
    isCompact_iff_compactSpace.mp hL
  obtain ⟨u, hu⟩ :=
    exists_rational_mem_polynomialClosure hLc
      (Polynomial.C (-m₀) + Polynomial.C m₁ * Polynomial.X)
      (Polynomial.X ^ 2) (by
        intro ζ hζ
        simp only [Polynomial.eval_pow, Polynomial.eval_X]
        exact pow_ne_zero 2 fun hζ0 ↦ h0 (hζ0 ▸ hζ))
  have hFu :
      restrictTo F hF = (u : C(L, ℂ)) := by
    ext ζ
    rw [restrictTo_apply, hu]
    simp only [Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow]
    rfl
  have hFclosure :
      restrictTo F hF ∈
        (polynomialFunctions L).topologicalClosure := by
    rw [hFu]
    exact u.property
  obtain ⟨R₀, hLR₀⟩ :=
    hL.isBounded.subset_closedBall (0 : ℂ)
  let R : ℝ := max R₀ 1
  have hR : 0 < R :=
    lt_max_of_lt_right zero_lt_one
  have hLR : ∀ ζ ∈ L, ‖ζ‖ ≤ R := by
    intro ζ hζ
    have hζR := hLR₀ hζ
    rw [Metric.mem_closedBall, dist_zero_right] at hζR
    exact hζR.trans (le_max_left _ _)
  let d : ℝ := e / (R ^ 3 + 1)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  obtain ⟨P, hP⟩ :=
    (mem_polynomialFunctions_topologicalClosure_iff F hF).mp
      hFclosure d hd
  refine ⟨P, ?_⟩
  intro ζ hζ
  have hζ0 : ζ ≠ 0 := fun h ↦ h0 (h ▸ hζ)
  have hid :
      m₀ * ζ - m₁ * ζ ^ 2 + ζ ^ 3 * P.eval ζ =
        ζ ^ 3 * (P.eval ζ - F ζ) := by
    dsimp [F]
    field_simp [hζ0]
    ring
  rw [hid, norm_mul, norm_pow]
  calc
    ‖ζ‖ ^ 3 * ‖P.eval ζ - F ζ‖
        ≤ R ^ 3 * ‖P.eval ζ - F ζ‖ := by
      gcongr
      exact hLR ζ hζ
    _ < R ^ 3 * d := by
      apply mul_lt_mul_of_pos_left
      · simpa only [norm_sub_rev] using hP ζ hζ
      · positivity
    _ < e := by
      dsimp [d]
      have hden : 0 < R ^ 3 + 1 := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hden]
      nlinarith [pow_pos hR 3]

/-- Higher-power moment regularization with independent near- and far-field
control.  Besides cancelling the prescribed linear and quadratic terms on
`L`, the polynomial is forced to be arbitrarily small on a disk about zero.
After substituting a resolvent coordinate, the latter condition gives a
chosen cubic-decay coefficient in the far field.

The proof applies the local Runge theorem to the disjoint compact union of
`L` and the zero-centered disk. -/
theorem exists_higherPower_moment_regularization_near_far
    (L : Set ℂ) (hL : IsCompact L) (hLc : IsConnected (Lᶜ))
    (h0 : 0 ∉ L) (ρ σ : ℝ) (hρ : 0 ≤ ρ) (hρσ : ρ < σ)
    (hσ : Metric.ball (0 : ℂ) σ ⊆ Lᶜ)
    (m₀ m₁ : ℂ) (eNear eFar : ℝ)
    (heNear : 0 < eNear) (heFar : 0 < eFar) :
    ∃ P : ℂ[X],
      (∀ ζ ∈ L,
        ‖m₀ * ζ - m₁ * ζ ^ 2 + ζ ^ 3 * P.eval ζ‖ <
          eNear) ∧
      ∀ ζ ∈ Metric.closedBall (0 : ℂ) ρ,
        ‖P.eval ζ‖ < eFar := by
  let t : ℝ := (ρ + σ) / 2
  have hρt : ρ < t := by
    dsimp [t]
    linarith
  have htσ : t < σ := by
    dsimp [t]
    linarith
  let U : Set ℂ := (Metric.closedBall (0 : ℂ) t)ᶜ
  have hUopen : IsOpen U :=
    Metric.isClosed_closedBall.isOpen_compl
  have hLU : L ⊆ U := by
    intro ζ hζ
    change ζ ∉ Metric.closedBall (0 : ℂ) t
    rw [Metric.mem_closedBall, dist_zero_right, not_le]
    by_contra hζt
    have hζle : ‖ζ‖ ≤ t :=
      le_of_not_gt hζt
    have hζσ : ζ ∈ Metric.ball (0 : ℂ) σ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hζle.trans_lt htσ
    exact (hσ hζσ) hζ
  obtain ⟨δ, hδ, χ, hχsmooth, hχcompact, _hχbounds,
      hχone, hχsupport⟩ :=
    exists_smooth_cutoff_bounded L U hL hUopen hLU
  let F : ℂ → ℂ :=
    fun ζ ↦ (-m₀ + m₁ * ζ) / ζ ^ 2
  let G : ℂ → ℂ :=
    fun ζ ↦ (χ ζ : ℂ) * F ζ
  have hFRealAt {ζ : ℂ} (hζ : ζ ≠ 0) :
      ContDiffAt ℝ ∞ F ζ := by
    dsimp only [F]
    have hnum :
        ContDiffAt ℝ ∞
          (fun w : ℂ ↦ -m₀ + m₁ * w) ζ := by
      fun_prop
    have hden :
        ContDiffAt ℝ ∞ (fun w : ℂ ↦ w ^ 2) ζ := by
      fun_prop
    simpa only [div_eq_mul_inv] using
      hnum.mul (hden.inv (pow_ne_zero 2 hζ))
  have hFComplexAt {ζ : ℂ} (hζ : ζ ≠ 0) :
      DifferentiableAt ℂ F ζ := by
    dsimp only [F]
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero 2 hζ
  have hχcomplex :
      ContDiff ℝ ∞ (fun ζ ↦ (χ ζ : ℂ)) := by
    change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ χ)
    exact Complex.ofRealCLM.contDiff.comp hχsmooth
  have hGsmooth : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro ζ
    by_cases hζ : ζ = 0
    · subst ζ
      have hzeroU : (0 : ℂ) ∉ U := by
        dsimp only [U]
        rw [mem_compl_iff, not_not, Metric.mem_closedBall,
          dist_self]
        exact le_trans hρ hρt.le
      have hzeroSupport : (0 : ℂ) ∉ tsupport χ :=
        fun hz ↦ hzeroU (hχsupport hz)
      have hχzero :
          χ =ᶠ[𝓝 (0 : ℂ)] 0 :=
        (notMem_tsupport_iff_eventuallyEq).mp hzeroSupport
      have hGzero :
          G =ᶠ[𝓝 (0 : ℂ)] 0 := by
        filter_upwards [hχzero] with w hw
        simp [G, hw]
      exact
        (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
          hGzero
    · exact hχcomplex.contDiffAt.mul (hFRealAt hζ)
  have hGcompact : HasCompactSupport G := by
    have hχcomplexCompact :
        HasCompactSupport (fun ζ ↦ (χ ζ : ℂ)) :=
      hχcompact.comp_left Complex.ofReal_zero
    exact hχcomplexCompact.mul_right
  let H : Set ℂ :=
    L ∪ Metric.closedBall (0 : ℂ) ρ
  have hHcompact : IsCompact H :=
    hL.union (isCompact_closedBall (0 : ℂ) ρ)
  have hHc : IsConnected (Hᶜ) := by
    simpa only [H] using
      isConnected_compl_union_closedBall_complex
        L hLc (0 : ℂ) hρ hρσ hσ
  let V : Set ℂ :=
    Metric.thickening (δ / 3) L ∪ (tsupport χ)ᶜ
  have hVopen : IsOpen V :=
    Metric.isOpen_thickening.union isClosed_closure.isOpen_compl
  have hDiskOutsideSupport :
      Metric.closedBall (0 : ℂ) ρ ⊆ (tsupport χ)ᶜ := by
    intro ζ hζ
    rw [mem_compl_iff]
    intro hζSupport
    have hζU := hχsupport hζSupport
    change ζ ∉ Metric.closedBall (0 : ℂ) t at hζU
    rw [Metric.mem_closedBall, dist_zero_right] at hζU
    have hζρ : ‖ζ‖ ≤ ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hζ
    exact hζU (hζρ.trans hρt.le)
  have hHV : H ⊆ V := by
    intro ζ hζ
    rcases hζ with hζL | hζDisk
    · exact Or.inl
        (Metric.self_subset_thickening
          (by positivity : 0 < δ / 3) L hζL)
    · exact Or.inr (hDiskOutsideSupport hζDisk)
  have hGV : DifferentiableOn ℂ G V := by
    intro ζ hζ
    rcases hζ with hζNear | hζOutside
    · have hζClosed :
          ζ ∈ Metric.cthickening (δ / 3) L :=
        Metric.thickening_subset_cthickening (δ / 3) L hζNear
      have hχζ : χ ζ = 1 :=
        hχone ζ hζClosed
      have hζSupport : ζ ∈ tsupport χ := by
        apply subset_tsupport
        simp [hχζ]
      have hζU := hχsupport hζSupport
      have hζ0 : ζ ≠ 0 := by
        intro hζzero
        subst ζ
        change (0 : ℂ) ∉ Metric.closedBall (0 : ℂ) t at hζU
        rw [Metric.mem_closedBall, dist_self] at hζU
        exact hζU (le_trans hρ hρt.le)
      have hGF : G =ᶠ[𝓝 ζ] F := by
        filter_upwards
          [Metric.isOpen_thickening.mem_nhds hζNear] with w hw
        have hwClosed :
            w ∈ Metric.cthickening (δ / 3) L :=
          Metric.thickening_subset_cthickening (δ / 3) L hw
        simp [G, hχone w hwClosed]
      exact
        (hGF.differentiableAt_iff.mpr
          (hFComplexAt hζ0)).differentiableWithinAt
    · have hχzero :
          χ =ᶠ[𝓝 ζ] 0 :=
        (notMem_tsupport_iff_eventuallyEq).mp hζOutside
      have hGzero : G =ᶠ[𝓝 ζ] 0 := by
        filter_upwards [hχzero] with w hw
        simp [G, hw]
      exact
        (hGzero.differentiableAt_iff.mpr
          (differentiableAt_const (c := (0 : ℂ)))).differentiableWithinAt
  obtain ⟨R₀, hLR₀⟩ :=
    hL.isBounded.subset_closedBall (0 : ℂ)
  let R : ℝ := max R₀ 1
  have hR : 0 < R :=
    lt_max_of_lt_right zero_lt_one
  have hLR : ∀ ζ ∈ L, ‖ζ‖ ≤ R := by
    intro ζ hζ
    have hζR := hLR₀ hζ
    rw [Metric.mem_closedBall, dist_zero_right] at hζR
    exact hζR.trans (le_max_left _ _)
  let d : ℝ :=
    min (eNear / (R ^ 3 + 1)) eFar
  have hd : 0 < d := by
    dsimp [d]
    positivity
  obtain ⟨P, hP⟩ :=
    exists_polynomial_approx_of_differentiableOn_nhd
      H hHcompact hHc G hGsmooth hGcompact
      hVopen hHV hGV d hd
  refine ⟨P, ?_, ?_⟩
  · intro ζ hζ
    have hχζ : χ ζ = 1 :=
      hχone ζ
        (Metric.self_subset_cthickening L hζ)
    have hGζ : G ζ = F ζ := by
      simp [G, hχζ]
    have hζ0 : ζ ≠ 0 :=
      fun h ↦ h0 (h ▸ hζ)
    have hid :
        m₀ * ζ - m₁ * ζ ^ 2 + ζ ^ 3 * P.eval ζ =
          ζ ^ 3 * (P.eval ζ - F ζ) := by
      dsimp [F]
      field_simp [hζ0]
      ring
    rw [hid, norm_mul, norm_pow]
    calc
      ‖ζ‖ ^ 3 * ‖P.eval ζ - F ζ‖
          ≤ R ^ 3 * ‖P.eval ζ - F ζ‖ := by
        gcongr
        exact hLR ζ hζ
      _ < R ^ 3 * d := by
        apply mul_lt_mul_of_pos_left
        · simpa only [hGζ, norm_sub_rev] using
            hP ζ (Or.inl hζ)
        · positivity
      _ ≤ R ^ 3 * (eNear / (R ^ 3 + 1)) := by
        gcongr
        exact min_le_left _ _
      _ < eNear := by
        have hden : 0 < R ^ 3 + 1 := by positivity
        rw [← mul_div_assoc, div_lt_iff₀ hden]
        nlinarith [pow_pos hR 3]
  · intro ζ hζ
    have hζOutside := hDiskOutsideSupport hζ
    have hχζ : χ ζ = 0 := by
      apply Function.notMem_support.mp
      intro hζSupport
      exact hζOutside (subset_tsupport χ hζSupport)
    have hGζ : G ζ = 0 := by
      simp [G, hχζ]
    calc
      ‖P.eval ζ‖ = ‖G ζ - P.eval ζ‖ := by
        rw [hGζ, zero_sub, norm_neg]
      _ < d :=
        hP ζ (Or.inr hζ)
      _ ≤ eFar :=
        min_le_right _ _

/-- Specialization of higher-power regularization to the resolvent
coordinate associated to one exterior pole. -/
theorem exists_resolventMoment_regularization
    (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    (a : ℂ) (ha : a ∉ K)
    (m₀ m₁ : ℂ) (e : ℝ) (he : 0 < e) :
    ∃ P : ℂ[X], ∀ z ∈ K,
      ‖(a - z)⁻¹ * m₀ -
          (a - z)⁻¹ ^ 2 * m₁ +
        (a - z)⁻¹ ^ 3 * P.eval (a - z)⁻¹‖ < e := by
  let L : Set ℂ := (fun z : ℂ ↦ (a - z)⁻¹) '' K
  have hresContinuous :
      ContinuousOn (fun z : ℂ ↦ (a - z)⁻¹) K :=
    (continuousOn_const.sub continuousOn_id).inv₀ fun z hz ↦
      sub_ne_zero.mpr fun h ↦ ha (h ▸ hz)
  have hL : IsCompact L :=
    hK.image_of_continuousOn hresContinuous
  have h0 : 0 ∉ L := by
    rintro ⟨z, hz, hza⟩
    have haz : a - z ≠ 0 := sub_ne_zero.mpr fun h ↦ ha (h ▸ hz)
    exact (inv_ne_zero haz) hza
  obtain ⟨P, hP⟩ :=
    exists_higherPower_moment_regularization
      L hL (by
        simpa only [L] using
          isConnected_compl_resolvent_image K hK hKc a ha)
      h0 m₀ m₁ e he
  refine ⟨P, ?_⟩
  intro z hz
  simpa only [mul_comm (a - z)⁻¹ m₀,
    mul_comm ((a - z)⁻¹ ^ 2) m₁] using
    hP (a - z)⁻¹ ⟨z, hz, rfl⟩

/-- The regularized moment expression is still an element of the closed
polynomial algebra: it is a polynomial in one resolvent whose pole misses
`K`. -/
theorem exists_small_regularizedMoment_mem_polynomialClosure
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    (a : ℂ) (ha : a ∉ K) (m₀ m₁ : ℂ)
    (e : ℝ) (he : 0 < e) :
    ∃ P : ℂ[X],
      ∃ u : (polynomialFunctions K).topologicalClosure,
        (∀ z : K,
          (u : C(K, ℂ)) z =
            (a - (z : ℂ))⁻¹ * m₀ -
              (a - (z : ℂ))⁻¹ ^ 2 * m₁ +
            (a - (z : ℂ))⁻¹ ^ 3 *
              P.eval (a - (z : ℂ))⁻¹) ∧
        ∀ z : K, ‖(u : C(K, ℂ)) z‖ < e := by
  have hK : IsCompact K :=
    isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨P, hP⟩ :=
    exists_resolventMoment_regularization
      K hK hKc a ha m₀ m₁ e he
  obtain ⟨s, hs⟩ :=
    exists_resolvent_mem_polynomialClosure hKc ha
  let u : (polynomialFunctions K).topologicalClosure :=
    m₀ • s - m₁ • s ^ 2 +
      s ^ 3 * Polynomial.aeval s P
  have hu (z : K) :
      (u : C(K, ℂ)) z =
        (a - (z : ℂ))⁻¹ * m₀ -
          (a - (z : ℂ))⁻¹ ^ 2 * m₁ +
        (a - (z : ℂ))⁻¹ ^ 3 *
          P.eval (a - (z : ℂ))⁻¹ := by
    change
      m₀ * (s : C(K, ℂ)) z -
          m₁ * (s : C(K, ℂ)) z ^ 2 +
        (s : C(K, ℂ)) z ^ 3 *
          ((Polynomial.aeval s P :
            (polynomialFunctions K).topologicalClosure) :
              C(K, ℂ)) z = _
    rw [Polynomial.aeval_subalgebra_coe,
      Polynomial.aeval_continuousMap_apply, hs]
    ring
  refine ⟨P, u, hu, ?_⟩
  intro z
  rw [hu]
  exact hP z z.property

/-- Near/far resolvent regularization around a geometric source center.
The near compact is assumed to lie at distance at most `A` from the pole.
On that compact the first two moments are cancelled to a chosen tolerance;
once an evaluation is at distance at least `2A` from the pole, the added
term has a separately chosen cubic coefficient. -/
theorem exists_centeredBall_resolventMoment_regularization_near_far
    (K : Set ℂ) [CompactSpace K]
    (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    (a : ℂ) (ha : a ∉ K) (x : ℂ) (R A : ℝ) (hA : 0 < A)
    (hnearDist :
      ∀ z ∈ K, dist x z ≤ R → dist a z ≤ A)
    (m₀ m₁ : ℂ) (eNear eFar : ℝ)
    (heNear : 0 < eNear) (heFar : 0 < eFar) :
    ∃ (P : ℂ[X])
        (u : (polynomialFunctions K).topologicalClosure),
      (∀ z : K,
        (u : C(K, ℂ)) z =
          (a - (z : ℂ))⁻¹ * m₀ -
            (a - (z : ℂ))⁻¹ ^ 2 * m₁ +
          (a - (z : ℂ))⁻¹ ^ 3 *
            P.eval (a - (z : ℂ))⁻¹) ∧
      (∀ z : K, dist x (z : ℂ) ≤ R →
        ‖(u : C(K, ℂ)) z‖ < eNear) ∧
      ∀ z : K, 2 * A ≤ dist a (z : ℂ) →
        ‖(a - (z : ℂ))⁻¹ ^ 3 *
            P.eval (a - (z : ℂ))⁻¹‖ <
          eFar * (dist a (z : ℂ))⁻¹ ^ 3 := by
  let E : Set ℂ := K ∩ Metric.closedBall x R
  let L : Set ℂ := (fun z : ℂ ↦ (a - z)⁻¹) '' E
  have hE : IsCompact E :=
    hK.inter (isCompact_closedBall x R)
  have hEc : IsConnected (Eᶜ) := by
    simpa only [E] using
      isConnected_compl_inter_closedBall_complex
        K hK hKc x R
  have haE : a ∉ E := by
    intro haMem
    exact ha haMem.1
  have hresContinuous :
      ContinuousOn (fun z : ℂ ↦ (a - z)⁻¹) E :=
    (continuousOn_const.sub continuousOn_id).inv₀ fun z hz ↦
      sub_ne_zero.mpr fun h ↦ ha (h ▸ hz.1)
  have hL : IsCompact L :=
    hE.image_of_continuousOn hresContinuous
  have hLc : IsConnected (Lᶜ) := by
    simpa only [L] using
      isConnected_compl_resolvent_image
        E hE hEc a haE
  have h0 : 0 ∉ L := by
    rintro ⟨z, hz, hza⟩
    have haz : a - z ≠ 0 :=
      sub_ne_zero.mpr fun h ↦ ha (h ▸ hz.1)
    exact (inv_ne_zero haz) hza
  let ρ : ℝ := (2 * A)⁻¹
  let σ : ℝ := A⁻¹
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hρσ : ρ < σ := by
    dsimp [ρ, σ]
    exact
      (inv_lt_inv₀ (mul_pos (by norm_num) hA) hA).2
        (by nlinarith)
  have hσ : Metric.ball (0 : ℂ) σ ⊆ Lᶜ := by
    intro ζ hζ
    rw [mem_compl_iff]
    rintro ⟨z, hzE, rfl⟩
    have haz : a ≠ z := by
      intro h
      apply ha
      rw [h]
      exact hzE.1
    have hdaz : 0 < dist a z :=
      dist_pos.mpr haz
    have hdazA : dist a z ≤ A :=
      hnearDist z hzE.1 (by
        simpa only [dist_comm] using
          Metric.mem_closedBall.mp hzE.2)
    have hAinv :
        A⁻¹ ≤ (dist a z)⁻¹ :=
      (inv_le_inv₀ hA hdaz).2 hdazA
    have hζnorm :
        ‖(a - z)⁻¹‖ < A⁻¹ := by
      simpa only [σ, Metric.mem_ball, dist_zero_right] using hζ
    rw [norm_inv, ← dist_eq_norm] at hζnorm
    exact (not_lt_of_ge hAinv) hζnorm
  obtain ⟨P, hPnear, hPfar⟩ :=
    exists_higherPower_moment_regularization_near_far
      L hL hLc h0 ρ σ hρ hρσ hσ
      m₀ m₁ eNear eFar heNear heFar
  obtain ⟨s, hs⟩ :=
    exists_resolvent_mem_polynomialClosure hKc ha
  let u : (polynomialFunctions K).topologicalClosure :=
    m₀ • s - m₁ • s ^ 2 +
      s ^ 3 * Polynomial.aeval s P
  have hu (z : K) :
      (u : C(K, ℂ)) z =
        (a - (z : ℂ))⁻¹ * m₀ -
          (a - (z : ℂ))⁻¹ ^ 2 * m₁ +
        (a - (z : ℂ))⁻¹ ^ 3 *
          P.eval (a - (z : ℂ))⁻¹ := by
    change
      m₀ * (s : C(K, ℂ)) z -
          m₁ * (s : C(K, ℂ)) z ^ 2 +
        (s : C(K, ℂ)) z ^ 3 *
          ((Polynomial.aeval s P :
            (polynomialFunctions K).topologicalClosure) :
              C(K, ℂ)) z = _
    rw [Polynomial.aeval_subalgebra_coe,
      Polynomial.aeval_continuousMap_apply, hs]
    ring
  refine ⟨P, u, hu, ?_, ?_⟩
  · intro z hzR
    rw [hu]
    simpa only [mul_comm] using
      hPnear (a - (z : ℂ))⁻¹
        ⟨z, ⟨z.property, by
          rw [Metric.mem_closedBall]
          simpa only [dist_comm] using hzR⟩, rfl⟩
  · intro z hfar
    have hdaz : 0 < dist a (z : ℂ) :=
      (mul_pos (by norm_num) hA).trans_le hfar
    have hinv :
        ‖(a - (z : ℂ))⁻¹‖ ≤ ρ := by
      rw [norm_inv, ← dist_eq_norm]
      exact
        (inv_le_inv₀ hdaz
          (mul_pos (by norm_num) hA)).2 hfar
    have hinvMem :
        (a - (z : ℂ))⁻¹ ∈
          Metric.closedBall (0 : ℂ) ρ := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hinv
    have hPeval :=
      hPfar (a - (z : ℂ))⁻¹ hinvMem
    rw [norm_mul, norm_pow, norm_inv, ← dist_eq_norm]
    calc
      (dist a (z : ℂ))⁻¹ ^ 3 *
            ‖P.eval (a - (z : ℂ))⁻¹‖
          < (dist a (z : ℂ))⁻¹ ^ 3 * eFar := by
        exact mul_lt_mul_of_pos_left hPeval (by positivity)
      _ = eFar * (dist a (z : ℂ))⁻¹ ^ 3 := by ring

/-- Localized moment regularization.  On the part of `K` lying near the
exterior pole, higher resolvent powers make the first two moment terms
uniformly small.  On the far part, the added term remains explicitly third
order in the resolvent and therefore admits the displayed cubic decay bound.

This is the near/far form needed in frontier localization: unlike global
regularization, it does not discard the first two Laurent moments away from
the source. -/
theorem exists_localized_resolventMoment_regularization
    (K : Set ℂ) [CompactSpace K]
    (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    (a : ℂ) (ha : a ∉ K) (R d : ℝ) (hd : 0 < d)
    (m₀ m₁ : ℂ) (e : ℝ) (he : 0 < e) :
    ∃ (P : ℂ[X]) (B : ℝ),
      0 < B ∧
      ∃ u : (polynomialFunctions K).topologicalClosure,
        (∀ z : K,
          (u : C(K, ℂ)) z =
            (a - (z : ℂ))⁻¹ * m₀ -
              (a - (z : ℂ))⁻¹ ^ 2 * m₁ +
            (a - (z : ℂ))⁻¹ ^ 3 *
              P.eval (a - (z : ℂ))⁻¹) ∧
        (∀ z : K, dist a (z : ℂ) ≤ R →
          ‖(u : C(K, ℂ)) z‖ < e) ∧
        ∀ z : K, d ≤ dist a (z : ℂ) →
          ‖(a - (z : ℂ))⁻¹ ^ 3 *
              P.eval (a - (z : ℂ))⁻¹‖ ≤
            B * (dist a (z : ℂ))⁻¹ ^ 3 := by
  let L : Set ℂ := K ∩ Metric.closedBall a R
  have hL : IsCompact L :=
    hK.inter (isCompact_closedBall a R)
  have hLc : IsConnected (Lᶜ) := by
    simpa only [L] using
      isConnected_compl_inter_closedBall_complex K hK hKc a R
  have haL : a ∉ L := by
    intro haMem
    exact ha haMem.1
  obtain ⟨P, hP⟩ :=
    exists_resolventMoment_regularization
      L hL hLc a haL m₀ m₁ e he
  let Z : Set ℂ :=
    P.eval '' Metric.closedBall (0 : ℂ) d⁻¹
  have hZ : IsCompact Z :=
    (isCompact_closedBall (0 : ℂ) d⁻¹).image P.continuous
  obtain ⟨B₀, hZB₀⟩ :=
    hZ.isBounded.subset_closedBall (0 : ℂ)
  let B : ℝ := max B₀ 1
  have hB : 0 < B :=
    lt_max_of_lt_right zero_lt_one
  have hZB : ∀ z ∈ Z, ‖z‖ ≤ B := by
    intro z hz
    have hzB := hZB₀ hz
    rw [Metric.mem_closedBall, dist_zero_right] at hzB
    exact hzB.trans (le_max_left _ _)
  obtain ⟨s, hs⟩ :=
    exists_resolvent_mem_polynomialClosure hKc ha
  let u : (polynomialFunctions K).topologicalClosure :=
    m₀ • s - m₁ • s ^ 2 +
      s ^ 3 * Polynomial.aeval s P
  have hu (z : K) :
      (u : C(K, ℂ)) z =
        (a - (z : ℂ))⁻¹ * m₀ -
          (a - (z : ℂ))⁻¹ ^ 2 * m₁ +
        (a - (z : ℂ))⁻¹ ^ 3 *
          P.eval (a - (z : ℂ))⁻¹ := by
    change
      m₀ * (s : C(K, ℂ)) z -
          m₁ * (s : C(K, ℂ)) z ^ 2 +
        (s : C(K, ℂ)) z ^ 3 *
          ((Polynomial.aeval s P :
            (polynomialFunctions K).topologicalClosure) :
              C(K, ℂ)) z = _
    rw [Polynomial.aeval_subalgebra_coe,
      Polynomial.aeval_continuousMap_apply, hs]
    ring
  refine ⟨P, B, hB, u, hu, ?_, ?_⟩
  · intro z hzR
    rw [hu]
    exact hP (z : ℂ) ⟨z.property, by
      rw [Metric.mem_closedBall]
      simpa only [dist_comm] using hzR⟩
  · intro z hdz
    have hdistPos : 0 < dist a (z : ℂ) :=
      hd.trans_le hdz
    have hinv :
        ‖(a - (z : ℂ))⁻¹‖ ≤ d⁻¹ := by
      rw [norm_inv, ← dist_eq_norm]
      exact
        (inv_le_inv₀ hdistPos hd).2 hdz
    have hinvMem :
        (a - (z : ℂ))⁻¹ ∈
          Metric.closedBall (0 : ℂ) d⁻¹ := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hinv
    have hPeval :
        ‖P.eval (a - (z : ℂ))⁻¹‖ ≤ B :=
      hZB _ ⟨(a - (z : ℂ))⁻¹, hinvMem, rfl⟩
    rw [norm_mul, norm_pow, norm_inv, ← dist_eq_norm]
    calc
      (dist a (z : ℂ))⁻¹ ^ 3 *
            ‖P.eval (a - (z : ℂ))⁻¹‖
          ≤ (dist a (z : ℂ))⁻¹ ^ 3 * B := by
        exact mul_le_mul_of_nonneg_left hPeval (by positivity)
      _ = B * (dist a (z : ℂ))⁻¹ ^ 3 := by ring

/-- A localization variant whose near set is centered at the geometric
source center rather than at the exterior pole.  This is the useful form
when the pole lies in a thin part of the complement: every evaluation near
the source is regularized, while evaluations separated from the pole retain
the explicit cubic resolvent bound. -/
theorem exists_centeredBall_resolventMoment_regularization
    (K : Set ℂ) [CompactSpace K]
    (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    (a : ℂ) (ha : a ∉ K) (x : ℂ) (R d : ℝ) (hd : 0 < d)
    (m₀ m₁ : ℂ) (e : ℝ) (he : 0 < e) :
    ∃ (P : ℂ[X]) (B : ℝ),
      0 < B ∧
      ∃ u : (polynomialFunctions K).topologicalClosure,
        (∀ z : K,
          (u : C(K, ℂ)) z =
            (a - (z : ℂ))⁻¹ * m₀ -
              (a - (z : ℂ))⁻¹ ^ 2 * m₁ +
            (a - (z : ℂ))⁻¹ ^ 3 *
              P.eval (a - (z : ℂ))⁻¹) ∧
        (∀ z : K, dist x (z : ℂ) ≤ R →
          ‖(u : C(K, ℂ)) z‖ < e) ∧
        ∀ z : K, d ≤ dist a (z : ℂ) →
          ‖(a - (z : ℂ))⁻¹ ^ 3 *
              P.eval (a - (z : ℂ))⁻¹‖ ≤
            B * (dist a (z : ℂ))⁻¹ ^ 3 := by
  let L : Set ℂ := K ∩ Metric.closedBall x R
  have hL : IsCompact L :=
    hK.inter (isCompact_closedBall x R)
  have hLc : IsConnected (Lᶜ) := by
    simpa only [L] using
      isConnected_compl_inter_closedBall_complex K hK hKc x R
  have haL : a ∉ L := by
    intro haMem
    exact ha haMem.1
  obtain ⟨P, hP⟩ :=
    exists_resolventMoment_regularization
      L hL hLc a haL m₀ m₁ e he
  let Z : Set ℂ :=
    P.eval '' Metric.closedBall (0 : ℂ) d⁻¹
  have hZ : IsCompact Z :=
    (isCompact_closedBall (0 : ℂ) d⁻¹).image P.continuous
  obtain ⟨B₀, hZB₀⟩ :=
    hZ.isBounded.subset_closedBall (0 : ℂ)
  let B : ℝ := max B₀ 1
  have hB : 0 < B :=
    lt_max_of_lt_right zero_lt_one
  have hZB : ∀ z ∈ Z, ‖z‖ ≤ B := by
    intro z hz
    have hzB := hZB₀ hz
    rw [Metric.mem_closedBall, dist_zero_right] at hzB
    exact hzB.trans (le_max_left _ _)
  obtain ⟨s, hs⟩ :=
    exists_resolvent_mem_polynomialClosure hKc ha
  let u : (polynomialFunctions K).topologicalClosure :=
    m₀ • s - m₁ • s ^ 2 +
      s ^ 3 * Polynomial.aeval s P
  have hu (z : K) :
      (u : C(K, ℂ)) z =
        (a - (z : ℂ))⁻¹ * m₀ -
          (a - (z : ℂ))⁻¹ ^ 2 * m₁ +
        (a - (z : ℂ))⁻¹ ^ 3 *
          P.eval (a - (z : ℂ))⁻¹ := by
    change
      m₀ * (s : C(K, ℂ)) z -
          m₁ * (s : C(K, ℂ)) z ^ 2 +
        (s : C(K, ℂ)) z ^ 3 *
          ((Polynomial.aeval s P :
            (polynomialFunctions K).topologicalClosure) :
              C(K, ℂ)) z = _
    rw [Polynomial.aeval_subalgebra_coe,
      Polynomial.aeval_continuousMap_apply, hs]
    ring
  refine ⟨P, B, hB, u, hu, ?_, ?_⟩
  · intro z hzR
    rw [hu]
    exact hP (z : ℂ) ⟨z.property, by
      rw [Metric.mem_closedBall]
      simpa only [dist_comm] using hzR⟩
  · intro z hdz
    have hdistPos : 0 < dist a (z : ℂ) :=
      hd.trans_le hdz
    have hinv :
        ‖(a - (z : ℂ))⁻¹‖ ≤ d⁻¹ := by
      rw [norm_inv, ← dist_eq_norm]
      exact (inv_le_inv₀ hdistPos hd).2 hdz
    have hinvMem :
        (a - (z : ℂ))⁻¹ ∈
          Metric.closedBall (0 : ℂ) d⁻¹ := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hinv
    have hPeval :
        ‖P.eval (a - (z : ℂ))⁻¹‖ ≤ B :=
      hZB _ ⟨(a - (z : ℂ))⁻¹, hinvMem, rfl⟩
    rw [norm_mul, norm_pow, norm_inv, ← dist_eq_norm]
    calc
      (dist a (z : ℂ))⁻¹ ^ 3 *
            ‖P.eval (a - (z : ℂ))⁻¹‖
          ≤ (dist a (z : ℂ))⁻¹ ^ 3 * B := by
        exact mul_le_mul_of_nonneg_left hPeval (by positivity)
      _ = B * (dist a (z : ℂ))⁻¹ ^ 3 := by ring

end Submission.Helpers
