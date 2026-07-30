import Submission.ComponentAdjugate

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

def twoSidedOrbitCore
    (T T_inv : EucPlane → EucPlane) (s : Set EucPlane) : Set EucPlane :=
  {x | ∀ n : ℕ, T^[n] x ∈ s ∧ T_inv^[n] x ∈ s}

lemma measurableSet_twoSidedOrbitCore
    (T T_inv : EucPlane → EucPlane)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    {s : Set EucPlane} (hs : MeasurableSet s) :
    MeasurableSet (twoSidedOrbitCore T T_inv s) := by
  have heq : twoSidedOrbitCore T T_inv s =
      ⋂ n : ℕ, (T^[n]) ⁻¹' s ∩ (T_inv^[n]) ⁻¹' s := by
    ext x
    simp [twoSidedOrbitCore]
  rw [heq]
  exact MeasurableSet.iInter fun n =>
    (hs.preimage (hT.iterate n)).inter (hs.preimage (hT_inv.iterate n))

lemma twoSidedOrbitCore_compl_measure_zero
    (mu : Measure EucPlane)
    (T T_inv : EucPlane → EucPlane)
    (hT : Measure.QuasiMeasurePreserving T mu mu)
    (hT_inv : Measure.QuasiMeasurePreserving T_inv mu mu)
    {s : Set EucPlane} (hs : mu sᶜ = 0) :
    mu (twoSidedOrbitCore T T_inv s)ᶜ = 0 := by
  apply mem_ae_iff.mp
  have hs_ae : ∀ᵐ x ∂mu, x ∈ s := mem_ae_iff.mpr hs
  have hforward := ae_all_iterates_of_ae hT hs_ae
  have hbackward := ae_all_iterates_of_ae hT_inv hs_ae
  filter_upwards [hforward, hbackward] with x hxf hxb
  exact fun n => ⟨hxf n, hxb n⟩

lemma twoSidedOrbitCore_forward_mem
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    {s : Set EucPlane} {x : EucPlane}
    (hx : x ∈ twoSidedOrbitCore T T_inv s) :
    T x ∈ twoSidedOrbitCore T T_inv s := by
  intro n
  constructor
  · simpa [Function.iterate_succ_apply] using (hx (n + 1)).1
  · cases n with
    | zero => simpa using (hx 1).1
    | succ n =>
        rw [Function.iterate_succ_apply, hT_left x]
        exact (hx n).2

lemma twoSidedOrbitCore_backward_mem
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    {s : Set EucPlane} {x : EucPlane}
    (hx : x ∈ twoSidedOrbitCore T T_inv s) :
    T_inv x ∈ twoSidedOrbitCore T T_inv s := by
  intro n
  constructor
  · cases n with
    | zero => simpa using (hx 1).2
    | succ n =>
        rw [Function.iterate_succ_apply, hT_right x]
        exact (hx n).1
  · simpa [Function.iterate_succ_apply] using (hx (n + 1)).2

lemma image_twoSidedOrbitCore
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (s : Set EucPlane) :
    T '' twoSidedOrbitCore T T_inv s = twoSidedOrbitCore T T_inv s := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact twoSidedOrbitCore_forward_mem T T_inv hT_left hx
  · intro x hx
    exact ⟨T_inv x,
      twoSidedOrbitCore_backward_mem T T_inv hT_right hx, hT_right x⟩

lemma component_fderiv_inverse_covariant_of_forward
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (S : EucPlane → EucPlane →L[ℝ] EucPlane) (x : EucPlane)
    (hcov : S x ∘L fderiv ℝ T (T_inv x) =
      fderiv ℝ T (T_inv x) ∘L S (T_inv x)) :
    S (T_inv x) ∘L fderiv ℝ T_inv x =
      fderiv ℝ T_inv x ∘L S x := by
  let A := fderiv ℝ T (T_inv x)
  let B := fderiv ℝ T_inv x
  have hT_diff : Differentiable ℝ T :=
    hT_smooth.differentiable (by norm_num)
  have hT_inv_diff : Differentiable ℝ T_inv :=
    hT_inv_smooth.differentiable (by norm_num)
  have hBA : B ∘L A = ContinuousLinearMap.id ℝ EucPlane := by
    dsimp [A, B]
    calc
      fderiv ℝ T_inv x ∘L fderiv ℝ T (T_inv x) =
          fderiv ℝ T_inv (T (T_inv x)) ∘L
            fderiv ℝ T (T_inv x) := by rw [hT_right x]
      _ =
          fderiv ℝ (T_inv ∘ T) (T_inv x) := by
        rw [fderiv_comp]
        · exact hT_inv_diff.differentiableAt
        · exact hT_diff.differentiableAt
      _ = ContinuousLinearMap.id ℝ EucPlane := by
        rw [hT_left.comp_eq_id, fderiv_id]
  have hAB : A ∘L B = ContinuousLinearMap.id ℝ EucPlane := by
    dsimp [A, B]
    calc
      fderiv ℝ T (T_inv x) ∘L fderiv ℝ T_inv x =
          fderiv ℝ (T ∘ T_inv) x := by
        rw [fderiv_comp]
        · exact hT_diff.differentiableAt
        · exact hT_inv_diff.differentiableAt
      _ = ContinuousLinearMap.id ℝ EucPlane := by
        rw [hT_right.comp_eq_id, fderiv_id]
  change S (T_inv x) ∘L B = B ∘L S x
  calc
    S (T_inv x) ∘L B =
        (B ∘L A) ∘L (S (T_inv x) ∘L B) := by rw [hBA]; simp
    _ = B ∘L ((A ∘L S (T_inv x)) ∘L B) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = B ∘L ((S x ∘L A) ∘L B) := by rw [hcov]
    _ = (B ∘L S x) ∘L (A ∘L B) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = B ∘L S x := by rw [hAB]; simp

lemma exists_measurable_full_subset_of_ae
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) {p : M → Prop} (hp : ∀ᵐ x ∂mu, p x) :
    ∃ s : Set M, MeasurableSet s ∧ mu sᶜ = 0 ∧ ∀ x ∈ s, p x := by
  obtain ⟨s, hs_ae, hs, hsp⟩ := hp.exists_measurable_mem
  exact ⟨s, hs, mem_ae_iff.mp hs_ae, hsp⟩

theorem exists_pesinStructuralCarrier
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∃ carrier : Set EucPlane,
      MeasurableSet carrier ∧ mu carrierᶜ = 0 ∧ T '' carrier = carrier ∧
      carrier ⊆ K ∧
      (∀ x ∈ carrier, SourceSplittingData T T_inv x) ∧
      (∀ x ∈ carrier,
        lyapunovStableComponent T T_inv (T x) ∘L fderiv ℝ T x =
            fderiv ℝ T x ∘L lyapunovStableComponent T T_inv x ∧
        lyapunovUnstableComponent T T_inv (T x) ∘L fderiv ℝ T x =
            fderiv ℝ T x ∘L lyapunovUnstableComponent T T_inv x) ∧
      ∀ x ∈ carrier,
        (lyapunovStableComponent T T_inv x).det = 0 ∧
        (lyapunovUnstableComponent T T_inv x).det = 0 := by
  have hsource := ae_sourceSplittingData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta (by linarith)
      hstable_neg hunstable_neg hrate
  have hcov := ae_lyapunovComponents_fderiv_covariant
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hdet := ae_lyapunovComponents_det_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  have hp : ∀ᵐ x ∂mu,
      x ∈ K ∧ SourceSplittingData T T_inv x ∧
        (lyapunovStableComponent T T_inv (T x) ∘L fderiv ℝ T x =
            fderiv ℝ T x ∘L lyapunovStableComponent T T_inv x ∧
          lyapunovUnstableComponent T T_inv (T x) ∘L fderiv ℝ T x =
            fderiv ℝ T x ∘L lyapunovUnstableComponent T T_inv x) ∧
        ((lyapunovStableComponent T T_inv x).det = 0 ∧
          (lyapunovUnstableComponent T T_inv x).det = 0) := by
    filter_upwards [mem_ae_iff.mpr hmu_supp, hsource, hcov, hdet]
      with x hxK hxsource hxcov hxdet
    exact ⟨hxK, hxsource, hxcov, hxdet⟩
  obtain ⟨s, hs, hmus, hsp⟩ := exists_measurable_full_subset_of_ae mu hp
  let carrier := twoSidedOrbitCore T T_inv s
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  refine ⟨carrier,
    measurableSet_twoSidedOrbitCore T T_inv hT.measurable hT_inv.measurable hs,
    twoSidedOrbitCore_compl_measure_zero mu T T_inv
      hT.quasiMeasurePreserving hT_inv.quasiMeasurePreserving hmus,
    image_twoSidedOrbitCore T T_inv hT_left hT_right s, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxs : x ∈ s := by simpa using (hx 0).1
    exact (hsp x hxs).1
  · intro x hx
    have hxs : x ∈ s := by simpa using (hx 0).1
    exact (hsp x hxs).2.1
  · intro x hx
    have hxs : x ∈ s := by simpa using (hx 0).1
    exact (hsp x hxs).2.2.1
  · intro x hx
    have hxs : x ∈ s := by simpa using (hx 0).1
    exact (hsp x hxs).2.2.2

lemma stableComponent_fderiv_iterate_covariant_on_structuralCarrier
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    (S : EucPlane → EucPlane →L[ℝ] EucPlane)
    {carrier : Set EucPlane} (hcarrier : T '' carrier = carrier)
    (hcov : ∀ x ∈ carrier,
      S (T x) ∘L fderiv ℝ T x = fderiv ℝ T x ∘L S x)
    {x : EucPlane} (hx : x ∈ carrier) (n : ℕ) :
    S (T^[n] x) ∘L fderiv ℝ (T^[n]) x =
      fderiv ℝ (T^[n]) x ∘L S x := by
  apply component_fderiv_iterate_covariant T hT_smooth S x
  intro k
  have hk : T^[k] x ∈ carrier := by
    rw [← image_iterate_eq_of_image_eq T hcarrier k]
    exact ⟨x, hx, rfl⟩
  simpa only [Function.iterate_succ_apply'] using hcov (T^[k] x) hk

lemma component_fderiv_inverse_iterate_covariant_on_structuralCarrier
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (S : EucPlane → EucPlane →L[ℝ] EucPlane)
    {carrier : Set EucPlane} (hcarrier : T '' carrier = carrier)
    (hcov : ∀ x ∈ carrier,
      S (T x) ∘L fderiv ℝ T x = fderiv ℝ T x ∘L S x)
    {x : EucPlane} (hx : x ∈ carrier) (n : ℕ) :
    S (T_inv^[n] x) ∘L fderiv ℝ (T_inv^[n]) x =
      fderiv ℝ (T_inv^[n]) x ∘L S x := by
  have hcarrier_inv : T_inv '' carrier = carrier :=
    inverse_image_eq_of_image_eq hT_left hcarrier
  apply component_fderiv_iterate_covariant T_inv hT_inv_smooth S x
  intro k
  let z := T_inv^[k] x
  have hz : z ∈ carrier := by
    rw [← image_iterate_eq_of_image_eq T_inv hcarrier_inv k]
    exact ⟨x, hx, rfl⟩
  have hzinv : T_inv z ∈ carrier := by
    rw [← hcarrier_inv]
    exact ⟨z, hz, rfl⟩
  have hforward :
      S z ∘L fderiv ℝ T (T_inv z) =
        fderiv ℝ T (T_inv z) ∘L S (T_inv z) := by
    have hz_cov := hcov (T_inv z) hzinv
    rw [hT_right z] at hz_cov
    exact hz_cov
  simpa only [z, Function.iterate_succ_apply'] using
    component_fderiv_inverse_covariant_of_forward
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right S z hforward

end Submission.Helpers
