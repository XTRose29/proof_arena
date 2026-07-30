import Submission.PesinGreenBlock
import Submission.PesinRegularBlock
import Submission.PesinExpansionBlock
import Submission.PesinGreenExpansionBlock

namespace Submission.Helpers

open LeanEval.Dynamics MeasureTheory

def pesinShadowingBlock
    (T T_inv : EucPlane → EucPlane)
  (lam1 lam2 eta : ℝ) (C : ℕ) : Set EucPlane :=
  ((pesinRegularBlock T T_inv lam1 lam2 eta C ∩
      pesinGreenBlock T T_inv lam1 lam2 eta C) ∩
    pesinExpansionBlock T T_inv lam1 lam2 eta C) ∩
    pesinGreenExpansionBlock T T_inv lam1 lam2 eta C

lemma measurableSet_pesinShadowingBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (lam1 lam2 eta : ℝ) (C : ℕ) :
    MeasurableSet (pesinShadowingBlock T T_inv lam1 lam2 eta C) := by
  exact (((measurableSet_pesinRegularBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      lam1 lam2 eta C).inter
    (measurableSet_pesinGreenBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C)).inter
    (measurableSet_pesinExpansionBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C)).inter
    (measurableSet_pesinGreenExpansionBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C)

lemma monotone_pesinShadowingBlock
    (T T_inv : EucPlane → EucPlane) (lam1 lam2 eta : ℝ) :
    Monotone (pesinShadowingBlock T T_inv lam1 lam2 eta) := by
  intro C D hCD x hx
  exact ⟨⟨⟨monotone_pesinRegularBlock T T_inv lam1 lam2 eta hCD hx.1.1.1,
      monotone_pesinGreenBlock T T_inv lam1 lam2 eta hCD hx.1.1.2⟩,
    monotone_pesinExpansionBlock T T_inv lam1 lam2 eta hCD hx.1.2⟩,
    monotone_pesinGreenExpansionBlock T T_inv lam1 lam2 eta hCD hx.2⟩

theorem tendsto_measureReal_compl_pesinShadowingBlock_zero
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
    Filter.Tendsto (fun C : ℕ => mu.real
      (pesinShadowingBlock T T_inv lam1 lam2 eta C)ᶜ)
      Filter.atTop (nhds 0) := by
  have hregular := tendsto_measureReal_compl_pesinRegularBlock_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  have hgreen := tendsto_measureReal_compl_pesinGreenBlock_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hexpansion := tendsto_measureReal_compl_pesinExpansionBlock_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hgreenExpansion :=
    tendsto_measureReal_compl_pesinGreenExpansionBlock_zero
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
        hstable_neg hunstable_neg hrate
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun C =>
      measureReal_nonneg (μ := mu)
        (s := (pesinShadowingBlock T T_inv lam1 lam2 eta C)ᶜ))
    (Filter.Eventually.of_forall fun C => ?_)
    (by simpa [add_assoc] using
      ((hregular.add hgreen).add hexpansion).add hgreenExpansion)
  rw [pesinShadowingBlock, Set.compl_inter]
  calc
    mu.real
        (((pesinRegularBlock T T_inv lam1 lam2 eta C ∩
            pesinGreenBlock T T_inv lam1 lam2 eta C) ∩
              pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ ∪
          (pesinGreenExpansionBlock T T_inv lam1 lam2 eta C)ᶜ) ≤
        mu.real
            ((pesinRegularBlock T T_inv lam1 lam2 eta C ∩
              pesinGreenBlock T T_inv lam1 lam2 eta C) ∩
                pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ +
          mu.real (pesinGreenExpansionBlock
            T T_inv lam1 lam2 eta C)ᶜ :=
      measureReal_union_le _ _
    _ ≤ ((mu.real (pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ +
          mu.real (pesinGreenBlock T T_inv lam1 lam2 eta C)ᶜ) +
        mu.real (pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ) +
        mu.real (pesinGreenExpansionBlock
          T T_inv lam1 lam2 eta C)ᶜ := by
      gcongr
      rw [Set.compl_inter]
      calc
        mu.real
            ((pesinRegularBlock T T_inv lam1 lam2 eta C ∩
              pesinGreenBlock T T_inv lam1 lam2 eta C)ᶜ ∪
                (pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ) ≤
            mu.real
                (pesinRegularBlock T T_inv lam1 lam2 eta C ∩
                  pesinGreenBlock T T_inv lam1 lam2 eta C)ᶜ +
              mu.real (pesinExpansionBlock
                T T_inv lam1 lam2 eta C)ᶜ := measureReal_union_le _ _
        _ ≤ (mu.real (pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ +
              mu.real (pesinGreenBlock T T_inv lam1 lam2 eta C)ᶜ) +
            mu.real (pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ := by
          gcongr
          rw [Set.compl_inter]
          exact measureReal_union_le _ _
    _ = mu.real (pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ +
          (mu.real (pesinGreenBlock T T_inv lam1 lam2 eta C)ᶜ +
            (mu.real (pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ +
              mu.real (pesinGreenExpansionBlock
                T T_inv lam1 lam2 eta C)ᶜ)) := by
      ring

/-- Points whose two balanced endpoints lie in the same fixed Pesin block. -/
def balancedEndpointBlock
    (T T_inv : EucPlane → EucPlane) (lam1 lam2 : ℝ)
    (G : Set EucPlane) (L : ℕ) : Set EucPlane :=
  (T_inv^[balancedBackward lam1 lam2 L]) ⁻¹' G ∩
    (T^[balancedForward lam1 lam2 L]) ⁻¹' G

lemma measurableSet_balancedEndpointBlock
    (T T_inv : EucPlane → EucPlane)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    (lam1 lam2 : ℝ) {G : Set EucPlane} (hG : MeasurableSet G)
    (L : ℕ) :
    MeasurableSet (balancedEndpointBlock T T_inv lam1 lam2 G L) := by
  exact (hG.preimage (hT_inv.iterate _)).inter
    (hG.preimage (hT.iterate _))

lemma measureReal_compl_balancedEndpointBlock_le
    (mu : Measure EucPlane)
    (T T_inv : EucPlane → EucPlane)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (lam1 lam2 : ℝ) {G : Set EucPlane} (hG : MeasurableSet G)
    (L : ℕ) :
    mu.real (balancedEndpointBlock T T_inv lam1 lam2 G L)ᶜ ≤
      2 * mu.real Gᶜ := by
  have hback : mu.real
      ((T_inv^[balancedBackward lam1 lam2 L]) ⁻¹' G)ᶜ =
        mu.real Gᶜ := by
    change (mu ((T_inv^[balancedBackward lam1 lam2 L]) ⁻¹' Gᶜ)).toReal =
      (mu Gᶜ).toReal
    rw [(hT_inv.iterate _).measure_preimage hG.compl.nullMeasurableSet]
  have hforward : mu.real
      ((T^[balancedForward lam1 lam2 L]) ⁻¹' G)ᶜ =
        mu.real Gᶜ := by
    change (mu ((T^[balancedForward lam1 lam2 L]) ⁻¹' Gᶜ)).toReal =
      (mu Gᶜ).toReal
    rw [(hT.iterate _).measure_preimage hG.compl.nullMeasurableSet]
  rw [balancedEndpointBlock, Set.compl_inter]
  calc
    mu.real
        (((T_inv^[balancedBackward lam1 lam2 L]) ⁻¹' G)ᶜ ∪
          ((T^[balancedForward lam1 lam2 L]) ⁻¹' G)ᶜ) ≤
        mu.real ((T_inv^[balancedBackward lam1 lam2 L]) ⁻¹' G)ᶜ +
          mu.real ((T^[balancedForward lam1 lam2 L]) ⁻¹' G)ᶜ :=
      measureReal_union_le _ _
    _ = 2 * mu.real Gᶜ := by rw [hback, hforward]; ring

lemma balancedEndpointBlock_endpoints
    (T T_inv : EucPlane → EucPlane) (lam1 lam2 : ℝ)
    {G : Set EucPlane} {L : ℕ} {x : EucPlane}
    (hx : x ∈ balancedEndpointBlock T T_inv lam1 lam2 G L) :
    T_inv^[balancedBackward lam1 lam2 L] x ∈ G ∧
    T^[balancedForward lam1 lam2 L] x ∈ G :=
  hx

theorem exists_uniform_balancedEndpointBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta gamma : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2)
    (hgamma : 0 < gamma) :
    ∃ C : ℕ,
      let G := pesinShadowingBlock T T_inv lam1 lam2 eta C
      MeasurableSet G ∧
        ∀ L : ℕ,
          MeasurableSet (balancedEndpointBlock T T_inv lam1 lam2 G L) ∧
          mu.real (balancedEndpointBlock T T_inv lam1 lam2 G L)ᶜ < gamma := by
  have hmeasure := tendsto_measureReal_compl_pesinShadowingBlock_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hhalf : 0 < gamma / 2 := div_pos hgamma (by norm_num)
  have hsmall : ∀ᶠ C : ℕ in Filter.atTop,
      mu.real (pesinShadowingBlock T T_inv lam1 lam2 eta C)ᶜ < gamma / 2 :=
    (tendsto_order.1 hmeasure).2 _ hhalf
  obtain ⟨C, hC⟩ := hsmall.exists
  let G := pesinShadowingBlock T T_inv lam1 lam2 eta C
  have hG : MeasurableSet G := measurableSet_pesinShadowingBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right lam1 lam2 eta C
  refine ⟨C, hG, fun L => ⟨
    measurableSet_balancedEndpointBlock
      T T_inv hT.measurable
        (measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right mu hT).measurable
      lam1 lam2 hG L, ?_⟩⟩
  have hle := measureReal_compl_balancedEndpointBlock_le
    mu T T_inv hT
      (measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right mu hT)
      lam1 lam2 hG L
  dsimp [G] at hle ⊢
  nlinarith

end Submission.Helpers
