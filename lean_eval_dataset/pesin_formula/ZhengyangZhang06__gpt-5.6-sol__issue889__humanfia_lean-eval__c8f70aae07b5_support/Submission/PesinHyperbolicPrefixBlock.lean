import Submission.MaximalErgodic
import Submission.PesinBlockFrequency
import Submission.PesinEndpointBlock

namespace Submission.Helpers

open LeanEval.Dynamics MeasureTheory

lemma setBadIndicator_nonneg
    {M : Type*} (G : Set M) (x : M) :
    0 ≤ setBadIndicator G x := by
  classical
  simp only [setBadIndicator, Set.indicator_apply]
  split <;> norm_num

lemma birkhoffSum_setBadIndicator_sub
    {M : Type*} (T : M → M) (G : Set M) (q : ℝ) (n : ℕ) (x : M) :
    birkhoffSum T (fun y => setBadIndicator G y - q) n x =
      badCount (fun j => T^[j] x ∈ G) 0 n - q * n := by
  calc
    birkhoffSum T (fun y => setBadIndicator G y - q) n x =
        birkhoffSum T (setBadIndicator G) n x -
          birkhoffSum T (fun _ => q) n x := by
      change birkhoffSum T (setBadIndicator G - fun _ => q) n x = _
      exact birkhoffSum_sub T (setBadIndicator G) (fun _ => q) n x
    _ = badCount (fun j => T^[j] x ∈ G) 0 n - q * n := by
      rw [badCount_orbit_set_eq_birkhoffSum]
      simp [birkhoffSum]
      ring

/-- Points for which every forward prefix spends at most a `q`-fraction of
its time outside `G`. -/
def maximalForwardBadPrefixBlock
    {M : Type*} (T : M → M) (G : Set M) (q : ℝ) : Set M :=
  (positiveMaxSetInfinite T (fun x => setBadIndicator G x - q))ᶜ

lemma mem_maximalForwardBadPrefixBlock_iff
    {M : Type*} (T : M → M) (G : Set M) (q : ℝ) (x : M) :
    x ∈ maximalForwardBadPrefixBlock T G q ↔
      ∀ n : ℕ,
        badCount (fun j => T^[j] x ∈ G) 0 n ≤ q * n := by
  rw [maximalForwardBadPrefixBlock, Set.mem_compl_iff]
  constructor
  · intro hx n
    by_contra hn
    have hnlt :
        q * n < badCount (fun j => T^[j] x ∈ G) 0 n :=
      lt_of_not_ge hn
    have hnpos : 0 < n := by
      by_contra hnzero
      have hnzero' : n = 0 := Nat.eq_zero_of_not_pos hnzero
      subst n
      simp [badCount] at hnlt
    apply hx
    apply Set.mem_iUnion_of_mem n
    apply Set.mem_iUnion_of_mem n
    apply Set.mem_iUnion_of_mem (Finset.mem_Icc.mpr ⟨hnpos, le_rfl⟩)
    change 0 < birkhoffSum T (fun y => setBadIndicator G y - q) n x
    rw [birkhoffSum_setBadIndicator_sub]
    linarith
  · intro hprefix hx
    obtain ⟨N, hxN⟩ := Set.mem_iUnion.mp hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxN
    obtain ⟨hn, hsum⟩ := Set.mem_iUnion.mp hxn
    have hle := hprefix n
    change 0 < birkhoffSum T (fun y => setBadIndicator G y - q) n x at hsum
    rw [birkhoffSum_setBadIndicator_sub] at hsum
    linarith

lemma measurableSet_maximalForwardBadPrefixBlock
    {M : Type*} [MeasurableSpace M]
    {T : M → M} (hT : Measurable T) {G : Set M}
    (hG : MeasurableSet G) (q : ℝ) :
    MeasurableSet (maximalForwardBadPrefixBlock T G q) := by
  exact (measurableSet_positiveMaxSetInfinite hT
    ((measurable_setBadIndicator hG).sub measurable_const)).compl

theorem mul_measureReal_compl_maximalForwardBadPrefixBlock_le
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    {G : Set M} (hG : MeasurableSet G) {q : ℝ} (hq : 0 ≤ q) :
    q * mu.real (maximalForwardBadPrefixBlock T G q)ᶜ ≤ mu.real Gᶜ := by
  let E := positiveMaxSetInfinite T (fun x => setBadIndicator G x - q)
  have hfmeas : Measurable (fun x => setBadIndicator G x - q) :=
    (measurable_setBadIndicator hG).sub measurable_const
  have hfint : Integrable (fun x => setBadIndicator G x - q) mu :=
    (integrable_setBadIndicator mu hG).sub (integrable_const q)
  have hmax : 0 ≤ ∫ x in E, setBadIndicator G x - q ∂mu :=
    integral_positiveMaxSetInfinite_nonneg_of_lowerBound
      mu T hT (fun x => setBadIndicator G x - q)
        hfmeas hfint hq (fun x => by
          linarith [setBadIndicator_nonneg G x])
  have hsplit :
      (∫ x in E, setBadIndicator G x - q ∂mu) =
        (∫ x in E, setBadIndicator G x ∂mu) - q * mu.real E := by
    rw [integral_sub
      (integrable_setBadIndicator mu hG).integrableOn
      (integrable_const q).integrableOn,
      setIntegral_const, smul_eq_mul]
    ring
  have hbad_le :
      (∫ x in E, setBadIndicator G x ∂mu) ≤
        ∫ x, setBadIndicator G x ∂mu :=
    setIntegral_le_integral (integrable_setBadIndicator mu hG)
      (Filter.Eventually.of_forall fun x => setBadIndicator_nonneg G x)
  rw [hsplit] at hmax
  rw [integral_setBadIndicator mu hG] at hbad_le
  have hbound : q * mu.real E ≤ mu.real Gᶜ := by linarith
  simpa [maximalForwardBadPrefixBlock, E] using hbound

def maximalTwoSidedBadPrefixBlock
    {M : Type*} (T T_inv : M → M) (G : Set M) (q : ℝ) : Set M :=
  maximalForwardBadPrefixBlock T G q ∩
    maximalForwardBadPrefixBlock T_inv G q

lemma measurableSet_maximalTwoSidedBadPrefixBlock
    {M : Type*} [MeasurableSpace M]
    {T T_inv : M → M} (hT : Measurable T) (hT_inv : Measurable T_inv)
    {G : Set M} (hG : MeasurableSet G) (q : ℝ) :
    MeasurableSet (maximalTwoSidedBadPrefixBlock T T_inv G q) := by
  exact (measurableSet_maximalForwardBadPrefixBlock hT hG q).inter
    (measurableSet_maximalForwardBadPrefixBlock hT_inv hG q)

lemma mem_maximalTwoSidedBadPrefixBlock_iff
    {M : Type*} (T T_inv : M → M) (G : Set M) (q : ℝ) (x : M) :
    x ∈ maximalTwoSidedBadPrefixBlock T T_inv G q ↔
      (∀ n : ℕ,
        badCount (fun j => T^[j] x ∈ G) 0 n ≤ q * n) ∧
      ∀ n : ℕ,
        badCount (fun j => T_inv^[j] x ∈ G) 0 n ≤ q * n := by
  simp only [maximalTwoSidedBadPrefixBlock, Set.mem_inter_iff,
    mem_maximalForwardBadPrefixBlock_iff]

theorem mul_measureReal_compl_maximalTwoSidedBadPrefixBlock_le
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    {G : Set M} (hG : MeasurableSet G) {q : ℝ} (hq : 0 ≤ q) :
    q * mu.real (maximalTwoSidedBadPrefixBlock T T_inv G q)ᶜ ≤
      2 * mu.real Gᶜ := by
  have hforward := mul_measureReal_compl_maximalForwardBadPrefixBlock_le
    mu T hT hG hq
  have hbackward := mul_measureReal_compl_maximalForwardBadPrefixBlock_le
    mu T_inv hT_inv hG hq
  rw [maximalTwoSidedBadPrefixBlock, Set.compl_inter]
  calc
    q * mu.real
        ((maximalForwardBadPrefixBlock T G q)ᶜ ∪
          (maximalForwardBadPrefixBlock T_inv G q)ᶜ) ≤
        q * (mu.real (maximalForwardBadPrefixBlock T G q)ᶜ +
          mu.real (maximalForwardBadPrefixBlock T_inv G q)ᶜ) :=
      mul_le_mul_of_nonneg_left (measureReal_union_le _ _) hq
    _ = q * mu.real (maximalForwardBadPrefixBlock T G q)ᶜ +
        q * mu.real (maximalForwardBadPrefixBlock T_inv G q)ᶜ := by ring
    _ ≤ mu.real Gᶜ + mu.real Gᶜ := add_le_add hforward hbackward
    _ = 2 * mu.real Gᶜ := by ring

theorem exists_pesinShadowing_maximalTwoSidedBadPrefixBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta q gamma : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2)
    (hq : 0 < q) (hgamma : 0 < gamma) :
    ∃ C : ℕ,
      let G := pesinShadowingBlock T T_inv lam1 lam2 eta C
      let P := maximalTwoSidedBadPrefixBlock T T_inv G q
      MeasurableSet G ∧ MeasurableSet P ∧ mu.real Pᶜ < gamma := by
  have hmeasure := tendsto_measureReal_compl_pesinShadowingBlock_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hscaled : Filter.Tendsto (fun C : ℕ =>
      2 * mu.real (pesinShadowingBlock T T_inv lam1 lam2 eta C)ᶜ)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hmeasure
  have htarget : 0 < q * gamma := mul_pos hq hgamma
  have hsmall : ∀ᶠ C : ℕ in Filter.atTop,
      2 * mu.real (pesinShadowingBlock T T_inv lam1 lam2 eta C)ᶜ <
        q * gamma :=
    (tendsto_order.1 hscaled).2 _ htarget
  obtain ⟨C, hC⟩ := hsmall.exists
  let G := pesinShadowingBlock T T_inv lam1 lam2 eta C
  let P := maximalTwoSidedBadPrefixBlock T T_inv G q
  have hG : MeasurableSet G := measurableSet_pesinShadowingBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right lam1 lam2 eta C
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hP : MeasurableSet P := measurableSet_maximalTwoSidedBadPrefixBlock
    hT.measurable hT_inv.measurable hG q
  have hle : q * mu.real Pᶜ ≤ 2 * mu.real Gᶜ :=
    mul_measureReal_compl_maximalTwoSidedBadPrefixBlock_le
      mu T T_inv hT hT_inv hG hq.le
  refine ⟨C, hG, hP, ?_⟩
  dsimp [G, P] at hle ⊢
  nlinarith

end Submission.Helpers
