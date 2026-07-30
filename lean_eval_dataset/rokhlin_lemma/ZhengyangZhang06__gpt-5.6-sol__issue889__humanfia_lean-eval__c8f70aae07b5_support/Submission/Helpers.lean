import ChallengeDeps

open LeanEval.Dynamics
open MeasureTheory Set
open Filter
open scoped Topology

namespace Submission.Helpers

noncomputable def orbitCode {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (x : Ω) : ENNReal :=
  ENNReal.ofReal (((orderIsoIooNegOneOne ℝ)
    (MeasureTheory.embeddingReal Ω x) : ℝ) + 1)

lemma orbitCode_measurable {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] : Measurable (orbitCode (Ω := Ω)) := by
  unfold orbitCode
  fun_prop

lemma orbitCode_pos {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (x : Ω) : 0 < orbitCode x := by
  rw [orbitCode, ENNReal.ofReal_pos]
  have hx := ((orderIsoIooNegOneOne ℝ)
    (MeasureTheory.embeddingReal Ω x)).property.1
  linarith

lemma orbitCode_lt_two {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (x : Ω) : orbitCode x < 2 := by
  have hxlow := ((orderIsoIooNegOneOne ℝ)
    (MeasureTheory.embeddingReal Ω x)).property.1
  have hxhigh := ((orderIsoIooNegOneOne ℝ)
    (MeasureTheory.embeddingReal Ω x)).property.2
  rw [orbitCode, ← ENNReal.ofReal_ofNat 2,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 2)]
  linarith

lemma orbitCode_injective {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] : Function.Injective (orbitCode (Ω := Ω)) := by
  intro x y hxy
  rw [orbitCode, orbitCode,
    ENNReal.ofReal_eq_ofReal_iff (le_of_lt (by
      have hx := ((orderIsoIooNegOneOne ℝ)
        (MeasureTheory.embeddingReal Ω x)).property.1
      linarith)) (le_of_lt (by
      have hy := ((orderIsoIooNegOneOne ℝ)
        (MeasureTheory.embeddingReal Ω y)).property.1
      linarith))] at hxy
  have he : MeasureTheory.embeddingReal Ω x =
      MeasureTheory.embeddingReal Ω y := by
    apply (orderIsoIooNegOneOne ℝ).injective
    apply Subtype.ext
    linarith
  exact (MeasureTheory.measurableEmbedding_embeddingReal Ω).injective he

noncomputable def tailInf {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (T : Ω → Ω) (x : Ω) : ENNReal :=
  ⨅ k : ℕ, orbitCode (T^[k] x)

lemma tailInf_measurable {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {T : Ω → Ω} (hT : Measurable T) :
    Measurable (tailInf T) := by
  apply Measurable.iInf
  intro k
  exact orbitCode_measurable.comp (hT.iterate k)

lemma tailInf_le_code {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (T : Ω → Ω) (x : Ω) :
    tailInf T x ≤ orbitCode x := by
  simpa [tailInf] using (iInf_le (fun k : ℕ ↦ orbitCode (T^[k] x)) 0)

lemma tailInf_lt_two {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (T : Ω → Ω) (x : Ω) :
    tailInf T x < 2 :=
  (tailInf_le_code T x).trans_lt (orbitCode_lt_two x)

lemma tailInf_le_iterate {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (T : Ω → Ω) (x : Ω) (j : ℕ) :
    tailInf T x ≤ tailInf T (T^[j] x) := by
  apply le_iInf
  intro k
  rw [tailInf]
  simpa only [Function.iterate_add_apply] using
    (iInf_le (fun m : ℕ ↦ orbitCode (T^[m] x)) (k + j))

lemma tailInf_ae_iterate_eq {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} {T : Ω → Ω}
    [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ) (j : ℕ) :
    tailInf T =ᵐ[μ] fun x ↦ tailInf T (T^[j] x) := by
  apply ae_eq_of_ae_le_of_lintegral_le
  · exact Filter.Eventually.of_forall fun x ↦ tailInf_le_iterate T x j
  · apply ne_of_lt
    calc
      ∫⁻ x, tailInf T x ∂μ ≤ ∫⁻ _ : Ω, (2 : ENNReal) ∂μ :=
        lintegral_mono fun x ↦ (tailInf_lt_two T x).le
      _ = 2 := by simp
      _ < ⊤ := by norm_num
  · exact (tailInf_measurable hT.measurable).comp_aemeasurable
      (hT.measurable.iterate j).aemeasurable
  · rw [(hT.iterate j).lintegral_comp (tailInf_measurable hT.measurable)]

noncomputable def nearMin {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (T : Ω → Ω) (k : ℕ) : Set Ω :=
  {x | orbitCode x <
    tailInf T x + (k : ENNReal)⁻¹}

lemma nearMin_measurable {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {T : Ω → Ω} (hT : Measurable T) (k : ℕ) :
    MeasurableSet (nearMin T k) := by
  exact measurableSet_lt orbitCode_measurable
    ((tailInf_measurable hT).add_const _)

lemma nearMin_antitone {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (T : Ω → Ω) : Antitone (nearMin T) := by
  intro i j hij x hx
  change orbitCode x < tailInf T x + (j : ENNReal)⁻¹ at hx
  change orbitCode x < tailInf T x + (i : ENNReal)⁻¹
  have hij' : (i : ENNReal) ≤ (j : ENNReal) := by
    exact_mod_cast hij
  exact hx.trans_le (add_le_add_right (ENNReal.inv_le_inv.2 hij') _)

noncomputable def exactMin {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (T : Ω → Ω) : Set Ω :=
  {x | orbitCode x = tailInf T x}

lemma exactMin_measurable {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {T : Ω → Ω} (hT : Measurable T) :
    MeasurableSet (exactMin T) :=
  measurableSet_eq_fun orbitCode_measurable (tailInf_measurable hT)

lemma iInter_nearMin {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (T : Ω → Ω) :
    ⋂ k : ℕ, nearMin T k = exactMin T := by
  ext x
  simp only [Set.mem_iInter, nearMin, Set.mem_setOf_eq, exactMin]
  constructor
  · intro hx
    apply le_antisymm
    · have hlim :
          Tendsto (fun k : ℕ ↦
            tailInf T x + (k : ENNReal)⁻¹) atTop
            (𝓝 (tailInf T x)) := by
          simpa only [ENNReal.inv_top, add_zero] using tendsto_const_nhds.add
            (tendsto_inv_iff.2 ENNReal.tendsto_nat_nhds_top)
      exact ge_of_tendsto' hlim fun k ↦ (hx k).le
    · exact tailInf_le_code T x
  · intro hx k
    rw [hx]
    exact ENNReal.lt_add_right (tailInf_lt_two T x).ne_top
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top k))

lemma exactMin_measure_zero {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hap : IsAperiodic T μ) : μ (exactMin T) = 0 := by
  have hinv : ∀ᵐ x ∂μ, ∀ j : ℕ,
      tailInf T x = tailInf T (T^[j] x) :=
    ae_all_iff.2 fun j ↦ tailInf_ae_iterate_eq hT j
  have hrec : ∀ᵐ x ∂μ, x ∈ exactMin T →
      ∃ᶠ j in atTop, T^[j] x ∈ exactMin T :=
    hT.conservative.ae_mem_imp_frequently_image_mem
      (exactMin_measurable hT.measurable).nullMeasurableSet
  have hsub : exactMin T ≤ᵐ[μ] Function.periodicPts T := by
    filter_upwards [hinv, hrec] with x hxinv hxrec hx
    obtain ⟨j, hjmem, hjpos⟩ :=
      ((hxrec hx).and_eventually (eventually_gt_atTop 0)).exists
    apply Function.mk_mem_periodicPts hjpos
    apply orbitCode_injective
    calc
      orbitCode (T^[j] x) = tailInf T (T^[j] x) := hjmem
      _ = tailInf T x := (hxinv j).symm
      _ = orbitCode x := hx.symm
  apply le_antisymm
  · exact (measure_mono_ae hsub).trans (by
      simpa [IsAperiodic] using le_of_eq hap)
  · exact bot_le

lemma tendsto_measure_nearMin_zero {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hap : IsAperiodic T μ) :
    Tendsto (fun k ↦ μ (nearMin T k)) atTop (𝓝 0) := by
  have hlim := tendsto_measure_iInter_atTop
    (fun k ↦ (nearMin_measurable hT.measurable k).nullMeasurableSet)
    (nearMin_antitone T) ⟨0, measure_ne_top μ _⟩
  change Tendsto (μ ∘ nearMin T) atTop (𝓝 0)
  simpa only [iInter_nearMin T,
    exactMin_measure_zero hT hap] using hlim

lemma nearMin_sweep_ae {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (k : ℕ) :
    ∀ᵐ x ∂μ, x ∈ ⋃ j : ℕ, T^[j] ⁻¹' nearMin T k := by
  have hinv : ∀ᵐ x ∂μ, ∀ j : ℕ,
      tailInf T x = tailInf T (T^[j] x) :=
    ae_all_iff.2 fun j ↦ tailInf_ae_iterate_eq hT j
  filter_upwards [hinv] with x hxinv
  have hlt : tailInf T x <
      tailInf T x + (k : ENNReal)⁻¹ :=
    ENNReal.lt_add_right (tailInf_lt_two T x).ne_top
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top k))
  rw [tailInf, iInf_lt_iff] at hlt
  obtain ⟨j, hj⟩ := hlt
  apply Set.mem_iUnion.2
  refine ⟨j, ?_⟩
  change orbitCode (T^[j] x) <
    tailInf T (T^[j] x) + (k : ENNReal)⁻¹
  rwa [← hxinv j]

lemma exists_small_sweep {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hap : IsAperiodic T μ) {δ : ENNReal} (hδ : 0 < δ) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A < δ ∧
      ∀ᵐ x ∂μ, x ∈ ⋃ j : ℕ, T^[j] ⁻¹' A := by
  have hevent : ∀ᶠ k : ℕ in atTop, μ (nearMin T k) < δ :=
    (tendsto_measure_nearMin_zero hT hap)
      (Iio_mem_nhds hδ)
  obtain ⟨k, hk⟩ := hevent.exists
  refine ⟨nearMin T (k + 1), nearMin_measurable hT.measurable _, ?_, ?_⟩
  · exact (measure_mono (nearMin_antitone T (Nat.le_succ k))).trans_lt hk
  · exact nearMin_sweep_ae hT (k + 1)

def hitLevel {Ω : Type*} (T : Ω → Ω) (A : Set Ω) (k : ℕ) : Set Ω :=
  T^[k] ⁻¹' A \ ⋃ j ∈ Finset.range k, T^[j] ⁻¹' A

lemma mem_hitLevel_iff {Ω : Type*} {T : Ω → Ω} {A : Set Ω}
    {k : ℕ} {x : Ω} :
    x ∈ hitLevel T A k ↔
      T^[k] x ∈ A ∧ ∀ j < k, T^[j] x ∉ A := by
  simp [hitLevel]

lemma hitLevel_measurable {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) (k : ℕ) :
    MeasurableSet (hitLevel T A k) := by
  unfold hitLevel
  measurability

lemma hitLevel_pairwiseDisjoint {Ω : Type*} (T : Ω → Ω)
    (A : Set Ω) :
    Set.PairwiseDisjoint Set.univ (hitLevel T A) := by
  intro i _ j _ hij
  change Disjoint (hitLevel T A i) (hitLevel T A j)
  rw [Set.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (mem_hitLevel_iff.1 hxj).2 i hij
      (mem_hitLevel_iff.1 hxi).1
  · exact (mem_hitLevel_iff.1 hxi).2 j hji
      (mem_hitLevel_iff.1 hxj).1

lemma iUnion_hitLevel {Ω : Type*} (T : Ω → Ω) (A : Set Ω) :
    ⋃ k : ℕ, hitLevel T A k = ⋃ k : ℕ, T^[k] ⁻¹' A := by
  classical
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (mem_hitLevel_iff.1 hk).1⟩
  · rintro ⟨k, hk⟩
    let hhit : ∃ k : ℕ, T^[k] x ∈ A := ⟨k, hk⟩
    refine ⟨Nat.find hhit,
      mem_hitLevel_iff.2 ⟨Nat.find_spec hhit, ?_⟩⟩
    intro j hj
    exact fun hjA ↦ (Nat.not_le_of_lt hj)
      (Nat.find_min' hhit hjA)

lemma iterate_mem_hitLevel {Ω : Type*} {T : Ω → Ω}
    {A : Set Ω} {k j : ℕ} {x : Ω} (hx : x ∈ hitLevel T A k)
    (hjk : j ≤ k) :
    T^[j] x ∈ hitLevel T A (k - j) := by
  rw [mem_hitLevel_iff] at hx ⊢
  constructor
  · rw [← Function.iterate_add_apply, Nat.sub_add_cancel hjk]
    exact hx.1
  · intro i hi
    rw [← Function.iterate_add_apply]
    exact hx.2 (i + j) (by omega)

lemma preimage_hitLevel_subset {Ω : Type*} {T : Ω → Ω}
    {A : Set Ω} (k : ℕ) :
    T ⁻¹' hitLevel T A k ⊆ hitLevel T A (k + 1) ∪ A := by
  intro x hx
  by_cases hxA : x ∈ A
  · exact Or.inr hxA
  · apply Or.inl
    change T x ∈ hitLevel T A k at hx
    rw [mem_hitLevel_iff] at hx ⊢
    constructor
    · simpa only [Function.iterate_succ_apply] using hx.1
    · intro j hj
      rcases j with _ | j
      · simpa using hxA
      · simpa only [Function.iterate_succ_apply] using hx.2 j (by omega)

def phase {Ω : Type*} (T : Ω → Ω) (A : Set Ω)
    (n r : ℕ) : Set Ω :=
  ⋃ q : ℕ, hitLevel T A (q * n + r)

lemma phase_measurable {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) (n r : ℕ) :
    MeasurableSet (phase T A n r) :=
  MeasurableSet.iUnion fun q ↦
    hitLevel_measurable hT hA (q * n + r)

lemma phase_pairwiseDisjoint {Ω : Type*} {T : Ω → Ω}
    {A : Set Ω} {n : ℕ} :
    (Finset.range n : Set ℕ).PairwiseDisjoint (phase T A n) := by
  intro r hr s hs hrs
  change Disjoint (phase T A n r) (phase T A n s)
  rw [Set.disjoint_left]
  intro x hxr hxs
  rw [phase, Set.mem_iUnion] at hxr hxs
  obtain ⟨q, hq⟩ := hxr
  obtain ⟨p, hp⟩ := hxs
  have hindex : q * n + r ≠ p * n + s := by
    intro h
    apply hrs
    have hmod : (q * n + r) % n = (p * n + s) % n :=
      congrArg (fun k : ℕ ↦ k % n) h
    rw [Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt (Finset.mem_range.1 hr),
      Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt (Finset.mem_range.1 hs)] at hmod
    exact hmod
  exact Set.disjoint_left.1
    (hitLevel_pairwiseDisjoint T A (Set.mem_univ _) (Set.mem_univ _) hindex)
    hq hp

lemma preimage_phase_subset {Ω : Type*} {T : Ω → Ω}
    {A : Set Ω} {n r : ℕ} (_hr : r + 1 < n) :
    T ⁻¹' phase T A n r ⊆ phase T A n (r + 1) ∪ A := by
  intro x hx
  rw [phase, Set.preimage_iUnion, Set.mem_iUnion] at hx
  obtain ⟨q, hq⟩ := hx
  rcases preimage_hitLevel_subset (T := T) (A := A) (q * n + r) hq with h | h
  · apply Or.inl
    rw [phase, Set.mem_iUnion]
    refine ⟨q, ?_⟩
    simpa only [Nat.add_assoc] using h
  · exact Or.inr h

lemma phase_measure_step {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {A : Set Ω} (hA : MeasurableSet A) {n r : ℕ}
    (hr : r + 1 < n) :
    μ (phase T A n r) ≤ μ (phase T A n (r + 1)) + μ A := by
  rw [← hT.measure_preimage
    (phase_measurable hT.measurable hA n r).nullMeasurableSet]
  calc
    μ (T ⁻¹' phase T A n r) ≤
        μ (phase T A n (r + 1) ∪ A) :=
      measure_mono (preimage_phase_subset hr)
    _ ≤ μ (phase T A n (r + 1)) + μ A :=
      measure_union_le _ _

lemma phase_measure_le_last {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {A : Set Ω} (hA : MeasurableSet A) {n r : ℕ}
    (hn : 0 < n) (hr : r < n) :
    μ (phase T A n r) ≤
      μ (phase T A n (n - 1)) + n • μ A := by
  let f : ℕ → ENNReal :=
    fun s ↦ μ (phase T A n s) + s • μ A
  have hf : MonotoneOn f (Set.Iic (n - 1)) := by
    apply monotoneOn_of_le_succ Set.ordConnected_Iic
    intro s _ hs hs'
    change μ (phase T A n s) + s • μ A ≤
      μ (phase T A n (s + 1)) + (s + 1) • μ A
    have hslt : s + 1 < n := by
      have hs'le : s + 1 ≤ n - 1 := by
        simpa only [Set.mem_Iic, Order.succ_eq_add_one] using hs'
      omega
    have hstep := phase_measure_step hT hA (n := n) (r := s) hslt
    calc
      μ (phase T A n s) + s • μ A ≤
          (μ (phase T A n (s + 1)) + μ A) + s • μ A :=
        add_le_add hstep le_rfl
      _ = μ (phase T A n (s + 1)) + (s + 1) • μ A := by
        simp only [add_nsmul, one_nsmul]
        ac_rfl
  calc
    μ (phase T A n r) ≤ f r := le_add_right le_rfl
    _ ≤ f (n - 1) := hf
      (Set.mem_Iic.2 (Nat.le_pred_of_lt hr))
      (Set.mem_Iic.2 le_rfl) (Nat.le_pred_of_lt hr)
    _ ≤ μ (phase T A n (n - 1)) + n • μ A := by
      dsimp [f]
      gcongr
      omega

def phaseUnion {Ω : Type*} (T : Ω → Ω) (A : Set Ω)
    (n : ℕ) : Set Ω :=
  ⋃ r ∈ Finset.range n, phase T A n r

lemma phaseUnion_measurable {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet (phaseUnion T A n) := by
  exact Finset.measurableSet_biUnion _ fun r _ ↦
    phase_measurable hT hA n r

lemma sweep_subset_phaseUnion {Ω : Type*} {T : Ω → Ω}
    {A : Set Ω} {n : ℕ} (hn : 0 < n) :
    (⋃ k : ℕ, T^[k] ⁻¹' A) ⊆ phaseUnion T A n := by
  rw [← iUnion_hitLevel T A]
  intro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨k, hk⟩ := hx
  rw [phaseUnion, Set.mem_iUnion₂]
  let r := k % n
  refine ⟨r, Finset.mem_range.2 (Nat.mod_lt k hn), ?_⟩
  rw [phase, Set.mem_iUnion]
  refine ⟨k / n, ?_⟩
  simpa [r, Nat.div_add_mod'] using hk

lemma phaseUnion_measure_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A)
    {n : ℕ} (hn : 0 < n)
    (hsweep : ∀ᵐ x ∂μ, x ∈ ⋃ k : ℕ, T^[k] ⁻¹' A) :
    μ (phaseUnion T A n) = 1 := by
  have hfull : ∀ᵐ x ∂μ, x ∈ phaseUnion T A n :=
    hsweep.mono fun x hx ↦ sweep_subset_phaseUnion hn hx
  have := (ae_mem_iff_measure_eq
    (phaseUnion_measurable hT hA n).nullMeasurableSet).1 hfull
  simpa using this

lemma one_le_nsmul_phase_last_add_error {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {A : Set Ω} (hA : MeasurableSet A) {n : ℕ} (hn : 0 < n)
    (hsweep : ∀ᵐ x ∂μ, x ∈ ⋃ k : ℕ, T^[k] ⁻¹' A) :
    1 ≤ n • μ (phase T A n (n - 1)) + n • (n • μ A) := by
  have hmeasure :
      (∑ r ∈ Finset.range n, μ (phase T A n r)) = 1 := by
    rw [← measure_biUnion_finset
      (phase_pairwiseDisjoint (T := T) (A := A))
      (fun r _ ↦ phase_measurable hT.measurable hA n r)]
    exact phaseUnion_measure_one hT.measurable hA hn hsweep
  rw [← hmeasure]
  calc
    (∑ r ∈ Finset.range n, μ (phase T A n r)) ≤
        ∑ r ∈ Finset.range n,
          (μ (phase T A n (n - 1)) + n • μ A) := by
      gcongr with r hr
      exact phase_measure_le_last hT hA hn (Finset.mem_range.1 hr)
    _ = n • μ (phase T A n (n - 1)) + n • (n • μ A) := by
      simp

lemma sum_measure_le_biUnion_of_separated {Ω ι : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (I : Finset ι)
    (s p : ι → Set Ω)
    (hp : ∀ i ∈ I, MeasurableSet (p i))
    (hsp : ∀ i ∈ I, s i ⊆ p i)
    (hpd : (I : Set ι).PairwiseDisjoint p) :
    (∑ i ∈ I, μ (s i)) ≤ μ (⋃ i ∈ I, s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
      have hpI : ∀ i ∈ I, MeasurableSet (p i) :=
        fun i hi ↦ hp i (Finset.mem_insert_of_mem hi)
      have hspI : ∀ i ∈ I, s i ⊆ p i :=
        fun i hi ↦ hsp i (Finset.mem_insert_of_mem hi)
      have hpdI : (I : Set ι).PairwiseDisjoint p := by
        intro i hi j hj hij
        exact hpd (Finset.mem_insert_of_mem hi)
          (Finset.mem_insert_of_mem hj) hij
      have hrest := ih hpI hspI hpdI
      let R : Set Ω := ⋃ i ∈ I, s i
      let U : Set Ω := s a ∪ R
      have hRcompl : R ⊆ (p a)ᶜ := by
        intro x hxR hxp
        change x ∈ ⋃ i ∈ I, s i at hxR
        rw [Set.mem_iUnion₂] at hxR
        obtain ⟨i, hiI, hxi⟩ := hxR
        have hai : a ≠ i := fun hai ↦ ha (hai ▸ hiI)
        exact Set.disjoint_left.1
          (hpd (by simp) (Finset.mem_insert_of_mem hiI) hai)
          hxp (hspI i hiI hxi)
      have hsa : s a ⊆ U ∩ p a :=
        fun x hx ↦ ⟨Or.inl hx, hsp a (by simp) hx⟩
      have hR : R ⊆ U \ p a :=
        fun x hx ↦ ⟨Or.inr hx, hRcompl hx⟩
      calc
        (∑ i ∈ insert a I, μ (s i)) =
            μ (s a) + ∑ i ∈ I, μ (s i) := by simp [ha]
        _ ≤ μ (U ∩ p a) + μ (U \ p a) :=
          add_le_add (measure_mono hsa) (hrest.trans (measure_mono hR))
        _ = μ U := measure_inter_add_sdiff U (hp a (by simp))
        _ = μ (⋃ i ∈ insert a I, s i) := by
          simp [U, R]

lemma towerFloor_subset_phase {Ω : Type*} {T : Ω → Ω}
    {A : Set Ω} {n j : ℕ} (hj : j < n) :
    towerFloor T (phase T A n (n - 1)) j ⊆
      phase T A n (n - 1 - j) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [phase, Set.mem_iUnion] at hx ⊢
  obtain ⟨q, hq⟩ := hx
  refine ⟨q, ?_⟩
  have hjlast : j ≤ n - 1 := Nat.le_pred_of_lt hj
  have hjindex : j ≤ q * n + (n - 1) :=
    hjlast.trans (Nat.le_add_left _ _)
  simpa only [Nat.add_sub_assoc hjlast] using
    iterate_mem_hitLevel hq hjindex

lemma towerFloor_measure_ge_base {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (B : Set Ω) (j : ℕ) :
    μ B ≤ μ (towerFloor T B j) := by
  calc
    μ B ≤ μ (T^[j] ⁻¹' towerFloor T B j) := by
      apply measure_mono
      intro x hx
      exact ⟨x, hx, rfl⟩
    _ ≤ μ (towerFloor T B j) :=
      (hT.iterate j).measure_preimage_le _

lemma phaseTower_isRokhlin {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) {n : ℕ} (hn : 0 < n) :
    IsRokhlinTower T (phase T A n (n - 1)) n := by
  refine ⟨phase_measurable hT hA _ _, ?_⟩
  intro i hi j hj hij
  change Disjoint
    (towerFloor T (phase T A n (n - 1)) i)
    (towerFloor T (phase T A n (n - 1)) j)
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hsubi := towerFloor_subset_phase
    (T := T) (A := A) (Finset.mem_range.1 hi) hxi
  have hsubj := towerFloor_subset_phase
    (T := T) (A := A) (Finset.mem_range.1 hj) hxj
  have hres : n - 1 - i ≠ n - 1 - j := by
    intro h
    apply hij
    calc
      i = n - 1 - (n - 1 - i) :=
        (Nat.sub_sub_self (Nat.le_pred_of_lt
          (Finset.mem_range.1 hi))).symm
      _ = n - 1 - (n - 1 - j) := congrArg (n - 1 - ·) h
      _ = j := Nat.sub_sub_self (Nat.le_pred_of_lt
        (Finset.mem_range.1 hj))
  exact Set.disjoint_left.1
    (phase_pairwiseDisjoint (T := T) (A := A)
      (show n - 1 - i ∈ Finset.range n by
        simp only [Finset.mem_range]
        omega)
      (show n - 1 - j ∈ Finset.range n by
        simp only [Finset.mem_range]
        omega)
      hres)
    hsubi hsubj

lemma phaseTower_measure_ge {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {A : Set Ω} (hA : MeasurableSet A) {n : ℕ} (hn : 0 < n) :
    n • μ (phase T A n (n - 1)) ≤
      μ (towerUnion T (phase T A n (n - 1)) n) := by
  let B := phase T A n (n - 1)
  let floors : ℕ → Set Ω := towerFloor T B
  let separators : ℕ → Set Ω :=
    fun j ↦ phase T A n (n - 1 - j)
  have hsep : (Finset.range n : Set ℕ).PairwiseDisjoint separators := by
    intro i hi j hj hij
    apply phase_pairwiseDisjoint (T := T) (A := A)
    · simpa [separators] using (show n - 1 - i < n by omega)
    · simpa [separators] using (show n - 1 - j < n by omega)
    · dsimp [separators]
      intro h
      apply hij
      calc
        i = n - 1 - (n - 1 - i) :=
          (Nat.sub_sub_self (Nat.le_pred_of_lt
            (Finset.mem_range.1 hi))).symm
        _ = n - 1 - (n - 1 - j) := congrArg (n - 1 - ·) h
        _ = j := Nat.sub_sub_self (Nat.le_pred_of_lt
          (Finset.mem_range.1 hj))
  calc
    n • μ B = ∑ j ∈ Finset.range n, μ B := by simp
    _ ≤ ∑ j ∈ Finset.range n, μ (floors j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact towerFloor_measure_ge_base hT B j
    _ ≤ μ (⋃ j ∈ Finset.range n, floors j) := by
      apply sum_measure_le_biUnion_of_separated
        (p := separators)
      · intro j hj
        exact phase_measurable hT.measurable hA n _
      · intro j hj
        exact towerFloor_subset_phase (T := T) (A := A)
          (Finset.mem_range.1 hj)
      · exact hsep
    _ = μ (towerUnion T B n) := rfl

end Submission.Helpers
