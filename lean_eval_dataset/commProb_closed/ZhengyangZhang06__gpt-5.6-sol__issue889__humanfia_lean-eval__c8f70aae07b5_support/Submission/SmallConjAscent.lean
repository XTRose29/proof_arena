import Submission.Helpers

namespace Submission.Helpers

open scoped Filter Topology

noncomputable section

def commuteFiberEquivCentralizer {G : Type} [Group G] (x : G) :
    {y : G // Commute x y} ≃ Subgroup.centralizer ({x} : Set G) where
  toFun y := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr y.2.eq.symm⟩
  invFun y := ⟨y, (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_conjClass_mul_card_commuteFiber (G : Type) [Group G] [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier * Nat.card {y : G // Commute x y} = Nat.card G := by
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite (MulAction.orbit (ConjAct G) x)
  letI := Fintype.ofFinite (MulAction.stabilizer (ConjAct G) x)
  letI := Fintype.ofFinite (ConjClasses.mk x).carrier
  letI := Fintype.ofFinite {y : G // Commute x y}
  letI := Fintype.ofFinite (Subgroup.centralizer ({x} : Set G))
  have hcentralizer : Fintype.card (Subgroup.centralizer ({x} : Set G)) =
      Fintype.card (MulAction.stabilizer (ConjAct G) x) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact Subgroup.nat_card_centralizer_nat_card_stabilizer x
  have hcardF : Fintype.card (ConjClasses.mk x).carrier *
      Fintype.card {y : G // Commute x y} = Fintype.card G := by
    calc
      Fintype.card (ConjClasses.mk x).carrier * Fintype.card {y : G // Commute x y} =
          Fintype.card (MulAction.orbit (ConjAct G) x) *
            Fintype.card (Subgroup.centralizer ({x} : Set G)) := by
        rw [Fintype.card_congr
          (Equiv.setCongr (ConjAct.orbit_eq_carrier_conjClasses x)).symm,
          Fintype.card_congr (commuteFiberEquivCentralizer x)]
      _ = Fintype.card (MulAction.orbit (ConjAct G) x) *
            Fintype.card (MulAction.stabilizer (ConjAct G) x) := by rw [hcentralizer]
      _ = Fintype.card G :=
        MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x
  simpa [Nat.card_eq_fintype_card] using hcardF

lemma succ_mul_card_commuteFiber_le_card_of_not_mem_smallConjSubgroup
    (G : Type) [Group G] [Finite G] (M : ℕ) {x : G}
    (hx : x ∉ smallConjSubgroup G M) :
    (M + 1) * Nat.card {y : G // Commute x y} ≤ Nat.card G := by
  have hx_not_small : x ∉ SmallConjSet G M := fun hx_small =>
    hx (Subgroup.subset_normalClosure hx_small)
  have hx_class : M + 1 ≤ Nat.card (ConjClasses.mk x).carrier := by
    exact Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hx_not_small)
  rw [← card_conjClass_mul_card_commuteFiber G x]
  exact Nat.mul_le_mul_right _ hx_class

abbrev OutsideFirstCommutingPairs (G : Type) [Group G] (K : Subgroup G) :=
  {p : G × G // Commute p.1 p.2 ∧ p.1 ∉ K}

def outsideFirstCommutingPairsEquivSigma (G : Type) [Group G] (K : Subgroup G) :
    OutsideFirstCommutingPairs G K ≃
      Σ x : {x : G // x ∉ K}, {y : G // Commute x.1 y} where
  toFun p := ⟨⟨p.1.1, p.2.2⟩, ⟨p.1.2, p.2.1⟩⟩
  invFun p := ⟨(p.1.1, p.2.1), p.2.2, p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma succ_mul_card_outsideFirstCommutingPairs_le_sq_card
    (G : Type) [Group G] [Finite G] (M : ℕ) :
    (M + 1) * Nat.card (OutsideFirstCommutingPairs G (smallConjSubgroup G M)) ≤
      Nat.card G ^ 2 := by
  classical
  let K := smallConjSubgroup G M
  letI := Fintype.ofFinite G
  rw [Nat.card_congr (outsideFirstCommutingPairsEquivSigma G K), Nat.card_sigma]
  rw [Finset.mul_sum]
  calc
    ∑ x : {x : G // x ∉ K}, (M + 1) * Nat.card {y : G // Commute x.1 y} ≤
        ∑ _x : {x : G // x ∉ K}, Nat.card G := by
      apply Finset.sum_le_sum
      intro x _hx
      exact succ_mul_card_commuteFiber_le_card_of_not_mem_smallConjSubgroup G M x.2
    _ = Nat.card {x : G // x ∉ K} * Nat.card G := by simp
    _ ≤ Nat.card G * Nat.card G := by
      exact Nat.mul_le_mul_right _ (Finite.card_subtype_le fun x : G => x ∉ K)
    _ = Nat.card G ^ 2 := by ring

abbrev CommutingPairs (G : Type) [Group G] :=
  {p : G × G // Commute p.1 p.2}

noncomputable def splitCommutingPair (G : Type) [Group G] (K : Subgroup G) :
    CommutingPairs G →
      CommutingPairs K ⊕
        (OutsideFirstCommutingPairs G K ⊕ OutsideFirstCommutingPairs G K) := by
  intro p
  by_cases hx : p.1.1 ∈ K
  · by_cases hy : p.1.2 ∈ K
    · exact Sum.inl ⟨(⟨p.1.1, hx⟩, ⟨p.1.2, hy⟩),
        Subtype.ext_iff.mpr p.2.eq⟩
    · exact Sum.inr (Sum.inr ⟨(p.1.2, p.1.1), p.2.symm, hy⟩)
  · exact Sum.inr (Sum.inl ⟨p.1, p.2, hx⟩)

def unsplitCommutingPair (G : Type) [Group G] (K : Subgroup G) :
    CommutingPairs K ⊕
        (OutsideFirstCommutingPairs G K ⊕ OutsideFirstCommutingPairs G K) →
      CommutingPairs G
  | Sum.inl p => ⟨((p.1.1 : G), (p.1.2 : G)), congrArg Subtype.val p.2.eq⟩
  | Sum.inr (Sum.inl p) => ⟨p.1, p.2.1⟩
  | Sum.inr (Sum.inr p) => ⟨(p.1.2, p.1.1), p.2.1.symm⟩

lemma unsplitCommutingPair_splitCommutingPair
    (G : Type) [Group G] (K : Subgroup G) (p : CommutingPairs G) :
    unsplitCommutingPair G K (splitCommutingPair G K p) = p := by
  simp only [splitCommutingPair]
  split <;> rename_i hx
  · split <;> rename_i hy
    · rfl
    · rfl
  · rfl

lemma card_commutingPairs_le_subgroup_add_two_mul_outside
    (G : Type) [Group G] [Finite G] (K : Subgroup G) :
    Nat.card (CommutingPairs G) ≤
      Nat.card (CommutingPairs K) + 2 * Nat.card (OutsideFirstCommutingPairs G K) := by
  have hinj : Function.Injective (splitCommutingPair G K) :=
    Function.LeftInverse.injective (unsplitCommutingPair_splitCommutingPair G K)
  have hcard := Nat.card_le_card_of_injective (splitCommutingPair G K) hinj
  simpa [Nat.card_sum, two_mul] using hcard

lemma commProb_le_smallConjSubgroup_scaled_add_error
    (G : Type) [Group G] [Finite G] (M : ℕ) :
    commProb G ≤
      commProb (smallConjSubgroup G M) /
          ((smallConjSubgroup G M).index : ℚ) ^ 2 +
        2 / ((M + 1 : ℕ) : ℚ) := by
  let K := smallConjSubgroup G M
  let cG := Nat.card (CommutingPairs G)
  let cK := Nat.card (CommutingPairs K)
  let o := Nat.card (OutsideFirstCommutingPairs G K)
  have htotalN : cG ≤ cK + 2 * o := by
    simpa [K, cG, cK, o] using card_commutingPairs_le_subgroup_add_two_mul_outside G K
  have houtN : (M + 1) * o ≤ Nat.card G ^ 2 := by
    simpa [K, o] using succ_mul_card_outsideFirstCommutingPairs_le_sq_card G M
  have hgN : 0 < Nat.card G := Finite.card_pos
  have hKN : 0 < Nat.card K := Finite.card_pos
  have hiN : 0 < K.index := Finite.card_pos
  have hMN : 0 < M + 1 := Nat.succ_pos M
  have hg : (0 : ℚ) < Nat.card G := by exact_mod_cast hgN
  have hK : (0 : ℚ) < Nat.card K := by exact_mod_cast hKN
  have hi : (0 : ℚ) < K.index := by exact_mod_cast hiN
  have hM : (0 : ℚ) < M + 1 := by exact_mod_cast hMN
  have hg2 : (0 : ℚ) < (Nat.card G : ℚ) ^ 2 := sq_pos_of_pos hg
  have htotal : (cG : ℚ) ≤ cK + 2 * o := by exact_mod_cast htotalN
  have hout : ((M + 1 : ℕ) : ℚ) * o ≤ (Nat.card G : ℚ) ^ 2 := by
    exact_mod_cast houtN
  have houtDiv : (o : ℚ) / (Nat.card G : ℚ) ^ 2 ≤ 1 / ((M + 1 : ℕ) : ℚ) := by
    apply (div_le_iff₀ hg2).2
    calc
      (o : ℚ) ≤ (Nat.card G : ℚ) ^ 2 / ((M + 1 : ℕ) : ℚ) := by
        norm_num [Nat.cast_add, Nat.cast_one] at hout ⊢
        apply (le_div_iff₀ hM).2
        nlinarith
      _ = 1 / ((M + 1 : ℕ) : ℚ) * (Nat.card G : ℚ) ^ 2 := by ring
  have htotalDiv : (cG : ℚ) / (Nat.card G : ℚ) ^ 2 ≤
      (cK : ℚ) / (Nat.card G : ℚ) ^ 2 +
        2 * ((o : ℚ) / (Nat.card G : ℚ) ^ 2) := by
    calc
      (cG : ℚ) / (Nat.card G : ℚ) ^ 2 ≤
          ((cK : ℚ) + 2 * o) / (Nat.card G : ℚ) ^ 2 :=
        (div_le_div_iff_of_pos_right hg2).2 htotal
      _ = (cK : ℚ) / (Nat.card G : ℚ) ^ 2 +
          2 * ((o : ℚ) / (Nat.card G : ℚ) ^ 2) := by ring
  have hcard : (Nat.card K : ℚ) * K.index = Nat.card G := by
    exact_mod_cast K.card_mul_index
  have hscale : (cK : ℚ) / (Nat.card G : ℚ) ^ 2 =
      commProb K / (K.index : ℚ) ^ 2 := by
    rw [commProb_def]
    rw [← hcard]
    field_simp
    ring
  rw [commProb_def]
  change (cG : ℚ) / (Nat.card G : ℚ) ^ 2 ≤
    commProb K / (K.index : ℚ) ^ 2 + 2 / ((M + 1 : ℕ) : ℚ)
  calc
    (cG : ℚ) / (Nat.card G : ℚ) ^ 2 ≤
        (cK : ℚ) / (Nat.card G : ℚ) ^ 2 +
          2 * ((o : ℚ) / (Nat.card G : ℚ) ^ 2) := htotalDiv
    _ ≤ (cK : ℚ) / (Nat.card G : ℚ) ^ 2 +
          2 * (1 / ((M + 1 : ℕ) : ℚ)) := by gcongr
    _ = commProb K / (K.index : ℚ) ^ 2 + 2 / ((M + 1 : ℕ) : ℚ) := by
      rw [hscale]
      ring

lemma smallConjSubgroup_commProb_le_scaled_commProb_real
    (G : Type) [Group G] [Finite G] (M : ℕ) :
    (commProb (smallConjSubgroup G M) : ℝ) ≤
      (commProb G : ℝ) * ((smallConjSubgroup G M).index : ℝ) ^ 2 := by
  exact_mod_cast (smallConjSubgroup G M).commProb_subgroup_le

lemma commProb_le_smallConjSubgroup_scaled_add_error_real
    (G : Type) [Group G] [Finite G] (M : ℕ) :
    (commProb G : ℝ) ≤
      (commProb (smallConjSubgroup G M) : ℝ) /
          ((smallConjSubgroup G M).index : ℝ) ^ 2 +
        2 / ((M + 1 : ℕ) : ℝ) := by
  have h := commProb_le_smallConjSubgroup_scaled_add_error G M
  have hcast : ((commProb G : ℚ) : ℝ) ≤
      ((commProb (smallConjSubgroup G M) /
          ((smallConjSubgroup G M).index : ℚ) ^ 2 +
        2 / ((M + 1 : ℕ) : ℚ) : ℚ) : ℝ) := Rat.cast_le.mpr h
  push_cast at hcast
  simpa using hcast

lemma clusterPt_scaled_of_smallConjSubgroup_index_eq
    (W : ℕ → FiniteCommProbWitness) {p : ℝ}
    (hprob : Filter.Tendsto (fun n => (W n).probability) Filter.atTop (𝓝 p))
    (M₀ m : ℕ)
    (hindex : ∀ n,
      let Wn := W n
      letI := Wn.group
      (smallConjSubgroup Wn.carrier (M₀ + n)).index = m) :
    ClusterPt ((m : ℝ) ^ 2 * p) (Filter.principal CommProbRange) := by
  let v : ℕ → ℝ := fun n =>
    let Wn := W n
    letI := Wn.group
    commProb (smallConjSubgroup Wn.carrier (M₀ + n))
  have hm_pos : 0 < m := by
    let W0 := W 0
    letI := W0.group
    letI := W0.finite
    rw [← hindex 0]
    exact Finite.card_pos
  have hm : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := sq_pos_of_pos hm
  have hv_upper : ∀ n, v n ≤ (m : ℝ) ^ 2 * (W n).probability := by
    intro n
    let Wn := W n
    letI := Wn.group
    letI := Wn.finite
    have h := smallConjSubgroup_commProb_le_scaled_commProb_real Wn.carrier (M₀ + n)
    rw [hindex n] at h
    simpa [v, Wn, FiniteCommProbWitness.probability, mul_comm] using h
  have hv_lower : ∀ n,
      (m : ℝ) ^ 2 * (W n).probability -
          (m : ℝ) ^ 2 * (2 / (((M₀ + n + 1 : ℕ) : ℝ))) ≤ v n := by
    intro n
    let Wn := W n
    letI := Wn.group
    letI := Wn.finite
    have h := commProb_le_smallConjSubgroup_scaled_add_error_real Wn.carrier (M₀ + n)
    rw [hindex n] at h
    have h' : (W n).probability - 2 / (((M₀ + n + 1 : ℕ) : ℝ)) ≤
        v n / (m : ℝ) ^ 2 := by
      simpa [v, Wn, FiniteCommProbWitness.probability] using (sub_le_iff_le_add.mpr h)
    have := (le_div_iff₀ hm2).mp h'
    nlinarith
  have herr : Filter.Tendsto
      (fun n : ℕ => (m : ℝ) ^ 2 * (2 / (((M₀ + n + 1 : ℕ) : ℝ))))
      Filter.atTop (𝓝 0) := by
    have hbase : Filter.Tendsto
        (fun n : ℕ => 1 / (((M₀ + n : ℕ) : ℝ) + 1)) Filter.atTop (𝓝 0) := by
      exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (by simpa [Nat.add_comm] using Filter.tendsto_add_atTop_nat M₀)
    have hc := (show Filter.Tendsto (fun _ : ℕ => ((m : ℝ) ^ 2 * 2)) Filter.atTop
      (𝓝 ((m : ℝ) ^ 2 * 2)) from tendsto_const_nhds).mul hbase
    simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one, mul_assoc] using hc
  have hscaled : Filter.Tendsto
      (fun n => (m : ℝ) ^ 2 * (W n).probability) Filter.atTop
      (𝓝 ((m : ℝ) ^ 2 * p)) := tendsto_const_nhds.mul hprob
  have hlower : Filter.Tendsto
      (fun n => (m : ℝ) ^ 2 * (W n).probability -
        (m : ℝ) ^ 2 * (2 / (((M₀ + n + 1 : ℕ) : ℝ)))) Filter.atTop
      (𝓝 ((m : ℝ) ^ 2 * p)) := by
    simpa using hscaled.sub herr
  have hv_tend : Filter.Tendsto v Filter.atTop (𝓝 ((m : ℝ) ^ 2 * p)) :=
    hlower.squeeze hscaled hv_lower hv_upper
  rw [← mem_closure_iff_clusterPt]
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨v, ?_, hv_tend⟩
  intro n
  let Wn := W n
  letI := Wn.group
  letI := Wn.finite
  refine ⟨smallConjSubgroup Wn.carrier (M₀ + n), inferInstance, ?_⟩
  rfl

def FiniteCommProbWitness.smallConjIndex (W : FiniteCommProbWitness) (M : ℕ) : ℕ :=
  letI := W.group
  (smallConjSubgroup W.carrier M).index

lemma smallConjSubgroup_mono (G : Type) [Group G] {M N : ℕ} (hMN : M ≤ N) :
    smallConjSubgroup G M ≤ smallConjSubgroup G N := by
  apply Subgroup.normalClosure_mono
  intro x hx
  exact hx.trans hMN

lemma FiniteCommProbWitness.smallConjIndex_antitone (W : FiniteCommProbWitness) :
    Antitone W.smallConjIndex := by
  intro M N hMN
  letI := W.group
  letI := W.finite
  exact Subgroup.index_antitone (smallConjSubgroup_mono W.carrier hMN)

lemma exists_uniform_smallConjIndex_bound_clusterWitness {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) :
    ∃ M₀ B : ℕ, ∀ n k,
      (clusterWitness hp hp_pos n).smallConjIndex (M₀ + k) ≤ B := by
  obtain ⟨M₀, hM₀⟩ := exists_nat_ge (4 / p)
  obtain ⟨B, hB⟩ := exists_nat_ge (4 / p)
  refine ⟨M₀, B, ?_⟩
  intro n k
  let W := clusterWitness hp hp_pos n
  let M := M₀ + k
  letI := W.group
  letI := W.finite
  have hM₀_nonneg : (0 : ℝ) ≤ M₀ := by positivity
  have hM_ge : (4 / p : ℝ) ≤ M := by
    exact hM₀.trans (by exact_mod_cast (Nat.le_add_right M₀ k))
  have hM_one : (0 : ℝ) < M + 1 := by positivity
  have hrecip : 1 / (((M + 1 : ℕ) : ℝ)) ≤ p / 4 := by
    have hp4 : 0 < p / 4 := by positivity
    rw [Nat.cast_add, Nat.cast_one]
    apply (one_div_le hM_one hp4).2
    calc
      1 / (p / 4) = 4 / p := by field_simp
      _ ≤ M := hM_ge
      _ ≤ (M : ℝ) + 1 := by linarith
  have hdensity : p / 4 * Nat.card W.carrier <
      Nat.card (SmallConjElements W.carrier M) := by
    have hrecip' : 1 / (((M + 1 : ℕ) : ℝ)) ≤ (p / 2) / 2 := by
      convert hrecip using 1
      ring
    have h := half_mul_card_lt_card_smallConjElements_of_lt_commProb
      (G := W.carrier) (r := p / 2) (M := M) hrecip'
      (by simpa [W, FiniteCommProbWitness.probability] using
        clusterWitness_lower hp hp_pos n)
    convert h using 1
    ring
  have hindexR : ((smallConjSubgroup W.carrier M).index : ℝ) < 4 / p := by
    have h := smallConjSubgroup_index_lt_inv_of_density W.carrier
      (show 0 < p / 4 by positivity) hdensity
    convert h using 1
    field_simp
  have hindexB : ((smallConjSubgroup W.carrier M).index : ℝ) < B :=
    hindexR.trans_le hB
  change (smallConjSubgroup W.carrier M).index ≤ B
  exact_mod_cast hindexB.le

lemma smallConjIndex_profile_dichotomy
    (W : ℕ → FiniteCommProbWitness) {p : ℝ}
    (hprob : Filter.Tendsto (fun n => (W n).probability) Filter.atTop (𝓝 p))
    (M₀ B : ℕ) (hbound : ∀ n k, (W n).smallConjIndex (M₀ + k) ≤ B) :
    (∃ q : ℕ, 2 ≤ q ∧
        ClusterPt ((q : ℝ) * p) (Filter.principal CommProbRange)) ∨
      ∃ M : ℕ, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
        Filter.Tendsto (fun n => (W (φ n)).probability) Filter.atTop (𝓝 p) ∧
        ∀ n, (W (φ n)).smallConjIndex M = 1 := by
  classical
  let f : ℕ → (ℕ → Fin (B + 1)) := fun n k =>
    ⟨(W n).smallConjIndex (M₀ + k), Nat.lt_succ_of_le (hbound n k)⟩
  obtain ⟨a, _ha, φ, hφ, hfa⟩ :=
    isSeqCompact_univ (x := f) (fun _ => Set.mem_univ _)
  have hcoord : ∀ k, Filter.Tendsto (fun n => f (φ n) k) Filter.atTop (𝓝 (a k)) := by
    intro k
    exact tendsto_pi_nhds.mp hfa k
  have heq : ∀ k, ∀ᶠ n in Filter.atTop, f (φ n) k = a k := by
    intro k
    have hsingleton : ({a k} : Set (Fin (B + 1))) ∈ 𝓝 (a k) :=
      (discreteTopology_iff_singleton_mem_nhds.mp (by infer_instance)) (a k)
    filter_upwards [(hcoord k).eventually hsingleton] with n hn
    change f (φ n) k = a k at hn
    exact hn
  have ha_step : ∀ k, (a (k + 1)).val ≤ (a k).val := by
    intro k
    obtain ⟨n, hnk, hnks⟩ := ((heq k).and (heq (k + 1))).exists
    rw [← hnk, ← hnks]
    apply (W (φ n)).smallConjIndex_antitone
    omega
  have ha_anti : Antitone (fun k => (a k).val) :=
    antitone_nat_of_succ_le ha_step
  let P : ℕ → Prop := fun r => ∃ k, (a k).val = r
  have hP : ∃ r, P r := ⟨(a 0).val, 0, rfl⟩
  let m := Nat.find hP
  obtain ⟨k₀, hk₀⟩ := Nat.find_spec hP
  have hm_min : ∀ k, m ≤ (a k).val := by
    intro k
    exact Nat.find_min' hP ⟨k, rfl⟩
  have ha_const : ∀ k, k₀ ≤ k → (a k).val = m := by
    intro k hk
    apply Nat.le_antisymm
    · calc
        (a k).val ≤ (a k₀).val := ha_anti hk
        _ = m := hk₀
    · exact hm_min k
  have hm_pos : 0 < m := by
    obtain ⟨n, hn⟩ := (heq k₀).exists
    have hpositive : 0 < (W (φ n)).smallConjIndex (M₀ + k₀) := by
      let Wn := W (φ n)
      letI := Wn.group
      letI := Wn.finite
      exact Finite.card_pos
    rw [show m = (a k₀).val from hk₀.symm, ← congrArg Fin.val hn]
    simpa [f] using hpositive
  by_cases hm_one : m = 1
  · right
    obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp (heq k₀)
    let χ : ℕ → ℕ := fun n => φ (J + n)
    have hχ : StrictMono χ := by
      apply hφ.comp
      intro i j hij
      omega
    refine ⟨M₀ + k₀, χ, hχ, hprob.comp hχ.tendsto_atTop, ?_⟩
    intro n
    have heqJ := hJ (J + n) (Nat.le_add_right J n)
    have hval := congrArg Fin.val heqJ
    calc
      (W (χ n)).smallConjIndex (M₀ + k₀) = (a k₀).val := by
        simpa [χ, f] using hval
      _ = m := hk₀
      _ = 1 := hm_one
  · left
    have hm_two : 2 ≤ m := by omega
    obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ, ∀ k j, N k ≤ j → f (φ j) k = a k := by
      choose N hN using fun k => Filter.eventually_atTop.mp (heq k)
      exact ⟨N, hN⟩
    let ψ : ℕ → ℕ := fun n => Nat.rec (N 0)
      (fun k previous => max (N (k + 1)) (previous + 1)) n
    have hψ_bound : ∀ n, N n ≤ ψ n := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n _ => exact Nat.le_max_left _ _
    have hψ_step : ∀ n, ψ n < ψ (n + 1) := by
      intro n
      change ψ n < max (N (n + 1)) (ψ n + 1)
      exact (Nat.lt_succ_self _).trans_le (Nat.le_max_right _ _)
    have hψ : StrictMono ψ := strictMono_nat_of_lt_succ hψ_step
    have hdiag : ∀ n, f (φ (ψ n)) n = a n := by
      intro n
      exact hN n (ψ n) (hψ_bound n)
    let χ : ℕ → ℕ := fun n => φ (ψ (k₀ + n))
    have hχ : StrictMono χ := by
      apply hφ.comp
      apply hψ.comp
      intro i j hij
      omega
    let W' : ℕ → FiniteCommProbWitness := fun n => W (χ n)
    have hprob' : Filter.Tendsto (fun n => (W' n).probability) Filter.atTop (𝓝 p) := by
      exact hprob.comp hχ.tendsto_atTop
    have hindex' : ∀ n,
        (W' n).smallConjIndex ((M₀ + k₀) + n) = m := by
      intro n
      have hd := congrArg Fin.val (hdiag (k₀ + n))
      have ha := ha_const (k₀ + n) (Nat.le_add_right k₀ n)
      simpa [W', χ, f, FiniteCommProbWitness.smallConjIndex, Nat.add_assoc, ha] using hd
    refine ⟨m ^ 2, Nat.le_trans hm_two (Nat.le_pow (by norm_num : 0 < 2)), ?_⟩
    have hc := clusterPt_scaled_of_smallConjSubgroup_index_eq W' hprob' (M₀ + k₀) m
      (by
        intro n
        simpa [FiniteCommProbWitness.smallConjIndex] using hindex' n)
    simpa [Nat.cast_pow] using hc

lemma clusterPt_ascent_or_fixed_smallConjIndex_one {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) :
    (∃ q : ℕ, 2 ≤ q ∧
        ClusterPt ((q : ℝ) * p) (Filter.principal CommProbRange)) ∨
      ∃ M : ℕ, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
        Filter.Tendsto
          (fun n => (clusterWitness hp hp_pos (φ n)).probability) Filter.atTop (𝓝 p) ∧
        ∀ n, (clusterWitness hp hp_pos (φ n)).smallConjIndex M = 1 := by
  obtain ⟨M₀, B, hbound⟩ := exists_uniform_smallConjIndex_bound_clusterWitness hp hp_pos
  exact smallConjIndex_profile_dichotomy (fun n => clusterWitness hp hp_pos n)
    (tendsto_clusterWitness_probability hp hp_pos) M₀ B hbound

lemma isClosed_CommProbRange_of_fixed_smallConjIndex_one
    (hfixed : ∀ {p : ℝ},
      (hp : ClusterPt p (Filter.principal CommProbRange)) → (hp_pos : 0 < p) →
      (∃ M : ℕ, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
        Filter.Tendsto
          (fun n => (clusterWitness hp hp_pos (φ n)).probability) Filter.atTop (𝓝 p) ∧
        ∀ n, (clusterWitness hp hp_pos (φ n)).smallConjIndex M = 1) →
      p ∈ CommProbRange ∨
        ∃ q : ℕ, 2 ≤ q ∧
          ClusterPt ((q : ℝ) * p) (Filter.principal CommProbRange)) :
    IsClosed CommProbRange := by
  apply isClosed_CommProbRange_of_cluster_point_ascent
  intro p hp hp_pos
  rcases clusterPt_ascent_or_fixed_smallConjIndex_one hp hp_pos with hascent | hfixedBranch
  · exact Or.inr hascent
  · exact hfixed hp hp_pos hfixedBranch

end
end Submission.Helpers
