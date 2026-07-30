import Mathlib

namespace Submission.Helpers

open scoped Filter Topology

noncomputable section

def CommProbRange : Set ℝ := {p : ℝ | ∃ (G : Type) (_ : Group G), commProb G = p}

lemma commProb_nonneg (G : Type) [Group G] : 0 ≤ (commProb G : ℝ) := by
  exact_mod_cast (show (0 : ℚ) ≤ commProb G by
    rw [commProb_def]
    exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

lemma commProb_le_one_real (G : Type) [Group G] : (commProb G : ℝ) ≤ 1 := by
  cases finite_or_infinite G with
  | inl hG =>
      haveI := hG
      exact_mod_cast (commProb_le_one (M := G))
  | inr hG =>
      haveI := hG
      simp [commProb_eq_zero_of_infinite]

lemma mem_commProbRange_nonneg {p : ℝ} (hp : p ∈ CommProbRange) : 0 ≤ p := by
  rcases hp with ⟨G, hG, hp⟩
  letI := hG
  rw [← hp]
  exact commProb_nonneg G

lemma mem_commProbRange_le_one {p : ℝ} (hp : p ∈ CommProbRange) : p ≤ 1 := by
  rcases hp with ⟨G, hG, hp⟩
  letI := hG
  rw [← hp]
  exact commProb_le_one_real G

lemma exists_mem_CommProbRange_abs_sub_lt_of_clusterPt {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ CommProbRange, |q - p| < ε := by
  rw [ClusterPt] at hp
  obtain ⟨q, hqball, hqmem⟩ :=
    (Filter.inf_neBot_iff.mp hp) (Metric.ball_mem_nhds p hε)
      (show CommProbRange ∈ Filter.principal CommProbRange by simp)
  refine ⟨q, hqmem, ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hqball

lemma exists_pos_mem_CommProbRange_near_of_clusterPt_pos {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) :
    ∃ q ∈ CommProbRange, p / 2 < q ∧ |q - p| < p / 2 := by
  obtain ⟨q, hqmem, hqdist⟩ :=
    exists_mem_CommProbRange_abs_sub_lt_of_clusterPt hp (half_pos hp_pos)
  refine ⟨q, hqmem, ?_, hqdist⟩
  rcases abs_lt.mp hqdist with hlow
  linarith

lemma exists_finite_witness_of_pos_mem_CommProbRange {q : ℝ}
    (hq : q ∈ CommProbRange) (hq_pos : 0 < q) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), commProb G = q := by
  rcases hq with ⟨G, hG, hprob⟩
  letI := hG
  cases finite_or_infinite G with
  | inl hfinite =>
      exact ⟨G, hG, hfinite, hprob⟩
  | inr hinfinite =>
      haveI := hinfinite
      rw [← hprob, commProb_eq_zero_of_infinite] at hq_pos
      norm_num at hq_pos

lemma exists_finite_witness_abs_sub_lt_of_clusterPt_pos {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : ℝ) (G : Type) (_ : Group G) (_ : Finite G),
      p / 2 < q ∧ |q - p| < ε ∧ commProb G = q := by
  have hδ : 0 < min ε (p / 2) := lt_min hε (half_pos hp_pos)
  obtain ⟨q, hqmem, hqdistδ⟩ :=
    exists_mem_CommProbRange_abs_sub_lt_of_clusterPt hp hδ
  have hqdist : |q - p| < ε := hqdistδ.trans_le (min_le_left ε (p / 2))
  have hqdist_half : |q - p| < p / 2 := hqdistδ.trans_le (min_le_right ε (p / 2))
  have hq_lower : p / 2 < q := by
    rcases abs_lt.mp hqdist_half with ⟨hlow, _⟩
    linarith
  obtain ⟨G, hG, hfinite, hprob⟩ :=
    exists_finite_witness_of_pos_mem_CommProbRange hqmem (lt_trans (half_pos hp_pos) hq_lower)
  exact ⟨q, G, hG, hfinite, hq_lower, hqdist, hprob⟩

lemma exists_finite_witness_near_of_clusterPt_pos {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) :
    ∃ (q : ℝ) (G : Type) (_ : Group G) (_ : Finite G),
      p / 2 < q ∧ |q - p| < p / 2 ∧ commProb G = q := by
  exact exists_finite_witness_abs_sub_lt_of_clusterPt_pos hp hp_pos (half_pos hp_pos)

structure FiniteCommProbWitness where
  carrier : Type
  group : Group carrier
  finite : Finite carrier

def FiniteCommProbWitness.probability (W : FiniteCommProbWitness) : ℝ :=
  letI := W.group
  commProb W.carrier

def FiniteCommProbWitness.centerIndex (W : FiniteCommProbWitness) : ℕ :=
  letI := W.group
  (Subgroup.center W.carrier).index

noncomputable def centerPart {G : Type} [Group G] (x : G) : Subgroup.center G :=
  ⟨(Quotient.out (x : G ⧸ Subgroup.center G))⁻¹ * x, by
    rw [← QuotientGroup.eq]
    simp⟩

lemma out_mul_centerPart {G : Type} [Group G] (x : G) :
    Quotient.out (x : G ⧸ Subgroup.center G) * centerPart x = x := by
  simp [centerPart]

lemma centerPart_out_mul {G : Type} [Group G] (q : G ⧸ Subgroup.center G)
    (z : Subgroup.center G) :
    centerPart (Quotient.out q * z) = z := by
  apply Subtype.ext
  simp [centerPart]

lemma quotient_out_mul_center {G : Type} [Group G] (q : G ⧸ Subgroup.center G)
    (z : Subgroup.center G) :
    ((Quotient.out q * z : G) : G ⧸ Subgroup.center G) = q := by
  calc
    ((Quotient.out q * z : G) : G ⧸ Subgroup.center G) =
        Quotient.mk'' (Quotient.out q) := by simp
    _ = q := Quotient.out_eq q

lemma commute_mul_center_iff {G : Type} [Group G] (x y : G)
    (z w : Subgroup.center G) :
    Commute (x * z) (y * w) ↔ Commute x y := by
  have hz_y : Commute (z : G) y :=
    (Subgroup.mem_center_iff.mp z.2 y).symm
  have hw_x : Commute (w : G) x :=
    (Subgroup.mem_center_iff.mp w.2 x).symm
  have hz_w : Commute (z : G) w :=
    (Subgroup.mem_center_iff.mp z.2 w).symm
  constructor
  · intro h
    have hcancel : x * y * ((z : G) * w) = y * x * ((z : G) * w) := by
      calc
        x * y * ((z : G) * w) = x * z * (y * w) :=
          (hz_y.mul_mul_mul_comm x w).symm
        _ = y * w * (x * z) := h.eq
        _ = y * x * ((w : G) * z) := hw_x.mul_mul_mul_comm y z
        _ = y * x * ((z : G) * w) := by rw [hz_w.eq]
    exact mul_right_cancel hcancel
  · intro h
    calc
      x * z * (y * w) = x * y * ((z : G) * w) := hz_y.mul_mul_mul_comm x w
      _ = y * x * ((z : G) * w) := by rw [h.eq]
      _ = y * x * ((w : G) * z) := by rw [hz_w.eq]
      _ = y * w * (x * z) := (hw_x.mul_mul_mul_comm y z).symm

abbrev CenterCommutingQuotientPairs (G : Type) [Group G] :=
  {p : (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) //
    Commute (Quotient.out p.1) (Quotient.out p.2)}

noncomputable def commutingPairsEquivCenter {G : Type} [Group G] :
    {p : G × G // Commute p.1 p.2} ≃
      CenterCommutingQuotientPairs G × (Subgroup.center G × Subgroup.center G) where
  toFun p :=
    let qx : G ⧸ Subgroup.center G := p.1.1
    let qy : G ⧸ Subgroup.center G := p.1.2
    let zx := centerPart p.1.1
    let zy := centerPart p.1.2
    ⟨⟨(qx, qy), by
      apply (commute_mul_center_iff (Quotient.out qx) (Quotient.out qy) zx zy).mp
      simpa [qx, qy, zx, zy, out_mul_centerPart] using p.2⟩, (zx, zy)⟩
  invFun p :=
    ⟨(Quotient.out p.1.1.1 * p.2.1, Quotient.out p.1.1.2 * p.2.2),
      (commute_mul_center_iff _ _ _ _).mpr p.1.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact out_mul_centerPart p.1.1
    · exact out_mul_centerPart p.1.2
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact quotient_out_mul_center p.1.1.1 p.2.1
      · exact quotient_out_mul_center p.1.1.2 p.2.2
    · apply Prod.ext
      · exact centerPart_out_mul p.1.1.1 p.2.1
      · exact centerPart_out_mul p.1.1.2 p.2.2

lemma commProb_eq_centerQuotientRatio (G : Type) [Group G] [Finite G] :
    commProb G = Nat.card (CenterCommutingQuotientPairs G) /
      ((Subgroup.center G).index : ℚ) ^ 2 := by
  rw [commProb_def]
  rw [Nat.card_congr commutingPairsEquivCenter, Nat.card_prod, Nat.card_prod]
  rw [← (Subgroup.center G).card_mul_index]
  push_cast
  have hcenter : (Nat.card (Subgroup.center G) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  field_simp

lemma card_centerCommutingQuotientPairs_le (G : Type) [Group G] [Finite G] :
    Nat.card (CenterCommutingQuotientPairs G) ≤ (Subgroup.center G).index ^ 2 := by
  simpa [Nat.card_prod, pow_two, (Subgroup.center G).index_eq_card] using
    (Finite.card_subtype_le fun p :
      (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) =>
        Commute (Quotient.out p.1) (Quotient.out p.2))

lemma twice_card_conjClasses_le_card_add_center (G : Type) [Group G] [Finite G] :
    2 * Nat.card (ConjClasses G) ≤ Nat.card G + Nat.card (Subgroup.center G) := by
  classical
  let nc : Set (ConjClasses G) := ConjClasses.noncenter G
  have hcompl : ncᶜ.ncard = Nat.card (Subgroup.center G) := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr
      (Set.BijOn.equiv ConjClasses.mk (ConjClasses.mk_bijOn G))).symm
  have hclasses : Nat.card (ConjClasses G) = nc.ncard + Nat.card (Subgroup.center G) := by
    rw [← hcompl, ← Set.ncard_add_ncard_compl nc, add_comm]
  have hnoncenter : 2 * nc.ncard ≤ ∑ᶠ x ∈ nc, Nat.card x.carrier := by
    letI := Fintype.ofFinite (ConjClasses G)
    have hfinite : nc.Finite := Set.toFinite nc
    have hsum : 2 * nc.ncard ≤ ∑ x ∈ nc.toFinset, Nat.card x.carrier := by
      calc
        2 * nc.ncard = ∑ x ∈ nc.toFinset, 2 := by
          rw [Set.ncard_eq_toFinset_card nc hfinite, Nat.mul_comm]
          simp
        _ ≤ ∑ x ∈ nc.toFinset, Nat.card x.carrier := by
          apply Finset.sum_le_sum
          intro x hx
          have hx' : x ∈ nc := Set.mem_toFinset.mp hx
          rw [Nat.card_coe_set_eq]
          exact Nat.succ_le_iff.mpr
            (Set.one_lt_ncard_iff_nontrivial.mpr ((ConjClasses.mem_noncenter x).mp hx'))
    rw [finsum_cond_eq_sum_of_cond_iff (fun x => Nat.card x.carrier)
      (t := nc.toFinset) (by intro x hx; simp)]
    exact hsum
  have hclassEq := Group.nat_card_center_add_sum_card_noncenter_eq_card G
  have hclassEq' : Nat.card (Subgroup.center G) +
      ∑ᶠ x ∈ nc, Nat.card x.carrier = Nat.card G := by
    simpa [nc] using hclassEq
  rw [hclasses]
  omega

abbrev SmallConjClasses (G : Type) [Group G] (M : ℕ) :=
  {x : ConjClasses G // Nat.card x.carrier ≤ M}

abbrev SmallConjElements (G : Type) [Group G] (M : ℕ) :=
  {g : G // Nat.card (ConjClasses.mk g).carrier ≤ M}

lemma mul_ncard_largeConjClasses_le_card (G : Type) [Group G] [Finite G] (M : ℕ) :
    (M + 1) * ({x : ConjClasses G | M < Nat.card x.carrier}).ncard ≤ Nat.card G := by
  classical
  letI := Fintype.ofFinite (ConjClasses G)
  let large : Set (ConjClasses G) := {x | M < Nat.card x.carrier}
  have hlarge : large.Finite := Set.toFinite large
  have hsum : ∑ x ∈ large.toFinset, (M + 1) ≤
      ∑ x ∈ large.toFinset, Nat.card x.carrier := by
    apply Finset.sum_le_sum
    intro x hx
    have hx' : x ∈ large := by simpa using hx
    exact Nat.succ_le_iff.mpr hx'
  calc
    (M + 1) * ({x : ConjClasses G | M < Nat.card x.carrier}).ncard =
        ∑ x ∈ large.toFinset, (M + 1) := by
      rw [show {x : ConjClasses G | M < Nat.card x.carrier} = large from rfl,
        Nat.mul_comm]
      simp only [Finset.sum_const, Set.toFinset_card, nsmul_eq_mul]
      rw [← Nat.card_coe_set_eq large, Nat.card_eq_fintype_card]
      rfl
    _ ≤ ∑ x ∈ large.toFinset, Nat.card x.carrier := hsum
    _ ≤ ∑ x : ConjClasses G, Nat.card x.carrier := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simp
      · intro i hi _
        exact Nat.zero_le _
    _ = Nat.card G := by
      simpa [finsum_eq_sum_of_fintype] using Group.sum_card_conj_classes_eq_card G

noncomputable def conjClassRep {G : Type} [Group G] (x : ConjClasses G) : G :=
  Classical.choose (ConjClasses.exists_rep x)

lemma mk_conjClassRep {G : Type} [Group G] (x : ConjClasses G) :
    ConjClasses.mk (conjClassRep x) = x :=
  Classical.choose_spec (ConjClasses.exists_rep x)

noncomputable def smallConjClassOutEmbedding (G : Type) [Group G] (M : ℕ) :
    SmallConjClasses G M ↪ SmallConjElements G M where
  toFun x := ⟨conjClassRep x.1, by
    rw [mk_conjClassRep]
    exact x.2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    calc
      x.1 = ConjClasses.mk (conjClassRep x.1) := (mk_conjClassRep x.1).symm
      _ = ConjClasses.mk (conjClassRep y.1) := by
        exact congrArg ConjClasses.mk (congrArg Subtype.val h)
      _ = y.1 := mk_conjClassRep y.1

lemma card_smallConjClasses_le_card_smallConjElements
    (G : Type) [Group G] [Finite G] (M : ℕ) :
    Nat.card (SmallConjClasses G M) ≤ Nat.card (SmallConjElements G M) :=
  Nat.card_le_card_of_injective _ (smallConjClassOutEmbedding G M).injective

lemma half_mul_card_lt_card_smallConjElements_of_lt_commProb
    (G : Type) [Group G] [Finite G] {r : ℝ} {M : ℕ}
    (hM : 1 / ((M + 1 : ℕ) : ℝ) ≤ r / 2)
    (hprob : r < (commProb G : ℝ)) :
    r / 2 * Nat.card G < Nat.card (SmallConjElements G M) := by
  classical
  let small : Set (ConjClasses G) := {x | Nat.card x.carrier ≤ M}
  let large : Set (ConjClasses G) := {x | M < Nat.card x.carrier}
  have hcompl : smallᶜ = large := by
    ext x
    simp [small, large]
  have hpartition : small.ncard + large.ncard = Nat.card (ConjClasses G) := by
    rw [← hcompl, Set.ncard_add_ncard_compl]
  have hlargeN : (M + 1) * large.ncard ≤ Nat.card G := by
    simpa [large] using mul_ncard_largeConjClasses_le_card G M
  have hsmallElemN : small.ncard ≤ Nat.card (SmallConjElements G M) := by
    rw [← Nat.card_coe_set_eq small]
    change Nat.card (SmallConjClasses G M) ≤ Nat.card (SmallConjElements G M)
    exact card_smallConjClasses_le_card_smallConjElements G M
  have hgN : 0 < Nat.card G := Finite.card_pos
  have hMN : 0 < M + 1 := Nat.succ_pos M
  have hg : (0 : ℝ) < Nat.card G := by exact_mod_cast hgN
  have hMr : (0 : ℝ) < M + 1 := by exact_mod_cast hMN
  have hprob' : r < (Nat.card (ConjClasses G) : ℝ) / Nat.card G := by
    simpa [commProb_def'] using hprob
  have hk : r * (Nat.card G : ℝ) < Nat.card (ConjClasses G) :=
    (lt_div_iff₀ hg).mp hprob'
  have hlarge : (large.ncard : ℝ) ≤ (Nat.card G : ℝ) / (M + 1) := by
    apply (le_div_iff₀ hMr).2
    have hlargeN' := hlargeN
    rw [Nat.mul_comm] at hlargeN'
    exact_mod_cast hlargeN'
  have hlarge' : (large.ncard : ℝ) ≤ r / 2 * Nat.card G := by
    calc
      (large.ncard : ℝ) ≤ (Nat.card G : ℝ) / (M + 1) := hlarge
      _ = (1 / ((M + 1 : ℕ) : ℝ)) * Nat.card G := by
        push_cast
        ring
      _ ≤ r / 2 * Nat.card G := by gcongr
  have hpartitionR : (small.ncard : ℝ) + large.ncard = Nat.card (ConjClasses G) := by
    exact_mod_cast hpartition
  have hsmallElem : (small.ncard : ℝ) ≤ Nat.card (SmallConjElements G M) := by
    exact_mod_cast hsmallElemN
  linarith

abbrev SmallConjSet (G : Type) [Group G] (M : ℕ) : Set G :=
  {g | Nat.card (ConjClasses.mk g).carrier ≤ M}

def smallConjSubgroup (G : Type) [Group G] (M : ℕ) : Subgroup G :=
  Subgroup.normalClosure (SmallConjSet G M)

instance smallConjSubgroup_normal (G : Type) [Group G] (M : ℕ) :
    (smallConjSubgroup G M).Normal :=
  Subgroup.normalClosure_normal

def smallConjElementsEmbeddingSmallConjSubgroup (G : Type) [Group G] (M : ℕ) :
    SmallConjElements G M ↪ smallConjSubgroup G M where
  toFun x := ⟨x.1, Subgroup.subset_normalClosure x.2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    change (x : G) = (y : G)
    exact congrArg (fun z : smallConjSubgroup G M => (z : G)) h

lemma card_smallConjElements_le_card_smallConjSubgroup
    (G : Type) [Group G] [Finite G] (M : ℕ) :
    Nat.card (SmallConjElements G M) ≤ Nat.card (smallConjSubgroup G M) :=
  Nat.card_le_card_of_injective _
    (smallConjElementsEmbeddingSmallConjSubgroup G M).injective

lemma smallConjSubgroup_index_lt_inv_of_density
    (G : Type) [Group G] [Finite G] {M : ℕ} {d : ℝ} (hd : 0 < d)
    (hdensity : d * Nat.card G < Nat.card (SmallConjElements G M)) :
    ((smallConjSubgroup G M).index : ℝ) < 1 / d := by
  let K := smallConjSubgroup G M
  have hsmallN : Nat.card (SmallConjElements G M) ≤ Nat.card K :=
    card_smallConjElements_le_card_smallConjSubgroup G M
  have hsmall : (Nat.card (SmallConjElements G M) : ℝ) ≤ Nat.card K := by
    exact_mod_cast hsmallN
  have hcardN : Nat.card K * K.index = Nat.card G := K.card_mul_index
  have hcard : (Nat.card K : ℝ) * K.index = Nat.card G := by
    exact_mod_cast hcardN
  have hK : (0 : ℝ) < Nat.card K := by
    exact_mod_cast (show 0 < Nat.card K from Finite.card_pos)
  have hprod : d * ((K.index : ℝ) * Nat.card K) < Nat.card K := by
    calc
      d * ((K.index : ℝ) * Nat.card K) =
          d * ((Nat.card K : ℝ) * K.index) := by ring
      _ = d * Nat.card G := by rw [hcard]
      _ < Nat.card K := hdensity.trans_le hsmall
  have hindex : d * (K.index : ℝ) < 1 := by
    have hscaled : (d * (K.index : ℝ)) * Nat.card K < 1 * Nat.card K := by
      simpa [mul_assoc] using hprod
    exact (mul_lt_mul_iff_left₀ hK).mp hscaled
  apply (lt_div_iff₀ hd).2
  simpa [mul_comm] using hindex

lemma commProb_le_half_add_inv_centerIndex_real (G : Type) [Group G] [Finite G] :
    (commProb G : ℝ) ≤ 1 / 2 + 1 / (2 * ((Subgroup.center G).index : ℝ)) := by
  have hcount := twice_card_conjClasses_le_card_add_center G
  have hcard : Nat.card (Subgroup.center G) * (Subgroup.center G).index = Nat.card G :=
    (Subgroup.center G).card_mul_index
  rw [commProb_def']
  simp only [Rat.cast_div, Rat.cast_natCast]
  have hgN : 0 < Nat.card G := Finite.card_pos
  have hiN : 0 < (Subgroup.center G).index := Finite.card_pos
  have hg : (0 : ℝ) < Nat.card G := by exact_mod_cast hgN
  have hi : (0 : ℝ) < (Subgroup.center G).index := by exact_mod_cast hiN
  have hcountR : 2 * (Nat.card (ConjClasses G) : ℝ) ≤
      Nat.card G + Nat.card (Subgroup.center G) := by
    exact_mod_cast hcount
  have hcardR : (Nat.card (Subgroup.center G) : ℝ) *
      (Subgroup.center G).index = Nat.card G := by
    exact_mod_cast hcard
  apply (div_le_iff₀ hg).2
  calc
    (Nat.card (ConjClasses G) : ℝ) ≤
        ((Nat.card G : ℝ) + Nat.card (Subgroup.center G)) / 2 := by
      linarith
    _ = (1 / 2 + 1 / (2 * ((Subgroup.center G).index : ℝ))) * Nat.card G := by
      rw [← hcardR]
      field_simp

lemma centerIndex_lt_inv_gap {G : Type} [Group G] [Finite G] {r : ℝ}
    (hr : 1 / 2 < r) (hprob : r < (commProb G : ℝ)) :
    ((Subgroup.center G).index : ℝ) < 1 / (2 * r - 1) := by
  have hbound := commProb_le_half_add_inv_centerIndex_real G
  have hi : (0 : ℝ) < (Subgroup.center G).index := by
    exact_mod_cast (show 0 < (Subgroup.center G).index from Finite.card_pos)
  have hgap : r - 1 / 2 < 1 / (2 * ((Subgroup.center G).index : ℝ)) := by
    linarith
  have hmul : (r - 1 / 2) * (2 * ((Subgroup.center G).index : ℝ)) < 1 := by
    exact (lt_div_iff₀ (mul_pos (by norm_num) hi)).mp hgap
  apply (lt_div_iff₀ (by linarith : 0 < 2 * r - 1)).2
  nlinarith

lemma exists_finiteCommProbWitness_abs_sub_lt_of_clusterPt_pos {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : FiniteCommProbWitness,
      p / 2 < W.probability ∧ |W.probability - p| < ε := by
  obtain ⟨q, G, hG, hfinite, hq_lower, hq_close, hprob⟩ :=
    exists_finite_witness_abs_sub_lt_of_clusterPt_pos hp hp_pos hε
  let W : FiniteCommProbWitness := ⟨G, hG, hfinite⟩
  refine ⟨W, ?_, ?_⟩
  · simpa [W, FiniteCommProbWitness.probability, hprob] using hq_lower
  · simpa [W, FiniteCommProbWitness.probability, hprob] using hq_close

noncomputable def clusterWitness {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) (n : ℕ) :
    FiniteCommProbWitness :=
  Classical.choose (exists_finiteCommProbWitness_abs_sub_lt_of_clusterPt_pos hp hp_pos
    (show 0 < 1 / ((n : ℝ) + 1) by positivity))

lemma clusterWitness_lower {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) (n : ℕ) :
    p / 2 < (clusterWitness hp hp_pos n).probability :=
  (Classical.choose_spec (exists_finiteCommProbWitness_abs_sub_lt_of_clusterPt_pos hp hp_pos
    (show 0 < 1 / ((n : ℝ) + 1) by positivity))).1

lemma clusterWitness_close {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) (n : ℕ) :
    |(clusterWitness hp hp_pos n).probability - p| < 1 / ((n : ℝ) + 1) :=
  (Classical.choose_spec (exists_finiteCommProbWitness_abs_sub_lt_of_clusterPt_pos hp hp_pos
    (show 0 < 1 / ((n : ℝ) + 1) by positivity))).2

lemma clusterWitness_probability_mem_CommProbRange {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) (n : ℕ) :
    (clusterWitness hp hp_pos n).probability ∈ CommProbRange := by
  let W := clusterWitness hp hp_pos n
  refine ⟨W.carrier, W.group, ?_⟩
  rfl

lemma tendsto_clusterWitness_probability {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) :
    Filter.Tendsto (fun n => (clusterWitness hp hp_pos n).probability) Filter.atTop (𝓝 p) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => dist_nonneg
  · exact Filter.Eventually.of_forall fun n => by
      simpa [Real.dist_eq] using (clusterWitness_close hp hp_pos n).le
  · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma mem_CommProbRange_of_clusterWitness_card_bounded {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) (N : ℕ)
    (hcard : ∀ n, Nat.card (clusterWitness hp hp_pos n).carrier ≤ N) :
    p ∈ CommProbRange := by
  let values : ℕ → ℝ := fun n => (clusterWitness hp hp_pos n).probability
  let candidates : Fin (N + 1) × Fin (N ^ 2 + 1) → ℝ := fun x =>
    (((x.2.1 : ℕ) : ℚ) / (((x.1.1 : ℕ) : ℚ) ^ 2) : ℚ)
  have hvalues_subset : Set.range values ⊆ Set.range candidates := by
    rintro _ ⟨n, rfl⟩
    let W := clusterWitness hp hp_pos n
    letI : Group W.carrier := W.group
    letI : Finite W.carrier := W.finite
    have hb : Nat.card W.carrier ≤ N := hcard n
    have ha : Nat.card {x : W.carrier × W.carrier // Commute x.1 x.2} ≤
        Nat.card W.carrier ^ 2 := by
      simpa [Nat.card_prod, pow_two] using
        (Finite.card_subtype_le (fun x : W.carrier × W.carrier => Commute x.1 x.2))
    let b : Fin (N + 1) := ⟨Nat.card W.carrier, Nat.lt_succ_of_le hb⟩
    let a : Fin (N ^ 2 + 1) :=
      ⟨Nat.card {x : W.carrier × W.carrier // Commute x.1 x.2},
        Nat.lt_succ_of_le (ha.trans (Nat.pow_le_pow_left hb 2))⟩
    refine ⟨(b, a), ?_⟩
    simp [values, candidates, W, b, a, FiniteCommProbWitness.probability, commProb_def]
  have hvalues_finite : (Set.range values).Finite :=
    (Set.finite_range candidates).subset hvalues_subset
  have hp_values : p ∈ Set.range values :=
    hvalues_finite.isClosed.mem_of_tendsto (tendsto_clusterWitness_probability hp hp_pos)
      (Filter.Eventually.of_forall fun n => ⟨n, rfl⟩)
  rcases hp_values with ⟨n, hn⟩
  have hn_mem : values n ∈ CommProbRange := by
    simpa [values] using clusterWitness_probability_mem_CommProbRange hp hp_pos n
  exact hn ▸ hn_mem

lemma mem_CommProbRange_of_clusterWitness_centerIndex_bounded {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) (N : ℕ)
    (hindex : ∀ n,
      let W := clusterWitness hp hp_pos n
      letI := W.group
      (Subgroup.center W.carrier).index ≤ N) :
    p ∈ CommProbRange := by
  let values : ℕ → ℝ := fun n => (clusterWitness hp hp_pos n).probability
  let candidates : Fin (N + 1) × Fin (N ^ 2 + 1) → ℝ := fun x =>
    (((x.2.1 : ℕ) : ℚ) / (((x.1.1 : ℕ) : ℚ) ^ 2) : ℚ)
  have hvalues_subset : Set.range values ⊆ Set.range candidates := by
    rintro _ ⟨n, rfl⟩
    let W := clusterWitness hp hp_pos n
    letI : Group W.carrier := W.group
    letI : Finite W.carrier := W.finite
    have hb : (Subgroup.center W.carrier).index ≤ N := hindex n
    have ha : Nat.card (CenterCommutingQuotientPairs W.carrier) ≤
        (Subgroup.center W.carrier).index ^ 2 :=
      card_centerCommutingQuotientPairs_le W.carrier
    let b : Fin (N + 1) :=
      ⟨(Subgroup.center W.carrier).index, Nat.lt_succ_of_le hb⟩
    let a : Fin (N ^ 2 + 1) :=
      ⟨Nat.card (CenterCommutingQuotientPairs W.carrier),
        Nat.lt_succ_of_le (ha.trans (Nat.pow_le_pow_left hb 2))⟩
    refine ⟨(b, a), ?_⟩
    simp [values, candidates, W, b, a, FiniteCommProbWitness.probability,
      commProb_eq_centerQuotientRatio]
  have hvalues_finite : (Set.range values).Finite :=
    (Set.finite_range candidates).subset hvalues_subset
  have hp_values : p ∈ Set.range values :=
    hvalues_finite.isClosed.mem_of_tendsto (tendsto_clusterWitness_probability hp hp_pos)
      (Filter.Eventually.of_forall fun n => ⟨n, rfl⟩)
  rcases hp_values with ⟨n, hn⟩
  have hn_mem : values n ∈ CommProbRange := by
    simpa [values] using clusterWitness_probability_mem_CommProbRange hp hp_pos n
  exact hn ▸ hn_mem

lemma mem_CommProbRange_of_clusterPt_gt_half {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_half : 1 / 2 < p) :
    p ∈ CommProbRange := by
  have hp_pos : 0 < p := by linarith
  let r : ℝ := (p + 1 / 2) / 2
  have hr_half : 1 / 2 < r := by dsimp [r]; linarith
  have hr_p : r < p := by dsimp [r]; linarith
  have hevent : ∀ᶠ n in Filter.atTop,
      r < (clusterWitness hp hp_pos n).probability :=
    (tendsto_clusterWitness_probability hp hp_pos).eventually (Ioi_mem_nhds hr_p)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / (2 * r - 1))
  let prefixBound : ℕ := ∑ n ∈ Finset.range M, (clusterWitness hp hp_pos n).centerIndex
  let B := max N prefixBound
  apply mem_CommProbRange_of_clusterWitness_centerIndex_bounded hp hp_pos B
  intro n
  change (clusterWitness hp hp_pos n).centerIndex ≤ B
  by_cases hn : n < M
  · have hprefix : (clusterWitness hp hp_pos n).centerIndex ≤ prefixBound := by
      simpa [prefixBound] using
        (Finset.single_le_sum (s := Finset.range M)
          (f := fun k => (clusterWitness hp hp_pos k).centerIndex)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn))
    exact hprefix.trans (Nat.le_max_right N prefixBound)
  · have hn_tail : M ≤ n := Nat.le_of_not_gt hn
    let W := clusterWitness hp hp_pos n
    have hWprob : r < W.probability := hM n hn_tail
    letI : Group W.carrier := W.group
    letI : Finite W.carrier := W.finite
    have hWindexR : (W.centerIndex : ℝ) < 1 / (2 * r - 1) := by
      simpa [W, FiniteCommProbWitness.centerIndex, FiniteCommProbWitness.probability] using
        (centerIndex_lt_inv_gap hr_half hWprob)
    have hWindexN : W.centerIndex ≤ N := by
      have hltR : (W.centerIndex : ℝ) < N := hWindexR.trans_le hN
      exact_mod_cast hltR.le
    exact hWindexN.trans (Nat.le_max_left N prefixBound)

lemma exists_strictMono_value_subsequence (f : ℕ → ℕ)
    (hbounded : ¬ ∃ N, ∀ n, f n ≤ N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (fun n => f (φ n)) := by
  have hf_unbounded : ∀ N, ∃ n, N < f n := by
    intro N
    by_contra hN
    exact hbounded ⟨N, fun n => Nat.le_of_not_gt (fun hn => hN ⟨n, hn⟩)⟩
  have htail : ∀ N, ∃ n, N < n ∧ f N < f n := by
    intro N
    let prefixSum := ∑ n ∈ Finset.range (N + 1), f n
    obtain ⟨n, hn⟩ := hf_unbounded prefixSum
    have hN_le : f N ≤ prefixSum := by
      apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      exact Finset.mem_range.mpr (Nat.lt_succ_self N)
    have hn_index : N < n := by
      by_contra hn_index
      have hn_mem : n ∈ Finset.range (N + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_of_not_gt hn_index))
      have hn_le : f n ≤ prefixSum := by
        apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        exact hn_mem
      exact (Nat.not_le_of_lt hn) hn_le
    exact ⟨n, hn_index, hN_le.trans_lt hn⟩
  let start := Classical.choose (hf_unbounded 0)
  let next : ℕ → ℕ := fun n => Classical.choose (htail n)
  let φ : ℕ → ℕ := fun n => Nat.rec start (fun _ previous => next previous) n
  have hφ_step : ∀ n, φ n < φ (n + 1) := by
    intro n
    change φ n < next (φ n)
    exact (Classical.choose_spec (htail (φ n))).1
  have hf_step : ∀ n, f (φ n) < f (φ (n + 1)) := by
    intro n
    change f (φ n) < f (next (φ n))
    exact (Classical.choose_spec (htail (φ n))).2
  exact ⟨φ, strictMono_nat_of_lt_succ hφ_step, strictMono_nat_of_lt_succ hf_step⟩

lemma exists_strictMono_card_subsequence (W : ℕ → FiniteCommProbWitness)
    (hcard : ¬ ∃ N, ∀ n, Nat.card (W n).carrier ≤ N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (fun n => Nat.card (W (φ n)).carrier) :=
  exists_strictMono_value_subsequence (fun n => Nat.card (W n).carrier) hcard

lemma exists_clusterWitness_subsequence_card_strictMono {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p)
    (hcard : ¬ ∃ N, ∀ n, Nat.card (clusterWitness hp hp_pos n).carrier ≤ N) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      StrictMono (fun n => Nat.card (clusterWitness hp hp_pos (φ n)).carrier) ∧
      Filter.Tendsto (fun n => (clusterWitness hp hp_pos (φ n)).probability)
        Filter.atTop (𝓝 p) := by
  obtain ⟨φ, hφ, hφcard⟩ := exists_strictMono_card_subsequence
    (fun n => clusterWitness hp hp_pos n) hcard
  refine ⟨φ, hφ, hφcard, ?_⟩
  exact (tendsto_clusterWitness_probability hp hp_pos).comp hφ.tendsto_atTop

lemma exists_clusterWitness_subsequence_centerIndex_strictMono {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p)
    (hindex : ¬ ∃ N, ∀ n, (clusterWitness hp hp_pos n).centerIndex ≤ N) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      StrictMono (fun n => (clusterWitness hp hp_pos (φ n)).centerIndex) ∧
      Filter.Tendsto (fun n => (clusterWitness hp hp_pos (φ n)).probability)
        Filter.atTop (𝓝 p) := by
  obtain ⟨φ, hφ, hφindex⟩ := exists_strictMono_value_subsequence
    (fun n => (clusterWitness hp hp_pos n).centerIndex) hindex
  refine ⟨φ, hφ, hφindex, ?_⟩
  exact (tendsto_clusterWitness_probability hp hp_pos).comp hφ.tendsto_atTop

lemma mem_CommProbRange_or_exists_centerIndex_strictMono_subsequence {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) :
    p ∈ CommProbRange ∨
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
        StrictMono (fun n => (clusterWitness hp hp_pos (φ n)).centerIndex) ∧
        Filter.Tendsto (fun n => (clusterWitness hp hp_pos (φ n)).probability)
          Filter.atTop (𝓝 p) := by
  by_cases hindex : ∃ N, ∀ n, (clusterWitness hp hp_pos n).centerIndex ≤ N
  · left
    obtain ⟨N, hN⟩ := hindex
    apply mem_CommProbRange_of_clusterWitness_centerIndex_bounded hp hp_pos N
    intro n
    change (clusterWitness hp hp_pos n).centerIndex ≤ N
    exact hN n
  · right
    exact exists_clusterWitness_subsequence_centerIndex_strictMono hp hp_pos hindex

lemma clusterPt_CommProbRange_nonneg {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) : 0 ≤ p := by
  by_contra hp_nonneg
  have hp_neg : p < 0 := lt_of_not_ge hp_nonneg
  obtain ⟨q, hqmem, hqdist⟩ :=
    exists_mem_CommProbRange_abs_sub_lt_of_clusterPt hp (by linarith : 0 < -p / 2)
  have hq_nonneg := mem_commProbRange_nonneg hqmem
  rcases abs_lt.mp hqdist with ⟨_, hq_upper⟩
  have hq_neg : q < 0 := by linarith
  exact not_lt_of_ge hq_nonneg hq_neg

lemma clusterPt_CommProbRange_le_one {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) : p ≤ 1 := by
  by_contra hp_le
  have hp_gt : 1 < p := lt_of_not_ge hp_le
  obtain ⟨q, hqmem, hqdist⟩ :=
    exists_mem_CommProbRange_abs_sub_lt_of_clusterPt hp (by linarith : 0 < (p - 1) / 2)
  have hq_le := mem_commProbRange_le_one hqmem
  rcases abs_lt.mp hqdist with ⟨hq_lower, _⟩
  have hq_gt : 1 < q := by linarith
  exact not_lt_of_ge hq_le hq_gt

lemma zero_mem_commProbRange : (0 : ℝ) ∈ CommProbRange := by
  refine ⟨Multiplicative ℤ, inferInstance, ?_⟩
  simp [commProb_eq_zero_of_infinite]

lemma one_mem_commProbRange : (1 : ℝ) ∈ CommProbRange := by
  refine ⟨PUnit, inferInstance, ?_⟩
  norm_num [commProb_def]

lemma reciprocal_mem_commProbRange (n : ℕ) : ((1 / n : ℚ) : ℝ) ∈ CommProbRange := by
  refine ⟨DihedralGroup.Product (DihedralGroup.reciprocalFactors n), inferInstance, ?_⟩
  norm_num [DihedralGroup.commProb_reciprocal]

lemma mem_CommProbRange_or_exists_centerIndex_strictMono_subsequence_lt_half {p : ℝ}
    (hp : ClusterPt p (Filter.principal CommProbRange)) (hp_pos : 0 < p) :
    p ∈ CommProbRange ∨
      (p < 1 / 2 ∧
        ∃ φ : ℕ → ℕ,
          StrictMono φ ∧
          StrictMono (fun n => (clusterWitness hp hp_pos (φ n)).centerIndex) ∧
          Filter.Tendsto (fun n => (clusterWitness hp hp_pos (φ n)).probability)
            Filter.atTop (𝓝 p)) := by
  by_cases hp_half : 1 / 2 < p
  · exact Or.inl (mem_CommProbRange_of_clusterPt_gt_half hp hp_half)
  by_cases hp_eq : p = 1 / 2
  · left
    subst p
    simpa using reciprocal_mem_commProbRange 2
  have hp_lt : p < 1 / 2 := lt_of_le_of_ne (le_of_not_gt hp_half) hp_eq
  rcases mem_CommProbRange_or_exists_centerIndex_strictMono_subsequence hp hp_pos with hp | hseq
  · exact Or.inl hp
  · exact Or.inr ⟨hp_lt, hseq⟩

lemma mul_mem_commProbRange {p q : ℝ}
    (hp : p ∈ CommProbRange) (hq : q ∈ CommProbRange) : p * q ∈ CommProbRange := by
  rcases hp with ⟨G, hG, hp⟩
  rcases hq with ⟨H, hH, hq⟩
  letI := hG
  letI := hH
  refine ⟨G × H, inferInstance, ?_⟩
  rw [commProb_prod, Rat.cast_mul, hp, hq]

lemma mul_reciprocal_mem_commProbRange {p : ℝ} (hp : p ∈ CommProbRange) (n : ℕ) :
    p * ((1 / n : ℚ) : ℝ) ∈ CommProbRange :=
  mul_mem_commProbRange hp (reciprocal_mem_commProbRange n)

lemma isClosed_CommProbRange_of_cluster_points
    (hcluster : ∀ p : ℝ, ClusterPt p (Filter.principal CommProbRange) → p ∈ CommProbRange) :
    IsClosed CommProbRange :=
  isClosed_iff_clusterPt.mpr hcluster

lemma isClosed_CommProbRange_of_positive_cluster_points
    (hpositive : ∀ p : ℝ, ClusterPt p (Filter.principal CommProbRange) → 0 < p → p ∈ CommProbRange) :
    IsClosed CommProbRange := by
  refine isClosed_CommProbRange_of_cluster_points ?_
  intro p hp
  rcases lt_or_eq_of_le (clusterPt_CommProbRange_nonneg hp) with hp_pos | rfl
  · exact hpositive p hp hp_pos
  · exact zero_mem_commProbRange

lemma isClosed_CommProbRange_of_cluster_points_reciprocal
    (hcluster : ∀ p : ℝ, ClusterPt p (Filter.principal CommProbRange) →
      p = 0 ∨ ∃ n : ℕ, p = ((1 / n : ℚ) : ℝ)) :
    IsClosed CommProbRange := by
  refine isClosed_CommProbRange_of_cluster_points ?_
  intro p hp
  rcases hcluster p hp with rfl | ⟨n, rfl⟩
  · exact zero_mem_commProbRange
  · exact reciprocal_mem_commProbRange n

lemma isClosed_CommProbRange_of_cluster_points_scaled
    (hcluster : ∀ p : ℝ, ClusterPt p (Filter.principal CommProbRange) →
      p = 0 ∨ ∃ q ∈ CommProbRange, ∃ n : ℕ, p = q * ((1 / n : ℚ) : ℝ)) :
    IsClosed CommProbRange := by
  refine isClosed_CommProbRange_of_cluster_points ?_
  intro p hp
  rcases hcluster p hp with rfl | ⟨q, hq, n, rfl⟩
  · exact zero_mem_commProbRange
  · exact mul_reciprocal_mem_commProbRange hq n

lemma isClosed_CommProbRange_of_cluster_point_ascent
    (hascent : ∀ {p : ℝ}, ClusterPt p (Filter.principal CommProbRange) → 0 < p →
      p ∈ CommProbRange ∨
        ∃ n : ℕ, 2 ≤ n ∧
          ClusterPt ((n : ℝ) * p) (Filter.principal CommProbRange)) :
    IsClosed CommProbRange := by
  apply isClosed_CommProbRange_of_positive_cluster_points
  intro p hp hp_pos
  have htend : Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k * p)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hp_pos
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hevent : ∀ᶠ k : ℕ in Filter.atTop, 1 < (2 : ℝ) ^ k * p :=
    htend.eventually_gt_atTop 1
  obtain ⟨k, hk⟩ := hevent.exists
  have hmain : ∀ k : ℕ, ∀ {q : ℝ},
      ClusterPt q (Filter.principal CommProbRange) → 0 < q →
      1 < (2 : ℝ) ^ k * q → q ∈ CommProbRange := by
    intro j
    induction j with
    | zero =>
        intro q hq hq_pos hj
        simp only [pow_zero, one_mul] at hj
        exact (not_lt_of_ge (clusterPt_CommProbRange_le_one hq) hj).elim
    | succ j ih =>
        intro q hq hq_pos hj
        rcases hascent hq hq_pos with hq_mem | ⟨n, hn, hnq⟩
        · exact hq_mem
        · have hn_pos : (0 : ℝ) < n := by
            exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
          have hnq_pos : 0 < (n : ℝ) * q := mul_pos hn_pos hq_pos
          have hj' : 1 < (2 : ℝ) ^ j * ((n : ℝ) * q) := by
            calc
              1 < (2 : ℝ) ^ (j + 1) * q := hj
              _ = (2 : ℝ) ^ j * (2 * q) := by rw [pow_succ]; ring
              _ ≤ (2 : ℝ) ^ j * ((n : ℝ) * q) := by
                gcongr
                exact_mod_cast hn
          have hnq_mem : (n : ℝ) * q ∈ CommProbRange := ih hnq hnq_pos hj'
          have hn_ne : n ≠ 0 := by omega
          have hq_eq : q = ((n : ℝ) * q) * (((1 / n : ℚ) : ℝ)) := by
            push_cast
            field_simp
          rw [hq_eq]
          exact mul_reciprocal_mem_commProbRange hnq_mem n
  exact hmain k hp hp_pos hk

end
end Submission.Helpers
