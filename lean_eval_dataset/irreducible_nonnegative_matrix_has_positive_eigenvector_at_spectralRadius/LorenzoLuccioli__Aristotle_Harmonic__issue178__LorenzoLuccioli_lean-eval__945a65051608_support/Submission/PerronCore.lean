import Mathlib

namespace Submission.PerronCore

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ## Auxiliary lemmas -/

lemma isCompact_nonneg_unitSphere :
    IsCompact {v : n → ℝ | (∀ i, 0 ≤ v i) ∧ ‖v‖ = 1} := by
  refine' ( Metric.isCompact_iff_isClosed_bounded.mpr _ );
  exact ⟨ by rw [ Set.setOf_and ] ; exact IsClosed.inter ( isClosed_Ici.preimage <| continuous_pi fun _ => continuous_apply _ ) ( isClosed_eq continuous_norm continuous_const ), isBounded_iff_forall_norm_le.mpr ⟨ 1, fun v hv => hv.2.le ⟩ ⟩

lemma nonempty_nonneg_unitSphere :
    Set.Nonempty {v : n → ℝ | (∀ i, 0 ≤ v i) ∧ ‖v‖ = 1} := by
  obtain ⟨ i ⟩ := ‹Nonempty n›;
  refine' ⟨ fun j => if j = i then 1 else 0, _, _ ⟩ <;> simp +decide [ Pi.norm_def ];
  · exact fun _ => by split_ifs <;> norm_num;
  · exact le_antisymm ( Finset.sup_le fun j _ => by aesop ) ( Finset.le_sup ( Finset.mem_univ i ) |> le_trans ( by aesop ) )

lemma nonneg_mulVec_ne_zero [Nontrivial n] {A : Matrix n n ℝ}
    (hA : A.IsIrreducible) {v : n → ℝ} (hv_nn : ∀ i, 0 ≤ v i) (hv_nz : v ≠ 0) :
    A.mulVec v ≠ 0 := by
  by_contra h_contra
  have h_zero : ∀ i, ∑ j, A i j * v j = 0 := by
    exact fun i => by simpa only [ Matrix.mulVec, dotProduct ] using congr_fun h_contra i;
  obtain ⟨j, hj⟩ : ∃ j, v j > 0 ∧ ∀ i, A i j = 0 := by
    obtain ⟨j, hj⟩ : ∃ j, v j > 0 := by
      exact Function.ne_iff.mp hv_nz |> Exists.imp fun i hi => lt_of_le_of_ne ( hv_nn i ) ( Ne.symm hi );
    refine' ⟨ j, hj, fun i => _ ⟩;
    have h_nonneg : ∀ i j, 0 ≤ A i j := by
      intro i j; have := hA.1; simp_all +decide [ Matrix.IsIrreducible ] ;
    exact le_antisymm ( le_of_not_gt fun hi => absurd ( h_zero i ▸ Finset.single_le_sum ( fun a _ => mul_nonneg ( h_nonneg i a ) ( hv_nn a ) ) ( Finset.mem_univ j ) ) ( by nlinarith [ h_nonneg i j ] ) ) ( h_nonneg i j );
  have h_irred : ∀ i, ∃ k > 0, (A ^ k) i j > 0 := by
    have := Matrix.isIrreducible_iff_exists_pow_pos ( show ∀ i j, 0 ≤ A i j from ?_ ) |>.1 hA;
    · exact fun i => this i j;
    · have := hA.1; simp_all +decide [ funext_iff, Matrix.mulVec ] ;
  have h_ind : ∀ k > 0, ∀ i, (A ^ k) i j = 0 := by
    intro k hk; induction hk <;> simp_all +decide [ pow_succ', Matrix.mul_apply ] ;
    simp_all +decide [ Matrix.one_apply ];
  exact absurd ( h_irred j ) ( by rintro ⟨ k, hk₀, hk ⟩ ; linarith [ h_ind k hk₀ j ] )

lemma exists_edge_to_complement {A : Matrix n n ℝ}
    (hA : A.IsIrreducible)
    (S : Finset n) (hS_ne : S.Nonempty) (hS_proper : S ≠ Finset.univ) :
    ∃ i ∈ S, ∃ j ∉ S, 0 < A i j := by
  by_contra h_no_edges
  push_neg at h_no_edges;
  have h_ind : ∀ k > 0, ∀ i ∈ S, ∀ j ∉ S, (A^k) i j = 0 := by
    intro k hk i hi j hj;
    induction' hk with k hk ih generalizing i j <;> simp_all +decide [ pow_succ, Matrix.mul_apply ];
    · by_cases hij : i = j <;> simp_all +decide [ Matrix.one_apply ];
      exact le_antisymm ( h_no_edges i hi j hj ) ( by have := hA.1; aesop );
    · rw [ Finset.sum_eq_zero ] ; intros ; by_cases hj' : ‹_› ∈ S <;> simp_all +decide [ Matrix.mul_apply ];
      grind +suggestions;
  have h_irred : ∀ i j, ∃ k > 0, 0 < (A ^ k) i j := by
    convert Matrix.isIrreducible_iff_exists_pow_pos ( show ∀ i j, 0 ≤ A i j from ?_ ) |>.1 hA using 1;
    exact fun i j => hA.nonneg i j;
  obtain ⟨ i, hi ⟩ := hS_ne; obtain ⟨ j, hj ⟩ := Finset.exists_of_ssubset ( lt_of_le_of_ne ( Finset.subset_univ S ) hS_proper ) ; obtain ⟨ k, hk₀, hk ⟩ := h_irred i j; specialize h_ind k hk₀ i hi j; aesop;

/-! ## Step-by-step Collatz-Wielandt argument -/

/-
There exists ρ ≥ 0 and v ≥ 0, ‖v‖ = 1 with Av ≥ ρv, and ρ is optimal
    (any nonneg nonzero w with Aw ≥ tw gives t ≤ ρ).
-/
lemma exists_optimal_cw_pair (A : Matrix n n ℝ) (hA_nn : ∀ i j, 0 ≤ A i j) :
    ∃ (ρ : ℝ) (v : n → ℝ), 0 ≤ ρ ∧ (∀ i, 0 ≤ v i) ∧ ‖v‖ = 1 ∧
      (∀ i, ρ * v i ≤ (A.mulVec v) i) ∧
      (∀ t : ℝ, 0 ≤ t → (∃ w : n → ℝ, (∀ i, 0 ≤ w i) ∧ w ≠ 0 ∧
        ∀ i, t * w i ≤ (A.mulVec w) i) → t ≤ ρ) := by
  -- Let's define the set T and show that it is nonempty and bounded above.
  set T := {t : ℝ | 0 ≤ t ∧ ∃ v : n → ℝ, (∀ i, 0 ≤ v i) ∧ ‖v‖ = 1 ∧ (∀ i, t * v i ≤ (A.mulVec v) i)} with hT_def
  have hT_nonempty : T.Nonempty := by
    refine' ⟨ 0, ⟨ le_rfl, _ ⟩ ⟩;
    obtain ⟨ v, hv ⟩ := nonempty_nonneg_unitSphere ( n := n );
    exact ⟨ v, hv.1, hv.2, fun i => by simpa [ Matrix.mulVec, dotProduct ] using Finset.sum_nonneg fun j _ => mul_nonneg ( hA_nn i j ) ( hv.1 j ) ⟩
  have hT_bounded_above : BddAbove T := by
    refine' ⟨ ∑ i, ∑ j, A i j, fun t ht => _ ⟩;
    obtain ⟨ ht_nonneg, v, hv_nonneg, hv_norm, hv_ineq ⟩ := ht
    have h_sum_ineq : t * ∑ i, v i ≤ ∑ i, ∑ j, A i j * v j := by
      simpa only [ Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun i _ => hv_ineq i;
    contrapose! h_sum_ineq;
    refine' lt_of_le_of_lt _ ( mul_lt_mul_of_pos_right h_sum_ineq _ );
    · simpa only [ Finset.sum_mul _ _ _ ] using Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun i _ => hv_nonneg i ) ( Finset.mem_univ j ) ) ( hA_nn i j );
    · -- Since $v$ is nonnegative and its norm is 1, there must be at least one component $v_i$ that is positive.
      obtain ⟨i, hi⟩ : ∃ i, 0 < v i := by
        exact not_forall_not.mp fun h => by rw [ show v = 0 from funext fun i => le_antisymm ( le_of_not_gt ( h i ) ) ( hv_nonneg i ) ] at hv_norm; simp +decide at hv_norm;
      exact lt_of_lt_of_le hi ( Finset.single_le_sum ( fun i _ => hv_nonneg i ) ( Finset.mem_univ i ) );
  -- Let ρ = sSup T. ρ ≥ 0 (since 0 ∈ T).
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = sSup T ∧ 0 ≤ ρ := by
    exact ⟨ _, rfl, le_trans hT_nonempty.choose_spec.1 ( le_csSup hT_bounded_above hT_nonempty.choose_spec ) ⟩;
  -- Attainment: Take t_k ∈ T with t_k → ρ, with witnesses v_k. By isCompact_nonneg_unitSphere, extract subsequence v_{k_j} → v*. Then v* ≥ 0, ‖v*‖ = 1, and Av* ≥ ρ v* (by continuity of mulVec and passing to limit t_{k_j} → ρ).
  obtain ⟨v, hv⟩ : ∃ v : n → ℝ, (∀ i, 0 ≤ v i) ∧ ‖v‖ = 1 ∧ ∀ i, ρ * v i ≤ (A.mulVec v) i := by
    -- By definition of supremum, there exists a sequence $(t_k, v_k)$ in $T$ such that $t_k \to \rho$.
    obtain ⟨t_k, v_k, ht_k, hv_k⟩ : ∃ (t_k : ℕ → ℝ) (v_k : ℕ → n → ℝ), (∀ k, t_k k ∈ T) ∧ Filter.Tendsto t_k Filter.atTop (nhds ρ) ∧ (∀ k, (∀ i, 0 ≤ v_k k i) ∧ ‖v_k k‖ = 1 ∧ (∀ i, t_k k * v_k k i ≤ (A.mulVec (v_k k)) i)) := by
      have h_seq : ∀ ε > 0, ∃ t ∈ T, ρ - ε < t ∧ t ≤ ρ := by
        exact fun ε εpos => by rcases exists_lt_of_lt_csSup hT_nonempty ( show ρ - ε < sSup T from by linarith ) with ⟨ t, htT, ht ⟩ ; exact ⟨ t, htT, by linarith, by linarith [ le_csSup hT_bounded_above htT ] ⟩ ;
      choose! t ht using h_seq;
      choose! v hv using fun k : ℕ => ht ( 1 / ( k + 1 ) ) ( by positivity ) |>.1 |>.2;
      exact ⟨ _, _, fun k => ht _ ( by positivity ) |>.1, tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => abs_nonneg _ ) ( fun k => abs_le.mpr ⟨ by linarith [ ht ( 1 / ( k + 1 ) ) ( by positivity ) ], by linarith [ ht ( 1 / ( k + 1 ) ) ( by positivity ) ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat, hv ⟩;
    -- By the compactness of the unit sphere, there exists a convergent subsequence $v_{k_j} \to v^*$.
    obtain ⟨v_star, hv_star⟩ : ∃ v_star : n → ℝ, (∀ i, 0 ≤ v_star i) ∧ ‖v_star‖ = 1 ∧ ∃ (subseq : ℕ → ℕ), StrictMono subseq ∧ Filter.Tendsto (fun j => v_k (subseq j)) Filter.atTop (nhds v_star) := by
      have h_compact : IsCompact {v : n → ℝ | (∀ i, 0 ≤ v i) ∧ ‖v‖ = 1} := by
        exact isCompact_nonneg_unitSphere;
      have := h_compact.isSeqCompact fun k => ⟨ hv_k.2 k |>.1, hv_k.2 k |>.2.1 ⟩;
      exact ⟨ this.choose, this.choose_spec.1.1, this.choose_spec.1.2, this.choose_spec.2 ⟩;
    refine' ⟨ v_star, hv_star.1, hv_star.2.1, fun i => _ ⟩;
    obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hv_star.2.2;
    exact le_of_tendsto_of_tendsto' ( Filter.Tendsto.mul ( hv_k.1.comp hsubseq₁.tendsto_atTop ) ( tendsto_pi_nhds.mp hsubseq₂ i ) ) ( tendsto_pi_nhds.mp ( Filter.Tendsto.comp ( show Filter.Tendsto ( fun v => A.mulVec v ) ( nhds v_star ) ( nhds ( A.mulVec v_star ) ) from Continuous.tendsto ( show Continuous fun v => A.mulVec v from continuous_const.matrix_mulVec continuous_id' ) _ ) hsubseq₂ ) i ) fun j => hv_k.2 ( subseq j ) |>.2.2 i;
  refine' ⟨ ρ, v, hρ.2, hv.1, hv.2.1, hv.2.2, fun t ht ⟨ w, hw₁, hw₂, hw₃ ⟩ => _ ⟩;
  refine' hρ.1 ▸ le_csSup hT_bounded_above ⟨ ht, _ ⟩;
  refine' ⟨ ‖w‖⁻¹ • w, _, _, _ ⟩ <;> simp_all +decide [ norm_smul ];
  simp_all +decide [ Matrix.mulVec, dotProduct, mul_assoc, mul_left_comm, mul_comm ];
  simp_all +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _ ]

/-
Given a CW maximizer v ≥ 0, ‖v‖ = 1, Av ≥ ρv with A irreducible,
    we can find w > 0 with Aw ≥ ρw and still ρ-optimal.
    Proof: extend support by adding ε e_p for p outside support with (Av)_p > 0.
-/
set_option maxHeartbeats 800000 in
lemma extend_support_to_positive [Nontrivial n] (A : Matrix n n ℝ) (hA : A.IsIrreducible)
    {ρ : ℝ} {v : n → ℝ} (hρ_nn : 0 ≤ ρ) (hv_nn : ∀ i, 0 ≤ v i) (hv_norm : ‖v‖ = 1)
    (hv_ge : ∀ i, ρ * v i ≤ (A.mulVec v) i)
    (hρ_opt : ∀ t : ℝ, 0 ≤ t → (∃ w : n → ℝ, (∀ i, 0 ≤ w i) ∧ w ≠ 0 ∧
        ∀ i, t * w i ≤ (A.mulVec w) i) → t ≤ ρ) :
    ∃ w : n → ℝ, (∀ i, 0 < w i) ∧
      (∀ i, ρ * w i ≤ (A.mulVec w) i) ∧
      (∀ t : ℝ, 0 ≤ t → (∃ u : n → ℝ, (∀ i, 0 ≤ u i) ∧ u ≠ 0 ∧
        ∀ i, t * u i ≤ (A.mulVec u) i) → t ≤ ρ) := by
  by_cases h_zero : ∃ i, v i = 0;
  · -- By induction on the number of zeros in v, we can find a vector w > 0 with Aw ≥ ρw.
    have h_ind : ∀ (S : Finset n), S.Nonempty → S ≠ Finset.univ → (∃ w : n → ℝ, (∀ i, 0 ≤ w i) ∧ (∀ i, ρ * w i ≤ (A.mulVec w) i) ∧ (∀ i ∈ S, w i = 0) ∧ (∀ i ∉ S, 0 < w i)) → ∃ w : n → ℝ, (∀ i, 0 ≤ w i) ∧ (∀ i, ρ * w i ≤ (A.mulVec w) i) ∧ (∃ i ∈ S, w i > 0) ∧ (∀ i ∉ S, 0 < w i) := by
      intro S hS_nonempty hS_ne_univ hS_exists
      obtain ⟨w, hw_nonneg, hw_ge, hw_zero, hw_pos⟩ := hS_exists
      obtain ⟨p, hpS, j, hjS, hpj⟩ : ∃ p ∈ S, ∃ j ∉ S, 0 < A p j := by
        exact exists_edge_to_complement hA S hS_nonempty hS_ne_univ;
      -- Define $w' = w + \epsilon e_p$ for small $\epsilon > 0$.
      obtain ⟨ε, hε_pos, hε_small⟩ : ∃ ε > 0, ∀ i, ρ * (w i + if i = p then ε else 0) ≤ (A.mulVec (fun i => w i + if i = p then ε else 0)) i := by
        -- Choose $\epsilon$ small enough such that $\rho \epsilon \leq (A.mulVec w) p$.
        obtain ⟨ε, hε_pos, hε_small⟩ : ∃ ε > 0, ρ * ε ≤ (A.mulVec w) p := by
          have h_pos : 0 < (A.mulVec w) p := by
            exact lt_of_lt_of_le ( mul_pos hpj ( hw_pos j hjS ) ) ( Finset.single_le_sum ( fun i _ => mul_nonneg ( show 0 ≤ A p i from by
                                                                                                                    contrapose! hv_ge;
                                                                                                                    exact absurd ( hA.1 p i ) ( by simp +decide [ hv_ge ] ) ) ( hw_nonneg i ) ) ( Finset.mem_univ j ) );
          exact ⟨ ( A *ᵥ w ) p / ( ρ + 1 ), div_pos h_pos ( add_pos_of_nonneg_of_pos hρ_nn zero_lt_one ), by nlinarith [ mul_div_cancel₀ ( ( A *ᵥ w ) p ) ( by linarith : ( ρ + 1 ) ≠ 0 ) ] ⟩;
        refine' ⟨ ε, hε_pos, fun i => _ ⟩ ; simp_all +decide [ Matrix.mulVec, dotProduct ];
        by_cases hi : i = p <;> simp_all +decide [ mul_add, Finset.sum_add_distrib ];
        · by_cases hpp : A p p ≥ 0;
          · exact le_add_of_le_of_nonneg hε_small ( mul_nonneg hpp hε_pos.le );
          · have := hA.1 p p; simp_all +decide [ Matrix.IsIrreducible ] ;
        · exact le_add_of_le_of_nonneg ( hw_ge i ) ( mul_nonneg ( show 0 ≤ A i p from by
                                                                    exact hA.nonneg i p ) hε_pos.le );
      refine' ⟨ fun i => w i + if i = p then ε else 0, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, mul_add ];
      · exact fun i => add_nonneg ( hw_nonneg i ) ( by split_ifs <;> linarith );
      · exact ⟨ p, hpS, by simp +decide [ hw_zero p hpS, hε_pos ] ⟩;
      · exact fun i hi => add_pos_of_pos_of_nonneg ( hw_pos i hi ) ( by split_ifs <;> linarith );
    -- Apply induction on the number of zeros in v.
    have h_induction : ∀ (S : Finset n), S.Nonempty → S ≠ Finset.univ → (∃ w : n → ℝ, (∀ i, 0 ≤ w i) ∧ (∀ i, ρ * w i ≤ (A.mulVec w) i) ∧ (∀ i ∈ S, w i = 0) ∧ (∀ i ∉ S, 0 < w i)) → ∃ w : n → ℝ, (∀ i, 0 < w i) ∧ (∀ i, ρ * w i ≤ (A.mulVec w) i) := by
      intro S hS_nonempty hS_ne_univ hS_exists
      induction' k : Finset.card S using Nat.strong_induction_on with k ih generalizing S;
      obtain ⟨ w, hw₁, hw₂, hw₃, hw₄ ⟩ := h_ind S hS_nonempty hS_ne_univ hS_exists;
      -- Let $T$ be the set of indices where $w$ is zero.
      set T := Finset.filter (fun i => w i = 0) Finset.univ with hT_def;
      by_cases hT_empty : T.Nonempty;
      · by_cases hT_ne_univ : T ≠ Finset.univ;
        · have hT_card : Finset.card T < Finset.card S := by
            refine' Finset.card_lt_card _;
            grind;
          exact ih _ ( by linarith ) _ hT_empty hT_ne_univ ⟨ w, hw₁, hw₂, fun i hi => Finset.mem_filter.mp hi |>.2, fun i hi => lt_of_le_of_ne ( hw₁ i ) ( Ne.symm <| by aesop ) ⟩ rfl;
        · grind;
      · exact ⟨ w, fun i => lt_of_le_of_ne ( hw₁ i ) ( Ne.symm <| by rintro hi; exact hT_empty ⟨ i, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hi ⟩ ⟩ ), hw₂ ⟩;
    contrapose! h_induction;
    refine' ⟨ Finset.univ.filter fun i => v i = 0, _, _, _, _ ⟩;
    · exact ⟨ h_zero.choose, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_zero.choose_spec ⟩ ⟩;
    · simp_all +decide [ Finset.ext_iff ];
      exact not_forall.mp fun h => by simp_all +decide [ show v = 0 from funext h ] ;
    · use v;
      grind;
    · intro w hw_pos
      by_contra h_contra
      push_neg at h_contra;
      exact absurd ( h_induction w hw_pos h_contra ) ( by rintro ⟨ t, ht₀, ⟨ u, hu₀, hu₁, hu₂ ⟩, ht ⟩ ; linarith [ hρ_opt t ht₀ ⟨ u, hu₀, hu₁, hu₂ ⟩ ] );
  · exact ⟨ v, fun i => lt_of_le_of_ne ( hv_nn i ) fun h => h_zero ⟨ i, h.symm ⟩, hv_ge, hρ_opt ⟩

/-
If v > 0 and Av > ρv strictly at all indices, then ρ is not optimal.
-/
lemma strict_ineq_contradicts_opt [Nontrivial n] (A : Matrix n n ℝ) (hA_nn : ∀ i j, 0 ≤ A i j)
    {ρ : ℝ} {v : n → ℝ} (hv_pos : ∀ i, 0 < v i)
    (hv_strict : ∀ i, ρ * v i < (A.mulVec v) i)
    (hρ_opt : ∀ t : ℝ, 0 ≤ t → (∃ w : n → ℝ, (∀ i, 0 ≤ w i) ∧ w ≠ 0 ∧
        ∀ i, t * w i ≤ (A.mulVec w) i) → t ≤ ρ) :
    False := by
  by_cases hρ_nonneg : 0 ≤ ρ;
  · -- Define δ_i = (Av)_i / v_i - ρ > 0 and let δ = Finset.inf' univ _ (fun i => (Av)_i / v_i - ρ) > 0 (minimum of positive values over a finite set).
    set δ := Finset.min' (Finset.univ.image (fun i => (A.mulVec v i) / v i - ρ)) (by
    exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ( Classical.arbitrary n ) ) ⟩) with hδ_def
    generalize_proofs at *;
    -- Since δ is the minimum of positive values, δ > 0.
    have hδ_pos : 0 < δ := by
      simp +zetaDelta at *;
      exact fun i => by rw [ lt_div_iff₀ ( hv_pos i ) ] ; linarith [ hv_strict i ] ;
    -- Then (ρ + δ) * v_i ≤ (Av)_i for all i.
    have h_ineq : ∀ i, (ρ + δ) * v i ≤ (A.mulVec v) i := by
      exact fun i => by nlinarith [ hv_pos i, hv_strict i, Finset.min'_le _ _ ( Finset.mem_image_of_mem ( fun i => ( A *ᵥ v ) i / v i - ρ ) ( Finset.mem_univ i ) ), mul_div_cancel₀ ( ( A *ᵥ v ) i ) ( ne_of_gt ( hv_pos i ) ) ] ;
    exact not_lt_of_ge ( hρ_opt ( ρ + δ ) ( by linarith ) ⟨ v, fun i => le_of_lt ( hv_pos i ), fun h => by simp_all +decide [ ne_of_gt ], h_ineq ⟩ ) ( by linarith );
  · contrapose! hρ_opt;
    refine' ⟨ 0, le_rfl, _, _ ⟩ <;> norm_num;
    · exact ⟨ fun _ => 1, fun _ => zero_le_one, fun h => by simpa using congr_fun h ( Classical.arbitrary n ), fun _ => Finset.sum_nonneg fun _ _ => mul_nonneg ( hA_nn _ _ ) zero_le_one ⟩;
    · linarith

/-
One step of the perturbation: given M nonempty proper, produce w with smaller M.
    M is the set of indices achieving equality in Av ≥ ρv.
-/
lemma shrink_minimizer_set [Nontrivial n] (A : Matrix n n ℝ) (hA : A.IsIrreducible)
    {ρ : ℝ} {v : n → ℝ} (hv_pos : ∀ i, 0 < v i)
    (hv_ge : ∀ i, ρ * v i ≤ (A.mulVec v) i)
    (hM_ne : (Finset.univ.filter (fun i => (A.mulVec v) i = ρ * v i)).Nonempty)
    (hM_proper : Finset.univ.filter (fun i => (A.mulVec v) i = ρ * v i) ≠ Finset.univ) :
    ∃ w : n → ℝ, (∀ i, 0 < w i) ∧
      (∀ i, ρ * w i ≤ (A.mulVec w) i) ∧
      (Finset.univ.filter (fun i => (A.mulVec w) i = ρ * w i)).card <
        (Finset.univ.filter (fun i => (A.mulVec v) i = ρ * v i)).card := by
  obtain ⟨i₀, hi₀M, j₀, hj₀M, hij₀, hAij₀⟩ : ∃ i₀ ∈ Finset.univ.filter (fun i => (A.mulVec v) i = ρ * v i), ∃ j₀ ∉ Finset.univ.filter (fun i => (A.mulVec v) i = ρ * v i), i₀ ≠ j₀ ∧ 0 < A i₀ j₀ := by
    have := exists_edge_to_complement hA ( Finset.univ.filter fun i => ( A.mulVec v ) i = ρ * v i ) ?_ ?_ <;> simp_all +decide [ Finset.ext_iff ];
    grind +ring;
  -- Choose ε > 0 small enough such that ε < gap / (|ρ| + Finset.sup' univ _ (fun i => A i j₀) + 1).
  obtain ⟨ε, hε_pos, hε_small⟩ : ∃ ε > 0, ε < ((A.mulVec v) j₀ - ρ * v j₀) / (|ρ| + (∑ i, |A i j₀|) + 1) := by
    exact exists_between ( div_pos ( sub_pos.mpr ( lt_of_le_of_ne ( hv_ge j₀ ) ( Ne.symm ( by aesop ) ) ) ) ( by linarith [ abs_nonneg ρ, show 0 ≤ ∑ i, |A i j₀| from Finset.sum_nonneg fun _ _ => abs_nonneg _ ] ) );
  refine' ⟨ fun i => v i + if i = j₀ then ε else 0, _, _, _ ⟩ <;> simp_all +decide [ Matrix.mulVec, dotProduct ];
  · exact fun i => add_pos_of_pos_of_nonneg ( hv_pos i ) ( by split_ifs <;> linarith );
  · intro i; specialize hv_ge i; simp_all +decide [ mul_add, Finset.sum_add_distrib ] ;
    split_ifs <;> simp_all +decide [ Finset.sum_add_distrib, mul_add, add_mul, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ];
    · rw [ lt_div_iff₀ ] at hε_small <;> cases abs_cases ρ <;> nlinarith [ hv_pos j₀, abs_le.mp ( Finset.single_le_sum ( fun i _ => abs_nonneg ( A i j₀ ) ) ( Finset.mem_univ j₀ ) ) ];
    · by_cases hAij₀_nonneg : 0 ≤ A i j₀;
      · exact le_add_of_le_of_nonneg hv_ge ( mul_nonneg hAij₀_nonneg hε_pos.le );
      · grind +suggestions;
  · refine' Finset.card_lt_card _;
    simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
    refine' ⟨ _, i₀, hi₀M, _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, mul_add ];
    · intro i hi; split_ifs at hi <;> simp_all +decide [ ne_of_gt ] ;
      · rw [ lt_div_iff₀ ] at hε_small <;> cases abs_cases ρ <;> nlinarith [ hv_pos j₀, hv_ge j₀, abs_le.mp ( Finset.single_le_sum ( fun i _ => abs_nonneg ( A i j₀ ) ) ( Finset.mem_univ j₀ ) ) ];
      · by_cases hAij₀ : A i j₀ < 0;
        · exact absurd ( hA.1 i j₀ ) ( by aesop );
        · nlinarith [ hv_ge i, hv_pos i, hv_pos j₀ ];
    · exact ⟨ ne_of_gt hAij₀, ne_of_gt hε_pos ⟩

/-
At a positive CW maximizer, equality holds: Av = ρv.
-/
lemma positive_cw_maximizer_eq [Nontrivial n] (A : Matrix n n ℝ) (hA : A.IsIrreducible)
    {ρ : ℝ} {v : n → ℝ} (hv_pos : ∀ i, 0 < v i)
    (hv_ge : ∀ i, ρ * v i ≤ (A.mulVec v) i)
    (hρ_opt : ∀ t : ℝ, 0 ≤ t → (∃ w : n → ℝ, (∀ i, 0 ≤ w i) ∧ w ≠ 0 ∧
        ∀ i, t * w i ≤ (A.mulVec w) i) → t ≤ ρ) :
    A.mulVec v = ρ • v := by
  -- By contradiction, assume there exists some $i$ such that $(A.mulVec v) i > ρ * v i$.
  by_contra h_contra;
  induction' k : Finset.card ( Finset.univ.filter ( fun i => ( A.mulVec v ) i = ρ * v i ) ) using Nat.strong_induction_on with k ih generalizing v;
  -- If the filter for v is univ, we're done.
  by_cases h_univ : Finset.univ.filter (fun i => (A.mulVec v) i = ρ * v i) = Finset.univ;
  · simp_all +decide [ Finset.ext_iff, funext_iff ];
  · obtain ⟨w, hw_pos, hw_ge, hw_lt⟩ : ∃ w : n → ℝ, (∀ i, 0 < w i) ∧ (∀ i, ρ * w i ≤ (A.mulVec w) i) ∧ (Finset.univ.filter (fun i => (A.mulVec w) i = ρ * w i)).card < (Finset.univ.filter (fun i => (A.mulVec v) i = ρ * v i)).card := by
      apply_rules [ shrink_minimizer_set ];
      by_cases h_empty : ∀ i, (A.mulVec v) i > ρ * v i;
      · exact False.elim ( strict_ineq_contradicts_opt A ( fun i j => by
          exact hA.nonneg i j ) hv_pos h_empty hρ_opt );
      · exact ⟨ Classical.choose ( not_forall.mp h_empty ), Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_antisymm ( le_of_not_gt ( Classical.choose_spec ( not_forall.mp h_empty ) ) ) ( hv_ge _ ) ⟩ ⟩;
    by_cases hw_eq : A.mulVec w = ρ • w;
    · simp_all +decide [ funext_iff ];
      exact absurd hw_lt ( not_lt_of_ge ( k ▸ Finset.card_le_univ _ ) );
    · exact ih _ ( by linarith ) hw_pos hw_ge hw_eq rfl

/-! ## Main theorem -/

theorem perron_frobenius_nontrivial_core [Nontrivial n]
    (A : Matrix n n ℝ) (hA : A.IsIrreducible) :
    ∃ (rho : ℝ) (v : n → ℝ),
      0 ≤ rho ∧ (∀ i, 0 ≤ v i) ∧ v ≠ 0 ∧ A.mulVec v = rho • v := by
  obtain ⟨ρ, v₀, hρ_nn, hv₀_nn, hv₀_norm, hv₀_ge, hρ_opt⟩ :=
    exists_optimal_cw_pair A hA.1
  obtain ⟨w, hw_pos, hw_ge, hρ_opt'⟩ :=
    extend_support_to_positive A hA hρ_nn hv₀_nn hv₀_norm hv₀_ge hρ_opt
  have hw_eq := positive_cw_maximizer_eq A hA hw_pos hw_ge hρ_opt'
  exact ⟨ρ, w, hρ_nn, fun i => le_of_lt (hw_pos i),
    ne_of_apply_ne (fun f => f (Classical.arbitrary n))
      (ne_of_gt (hw_pos (Classical.arbitrary n))),
    hw_eq⟩

end Submission.PerronCore