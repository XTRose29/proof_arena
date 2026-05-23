import Mathlib
import Submission.DiagOp

/-! # Amplification trick for the von Neumann double commutant theorem -/

namespace Submission.Amplification

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-
For a star subalgebra S, T ∈ S'', and any single vector x,
    T(x) is in the closure of {A(x) : A ∈ S}.
-/
set_option maxHeartbeats 800000 in
lemma single_vector_in_closure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x : H) :
    T x ∈ closure ((fun (A : H →L[ℂ] H) => A x) '' (S : Set (H →L[ℂ] H))) := by
  -- Let $K = \overline{\text{span}}\{Ax : A \in S\}$.
  set K := Submodule.topologicalClosure (Submodule.span ℂ (Set.image (fun A : H →L[ℂ] H => A x) S));
  -- Since $K$ is closed and invariant under $S$, the orthogonal projection $P$ onto $K$ commutes with every $A \in S$.
  obtain ⟨P, hP⟩ : ∃ P : H →L[ℂ] H, (∀ y ∈ K, P y = y) ∧ (∀ y ∈ Kᗮ, P y = 0) ∧ (∀ A ∈ S, P ∘L A = A ∘L P) := by
    have hP_comm : ∀ A ∈ S, ∀ y ∈ K, A y ∈ K := by
      intro A hA y hy
      have hA_y : ∀ z ∈ Submodule.span ℂ (Set.image (fun A : H →L[ℂ] H => A x) S), A z ∈ Submodule.span ℂ (Set.image (fun A : H →L[ℂ] H => A x) S) := by
        intro z hz
        induction' hz using Submodule.span_induction with z hz ih;
        · rcases hz with ⟨ B, hB, rfl ⟩ ; exact Submodule.subset_span ⟨ A * B, S.mul_mem hA hB, by simp +decide ⟩ ;
        · simp +decide;
        · simpa only [ map_add ] using Submodule.add_mem _ ‹_› ‹_›;
        · aesop;
      have hA_y_closure : ∀ y ∈ K, A y ∈ K := by
        intro y hy
        have h_seq : ∃ seq : ℕ → H, (∀ n, seq n ∈ Submodule.span ℂ (Set.image (fun A : H →L[ℂ] H => A x) S)) ∧ Filter.Tendsto seq Filter.atTop (nhds y) := by
          exact mem_closure_iff_seq_limit.mp hy
        obtain ⟨ seq, hseq₁, hseq₂ ⟩ := h_seq;
        exact mem_closure_of_tendsto ( A.continuous.continuousAt.tendsto.comp hseq₂ ) ( Filter.Eventually.of_forall fun n => hA_y _ ( hseq₁ n ) );
      exact hA_y_closure y hy;
    have hP_comm : ∀ A ∈ S, ∀ y ∈ Kᗮ, A y ∈ Kᗮ := by
      intro A hA y hy
      have h_comm : ∀ z ∈ K, inner ℂ (A y) z = 0 := by
        intro z hz
        have h_comm : ⟪y, (star A) z⟫_ℂ = 0 := by
          have h_comm : (star A) z ∈ K := by
            exact hP_comm _ ( StarMemClass.star_mem hA ) _ hz;
          exact inner_eq_zero_symm.mp (hy ((star A) z) h_comm)
        convert h_comm using 1;
        simp +decide [ ContinuousLinearMap.star_eq_adjoint ];
        rw [ ContinuousLinearMap.adjoint_inner_right ];
      exact (Submodule.mem_orthogonal' K (A y)).mpr h_comm
    have hP_comm : ∃ P : H →L[ℂ] H, (∀ y ∈ K, P y = y) ∧ (∀ y ∈ Kᗮ, P y = 0) := by
      have hP_comm : ∀ y : H, ∃! p : H, p ∈ K ∧ y - p ∈ Kᗮ := by
        intro y
        obtain ⟨p, hp⟩ : ∃ p : H, p ∈ K ∧ y - p ∈ Kᗮ := by
          exact Submodule.HasOrthogonalProjection.exists_orthogonal y
        refine' ⟨ p, hp, fun q hq => _ ⟩;
        have h_eq : q - p ∈ K ∧ q - p ∈ Kᗮ := by
          exact ⟨ Submodule.sub_mem _ hq.1 hp.1, by simpa using Submodule.sub_mem _ hp.2 hq.2 ⟩;
        have := h_eq.2 ( q - p ) h_eq.1; simp_all +decide [ sub_eq_zero ] ;
      choose P hP₁ hP₂ using hP_comm;
      have hP_linear : ∀ y z : H, P (y + z) = P y + P z := by
        intro y z;
        rw [ ← hP₂ ];
        exact ⟨ Submodule.add_mem _ ( hP₁ y |>.1 ) ( hP₁ z |>.1 ), by simpa [ add_sub_add_comm ] using Submodule.add_mem _ ( hP₁ y |>.2 ) ( hP₁ z |>.2 ) ⟩;
      have hP_smul : ∀ c : ℂ, ∀ y : H, P (c • y) = c • P y := by
        intro c y;
        rw [ ← hP₂ ];
        exact ⟨ Submodule.smul_mem _ _ ( hP₁ y |>.1 ), by simpa [ smul_sub ] using Submodule.smul_mem _ _ ( hP₁ y |>.2 ) ⟩;
      have hP_cont : Continuous P := by
        have hP_cont : ∀ y : H, ‖P y‖ ≤ ‖y‖ := by
          intro y;
          have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ( P y ) ( y - P y ) ( by simpa using hP₁ y |>.2 ( P y ) ( hP₁ y |>.1 ) );
          norm_num at this; nlinarith [ norm_nonneg y, norm_nonneg ( y - P y ) ] ;
        refine' AddMonoidHomClass.continuous_of_bound ( show AddMonoidHom H H from { toFun := P, map_zero' := by simpa using hP_smul 0 0, map_add' := hP_linear } ) 1 fun y => by simpa using hP_cont y;
      refine' ⟨ { toFun := P, map_add' := hP_linear, map_smul' := hP_smul, cont := hP_cont }, _, _ ⟩;
      · exact fun y hy => Eq.symm ( hP₂ y y ⟨ hy, by simp ⟩ );
      · intro y hy;
        specialize hP₂ y 0 ; simp_all +decide [ Submodule.mem_orthogonal ];
    obtain ⟨ P, hP₁, hP₂ ⟩ := hP_comm;
    refine' ⟨ P, hP₁, hP₂, fun A hA => _ ⟩;
    ext y;
    -- Since $y \in H$, we can write $y = y_1 + y_2$ where $y_1 \in K$ and $y_2 \in K^\perp$.
    obtain ⟨y1, y2, hy1, hy2, hy⟩ : ∃ y1 y2 : H, y1 ∈ K ∧ y2 ∈ Kᗮ ∧ y = y1 + y2 := by
      have h_decomp : ∀ y : H, ∃ y1 y2 : H, y1 ∈ K ∧ y2 ∈ Kᗮ ∧ y = y1 + y2 := by
        intro y
        have h_orthogonal : K ⊔ Kᗮ = ⊤ := by
          exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
        have := Submodule.mem_sup.mp ( show y ∈ K ⊔ Kᗮ from h_orthogonal.symm ▸ Submodule.mem_top ) ; tauto;
      exact h_decomp y;
    simp +decide [ *, map_add ];
  -- Since $T \in S''$, $T$ commutes with $P$, so $T(Px) = P(Tx)$.
  have h_comm : T (P x) = P (T x) := by
    have h_comm : P ∈ (S : Set (H →L[ℂ] H)).centralizer := by
      intro A hA; specialize hP; have := hP.2.2 A hA; simp_all +decide [ ContinuousLinearMap.ext_iff ] ;
    exact congr_arg ( fun f => f x ) ( hT P h_comm ) ▸ rfl;
  -- Since $x \in K$, we have $Px = x$.
  have hPx : P x = x := by
    exact hP.1 x ( subset_closure <| Submodule.subset_span <| Set.mem_image_of_mem _ <| S.one_mem );
  -- Since $P(Tx) = Tx$, we have $Tx \in K$.
  have hTx_in_K : T x ∈ K := by
    have hTx_in_K : P (T x) ∈ K := by
      have hTx_in_K : ∀ y, P y ∈ K := by
        intro y;
        have hTx_in_K : ∀ y, P y ∈ K := by
          intro y
          have h_decomp : ∃ k ∈ K, ∃ k' ∈ Kᗮ, y = k + k' := by
            exact Submodule.exists_add_mem_mem_orthogonal y
          obtain ⟨ k, hk, k', hk', rfl ⟩ := h_decomp; simp +decide [ hP.1 k hk, hP.2.1 k' hk' ] ;
          exact hk;
        exact hTx_in_K y;
      exact hTx_in_K _;
    grind;
  refine' closure_mono _ hTx_in_K;
  intro y hy;
  refine' Submodule.span_induction _ _ _ _ hy;
  · exact fun y hy => hy;
  · exact ⟨ 0, S.zero_mem, by simp +decide ⟩;
  · rintro _ _ _ _ ⟨ A, hA, rfl ⟩ ⟨ B, hB, rfl ⟩ ; exact ⟨ A + B, S.add_mem hA hB, by simp +decide ⟩;
  · rintro a y hy ⟨ A, hA, rfl ⟩ ; exact ⟨ a • A, S.smul_mem hA a, by simp +decide ⟩ ;

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 800000 in
lemma orthogonality_key_claim (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x w : ι → H)
    (hw : ∀ A ∈ S, ∑ i : ι, @inner ℂ H _ (w i) (A (x i)) = 0) :
    ∑ i : ι, @inner ℂ H _ (w i) (T (x i)) = 0 :=
  Submission.DiagOp.orthogonality_key_claim S T hT x w hw

/-
For a star subalgebra S, T in S double prime, and any finite family of vectors,
    the tuple of T applied to x_i is in the closure of the set of tuples of A applied to x_i
    for A in S, in the product topology.
-/
lemma finite_vectors_in_closure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x : ι → H) :
    (fun i => T (x i)) ∈
    closure (Set.range (fun (A : ↥S) => fun i => (A : H →L[ℂ] H) (x i))) := by
  refine' mem_closure_iff_nhds.2 _;
  intro t ht;
  -- Fix an arbitrary $w : ι → H$.
  by_contra h_contra;
  -- By the Hahn-Banach theorem, there exists a continuous linear functional $f$ on $(ι → H)$ such that $f(T(x_i)) \neq f(A(x_i))$ for all $A \in S$.
  obtain ⟨f, hf⟩ : ∃ f : (ι → H) →L[ℂ] ℂ, f (fun i => T (x i)) ≠ 0 ∧ ∀ A : S, f (fun i => A.val (x i)) = 0 := by
    -- Since $t$ is a neighborhood of $T(x_i)$ and does not intersect the range of $A(x_i)$, the point $T(x_i)$ is not in the closure of the range of $A(x_i)$.
    have h_not_in_closure : (fun i => T (x i)) ∉ closure (Set.range (fun A : S => fun i => A.val (x i))) := by
      rw [ mem_closure_iff_nhds ];
      exact fun h => h_contra <| h t ht;
    have h_hahn_banach : ∀ (M : Submodule ℂ (ι → H)), IsClosed (M : Set (ι → H)) → ∀ (v : ι → H), v ∉ M → ∃ f : (ι → H) →L[ℂ] ℂ, f v ≠ 0 ∧ ∀ m ∈ M, f m = 0 := by
      intro M hM v hv_not_in_M
      have h_hahn_banach : ∃ f : (ι → H) →L[ℂ] ℂ, f v ≠ 0 ∧ ∀ m ∈ M, f m = 0 := by
        have h_quotient : ∃ f : (ι → H) ⧸ M →L[ℂ] ℂ, f (Submodule.Quotient.mk v) ≠ 0 := by
          have h_quotient : ∀ (v : (ι → H) ⧸ M), v ≠ 0 → ∃ f : (ι → H) ⧸ M →L[ℂ] ℂ, f v ≠ 0 := by
            exact fun v a => SeparatingDual.exists_ne_zero' v a
          exact h_quotient _ ( by simpa [ Submodule.Quotient.mk_eq_zero ] using hv_not_in_M )
        obtain ⟨ f, hf ⟩ := h_quotient;
        refine' ⟨ f.comp ( ContinuousLinearMap.mk ( Submodule.mkQ M ) _ ), _, _ ⟩ <;> simp_all +decide [ Submodule.Quotient.mk_eq_zero ];
        · exact continuous_quotient_mk';
        · intro m hm; erw [ show Submodule.Quotient.mk m = 0 from by aesop ] ; simp +decide ;
      exact h_hahn_banach;
    specialize h_hahn_banach (Submodule.topologicalClosure (Submodule.span ℂ (Set.range (fun A : S => fun i => A.val (x i)))));
    refine' h_hahn_banach ( isClosed_closure ) _ _ |> fun ⟨ f, hf₁, hf₂ ⟩ => ⟨ f, hf₁, fun A => hf₂ _ _ ⟩;
    · refine' fun h => h_not_in_closure _;
      refine' closure_mono _ h;
      intro y hy;
      induction hy using Submodule.span_induction;
      · assumption;
      · exact ⟨ 0, by ext; simp +decide ⟩;
      · rename_i hx hy hx' hy';
        obtain ⟨ A, rfl ⟩ := hx'
        obtain ⟨ B, rfl ⟩ := hy'
        use A + B;
        ext i; simp +decide [ add_smul ] ;
      · rename_i c y hy₁ hy₂;
        obtain ⟨ A, rfl ⟩ := hy₂;
        exact ⟨ ⟨ c • A, by exact S.smul_mem A.2 c ⟩, by ext i; simp +decide ⟩;
    · exact subset_closure ( Submodule.subset_span ⟨ A, rfl ⟩ );
  -- By the Riesz representation theorem, there exists a vector $w : ι → H$ such that $f(v) = \sum_{i} \langle w_i, v_i \rangle$ for all $v : ι → H$.
  obtain ⟨w, hw⟩ : ∃ w : ι → H, ∀ v : ι → H, f v = ∑ i, inner ℂ (w i) (v i) := by
    have h_riesz : ∀ i : ι, ∃ w_i : H, ∀ v : H, f (Pi.single i v) = inner ℂ w_i v := by
      intro i;
      have h_riesz : ∀ (g : H →L[ℂ] ℂ), ∃ w : H, ∀ v : H, g v = inner ℂ w v := by
        intro g;
        use ( ContinuousLinearMap.adjoint g ) 1;
        simp +decide [ ContinuousLinearMap.adjoint_inner_left ];
      convert h_riesz ( f.comp ( ContinuousLinearMap.single ℂ ( fun _ => H ) i ) ) using 1;
    choose w hw using h_riesz;
    use w;
    intro v;
    rw [ ← Finset.sum_congr rfl fun i _ => hw i ( v i ) ];
    rw [ ← map_sum ];
    exact congr_arg f ( by ext i; simp +decide [ Pi.single_apply ] );
  exact hf.1 ( by simpa [ hw ] using orthogonality_key_claim S T hT x w fun A hA => by simpa [ hw ] using hf.2 ⟨ A, hA ⟩ )

/-
T in S double prime implies T is in the PwConv-closure of S.
-/
lemma double_commutant_in_pwconv_closure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T ∈
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      (S : Set (H →L[ℂ] H))) := by
  -- Fix an arbitrary finite subset F of H.
  intro F
  simp [PointwiseConvergenceCLM.continuous_of_continuous_eval, PointwiseConvergenceCLM.tendsto_iff_forall_tendsto] at *;
  intro hF hSF;
  have h_approx : ∀ (s : Finset H) (ε : ℝ), 0 < ε → ∃ A ∈ S, ∀ x ∈ s, ‖T x - A x‖ < ε := by
    intro s ε hε;
    have := finite_vectors_in_closure S T hT ( fun i => s.toList.get i );
    rw [ mem_closure_iff_nhds ] at this;
    specialize this ( Set.pi Set.univ fun i => Metric.ball ( T ( s.toList.get i ) ) ε ) ?_;
    · simp +decide [ nhds_pi, Metric.mem_nhds_iff ];
      exact fun i => ⟨ ε, hε, Set.Subset.rfl ⟩;
    · obtain ⟨ A, hA ⟩ := this;
      rcases hA with ⟨ hA₁, ⟨ A, rfl ⟩ ⟩;
      refine' ⟨ A, A.2, fun x hx => _ ⟩;
      have := List.mem_iff_get.mp ( Finset.mem_toList.mpr hx );
      obtain ⟨ n, rfl ⟩ := this; simpa [ dist_eq_norm' ] using hA₁ n ( Set.mem_univ n ) ;
  have h_closure : ∀ (s : Finset H) (ε : ℝ), 0 < ε → ∃ A ∈ F, ∀ x ∈ s, ‖T x - A x‖ < ε := by
    exact fun s ε hε => by obtain ⟨ A, hA₁, hA₂ ⟩ := h_approx s ε hε; exact ⟨ A, hSF hA₁, hA₂ ⟩ ;
  contrapose! h_closure;
  have := @PointwiseConvergenceCLM.isEmbedding_coeFn;
  specialize this ( RingHom.id ℂ ) H H;
  have := this.isClosed_iff.mp hF;
  obtain ⟨ t, ht, rfl ⟩ := this;
  have := ht.isOpen_compl.mem_nhds h_closure;
  rw [ nhds_pi ] at this;
  rw [ Filter.mem_pi ] at this;
  obtain ⟨ s, hs, t, ht, hst ⟩ := this;
  -- Since $t$ is a neighborhood of $T$, there exists an $\epsilon > 0$ such that for all $x \in s$, $B(T x, \epsilon) \subseteq t x$.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ x ∈ s, Metric.ball (T x) ε ⊆ t x := by
    choose! ε hε using fun x => Metric.mem_nhds_iff.mp ( ht x );
    rcases hs.exists_finset_coe with ⟨ s, rfl ⟩;
    rcases s.eq_empty_or_nonempty with ( rfl | ⟨ x, hx ⟩ ) <;> [ exact ⟨ 1, zero_lt_one, by simp +decide ⟩ ; exact ⟨ Finset.min' ( s.image ε ) ⟨ ε x, Finset.mem_image_of_mem ε hx ⟩, by have := Finset.min'_mem ( s.image ε ) ⟨ ε x, Finset.mem_image_of_mem ε hx ⟩ ; aesop, fun y hy => Set.Subset.trans ( Metric.ball_subset_ball ( Finset.min'_le _ _ ( Finset.mem_image_of_mem ε hy ) ) ) ( hε y |>.2 ) ⟩ ];
  use hs.toFinset, ε;
  simp_all +decide [ Set.subset_def ];
  exact fun A hA => not_forall_not.mp fun h => hst _ ( fun x hx => hε x hx _ <| by simpa [ dist_eq_norm' ] using lt_of_not_ge fun h' => h x <| by aesop ) hA

end Submission.Amplification