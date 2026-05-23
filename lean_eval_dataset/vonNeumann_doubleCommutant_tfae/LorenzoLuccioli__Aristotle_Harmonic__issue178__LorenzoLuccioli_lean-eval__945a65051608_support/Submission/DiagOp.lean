import Mathlib

/-! # Amplification trick for the von Neumann double commutant theorem -/

namespace Submission.DiagOp

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diag (A : H →L[ℂ] H) : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H)) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun (i : ι) => A.comp (ContinuousLinearMap.proj i))).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).toContinuousLinearMap)

@[simp] lemma diag_ofLp (A : H →L[ℂ] H) (v : PiLp 2 (fun _ : ι => H)) (i : ι) :
    (diag A v).ofLp i = A (v.ofLp i) := by
  simp [diag, PiLp.continuousLinearEquiv, WithLp.linearEquiv]; rfl

set_option maxHeartbeats 400000 in
lemma diag_comp (A B : H →L[ℂ] H) (v : PiLp 2 (fun _ : ι => H)) :
    diag A (diag B v) = diag (A * B) v := by
  apply (WithLp.equiv 2 (ι → H)).injective; funext i
  simp [ContinuousLinearMap.mul_apply]

/-! ## Orthogonal projection onto a closed invariant submodule -/

/-- The orthogonal projection onto M, viewed as an operator on PiLp 2 H. -/
def projM (M : Submodule ℂ (PiLp 2 (fun _ : ι => H)))
    (hM_closed : IsClosed (M : Set (PiLp 2 (fun _ : ι => H)))) :
    (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H)) :=
  haveI : M.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace M
  M.subtypeL.comp M.orthogonalProjection

lemma projM_mem (M : Submodule ℂ (PiLp 2 (fun _ : ι => H)))
    (hM_closed : IsClosed (M : Set (PiLp 2 (fun _ : ι => H)))) (v : PiLp 2 (fun _ : ι => H)) :
    projM M hM_closed v ∈ M := by
  haveI : M.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace M
  exact Subtype.coe_prop _

lemma projM_eq_self (M : Submodule ℂ (PiLp 2 (fun _ : ι => H)))
    (hM_closed : IsClosed (M : Set (PiLp 2 (fun _ : ι => H))))
    (v : PiLp 2 (fun _ : ι => H)) (hv : v ∈ M) :
    projM M hM_closed v = v := by
  haveI : M.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace M
  simp [projM]
  exact congrArg Subtype.val (Submodule.orthogonalProjection_mem_subspace_eq_self ⟨v, hv⟩)

/-! ## M^perp is invariant under diag(A) when M is invariant under diag(A*) -/

set_option maxHeartbeats 800000 in
lemma orthogonal_invariant_of_star_invariant
    (M : Submodule ℂ (PiLp 2 (fun _ : ι => H)))
    (A : H →L[ℂ] H)
    (hM_star : ∀ v ∈ M, diag (ι := ι) (star A) v ∈ M)
    (v : PiLp 2 (fun _ : ι => H)) (hv : v ∈ Mᗮ) :
    diag (ι := ι) A v ∈ Mᗮ := by
  intro w hw;
  convert hv ( diag ( star A ) w ) ( hM_star w hw ) using 1;
  simp +decide [ PiLp.inner_apply, ContinuousLinearMap.star_eq_adjoint ];
  simp +decide only [ContinuousLinearMap.adjoint_inner_left]

/-! ## projM commutes with diag(A) for S-invariant M -/

set_option maxHeartbeats 800000 in
lemma projM_comm_diag
    (M : Submodule ℂ (PiLp 2 (fun _ : ι => H)))
    (hM_closed : IsClosed (M : Set (PiLp 2 (fun _ : ι => H))))
    (A : H →L[ℂ] H)
    (hM_inv : ∀ v ∈ M, diag (ι := ι) A v ∈ M)
    (hM_orth_inv : ∀ v ∈ Mᗮ, diag (ι := ι) A v ∈ Mᗮ) :
    (projM M hM_closed).comp (diag (ι := ι) A) =
    (diag (ι := ι) A).comp (projM M hM_closed) := by
  -- By definition of $projM$, we know that for any $v \in M$, $projM M hM_closed v = v$.
  have h_projM_self : ∀ v ∈ M, (projM M hM_closed) v = v := by
    exact fun v a => projM_eq_self M hM_closed v a
  -- By definition of $projM$, we know that for any $v \in M^\perp$, $projM M hM_closed v = 0$.
  have h_projM_zero : ∀ v ∈ Mᗮ, (projM M hM_closed) v = 0 := by
    intro v hv
    have h_orthogonal : (M.orthogonalProjection v) = 0 := by
      exact Submodule.orthogonalProjection_eq_zero_iff.mpr hv
    simp [h_orthogonal, projM];
  -- By definition of $projM$, we know that for any $v \in H$, $v = v_M + v_\perp$ where $v_M \in M$ and $v_\perp \in M^\perp$.
  have h_decomp : ∀ v : PiLp 2 (fun _ : ι => H), ∃ v_M v_perp : PiLp 2 (fun _ : ι => H), v = v_M + v_perp ∧ v_M ∈ M ∧ v_perp ∈ Mᗮ := by
    intro v
    obtain ⟨v_M, hv_M⟩ : ∃ v_M ∈ M, v - v_M ∈ Mᗮ := by
      exact Submodule.HasOrthogonalProjection.exists_orthogonal v
    exact ⟨ v_M, v - v_M, by simp +decide, hv_M ⟩;
  ext v
  obtain ⟨v_M, v_perp, hv, hv_M, hv_perp⟩ := h_decomp v
  simp [hv, hv_M, hv_perp, h_projM_self, h_projM_zero];
  rw [ h_projM_self _ ( hM_inv _ hv_M ), h_projM_zero _ ( hM_orth_inv _ hv_perp ) ] ; simp +decide [ diag_ofLp ]

/-! ## Matrix entry extraction -/

/-- The (i,j) matrix entry of an operator on PiLp 2 H:
    P_{ij}(h) = (P(embed_j(h)))_i -/
def matEntry (P : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H)))
    (i j : ι) : H →L[ℂ] H :=
  -- proj_i ∘ P ∘ embed_j
  let embed_j : H →L[ℂ] PiLp 2 (fun _ : ι => H) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℂ (fun _ : ι => H) j)
  let proj_i : PiLp 2 (fun _ : ι => H) →L[ℂ] H :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => H) i).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).toContinuousLinearMap
  proj_i.comp (P.comp embed_j)

set_option maxHeartbeats 800000 in
lemma matEntry_apply (P : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H)))
    (i j : ι) (h : H) :
    matEntry P i j h = (P ((WithLp.equiv 2 (ι → H)).symm (Pi.single j h))).ofLp i := by
  simp [matEntry, PiLp.continuousLinearEquiv, WithLp.linearEquiv]
  rfl

set_option maxHeartbeats 800000 in
lemma apply_eq_sum_matEntry (P : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H)))
    (v : PiLp 2 (fun _ : ι => H)) (i : ι) :
    (P v).ofLp i = ∑ j, matEntry P i j (v.ofLp j) := by
  -- By definition of $v$, we can write it as a sum of its components.
  have hv : v = ∑ j, (WithLp.equiv 2 (ι → H)).symm (Pi.single j (v.ofLp j)) := by
    ext j;
    simp +decide [ Pi.single_apply ];
  conv_lhs => rw [ hv, map_sum ];
  simp +decide [ matEntry_apply ]

/-! ## P commutes with diag(A) implies matrix entries commute with A -/

set_option maxHeartbeats 800000 in
lemma matEntry_comm_of_projM_comm
    (P : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H)))
    (A : H →L[ℂ] H)
    (hcomm : P.comp (diag (ι := ι) A) = (diag (ι := ι) A).comp P)
    (i j : ι) :
    matEntry P i j * A = A * matEntry P i j := by
  refine' ContinuousLinearMap.ext fun x => _;
  have h_diag_embed : ∀ x : H, (diag A ((WithLp.equiv 2 (ι → H)).symm (Pi.single j x))) = (WithLp.equiv 2 (ι → H)).symm (Pi.single j (A x)) := by
    intro x; exact (by
    ext i; by_cases hi : i = j <;> simp +decide [ hi, diag_ofLp ] ;);
  replace hcomm := congr_arg ( fun f => f ( ( WithLp.equiv 2 ( ι → H ) ).symm ( Pi.single j x ) ) ) hcomm ; simp_all +decide [ ContinuousLinearMap.ext_iff ];
  convert congr_arg ( fun v => ( v.ofLp i ) ) hcomm using 1

/-! ## T commutes with matrix entries implies diag(T) commutes with P -/

set_option maxHeartbeats 800000 in
lemma diag_comm_of_matEntry_comm
    (P : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H)))
    (T : H →L[ℂ] H)
    (hcomm : ∀ i j, matEntry P i j * T = T * matEntry P i j) :
    P.comp (diag (ι := ι) T) = (diag (ι := ι) T).comp P := by
  -- By definition of matrix multiplication and the hypothesis hcomm, we can show that the action of P on the block matrix representation of diag T is the same as the action of diag T on the block matrix representation of P.
  have h_action : ∀ v : PiLp 2 (fun _ : ι => H), ∀ i, (P (diag T v)).ofLp i = (diag T (P v)).ofLp i := by
    intro v i
    have h_eq : (P (diag T v)).ofLp i = ∑ j, matEntry P i j (T (v.ofLp j)) := by
      convert apply_eq_sum_matEntry P ( diag T v ) i using 1;
    have h_eq' : (diag T (P v)).ofLp i = T ((P v).ofLp i) := by
      exact diag_ofLp T (P v) i
    rw [ h_eq, h_eq', apply_eq_sum_matEntry ];
    simp_all +decide [ funext_iff, ContinuousLinearMap.ext_iff ];
  exact ContinuousLinearMap.ext fun v => by ext i; exact h_action v i;

/-! ## Main theorem: diag(T) preserves invariant subspace -/

set_option maxHeartbeats 3200000 in
lemma diag_T_in_invariant_subspace
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (M : Submodule ℂ (PiLp 2 (fun _ : ι => H)))
    (hM_closed : IsClosed (M : Set (PiLp 2 (fun _ : ι => H))))
    (hM_inv : ∀ A ∈ S, ∀ v ∈ M, diag (ι := ι) A v ∈ M)
    (hM_star_inv : ∀ A ∈ S, ∀ v ∈ M, diag (ι := ι) (star A) v ∈ M)
    (v₀ : PiLp 2 (fun _ : ι => H)) (hv₀ : v₀ ∈ M) :
    diag (ι := ι) T v₀ ∈ M := by
  -- Step 1: projM commutes with diag(A) for all A ∈ S
  have hP_comm : ∀ A ∈ S, (projM M hM_closed).comp (diag (ι := ι) A) =
      (diag (ι := ι) A).comp (projM M hM_closed) := by
    intro A hA
    exact projM_comm_diag M hM_closed A (hM_inv A hA) (orthogonal_invariant_of_star_invariant M A (hM_star_inv A hA))
  -- Step 2: matrix entries of projM are in S'
  have hentry_in_comm : ∀ i j, matEntry (projM M hM_closed) i j ∈
      (S : Set (H →L[ℂ] H)).centralizer := by
    intro i j A hA
    exact (matEntry_comm_of_projM_comm _ A (hP_comm A hA) i j).symm
  -- Step 3: T commutes with matrix entries (since T ∈ S'')
  have hT_comm_entry : ∀ i j, matEntry (projM M hM_closed) i j * T =
      T * matEntry (projM M hM_closed) i j := by
    intro i j
    exact hT _ (hentry_in_comm i j)
  -- Step 4: diag(T) commutes with projM
  have hP_comm_T := diag_comm_of_matEntry_comm (projM M hM_closed) T hT_comm_entry
  -- Step 5: Conclude
  have h1 : projM M hM_closed (diag T v₀) = diag T (projM M hM_closed v₀) := by
    exact ContinuousLinearMap.ext_iff.mp hP_comm_T v₀
  rw [projM_eq_self M hM_closed v₀ hv₀] at h1
  rw [← h1]
  exact projM_mem M hM_closed _

/-! ## Helper lemmas for the main orthogonality claim -/

lemma closure_inv_of_set_inv {X : Type*} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) (s : Set X) (hs : ∀ x ∈ s, f x ∈ s)
    (x : X) (hx : x ∈ closure s) : f x ∈ closure s :=
  (image_closure_subset_closure_image hf).trans
    (closure_mono (fun _ ⟨y, hy, hxy⟩ => hxy ▸ hs y hy)) ⟨x, hx, rfl⟩

lemma span_diag_inv (S : StarSubalgebra ℂ (H →L[ℂ] H)) (A : H →L[ℂ] H) (hA : A ∈ S)
    (x' u : PiLp 2 (fun _ : ι => H))
    (hu : u ∈ Submodule.span ℂ ((fun B => diag B x') '' (S : Set (H →L[ℂ] H)))) :
    diag A u ∈ Submodule.span ℂ ((fun B => diag B x') '' (S : Set (H →L[ℂ] H))) := by
  induction hu using Submodule.span_induction with
  | mem u hu => obtain ⟨B, hB, rfl⟩ := hu; rw [diag_comp]; exact Submodule.subset_span ⟨A * B, S.mul_mem hA hB, rfl⟩
  | zero => simp
  | add _ _ _ _ h1 h2 => simp [map_add]; exact Submodule.add_mem _ h1 h2
  | smul c _ _ h1 => simp [map_smul]; exact Submodule.smul_mem _ c h1

set_option maxHeartbeats 3200000 in
theorem orthogonality_key_claim (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x w : ι → H)
    (hw : ∀ A ∈ S, ∑ i : ι, @inner ℂ H _ (w i) (A (x i)) = 0) :
    ∑ i : ι, @inner ℂ H _ (w i) (T (x i)) = 0 := by
  set x' : PiLp 2 (fun _ : ι => H) := (WithLp.equiv 2 (ι → H)).symm x
  set w' : PiLp 2 (fun _ : ι => H) := (WithLp.equiv 2 (ι → H)).symm w
  set span_S := Submodule.span ℂ ((fun (A : H →L[ℂ] H) => diag A x') '' (S : Set (H →L[ℂ] H)))
  set M := Submodule.topologicalClosure span_S
  have hgoal : ∑ i, @inner ℂ H _ (w i) (T (x i)) = @inner ℂ _ _ w' (diag T x') := by
    simp [PiLp.inner_apply, diag_ofLp, x', w']
  rw [hgoal]
  have hw_orth : ∀ v ∈ M, @inner ℂ _ _ w' v = 0 := by
    apply (isClosed_eq (continuous_const.inner continuous_id) continuous_const).closure_subset_iff.mpr
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨A, hA, rfl⟩ := hv
      simp [PiLp.inner_apply, diag_ofLp, w', x']; exact hw A hA
    | zero => simp
    | add u v _ _ hu hv =>
      show @inner ℂ _ _ w' (u + v) = 0
      simp only [id] at hu hv
      rw [inner_add_right, hu, hv, add_zero]
    | smul c v _ hv =>
      show @inner ℂ _ _ w' (c • v) = 0
      simp only [id] at hv
      rw [inner_smul_right, hv, mul_zero]
  have hTx_in_M : diag T x' ∈ M := by
    apply diag_T_in_invariant_subspace S T hT M isClosed_closure
    · intro A hA v hv
      exact closure_inv_of_set_inv (diag A) (diag A).continuous (span_S : Set _)
        (fun u hu => span_diag_inv S A hA x' u hu) v (show v ∈ closure (span_S : Set _) from hv)
    · intro A hA v hv
      exact closure_inv_of_set_inv (diag (star A)) (diag (star A)).continuous (span_S : Set _)
        (fun u hu => span_diag_inv S (star A) (StarMemClass.star_mem hA) x' u hu) v
        (show v ∈ closure (span_S : Set _) from hv)
    · apply Submodule.le_topologicalClosure
      have : diag (1 : H →L[ℂ] H) x' = x' := by
        apply (WithLp.equiv 2 (ι → H)).injective; funext i; simp
      rw [← this]; exact Submodule.subset_span ⟨1, S.one_mem, rfl⟩
  exact hw_orth _ hTx_in_M

end

end Submission.DiagOp