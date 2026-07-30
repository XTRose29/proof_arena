import Submission.SparsePhaseFamilies
import Submission.SparsePieceComparison

namespace Submission.Helpers

open LeanEval.Dynamics

lemma dist_sparseEdgePiece_left_le_linearNetPairRadius
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ)
    (m n H D : ℕ) (c : EucPlane) (base : Set EucPlane)
    (label : (k : Fin ((sparseSelectedSet
      T T_inv G m n H c).card - 1)) → Set EucPlane)
    (hlabel : label ∈ sparseEdgeLabels
      T T_inv G F R m n H D c)
    {y z : EucPlane}
    (hy : y ∈ sparseEdgePiece T T_inv G m n H c base label)
    (hz : z ∈ sparseEdgePiece T T_inv G m n H c base label)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1))
    (hgap : 1 < sparseEdgeIndexGap T T_inv G m n H c k) :
    dist
        (centeredOrbit T T_inv m n y
          ⟨H * sparseNodeIndex T T_inv G m n H c
            (sparseEdgeLeft T T_inv G m n H c k),
            sparseNodeIndex_lt T T_inv G m n H c _⟩)
        (centeredOrbit T T_inv m n z
          ⟨H * sparseNodeIndex T T_inv G m n H c
            (sparseEdgeLeft T T_inv G m n H c k),
            sparseNodeIndex_lt T T_inv G m n H c _⟩) ≤
      linearNetPairRadius R D
        (sparseEdgeTimeGap T T_inv G m n H c k) := by
  have hball := Fintype.mem_piFinset.mp hlabel k
  obtain ⟨w, _hw, hlabelEq⟩ := Finset.mem_image.mp hball
  have hylabel := mem_sparseEdgePiece_label
    T T_inv G m n H c base label hy k
  have hzlabel := mem_sparseEdgePiece_label
    T T_inv G m n H c base label hz k
  rw [← hlabelEq] at hylabel hzlabel
  have hyr := Metric.mem_closedBall.mp hylabel
  have hzr := Metric.mem_closedBall.mp hzlabel
  calc
    dist
        (centeredOrbit T T_inv m n y
          ⟨H * sparseNodeIndex T T_inv G m n H c
            (sparseEdgeLeft T T_inv G m n H c k),
            sparseNodeIndex_lt T T_inv G m n H c _⟩)
        (centeredOrbit T T_inv m n z
          ⟨H * sparseNodeIndex T T_inv G m n H c
            (sparseEdgeLeft T T_inv G m n H c k),
            sparseNodeIndex_lt T T_inv G m n H c _⟩) ≤
        dist
          (centeredOrbit T T_inv m n y
            ⟨H * sparseNodeIndex T T_inv G m n H c
              (sparseEdgeLeft T T_inv G m n H c k),
              sparseNodeIndex_lt T T_inv G m n H c _⟩) w +
          dist w
            (centeredOrbit T T_inv m n z
              ⟨H * sparseNodeIndex T T_inv G m n H c
                (sparseEdgeLeft T T_inv G m n H c k),
                sparseNodeIndex_lt T T_inv G m n H c _⟩) :=
      dist_triangle _ _ _
    _ ≤ scaledNetRadius R
          (sparseEdgeDepth T T_inv G m n H D c k) +
        scaledNetRadius R
          (sparseEdgeDepth T T_inv G m n H D c k) := by
      exact add_le_add hyr (by simpa [dist_comm] using hzr)
    _ = linearNetPairRadius R D
        (sparseEdgeTimeGap T T_inv G m n H c k) := by
      rw [sparseEdgeDepth, if_pos hgap]
      simp [linearNetPairRadius, two_mul]

/-- Raw path estimate for two points in one refined sparse-pattern piece.
All parameter choices are exposed as elementary scale inequalities so that
the global entropy argument can tune them independently. -/
lemma sparseEdgePiece_selected_path_displacement_le
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K S carrier : Set EucPlane}
    (hK_inv : T '' K = K) (hKS : K ⊆ S)
    (hS_convex : Convex ℝ S)
    (hcarrier : T '' carrier = carrier)
    (hsource : ∀ u ∈ carrier, SourceSplittingData T T_inv u)
    (hcov : ∀ u ∈ carrier,
      lyapunovStableComponent T T_inv (T u) ∘L fderiv ℝ T u =
          fderiv ℝ T u ∘L lyapunovStableComponent T T_inv u ∧
      lyapunovUnstableComponent T T_inv (T u) ∘L fderiv ℝ T u =
          fderiv ℝ T u ∘L lyapunovUnstableComponent T T_inv u)
    {M R : ℝ} (hM : 1 ≤ M) (hR : 0 < R)
    (hT_lipschitz : ∀ x ∈ K, ∀ y ∈ K,
      dist (T x) (T y) ≤ M * dist x y)
    (hderiv : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ M)
    (hderiv_lipschitz : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ M * dist x y)
    {lam1 lam2 eta : ℝ} {C : ℕ}
    (F : Finset EucPlane) (m n : ℕ) {H : ℕ} (hH : 0 < H) (D : ℕ)
    (c : EucPlane) (base : Set EucPlane)
    (label : (k : Fin ((sparseSelectedSet
      T T_inv (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
        m n H c).card - 1)) → Set EucPlane)
    (hlabel : label ∈ sparseEdgeLabels T T_inv
      (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
      F R m n H D c)
    {y z : EucPlane}
    (hy : y ∈ sparseEdgePiece T T_inv
      (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
      m n H c base label)
    (hz : z ∈ sparseEdgePiece T T_inv
      (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
      m n H c base label)
    (hyK : ∀ i : Fin (m + n), centeredOrbit T T_inv m n y i ∈ K)
    (hzK : ∀ i : Fin (m + n), centeredOrbit T T_inv m n z i ∈ K)
    (hyleftCarrier : T_inv^[m] y ∈ carrier)
    (hselectedG : ∀ i : Fin (sparseSelectedSet T T_inv
      (pesinFullShadowingBlock T T_inv lam1 lam2 eta C) m n H c).card,
      centeredOrbit T T_inv m n y
        ⟨H * sparseNodeIndex T T_inv
          (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
          m n H c i,
          sparseNodeIndex_lt T T_inv
            (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
            m n H c i⟩ ∈
        pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
    (hclose : ∀ i : Fin (m + n),
      dist (centeredOrbit T T_inv m n y i)
        (centeredOrbit T T_inv m n z i) ≤ R)
    (hselected : (sparseSelectedSet T T_inv
      (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
      m n H c).Nonempty)
    (hshortSmall : M ^ H * R ≤ 1)
    (hshortError :
      H * (M * (M ^ H * R)) * (2 * M) ^ (H + 1) ≤
        Real.exp ((lam2 + 6 * eta) * H))
    (hscaleR : 2 * R ≤ (4 : ℝ) ^ D)
    (hscaleM : M ≤ (4 : ℝ) ^ D)
    (hscaleConst : 4 * R * M ^ 2 ≤ (4 : ℝ) ^ D)
    (hscaleRate :
      4 * M ^ 2 * Real.exp (-(lam2 + 6 * eta)) ≤ (4 : ℝ) ^ D)
    {q : ℝ} (hq : 0 < q)
    (hAq : (4 * C : ℝ) / q ≤ 1 / 4)
    (hcross : ∀ g : ℕ, H ≤ g →
      (4 * C : ℝ) * q *
        Real.exp (((lam2 + 6 * eta) + (-lam1 + 6 * eta)) * g) ≤ 1 / 4)
    (hunstable : ∀ g : ℕ, H ≤ g →
      (C : ℝ) * Real.exp ((-lam1 + 6 * eta) * g) *
        Real.exp ((lam2 + 6 * eta) * g) ≤ 1 / 2) :
    let card := (sparseSelectedSet T T_inv
      (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
      m n H c).card
    let hcard : card - 1 + 1 = card := by
      have := Finset.card_pos.mpr hselected
      omega
    let node : Fin (card - 1 + 1) → ℕ := fun i =>
      sparseNodeIndex T T_inv
        (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
        m n H c (Fin.cast hcard i)
    ∀ i : Fin (card - 1 + 1),
      dist
          (centeredOrbit T T_inv m n y
            ⟨H * node i, by
              simpa [node] using sparseNodeIndex_lt T T_inv
                (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
                m n H c (Fin.cast hcard i)⟩)
          (centeredOrbit T T_inv m n z
            ⟨H * node i, by
              simpa [node] using sparseNodeIndex_lt T T_inv
                (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
                m n H c (Fin.cast hcard i)⟩) ≤
        R * (q ^ i.val *
            Real.exp ((lam2 + 6 * eta) *
              ((H * node i : ℕ) - H * node 0)) +
          q ^ (card - 1 - i.val) *
            Real.exp ((-lam1 + 6 * eta) *
              ((H * node (Fin.last (card - 1)) : ℕ) -
                H * node i))) := by
  classical
  dsimp only
  let G := pesinFullShadowingBlock T T_inv lam1 lam2 eta C
  let card := (sparseSelectedSet T T_inv G m n H c).card
  have hcardPos : 0 < card := by
    simpa [card, G] using Finset.card_pos.mpr hselected
  have hcard : card - 1 + 1 = card := by omega
  let node : Fin (card - 1 + 1) → ℕ := fun i =>
    sparseNodeIndex T T_inv G m n H c (Fin.cast hcard i)
  let t : Fin (card - 1 + 1) → ℕ := fun i => H * node i
  have ht : ∀ i j, i.val < j.val → t i < t j := by
    intro i j hij
    apply Nat.mul_lt_mul_of_pos_left _ hH
    exact strictMono_selectedGridIndex H (m + n)
      (centeredOrbitGoodTime T T_inv G m n c) (by
        simpa [node, sparseNodeIndex, sparseSelectedSet, G] using hij)
  have ht_node (i : Fin (card - 1 + 1)) :
      t i = H * node i := rfl
  have horbit_y (i : Fin (card - 1 + 1)) :
      T^[t i] (T_inv^[m] y) =
        centeredOrbit T T_inv m n y
          ⟨H * node i, by
            simpa [node, card, G] using sparseNodeIndex_lt T T_inv G
              m n H c (Fin.cast hcard i)⟩ := by
    rfl
  have horbit_z (i : Fin (card - 1 + 1)) :
      T^[t i] (T_inv^[m] z) =
        centeredOrbit T T_inv m n z
          ⟨H * node i, by
            simpa [node, card, G] using sparseNodeIndex_lt T T_inv G
              m n H c (Fin.cast hcard i)⟩ := by
    rfl
  let edgeGap : Fin (card - 1) → ℕ := fun k =>
    t k.succ - t k.castSucc
  have hedge_cast (k : Fin (card - 1)) :
      Fin.cast hcard k.castSucc =
        sparseEdgeLeft T T_inv G m n H c k := by
    apply Fin.ext
    rfl
  have hedge_succ (k : Fin (card - 1)) :
      Fin.cast hcard k.succ =
        sparseEdgeRight T T_inv G m n H c k := by
    apply Fin.ext
    rfl
  have hedgeGap (k : Fin (card - 1)) :
      edgeGap k = sparseEdgeTimeGap T T_inv G m n H c k := by
    dsimp [edgeGap, t, node]
    rw [hedge_cast, hedge_succ, ← Nat.mul_sub_left_distrib]
    rfl
  have hedgeGapH (k : Fin (card - 1)) : H ≤ edgeGap k := by
    rw [hedgeGap, sparseEdgeTimeGap]
    exact Nat.le_mul_of_pos_right H (by
      have hstrict := strictMono_selectedGridIndex H (m + n)
        (centeredOrbitGoodTime T T_inv G m n c)
        (show (sparseEdgeLeft T T_inv G m n H c k).val <
          (sparseEdgeRight T T_inv G m n H c k).val by
            simp [sparseEdgeLeft, sparseEdgeRight])
      simpa [sparseEdgeIndexGap, sparseNodeIndex] using
        Nat.sub_pos_of_lt hstrict)
  let edgeError : Fin (card - 1) → ℝ := fun k =>
    Real.exp ((lam2 + 6 * eta) * edgeGap k)
  have herror (k : Fin (card - 1)) :
      ‖clmPrefixProduct
            (orbitSecantStep T
              (T^[t k.castSucc] (T_inv^[m] y))
              (T^[t k.castSucc] (T_inv^[m] z)))
            (t k.succ - t k.castSucc) -
          fderiv ℝ (T^[t k.succ - t k.castSucc])
            (T^[t k.castSucc] (T_inv^[m] y))‖ ≤ edgeError k := by
    let left : Fin (m + n) :=
      ⟨H * sparseNodeIndex T T_inv G m n H c
        (sparseEdgeLeft T T_inv G m n H c k),
        sparseNodeIndex_lt T T_inv G m n H c _⟩
    have hyStart : T^[t k.castSucc] (T_inv^[m] y) =
        centeredOrbit T T_inv m n y left := by
      rw [horbit_y]
      apply congrArg (centeredOrbit T T_inv m n y)
      apply Fin.ext
      simp [node, left, hedge_cast]
    have hzStart : T^[t k.castSucc] (T_inv^[m] z) =
        centeredOrbit T T_inv m n z left := by
      rw [horbit_z]
      apply congrArg (centeredOrbit T T_inv m n z)
      apply Fin.ext
      simp [node, left, hedge_cast]
    by_cases hlong :
        1 < sparseEdgeIndexGap T T_inv G m n H c k
    · have hdist := dist_sparseEdgePiece_left_le_linearNetPairRadius
        T T_inv G F R m n H D c base label hlabel hy hz k hlong
      have htgap :
          t k.succ - t k.castSucc =
            sparseEdgeTimeGap T T_inv G m n H c k := by
        simpa only [edgeGap] using hedgeGap k
      rw [hyStart, hzStart]
      dsimp only [edgeError]
      rw [htgap, hedgeGap]
      apply (norm_orbitSecantPrefix_sub_fderiv_le_of_start_dist
        T hT_smooth hK_inv hKS hS_convex hM
          (mul_nonneg (by norm_num) (scaledNetRadius_pos hR _).le)
          hT_lipschitz hderiv hderiv_lipschitz
          (centeredOrbit T T_inv m n y left)
          (centeredOrbit T T_inv m n z left)
          (hyK left) (hzK left) hdist
          (mul_pow_linearNetPairRadius_le_one
            hM hR hscaleR hscaleM _)).trans
        (linearNetPairRadius_secant_budget
          hM hR hscaleConst hscaleRate _)
    · have hgapOne :
          sparseEdgeIndexGap T T_inv G m n H c k = 1 := by
        have hpos : 0 <
            sparseEdgeIndexGap T T_inv G m n H c k := by
          have hstrict := strictMono_selectedGridIndex H (m + n)
            (centeredOrbitGoodTime T T_inv G m n c)
            (show (sparseEdgeLeft T T_inv G m n H c k).val <
              (sparseEdgeRight T T_inv G m n H c k).val by
                simp [sparseEdgeLeft, sparseEdgeRight])
          simpa [sparseEdgeIndexGap, sparseNodeIndex] using
            Nat.sub_pos_of_lt hstrict
        omega
      have hgapH :
          sparseEdgeTimeGap T T_inv G m n H c k = H := by
        simp [sparseEdgeTimeGap, hgapOne]
      have hdist : dist
          (centeredOrbit T T_inv m n y left)
          (centeredOrbit T T_inv m n z left) ≤ R :=
        hclose left
      have htgap :
          t k.succ - t k.castSucc =
            sparseEdgeTimeGap T T_inv G m n H c k := by
        simpa only [edgeGap] using hedgeGap k
      rw [hyStart, hzStart]
      dsimp only [edgeError]
      rw [htgap, hedgeGap, hgapH]
      exact (norm_orbitSecantPrefix_sub_fderiv_le_of_start_dist
        T hT_smooth hK_inv hKS hS_convex hM hR.le
          hT_lipschitz hderiv hderiv_lipschitz
          (centeredOrbit T T_inv m n y left)
          (centeredOrbit T T_inv m n z left)
          (hyK left) (hzK left) hdist hshortSmall).trans hshortError
  have hpath := sparse_pesin_path_displacement_le
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hcarrier hsource hcov t ht edgeError
      (T_inv^[m] y) (T_inv^[m] z) hyleftCarrier
      (fun i => by
        rw [horbit_y]
        simpa [node, card, G] using hselectedG (Fin.cast hcard i))
      herror
      (fun k => le_rfl)
      (fun k => by
        dsimp [edgeError]
        exact hunstable (edgeGap k) (hedgeGapH k))
      hq hR.le hAq
      (fun k => hcross (edgeGap k) (hedgeGapH k))
      (by
        rw [horbit_y, horbit_z]
        simpa [dist_eq_norm, norm_sub_rev] using hclose
          ⟨H * node 0, by
            simpa [node, card, G] using sparseNodeIndex_lt T T_inv G
              m n H c (Fin.cast hcard 0)⟩)
      (by
        rw [horbit_y, horbit_z]
        simpa [dist_eq_norm, norm_sub_rev] using hclose
          ⟨H * node (Fin.last (card - 1)), by
            simpa [node, card, G] using sparseNodeIndex_lt T T_inv G
              m n H c (Fin.cast hcard (Fin.last (card - 1)))⟩)
  intro i
  have hi := hpath i
  rw [horbit_y, horbit_z] at hi
  simpa [dist_eq_norm, norm_sub_rev, t, ht_node, node, card, G] using hi

end Submission.Helpers
