import Submission.SparsePatternCover
import Submission.SparsePesinRecurrence

namespace Submission.Helpers

open LeanEval.Dynamics

/-- The first element of a nonempty `Fin` type. -/
def cardPathZero {M : ℕ} (hM : 0 < M) : Fin M :=
  ⟨0, hM⟩

/-- The last element of a nonempty `Fin` type, with the cardinality rather
than a predecessor supplied as the parameter. -/
def cardPathLast {M : ℕ} (hM : 0 < M) : Fin M :=
  ⟨M - 1, Nat.sub_lt hM (Nat.succ_pos 0)⟩

/-- The preceding point of an interior point of a nonempty finite path. -/
def cardPathPrev {M : ℕ} (i : Fin M) : Fin M :=
  ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- The following point of a nonempty finite path, clamped at its last
element. -/
def cardPathNext {M : ℕ} (hM : 0 < M) (i : Fin M) : Fin M :=
  ⟨min (i.val + 1) (M - 1), by omega⟩

/-- The left endpoint of an edge in a cardinality-indexed finite path. -/
def cardPathEdgeLeft {M : ℕ} (k : Fin (M - 1)) : Fin M :=
  ⟨k.val, by omega⟩

/-- The right endpoint of an edge in a cardinality-indexed finite path. -/
def cardPathEdgeRight {M : ℕ} (k : Fin (M - 1)) : Fin M :=
  ⟨k.val + 1, by omega⟩

/-- Two points in one ball of a scaled net are separated by at most twice
the terminal net radius. -/
lemma dist_le_two_scaledNetRadius_of_mem
    {F : Finset EucPlane} {c : EucPlane} {R : ℝ} {n : ℕ}
    {A : Set EucPlane} (hA : A ∈ scaledNetBalls F c R n)
    {x y : EucPlane} (hx : x ∈ A) (hy : y ∈ A) :
    dist x y ≤ 2 * scaledNetRadius R n := by
  obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hA
  have hxz := Metric.mem_closedBall.mp hx
  have hyz := Metric.mem_closedBall.mp hy
  calc
    dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
    _ ≤ scaledNetRadius R n + scaledNetRadius R n := by
      gcongr
      simpa [dist_comm] using hyz
    _ = 2 * scaledNetRadius R n := by ring

/-- The generic cardinality-indexed endpoints agree with the endpoints used
by a sparse edge. -/
lemma sparseEdgeLeft_eq_cardPathEdgeLeft
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) :
    sparseEdgeLeft T T_inv G m n H c k = cardPathEdgeLeft k :=
  Fin.ext rfl

lemma sparseEdgeRight_eq_cardPathEdgeRight
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) :
    sparseEdgeRight T T_inv G m n H c k = cardPathEdgeRight k :=
  Fin.ext rfl

lemma sparseEdgeTimeGap_eq_path_time_sub
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) :
    sparseEdgeTimeGap T T_inv G m n H c k =
      H * sparseNodeIndex T T_inv G m n H c (cardPathEdgeRight k) -
        H * sparseNodeIndex T T_inv G m n H c (cardPathEdgeLeft k) := by
  rw [sparseEdgeTimeGap, sparseEdgeIndexGap,
    sparseEdgeLeft_eq_cardPathEdgeLeft,
    sparseEdgeRight_eq_cardPathEdgeRight]
  exact Nat.mul_sub_left_distrib _ _ _

/-- A selected-grid predicate holding at time zero makes the selected path
nonempty. -/
lemma zero_mem_selectedGridIndices
    {H L : ℕ} (hL : 0 < L) {good : ℕ → Prop} (hgood : good 0) :
    0 ∈ selectedGridIndices H L good := by
  apply mem_selectedGridIndices_iff.mpr
  simpa using And.intro hL (And.intro hL hgood)

/-- The coarse-grid point immediately to the left of a time inside the
window is a grid index. -/
lemma div_mem_gridIndexSet
    {H L a : ℕ} (ha : a < L) :
    a / H ∈ gridIndexSet H L := by
  apply mem_gridIndexSet_iff.mpr
  constructor
  · exact (Nat.div_le_self a H).trans_lt ha
  · exact (Nat.mul_div_le a H).trans_lt ha

/-- The rank of a member in the increasing enumeration of a finite set. -/
noncomputable def selectedGridRank
    (H L : ℕ) (good : ℕ → Prop) {j : ℕ}
    (hj : j ∈ selectedGridIndices H L good) :
    Fin (selectedGridIndices H L good).card :=
  (selectedGridIndices H L good).orderIsoOfFin rfl |>.symm ⟨j, hj⟩

lemma selectedGridIndex_selectedGridRank
    (H L : ℕ) (good : ℕ → Prop) {j : ℕ}
    (hj : j ∈ selectedGridIndices H L good) :
    selectedGridIndex H L good (selectedGridRank H L good hj) = j := by
  rw [selectedGridIndex, ← Finset.coe_orderIsoOfFin_apply]
  simp [selectedGridRank]

/-- If zero is selected, it is the first enumerated grid index. -/
lemma selectedGridIndex_cardPathZero_eq_zero
    {H L : ℕ} {good : ℕ → Prop}
    (hcard : 0 < (selectedGridIndices H L good).card)
    (hzero : 0 ∈ selectedGridIndices H L good) :
    selectedGridIndex H L good
        (cardPathZero hcard) = 0 := by
  let S := selectedGridIndices H L good
  have hS : S.Nonempty := Finset.card_pos.mp hcard
  have hmin : S.min' hS = 0 := by
    apply (Finset.min'_eq_iff S hS 0).mpr
    exact ⟨hzero, fun b _hb => Nat.zero_le b⟩
  rw [selectedGridIndex]
  change S.orderEmbOfFin rfl ⟨0, hcard⟩ = 0
  rw [Finset.orderEmbOfFin_zero]
  simpa only using hmin

/-- If the last possible coarse-grid point is selected, it is the final
enumerated grid index. -/
lemma selectedGridIndex_cardPathLast_eq_div_pred
    {H L : ℕ} (hH : 0 < H) (hL : 0 < L) {good : ℕ → Prop}
    (hcard : 0 < (selectedGridIndices H L good).card)
    (hlast : (L - 1) / H ∈ selectedGridIndices H L good) :
    selectedGridIndex H L good
        (cardPathLast hcard) =
      (L - 1) / H := by
  let S := selectedGridIndices H L good
  have hS : S.Nonempty := Finset.card_pos.mp hcard
  have hmax : S.max' hS = (L - 1) / H := by
    apply (Finset.max'_eq_iff S hS ((L - 1) / H)).mpr
    refine ⟨hlast, fun b hb => ?_⟩
    have hbtime := (mem_selectedGridIndices_iff.mp hb).2.1
    apply (Nat.le_div_iff_mul_le hH).mpr
    rw [Nat.mul_comm]
    omega
  rw [selectedGridIndex]
  change (selectedGridIndices H L good).orderEmbOfFin rfl
      ⟨(selectedGridIndices H L good).card - 1,
        Nat.sub_lt hcard (Nat.succ_pos 0)⟩ = (L - 1) / H
  rw [Finset.orderEmbOfFin_last]
  simpa only [S] using hmax
  all_goals exact hcard

/-- A cardinality-indexed form of
`finite_exponential_path_comparison_nat`.  It avoids repeatedly transporting
a naturally occurring nonempty path of cardinality `M` to `Fin (N + 1)`. -/
lemma finite_exponential_path_comparison_card
    {M : ℕ} (hM : 0 < M)
    (d : Fin M → ℝ) (t : Fin M → ℕ)
    {A q a b delta : ℝ}
    (hd : ∀ i, 0 ≤ d i) (hA : 0 ≤ A) (hq : 0 < q)
    (hdelta : 0 ≤ delta)
    (ht : StrictMono t)
    (hAq : A / q ≤ 1 / 4)
    (hcross_left : ∀ i, 0 < i.val → i.val + 1 < M →
      A * q * Real.exp ((a + b) *
        ((t i - t (cardPathPrev i) : ℕ) : ℝ)) ≤ 1 / 4)
    (hcross_right : ∀ i, 0 < i.val → i.val + 1 < M →
      A * q * Real.exp ((a + b) *
        ((t (cardPathNext hM i) - t i : ℕ) : ℝ)) ≤ 1 / 4)
    (hboundary_left : d (cardPathZero hM) ≤ delta)
    (hboundary_right : d (cardPathLast hM) ≤ delta)
    (hstep : ∀ i, 0 < i.val → i.val + 1 < M →
      d i ≤
        (A * Real.exp (a *
          ((t i - t (cardPathPrev i) : ℕ) : ℝ))) * d (cardPathPrev i) +
        (A * Real.exp (b *
          ((t (cardPathNext hM i) - t i : ℕ) : ℝ))) *
            d (cardPathNext hM i)) :
    ∀ i, d i ≤ delta *
      (q ^ i.val *
          Real.exp (a * ((t i : ℝ) - t (cardPathZero hM))) +
        q ^ (M - 1 - i.val) *
          Real.exp (b * ((t (cardPathLast hM) : ℝ) - t i))) := by
  let N := M - 1
  have hNM : N + 1 = M := by
    dsimp [N]
    omega
  let e : Fin (N + 1) → Fin M := Fin.cast hNM
  let d' : Fin (N + 1) → ℝ := fun i => d (e i)
  let t' : Fin (N + 1) → ℕ := fun i => t (e i)
  have he_val (i : Fin (N + 1)) : (e i).val = i.val := rfl
  have he_zero : e 0 = cardPathZero hM := by
    apply Fin.ext
    rfl
  have he_last : e (Fin.last N) = cardPathLast hM := by
    apply Fin.ext
    simp [e, cardPathLast, N]
  have he_prev (i : Fin (N + 1)) :
      e (pathPrev i) = cardPathPrev (e i) := by
    apply Fin.ext
    rfl
  have he_next (i : Fin (N + 1)) (_hi : i.val < N) :
      e (pathNext i) = cardPathNext hM (e i) := by
    apply Fin.ext
    change (pathNext i).val = min ((e i).val + 1) (M - 1)
    rw [he_val]
    change min (i.val + 1) N = min (i.val + 1) (M - 1)
    rfl
  have ht' : ∀ i j : Fin (N + 1), i.val < j.val → t' i < t' j := by
    intro i j hij
    exact ht (by simpa [e] using hij)
  have hmain := finite_exponential_path_comparison_nat
    d' t' (fun i => hd (e i)) hA hq hdelta ht' hAq
    (fun i hi0 hiN => by
      have hei0 : 0 < (e i).val := by rw [he_val]; exact hi0
      have heiN : (e i).val + 1 < M := by
        rw [he_val]
        dsimp [N] at hiN
        omega
      simpa [d', t', he_prev] using
        hcross_left (e i) hei0 heiN)
    (fun i hi0 hiN => by
      have hei0 : 0 < (e i).val := by rw [he_val]; exact hi0
      have heiN : (e i).val + 1 < M := by
        rw [he_val]
        dsimp [N] at hiN
        omega
      simpa [d', t', he_next i hiN] using
        hcross_right (e i) hei0 heiN)
    (by simpa [d', he_zero] using hboundary_left)
    (by simpa [d', he_last] using hboundary_right)
    (fun i hi0 hiN => by
      have hei0 : 0 < (e i).val := by rw [he_val]; exact hi0
      have heiN : (e i).val + 1 < M := by
        rw [he_val]
        dsimp [N] at hiN
        omega
      simpa [d', t', he_prev, he_next i hiN] using
        hstep (e i) hei0 heiN)
  intro i
  let j : Fin (N + 1) := Fin.cast hNM.symm i
  have hej : e j = i := by simp [e, j]
  have hjval : j.val = i.val := rfl
  have hlast_cast : t' (Fin.last N) = t (cardPathLast hM) := by
    simp [t', he_last]
  have hzero_cast : t' 0 = t (cardPathZero hM) := by
    simp [t', he_zero]
  simpa [d', t', hej, hjval, hlast_cast, hzero_cast, N] using hmain j

/-- A cardinality-indexed form of `sparse_pesin_neighbor_recurrence`. -/
lemma sparse_pesin_neighbor_recurrence_card
    {M : ℕ} (hM : 0 < M)
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {carrier : Set EucPlane} (hcarrier : T '' carrier = carrier)
    (hsource : ∀ z ∈ carrier, SourceSplittingData T T_inv z)
    (hcov : ∀ z ∈ carrier,
      lyapunovStableComponent T T_inv (T z) ∘L fderiv ℝ T z =
          fderiv ℝ T z ∘L lyapunovStableComponent T T_inv z ∧
      lyapunovUnstableComponent T T_inv (T z) ∘L fderiv ℝ T z =
          fderiv ℝ T z ∘L lyapunovUnstableComponent T T_inv z)
    {lam1 lam2 eta : ℝ} {C : ℕ}
    (t : Fin M → ℕ) (ht : StrictMono t)
    (edgeError : Fin (M - 1) → ℝ)
    (x y : EucPlane)
    (hxcarrier : x ∈ carrier)
    (hxG : ∀ i, T^[t i] x ∈
      pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
    (herror : ∀ k : Fin (M - 1),
      ‖clmPrefixProduct
            (orbitSecantStep T
              (T^[t (cardPathEdgeLeft k)] x)
              (T^[t (cardPathEdgeLeft k)] y))
            (t (cardPathEdgeRight k) - t (cardPathEdgeLeft k)) -
          fderiv ℝ
            (T^[t (cardPathEdgeRight k) - t (cardPathEdgeLeft k)])
            (T^[t (cardPathEdgeLeft k)] x)‖ ≤ edgeError k)
    (hstableError : ∀ k : Fin (M - 1),
      edgeError k ≤ Real.exp ((lam2 + 6 * eta) *
        ((t (cardPathEdgeRight k) -
          t (cardPathEdgeLeft k) : ℕ) : ℝ)))
    (hunstableError : ∀ k : Fin (M - 1),
      (C : ℝ) * Real.exp ((-lam1 + 6 * eta) *
          ((t (cardPathEdgeRight k) -
            t (cardPathEdgeLeft k) : ℕ) : ℝ)) * edgeError k ≤ 1 / 2) :
    ∀ i : Fin M, 0 < i.val → i.val + 1 < M →
      ‖T^[t i] y - T^[t i] x‖ ≤
        (4 * C) * Real.exp ((lam2 + 6 * eta) *
            ((t i - t (cardPathPrev i) : ℕ) : ℝ)) *
          ‖T^[t (cardPathPrev i)] y - T^[t (cardPathPrev i)] x‖ +
        (4 * C) * Real.exp ((-lam1 + 6 * eta) *
            ((t (cardPathNext hM i) - t i : ℕ) : ℝ)) *
          ‖T^[t (cardPathNext hM i)] y -
            T^[t (cardPathNext hM i)] x‖ := by
  cases M with
  | zero => omega
  | succ N =>
      have hmain := sparse_pesin_neighbor_recurrence
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right
          hcarrier hsource hcov t
          (fun i j hij => ht hij) edgeError x y hxcarrier hxG
          (by
            intro k
            have hleft : cardPathEdgeLeft (M := N + 1) k = k.castSucc :=
              Fin.ext rfl
            have hright : cardPathEdgeRight (M := N + 1) k = k.succ :=
              Fin.ext rfl
            simpa only [hleft, hright] using herror k)
          (by
            intro k
            have hleft : cardPathEdgeLeft (M := N + 1) k = k.castSucc :=
              Fin.ext rfl
            have hright : cardPathEdgeRight (M := N + 1) k = k.succ :=
              Fin.ext rfl
            simpa only [hleft, hright] using hstableError k)
          (by
            intro k
            have hleft : cardPathEdgeLeft (M := N + 1) k = k.castSucc :=
              Fin.ext rfl
            have hright : cardPathEdgeRight (M := N + 1) k = k.succ :=
              Fin.ext rfl
            simpa only [hleft, hright] using hunstableError k)
      intro i hi0 hiM
      have hiN : i.val < N := by omega
      simpa [cardPathPrev, cardPathNext, pathPrev, pathNext,
        min_eq_left (Nat.succ_le_iff.mpr hiN)] using hmain i hi0 hiN

lemma sparseSelected_time_sub_ge
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    {m n H : ℕ} (c : EucPlane)
    {i j : Fin (sparseSelectedSet T T_inv G m n H c).card}
    (hij : i.val < j.val) :
    H ≤
      H * sparseNodeIndex T T_inv G m n H c j -
        H * sparseNodeIndex T T_inv G m n H c i := by
  have hindex :
      sparseNodeIndex T T_inv G m n H c i <
        sparseNodeIndex T T_inv G m n H c j :=
    strictMono_selectedGridIndex H (m + n)
      (centeredOrbitGoodTime T T_inv G m n c) hij
  have hdiff : 1 ≤
      sparseNodeIndex T T_inv G m n H c j -
        sparseNodeIndex T T_inv G m n H c i := by omega
  calc
    H = H * 1 := by simp
    _ ≤ H * (sparseNodeIndex T T_inv G m n H c j -
        sparseNodeIndex T T_inv G m n H c i) :=
      Nat.mul_le_mul_left H hdiff
    _ = H * sparseNodeIndex T T_inv G m n H c j -
        H * sparseNodeIndex T T_inv G m n H c i :=
      Nat.mul_sub_left_distrib _ _ _

lemma norm_sparseSelected_orbit_sub_le_of_mem_centeredJoin_atom
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (P : Finset (Set EucPlane))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hP_diam : ∀ A ∈ P, Metric.ediam A ≤ ENNReal.ofReal delta)
    {m n H : ℕ} (c : EucPlane) {A : Set EucPlane}
    (hA : A ∈ centeredJoin T T_inv P m n)
    {y z : EucPlane} (hy : y ∈ A) (hz : z ∈ A)
    (i : Fin (sparseSelectedSet T T_inv G m n H c).card) :
    ‖T^[H * sparseNodeIndex T T_inv G m n H c i] (T_inv^[m] z) -
        T^[H * sparseNodeIndex T T_inv G m n H c i] (T_inv^[m] y)‖ ≤
      delta := by
  exact norm_centeredOrbit_sub_le_of_mem_centeredJoin_atom
    T T_inv P hdelta hP_diam hA hy hz
      ⟨H * sparseNodeIndex T T_inv G m n H c i,
        sparseNodeIndex_lt T T_inv G m n H c i⟩

set_option maxHeartbeats 4000000 in
/-- A sparse labeled piece has the exponential finite-path diameter bound.
All quantitative hypotheses are independent of the orbit length, which is
essential when this lemma is used in a Hausdorff tail cover. -/
lemma ediam_sparseEdgePiece_le_path_bound
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K S carrier G : Set EucPlane}
    (hK_inv : T '' K = K) (hKS : K ⊆ S) (hS_convex : Convex ℝ S)
    (hcarrier : T '' carrier = carrier) (hcarrierK : carrier ⊆ K)
    (hsource : ∀ z ∈ carrier, SourceSplittingData T T_inv z)
    (hcov : ∀ z ∈ carrier,
      lyapunovStableComponent T T_inv (T z) ∘L fderiv ℝ T z =
          fderiv ℝ T z ∘L lyapunovStableComponent T T_inv z ∧
      lyapunovUnstableComponent T T_inv (T z) ∘L fderiv ℝ T z =
          fderiv ℝ T z ∘L lyapunovUnstableComponent T T_inv z)
    {Lip : ℝ} (hLip : 1 ≤ Lip)
    (hT_lipschitz : ∀ x ∈ K, ∀ y ∈ K,
      dist (T x) (T y) ≤ Lip * dist x y)
    (hderiv : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ Lip)
    (hderiv_lipschitz : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ Lip * dist x y)
    (P : Finset (Set EucPlane)) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hP_diam : ∀ A ∈ P, Metric.ediam A ≤ ENNReal.ofReal delta)
    {lam1 lam2 eta q R : ℝ} {C D m n H : ℕ}
    (hH : 0 < H) (hR : 0 < R) (hq : 0 < q)
    (hG : G = pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
    (hab : lam2 + 6 * eta + (-lam1 + 6 * eta) < 0)
    (hAq : (4 * C : ℝ) / q ≤ 1 / 4)
    (hcrossH : (4 * C : ℝ) * q *
      Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) * H) ≤ 1 / 4)
    (hunstableH : (C : ℝ) *
      Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) * H) ≤ 1 / 2)
    (hshort_small : Lip ^ H * delta ≤ 1)
    (hshort_error :
      (H : ℝ) * (Lip * (Lip ^ H * delta)) * (2 * Lip) ^ (H + 1) ≤
        Real.exp ((lam2 + 6 * eta) * H))
    (hscaleR : 2 * R ≤ (4 : ℝ) ^ D)
    (hscaleLip : Lip ≤ (4 : ℝ) ^ D)
    (hscaleConst : 4 * R * Lip ^ 2 ≤ (4 : ℝ) ^ D)
    (hscaleRate :
      4 * Lip ^ 2 * Real.exp (-(lam2 + 6 * eta)) ≤ (4 : ℝ) ^ D)
    {A base : Set EucPlane}
    (hA : A ∈ centeredJoin T T_inv P m n)
    (hbaseA : base ⊆ A) (hbaseCarrier : base ⊆ carrier)
    (F : Finset EucPlane) (c : EucPlane)
    (label : (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) →
      Set EucPlane)
    (hlabel : label ∈ sparseEdgeLabels T T_inv G F R m n H D c)
    (hpath : 0 < (sparseSelectedSet T T_inv G m n H c).card)
    (ic : Fin (sparseSelectedSet T T_inv G m n H c).card)
    (hcenter :
      sparseNodeIndex T T_inv G m n H c ic = m / H)
    (hzero :
      sparseNodeIndex T T_inv G m n H c (cardPathZero hpath) = 0)
    (hlast :
      sparseNodeIndex T T_inv G m n H c (cardPathLast hpath) =
        (m + n - 1) / H)
    (hselectedGood : ∀ y ∈ base,
      ∀ i : Fin (sparseSelectedSet T T_inv G m n H c).card,
        centeredOrbit T T_inv m n y
          ⟨H * sparseNodeIndex T T_inv G m n H c i,
            sparseNodeIndex_lt T T_inv G m n H c i⟩ ∈ G) :
    Metric.ediam
        (sparseEdgePiece T T_inv G m n H c base label) ≤
      ENNReal.ofReal
        (Lip ^ H * delta *
          (q ^ ic.val *
              Real.exp ((lam2 + 6 * eta) *
                (H * sparseNodeIndex T T_inv G m n H c ic : ℕ)) +
            q ^ ((sparseSelectedSet T T_inv G m n H c).card - 1 - ic.val) *
              Real.exp ((-lam1 + 6 * eta) *
                ((H * ((m + n - 1) / H) : ℕ) -
                  H * sparseNodeIndex T T_inv G m n H c ic)))) := by
  let Mpath := (sparseSelectedSet T T_inv G m n H c).card
  let t : Fin Mpath → ℕ := fun i =>
    H * sparseNodeIndex T T_inv G m n H c i
  let a := lam2 + 6 * eta
  let b := -lam1 + 6 * eta
  let edgeError : Fin (Mpath - 1) → ℝ := fun k =>
    Real.exp (a * ((t (cardPathEdgeRight k) -
      t (cardPathEdgeLeft k) : ℕ) : ℝ))
  have hLip_nonneg : 0 ≤ Lip := zero_le_one.trans hLip
  have ht : StrictMono t :=
    strictMono_selectedGridTime hH (m + n)
      (centeredOrbitGoodTime T T_inv G m n c)
  have hcarrier_inv : T_inv '' carrier = carrier :=
    inverse_image_eq_of_image_eq hT_left hcarrier
  have horbitCarrier (y : EucPlane) (hy : y ∈ base) (j : ℕ) :
      T^[j] (T_inv^[m] y) ∈ carrier := by
    have hleft : T_inv^[m] y ∈ carrier := by
      rw [← image_iterate_eq_of_image_eq T_inv hcarrier_inv m]
      exact ⟨y, hbaseCarrier hy, rfl⟩
    rw [← image_iterate_eq_of_image_eq T hcarrier j]
    exact ⟨T_inv^[m] y, hleft, rfl⟩
  have horbitK (y : EucPlane) (hy : y ∈ base) (j : ℕ) :
      T^[j] (T_inv^[m] y) ∈ K :=
    hcarrierK (horbitCarrier y hy j)
  have hcenter_time_le : t ic ≤ m := by
    dsimp [t]
    rw [hcenter]
    exact Nat.mul_div_le m H
  apply Metric.ediam_le_of_forall_dist_le
  intro y hy z hz
  have hybase := mem_sparseEdgePiece_base T T_inv G m n H c base label hy
  have hzbase := mem_sparseEdgePiece_base T T_inv G m n H c base label hz
  let y0 := T_inv^[m] y
  let z0 := T_inv^[m] z
  let d : Fin Mpath → ℝ := fun i => ‖T^[t i] z0 - T^[t i] y0‖
  have hd (i : Fin Mpath) : 0 ≤ d i := norm_nonneg _
  have horbit_eq (w : EucPlane) (i : Fin Mpath) :
      T^[t i] (T_inv^[m] w) =
        centeredOrbit T T_inv m n w
          ⟨H * sparseNodeIndex T T_inv G m n H c i,
            sparseNodeIndex_lt T T_inv G m n H c i⟩ := rfl
  have hd_atom (i : Fin Mpath) : d i ≤ delta := by
    dsimp [d, y0, z0]
    exact norm_sparseSelected_orbit_sub_le_of_mem_centeredJoin_atom
      T T_inv G P hdelta hP_diam c hA
        (hbaseA hybase) (hbaseA hzbase) i
  have hgap_ge (k : Fin (Mpath - 1)) :
      H ≤ t (cardPathEdgeRight k) - t (cardPathEdgeLeft k) := by
    apply sparseSelected_time_sub_ge T T_inv G c
    change k.val < k.val + 1
    omega
  have herror (k : Fin (Mpath - 1)) :
      ‖clmPrefixProduct
            (orbitSecantStep T
              (T^[t (cardPathEdgeLeft k)] y0)
              (T^[t (cardPathEdgeLeft k)] z0))
            (t (cardPathEdgeRight k) - t (cardPathEdgeLeft k)) -
          fderiv ℝ
            (T^[t (cardPathEdgeRight k) - t (cardPathEdgeLeft k)])
            (T^[t (cardPathEdgeLeft k)] y0)‖ ≤ edgeError k := by
    let gap := t (cardPathEdgeRight k) - t (cardPathEdgeLeft k)
    have hyK : T^[t (cardPathEdgeLeft k)] y0 ∈ K := by
      exact horbitK y hybase _
    have hzK : T^[t (cardPathEdgeLeft k)] z0 ∈ K := by
      exact horbitK z hzbase _
    by_cases hlong :
        1 < sparseEdgeIndexGap T T_inv G m n H c k
    · have htime :
          gap = sparseEdgeTimeGap T T_inv G m n H c k := by
        dsimp [gap, t]
        exact (sparseEdgeTimeGap_eq_path_time_sub
          T T_inv G m n H c k).symm
      have hdepth :
          sparseEdgeDepth T T_inv G m n H D c k = D * (gap + 1) := by
        rw [sparseEdgeDepth, if_pos hlong, ← htime]
      have hklabel :
          label k ∈ sparseEdgeBalls T T_inv G F R m n H D c k :=
        Fintype.mem_piFinset.mp hlabel k
      have hyleft := mem_sparseEdgePiece_label
        T T_inv G m n H c base label hy k
      have hzleft := mem_sparseEdgePiece_label
        T T_inv G m n H c base label hz k
      have hpair :
          dist (T^[t (cardPathEdgeLeft k)] y0)
              (T^[t (cardPathEdgeLeft k)] z0) ≤
            linearNetPairRadius R D gap := by
        rw [horbit_eq, horbit_eq]
        rw [sparseEdgeLeft_eq_cardPathEdgeLeft] at hyleft hzleft
        have hdist := dist_le_two_scaledNetRadius_of_mem
          hklabel hyleft hzleft
        simpa [sparseEdgeBalls, hdepth, linearNetPairRadius] using hdist
      have hsmall := mul_pow_linearNetPairRadius_le_one
        hLip hR hscaleR hscaleLip gap
      have hraw := norm_orbitSecantPrefix_sub_fderiv_le_of_start_dist
        T hT_smooth hK_inv hKS hS_convex hLip
          (mul_nonneg (by norm_num) (scaledNetRadius_pos hR _).le)
          hT_lipschitz hderiv hderiv_lipschitz
          (T^[t (cardPathEdgeLeft k)] y0)
          (T^[t (cardPathEdgeLeft k)] z0) hyK hzK hpair hsmall
      exact hraw.trans (by
        exact linearNetPairRadius_secant_budget
          hLip hR hscaleConst hscaleRate gap)
    · have hindex_pos :
          0 < sparseEdgeIndexGap T T_inv G m n H c k := by
        rw [sparseEdgeIndexGap]
        have hmono := strictMono_selectedGridIndex H (m + n)
          (centeredOrbitGoodTime T T_inv G m n c)
          (show (sparseEdgeLeft T T_inv G m n H c k).val <
              (sparseEdgeRight T T_inv G m n H c k).val by
            simp [sparseEdgeLeft, sparseEdgeRight])
        exact Nat.sub_pos_of_lt hmono
      have hindex :
          sparseEdgeIndexGap T T_inv G m n H c k = 1 := by omega
      have htime : gap = H := by
        dsimp [gap, t]
        rw [← sparseEdgeTimeGap_eq_path_time_sub
          T T_inv G m n H c k, sparseEdgeTimeGap, hindex]
        simp
      have hpair :
          dist (T^[t (cardPathEdgeLeft k)] y0)
              (T^[t (cardPathEdgeLeft k)] z0) ≤ delta := by
        rw [dist_eq_norm]
        dsimp [t, y0, z0]
        simpa [norm_sub_rev] using
          norm_sparseSelected_orbit_sub_le_of_mem_centeredJoin_atom
            T T_inv G P hdelta hP_diam c hA
              (hbaseA hybase) (hbaseA hzbase) (cardPathEdgeLeft k)
      have hraw := norm_orbitSecantPrefix_sub_fderiv_le_of_start_dist
        T hT_smooth hK_inv hKS hS_convex hLip hdelta
          hT_lipschitz hderiv hderiv_lipschitz
          (T^[t (cardPathEdgeLeft k)] y0)
          (T^[t (cardPathEdgeLeft k)] z0) hyK hzK hpair (by
            simpa [htime] using hshort_small)
      have hbound := hraw.trans (by
        simpa [htime] using hshort_error)
      have htime' :
          t (cardPathEdgeRight k) - t (cardPathEdgeLeft k) = H := by
        simpa [gap] using htime
      rw [htime']
      simpa [edgeError, a, htime'] using hbound
  have hstableError (k : Fin (Mpath - 1)) :
      edgeError k ≤ Real.exp ((lam2 + 6 * eta) *
        ((t (cardPathEdgeRight k) -
          t (cardPathEdgeLeft k) : ℕ) : ℝ)) := by
    rfl
  have hunstableError (k : Fin (Mpath - 1)) :
      (C : ℝ) * Real.exp ((-lam1 + 6 * eta) *
          ((t (cardPathEdgeRight k) -
            t (cardPathEdgeLeft k) : ℕ) : ℝ)) * edgeError k ≤ 1 / 2 := by
    have hge := hgap_ge k
    have hexp :
        Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) *
            (t (cardPathEdgeRight k) - t (cardPathEdgeLeft k) : ℕ)) ≤
          Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) * H) := by
      apply Real.exp_le_exp.mpr
      have hcast : (H : ℝ) ≤
          (t (cardPathEdgeRight k) - t (cardPathEdgeLeft k) : ℕ) := by
        exact_mod_cast hge
      nlinarith
    calc
      (C : ℝ) * Real.exp ((-lam1 + 6 * eta) *
            ((t (cardPathEdgeRight k) -
              t (cardPathEdgeLeft k) : ℕ) : ℝ)) * edgeError k =
          (C : ℝ) * Real.exp
            ((lam2 + 6 * eta + (-lam1 + 6 * eta)) *
              (t (cardPathEdgeRight k) -
                t (cardPathEdgeLeft k) : ℕ)) := by
            dsimp [edgeError, a]
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring
      _ ≤ (C : ℝ) * Real.exp
          ((lam2 + 6 * eta + (-lam1 + 6 * eta)) * H) := by
        gcongr
      _ ≤ 1 / 2 := hunstableH
  have hxG (i : Fin Mpath) :
      T^[t i] y0 ∈ pesinFullShadowingBlock T T_inv lam1 lam2 eta C := by
    dsimp [y0]
    rw [horbit_eq]
    simpa only [hG] using hselectedGood y hybase i
  have hrec := sparse_pesin_neighbor_recurrence_card
    hpath T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hcarrier hsource hcov t ht edgeError y0 z0
      (by
        dsimp [y0]
        exact horbitCarrier y hybase 0)
      hxG herror hstableError hunstableError
  have hcross_gap {i j : Fin Mpath} (hij : i.val < j.val) :
      (4 * C : ℝ) * q *
          Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) *
            ((t j - t i : ℕ) : ℝ)) ≤ 1 / 4 := by
    have hge := sparseSelected_time_sub_ge T T_inv G c hij
    have hcast : (H : ℝ) ≤ (t j - t i : ℕ) := by
      exact_mod_cast hge
    have hexp : Real.exp
        ((lam2 + 6 * eta + (-lam1 + 6 * eta)) *
          ((t j - t i : ℕ) : ℝ)) ≤
        Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) * H) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact (mul_le_mul_of_nonneg_left hexp
      (mul_nonneg (by positivity) hq.le)).trans hcrossH
  have hcomparison := finite_exponential_path_comparison_card
    hpath d t hd (show 0 ≤ (4 * C : ℝ) by positivity) hq hdelta ht hAq
    (fun i hi0 hiM => by
      apply hcross_gap
      dsimp [cardPathPrev]
      omega)
    (fun i hi0 hiM => by
      apply hcross_gap
      dsimp [cardPathNext]
      omega)
    (hd_atom (cardPathZero hpath))
    (hd_atom (cardPathLast hpath))
    (fun i hi0 hiM => hrec i hi0 hiM)
  have hcenter_bound := hcomparison ic
  have hcenter_y :
      T^[m - t ic] (T^[t ic] y0) = y := by
    dsimp [y0]
    rw [← Function.iterate_add_apply]
    rw [Nat.sub_add_cancel hcenter_time_le]
    exact hT_right.iterate m y
  have hcenter_z :
      T^[m - t ic] (T^[t ic] z0) = z := by
    dsimp [z0]
    rw [← Function.iterate_add_apply]
    rw [Nat.sub_add_cancel hcenter_time_le]
    exact hT_right.iterate m z
  have hiterate := dist_iterate_le_pow_of_lipschitz_on_invariant
    T hK_inv hLip_nonneg hT_lipschitz
      (m - t ic) (T^[t ic] y0) (horbitK y hybase _)
        (T^[t ic] z0) (horbitK z hzbase _)
  rw [hcenter_y, hcenter_z] at hiterate
  have hpow : Lip ^ (m - t ic) ≤ Lip ^ H := by
    apply pow_le_pow_right₀ hLip
    dsimp [t] at hcenter_time_le
    have hmod := Nat.mod_lt m hH
    have hdecomp := Nat.mod_add_div m H
    have hrem : m - H * (m / H) < H := by omega
    simpa [t, hcenter] using hrem.le
  have hdist_d : dist y z ≤ Lip ^ H * d ic := by
    calc
      dist y z ≤ Lip ^ (m - t ic) * dist (T^[t ic] y0) (T^[t ic] z0) :=
        hiterate
      _ = Lip ^ (m - t ic) * d ic := by
        dsimp [d]
        rw [dist_eq_norm, norm_sub_rev]
      _ ≤ Lip ^ H * d ic := by
        gcongr
  calc
    dist y z ≤ Lip ^ H * d ic := hdist_d
    _ ≤ Lip ^ H * (delta *
        (q ^ ic.val *
            Real.exp (a * ((t ic : ℝ) - t (cardPathZero hpath))) +
          q ^ (Mpath - 1 - ic.val) *
            Real.exp (b * ((t (cardPathLast hpath) : ℝ) - t ic)))) := by
      exact mul_le_mul_of_nonneg_left hcenter_bound (pow_nonneg hLip_nonneg H)
    _ = Lip ^ H * delta *
          (q ^ ic.val *
              Real.exp ((lam2 + 6 * eta) *
                (H * sparseNodeIndex T T_inv G m n H c ic : ℕ)) +
            q ^ ((sparseSelectedSet T T_inv G m n H c).card - 1 - ic.val) *
              Real.exp ((-lam1 + 6 * eta) *
                ((H * ((m + n - 1) / H) : ℕ) -
                  H * sparseNodeIndex T T_inv G m n H c ic))) := by
      dsimp [a, b, t, Mpath]
      rw [hzero, hlast]
      norm_num
      ring

end Submission.Helpers
