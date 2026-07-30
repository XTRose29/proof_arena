import Submission.SpatialGenerator
import Submission.CenteredOrbitBridge
import Submission.GeometricBoundaryScale
import Mathlib.Data.Nat.Pairing

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

theorem entropyW_sub_le_dimMeasure_mul_rate_of_orbit_control
    (mu : Measure EucPlane) [IsProbabilityMeasure mu] [NoAtoms mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu) (hErg_inv : Ergodic T_inv mu)
    {K carrier : Set EucPlane}
    (hK_compact : IsCompact K)
    (hcarrier_measurable : MeasurableSet carrier)
    (hcarrier_full : mu carrierᶜ = 0)
    (hcarrier_invariant : T '' carrier = carrier)
    (hcarrierK : carrier ⊆ K)
    (hcarrier_dim : dimH carrier = dimMeasure mu)
    (hdim_top : dimMeasure mu ≠ ⊤)
    (q : NNReal) (hq_pos : 0 < q) (hq_lt : q < 1)
    {lam1 lam2 epsilon R : ℝ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (hepsilon : 0 < epsilon) (hR : 0 < R)
    (horbit : ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ y ∈ carrier, dist x y ≤ Real.exp (-R * L) →
        (∀ j : Fin (balancedForward lam1 lam2 L),
          dist (T^[j.val] x) (T^[j.val] y) < geometricBoundaryScale q L) ∧
        ∀ k, 0 < k → k ≤ balancedBackward lam1 lam2 L →
          dist (T_inv^[k] x) (T_inv^[k] y) < geometricBoundaryScale q L)
    (Q : Finset (Set EucPlane)) (hQ : IsMeasurablePartition mu Q) :
    entropyW mu T Q - epsilon ≤
      (dimMeasure mu).toReal * R := by
  let scale : ℕ → ℝ := fun j => 1 / (j + 1 : ℝ)
  have hscale_pos (j : ℕ) : 0 < scale j := by
    dsimp [scale]
    positivity
  have hfamilies (j : ℕ) := exists_small_geometric_boundary_ball_partition
    mu hK_compact hcarrier_measurable hcarrier_full hcarrierK
      (hscale_pos j) q hq_pos hq_lt
  choose p center radius partition hfamily using hfamilies
  have hradius (j : ℕ) (i : Fin (p j)) :
      scale j < radius j i ∧ radius j i < 2 * scale j ∧
        (∑' L : ℕ, (L + 1 : ℝ≥0∞) *
          mu {x | |dist x (center j i) - radius j i| ≤
            geometricBoundaryScale q L}) ≠ ⊤ :=
    (hfamily j).1 i
  have hcover (j : ℕ) :
      carrier ⊆ ⋃ i, Metric.ball (center j i) (radius j i) :=
    (hfamily j).2.1
  let bit : ℕ → EucPlane → Bool := fun k x =>
    if h : (Nat.unpair k).2 < p (Nat.unpair k).1 then
      (Metric.ball
        (center (Nat.unpair k).1 ⟨(Nat.unpair k).2, h⟩)
        (radius (Nat.unpair k).1 ⟨(Nat.unpair k).2, h⟩)).indicator
          (fun _ => true) x
    else false
  have hbit : ∀ k, Measurable (bit k) := by
    intro k
    dsimp [bit]
    split
    · exact measurable_const.indicator measurableSet_ball
    · exact measurable_const
  have hemb : MeasurableEmbedding
      (fun x : carrier => fun k => bit k x.1) := by
    letI : StandardBorelSpace carrier := hcarrier_measurable.standardBorel
    have hmeas : Measurable (fun x : carrier => fun k => bit k x.1) :=
      (measurable_spatialCode bit hbit).comp measurable_subtype_coe
    apply hmeas.measurableEmbedding
    intro x y hxy
    apply Subtype.ext
    have hdist (j : ℕ) : dist x.1 y.1 < 4 * scale j := by
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover j x.2)
      have hbit_eq := congrFun hxy (Nat.pair j i.val)
      dsimp [bit] at hbit_eq
      rw [Nat.unpair_pair] at hbit_eq
      simp only [dif_pos i.isLt] at hbit_eq
      have hbit_eq' :
          (Metric.ball (center j i) (radius j i)).indicator
              (fun _ => true) x.1 =
            (Metric.ball (center j i) (radius j i)).indicator
              (fun _ => true) y.1 := by
        simpa using hbit_eq
      have hyi : y.1 ∈ Metric.ball (center j i) (radius j i) :=
        (mem_iff_of_bool_indicator_eq hbit_eq').mp hxi
      have hxr : dist x.1 (center j i) < radius j i := by
        exact Metric.mem_ball.mp hxi
      have hyr : dist (center j i) y.1 < radius j i := by
        rw [dist_comm]
        exact Metric.mem_ball.mp hyi
      calc
        dist x.1 y.1 ≤ dist x.1 (center j i) + dist (center j i) y.1 :=
          dist_triangle _ _ _
        _ < radius j i + radius j i := add_lt_add hxr hyr
        _ < 4 * scale j := by
          have hr := (hradius j i).2.1
          linarith
    have hscale_tend : Tendsto (fun j => 4 * scale j) atTop (nhds 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)).comp
        (tendsto_add_atTop_nat 1)
      simpa [scale, Function.comp_def, Nat.cast_add, Nat.cast_one,
        div_eq_mul_inv] using h
    exact dist_le_zero.mp
      (ge_of_tendsto hscale_tend (Eventually.of_forall fun j => (hdist j).le))
  have hprefix : ∀ N, entropyW mu T
      (fiberPartition (spatialPrefixObservation bit N)) ≤
        (dimMeasure mu).toReal * R + epsilon := by
    intro N
    let valid : Finset ℕ := (Finset.range (N + 1)).filter fun k =>
      (Nat.unpair k).2 < p (Nat.unpair k).1
    let I := ↥valid
    let equivFin := Fintype.equivFin I
    let indexN : I → ℕ := fun k => k.1
    have hindexN (k : I) :
        (Nat.unpair (indexN k)).2 < p (Nat.unpair (indexN k)).1 :=
      (Finset.mem_filter.mp k.2).2
    let centerN : Fin (Fintype.card I) → EucPlane := fun i =>
      center (Nat.unpair (indexN (equivFin.symm i))).1
        ⟨(Nat.unpair (indexN (equivFin.symm i))).2,
          hindexN (equivFin.symm i)⟩
    let radiusN : Fin (Fintype.card I) → ℝ := fun i =>
      radius (Nat.unpair (indexN (equivFin.symm i))).1
        ⟨(Nat.unpair (indexN (equivFin.symm i))).2,
          hindexN (equivFin.symm i)⟩
    let P := fiberPartition (spatialPrefixObservation bit N)
    have hP : IsMeasurablePartition mu P :=
      isMeasurablePartition_fiberPartition mu _
        (measurable_spatialPrefixObservation bit hbit N)
    have hsum (i : Fin (Fintype.card I)) :
        (∑' L : ℕ, (L + 1 : ℝ≥0∞) *
          mu {x | |dist x (centerN i) - radiusN i| ≤
            geometricBoundaryScale q L}) ≠ ⊤ := by
      let k := (equivFin.symm i).1
      simpa [centerN, radiusN, indexN, k] using
        (hradius (Nat.unpair k).1
          ⟨(Nat.unpair k).2, hindexN (equivFin.symm i)⟩).2.2
    have hstable : ∀ {u v}, u ∈ carrier → v ∈ carrier →
        (∀ i, u ∈ Metric.ball (centerN i) (radiusN i) ↔
          v ∈ Metric.ball (centerN i) (radiusN i)) →
        ∀ A ∈ P, u ∈ A ↔ v ∈ A := by
      intro u v hu hv hballs A hA
      have hobs : spatialPrefixObservation bit N u =
          spatialPrefixObservation bit N v := by
        funext k
        change bit k.1 u = bit k.1 v
        by_cases hkvalid : (Nat.unpair k.1).2 < p (Nat.unpair k.1).1
        · have hkrange : k.1 ∈ Finset.range (N + 1) := by
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le k.2)
          let ki : I := ⟨k.1, Finset.mem_filter.mpr ⟨hkrange, hkvalid⟩⟩
          let i := equivFin ki
          have hmem := hballs i
          have heq : equivFin.symm i = ki := by simp [i]
          have hcenter : centerN i = center (Nat.unpair k.1).1
              ⟨(Nat.unpair k.1).2, hkvalid⟩ := by
            dsimp [centerN]
            rw [heq]
          have hradius' : radiusN i = radius (Nat.unpair k.1).1
              ⟨(Nat.unpair k.1).2, hkvalid⟩ := by
            dsimp [radiusN]
            rw [heq]
          simp only [bit, dif_pos hkvalid]
          rw [← hcenter, ← hradius']
          by_cases hu' : u ∈ Metric.ball (centerN i) (radiusN i)
          · have hv' := hmem.mp hu'
            simp [Set.indicator_of_mem, hu', hv']
          · have hv' : v ∉ Metric.ball (centerN i) (radiusN i) :=
              fun h => hu' (hmem.mpr h)
            simp [Set.indicator_of_notMem, hu', hv']
        · simp [bit, hkvalid]
      obtain ⟨label, _hlabel, rfl⟩ := Finset.mem_image.mp hA
      change spatialPrefixObservation bit N u = label ↔
        spatialPrefixObservation bit N v = label
      rw [hobs]
    have hbound := entropyW_sub_le_dimMeasure_mul_rate_of_balanced_orbit_control
      mu T T_inv hT_left hT_right hT hT_inv hErg hErg_inv
        hcarrier_measurable hcarrier_full hcarrier_invariant hcarrier_dim
        hdim_top centerN radiusN P hP hstable q hsum
        hlam1 hlam2 hepsilon hR horbit
    have hbound' : entropyW mu T
          (fiberPartition (spatialPrefixObservation bit N)) - epsilon ≤
        (dimMeasure mu).toReal * R := by
      simpa [P] using hbound
    linarith
  have hQbound := entropyW_le_of_uniform_spatial_prefix_bound
    mu T T_inv hT_right hT bit hbit hcarrier_full hemb hprefix Q hQ
  linarith

theorem kolmogorovSinaiEntropy_sub_le_dimMeasure_mul_rate_of_orbit_control
    (mu : Measure EucPlane) [IsProbabilityMeasure mu] [NoAtoms mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu) (hErg_inv : Ergodic T_inv mu)
    {K carrier : Set EucPlane}
    (hK_compact : IsCompact K)
    (hcarrier_measurable : MeasurableSet carrier)
    (hcarrier_full : mu carrierᶜ = 0)
    (hcarrier_invariant : T '' carrier = carrier)
    (hcarrierK : carrier ⊆ K)
    (hcarrier_dim : dimH carrier = dimMeasure mu)
    (hdim_top : dimMeasure mu ≠ ⊤)
    (q : NNReal) (hq_pos : 0 < q) (hq_lt : q < 1)
    {lam1 lam2 epsilon R : ℝ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (hepsilon : 0 < epsilon) (hR : 0 < R)
    (horbit : ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ y ∈ carrier, dist x y ≤ Real.exp (-R * L) →
        (∀ j : Fin (balancedForward lam1 lam2 L),
          dist (T^[j.val] x) (T^[j.val] y) < geometricBoundaryScale q L) ∧
        ∀ k, 0 < k → k ≤ balancedBackward lam1 lam2 L →
          dist (T_inv^[k] x) (T_inv^[k] y) < geometricBoundaryScale q L) :
    kolmogorovSinaiEntropy mu T - epsilon ≤
      (dimMeasure mu).toReal * R := by
  unfold kolmogorovSinaiEntropy
  apply sub_le_iff_le_add.mpr
  apply csSup_le
  · exact ⟨0, {Set.univ}, isMeasurablePartition_singleton_univ mu,
      entropyW_singleton_univ mu T⟩
  · intro h hh
    obtain ⟨Q, hQ, rfl⟩ := hh
    have hbound := entropyW_sub_le_dimMeasure_mul_rate_of_orbit_control
      mu T T_inv hT_left hT_right hT hT_inv hErg hErg_inv
        hK_compact hcarrier_measurable hcarrier_full hcarrier_invariant
        hcarrierK hcarrier_dim hdim_top q hq_pos hq_lt
        hlam1 hlam2 hepsilon hR horbit Q hQ
    linarith

end Submission.Helpers
