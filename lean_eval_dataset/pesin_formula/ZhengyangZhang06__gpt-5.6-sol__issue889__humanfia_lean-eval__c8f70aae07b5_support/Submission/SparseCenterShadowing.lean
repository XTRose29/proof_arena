import Submission.SparsePieceShadowing

namespace Submission.Helpers

open LeanEval.Dynamics

/-- A phase-refined sparse piece has exponentially controlled diameter at the
center of the orbit interval.  The displayed estimate keeps the finite-scale
losses explicit; they will be made negligible by the global parameter choice. -/
lemma dist_le_of_mem_sparsePhasePiece
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K S carrier : Set EucPlane}
    (hK_inv : T '' K = K) (hKS : K ⊆ S)
    (hS_convex : Convex ℝ S)
    (hcarrier : T '' carrier = carrier)
    (hcarrierK : carrier ⊆ K)
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
    (F : Finset EucPlane) (goodSet A : Set EucPlane)
    (hAcarrier : A ⊆ carrier)
    (m n : ℕ) {H : ℕ} (hH : 0 < H) (D B : ℕ)
    (hn : 0 < n) (hbudgetCenter : B + H ≤ m)
    (hclose : ∀ x ∈ A, ∀ y ∈ A, ∀ i : Fin (m + n),
      dist (centeredOrbit T T_inv m n x i)
        (centeredOrbit T T_inv m n y i) ≤ R)
    (hshortSmall : M ^ H * R ≤ 1)
    (hshortError :
      H * (M * (M ^ H * R)) * (2 * M) ^ (H + 1) ≤
        Real.exp ((lam2 + 6 * eta) * H))
    (hscaleR : 2 * R ≤ (4 : ℝ) ^ D)
    (hscaleM : M ≤ (4 : ℝ) ^ D)
    (hscaleConst : 4 * R * M ^ 2 ≤ (4 : ℝ) ^ D)
    (hscaleRate :
      4 * M ^ 2 * Real.exp (-(lam2 + 6 * eta)) ≤ (4 : ℝ) ^ D)
    {q : ℝ} (hq : 1 ≤ q)
    (hAq : (4 * C : ℝ) / q ≤ 1 / 4)
    (hcross : ∀ g : ℕ, H ≤ g →
      (4 * C : ℝ) * q *
        Real.exp (((lam2 + 6 * eta) + (-lam1 + 6 * eta)) * g) ≤ 1 / 4)
    (hunstable : ∀ g : ℕ, H ≤ g →
      (C : ℝ) * Real.exp ((-lam1 + 6 * eta) * g) *
        Real.exp ((lam2 + 6 * eta) * g) ≤ 1 / 2)
    (hstableRate : lam2 + 6 * eta < 0)
    (hunstableRate : -lam1 + 6 * eta < 0)
    {U : Set EucPlane}
    (hU : U ∈ sparsePhasePieces T T_inv
      (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
      F R goodSet A m n H D B)
    {y z : EucPlane} (hy : y ∈ U) (hz : z ∈ U) :
    dist y z ≤
      M ^ (B + H) * R *
        (q ^ ((m + n) / H + 1) *
            Real.exp ((lam2 + 6 * eta) *
              ((m : ℝ) - 2 * B - 2 * H)) +
          q ^ ((m + n) / H + 1) *
            Real.exp ((-lam1 + 6 * eta) *
              ((n : ℝ) - B - H))) := by
  classical
  let G := pesinFullShadowingBlock T T_inv lam1 lam2 eta C
  rw [sparsePhasePieces] at hU
  obtain ⟨r, hrRange, hUr⟩ := Finset.mem_biUnion.mp hU
  have hrH : r < H := Finset.mem_range.mp hrRange
  have hrm : r ≤ m := by omega
  obtain ⟨p, hbase, hbad, label, hlabel, hUeq⟩ :=
    exists_sparseEdgePiece_of_mem_sparseBoundedPatternPieces
      T T_inv G F R goodSet A (m - r) n H D B hUr
  rw [hUeq] at hy hz
  let c := sparsePatternReference T T_inv G goodSet A (m - r) n H p hbase
  let base := sparsePatternBase T T_inv G goodSet A (m - r) n H p
  have hcbase : c ∈ base := by
    exact sparsePatternReference_mem
      T T_inv G goodSet A (m - r) n H p hbase
  have hybase : y ∈ base :=
    mem_sparseEdgePiece_base
      T T_inv G (m - r) n H c base label hy
  have hzbase : z ∈ base :=
    mem_sparseEdgePiece_base
      T T_inv G (m - r) n H c base label hz
  have hyA : y ∈ A := hybase.1.1
  have hzA : z ∈ A := hzbase.1.1
  have hycarrier : y ∈ carrier := hAcarrier hyA
  have hzcarrier : z ∈ carrier := hAcarrier hzA
  have hcarrier_inv : T_inv '' carrier = carrier :=
    inverse_image_eq_of_image_eq hT_left hcarrier
  have hyleftCarrier : T_inv^[m - r] y ∈ carrier := by
    rw [← image_iterate_eq_of_image_eq T_inv hcarrier_inv (m - r)]
    exact ⟨y, hycarrier, rfl⟩
  have hzleftCarrier : T_inv^[m - r] z ∈ carrier := by
    rw [← image_iterate_eq_of_image_eq T_inv hcarrier_inv (m - r)]
    exact ⟨z, hzcarrier, rfl⟩
  have hyK (i : Fin ((m - r) + n)) :
      centeredOrbit T T_inv (m - r) n y i ∈ K := by
    apply hcarrierK
    rw [← image_iterate_eq_of_image_eq T hcarrier i.val]
    exact ⟨T_inv^[m - r] y, hyleftCarrier, rfl⟩
  have hzK (i : Fin ((m - r) + n)) :
      centeredOrbit T T_inv (m - r) n z i ∈ K := by
    apply hcarrierK
    rw [← image_iterate_eq_of_image_eq T hcarrier i.val]
    exact ⟨T_inv^[m - r] z, hzleftCarrier, rfl⟩
  have hclosePhase :
      ∀ x ∈ A, ∀ w ∈ A, ∀ i : Fin ((m - r) + n),
        dist (centeredOrbit T T_inv (m - r) n x i)
          (centeredOrbit T T_inv (m - r) n w i) ≤ R := by
    intro x hx w hw i
    rw [centeredOrbit_phase T T_inv hT_right hrm,
      centeredOrbit_phase T T_inv hT_right hrm]
    exact hclose x hx w hw _
  have hBm : B < m - r := by omega
  obtain ⟨hselected, i, hfirst, hicenter, hcenterGap, htail⟩ :=
    exists_selectedGridIndex_center_with_endpoint_bounds
      hH hn hBm (centeredOrbitGoodTime T T_inv G (m - r) n c) hbad
  have hselectedG :
      ∀ j : Fin (sparseSelectedSet T T_inv G (m - r) n H c).card,
        centeredOrbit T T_inv (m - r) n y
          ⟨H * sparseNodeIndex T T_inv G (m - r) n H c j,
            sparseNodeIndex_lt T T_inv G (m - r) n H c j⟩ ∈ G := by
    intro j
    have hcgood :=
      sparseNodeIndex_good T T_inv G (m - r) n H c j
    have hjmem :
        sparseNodeIndex T T_inv G (m - r) n H c j ∈
          gridIndexSet H ((m - r) + n) := by
      exact (Finset.mem_filter.mp
        (selectedGridIndex_mem H ((m - r) + n)
          (centeredOrbitGoodTime T T_inv G (m - r) n c) j)).1
    have hyg :
        centeredOrbitGoodTime T T_inv G (m - r) n y
          (H * sparseNodeIndex T T_inv G (m - r) n H c j) :=
      (same_centeredGridPattern_goodTime_iff
        T T_inv G (m - r) n H p hcbase.2 hybase.2 hjmem).mp hcgood
    exact (centeredOrbitGoodTime_iff
      T T_inv G (m - r) n y
        (sparseNodeIndex_lt T T_inv G (m - r) n H c j)).mp hyg
  have hpath := sparseEdgePiece_selected_path_displacement_le
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_inv hKS hS_convex hcarrier hsource hcov hM hR
      hT_lipschitz hderiv hderiv_lipschitz
      F (m - r) n hH D c base label hlabel hy hz
      hyK hzK hyleftCarrier hselectedG
      (fun j => hclosePhase y hyA z hzA j) hselected
      hshortSmall hshortError hscaleR hscaleM hscaleConst hscaleRate
      (lt_of_lt_of_le zero_lt_one hq) hAq hcross hunstable
  let card :=
    (selectedGridIndices H ((m - r) + n)
      (centeredOrbitGoodTime T T_inv G (m - r) n c)).card
  have hcardPos : 0 < card := by
    simpa [card] using Finset.card_pos.mpr hselected
  have hcard : card - 1 + 1 = card := by omega
  let node : Fin (card - 1 + 1) → ℕ := fun j =>
    sparseNodeIndex T T_inv G (m - r) n H c (Fin.cast hcard j)
  let ii : Fin (card - 1 + 1) := Fin.cast hcard.symm i
  have hii : Fin.cast hcard ii = i := by
    apply Fin.ext
    rfl
  let i0 : Fin card := ⟨0, hcardPos⟩
  let ilast : Fin card :=
    ⟨card - 1, Nat.sub_lt hcardPos (Nat.succ_pos 0)⟩
  have hcastZero :
      ∀ h : card - 1 + 1 = card,
        Fin.cast h (0 : Fin (card - 1 + 1)) = i0 := by
    intro h
    apply Fin.ext
    rfl
  have hcastLast :
      ∀ h : card - 1 + 1 = card,
        Fin.cast h (Fin.last (card - 1)) = ilast := by
    intro h
    apply Fin.ext
    rfl
  let ti := H * sparseNodeIndex T T_inv G (m - r) n H c i
  let t0 := H * sparseNodeIndex T T_inv G (m - r) n H c i0
  let tlast := H * sparseNodeIndex T T_inv G (m - r) n H c ilast
  have ht0i : t0 ≤ ti := by
    apply Nat.mul_le_mul_left H
    exact (strictMono_selectedGridIndex H ((m - r) + n)
      (centeredOrbitGoodTime T T_inv G (m - r) n c)).monotone
        (Fin.le_iff_val_le_val.mpr (by simp [i0]))
  have hitiLast : ti ≤ tlast := by
    apply Nat.mul_le_mul_left H
    exact (strictMono_selectedGridIndex H ((m - r) + n)
      (centeredOrbitGoodTime T T_inv G (m - r) n c)).monotone
        (Fin.le_iff_val_le_val.mpr (by
          dsimp [ilast]
          omega))
  have hnodeZero
      (j : Fin (sparseSelectedSet T T_inv G (m - r) n H c).card)
      (hj : j.val = 0) :
      sparseNodeIndex T T_inv G (m - r) n H c j =
        sparseNodeIndex T T_inv G (m - r) n H c i0 := by
    apply congrArg
    apply Fin.ext
    simpa [i0] using hj
  have hpathi :
      dist
          (centeredOrbit T T_inv (m - r) n y
            ⟨ti, by
              simpa [ti] using sparseNodeIndex_lt
                T T_inv G (m - r) n H c i⟩)
          (centeredOrbit T T_inv (m - r) n z
            ⟨ti, by
              simpa [ti] using sparseNodeIndex_lt
                T T_inv G (m - r) n H c i⟩) ≤
        R * (q ^ i.val *
              Real.exp ((lam2 + 6 * eta) * ((ti : ℝ) - t0)) +
            q ^ (card - 1 - i.val) *
              Real.exp ((-lam1 + 6 * eta) *
                ((tlast : ℝ) - ti))) := by
    simpa [G, sparseSelectedSet, card, node, ii, hii, i0, ilast,
      hcastZero, hcastLast, hnodeZero, ti, t0, tlast, Nat.cast_sub ht0i,
      Nat.cast_sub hitiLast] using hpath ii
  have ht0B : t0 ≤ B := by
    dsimp [t0, i0, card, sparseNodeIndex, sparseSelectedSet,
      selectedGridIndex, G]
    rw [Finset.orderEmbOfFin_zero]
    rw [Finset.orderEmbOfFin_zero] at hfirst
    simpa only [G] using hfirst
  have htiCenter : ti ≤ m - r := by
    simpa [ti, sparseNodeIndex, sparseSelectedSet,
      selectedGridIndex, G] using hicenter
  have hcenterGap' : m - r - ti ≤ B + H := by
    simpa [ti, sparseNodeIndex, sparseSelectedSet,
      selectedGridIndex, G] using hcenterGap
  have htail' : m - r + n - tlast ≤ B + H := by
    dsimp [tlast, ilast, card, sparseNodeIndex, sparseSelectedSet,
      selectedGridIndex, G]
    rw [Finset.orderEmbOfFin_last]
    rw [Finset.orderEmbOfFin_last] at htail
    simpa only [G] using htail
    all_goals simpa [G, card] using hcardPos
  have hstableGap :
      (m : ℝ) - 2 * B - 2 * H ≤ (ti : ℝ) - t0 := by
    have hnat : m ≤ (ti - t0) + 2 * B + 2 * H := by
      omega
    have hcast : ((ti - t0 : ℕ) : ℝ) = (ti : ℝ) - t0 := by
      exact Nat.cast_sub ht0i
    have hnat' :
        (m : ℝ) ≤ ((ti - t0 : ℕ) : ℝ) +
          2 * (B : ℝ) + 2 * (H : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hunstableGap :
      (n : ℝ) - B - H ≤ (tlast : ℝ) - ti := by
    have hnat : n ≤ (tlast - ti) + B + H := by
      omega
    have hcast : ((tlast - ti : ℕ) : ℝ) = (tlast : ℝ) - ti := by
      exact Nat.cast_sub hitiLast
    have hnat' :
        (n : ℝ) ≤ ((tlast - ti : ℕ) : ℝ) +
          (B : ℝ) + (H : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hcardGrid :
      card ≤ (m + n) / H + 1 := by
    calc
      card ≤ (gridIndexSet H ((m - r) + n)).card := by
        exact Finset.card_filter_le _ _
      _ ≤ ((m - r) + n) / H + 1 :=
        card_gridIndexSet_le_div_add_one hH
      _ ≤ (m + n) / H + 1 := by
        exact Nat.add_le_add_right
          (Nat.div_le_div_right (c := H)
            (Nat.add_le_add_right (Nat.sub_le m r) n)) 1
  have hiQ : i.val ≤ (m + n) / H + 1 :=
    (Nat.lt_of_lt_of_le i.isLt hcardGrid).le
  have hrightQ :
      card - 1 - i.val ≤ (m + n) / H + 1 := by omega
  have hqLeft :
      q ^ i.val ≤ q ^ ((m + n) / H + 1) :=
    pow_le_pow_right₀ hq hiQ
  have hqRight :
      q ^ (card - 1 - i.val) ≤ q ^ ((m + n) / H + 1) :=
    pow_le_pow_right₀ hq hrightQ
  have hstableExp :
      Real.exp ((lam2 + 6 * eta) * ((ti : ℝ) - t0)) ≤
        Real.exp ((lam2 + 6 * eta) *
          ((m : ℝ) - 2 * B - 2 * H)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hstableGap hstableRate.le
  have hunstableExp :
      Real.exp ((-lam1 + 6 * eta) * ((tlast : ℝ) - ti)) ≤
        Real.exp ((-lam1 + 6 * eta) *
          ((n : ℝ) - B - H)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hunstableGap hunstableRate.le
  have hselectedBound :
      dist
          (centeredOrbit T T_inv (m - r) n y
            ⟨ti, by
              simpa [ti] using sparseNodeIndex_lt
                T T_inv G (m - r) n H c i⟩)
          (centeredOrbit T T_inv (m - r) n z
            ⟨ti, by
              simpa [ti] using sparseNodeIndex_lt
                T T_inv G (m - r) n H c i⟩) ≤
        R * (q ^ ((m + n) / H + 1) *
              Real.exp ((lam2 + 6 * eta) *
                ((m : ℝ) - 2 * B - 2 * H)) +
            q ^ ((m + n) / H + 1) *
              Real.exp ((-lam1 + 6 * eta) *
                ((n : ℝ) - B - H))) := by
    have hp := hpathi
    simpa only [G, card, node, ii, ti, t0, tlast,
      dist_eq_norm, norm_sub_rev] using
      hp.trans (mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul hqLeft hstableExp (by positivity) (by positivity))
          (mul_le_mul hqRight hunstableExp (by positivity) (by positivity)))
        hR.le)
  let k := (m - r) - ti
  have hkBound : k ≤ B + H := by
    simpa [k] using hcenterGap'
  let yi : EucPlane := centeredOrbit T T_inv (m - r) n y
    ⟨ti, by
      simpa [ti] using sparseNodeIndex_lt T T_inv G (m - r) n H c i⟩
  let zi : EucPlane := centeredOrbit T T_inv (m - r) n z
    ⟨ti, by
      simpa [ti] using sparseNodeIndex_lt T T_inv G (m - r) n H c i⟩
  have hycenter : T^[k] yi = y := by
    calc
      T^[k] yi =
          centeredOrbit T T_inv (m - r) n y
            ⟨ti + k, by
              dsimp [k]
              omega⟩ := (centeredOrbit_forward
                T T_inv y
                ⟨ti, by
                  simpa [ti] using sparseNodeIndex_lt
                    T T_inv G (m - r) n H c i⟩ k (by
                      dsimp [k]
                      omega)).symm
      _ = centeredOrbit T T_inv (m - r) n y
          ⟨m - r, by omega⟩ := by
            apply congrArg (centeredOrbit T T_inv (m - r) n y)
            apply Fin.ext
            dsimp [k]
            omega
      _ = y := centeredOrbit_center T T_inv hT_right hn y
  have hzcenter : T^[k] zi = z := by
    calc
      T^[k] zi =
          centeredOrbit T T_inv (m - r) n z
            ⟨ti + k, by
              dsimp [k]
              omega⟩ := (centeredOrbit_forward
                T T_inv z
                ⟨ti, by
                  simpa [ti] using sparseNodeIndex_lt
                    T T_inv G (m - r) n H c i⟩ k (by
                      dsimp [k]
                      omega)).symm
      _ = centeredOrbit T T_inv (m - r) n z
          ⟨m - r, by omega⟩ := by
            apply congrArg (centeredOrbit T T_inv (m - r) n z)
            apply Fin.ext
            dsimp [k]
            omega
      _ = z := centeredOrbit_center T T_inv hT_right hn z
  have hiterate := dist_iterate_le_pow_of_lipschitz_on_invariant
    T hK_inv (zero_le_one.trans hM) hT_lipschitz
      k yi (hyK _) zi (hzK _)
  rw [hycenter, hzcenter] at hiterate
  calc
    dist y z ≤ M ^ k * dist yi zi := hiterate
    _ ≤ M ^ (B + H) * dist yi zi := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hM hkBound) dist_nonneg
    _ ≤ M ^ (B + H) *
        (R * (q ^ ((m + n) / H + 1) *
              Real.exp ((lam2 + 6 * eta) *
                ((m : ℝ) - 2 * B - 2 * H)) +
            q ^ ((m + n) / H + 1) *
              Real.exp ((-lam1 + 6 * eta) *
                ((n : ℝ) - B - H)))) := by
      exact mul_le_mul_of_nonneg_left (by simpa [yi, zi] using hselectedBound)
        (pow_nonneg (zero_le_one.trans hM) _)
    _ = _ := by ring

end Submission.Helpers
