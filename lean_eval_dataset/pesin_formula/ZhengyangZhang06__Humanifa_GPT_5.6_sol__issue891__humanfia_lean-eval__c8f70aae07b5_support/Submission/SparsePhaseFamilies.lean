import Submission.SparsePatternFamilies
import Submission.SparsePhase

namespace Submission.Helpers

open LeanEval.Dynamics

lemma centeredOrbit_phase
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    {m n r : ℕ} (hrm : r ≤ m) (x : EucPlane)
    (i : Fin ((m - r) + n)) :
    centeredOrbit T T_inv (m - r) n x i =
      centeredOrbit T T_inv m n x ⟨r + i.val, by omega⟩ := by
  simp only [centeredOrbit]
  rw [show r + i.val = i.val + r by omega, Function.iterate_add_apply]
  rw [iterate_before_inverse_cancel hT_right hrm]

lemma centeredOrbitGoodTime_phase_iff
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (G : Set EucPlane) {m n r t : ℕ}
    (hrm : r ≤ m) (ht : t < (m - r) + n) (x : EucPlane) :
    centeredOrbitGoodTime T T_inv G (m - r) n x t ↔
      centeredOrbitGoodTime T T_inv G m n x (r + t) := by
  have hrt : r + t < m + n := by omega
  rw [centeredOrbitGoodTime_iff T T_inv G (m - r) n x ht,
    centeredOrbitGoodTime_iff T T_inv G m n x hrt]
  rw [centeredOrbit_phase T T_inv hT_right hrm x ⟨t, ht⟩]

lemma badGridIndices_phase_eq
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (G : Set EucPlane) {m n r H : ℕ}
    (hrm : r ≤ m) (x : EucPlane) :
    badGridIndices H ((m - r) + n)
        (centeredOrbitGoodTime T T_inv G (m - r) n x) =
      phaseBadGridIndices H (m + n) r
        (centeredOrbitGoodTime T T_inv G m n x) := by
  classical
  ext j
  rw [mem_badGridIndices_iff,
    mem_phaseBadGridIndices_iff]
  have hlength : m + n - r = (m - r) + n := by omega
  rw [hlength]
  constructor
  · rintro ⟨hj, hjtime, hjbad⟩
    refine ⟨hj, hjtime, ?_⟩
    intro hgood
    exact hjbad ((centeredOrbitGoodTime_phase_iff
      T T_inv hT_right G hrm hjtime x).mpr (by
        simpa [Nat.add_assoc] using hgood))
  · rintro ⟨hj, hjtime, hjbad⟩
    refine ⟨hj, hjtime, ?_⟩
    intro hgood
    exact hjbad (by
      simpa [Nat.add_assoc] using
        (centeredOrbitGoodTime_phase_iff
          T T_inv hT_right G hrm hjtime x).mp hgood)

/-- Take the union of the budgeted pattern refinements over all coarse-grid
phases. -/
noncomputable def sparsePhasePieces
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ)
    (goodSet A : Set EucPlane) (m n H D B : ℕ) :
    Finset (Set EucPlane) :=
  (Finset.range H).biUnion fun r =>
    sparseBoundedPatternPieces
      T T_inv G F R goodSet A (m - r) n H D B

lemma measurableSet_of_mem_sparsePhasePieces
    (T T_inv : EucPlane → EucPlane)
    (hT : Continuous T) (hT_inv : Continuous T_inv)
    {G goodSet A : Set EucPlane}
    (hG : MeasurableSet G) (hgood : MeasurableSet goodSet)
    (hA : MeasurableSet A)
    (F : Finset EucPlane) (R : ℝ) (m n H D B : ℕ)
    {U : Set EucPlane}
    (hU : U ∈ sparsePhasePieces
      T T_inv G F R goodSet A m n H D B) :
    MeasurableSet U := by
  rw [sparsePhasePieces] at hU
  obtain ⟨r, _hr, hUr⟩ := Finset.mem_biUnion.mp hU
  exact measurableSet_of_mem_sparseBoundedPatternPieces
    T T_inv hT hT_inv hG hgood hA F R (m - r) n H D B hUr

lemma card_sparsePhasePieces_le
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ)
    (goodSet A : Set EucPlane) (m n : ℕ)
    {H : ℕ} (hH : 0 < H) (D B : ℕ)
    (hF : 0 < F.card) :
    (sparsePhasePieces
        T T_inv G F R goodSet A m n H D B).card ≤
      H * (2 ^ ((m + n) / H + 1) * F.card ^ (4 * D * B)) := by
  classical
  rw [sparsePhasePieces]
  calc
    ((Finset.range H).biUnion fun r =>
        sparseBoundedPatternPieces
          T T_inv G F R goodSet A (m - r) n H D B).card ≤
        ∑ r ∈ Finset.range H,
          (sparseBoundedPatternPieces
            T T_inv G F R goodSet A (m - r) n H D B).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ Finset.range H,
        2 ^ ((m + n) / H + 1) * F.card ^ (4 * D * B) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrH : r < H := Finset.mem_range.mp hr
      calc
        (sparseBoundedPatternPieces
            T T_inv G F R goodSet A (m - r) n H D B).card ≤
            2 ^ (gridIndexSet H ((m - r) + n)).card *
              F.card ^ (4 * D * B) :=
          card_sparseBoundedPatternPieces_le
            T T_inv G F R goodSet A (m - r) n hH D B hF
        _ ≤ 2 ^ ((m + n) / H + 1) *
              F.card ^ (4 * D * B) := by
          gcongr
          · omega
          · exact (card_gridIndexSet_le_div_add_one
              (L := (m - r) + n) hH).trans (by
                apply Nat.add_le_add_right
                exact Nat.div_le_div_right (c := H)
                  (Nat.add_le_add_right (Nat.sub_le m r) n))
    _ = H * (2 ^ ((m + n) / H + 1) *
          F.card ^ (4 * D * B)) := by simp

lemma sparsePhasePieces_cover
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (G : Set EucPlane) (F : Finset EucPlane)
    (hF : ∀ u : EucPlane, ‖u‖ ≤ 1 → ∃ f ∈ F, dist u f < 1 / 4)
    {R : ℝ} (hR : 0 < R)
    (goodSet A : Set EucPlane) (m n : ℕ)
    {H : ℕ} (hH : 0 < H) (hHm : H ≤ m)
    (D B : ℕ)
    (hbad : ∀ x ∈ goodSet,
      finiteBadCountNat
        (centeredOrbitGoodTime T T_inv G m n x) (m + n) ≤ B)
    (hclose : ∀ x ∈ A, ∀ y ∈ A, ∀ i : Fin (m + n),
      dist (centeredOrbit T T_inv m n x i)
        (centeredOrbit T T_inv m n y i) ≤ R) :
    A ∩ goodSet ⊆
      ⋃ U ∈ sparsePhasePieces
        T T_inv G F R goodSet A m n H D B, U := by
  classical
  intro x hx
  obtain ⟨r, hr⟩ :=
    exists_phase_mul_card_le_finiteBadCountNat
      hH (m + n) (centeredOrbitGoodTime T T_inv G m n x)
  have hrm : r.val ≤ m := (Nat.lt_of_lt_of_le r.isLt hHm).le
  have hphase :
      H * (badGridIndices H ((m - r.val) + n)
          (centeredOrbitGoodTime T T_inv G (m - r.val) n x)).card ≤ B := by
    rw [badGridIndices_phase_eq T T_inv hT_right G hrm x]
    exact hr.trans (hbad x hx.2)
  have hclose_phase :
      ∀ y ∈ A, ∀ z ∈ A, ∀ i : Fin ((m - r.val) + n),
        dist (centeredOrbit T T_inv (m - r.val) n y i)
          (centeredOrbit T T_inv (m - r.val) n z i) ≤ R := by
    intro y hy z hz i
    rw [centeredOrbit_phase T T_inv hT_right hrm,
      centeredOrbit_phase T T_inv hT_right hrm]
    exact hclose y hy z hz _
  have hxcover := sparseBoundedPatternPieces_cover
    T T_inv G F hF hR goodSet A (m - r.val) n H D B
      hclose_phase ⟨hx, hphase⟩
  simp only [Set.mem_iUnion] at hxcover ⊢
  obtain ⟨U, hU, hxU⟩ := hxcover
  refine ⟨U, ?_, hxU⟩
  rw [sparsePhasePieces]
  exact Finset.mem_biUnion.mpr
    ⟨r.val, Finset.mem_range.mpr r.isLt, hU⟩

end Submission.Helpers
