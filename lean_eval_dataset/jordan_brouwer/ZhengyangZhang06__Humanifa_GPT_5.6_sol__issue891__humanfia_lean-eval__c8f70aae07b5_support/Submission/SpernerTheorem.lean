import Submission.SpernerNeighbors

namespace Submission
namespace SpernerParity

theorem exists_castSucc_label_embedLowerVertex {n N : ℕ}
    (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (hadm : SpernerAdmissible label) (v : GridVertex n N) :
    ∃ l : CubeLabel n, CubeLabel.castSucc l = label (embedLowerVertex v) := by
  cases hlabel : label (embedLowerVertex v) with
  | none => exact ⟨none, by simp⟩
  | some i =>
      cases i using Fin.lastCases with
      | last =>
          have hpos := hadm.2 (embedLowerVertex v) (Fin.last n) hlabel
          simp at hpos
      | cast i => exact ⟨some i, by simp⟩

noncomputable def restrictLowerLabel {n N : ℕ}
    (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (hadm : SpernerAdmissible label) (v : GridVertex n N) : CubeLabel n :=
  Classical.choose (exists_castSucc_label_embedLowerVertex label hadm v)

theorem restrictLowerLabel_spec {n N : ℕ}
    (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (hadm : SpernerAdmissible label) (v : GridVertex n N) :
    CubeLabel.castSucc (restrictLowerLabel label hadm v) =
      label (embedLowerVertex v) :=
  Classical.choose_spec (exists_castSucc_label_embedLowerVertex label hadm v)

theorem restrictLowerLabel_admissible {n N : ℕ}
    (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (hadm : SpernerAdmissible label) :
    SpernerAdmissible (restrictLowerLabel label hadm) := by
  constructor
  · intro v hv i
    have hfull : label (embedLowerVertex v) = none := by
      rw [← restrictLowerLabel_spec label hadm v]
      simp [hv]
    simpa using hadm.1 (embedLowerVertex v) hfull i.castSucc
  · intro v i hv
    have hfull : label (embedLowerVertex v) = some i.castSucc := by
      rw [← restrictLowerLabel_spec label hadm v]
      simp [hv]
    simpa using hadm.2 (embedLowerVertex v) i.castSucc hfull

theorem labelIndex_castSucc {n : ℕ} (l : CubeLabel n) :
    labelIndex (CubeLabel.castSucc l) =
      (inductionPivot n).succAbove (labelIndex l) := by
  cases l with
  | none => simp [inductionPivot]
  | some i => simp [inductionPivot]

theorem facetWeight_embedLowerSimplex {n N : ℕ} (hN : 0 < N)
    (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (hadm : SpernerAdmissible label) (s : KuhnSimplex n N) :
    facetWeightAt label (embedLowerSimplex hN s) (inductionPivot n)
        (Fin.last (n + 1)) =
      (basisMatrix (restrictLowerLabel label hadm) s).det := by
  apply congrArg Matrix.det
  ext r k
  simp [augmentedMatrixAt, basisMatrix,
    embedLowerSimplex_vertex, ← restrictLowerLabel_spec label hadm,
    labelIndex_castSucc]

theorem incidenceWeight_embedLowerIncidence {n N : ℕ} (hN : 0 < N)
    (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (hadm : SpernerAdmissible label) (s : KuhnSimplex n N) :
    incidenceWeight label (inductionPivot n) (embedLowerIncidence hN s) =
      (augmentedMatrix (restrictLowerLabel label hadm) s).det := by
  rw [incidenceWeight, embedLowerIncidence, facetWeight_embedLowerSimplex]
  exact (det_augmentedMatrix_eq_det_basisMatrix _ _).symm

def facetIncidenceEquiv (n N : ℕ) :
    KuhnSimplex (n + 1) N × Fin (n + 2) ≃ FacetIncidence n N where
  toFun a := ⟨a.1, a.2⟩
  invFun a := (a.simplex, a.face)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_det_augmentedMatrix_eq_one {d N : ℕ} (hN : 0 < N)
    (label : GridVertex d N → CubeLabel d) (hadm : SpernerAdmissible label) :
    ∑ s : KuhnSimplex d N, (augmentedMatrix label s).det = 1 := by
  induction d with
  | zero =>
      let s0 : KuhnSimplex 0 N :=
        { base := Fin.elim0
          perm := Equiv.refl _ }
      letI : Unique (KuhnSimplex 0 N) :=
        { default := s0
          uniq := by
            intro s
            apply kuhnSimplex_ext
            · funext i
              exact Fin.elim0 i
            · ext i
              exact Fin.elim0 i }
      rw [Fintype.sum_unique, det_augmentedMatrix]
      have hfull : FullyLabeled label (default : KuhnSimplex 0 N) := by
        obtain ⟨s, hs⟩ := exists_fullyLabeled_zero label
        simpa only [Subsingleton.elim s default] using hs
      simp [hfull]
  | succ n ih =>
      let lowerLabel := restrictLowerLabel label hadm
      have hlower : SpernerAdmissible lowerLabel :=
        restrictLowerLabel_admissible label hadm
      calc
        ∑ s : KuhnSimplex (n + 1) N, (augmentedMatrix label s).det =
            ∑ s : KuhnSimplex (n + 1) N,
              ∑ k, facetWeightAt label s (inductionPivot n) k := by
                apply Fintype.sum_congr
                intro s
                rw [det_augmentedMatrix_eq_det_basisMatrix,
                  ← det_augmentedMatrixAt_eq_det_basisMatrix label s (inductionPivot n),
                  det_augmentedMatrixAt_eq_sum_facetWeightAt]
        _ = ∑ a : FacetIncidence n N,
              incidenceWeight label (inductionPivot n) a := by
                rw [← (facetIncidenceEquiv n N).sum_comp]
                rw [Fintype.sum_prod_type]
                rfl
        _ = ∑ a ∈ Finset.univ.filter
              (fun a : FacetIncidence n N => incidencePartner a = a),
              incidenceWeight label (inductionPivot n) a :=
                sum_incidenceWeight_eq_sum_fixed label (inductionPivot n)
        _ = ∑ a ∈ Finset.univ.filter
              (fun a : FacetIncidence n N => distinguishedIncidence a),
              incidenceWeight label (inductionPivot n) a :=
                sum_fixed_eq_sum_distinguished label hadm
        _ = ∑ a : {a : FacetIncidence n N // distinguishedIncidence a},
              incidenceWeight label (inductionPivot n) a := by
                apply Finset.sum_subtype
                simp
        _ = ∑ s : KuhnSimplex n N,
              incidenceWeight label (inductionPivot n) (embedLowerIncidence hN s) := by
                symm
                simpa [lowerIncidenceEquiv] using
                  (lowerIncidenceEquiv n N hN).sum_comp
                    (fun a => incidenceWeight label (inductionPivot n) a.1)
        _ = ∑ s : KuhnSimplex n N, (augmentedMatrix lowerLabel s).det := by
                apply Fintype.sum_congr
                intro s
                exact incidenceWeight_embedLowerIncidence hN label hadm s
        _ = 1 := ih lowerLabel hlower

theorem exists_fullyLabeled {d N : ℕ} (hN : 0 < N)
    (label : GridVertex d N → CubeLabel d) (hadm : SpernerAdmissible label) :
    ∃ s : KuhnSimplex d N, FullyLabeled label s := by
  by_contra h
  push Not at h
  have hzero : ∑ s : KuhnSimplex d N, (augmentedMatrix label s).det = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    simp [det_augmentedMatrix, h s]
  rw [sum_det_augmentedMatrix_eq_one hN label hadm] at hzero
  exact one_ne_zero hzero

end SpernerParity
end Submission
