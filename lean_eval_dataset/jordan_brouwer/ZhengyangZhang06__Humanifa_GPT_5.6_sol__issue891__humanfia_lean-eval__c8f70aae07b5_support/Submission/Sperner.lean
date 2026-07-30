import Mathlib

namespace Submission

/-- A vertex of the `N`-grid in a `d`-dimensional cube. -/
structure GridVertex (d N : ℕ) where
  coord : Fin d → Fin (N + 1)
deriving DecidableEq, Fintype

namespace GridVertex

@[ext]
theorem ext {d N : ℕ} {v w : GridVertex d N}
    (h : ∀ i, v.coord i = w.coord i) : v = w := by
  cases v
  cases w
  simp only at h
  simp [funext h]

/-- The point of the unit cube represented by a positive-scale grid vertex. -/
noncomputable def point {d N : ℕ} (_hN : 0 < N) (v : GridVertex d N) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => (v.coord i : ℝ) / N

@[simp]
theorem point_apply {d N : ℕ} (hN : 0 < N) (v : GridVertex d N) (i : Fin d) :
    v.point hN i = (v.coord i : ℝ) / N :=
  rfl

end GridVertex

/-- A tagged simplex in the Kuhn triangulation of the `N`-grid cube. -/
structure KuhnSimplex (d N : ℕ) where
  base : Fin d → Fin N
  perm : Equiv.Perm (Fin d)
deriving DecidableEq, Fintype

namespace KuhnSimplex

/-- The `k`-th ordered vertex of a Kuhn simplex. -/
def vertex {d N : ℕ} (s : KuhnSimplex d N) (k : Fin (d + 1)) : GridVertex d N where
  coord i := by
    by_cases h : (s.perm.symm i).val < k.val
    · exact ⟨(s.base i).val + 1, by omega⟩
    · exact ⟨(s.base i).val, by omega⟩

@[simp]
theorem vertex_coord {d N : ℕ} (s : KuhnSimplex d N) (k : Fin (d + 1)) (i : Fin d) :
    (s.vertex k).coord i =
      if (s.perm.symm i).val < k.val then
        ⟨(s.base i).val + 1, by omega⟩
      else
        ⟨(s.base i).val, by omega⟩ := by
  simp [vertex]

@[simp]
theorem vertex_zero {d N : ℕ} (s : KuhnSimplex d N) :
    s.vertex 0 = ⟨fun i => Fin.castSucc (s.base i)⟩ := by
  ext i
  simp [vertex]

end KuhnSimplex

/-- Labels for the cubical Sperner argument: `none` points inward from the upper faces,
and `some i` points inward from the lower face in coordinate `i`. -/
abbrev CubeLabel (d : ℕ) := Option (Fin d)

namespace CubeLabel

def castSucc {d : ℕ} : CubeLabel d → CubeLabel (d + 1) :=
  Option.map Fin.castSucc

@[simp]
theorem castSucc_none {d : ℕ} : castSucc (d := d) none = none :=
  rfl

@[simp]
theorem castSucc_some {d : ℕ} (i : Fin d) :
    castSucc (some i) = some i.castSucc :=
  rfl

end CubeLabel

/-- The boundary condition used by the cubical Sperner lemma. -/
def SpernerAdmissible {d N : ℕ} (label : GridVertex d N → CubeLabel d) : Prop :=
  (∀ v, label v = none → ∀ i, (v.coord i).val < N) ∧
    ∀ v i, label v = some i → 0 < (v.coord i).val

/-- A Kuhn simplex carries every cubical label. -/
def FullyLabeled {d N : ℕ} (label : GridVertex d N → CubeLabel d)
    (s : KuhnSimplex d N) : Prop :=
  Function.Surjective fun k : Fin (d + 1) => label (s.vertex k)

instance {d N : ℕ} (label : GridVertex d N → CubeLabel d) (s : KuhnSimplex d N) :
    Decidable (FullyLabeled label s) := by
  unfold FullyLabeled
  infer_instance

theorem exists_fullyLabeled_zero {N : ℕ} (label : GridVertex 0 N → CubeLabel 0) :
    ∃ s : KuhnSimplex 0 N, FullyLabeled label s := by
  let s : KuhnSimplex 0 N :=
    { base := Fin.elim0
      perm := Equiv.refl _ }
  refine ⟨s, ?_⟩
  intro l
  cases l with
  | none =>
      have hlabel : label (s.vertex 0) = none := by
        cases h : label (s.vertex 0) with
        | none => rfl
        | some i => exact Fin.elim0 i
      exact ⟨0, hlabel⟩
  | some i => exact Fin.elim0 i

namespace SpernerParity

open Matrix

/-- Index cubical labels so that `none` is the last index. -/
def labelIndex {d : ℕ} : CubeLabel d ≃ Fin (d + 1) :=
  finSuccEquivLast.symm

@[simp]
theorem labelIndex_none {d : ℕ} : labelIndex (d := d) none = Fin.last d :=
  finSuccEquivLast_symm_none

@[simp]
theorem labelIndex_some {d : ℕ} (i : Fin d) :
    labelIndex (some i) = i.castSucc :=
  finSuccEquivLast_symm_some i

/-- The one-hot matrix of the labels on the ordered vertices of a simplex. -/
def basisMatrix {d N : ℕ} (label : GridVertex d N → CubeLabel d)
    (s : KuhnSimplex d N) : Matrix (Fin (d + 1)) (Fin (d + 1)) (ZMod 2) :=
  fun r k => if labelIndex (label (s.vertex k)) = r then 1 else 0

/-- Replace one basis row by the all-one row. This does not change the determinant because
the all-one row is the sum of all one-hot rows. -/
def augmentedMatrixAt {d N : ℕ} (label : GridVertex d N → CubeLabel d)
    (s : KuhnSimplex d N) (pivot : Fin (d + 1)) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (ZMod 2) :=
  (basisMatrix label s).updateRow pivot (fun _ => 1)

/-- The augmentation with `none` as pivot, used to detect fully labeled simplices. -/
def augmentedMatrix {d N : ℕ} (label : GridVertex d N → CubeLabel d)
    (s : KuhnSimplex d N) : Matrix (Fin (d + 1)) (Fin (d + 1)) (ZMod 2) :=
  augmentedMatrixAt label s (Fin.last d)

theorem sum_basisMatrix_column {d N : ℕ} (label : GridVertex d N → CubeLabel d)
    (s : KuhnSimplex d N) (k : Fin (d + 1)) :
    ∑ r, basisMatrix label s r k = 1 := by
  simp [basisMatrix]

theorem det_augmentedMatrixAt_eq_det_basisMatrix {d N : ℕ}
    (label : GridVertex d N → CubeLabel d) (s : KuhnSimplex d N)
    (pivot : Fin (d + 1)) :
    (augmentedMatrixAt label s pivot).det = (basisMatrix label s).det := by
  have hrow : (fun _ : Fin (d + 1) => (1 : ZMod 2)) =
      ∑ r, (1 : ZMod 2) • basisMatrix label s r := by
    funext k
    simpa using (sum_basisMatrix_column label s k).symm
  rw [augmentedMatrixAt, hrow, Matrix.det_updateRow_sum]
  simp

theorem det_augmentedMatrix_eq_det_basisMatrix {d N : ℕ}
    (label : GridVertex d N → CubeLabel d) (s : KuhnSimplex d N) :
    (augmentedMatrix label s).det = (basisMatrix label s).det := by
  exact det_augmentedMatrixAt_eq_det_basisMatrix label s (Fin.last d)

/-- The determinant weight of the facet obtained by deleting vertex `k`, with the pivot label
row deleted as well. -/
def facetWeightAt {d N : ℕ} (label : GridVertex d N → CubeLabel d)
    (s : KuhnSimplex d N) (pivot k : Fin (d + 1)) : ZMod 2 :=
  ((augmentedMatrixAt label s pivot).submatrix pivot.succAbove k.succAbove).det

theorem det_augmentedMatrixAt_eq_sum_facetWeightAt {d N : ℕ}
    (label : GridVertex d N → CubeLabel d) (s : KuhnSimplex d N)
    (pivot : Fin (d + 1)) :
    (augmentedMatrixAt label s pivot).det = ∑ k, facetWeightAt label s pivot k := by
  rw [Matrix.det_succ_row _ pivot]
  apply Finset.sum_congr rfl
  intro k _
  simp [facetWeightAt, augmentedMatrixAt]

theorem facetWeightAt_congr {d N : ℕ} (label : GridVertex d N → CubeLabel d)
    {s t : KuhnSimplex d N} {pivot k l : Fin (d + 1)}
    (h : ∀ j : Fin d, s.vertex (k.succAbove j) = t.vertex (l.succAbove j)) :
    facetWeightAt label s pivot k = facetWeightAt label t pivot l := by
  apply congrArg Matrix.det
  ext r j
  simp [augmentedMatrixAt, basisMatrix, h j]

theorem facetWeightAt_eq_zero_of_missing {d N : ℕ}
    (label : GridVertex d N → CubeLabel d) (s : KuhnSimplex d N)
    {pivot k r : Fin (d + 1)} (hr : r ≠ pivot)
    (hmissing : ∀ j : Fin d, labelIndex (label (s.vertex (k.succAbove j))) ≠ r) :
    facetWeightAt label s pivot k = 0 := by
  obtain ⟨r', hr'⟩ := Fin.exists_succAbove_eq hr
  apply Matrix.det_eq_zero_of_row_eq_zero r'
  intro j
  simp only [Matrix.submatrix_apply, augmentedMatrixAt]
  rw [Matrix.updateRow_ne]
  · simp [basisMatrix, hr', hmissing j]
  · exact Fin.succAbove_ne _ _

theorem det_basisMatrix {d N : ℕ} (label : GridVertex d N → CubeLabel d)
    (s : KuhnSimplex d N) :
    (basisMatrix label s).det =
      if Function.Surjective (fun k : Fin (d + 1) => labelIndex (label (s.vertex k)))
      then 1 else 0 := by
  classical
  let g : Fin (d + 1) → Fin (d + 1) :=
    fun k => labelIndex (label (s.vertex k))
  by_cases hg : Function.Surjective g
  · rw [if_pos hg]
    have hi : Function.Injective g := (Finite.injective_iff_surjective).2 hg
    let e : Equiv.Perm (Fin (d + 1)) := Equiv.ofBijective g ⟨hi, hg⟩
    have hmatrix : basisMatrix label s = Equiv.Perm.permMatrix (ZMod 2) e.symm := by
      ext r k
      simp only [basisMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
      change (if g k = r then (1 : ZMod 2) else 0) =
        (if e.symm r = k then 1 else 0)
      have hcond : g k = r ↔ e.symm r = k := by
        change e k = r ↔ e.symm r = k
        rw [e.apply_eq_iff_eq_symm_apply, eq_comm]
      simp only [hcond]
    rw [hmatrix, Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with hsign | hsign
    · simp [hsign]
    · simp [hsign]
  · rw [if_neg hg]
    have hni : ¬Function.Injective g := by
      intro hi
      exact hg ((Finite.injective_iff_surjective).1 hi)
    obtain ⟨k, l, hkl, hne⟩ := Function.not_injective_iff.mp hni
    apply Matrix.det_zero_of_column_eq hne
    intro r
    simp [basisMatrix, g, hkl]

theorem surjective_labelIndex_iff {d N : ℕ} (label : GridVertex d N → CubeLabel d)
    (s : KuhnSimplex d N) :
    Function.Surjective (fun k : Fin (d + 1) => labelIndex (label (s.vertex k))) ↔
      FullyLabeled label s := by
  constructor
  · intro h l
    obtain ⟨k, hk⟩ := h (labelIndex l)
    exact ⟨k, labelIndex.injective hk⟩
  · intro h r
    obtain ⟨k, hk⟩ := h (labelIndex.symm r)
    exact ⟨k, by simpa using congrArg labelIndex hk⟩

theorem det_augmentedMatrix {d N : ℕ} (label : GridVertex d N → CubeLabel d)
    (s : KuhnSimplex d N) :
    (augmentedMatrix label s).det = if FullyLabeled label s then 1 else 0 := by
  classical
  rw [det_augmentedMatrix_eq_det_basisMatrix, det_basisMatrix]
  simp only [surjective_labelIndex_iff]

end SpernerParity

end Submission
