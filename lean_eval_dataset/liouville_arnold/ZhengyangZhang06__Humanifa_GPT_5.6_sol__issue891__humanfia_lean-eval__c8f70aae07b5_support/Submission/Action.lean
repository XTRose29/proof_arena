import Submission.System

namespace Submission.Helpers

open Function Set Topology
open scoped BigOperators Topology

section CommutingFlows

variable {ι M : Type*} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace M]
  (φ : ι → Flow ℝ M)
  (hcomm : ∀ i j s t, Function.Commute (φ i s) (φ j t))

private noncomputable def componentHomeomorph (t : ι → ℝ) (i : ι) : M ≃ₜ M :=
  (φ i).toHomeomorph (t i)

omit [Fintype ι] [DecidableEq ι] in
include hcomm in
private theorem componentHomeomorph_commute (t : ι → ℝ) (i j : ι) :
    Commute (componentHomeomorph φ t i) (componentHomeomorph φ t j) := by
  apply Homeomorph.ext
  intro x
  exact hcomm i j (t i) (t j) x

omit [Fintype ι] [DecidableEq ι] in
include hcomm in
private theorem componentHomeomorph_cross_commute
    (t u : ι → ℝ) (i j : ι) :
    Commute (componentHomeomorph φ u i) (componentHomeomorph φ t j) := by
  apply Homeomorph.ext
  intro x
  exact hcomm i j (u i) (t j) x

include hcomm in
private noncomputable def flowProduct (s : Finset ι) (t : ι → ℝ) : M ≃ₜ M :=
  s.noncommProd (componentHomeomorph φ t) fun i _ j _ _ ↦
    componentHomeomorph_commute φ hcomm t i j

omit [Fintype ι] [DecidableEq ι] in
private theorem flowProduct_empty (t : ι → ℝ) :
    flowProduct φ hcomm ∅ t = 1 := by
  simp [flowProduct]

omit [Fintype ι] [DecidableEq ι] in
private theorem flowProduct_cons (s : Finset ι) (a : ι) (ha : a ∉ s) (t : ι → ℝ) :
    flowProduct φ hcomm (Finset.cons a s ha) t =
      componentHomeomorph φ t a * flowProduct φ hcomm s t := by
  unfold flowProduct
  rw [Finset.noncommProd_cons]

omit [Fintype ι] [DecidableEq ι] in
private theorem flowProduct_zero (s : Finset ι) :
    flowProduct φ hcomm s 0 = 1 := by
  rw [flowProduct, Finset.noncommProd_eq_pow_card _ _ _ (1 : M ≃ₜ M)]
  · simp
  · intro i hi
    apply Homeomorph.ext
    intro x
    exact (φ i).map_zero_apply x

omit [Fintype ι] [DecidableEq ι] in
private theorem flowProduct_add (s : Finset ι) (t u : ι → ℝ) :
    flowProduct φ hcomm s (t + u) =
      flowProduct φ hcomm s t * flowProduct φ hcomm s u := by
  let commT : (s : Set ι).Pairwise (Commute on componentHomeomorph φ t) :=
    fun i _ j _ _ ↦ componentHomeomorph_commute φ hcomm t i j
  let commU : (s : Set ι).Pairwise (Commute on componentHomeomorph φ u) :=
    fun i _ j _ _ ↦ componentHomeomorph_commute φ hcomm u i j
  let commUT : (s : Set ι).Pairwise fun i j ↦
      Commute (componentHomeomorph φ u i) (componentHomeomorph φ t j) :=
    fun i _ j _ _ ↦ componentHomeomorph_cross_commute φ hcomm t u i j
  calc
    flowProduct φ hcomm s (t + u) =
        s.noncommProd
          (fun i ↦ componentHomeomorph φ t i * componentHomeomorph φ u i)
          (Finset.noncommProd_mul_distrib_aux commT commU commUT) := by
      apply Finset.noncommProd_congr rfl
      intro i hi
      apply Homeomorph.ext
      intro x
      exact (φ i).map_add (t i) (u i) x
    _ = s.noncommProd (componentHomeomorph φ t) commT *
        s.noncommProd (componentHomeomorph φ u) commU :=
      Finset.noncommProd_mul_distrib _ _ commT commU commUT
    _ = flowProduct φ hcomm s t * flowProduct φ hcomm s u := by
      rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem continuous_flowProduct_apply (s : Finset ι) :
    Continuous (fun p : (ι → ℝ) × M ↦ flowProduct φ hcomm s p.1 p.2) := by
  induction s using Finset.cons_induction_on with
  | empty =>
      simpa [flowProduct_empty] using (continuous_snd : Continuous (Prod.snd : (ι → ℝ) × M → M))
  | @cons a s ha ih =>
      simp_rw [flowProduct_cons]
      change Continuous (fun p : (ι → ℝ) × M ↦
        φ a (p.1 a) (flowProduct φ hcomm s p.1 p.2))
      exact (φ a).continuous ((continuous_apply a).comp continuous_fst) ih

/-- Pairwise commuting real flows combine coordinatewise into a flow by a finite-dimensional real
vector group. -/
noncomputable def piFlow : Flow (ι → ℝ) M where
  toFun t x := flowProduct φ hcomm Finset.univ t x
  cont' := continuous_flowProduct_apply φ hcomm Finset.univ
  map_add' t u x := by
    rw [flowProduct_add]
    rfl
  map_zero' x := by
    rw [flowProduct_zero]
    rfl

omit [DecidableEq ι] in
@[simp]
theorem piFlow_apply (t : ι → ℝ) (x : M) :
    piFlow φ hcomm t x = flowProduct φ hcomm Finset.univ t x := rfl

end CommutingFlows

end Submission.Helpers
