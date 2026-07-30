import Submission.CenteredDiameterBridge
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Logic.Equiv.Nat

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

def biIterate {M : Type*} (T T_inv : M → M) : ℤ → M → M
  | Int.ofNat n => T^[n]
  | Int.negSucc n => T_inv^[n + 1]

lemma measurable_biIterate
    {M : Type*} [MeasurableSpace M]
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (z : ℤ) : Measurable (biIterate T T_inv z) := by
  cases z with
  | ofNat n => exact hT.iterate n
  | negSucc n => exact hT_inv.iterate (n + 1)

noncomputable def twoSidedPartitionCode
    {M : Type*} (T T_inv : M → M) (P : Finset (Set M))
    (x : M) : ℤ → (↥P → Bool) :=
  fun z => partitionSymbol P (biIterate T T_inv z x)

lemma measurable_twoSidedPartitionCode
    {M : Type*} [MeasurableSpace M]
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    Measurable (twoSidedPartitionCode T T_inv P) := by
  apply measurable_pi_lambda
  intro z
  exact (measurable_partitionSymbol P hP).comp
    (measurable_biIterate T T_inv hT hT_inv z)

lemma mem_iff_of_bool_indicator_eq
    {M : Type*} {A : Set M} {x y : M}
    (h : A.indicator (fun _ => true) x = A.indicator (fun _ => true) y) :
    x ∈ A ↔ y ∈ A := by
  constructor
  · intro hx
    by_contra hy
    rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hy] at h
    contradiction
  · intro hy
    by_contra hx
    rw [Set.indicator_of_notMem hx, Set.indicator_of_mem hy] at h
    contradiction

lemma mem_centeredJoin_atom_of_same_partition_names
    {M : Type*}
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (P : Finset (Set M))
    {m n : ℕ} {x y : M} {A : Set M}
    (hA : A ∈ centeredJoin T T_inv P m n) (hxA : x ∈ A)
    (hforward : ∀ j : Fin n, ∀ C ∈ P,
      T^[j.val] x ∈ C ↔ T^[j.val] y ∈ C)
    (hbackward : ∀ q, 0 < q → q ≤ m → ∀ C ∈ P,
      T_inv^[q] x ∈ C ↔ T_inv^[q] y ∈ C) :
    y ∈ A := by
  classical
  rw [centeredJoin, preimagePartition] at hA
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
  change T_inv^[m] y ∈ B
  change T_inv^[m] x ∈ B at hxA
  rw [iteratedJoin] at hB
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hB
  apply Set.mem_iInter.mpr
  intro i
  have hfi : f i ∈ P := Fintype.mem_piFinset.mp hf i
  have hxi := Set.mem_iInter.mp hxA i
  change T^[i.val] (T_inv^[m] x) ∈ f i at hxi
  change T^[i.val] (T_inv^[m] y) ∈ f i
  by_cases hi : i.val < m
  · let q := m - i.val
    have hq_pos : 0 < q := by omega
    have hq_le : q ≤ m := Nat.sub_le _ _
    have hiq : m - q = i.val := by omega
    rw [← hiq, iterate_sub_inverse_cancel hT_right hq_le] at hxi ⊢
    exact (hbackward q hq_pos hq_le (f i) hfi).mp hxi
  · have hmi : m ≤ i.val := le_of_not_gt hi
    let j := i.val - m
    have hj_lt : j < n := by omega
    let jf : Fin n := ⟨j, hj_lt⟩
    have hij : m + jf.val = i.val := by
      dsimp [jf, j]
      omega
    rw [← hij, iterate_after_inverse_cancel hT_right] at hxi ⊢
    exact (hforward jf (f i) hfi).mp hxi

lemma mem_centeredJoin_atom_of_twoSidedCode_eq
    {M : Type*}
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (P : Finset (Set M))
    {m n : ℕ} {x y : M} {A : Set M}
    (hcode : twoSidedPartitionCode T T_inv P x =
      twoSidedPartitionCode T T_inv P y)
    (hA : A ∈ centeredJoin T T_inv P m n) (hxA : x ∈ A) :
    y ∈ A := by
  apply mem_centeredJoin_atom_of_same_partition_names
    T T_inv hT_right P hA hxA
  · intro j C hC
    have hz := congrFun (congrFun hcode (Int.ofNat j.val)) ⟨C, hC⟩
    apply mem_iff_of_bool_indicator_eq
    simpa [twoSidedPartitionCode, biIterate, partitionSymbol] using hz
  · intro q hq_pos _hq_le C hC
    let z : ℤ := Int.negSucc (q - 1)
    have hz := congrFun (congrFun hcode z) ⟨C, hC⟩
    have hq : q - 1 + 1 = q := Nat.sub_add_cancel hq_pos
    apply mem_iff_of_bool_indicator_eq
    simpa [twoSidedPartitionCode, biIterate, partitionSymbol, z, hq] using hz

lemma measurableEmbedding_twoSidedPartitionCode_restrict_of_shrinking
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set EucPlane)) (hP : ∀ A ∈ P, MeasurableSet A)
    {s : Set EucPlane} (hs : MeasurableSet s)
    {lam1 lam2 R : ℝ} (hR : 0 < R)
    (good : ℕ → Set EucPlane)
    (hs_good : ∀ x ∈ s, ∀ᶠ L : ℕ in atTop, x ∈ good L)
    (hs_atom : ∀ x ∈ s, ∀ L,
      ∃ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L), x ∈ A)
    (hpair : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
        dist x y ≤ Real.exp (-R * L)) :
    MeasurableEmbedding
      (fun x : s => twoSidedPartitionCode T T_inv P x.1) := by
  have hcode_measurable : Measurable
      (fun x : s => twoSidedPartitionCode T T_inv P x.1) :=
    (measurable_twoSidedPartitionCode T T_inv hT hT_inv P hP).comp
      measurable_subtype_coe
  letI : StandardBorelSpace s := hs.standardBorel
  apply hcode_measurable.measurableEmbedding
  intro x y hxy
  apply Subtype.ext
  have hradius : Tendsto (fun L : ℕ => Real.exp (-R * L)) atTop (nhds 0) := by
    have hexponent : Tendsto (fun L : ℕ => -R * (L : ℝ)) atTop atBot :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg
        (neg_neg_of_pos hR)
    exact Real.tendsto_exp_atBot.comp hexponent
  have hdist_eventually : ∀ᶠ L : ℕ in atTop,
      dist x.1 y.1 ≤ Real.exp (-R * L) := by
    filter_upwards [hs_good x.1 x.2, hs_good y.1 y.2] with L hxgood hyg
    obtain ⟨A, hA, hxA⟩ := hs_atom x.1 x.2 L
    have hyA := mem_centeredJoin_atom_of_twoSidedCode_eq
      T T_inv hT_right P hxy hA hxA
    exact hpair L A hA x.1 ⟨hxA, hxgood⟩ y.1 ⟨hyA, hyg⟩
  exact dist_le_zero.mp (ge_of_tendsto hradius hdist_eventually)

lemma measurableSpace_eq_comap_of_measurableEmbedding
    {α β : Type*} [mα : MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) :
    mα = MeasurableSpace.comap f inferInstance := by
  apply le_antisymm
  · intro t ht
    apply MeasurableSpace.measurableSet_comap.mpr
    refine ⟨f '' t, hf.measurableSet_image' ht, ?_⟩
    exact hf.injective.preimage_image t
  · exact hf.measurable.comap_le

lemma measurableSpace_restrict_eq_comap_twoSidedPartitionCode_of_shrinking
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set EucPlane)) (hP : ∀ A ∈ P, MeasurableSet A)
    {s : Set EucPlane} (hs : MeasurableSet s)
    {lam1 lam2 R : ℝ} (hR : 0 < R)
    (good : ℕ → Set EucPlane)
    (hs_good : ∀ x ∈ s, ∀ᶠ L : ℕ in atTop, x ∈ good L)
    (hs_atom : ∀ x ∈ s, ∀ L,
      ∃ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L), x ∈ A)
    (hpair : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
        dist x y ≤ Real.exp (-R * L)) :
    (inferInstance : MeasurableSpace s) = MeasurableSpace.comap
      (fun x : s => twoSidedPartitionCode T T_inv P x.1) inferInstance := by
  apply measurableSpace_eq_comap_of_measurableEmbedding
  exact measurableEmbedding_twoSidedPartitionCode_restrict_of_shrinking
    T T_inv hT_right hT hT_inv P hP hs hR good hs_good hs_atom hpair

noncomputable def natTwoSidedPartitionCode
    {M : Type*} (T T_inv : M → M) (P : Finset (Set M))
    (x : M) : ℕ → (↥P → Bool) :=
  fun k => twoSidedPartitionCode T T_inv P x (Equiv.intEquivNat.symm k)

lemma measurable_natTwoSidedPartitionCode
    {M : Type*} [MeasurableSpace M]
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    Measurable (natTwoSidedPartitionCode T T_inv P) := by
  apply measurable_pi_lambda
  intro k
  exact (measurable_partitionSymbol P hP).comp
    (measurable_biIterate T T_inv hT hT_inv (Equiv.intEquivNat.symm k))

lemma measurableEmbedding_natTwoSidedPartitionCode_restrict_of_shrinking
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set EucPlane)) (hP : ∀ A ∈ P, MeasurableSet A)
    {s : Set EucPlane} (hs : MeasurableSet s)
    {lam1 lam2 R : ℝ} (hR : 0 < R)
    (good : ℕ → Set EucPlane)
    (hs_good : ∀ x ∈ s, ∀ᶠ L : ℕ in atTop, x ∈ good L)
    (hs_atom : ∀ x ∈ s, ∀ L,
      ∃ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L), x ∈ A)
    (hpair : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
        dist x y ≤ Real.exp (-R * L)) :
    MeasurableEmbedding
      (fun x : s => natTwoSidedPartitionCode T T_inv P x.1) := by
  letI : StandardBorelSpace s := hs.standardBorel
  have hmeas : Measurable
      (fun x : s => natTwoSidedPartitionCode T T_inv P x.1) :=
    (measurable_natTwoSidedPartitionCode T T_inv hT hT_inv P hP).comp
      measurable_subtype_coe
  apply hmeas.measurableEmbedding
  intro x y hxy
  have hxyInt : twoSidedPartitionCode T T_inv P x.1 =
      twoSidedPartitionCode T T_inv P y.1 := by
    funext z
    have hz := congrFun hxy (Equiv.intEquivNat z)
    simpa [natTwoSidedPartitionCode] using hz
  exact (measurableEmbedding_twoSidedPartitionCode_restrict_of_shrinking
    T T_inv hT_right hT hT_inv P hP hs hR good hs_good hs_atom hpair).injective
      hxyInt

noncomputable def twoSidedCodeFiltration
    {M : Type*} [MeasurableSpace M]
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    Filtration ℕ ‹MeasurableSpace M› :=
  Filtration.natural
    (fun k x => natTwoSidedPartitionCode T T_inv P x k)
    (fun k => ((measurable_pi_apply k).comp
      (measurable_natTwoSidedPartitionCode
        T T_inv hT hT_inv P hP)).stronglyMeasurable)

lemma iSup_twoSidedCodeFiltration_eq_comap
    {M : Type*} [MeasurableSpace M]
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) :
    (⨆ n, twoSidedCodeFiltration T T_inv hT hT_inv P hP n) =
      MeasurableSpace.comap (natTwoSidedPartitionCode T T_inv P) inferInstance := by
  have hcomap : MeasurableSpace.comap
      (natTwoSidedPartitionCode T T_inv P) inferInstance =
        ⨆ k, MeasurableSpace.comap
          (fun x => natTwoSidedPartitionCode T T_inv P x k) inferInstance := by
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, Function.comp_def]
  rw [hcomap]
  apply le_antisymm
  · apply iSup_le
    intro n
    change (⨆ k ≤ n, MeasurableSpace.comap
      (fun x => natTwoSidedPartitionCode T T_inv P x k) inferInstance) ≤ _
    apply iSup₂_le
    intro k hk
    exact le_iSup (fun j => MeasurableSpace.comap
      (fun x => natTwoSidedPartitionCode T T_inv P x j) inferInstance) k
  · apply iSup_le
    intro k
    apply le_iSup_of_le k
    change MeasurableSpace.comap
      (fun x => natTwoSidedPartitionCode T T_inv P x k) inferInstance ≤
        ⨆ j ≤ k, MeasurableSpace.comap
          (fun x => natTwoSidedPartitionCode T T_inv P x j) inferInstance
    exact le_iSup₂_of_le k le_rfl le_rfl

end Submission.Helpers
