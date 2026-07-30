import Submission.Helpers
import Submission.Hilbert

namespace Submission.GeneratorRank

open LeanEval.GroupTheory
open Submission.GroupAlgebra Submission.Hilbert

variable (k : Type*) (G : Type) [Field k] [Group G]

/-- The square of the augmentation ideal, as a subspace of the augmentation
ideal itself. -/
noncomputable def augmentationSquareInIdeal :
    Submodule k (augmentationPower k G 1) :=
  (augmentationPower k G 2).comap (augmentationPower k G 1).subtype

/-- The cotangent space `J / J²` of the augmented group algebra. -/
noncomputable abbrev AugmentationCotangent :=
  augmentationPower k G 1 ⧸ augmentationSquareInIdeal k G

/-- The augmentation-ideal element represented by a group element. -/
noncomputable def groupDifference (g : G) : augmentationPower k G 1 :=
  ⟨MonoidAlgebra.single g 1 - 1, by
    rw [augmentationPower_one]
    change augmentation k G (MonoidAlgebra.single g 1 - 1) = 0
    simp [augmentation]⟩

/-- The class of `g - 1` in `J / J²`. -/
noncomputable def groupToCotangent (g : G) : AugmentationCotangent k G :=
  Submodule.Quotient.mk (groupDifference k G g)

theorem groupDifference_mul_sub (g h : G) :
    groupDifference k G (g * h) - groupDifference k G g - groupDifference k G h =
      ⟨(MonoidAlgebra.single g 1 - 1) * (MonoidAlgebra.single h 1 - 1), by
        rw [augmentationPower_one]
        change augmentation k G
          ((MonoidAlgebra.single g 1 - 1) * (MonoidAlgebra.single h 1 - 1)) = 0
        simp [augmentation]⟩ := by
  apply Subtype.ext
  change MonoidAlgebra.single (g * h) 1 - 1 -
      (MonoidAlgebra.single g 1 - 1) - (MonoidAlgebra.single h 1 - 1) = _
  simp only [mul_sub, sub_mul, MonoidAlgebra.single_mul_single, mul_one]
  noncomm_ring

theorem groupToCotangent_mul (g h : G) :
    groupToCotangent k G (g * h) =
      groupToCotangent k G g + groupToCotangent k G h := by
  rw [← sub_eq_zero]
  change Submodule.Quotient.mk (p := augmentationSquareInIdeal k G)
      (groupDifference k G (g * h)) -
        (Submodule.Quotient.mk (groupDifference k G g) +
          Submodule.Quotient.mk (groupDifference k G h)) = 0
  rw [← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_sub,
    Submodule.Quotient.mk_eq_zero, sub_add_eq_sub_sub, groupDifference_mul_sub]
  change (MonoidAlgebra.single g 1 - 1) * (MonoidAlgebra.single h 1 - 1) ∈
    augmentationIdeal k G ^ 2
  rw [show (2 : ℕ) = 1 + 1 by omega, Submodule.pow_succ, Submodule.pow_one]
  apply Ideal.mul_mem_mul
  · change augmentation k G (MonoidAlgebra.single g 1 - 1) = 0
    simp [augmentation]
  · change augmentation k G (MonoidAlgebra.single h 1 - 1) = 0
    simp [augmentation]

@[simp]
theorem groupToCotangent_one : groupToCotangent k G 1 = 0 := by
  rw [groupToCotangent, Submodule.Quotient.mk_eq_zero]
  change MonoidAlgebra.single 1 1 - 1 ∈ augmentationIdeal k G ^ 2
  rw [← MonoidAlgebra.one_def, sub_self]
  exact Submodule.zero_mem _

@[simp]
theorem groupToCotangent_inv (g : G) :
    groupToCotangent k G g⁻¹ = -groupToCotangent k G g := by
  have h := groupToCotangent_mul k G g g⁻¹
  rw [mul_inv_cancel, groupToCotangent_one] at h
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h.symm)

/-- Subtracting the augmentation gives a canonical element of the augmentation ideal. -/
noncomputable def augmentationReduction :
    MonoidAlgebra k G →ₗ[k] augmentationPower k G 1 where
  toFun a := ⟨a - MonoidAlgebra.single 1 (augmentation k G a), by
    rw [augmentationPower_one]
    change augmentation k G
      (a - MonoidAlgebra.single 1 (augmentation k G a)) = 0
    simp [augmentation]⟩
  map_add' a b := by
    apply Subtype.ext
    change a + b - MonoidAlgebra.single 1 (augmentation k G (a + b)) =
      (a - MonoidAlgebra.single 1 (augmentation k G a)) +
        (b - MonoidAlgebra.single 1 (augmentation k G b))
    rw [map_add, MonoidAlgebra.single_add]
    abel
  map_smul' c a := by
    apply Subtype.ext
    change c • a - MonoidAlgebra.single 1 (augmentation k G (c • a)) =
      c • (a - MonoidAlgebra.single 1 (augmentation k G a))
    rw [map_smul, smul_sub]
    congr 1
    ext x
    simp

theorem augmentationReduction_single (g : G) (c : k) :
    augmentationReduction k G (MonoidAlgebra.single g c) =
      c • groupDifference k G g := by
  apply Subtype.ext
  simp [augmentationReduction, groupDifference, augmentation, Algebra.smul_def,
    MonoidAlgebra.one_def, mul_sub, MonoidAlgebra.single_mul_single]

theorem augmentationReduction_of_mem (a : augmentationPower k G 1) :
    augmentationReduction k G a.1 = a := by
  apply Subtype.ext
  have ha : augmentation k G a.1 = 0 := by
    have ha' := a.2
    have ha'' : a.1 ∈ augmentationIdeal k G := by
      change a.1 ∈ augmentationIdeal k G ^ 1 at ha'
      simpa only [Submodule.pow_one] using ha'
    change augmentation k G a.1 = 0 at ha''
    exact ha''
  change a.1 - MonoidAlgebra.single 1 (augmentation k G a.1) = a.1
  rw [ha]
  rw [MonoidAlgebra.single_zero, sub_zero]

/-- The canonical linear map from the group algebra onto its augmentation cotangent space. -/
noncomputable def cotangentMap :
    MonoidAlgebra k G →ₗ[k] AugmentationCotangent k G :=
  (augmentationSquareInIdeal k G).mkQ.comp (augmentationReduction k G)

theorem cotangentMap_single (g : G) (c : k) :
    cotangentMap k G (MonoidAlgebra.single g c) =
      c • groupToCotangent k G g := by
  rw [cotangentMap, LinearMap.comp_apply, augmentationReduction_single, map_smul,
    groupToCotangent, Submodule.mkQ_apply]

theorem cotangentMap_mul_groupDifference (a : MonoidAlgebra k G) (g : G) :
    cotangentMap k G (a * (MonoidAlgebra.single g 1 - 1)) =
      augmentation k G a • groupToCotangent k G g := by
  refine MonoidAlgebra.induction_on
    (p := fun b ↦ cotangentMap k G
      (b * (MonoidAlgebra.single g 1 - 1)) =
        augmentation k G b • groupToCotangent k G g) a ?_ ?_ ?_
  · intro h
    rw [MonoidAlgebra.of_apply]
    rw [mul_sub, mul_one, MonoidAlgebra.single_mul_single, one_mul, map_sub,
      cotangentMap_single, cotangentMap_single, augmentation,
      MonoidAlgebra.lift_single, MonoidHom.one_apply, one_smul,
      groupToCotangent_mul]
    simp only [one_smul]
    abel
  · intro a b ha hb
    rw [add_mul, map_add, ha, hb, map_add, add_smul]
  · intro c a ha
    rw [smul_mul_assoc, map_smul, ha, map_smul, smul_smul]
    rfl

theorem cotangentMap_surjective : Function.Surjective (cotangentMap k G) := by
  intro x
  obtain ⟨a, rfl⟩ := (augmentationSquareInIdeal k G).mkQ_surjective x
  refine ⟨a.1, ?_⟩
  rw [cotangentMap, LinearMap.comp_apply, augmentationReduction_of_mem]

/-- The classes of the elements `g - 1` span the augmentation cotangent space. -/
theorem span_range_groupToCotangent :
    Submodule.span k (Set.range (groupToCotangent k G)) = ⊤ := by
  rw [eq_top_iff]
  intro x hx
  clear hx
  obtain ⟨a, rfl⟩ := cotangentMap_surjective k G x
  refine MonoidAlgebra.induction_on
    (p := fun b ↦ cotangentMap k G b ∈
      Submodule.span k (Set.range (groupToCotangent k G))) a ?_ ?_ ?_
  · intro g
    simpa [cotangentMap_single] using
      (Submodule.subset_span (R := k) (Set.mem_range_self g))
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro c a ha
    rw [map_smul]
    exact Submodule.smul_mem _ c ha

/-- A finite group supplies a basis of `J/J²` represented by group
differences. -/
theorem exists_groupElements_cotangent_basis [Finite G] :
    ∃ g : Fin (Module.finrank k (AugmentationCotangent k G)) → G,
      LinearIndependent k (fun i ↦ groupToCotangent k G (g i)) ∧
        Submodule.span k (Set.range fun i ↦ groupToCotangent k G (g i)) = ⊤ := by
  classical
  letI := Fintype.ofFinite G
  have hfull := span_range_groupToCotangent k G
  rw [← show Module.finrank k
    (Submodule.span k (Set.range (groupToCotangent k G))) =
      Module.finrank k (AugmentationCotangent k G) by rw [hfull, finrank_top]]
  obtain ⟨f, hfmem, hfspan, hfind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq k
      (Set.range (groupToCotangent k G))
  choose g hg using hfmem
  have hfg : (fun i ↦ groupToCotangent k G (g i)) = f := by
    funext i
    exact hg i
  refine ⟨g, ?_, ?_⟩
  · rw [hfg]
    exact hfind
  · rw [hfg, hfspan, hfull]

section NilpotentGeneration

variable {R : Type*} [Ring R]

/-- A nilpotent two-sided ideal is contained in a left ideal as soon as it is
contained modulo its square. -/
theorem le_leftIdeal_of_le_sup_sq_of_isNilpotent (J L : Ideal R) [J.IsTwoSided]
    (hJL : J ≤ L ⊔ J ^ 2) (hnil : IsNilpotent J) : J ≤ L := by
  have hstep (n : ℕ) : J ^ (n + 1) ≤ L ⊔ J ^ (n + 2) := by
    rw [Submodule.pow_succ]
    calc
      J ^ n * J ≤ J ^ n * (L ⊔ J ^ 2) :=
        Ideal.mul_mono le_rfl hJL
      _ = J ^ n * L ⊔ J ^ n * J ^ 2 :=
        Ideal.mul_sup _ _ _
      _ ≤ L ⊔ J ^ (n + 2) := by
        apply sup_le
        · exact Ideal.mul_le_left.trans le_sup_left
        · rw [← Ideal.IsTwoSided.pow_add]
          exact le_sup_right
  have hpow (n : ℕ) : J ≤ L ⊔ J ^ (n + 1) := by
    induction n with
    | zero => simpa only [Nat.zero_add, Submodule.pow_one] using
        (le_sup_right : J ≤ L ⊔ J)
    | succ n ih =>
        exact ih.trans (sup_le le_sup_left (hstep n))
  obtain ⟨N, hN⟩ := hnil
  have hNsucc : J ^ (N + 1) = ⊥ := by
    rw [Submodule.pow_succ, hN]
    change (⊥ : Ideal R) * J = ⊥
    exact Ideal.bot_mul J
  simpa only [hNsucc, sup_bot_eq] using hpow N

variable (T : Set G)

/-- The left ideal generated by the differences `g - 1`, for `g ∈ T`. -/
noncomputable def generatorLeftIdeal : Ideal (MonoidAlgebra k G) :=
  Ideal.span ((fun g : G ↦ MonoidAlgebra.single g 1 - 1) '' T)

/-- The part of the generated left ideal lying in the augmentation ideal. -/
noncomputable def generatorLeftSubspaceInIdeal :
    Submodule k (augmentationPower k G 1) :=
  ((generatorLeftIdeal k G T : Submodule (MonoidAlgebra k G) _).restrictScalars k).comap
    (augmentationPower k G 1).subtype

theorem groupDifference_mem_generatorLeftSubspaceInIdeal {g : G} (hg : g ∈ T) :
    groupDifference k G g ∈ generatorLeftSubspaceInIdeal k G T := by
  change MonoidAlgebra.single g 1 - 1 ∈ generatorLeftIdeal k G T
  exact Ideal.subset_span ⟨g, hg, rfl⟩

theorem augmentationIdeal_le_generatorLeftIdeal_of_span
    (hspan : Submodule.span k (groupToCotangent k G '' T) = ⊤)
    (hnil : IsNilpotent (augmentationIdeal k G)) :
    augmentationIdeal k G ≤ generatorLeftIdeal k G T := by
  let W : Submodule k (AugmentationCotangent k G) :=
    (generatorLeftSubspaceInIdeal k G T).map (augmentationSquareInIdeal k G).mkQ
  have hspanW : Submodule.span k (groupToCotangent k G '' T) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨groupDifference k G g,
      groupDifference_mem_generatorLeftSubspaceInIdeal k G T hg, rfl⟩
  have hW : W = ⊤ := top_unique (hspan ▸ hspanW)
  have hmod : augmentationIdeal k G ≤
      generatorLeftIdeal k G T ⊔ augmentationIdeal k G ^ 2 := by
    intro a ha
    let x : augmentationPower k G 1 := ⟨a, by
      change a ∈ augmentationIdeal k G ^ 1
      simpa only [Submodule.pow_one] using ha⟩
    have hxW : (augmentationSquareInIdeal k G).mkQ x ∈ W := by
      rw [hW]
      exact Submodule.mem_top
    obtain ⟨y, hy, hxy⟩ := hxW
    have hdiff : x - y ∈ augmentationSquareInIdeal k G := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change (augmentationSquareInIdeal k G).mkQ x -
        (augmentationSquareInIdeal k G).mkQ y = 0
      rw [hxy, sub_self]
    refine Submodule.mem_sup.mpr ⟨y.1, hy, (x - y).1, hdiff, ?_⟩
    change y.1 + (x.1 - y.1) = a
    simp [x]
  letI : (augmentationIdeal k G).IsTwoSided := ⟨fun b ha ↦ by
    change augmentation k G (_ * b) = 0
    rw [map_mul]
    change augmentation k G _ = 0 at ha
    rw [ha, zero_mul]⟩
  exact le_leftIdeal_of_le_sup_sq_of_isNilpotent
    (augmentationIdeal k G) (generatorLeftIdeal k G T) hmod hnil

section DetectGeneratedSubgroup

variable [Finite G]

/-- The sum of the elements of a subgroup, regarded as an element of the group
algebra.  Its stabilizer under left multiplication is exactly the subgroup. -/
noncomputable def subgroupSum (H : Subgroup G) : MonoidAlgebra k G := by
  classical
  letI := Fintype.ofFinite G
  exact ∑ h : H, MonoidAlgebra.single h.1 1

theorem subgroupSum_coeff_of_mem (H : Subgroup G) (g : G) (hg : g ∈ H) :
    (subgroupSum k G H).coeff g = 1 := by
  classical
  letI := Fintype.ofFinite G
  let ev : MonoidAlgebra k G →+ k :=
    { toFun := fun (a : MonoidAlgebra k G) ↦ a.coeff g
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev (subgroupSum k G H) = 1
  rw [subgroupSum, map_sum]
  dsimp only [ev]
  change (∑ h : H, (MonoidAlgebra.single h.1 (1 : k)).coeff g) = 1
  simp only [MonoidAlgebra.coeff, MonoidAlgebra.single_apply]
  rw [Finset.sum_eq_single (⟨g, hg⟩ : H)]
  · simp
  · intro h _ hne
    rw [if_neg]
    exact fun heq ↦ hne (Subtype.ext heq)
  · simp

theorem subgroupSum_coeff_of_not_mem (H : Subgroup G) (g : G) (hg : g ∉ H) :
    (subgroupSum k G H).coeff g = 0 := by
  classical
  letI := Fintype.ofFinite G
  let ev : MonoidAlgebra k G →+ k :=
    { toFun := fun (a : MonoidAlgebra k G) ↦ a.coeff g
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev (subgroupSum k G H) = 0
  rw [subgroupSum, map_sum]
  dsimp only [ev]
  change (∑ h : H, (MonoidAlgebra.single h.1 (1 : k)).coeff g) = 0
  simp only [MonoidAlgebra.coeff, MonoidAlgebra.single_apply]
  apply Finset.sum_eq_zero
  intro h _
  rw [if_neg]
  exact fun heq ↦ hg (heq ▸ h.2)

theorem single_mul_subgroupSum {H : Subgroup G} {g : G} (hg : g ∈ H) :
    MonoidAlgebra.single g (1 : k) * subgroupSum k G H = subgroupSum k G H := by
  ext x
  change (MonoidAlgebra.single g (1 : k) * subgroupSum k G H : G →₀ k) x =
    (subgroupSum k G H).coeff x
  rw [MonoidAlgebra.single_mul_apply, one_mul]
  have hmem : g⁻¹ * x ∈ H ↔ x ∈ H := by
    constructor
    · intro hx
      simpa only [mul_assoc, mul_inv_cancel_left] using H.mul_mem hg hx
    · intro hx
      exact H.mul_mem (H.inv_mem hg) hx
  by_cases hx : x ∈ H
  · exact (subgroupSum_coeff_of_mem k G H (g⁻¹ * x) (hmem.mpr hx)).trans
      (subgroupSum_coeff_of_mem k G H x hx).symm
  · exact (subgroupSum_coeff_of_not_mem k G H (g⁻¹ * x)
      (fun h ↦ hx (hmem.mp h))).trans
        (subgroupSum_coeff_of_not_mem k G H x hx).symm

/-- The left ideal annihilating the subgroup sum on the right. -/
noncomputable def subgroupSumAnnihilator (H : Subgroup G) :
    Ideal (MonoidAlgebra k G) where
  carrier := {a | a * subgroupSum k G H = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_mul, ha, hb, add_zero]
  smul_mem' := by
    intro a b hb
    simp only [Set.mem_setOf_eq] at hb ⊢
    change (a * b) * subgroupSum k G H = 0
    rw [mul_assoc, hb, mul_zero]

theorem generatorLeftIdeal_le_subgroupSumAnnihilator
    {H : Subgroup G} (hT : T ⊆ H) :
    generatorLeftIdeal k G T ≤ subgroupSumAnnihilator k G H := by
  rw [generatorLeftIdeal, Ideal.span_le]
  rintro _ ⟨g, hg, rfl⟩
  change (MonoidAlgebra.single g 1 - 1) * subgroupSum k G H = 0
  rw [sub_mul, single_mul_subgroupSum k G (hT hg), one_mul, sub_self]

theorem mem_closure_of_groupDifference_mem_generatorLeftIdeal {g : G}
    (hg : MonoidAlgebra.single g (1 : k) - 1 ∈ generatorLeftIdeal k G T) :
    g ∈ Subgroup.closure T := by
  classical
  letI := Fintype.ofFinite G
  let H := Subgroup.closure T
  have hT : T ⊆ H := Subgroup.subset_closure
  have hle := generatorLeftIdeal_le_subgroupSumAnnihilator k G T hT
  have hzero : (MonoidAlgebra.single g (1 : k) - 1) * subgroupSum k G H = 0 := hle hg
  have heq : MonoidAlgebra.single g (1 : k) * subgroupSum k G H = subgroupSum k G H := by
    simpa only [sub_mul, one_mul, sub_eq_zero] using hzero
  by_contra hnot
  have hcoeff := congrArg (fun a : MonoidAlgebra k G ↦ a.coeff g) heq
  have hleft :
      (MonoidAlgebra.single g (1 : k) * subgroupSum k G H).coeff g = 1 := by
    change (MonoidAlgebra.single g (1 : k) * subgroupSum k G H : G →₀ k) g = 1
    rw [MonoidAlgebra.single_mul_apply, one_mul]
    change (subgroupSum k G H).coeff (g⁻¹ * g) = 1
    rw [inv_mul_cancel]
    exact subgroupSum_coeff_of_mem k G H 1 H.one_mem
  have hright : (subgroupSum k G H).coeff g = 0 :=
    subgroupSum_coeff_of_not_mem k G H g hnot
  rw [hleft, hright] at hcoeff
  exact one_ne_zero hcoeff

/-- A set whose group differences span `J/J²` generates a finite group when
the augmentation ideal is nilpotent. -/
theorem closure_eq_top_of_span_groupToCotangent
    (hspan : Submodule.span k (groupToCotangent k G '' T) = ⊤)
    (hnil : IsNilpotent (augmentationIdeal k G)) :
    Subgroup.closure T = ⊤ := by
  rw [eq_top_iff]
  intro g _
  apply mem_closure_of_groupDifference_mem_generatorLeftIdeal k G T
  exact augmentationIdeal_le_generatorLeftIdeal_of_span k G T hspan hnil
    (show MonoidAlgebra.single g (1 : k) - 1 ∈ augmentationIdeal k G by
      change augmentation k G (MonoidAlgebra.single g 1 - 1) = 0
      simp [augmentation])

/-- The inverse image of a subspace of `J/J²` under `g ↦ g - 1` is a
subgroup. -/
noncomputable def cotangentPreimageSubgroup
    (W : Submodule k (AugmentationCotangent k G)) : Subgroup G where
  carrier := {g | groupToCotangent k G g ∈ W}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change groupToCotangent k G (g * h) ∈ W
    change groupToCotangent k G g ∈ W at hg
    change groupToCotangent k G h ∈ W at hh
    rw [groupToCotangent_mul]
    exact W.add_mem hg hh
  inv_mem' := by
    intro g hg
    change groupToCotangent k G g⁻¹ ∈ W
    change groupToCotangent k G g ∈ W at hg
    rw [groupToCotangent_inv]
    exact W.neg_mem hg

omit [Finite G] in
/-- The cotangent images of any group-generating set span `J/J²`. -/
theorem span_groupToCotangent_eq_top_of_closure_eq_top
    (hT : Subgroup.closure T = ⊤) :
    Submodule.span k (groupToCotangent k G '' T) = ⊤ := by
  let W := Submodule.span k (groupToCotangent k G '' T)
  have hclosure : Subgroup.closure T ≤ cotangentPreimageSubgroup k G W := by
    rw [Subgroup.closure_le]
    intro g hg
    exact Submodule.subset_span ⟨g, hg, rfl⟩
  apply top_unique
  rw [← span_range_groupToCotangent k G, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ Subgroup.closure T := by
    rw [hT]
    exact Subgroup.mem_top g
  exact hclosure hg

/-- Burnside's basis theorem in the form needed here: for a finite group with
nilpotent augmentation ideal, the minimal number of generators is the
dimension of `J/J²`. -/
theorem generatorRank_eq_finrank_augmentationCotangent
    [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]
    (hnil : IsNilpotent (augmentationIdeal k G)) :
    generatorRank G = Module.finrank k (AugmentationCotangent k G) := by
  classical
  letI := Fintype.ofFinite G
  let d := Module.finrank k (AugmentationCotangent k G)
  have hgen_le : generatorRank G ≤ d := by
    have hfull := span_range_groupToCotangent k G
    obtain ⟨f, hfmem, hfspan, _⟩ :=
      Submodule.exists_fun_fin_finrank_span_eq k
        (Set.range (groupToCotangent k G))
    choose g hg using hfmem
    let S : Finset G := Finset.univ.image g
    have hsub : Set.range f ⊆ groupToCotangent k G '' (S : Set G) := by
      rintro _ ⟨i, rfl⟩
      refine ⟨g i, ?_, ?_⟩
      · simp [S]
      · exact hg i
    have hspanS : Submodule.span k
        (groupToCotangent k G '' (S : Set G)) = ⊤ := by
      apply top_unique
      have htop : Submodule.span k (Set.range f) = ⊤ := by
        rw [hfspan, hfull]
      rw [← htop]
      exact Submodule.span_mono hsub
    have hclosure : Subgroup.closure (S : Set G) = ⊤ :=
      closure_eq_top_of_span_groupToCotangent k G (S : Set G) hspanS hnil
    calc
      generatorRank G ≤ S.card := Helpers.generatorRank_le_card G S (by
        rw [Helpers.topologicalClosure_eq_self, hclosure])
      _ ≤ Module.finrank k
          (Submodule.span k (Set.range (groupToCotangent k G))) := by
        simpa only [S, Finset.card_univ, Fintype.card_fin] using (Finset.card_image_le :
          (Finset.univ.image g).card ≤ Finset.univ.card)
      _ = d := by rw [hfull, finrank_top]
  have hfinrank_le : Module.finrank k (AugmentationCotangent k G) ≤ generatorRank G := by
    obtain ⟨S, hcard, htop⟩ := Helpers.exists_generatorRank_finset G
    rw [Helpers.topologicalClosure_eq_self] at htop
    have hspan := span_groupToCotangent_eq_top_of_closure_eq_top
      k G (S : Set G) htop
    let U : Finset (AugmentationCotangent k G) := S.image (groupToCotangent k G)
    have hspanU : Submodule.span k (U : Set (AugmentationCotangent k G)) = ⊤ := by
      simpa only [U, Finset.coe_image] using hspan
    calc
      Module.finrank k (AugmentationCotangent k G) =
          Module.finrank k (Submodule.span k (U : Set (AugmentationCotangent k G))) := by
            rw [hspanU, finrank_top]
      _ ≤ U.card := by
        simpa using finrank_span_le_card (U : Set (AugmentationCotangent k G))
      _ ≤ S.card := Finset.card_image_le
      _ = generatorRank G := hcard
  exact Nat.le_antisymm hgen_le hfinrank_le

end DetectGeneratedSubgroup

end NilpotentGeneration

end Submission.GeneratorRank
