import Submission.GeneratorRank

namespace Submission.Presentation

open Submission.GroupAlgebra Submission.GeneratorRank Submission.Hilbert

variable (k : Type*) (G : Type) [Field k] [Group G]

abbrev GroupAlgebra := MonoidAlgebra k G

noncomputable abbrev AugmentationIdeal := augmentationIdeal k G

abbrev FreeRelations (d : ℕ) := Fin d → GroupAlgebra k G

/-- The first differential in the minimal group-algebra presentation, sending
the `i`th free basis vector to `gᵢ - 1`. -/
noncomputable def presentationMap {d : ℕ} (g : Fin d → G) :
    FreeRelations k G d →ₗ[GroupAlgebra k G] AugmentationIdeal k G where
  toFun v := ⟨∑ i, v i * (MonoidAlgebra.single (g i) 1 - 1), by
    change augmentation k G (∑ i, v i * (MonoidAlgebra.single (g i) 1 - 1)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_mul]
    simp [augmentation]⟩
  map_add' v w := by
    apply Subtype.ext
    change (∑ i, (v i + w i) * (MonoidAlgebra.single (g i) 1 - 1)) =
      (∑ i, v i * (MonoidAlgebra.single (g i) 1 - 1)) +
        ∑ i, w i * (MonoidAlgebra.single (g i) 1 - 1)
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' a v := by
    apply Subtype.ext
    change (∑ i, (a * v i) * (MonoidAlgebra.single (g i) 1 - 1)) =
      a * ∑ i, v i * (MonoidAlgebra.single (g i) 1 - 1)
    simp only [mul_assoc, Finset.mul_sum]

/-- The range of `presentationMap`, regarded as a left ideal. -/
noncomputable def presentationRangeIdeal {d : ℕ} (g : Fin d → G) :
    Ideal (GroupAlgebra k G) where
  carrier := Set.range fun v ↦ (presentationMap k G g v).1
  zero_mem' := ⟨0, congrArg Subtype.val (map_zero (presentationMap k G g))⟩
  add_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨v + w, congrArg Subtype.val (map_add (presentationMap k G g) v w)⟩
  smul_mem' := by
    rintro a _ ⟨v, rfl⟩
    exact ⟨a • v, congrArg Subtype.val (map_smul (presentationMap k G g) a v)⟩

theorem generator_mem_presentationRangeIdeal {d : ℕ} (g : Fin d → G) (i : Fin d) :
    MonoidAlgebra.single (g i) (1 : k) - 1 ∈ presentationRangeIdeal k G g := by
  classical
  change ∃ v, (presentationMap k G g v).1 =
    MonoidAlgebra.single (g i) (1 : k) - 1
  refine ⟨Pi.single i 1, ?_⟩
  simp [presentationMap, Pi.single_apply]

theorem generatorLeftIdeal_range_le_presentationRangeIdeal {d : ℕ}
    (g : Fin d → G) :
    generatorLeftIdeal k G (Set.range g) ≤ presentationRangeIdeal k G g := by
  rw [generatorLeftIdeal, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact generator_mem_presentationRangeIdeal k G g i

theorem presentationMap_surjective_of_cotangent_span [Finite G]
    {d : ℕ} (g : Fin d → G)
    (hspan : Submodule.span k
      (groupToCotangent k G '' Set.range g) = ⊤)
    (hnil : IsNilpotent (augmentationIdeal k G)) :
    Function.Surjective (presentationMap k G g) := by
  intro x
  have hxJ : x.1 ∈ augmentationIdeal k G := x.2
  have hxrange : x.1 ∈ presentationRangeIdeal k G g :=
    generatorLeftIdeal_range_le_presentationRangeIdeal k G g
      (augmentationIdeal_le_generatorLeftIdeal_of_span k G (Set.range g) hspan hnil hxJ)
  change ∃ v, (presentationMap k G g v).1 = x.1 at hxrange
  obtain ⟨v, hv⟩ := hxrange
  refine ⟨v, Subtype.ext ?_⟩
  exact hv

noncomputable abbrev RelationKernel {d : ℕ} (g : Fin d → G) :=
  LinearMap.ker (presentationMap k G g)

theorem relationKernel_coordinate_mem_augmentationIdeal {d : ℕ}
    (g : Fin d → G)
    (hlin : LinearIndependent k (fun i ↦ groupToCotangent k G (g i)))
    (x : RelationKernel k G g) (i : Fin d) :
    x.1 i ∈ augmentationIdeal k G := by
  have hsum : ∑ j, x.1 j * (MonoidAlgebra.single (g j) 1 - 1) = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp x.2)
  have hcot := congrArg (cotangentMap k G) hsum
  simp only [map_sum, cotangentMap_mul_groupDifference, map_zero] at hcot
  exact (Fintype.linearIndependent_iff.mp hlin
    (fun j ↦ augmentation k G (x.1 j)) hcot i)

/-- The radical of the relation module: the span of augmentation-ideal
multiples of relations. -/
noncomputable def relationRadical {d : ℕ} (g : Fin d → G) :
    Submodule k (RelationKernel k G g) :=
  Submodule.span k {z | ∃ (a : GroupAlgebra k G), a ∈ augmentationIdeal k G ∧
    ∃ x : RelationKernel k G g, z = a • x}

/-- The space of minimal relations `K / J K`. -/
noncomputable abbrev RelationSpace {d : ℕ} (g : Fin d → G) :=
  RelationKernel k G g ⧸ relationRadical k G g

/-- A functional on minimal relations, pulled back to the full relation
module. -/
noncomputable def relationFunctional {d : ℕ} (g : Fin d → G)
    (ell : Module.Dual k (RelationSpace k G g)) :
    RelationKernel k G g →ₗ[k] k :=
  ell.comp (relationRadical k G g).mkQ

theorem relationFunctional_smul {d : ℕ} (g : Fin d → G)
    (ell : Module.Dual k (RelationSpace k G g))
    (a : GroupAlgebra k G) (x : RelationKernel k G g) :
    relationFunctional k G g ell (a • x) =
      augmentation k G a * relationFunctional k G g ell x := by
  let a₀ := a - MonoidAlgebra.single 1 (augmentation k G a)
  have ha₀ : a₀ ∈ augmentationIdeal k G := by
    change augmentation k G a₀ = 0
    simp [a₀, augmentation]
  have hrad : a₀ • x ∈ relationRadical k G g :=
    Submodule.subset_span ⟨a₀, ha₀, x, rfl⟩
  have hdiff : a • x - augmentation k G a • x = a₀ • x := by
    apply Subtype.ext
    ext i h
    simp [a₀, Algebra.smul_def, sub_mul]
  have hquot : (relationRadical k G g).mkQ (a • x) =
      augmentation k G a • (relationRadical k G g).mkQ x := by
    rw [← sub_eq_zero, ← map_smul, ← map_sub, hdiff,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hrad
  simp only [relationFunctional, LinearMap.comp_apply, hquot, map_smul, smul_eq_mul]

end Submission.Presentation
