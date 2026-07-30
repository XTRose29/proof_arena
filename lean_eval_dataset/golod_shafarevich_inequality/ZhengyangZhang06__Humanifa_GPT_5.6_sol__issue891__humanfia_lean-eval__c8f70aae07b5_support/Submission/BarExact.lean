import Submission.Presentation

namespace Submission.BarExact

open Submission.GroupAlgebra Submission.Presentation

noncomputable section

variable (k : Type*) (G : Type) [Field k] [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G
local instance : DecidableEq G := Classical.decEq G

abbrev BarOne := G → GroupAlgebra k G

noncomputable def barBasis (g : G) : BarOne k G := Pi.single g 1

noncomputable def barBoundary :
    BarOne k G →ₗ[GroupAlgebra k G] GroupAlgebra k G where
  toFun b := ∑ g, b g * (MonoidAlgebra.single g 1 - 1)
  map_add' b c := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a b := by
    change (∑ g, (a * b g) * (MonoidAlgebra.single g 1 - 1)) =
      a * ∑ g, b g * (MonoidAlgebra.single g 1 - 1)
    simp only [mul_assoc, Finset.mul_sum]

/-- The elementary degree-two bar relation
`g·[h] - [gh] + [g]`. -/
noncomputable def barRelation (g h : G) : BarOne k G :=
  MonoidAlgebra.single g (1 : k) • barBasis k G h - barBasis k G (g * h) +
    barBasis k G g

noncomputable def barRelationSpan : Submodule (GroupAlgebra k G) (BarOne k G) :=
  Submodule.span (GroupAlgebra k G)
    (Set.range fun gh : G × G ↦ barRelation k G gh.1 gh.2)

omit [Finite G] in
theorem barRelation_mem_span (g h : G) :
    barRelation k G g h ∈ barRelationSpan k G :=
  Submodule.subset_span ⟨(g, h), rfl⟩

theorem barBoundary_barBasis (g : G) :
    barBoundary k G (barBasis k G g) = MonoidAlgebra.single g 1 - 1 := by
  simp [barBoundary, barBasis, Pi.single_apply]

theorem barBoundary_barRelation (g h : G) :
    barBoundary k G (barRelation k G g h) = 0 := by
  rw [barRelation, map_add, map_sub, map_smul, barBoundary_barBasis,
    barBoundary_barBasis, barBoundary_barBasis]
  rw [smul_eq_mul]
  change MonoidAlgebra.single g (1 : k) *
      (MonoidAlgebra.single h (1 : k) - (1 : GroupAlgebra k G)) -
    (MonoidAlgebra.single (g * h) (1 : k) - 1) +
      (MonoidAlgebra.single g (1 : k) - 1) = 0
  rw [mul_sub, MonoidAlgebra.single_mul_single, mul_one]
  simp

/-- Expand a group-algebra element in the bar basis, using scalar
coefficients. -/
noncomputable def scalarBar : GroupAlgebra k G →ₗ[k] BarOne k G where
  toFun a g := MonoidAlgebra.single 1 (a.coeff g)
  map_add' a b := by
    funext g
    change MonoidAlgebra.single (1 : G) ((a + b).coeff g) =
      MonoidAlgebra.single 1 (a.coeff g) + MonoidAlgebra.single 1 (b.coeff g)
    rw [MonoidAlgebra.coeff_add]
    exact MonoidAlgebra.single_add 1 (a.coeff g) (b.coeff g)
  map_smul' c a := by
    funext g
    change MonoidAlgebra.single (1 : G) ((c • a).coeff g) =
      c • MonoidAlgebra.single 1 (a.coeff g)
    rw [MonoidAlgebra.coeff_smul]
    exact (MonoidAlgebra.smul_single c 1 (a.coeff g)).symm

omit [Finite G] in
theorem scalarBar_single (g : G) (c : k) :
    scalarBar k G (MonoidAlgebra.single g c) =
      c • barBasis k G g := by
  classical
  funext h
  ext x
  by_cases hgh : g = h
  · subst h
    simp [scalarBar, barBasis, MonoidAlgebra.coeff, Algebra.smul_def]
  · simp [scalarBar, barBasis, MonoidAlgebra.coeff, Algebra.smul_def,
      Ne.symm hgh]
    change (0 : k) = 0
    rfl

omit [Finite G] in
theorem smul_barBasis_sub_scalarBar_mul_mem (a : GroupAlgebra k G) (h : G) :
    a • barBasis k G h -
      scalarBar k G (a * (MonoidAlgebra.single h 1 - 1)) ∈
        barRelationSpan k G := by
  refine MonoidAlgebra.induction_on
    (p := fun b ↦ b • barBasis k G h -
      scalarBar k G (b * (MonoidAlgebra.single h 1 - 1)) ∈
        barRelationSpan k G) a ?_ ?_ ?_
  · intro g
    rw [MonoidAlgebra.of_apply, mul_sub, mul_one,
      MonoidAlgebra.single_mul_single, one_mul, map_sub,
      scalarBar_single, scalarBar_single, one_smul]
    convert barRelation_mem_span k G g h using 1
    simp only [barRelation, one_smul]
    abel
  · intro b c hb hc
    rw [show (b + c) • barBasis k G h -
        scalarBar k G ((b + c) * (MonoidAlgebra.single h 1 - 1)) =
      (b • barBasis k G h -
        scalarBar k G (b * (MonoidAlgebra.single h 1 - 1))) +
      (c • barBasis k G h -
        scalarBar k G (c * (MonoidAlgebra.single h 1 - 1))) by
      rw [add_smul, add_mul, map_add]
      abel]
    exact Submodule.add_mem _ hb hc
  · intro c b hb
    have hc : c • (b • barBasis k G h -
        scalarBar k G (b * (MonoidAlgebra.single h 1 - 1))) ∈
        barRelationSpan k G :=
      ((barRelationSpan k G).restrictScalars k).smul_mem c hb
    simpa only [smul_sub, smul_assoc, smul_mul_assoc, map_smul] using hc

theorem sum_smul_barBasis (b : BarOne k G) :
    (∑ g, b g • barBasis k G g) = b := by
  classical
  funext h
  simp [barBasis, Pi.single_apply]

theorem mem_barRelationSpan_of_barBoundary_eq_zero (b : BarOne k G)
    (hb : barBoundary k G b = 0) : b ∈ barRelationSpan k G := by
  classical
  have hsum : ∑ g, (b g • barBasis k G g -
      scalarBar k G (b g * (MonoidAlgebra.single g 1 - 1))) ∈
      barRelationSpan k G := by
    exact Submodule.sum_mem _ fun g _ ↦
      smul_barBasis_sub_scalarBar_mul_mem k G (b g) g
  rw [Finset.sum_sub_distrib, sum_smul_barBasis,
    ← map_sum, show (∑ g, b g * (MonoidAlgebra.single g 1 - 1)) = 0 from hb,
    map_zero, sub_zero] at hsum
  exact hsum

end

end Submission.BarExact
