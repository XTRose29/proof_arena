import Submission.OddOrder.MathlibSupport.Metacyclic

/-!
Subgroup heredity of metacyclicity.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- Every subgroup of a metacyclic group is metacyclic. -/
theorem isMetacyclic_subgroup
    (hG : IsMetacyclic G) (H : Subgroup G) : IsMetacyclic H := by
  classical
  rcases hG with ⟨S, hSnormal, hScyclic, hQcyclic⟩
  letI : S.Normal := hSnormal
  let T : Subgroup H := S.subgroupOf H
  have hTnormal : T.Normal := by
    dsimp [T]
    infer_instance
  letI : T.Normal := hTnormal
  let toS : T →* S :=
    { toFun := fun t ↦ ⟨((t : H) : G), t.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hTcyclic : IsCyclic T := by
    apply isCyclic_of_injective toS
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S ↦ (z : G)) hxy
  let q : G →* G ⧸ S := QuotientGroup.mk' S
  let f : H →* G ⧸ S := q.comp H.subtype
  let I : Subgroup (G ⧸ S) := f.range
  let fI : H →* I := f.rangeRestrict
  have hfIsurj : Function.Surjective fI :=
    MonoidHom.rangeRestrict_surjective f
  have hker : T = fI.ker := by
    ext x
    change ((x : H) : G) ∈ S ↔ fI x = 1
    constructor
    · intro hx
      apply Subtype.ext
      change q ((x : H) : G) = 1
      exact (QuotientGroup.eq_one_iff ((x : H) : G)).mpr hx
    · intro hx
      have hx' : q ((x : H) : G) = 1 :=
        congrArg (fun z : I ↦ (z : G ⧸ S)) hx
      exact (QuotientGroup.eq_one_iff ((x : H) : G)).mp hx'
  let e : H ⧸ T ≃* I := QuotientGroup.liftEquiv T hfIsurj hker
  have hIcyclic : IsCyclic I := by
    letI : IsCyclic (G ⧸ S) := hQcyclic
    exact Subgroup.isCyclic_of_le le_top
  have hQcyclic' : IsCyclic (H ⧸ T) := e.isCyclic.mpr hIcyclic
  exact ⟨T, hTnormal, hTcyclic, hQcyclic'⟩

/-- The derived subgroup of a metacyclic group is cyclic. -/
theorem commutator_isCyclic_of_isMetacyclic
    (hG : IsMetacyclic G) : IsCyclic (_root_.commutator G) := by
  rcases hG with ⟨S, hSnormal, hScyclic, hQcyclic⟩
  letI : S.Normal := hSnormal
  letI : IsCyclic S := hScyclic
  exact Subgroup.isCyclic_of_le
    (Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      hQcyclic.isMulCommutative)

end Submission.OddOrder.MathlibSupport
