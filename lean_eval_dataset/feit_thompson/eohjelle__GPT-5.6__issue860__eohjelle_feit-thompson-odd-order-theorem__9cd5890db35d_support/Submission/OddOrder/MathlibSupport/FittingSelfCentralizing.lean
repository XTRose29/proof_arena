import Submission.OddOrder.MathlibSupport.FittingNilpotent
import Submission.OddOrder.MathlibSupport.MinimalNormalExistence

/-!
The Fitting subgroup of a finite solvable group contains its centralizer.

This is the mathlib-shaped form of `BGsection1.cent_sub_Fitting`.  The proof
uses a chief factor inside `C_G(F) / (C_G(F) ∩ F)` and the fact that a central
extension of a nilpotent group is nilpotent.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

theorem centralizer_fittingCore_le [IsSolvable G] :
    Subgroup.centralizer (fittingCore G : Set G) ≤ fittingCore G := by
  let F : Subgroup G := fittingCore G
  letI : F.Characteristic := by
    dsimp [F]
    infer_instance
  let C : Subgroup G := Subgroup.centralizer (F : Set G)
  letI : C.Characteristic := by
    dsimp [C]
    infer_instance
  let Z : Subgroup G := C ⊓ F
  letI : Z.Normal := by
    dsimp [Z]
    infer_instance
  change C ≤ F
  by_contra hCF
  have hZC : Z < C := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hZCeq
    apply hCF
    intro x hx
    have hxZ : x ∈ Z := by rw [hZCeq]; exact hx
    exact hxZ.2
  obtain ⟨N, hChief, hNC⟩ :=
    exists_chiefFactor_le hZC (by infer_instance : C.Normal)
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  let Nbar : Subgroup (G ⧸ Z) := N.map q
  obtain ⟨p, hp, hNbarP, _⟩ := hChief.exists_prime_isPGroup_pow_eq_one
  letI : Fact p.Prime := ⟨hp⟩
  have hNbarP' : IsPGroup p Nbar := by
    simpa [Nbar, q] using hNbarP
  letI : Group.IsNilpotent Nbar := hNbarP'.isNilpotent
  let f : N →* Nbar :=
    (q.comp N.subtype).codRestrict Nbar (fun x ↦ by
      change q (x : G) ∈ N.map q
      exact ⟨x, x.property, rfl⟩)
  have hfker : f.ker ≤ Subgroup.center N := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : G) * (x : G) = (x : G) * (y : G)
    have hfx : f x = 1 := MonoidHom.mem_ker.mp hx
    have hqx : q (x : G) = 1 := congrArg Subtype.val hfx
    have hxZ : (x : G) ∈ Z := by
      exact QuotientGroup.eq_one_iff (x : G) |>.mp hqx
    have hxF : (x : G) ∈ F := hxZ.2
    have hyC : (y : G) ∈ C := hNC y.property
    exact (Subgroup.mem_centralizer_iff.mp hyC (x : G) hxF).symm
  have hNnil : Group.IsNilpotent N :=
    Subgroup.isNilpotent_of_ker_le_center f hfker
  have hNF : N ≤ F :=
    nilpotent_normal_le_fittingCore hChief.upper_normal hNnil
  have hNZ : N ≤ Z := le_inf hNC hNF
  exact (not_le_of_gt hChief.lt) hNZ

end Submission.OddOrder.MathlibSupport
