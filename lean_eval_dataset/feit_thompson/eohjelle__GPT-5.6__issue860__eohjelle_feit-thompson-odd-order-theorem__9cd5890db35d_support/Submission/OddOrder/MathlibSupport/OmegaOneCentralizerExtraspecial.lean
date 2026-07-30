import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.Extraspecial
import Submission.OddOrder.MathlibSupport.OmegaOne

/-!
The first omega subgroup of the centralizer of an extraspecial omega subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- If the image of `omegaOne p R` is an extraspecial subgroup `S`, then the
image of the first omega subgroup of its centralizer in `R` is the derived
subgroup of `S`. -/
theorem map_omegaOne_centralizerWithin_eq_map_commutator_of_extraspecial
    {p : ℕ} [Fact p.Prime] {R S : Subgroup G}
    (hR : IsPGroup p R)
    (hOmega : (omegaOne p R).map R.subtype = S)
    (hS : IsExtraspecial S) :
    (omegaOne p (centralizerWithin R S)).map
        (centralizerWithin R S).subtype =
      (_root_.commutator S).map S.subtype := by
  have hSR : S ≤ R := by
    rw [← hOmega]
    rintro _ ⟨x, _hx, rfl⟩
    exact x.property
  have hSp : IsPGroup p S :=
    (hR.to_subgroup (S.subgroupOf R)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hSR)
  have hcenterCard : Nat.card (Subgroup.center S) = p :=
    hS.center_card_eq hSp
  rw [hS.toIsSpecial.commutator_eq_center, map_center_eq_centerWithin]
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply omegaOne_le p
    intro x hxpow
    have hxpowG : (x : G) ^ p = 1 := by
      exact congrArg Subtype.val hxpow
    let xR : R := ⟨x, x.property.1⟩
    have hxRpow : xR ^ p = 1 := by
      apply Subtype.ext
      exact hxpowG
    have hxS : (x : G) ∈ S := by
      apply hOmega.le
      exact ⟨xR, mem_omegaOne_of_pow_eq_one p hxRpow, rfl⟩
    exact ⟨hxS, x.property.2⟩
  · intro z hz
    let zS : S := ⟨z, hz.1⟩
    have hzCenter : zS ∈ Subgroup.center S := by
      apply Subgroup.mem_center_iff.mpr
      intro s
      apply Subtype.ext
      exact hz.2 s s.property
    let zZ : Subgroup.center S := ⟨zS, hzCenter⟩
    have hzPowZ : zZ ^ p = 1 := by
      rw [← hcenterCard]
      exact pow_card_eq_one'
    have hzPowG : z ^ p = 1 := by
      exact congrArg (fun w : Subgroup.center S => ((w : S) : G)) hzPowZ
    let zC : centralizerWithin R S :=
      ⟨z, hSR hz.1, hz.2⟩
    have hzPowC : zC ^ p = 1 := by
      apply Subtype.ext
      exact hzPowG
    exact ⟨zC, mem_omegaOne_of_pow_eq_one p hzPowC, rfl⟩

end Submission.OddOrder.MathlibSupport
