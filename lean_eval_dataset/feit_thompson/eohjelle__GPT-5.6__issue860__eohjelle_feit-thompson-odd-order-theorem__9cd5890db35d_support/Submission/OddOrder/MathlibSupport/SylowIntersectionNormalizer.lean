import Submission.OddOrder.MathlibSupport.PGroupNormalizer

/-!
# Extending a Sylow subgroup of an intersection

If a Sylow subgroup of `H ⊓ M` has ambient normalizer contained in `M`,
then it is already the image of a Sylow subgroup of `H`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- A Sylow subgroup of an intersection whose ambient normalizer remains in
the second subgroup extends to a Sylow subgroup of the first subgroup without
growing in the ambient group. -/
theorem exists_sylow_map_eq_of_sylow_inf_of_normalizer_le
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (H M : Subgroup G)
    (R : Sylow p ↑(H ⊓ M))
    (hNRM : Subgroup.normalizer
      ((R : Subgroup ↑(H ⊓ M)).map (H ⊓ M).subtype : Set G) ≤ M) :
    ∃ S : Sylow p H,
      (S : Subgroup H).map H.subtype =
        (R : Subgroup ↑(H ⊓ M)).map (H ⊓ M).subtype := by
  let I : Subgroup G := H ⊓ M
  let RG : Subgroup G := (R : Subgroup I).map I.subtype
  have hRGH : RG ≤ H :=
    Subgroup.map_subtype_le (R : Subgroup I) |>.trans inf_le_left
  have hRGp : IsPGroup p RG := R.isPGroup'.map I.subtype
  let SHsub : Subgroup H := RG.subgroupOf H
  have hSHp : IsPGroup p SHsub :=
    hRGp.of_equiv (Subgroup.subgroupOfEquivOfLe hRGH).symm
  let S : Sylow p H :=
    { toSubgroup := SHsub
      isPGroup' := hSHp
      is_maximal' := by
        intro X hXp hSHX
        by_contra hXne
        have hSHltX : SHsub < X :=
          lt_of_le_of_ne hSHX (Ne.symm hXne)
        let XG : Subgroup G := X.map H.subtype
        have hXGp : IsPGroup p XG := hXp.map H.subtype
        have hRGltXG : RG < XG := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hRGH]
          exact Subgroup.map_subtype_lt_map_subtype.mpr hSHltX
        let T : Subgroup G :=
          XG ⊓ Subgroup.normalizer (RG : Set G)
        have hRGltT : RG < T :=
          lt_inf_normalizer_of_isPGroup hXGp hRGltXG
        have hTH : T ≤ H :=
          inf_le_left.trans (Subgroup.map_subtype_le X)
        have hTM : T ≤ M := inf_le_right.trans hNRM
        have hTI : T ≤ I := le_inf hTH hTM
        let TI : Subgroup I := T.subgroupOf I
        have hTIp : IsPGroup p TI :=
          (hXGp.to_le inf_le_left).of_equiv
            (Subgroup.subgroupOfEquivOfLe hTI).symm
        have hRTI : (R : Subgroup I) ≤ TI := by
          intro x hx
          change (x : G) ∈ T
          exact hRGltT.le (Subgroup.mem_map_of_mem I.subtype hx)
        have hTIR : TI = (R : Subgroup I) :=
          R.is_maximal' hTIp hRTI
        have hTRG : T = RG := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hTI]
          change TI.map I.subtype = RG
          rw [hTIR]
        exact hRGltT.ne hTRG.symm }
  refine ⟨S, ?_⟩
  change SHsub.map H.subtype = RG
  exact Subgroup.map_subgroupOf_eq_of_le hRGH

end Submission.OddOrder.MathlibSupport
