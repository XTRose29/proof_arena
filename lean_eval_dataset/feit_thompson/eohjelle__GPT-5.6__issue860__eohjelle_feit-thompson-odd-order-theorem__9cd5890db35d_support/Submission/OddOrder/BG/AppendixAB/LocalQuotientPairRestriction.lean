import Submission.OddOrder.BG.AppendixAB.PairGeneratedLocalQuotientHom

/-!
Restriction maps between local quotient pairs attached to nested invariant
subgroups.
-/

namespace Submission.OddOrder.BG.AppendixAB

variable {G : Type*} [Group G]

/-- If `M ≤ E` and the same pair normalizes both subgroups, restriction of
the pair action induces a homomorphism from the local quotient for `E` onto
the local quotient for `M`. -/
noncomputable def localQuotientPairRestrictionHom
    {M E : Subgroup G} (hME : M ≤ E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G)) :
    localQuotientPair E hxNE hyNE →*
      localQuotientPair M hxNM hyNM :=
  let fE := pairGeneratedLocalQuotientHom E hxNE hyNE
  let fM := pairGeneratedLocalQuotientHom M hxNM hyNM
  let e := QuotientGroup.quotientKerEquivOfSurjective fE
    (pairGeneratedLocalQuotientHom_surjective E hxNE hyNE)
  (QuotientGroup.lift fE.ker fM (fun _z hz ↦
    MonoidHom.mem_ker.mp
      (pairGeneratedLocalQuotientHom_ker_mono
        hME hxNE hyNE hxNM hyNM hz))).comp e.symm.toMonoidHom

theorem localQuotientPairRestrictionHom_comp
    {M E : Subgroup G} (hME : M ≤ E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G)) :
    (localQuotientPairRestrictionHom hME hxNE hyNE hxNM hyNM).comp
        (pairGeneratedLocalQuotientHom E hxNE hyNE) =
      pairGeneratedLocalQuotientHom M hxNM hyNM := by
  let fE := pairGeneratedLocalQuotientHom E hxNE hyNE
  let fM := pairGeneratedLocalQuotientHom M hxNM hyNM
  let hfE := pairGeneratedLocalQuotientHom_surjective E hxNE hyNE
  let e := QuotientGroup.quotientKerEquivOfSurjective fE hfE
  have hker : fE.ker ≤ fM.ker :=
    pairGeneratedLocalQuotientHom_ker_mono
      hME hxNE hyNE hxNM hyNM
  apply MonoidHom.ext
  intro z
  have he : e.symm (fE z) =
      (z : (pairGenerated x y) ⧸ fE.ker) := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  change QuotientGroup.lift fE.ker fM
    (fun _z hz ↦ MonoidHom.mem_ker.mp (hker hz))
      (e.symm (fE z)) = fM z
  rw [he]
  rfl

theorem localQuotientPairRestrictionHom_surjective
    {M E : Subgroup G} (hME : M ≤ E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G)) :
    Function.Surjective
      (localQuotientPairRestrictionHom hME hxNE hyNE hxNM hyNM) := by
  intro q
  obtain ⟨z, rfl⟩ :=
    pairGeneratedLocalQuotientHom_surjective M hxNM hyNM q
  refine ⟨pairGeneratedLocalQuotientHom E hxNE hyNE z, ?_⟩
  exact DFunLike.congr_fun
    (localQuotientPairRestrictionHom_comp
      hME hxNE hyNE hxNM hyNM) z

/-- The induced restriction map sends the derived subgroup of the larger
local quotient pair onto the derived subgroup of the smaller one. -/
theorem localQuotientPairRestrictionHom_map_commutator
    {M E : Subgroup G} (hME : M ≤ E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G)) :
    (_root_.commutator (localQuotientPair E hxNE hyNE)).map
        (localQuotientPairRestrictionHom hME hxNE hyNE hxNM hyNM) =
      _root_.commutator (localQuotientPair M hxNM hyNM) := by
  let f := localQuotientPairRestrictionHom hME hxNE hyNE hxNM hyNM
  have hf : Function.Surjective f :=
    localQuotientPairRestrictionHom_surjective
      hME hxNE hyNE hxNM hyNM
  rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective f hf]

end Submission.OddOrder.BG.AppendixAB
