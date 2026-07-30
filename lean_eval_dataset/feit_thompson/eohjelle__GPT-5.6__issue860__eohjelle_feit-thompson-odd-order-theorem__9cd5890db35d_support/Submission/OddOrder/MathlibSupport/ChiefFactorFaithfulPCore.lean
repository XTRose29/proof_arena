import Submission.OddOrder.MathlibSupport.ChiefFactor
import Submission.OddOrder.MathlibSupport.SubgroupConjugationFactor
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
Faithfulness of the action on a chief `p`-factor.

This packages the chief-factor action used in Bender--Glauberman,
Theorem 4.19.  The ambient group acts by conjugation on `U / V`; after
dividing by the kernel of that action, the resulting faithful group has
trivial `p`-core when the chief factor is a `p`-group.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative commutatorElement

universe u

variable {G : Type u} [Group G]

/-- The internal quotient `U / (V ∩ U)` is the image of `U` in the
ambient quotient by `V`. -/
private noncomputable def chiefFactorQuotientEquivImage
    {V U : Subgroup G} [V.Normal]
    (_hchief : IsChiefFactor V U) :
    (U ⧸ V.subgroupOf U) ≃*
      U.map (QuotientGroup.mk' V) :=
  QuotientGroup.liftEquiv (V.subgroupOf U)
    ((QuotientGroup.mk' V).subgroupMap_surjective U) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

/-- The conjugation action of the ambient group on the chief factor
`U / V`. -/
noncomputable def chiefFactorConjugationHom
    {V U : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U) :
    G →* MulAut (U ⧸ V.subgroupOf U) := by
  letI : U.Normal := hchief.upper_normal
  exact
    (subgroupConjugationFactorHom V U ⊤
      Subgroup.le_normalizer_of_normal
      Subgroup.le_normalizer_of_normal).comp
      Subgroup.topEquiv.symm.toMonoidHom

@[simp]
theorem chiefFactorConjugationHom_apply_mk
    {V U : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U) (g : G) (u : U) :
    chiefFactorConjugationHom hchief g
        (QuotientGroup.mk' (V.subgroupOf U) u) =
      QuotientGroup.mk' (V.subgroupOf U)
        ⟨g * (u : G) * g⁻¹,
          ((hchief.upper_normal : U.Normal).conj_mem
            u u.property g)⟩ := by
  rfl

/-- The faithful action obtained after quotienting by the action kernel. -/
private noncomputable def quotientKerChiefFactorConjugationHom
    {V U : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U) :
    (G ⧸ (chiefFactorConjugationHom hchief).ker) →*
      MulAut (U ⧸ V.subgroupOf U) :=
  QuotientGroup.lift (chiefFactorConjugationHom hchief).ker
    (chiefFactorConjugationHom hchief) le_rfl

private theorem quotientKerChiefFactorConjugationHom_injective
    {V U : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U) :
    Function.Injective (quotientKerChiefFactorConjugationHom hchief) := by
  apply (QuotientGroup.injective_lift_iff
    (chiefFactorConjugationHom hchief).ker
    (chiefFactorConjugationHom hchief) _).mpr
  rfl

/-- A faithful quotient acting on a chief `p`-factor has trivial `p`-core.

The `p`-core has a nonidentity fixed point on the factor by the orbit-counting
lemma for `p`-groups.  Its fixed subgroup is normal under the full quotient
action, so chief minimality makes that subgroup the whole factor.  Faithfulness
then kills the `p`-core. -/
theorem pCore_quotient_ker_chiefFactorConjugationHom_eq_bot
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {V U : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U)
    (hfactor : IsPGroup p
      (U.map (QuotientGroup.mk' V))) :
    pCore p
      (G ⧸ (chiefFactorConjugationHom hchief).ker) = ⊥ := by
  classical
  let P := U ⧸ V.subgroupOf U
  let rho := chiefFactorConjugationHom hchief
  let Q := G ⧸ rho.ker
  let rhoQ : Q →* MulAut P :=
    QuotientGroup.lift rho.ker rho le_rfl
  letI : MulDistribMulAction Q P :=
    MulDistribMulAction.compHom P rhoQ
  let R : Subgroup Q := pCore p Q
  let C : Subgroup P := FixedPoints.subgroup R P
  let qV : G →* G ⧸ V := QuotientGroup.mk' V
  let M : Subgroup (G ⧸ V) := U.map qV
  let e : P ≃* M := chiefFactorQuotientEquivImage hchief
  have hP : IsPGroup p P := hfactor.of_equiv e.symm
  let f : P →* G ⧸ V := M.subtype.comp e.toMonoidHom
  have hf_smul (g : G) (x : P) :
      f ((QuotientGroup.mk' rho.ker g : Q) • x) =
        qV g * f x * (qV g)⁻¹ := by
    obtain ⟨u, rfl⟩ :=
      QuotientGroup.mk'_surjective (V.subgroupOf U) x
    change qV (g * (u : G) * g⁻¹) =
      qV g * qV (u : G) * (qV g)⁻¹
    simp
  let W : Subgroup (G ⧸ V) := C.map f
  have hWnormal : W.Normal := by
    constructor
    intro x hx z
    obtain ⟨c, hcC, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V z
    have hcfix : c ∈ MulAction.fixedPoints R P := hcC
    have hc'fix :
        (QuotientGroup.mk' rho.ker g : Q) • c ∈
          MulAction.fixedPoints R P :=
      smul_mem_fixedPoints_of_normal _ hcfix
    have hc'C :
        (QuotientGroup.mk' rho.ker g : Q) • c ∈ C := hc'fix
    refine ⟨(QuotientGroup.mk' rho.ker g : Q) • c, hc'C, ?_⟩
    exact hf_smul g c
  have hWle : W ≤ M := by
    intro x hx
    obtain ⟨c, _hc, rfl⟩ := hx
    exact (e c).property
  have hWnon : W ≠ ⊥ := by
    letI : Nontrivial P := QuotientGroup.nontrivial_iff.mpr (by
      intro htop
      exact (not_le_of_gt hchief.lt)
        (Subgroup.subgroupOf_eq_top.mp htop))
    have hpP : p ∣ Nat.card P :=
      hP.card_eq_or_dvd.resolve_left
        (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne'
    have honefix : (1 : P) ∈ MulAction.fixedPoints R P := by simp
    obtain ⟨c, hcfix, hcne⟩ :=
      (pCore_isPGroup (p := p) (G := Q)).exists_fixed_point_of_prime_dvd_card_of_fixed_point
          P hpP honefix
    have hcC : c ∈ C := hcfix
    intro hW
    have hfc : f c = 1 := by
      have : f c ∈ W := ⟨c, hcC, rfl⟩
      rw [hW] at this
      exact Subgroup.mem_bot.mp this
    have hc1 : c = 1 := by
      apply e.injective
      apply Subtype.ext
      exact hfc
    exact hcne hc1.symm
  have hWM : W = M :=
    hchief.quotient_minimal_normal.eq_of_normal_le
      hWnormal hWle hWnon
  have hCtop : C = ⊤ := by
    apply (Subgroup.eq_top_iff' C).mpr
    intro c
    have hfcM : f c ∈ M := (e c).property
    rw [← hWM] at hfcM
    obtain ⟨d, hdC, hfd⟩ := hfcM
    have hdc : d = c := by
      apply e.injective
      apply Subtype.ext
      exact hfd
    simpa [hdc] using hdC
  apply (Subgroup.eq_bot_iff_forall R).mpr
  intro r hr
  apply quotientKerChiefFactorConjugationHom_injective hchief
  apply MulEquiv.ext
  intro x
  have hxC : x ∈ C := by rw [hCtop]; trivial
  have hxfix := (FixedPoints.mem_subgroup R P x).mp hxC ⟨r, hr⟩
  change rhoQ r x = x at hxfix
  change rhoQ r x = rhoQ 1 x
  simpa using hxfix

@[simp]
private theorem mem_ker_chiefFactorConjugationHom_iff
    {V U : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U) (g : G) :
    g ∈ (chiefFactorConjugationHom hchief).ker ↔
      ∀ u : G, u ∈ U → ⁅g, u⁆ ∈ V := by
  letI : U.Normal := hchief.upper_normal
  exact mem_ker_subgroupConjugationFactorHom_iff
    V U ⊤ Subgroup.le_normalizer_of_normal
      Subgroup.le_normalizer_of_normal ⟨g, trivial⟩

/-- The derived subgroup acts trivially on a chief factor exactly when it
centralizes the upper term modulo the lower term. -/
theorem commutator_le_ker_chiefFactorConjugationHom_iff
    {V U : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U) :
    _root_.commutator G ≤
        (chiefFactorConjugationHom hchief).ker ↔
      ⁅(_root_.commutator G), U⁆ ≤ V := by
  constructor
  · intro hker
    apply Subgroup.commutator_le.mpr
    intro g hg u hu
    exact (mem_ker_chiefFactorConjugationHom_iff hchief g).mp
      (hker hg) u hu
  · intro hcomm g hg
    apply (mem_ker_chiefFactorConjugationHom_iff hchief g).mpr
    intro u hu
    exact Subgroup.commutator_le.mp hcomm g hg u hu

end Submission.OddOrder.MathlibSupport
