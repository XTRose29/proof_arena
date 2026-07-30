import Submission.OddOrder.MathlibSupport.ClassTwoQuotientCommutatorPairing
import Submission.OddOrder.PF.Section11.FTType34BoundsCore

/-!
# Peterfalvi Section 11: triviality of the type III/IV F-core kernel

This final module proves Peterfalvi (11.7).  The context, character layers,
bounds, second-derived identification, and group facts from (11.1)--(11.6)
are provided by `FTType34BoundsCore`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section06
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {M U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) ftType34BoundsFintypeOfFinite
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

private noncomputable abbrev ftType34FactorFactsFinal
    (base : FTType34Base M U W W₁ W₂ defW) :
    PTypeFCoreFactorFacts base.ptypeCtx :=
  Ptype_Fcore_factor_facts base.ptypeCtx

/-- The factor Frobenius input used in the proof of (11.7). -/
structure FTType34ComplementFactorFrobenius
    (base : FTType34Base M U W W₁ W₂ defW) : Prop where
  complement_frobenius : PTypeFrobeniusProduct U W₁
  kernel_eq_derived : base.C = base.U'

/-- Source local fact `frobUW1bar`. -/
theorem frobUW1bar
    (base : FTType34Base M U W W₁ W₂ defW) :
    FTType34ComplementFactorFrobenius base :=
  { complement_frobenius := Ptype_compl_Frobenius base.ptypeCtx
    kernel_eq_derived := (FTtype34_facts base).C_eq_derived_U }

/-! ## Peterfalvi (11.7) -/

/-- The three clauses of Peterfalvi (11.7). -/
structure FTType34FCoreKernelTrivial
    (base : FTType34Base M U W W₁ W₂ defW) : Prop where
  H_elementaryAbelian : IsElementaryAbelianGroup base.p base.H
  card_H_eq : Nat.card base.H = base.p ^ base.q
  H0_eq_bot : base.H0 = ⊥

private noncomputable abbrev ftType34ActionData
    (base : FTType34Base M U W W₁ W₂ defW) :=
  Ptype_factor_action base.ptypeCtx (ftType34FactorFactsFinal base)

private theorem even_finrank_of_nondegenerate_alternating34
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {V : Type} [AddCommGroup V] [Finite V] [Module (ZMod p) V]
    (B : LinearMap.BilinForm (ZMod p) V) (hB : B.IsAlt)
    (hBnondegenerate : B.Nondegenerate) :
    Even (Module.finrank (ZMod p) V) := by
  classical
  letI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let b := Module.finBasis (ZMod p) V
  let A := LinearMap.BilinForm.toMatrix b B
  have hdet : A.det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hBnondegenerate
  by_contra hneven
  have hodd : Odd (Module.finrank (ZMod p) V) :=
    Nat.not_even_iff_odd.mp hneven
  have htranspose : A.transpose = -A := by
    ext i j
    simpa only [A, Matrix.transpose_apply, LinearMap.BilinForm.toMatrix_apply,
      Matrix.neg_apply] using (hB.neg_eq (b i) (b j)).symm
  have hdet_neg : A.det = -A.det := by
    calc
      A.det = A.transpose.det := (Matrix.det_transpose A).symm
      _ = (-A).det := congrArg Matrix.det htranspose
      _ = (-1) ^ Fintype.card (Fin (Module.finrank (ZMod p) V)) * A.det :=
        Matrix.det_neg A
      _ = -A.det := by
        rw [Fintype.card_fin, hodd.neg_one_pow, neg_one_mul]
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro htwozero
    have hpTwo : p ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 p).mp htwozero
    rcases (Nat.dvd_prime Nat.prime_two).mp hpTwo with hpOne | hpTwoEq
    · exact (Fact.out : p.Prime).ne_one hpOne
    · subst p
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  have hzero : (2 : ZMod p) * A.det = 0 := by
    calc
      (2 : ZMod p) * A.det = A.det + A.det := two_mul A.det
      _ = -A.det + A.det :=
        congrArg (fun x : ZMod p ↦ x + A.det) hdet_neg
      _ = 0 := neg_add_cancel A.det
  rcases mul_eq_zero.mp hzero with htwozero | hdetzero
  · exact htwo htwozero
  · exact hdet hdetzero

private theorem extraspecial_quotient_exponent_even34
    {P : Type} [Group P] [Finite P]
    {p n : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (hpP : IsPGroup p P) (hP : IsExtraspecial P)
    (hcard : Nat.card (P ⧸ Subgroup.center P) = p ^ n) : Even n := by
  letI : CommGroup (P ⧸ Subgroup.center P) :=
    hP.toIsSpecial.quotientCenterCommGroup
  letI : CommGroup (Subgroup.center P) := centerCommGroup
  letI quotientModule : Module (ZMod p)
      (Additive (P ⧸ Subgroup.center P)) :=
    hP.quotientCenterZModModule hpP
  letI quotientFree : Module.Free (ZMod p)
      (Additive (P ⧸ Subgroup.center P)) :=
    @Module.Free.of_divisionRing
      (ZMod p) (Additive (P ⧸ Subgroup.center P))
      inferInstance inferInstance quotientModule
  letI quotientFinite : Module.Finite (ZMod p)
      (Additive (P ⧸ Subgroup.center P)) :=
    @Module.Finite.of_finite
      (ZMod p) (Additive (P ⧸ Subgroup.center P))
      inferInstance inferInstance quotientModule inferInstance
  letI centerModule : Module (ZMod p) (Additive (Subgroup.center P)) :=
    hP.centerZModModule hpP
  letI centerFree : Module.Free (ZMod p)
      (Additive (Subgroup.center P)) :=
    @Module.Free.of_divisionRing
      (ZMod p) (Additive (Subgroup.center P))
      inferInstance inferInstance centerModule
  letI centerSmulComm : SMulCommClass (ZMod p) (ZMod p)
      (Additive (Subgroup.center P)) :=
    inferInstance
  letI dualAddCommMonoid : AddCommMonoid
      (Additive (P ⧸ Subgroup.center P) →ₗ[ZMod p]
        Additive (Subgroup.center P)) :=
    @LinearMap.addCommMonoid
      (ZMod p) (ZMod p)
      (Additive (P ⧸ Subgroup.center P))
      (Additive (Subgroup.center P))
      inferInstance inferInstance inferInstance inferInstance
      quotientModule centerModule (RingHom.id (ZMod p))
  letI dualModule : @Module (ZMod p)
      (Additive (P ⧸ Subgroup.center P) →ₗ[ZMod p]
        Additive (Subgroup.center P)) inferInstance dualAddCommMonoid :=
    @LinearMap.module
      (ZMod p) (ZMod p) (ZMod p)
      (Additive (P ⧸ Subgroup.center P))
      (Additive (Subgroup.center P))
      inferInstance inferInstance inferInstance inferInstance
      quotientModule centerModule (RingHom.id (ZMod p))
      inferInstance centerModule centerSmulComm
  letI centerFinite : Module.Finite (ZMod p)
      (Additive (Subgroup.center P)) :=
    @Module.Finite.of_finite
      (ZMod p) (Additive (Subgroup.center P))
      inferInstance inferInstance centerModule inferInstance
  let c : Additive (Subgroup.center P) ≃ₗ[ZMod p] ZMod p :=
    @LinearEquiv.ofFinrankEq
      (ZMod p) (Additive (Subgroup.center P)) (ZMod p)
      inferInstance inferInstance centerModule
      centerFree inferInstance inferInstance inferInstance inferInstance
      centerFinite inferInstance (by
        simpa using hP.center_finrank_eq_one hpP)
  let b₀ : @LinearMap
      (ZMod p) (ZMod p) inferInstance inferInstance
      (RingHom.id (ZMod p))
      (Additive (P ⧸ Subgroup.center P))
      (Additive (P ⧸ Subgroup.center P) →ₗ[ZMod p]
        Additive (Subgroup.center P))
      inferInstance dualAddCommMonoid quotientModule dualModule :=
    hP.toIsSpecial.quotientCommutatorLinearMap (p := p)
  let b : LinearMap.BilinForm (ZMod p)
      (Additive (P ⧸ Subgroup.center P)) :=
    b₀.compr₂ c.toLinearMap
  have hbAlt : b.IsAlt := by
    intro x
    have hself : Additive.ofMul
        (hP.toIsSpecial.quotientCommutatorPairing x.toMul x.toMul) = 0 := by
      apply Additive.toMul.injective
      simpa only [toMul_ofMul, toMul_zero] using
        hP.toIsSpecial.quotientCommutatorPairing_self x.toMul
    change c.toLinearMap.toFun (Additive.ofMul
      (hP.toIsSpecial.quotientCommutatorPairing x.toMul x.toMul)) = 0
    rw [hself]
    exact c.toLinearMap.map_zero
  have hbSeparating : b.SeparatingLeft := by
    intro x hx
    apply Additive.toMul.injective
    rw [toMul_zero]
    apply hP.toIsSpecial.quotientCommutatorPairing_nondegenerate x.toMul
    intro y
    have hxy := hx (Additive.ofMul y)
    change c.toLinearMap.toFun (Additive.ofMul
      (hP.toIsSpecial.quotientCommutatorPairing x.toMul y)) = 0 at hxy
    have hcenter : Additive.ofMul
        (hP.toIsSpecial.quotientCommutatorPairing x.toMul y) = 0 := by
      apply c.injective
      exact hxy.trans c.toLinearMap.map_zero.symm
    simpa only [toMul_ofMul, toMul_zero] using
      congrArg Additive.toMul hcenter
  have hbNondegenerate : b.Nondegenerate :=
    @LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
      (ZMod p) (Additive (P ⧸ Subgroup.center P))
      inferInstance inferInstance quotientModule inferInstance
      quotientFree quotientFinite b hbSeparating
  have hfinrank :
      Module.finrank (ZMod p)
          (Additive (P ⧸ Subgroup.center P)) = n := by
    apply zmod_finrank_eq_of_natCard
    calc
      Nat.card (Additive (P ⧸ Subgroup.center P)) =
          Nat.card (P ⧸ Subgroup.center P) :=
        Nat.card_congr Additive.ofMul
      _ = p ^ n := hcard
  rw [← hfinrank]
  exact even_finrank_of_nondegenerate_alternating34
    hpodd b hbAlt hbNondegenerate

private theorem ftType34_not_Galois_of_kernel_ne_bot
    (base : FTType34Base M U W W₁ W₂ defW)
    (hH0 : base.H0 ≠ ⊥) :
    ¬ typeP_Galois
      (Ptype_factor_action base.ptypeCtx
        (ftType34FactorFactsFinal base)) := by
  classical
  let facts := FTtype34_facts base
  let factorFacts := ftType34FactorFactsFinal base
  letI : Fact base.p.Prime := ⟨base.p_prime⟩
  let D : Subgroup base.H := _root_.commutator base.H
  letI : D.Normal := by
    dsimp [D]
    infer_instance
  have hH0D : base.H0.subgroupOf base.H = D := by
    dsimp [D]
    apply Subgroup.map_injective base.H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le base.H0_le_H,
      base.H.map_subtype_commutator]
    simpa only [derivedWithin, base.H.map_subtype_commutator] using
      facts.H0_eq_derived_H
  have hDne : D ≠ ⊥ := by
    intro hDbot
    apply hH0
    apply le_antisymm
    · intro x hx
      have hxD :
          (⟨x, base.H0_le_H hx⟩ : base.H) ∈ D := by
        rw [← hH0D]
        exact hx
      rw [hDbot] at hxD
      exact Subgroup.mem_bot.mpr
        (congrArg Subtype.val (Subgroup.mem_bot.mp hxD))
    · exact bot_le
  let Good : Subgroup base.H → Prop :=
    fun Q ↦ Q.Normal ∧ Q < D
  have hbotGood : Good (⊥ : Subgroup base.H) :=
    ⟨by infer_instance, bot_lt_iff_ne_bot.mpr hDne⟩
  letI : Finite (Subgroup base.H) :=
    Finite.of_injective (fun Q : Subgroup base.H ↦ (Q : Set base.H))
      SetLike.coe_injective
  obtain ⟨Q, _hbotQ, hQgood, hQmax⟩ :=
    Finite.exists_le_maximal (p := Good) hbotGood
  letI : Q.Normal := hQgood.1
  let S := base.H ⧸ Q
  let qH : base.H →* S := QuotientGroup.mk' Q
  have hqHker : qH.ker = Q := by
    change (QuotientGroup.mk' Q).ker = Q
    exact QuotientGroup.ker_mk' Q
  let Dbar : Subgroup S := D.map qH
  letI : Dbar.Normal := by
    dsimp [Dbar]
    exact Subgroup.Normal.map (inferInstance : D.Normal) qH
      (QuotientGroup.mk'_surjective Q)
  have hDbarNe : Dbar ≠ ⊥ := by
    intro hDbarBot
    have hDleQ : D ≤ Q := by
      have hker := (Subgroup.map_eq_bot_iff D).mp hDbarBot
      rw [hqHker] at hker
      exact hker
    exact (not_le_of_gt hQgood.2) hDleQ
  have hDbarMinimal : IsMinimalNormal Dbar := by
    refine ⟨hDbarNe, inferInstance, ?_⟩
    intro N hNnormal hNDbar hNne
    let R : Subgroup base.H := N.comap qH
    have hRnormal : R.Normal := by
      dsimp [R]
      exact Subgroup.Normal.comap hNnormal qH
    have hQR : Q ≤ R := by
      dsimp [R, qH]
      exact QuotientGroup.le_comap_mk' Q N
    have hkerD : qH.ker ≤ D := by
      rw [hqHker]
      exact hQgood.2.le
    have hcomapD : Dbar.comap qH = D := by
      dsimp [Dbar]
      exact Subgroup.comap_map_eq_self hkerD
    have hRD : R ≤ D := by
      calc
        R ≤ Dbar.comap qH := Subgroup.comap_mono hNDbar
        _ = D := hcomapD
    have hRneQ : R ≠ Q := by
      intro hRQ
      apply hNne
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective Q)
      simpa only [R, qH, MonoidHom.comap_bot,
        QuotientGroup.ker_mk'] using hRQ
    have hReqD : R = D := by
      by_contra hRDne
      have hRltD : R < D := lt_of_le_of_ne hRD hRDne
      have hRgood : Good R := ⟨hRnormal, hRltD⟩
      have hRQ : R ≤ Q := hQmax hRgood hQR
      exact hRneQ (le_antisymm hRQ hQR)
    dsimp [Dbar]
    apply Subgroup.map_le_iff_le_comap.mpr
    change D ≤ R
    exact hReqD.symm.le
  have hpS : IsPGroup base.p S := facts.H_isPGroup.to_quotient Q
  have hDbarMeetCenter :
      Dbar ⊓ Subgroup.center S ≠ ⊥ :=
    normal_inf_center_ne_bot hpS Dbar hDbarNe
  have hDbarMeetEq : Dbar ⊓ Subgroup.center S = Dbar :=
    hDbarMinimal.eq_of_normal_le (by infer_instance)
      inf_le_left hDbarMeetCenter
  have hcentral : Dbar ≤ Subgroup.center S := by
    intro x hx
    have hxMeet : x ∈ Dbar ⊓ Subgroup.center S := by
      rw [hDbarMeetEq]
      exact hx
    exact hxMeet.2
  have hpDbar : IsPGroup base.p Dbar := hpS.to_subgroup Dbar
  have hpDbarCard : base.p ∣ Nat.card Dbar :=
    hpDbar.card_eq_or_dvd.resolve_left
      (Dbar.one_lt_card_iff_ne_bot.mpr hDbarNe).ne'
  obtain ⟨z, hz⟩ :=
    exists_prime_orderOf_dvd_card' (G := Dbar) base.p hpDbarCard
  let zS : S := z
  have hzS : orderOf zS = base.p :=
    (Subgroup.orderOf_coe z).trans hz
  let E : Subgroup S := Subgroup.zpowers zS
  have hEcard : Nat.card E = base.p := by
    rw [Nat.card_zpowers, hzS]
  have hEDbar : E ≤ Dbar := by
    apply Subgroup.zpowers_le.mpr
    exact z.property
  have hEcenter : E ≤ Subgroup.center S := hEDbar.trans hcentral
  letI : E.Normal := ⟨fun a ha b ↦ by
    simpa [Subgroup.mem_center_iff.mp (hEcenter ha) b] using ha⟩
  have hEne : E ≠ ⊥ := by
    apply E.one_lt_card_iff_ne_bot.mp
    rw [hEcard]
    exact base.p_prime.one_lt
  have hEDbarEq : E = Dbar :=
    hDbarMinimal.eq_of_normal_le (by infer_instance) hEDbar hEne
  have hDbarCard : Nat.card Dbar = base.p := by
    rw [← hEDbarEq, hEcard]
  letI : IsMulCommutative Dbar :=
    ⟨⟨fun a b ↦ Subtype.ext
      (Subgroup.mem_center_iff.mp (hcentral a.property) b).symm⟩⟩
  let pairing := classTwoQuotientCommutatorPairing
    Q hQgood.2.le hcentral
  let radical : Subgroup (base.H ⧸ D) := pairing.ker
  have mem_radical_iff (x : base.H) :
      QuotientGroup.mk' D x ∈ radical ↔
        ∀ y : base.H, qH ⁅x, y⁆ = 1 := by
    constructor
    · intro hx y
      have hxy := congrArg
        (fun f : (base.H ⧸ D) →* Dbar ↦
          f (QuotientGroup.mk' D y))
        (MonoidHom.mem_ker.mp hx)
      have hxyVal := congrArg Subtype.val hxy
      have hpair :
          (((pairing (QuotientGroup.mk' D x))
              (QuotientGroup.mk' D y) : Dbar) : S) =
            qH ⁅x, y⁆ := by
        simpa only [pairing, D, qH] using
          classTwoQuotientCommutatorPairing_mk_mk
            Q hQgood.2.le hcentral x y
      exact hpair.symm.trans hxyVal
    · intro hx
      change pairing (QuotientGroup.mk' D x) = 1
      apply QuotientGroup.monoidHom_ext
      ext y
      change qH ⁅x, y⁆ = 1
      exact hx y
  have hradicalNeTop : radical ≠ ⊤ := by
    intro hradicalTop
    have hDleQ : D ≤ Q := by
      dsimp [D]
      apply Subgroup.commutator_le.mpr
      intro x _hx y _hy
      have hxradical : QuotientGroup.mk' D x ∈ radical := by
        rw [hradicalTop]
        exact Subgroup.mem_top _
      exact (QuotientGroup.eq_one_iff ⁅x, y⁆).mp
        ((mem_radical_iff x).mp hxradical y)
    exact (not_le_of_gt hQgood.2) hDleQ
  let e : (base.H ⧸ D) ≃* ptypeFCoreFactor base.ptypeCtx :=
    QuotientGroup.quotientMulEquivOfEq hH0D.symm
  have e_mk (x : base.H) :
      e (QuotientGroup.mk' D x) =
        QuotientGroup.mk' (base.H0.subgroupOf base.H) x :=
    QuotientGroup.quotientMulEquivOfEq_mk hH0D.symm x
  let radicalBar : Subgroup (ptypeFCoreFactor base.ptypeCtx) :=
    radical.map e.toMonoidHom
  have hradicalBarNeTop : radicalBar ≠ ⊤ := by
    intro htop
    apply hradicalNeTop
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa [radicalBar] using htop
  have hUnormH : U ≤ Subgroup.normalizer (base.H : Set G) :=
    (base.U_le_HU.trans base.HU_le_M).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M))
  let cH (u : U) (x : base.H) : base.H :=
    ⟨(u : G) * (x : G) * (u : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hUnormH u.property) x).mp
        x.property⟩
  have hcommConj (u : U) (x y : base.H) :
      ⁅cH u x, y⁆ = ⁅x, cH u⁻¹ y⁆ := by
    apply Subtype.ext
    change base.H.subtype ⁅cH u x, y⁆ =
      base.H.subtype ⁅x, cH u⁻¹ y⁆
    rw [map_commutatorElement, map_commutatorElement]
    dsimp only [cH]
    simp only [Subgroup.coe_subtype, Subgroup.coe_inv, inv_inv]
    let c : G := ⁅(x : G), (u : G)⁻¹ * (y : G) * (u : G)⁆
    have hcH0 : c ∈ base.H0 := by
      rw [facts.H0_eq_derived_H]
      change c ∈ (_root_.commutator base.H).map base.H.subtype
      refine ⟨⁅x, cH u⁻¹ y⁆,
        Subgroup.commutator_mem_commutator trivial trivial, ?_⟩
      simp [c, cH]
    have hcu : c * (u : G) = (u : G) * c :=
      Subgroup.mem_centralizer_iff.mp
        (facts.U_le_centralizer_H0 u.property) c hcH0
    calc
      ⁅(u : G) * (x : G) * (u : G)⁻¹, (y : G)⁆ =
          (u : G) * c * (u : G)⁻¹ := by
        dsimp [c]
        simp only [commutatorElement_def]
        group
      _ = c := by rw [← hcu]; group
      _ = ⁅(x : G), (u : G)⁻¹ * (y : G) * (u : G)⁆ := rfl
  have hradicalConj (u : U) (x : base.H)
      (hx : QuotientGroup.mk' D x ∈ radical) :
      QuotientGroup.mk' D (cH u x) ∈ radical := by
    apply (mem_radical_iff (cH u x)).mpr
    intro y
    rw [hcommConj]
    exact (mem_radical_iff x).mp hx (cH u⁻¹ y)
  have haction (u : U) (x : base.H) :
      (Ptype_factor_action base.ptypeCtx factorFacts).U_action u
          (e (QuotientGroup.mk' D x)) =
        e (QuotientGroup.mk' D (cH u x)) := by
    change ptypeFCoreAction base.ptypeCtx u
        (e (QuotientGroup.mk' D x)) =
      e (QuotientGroup.mk' D (cH u x))
    rw [e_mk x, e_mk (cH u x)]
    rw [ptypeFCoreAction, subgroupConjugationFactorHom_apply_mk]
  have hradicalBarMem (u : U) {z : ptypeFCoreFactor base.ptypeCtx}
      (hz : z ∈ radicalBar) :
      (Ptype_factor_action base.ptypeCtx factorFacts).U_action u z ∈
        radicalBar := by
    rcases hz with ⟨x, hx, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D x
    refine ⟨QuotientGroup.mk' D (cH u x),
      hradicalConj u x hx, ?_⟩
    exact (haction u x).symm
  have hradicalBarInvariant :
      IsInvariantSubgroup
        (Ptype_factor_action base.ptypeCtx factorFacts).U_action
        radicalBar := by
    intro u
    apply le_antisymm
    · rintro z ⟨x, hx, rfl⟩
      exact hradicalBarMem u hx
    · intro z hz
      refine ⟨(Ptype_factor_action base.ptypeCtx factorFacts).U_action
          u⁻¹ z, hradicalBarMem u⁻¹ hz, ?_⟩
      simp
  intro hGalois
  have hradicalBarBot : radicalBar = ⊥ := by
    rcases hGalois.2 radicalBar hradicalBarInvariant with hbot | htop
    · exact hbot
    · exact (hradicalBarNeTop htop).elim
  have hradicalBot : radical = ⊥ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa [radicalBar, hradicalBarBot]
  have hDbarCommutator : Dbar = _root_.commutator S := by
    calc
      Dbar = ⁅qH.range, qH.range⁆ := map_commutator_eq base.H qH
      _ = ⁅(⊤ : Subgroup S), ⊤⁆ := by
        rw [MonoidHom.range_eq_top.mpr
          (QuotientGroup.mk'_surjective Q)]
      _ = _root_.commutator S := rfl
  have hcenterLeDbar : Subgroup.center S ≤ Dbar := by
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q z
    have hxradical : QuotientGroup.mk' D x ∈ radical := by
      apply (mem_radical_iff x).mpr
      intro y
      rw [map_commutatorElement]
      apply commutatorElement_eq_one_iff_commute.mpr
      exact (Subgroup.mem_center_iff.mp hz (qH y)).symm
    rw [hradicalBot] at hxradical
    have hxone : QuotientGroup.mk' D x = 1 :=
      Subgroup.mem_bot.mp hxradical
    have hxD : x ∈ D := (QuotientGroup.eq_one_iff x).mp hxone
    exact ⟨x, hxD, rfl⟩
  have hcenterEq : Subgroup.center S = Dbar :=
    le_antisymm hcenterLeDbar hcentral
  have hcommutatorCenter :
      _root_.commutator S = Subgroup.center S :=
    hDbarCommutator.symm.trans hcenterEq.symm
  let eCenter :
      (S ⧸ Subgroup.center S) ≃*
        ptypeFCoreFactor base.ptypeCtx :=
    (QuotientGroup.quotientMulEquivOfEq hcenterEq).trans
      ((QuotientGroup.quotientQuotientEquivQuotient
        Q D hQgood.2.le).trans e)
  letI : IsMulCommutative (S ⧸ Subgroup.center S) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      hcommutatorCenter.le
  have hpowCenterQuotient (x : S ⧸ Subgroup.center S) :
      x ^ base.p = 1 := by
    apply eCenter.injective
    simpa using
      (FTType34BoundsCoreInternal.factor_elementary base).pow_eq_one
        (eCenter x)
  have hfrattiniCenterQuotient :
      frattini (S ⧸ Subgroup.center S) = ⊥ :=
    IsPGroup.frattini_eq_bot_of_isMulCommutative_of_pow_prime
      hpowCenterQuotient
  have hfrattiniLeCenter : frattini S ≤ Subgroup.center S := by
    have hle := frattini_le_comap_frattini_of_surjective
      (φ := QuotientGroup.mk' (Subgroup.center S))
      (QuotientGroup.mk'_surjective (Subgroup.center S))
    rw [hfrattiniCenterQuotient, MonoidHom.comap_bot,
      QuotientGroup.ker_mk'] at hle
    exact hle
  have hcenterLeFrattini : Subgroup.center S ≤ frattini S := by
    rw [← hcommutatorCenter]
    exact IsPGroup.commutator_le_frattini hpS
  have hspecial : IsSpecial S :=
    { frattini_eq_center :=
        le_antisymm hfrattiniLeCenter hcenterLeFrattini
      commutator_eq_center := hcommutatorCenter }
  have hextraspecial : IsExtraspecial S :=
    { toIsSpecial := hspecial
      center_card_prime := by
        rw [hcenterEq, hDbarCard]
        exact base.p_prime }
  have hcenterQuotientCard :
      Nat.card (S ⧸ Subgroup.center S) = base.p ^ base.q := by
    calc
      Nat.card (S ⧸ Subgroup.center S) =
          Nat.card (ptypeFCoreFactor base.ptypeCtx) :=
        Nat.card_congr eCenter.toEquiv
      _ = base.p ^ base.q :=
        FTType34BoundsCoreInternal.factor_card base
  have heven : Even base.q :=
    extraspecial_quotient_exponent_even34 base.p_odd hpS
      hextraspecial hcenterQuotientCard
  exact (Nat.not_even_iff_odd.mpr base.q_odd) heven

private theorem ftType34_nonGalois_kernel_impossible
    (base : FTType34Base M U W W₁ W₂ defW)
    (hH0 : base.H0 ≠ ⊥)
    (hnotGalois : ¬ typeP_Galois (ftType34ActionData base)) : False := by
  classical
  let facts := Ptype_Fcore_factor_facts base.ptypeCtx
  let D := Ptype_factor_action base.ptypeCtx facts
  let hD := Ptype_factor_action_hypotheses base.ptypeCtx facts
  let data := typeP_Galois_Pn hD (by
    simpa only [D, facts, ftType34ActionData,
      ftType34FactorFactsFinal] using hnotGalois)
  let H := base.H
  let N : Subgroup H := base.H0.subgroupOf H
  have hNne : N ≠ ⊥ := by
    intro hN
    apply hH0
    calc
      base.H0 = N.map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le base.H0_le_H).symm
      _ = ⊥ := by rw [hN]; simp
  have hNder : N = _root_.commutator H := by
    change base.H0.subgroupOf base.H = _root_.commutator base.H
    rw [(FTtype34_facts base).H0_eq_derived_H]
    change
      ((_root_.commutator base.H).map base.H.subtype).comap
          base.H.subtype = _root_.commutator base.H
    exact Subgroup.comap_map_eq_self_of_injective
      base.H.subtype_injective (_root_.commutator base.H)
  letI : N.Normal := by
    rw [hNder]
    infer_instance
  let Good : Subgroup H → Prop := fun Q ↦ Q.Normal ∧ Q < N
  have hbotGood : Good (⊥ : Subgroup H) :=
    ⟨by infer_instance, bot_lt_iff_ne_bot.mpr hNne⟩
  letI : Finite (Subgroup H) :=
    Finite.of_injective (fun L : Subgroup H ↦ (L : Set H))
      SetLike.coe_injective
  obtain ⟨Q, _hbotQ, hQgood, hQmax⟩ :=
    Finite.exists_le_maximal (p := Good) hbotGood
  letI : Q.Normal := hQgood.1
  have hQN : Q ≤ N := hQgood.2.le
  have hQder : Q ≤ _root_.commutator H := hQN.trans_eq hNder
  let qQ : H →* H ⧸ Q := QuotientGroup.mk' Q
  let Nq : Subgroup (H ⧸ Q) := N.map qQ
  have hNqNormal : Nq.Normal := by
    dsimp only [Nq, qQ]
    exact Subgroup.Normal.map (inferInstance : N.Normal)
      (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
  letI : Nq.Normal := hNqNormal
  have hNqne : Nq ≠ ⊥ := by
    intro hNq
    have hNQ : N ≤ Q := by
      have hker := (Subgroup.map_eq_bot_iff N).mp hNq
      simpa only [Nq, qQ, QuotientGroup.ker_mk'] using hker
    exact (not_le_of_gt hQgood.2) hNQ
  have hNqMinimal : IsMinimalNormal Nq := by
    refine ⟨hNqne, hNqNormal, ?_⟩
    intro K hKnormal hKNq hKne
    let L : Subgroup H := K.comap qQ
    have hLnormal : L.Normal := by
      dsimp only [L]
      exact Subgroup.Normal.comap hKnormal qQ
    have hQL : Q ≤ L := by
      dsimp only [L, qQ]
      exact QuotientGroup.le_comap_mk' Q K
    have hLN : L ≤ N := by
      calc
        L ≤ (N.map qQ).comap qQ := Subgroup.comap_mono hKNq
        _ = N := Subgroup.comap_map_eq_self (by
          simpa only [qQ, QuotientGroup.ker_mk'] using hQN)
    by_cases hLeqN : L = N
    · exact Subgroup.map_le_iff_le_comap.mpr hLeqN.symm.le
    · have hLltN : L < N := lt_of_le_of_ne hLN hLeqN
      have hLQ : L ≤ Q := hQmax ⟨hLnormal, hLltN⟩ hQL
      have hLQeq : L = Q := le_antisymm hLQ hQL
      exfalso
      apply hKne
      calc
        K = L.map qQ :=
          (Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective Q) K).symm
        _ = Q.map qQ := by rw [hLQeq]
        _ = ⊥ := QuotientGroup.map_mk'_self Q
  letI : Fact base.p.Prime := ⟨base.p_prime⟩
  have hHqP : IsPGroup base.p (H ⧸ Q) :=
    (FTtype34_facts base).H_isPGroup.to_quotient Q
  let Cq : Subgroup (H ⧸ Q) := Nq ⊓ Subgroup.center (H ⧸ Q)
  letI : Cq.Normal := by
    dsimp only [Cq]
    infer_instance
  have hCqne : Cq ≠ ⊥ := by
    dsimp only [Cq]
    exact normal_inf_center_ne_bot hHqP Nq hNqne
  have hCqNq : Cq = Nq :=
    hNqMinimal.eq_of_normal_le (inferInstance : Cq.Normal) inf_le_left hCqne
  have hcentral :
      (_root_.commutator H).map qQ ≤ Subgroup.center (H ⧸ Q) := by
    rw [← hNder]
    change Nq ≤ Subgroup.center (H ⧸ Q)
    rw [← hCqNq]
    exact inf_le_right

  let T : Subgroup (H ⧸ Q) := (_root_.commutator H).map qQ
  letI : IsMulCommutative T := by
    refine ⟨⟨fun x y ↦ ?_⟩⟩
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hcentral x.property) y).symm
  let e : (H ⧸ N) ≃* (H ⧸ _root_.commutator H) :=
    QuotientGroup.quotientMulEquivOfEq hNder
  have e_mk (x : H) :
      e (QuotientGroup.mk' N x) =
        QuotientGroup.mk' (_root_.commutator H) x :=
    QuotientGroup.quotientMulEquivOfEq_mk hNder x
  let pairing := classTwoQuotientCommutatorPairing Q hQder hcentral
  let beta : (H ⧸ N) →* ((H ⧸ N) →* T) :=
    { toFun := fun x ↦ (pairing (e x)).comp e.toMonoidHom
      map_one' := by
        apply MonoidHom.ext
        intro y
        simp
      map_mul' := by
        intro x y
        apply MonoidHom.ext
        intro z
        simp }
  have hbeta_mk (x y : H) :
      ((beta (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) : T) :
          H ⧸ Q) = QuotientGroup.mk' Q ⁅x, y⁆ := by
    change (((pairing (e (QuotientGroup.mk' N x)))
        (e (QuotientGroup.mk' N y)) : T) : H ⧸ Q) =
      QuotientGroup.mk' Q ⁅x, y⁆
    rw [e_mk x, e_mk y]
    exact classTwoQuotientCommutatorPairing_mk_mk
      Q hQder hcentral x y

  have hUnormH : U ≤ Subgroup.normalizer (H : Set G) :=
    (base.U_le_HU.trans base.HU_le_M).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M))
  have hbetaU (u : U) (a b : H ⧸ N) :
      beta (D.U_action u a) (D.U_action u b) = beta a b := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
    let xu : H :=
      ⟨(u : G) * (x : G) * (u : G)⁻¹,
        (hUnormH u.property x).mp x.property⟩
    let yu : H :=
      ⟨(u : G) * (y : G) * (u : G)⁻¹,
        (hUnormH u.property y).mp y.property⟩
    have haction_x :
        D.U_action u (QuotientGroup.mk' N x) =
          QuotientGroup.mk' N xu := by
      change ptypeFCoreAction base.ptypeCtx u
          (QuotientGroup.mk' N x) = QuotientGroup.mk' N xu
      rw [ptypeFCoreAction, subgroupConjugationFactorHom_apply_mk]
    have haction_y :
        D.U_action u (QuotientGroup.mk' N y) =
          QuotientGroup.mk' N yu := by
      change ptypeFCoreAction base.ptypeCtx u
          (QuotientGroup.mk' N y) = QuotientGroup.mk' N yu
      rw [ptypeFCoreAction, subgroupConjugationFactorHom_apply_mk]
    rw [haction_x, haction_y]
    apply Subtype.ext
    rw [hbeta_mk, hbeta_mk]
    apply congrArg (QuotientGroup.mk' Q)
    apply Subtype.ext
    have hxyN : ⁅x, y⁆ ∈ N := by
      rw [hNder]
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y)
    have hxyH0 : ⁅(x : G), (y : G)⁆ ∈ base.H0 := hxyN
    have hcomm :
        (u : G) * ⁅(x : G), (y : G)⁆ =
          ⁅(x : G), (y : G)⁆ * (u : G) :=
      (Subgroup.mem_centralizer_iff.mp
        ((FTtype34_facts base).U_le_centralizer_H0 u.property)
        ⁅(x : G), (y : G)⁆ hxyH0).symm
    change
      ⁅(u : G) * (x : G) * (u : G)⁻¹,
          (u : G) * (y : G) * (u : G)⁻¹⁆ =
        ⁅(x : G), (y : G)⁆
    calc
      ⁅(u : G) * (x : G) * (u : G)⁻¹,
          (u : G) * (y : G) * (u : G)⁻¹⁆ =
          (u : G) * ⁅(x : G), (y : G)⁆ * (u : G)⁻¹ := by
            group
      _ = ⁅(x : G), (y : G)⁆ := by rw [hcomm]; group

  let A : W₁ → Subgroup (H ⧸ N) := fun w ↦
    actionConjugate D.W₁_action data.H₁ w
  have hpairExists : ∃ (w₁ w₂ : W₁) (x y : H ⧸ N),
      x ∈ A w₁ ∧ y ∈ A w₂ ∧ beta x y ≠ 1 := by
    by_contra hex
    have hzero (w₁ w₂ : W₁) (x y : H ⧸ N)
        (hx : x ∈ A w₁) (hy : y ∈ A w₂) : beta x y = 1 := by
      by_contra hne
      exact hex ⟨w₁, w₂, x, y, hx, hy, hne⟩
    have hAker (w : W₁) : A w ≤ beta.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      apply MonoidHom.ext
      intro y
      have hrightKer : (beta x).ker = ⊤ := by
        apply top_unique
        rw [← data.conjugates_direct.1]
        apply iSup_le
        intro v z hz
        rw [MonoidHom.mem_ker]
        exact hzero w v x z hx hz
      have hyker : y ∈ (beta x).ker := by
        rw [hrightKer]
        exact Subgroup.mem_top y
      simpa only [MonoidHom.one_apply] using
        (MonoidHom.mem_ker.mp hyker)
    have hbetaKer : beta.ker = ⊤ := by
      apply top_unique
      rw [← data.conjugates_direct.1]
      exact iSup_le hAker
    have hbetaEq : beta = 1 := beta.ker_eq_top_iff.mp hbetaKer
    have hbetaTrivial (x : H ⧸ N) : beta x = 1 := by
      rw [hbetaEq]
      rfl
    have hcommQ : _root_.commutator H ≤ Q := by
      apply Subgroup.commutator_le.mpr
      intro x _hx y _hy
      have hb :
          beta (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) = 1 := by
        have hb' := congrArg
          (fun f : (H ⧸ N) →* T ↦ f (QuotientGroup.mk' N y))
          (hbetaTrivial (QuotientGroup.mk' N x))
        simpa only [MonoidHom.one_apply] using hb'
      have hq : QuotientGroup.mk' Q ⁅x, y⁆ = 1 := by
        rw [← hbeta_mk]
        exact congrArg Subtype.val hb
      exact (QuotientGroup.eq_one_iff (N := Q) ⁅x, y⁆).mp hq
    apply (not_le_of_gt hQgood.2)
    rw [hNder]
    exact hcommQ
  obtain ⟨w₁, w₂, xbar₁, xbar₂, hx₁, hx₂, hpair⟩ :=
    hpairExists
  let a : data.H₁ :=
    ⟨(D.W₁_action w₁).symm xbar₁,
      (mem_actionConjugate_iff D.W₁_action data.H₁ w₁ xbar₁).mp hx₁⟩
  let b : data.H₁ :=
    ⟨(D.W₁_action w₂).symm xbar₂,
      (mem_actionConjugate_iff D.W₁_action data.H₁ w₂ xbar₂).mp hx₂⟩
  have hcoord_a : D.W₁_action w₁ (a : H ⧸ N) = xbar₁ := by
    simp only [a, MulEquiv.apply_symm_apply]
  have hcoord_b : D.W₁_action w₂ (b : H ⧸ N) = xbar₂ := by
    simp only [b, MulEquiv.apply_symm_apply]
  have hpairab :
      beta (D.W₁_action w₁ (a : H ⧸ N))
        (D.W₁_action w₂ (b : H ⧸ N)) ≠ 1 := by
    simpa only [hcoord_a, hcoord_b] using hpair
  have ha : a ≠ 1 := by
    intro ha1
    apply hpairab
    simp [ha1]
  have hb : b ≠ 1 := by
    intro hb1
    apply hpairab
    simp [hb1]

  letI : Fact D.p.Prime := ⟨D.p_prime⟩
  letI : Fact (Nat.card data.H₁).Prime := ⟨by
    rw [data.card_H₁]
    exact D.p_prime⟩
  letI : IsCyclic data.H₁ := isCyclic_of_prime_card data.card_H₁
  letI : IsMulCommutative (MulAut data.H₁) := by
    apply isMulCommutative_iff.mpr
    intro alpha gamma
    obtain ⟨m, hm⟩ := alpha.toMonoidHom.map_cyclic
    obtain ⟨n, hn⟩ := gamma.toMonoidHom.map_cyclic
    apply MulEquiv.ext
    intro z
    change alpha (gamma z) = gamma (alpha z)
    calc
      alpha (gamma z) = (gamma z) ^ m := hm (gamma z)
      _ = (z ^ n) ^ m :=
        congrArg (fun q : data.H₁ ↦ q ^ m) (hn z)
      _ = z ^ (n * m) := (zpow_mul z n m).symm
      _ = z ^ (m * n) := by rw [mul_comm]
      _ = (z ^ m) ^ n := zpow_mul z m n
      _ = (alpha z) ^ n :=
        congrArg (fun q : data.H₁ ↦ q ^ n) (hm z).symm
      _ = gamma (alpha z) := (hn (alpha z)).symm
  let rho : U →* MulAut data.H₁ :=
    restrictMulAutHom data.H₁ D.U_action data.H₁_normalized
  let rhoW : W₁ → U →* MulAut data.H₁ := fun w ↦
    rho.comp (D.W₁_action_U w⁻¹).toMonoidHom
  let f : data.H₁ →* T :=
    { toFun := fun z ↦
        beta (D.W₁_action w₁ (z : H ⧸ N))
          (D.W₁_action w₂ (b : H ⧸ N))
      map_one' := by simp
      map_mul' := by intro z t; simp }
  have hfa : f a ≠ 1 := by
    change
      beta (D.W₁_action w₁ (a : H ⧸ N))
          (D.W₁_action w₂ (b : H ⧸ N)) ≠ 1
    exact hpairab
  have hfker : f.ker = ⊥ := by
    rcases f.ker.eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exact hbot
    · exfalso
      apply hfa
      apply MonoidHom.mem_ker.mp
      rw [htop]
      exact Subgroup.mem_top a
  have hfinjective : Function.Injective f :=
    f.ker_eq_bot_iff.mp hfker
  have hscale (alpha gamma : MulAut data.H₁) :
      beta (D.W₁_action w₁ (alpha a : H ⧸ N))
          (D.W₁_action w₂ (gamma b : H ⧸ N)) =
        f ((alpha * gamma) a) := by
    obtain ⟨m, hm⟩ := alpha.toMonoidHom.map_cyclic
    obtain ⟨n, hn⟩ := gamma.toMonoidHom.map_cyclic
    have halpha : alpha a = a ^ m := hm a
    have hgamma : gamma b = b ^ n := hn b
    have hproductAction : (alpha * gamma) a = a ^ (n * m) := by
      rw [MulAut.mul_apply]
      calc
        alpha (gamma a) = (gamma a) ^ m := hm (gamma a)
        _ = (a ^ n) ^ m :=
          congrArg (fun q : data.H₁ ↦ q ^ m) (hn a)
        _ = a ^ (n * m) := (zpow_mul a n m).symm
    change
      beta (D.W₁_action w₁ (alpha a : H ⧸ N))
          (D.W₁_action w₂ (gamma b : H ⧸ N)) =
        beta (D.W₁_action w₁ ((alpha * gamma) a : H ⧸ N))
          (D.W₁_action w₂ (b : H ⧸ N))
    rw [halpha, hgamma, hproductAction]
    simp only [Subgroup.coe_zpow, map_zpow, MonoidHom.zpow_apply,
      zpow_mul]
    rw [← zpow_mul, ← zpow_mul, mul_comm]
  have haction (w : W₁) (u : U) (z : data.H₁) :
      D.U_action u (D.W₁_action w (z : H ⧸ N)) =
        D.W₁_action w (rhoW w u z : H ⧸ N) := by
    have hcompat := D.action_compatibility
      (D.W₁_action_U w⁻¹ u) w (z : H ⧸ N)
    simpa only [rhoW, rho, MonoidHom.comp_apply,
      coe_restrictMulAutHom_apply, MulEquiv.coe_toMonoidHom,
      map_inv, MulAut.apply_inv_self,
      MulAut.inv_apply_self] using
      hcompat
  have hproduct (u : U) : rhoW w₁ u * rhoW w₂ u = 1 := by
    have hinvariant := hbetaU u
      (D.W₁_action w₁ (a : H ⧸ N))
      (D.W₁_action w₂ (b : H ⧸ N))
    rw [haction w₁ u a, haction w₂ u b] at hinvariant
    have hinvariant' :
        beta (D.W₁_action w₁ (rhoW w₁ u a : H ⧸ N))
            (D.W₁_action w₂ (rhoW w₂ u b : H ⧸ N)) = f a := by
      change
        beta (D.W₁_action w₁ (rhoW w₁ u a : H ⧸ N))
            (D.W₁_action w₂ (rhoW w₂ u b : H ⧸ N)) =
          beta (D.W₁_action w₁ (a : H ⧸ N))
            (D.W₁_action w₂ (b : H ⧸ N))
      exact hinvariant
    have hvalues :
        f ((rhoW w₁ u * rhoW w₂ u) a) = f a :=
      (hscale (rhoW w₁ u) (rhoW w₂ u)).symm.trans hinvariant'
    have hfix : (rhoW w₁ u * rhoW w₂ u) a = a :=
      hfinjective hvalues
    apply MulEquiv.ext
    intro z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card data.card_H₁ ha (g' := z))
    calc
      (rhoW w₁ u * rhoW w₂ u) z =
          (rhoW w₁ u * rhoW w₂ u) (a ^ n) := by rw [hn]
      _ = ((rhoW w₁ u * rhoW w₂ u) a) ^ n := map_zpow _ _ n
      _ = a ^ n := by rw [hfix]
      _ = z := hn
      _ = (1 : MulAut data.H₁) z := by simp

  let t : W₁ := w₂⁻¹ * w₁
  have hrhoConj (u : U) :
      rho (D.W₁_action_U t u) = (rho u)⁻¹ := by
    have hp := hproduct (D.W₁_action_U w₁ u)
    have hi := eq_inv_of_mul_eq_one_right hp
    simpa only [rhoW, t, MonoidHom.comp_apply, map_mul, map_inv,
      MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.apply_inv_self,
      MulAut.inv_apply_self] using hi
  let theta : MulAut U := D.W₁_action_U t
  have hrhoTheta (u : U) : rho (theta u) = (rho u)⁻¹ := by
    simpa only [theta] using hrhoConj u
  have hrhoEven (k : ℕ) (u : U) :
      rho ((theta ^ (2 * k)) u) = rho u := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
        change rho (theta (theta ((theta ^ (2 * k)) u))) = rho u
        rw [hrhoTheta, hrhoTheta, inv_inv, ih]
  obtain ⟨k, htk⟩ : ∃ k : ℕ, t = (t ^ 2) ^ k := by
    have htodd : Odd (orderOf t) :=
      Odd.of_dvd_nat (mFT_odd W₁) (orderOf_dvd_natCard t)
    obtain ⟨j, hj⟩ := htodd
    refine ⟨j + 1, ?_⟩
    rw [← pow_mul]
    rw [show 2 * (j + 1) = orderOf t + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have htPow : t = t ^ (2 * k) := by
    calc
      t = (t ^ 2) ^ k := htk
      _ = t ^ (2 * k) := (pow_mul t 2 k).symm
  have hthetaPow : theta = theta ^ (2 * k) := by
    calc
      theta = D.W₁_action_U (t ^ (2 * k)) := by
        simpa only [theta] using congrArg D.W₁_action_U htPow
      _ = theta ^ (2 * k) := by
        simpa only [theta] using D.W₁_action_U.map_pow t (2 * k)
  have hrhoSelfInv (u : U) : rho u = (rho u)⁻¹ := by
    have h := hrhoTheta u
    rw [hthetaPow, hrhoEven k u] at h
    exact h
  have hrhoTrivial (u : U) : rho u = 1 := by
    obtain ⟨k, huk⟩ : ∃ k : ℕ, u = (u ^ 2) ^ k := by
      have huodd : Odd (orderOf u) :=
        Odd.of_dvd_nat (mFT_odd U) (orderOf_dvd_natCard u)
      obtain ⟨j, hj⟩ := huodd
      refine ⟨j + 1, ?_⟩
      rw [← pow_mul]
      rw [show 2 * (j + 1) = orderOf u + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have hu2 : rho (u ^ 2) = 1 := by
      calc
        rho (u ^ 2) = (rho u) ^ 2 := map_pow rho u 2
        _ = rho u * rho u := pow_two (rho u)
        _ = (rho u)⁻¹ * rho u :=
          congrArg (fun alpha : MulAut data.H₁ ↦ alpha * rho u)
            (hrhoSelfInv u)
        _ = 1 := inv_mul_cancel (rho u)
    calc
      rho u = rho ((u ^ 2) ^ k) := congrArg rho huk
      _ = (rho (u ^ 2)) ^ k := map_pow rho (u ^ 2) k
      _ = 1 := by rw [hu2]; simp

  let K := pointwiseActionKernel D.U_action data.H₁
  have hKtop : K = ⊤ := by
    apply top_unique
    intro u _hu
    rw [mem_pointwiseActionKernel_iff]
    intro z hz
    let z₁ : data.H₁ := ⟨z, hz⟩
    have hfix := congrArg (fun alpha : MulAut data.H₁ ↦ alpha z₁)
      (hrhoTrivial u)
    exact congrArg Subtype.val (by
      simpa only [MulAut.one_apply] using hfix)
  have hKwtop (w : W₁) :
      pointwiseActionKernel D.U_action
          (actionConjugate D.W₁_action data.H₁ w) = ⊤ := by
    apply top_unique
    intro u _hu
    rw [D.mem_pointwiseActionKernel_actionConjugate_iff data.H₁ w u]
    change D.W₁_action_U w⁻¹ u ∈ K
    rw [hKtop]
    exact Subgroup.mem_top _
  have hCtop : D.C = ⊤ := by
    rw [D.C_eq_iInf_pointwiseActionKernel_of_iSup_eq_top
      data.H₁ data.conjugates_direct.1]
    apply top_unique
    rw [le_iInf_iff]
    intro w
    rw [hKwtop w]
  apply facts.compl_kernel_ne
  ext g
  constructor
  · intro hg
    exact Ptype_Fcompl_kernel_le base.ptypeCtx hg
  · intro hg
    let gU : U := ⟨g, hg⟩
    refine ⟨gU, ?_, rfl⟩
    change gU ∈ (ptypeFCoreAction base.ptypeCtx).ker
    change gU ∈ D.C
    rw [hCtop]
    exact Subgroup.mem_top gU

/-- `PFsection11.v: FTtype34_Fcore_kernel_trivial`, Peterfalvi (11.7). -/
theorem FTtype34_Fcore_kernel_trivial
    (base : FTType34Base M U W W₁ W₂ defW) :
    FTType34FCoreKernelTrivial base := by
  have hH0 : base.H0 = ⊥ := by
    by_contra hne
    exact ftType34_nonGalois_kernel_impossible base hne
      (ftType34_not_Galois_of_kernel_ne_bot base hne)
  have hfactorElementary := FTType34BoundsCoreInternal.factor_elementary base
  have hfactorCard := FTType34BoundsCoreInternal.factor_card base
  have hH0sub : base.H0.subgroupOf base.H = ⊥ := by
    rw [hH0, Subgroup.bot_subgroupOf]
  let e : (base.H ⧸ base.H0.subgroupOf base.H) ≃* base.H :=
    (QuotientGroup.quotientMulEquivOfEq hH0sub).trans
      (QuotientGroup.quotientBot (G := base.H))
  exact
    { H_elementaryAbelian := by
        exact
          { isPGroup := hfactorElementary.isPGroup.of_equiv e
            commutative :=
              { is_comm :=
                  { comm := fun x y ↦ by
                      apply e.symm.injective
                      simp only [map_mul]
                      exact hfactorElementary.commutative.is_comm.comm
                        (e.symm x) (e.symm y) } }
            pow_eq_one := fun x ↦ by
              apply e.symm.injective
              rw [map_pow, map_one]
              exact hfactorElementary.pow_eq_one (e.symm x) }
      card_H_eq := by
        exact (Nat.card_congr e.toEquiv).symm.trans hfactorCard
      H0_eq_bot := hH0 }

end

end Submission.OddOrder.PF
