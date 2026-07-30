import Mathlib.Analysis.Complex.Polynomial.Basic
import Submission.OddOrder.MathlibSupport.CentralizerConjugationOrbitCount
import Submission.OddOrder.MathlibSupport.CyclicOrbitConjugationRankDrop
import Submission.OddOrder.MathlibSupport.CyclicRepresentationQuasiHomocyclic
import Submission.OddOrder.MathlibSupport.EndomorphismScalarLine
import Submission.OddOrder.MathlibSupport.ExtraspecialIrreducibleDegree
import Submission.OddOrder.MathlibSupport.ExtraspecialNormalRestrictionNonmodular
import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientEndomorphismBasis
import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientFinrank
import Submission.OddOrder.MathlibSupport.FixedPointFreeCyclicOrbitRepresentatives
import Submission.OddOrder.MathlibSupport.MaschkeNormalConstituent
import Submission.OddOrder.MathlibSupport.RepresentationLinearEquiv
import Submission.OddOrder.PF.Section02.DadeHypothesis

/-!
# Bender--Glauberman Theorem 2.5

This file assembles the numerical conclusion of `BGsection2.v:
repr_extraspecial_prime_sdprod_cycle` from the representation-theoretic and
quasi-homocyclic components ported in `MathlibSupport`.
-/

namespace Submission.OddOrder.BG.Section02

open scoped IsMulCommutative

universe u v w

noncomputable section

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF

private theorem extraspecial_cyclic_rank_profile
    {k : Type u} {J : Type v} {V : Type w}
    [Field k] [IsAlgClosed k] [Group J] [Finite J]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {P H : Subgroup J} {p : ℕ} [Fact p.Prime] [IsCyclic H]
    (hpP : IsPGroup p P) (hP : IsExtraspecial P)
    (hHP : H ≤ Subgroup.normalizer P)
    (hcop : (Nat.card P).Coprime (Nat.card H))
    (hcardP : (Nat.card P : k) ≠ 0)
    (hcardH : (Nat.card H : k) ≠ 0)
    (hHgt : 1 < Nat.card H)
    (hcentralizer : ∀ h : H, h ≠ 1 →
      centralizerWithin P (Subgroup.zpowers (h : J)) = centerWithin P)
    (rho : Representation k J V)
    [Representation.IsIrreducible (rho.comp P.subtype)]
    (hrhoP : Function.Injective (rho.comp P.subtype)) :
    ∃ m : ℕ,
      Nat.dist (Module.finrank k V) (Nat.card H * m) = 1 := by
  classical
  letI : Nontrivial P := hP.nontrivial
  letI : Nontrivial V := by
    by_contra hV
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    have hsubP : Subsingleton P := hrhoP.subsingleton
    exact not_subsingleton_iff_nontrivial.mpr inferInstance hsubP
  letI : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩
  letI : NeZero (Nat.card H : k) := ⟨hcardH⟩

  have hcenter : H ≤ Subgroup.centralizer (centerWithin P : Set J) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    let hH : H := ⟨h, hh⟩
    by_cases heq : hH = 1
    · have hOne : h = 1 := congrArg Subtype.val heq
      subst h
      exact Commute.one_right z
    · have hzCent : z ∈
          centralizerWithin P (Subgroup.zpowers (hH : J)) := by
        rw [hcentralizer hH heq]
        exact hz
      exact ((mem_centralizerWithin.mp hzCent).2 (hH : J)
        (Subgroup.mem_zpowers (hH : J))).symm

  letI := subgroupConjugationAction P H hHP
  letI := subgroupConjugationCenterQuotientAction P H hHP
  let Q := P ⧸ Subgroup.center P
  let O := nonidentityFixedOneOrbitQuotient (G := H) (X := Q)
  letI : Fintype O := Fintype.ofFinite O

  obtain ⟨generator, hgenerator⟩ := IsCyclic.exists_generator (α := H)
  let e : Multiplicative (ZMod (Nat.card H)) ≃* H :=
    zmodMulEquivOfGenerator hgenerator rfl

  have hfixedQ : ∀ h : H, h ≠ 1 → ∀ q : Q,
      h • q = q → q = 1 :=
    centerQuotient_fixed_eq_one_of_centralizers P H hHP hcop hcenter
      hcentralizer
  have honeQ : ∀ h : H, h • (1 : Q) = 1 := by
    intro h
    change h • ((1 : P) : Q) = ((1 : P) : Q)
    rw [MulAction.Quotient.smul_coe]
    simp

  let orbitClass (o : O) (t : ZMod (Nat.card H)) : Q :=
    fixedPointFreeCyclicOrbitRepresentative e o t
  let orbitElement (o : O) (t : ZMod (Nat.card H)) : P :=
    e (Multiplicative.ofAdd t) • centerQuotientRepresentative o.1.out
  let rhoP : Representation k P V := rho.comp P.subtype
  let orbit (o : O) (t : ZMod (Nat.card H)) : Module.End k V :=
    rhoP (orbitElement o t)

  have horbitMk (o : O) (t : ZMod (Nat.card H)) :
      QuotientGroup.mk' (Subgroup.center P) (orbitElement o t) =
        orbitClass o t := by
    change ((e (Multiplicative.ofAdd t) •
        centerQuotientRepresentative o.1.out : P) : Q) =
      e (Multiplicative.ofAdd t) • o.1.out
    calc
      ((e (Multiplicative.ofAdd t) •
          centerQuotientRepresentative o.1.out : P) : Q) =
          e (Multiplicative.ofAdd t) •
            (centerQuotientRepresentative (G := P) o.1.out : Q) :=
        (MulAction.Quotient.smul_coe (H := Subgroup.center P)
          (e (Multiplicative.ofAdd t))
          (centerQuotientRepresentative (G := P) o.1.out)).symm
      _ = e (Multiplicative.ofAdd t) • o.1.out :=
        congrArg (fun q : Q ↦ e (Multiplicative.ofAdd t) • q)
          (centerQuotientRepresentative_mk (G := P) o.1.out)
  have horbitClassInjective : Function.Injective
      (fun ot : O × ZMod (Nat.card H) ↦ orbitClass ot.1 ot.2) :=
    fixedPointFreeCyclicOrbitRepresentative_injective e hfixedQ

  let fullElement : Option (O × ZMod (Nat.card H)) → P
    | none => 1
    | some ot => orbitElement ot.1 ot.2
  have hfullMk (a : Option (O × ZMod (Nat.card H))) :
      QuotientGroup.mk' (Subgroup.center P) (fullElement a) =
        match a with
        | none => 1
        | some ot => orbitClass ot.1 ot.2 := by
    cases a with
    | none => simp [fullElement]
    | some ot => exact horbitMk ot.1 ot.2
  have hfullClassInjective : Function.Injective
      (fun a : Option (O × ZMod (Nat.card H)) ↦
        QuotientGroup.mk' (Subgroup.center P) (fullElement a)) := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some ot =>
            exfalso
            apply fixedPointFreeCyclicOrbitRepresentative_ne_one e honeQ
              ot.1 ot.2
            change orbitClass ot.1 ot.2 = 1
            exact (hfullMk (some ot)).symm.trans
              (hxy.symm.trans (hfullMk none))
    | some ot =>
        cases y with
        | none =>
            exfalso
            apply fixedPointFreeCyclicOrbitRepresentative_ne_one e honeQ
              ot.1 ot.2
            change orbitClass ot.1 ot.2 = 1
            exact (hfullMk (some ot)).symm.trans
              (hxy.trans (hfullMk none))
        | some ot' =>
            apply congrArg some
            apply horbitClassInjective
            exact (hfullMk (some ot)).symm.trans
              (hxy.trans (hfullMk (some ot')))
  have hfullLI : LinearIndependent k
      (fun a : Option (O × ZMod (Nat.card H)) ↦ rhoP (fullElement a)) :=
    hP.representationEnd_linearIndependent_of_quotient_injective hpP rhoP
      hrhoP hcardP fullElement hfullClassInjective
  have horbitLI : LinearIndependent k
      (fun ot : O × ZMod (Nat.card H) ↦ orbit ot.1 ot.2) := by
    change LinearIndependent k
      ((fun a : Option (O × ZMod (Nat.card H)) ↦ rhoP (fullElement a)) ∘
        fun ot : O × ZMod (Nat.card H) ↦ some ot)
    exact hfullLI.comp (fun ot : O × ZMod (Nat.card H) ↦ some ot)
      (Option.some_injective _)

  have honeNotOrbitSpan : (1 : Module.End k V) ∉
      Submodule.span k
        (Set.range (fun ot : O × ZMod (Nat.card H) ↦ orbit ot.1 ot.2)) := by
    have hnone : (none : Option (O × ZMod (Nat.card H))) ∉
        Set.range (fun ot : O × ZMod (Nat.card H) ↦ some ot) := by simp
    have hnot := hfullLI.notMem_span_image hnone
    have himage :
        (fun a : Option (O × ZMod (Nat.card H)) ↦ rhoP (fullElement a)) ''
            Set.range (fun ot : O × ZMod (Nat.card H) ↦ some ot) =
          Set.range (fun ot : O × ZMod (Nat.card H) ↦ orbit ot.1 ot.2) := by
      ext T
      simp [orbit, fullElement]
    rw [himage] at hnot
    simpa [fullElement] using hnot

  have hcount : Nat.card Q =
      1 + Nat.card O * Nat.card H := by
    simpa [Q, O] using
      natCard_centerQuotient_eq_one_add_orbits_mul_natCard_of_centralizers
        P H hHP hcop hcenter hcentralizer
  have hend : Module.finrank k (Module.End k V) = Nat.card Q := by
    simpa [rhoP, Q] using
      hP.faithful_irreducible_finrank_end_eq_quotient_center_card
        hpP rhoP hrhoP hcardP
  have hambient : Module.finrank k (Module.End k V) =
      Nat.card H * Fintype.card O + 1 := by
    rw [hend, hcount]
    simp only [Nat.card_eq_fintype_card]
    ac_rfl
  have hfullSpanTop :
      Submodule.span k
          (Set.range (fun a : Option (O × ZMod (Nat.card H)) ↦
            rhoP (fullElement a))) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hfullLI, hambient]
    simp [Nat.card_eq_fintype_card, Nat.mul_comm]
  have hspan :
      endomorphismScalarLine (k := k) (V := V) ⊔
          Submodule.span k
            (Set.range (fun ot : O × ZMod (Nat.card H) ↦
              orbit ot.1 ot.2)) = ⊤ := by
    apply top_unique
    rw [← hfullSpanTop, Submodule.span_le]
    rintro T ⟨a, rfl⟩
    cases a with
    | none =>
        have hone : (1 : Module.End k V) ∈
            endomorphismScalarLine (k := k) (V := V) := by
          exact Submodule.mem_span_singleton_self 1
        simpa [fullElement] using
          (show (1 : Module.End k V) ∈
              endomorphismScalarLine (k := k) (V := V) ⊔ _ from
            (le_sup_left : endomorphismScalarLine (k := k) (V := V) ≤ _) hone)
    | some ot =>
        apply (le_sup_right :
          Submodule.span k
            (Set.range (fun ot : O × ZMod (Nat.card H) ↦
              orbit ot.1 ot.2)) ≤ _)
        exact Submodule.subset_span ⟨ot, by simp [orbit, fullElement]⟩

  obtain ⟨omegaVal, homegaVal⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot k (Nat.card H)
  let omega : kˣ := (homegaVal.isUnit (NeZero.ne (Nat.card H))).unit
  have homega : IsPrimitiveRoot omega (Nat.card H) :=
    homegaVal.isUnit_unit (NeZero.ne (Nat.card H))
  have honeNotBlock : (1 : Module.End k V) ∉
      indexedWeightBlock (k := k)
        (cyclicOrbitFourierFamily homega orbit) 0 := by
    intro hone
    apply honeNotOrbitSpan
    apply (show indexedWeightBlock (k := k)
        (cyclicOrbitFourierFamily homega orbit) 0 ≤
          Submodule.span k
            (Set.range (fun ot : O × ZMod (Nat.card H) ↦
              orbit ot.1 ot.2)) from ?_) hone
    rw [indexedWeightBlock, Submodule.span_le]
    rintro T ⟨o, rfl⟩
    unfold cyclicOrbitFourierFamily
    exact Submodule.sum_mem _ fun t _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(o, t), rfl⟩)

  let z : H := generator⁻¹
  have hzgen : ∀ x : H, x ∈ Subgroup.zpowers z :=
    forall_mem_zpowers_inv_of_forall_mem_zpowers generator hgenerator
  have hzeq : z = e (Multiplicative.ofAdd (-1 : ZMod (Nat.card H))) := by
    simpa [z, e] using
      (zmodMulEquivOfGenerator_apply_ofAdd_intCast hgenerator rfl (-1)).symm
  have hzpow : z ^ Nat.card H = 1 := pow_card_eq_one'
  have horbitShift (o : O) (t : ZMod (Nat.card H)) :
      z⁻¹ • orbitElement o t = orbitElement o (t + 1) := by
    rw [hzeq]
    simp [orbitElement, ← mul_smul, ← map_mul, mul_comm]
  have hshift (o : O) (t : ZMod (Nat.card H)) :
      linearEquivConjugation
          (representationLinearEquiv (rho.comp H.subtype) z) (orbit o t) =
        orbit o (t + 1) := by
    rw [linearEquivConjugation_representationLinearEquiv]
    rw [endomorphismConjugationRepresentation_apply]
    change rho (z⁻¹ : H) * rho (orbitElement o t : P) *
        rho ((z⁻¹)⁻¹ : H) = rho (orbitElement o (t + 1) : P)
    rw [inv_inv]
    rw [← rho.map_mul, ← rho.map_mul]
    apply congrArg rho
    have hshiftJ := congrArg Subtype.val (horbitShift o t)
    simpa [z, rhoP, coe_subgroupConjugationAction_smul P H hHP] using hshiftJ
  have hdrop := primitiveRoot_conjugation_rank_drop_of_cyclic_orbits
    homega (representationLinearEquiv (rho.comp H.subtype) z) orbit
    horbitLI hshift honeNotBlock hspan hambient
  obtain ⟨m, _, htotal, _, _⟩ :=
    cyclicRepresentation_quasiHomocyclic_rank_profile
      hHgt
      homega (rho.comp H.subtype) z hzpow hdrop
  exact ⟨m, htotal⟩

private theorem leftRegular_injective
    {k : Type u} {G : Type v} [Field k] [Group G] :
    Function.Injective (Representation.leftRegular k G) := by
  intro g h hgh
  have hsingle := DFunLike.congr_fun hgh (Finsupp.single 1 (1 : k))
  simp only [Representation.ofMulAction_single, smul_eq_mul, mul_one] at hsingle
  exact Finsupp.single_left_injective one_ne_zero hsingle

set_option maxHeartbeats 2000000 in
/-- `BGsection2.v: repr_extraspecial_prime_sdprod_cycle`, Theorem 2.5,
numerical conclusion.  A cyclic coprime complement acting fixed-point-freely
on the noncentral elements of an extraspecial group has order dividing one
of the two adjacent powers `p ^ n ± 1`. -/
theorem repr_extraspecial_prime_sdprod_cycle
    {J : Type u} [Group J] [Finite J]
    {p n : ℕ} (P H : Subgroup J)
    (hp : p.Prime)
    (hpP : IsPGroup p P)
    (hP : IsExtraspecial P)
    (hsd : IsInternalSemidirectProductIn P H (⊤ : Subgroup J))
    (hcyclic : IsCyclic H)
    (hcard : Nat.card P = p ^ (2 * n + 1))
    (hcop : Nat.Coprime p (Nat.card H))
    (hcentralizer : ∀ h : H, h ≠ 1 →
      centralizerWithin P (Subgroup.zpowers (h : J)) = centerWithin P) :
    Nat.card H ∣ p ^ n + 1 ∨ Nat.card H ∣ p ^ n - 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic H := hcyclic
  by_cases hHone : Nat.card H = 1
  · left
    simpa [hHone]
  have hHgt : 1 < Nat.card H := by
    have hHpos : 0 < Nat.card H := Nat.card_pos
    omega

  have hnormTop : (⊤ : Subgroup J) ≤ Subgroup.normalizer P :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsd.1).mp hsd.2.2.1
  have hHP : H ≤ Subgroup.normalizer P := hsd.2.1.trans hnormTop
  letI : P.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact top_unique hnormTop

  have hPcentral : P ≤ Subgroup.centralizer (centerWithin P : Set J) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_centralizerWithin.mp hz).2 x hx).symm
  have hHcentral : H ≤ Subgroup.centralizer (centerWithin P : Set J) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    let hH : H := ⟨h, hh⟩
    by_cases heq : hH = 1
    · have hOne : h = 1 := congrArg Subtype.val heq
      subst h
      exact Commute.one_right z
    · have hzCent : z ∈
          centralizerWithin P (Subgroup.zpowers (hH : J)) := by
        rw [hcentralizer hH heq]
        exact hz
      exact ((mem_centralizerWithin.mp hzCent).2 (hH : J)
        (Subgroup.mem_zpowers (hH : J))).symm
  have hsup : P ⊔ H = (⊤ : Subgroup J) := by
    apply le_antisymm le_top
    intro x _
    let xTop : (⊤ : Subgroup J) := ⟨x, Subgroup.mem_top x⟩
    obtain ⟨⟨a, b⟩, hab⟩ := hsd.2.2.2.2 xTop
    have habJ : (a : J) * (b : J) = x := congrArg Subtype.val hab
    rw [← habJ]
    exact Subgroup.mul_mem_sup a.property b.property
  have hcentralTop :
      Subgroup.centralizer (centerWithin P : Set J) = ⊤ := by
    apply top_unique
    rw [← hsup]
    exact sup_le hPcentral hHcentral

  let qH : H →* J ⧸ P := (QuotientGroup.mk' P).comp H.subtype
  have hqHsurj : Function.Surjective qH := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P q
    let xTop : (⊤ : Subgroup J) := ⟨x, Subgroup.mem_top x⟩
    obtain ⟨⟨a, b⟩, hab⟩ := hsd.2.2.2.2 xTop
    have habJ : (a : J) * (b : J) = x := congrArg Subtype.val hab
    let bH : H := ⟨(b : J), b.property⟩
    refine ⟨bH, ?_⟩
    change QuotientGroup.mk' P (b : J) = QuotientGroup.mk' P x
    have hqa : QuotientGroup.mk' P (a : J) = 1 :=
      (QuotientGroup.eq_one_iff (a : J)).mpr a.property
    calc
      QuotientGroup.mk' P (b : J) =
          1 * QuotientGroup.mk' P (b : J) := (one_mul _).symm
      _ = QuotientGroup.mk' P (a : J) * QuotientGroup.mk' P (b : J) := by
        rw [hqa]
      _ = QuotientGroup.mk' P ((a : J) * (b : J)) := by rw [map_mul]
      _ = QuotientGroup.mk' P x := congrArg (QuotientGroup.mk' P) habJ
  letI : IsCyclic (J ⧸ P) := isCyclic_of_surjective qH hqHsurj

  have hcopPH : (Nat.card P).Coprime (Nat.card H) := by
    rw [hcard]
    exact hcop.pow_left (2 * n + 1)
  have hcardPC : (Nat.card P : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcardHC : (Nat.card H : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcardJC : (Nat.card J : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'

  let rho : Representation ℂ J (J →₀ ℂ) := Representation.leftRegular ℂ J
  have hrho : Function.Injective rho := leftRegular_injective
  let Z : Subgroup J := (Subgroup.center P).map P.subtype
  have hcentralTopZ : Subgroup.centralizer (Z : Set J) = ⊤ := by
    simpa [Z, map_center_eq_centerWithin P] using hcentralTop
  letI : Z.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← hcentralTopZ]
    exact Subgroup.centralizer_le_normalizer (Z : Set J)
  have hZne : Z ≠ ⊥ := by
    intro hZbot
    apply hP.center_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hzmap : ((z : P) : J) ∈ Z := ⟨z, hz, rfl⟩
    exact Subgroup.mem_bot.mp (hZbot ▸ hzmap)
  have hZnot : ¬ Z ≤ rho.ker := by
    intro hle
    apply hZne
    apply le_antisymm
    · rw [← rho.ker_eq_bot_iff.mpr hrho]
      exact hle
    · exact bot_le
  obtain ⟨U, hU, hUZ⟩ :=
    exists_irreducible_subrepresentation_not_le_ker_of_normal
      rho Z hcardJC hZnot
  letI := hU
  let sigma := U.toRepresentation
  let sigmaP := sigma.comp P.subtype
  have hcenterNot : ¬ Subgroup.center P ≤ sigmaP.ker := by
    intro hle
    apply hUZ
    rintro a ⟨z, hz, rfl⟩
    have hzker := hle hz
    rw [MonoidHom.mem_ker] at hzker ⊢
    exact hzker
  have hsigmaP : Function.Injective sigmaP := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hP.normal_eq_bot_or_center_le hpP sigmaP.ker with
      hbot | hcenterLe
    · exact hbot
    · exact False.elim (hcenterNot hcenterLe)
  obtain ⟨T, hT, hTcenter⟩ :=
    exists_irreducible_subrepresentation_not_le_ker_of_normal
      (k := ℂ) (G := P) (V := U.toSubmodule)
      sigmaP (Subgroup.center P) hcardPC hcenterNot
  letI := hT
  let tau := T.toRepresentation
  have htau : Function.Injective tau := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hP.normal_eq_bot_or_center_le hpP tau.ker with
      hbot | hcenterLe
    · exact hbot
    · exact False.elim (hTcenter hcenterLe)
  have htauExact := htau
  dsimp [tau] at htauExact
  have hsigmaPIrr :=
    @IsExtraspecial.normalRestriction_irreducible_of_quotient_isCyclic_of_card_ne_zero
      ℂ J U.toSubmodule _ _ _ _ _ _ _ p _ P _ _ hP hpP hcardPC
        sigma hU T hT htauExact hcentralTop
  letI := hsigmaPIrr
  have hsigmaPExact : Function.Injective (sigma.comp P.subtype) := by
    simpa only [sigmaP] using hsigmaP
  obtain ⟨m, hdist⟩ :=
    @extraspecial_cyclic_rank_profile ℂ J U.toSubmodule
      _ _ _ _ _ _ _ P H p _ _ hpP hP hHP hcopPH hcardPC hcardHC hHgt
        hcentralizer sigma hsigmaPIrr hsigmaPExact
  have hdegree : Module.finrank ℂ U.toSubmodule = p ^ n := by
    exact
      @IsExtraspecial.faithful_irreducible_finrank_eq
        ℂ P U.toSubmodule _ _ _ _ _ _ _ _ p n _ hP hpP hcard
          (sigma.comp P.subtype) hsigmaPIrr hsigmaPExact
  rw [hdegree] at hdist
  by_cases hle : p ^ n ≤ Nat.card H * m
  · left
    rw [Nat.dist_eq_sub_of_le hle] at hdist
    have heq : Nat.card H * m = p ^ n + 1 := by omega
    rw [← heq]
    exact dvd_mul_right _ _
  · right
    have hle' : Nat.card H * m ≤ p ^ n := Nat.le_of_not_ge hle
    rw [Nat.dist_eq_sub_of_le_right hle'] at hdist
    have heq : p ^ n - 1 = Nat.card H * m := by omega
    rw [heq]
    exact dvd_mul_right _ _

end

end Submission.OddOrder.BG.Section02
