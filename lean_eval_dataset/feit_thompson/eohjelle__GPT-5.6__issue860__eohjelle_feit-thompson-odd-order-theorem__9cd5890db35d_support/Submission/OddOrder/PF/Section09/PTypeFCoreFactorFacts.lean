import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.PF.Section09.PTypeFCoreActions

/-!
# Peterfalvi Section 9: arithmetic of the selected F-core factor

This phase proves the elementary-abelian, fixed-point, and cardinality facts
for the chief factor selected in `PTypeFCoreActions`.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative Pointwise commutatorElement

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## Local adapters for the factor calculation -/

private theorem U_le_M_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) : U ≤ M :=
  ctx.typeP.2.1.2.1.trans ctx.typeP.1.2.2.2.1

private theorem W₁_le_M_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) : W₁ ≤ M :=
  ctx.typeP.1.2.1.1

private theorem U_normalizes_Fcore_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    U ≤ Subgroup.normalizer (Fitting_core M : Set G) :=
  (U_le_M_factorFacts ctx).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
      (Fcore_normal M))

private theorem W₁_normalizes_Fcore_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    W₁ ≤ Subgroup.normalizer (Fitting_core M : Set G) :=
  (W₁_le_M_factorFacts ctx).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
      (Fcore_normal M))

private theorem semidirect_sup_eq_factorFacts
    {N R K : Subgroup G} (h : IsInternalSemidirectProductIn N R K) :
    N ⊔ R = K := by
  apply le_antisymm (sup_le h.1 h.2.1)
  intro k hk
  obtain ⟨⟨n, r⟩, hnr⟩ := h.2.2.2.2 ⟨k, hk⟩
  have : (n : G) * (r : G) = k := congrArg Subtype.val hnr
  rw [← this]
  exact Subgroup.mul_mem_sup n.property r.property

private theorem frobeniusWielandtCard_factorFacts
    {M V U W : Subgroup G}
    (hfrob : PTypeFrobeniusProduct U W)
    (hVM : V ≤ M) (hVnormal : (V.subgroupOf M).Normal)
    (hUM : U ≤ M) (hWM : W ≤ M)
    (hcop : Nat.Coprime (Nat.card V) (Nat.card ↑(U ⊔ W)))
    (hsol : IsSolvable V) :
    Nat.card V *
        Nat.card (centralizerWithin V (U ⊔ W)) ^ Nat.card W =
      Nat.card (centralizerWithin V U) *
        Nat.card (centralizerWithin V W) ^ Nat.card W := by
  have hnorm : U ⊔ W ≤ Subgroup.normalizer (V : Set G) :=
    (sup_le hUM hWM).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mp hVnormal)
  simpa [Nat.mul_comm] using
    (Frobenius_Wielandt_fixpoint hfrob hnorm hcop hsol).1

private theorem W₂_le_Fcore_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    W₂ ≤ Fitting_core M :=
  ctx.typeP.2.2.2.1.2.2.1

private noncomputable def ptypeW₂FactorMap_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    W₂ →* ptypeFCoreFactor ctx :=
  (QuotientGroup.mk'
      ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M))).comp
    (Subgroup.inclusion (W₂_le_Fcore_factorFacts ctx))

private theorem ptypeW₂Factor_eq_range_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    ptypeW₂Factor ctx = (ptypeW₂FactorMap_factorFacts ctx).range := by
  classical
  let H := Fitting_core M
  let H₀ := Ptype_Fcore_kernel ctx
  letI : MulDistribMulAction W₁ (ptypeFCoreFactor ctx) :=
    MulDistribMulAction.compHom
      (ptypeFCoreFactor ctx) (ptypeW₁FactorAction ctx)
  change FixedPoints.subgroup W₁ (ptypeFCoreFactor ctx) =
    (ptypeW₂FactorMap_factorFacts ctx).range
  have hH₀H : H₀ ≤ H := (Ptype_Fcore_kernel_lt ctx).le
  have hH₀M : H₀ ≤ M := Ptype_Fcore_kernel_le_M ctx
  have hHM : H ≤ M := Fcore_sub M
  have hW₁M : W₁ ≤ M := W₁_le_M_factorFacts ctx
  have hcent : centralizerWithin H W₁ = W₂ := by
    simpa [H] using
      typeP_cent_core_compl M U W W₁ W₂ ctx.defW ctx.typeP
  apply le_antisymm
  · intro z hz
    obtain ⟨h, rfl⟩ :=
      QuotientGroup.mk'_surjective (H₀.subgroupOf H) z
    have hzfix :=
      (FixedPoints.mem_subgroup W₁ (ptypeFCoreFactor ctx)
        (QuotientGroup.mk' (H₀.subgroupOf H) h)).mp hz
    let HM : Subgroup M := H.subgroupOf M
    let NM : Subgroup M := H₀.subgroupOf M
    let RM : Subgroup M := W₁.subgroupOf M
    have hNMHM : NM ≤ HM := by
      intro x hx
      exact hH₀H hx
    letI : NM.Normal := Ptype_Fcore_kernel_normal_M ctx
    let qM : M →* M ⧸ NM := QuotientGroup.mk' NM
    let hM : M := ⟨(h : G), hHM h.property⟩
    letI : IsSolvable M := mmax_sol ctx.maxM
    letI : IsSolvable RM := isSolvable_subgroup_of_isSolvable RM
    have hcopAmbient :
        Nat.Coprime (Nat.card H₀) (Nat.card W₁) :=
      ((Ptype_Fcore_coprime ctx).coprime_dvd_left
        (Subgroup.card_dvd_of_le hH₀H)).coprime_dvd_right
          (Subgroup.card_dvd_of_le (show W₁ ≤ U ⊔ W₁ from le_sup_right))
    have hcop : Nat.Coprime (Nat.card NM) (Nat.card RM) := by
      simpa [NM, RM, MathlibSupport.natCard_subgroupOf_eq hH₀M,
        MathlibSupport.natCard_subgroupOf_eq hW₁M] using hcopAmbient
    have hzcent : qM hM ∈
        centralizerWithin (HM.map qM) (RM.map qM) := by
      refine ⟨⟨hM, h.property, rfl⟩, ?_⟩
      intro r hr
      rcases hr with ⟨rM, hrRM, hrEq⟩
      let w : W₁ := ⟨((rM : M) : G), hrRM⟩
      have hfixed := hzfix w
      change ptypeW₁FactorAction ctx w
          (QuotientGroup.mk' (H₀.subgroupOf H) h) =
        QuotientGroup.mk' (H₀.subgroupOf H) h at hfixed
      rw [ptypeW₁FactorAction,
        subgroupConjugationFactorHom_apply_mk] at hfixed
      have hfactorEq :
          QuotientGroup.mk' (H₀.subgroupOf H)
              ⟨(w : G) * (h : G) * (w : G)⁻¹,
                (W₁_normalizes_Fcore_factorFacts ctx w.property h).mp
                  h.property⟩ =
            QuotientGroup.mk' (H₀.subgroupOf H) h := hfixed
      change
          ((⟨(w : G) * (h : G) * (w : G)⁻¹,
              (W₁_normalizes_Fcore_factorFacts ctx w.property h).mp
                h.property⟩ : H) : H ⧸ (H₀.subgroupOf H)) =
            (h : H ⧸ (H₀.subgroupOf H)) at hfactorEq
      have hdiffH₀ :
          ((w : G) * (h : G) * (w : G)⁻¹)⁻¹ * (h : G) ∈ H₀ :=
        by
          have hdiffSub :
              (⟨(w : G) * (h : G) * (w : G)⁻¹,
                (W₁_normalizes_Fcore_factorFacts ctx w.property h).mp
                  h.property⟩ : H)⁻¹ * h ∈ H₀.subgroupOf H :=
            QuotientGroup.eq.mp hfactorEq
          exact hdiffSub
      have hconjM :
          qM (rM * hM * rM⁻¹) = qM hM := by
        apply QuotientGroup.eq.mpr
        exact hdiffH₀
      rw [← hrEq]
      change qM rM * qM hM = qM hM * qM rM
      calc
        qM rM * qM hM =
            (qM rM * qM hM * (qM rM)⁻¹) * qM rM := by group
        _ = qM hM * qM rM := by
          rw [← map_inv, ← map_mul, ← map_mul, hconjM]
    have hmapCent :=
      map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        (N := NM) (Y := HM) (R := RM) hNMHM hcop
    rw [← hmapCent] at hzcent
    rcases hzcent with ⟨cM, hcM, hqc⟩
    let c : H := ⟨((cM : M) : G), hcM.1⟩
    have hcCent : (c : G) ∈ centralizerWithin H W₁ := by
      refine ⟨c.property, ?_⟩
      intro w hw
      let wM : M := ⟨w, hW₁M hw⟩
      have hwRM : wM ∈ RM := hw
      exact congrArg Subtype.val (hcM.2 wM hwRM)
    have hcW₂ : (c : G) ∈ W₂ := by
      rw [← hcent]
      exact hcCent
    let cW₂ : W₂ := ⟨(c : G), hcW₂⟩
    refine ⟨cW₂, ?_⟩
    apply QuotientGroup.eq.mpr
    have hdiffM : (cM : M)⁻¹ * hM ∈ NM :=
      QuotientGroup.eq.mp hqc
    exact hdiffM
  · rintro z ⟨w₂, rfl⟩
    apply (FixedPoints.mem_subgroup W₁ (ptypeFCoreFactor ctx)
      ((ptypeW₂FactorMap_factorFacts ctx) w₂)).mpr
    intro w₁
    change ptypeW₁FactorAction ctx w₁
        ((ptypeW₂FactorMap_factorFacts ctx) w₂) =
      (ptypeW₂FactorMap_factorFacts ctx) w₂
    change ptypeW₁FactorAction ctx w₁
        (QuotientGroup.mk' (H₀.subgroupOf H)
          ⟨(w₂ : G), W₂_le_Fcore_factorFacts ctx w₂.property⟩) =
      QuotientGroup.mk' (H₀.subgroupOf H)
        ⟨(w₂ : G), W₂_le_Fcore_factorFacts ctx w₂.property⟩
    rw [ptypeW₁FactorAction,
      subgroupConjugationFactorHom_apply_mk]
    apply congrArg (QuotientGroup.mk' (H₀.subgroupOf H))
    apply Subtype.ext
    have hw₂Cent : (w₂ : G) ∈ centralizerWithin H W₁ := by
      rw [hcent]
      exact w₂.property
    have hcomm := hw₂Cent.2 (w₁ : G) w₁.property
    change (w₁ : G) * (w₂ : G) * (w₁ : G)⁻¹ = (w₂ : G)
    calc
      (w₁ : G) * (w₂ : G) * (w₁ : G)⁻¹ =
          (w₂ : G) * (w₁ : G) * (w₁ : G)⁻¹ := by rw [hcomm]
      _ = (w₂ : G) := by simp

/-! ## Elementary structure and joint minimality -/

/-- The three conclusions of `PFsection9.v: Ptype_Fcore_factor_facts`. -/
structure PTypeFCoreFactorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) : Prop where
  compl_kernel_ne : Ptype_Fcompl_kernel ctx ≠ U
  fixed_factor_card :
    Nat.card (ptypeW₂Factor ctx) = ptypeFactorPrime ctx
  factor_card :
    Nat.card (ptypeFCoreFactor ctx) =
      ptypeFactorPrime ctx ^ Nat.card W₁

/-- The selected chief factor is elementary abelian at its least prime
divisor. -/
theorem ptypeFCoreFactor_elementary
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    IsElementaryAbelianGroup (ptypeFactorPrime ctx)
      (ptypeFCoreFactor ctx) := by
  classical
  let H := Fitting_core M
  let H₀ := Ptype_Fcore_kernel ctx
  let HM : Subgroup M := H.subgroupOf M
  let NM : Subgroup M := H₀.subgroupOf M
  have hH₀H : H₀ ≤ H := (Ptype_Fcore_kernel_lt ctx).le
  have hHM : H ≤ M := Fcore_sub M
  have hH₀M : H₀ ≤ M := Ptype_Fcore_kernel_le_M ctx
  have hNMHM : NM ≤ HM := by
    intro x hx
    exact hH₀H hx
  letI : NM.Normal := Ptype_Fcore_kernel_normal_M ctx
  letI : HM.Normal := Fcore_normal M
  let qM : M →* M ⧸ NM := QuotientGroup.mk' NM
  have hminImage : IsMinimalNormal (HM.map qM) := by
    refine ⟨?_, inferInstance, ?_⟩
    · intro hbot
      have hleKer : HM ≤ qM.ker :=
        (Subgroup.map_eq_bot_iff HM).mp hbot
      have hleNM : HM ≤ NM := by
        simpa [qM, QuotientGroup.ker_mk'] using hleKer
      have hHH₀ : H ≤ H₀ := by
        intro h hh
        exact hleNM (show (⟨h, hHM hh⟩ : M) ∈ HM from hh)
      exact (not_le_of_gt (Ptype_Fcore_kernel_lt ctx)) hHH₀
    · intro L hLnormal hLle hLne
      let R : Subgroup M := L.comap qM
      have hkerR : qM.ker ≤ R := by
        intro x hx
        change qM x ∈ L
        rw [MonoidHom.mem_ker.mp hx]
        exact L.one_mem
      have hNMR : NM ≤ R := by
        simpa [qM, QuotientGroup.ker_mk'] using hkerR
      have hkerHM : qM.ker ≤ HM := by
        simpa [qM, QuotientGroup.ker_mk'] using hNMHM
      have hRHM : R ≤ HM := by
        calc
          R ≤ (HM.map qM).comap qM := Subgroup.comap_mono hLle
          _ = HM := Subgroup.comap_map_eq_self hkerHM
      have hRnormal : R.Normal := Subgroup.Normal.comap hLnormal qM
      let A : Subgroup G := R.map M.subtype
      have hH₀A : H₀ ≤ A := by
        intro n hn
        exact ⟨(⟨n, hH₀M hn⟩ : M), hNMR hn, rfl⟩
      have hAH : A ≤ H := by
        rintro _ ⟨r, hr, rfl⟩
        exact hRHM hr
      have hAsub : A.subgroupOf M = R := by
        ext x
        constructor
        · rintro ⟨r, hr, hrx⟩
          have hrx' : r = x := Subtype.ext hrx
          exact hrx' ▸ hr
        · intro hx
          exact ⟨x, hx, rfl⟩
      have hAnormal : (A.subgroupOf M).Normal := by
        rw [hAsub]
        exact hRnormal
      rcases (Ptype_Fcore_kernel_exists ctx).1.2.2.2.2
          A hH₀A hAH hAnormal with hA | hA
      · exfalso
        apply hLne
        have hRN : R = NM := by
          apply Subgroup.map_injective M.subtype_injective
          calc
            R.map M.subtype = A := rfl
            _ = H₀ := hA
            _ = NM.map M.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hH₀M).symm
        calc
          L = R.map qM :=
            (Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective NM) L).symm
          _ = NM.map qM := congrArg (Subgroup.map qM) hRN
          _ = ⊥ := QuotientGroup.map_mk'_self NM
      · have hRHM_eq : R = HM := by
          apply Subgroup.map_injective M.subtype_injective
          calc
            R.map M.subtype = A := rfl
            _ = H := hA
            _ = HM.map M.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hHM).symm
        have hImageEq : HM.map qM = L := by
          calc
            HM.map qM = R.map qM :=
              congrArg (Subgroup.map qM) hRHM_eq.symm
            _ = L := Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective NM) L
        exact hImageEq.le
  have hchief : IsChiefFactor NM HM :=
    ⟨hNMHM, inferInstance, hminImage⟩
  letI : IsSolvable M := mmax_sol ctx.maxM
  obtain ⟨r, hr, hrP, hrPow⟩ :=
    hchief.exists_prime_isPGroup_pow_eq_one
  letI : Fact r.Prime := ⟨hr⟩
  let toHM : H →* HM :=
    { toFun := fun h ↦ ⟨⟨(h : G), hHM h.property⟩, h.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have htoHM : Function.Surjective toHM := by
    intro h
    exact ⟨⟨(((h : HM) : M) : G), h.property⟩, rfl⟩
  let f : H →* HM.map qM := (qM.subgroupMap HM).comp toHM
  have hf : Function.Surjective f :=
    (qM.subgroupMap_surjective HM).comp htoHM
  have hfker : H₀.subgroupOf H = f.ker := by
    ext h
    rw [MonoidHom.mem_ker]
    constructor
    · intro hh
      apply Subtype.ext
      exact QuotientGroup.eq_one_iff (toHM h : M) |>.mpr hh
    · intro hh
      have hh' := congrArg Subtype.val hh
      exact QuotientGroup.eq_one_iff (toHM h : M) |>.mp hh'
  let e : ptypeFCoreFactor ctx ≃* HM.map qM :=
    QuotientGroup.liftEquiv (H₀.subgroupOf H) hf hfker
  have hElemImage : IsElementaryAbelianGroup r (HM.map qM) :=
    ⟨hrP, hminImage.isMulCommutative, hrPow⟩
  have hElem : IsElementaryAbelianGroup r (ptypeFCoreFactor ctx) := by
    letI : IsMulCommutative (HM.map qM) := hElemImage.commutative
    refine
      { isPGroup := hElemImage.isPGroup.of_equiv e.symm
        commutative := ?_
        pow_eq_one := ?_ }
    · exact isMulCommutative_iff.mpr fun x y ↦ by
        apply e.injective
        simpa only [map_mul] using (mul_comm' (e x) (e y))
    · intro x
      apply e.injective
      simpa using hElemImage.pow_eq_one (e x)
  obtain ⟨n, hn⟩ := hElem.isPGroup.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro hn0
    subst n
    have hcardOne : Nat.card (ptypeFCoreFactor ctx) = 1 := by
      simpa using hn
    have hcardGt : 1 < Nat.card (ptypeFCoreFactor ctx) :=
      Finite.one_lt_card_iff_nontrivial.mpr
        (QuotientGroup.nontrivial_iff.mpr (by
          intro htop
          exact (not_le_of_gt (Ptype_Fcore_kernel_lt ctx))
            (Subgroup.subgroupOf_eq_top.mp htop)))
    omega
  have hprimeEq : ptypeFactorPrime ctx = r := by
    unfold ptypeFactorPrime
    rw [hn, hr.pow_minFac hn0]
  simpa [hprimeEq] using hElem

/-- A subgroup of the chief factor invariant under both complement actions is
trivial or the whole factor. -/
theorem ptypeFCoreFactor_joint_minimal
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (L : Subgroup (ptypeFCoreFactor ctx))
    (hU : IsInvariantUnderMulAutAction (ptypeFCoreAction ctx) L)
    (hW : IsInvariantUnderMulAutAction (ptypeW₁FactorAction ctx) L) :
    L = ⊥ ∨ L = ⊤ := by
  classical
  let H := Fitting_core M
  let H₀ := Ptype_Fcore_kernel ctx
  let N : Subgroup H := H₀.subgroupOf H
  let qH : H →* ptypeFCoreFactor ctx := QuotientGroup.mk' N
  let B : Subgroup H := L.comap qH
  let A : Subgroup G := B.map H.subtype
  have hH₀H : H₀ ≤ H := (Ptype_Fcore_kernel_lt ctx).le
  have hAH : A ≤ H := Subgroup.map_subtype_le B
  have hH₀A : H₀ ≤ A := by
    intro n hn
    let nH : H := ⟨n, hH₀H hn⟩
    refine ⟨nH, ?_, rfl⟩
    change qH nH ∈ L
    have hqn : qH nH = 1 :=
      QuotientGroup.eq_one_iff nH |>.mpr hn
    rw [hqn]
    exact L.one_mem
  have hAsub : A.subgroupOf H = B := by
    ext x
    constructor
    · rintro ⟨b, hb, hbx⟩
      have hbx' : b = x := Subtype.ext hbx
      exact hbx' ▸ hb
    · intro hx
      exact ⟨x, hx, rfl⟩
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    (ptypeFCoreFactor_elementary ctx).commutative
  letI : L.Normal := by infer_instance
  have hBnormal : B.Normal := Subgroup.Normal.comap inferInstance qH
  have hAnormalH : (A.subgroupOf H).Normal := by
    rw [hAsub]
    exact hBnormal
  have hHnormA : H ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hAnormalH
  have hUnormA : U ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro u hu a ha
    let uU : U := ⟨u, hu⟩
    let aH : H := ⟨a, hAH ha⟩
    have haB : aH ∈ B := by
      rw [← hAsub]
      exact ha
    have hqaL : qH aH ∈ L := haB
    let uaH : H :=
      ⟨u * a * u⁻¹,
        (U_normalizes_Fcore_factorFacts ctx hu a).mp (hAH ha)⟩
    have hactL : ptypeFCoreAction ctx uU (qH aH) ∈ L := by
      rw [← hU uU]
      exact ⟨qH aH, hqaL, rfl⟩
    change qH uaH ∈ L at hactL
    exact ⟨uaH, hactL, rfl⟩
  have hWnormA : W₁ ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro w hw a ha
    let wW₁ : W₁ := ⟨w, hw⟩
    let aH : H := ⟨a, hAH ha⟩
    have haB : aH ∈ B := by
      rw [← hAsub]
      exact ha
    have hqaL : qH aH ∈ L := haB
    let waH : H :=
      ⟨w * a * w⁻¹,
        (W₁_normalizes_Fcore_factorFacts ctx hw a).mp (hAH ha)⟩
    have hactL : ptypeW₁FactorAction ctx wW₁ (qH aH) ∈ L := by
      rw [← hW wW₁]
      exact ⟨qH aH, hqaL, rfl⟩
    change qH waH ∈ L at hactL
    exact ⟨waH, hactL, rfl⟩
  have hMnormA : M ≤ Subgroup.normalizer (A : Set G) := by
    rw [← semidirect_sup_eq_factorFacts (Ptype_Fcore_sdprod ctx)]
    exact sup_le hHnormA (sup_le hUnormA hWnormA)
  have hAnormalM : (A.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hMnormA
  have hmapPre : B.map qH = L := by
    dsimp [B]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N) L
  rcases (Ptype_Fcore_kernel_exists ctx).1.2.2.2.2
      A hH₀A hAH hAnormalM with hA | hA
  · left
    have hBN : B = N := by
      apply Subgroup.map_injective H.subtype_injective
      calc
        B.map H.subtype = A := rfl
        _ = H₀ := hA
        _ = N.map H.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hH₀H).symm
    calc
      L = B.map qH := hmapPre.symm
      _ = N.map qH := congrArg (Subgroup.map qH) hBN
      _ = ⊥ := QuotientGroup.map_mk'_self N
  · right
    have htopMap : (⊤ : Subgroup H).map H.subtype = H :=
      (MonoidHom.range_eq_map H.subtype).symm.trans H.range_subtype
    have hBtop : B = ⊤ := by
      apply Subgroup.map_injective H.subtype_injective
      calc
        B.map H.subtype = A := rfl
        _ = H := hA
        _ = (⊤ : Subgroup H).map H.subtype := htopMap.symm
    calc
      L = B.map qH := hmapPre.symm
      _ = (⊤ : Subgroup H).map qH :=
        congrArg (Subgroup.map qH) hBtop
      _ = ⊤ := Subgroup.map_top_of_surjective qH
        (QuotientGroup.mk'_surjective N)

/-! ## Fixed points and cardinalities -/

private theorem U_fixed_eq_one_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (z : ptypeFCoreFactor ctx)
    (hz : ∀ u : U, ptypeFCoreAction ctx u z = z) :
    z = 1 := by
  classical
  let H := Fitting_core M
  let H₀ := Ptype_Fcore_kernel ctx
  obtain ⟨h, rfl⟩ :=
    QuotientGroup.mk'_surjective (H₀.subgroupOf H) z
  let HM : Subgroup M := H.subgroupOf M
  let NM : Subgroup M := H₀.subgroupOf M
  let RM : Subgroup M := U.subgroupOf M
  have hH₀H : H₀ ≤ H := (Ptype_Fcore_kernel_lt ctx).le
  have hNMHM : NM ≤ HM := by
    intro x hx
    exact hH₀H hx
  letI : NM.Normal := Ptype_Fcore_kernel_normal_M ctx
  let qM : M →* M ⧸ NM := QuotientGroup.mk' NM
  let hM : M := ⟨(h : G), Fcore_sub M h.property⟩
  letI : IsSolvable M := mmax_sol ctx.maxM
  letI : IsSolvable RM := isSolvable_subgroup_of_isSolvable RM
  have hcopAmbient : Nat.Coprime (Nat.card H₀) (Nat.card U) :=
    ((Ptype_Fcore_coprime ctx).coprime_dvd_left
      (Subgroup.card_dvd_of_le hH₀H)).coprime_dvd_right
        (Subgroup.card_dvd_of_le (show U ≤ U ⊔ W₁ from le_sup_left))
  have hH₀M : H₀ ≤ M := Ptype_Fcore_kernel_le_M ctx
  have hUM : U ≤ M := U_le_M_factorFacts ctx
  have hcop : Nat.Coprime (Nat.card NM) (Nat.card RM) := by
    simpa [NM, RM,
      MathlibSupport.natCard_subgroupOf_eq hH₀M,
      MathlibSupport.natCard_subgroupOf_eq hUM] using
        hcopAmbient
  have hzcent : qM hM ∈ centralizerWithin (HM.map qM) (RM.map qM) := by
    refine ⟨⟨hM, h.property, rfl⟩, ?_⟩
    intro r hr
    rcases hr with ⟨rM, hrRM, hrEq⟩
    let u : U := ⟨((rM : M) : G), hrRM⟩
    have hfixed := hz u
    rw [ptypeFCoreAction,
      subgroupConjugationFactorHom_apply_mk] at hfixed
    change
        ((⟨(u : G) * (h : G) * (u : G)⁻¹,
            (U_normalizes_Fcore_factorFacts ctx u.property h).mp
              h.property⟩ : H) : H ⧸ (H₀.subgroupOf H)) =
          (h : H ⧸ (H₀.subgroupOf H)) at hfixed
    have hdiffH₀ :
        ((u : G) * (h : G) * (u : G)⁻¹)⁻¹ * (h : G) ∈ H₀ :=
      by
        have hdiffSub :
            (⟨(u : G) * (h : G) * (u : G)⁻¹,
              (U_normalizes_Fcore_factorFacts ctx u.property h).mp
                h.property⟩ : H)⁻¹ * h ∈ H₀.subgroupOf H :=
          QuotientGroup.eq.mp hfixed
        exact hdiffSub
    have hconjM : qM (rM * hM * rM⁻¹) = qM hM := by
      apply QuotientGroup.eq.mpr
      exact hdiffH₀
    rw [← hrEq]
    change qM rM * qM hM = qM hM * qM rM
    calc
      qM rM * qM hM =
          (qM rM * qM hM * (qM rM)⁻¹) * qM rM := by group
      _ = qM hM * qM rM := by
        rw [← map_inv, ← map_mul, ← map_mul, hconjM]
  have hmapCent :=
    map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
      (N := NM) (Y := HM) (R := RM) hNMHM hcop
  rw [← hmapCent] at hzcent
  rcases hzcent with ⟨cM, hcM, hqc⟩
  have hcH₀ : ((cM : M) : G) ∈ H₀ := by
    apply (Ptype_Fcore_kernel_exists ctx).2
    refine ⟨hcM.1, ?_⟩
    intro u hu
    let uM : M := ⟨u, U_le_M_factorFacts ctx hu⟩
    exact congrArg Subtype.val (hcM.2 uM hu)
  have hcOne : qM cM = 1 :=
    QuotientGroup.eq_one_iff cM |>.mpr hcH₀
  have hhOne : qM hM = 1 := hqc.symm.trans hcOne
  apply QuotientGroup.eq_one_iff h |>.mpr
  exact QuotientGroup.eq_one_iff hM |>.mp hhOne

private theorem complement_kernel_ne_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Ptype_Fcompl_kernel ctx ≠ U := by
  intro hCU
  have hkerTop : (ptypeFCoreAction ctx).ker = ⊤ := by
    apply top_unique
    intro u _
    have huC : (u : G) ∈ Ptype_Fcompl_kernel ctx := by
      rw [hCU]
      exact u.property
    rcases huC with ⟨v, hv, hvu⟩
    have hvEq : v = u := by
      apply Subtype.ext
      exact hvu
    rwa [hvEq] at hv
  letI : Nontrivial (ptypeFCoreFactor ctx) :=
    QuotientGroup.nontrivial_iff.mpr (by
      intro htop
      exact (not_le_of_gt (Ptype_Fcore_kernel_lt ctx))
        (Subgroup.subgroupOf_eq_top.mp htop))
  obtain ⟨z, hz⟩ := exists_ne (1 : ptypeFCoreFactor ctx)
  apply hz
  apply U_fixed_eq_one_factorFacts ctx z
  intro u
  have huKer : u ∈ (ptypeFCoreAction ctx).ker := by
    rw [hkerTop]
    trivial
  have huOne : ptypeFCoreAction ctx u = 1 := MonoidHom.mem_ker.mp huKer
  rw [huOne]
  rfl

private theorem ptypeW₂Factor_cyclic_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    IsCyclic (ptypeW₂Factor ctx) := by
  letI : IsCyclic W₂ := ctx.typeP.2.2.2.1.1
  have hcyclic : IsCyclic (ptypeW₂FactorMap_factorFacts ctx).range :=
    isCyclic_of_surjective (ptypeW₂FactorMap_factorFacts ctx).rangeRestrict
      (MonoidHom.rangeRestrict_surjective
        (ptypeW₂FactorMap_factorFacts ctx))
  rw [ptypeW₂Factor_eq_range_factorFacts ctx]
  exact hcyclic

private theorem ptypeW₂Factor_elementary_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    IsElementaryAbelianGroup (ptypeFactorPrime ctx)
      (ptypeW₂Factor ctx) := by
  have hE := ptypeFCoreFactor_elementary ctx
  letI : IsMulCommutative (ptypeFCoreFactor ctx) := hE.commutative
  refine
    { isPGroup := hE.isPGroup.to_subgroup (ptypeW₂Factor ctx)
      commutative := isMulCommutative_iff.mpr ?_
      pow_eq_one := ?_ }
  · intro x y
    apply Subtype.ext
    exact mul_comm' (x : ptypeFCoreFactor ctx) (y : ptypeFCoreFactor ctx)
  · intro x
    apply Subtype.ext
    exact hE.pow_eq_one (x : ptypeFCoreFactor ctx)

private theorem ptypeW₂FactorMap_ker_map_eq_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (ptypeW₂FactorMap_factorFacts ctx).ker.map W₂.subtype =
      centralizerWithin (Ptype_Fcore_kernel ctx) W₁ := by
  let H := Fitting_core M
  let H₀ := Ptype_Fcore_kernel ctx
  have hcent : centralizerWithin H W₁ = W₂ := by
    simpa [H] using
      typeP_cent_core_compl M U W W₁ W₂ ctx.defW ctx.typeP
  ext x
  constructor
  · rintro ⟨w₂, hwKer, rfl⟩
    have hwH₀ : (w₂ : G) ∈ H₀ := by
      have hwOne := MonoidHom.mem_ker.mp hwKer
      change QuotientGroup.mk' (H₀.subgroupOf H)
          ⟨(w₂ : G), W₂_le_Fcore_factorFacts ctx w₂.property⟩ = 1 at hwOne
      exact QuotientGroup.eq_one_iff
        (⟨(w₂ : G), W₂_le_Fcore_factorFacts ctx w₂.property⟩ : H) |>.mp
          hwOne
    refine ⟨hwH₀, ?_⟩
    have hwCent : (w₂ : G) ∈ centralizerWithin H W₁ := by
      rw [hcent]
      exact w₂.property
    exact hwCent.2
  · intro hx
    have hxCentH : x ∈ centralizerWithin H W₁ :=
      ⟨(Ptype_Fcore_kernel_lt ctx).le hx.1, hx.2⟩
    have hxW₂ : x ∈ W₂ := by
      rw [← hcent]
      exact hxCentH
    let xW₂ : W₂ := ⟨x, hxW₂⟩
    refine ⟨xW₂, ?_, rfl⟩
    apply MonoidHom.mem_ker.mpr
    change QuotientGroup.mk' (H₀.subgroupOf H)
      ⟨x, W₂_le_Fcore_factorFacts ctx hxW₂⟩ = 1
    exact QuotientGroup.eq_one_iff
      (⟨x, W₂_le_Fcore_factorFacts ctx hxW₂⟩ : H) |>.mpr hx.1

private theorem ptypeFCore_factor_card_factorFacts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Nat.card (ptypeFCoreFactor ctx) =
      Nat.card (ptypeW₂Factor ctx) ^ Nat.card W₁ := by
  let H := Fitting_core M
  let H₀ := Ptype_Fcore_kernel ctx
  let J := U ⊔ W₁
  let q := Nat.card W₁
  have hH₀H : H₀ ≤ H := (Ptype_Fcore_kernel_lt ctx).le
  have hcopH₀J : Nat.Coprime (Nat.card H₀) (Nat.card J) :=
    (Ptype_Fcore_coprime ctx).coprime_dvd_left
      (Subgroup.card_dvd_of_le hH₀H)
  have hfixH := frobeniusWielandtCard_factorFacts
    (Ptype_compl_Frobenius ctx)
    (Fcore_sub M) (Fcore_normal M)
    (U_le_M_factorFacts ctx) (W₁_le_M_factorFacts ctx)
    (Ptype_Fcore_coprime ctx)
    (by
      letI : IsSolvable M := mmax_sol ctx.maxM
      exact isSolvable_of_injective (Subgroup.inclusion (Fcore_sub M))
        (Subgroup.inclusion_injective (Fcore_sub M)))
  have hfixH₀ := frobeniusWielandtCard_factorFacts
    (Ptype_compl_Frobenius ctx)
    (Ptype_Fcore_kernel_le_M ctx) (Ptype_Fcore_kernel_normal_M ctx)
    (U_le_M_factorFacts ctx) (W₁_le_M_factorFacts ctx)
    hcopH₀J
    (by
      letI : IsSolvable M := mmax_sol ctx.maxM
      exact isSolvable_of_injective
        (Subgroup.inclusion (Ptype_Fcore_kernel_le_M ctx))
        (Subgroup.inclusion_injective (Ptype_Fcore_kernel_le_M ctx)))
  have hcentU : centralizerWithin H₀ U = centralizerWithin H U := by
    apply le_antisymm (centralizerWithin_mono_left hH₀H)
    intro x hx
    exact ⟨(Ptype_Fcore_kernel_exists ctx).2 hx, hx.2⟩
  have hcentJ : centralizerWithin H₀ J = centralizerWithin H J := by
    apply le_antisymm (centralizerWithin_mono_left hH₀H)
    intro x hx
    have hxU : x ∈ centralizerWithin H U :=
      (centralizerWithin_antitone_right
        (show U ≤ J from le_sup_left)) hx
    exact ⟨(Ptype_Fcore_kernel_exists ctx).2 hxU, hx.2⟩
  have hcardKerCent :
      Nat.card (centralizerWithin H₀ W₁) =
        Nat.card (ptypeW₂FactorMap_factorFacts ctx).ker := by
    have hcard := Subgroup.card_map_of_injective
      (K := (ptypeW₂FactorMap_factorFacts ctx).ker)
      W₂.subtype_injective
    rw [ptypeW₂FactorMap_ker_map_eq_factorFacts ctx] at hcard
    exact hcard
  have hcardFactor :
      Nat.card H = Nat.card (ptypeFCoreFactor ctx) * Nat.card H₀ := by
    simpa [H, H₀, ptypeFCoreFactor,
      MathlibSupport.natCard_subgroupOf_eq hH₀H, Nat.mul_comm] using
        (Subgroup.card_eq_card_quotient_mul_card_subgroup
          (H₀.subgroupOf H))
  have hcardW₂ :
      Nat.card W₂ = Nat.card (ptypeW₂FactorMap_factorFacts ctx).ker *
        Nat.card (ptypeW₂Factor ctx) := by
    have hcard := (ptypeW₂FactorMap_factorFacts ctx).ker.card_mul_index
    rw [Subgroup.index_ker,
      ← ptypeW₂Factor_eq_range_factorFacts ctx] at hcard
    exact hcard.symm
  have hfixH' :
      Nat.card H * Nat.card (centralizerWithin H J) ^ q =
        Nat.card (centralizerWithin H U) * Nat.card W₂ ^ q := by
    simpa [H, J, q,
      typeP_cent_core_compl M U W W₁ W₂ ctx.defW ctx.typeP] using hfixH
  have hfixH₀' :
      Nat.card H₀ * Nat.card (centralizerWithin H J) ^ q =
        Nat.card (centralizerWithin H U) *
          Nat.card (ptypeW₂FactorMap_factorFacts ctx).ker ^ q := by
    rw [← hcentJ, ← hcentU, ← hcardKerCent]
    exact hfixH₀
  have hmul :
      Nat.card (ptypeFCoreFactor ctx) *
          (Nat.card (centralizerWithin H U) *
            Nat.card (ptypeW₂FactorMap_factorFacts ctx).ker ^ q) =
        Nat.card (ptypeW₂Factor ctx) ^ q *
          (Nat.card (centralizerWithin H U) *
            Nat.card (ptypeW₂FactorMap_factorFacts ctx).ker ^ q) := by
    calc
      Nat.card (ptypeFCoreFactor ctx) *
          (Nat.card (centralizerWithin H U) *
            Nat.card (ptypeW₂FactorMap_factorFacts ctx).ker ^ q) =
          Nat.card (ptypeFCoreFactor ctx) *
            (Nat.card H₀ * Nat.card (centralizerWithin H J) ^ q) := by
              rw [hfixH₀']
      _ = Nat.card H * Nat.card (centralizerWithin H J) ^ q := by
            rw [hcardFactor]
            ac_rfl
      _ = Nat.card (centralizerWithin H U) * Nat.card W₂ ^ q := hfixH'
      _ = Nat.card (ptypeW₂Factor ctx) ^ q *
          (Nat.card (centralizerWithin H U) *
            Nat.card (ptypeW₂FactorMap_factorFacts ctx).ker ^ q) := by
            rw [hcardW₂, mul_pow]
            ac_rfl
  exact Nat.mul_right_cancel
    (mul_pos Nat.card_pos (pow_pos Nat.card_pos q)) hmul

private theorem factor_fixedpoint_package
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Ptype_Fcompl_kernel ctx ≠ U ∧
      Nat.card (ptypeFCoreFactor ctx) =
        Nat.card (ptypeW₂Factor ctx) ^ Nat.card W₁ ∧
      IsElementaryAbelianGroup (ptypeFactorPrime ctx)
        (ptypeW₂Factor ctx) ∧
      IsCyclic (ptypeW₂Factor ctx) ∧
      ptypeW₂Factor ctx ≠ ⊥ := by
  have hfactor := ptypeFCore_factor_card_factorFacts ctx
  have hfixedNe : ptypeW₂Factor ctx ≠ ⊥ := by
    intro hbot
    have hfixedCard : Nat.card (ptypeW₂Factor ctx) = 1 := by
      rw [hbot]
      simp
    have hfactorCard : Nat.card (ptypeFCoreFactor ctx) = 1 := by
      rw [hfactor, hfixedCard]
      simp
    have hfactorGt : 1 < Nat.card (ptypeFCoreFactor ctx) :=
      Finite.one_lt_card_iff_nontrivial.mpr
        (QuotientGroup.nontrivial_iff.mpr (by
          intro htop
          exact (not_le_of_gt (Ptype_Fcore_kernel_lt ctx))
            (Subgroup.subgroupOf_eq_top.mp htop)))
    omega
  exact ⟨complement_kernel_ne_factorFacts ctx, hfactor,
    ptypeW₂Factor_elementary_factorFacts ctx,
    ptypeW₂Factor_cyclic_factorFacts ctx, hfixedNe⟩

private theorem natCard_eq_prime_of_elementary_cyclic
    {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hX : IsElementaryAbelianGroup p X)
    (hcyclic : IsCyclic X) (hcard : 1 < Nat.card X) :
    Nat.card X = p := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic X := hcyclic
  have hle : Nat.card X ≤ p := by
    letI := Fintype.ofFinite X
    classical
    rw [Nat.card_eq_fintype_card]
    simpa only [hX.pow_eq_one, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := X) hp.pos)
  obtain ⟨n, hn⟩ := hX.isPGroup.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro hn0
    subst n
    simp at hn
    exact (ne_of_gt hcard) hn
  have hpdiv : p ∣ Nat.card X := by
    rw [hn]
    exact dvd_pow_self p hn0
  exact le_antisymm hle
    (Nat.le_of_dvd (Nat.zero_lt_of_lt hcard) hpdiv)

/-- `PFsection9.v: Ptype_Fcore_factor_facts`, Peterfalvi (9.6). -/
theorem Ptype_Fcore_factor_facts
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    PTypeFCoreFactorFacts ctx := by
  obtain ⟨hCne, hfactor, helem, hcyclic, hfixedNe⟩ :=
    factor_fixedpoint_package ctx
  have hfixedCard :
      Nat.card (ptypeW₂Factor ctx) = ptypeFactorPrime ctx :=
    natCard_eq_prime_of_elementary_cyclic
      (ptypeFactorPrime_prime ctx) helem hcyclic
        ((ptypeW₂Factor ctx).one_lt_card_iff_ne_bot.mpr hfixedNe)
  refine ⟨hCne, hfixedCard, ?_⟩
  rw [hfactor, hfixedCard]

/-- The image of `W₂` modulo an ambient normal subgroup cutting the F-core
at the selected lower term has order `ptypeFactorPrime ctx`. -/
theorem ptypeW₂_quotient_image_card
    {M U W W₁ W₂ K : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    [hKnormal : (K.subgroupOf M).Normal]
    (hKder : K ≤ derivedWithin M)
    (hKcap : K ⊓ Fitting_core M = Ptype_Fcore_kernel ctx) :
    Nat.card
        ((W₂.subgroupOf M).map
          (QuotientGroup.mk' (K.subgroupOf M))) =
      ptypeFactorPrime ctx := by
  classical
  let H := Fitting_core M
  let H₀ := Ptype_Fcore_kernel ctx
  let KM : Subgroup M := K.subgroupOf M
  let qK : M →* M ⧸ KM := QuotientGroup.mk' KM
  have hKM : K ≤ M :=
    hKder.trans (Subgroup.map_subtype_le (_root_.commutator M))
  have hW₂H : W₂ ≤ H := W₂_le_Fcore_factorFacts ctx
  have hW₂M : W₂ ≤ M := hW₂H.trans (Fcore_sub M)
  let iM : W₂ →* M := Subgroup.inclusion hW₂M
  let fK : W₂ →* M ⧸ KM := qK.comp iM
  have hrangeK : fK.range = (W₂.subgroupOf M).map qK := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact
        ⟨(⟨(w : G), hW₂M w.property⟩ : M), w.property, rfl⟩
    · rintro ⟨wM, hwW₂, rfl⟩
      let w : W₂ := ⟨((wM : M) : G), hwW₂⟩
      exact ⟨w, rfl⟩
  have hker : fK.ker = (ptypeW₂FactorMap_factorFacts ctx).ker := by
    ext w
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change
      ((⟨(w : G), hW₂M w.property⟩ : M) : M ⧸ KM) = 1 ↔
        ((⟨(w : G), hW₂H w.property⟩ : H) :
          H ⧸ (H₀.subgroupOf H)) = 1
    rw [QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]
    constructor
    · intro hwK
      have hwInf : (w : G) ∈ K ⊓ H := ⟨hwK, hW₂H w.property⟩
      rw [hKcap] at hwInf
      exact hwInf
    · intro hwH₀
      have hwInf : (w : G) ∈ K ⊓ H := by
        rw [hKcap]
        exact hwH₀
      exact hwInf.1
  have hcardRanges :
      Nat.card fK.range =
        Nat.card (ptypeW₂FactorMap_factorFacts ctx).range := by
    calc
      Nat.card fK.range = fK.ker.index := (Subgroup.index_ker fK).symm
      _ = (ptypeW₂FactorMap_factorFacts ctx).ker.index :=
        congrArg Subgroup.index hker
      _ = Nat.card (ptypeW₂FactorMap_factorFacts ctx).range :=
        Subgroup.index_ker (ptypeW₂FactorMap_factorFacts ctx)
  calc
    Nat.card
        ((W₂.subgroupOf M).map
          (QuotientGroup.mk' (K.subgroupOf M))) =
        Nat.card fK.range := by
          exact Nat.card_congr
            (MulEquiv.subgroupCongr hrangeK.symm).toEquiv
    _ = Nat.card (ptypeW₂FactorMap_factorFacts ctx).range := hcardRanges
    _ = Nat.card (ptypeW₂Factor ctx) := by
      exact Nat.card_congr
        (MulEquiv.subgroupCongr
          (ptypeW₂Factor_eq_range_factorFacts ctx).symm).toEquiv
    _ = ptypeFactorPrime ctx :=
      (Ptype_Fcore_factor_facts ctx).fixed_factor_card

private theorem ptypeW₂Factor_card_dvd_W₂
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Nat.card (ptypeW₂Factor ctx) ∣ Nat.card W₂ := by
  rw [ptypeW₂Factor_eq_range_factorFacts ctx]
  exact Subgroup.card_range_dvd (ptypeW₂FactorMap_factorFacts ctx)

/-- `PFsection9.v: def_Ptype_factor_prime`. -/
theorem def_Ptype_factor_prime
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (hW₂prime : (Nat.card W₂).Prime) :
    ptypeFactorPrime ctx = Nat.card W₂ := by
  have hpdiv : ptypeFactorPrime ctx ∣ Nat.card W₂ := by
    rw [← (Ptype_Fcore_factor_facts ctx).fixed_factor_card]
    exact ptypeW₂Factor_card_dvd_W₂ ctx
  exact ((Nat.dvd_prime hW₂prime).mp hpdiv).resolve_left
    (ptypeFactorPrime_prime ctx).ne_one

/-- `PFsection9.v: typeIII_IV_core_prime`, the first assertion of
Peterfalvi (9.4)(b). -/
theorem typeIII_IV_core_prime
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (hnotII : FTtype M ≠ 2) :
    ptypeFactorPrime ctx = Nat.card W₂ := by
  have hcore := typeII_IV_core ctx
  rw [TypeIIIVCoreConclusion, if_neg hnotII] at hcore
  exact def_Ptype_factor_prime ctx hcore.1

end

end Submission.OddOrder.PF
