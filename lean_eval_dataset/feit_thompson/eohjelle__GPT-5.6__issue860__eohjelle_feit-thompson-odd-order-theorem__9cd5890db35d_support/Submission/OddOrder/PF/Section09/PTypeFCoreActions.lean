import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.MinimalNormalExistence
import Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy
import Submission.OddOrder.MathlibSupport.SubgroupConjugationFactor
import Submission.OddOrder.MathlibSupport.SubnormalMaximalNormal
import Submission.OddOrder.PF.Section09.PTypeFCoreContext

/-!
# Peterfalvi Section 9: the F-core factor and its actions

This module selects the lower term of the chief F-core factor, constructs the
actions of `U` and `W₁` on that factor, and proves the normality conclusions
of Peterfalvi (9.4)--(9.5).  The later arithmetic facts about the factor live in
the following phase.
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

/-! ## Context adapters -/

private theorem context_U_le_M
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) : U ≤ M :=
  ctx.typeP.2.1.2.1.trans ctx.typeP.1.2.2.2.1

private theorem context_W₁_le_M
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) : W₁ ≤ M :=
  ctx.typeP.1.2.1.1

private theorem context_typeII_IV
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    of_typeII_IV M U W W₁ W₂ ctx.defW :=
  compl_of_typeII_IV M U W W₁ W₂ ctx.defW ctx.maxM
    ctx.typeP ctx.not_type5

private theorem semidirect_sup_eq
    {N R K : Subgroup G} (h : IsInternalSemidirectProductIn N R K) :
    N ⊔ R = K := by
  apply le_antisymm (sup_le h.1 h.2.1)
  intro k hk
  obtain ⟨⟨n, r⟩, hnr⟩ := h.2.2.2.2 ⟨k, hk⟩
  have : (n : G) * (r : G) = k := congrArg Subtype.val hnr
  rw [← this]
  exact Subgroup.mul_mem_sup n.property r.property

/-! ## The chief F-core factor -/

private theorem centralizerWithin_normalized_by_common_normalizer
    {A B C : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) :
    A ≤ Subgroup.normalizer (centralizerWithin B C : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha x hx
  refine ⟨(hAB ha x).mp hx.1, ?_⟩
  intro c hc
  have haInvC : a⁻¹ ∈ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normalizer (C : Set G)).inv_mem (hAC ha)
  have hc' : a⁻¹ * c * a ∈ (C : Set G) := by
    simpa only [inv_inv] using (haInvC c).mp hc
  have hcomm := hx.2 (a⁻¹ * c * a) hc'
  calc
    c * (a * x * a⁻¹) =
        a * ((a⁻¹ * c * a) * x) * a⁻¹ := by group
    _ = a * (x * (a⁻¹ * c * a)) * a⁻¹ := by rw [hcomm]
    _ = (a * x * a⁻¹) * c := by group

private theorem normalClosure_image_normalized
    {H A J : Subgroup G} (hAH : A ≤ H)
    (hJH : J ≤ Subgroup.normalizer (H : Set G))
    (hJA : J ≤ Subgroup.normalizer (A : Set G)) :
    J ≤ Subgroup.normalizer
      ((Subgroup.normalClosure ((A.subgroupOf H : Subgroup H) : Set H)).map
        H.subtype : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro j hj x hx
  let AH : Subgroup H := A.subgroupOf H
  let R : Subgroup H := Subgroup.normalClosure (AH : Set H)
  rcases hx with ⟨xH, hxR, rfl⟩
  let jN : Subgroup.normalizer (H : Set G) := ⟨j, hJH hj⟩
  let phi : H →* H := (H.normalizerMonoidHom jN).toMonoidHom
  have himage : phi '' (AH : Set H) ⊆ (AH : Set H) := by
    rintro _ ⟨a, ha, rfl⟩
    change j * (a : G) * j⁻¹ ∈ A
    exact (hJA hj (a : G)).mp ha
  have hmapR : R.map phi ≤ R :=
    (Subgroup.map_normalClosure_le (AH : Set H) phi).trans
      (Subgroup.normalClosure_mono himage)
  have hxMap : phi xH ∈ R.map phi := ⟨xH, hxR, rfl⟩
  refine ⟨phi xH, hmapR hxMap, ?_⟩
  rfl

private theorem exists_proper_normal_over_centralizer
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    ∃ S : Subgroup G,
      centralizerWithin (Fitting_core M) U ≤ S ∧
      S < Fitting_core M ∧ (S.subgroupOf M).Normal := by
  classical
  let H := Fitting_core M
  let A := centralizerWithin H U
  let AH : Subgroup H := A.subgroupOf H
  let R : Subgroup H := Subgroup.normalClosure (AH : Set H)
  let S : Subgroup G := R.map H.subtype
  have hAH : A ≤ H := centralizerWithin_le_left H U
  have hUne : U ≠ ⊥ := (context_typeII_IV ctx).2.1
  have hAneH : A ≠ H := by
    intro hAH_eq
    have hnotCentral : ¬ U ≤ Subgroup.centralizer (H : Set G) :=
      (typeP_context M U W W₁ W₂ ctx.defW ctx.typeP).nontrivial_not_le_centralizer hUne
    apply hnotCentral
    rw [Subgroup.le_centralizer_iff]
    intro h hh
    have hhA : h ∈ A := by rw [hAH_eq]; exact hh
    exact hhA.2
  have hAHneTop : AH ≠ ⊤ := by
    intro htop
    apply hAneH
    exact le_antisymm hAH (Subgroup.subgroupOf_eq_top.mp htop)
  obtain ⟨B, hBcoatom, hAHB⟩ :=
    (eq_top_or_exists_le_coatom AH).resolve_left hAHneTop
  letI : Group.IsNilpotent H := inferInstance
  have hBnormal : B.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom B
      Group.normalizerCondition_of_isNilpotent hBcoatom
  letI : B.Normal := hBnormal
  have hRleB : R ≤ B := Subgroup.normalClosure_le_normal hAHB
  have hSleH : S ≤ H := Subgroup.map_subtype_le R
  have hSltH : S < H := by
    refine lt_of_le_of_ne hSleH ?_
    intro hSH
    have hRsub : S.subgroupOf H = R := by
      change (R.map H.subtype).comap H.subtype = R
      exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective R
    have hRtop : R = ⊤ := by
      rw [← hRsub, hSH]
      exact Subgroup.subgroupOf_self H
    apply hBcoatom.1
    apply top_unique
    intro b _
    exact hRleB (by rw [hRtop]; exact Subgroup.mem_top b)
  have hcentS : A ≤ S := by
    intro a ha
    let aH : H := ⟨a, hAH ha⟩
    refine ⟨aH, ?_, rfl⟩
    exact Subgroup.subset_normalClosure (show aH ∈ AH from ha)
  have hJleM : U ⊔ W₁ ≤ M :=
    sup_le (context_U_le_M ctx) (context_W₁_le_M ctx)
  have hJnormH : U ⊔ W₁ ≤ Subgroup.normalizer (H : Set G) :=
    hJleM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M))
  have hJnormU : U ⊔ W₁ ≤ Subgroup.normalizer (U : Set G) :=
    sup_le U.le_normalizer ctx.typeP.2.1.2.2.1
  have hJnormA : U ⊔ W₁ ≤ Subgroup.normalizer (A : Set G) :=
    centralizerWithin_normalized_by_common_normalizer hJnormH hJnormU
  have hJnormS : U ⊔ W₁ ≤ Subgroup.normalizer (S : Set G) := by
    simpa [S, R, AH, A, H] using
      normalClosure_image_normalized hAH hJnormH hJnormA
  have hHnormS : H ≤ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh s hs
    rcases hs with ⟨sH, hsR, rfl⟩
    let hH : H := ⟨h, hh⟩
    refine ⟨hH * sH * hH⁻¹, ?_, rfl⟩
    exact (inferInstance : R.Normal).conj_mem sH hsR hH
  have hMnormS : M ≤ Subgroup.normalizer (S : Set G) := by
    rw [← semidirect_sup_eq (Ptype_Fcore_sdprod ctx)]
    exact sup_le hHnormS hJnormS
  refine ⟨S, ?_, hSltH, ?_⟩
  · simpa [A, H] using hcentS
  · apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact hMnormS

private theorem exists_kernel_lower_term
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    ∃ H₀ : Subgroup G, IsPTypeFCoreKernel M U H₀ := by
  classical
  obtain ⟨S, hcentS, hSF, hSnormal⟩ :=
    exists_proper_normal_over_centralizer ctx
  let Good : Subgroup G → Prop := fun L ↦
    S ≤ L ∧ L < Fitting_core M ∧ (L.subgroupOf M).Normal
  have hS : Good S := ⟨le_rfl, hSF, hSnormal⟩
  letI : Finite (Subgroup G) :=
    Finite.of_injective (fun L : Subgroup G ↦ (L : Set G))
      SetLike.coe_injective
  obtain ⟨H₀, _, hH₀, hmax⟩ := Finite.exists_le_maximal (p := Good) hS
  have hminimal : IsMinimalNormalFactor H₀ (Fitting_core M) M := by
    refine ⟨hH₀.2.1, Fcore_sub M, hH₀.2.2, Fcore_normal M, ?_⟩
    intro L hH₀L hLF hLnormal
    by_cases hLFcore : L = Fitting_core M
    · exact Or.inr hLFcore
    · left
      have hLgood : Good L :=
        ⟨hH₀.1.trans hH₀L, lt_of_le_of_ne hLF hLFcore, hLnormal⟩
      exact le_antisymm (hmax hLgood hH₀L) hH₀L
  exact ⟨H₀, hminimal, hcentS.trans hH₀.1⟩

/-- `PFsection9.v: Ptype_Fcore_kernel`.

The selected lower term of a chief factor of `M` inside `Fitting_core M`
contains the fixed subgroup `C_(Fitting_core M)(U)`. -/
noncomputable def Ptype_Fcore_kernel
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) : Subgroup G :=
  Classical.choose (exists_kernel_lower_term ctx)

/-- `PFsection9.v: Ptype_Fcore_kernel_exists`, Peterfalvi (9.4). -/
theorem Ptype_Fcore_kernel_exists
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    IsPTypeFCoreKernel M U (Ptype_Fcore_kernel ctx) :=
  Classical.choose_spec (exists_kernel_lower_term ctx)

/-- The selected lower term lies properly below the F-core. -/
theorem Ptype_Fcore_kernel_lt
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Ptype_Fcore_kernel ctx < Fitting_core M :=
  (Ptype_Fcore_kernel_exists ctx).1.1

/-- The selected lower term lies in `M`. -/
theorem Ptype_Fcore_kernel_le_M
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Ptype_Fcore_kernel ctx ≤ M :=
  (Ptype_Fcore_kernel_lt ctx).le.trans (Fcore_sub M)

/-- The selected lower term is normal in `M`. -/
theorem Ptype_Fcore_kernel_normal_M
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    ((Ptype_Fcore_kernel ctx).subgroupOf M).Normal :=
  (Ptype_Fcore_kernel_exists ctx).1.2.2.1

/-- The selected lower term is normal in the F-core. -/
theorem Ptype_Fcore_kernel_normal_Fcore
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)).Normal := by
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  exact (Fcore_sub M).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Ptype_Fcore_kernel_le_M ctx)).mp
        (Ptype_Fcore_kernel_normal_M ctx))

noncomputable instance ptypeFCoreKernelNormal
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)).Normal :=
  Ptype_Fcore_kernel_normal_Fcore ctx

/-- The chief factor `H/H₀` used in Peterfalvi Sections 9--11. -/
abbrev ptypeFCoreFactor
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :=
  Fitting_core M ⧸
    (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)

private theorem U_normalizes_Fcore
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    U ≤ Subgroup.normalizer (Fitting_core M : Set G) :=
  (context_U_le_M ctx).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
      (Fcore_normal M))

private theorem U_normalizes_kernel
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    U ≤ Subgroup.normalizer (Ptype_Fcore_kernel ctx : Set G) :=
  (context_U_le_M ctx).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Ptype_Fcore_kernel_le_M ctx)).mp
        (Ptype_Fcore_kernel_normal_M ctx))

/-- Conjugation by `U` on the chief factor `H/H₀`. -/
noncomputable def ptypeFCoreAction
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    U →* MulAut (ptypeFCoreFactor ctx) :=
  subgroupConjugationFactorHom
    (Ptype_Fcore_kernel ctx) (Fitting_core M) U
    (U_normalizes_Fcore ctx) (U_normalizes_kernel ctx)

/-- `PFsection9.v: Ptype_Fcompl_kernel`, Peterfalvi Hypothesis (9.5). -/
noncomputable def Ptype_Fcompl_kernel
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) : Subgroup G :=
  (ptypeFCoreAction ctx).ker.map U.subtype

/-- The complement kernel is contained in `U`. -/
theorem Ptype_Fcompl_kernel_le
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Ptype_Fcompl_kernel ctx ≤ U :=
  Subgroup.map_subtype_le (ptypeFCoreAction ctx).ker

/-- The quotient denoted `Ubar = U/C` in the source. -/
abbrev ptypeFComplFactor
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :=
  U ⧸ (ptypeFCoreAction ctx).ker

/-- The derived subgroup of `U` acts trivially on the chosen chief factor. -/
theorem ptypeFCoreAction_commutator_le_ker
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    _root_.commutator U ≤ (ptypeFCoreAction ctx).ker := by
  intro c hc
  apply (mem_ker_subgroupConjugationFactorHom_iff
    (Ptype_Fcore_kernel ctx) (Fitting_core M) U
    (U_normalizes_Fcore ctx) (U_normalizes_kernel ctx) c).mpr
  intro h hh
  have hcDer : (c : G) ∈ derivedWithin U :=
    ⟨c, hc, rfl⟩
  have hcCent : (c : G) ∈
      Subgroup.centralizer (Fitting_core M : Set G) :=
    (typeP_context M U W W₁ W₂ ctx.defW ctx.typeP).derived_centralizes_fitting hcDer
  have hcomm : ⁅(c : G), h⁆ = 1 :=
    (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hcCent) h hh
  simpa [hcomm] using (Ptype_Fcore_kernel ctx).one_mem

/-! ## The `W₁` actions -/

private theorem W₁_normalizes_Fcore
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    W₁ ≤ Subgroup.normalizer (Fitting_core M : Set G) :=
  (context_W₁_le_M ctx).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
      (Fcore_normal M))

private theorem W₁_normalizes_kernel
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    W₁ ≤ Subgroup.normalizer (Ptype_Fcore_kernel ctx : Set G) :=
  (context_W₁_le_M ctx).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Ptype_Fcore_kernel_le_M ctx)).mp
        (Ptype_Fcore_kernel_normal_M ctx))

/-- Conjugation by `W₁` on `H/H₀`. -/
noncomputable def ptypeW₁FactorAction
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    W₁ →* MulAut (ptypeFCoreFactor ctx) :=
  subgroupConjugationFactorHom
    (Ptype_Fcore_kernel ctx) (Fitting_core M) W₁
    (W₁_normalizes_Fcore ctx) (W₁_normalizes_kernel ctx)

/-- Conjugation by `W₁` on its normalized subgroup `U`. -/
noncomputable def ptypeW₁ComplAction
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    W₁ →* MulAut U :=
  U.normalizerMonoidHom.comp
    (Subgroup.inclusion ctx.typeP.2.1.2.2.1)

/-- The fixed subgroup of `W₁` on the chief factor. -/
noncomputable def ptypeW₂Factor
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Subgroup (ptypeFCoreFactor ctx) := by
  letI : MulDistribMulAction W₁ (ptypeFCoreFactor ctx) :=
    MulDistribMulAction.compHom
      (ptypeFCoreFactor ctx) (ptypeW₁FactorAction ctx)
  exact FixedPoints.subgroup W₁ (ptypeFCoreFactor ctx)

/-- The prime `p = pdiv |Hbar|` from the source. -/
def ptypeFactorPrime
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) : ℕ :=
  Nat.minFac (Nat.card (ptypeFCoreFactor ctx))

/-- The least prime divisor of the nontrivial chief factor is prime. -/
theorem ptypeFactorPrime_prime
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (ptypeFactorPrime ctx).Prime := by
  letI : Nontrivial (ptypeFCoreFactor ctx) :=
    QuotientGroup.nontrivial_iff.mpr (by
      intro htop
      exact (not_le_of_gt (Ptype_Fcore_kernel_lt ctx))
        (Subgroup.subgroupOf_eq_top.mp htop))
  exact Nat.minFac_prime
    (ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance))

/-! ## The complement kernel and fixed cosets -/

private theorem mem_complement_kernel_iff
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) {c : G} :
    c ∈ Ptype_Fcompl_kernel ctx ↔
      c ∈ U ∧
        ∀ h : G, h ∈ Fitting_core M →
          ⁅c, h⁆ ∈ Ptype_Fcore_kernel ctx := by
  constructor
  · rintro ⟨cU, hc, rfl⟩
    refine ⟨cU.property, ?_⟩
    exact (mem_ker_subgroupConjugationFactorHom_iff
      (Ptype_Fcore_kernel ctx) (Fitting_core M) U
      (U_normalizes_Fcore ctx) (U_normalizes_kernel ctx) cU).mp hc
  · rintro ⟨hcU, hc⟩
    let cU : U := ⟨c, hcU⟩
    refine ⟨cU, ?_, rfl⟩
    exact (mem_ker_subgroupConjugationFactorHom_iff
      (Ptype_Fcore_kernel ctx) (Fitting_core M) U
      (U_normalizes_Fcore ctx) (U_normalizes_kernel ctx) cU).mpr hc

private theorem U_normalizes_complement_kernel
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    U ≤ Subgroup.normalizer (Ptype_Fcompl_kernel ctx : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro u hu c hc
  let uU : U := ⟨u, hu⟩
  obtain ⟨cU, hcKer, hc⟩ := hc
  refine ⟨uU * cU * uU⁻¹, ?_, ?_⟩
  · exact (inferInstance : (ptypeFCoreAction ctx).ker.Normal).conj_mem
      cU hcKer uU
  · change u * (cU : G) * u⁻¹ = u * c * u⁻¹
    have hc' : (cU : G) = c := hc
    rw [hc']

private theorem W₁_normalizes_complement_kernel
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    W₁ ≤ Subgroup.normalizer (Ptype_Fcompl_kernel ctx : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro w hw c hc
  have hc' := (mem_complement_kernel_iff ctx).mp hc
  apply (mem_complement_kernel_iff ctx).mpr
  refine ⟨(ctx.typeP.2.1.2.2.1 hw c).mp hc'.1, ?_⟩
  intro h hh
  have hwInv : w⁻¹ ∈ W₁ := W₁.inv_mem hw
  have hh' : w⁻¹ * h * w ∈ Fitting_core M := by
    simpa using (W₁_normalizes_Fcore ctx hwInv h).mp hh
  have hcomm := hc'.2 (w⁻¹ * h * w) hh'
  have hconj :=
    (W₁_normalizes_kernel ctx hw ⁅c, w⁻¹ * h * w⁆).mp hcomm
  rw [commutatorElement_def] at hconj ⊢
  have heq :
      w * c * w⁻¹ * h * (w * c * w⁻¹)⁻¹ * h⁻¹ =
        w * (c * (w⁻¹ * h * w) * c⁻¹ *
          (w⁻¹ * h * w)⁻¹) * w⁻¹ := by
    group
  rw [heq]
  exact hconj

private theorem complement_kernel_normal_in_join
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    ((Ptype_Fcompl_kernel ctx).subgroupOf (U ⊔ W₁)).Normal := by
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  exact sup_le (U_normalizes_complement_kernel ctx)
    (W₁_normalizes_complement_kernel ctx)

/-- A nonidentity element of `W₁` has no nontrivial fixed coset in
`U / Ptype_Fcompl_kernel`. -/
theorem ptypeFComplFactor_fixed_coset_trivial
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (w : W₁) (hw : w ≠ 1) (x : U)
    (hx : ptypeW₁ComplAction ctx w x * x⁻¹ ∈
      (ptypeFCoreAction ctx).ker) :
    x ∈ (ptypeFCoreAction ctx).ker := by
  let J := U ⊔ W₁
  let K : Subgroup J := U.subgroupOf J
  let R : Subgroup J := W₁.subgroupOf J
  let C := Ptype_Fcompl_kernel ctx
  let N : Subgroup J := C.subgroupOf J
  have hNK : N ≤ K := fun _ hy ↦ Ptype_Fcompl_kernel_le ctx hy
  letI : N.Normal := by
    dsimp [N, C, J]
    exact complement_kernel_normal_in_join ctx
  have hfrob : IsFrobeniusDecomposition K R := by
    simpa [J, K, R, PTypeFrobeniusProduct] using
      Ptype_compl_Frobenius ctx
  let r : R :=
    ⟨⟨(w : G), (show W₁ ≤ J from le_sup_right) w.property⟩,
      w.property⟩
  have hr : r ≠ 1 := by
    intro hrOne
    apply hw
    apply Subtype.ext
    simpa [r] using congrArg (fun y : R ↦ (((y : J) : G))) hrOne
  letI := hfrob.conjugationAction
  let NK : Subgroup K := N.subgroupOf K
  let phiK : K →* K := MulDistribMulAction.toMonoidHom K r
  let phiN : NK →* NK :=
    { toFun := fun n ↦
        ⟨phiK (n : K), by
          change (r : J) * ((n : K) : J) * (r : J)⁻¹ ∈ N
          exact (inferInstance : N.Normal).conj_mem
            ((n : K) : J) n.property (r : J)⟩
      map_one' := by
        apply Subtype.ext
        exact phiK.map_one
      map_mul' := fun a b ↦ by
        apply Subtype.ext
        exact phiK.map_mul a b }
  let xK : K :=
    ⟨⟨(x : G), (show U ≤ J from le_sup_left) x.property⟩,
      x.property⟩
  have hxC :
      (((ptypeW₁ComplAction ctx w x) * x⁻¹ : U) : G) ∈ C := by
    exact ⟨ptypeW₁ComplAction ctx w x * x⁻¹, hx, rfl⟩
  change ((w : G) * (x : G) * (w : G)⁻¹) * (x : G)⁻¹ ∈ C at hxC
  have hcommN : (xK / phiK xK : K) ∈ NK := by
    change (((xK / phiK xK : K) : K) : J) ∈ N
    rw [div_eq_mul_inv]
    change ((xK : K) : J) * (((r • xK : K) : J))⁻¹ ∈ N
    rw [hfrob.coe_smul]
    change (x : G) *
      ((w : G) * (x : G) * (w : G)⁻¹)⁻¹ ∈ C
    convert C.inv_mem hxC using 1 <;> group
  obtain ⟨n, hn⟩ :=
    hfrob.restrictedKernelCommutatorMap_surjective hNK r hr
      ⟨(xK / phiK xK : K), hcommN⟩
  have hnK : MonoidHom.commutatorMap phiK (n : K) =
      MonoidHom.commutatorMap phiK xK := by
    apply Subtype.ext
    exact congrArg (fun y : NK ↦ (((y : K) : J))) hn
  have hnx : (n : K) = xK :=
    (hfrob.kernelConjugation_fixedPointFree r hr).commutatorMap_injective hnK
  have hxN : ((xK : K) : J) ∈ N := by
    have hnN := n.property
    rwa [hnx] at hnN
  have hxCmap : (x : G) ∈ Ptype_Fcompl_kernel ctx := hxN
  rcases hxCmap with ⟨y, hy, hyx⟩
  have hyx' : y = x := Subtype.ext hyx
  simpa [hyx'] using hy

/-! ## Normal extensions -/

private theorem normalIn_sup
    {A B M : Subgroup G}
    (hA : PTypeNormalIn A M) (hB : PTypeNormalIn B M) :
    PTypeNormalIn (A ⊔ B) M := by
  refine ⟨sup_le hA.1 hB.1, ?_⟩
  rw [Subgroup.subgroupOf_sup hA.1 hB.1]
  letI : (A.subgroupOf M).Normal := hA.2
  letI : (B.subgroupOf M).Normal := hB.2
  infer_instance

private theorem characteristic_image_normalized
    {K : Type*} [Group K] (S : Subgroup K)
    (R : Subgroup S) [R.Characteristic] :
    Subgroup.normalizer (S : Set K) ≤
      Subgroup.normalizer (R.map S.subtype : Set K) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · exact characteristic_map_subtype_invariant_under_normalizer
      S (Subgroup.normalizer (S : Set K)) R le_rfl g hg r
  · intro hr
    have hginv : g⁻¹ ∈ Subgroup.normalizer (S : Set K) :=
      (Subgroup.normalizer (S : Set K)).inv_mem hg
    have h := characteristic_map_subtype_invariant_under_normalizer
      S (Subgroup.normalizer (S : Set K)) R le_rfl
      g⁻¹ hginv (g * r * g⁻¹) hr
    simp only [inv_inv] at h
    have heq : g⁻¹ * (g * r * g⁻¹) * g = r := by group
    rw [heq] at h
    exact h

private theorem Fcore_normalizes_kernel_join
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Fitting_core M ≤ Subgroup.normalizer
      ((Ptype_Fcore_kernel ctx ⊔ Ptype_Fcompl_kernel ctx :
        Subgroup G) : Set G) := by
  let H₀ := Ptype_Fcore_kernel ctx
  let C := Ptype_Fcompl_kernel ctx
  let K := H₀ ⊔ C
  rw [Subgroup.le_normalizer_iff]
  intro h hh x hx
  let conjugate : G →* G := (MulAut.conj h).toMonoidHom
  have hgenerators : K ≤ K.comap conjugate := by
    apply sup_le
    · intro x hx
      change h * x * h⁻¹ ∈ K
      exact (show H₀ ≤ K from le_sup_left)
        ((Ptype_Fcore_kernel_normal_M ctx).conj_mem
          ⟨x, Ptype_Fcore_kernel_le_M ctx hx⟩ hx
          ⟨h, Fcore_sub M hh⟩)
    · intro c hc
      change h * c * h⁻¹ ∈ K
      have hcComm := (mem_complement_kernel_iff ctx).mp hc |>.2 h hh
      have hrewrite : h * c * h⁻¹ = ⁅c, h⁆⁻¹ * c := by
        rw [commutatorElement_def]
        group
      rw [hrewrite]
      exact K.mul_mem
        ((show H₀ ≤ K from le_sup_left) (H₀.inv_mem hcComm))
        ((show C ≤ K from le_sup_right) hc)
  exact hgenerators hx

private theorem kernel_join_complement_normal
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    PTypeNormalIn
      (Ptype_Fcore_kernel ctx ⊔ Ptype_Fcompl_kernel ctx) M := by
  let H := Fitting_core M
  let H₀ := Ptype_Fcore_kernel ctx
  let C := Ptype_Fcompl_kernel ctx
  let J := U ⊔ W₁
  let K := H₀ ⊔ C
  have hJleM : J ≤ M :=
    sup_le (context_U_le_M ctx) (context_W₁_le_M ctx)
  have hKleM : K ≤ M :=
    sup_le (Ptype_Fcore_kernel_le_M ctx)
      ((Ptype_Fcompl_kernel_le ctx).trans (context_U_le_M ctx))
  have hJnormH₀ : J ≤ Subgroup.normalizer (H₀ : Set G) :=
    hJleM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Ptype_Fcore_kernel_le_M ctx)).mp
          (Ptype_Fcore_kernel_normal_M ctx))
  have hJnormC : J ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (U_normalizes_complement_kernel ctx)
      (W₁_normalizes_complement_kernel ctx)
  have hJnormK : J ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf hJnormH₀ hJnormC).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup H₀ C)
  have hMnormK : M ≤ Subgroup.normalizer (K : Set G) := by
    rw [← semidirect_sup_eq (Ptype_Fcore_sdprod ctx)]
    exact sup_le (Fcore_normalizes_kernel_join ctx) hJnormK
  exact ⟨hKleM, Subgroup.normal_subgroupOf_of_le_normalizer hMnormK⟩

private theorem Fcore_join_complement_normal
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    PTypeNormalIn
      (Fitting_core M ⊔ Ptype_Fcompl_kernel ctx) M := by
  have hFcore : PTypeNormalIn (Fitting_core M) M :=
    ⟨Fcore_sub M, Fcore_normal M⟩
  have hnormal := normalIn_sup hFcore (kernel_join_complement_normal ctx)
  rw [← sup_assoc,
    sup_eq_left.mpr (Ptype_Fcore_kernel_lt ctx).le] at hnormal
  exact hnormal

private theorem derived_U_normal
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    PTypeNormalIn (derivedWithin U) M := by
  let H := Fitting_core M
  let D := derivedWithin U
  let J := U ⊔ W₁
  have hDleU : D ≤ U := Subgroup.map_subtype_le _
  have hDleM : D ≤ M := hDleU.trans (context_U_le_M ctx)
  have hJnormU : J ≤ Subgroup.normalizer (U : Set G) :=
    sup_le U.le_normalizer ctx.typeP.2.1.2.2.1
  have hJnormD : J ≤ Subgroup.normalizer (D : Set G) :=
    hJnormU.trans
      (characteristic_image_normalized U (_root_.commutator U))
  have hHcentD : H ≤ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact (typeP_context M U W W₁ W₂ ctx.defW ctx.typeP).derived_centralizes_fitting
  have hHnormD : H ≤ Subgroup.normalizer (D : Set G) :=
    hHcentD.trans (Subgroup.centralizer_le_normalizer (D : Set G))
  have hMnormD : M ≤ Subgroup.normalizer (D : Set G) := by
    rw [← semidirect_sup_eq (Ptype_Fcore_sdprod ctx)]
    exact sup_le hHnormD hJnormD
  exact ⟨hDleM, Subgroup.normal_subgroupOf_of_le_normalizer hMnormD⟩

private theorem kernel_join_derived_U_normal
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    PTypeNormalIn (Ptype_Fcore_kernel ctx ⊔ derivedWithin U) M :=
  normalIn_sup
    ⟨Ptype_Fcore_kernel_le_M ctx, Ptype_Fcore_kernel_normal_M ctx⟩
    (derived_U_normal ctx)

private theorem derivedWithin_mono
    {A B : Subgroup G} (hAB : A ≤ B) :
    derivedWithin A ≤ derivedWithin B := by
  rw [derivedWithin, A.map_subtype_commutator,
    derivedWithin, B.map_subtype_commutator]
  exact Subgroup.commutator_mono hAB hAB

private theorem kernel_join_derived_complement_eq
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    Ptype_Fcore_kernel ctx ⊔ derivedWithin (Ptype_Fcompl_kernel ctx) =
      Ptype_Fcore_kernel ctx ⊔
        derivedWithin
          (Ptype_Fcore_kernel ctx ⊔ Ptype_Fcompl_kernel ctx) := by
  classical
  let H₀ := Ptype_Fcore_kernel ctx
  let C := Ptype_Fcompl_kernel ctx
  let D := derivedWithin C
  let K := H₀ ⊔ C
  let N := H₀ ⊔ D
  have hH₀M : H₀ ≤ M := Ptype_Fcore_kernel_le_M ctx
  have hCM : C ≤ M :=
    (Ptype_Fcompl_kernel_le ctx).trans (context_U_le_M ctx)
  have hKM : K ≤ M := sup_le hH₀M hCM
  have hH₀K : H₀ ≤ K := le_sup_left
  have hCK : C ≤ K := le_sup_right
  have hDN : D ≤ N := le_sup_right
  have hH₀N : H₀ ≤ N := le_sup_left
  have hNK : N ≤ K :=
    sup_le hH₀K ((derivedWithin_mono hCK).trans
      (Subgroup.map_subtype_le (_root_.commutator K)))
  have hKnormH₀ : K ≤ Subgroup.normalizer (H₀ : Set G) :=
    hKM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hH₀M).mp
        (Ptype_Fcore_kernel_normal_M ctx))
  have hCnormD : C ≤ Subgroup.normalizer (D : Set G) :=
    C.le_normalizer.trans
      (characteristic_image_normalized C (_root_.commutator C))
  have hCnormN : C ≤ Subgroup.normalizer (N : Set G) :=
    (le_inf (hCK.trans hKnormH₀) hCnormD).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup H₀ D)
  have hH₀normN : H₀ ≤ Subgroup.normalizer (N : Set G) :=
    hH₀N.trans N.le_normalizer
  have hKnormN : K ≤ Subgroup.normalizer (N : Set G) :=
    sup_le hH₀normN hCnormN
  let H₀K : Subgroup K := H₀.subgroupOf K
  let CK : Subgroup K := C.subgroupOf K
  let NK : Subgroup K := N.subgroupOf K
  letI : H₀K.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKnormH₀
  letI : NK.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKnormN
  let qK : K →* K ⧸ NK := QuotientGroup.mk' NK
  let iC : C →* K := Subgroup.inclusion hCK
  let phi : C →* K ⧸ NK := qK.comp iC
  have hsupK : H₀K ⊔ CK = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hH₀K hCK]
    exact Subgroup.subgroupOf_self K
  have hphi : Function.Surjective phi := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective NK z
    have hkSup : k ∈ H₀K ⊔ CK := by
      rw [hsupK]
      exact Subgroup.mem_top k
    obtain ⟨n, hn, c, hc, hnc⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hkSup
    let cC : C := ⟨((c : K) : G), hc⟩
    refine ⟨cC, ?_⟩
    change qK (iC cC) = qK k
    rw [← hnc, map_mul]
    have hnNK : n ∈ NK := hH₀N hn
    have hcEq : iC cC = c := rfl
    have hqn : qK n = 1 := by
      exact (QuotientGroup.eq_one_iff n).mpr hnNK
    rw [hcEq, hqn, one_mul]
  have hquotComm : IsMulCommutative (K ⧸ NK) := by
    constructor
    constructor
    intro x y
    obtain ⟨c, rfl⟩ := hphi x
    obtain ⟨d, rfl⟩ := hphi y
    rw [← commutatorElement_eq_one_iff_mul_comm,
      ← map_commutatorElement]
    apply QuotientGroup.eq_one_iff (iC ⁅c, d⁆) |>.mpr
    change ⁅(c : G), (d : G)⁆ ∈ N
    exact hDN (by
      change ⁅(c : G), (d : G)⁆ ∈ derivedWithin C
      rw [derivedWithin, C.map_subtype_commutator]
      exact Subgroup.commutator_mem_commutator c.property d.property)
  have hcommK : _root_.commutator K ≤ NK :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hquotComm
  have hderivedK : derivedWithin K ≤ N := by
    rintro _ ⟨d, hd, rfl⟩
    exact hcommK hd
  apply le_antisymm
  · exact sup_le le_sup_left
      ((derivedWithin_mono hCK).trans le_sup_right)
  · exact sup_le le_sup_left (hderivedK.trans le_rfl)

private theorem kernel_join_derived_complement_normal
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    PTypeNormalIn
      (Ptype_Fcore_kernel ctx ⊔
        derivedWithin (Ptype_Fcompl_kernel ctx)) M := by
  let K := Ptype_Fcore_kernel ctx ⊔ Ptype_Fcompl_kernel ctx
  have hKnormal := kernel_join_complement_normal ctx
  have hMnormK : M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKnormal.1).mp hKnormal.2
  have hMnormDerived : M ≤
      Subgroup.normalizer (derivedWithin K : Set G) :=
    hMnormK.trans
      (characteristic_image_normalized K (_root_.commutator K))
  have hDerivedLeM : derivedWithin K ≤ M :=
    (Subgroup.map_subtype_le (_root_.commutator K)).trans hKnormal.1
  have hDerivedNormal : PTypeNormalIn (derivedWithin K) M :=
    ⟨hDerivedLeM,
      Subgroup.normal_subgroupOf_of_le_normalizer hMnormDerived⟩
  have hnormal := normalIn_sup
    (⟨Ptype_Fcore_kernel_le_M ctx,
      Ptype_Fcore_kernel_normal_M ctx⟩ :
        PTypeNormalIn (Ptype_Fcore_kernel ctx) M)
    hDerivedNormal
  rw [kernel_join_derived_complement_eq ctx]
  exact hnormal

/-- The four normality conclusions of
`PFsection9.v: Ptype_Fcore_extensions_normal`. -/
structure PTypeFCoreExtensionsNormal
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) : Prop where
  H₀C_normal :
    PTypeNormalIn
      (Ptype_Fcore_kernel ctx ⊔ Ptype_Fcompl_kernel ctx) M
  HC_normal :
    PTypeNormalIn
      (Fitting_core M ⊔ Ptype_Fcompl_kernel ctx) M
  H₀U'_normal :
    PTypeNormalIn
      (Ptype_Fcore_kernel ctx ⊔ derivedWithin U) M
  H₀C'_normal :
    PTypeNormalIn
      (Ptype_Fcore_kernel ctx ⊔
        derivedWithin (Ptype_Fcompl_kernel ctx)) M

/-- `PFsection9.v: Ptype_Fcore_extensions_normal`. -/
theorem Ptype_Fcore_extensions_normal
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    PTypeFCoreExtensionsNormal ctx :=
  { H₀C_normal := kernel_join_complement_normal ctx
    HC_normal := Fcore_join_complement_normal ctx
    H₀U'_normal := kernel_join_derived_U_normal ctx
    H₀C'_normal := kernel_join_derived_complement_normal ctx }

end

end Submission.OddOrder.PF
