import Submission.OddOrder.PF.Section12.FTType1ConstituentConstants

/-!
# Peterfalvi Section 12: the Frobenius type-I alternative

This module proves Peterfalvi (12.6).  When a maximal subgroup is displayed
as a Frobenius group with its Fitting core as kernel, its Feit--Thompson type
is one and its support is exactly the nonidentity part of that kernel.  The
type-I subcoherent family can then be upgraded to a coherent family for the
canonical Dade map.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe u

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance : Fintype G := Fintype.ofFinite G

local instance : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## Frobenius data and the canonical map -/

/-- A Frobenius presentation of `L` whose kernel is its Fitting core. -/
def FTFrobeniusWithFittingKernel (L : Subgroup G) : Prop :=
  ∃ U : Subgroup G, IsFrobeniusIn (Fitting_core L) U L

/-- The hypotheses fixed in the Frobenius specialization of Section 12. -/
structure FTFrobeniusContext (L : Subgroup G) : Prop where
  maxL : L ∈ minSimple_max_groups (G := G)
  frobenius : FTFrobeniusWithFittingKernel L

namespace FTFrobeniusContext

/-- The full-support Dade map attached to a Frobenius type-I context. -/
noncomputable def tau {L : Subgroup G} (ctx : FTFrobeniusContext L) :
    ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  (ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom).comp
    (Dade (FT_Dade_hyp L ctx.maxL))

end FTFrobeniusContext

/-- Transport class functions from the ambient top subgroup back to the
ambient group. -/
private noncomputable def frobeniusTargetMap :
    ClassFunction (⊤ : Subgroup G) ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom

private theorem frobeniusTargetMap_pairing
    (phi psi : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterPairing (frobeniusTargetMap phi)
        (frobeniusTargetMap psi) =
      characterPairing phi psi := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [frobeniusTargetMap, ClassFunction.comap_apply]

private theorem frobeniusTargetMap_virtual
    {phi : ClassFunction (⊤ : Subgroup G) ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (frobeniusTargetMap phi) := by
  obtain ⟨z, hz⟩ := hphi
  refine ⟨VirtualCharacter.comap
    Subgroup.topEquiv.symm.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap, hz]
  rfl

private theorem coherentWith_frobeniusTargetMap
    {L : Type} [Group L] [Fintype L]
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    {sigma nu : ClassFunction L ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ}
    (hcoh : coherent_with S A sigma nu) :
    coherent_with S A
      (frobeniusTargetMap.comp sigma)
      (frobeniusTargetMap.comp nu) := by
  exact
    { isometry := by
        intro phi hphi psi hpsi
        simpa [LinearMap.comp_apply] using
          (frobeniusTargetMap_pairing (nu phi) (nu psi)).trans
            (hcoh.isometry phi hphi psi hpsi)
      mapsToVirtual := by
        intro phi hphi
        exact frobeniusTargetMap_virtual (hcoh.mapsToVirtual phi hphi)
      agrees := by
        intro phi hphi hsupp
        simpa [LinearMap.comp_apply, hcoh.agrees phi hphi hsupp] }

/-- Irreducibility and coherence in the Frobenius type-I alternative. -/
structure FTFrobeniusCoherenceConclusion
    {L : Subgroup G} (ctx : FTFrobeniusContext L) : Prop where
  seqInd_irreducible :
    ∀ phi ∈ FTType1SeqIndFamily L,
      IsIrreducibleCharacter L ℂ phi
  coherent_family :
    coherent
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ))
      (nonidentitySet L) ctx.tau

/-! ## Type and support -/

/-- `PFsection12.v: FT_Frobenius_type1`. -/
theorem FT_Frobenius_type1
    {L : Subgroup G} (ctx : FTFrobeniusContext L) :
    FTtype L = 1 := by
  obtain ⟨U, hFrob⟩ := ctx.frobenius
  have hTypeF : of_typeF L U := Frobenius_of_typeF L U hFrob
  by_contra hTypeNe
  obtain ⟨V, W, W₁, W₂, hW, hTypeP⟩ :=
    FTtypeP_witness L ctx.maxL hTypeNe
  exact typePF_exclusion L V W W₁ W₂ U hW hTypeP hTypeF

/-- An element commuting with a nonidentity element of a Frobenius kernel
belongs to that kernel. -/
private theorem mem_kernel_of_commute
    {Q : Type u} [Group Q] [Finite Q]
    {K R : Subgroup Q}
    (hFrob : IsFrobeniusDecomposition K R)
    {g : Q} {k : K} (hk : k ≠ 1)
    (hcomm : Commute g (k : Q)) :
    g ∈ K := by
  letI : K.Normal := hFrob.kernel_normal
  by_contra hg
  obtain ⟨x, hx⟩ :=
    hFrob.exists_kernel_conjugate_complement_of_not_mem hg
  rcases hx with ⟨r, hr, hrg⟩
  have hrg' : (x : Q) * r * (x : Q)⁻¹ = g := by
    simpa [MulAut.conj_apply] using hrg
  let rR : R := ⟨r, hr⟩
  have hrNe : rR ≠ 1 := by
    intro hrOne
    apply hg
    have hrOneQ : r = 1 := congrArg Subtype.val hrOne
    rw [← hrg', hrOneQ]
    simpa using x.property
  let kx : K :=
    ⟨(x : Q)⁻¹ * (k : Q) * (x : Q),
      by
        simpa using (inferInstance : K.Normal).conj_mem
          (k : Q) k.property (x : Q)⁻¹⟩
  have hkxNe : kx ≠ 1 := by
    intro hkxOne
    apply hk
    apply Subtype.ext
    have hkxValue : (kx : Q) = 1 := congrArg Subtype.val hkxOne
    change (x : Q)⁻¹ * (k : Q) * (x : Q) = 1 at hkxValue
    calc
      (k : Q) =
          (x : Q) * ((x : Q)⁻¹ * (k : Q) * (x : Q)) *
            (x : Q)⁻¹ := by group
      _ = 1 := by rw [hkxValue]; simp
  have hfixed :
      (rR : Q) * (kx : Q) * (rR : Q)⁻¹ = (kx : Q) := by
    change r * ((x : Q)⁻¹ * (k : Q) * (x : Q)) * r⁻¹ =
      (x : Q)⁻¹ * (k : Q) * (x : Q)
    calc
      r * ((x : Q)⁻¹ * (k : Q) * (x : Q)) * r⁻¹ =
          (x : Q)⁻¹ *
            (((x : Q) * r * (x : Q)⁻¹) * (k : Q) *
              ((x : Q) * r * (x : Q)⁻¹)⁻¹) * (x : Q) := by group
      _ = (x : Q)⁻¹ * (g * (k : Q) * g⁻¹) * (x : Q) := by
        rw [hrg']
      _ = (x : Q)⁻¹ * ((k : Q) * g * g⁻¹) * (x : Q) := by
        rw [hcomm.eq]
      _ = (x : Q)⁻¹ * (k : Q) * (x : Q) := by simp
  exact hkxNe (hFrob.fixedPointFree rR hrNe kx hfixed)

/-- Display an ambient Frobenius presentation directly inside its stated
ambient subgroup. -/
private theorem frobeniusIn_decomposition
    {H U L : Subgroup G} (h : IsFrobeniusIn H U L) :
    IsFrobeniusDecomposition (H.subgroupOf L) (U.subgroupOf L) := by
  let J := H ⊔ U
  let e : J ≃* L := MulEquiv.subgroupCongr h.1
  have hFrob := FTContextInternal.frobenius_map_mulEquiv8 h.2.2 e
  have hHmap :
      (H.subgroupOf J).map e.toMonoidHom = H.subgroupOf L := by
    ext x
    rw [Subgroup.mem_map_equiv]
    rfl
  have hUmap :
      (U.subgroupOf J).map e.toMonoidHom = U.subgroupOf L := by
    ext x
    rw [Subgroup.mem_map_equiv]
    rfl
  rwa [hHmap, hUmap] at hFrob

/-- `PFsection12.v: FTsupp_Frobenius`. -/
theorem FTsupp_Frobenius
    {L : Subgroup G} (ctx : FTFrobeniusContext L) :
    ftSupport L = subgroupNonidentity (Fitting_core L) := by
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨U, hFrob⟩ := ctx.frobenius
    have hFrobL : IsFrobeniusDecomposition
        (FTType1FittingIn L) (U.subgroupOf L) :=
      frobeniusIn_decomposition hFrob
    simp only [FTsupport, ftSupport, Set.mem_iUnion] at hy
    rcases hy with ⟨a, haFirst, hyCentralizer⟩
    have haCore : a ∈ subgroupNonidentity (Fitting_core L) := by
      rw [← FTsupp1_type1 L (FT_Frobenius_type1 ctx)]
      exact haFirst
    have hyL : y ∈ L := by
      have hyDerived :=
        (mem_centralizerWithin.mp hyCentralizer.1).1
      simpa [FTder, ftDerived, FT_Frobenius_type1 ctx] using hyDerived
    let yL : L := ⟨y, hyL⟩
    let aL : FTType1FittingIn L :=
      ⟨⟨a, Fcore_sub L haCore.1⟩, haCore.1⟩
    have haLNe : aL ≠ 1 := by
      intro haOne
      apply haCore.2
      exact congrArg
        (fun z : FTType1FittingIn L ↦ ((z : L) : G)) haOne
    have hyCommutesA : Commute y a :=
      ((mem_centralizerWithin.mp hyCentralizer.1).2
        a (Subgroup.mem_zpowers a)).symm
    have hyCommutesAL : Commute yL (aL : L) := by
      rw [commute_iff_eq]
      apply Subtype.ext
      exact hyCommutesA.eq
    have hyCore : yL ∈ FTType1FittingIn L :=
      mem_kernel_of_commute hFrobL haLNe hyCommutesAL
    exact ⟨hyCore, hyCentralizer.2⟩
  · exact Fcore_sub_FTsupp ctx.maxL

/-! ## Coherence -/

/-- A nontrivial subgroup stays nontrivial after it is displayed inside an
overgroup. -/
private theorem subgroupOf_ne_bot
    {Q : Type u} [Group Q] {H L : Subgroup Q}
    (hHL : H ≤ L) (hH : H ≠ ⊥) :
    H.subgroupOf L ≠ ⊥ := by
  intro hbot
  apply hH
  apply le_bot_iff.mp
  intro x hx
  let xL : L := ⟨x, hHL hx⟩
  have hxSub : xL ∈ H.subgroupOf L := hx
  have hxOne : xL = 1 := by
    apply Subgroup.mem_bot.mp
    simpa only [hbot] using hxSub
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxOne)

/-- Every type-F complement gives the Frobenius decomposition inside `L`
once one Frobenius complement for the same kernel is available. -/
private theorem frobenius_decomposition_of_typeF_complement
    {L U : Subgroup G} (ctx : FTFrobeniusContext L)
    (hTypeF : of_typeF L U) :
    IsFrobeniusDecomposition
      (FTType1FittingIn L) (U.subgroupOf L) := by
  let H := FTType1FittingIn L
  have hUL : U ≤ L := hTypeF.2.2.1.2.1
  have hNormal : H.Normal := by
    simpa only [H] using hTypeF.2.2.1.2.2.1
  have hComplement : H.IsComplement' (U.subgroupOf L) := by
    simpa only [H] using hTypeF.2.2.1.2.2.2
  obtain ⟨E, hFrobE⟩ := ctx.frobenius
  have hExisting :
      IsFrobeniusDecomposition H (E.subgroupOf L) :=
    frobeniusIn_decomposition hFrobE
  refine
    { isComplement := hComplement
      kernel_normal := hNormal
      kernel_ne_bot := hExisting.kernel_ne_bot
      complement_ne_bot := subgroupOf_ne_bot hUL hTypeF.2.1
      fixedPointFree := ?_ }
  intro r hr k hfix
  by_contra hk
  have hcomm : Commute (r : L) (k : L) := by
    rw [commute_iff_eq]
    exact mul_inv_eq_iff_eq_mul.mp hfix
  have hrKernel : (r : L) ∈ H :=
    mem_kernel_of_commute hExisting hk hcomm
  have hrInf : (r : L) ∈ H ⊓ U.subgroupOf L :=
    ⟨hrKernel, r.property⟩
  have hInfBot : H ⊓ U.subgroupOf L = ⊥ :=
    disjoint_iff.mp hComplement.disjoint
  rw [hInfBot] at hrInf
  exact hr (Subtype.ext (Subgroup.mem_bot.mp hrInf))

/-- On functions in the type-I sequential span, ordinary induction and the
Dade map agree once the Dade set is exactly the nonidentity kernel. -/
private theorem coherent_with_dade_of_sibley
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {Q L : Subgroup Gamma} {A : Set Gamma}
    (K : Subgroup L) [K.Normal]
    (ddA : DadeHypothesis Q L A)
    (hTI : IsNormalizedTI A Q L)
    (hA : {x : L | (x : Gamma) ∈ A} = (K : Set L) \ {1})
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction Q ℂ)
    (hcoh : coherent_with
      (seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥ :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) (sibleyInduce Q L ddA.2.1) nu) :
    coherent_with
      (seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥ :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu := by
  refine ⟨hcoh.isometry, hcoh.mapsToVirtual, ?_⟩
  intro phi hphi hoff
  have hKernelSupport :
      phi ∈ ClassFunction.supportedOn (K : Set L) := by
    have hclosure : ∀ {psi : ClassFunction L ℂ},
        psi ∈ AddSubgroup.closure
            (seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥ :
              Set (ClassFunction L ℂ)) →
          psi ∈ ClassFunction.supportedOn (K : Set L) := by
      intro psi hpsi
      induction hpsi using AddSubgroup.closure_induction with
      | mem xi hxi => exact seqInd_on K hxi
      | zero =>
          exact (ClassFunction.supportedOn (R := ℂ) (K : Set L)).zero_mem
      | add x y hx hy ihx ihy =>
          exact (ClassFunction.supportedOn (R := ℂ) (K : Set L)).add_mem
            ihx ihy
      | neg x hx ihx =>
          exact (ClassFunction.supportedOn (R := ℂ) (K : Set L)).neg_mem ihx
    exact hclosure hphi
  have hDadeSupport : phi ∈ ClassFunction.supportedOn
      {x : L | (x : Gamma) ∈ A} := by
    rw [hA, ClassFunction.mem_supportedOn_iff]
    intro x hx
    by_cases hxK : x ∈ K
    · apply ClassFunction.eq_zero_of_mem_supportedOn hoff
      intro hxNe
      exact hx ⟨hxK, hxNe⟩
    · exact ClassFunction.eq_zero_of_mem_supportedOn hKernelSupport hxK
  calc
    nu phi = sibleyInduce Q L ddA.2.1 phi :=
      hcoh.agrees phi hphi hoff
    _ = Dade ddA phi := (Dade_Ind ddA hTI phi hDadeSupport).symm

/-- Commutativity passes to a subgroup displayed inside an overgroup. -/
private theorem subgroupOf_isMulCommutative
    {Q : Type u} [Group Q] {H L : Subgroup Q}
    (hHL : H ≤ L) (hH : IsMulCommutative H) :
    IsMulCommutative (H.subgroupOf L) := by
  let e : H.subgroupOf L ≃* H := Subgroup.subgroupOfEquivOfLe hHL
  apply isMulCommutative_iff.mpr
  intro x y
  exact e.injective (isMulCommutative_iff.mp hH (e x) (e y))

/-- Every complex irreducible character of a finite commutative group has
degree one. -/
private theorem irreducible_degree_one
    {Q : Type u} [Group Q] [Fintype Q] [IsMulCommutative Q]
    (chi : IrreducibleCharacter Q ℂ) :
    chi 1 = 1 := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  rw [IrreducibleCharacter.apply_one_eq_finrank,
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
      chi.representation.ρ]
  norm_num

private theorem fittingIn_isNilpotent {L : Subgroup G} :
    Group.IsNilpotent (FTType1FittingIn L) := by
  let e : FTType1FittingIn L ≃* Fitting_core L :=
    Subgroup.subgroupOfEquivOfLe (Fcore_sub L)
  exact (Group.isNilpotent_congr e).mpr (Fcore_nil L)

/-- The bottom quotient of the Fitting core supplies the quotient input to
the noncoherent-chief alternative. -/
private theorem typeOne_oddFrobeniusQuotient
    {L U : Subgroup G} (hTypeF : of_typeF L U)
    (hFrob : IsFrobeniusDecomposition
      (FTType1FittingIn L) (U.subgroupOf L)) :
    odd_Frobenius_quotient (FTType1FittingIn L)
      (⊥ : Subgroup (FTType1FittingIn L)) := by
  let K := FTType1FittingIn L
  letI : K.Normal := Fcore_normal L
  letI : Group.IsNilpotent K := fittingIn_isNilpotent
  letI : IsSolvable K := inferInstance
  letI : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hFrob.kernel_ne_bot
  have hNilpotent : Group.IsNilpotent (K ⧸ (⊥ : Subgroup K)) :=
    Group.nilpotent_of_surjective
      (QuotientGroup.mk' (⊥ : Subgroup K))
      (QuotientGroup.mk'_surjective (⊥ : Subgroup K))
  dsimp [odd_Frobenius_quotient]
  refine ⟨mFT_odd L, hNilpotent, ?_⟩
  let H₁ : Subgroup L :=
    (_root_.commutator K ⊔ (⊥ : Subgroup K)).map K.subtype
  have hCommutatorProper :
      _root_.commutator K < (⊤ : Subgroup K) :=
    IsSolvable.commutator_lt_top_of_nontrivial K
  have hH₁Proper : H₁ < K := by
    have hmap :=
      (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).2
        hCommutatorProper
    simpa only [H₁, sup_bot_eq, ← MonoidHom.range_eq_map,
      K.range_subtype] using hmap
  letI : H₁.Normal := by
    dsimp only [H₁]
    rw [Subgroup.map_sup]
    infer_instance
  change ∃ E : Subgroup (L ⧸ H₁),
    IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk' H₁)) E
  exact ⟨(U.subgroupOf L).map (QuotientGroup.mk' H₁),
    hFrob.quotient hH₁Proper⟩

/-- `PFsection12.v: FT_Frobenius_coherence`, Peterfalvi (12.6). -/
theorem FT_Frobenius_coherence
    {L : Subgroup G} (ctx : FTFrobeniusContext L) :
    FTFrobeniusCoherenceConclusion ctx := by
  classical
  let H := FTType1FittingIn L
  letI : H.Normal := Fcore_normal L
  letI : Group.IsNilpotent H := fittingIn_isNilpotent
  letI : IsSolvable H := inferInstance
  obtain ⟨E, hFrobE⟩ := ctx.frobenius
  have hFrobEL :
      IsFrobeniusDecomposition H (E.subgroupOf L) :=
    frobeniusIn_decomposition hFrobE
  have hIrr : ∀ phi ∈ FTType1SeqIndFamily L,
      IsIrreducibleCharacter L ℂ phi := by
    intro phi hphi
    obtain ⟨theta, htheta, rfl⟩ :=
      (seqIndC1P (k := ℂ) H).mp hphi
    exact irr_induced_Frobenius_ker hFrobEL theta htheta
  refine ⟨hIrr, ?_⟩
  let typeCtx : FTType1Context L :=
    ⟨ctx.maxL, FT_Frobenius_type1 ctx⟩
  have hSubcoherent := typeCtx.R_spec.subcoherent_family
  obtain ⟨U, hTypeI⟩ :=
    (FTtypeP 1 L ctx.maxL).mpr (FT_Frobenius_type1 ctx)
  have hTypeF : of_typeF L U := hTypeI.1
  have hUL : U ≤ L := hTypeF.2.2.1.2.1
  have hFrobUL : IsFrobeniusDecomposition H (U.subgroupOf L) :=
    frobenius_decomposition_of_typeF_complement ctx hTypeF
  have hNilpotentCore : Group.IsNilpotent (Fitting_core L) := Fcore_nil L
  rcases hTypeI.2 with hTI | hOther
  · obtain ⟨nu, hnu⟩ :=
      Sibley_coherence (⊤ : Subgroup G) L (Fitting_core L) U
        le_top (Fcore_sub L) hUL (mFT_odd L) hNilpotentCore hTI
        (Or.inl hFrobUL)
    have hSupport : {x : L | (x : G) ∈ FTsupport L} =
        (H : Set L) \ {1} := by
      change {x : L | (x : G) ∈ ftSupport L} =
        (H : Set L) \ {1}
      ext x
      rw [FTsupp_Frobenius ctx]
      simp only [H, mem_subgroupNonidentity, Set.mem_diff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx, hxOne⟩
        exact ⟨hx, fun h ↦ hxOne (congrArg Subtype.val h)⟩
      · rintro ⟨hx, hxOne⟩
        exact ⟨hx, fun h ↦ hxOne (Subtype.ext h)⟩
    have hTIFull : IsNormalizedTI (FTsupport L)
        (⊤ : Subgroup G) L := by
      change IsNormalizedTI (ftSupport L) (⊤ : Subgroup G) L
      rw [FTsupp_Frobenius ctx]
      exact hTI
    have hcohTop := coherent_with_dade_of_sibley H
      (FT_Dade_hyp L ctx.maxL) hTIFull hSupport nu
      (by simpa only [sibleyFamily, H] using hnu)
    have hcohAmbient := coherentWith_frobeniusTargetMap hcohTop
    exact ⟨frobeniusTargetMap.comp nu, by
      simpa only [FTFrobeniusContext.tau, frobeniusTargetMap,
        FTType1SeqIndFamily, H] using
        hcohAmbient⟩
  · rcases hOther with hCommutative | hExponent
    · have hDegrees : ∀ phi ∈ FTType1SeqIndFamily L,
          ∀ psi ∈ FTType1SeqIndFamily L, phi 1 = psi 1 := by
        intro phi hphi psi hpsi
        obtain ⟨theta, htheta, rfl⟩ :=
          (seqIndC1P (k := ℂ) H).mp hphi
        obtain ⟨eta, heta, rfl⟩ :=
          (seqIndC1P (k := ℂ) H).mp hpsi
        letI : IsMulCommutative H :=
          subgroupOf_isMulCommutative (Fcore_sub L) hCommutative.1
        rw [ClassFunction.induce_one, ClassFunction.induce_one,
          irreducible_degree_one theta, irreducible_degree_one eta]
      have hCoherent := uniform_degree_coherence hSubcoherent hDegrees
      simpa only [FTFrobeniusContext.tau, FTType1Context.tau] using
        hCoherent
    · have hQuotient : odd_Frobenius_quotient H (⊥ : Subgroup H) :=
        typeOne_oddFrobeniusQuotient hTypeF hFrobUL
      rcases non_coherent_chief H typeCtx.tau typeCtx.R
          hSubcoherent ⊥ hQuotient with hCoherent | hExceptional
      · simpa only [H, FTType1SeqIndFamily,
          FTFrobeniusContext.tau, FTType1Context.tau] using hCoherent
      · rcases hExceptional with
          ⟨_, _, p, hp, hpGroup, hNoncommutative, hNotDvd⟩
        letI : Fact p.Prime := ⟨hp⟩
        have hPGroup : IsPGroup p H :=
          hpGroup.of_equiv QuotientGroup.quotientBot
        have hCardNeOne : Nat.card H ≠ 1 := by
          intro hCard
          apply hNoncommutative
          letI : Subsingleton H :=
            (Nat.card_eq_one_iff_unique.mp hCard).1
          have hHcomm : IsMulCommutative H := inferInstance
          exact FTContextInternal.isMulCommutative_of_mulEquiv8 hHcomm
            QuotientGroup.quotientBot.symm
        have hpCard : p ∣ Nat.card H :=
          hPGroup.card_eq_or_dvd.resolve_left hCardNeOne
        have hpCore : p ∈ primeSupport (Nat.card (Fitting_core L)) := by
          refine ⟨hp, ?_⟩
          change p ∣ Nat.card ((Fitting_core L).subgroupOf L) at hpCard
          rwa [MathlibSupport.natCard_subgroupOf_eq (Fcore_sub L)] at hpCard
        have hSup : Fitting_core L ⊔ U = L :=
          FTContextInternal.semidirect_sup_eq8 hTypeF.2.2.1
        have hFrobInU :
            IsFrobeniusIn (Fitting_core L) U L := by
          refine ⟨hSup, ?_⟩
          rw [hSup]
          exact ⟨hTypeF.2.2.1, hFrobUL⟩
        have hComplement : is_typeF_complement L U U := by
          exact ⟨le_rfl, rfl, hFrobInU.2.1, hFrobInU.2.2⟩
        have hCardU : Nat.card U = Monoid.exponent U :=
          (typeF_context L U hTypeF).complement_card U hComplement
        have hIndex : H.index = Nat.card U := by
          exact hFrobUL.isComplement.symm.index_eq_card.trans
            (MathlibSupport.natCard_subgroupOf_eq hUL)
        exfalso
        apply hNotDvd
        rw [hIndex, hCardU]
        exact hExponent.1 p hpCore

end

end Submission.OddOrder.PF
