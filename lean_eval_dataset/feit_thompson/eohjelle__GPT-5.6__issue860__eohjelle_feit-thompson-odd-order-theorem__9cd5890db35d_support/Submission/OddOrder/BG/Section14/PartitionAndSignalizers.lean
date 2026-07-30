import Submission.OddOrder.BG.Section14.SigmaDecompositionAndTypes
import Submission.OddOrder.BG.Section14.PTypeStructure
import Submission.OddOrder.BG.Section14.SigmaSupport
import Submission.OddOrder.BG.Section14.PTypeEmbedding
import Submission.OddOrder.BG.Section12.Tau2NormalizerFTType
import Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset
import Submission.OddOrder.PF.Section02.DadeSupportConjugation
import Submission.OddOrder.PF.Section05.InducedIrreducibles
import Submission.OddOrder.MathlibSupport.InternalSemidirectProjection

/-!
# Bender--Glauberman Section 14: the partition and signalizer consequences

This file ports the closing block of `BGsection14.v`, lines 1947--2510:
Corollaries 14.9 and 14.10 and Lemmas 14.11--14.13(a).

MathComp's family-valued `partition` predicate is represented by
`Submission.OddOrder.PF.IsSetPartition`.  An ambient Hall subgroup is
represented by an explicit containment followed by `IsHall` on
`Subgroup.subgroupOf`; rank-one elementary-abelian subgroups use
`RankOneLineIn`.
-/

namespace Submission.OddOrder.BG.Section14

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative commutatorElement

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## The global support family -/

/-- The family denoted `Pcover` in Corollary 14.9. -/
def pTypeSupportCover : Set (Set G) :=
  (fun M : Subgroup G =>
      classSupportWithin (⊤ : Subgroup G) (sigmaCover M)) ''
    minSimple_max_groups (G := G)

/-- The extra class support associated with a `P`-type maximal subgroup
and a selected `kappa`-Hall subgroup. -/
def pTypeExceptionalSupport (M K : Subgroup G) : Set G :=
  classSupportWithin (⊤ : Subgroup G) (pTypeTISet M K)

private theorem mem_classSupportWithin_top_of_mem
    {S : Set G} {x : G} (hx : x ∈ S) :
    x ∈ classSupportWithin (⊤ : Subgroup G) S := by
  exact ⟨x, hx, 1, Subgroup.mem_top 1, by simp⟩

private theorem classSupportWithin_top_mono
    {S T : Set G} (hST : S ⊆ T) :
    classSupportWithin (⊤ : Subgroup G) S ⊆
      classSupportWithin (⊤ : Subgroup G) T := by
  rintro y ⟨x, hx, g, -, rfl⟩
  exact ⟨x, hST hx, g, Subgroup.mem_top g, rfl⟩

/-- Conjugating the underlying maximal subgroup does not change its
conjugacy-saturated sigma support. -/
private theorem classSupport_sigmaCover_eq_of_conjugate
    {M H : Subgroup G} (hMH : AreConjugateSubgroups M H) :
    classSupportWithin (⊤ : Subgroup G) (sigmaCover M) =
      classSupportWithin (⊤ : Subgroup G) (sigmaCover H) := by
  rcases hMH with ⟨g, rfl⟩
  rw [sigma_supportJ]
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, z, -, rfl⟩
    refine ⟨(MulAut.conj g) x, ⟨x, hx, rfl⟩,
      g * z, Subgroup.mem_top _, ?_⟩
    simp only [MulAut.conj_apply]
    group
  · rintro y ⟨x, ⟨a, ha, rfl⟩, z, -, rfl⟩
    refine ⟨a, ha, g⁻¹ * z, Subgroup.mem_top _, ?_⟩
    simp only [MulAut.conj_apply]
    group

/-- Pull an inclusion in a conjugate subgroup back by inverse
conjugation. -/
private theorem map_conj_inv_le_of_le_map_conj_14
    {A B : Subgroup G} {g : G}
    (h : A ≤ B.map (MulAut.conj g).toMonoidHom) :
    A.map (MulAut.conj g⁻¹).toMonoidHom ≤ B := by
  rintro z ⟨a, ha, rfl⟩
  rcases h ha with ⟨b, hb, hba⟩
  have heq : g⁻¹ * a * (g⁻¹)⁻¹ = b := by
    rw [← hba]
    simp [MulAut.conj_apply, mul_assoc]
  change g⁻¹ * a * (g⁻¹)⁻¹ ∈ B
  rw [heq]
  exact hb

/-- Every conjugate of an element of a sigma support is nonidentity. -/
private theorem classSupport_sigmaCover_subset_nonidentity
    {M : Subgroup G} (hM : M ∈ minSimple_max_groups (G := G)) :
    classSupportWithin (⊤ : Subgroup G) (sigmaCover M) ⊆
      nonidentitySet G := by
  rintro y ⟨x, hxCover, g, -, rfl⟩
  change g⁻¹ * x * g ≠ 1
  intro hconjOne
  have hxOne : x = 1 := by
    calc
      x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [hconjOne]; simp
  rcases hxCover with ⟨a, haSigma, haOne, r, hr, rfl⟩
  have haDecomp : a ∈ sigmaDecomposition (a * r) :=
    mem_sigma_cover_decomposition
      (Msigma_ell1 hM haSigma haOne)
      ⟨a, Set.mem_singleton a, r, hr, rfl⟩
  have hlenNe : sigmaLength (a * r) ≠ 0 :=
    Set.ncard_ne_zero_of_mem haDecomp
  exact hlenNe ((ell_sigma0P (a * r)).mpr hxOne)

/-- Sigma length one supplies at least one sigma-maximal overgroup. -/
private theorem sigmaMaximalOvergroups_nonempty
    {x : G} (hell : sigmaLength x = 1) :
    (sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G)).Nonempty :=
  (ell_sigma1P.mp hell).2

/-- A signalizer-coset element belongs to the sigma cover of every
sigma-maximal overgroup of its base element. -/
private theorem sigmaCover_of_signalizer_coset
    {x y : G} {M : Subgroup G}
    (hell : sigmaLength x = 1)
    (hM : M ∈ sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G))
    (hy : x⁻¹ * y ∈ ftSignalizer x) :
    y ∈ sigmaCover M := by
  refine ⟨x, hM.2 (Subgroup.mem_zpowers x),
    (ell_sigma1P.mp hell).1, x⁻¹ * y, hy, ?_⟩
  group

/-- Sigma length is constant on the class support of a sigma cover. -/
private theorem ell_sigma_support_class
    {M : Subgroup G} (hM : M ∈ minSimple_max_groups (G := G))
    {y : G}
    (hy : y ∈ classSupportWithin (⊤ : Subgroup G) (sigmaCover M)) :
    sigmaLength y ≤ 2 := by
  rcases hy with ⟨x, hx, g, -, rfl⟩
  have hlen := ell_sigma_support hM hx
  simpa [MulAut.conj_apply] using (ell_sigmaJ x g⁻¹).le.trans hlen

/-- A normalized TI set has nonempty conjugacy support. -/
private theorem classSupportWithin_nonempty_of_normalizedTI
    {S : Set G} {L : Subgroup G}
    (hTI : IsNormalizedTI S (⊤ : Subgroup G) L) :
    (classSupportWithin (⊤ : Subgroup G) S).Nonempty := by
  obtain ⟨x, hx⟩ := hTI.1
  exact ⟨x, x, hx, 1, Subgroup.mem_top 1, by simp⟩

/-- The exceptional P-type class support contains no identity element. -/
private theorem pTypeExceptionalSupport_subset_nonidentity
    {M K Mstar : Subgroup G} (_hEmbed : PTypeEmbedding M K Mstar) :
    pTypeExceptionalSupport M K ⊆ nonidentitySet G := by
  rintro y ⟨x, hx, g, -, rfl⟩
  change g⁻¹ * x * g ≠ 1
  intro hconjOne
  have hxOne : x = 1 := by
    calc
      x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [hconjOne]; simp
  exact hx.2 (Or.inl (by simpa [hxOne] using K.one_mem))

/-- Saturating both sides preserves disjointness from all conjugate sigma
covers. -/
private theorem classSupport_disjoint_of_disjoint_sigmaCover_14_9
    {T : Set G}
    (hdis : ∀ {H : Subgroup G},
      H ∈ minSimple_max_groups (G := G) →
        Disjoint T (sigmaCover H))
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Disjoint
      (classSupportWithin (⊤ : Subgroup G) T)
      (classSupportWithin (⊤ : Subgroup G) (sigmaCover M)) := by
  apply Set.disjoint_left.2
  intro z hzT hzM
  rcases hzT with ⟨t, htT, g, -, rfl⟩
  rcases hzM with ⟨s, hsM, a, -, hconj⟩
  let c : G := g * a⁻¹
  have hst : (MulAut.conj c) s = t := by
    rw [MulAut.conj_apply]
    calc
      c * s * c⁻¹ = g * (a⁻¹ * s * a) * g⁻¹ := by
        simp [c]
        group
      _ = g * (g⁻¹ * t * g) * g⁻¹ := by
        rw [show a⁻¹ * s * a = g⁻¹ * t * g by simpa using hconj]
      _ = t := by group
  have htSigma :
      t ∈ sigmaCover (M.map (MulAut.conj c).toMonoidHom) := by
    rw [sigma_supportJ]
    exact ⟨s, hsM, hst⟩
  have hMc :
      M.map (MulAut.conj c).toMonoidHom ∈
        minSimple_max_groups (G := G) :=
    (mmaxJ M (MulAut.conj c)).2 hM
  exact (Set.disjoint_left.mp (hdis hMc)) htT htSigma

/-- Distinct conjugacy-saturated sigma supports are disjoint. -/
private theorem classSupport_sigmaCover_disjoint_of_ne_14_9
    {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hne :
      classSupportWithin (⊤ : Subgroup G) (sigmaCover M) ≠
        classSupportWithin (⊤ : Subgroup G) (sigmaCover H)) :
    Disjoint
      (classSupportWithin (⊤ : Subgroup G) (sigmaCover M))
      (classSupportWithin (⊤ : Subgroup G) (sigmaCover H)) := by
  apply Set.disjoint_left.2
  intro q hqM hqH
  rcases hqM with ⟨a, ha, x, -, rfl⟩
  rcases hqH with ⟨b, hb, y, -, hy⟩
  let Mx : Subgroup G := M.map (MulAut.conj x⁻¹).toMonoidHom
  let Hy : Subgroup G := H.map (MulAut.conj y⁻¹).toMonoidHom
  have hMx : Mx ∈ minSimple_max_groups (G := G) :=
    (mmaxJ M (MulAut.conj x⁻¹)).2 hM
  have hHy : Hy ∈ minSimple_max_groups (G := G) :=
    (mmaxJ H (MulAut.conj y⁻¹)).2 hH
  have hnotRaw : ∀ z : G,
      Hy ≠ Mx.map (MulAut.conj z).toMonoidHom := by
    intro z heq
    apply hne
    have hMMx :
        classSupportWithin (⊤ : Subgroup G) (sigmaCover M) =
          classSupportWithin (⊤ : Subgroup G) (sigmaCover Mx) :=
      classSupport_sigmaCover_eq_of_conjugate
        (M := M) (H := Mx) ⟨x⁻¹, rfl⟩
    have hMxHy :
        classSupportWithin (⊤ : Subgroup G) (sigmaCover Mx) =
          classSupportWithin (⊤ : Subgroup G) (sigmaCover Hy) :=
      classSupport_sigmaCover_eq_of_conjugate
        (M := Mx) (H := Hy) ⟨z, heq⟩
    have hHHy :
        classSupportWithin (⊤ : Subgroup G) (sigmaCover H) =
          classSupportWithin (⊤ : Subgroup G) (sigmaCover Hy) :=
      classSupport_sigmaCover_eq_of_conjugate
        (M := H) (H := Hy) ⟨y⁻¹, rfl⟩
    exact hMMx.trans (hMxHy.trans hHHy.symm)
  have hdis := sigma_support_disjoint hMx hHy hnotRaw
  apply Set.disjoint_left.mp hdis
  · change x⁻¹ * a * x ∈ sigmaCover Mx
    rw [sigma_supportJ]
    exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  · change x⁻¹ * a * x ∈ sigmaCover Hy
    rw [sigma_supportJ]
    refine ⟨b, hb, ?_⟩
    simpa [MulAut.conj_apply] using hy

/-- Every exceptional element has a unique mixed factorization with its
partner component written first. -/
private theorem pTypeTISet_factor_14_9
    {M K : Subgroup G}
    (hMP : M ∈ typePMaximalSubgroups (G := G))
    (hKM : K ≤ M)
    (hHallK : IsHall (kappaPrimes M) (K.subgroupOf M))
    {t : G} (ht : t ∈ pTypeTISet M K) :
    ∃ y : G, y ∈ subgroupNonidentity (pTypePartner M K) ∧
      ∃ y' : G, y' ∈ subgroupNonidentity K ∧ t = y * y' := by
  let N : Subgroup G := normalizerWithin M K
  have hStruct := Ptype_structure hMP hKM hHallK
  have htN : t ∈ N :=
    (sup_le hStruct.normalizer_direct.left_le
      hStruct.normalizer_direct.right_le) ht.1
  let ab : K × pTypePartner M K :=
    hStruct.normalizer_direct.mulEquiv.symm ⟨t, htN⟩
  let a : K := ab.1
  let b : pTypePartner M K := ab.2
  have habG : (a : G) * (b : G) = t := by
    have hab := hStruct.normalizer_direct.mulEquiv.apply_symm_apply
      (⟨t, htN⟩ : N)
    exact congrArg Subtype.val hab
  have ha1 : (a : G) ≠ 1 := by
    intro ha
    apply ht.2
    apply Or.inr
    rw [← habG, ha, one_mul]
    exact b.property
  have hb1 : (b : G) ≠ 1 := by
    intro hb
    apply ht.2
    apply Or.inl
    rw [← habG, hb, mul_one]
    exact a.property
  refine ⟨(b : G), mem_subgroupNonidentity.mpr ⟨b.property, hb1⟩,
    (a : G), mem_subgroupNonidentity.mpr ⟨a.property, ha1⟩, ?_⟩
  calc
    t = (a : G) * (b : G) := habG.symm
    _ = (b : G) * (a : G) :=
      (hStruct.normalizer_direct.commute a b).eq

/-- The raw exceptional set is disjoint from every maximal sigma cover. -/
private theorem pTypeTISet_disjoint_sigmaCover_14_9
    {M K : Subgroup G}
    (hMP : M ∈ typePMaximalSubgroups (G := G))
    (hKM : K ≤ M)
    (hHallK : IsHall (kappaPrimes M) (K.subgroupOf M))
    {H : Subgroup G}
    (hH : H ∈ minSimple_max_groups (G := G)) :
    Disjoint (pTypeTISet M K) (sigmaCover H) := by
  apply Set.disjoint_left.2
  intro t htT htH
  rcases htH with ⟨x, hxSigma, hx1, r, hr, htCover⟩
  have ht1 : t ≠ 1 := by
    intro htOne
    exact htT.2 (Or.inl (by simpa [htOne] using K.one_mem))
  have hcovered : SigmaSignalizerAlternative t := by
    refine ⟨x, Msigma_ell1 hH hxSigma hx1, ?_⟩
    rw [htCover]
    simpa using hr
  rcases pTypeTISet_factor_14_9 hMP hKM hHallK htT with
    ⟨y, hy, y', hy', htFactor⟩
  rcases mem_subgroupNonidentity.mp hy with ⟨hyKs, hy1⟩
  rcases mem_subgroupNonidentity.mp hy' with ⟨hyK, hy'1⟩
  have hresidual : SigmaKappaResidualAlternative t := by
    have hStruct := Ptype_structure hMP hKM hHallK
    refine ⟨y, Msigma_ell1 hMP.1
      (centralizerWithin_le_left _ _ hyKs) hy1, M, ?_, ?_, ?_, ?_⟩
    · exact ⟨hMP.1,
        Subgroup.zpowers_le.mpr (centralizerWithin_le_left _ _ hyKs)⟩
    · simpa [htFactor] using hy'1
    · have hcomm := hStruct.normalizer_direct.commute
        ⟨y', hyK⟩ ⟨y, hyKs⟩
      have hyres : y⁻¹ * t = y' := by
        rw [htFactor]
        simp
      refine ⟨hKM (hyres.symm ▸ hyK), ?_⟩
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [hyres]
      simpa using hcomm.symm.zpow_left n |>.eq
    · have horder : orderOf y' ∣ Nat.card K := by
        exact K.orderOf_dvd_natCard hyK
      have hKPi : IsPiNumber (kappaPrimes M) (Nat.card K) := by
        simpa [MathlibSupport.natCard_subgroupOf_eq hKM] using
          hHallK.isPiNumber_card
      simpa [htFactor] using
        hKPi.of_dvd horder
  exact (sigma_decomposition_dichotomy ht1).exclusive
    ⟨hcovered, hresidual⟩

/-- The exceptional class support and every maximal sigma support are
disjoint. -/
private theorem pTypeExceptionalSupport_disjoint_sigmaSupport
    {M K Mstar H : Subgroup G}
    (hMP : M ∈ typePMaximalSubgroups (G := G))
    (hKM : K ≤ M)
    (hHallK : IsHall (kappaPrimes M) (K.subgroupOf M))
    (_hEmbed : PTypeEmbedding M K Mstar)
    (hH : H ∈ minSimple_max_groups (G := G)) :
    Disjoint (pTypeExceptionalSupport M K)
      (classSupportWithin (⊤ : Subgroup G) (sigmaCover H)) := by
  exact classSupport_disjoint_of_disjoint_sigmaCover_14_9
    (fun hL ↦ pTypeTISet_disjoint_sigmaCover_14_9
      hMP hKM hHallK hL) hH

/-- Consequently the exceptional support is not one of the ordinary sigma
supports in the global cover. -/
private theorem pTypeExceptionalSupport_not_sigmaSupport
    {M K Mstar H : Subgroup G}
    (hMP : M ∈ typePMaximalSubgroups (G := G))
    (hKM : K ≤ M)
    (hHallK : IsHall (kappaPrimes M) (K.subgroupOf M))
    (hEmbed : PTypeEmbedding M K Mstar)
    (hH : H ∈ minSimple_max_groups (G := G))
    (hEq : classSupportWithin (⊤ : Subgroup G) (sigmaCover H) =
      pTypeExceptionalSupport M K) : False := by
  have hdis := pTypeExceptionalSupport_disjoint_sigmaSupport
    hMP hKM hHallK hEmbed hH
  rw [hEq] at hdis
  obtain ⟨x, hx⟩ :=
    classSupportWithin_nonempty_of_normalizedTI hEmbed.normalizedTI
  exact (Set.disjoint_left.mp hdis) hx hx

private theorem map_conj_eq_self_of_mem_14_9
    (H : Subgroup G) {g : G} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg)
  · intro x hx
    refine ⟨g⁻¹ * x * g,
      H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

/-- Residual data based in a P-type maximal subgroup puts the element in
the exceptional class support associated with any selected kappa Hall
subgroup of that maximal subgroup. -/
private theorem exceptionalSupport_mem_of_residual_self_14_9
    {J L : Subgroup G}
    (hJP : J ∈ typePMaximalSubgroups (G := G))
    (hLJ : L ≤ J)
    (hHallL : IsHall (kappaPrimes J) (L.subgroupOf J))
    (hcyclic : IsCyclic (pTypeJoin J L))
    (hcentral : ∀ {v : G}, v ∈ L → v ≠ 1 →
      centralizerWithin J (Subgroup.zpowers v) = pTypeJoin J L)
    {t y : G}
    (hyLength : sigmaLength y = 1)
    (hySigma : y ∈ sigmaCore J)
    (hy'1 : y⁻¹ * t ≠ 1)
    (hy'Cent : y⁻¹ * t ∈ elementCentralizerWithin J y)
    (hy'Kappa : IsPiNumber (kappaPrimes J) (orderOf (y⁻¹ * t))) :
    t ∈ pTypeExceptionalSupport J L := by
  let v : G := y⁻¹ * t
  let A : Subgroup G := Subgroup.zpowers v
  have hAJ : A ≤ J := Subgroup.zpowers_le.mpr hy'Cent.1
  have hApi : IsPiNumber (kappaPrimes J) (Nat.card A) := by
    simpa [A, Nat.card_zpowers, v] using hy'Kappa
  obtain ⟨a, hALa, -, -, -, -, -⟩ :=
    exists_ambient_isHall_map_conj_ge_of_isSolvable
      hAJ hLJ (mmax_sol hJP.1) hApi hHallL
  let e : G ≃* G := MulAut.conj (a : G)⁻¹
  let yc : G := e y
  let vc : G := e v
  let tc : G := e t
  have hvcL : vc ∈ L := by
    have hvLa : v ∈ L.map (MulAut.conj (a : G)).toMonoidHom :=
      hALa (Subgroup.mem_zpowers v)
    have hvBack := Subgroup.mem_map_equiv.mp hvLa
    simpa [e, vc] using hvBack
  have hycSigma : yc ∈ sigmaCore J := by
    have hJmap :
        J.map e.toMonoidHom = J := by
      exact map_conj_eq_self_of_mem_14_9 J (J.inv_mem a.property)
    have hcoreMap :
        (sigmaCore J).map e.toMonoidHom = sigmaCore J := by
      rw [← sigmaCore_conj, hJmap]
    rw [← hcoreMap]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hySigma
  have hyc1 : yc ≠ 1 := by
    simpa [yc] using e.injective.ne (ell_sigma1P.mp hyLength).1
  have hvc1 : vc ≠ 1 := by
    simpa [vc] using e.injective.ne (by simpa [v] using hy'1)
  have hcomm : Commute v y := by
    exact (hy'Cent.2 y (Subgroup.mem_zpowers y)).symm
  have hcommc : Commute vc yc := by
    exact hcomm.map e.toMonoidHom
  have hycCent : yc ∈ centralizerWithin J (Subgroup.zpowers vc) := by
    refine ⟨(sigmaCore_le J) hycSigma, ?_⟩
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact hcommc.zpow_left n |>.eq
  have hycJoin : yc ∈ pTypeJoin J L := by
    rw [← hcentral hvcL hvc1]
    exact hycCent
  letI : IsCyclic (pTypeJoin J L) := hcyclic
  have hycPartner : yc ∈ pTypePartner J L := by
    refine ⟨hycSigma, ?_⟩
    intro l hl
    exact (congrArg Subtype.val
        (mul_comm
        (⟨yc, hycJoin⟩ : pTypeJoin J L)
        (⟨l, (show L ≤ pTypeJoin J L from le_sup_left) hl⟩ :
          pTypeJoin J L))).symm
  have htcFactor : tc = yc * vc := by
    calc
      tc = e (y * v) := by simp [tc, v]
      _ = yc * vc := by simp [yc, vc]
  have hStruct := Ptype_structure hJP hLJ hHallL
  have htcT : tc ∈ pTypeTISet J L := by
    refine ⟨?_, ?_⟩
    · rw [htcFactor]
      exact (pTypeJoin J L).mul_mem
        ((show pTypePartner J L ≤ pTypeJoin J L from le_sup_right)
          hycPartner)
        ((show L ≤ pTypeJoin J L from le_sup_left) hvcL)
    · rintro (htcL | htcPartner)
      · rw [htcFactor] at htcL
        have hycL : yc ∈ L := by
          have := L.mul_mem htcL (L.inv_mem hvcL)
          simpa [mul_assoc] using this
        have hycN : yc ∈ normalizerWithin J L :=
          hStruct.normalizer_direct.right_le hycPartner
        have hycInf :
            (⟨yc, hycN⟩ : normalizerWithin J L) ∈
              (L.subgroupOf (normalizerWithin J L)) ⊓
                ((pTypePartner J L).subgroupOf (normalizerWithin J L)) :=
          ⟨hycL, hycPartner⟩
        exact hyc1 (congrArg Subtype.val
          (Subgroup.mem_bot.mp
            (hStruct.normalizer_direct.complement.disjoint.le_bot hycInf)))
      · rw [htcFactor] at htcPartner
        have hvcPartner : vc ∈ pTypePartner J L := by
          have := (pTypePartner J L).mul_mem
            ((pTypePartner J L).inv_mem hycPartner) htcPartner
          simpa [mul_assoc] using this
        have hvcN : vc ∈ normalizerWithin J L :=
          hStruct.normalizer_direct.left_le hvcL
        have hvcInf :
            (⟨vc, hvcN⟩ : normalizerWithin J L) ∈
              (L.subgroupOf (normalizerWithin J L)) ⊓
                ((pTypePartner J L).subgroupOf (normalizerWithin J L)) :=
          ⟨hvcL, hvcPartner⟩
        exact hvc1 (congrArg Subtype.val
          (Subgroup.mem_bot.mp
            (hStruct.normalizer_direct.complement.disjoint.le_bot hvcInf)))
  refine ⟨tc, htcT, (a : G)⁻¹, Subgroup.mem_top _, ?_⟩
  simp only [tc, e, MulAut.conj_apply, inv_inv]
  group

/-- Transport the preceding residual calculation from a conjugate maximal
subgroup back to the selected representative. -/
private theorem exceptionalSupport_mem_of_residual_conjugate_14_9
    {J L H : Subgroup G}
    (hJP : J ∈ typePMaximalSubgroups (G := G))
    (hLJ : L ≤ J)
    (hHallL : IsHall (kappaPrimes J) (L.subgroupOf J))
    (hcyclic : IsCyclic (pTypeJoin J L))
    (hcentral : ∀ {v : G}, v ∈ L → v ≠ 1 →
      centralizerWithin J (Subgroup.zpowers v) = pTypeJoin J L)
    (hJH : AreConjugateSubgroups J H)
    {t y : G}
    (hyLength : sigmaLength y = 1)
    (hySigma : y ∈ sigmaCore H)
    (hy'1 : y⁻¹ * t ≠ 1)
    (hy'Cent : y⁻¹ * t ∈ elementCentralizerWithin H y)
    (hy'Kappa : IsPiNumber (kappaPrimes H) (orderOf (y⁻¹ * t))) :
    t ∈ pTypeExceptionalSupport J L := by
  rcases hJH with ⟨g, rfl⟩
  let e : G ≃* G := MulAut.conj g⁻¹
  let yc : G := e y
  let tc : G := e t
  have hresMap : yc⁻¹ * tc = e (y⁻¹ * t) := by
    simp [yc, tc]
  have hycLength : sigmaLength yc = 1 := by
    exact (ell_sigmaJ y g⁻¹).trans hyLength
  have hycSigma : yc ∈ sigmaCore J := by
    rw [sigmaCore_conj] at hySigma
    have := Subgroup.mem_map_equiv.mp hySigma
    simpa [e, yc] using this
  have hyc'1 : yc⁻¹ * tc ≠ 1 := by
    have hmapNe := e.injective.ne hy'1
    rw [hresMap]
    simpa using hmapNe
  have hyc'Cent :
      yc⁻¹ * tc ∈ elementCentralizerWithin J yc := by
    have hvJ := Subgroup.mem_map_equiv.mp hy'Cent.1
    refine ⟨?_, ?_⟩
    · have heq : yc⁻¹ * tc = g⁻¹ * (y⁻¹ * t) * g := by
        simp only [yc, tc, e, MulAut.conj_apply, map_inv, map_mul]
        group
      rw [heq]
      exact hvJ
    · intro z hz
      have hzMap : z ∈
          (Subgroup.zpowers y).map e.toMonoidHom := by
        simpa [yc, MonoidHom.map_zpowers] using hz
      obtain ⟨z₀, hz₀, rfl⟩ := hzMap
      have hcomm := hy'Cent.2 z₀ hz₀
      simpa [hresMap] using congrArg e hcomm
  have hyc'Kappa :
      IsPiNumber (kappaPrimes J) (orderOf (yc⁻¹ * tc)) := by
    intro p hp hpOrder
    apply (kappaJ J g).mp
    apply hy'Kappa hp
    have horder :
        orderOf (e (y⁻¹ * t)) = orderOf (y⁻¹ * t) :=
      orderOf_injective e.toMonoidHom e.injective (y⁻¹ * t)
    rw [← horder]
    rw [← hresMap]
    exact hpOrder
  have htc := exceptionalSupport_mem_of_residual_self_14_9
    hJP hLJ hHallL hcyclic hcentral
      hycLength hycSigma hyc'1 hyc'Cent hyc'Kappa
  apply (classSupportWithin_rightConj_iff
    (G := (⊤ : Subgroup G)) (S := pTypeTISet J L)
    (x := t) (g := g) (Subgroup.mem_top g)).mp
  simpa [pTypeExceptionalSupport, e, tc, MulAut.conj_apply] using htc

/-- The residual alternative of Lemma 14.6 is captured by the exceptional
support belonging to either representative of the two P-type conjugacy
classes. -/
private theorem pTypeExceptionalSupport_mem_of_residual
    {M K Mstar : Subgroup G}
    (hMP : M ∈ typePMaximalSubgroups (G := G))
    (hKM : K ≤ M)
    (hHallK : IsHall (kappaPrimes M) (K.subgroupOf M))
    (hEmbed : PTypeEmbedding M K Mstar)
    {t : G} (hresidual : SigmaKappaResidualAlternative t) :
    t ∈ pTypeExceptionalSupport M K := by
  rcases hresidual with
    ⟨y, hyLength, H, hHy, hy'1, hy'Cent, hy'Kappa⟩
  have horderNe : orderOf (y⁻¹ * t) ≠ 1 := by
    simpa [orderOf_eq_one_iff] using hy'1
  obtain ⟨q, hq, hqOrder⟩ := Nat.exists_prime_and_dvd horderNe
  have hqKappa : q ∈ kappaPrimes H := hy'Kappa hq hqOrder
  have hHP : H ∈ typePMaximalSubgroups (G := G) :=
    (PtypeP hHy.1).2 ⟨q, hqKappa⟩
  have hySigma : y ∈ sigmaCore H :=
    hHy.2 (Subgroup.mem_zpowers y)
  rcases hEmbed.typeP_transitive hHP with hMH | hMstarH
  · exact exceptionalSupport_mem_of_residual_conjugate_14_9
      hMP hKM hHallK hEmbed.cyclicStructure.cyclic_join
        hEmbed.cyclicStructure.centralizer_left hMH
          hyLength hySigma hy'1 hy'Cent hy'Kappa
  · let Ks : Subgroup G := pTypePartner M K
    have hPartnerSwap : pTypePartner Mstar Ks = K := by
      simpa [Ks, pTypePartner] using hEmbed.doubleCentralizer
    have hJoinSwap : pTypeJoin Mstar Ks = pTypeJoin M K := by
      change Ks ⊔ pTypePartner Mstar Ks = K ⊔ Ks
      rw [hPartnerSwap, sup_comm]
    have hcyclicSwap : IsCyclic (pTypeJoin Mstar Ks) := by
      rw [hJoinSwap]
      exact hEmbed.cyclicStructure.cyclic_join
    have hcentralSwap : ∀ {v : G}, v ∈ Ks → v ≠ 1 →
        centralizerWithin Mstar (Subgroup.zpowers v) =
          pTypeJoin Mstar Ks := by
      intro v hv hv1
      rw [hJoinSwap]
      exact hEmbed.cyclicStructure.centralizer_right hv hv1
    have htStar := exceptionalSupport_mem_of_residual_conjugate_14_9
      hEmbed.Mstar_typeP hEmbed.Kstar_le_Mstar
        hEmbed.Kstar_hall_kappa hcyclicSwap hcentralSwap hMstarH
          hyLength hySigma hy'1 hy'Cent hy'Kappa
    have hTISetSwap : pTypeTISet Mstar Ks = pTypeTISet M K := by
      ext z
      simp [pTypeTISet, hJoinSwap, hPartnerSwap, Ks,
        Set.union_comm]
    change t ∈ classSupportWithin (⊤ : Subgroup G)
      (pTypeTISet Mstar Ks) at htStar
    rw [hTISetSwap] at htStar
    exact htStar

private theorem IsSetPartition.exists_mem
    {P : Set (Set G)} {D : Set G}
    (hP : IsSetPartition P D) {x : G} (hx : x ∈ D) :
    ∃ A ∈ P, x ∈ A := by
  have hx' : x ∈ ⋃₀ P := hP.1.symm ▸ hx
  exact Set.mem_sUnion.mp hx'

private theorem IsSetPartition.subset
    {P : Set (Set G)} {D : Set G}
    (hP : IsSetPartition P D) {A : Set G} (hA : A ∈ P) :
    A ⊆ D := by
  intro x hx
  rw [← hP.1]
  exact Set.mem_sUnion_of_mem hx hA

/-- A mixed element in the exceptional P-type support has exactly one
ordinary sigma component and a sigma-complement component of sigma length
one in the partner maximal subgroup. -/
private theorem sigmaLength_le_two_of_mem_pTypeExceptionalSupport
    {M K : Subgroup G}
    (hMP : M ∈ typePMaximalSubgroups (G := G))
    (hKM : K ≤ M)
    (hHallK : IsHall (kappaPrimes M) (K.subgroupOf M))
    {x : G} (hx : x ∈ pTypeExceptionalSupport M K) :
    sigmaLength x ≤ 2 := by
  rcases hx with ⟨t, ht, g, -, rfl⟩
  obtain ⟨Mstar, hEmbed⟩ := Ptype_embedding hMP hKM hHallK
  rcases pTypeTISet_factor_14_9 hMP hKM hHallK ht with
    ⟨y, hy, y', hy', htFactor⟩
  rcases mem_subgroupNonidentity.mp hy with ⟨hyPartner, hy1⟩
  rcases mem_subgroupNonidentity.mp hy' with ⟨hyK, hy'1⟩
  have hcomm : Commute y' y := by
    exact (Ptype_structure hMP hKM hHallK).normalizer_direct.commute
      ⟨y', hyK⟩ ⟨y, hyPartner⟩
  have hySigma :
      IsPiNumber (sigmaPrimes M) (orderOf y) := by
    exact (sigmaCore_isPiNumber M).of_dvd
      ((sigmaCore M).orderOf_dvd_natCard
        (centralizerWithin_le_left _ _ hyPartner))
  have hy'Compl :
      IsPiNumber (sigmaPrimes M)ᶜ (orderOf y') := by
    have hy'Kappa :
        IsPiNumber (kappaPrimes M) (orderOf y') := by
      have hKPi : IsPiNumber (kappaPrimes M) (Nat.card K) := by
        simpa [MathlibSupport.natCard_subgroupOf_eq hKM] using
          hHallK.isPiNumber_card
      exact hKPi.of_dvd (by
        exact K.orderOf_dvd_natCard hyK)
    exact hy'Kappa.mono (kappa_sigma' M)
  have htFactor' : t = y' * y := by
    rw [hcomm.eq]
    exact htFactor
  have hcomponent : sigmaComponent M t = y := by
    rw [htFactor']
    exact sigmaComponent_mul_eq_right_of_compl_left_of_sigma_right
      M hcomm hy'Compl hySigma
  have hcomplement : sigmaComplementComponent M t = y' := by
    rw [htFactor']
    exact sigmaComplementComponent_mul_eq_left_of_compl_left_of_sigma_right
      M hcomm hy'Compl hySigma
  have hyDecomp : y ∈ sigmaDecomposition t :=
    ⟨hy1, M, hMP.1, hcomponent.symm⟩
  have hy'Mstar : y' ∈ sigmaCore Mstar := by
    apply centralizerWithin_le_left _ _
    rw [hEmbed.doubleCentralizer]
    exact hyK
  have hy'Length : sigmaLength y' = 1 :=
    Msigma_ell1 hEmbed.Mstar_typeP.1 hy'Mstar hy'1
  have hdecomp :
      sigmaDecomposition y' = sigmaDecomposition t \ {y} := by
    simpa [hcomplement, hcomponent] using
      sigma_decomposition_constt' (x := t) hMP.1
  have htLength : sigmaLength t = 2 := by
    have hne : (sigmaDecomposition t).ncard ≠ 0 :=
      Set.ncard_ne_zero_of_mem hyDecomp
    have hcard : sigmaLength y' + 1 = sigmaLength t := by
      rw [sigmaLength, hdecomp, sigmaLength,
        Set.ncard_diff_singleton_of_mem hyDecomp]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hne)
    omega
  simpa [MulAut.conj_apply, htLength] using
    (ell_sigmaJ t g⁻¹).le

/-! ## Corollaries 14.9 and 14.10 -/

/-- `BGsection14.v: mFT_partition`, Bender--Glauberman Corollary 14.9.

The additional argument `hKM` is the Lean expansion of the containment
which MathComp includes in `kappa(M).-Hall(M) K`. -/
theorem mFT_partition :
    (typePMaximalSubgroups (G := G) = ∅ →
      IsSetPartition (pTypeSupportCover (G := G))
        (nonidentitySet G)) ∧
    ∀ (M K : Subgroup G),
      M ∈ typePMaximalSubgroups (G := G) →
      K ≤ M →
      IsHall (kappaPrimes M) (K.subgroupOf M) →
      IsSetPartition
          ({pTypeExceptionalSupport M K} ∪
            pTypeSupportCover (G := G))
          (nonidentitySet G) ∧
        pTypeExceptionalSupport M K ∉
          pTypeSupportCover (G := G) := by
  classical
  have hcover_nonempty :
      (∅ : Set G) ∉ pTypeSupportCover (G := G) := by
    rintro ⟨M, hM, hzero⟩
    have hsigma : sigmaCore M ≠ ⊥ := Msigma_neq1 hM
    obtain ⟨x, hx1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hsigma
    have hxSigma : (x : G) ∈ sigmaCore M := x.property
    have hxG1 : (x : G) ≠ 1 := by
      intro hx
      exact hx1 (Subtype.ext hx)
    have hxCover : (x : G) ∈ sigmaCover M := by
      exact ⟨(x : G), hxSigma, hxG1, 1,
        (ftSignalizer (x : G)).one_mem, by simp⟩
    have hxClass := mem_classSupportWithin_top_of_mem hxCover
    have hxEmpty : (x : G) ∈ (∅ : Set G) := hzero ▸ hxClass
    exact hxEmpty
  have hcover_pairwise :
      (pTypeSupportCover (G := G)).PairwiseDisjoint id := by
    rw [Set.pairwiseDisjoint_iff]
    rintro A ⟨M, hM, rfl⟩ B ⟨H, hH, rfl⟩ hinter
    by_contra hne
    have hdis := classSupport_sigmaCover_disjoint_of_ne_14_9
      hM hH hne
    rcases hinter with ⟨x, hxM, hxH⟩
    exact (Set.disjoint_left.mp hdis) hxM hxH
  have hcover_sub :
      ⋃₀ (pTypeSupportCover (G := G)) ⊆ nonidentitySet G := by
    intro x hx
    obtain ⟨A, ⟨M, hM, rfl⟩, hxA⟩ := Set.mem_sUnion.mp hx
    exact classSupport_sigmaCover_subset_nonidentity hM hxA
  constructor
  · intro hPempty
    apply And.intro
    · apply Set.Subset.antisymm hcover_sub
      intro x hx
      have hx1 : x ≠ 1 := by simpa [nonidentitySet] using hx
      rcases (sigma_decomposition_dichotomy hx1).exhaustive with
        hcovered | hresidual
      · obtain ⟨y, hyLength, hyx⟩ := hcovered
        obtain ⟨M, hM⟩ := sigmaMaximalOvergroups_nonempty hyLength
        apply Set.mem_sUnion_of_mem
          (mem_classSupportWithin_top_of_mem
            (sigmaCover_of_signalizer_coset hyLength hM hyx))
        exact ⟨M, hM.1, rfl⟩
      · obtain ⟨y, hyLength, M, hMy, hy'1, hy'M, hy'Kappa⟩ :=
          hresidual
        have horderNe : orderOf (y⁻¹ * x) ≠ 1 := by
          simpa [orderOf_eq_one_iff] using hy'1
        obtain ⟨q, hq, hqOrder⟩ :=
          Nat.exists_prime_and_dvd horderNe
        have hMP : M ∈ typePMaximalSubgroups (G := G) :=
          (PtypeP hMy.1).2 ⟨q, hy'Kappa hq hqOrder⟩
        rw [hPempty] at hMP
        exact hMP.elim
    exact ⟨hcover_pairwise, hcover_nonempty⟩
  · intro M K hMP hKM hHallK
    obtain ⟨Mstar, hEmbed⟩ := Ptype_embedding hMP hKM hHallK
    let C : Set G := pTypeExceptionalSupport M K
    have hC_ne : C.Nonempty := by
      exact classSupportWithin_nonempty_of_normalizedTI hEmbed.normalizedTI
    have hC_not_cover : C ∉ pTypeSupportCover (G := G) := by
      intro hCmem
      obtain ⟨H, hH, hCH⟩ := hCmem
      exact pTypeExceptionalSupport_not_sigmaSupport
        hMP hKM hHallK hEmbed hH hCH
    have hC_disjoint :
        ∀ A ∈ pTypeSupportCover (G := G), Disjoint C A := by
      intro A hA
      obtain ⟨H, hH, rfl⟩ := hA
      exact pTypeExceptionalSupport_disjoint_sigmaSupport
        hMP hKM hHallK hEmbed hH
    have hpair :
        ({C} ∪ pTypeSupportCover (G := G)).PairwiseDisjoint id := by
      exact Set.pairwiseDisjoint_insert.mpr
        ⟨hcover_pairwise, fun A hA _ ↦ hC_disjoint A hA⟩
    have hnonempty :
        (∅ : Set G) ∉ {C} ∪ pTypeSupportCover (G := G) := by
      simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
      exact ⟨fun h ↦ by
        rw [← h] at hC_ne
        exact Set.not_nonempty_empty hC_ne, hcover_nonempty⟩
    have hunion :
        ⋃₀ ({C} ∪ pTypeSupportCover (G := G)) =
          nonidentitySet G := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases Set.mem_sUnion.mp hx with ⟨A, hA, hxA⟩
        rcases hA with rfl | hA
        · exact pTypeExceptionalSupport_subset_nonidentity hEmbed hxA
        · exact hcover_sub (Set.mem_sUnion_of_mem hxA hA)
      · intro x hx
        have hx1 : x ≠ 1 := by simpa [nonidentitySet] using hx
        rcases (sigma_decomposition_dichotomy hx1).exhaustive with
          hcovered | hresidual
        · obtain ⟨y, hyLength, hyx⟩ := hcovered
          obtain ⟨H, hH⟩ := sigmaMaximalOvergroups_nonempty hyLength
          apply Set.mem_sUnion_of_mem
            (mem_classSupportWithin_top_of_mem
              (sigmaCover_of_signalizer_coset hyLength hH hyx))
          exact Or.inr ⟨H, hH.1, rfl⟩
        · exact Set.mem_sUnion_of_mem
            (pTypeExceptionalSupport_mem_of_residual
              hMP hKM hHallK hEmbed hresidual)
            (Or.inl rfl)
    exact ⟨⟨hunion, hpair, hnonempty⟩, by simpa [C] using hC_not_cover⟩

/-- `BGsection14.v: ell_sigma_leq_2`, Bender--Glauberman Corollary 14.10. -/
theorem ell_sigma_leq_2 (x : G) : sigmaLength x ≤ 2 := by
  classical
  by_cases hx1 : x = 1
  · subst x
    have hzero : sigmaLength (1 : G) = 0 :=
      (ell_sigma0P (1 : G)).mpr rfl
    omega
  by_cases hxCover :
      x ∈ ⋃₀ (pTypeSupportCover (G := G))
  · obtain ⟨A, ⟨M, hM, rfl⟩, hxA⟩ := Set.mem_sUnion.mp hxCover
    exact ell_sigma_support_class hM hxA
  obtain hPempty | ⟨M, hMP⟩ :=
    Set.eq_empty_or_nonempty (typePMaximalSubgroups (G := G))
  · have hpart := mFT_partition (G := G) |>.1 hPempty
    exact (hxCover (by
      rw [hpart.1]
      simpa [nonidentitySet] using hx1)).elim
  · have hmaxM : M ∈ minSimple_max_groups (G := G) := hMP.1
    obtain ⟨K, hKM, hHallK⟩ :=
      MathlibSupport.exists_ambient_isHall_of_isSolvable
        (mmax_sol hmaxM) (kappaPrimes M)
    have hpart := mFT_partition (G := G) |>.2 M K hMP hKM hHallK |>.1
    obtain ⟨A, hA, hxA⟩ := IsSetPartition.exists_mem hpart (by
      simpa [nonidentitySet] using hx1)
    rcases hA with rfl | hA
    · exact sigmaLength_le_two_of_mem_pTypeExceptionalSupport
        hMP hKM hHallK hxA
    · exact (hxCover (Set.mem_sUnion_of_mem hxA hA)).elim

/-! ## Lemma 14.11 -/

/-- A subgroup supported on `pi` lies in a normal ambient `pi`-Hall
subgroup.  This local form keeps all three groups in the common ambient
group `G`. -/
private theorem le_normal_isHall_of_isPiNumber_14_11
    {pi : Set ℕ} {C K L : Subgroup G}
    (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    (hLC : L ≤ C) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa [KC] using hKnormal
  have hcop : (Nat.card L).Coprime KC.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    exact (hKHall.isPiNumber_index hp hpIndex) (hLpi hp hpL)
  intro x hxL
  let xC : C := ⟨x, hLC hxL⟩
  let qC : C →* C ⧸ KC := QuotientGroup.mk' KC
  have horderL : orderOf (qC xC) ∣ Nat.card L :=
    (orderOf_map_dvd qC xC).trans (by
      simpa [xC] using L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (qC xC) ∣ KC.index := by
    simpa only [KC.index_eq_card] using orderOf_dvd_natCard (qC xC)
  have hone : orderOf (qC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp hone
  change QuotientGroup.mk' KC xC = 1 at hqOne
  exact (QuotientGroup.eq_one_iff xC).mp hqOne

/-- Ambient form of the defining maximality of the Fitting subgroup. -/
private theorem nilpotent_normal_le_fittingWithin_14_11
    {K H : Subgroup G} (hKH : K ≤ H)
    (hKnormal : (K.subgroupOf H).Normal)
    (hKnil : Group.IsNilpotent K) :
    K ≤ fittingWithin H := by
  let KH : Subgroup H := K.subgroupOf H
  let eKH : KH ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  letI : KH.Normal := hKnormal
  letI : Group.IsNilpotent KH :=
    Group.nilpotent_of_mulEquiv eKH.symm
  have hcore : KH ≤ fittingCore H :=
    nilpotent_normal_le_fittingCore (by infer_instance) (by infer_instance)
  rw [← Subgroup.map_subgroupOf_eq_of_le hKH]
  exact Subgroup.map_mono hcore

/-- A proposition-valued commutativity witness gives the one-step upper
central series proof of nilpotency. -/
private theorem isNilpotent_of_isMulCommutative_14_11
    {K : Type*} [Group K] (hK : IsMulCommutative K) :
    Group.IsNilpotent K := by
  exact ⟨1, Subgroup.upperCentralSeries_one_eq_top_iff.mpr hK⟩

/-- Prime divisors of a sigma complement lie in the three tau classes. -/
private theorem primeSupport_sigma_complement_subset_tau_14_11
    {M E : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    primeSupport (Nat.card E) ⊆
      tau1Primes M ∪ tau2Primes M ∪ tau3Primes M := by
  intro r hrE
  have hr : r.Prime := hrE.1
  letI : Fact r.Prime := ⟨hr⟩
  have hrMcard : r ∣ Nat.card M :=
    hrE.2.trans (Subgroup.card_dvd_of_le hEM)
  have hrNotSigma : r ∉ sigmaPrimes M := by
    have hrEsub : r ∣ Nat.card (E.subgroupOf M) := by
      simpa [MathlibSupport.natCard_subgroupOf_eq hEM] using hrE.2
    exact hHall.isPiNumber_card hr hrEsub
  obtain ⟨x, hxorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := M) r hrMcard
  let X : Subgroup G := (Subgroup.zpowers x).map M.subtype
  have hXcard : Nat.card X = r := by
    dsimp only [X]
    rw [Subgroup.card_map_of_injective M.subtype_injective,
      Nat.card_zpowers, hxorder]
  have hXrank : IsElementaryAbelianOfRank r 1 X :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
  have hRankOne : HasElementaryAbelianRankAtLeast r 1 M :=
    ⟨X, Subgroup.map_subtype_le _, hXrank⟩
  by_cases hRankTwo : HasElementaryAbelianRankAtLeast r 2 M
  · have hNoRankThree :
        ¬ HasElementaryAbelianRankAtLeast r 3 M := by
      intro hRankThree
      exact hrNotSigma (alpha_sub_sigma hM ⟨hr, hRankThree⟩)
    exact Or.inl (Or.inr
      ⟨hr, hrNotSigma, hRankTwo, hNoRankThree⟩)
  · by_cases hrDer : r ∣ Nat.card (_root_.commutator M)
    · exact Or.inr
        ⟨hr, hrNotSigma, hRankOne, hRankTwo, hrDer⟩
    · exact Or.inl (Or.inl
        ⟨hr, hrNotSigma, hRankOne, hRankTwo, hrDer⟩)

/-- In an F-type sigma complement, a rank-one subgroup not contained in
the Fitting subgroup has tau-one prime. -/
private theorem typeF_nonFitting_rankOne_tau1
    {M E Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hMF : M ∈ typeFMaximalSubgroups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hQ : RankOneLineIn q E Q)
    (hQnotF : ¬ Q ≤ fittingWithin E) :
    q ∈ tau1Primes M := by
  have hqE : q ∈ primeSupport (Nat.card E) := by
    refine ⟨Fact.out, ?_⟩
    have hQcard : Nat.card Q = q := by
      simpa using hQ.2.card_eq
    have hqQ : q ∣ Nat.card Q := by rw [hQcard]
    exact hqQ.trans (Subgroup.card_dvd_of_le hQ.1)
  rcases primeSupport_sigma_complement_subset_tau_14_11
      hMF.1 hEM hHallE hqE with (hqTau1 | hqTau2) | hqTau3
  · exact hqTau1
  · obtain ⟨A, hAE, _hAM, hA⟩ := ex_tau2Elem hEM hHallE hqTau2
    have hTau := tau2_compl_context hMF.1 hEM hHallE
      hqTau2 hAE hA
    have hQA : Q ≤ A :=
      (hTau.rankOne_iff Q).mp ⟨hQ.1, hQ.2⟩ |>.1
    have hAF : A ≤ fittingWithin E :=
      nilpotent_normal_le_fittingWithin_14_11 hAE hTau.A_normal
        hA.isPGroup.isNilpotent
    exact (hQnotF (hQA.trans hAF)).elim
  · obtain ⟨E₁, hE₁E, hHallE₁⟩ :=
      (ex_tau13_compl hEM hHallE).1
    obtain ⟨E₃, hE₃E, hHallE₃⟩ :=
      (ex_tau13_compl hEM hHallE).2
    obtain ⟨E₂, _hE₂E, _hHallE₂, hCompl⟩ :=
      ex_tau2_compl hEM hHallE hE₁E hHallE₁ hE₃E hHallE₃
    have hComplCtx := sigma_compl_context hMF.1 hCompl
    have hQE₃ : Q ≤ E₃ :=
      le_normal_isHall_of_isPiNumber_14_11
        hComplCtx.E₃_normal hHallE₃ hQ.1
          (hQ.2.isPGroup.isPiNumber_natCard hqTau3)
    have hE₃F : E₃ ≤ fittingWithin E :=
      nilpotent_normal_le_fittingWithin_14_11 hE₃E
        hComplCtx.E₃_normal
          (isNilpotent_of_isMulCommutative_14_11
            hComplCtx.E₃_cyclic.isMulCommutative)
    exact (hQnotF (hQE₃.trans hE₃F)).elim

/-- Cauchy's theorem in the rank-one subgroup language used in the closing
Section 14 arguments. -/
private theorem rankOneLineIn_of_prime_dvd_14
    {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hpK : p ∣ Nat.card K) :
    ∃ P : Subgroup G, RankOneLineIn p K P := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
  let P : Subgroup G := (Subgroup.zpowers x).map K.subtype
  have hcardP : Nat.card P = p := by
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Nat.card_zpowers, hx]
  exact ⟨P, Subgroup.map_subtype_le _,
    isElementaryAbelianOfRank_one_of_card_eq_prime hcardP⟩

private theorem rankOneLineIn_map_conj_14
    {p : ℕ} {M P : Subgroup G} (z : G)
    (hP : RankOneLineIn p M P) :
    RankOneLineIn p
      (M.map (MulAut.conj z).toMonoidHom)
      (P.map (MulAut.conj z).toMonoidHom) := by
  exact ⟨Subgroup.map_mono hP.1,
    hP.2.map_of_injective (MulAut.conj z).toMonoidHom
      (MulAut.conj z).injective⟩

private theorem exists_sylow_containing_rankOneLine_14
    {p : ℕ} [Fact p.Prime] {M P : Subgroup G}
    (hP : RankOneLineIn p M P) :
    ∃ S : Sylow p M, P ≤ ambientSylow M S := by
  let PM : Subgroup M := P.subgroupOf M
  have hPMp : IsPGroup p PM := hP.2.isPGroup.comap_subtype
  obtain ⟨S, hPMS⟩ := hPMp.exists_le_sylow
  refine ⟨S, ?_⟩
  intro x hx
  let xM : M := ⟨x, hP.1 hx⟩
  have hxPM : xM ∈ PM := hx
  exact ⟨xM, hPMS hxPM, rfl⟩

private theorem ambientSylow_isCyclic_of_no_rankTwo_14
    {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hNoRank : ¬ HasElementaryAbelianRankAtLeast p 2 M)
    (S : Sylow p M) : IsCyclic (ambientSylow M S) := by
  have hNoRankS :
      ¬ ∃ E : Subgroup S, IsElementaryAbelianOfRank p 2 E := by
    rintro ⟨E, hE⟩
    let EG : Subgroup G :=
      (E.map (S : Subgroup M).subtype).map M.subtype
    have hEGM : EG ≤ M :=
      (Subgroup.map_subtype_le
        (E.map (S : Subgroup M).subtype))
    have hEG : IsElementaryAbelianOfRank p 2 EG :=
      (hE.map_of_injective (S : Subgroup M).subtype
        (S : Subgroup M).subtype_injective).map_of_injective
          M.subtype M.subtype_injective
    exact hNoRank ⟨EG, hEGM, hEG⟩
  have hScard : Nat.card (ambientSylow M S) = Nat.card S := by
    rw [ambientSylow,
      Subgroup.card_map_of_injective M.subtype_injective]
  have hSodd : Odd (Nat.card S) := by
    rw [← hScard]
    exact mFT_odd (ambientSylow M S)
  have hScyclic : IsCyclic S :=
    (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
      S.isPGroup' hSodd).mpr hNoRankS
  let f : S →* ambientSylow M S :=
    M.subtype.subgroupMap (S : Subgroup M)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply M.subtype_injective
      change (f a : G) = (f b : G)
      exact congrArg Subtype.val hab
    · rintro ⟨x, hx⟩
      rcases hx with ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  let e : S ≃* ambientSylow M S := MulEquiv.ofBijective f hf
  exact e.isCyclic.mp hScyclic

private theorem rankOneLine_eq_sylowOmegaOne_14
    {p : ℕ} [Fact p.Prime] {M P : Subgroup G}
    (S : Sylow p M) (hScyclic : IsCyclic (ambientSylow M S))
    (hP : RankOneLineIn p M P)
    (hPS : P ≤ ambientSylow M S) :
    P = (omegaOne p (ambientSylow M S)).map
      (ambientSylow M S).subtype := by
  let A : Subgroup G :=
    (omegaOne p (ambientSylow M S)).map
      (ambientSylow M S).subtype
  have hPA : P ≤ A := by
    intro x hx
    let xS : ambientSylow M S := ⟨x, hPS hx⟩
    have hxpow : xS ^ p = 1 := by
      apply Subtype.ext
      simpa [xS] using hP.2.pow_eq_one ⟨x, hx⟩
    exact ⟨xS, mem_omegaOne_of_pow_eq_one p hxpow, rfl⟩
  have hSnontrivial : Nat.card (ambientSylow M S) ≠ 1 := by
    intro hcard
    have hPdvdOne : Nat.card P ∣ 1 := by
      simpa [hcard] using Subgroup.card_dvd_of_le hPS
    have hPcardOne : Nat.card P = 1 :=
      Nat.eq_one_of_dvd_one hPdvdOne
    rw [hP.2.card_eq, pow_one] at hPcardOne
    exact (Fact.out : p.Prime).ne_one hPcardOne
  letI : IsCyclic (ambientSylow M S) := hScyclic
  have hAmbientP : IsPGroup p (ambientSylow M S) :=
    S.isPGroup'.map M.subtype
  have hcardOmega : Nat.card (omegaOne p (ambientSylow M S)) = p :=
    card_omegaOne_of_isCyclic_isPGroup (Fact.out : p.Prime)
      hAmbientP hSnontrivial
  apply Subgroup.eq_of_le_of_card_ge hPA
  dsimp only [A]
  rw [hP.2.card_eq, pow_one,
    Subgroup.card_map_of_injective
      (ambientSylow M S).subtype_injective, hcardOmega]

private theorem rankOneLines_conjugate_of_no_rankTwo_14
    {p : ℕ} [Fact p.Prime] {M P Q : Subgroup G}
    (hNoRank : ¬ HasElementaryAbelianRankAtLeast p 2 M)
    (hP : RankOneLineIn p M P) (hQ : RankOneLineIn p M Q) :
    ∃ m : M, P.map (MulAut.conj (m : G)).toMonoidHom = Q := by
  obtain ⟨S, hPS⟩ := exists_sylow_containing_rankOneLine_14 hP
  obtain ⟨T, hQT⟩ := exists_sylow_containing_rankOneLine_14 hQ
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M S T
  let e : G ≃* G := MulAut.conj (m : G)
  have hST :
      (ambientSylow M S).map e.toMonoidHom = ambientSylow M T := by
    have hsmul : ((m • S : Sylow p M) : Subgroup M) =
        (T : Subgroup M) :=
      congrArg (fun U : Sylow p M ↦ (U : Subgroup M)) hm
    rw [ambientSylow, ambientSylow, ← hsmul]
    change ((S : Subgroup M).map M.subtype).map e.toMonoidHom =
      ((S : Subgroup M).map (MulAut.conj m).toMonoidHom).map M.subtype
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hPmapT : P.map e.toMonoidHom ≤ ambientSylow M T := by
    rw [← hST]
    exact Subgroup.map_mono hPS
  have hPmap : RankOneLineIn p M (P.map e.toMonoidHom) := by
    have hMmap : M.map e.toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer m.property)
    have htmp := rankOneLineIn_map_conj_14 (z := (m : G)) hP
    change RankOneLineIn p (M.map e.toMonoidHom)
      (P.map e.toMonoidHom) at htmp
    rw [hMmap] at htmp
    exact htmp
  have hTcyclic := ambientSylow_isCyclic_of_no_rankTwo_14 hNoRank T
  have hPomega := rankOneLine_eq_sylowOmegaOne_14
    T hTcyclic hPmap hPmapT
  have hQomega := rankOneLine_eq_sylowOmegaOne_14
    T hTcyclic hQ hQT
  exact ⟨m, hPomega.trans hQomega.symm⟩

/-- The Fitting subgroup of the sigma complement has order prime to a
tau-one line that it does not contain. -/
private theorem fittingWithin_isPrimeComplement_of_tau1_rankOne_not_le
    {M E Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hEM : E ≤ M)
    (_hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hqTau : q ∈ tau1Primes M)
    (hQ : RankOneLineIn q E Q)
    (hQnotF : ¬ Q ≤ fittingWithin E) :
    IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card (fittingWithin E)) := by
  intro r hr hrdvd
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hrq
  subst r
  obtain ⟨P, hPF, hP⟩ :=
    rankOneLineIn_of_prime_dvd_14
      (G := G) (K := fittingWithin E) (p := q) hrdvd
  have hPE : P ≤ E := hPF.trans (fittingWithin_le E)
  have hNoRankE :
      ¬ HasElementaryAbelianRankAtLeast q 2 E := by
    rintro ⟨B, hBE, hB⟩
    exact hqTau.2.2.2.1 ⟨B, hBE.trans hEM, hB⟩
  obtain ⟨e, he⟩ :=
    rankOneLines_conjugate_of_no_rankTwo_14
      hNoRankE ⟨hPE, hP⟩ hQ
  apply hQnotF
  have heNorm : (e : G) ∈
      Subgroup.normalizer (fittingWithin E : Set G) :=
    fittingWithin_le_normalizer E e.property
  have hmapF :
      (fittingWithin E).map (MulAut.conj (e : G)).toMonoidHom =
        fittingWithin E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp heNorm
  rw [← he, ← hmapF]
  exact Subgroup.map_mono hPF

/-- The source Frattini argument: if `K = [E,Q]` is a normal `q'`-subgroup
and `Q` has order `q`, then the coprime action on `K` is perfect. -/
private theorem commutator_rankOne_eq_self
    {E Q K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hQE : Q ≤ E)
    (hKnormalE : (K.subgroupOf E).Normal)
    (hKq' : IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card K))
    (hQ : RankOneLineIn q E Q)
    (hKdef : K = ⁅E, Q⁆) :
    ⁅K, Q⁆ = K := by
  classical
  let KE : Subgroup E := K.subgroupOf E
  let QE : Subgroup E := Q.subgroupOf E
  have hKE : K ≤ E := by
    rw [hKdef]
    exact (Subgroup.commutator_mono le_rfl hQE).trans
      (Subgroup.commutator_le_self E)
  letI : KE.Normal := by simpa [KE] using hKnormalE
  have hQcard : Nat.card Q = q := by
    simpa using hQ.2.card_eq
  have hQpi : IsPiNumber ({q} : Set ℕ) (Nat.card Q) :=
    hQ.2.isPGroup.isPiNumber_natCard (by simp)
  have hcopKEQE : (Nat.card KE).Coprime (Nat.card QE) := by
    rw [MathlibSupport.natCard_subgroupOf_eq hKE,
      MathlibSupport.natCard_subgroupOf_eq hQE]
    exact (hQpi.coprime_compl hKq').symm
  have hdisKEQE : Disjoint KE QE :=
    Subgroup.disjoint_of_coprime_natCard hcopKEQE
  have hmapTopQE :
      (⁅(⊤ : Subgroup E), QE⁆).map E.subtype = K := by
    calc
      (⁅(⊤ : Subgroup E), QE⁆).map E.subtype = ⁅E, Q⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          E.range_subtype, Subgroup.map_subgroupOf_eq_of_le hQE]
      _ = K := hKdef.symm
  have hTopQE : ⁅(⊤ : Subgroup E), QE⁆ = KE := by
    apply Subgroup.map_injective E.subtype_injective
    rw [hmapTopQE, Subgroup.map_subgroupOf_eq_of_le hKE]
  let LE : Subgroup E := KE ⊔ QE
  have hLEnormal : LE.Normal := by
    rw [← Subgroup.commutator_top_left_le_iff]
    dsimp [LE]
    exact (commutator_sup_le_of_normal
      (Subgroup.commutator_le_right (⊤ : Subgroup E) KE)
      hTopQE.le).trans le_sup_left
  letI : LE.Normal := hLEnormal
  let KEL : Subgroup LE := KE.subgroupOf LE
  let QEL : Subgroup LE := QE.subgroupOf LE
  letI : KEL.Normal := by
    exact Subgroup.Normal.subgroupOf (inferInstance : KE.Normal) LE
  have hdisKELQEL : Disjoint KEL QEL := by
    rw [disjoint_iff_inf_le]
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hxBot : ((x : LE) : E) ∈ (⊥ : Subgroup E) :=
      hdisKEQE.le_bot ⟨hx.1, hx.2⟩
    exact Subgroup.mem_bot.mp hxBot
  have hcomp : KEL.IsComplement' QEL := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisKELQEL
    have htop : KEL ⊔ QEL = ⊤ := by
      change KE.subgroupOf LE ⊔ QE.subgroupOf LE = ⊤
      rw [← Subgroup.subgroupOf_sup
        (show KE ≤ LE from le_sup_left)
        (show QE ≤ LE from le_sup_right)]
      exact Subgroup.subgroupOf_self LE
    rw [← Subgroup.normal_mul KEL QEL, htop]
    rfl
  have hQEp : IsPGroup q QE :=
    hQ.2.isPGroup.of_equiv
      (Subgroup.subgroupOfEquivOfLe hQE).symm
  have hQELp : IsPGroup q QEL :=
    hQEp.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (show QE ≤ LE from le_sup_right)).symm
  have hqNotCardKE : ¬ q ∣ Nat.card KE := by
    intro hqKE
    have hqK : q ∣ Nat.card K := by
      rw [← MathlibSupport.natCard_subgroupOf_eq hKE]
      exact hqKE
    have hqCompl : q ∈ ({q} : Set ℕ)ᶜ := by
      apply hKq' (Fact.out : q.Prime)
      exact hqK
    exact hqCompl (by simp)
  have hqNotIndex : ¬ q ∣ QEL.index := by
    rw [hcomp.index_eq_card,
      MathlibSupport.natCard_subgroupOf_eq
        (show KE ≤ LE from le_sup_left)]
    exact hqNotCardKE
  let P : Sylow q LE := hQELp.toSylow hqNotIndex
  have hPcoe : (P : Subgroup LE) = QEL :=
    IsPGroup.toSylow_coe hQELp hqNotIndex
  have hFrattini :
      Subgroup.normalizer (QE : Set E) ⊔ LE = ⊤ := by
    simpa [hPcoe, QEL,
      Subgroup.map_subgroupOf_eq_of_le
        (show QE ≤ LE from le_sup_right)] using
      Sylow.normalizer_sup_eq_top P
  let N : Subgroup E := Subgroup.normalizer (QE : Set E)
  have hQEN : QE ≤ N := Subgroup.le_normalizer
  have hLEN : LE ≤ KE ⊔ N := by
    dsimp [LE]
    exact sup_le le_sup_left (hQEN.trans le_sup_right)
  have hKEN : KE ⊔ N = ⊤ := by
    apply top_unique
    rw [← hFrattini]
    exact sup_le le_sup_right hLEN
  have hNQleQ : ⁅N, QE⁆ ≤ QE :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp le_rfl
  have hNQleK : ⁅N, QE⁆ ≤ KE :=
    (Subgroup.commutator_mono le_top le_rfl).trans hTopQE.le
  have hNQbot : ⁅N, QE⁆ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro y hy
    exact hdisKEQE.le_bot ⟨hNQleK hy, hNQleQ hy⟩
  have hNcent : N ≤ Subgroup.centralizer (QE : Set E) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hNQbot
  have hTopQle :
      ⁅(⊤ : Subgroup E), QE⁆ ≤ ⁅KE, QE⁆ := by
    rw [Subgroup.commutator_le]
    intro e _ q hq
    have heSup : e ∈ KE ⊔ N := by rw [hKEN]; trivial
    rw [Subgroup.mem_sup_of_normal_left] at heSup
    obtain ⟨k, hk, n, hn, hkn⟩ := heSup
    have hncomm : Commute n q :=
      (Subgroup.mem_centralizer_iff.mp (hNcent hn) q hq).symm
    have hnCommOne : ⁅n, q⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr hncomm
    rw [← hkn, commutatorElement_mul_left_eq_conj_mul,
      hnCommOne]
    simpa using Subgroup.commutator_mem_commutator hk hq
  have hTopQeq :
      ⁅(⊤ : Subgroup E), QE⁆ = ⁅KE, QE⁆ :=
    le_antisymm hTopQle
      (Subgroup.commutator_mono le_top le_rfl)
  have hKEQeq : ⁅KE, QE⁆ = KE :=
    hTopQeq.symm.trans hTopQE
  have hmap := congrArg (Subgroup.map E.subtype) hKEQeq
  have hmapKE : KE.map E.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKE
  have hmapQE : QE.map E.subtype = Q :=
    Subgroup.map_subgroupOf_eq_of_le hQE
  rw [Subgroup.map_commutator, hmapKE, hmapQE] at hmap
  exact hmap

/-- Enlarge an ambient `p`-subgroup to the ambient image of a Sylow
subgroup of a prescribed overgroup. -/
private theorem exists_ambient_sylow_containing
    {A E : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hAp : IsPGroup p A) (hAE : A ≤ E) :
    ∃ S : Subgroup G,
      IsPGroup p S ∧ A ≤ S ∧ IsSylowSubgroupOf p S E := by
  let AE : Subgroup E := A.subgroupOf E
  let eAE : AE ≃* A := Subgroup.subgroupOfEquivOfLe hAE
  have hAEp : IsPGroup p AE := hAp.of_equiv eAE.symm
  obtain ⟨P, hAEP⟩ := hAEp.exists_le_sylow
  let S : Subgroup G := ambientSylow E P
  have hAS : A ≤ S := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAE]
    exact Subgroup.map_mono hAEP
  exact ⟨S, P.isPGroup'.map E.subtype, hAS, P, rfl⟩

private theorem isMulCommutative_of_le_14_11
    {A B : Subgroup G} (hAB : A ≤ B)
    (hB : IsMulCommutative B) :
    IsMulCommutative A := by
  rw [isMulCommutative_iff] at hB ⊢
  intro x y
  apply A.subtype_injective
  change (x : G) * (y : G) = (y : G) * (x : G)
  exact congrArg Subtype.val
    (hB ⟨x, hAB x.property⟩ ⟨y, hAB y.property⟩)

/-- The mixed commutator lies in the (abelian) derived subgroup of the
sigma complement. -/
private theorem commutator_isMulCommutative_of_derived_commutative
    {E Q : Subgroup G}
    (hDer : IsMulCommutative (_root_.commutator E))
    (hQE : Q ≤ E) :
    IsMulCommutative (⁅E, Q⁆ : Subgroup G) := by
  let D : Subgroup G := (_root_.commutator E).map E.subtype
  let eD : (_root_.commutator E) ≃* D :=
    (_root_.commutator E).equivMapOfInjective
      E.subtype E.subtype_injective
  have hDcomm : IsMulCommutative D := by
    rw [isMulCommutative_iff] at hDer ⊢
    intro x y
    rw [← eD.apply_symm_apply x, ← eD.apply_symm_apply y,
      ← map_mul, hDer, map_mul]
  apply isMulCommutative_of_le_14_11 (B := D) _ hDcomm
  calc
    ⁅E, Q⁆ ≤ ⁅E, E⁆ :=
      Subgroup.commutator_mono le_rfl hQE
    _ = D := by
      simpa only [D] using E.map_subtype_commutator.symm

/-- The mixed commutator with the whole left-hand ambient group is normal
in that ambient group. -/
private theorem commutator_subgroupOf_normal
    {E Q : Subgroup G} (hQE : Q ≤ E) :
    ((⁅E, Q⁆).subgroupOf E).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((Subgroup.commutator_mono le_rfl hQE).trans
      (Subgroup.commutator_le_self E))).mpr
  exact Subgroup.normalizer_commutator_ge_left E Q

private theorem commutative_normal_le_fittingWithin
    {K E : Subgroup G} (hKE : K ≤ E)
    (hKnormal : (K.subgroupOf E).Normal)
    (hKcomm : IsMulCommutative K) :
    K ≤ fittingWithin E :=
  nilpotent_normal_le_fittingWithin_14_11
    hKE hKnormal (isNilpotent_of_isMulCommutative_14_11 hKcomm)

private theorem rankOne_le_fittingWithin_of_commutator_eq_bot
    {E Q : Subgroup G} {q : ℕ}
    (hQE : Q ≤ E) (hQ : IsElementaryAbelianOfRank q 1 Q)
    (hcomm : ⁅E, Q⁆ = ⊥) :
    Q ≤ fittingWithin E := by
  have hEcentQ : E ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hQnormal : (Q.subgroupOf E).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQE).mpr
    exact hEcentQ.trans
      (Subgroup.centralizer_le_normalizer (Q : Set G))
  exact nilpotent_normal_le_fittingWithin_14_11
    hQE hQnormal
      (isNilpotent_of_isMulCommutative_14_11 hQ.commutative)

private theorem rankOne_le_fittingWithin_of_tau2_sylow_commutative
    {M E A Q : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hMF : M ∈ typeFMaximalSubgroups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hqTau : q ∈ tau1Primes M)
    (hAE : A ≤ E) (hA : IsElementaryAbelianOfRank p 2 A)
    (hQ : RankOneLineIn q E Q)
    (_hAnormal : (A.subgroupOf E).Normal)
    (S : Sylow p G) (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    Q ≤ fittingWithin E := by
  obtain ⟨E₁, hQE₁, hE₁E, hHallE₁⟩ :=
    MathlibSupport.exists_ambient_isHall_ge_of_isSolvable hQ.1
      (sigma_compl_sol hEM hHallE) (tau1Primes M)
        (hQ.2.isPGroup.isPiNumber_natCard hqTau)
  obtain ⟨E₃, hE₃E, hHallE₃⟩ :=
    (ex_tau13_compl hEM hHallE).2
  obtain ⟨E₂, _hE₂E, _hHallE₂, hCompl⟩ :=
    ex_tau2_compl hEM hHallE hE₁E hHallE₁ hE₃E hHallE₃
  have hreg : centralizerWithin (sigmaCore M) Q = ⊥ := by
    apply le_antisymm
    · by_contra hne
      have hne' : centralizerWithin (sigmaCore M) Q ≠ ⊥ := by
        intro heq
        exact hne heq.le
      have hqKappa : q ∈ kappaPrimes M :=
        ⟨Or.inl hqTau, Q, ⟨hQ.1.trans hEM, hQ.2⟩, hne'⟩
      have hempty : kappaPrimes M = ∅ := (FtypeP hM).mp hMF
      rw [hempty] at hqKappa
      exact hqKappa.elim
    · exact bot_le
  have hQcenter : Q ≤ centerWithin E := by
    exact (abelian_tau2 S hM hCompl hpTau hAE hA hAS hScomm)
      |>.regular_rank_one_central ⟨hQE₁, hQ.2⟩ hreg
  have hEcentQ : E ≤ Subgroup.centralizer (Q : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_centerWithin.mp (hQcenter hz)).2 e he).symm
  have hQnormal : (Q.subgroupOf E).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQ.1).mpr
    exact hEcentQ.trans
      (Subgroup.centralizer_le_normalizer (Q : Set G))
  exact nilpotent_normal_le_fittingWithin_14_11
    hQ.1 hQnormal hQ.2.isPGroup.isNilpotent

private theorem characteristic_map_subtype_le_normalizer_14_11
    {K : Type*} [Group K] (S : Subgroup K)
    (R : Subgroup S) [R.Characteristic] :
    Subgroup.normalizer (S : Set K) ≤
      Subgroup.normalizer (R.map S.subtype : Set K) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact characteristic_map_subtype_invariant_under_normalizer
      S (Subgroup.normalizer (S : Set K)) R le_rfl
      g hg r hr
  · intro hr
    have hginv : g⁻¹ ∈ Subgroup.normalizer (S : Set K) :=
      (Subgroup.normalizer (S : Set K)).inv_mem hg
    have h := characteristic_map_subtype_invariant_under_normalizer
      S (Subgroup.normalizer (S : Set K)) R le_rfl
      g⁻¹ hginv (g * r * g⁻¹) hr
    have hcancel : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by
      group
    simpa only [hcancel] using h

private theorem normal_abelian_sigmaComplement_prime_mem_tau2
    {M K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hKM : K ≤ M)
    (hKnormal : (K.subgroupOf M).Normal)
    (hKcomm : IsMulCommutative K)
    (hKsigmaCompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K))
    (hpK : p ∣ Nat.card K) :
    p ∈ tau2Primes M := by
  have hpNotSigma : p ∉ sigmaPrimes M :=
    hKsigmaCompl Fact.out hpK
  let P : Subgroup G := (pCore p K).map K.subtype
  have hpCoreNe : pCore p K ≠ ⊥ := by
    letI : Group.IsNilpotent K :=
      isNilpotent_of_isMulCommutative_14_11 hKcomm
    exact (pCore_ne_bot_iff_dvd_card_of_isNilpotent
      (G := K) p).2 hpK
  have hPne : P ≠ ⊥ := by
    intro hPbot
    apply hpCoreNe
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore p K) K.subtype_injective).mp hPbot
  have hPK : P ≤ K := Subgroup.map_subtype_le _
  have hPM : P ≤ M := hPK.trans hKM
  have hMnormK : M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKnormal
  have hMnormP : M ≤ Subgroup.normalizer (P : Set G) := by
    exact hMnormK.trans
      (characteristic_map_subtype_le_normalizer_14_11
        K (pCore p K))
  have hPnormal : (P.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mpr hMnormP
  have hPp : IsPGroup p P := pCore_isPGroup.map K.subtype
  have hNormP : Subgroup.normalizer (P : Set G) = M :=
    mmax_normal hM hPM hPnormal hPne
  have hRank := sigma'_norm_mmax_rank2 hM hpNotSigma hPp (by
    rw [hNormP])
  exact ⟨Fact.out, hpNotSigma, hRank.1, hRank.2⟩

private theorem commutator_sigmaComplement_rankOne_normal
    {M E Q K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hMF : M ∈ typeFMaximalSubgroups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hqTau : q ∈ tau1Primes M)
    (hQ : RankOneLineIn q E Q)
    (hKE : K ≤ E)
    (hKnormalE : (K.subgroupOf E).Normal)
    (hKq' : IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card K))
    (hKcomm : IsMulCommutative K)
    (hcommKQ : ⁅K, Q⁆ = K) :
    (K.subgroupOf M).Normal := by
  have hKM : K ≤ M := hKE.trans hEM
  have hKsigmaCompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K) := by
    have hEpi : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card E) := by
      simpa [MathlibSupport.natCard_subgroupOf_eq hEM] using
        hHallE.isPiNumber_card
    exact hEpi.of_dvd (Subgroup.card_dvd_of_le hKE)
  have hQnormK : Q ≤ Subgroup.normalizer (K : Set G) := by
    exact hQ.1.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKE).mp hKnormalE)
  have hQMN : Q ≤ M ⊓ Subgroup.normalizer (K : Set G) :=
    le_inf (hQ.1.trans hEM) hQnormK
  have hreg : centralizerWithin (sigmaCore M) Q = ⊥ := by
    apply le_antisymm
    · by_contra hne
      have hne' : centralizerWithin (sigmaCore M) Q ≠ ⊥ := by
        intro heq
        exact hne heq.le
      have hqKappa : q ∈ kappaPrimes M :=
        ⟨Or.inl hqTau, Q, ⟨hQ.1.trans hEM, hQ.2⟩, hne'⟩
      have hempty : kappaPrimes M = ∅ := (FtypeP hM).mp hMF
      rw [hempty] at hqKappa
      exact hqKappa.elim
    · exact bot_le
  have hconclusion := commG_sigma'_1Elem_cyclic
    hM hKM hKsigmaCompl hqTau.2.1 hQ.2 hQMN
      hreg hKq' hKcomm
  simpa [hcommKQ] using hconclusion.2.2

/-- Complementarity after restricting to a common ambient subgroup gives
ambient disjointness of the original factors. -/
private theorem disjoint_of_isComplement_subgroupOf_14_11
    {A B W : Subgroup G}
    (hAW : A ≤ W) (hBW : B ≤ W)
    (hcomp : (A.subgroupOf W).IsComplement' (B.subgroupOf W)) :
    Disjoint A B := by
  rw [disjoint_iff]
  apply le_antisymm ?_ bot_le
  intro x hx
  let xW : W := ⟨x, hAW hx.1⟩
  have hxInf : xW ∈ A.subgroupOf W ⊓ B.subgroupOf W :=
    ⟨hx.1, hx.2⟩
  have hxBot : xW ∈ (⊥ : Subgroup W) :=
    hcomp.disjoint.le_bot hxInf
  exact Subgroup.mem_bot.mpr
    (congrArg Subtype.val (Subgroup.mem_bot.mp hxBot))

/-- In the nonabelian `tau2` case, every nontrivial abelian normal subgroup
of the complement that lies in the Fitting subgroup is the distinguished
prime-order direct factor `C_A(M_sigma)`. -/
private theorem centralizer_tau2_eq_normal_abelian_complement
    {M E A K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hAE : A ≤ E)
    (hKM : K ≤ M) (hKE : K ≤ E)
    (hKnormalM : (K.subgroupOf M).Normal)
    (hKcomm : IsMulCommutative K) (hKne : K ≠ ⊥)
    (hTauCtx : NonabelianTau2Conclusion M E p
      (centralizerWithin A (sigmaCore M)))
    (hA₀card : Nat.card (centralizerWithin A (sigmaCore M)) = p) :
    centralizerWithin A (sigmaCore M) = K := by
  let A₀ : Subgroup G := centralizerWithin A (sigmaCore M)
  have hA₀E : A₀ ≤ E :=
    (centralizerWithin_le_left A (sigmaCore M)).trans hAE
  have hKfit : K ≤ fittingWithin M :=
    commutative_normal_le_fittingWithin hKM hKnormalM hKcomm
  have hdisSigmaE : Disjoint (sigmaCore M) E :=
    disjoint_of_isComplement_subgroupOf_14_11
      (sigmaCore_le M) hEM (sdprod_sigma hM hEM hHallE).2.2.2
  have hKA₀ : K ≤ A₀ := by
    intro k hk
    let kF : fittingWithin M := ⟨k, hKfit hk⟩
    obtain ⟨⟨s, a⟩, hsa⟩ :=
      hTauCtx.fitting_decomposition.complement.2 kF
    have hsaG : (s : G) * (a : G) = k :=
      congrArg Subtype.val hsa
    have hsSigma : (s : G) ∈ sigmaCore M := s.property
    have haA₀ : (a : G) ∈ A₀ := a.property
    have hsE : (s : G) ∈ E := by
      have hsEq : (s : G) = k * (a : G)⁻¹ := by
        rw [← hsaG]
        group
      rw [hsEq]
      exact E.mul_mem (hKE hk) (E.inv_mem (hA₀E haA₀))
    have hsOne : (s : G) = 1 := by
      exact Subgroup.mem_bot.mp
        (hdisSigmaE.le_bot ⟨hsSigma, hsE⟩)
    rw [← hsaG, hsOne, one_mul]
    exact haA₀
  have hA₀prime : (Nat.card A₀).Prime := by
    rw [hA₀card]
    exact Fact.out
  letI : Fact (Nat.card A₀).Prime := ⟨hA₀prime⟩
  rcases (K.subgroupOf A₀).eq_bot_or_eq_top_of_prime_card with
    hbot | htop
  · have hdis : Disjoint K A₀ :=
      Subgroup.subgroupOf_eq_bot.mp hbot
    have hKbot : K = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro k hk
      exact hdis.le_bot ⟨hk, hKA₀ hk⟩
    exact (hKne hKbot).elim
  · exact (le_antisymm hKA₀
      (Subgroup.subgroupOf_eq_top.mp htop)).symm

/-- The fixed subgroup `C_A(Q)` is nontrivial and, after passing to the
normalizer maximal subgroup, lies in its sigma core. -/
private theorem centralizerWithin_ne_bot_of_tau2_commutator
    {M E A Q K H : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hqTau : q ∈ tau1Primes M)
    (hpSigmaH : p ∈ sigmaPrimes H)
    (hAE : A ≤ E) (hA : IsElementaryAbelianOfRank p 2 A)
    (hQ : RankOneLineIn q E Q)
    (hKdef : K = ⁅E, Q⁆)
    (hA₀eqK : centralizerWithin A (sigmaCore M) = K)
    (hA₀card : Nat.card (centralizerWithin A (sigmaCore M)) = p)
    (hKne : K ≠ ⊥)
    (hNAH : Subgroup.normalizer (A : Set G) ≤ H) :
    centralizerWithin (sigmaCore H) Q ≠ ⊥ := by
  let C : Subgroup G := centralizerWithin A Q
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hqTau.2.2.2.1 hpTau.2.2.1
  have hQnormA : Q ≤ Subgroup.normalizer (A : Set G) := by
    exact hQ.1.trans
      (tau2_compl_context hM hEM hHallE hpTau hAE hA).A_normalizer_le
  have hcopAQ : (Nat.card A).Coprime (Nat.card Q) :=
    IsPGroup.coprime_card_of_ne p q hpq A Q
      hA.isPGroup hQ.2.isPGroup
  have hCne : C ≠ ⊥ := by
    intro hCbot
    letI : IsMulCommutative A := hA.commutative
    letI : IsSolvable A :=
      Submission.OddOrder.MathlibSupport.isSolvable_of_comm
        (fun a b : A ↦ mul_comm a b)
    have hdecomp :=
      le_commutator_sup_centralizerWithin_of_coprime
        (K := A) (R := Q) hQnormA hcopAQ
    have hAle : A ≤ ⁅Q, A⁆ := by
      simpa only [C, hCbot, sup_bot_eq] using hdecomp
    have hcommLeK : ⁅Q, A⁆ ≤ K := by
      rw [hKdef]
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mono hAE le_rfl
    have hAK : A ≤ K := hAle.trans hcommLeK
    have hcardLe : Nat.card A ≤ Nat.card K :=
      Subgroup.card_le_of_le hAK
    have hKcard : Nat.card K = p := by
      rw [← hA₀eqK]
      exact hA₀card
    rw [hA.card_eq, hKcard] at hcardLe
    nlinarith [(Fact.out : p.Prime).two_le]
  have hEH : E ≤ H :=
    (tau2_compl_context hM hEM hHallE hpTau hAE hA).A_normalizer_le.trans
      hNAH
  have hCH : C ≤ H :=
    (centralizerWithin_le_left A Q).trans (hAE.trans hEH)
  have hCpi : IsPiNumber (sigmaPrimes H) (Nat.card C) :=
    (hA.isPGroup.isPiNumber_natCard hpSigmaH).of_dvd
      (Subgroup.card_dvd_of_le (centralizerWithin_le_left A Q))
  have hCsigma : C ≤ sigmaCore H :=
    le_normal_isHall_of_isPiNumber_14_11
      (sigmaCore_normal H) (Msigma_Hall hH) hCH hCpi
  have hCcent : C ≤ centralizerWithin (sigmaCore H) Q :=
    le_inf hCsigma inf_le_right
  intro hbot
  apply hCne
  apply le_antisymm
  · rw [← hbot]
    exact hCcent
  · exact bot_le

/-- A sigma prime excluded from beta rules out the type-`P2` branch. -/
private theorem typeP1_of_sigma_not_beta
    {H : Subgroup G} {p : ℕ}
    (hHP : H ∈ typePMaximalSubgroups (G := G))
    (hpSigma : p ∈ sigmaPrimes H)
    (hpNotBeta : p ∉ betaPrimes H) :
    H ∈ typeP1MaximalSubgroups (G := G) := by
  obtain ⟨L, hLH, hHallL⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable
      (mmax_sol hHP.1) (kappaPrimes H)
  by_contra hHP1
  have hHP2 : H ∈ typeP2MaximalSubgroups (G := G) :=
    ⟨hHP, hHP1⟩
  have hP2 := (Ptype_structure hHP hLH hHallL).typeP2 hHP2
  exact hpNotBeta (hP2.sigma_eq_beta ▸ hpSigma)

/-- The prime-order calculation following Lemma 12.11(b) in the source.

If `Q ∩ C_E(A)` were nontrivial, prime order would force `Q` to centralize
all of `A`.  This would make `[K,Q]` trivial for
`K = C_A(Mσ)`, contrary to `[K,Q] = K ≠ 1`.  Normality of `C_E(A)` then
identifies the relevant relative index with `|Q| = q`. -/
private theorem rankOne_prime_dvd_centralizer_index
    {M E A Q K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hQ : RankOneLineIn q E Q)
    (hKne : K ≠ ⊥)
    (hA₀eqK : centralizerWithin A (sigmaCore M) = K)
    (hcommKQ : ⁅K, Q⁆ = K)
    (hCnormal : ((centralizerWithin E A).subgroupOf E).Normal) :
    q ∣ ((centralizerWithin E A).subgroupOf E).index := by
  let C : Subgroup G := centralizerWithin E A
  let CE : Subgroup E := C.subgroupOf E
  let QE : Subgroup E := Q.subgroupOf E
  have hQcard : Nat.card Q = q := by
    simpa using hQ.2.card_eq
  have hdisCQ : Disjoint C Q := by
    letI : Fact (Nat.card Q).Prime := ⟨by simpa [hQcard] using (Fact.out : q.Prime)⟩
    rcases (C.subgroupOf Q).eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exact Subgroup.subgroupOf_eq_bot.mp hbot
    · have hQC : Q ≤ C := Subgroup.subgroupOf_eq_top.mp htop
      have hQAcentral : Q ≤ Subgroup.centralizer (A : Set G) := by
        exact hQC.trans (show C ≤ Subgroup.centralizer (A : Set G) from inf_le_right)
      have hAQbot : ⁅A, Q⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hQAcentral
      have hKA : K ≤ A := by
        rw [← hA₀eqK]
        exact centralizerWithin_le_left A (sigmaCore M)
      have hKQbot : ⁅K, Q⁆ = ⊥ := by
        apply le_antisymm
        · exact (Subgroup.commutator_mono hKA le_rfl).trans hAQbot.le
        · exact bot_le
      exact (hKne (hcommKQ.symm.trans hKQbot)).elim
  have hdisCEQE : Disjoint CE QE := by
    rw [disjoint_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxCQ : (x : G) ∈ C ⊓ Q := ⟨hx.1, hx.2⟩
    have hxOne : (x : G) = 1 := by
      exact Subgroup.mem_bot.mp (hdisCQ.le_bot hxCQ)
    exact Subtype.ext hxOne
  have hCEQEbot : CE.subgroupOf QE = ⊥ :=
    Subgroup.subgroupOf_eq_bot.mpr hdisCEQE
  letI : CE.Normal := by
    simpa [CE, C] using hCnormal
  have hdvd : CE.relIndex QE ∣ CE.index :=
    CE.relIndex_dvd_index_of_normal QE
  have hrel : CE.relIndex QE = Nat.card QE := by
    rw [Subgroup.relIndex, hCEQEbot, Subgroup.index_bot]
  have hQEcard : Nat.card QE = Nat.card Q := by
    simpa [QE] using MathlibSupport.natCard_subgroupOf_eq hQ.1
  rw [hrel, hQEcard, hQcard] at hdvd
  simpa [CE, C] using hdvd

/-- `BGsection14.v: primes_non_Fitting_Ftype`, Bender--Glauberman
Lemma 14.11.

The source membership `Q \in 'E_q^1(E)` is the pair `RankOneLineIn q E Q`;
primality of `q`, implicit in the MathComp predicate, is explicit through a
typeclass. -/
theorem primes_non_Fitting_Ftype
    {M E Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hMF : M ∈ typeFMaximalSubgroups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hQ : RankOneLineIn q E Q)
    (hQnotF : ¬ Q ≤ fittingWithin E) :
    ∃ Mstar : Subgroup G,
      Mstar ∈ minSimple_max_groups (G := G) ∧
        ((q ∈ tau2Primes Mstar ∧
            minSimple_max_groups_of (G := G)
              (Subgroup.centralizer (Q : Set G) : Set G) = {Mstar}) ∨
          (q ∈ kappaPrimes Mstar ∧
            Mstar ∈ typeP1MaximalSubgroups (G := G))) := by
  classical
  have hmaxM : M ∈ minSimple_max_groups (G := G) := hMF.1
  have hQE : Q ≤ E := hQ.1
  have hqTau1 : q ∈ tau1Primes M := by
    exact typeF_nonFitting_rankOne_tau1
      hMF hEM hHallE hQ hQnotF
  have hFq' : IsPiNumber ({q} : Set ℕ)ᶜ
      (Nat.card (fittingWithin E)) := by
    exact fittingWithin_isPrimeComplement_of_tau1_rankOne_not_le
      hEM hHallE hqTau1 hQ hQnotF

  let K : Subgroup G := ⁅E, Q⁆
  have hKcomm : IsMulCommutative K := by
    exact commutator_isMulCommutative_of_derived_commutative
      (der_mmax_compl_abelian hmaxM hEM hHallE) hQE
  have hKE : K ≤ E :=
    (Subgroup.commutator_mono le_rfl hQE).trans
      (Subgroup.commutator_le_self E)
  have hKnormalE : (K.subgroupOf E).Normal := by
    exact commutator_subgroupOf_normal hQE
  have hKq' : IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card K) := by
    exact hFq'.of_dvd (Subgroup.card_dvd_of_le
      (commutative_normal_le_fittingWithin hKE hKnormalE hKcomm))
  have hcommKQ : ⁅K, Q⁆ = K := by
    exact commutator_rankOne_eq_self hQE hKnormalE hKq' hQ rfl
  have hKM : K ≤ M := hKE.trans hEM
  have hKnormalM : (K.subgroupOf M).Normal := by
    exact commutator_sigmaComplement_rankOne_normal
      hmaxM hMF hEM hHallE hqTau1 hQ hKE hKnormalE
        hKq' hKcomm hcommKQ
  have hKne : K ≠ ⊥ := by
    intro hKbot
    apply hQnotF
    exact rankOne_le_fittingWithin_of_commutator_eq_bot
      hQE hQ.2 hKbot

  have hKcardNe : Nat.card K ≠ 1 :=
    ne_of_gt (K.one_lt_card_iff_ne_bot.mpr hKne)
  obtain ⟨p, hp, hpK⟩ := Nat.exists_prime_and_dvd hKcardNe
  letI : Fact p.Prime := ⟨hp⟩
  have hKsigmaCompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K) := by
    have hEpi : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card E) := by
      simpa [MathlibSupport.natCard_subgroupOf_eq hEM] using
        hHallE.isPiNumber_card
    exact hEpi.of_dvd (Subgroup.card_dvd_of_le hKE)
  have hpTau2 : p ∈ tau2Primes M := by
    exact normal_abelian_sigmaComplement_prime_mem_tau2
      hmaxM hKM hKnormalM hKcomm hKsigmaCompl hpK
  obtain ⟨A, hAE, _hAM, hA⟩ := ex_tau2Elem hEM hHallE hpTau2
  have hAnormalE : (A.subgroupOf E).Normal :=
    (tau2_compl_context hmaxM hEM hHallE hpTau2 hAE hA).A_normal
  obtain ⟨SG, hASG⟩ := hA.isPGroup.exists_le_sylow
  let S : Subgroup G := (SG : Subgroup G)
  have hSp : IsPGroup p S := SG.isPGroup'
  have hAS : A ≤ S := hASG
  have hSnoncomm : ¬ IsMulCommutative S := by
    intro hScomm
    apply hQnotF
    exact rankOne_le_fittingWithin_of_tau2_sylow_commutative
      hmaxM hMF hEM hHallE hpTau2 hqTau1 hAE hA hQ hAnormalE
        SG hAS hScomm
  let A₀ : Subgroup G := centralizerWithin A (sigmaCore M)
  have hTauCtx := nonabelian_tau2 hmaxM hEM hHallE hpTau2
    hAE hA hSp hSnoncomm
  have hA₀card : Nat.card A₀ = p := hTauCtx.A0_card
  have hA₀eqK : A₀ = K := by
    exact centralizer_tau2_eq_normal_abelian_complement
      hmaxM hEM hHallE hAE hKM hKE hKnormalM hKcomm hKne
        hTauCtx hA₀card

  have hAne : A ≠ ⊥ := by
    exact hA.ne_bot
  obtain ⟨H, hmaxH, hNAH⟩ :=
    mmax_exists (Subgroup.normalizer (A : Set G))
      (mFT_norm_proper A hAne (mFT_pgroup_proper A hA.isPGroup))
  have hQH : Q ≤ H := by
    exact hQE.trans
      ((tau2_compl_context hmaxM hEM hHallE hpTau2 hAE hA).A_normalizer_le
        |>.trans hNAH)
  have hFactor : Tau1CentralizerFactor M E A :=
    tau1_cent_tau2Elem_factor
      hmaxM hEM hHallE hpTau2 hAE hA
  have hclassification :
      ∀ {r : ℕ}, r ∈ tau2Primes M →
        r ∈ sigmaPrimes H ∧ r ∉ betaPrimes H :=
    primes_norm_tau2Elem_tau2_classification
      hmaxM hEM hHallE hpTau2 hAE hA hmaxH hNAH
  have hpSigmaH : p ∈ sigmaPrimes H :=
    (hclassification hpTau2).1
  have hpBetaComplH : p ∉ betaPrimes H := by
    exact (hclassification hpTau2).2
  have hcentQHne :
      centralizerWithin (sigmaCore H) Q ≠ ⊥ := by
    exact centralizerWithin_ne_bot_of_tau2_commutator
      hmaxM hmaxH hEM hHallE hpTau2 hqTau1 hpSigmaH
        hAE hA hQ rfl hA₀eqK hA₀card hKne hNAH
  have hqIndex :
      q ∣ ((centralizerWithin E A).subgroupOf E).index := by
    exact rankOne_prime_dvd_centralizer_index
      hQ hKne hA₀eqK hcommKQ hFactor.centralizer_normal
  have hquotientTau12 :
      IsPiNumber (tau1Primes H ∪ tau2Primes H)
        ((centralizerWithin E A).subgroupOf E).index :=
    primes_norm_tau2Elem_quotient_tau12
      hmaxM hEM hHallE hpTau2 hAE hA hmaxH hNAH
        hclassification hFactor.quotient_isPiNumber
  have hqTau12H : q ∈ tau1Primes H ∪ tau2Primes H := by
    exact hquotientTau12 (Fact.out : q.Prime) hqIndex
  rcases hqTau12H with hqTau1H | hqTau2H
  · have hqKappaH : q ∈ kappaPrimes H := by
      exact ⟨Or.inl hqTau1H, Q, ⟨hQH, hQ.2⟩, hcentQHne⟩
    have hHP : H ∈ typePMaximalSubgroups (G := G) :=
      (PtypeP hmaxH).2 ⟨q, hqKappaH⟩
    have hHP1 : H ∈ typeP1MaximalSubgroups (G := G) := by
      exact typeP1_of_sigma_not_beta hHP hpSigmaH hpBetaComplH
    exact ⟨H, hmaxH, Or.inr ⟨hqKappaH, hHP1⟩⟩
  · have huniq :
        minSimple_max_groups_of (G := G)
          (Subgroup.centralizer (Q : Set G) : Set G) = {H} := by
      obtain ⟨x, hx1⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp hQ.2.ne_bot
      have hxQ : (x : G) ∈ Q := x.property
      have hxG1 : (x : G) ≠ 1 := by
        intro hx
        exact hx1 (Subtype.ext hx)
      have hQcard : Nat.card Q = q := by
        simpa using hQ.2.card_eq
      have hQprime : (Nat.card Q).Prime := by
        simpa [hQcard] using (Fact.out : q.Prime)
      have hQeq : Subgroup.zpowers (x : G) = Q :=
        zpowers_eq_of_mem_subgroup_prime_card Q hQprime hxQ hxG1
      have hxOrderDvd : orderOf (x : G) ∣ Nat.card Q := by
        simpa using orderOf_dvd_natCard (⟨x, hxQ⟩ : Q)
      have hxTau2 : IsPiNumber (tau2Primes H) (orderOf (x : G)) :=
        (hQ.2.isPGroup.isPiNumber_natCard hqTau2H).of_dvd hxOrderDvd
      have hcentX :
          centralizerWithin (sigmaCore H) (Subgroup.zpowers (x : G)) ≠ ⊥ := by
        simpa only [hQeq] using hcentQHne
      have huniqX := cent1_nreg_sigma_uniq
        hmaxH (hQH hxQ) hxG1 hxTau2 hcentX
      have hcentralizerQZ :
          Subgroup.centralizer (Q : Set G) =
            Subgroup.centralizer
              (Subgroup.zpowers (x : G) : Set G) :=
        congrArg
          (fun R : Subgroup G ↦ Subgroup.centralizer (R : Set G))
          hQeq.symm
      have hcentralizerZ :
          Subgroup.centralizer
              (Subgroup.zpowers (x : G) : Set G) =
            Subgroup.centralizer ({(x : G)} : Set G) := by
        rw [Subgroup.zpowers_eq_closure,
          Subgroup.centralizer_closure]
      have hcentralizer :
          Subgroup.centralizer (Q : Set G) =
            Subgroup.centralizer ({(x : G)} : Set G) := by
        exact hcentralizerQZ.trans hcentralizerZ
      rw [hcentralizer]
      exact huniqX
    exact ⟨H, hmaxH, Or.inl ⟨hqTau2H, huniq⟩⟩

/-! ## Lemma 14.12 -/

private theorem isSylowSubgroupOf_le_14
    {p : ℕ} {Q K : Subgroup G}
    (hQ : IsSylowSubgroupOf p Q K) : Q ≤ K := by
  obtain ⟨P, rfl⟩ := hQ
  exact Subgroup.map_subtype_le (P : Subgroup K)

/-- A Sylow subgroup of a Hall subgroup is Sylow in the ambient group,
stated for ambiently represented subgroups. -/
private theorem isSylowSubgroupOf_of_hall_14
    {pi : Set ℕ} {p : ℕ} [Fact p.Prime]
    {R U M : Subgroup G}
    (hUM : U ≤ M)
    (hHall : IsHall pi (U.subgroupOf M))
    (hpPi : p ∈ pi)
    (hR : IsSylowSubgroupOf p R U) :
    IsSylowSubgroupOf p R M := by
  have hRp : IsPGroup p R := IsSylowSubgroupOf.isPGroup hR
  obtain ⟨P, hRP⟩ := hR
  have hRU : R ≤ U := by
    rw [hRP]
    exact Subgroup.map_subtype_le (P : Subgroup U)
  have hRM : R ≤ M := hRU.trans hUM
  have hRsubU : R.subgroupOf U = (P : Subgroup U) := by
    rw [hRP]
    change ((P : Subgroup U).map U.subtype).comap U.subtype = P
    exact Subgroup.comap_map_eq_self_of_injective
      U.subtype_injective P
  have hpRindexU : ¬ p ∣ R.relIndex U := by
    change ¬ p ∣ (R.subgroupOf U).index
    rw [hRsubU]
    exact P.not_dvd_index
  have hpUindexM : ¬ p ∣ U.relIndex M := by
    change ¬ p ∣ (U.subgroupOf M).index
    intro hpIndex
    exact hHall.isPiNumber_index (Fact.out : p.Prime) hpIndex hpPi
  have hpRindexM : ¬ p ∣ R.relIndex M := by
    rw [← Subgroup.relIndex_mul_relIndex R U M hRU hUM]
    exact (Fact.out : p.Prime).not_dvd_mul hpRindexU hpUindexM
  let RM : Subgroup M := R.subgroupOf M
  have hRMp : IsPGroup p RM :=
    hRp.of_equiv
      (Subgroup.subgroupOfEquivOfLe hRM).symm
  let S : Sylow p M := hRMp.toSylow hpRindexM
  have hSco : (S : Subgroup M) = RM :=
    IsPGroup.toSylow_coe hRMp hpRindexM
  refine ⟨S, ?_⟩
  rw [hSco,
    Subgroup.map_subgroupOf_eq_of_le hRM]

/-- A maximal overgroup of a Sylow normalizer cannot be conjugate to a
maximal subgroup in whose sigma set the Sylow prime is absent. -/
private theorem not_conjugate_of_sylow_normalizer_14
    {p : ℕ} [Fact p.Prime] {M H R : Subgroup G}
    (hmaxM : M ∈ minSimple_max_groups (G := G))
    (hmaxH : H ∈ minSimple_max_groups (G := G))
    (hRM : IsSylowSubgroupOf p R M)
    (hRH : R ≤ H)
    (hpNotSigmaM : p ∉ sigmaPrimes M)
    (hNRH : Subgroup.normalizer (R : Set G) ≤ H) :
    ¬ AreConjugateSubgroups M H := by
  intro hconj
  have hRp : IsPGroup p R := IsSylowSubgroupOf.isPGroup hRM
  have hRMle : R ≤ M := isSylowSubgroupOf_le_14 hRM
  obtain ⟨P, hRP⟩ := hRM
  have hRsubM : R.subgroupOf M = (P : Subgroup M) := by
    rw [hRP]
    change ((P : Subgroup M).map M.subtype).comap M.subtype = P
    exact Subgroup.comap_map_eq_self_of_injective
      M.subtype_injective P
  have hcardHM : Nat.card H = Nat.card M := by
    rcases hconj with ⟨g, rfl⟩
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hindexEq :
      (R.subgroupOf H).index = (R.subgroupOf M).index := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.card_pos (α := R.subgroupOf H))
    calc
      Nat.card (R.subgroupOf H) * (R.subgroupOf H).index =
          Nat.card H := (R.subgroupOf H).card_mul_index
      _ = Nat.card M := hcardHM
      _ = Nat.card (R.subgroupOf M) *
          (R.subgroupOf M).index :=
        (R.subgroupOf M).card_mul_index.symm
      _ = Nat.card (R.subgroupOf H) *
          (R.subgroupOf M).index := by
        rw [MathlibSupport.natCard_subgroupOf_eq hRH,
          MathlibSupport.natCard_subgroupOf_eq hRMle]
  let RH : Subgroup H := R.subgroupOf H
  have hRHp : IsPGroup p RH :=
    hRp.of_equiv
      (Subgroup.subgroupOfEquivOfLe hRH).symm
  have hpIndexH : ¬ p ∣ RH.index := by
    rw [hindexEq, hRsubM]
    exact P.not_dvd_index
  let S : Sylow p H := hRHp.toSylow hpIndexH
  have hAmbient : ambientSylow H S = R := by
    dsimp [ambientSylow, S]
    exact Subgroup.map_subgroupOf_eq_of_le hRH
  have hpSigmaH : p ∈ sigmaPrimes H := by
    refine ⟨Fact.out, S, ?_⟩
    rw [hAmbient]
    exact hNRH
  rcases hconj with ⟨g, rfl⟩
  exact hpNotSigmaM (by
    simpa only [sigmaPrimes_conj] using hpSigmaH)

private theorem internalDirectProduct_eq_sup_14_12
    {A B W : Subgroup G} (h : IsInternalDirectProductIn A B W) :
    W = A ⊔ B := by
  apply le_antisymm
  · intro x hx
    let ab : A × B := h.mulEquiv.symm ⟨x, hx⟩
    have hab := h.mulEquiv.apply_symm_apply (⟨x, hx⟩ : W)
    have habG : (ab.1 : G) * (ab.2 : G) = x :=
      congrArg Subtype.val hab
    rw [← habG]
    exact (A ⊔ B).mul_mem
      ((show A ≤ A ⊔ B from le_sup_left) ab.1.property)
      ((show B ≤ A ⊔ B from le_sup_right) ab.2.property)
  · exact sup_le h.left_le h.right_le

private theorem centralizerWithin_eq_bot_of_semiregular_actor_ne_bot_14_12
    {A B : Subgroup G} (hreg : IsSemiregularConjugation A B)
    (hB : B ≠ ⊥) :
    centralizerWithin A B = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨b, hb1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have hbB : (b : G) ∈ B := b.property
  let bB : B := ⟨b, hbB⟩
  let xA : A := ⟨x, hx.1⟩
  have hbB1 : bB ≠ 1 := by
    intro hb
    exact hb1 (by simpa [bB] using hb)
  have hcomm : b * x = x * b := hx.2 b hbB
  have hfix : (bB : G) * (xA : G) * (bB : G)⁻¹ = (xA : G) := by
    change b * x * b⁻¹ = x
    rw [hcomm]
    simp
  have hxOne : xA = 1 := hreg bB hbB1 xA hfix
  simpa [xA] using congrArg Subtype.val hxOne

/-- Nilpotence grows any subgroup through proper normalizers.  If every
conjugate maximal overgroup containing the fixed subgroup is forced back
to `Mstar`, that growth is captured inside `Mstar`. -/
private theorem nilpotent_over_unique_conjugate_le_14_12
    {K F Mstar : Subgroup G}
    (hKF : K ≤ F) (hKMstar : K ≤ Mstar)
    (hnil : Group.IsNilpotent F)
    (huniq : ∀ g : G,
      K ≤ Mstar.map (MulAut.conj g).toMonoidHom → g ∈ Mstar) :
    F ≤ Mstar := by
  letI : Group.IsNilpotent F := hnil
  let P : Subgroup G → Prop := fun A ↦
    A ≤ F → K ≤ A → A ≤ Mstar → F ≤ Mstar
  have hPK : P K :=
    (measure (fun A : Subgroup G ↦
      Nat.card F - Nat.card A)).wf.induction K (fun A ih ↦ by
  intro hAF hKA hAMstar
  by_cases hAF_eq : A = F
  · simpa [← hAF_eq] using hAMstar
  let AF : Subgroup F := A.subgroupOf F
  let NF : Subgroup F := Subgroup.normalizer (AF : Set F)
  let N : Subgroup G := NF.map F.subtype
  have hAF_ne_top : AF ≠ ⊤ := by
    intro htop
    apply hAF_eq
    exact le_antisymm hAF (Subgroup.subgroupOf_eq_top.mp htop)
  have hAF_lt_NF : AF < NF := by
    exact Group.normalizerCondition_of_isNilpotent AF
      (lt_top_iff_ne_top.mpr hAF_ne_top)
  have hA_lt_N : A < N := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAF]
    exact Subgroup.map_subtype_lt_map_subtype.mpr hAF_lt_NF
  have hNF : N ≤ F := Subgroup.map_subtype_le NF
  have hNstar : N ≤ Mstar := by
    rintro _ ⟨n, hn, rfl⟩
    apply huniq (n : G)
    intro k hk
    let kF : F := ⟨k, hAF (hKA hk)⟩
    have hnInv : n⁻¹ ∈ NF := (Subgroup.normalizer (AF : Set F)).inv_mem hn
    have hkAF : kF ∈ AF := hKA hk
    have hconjAF : n⁻¹ * kF * (n⁻¹)⁻¹ ∈ AF :=
      (Subgroup.mem_normalizer_iff.mp hnInv kF).mp hkAF
    have hconjA : (n : G)⁻¹ * k * (n : G) ∈ A := by
      have hconjA' :
          ((n⁻¹ * kF * (n⁻¹)⁻¹ : F) : G) ∈ A := hconjAF
      simpa [kF] using hconjA'
    refine ⟨(n : G)⁻¹ * k * (n : G), hAMstar hconjA, ?_⟩
    change (n : G) * ((n : G)⁻¹ * k * (n : G)) * (n : G)⁻¹ = k
    group
  have hNcardLe : Nat.card N ≤ Nat.card F :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hNF)
  have hAcardLt : Nat.card A < Nat.card N :=
    natCard_subgroup_lt_of_lt hA_lt_N
  have hmeasure :
      Nat.card F - Nat.card N < Nat.card F - Nat.card A := by
    omega
  exact ih N hmeasure hNF (hKA.trans hA_lt_N.le) hNstar)
  exact hPK hKF le_rfl hKMstar

private theorem piCore_isHall_of_isNilpotent_14_12
    {X : Type*} [Group X] [Finite X] [Group.IsNilpotent X]
    (pi : Set ℕ) : IsHall pi (piCore pi X) := by
  refine ⟨piCore_isPiNumber pi, ?_⟩
  intro p hp hpIndex hpPi
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p X := Classical.choice Sylow.nonempty
  have hPnormal : (P : Subgroup X).Normal := by infer_instance
  have hPpi : IsPiNumber pi (Nat.card P) :=
    P.isPGroup'.isPiNumber_natCard hpPi
  have hPle : (P : Subgroup X) ≤ piCore pi X :=
    le_piCore hPnormal hPpi
  exact P.not_dvd_index
    (hpIndex.trans (Subgroup.index_dvd_of_le hPle))

/-- `BGsection14.v: P2type_signalizer`, Bender--Glauberman Lemma 14.12. -/
theorem P2type_signalizer
    {M Mstar U K R H : Subgroup G} {r : ℕ} [Fact r.Prime]
    (hMP2 : M ∈ typeP2MaximalSubgroups (G := G))
    (hCompl : KappaComplement M U K)
    (hMstar : Mstar ∈ minSimple_max_groups_of (G := G)
      (Subgroup.centralizer (K : Set G) : Set G))
    (hR : IsSylowSubgroupOf r R U)
    (hH : H ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (R : Set G) : Set G)) :
    H ∈ typeFMaximalSubgroups (G := G) ∧
      U ≤ sigmaCore H ∧
      U ⊔ K = M ⊓ H ∧
      (¬ normalizerWithin H U ≤ M) ∧
      K ≤ fittingWithin (H ⊓ Mstar) ∧
      IsHall (sigmaPrimes H)ᶜ ((H ⊓ Mstar).subgroupOf H) := by
  classical
  have hMP : M ∈ typePMaximalSubgroups (G := G) := hMP2.1
  have hmaxM : M ∈ minSimple_max_groups (G := G) := hMP.1
  have hmaxH : H ∈ minSimple_max_groups (G := G) := hH.1
  have hmaxMstar : Mstar ∈ minSimple_max_groups (G := G) := hMstar.1
  have hCtx := kappa_compl_context hmaxM hCompl
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hF := (trivg_kappa hmaxM hCompl.K_le_M hCompl.hall_K).mp hKbot
    exact hMP.2 hF
  obtain ⟨Mpartner, hEmbed⟩ :=
    Ptype_embedding hMP hCompl.K_le_M hCompl.hall_K
  have hStruct := Ptype_structure hMP hCompl.K_le_M hCompl.hall_K
  have hKprime : (Nat.card K).Prime :=
    (hStruct.typeP2 hMP2).card_K_prime
  letI : Fact (Nat.card K).Prime := ⟨hKprime⟩
  have hKline : RankOneLineIn (Nat.card K) K K :=
    ⟨le_rfl, isElementaryAbelianOfRank_one_of_card_eq_prime rfl⟩
  have huniqK := hEmbed.rankOne_unique hKprime hKline
  have hMstar_eq : Mstar = Mpartner := by
    exact eq_uniq_mmax huniqK hmaxMstar hMstar.2
  subst Mpartner

  have hRne : R ≠ ⊥ := by
    intro hRbot
    have hnormalizerBot :
        Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top (⊥ : Subgroup G)
    have htop : (⊤ : Subgroup G) ≤ H := by
      have hnormalizerR := hH.2
      rw [hRbot, hnormalizerBot] at hnormalizerR
      exact hnormalizerR
    exact (not_le_of_gt (mmax_proper hmaxH)) htop
  have hRU : R ≤ U := isSylowSubgroupOf_le_14 hR
  have hrR : r ∣ Nat.card R :=
    (IsSylowSubgroupOf.isPGroup hR).card_eq_or_dvd.resolve_left
      (fun hcard ↦ hRne (Subgroup.card_eq_one.mp hcard))
  have hrU : r ∣ Nat.card U :=
    hrR.trans (Subgroup.card_dvd_of_le hRU)
  have hrUsub : r ∣ Nat.card (U.subgroupOf M) := by
    simpa [MathlibSupport.natCard_subgroupOf_eq hCompl.U_le_M] using hrU
  have hrCompl : r ∈ (sigmaKappaPrimes M)ᶜ :=
    hCompl.hall_U.isPiNumber_card Fact.out hrUsub
  have hR_M : IsSylowSubgroupOf r R M :=
    isSylowSubgroupOf_of_hall_14
      hCompl.U_le_M hCompl.hall_U hrCompl hR
  have hrNotSigmaM : r ∉ sigmaPrimes M := by
    exact fun hrSigma ↦ hrCompl (Or.inl hrSigma)
  have hRM : R ≤ M := isSylowSubgroupOf_le_14 hR_M
  have hRH : R ≤ H := Subgroup.le_normalizer.trans hH.2
  have hHnotM : ¬ AreConjugateSubgroups M H := by
    exact not_conjugate_of_sylow_normalizer_14
      hmaxM hmaxH hR_M hRH hrNotSigmaM hH.2

  have hE_le_H : U ⊔ K ≤ H := by
    have hUcomm := hCtx.U_abelian_of_K_ne_bot hKne
    have hUcentR : U ≤ Subgroup.centralizer (R : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val
        ((isMulCommutative_iff.mp hUcomm
          ⟨u, hu⟩ ⟨x, hRU hx⟩).symm)
    have hUH : U ≤ H :=
      hUcentR.trans
        (Subgroup.centralizer_le_normalizer (R : Set G)) |>.trans hH.2
    obtain ⟨P, hRP⟩ := hR
    letI : Group.IsNilpotent U :=
      isNilpotent_of_isMulCommutative_14_11 hUcomm
    have hRcore : R = (pCore r U).map U.subtype := by
      rw [hRP, pCore_eq_sylow_of_isNilpotent P]
    have hKnormU : K ≤ Subgroup.normalizer (U : Set G) := by
      exact le_sup_right.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          hCtx.U_K_sdprod.1).mp hCtx.U_K_sdprod.2.2.1)
    have hKnormR : K ≤ Subgroup.normalizer (R : Set G) := by
      rw [hRcore]
      exact hKnormU.trans
        (characteristic_map_subtype_le_normalizer_14_11
          U (pCore r U))
    exact sup_le hUH (hKnormR.trans hH.2)
  have hUH : U ≤ H := le_sup_left.trans hE_le_H
  have hKH : K ≤ H := le_sup_right.trans hE_le_H
  have hKMstar : K ≤ Mstar := by
    rw [← hEmbed.doubleCentralizer]
    exact (centralizerWithin_le_left _ _).trans (sigmaCore_le Mstar)
  have hStarStruct := Ptype_structure hEmbed.Mstar_typeP
    hEmbed.Kstar_le_Mstar hEmbed.Kstar_hall_kappa
  have hK_unique_conj : ∀ g : G,
      K ≤ Mstar.map (MulAut.conj g).toMonoidHom → g ∈ Mstar := by
    intro g hKg
    by_contra hg
    have hbot := hStarStruct.Kstar_TI_outside g hg
    change centralizerWithin (sigmaCore Mstar) (pTypePartner M K) ⊓
        Mstar.map (MulAut.conj g).toMonoidHom = ⊥ at hbot
    rw [hEmbed.doubleCentralizer] at hbot
    have hKbot : K ≤ ⊥ := by
      rw [← hbot]
      exact le_inf le_rfl hKg
    exact hKne (eq_bot_iff.mpr hKbot)
  have hHnotMstar : ¬ AreConjugateSubgroups Mstar H := by
    rintro ⟨g, rfl⟩
    have hgMstar : g ∈ Mstar := hK_unique_conj g hKH
    have hMstarJ :
        Mstar.map (MulAut.conj g).toMonoidHom = Mstar :=
      map_conj_eq_self_of_mem_14_9 Mstar hgMstar
    have hRMstar : R ≤ Mstar := by
      simpa only [hMstarJ] using hRH
    have hRjoin : R ≤ pTypeJoin M K := by
      rw [← hEmbed.cyclicStructure.inf_eq_join]
      exact le_inf hRM hRMstar
    have hrK : ¬ r ∣ Nat.card K := by
      intro hrK
      exact hrCompl (Or.inr
        (hCompl.hall_K.isPiNumber_card Fact.out (by
          simpa [MathlibSupport.natCard_subgroupOf_eq hCompl.K_le_M]
            using hrK)))
    have hrPartner : ¬ r ∣ Nat.card (pTypePartner M K) := by
      intro hrKs
      exact hrCompl (Or.inl
        (hEmbed.Kstar_hall_sigma.isPiNumber_card Fact.out (by
          simpa [MathlibSupport.natCard_subgroupOf_eq
            hEmbed.Kstar_le_Mstar] using hrKs)))
    have hjoin :
        normalizerWithin M K = pTypeJoin M K := by
      change normalizerWithin M K = K ⊔ pTypeCentralizer M K
      exact internalDirectProduct_eq_sup_14_12
        hStruct.normalizer_direct
    have hcardJoin :
        Nat.card (pTypeJoin M K) =
          Nat.card K * Nat.card (pTypePartner M K) := by
      rw [← hjoin]
      exact hStruct.normalizer_direct.card_eq_mul_card
    have hrJoin : r ∣ Nat.card (pTypeJoin M K) :=
      hrR.trans (Subgroup.card_dvd_of_le hRjoin)
    rw [hcardJoin] at hrJoin
    exact (Fact.out : r.Prime).not_dvd_mul hrK hrPartner hrJoin
  have hHF : H ∈ typeFMaximalSubgroups (G := G) := by
    by_contra hnotF
    have hHP : H ∈ typePMaximalSubgroups (G := G) :=
      ⟨hmaxH, hnotF⟩
    rcases hEmbed.typeP_transitive hHP with hconj | hconj
    · exact hHnotM hconj
    · exact hHnotMstar hconj

  have hKsigmaComplH :
      IsPiNumber (sigmaPrimes H)ᶜ (Nat.card K) := by
    have hKsigmaMstar : K ≤ sigmaCore Mstar := by
      rw [← hEmbed.doubleCentralizer]
      exact centralizerWithin_le_left _ _
    have hKpi : IsPiNumber (sigmaPrimes Mstar) (Nat.card K) :=
      (sigmaCore_isPiNumber Mstar).of_dvd
        (Subgroup.card_dvd_of_le hKsigmaMstar)
    have hnotmap : ∀ g : G,
        H ≠ Mstar.map (MulAut.conj g).toMonoidHom := by
      intro g heq
      exact hHnotMstar ⟨g, heq⟩
    exact hKpi.mono fun p hpMstar hpH ↦
      (Set.disjoint_left.mp
        (sigma_partition hmaxMstar hmaxH hnotmap)) hpMstar hpH
  obtain ⟨D, hKD, hDH, hHallD⟩ :=
    MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
      hKH (mmax_sol hmaxH) (sigmaPrimes H)ᶜ hKsigmaComplH
  have hKfitD : K ≤ fittingWithin D := by
    let q := Nat.card K
    letI : Fact q.Prime := ⟨hKprime⟩
    have hKlineD : RankOneLineIn q D K :=
      ⟨hKD, isElementaryAbelianOfRank_one_of_card_eq_prime rfl⟩
    by_contra hnotFit
    obtain ⟨L, hmaxL, hcase⟩ :=
      primes_non_Fitting_Ftype hHF hDH hHallD hKlineD hnotFit
    have hKsigmaMstar : K ≤ sigmaCore Mstar := by
      rw [← hEmbed.doubleCentralizer]
      exact centralizerWithin_le_left _ _
    have hqSigmaMstar : q ∈ sigmaPrimes Mstar := by
      exact (sigmaCore_isPiNumber Mstar).of_dvd
        (Subgroup.card_dvd_of_le hKsigmaMstar)
        hKprime (by simp [q])
    rcases hcase with ⟨hqTau2L, huniqL⟩ |
        ⟨hqKappaL, hLP1⟩
    · have hLMstar : L = Mstar :=
        eq_uniq_mmax huniqK hmaxL (mem_uniq_mmax huniqL).2
      subst L
      exact hqTau2L.2.1 hqSigmaMstar
    · rcases hEmbed.typeP_transitive hLP1.1 with hML | hMstarL
      · rcases hML with ⟨g, rfl⟩
        exact hMP2.2 ((P1typeJ M g).mp hLP1)
      · rcases hMstarL with ⟨g, rfl⟩
        have hqKappaMstar : q ∈ kappaPrimes Mstar := by
          simpa only [kappaJ Mstar g] using hqKappaL
        exact (kappa_sigma' Mstar hqKappaMstar) hqSigmaMstar
  have hDMstar : D ≤ Mstar := by
    have hFMstar : fittingWithin D ≤ Mstar :=
      nilpotent_over_unique_conjugate_le_14_12
        hKfitD hKMstar (fittingWithin_isNilpotent D) hK_unique_conj
    intro d hd
    apply hK_unique_conj d
    intro k hk
    have hdInv : d⁻¹ ∈
        Subgroup.normalizer (fittingWithin D : Set G) :=
      (Subgroup.normalizer (fittingWithin D : Set G)).inv_mem
        (fittingWithin_le_normalizer D hd)
    have hconjFit : d⁻¹ * k * d ∈ fittingWithin D := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp hdInv k).mp (hKfitD hk)
    refine ⟨d⁻¹ * k * d, hFMstar hconjFit, ?_⟩
    change d * (d⁻¹ * k * d) * d⁻¹ = k
    group

  have hcommUK : ⁅U, K⁆ = U := by
    have hKnormU : K ≤ Subgroup.normalizer (U : Set G) := by
      exact le_sup_right.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          hCtx.U_K_sdprod.1).mp hCtx.U_K_sdprod.2.2.1)
    have hcopUK : Nat.Coprime (Nat.card U) (Nat.card K) :=
      by
        have hUPi :
            IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card U) := by
          simpa [MathlibSupport.natCard_subgroupOf_eq hCompl.U_le_M]
            using hCompl.hall_U.isPiNumber_card
        have hKPi : IsPiNumber (sigmaKappaPrimes M) (Nat.card K) := by
          have hKappa : IsPiNumber (kappaPrimes M) (Nat.card K) := by
            simpa [MathlibSupport.natCard_subgroupOf_eq hCompl.K_le_M]
              using hCompl.hall_K.isPiNumber_card
          exact hKappa.mono fun _ hp ↦ Or.inr hp
        exact (hKPi.coprime_compl hUPi).symm
    have hUsol : IsSolvable U := by
      letI : IsSolvable M := mmax_sol hmaxM
      exact isSolvable_of_injective
        (Subgroup.inclusion hCompl.U_le_M)
        (Subgroup.inclusion_injective hCompl.U_le_M)
    have hcentUK : centralizerWithin U K = ⊥ :=
      centralizerWithin_eq_bot_of_semiregular_actor_ne_bot_14_12
        hCtx.U_K_semiregular hKne
    have hUcomm : U ≤ ⁅K, U⁆ := by
      letI : IsSolvable U := hUsol
      have hdecomp :=
        le_commutator_sup_centralizerWithin_of_coprime hKnormU hcopUK
      simpa [hcentUK, sup_bot_eq] using hdecomp
    rw [Subgroup.commutator_comm]
    exact le_antisymm
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hKnormU)
      hUcomm
  have hU_sigmaH : U ≤ sigmaCore H := by
    let q := Nat.card K
    letI : Fact q.Prime := ⟨hKprime⟩
    have hqKappaM : q ∈ kappaPrimes M := by
      exact hCompl.hall_K.isPiNumber_card hKprime (by
        simpa [q, MathlibSupport.natCard_subgroupOf_eq hCompl.K_le_M])
    have hUqCompl :
        IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card U) := by
      have hUpi :
          IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card U) := by
        simpa [MathlibSupport.natCard_subgroupOf_eq hCompl.U_le_M] using
          hCompl.hall_U.isPiNumber_card
      apply hUpi.mono
      intro p hpU
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hpq
      subst p
      exact hpU (Or.inr hqKappaM)
    have hKq : IsPGroup q K :=
      (isElementaryAbelianOfRank_one_of_card_eq_prime
        (by rfl : Nat.card K = q)).isPGroup
    have hKpCoreAmbient : K ≤ (pCore q D).map D.subtype := by
      let F : Subgroup G := fittingWithin D
      letI : Group.IsNilpotent F := fittingWithin_isNilpotent D
      have hKFq : IsPGroup q (K.subgroupOf F) :=
        hKq.of_equiv (Subgroup.subgroupOfEquivOfLe hKfitD).symm
      calc
        K = (K.subgroupOf F).map F.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hKfitD).symm
        _ ≤ (pCore q F).map F.subtype :=
          Subgroup.map_mono hKFq.le_pCore_of_isNilpotent
        _ = (pCore q D).map D.subtype :=
          map_pCore_fittingWithin_eq_map_pCore D q
    have hKsubD : K.subgroupOf D ≤ pCore q D := by
      intro x hx
      rcases hKpCoreAmbient hx with ⟨y, hy, hxy⟩
      have hyx : y = x := by
        apply Subtype.ext
        exact hxy
      simpa [hyx] using hy

    have hsd := sdprod_sigma hmaxH hDH hHallD
    let SH : Subgroup H := (sigmaCore H).subgroupOf H
    let DH : Subgroup H := D.subgroupOf H
    letI : SH.Normal := hsd.2.2.1
    let hcomp : SH.IsComplement' DH := hsd.2.2.2
    let rp : H →* DH :=
      Subgroup.IsComplement'.rightProjection hcomp
    let eDH : DH ≃* D := Subgroup.subgroupOfEquivOfLe hDH
    let proj : H →* D := eDH.toMonoidHom.comp rp
    let UH : Subgroup H := U.subgroupOf H
    let KH : Subgroup H := K.subgroupOf H
    let UD : Subgroup D := UH.map proj
    let KD : Subgroup D := KH.map proj
    have hcommHK : ⁅UH, KH⁆ = UH := by
      rw [← subgroupOf_commutator_eq hUH hKH, hcommUK]
    have hKDcore : KD ≤ pCore q D := by
      rintro _ ⟨x, hx, rfl⟩
      let xDH : DH := ⟨(x : H), hKD hx⟩
      have hrpx : rp (x : H) = xDH := by
        exact Subgroup.IsComplement'.rightProjection_apply_right
          hcomp xDH
      change eDH (rp (x : H)) ∈ pCore q D
      rw [hrpx]
      exact hKsubD hx
    have hcommUD : ⁅UD, KD⁆ = UD := by
      rw [← Subgroup.map_commutator, hcommHK]
    have hUDnormCore :
        UD ≤ Subgroup.normalizer (pCore q D : Set D) := by
      rw [(pCore q D).normalizer_eq_top]
      exact le_top
    have hUDcore : UD ≤ pCore q D := by
      have hcommLe : ⁅UD, KD⁆ ≤ pCore q D :=
        (Subgroup.commutator_mono le_rfl hKDcore).trans
          (Subgroup.le_normalizer_iff_commutator_le_right.mp
            hUDnormCore)
      simpa only [hcommUD] using hcommLe
    have hUDq : IsPGroup q UD :=
      (pCore_isPGroup.to_subgroup (UD.subgroupOf (pCore q D))).of_equiv
        (Subgroup.subgroupOfEquivOfLe hUDcore)
    have hUDqPi : IsPiNumber ({q} : Set ℕ) (Nat.card UD) :=
      hUDq.isPiNumber_natCard (Set.mem_singleton q)
    have hUDqCompl : IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card UD) := by
      apply hUqCompl.of_dvd
      simpa only [UD, UH,
        MathlibSupport.natCard_subgroupOf_eq hUH] using
          Subgroup.card_map_dvd UH proj
    have hUDcard : Nat.card UD = 1 :=
      Nat.eq_one_of_dvd_coprimes
        (hUDqPi.coprime_compl hUDqCompl) dvd_rfl dvd_rfl
    have hUDbot : UD = ⊥ := Subgroup.card_eq_one.mp hUDcard
    have hUHker : UH ≤ proj.ker := by
      exact (Subgroup.map_eq_bot_iff UH).mp (by
        simpa only [UD] using hUDbot)
    intro u hu
    let uH : H := ⟨u, hUH hu⟩
    have huProj : proj uH = 1 := hUHker hu
    have huRp : rp uH = 1 := by
      apply eDH.injective
      simpa [proj] using huProj
    obtain ⟨⟨s, d⟩, hsdEq⟩ := hcomp.2 uH
    have hdOne : d = 1 := by
      have hprojEq := congrArg rp hsdEq
      have hrs : rp (s : H) = 1 :=
        Subgroup.IsComplement'.rightProjection_apply_left hcomp s
      have hrd : rp (d : H) = d :=
        Subgroup.IsComplement'.rightProjection_apply_right hcomp d
      simpa only [map_mul, hrs, hrd, huRp, one_mul] using hprojEq
    have huEq : uH = (s : H) := by
      calc
        uH = (s : H) * (d : H) := hsdEq.symm
        _ = (s : H) := by rw [hdOne]; simp
    have huVal : u = (s : G) :=
      congrArg (fun z : H ↦ (z : G)) huEq
    rw [huVal]
    exact s.property
  have hnormalizer_eq : normalizerWithin M U = U ⊔ K := by
    let E : Subgroup G := U ⊔ K
    have hEnormU : E ≤ Subgroup.normalizer (U : Set G) := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        hCtx.U_K_sdprod.1).mp hCtx.U_K_sdprod.2.2.1
    apply le_antisymm
    · intro x hx
      have hsd := sdprod_sigma hmaxM
        hCtx.U_sup_K_le_M hCtx.hall_sigma_complement
      obtain ⟨⟨s, e⟩, hse⟩ := hsd.2.2.2.2 ⟨x, hx.1⟩
      have hseG : (s : G) * (e : G) = x :=
        congrArg Subtype.val hse
      have hsNormU : (s : G) ∈ Subgroup.normalizer (U : Set G) := by
        have hsEq : (s : G) = x * (e : G)⁻¹ := by
          rw [← hseG]
          group
        rw [hsEq]
        exact (Subgroup.normalizer (U : Set G)).mul_mem hx.2
          ((Subgroup.normalizer (U : Set G)).inv_mem
            (hEnormU e.property))
      have hUnormSigma :
          U ≤ Subgroup.normalizer (sigmaCore M : Set G) := by
        exact hCompl.U_le_M.trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (sigmaCore_le M)).mp hsd.2.2.1)
      have hcopSigmaU :
          (Nat.card (sigmaCore M)).Coprime (Nat.card U) := by
        exact (coprime_sigma_compl hCtx.U_sup_K_le_M
          hCtx.hall_sigma_complement).coprime_dvd_right
            (Subgroup.card_dvd_of_le le_sup_left)
      have hsCentU :
          (s : G) ∈ Subgroup.centralizer (U : Set G) :=
        mem_centralizer_of_mem_of_mem_normalizer_of_coprime
          hUnormSigma hcopSigmaU s.property hsNormU
      obtain ⟨S, hRS⟩ := hR_M
      have hOmegaU : sylowOmegaOne M S ≤ U := by
        have hOmegaR : sylowOmegaOne M S ≤ R := by
          rw [hRS]
          exact Subgroup.map_subtype_le (omegaOne r (ambientSylow M S))
        exact hOmegaR.trans hRU
      have hrMcard : r ∣ Nat.card M :=
        hrR.trans (Subgroup.card_dvd_of_le hRM)
      have hrNotKappaM : r ∉ kappaPrimes M := by
        exact fun hrKappa ↦ hrCompl (Or.inr hrKappa)
      have hFacts := sigma'_kappa'_facts S hmaxM
        ⟨Fact.out, hrMcard⟩ hrNotSigmaM hrNotKappaM
      have hsCentOmega :
          (s : G) ∈ Subgroup.centralizer
            (sylowOmegaOne M S : Set G) :=
        Subgroup.centralizer_le hOmegaU hsCentU
      have hsOne : (s : G) = 1 := by
        have hsBot : (s : G) ∈ (⊥ : Subgroup G) := by
          rw [← hFacts.sigma_centralizer]
          exact ⟨s.property, hsCentOmega⟩
        exact Subgroup.mem_bot.mp hsBot
      rw [← hseG, hsOne, one_mul]
      exact e.property
    · exact le_inf hCtx.U_sup_K_le_M hEnormU
  let q := Nat.card K
  letI : Fact q.Prime := ⟨hKprime⟩
  have hqD : q ∣ Nat.card D := by
    exact (by simp [q] : q ∣ Nat.card K).trans
      (Subgroup.card_dvd_of_le hKD)
  have hqH : q ∣ Nat.card H :=
    hqD.trans (Subgroup.card_dvd_of_le hDH)
  have hqNotSigmaH : q ∉ sigmaPrimes H := by
    have hqDsub : q ∣ Nat.card (D.subgroupOf H) := by
      simpa [MathlibSupport.natCard_subgroupOf_eq hDH] using hqD
    exact hHallD.isPiNumber_card hKprime hqDsub
  have hqNotKappaH : q ∉ kappaPrimes H := by
    have hkappaEmpty : kappaPrimes H = ∅ := (FtypeP hmaxH).mp hHF
    rw [hkappaEmpty]
    simp
  let Sq : Sylow q H := Classical.choice Sylow.nonempty
  have hSigmaHnil : Group.IsNilpotent (sigmaCore H) :=
    (sigma'_kappa'_facts Sq hmaxH ⟨hKprime, hqH⟩
      hqNotSigmaH hqNotKappaH).sigma_nilpotent
  have hSigmaHfit : sigmaCore H ≤ fittingWithin H := by
    exact nilpotent_normal_le_fittingWithin_14_11
      (sigmaCore_le H) (sdprod_sigma hmaxH hDH hHallD).2.2.1
        hSigmaHnil
  let pi : Set ℕ := (sigmaKappaPrimes M)ᶜ
  let F : Subgroup G := fittingWithin H
  let Fu0 : Subgroup F := piCore pi F
  let Fu : Subgroup G := Fu0.map F.subtype
  have hFuF : Fu ≤ F := Subgroup.map_subtype_le Fu0
  have hFH : F ≤ H := fittingWithin_le H
  have hFuH : Fu ≤ H := hFuF.trans hFH
  have hFuSubF : Fu.subgroupOf F = Fu0 := by
    exact Subgroup.comap_map_eq_self_of_injective
      F.subtype_injective Fu0
  letI : Group.IsNilpotent F := fittingWithin_isNilpotent H
  have hFuHallF : IsHall pi (Fu.subgroupOf F) := by
    rw [hFuSubF]
    exact piCore_isHall_of_isNilpotent_14_12 pi
  have hUCardPi : IsPiNumber pi (Nat.card U) := by
    simpa [pi, MathlibSupport.natCard_subgroupOf_eq hCompl.U_le_M] using
      hCompl.hall_U.isPiNumber_card
  have hUF : U ≤ F := hU_sigmaH.trans hSigmaHfit
  have hUFu : U ≤ Fu := by
    apply le_normal_isHall_of_isPiNumber_14_11
      (C := F) (K := Fu)
    · rw [hFuSubF]
      infer_instance
    · exact hFuHallF
    · exact hUF
    · exact hUCardPi
  have hHnormFu : H ≤ Subgroup.normalizer (Fu : Set G) := by
    exact (fittingWithin_le_normalizer H).trans
      (by
        simpa only [Fu, Fu0] using
          (characteristic_map_subtype_le_normalizer_14_11
            F (piCore pi F)))
  have hFuPi : IsPiNumber pi (Nat.card Fu) := by
    simpa [MathlibSupport.natCard_subgroupOf_eq hFuF] using
      hFuHallF.isPiNumber_card
  have hMFu : M ⊓ Fu = U := by
    have hUI : U ≤ M ⊓ Fu := le_inf hCompl.U_le_M hUFu
    have hIpi : IsPiNumber pi (Nat.card (↑(M ⊓ Fu))) :=
      hFuPi.of_dvd (Subgroup.card_dvd_of_le inf_le_right)
    have hrelPi : IsPiNumber pi (U.relIndex (M ⊓ Fu)) :=
      hIpi.of_dvd (Subgroup.relIndex_dvd_card U (M ⊓ Fu))
    have hrelCompl : IsPiNumber piᶜ (U.relIndex (M ⊓ Fu)) := by
      apply hCompl.hall_U.isPiNumber_index.of_dvd
      exact ⟨(M ⊓ Fu).relIndex M,
        (U.relIndex_mul_relIndex (M ⊓ Fu) M
          hUI inf_le_left).symm⟩
    have hone : U.relIndex (M ⊓ Fu) = 1 :=
      Nat.eq_one_of_dvd_coprimes
        (hrelPi.coprime_compl hrelCompl) dvd_rfl dvd_rfl
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hUI
  have hsup_eq : U ⊔ K = M ⊓ H := by
    apply le_antisymm
    · exact le_inf hCtx.U_sup_K_le_M hE_le_H
    · have hInterNormU : M ⊓ H ≤
          Subgroup.normalizer (U : Set G) := by
        intro x hx
        have hxNormM : x ∈ Subgroup.normalizer (M : Set G) :=
          Subgroup.le_normalizer hx.1
        have hxNormFu : x ∈ Subgroup.normalizer (Fu : Set G) :=
          hHnormFu hx.2
        have hxNormInf : x ∈
            Subgroup.normalizer ((M ⊓ Fu : Subgroup G) : Set G) :=
          Subgroup.inf_normalizer_le_normalizer_inf
            ⟨hxNormM, hxNormFu⟩
        simpa only [hMFu] using hxNormInf
      have hle : M ⊓ H ≤ normalizerWithin M U :=
        le_inf inf_le_left hInterNormU
      simpa only [hnormalizer_eq] using hle
  letI : Group.IsNilpotent Fu := by
    letI : Group.IsNilpotent (Fu.subgroupOf F) := by infer_instance
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hFuF)
  have hnormalizer_not : ¬ normalizerWithin H U ≤ M := by
    intro hnorm
    by_cases hUFuEq : U = Fu
    · have hHnormU : H ≤ Subgroup.normalizer (U : Set G) := by
        simpa only [hUFuEq] using hHnormFu
      have hHM : H ≤ M :=
        (le_inf le_rfl hHnormU).trans hnorm
      exact hHnotM ⟨1, by
        rw [map_conj_eq_self_of_mem_14_9 M M.one_mem]
        exact eq_mmax hmaxH hmaxM hHM⟩
    · have hUsubNeTop : U.subgroupOf Fu ≠ ⊤ := by
        intro htop
        exact hUFuEq (le_antisymm hUFu
          (Subgroup.subgroupOf_eq_top.mp htop))
      have hNormProper : U.subgroupOf Fu <
          Subgroup.normalizer (U.subgroupOf Fu : Set Fu) :=
        Group.normalizerCondition_of_isNilpotent (U.subgroupOf Fu)
          (lt_top_iff_ne_top.mpr hUsubNeTop)
      obtain ⟨y, hyNorm, hyNotU⟩ := SetLike.exists_of_lt hNormProper
      have hyNormG : (y : G) ∈ Subgroup.normalizer (U : Set G) := by
        have hySub : y ∈
            (Subgroup.normalizer (U : Set G)).subgroupOf Fu := by
          rw [Subgroup.subgroupOf_normalizer_eq hUFu]
          exact hyNorm
        exact hySub
      have hyH : (y : G) ∈ H := hFuH y.property
      have hyM : (y : G) ∈ M := hnorm ⟨hyH, hyNormG⟩
      have hyU : (y : G) ∈ U := by
        rw [← hMFu]
        exact ⟨hyM, y.property⟩
      exact hyNotU hyU
  have hintersection : H ⊓ Mstar = D := by
    have hnotmap : ∀ g : G,
        H ≠ Mstar.map (MulAut.conj g).toMonoidHom := by
      intro g heq
      exact hHnotMstar ⟨g, heq⟩
    have hSigmaPrimeDisjoint :
        Disjoint (sigmaPrimes H) (sigmaPrimes Mstar) :=
      (sigma_partition hmaxMstar hmaxH hnotmap).symm
    have hSigmaPiH :
        IsPiNumber (sigmaPrimes H) (Nat.card (sigmaCore H)) :=
      sigmaCore_isPiNumber H
    have hSigmaPiMstar :
        IsPiNumber (sigmaPrimes Mstar) (Nat.card (sigmaCore Mstar)) :=
      sigmaCore_isPiNumber Mstar
    have hSigmaCoreDisjoint :
        Disjoint (sigmaCore H) (sigmaCore Mstar) :=
      Subgroup.disjoint_of_coprime_natCard
        (by
          apply Nat.coprime_of_dvd
          intro p hp hpH hpMstar
          exact (Set.disjoint_left.mp hSigmaPrimeDisjoint)
            (hSigmaPiH hp hpH) (hSigmaPiMstar hp hpMstar))
    have hSigmaInter : sigmaCore H ⊓ Mstar = ⊥ := by
      by_contra hne
      let X : Subgroup G := sigmaCore H ⊓ Mstar
      have hHnormSigma :
          H ≤ Subgroup.normalizer (sigmaCore H : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (sigmaCore_le H)).mp (sigmaCore_normal H)
      have hMstarNormSigma :
          Mstar ≤ Subgroup.normalizer (sigmaCore Mstar : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (sigmaCore_le Mstar)).mp (sigmaCore_normal Mstar)
      have hcommH : ⁅X, K⁆ ≤ sigmaCore H :=
        (Subgroup.commutator_mono inf_le_left le_rfl).trans
          (Subgroup.le_normalizer_iff_commutator_le_left.mp
            (hKH.trans hHnormSigma))
      have hcommMstar : ⁅X, K⁆ ≤ sigmaCore Mstar :=
        (Subgroup.commutator_mono inf_le_right
          (by
            rw [← hEmbed.doubleCentralizer]
            exact centralizerWithin_le_left _ _)).trans
          (Subgroup.le_normalizer_iff_commutator_le_right.mp
            hMstarNormSigma)
      have hcommBot : ⁅X, K⁆ = ⊥ := by
        apply le_antisymm ?_ bot_le
        exact (le_inf hcommH hcommMstar).trans
          (disjoint_iff.mp hSigmaCoreDisjoint).le
      have hXcentK : X ≤ Subgroup.centralizer (K : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
      have hcentNe : centralizerWithin (sigmaCore H) K ≠ ⊥ := by
        intro hcentBot
        apply hne
        apply le_antisymm ?_ bot_le
        exact (le_inf inf_le_left hXcentK).trans hcentBot.le
      have hqTau2H : q ∈ tau2Primes H := by
        have hqSupportD : q ∈ primeSupport (Nat.card D) :=
          ⟨hKprime, hqD⟩
        rcases primeSupport_sigma_complement_subset_tau_14_11
            hmaxH hDH hHallD hqSupportD with
          (hqTau1 | hqTau2) | hqTau3
        · exact (hqNotKappaH
            ⟨Or.inl hqTau1, K,
              ⟨hKH, isElementaryAbelianOfRank_one_of_card_eq_prime rfl⟩,
              hcentNe⟩).elim
        · exact hqTau2
        · exact (hqNotKappaH
            ⟨Or.inr hqTau3, K,
              ⟨hKH, isElementaryAbelianOfRank_one_of_card_eq_prime rfl⟩,
              hcentNe⟩).elim
      obtain ⟨A, hAD, hAH, hA⟩ := ex_tau2Elem hDH hHallD hqTau2H
      have hMstarNeH : Mstar ≠ H := by
        intro hEq
        apply hHnotMstar
        subst H
        refine ⟨1, ?_⟩
        exact (map_conj_eq_self_of_mem_14_9 Mstar Mstar.one_mem).symm
      have hAmaxMstar :
          Mstar ∈ minSimple_max_groups_of (G := G) (A : Set G) :=
        ⟨hmaxMstar, hAD.trans hDMstar⟩
      have hbot := (tau2_context hmaxH hqTau2H hAH hA)
        |>.maximal_intersection_eq_bot hAmaxMstar hMstarNeH
      exact hne hbot
    apply le_antisymm
    · intro x hx
      have hsd := sdprod_sigma hmaxH hDH hHallD
      obtain ⟨⟨s, d⟩, hsdEq⟩ := hsd.2.2.2.2 ⟨x, hx.1⟩
      have hsdG : (s : G) * (d : G) = x :=
        congrArg Subtype.val hsdEq
      have hsMstar : (s : G) ∈ Mstar := by
        have hsEq : (s : G) = x * (d : G)⁻¹ := by
          rw [← hsdG]
          group
        rw [hsEq]
        exact Mstar.mul_mem hx.2 (Mstar.inv_mem (hDMstar d.property))
      have hsOne : (s : G) = 1 := by
        have hsBot : (s : G) ∈ (⊥ : Subgroup G) := by
          rw [← hSigmaInter]
          exact ⟨s.property, hsMstar⟩
        exact Subgroup.mem_bot.mp hsBot
      rw [← hsdG, hsOne, one_mul]
      exact d.property
    · exact le_inf hDH hDMstar
  have hKfit : K ≤ fittingWithin (H ⊓ Mstar) := by
    simpa [hintersection] using hKfitD
  have hHallI :
      IsHall (sigmaPrimes H)ᶜ ((H ⊓ Mstar).subgroupOf H) := by
    simpa [hintersection] using hHallD
  exact ⟨hHF, hU_sigmaH, hsup_eq, hnormalizer_not, hKfit, hHallI⟩

/-! ## Lemma 14.13(a) -/

/-- Failure of a complementary pi-number condition exhibits a prime in
both the cardinal support and the selected prime set.  This formulation is
also used by the Section 16 summary. -/
theorem exists_primeSupport_inter_of_not_isPiNumber
    {pi : Set ℕ} {n : ℕ}
    (hpi : ¬ IsPiNumber piᶜ n) :
    ∃ p : ℕ, p ∈ primeSupport n ∧ p ∈ pi := by
  simp only [IsPiNumber] at hpi
  push_neg at hpi
  obtain ⟨p, hp, hpn, hpcompl⟩ := hpi
  exact ⟨p, ⟨hp, hpn⟩, by simpa using hpcompl⟩

/-- A prime cannot be a sigma prime in one maximal subgroup and a tau-two
prime in a conjugate maximal subgroup.  This is the conjugacy exclusion
used here and in the Section 16 support argument. -/
theorem not_conjugate_of_tau2_sigma
    {M N : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hN : N ∈ minSimple_max_groups (G := G))
    (hpSigma : p ∈ sigmaPrimes M)
    (hpTau : p ∈ tau2Primes N) :
    ¬ AreConjugateSubgroups M N := by
  intro hconj
  rcases hconj with ⟨g, rfl⟩
  apply hpTau.2.1
  simpa only [sigmaPrimes_conj] using hpSigma

private theorem rankOne_conjugate_into_sigmaMaximal_14_13
    {N Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hN : N ∈ minSimple_max_groups (G := G))
    (hqSigma : q ∈ sigmaPrimes N)
    (hQ : IsElementaryAbelianOfRank q 1 Q) :
    ∃ g : G, Q ≤ N.map (MulAut.conj g).toMonoidHom := by
  let S : Sylow q N := Classical.choice Sylow.nonempty
  obtain ⟨T, hT⟩ := sigma_Sylow_G hN hqSigma S
  obtain ⟨V, hQV⟩ := hQ.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T V
  have hTV :
      (T : Subgroup G).map (MulAut.conj g).toMonoidHom =
        (V : Subgroup G) := by
    change MulAut.conj g • (T : Subgroup G) = (V : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
  refine ⟨g, hQV.trans ?_⟩
  rw [← hTV, hT]
  exact Subgroup.map_mono (Subgroup.map_subtype_le (S : Subgroup N))

private theorem rankOne_prime_dvd_centralizer_index_of_commutator_ne_14_13
    {E A Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hQ : RankOneLineIn q E Q)
    (hcomm : ⁅A, Q⁆ ≠ ⊥)
    (hCnormal : ((centralizerWithin E A).subgroupOf E).Normal) :
    q ∣ ((centralizerWithin E A).subgroupOf E).index := by
  let C : Subgroup G := centralizerWithin E A
  let CE : Subgroup E := C.subgroupOf E
  let QE : Subgroup E := Q.subgroupOf E
  have hQcard : Nat.card Q = q := by
    simpa using hQ.2.card_eq
  have hdisCQ : Disjoint C Q := by
    letI : Fact (Nat.card Q).Prime :=
      ⟨by simpa [hQcard] using (Fact.out : q.Prime)⟩
    rcases (C.subgroupOf Q).eq_bot_or_eq_top_of_prime_card with
      hbot | htop
    · exact Subgroup.subgroupOf_eq_bot.mp hbot
    · have hQC : Q ≤ C := Subgroup.subgroupOf_eq_top.mp htop
      have hAcentQ : A ≤ Subgroup.centralizer (Q : Set G) :=
        Subgroup.le_centralizer_iff.mp (hQC.trans inf_le_right)
      exact (hcomm
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAcentQ)).elim
  have hdisCEQE : Disjoint CE QE := by
    rw [disjoint_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxOne : (x : G) = 1 := by
      exact Subgroup.mem_bot.mp
        (hdisCQ.le_bot ⟨hx.1, hx.2⟩)
    exact Subtype.ext hxOne
  have hCEQEbot : CE.subgroupOf QE = ⊥ :=
    Subgroup.subgroupOf_eq_bot.mpr hdisCEQE
  letI : CE.Normal := by
    simpa [CE, C] using hCnormal
  have hdvd : CE.relIndex QE ∣ CE.index :=
    CE.relIndex_dvd_index_of_normal QE
  have hrel : CE.relIndex QE = Nat.card QE := by
    rw [Subgroup.relIndex, hCEQEbot, Subgroup.index_bot]
  have hQEcard : Nat.card QE = Nat.card Q := by
    simpa [QE] using MathlibSupport.natCard_subgroupOf_eq hQ.1
  rw [hrel, hQEcard, hQcard] at hdvd
  simpa [CE, C] using hdvd

/-- `BGsection14.v: non_disjoint_signalizer_Frobenius`,
Bender--Glauberman Lemma 14.13(a).

Part (b) of the source lemma is not used in the Peterfalvi revision and is
therefore omitted, exactly as in the MathComp development. -/
theorem non_disjoint_signalizer_Frobenius
    {x : G} {M : Subgroup G}
    (hell : sigmaLength x = 1)
    (hlarge : 1 <
      (sigmaMaximalOvergroups
        (Subgroup.zpowers x : Set G)).ncard)
    (hM : M ∈ sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G))
    (hnot : ¬ IsPiNumber
      (sigmaPrimes (ftSignalizerBase x))ᶜ (Nat.card M)) :
    M ∈ typeFMaximalSubgroups (G := G) ∧
      IsPiNumber (tau2Primes M)ᶜ (Nat.card M) := by
  classical
  let N : Subgroup G := ftSignalizerBase x
  let R : Subgroup G := ftSignalizer x
  have hCtx := FT_signalizer_context hell
  have hLarge := hCtx.large hlarge
  have hmaxM : M ∈ minSimple_max_groups (G := G) := hM.1
  have hmaxN : N ∈ minSimple_max_groups (G := G) :=
    (mem_uniq_mmax hLarge.centralizer_maximal).1
  have hxSigmaM : Subgroup.zpowers x ≤ sigmaCore M := hM.2

  obtain ⟨q, hqM, hqSigmaN⟩ :=
    exists_primeSupport_inter_of_not_isPiNumber hnot
  letI : Fact q.Prime := ⟨hqM.1⟩
  obtain ⟨Q, hQ⟩ :=
    rankOneLineIn_of_prime_dvd_14 hqM.2
  have hQM : Q ≤ M := hQ.1
  have hlocal := hLarge.overgroup_context hM
  have hqBetaN : q ∈ betaPrimes N :=
    hlocal.beta_control ⟨hqM, hqSigmaN⟩
  have hqBetaG : q ∈ betaPrimes (⊤ : Subgroup G) := by
    have hpair :
        q ∈ sigmaPrimes N ∩ betaPrimes (⊤ : Subgroup G) := by
      rw [predI_sigma_beta hmaxN]
      exact hqBetaN
    exact hpair.2

  have hx1 : x ≠ 1 := by
    intro hx
    have hzero : sigmaLength x = 0 := (ell_sigma0P x).mpr hx
    omega
  obtain ⟨p, hpOrder⟩ :=
    exists_prime_mem_primeSupport_orderOf hx1
  letI : Fact p.Prime := ⟨hpOrder.1⟩
  have hpSigmaM : p ∈ sigmaPrimes M := by
    exact (sigmaCore_isPiNumber M).of_dvd
      ((sigmaCore M).orderOf_dvd_natCard
        (hxSigmaM (Subgroup.mem_zpowers x)))
        hpOrder.1 hpOrder.2
  have hpTau2N : p ∈ tau2Primes N :=
    hLarge.x_tau2 hpOrder.1 hpOrder.2
  have hNnotM : ¬ AreConjugateSubgroups M N := by
    exact not_conjugate_of_tau2_sigma hmaxM hmaxN
      hpSigmaM hpTau2N
  have hNnotMmap : ∀ g : G,
      N ≠ M.map (MulAut.conj g).toMonoidHom := by
    intro g heq
    exact hNnotM ⟨g, heq⟩
  have hqNotSigmaM : q ∉ sigmaPrimes M := by
    intro hq
    exact (Set.disjoint_left.mp
      (sigma_partition hmaxM hmaxN hNnotMmap)) hq hqSigmaN

  obtain ⟨g, hQNg⟩ :
      ∃ g : G, Q ≤ N.map (MulAut.conj g).toMonoidHom := by
    exact rankOne_conjugate_into_sigmaMaximal_14_13
      hmaxN hqSigmaN hQ.2
  let Ng : Subgroup G := N.map (MulAut.conj g).toMonoidHom
  have huniqQ :
      minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (Q : Set G) : Set G) = {Ng} := by
    have hqBetaNg : q ∈ betaPrimes Ng := by
      dsimp only [Ng]
      rw [betaPrimes_conj]
      exact hqBetaN
    exact (cent_der_sigma_uniq
      ((mmaxJ N (MulAut.conj g)).2 hmaxN)
      hQNg hQ.2
      (Or.inl hqBetaNg)).1
  have hpNotBetaM : p ∉ betaPrimes M := by
    intro hpBetaM
    have hpPair :
        p ∈ sigmaPrimes M ∩ betaPrimes (⊤ : Subgroup G) := by
      rw [predI_sigma_beta hmaxM]
      exact hpBetaM
    exact (tau2_not_beta hmaxN hpTau2N).1 hpPair.2

  have hMF : M ∈ typeFMaximalSubgroups (G := G) := by
    by_cases hMP1 : M ∈ typeP1MaximalSubgroups (G := G)
    · have hMP : M ∈ typePMaximalSubgroups (G := G) := hMP1.1
      have hqKappaM : q ∈ kappaPrimes M := by
        have hqSigmaKappa : q ∈ sigmaKappaPrimes M :=
          hMP1.2 hqM.1 hqM.2
        rcases hqSigmaKappa with hqSigma | hqKappa
        · exact (hqNotSigmaM hqSigma).elim
        · exact hqKappa
      obtain ⟨K, hQK, hKM, hHallK⟩ :=
        MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
          hQM (mmax_sol hmaxM) (kappaPrimes M)
            (hQ.2.isPGroup.isPiNumber_natCard hqKappaM)
      obtain ⟨L, hEmbed⟩ := Ptype_embedding hMP hKM hHallK
      have hLNg : L = Ng := by
        have huniqL := hEmbed.rankOne_unique hqM.1
          (show RankOneLineIn q K Q from ⟨hQK, hQ.2⟩)
        exact eq_uniq_mmax huniqQ hEmbed.Mstar_typeP.1
          (mem_uniq_mmax huniqL).2
      have hpRankL : HasElementaryAbelianRankAtLeast p 2 L := by
        rcases hpTau2N.2.2.1 with ⟨A, hAN, hA⟩
        refine ⟨A.map (MulAut.conj g).toMonoidHom, ?_,
          hA.map_of_injective (MulAut.conj g).toMonoidHom
            (MulAut.conj g).injective⟩
        simpa [Ng, hLNg] using Subgroup.map_mono
          (f := (MulAut.conj g).toMonoidHom) hAN
      have hpL : p ∣ Nat.card L := by
        rcases hpRankL with ⟨A, hAL, hA⟩
        have hpA : p ∣ Nat.card A := by
          rw [hA.card_eq, pow_two]
          exact dvd_mul_right p p
        exact hpA.trans (Subgroup.card_dvd_of_le hAL)
      have hpPartner : p ∣ Nat.card (pTypePartner M K) := by
        have hpProd :
            p ∣ Nat.card ((pTypePartner M K).subgroupOf L) *
              ((pTypePartner M K).subgroupOf L).index := by
          rw [((pTypePartner M K).subgroupOf L).card_mul_index]
          exact hpL
        rcases hpOrder.1.dvd_mul.mp hpProd with hpCard | hpIndex
        · simpa [MathlibSupport.natCard_subgroupOf_eq
            hEmbed.Kstar_le_Mstar] using hpCard
        · exact (hEmbed.Kstar_hall_sigma.isPiNumber_index
            hpOrder.1 hpIndex hpSigmaM).elim
      have hpKappaL : p ∈ kappaPrimes L := by
        exact hEmbed.Kstar_hall_kappa.isPiNumber_card
          hpOrder.1 (by
            simpa [MathlibSupport.natCard_subgroupOf_eq
              hEmbed.Kstar_le_Mstar] using
              hpPartner)
      exact ((rank_kappa hpKappaL).2 hpRankL).elim
    · by_contra hnotF
      have hMP : M ∈ typePMaximalSubgroups (G := G) :=
        ⟨hmaxM, hnotF⟩
      have hMP2 : M ∈ typeP2MaximalSubgroups (G := G) :=
        ⟨hMP, hMP1⟩
      obtain ⟨K, hKM, hHallK⟩ :=
        MathlibSupport.exists_ambient_isHall_of_isSolvable
          (mmax_sol hmaxM) (kappaPrimes M)
      have hP2 := (Ptype_structure hMP hKM hHallK).typeP2 hMP2
      exact hpNotBetaM (hP2.sigma_eq_beta ▸ hpSigmaM)

  apply And.intro hMF
  intro r hr hrDivM hrtau2
  letI : Fact r.Prime := ⟨hr⟩
  have hrM : r ∈ primeSupport (Nat.card M) :=
    ⟨hr, hrDivM⟩
  have hrRankN : ¬ HasElementaryAbelianRankAtLeast r 2 N := by
    intro hrank
    have hrNotBetaN : r ∉ betaPrimes N := by
      intro hrBetaN
      have hrPair :
          r ∈ sigmaPrimes N ∩ betaPrimes (⊤ : Subgroup G) := by
        rw [predI_sigma_beta hmaxN]
        exact hrBetaN
      exact (tau2_not_beta hmaxM hrtau2).1 hrPair.2
    have hrSigmaN : r ∈ sigmaPrimes N := by
      by_contra hrNotSigmaN
      by_cases hrank3 : HasElementaryAbelianRankAtLeast r 3 N
      · exact hrNotSigmaN (alpha_sub_sigma hmaxN ⟨hr, hrank3⟩)
      · have hrTauN : r ∈ tau2Primes N :=
          ⟨hr, hrNotSigmaN, hrank, hrank3⟩
        exact hrtau2.2.1 (hlocal.tau2_subset_sigma hrTauN)
    exact hrNotBetaN (hlocal.beta_control ⟨hrM, hrSigmaN⟩)
  obtain ⟨E, hQE, hEM, hHallE⟩ :=
    MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
      hQM (mmax_sol hmaxM) (sigmaPrimes M)ᶜ
        (hQ.2.isPGroup.isPiNumber_natCard (by
          simpa only [Set.mem_compl_iff] using hqNotSigmaM))
  obtain ⟨A, hAE, hAM, hA⟩ := ex_tau2Elem hEM hHallE hrtau2
  let A₀ : Subgroup G := ⁅A, Q⁆
  let A₁ : Subgroup G := centralizerWithin A Q
  have hA₀ne : A₀ ≠ ⊥ := by
    intro hA₀bot
    have hAcentQ : A ≤ Subgroup.centralizer (Q : Set G) := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      simpa [A₀] using hA₀bot
    have hANg : A ≤ Ng :=
      hAcentQ.trans (mem_uniq_mmax huniqQ).2
    have hbackN :
        A.map (MulAut.conj g⁻¹).toMonoidHom ≤ N := by
      exact map_conj_inv_le_of_le_map_conj_14 hANg
    apply hrRankN
    exact ⟨A.map (MulAut.conj g⁻¹).toMonoidHom, hbackN,
      hA.map_of_injective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective⟩
  have hqTau1M : q ∈ tau1Primes M := by
    have hFactor := tau1_cent_tau2Elem_factor
      hmaxM hEM hHallE hrtau2 hAE hA
    have hqIndex :
        q ∣ ((centralizerWithin E A).subgroupOf E).index := by
      exact rankOne_prime_dvd_centralizer_index_of_commutator_ne_14_13
        ⟨hQE, hQ.2⟩ (by simpa [A₀] using hA₀ne)
          hFactor.centralizer_normal
    exact hFactor.quotient_isPiNumber hqM.1 hqIndex
  have hregQ : centralizerWithin (sigmaCore M) Q = ⊥ := by
    apply le_antisymm ?_ bot_le
    by_contra hne
    have hne' : centralizerWithin (sigmaCore M) Q ≠ ⊥ := by
      intro heq
      exact hne heq.le
    have hqKappa : q ∈ kappaPrimes M :=
      ⟨Or.inl hqTau1M, Q, ⟨hQM, hQ.2⟩, hne'⟩
    have hempty : kappaPrimes M = ∅ := (FtypeP hmaxM).mp hMF
    rw [hempty] at hqKappa
    exact hqKappa.elim
  have hAction := tau1_act_tau2 hmaxM hEM hHallE hrtau2
    hAE hA hqTau1M hQE hQ.2 hregQ
      (by simpa [A₀, tau1ActionCommutator] using hA₀ne)
  have hA₀line := hAction.A0_rank_one
  have hA₁line := hAction.A1_rank_one
  have hA₀N : A₀ ≤ N := by
    have hA₀centSigma :
        A₀ ≤ Subgroup.centralizer (sigmaCore M : Set G) := by
      change tau1ActionCommutator A Q ≤
        Subgroup.centralizer (sigmaCore M : Set G)
      rw [← hAction.A0_sigma_centralizer]
      exact inf_le_right
    have hA₀centX : A₀ ≤ elementCentralizer x := by
      exact hA₀centSigma.trans
        (Subgroup.centralizer_le hxSigmaM)
    exact hA₀centX.trans hLarge.centralizer_le_base
  have hA₁gN :
      A₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ N := by
    have hA₁Ng : A₁ ≤ Ng :=
      inf_le_right.trans (mem_uniq_mmax huniqQ).2
    exact map_conj_inv_le_of_le_map_conj_14 hA₁Ng
  obtain ⟨P, hPp, hA₀P, hPsylow⟩ :=
    exists_ambient_sylow_containing
      hA₀line.2.isPGroup hA₀N
  have hPcyclic : IsCyclic P := by
    apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
      hPp (mFT_odd P)).2
    rintro ⟨B, hB⟩
    exact hrRankN ⟨B.map P.subtype,
      (Subgroup.map_subtype_le B).trans
        (isSylowSubgroupOf_le_14 hPsylow),
      hB.map_of_injective P.subtype P.subtype_injective⟩
  obtain ⟨S, hPS⟩ := hPsylow
  have hAmbientEq : ambientSylow N S = P := by
    simpa [ambientSylow] using hPS.symm
  let B : Subgroup G :=
    A₁.map (MulAut.conj g⁻¹).toMonoidHom
  have hBline : RankOneLineIn r N B := by
    exact ⟨hA₁gN,
      hA₁line.2.map_of_injective
        (MulAut.conj g⁻¹).toMonoidHom
          (MulAut.conj g⁻¹).injective⟩
  obtain ⟨z, hz⟩ := exists_conjugate_le_sylow_map
    S hA₁gN hBline.2.isPGroup
  have hBzP :
      B.map (MulAut.conj (z : G)).toMonoidHom ≤ P := by
    intro y hy
    rcases hy with ⟨b, hb, rfl⟩
    rw [hPS]
    exact hz b hb
  have hBzline :
      RankOneLineIn r N
        (B.map (MulAut.conj (z : G)).toMonoidHom) := by
    exact ⟨hBzP.trans (by
        rw [hPS]
        exact Subgroup.map_subtype_le (S : Subgroup N)),
      hBline.2.map_of_injective
        (MulAut.conj (z : G)).toMonoidHom
          (MulAut.conj (z : G)).injective⟩
  have hAmbientCyclic : IsCyclic (ambientSylow N S) := by
    rw [hAmbientEq]
    exact hPcyclic
  have hA₀eq :
      A₀ = (omegaOne r (ambientSylow N S)).map
        (ambientSylow N S).subtype := by
    exact rankOneLine_eq_sylowOmegaOne_14 S hAmbientCyclic
      ⟨hA₀N, hA₀line.2⟩ (by rw [hAmbientEq]; exact hA₀P)
  have hBzeq :
      B.map (MulAut.conj (z : G)).toMonoidHom =
        (omegaOne r (ambientSylow N S)).map
          (ambientSylow N S).subtype := by
    exact rankOneLine_eq_sylowOmegaOne_14 S hAmbientCyclic
      hBzline (by rw [hAmbientEq]; exact hBzP)
  have hEq :
      A₀ = A₁.map
        (MulAut.conj ((z : G) * g⁻¹)).toMonoidHom := by
    rw [hA₀eq, ← hBzeq]
    simp only [B, Subgroup.map_map]
    congr 1
    ext a
    simp [MulAut.conj_apply, mul_assoc]
  exact hAction.A0_not_conjugate_to_A1
    ((z : G) * g⁻¹)
      (by simpa [A₀, A₁, tau1ActionCommutator,
        tau1ActionFixedLine] using hEq)

end

end Submission.OddOrder.BG.Section14
