import Submission.OddOrder.BG.Section03.FrobeniusBasic
import Submission.OddOrder.BG.Section06.PrimeNilDerivedFactor
import Submission.OddOrder.MathlibSupport.ChiefFactor
import Submission.OddOrder.MathlibSupport.FaithfulQuotientRepresentation
import Submission.OddOrder.MathlibSupport.IrreducibleCenterScalar
import Submission.OddOrder.MathlibSupport.IrreducibleCharacterDegreeDivides
import Submission.OddOrder.MathlibSupport.IrreducibleDegreeIndexBound
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall
import Submission.OddOrder.MathlibSupport.RepresentationIrreducibleComp
import Submission.OddOrder.MathlibSupport.Solvability
import Submission.OddOrder.PF.Section01.NormalSubgroupConstituentKernels
import Submission.OddOrder.PF.Section06.BoundedSeqIndCoherence

/-!
# Odd Frobenius quotients and irreducible induced layers

This file ports Peterfalvi (6.4)--(6.6).  The derived join attached to a
normal subgroup `M` of the Frobenius kernel `K` is represented inside `K` by
`commutator K ⊔ M`; its image under `K.subtype` is the corresponding
ambient normal subgroup of `L`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.MathlibSupport
open CategoryTheory
open scoped BigOperators Classical IsMulCommutative MonoidAlgebra Pointwise

universe u

local instance oddFrobeniusQuotientInvertibleCard
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private abbrev derivedJoin {L : Type u} [Group L]
    (K : Subgroup L) (M : Subgroup K) : Subgroup K :=
  _root_.commutator K ⊔ M

private abbrev ambientDerivedJoin {L : Type u} [Group L]
    (K : Subgroup L) (M : Subgroup K) : Subgroup L :=
  (derivedJoin K M).map K.subtype

private theorem ambientDerivedJoin_normal
    {L : Type u} [Group L]
    (K : Subgroup L) [K.Normal]
    (M : Subgroup K)
    [((M.map K.subtype : Subgroup L)).Normal] :
    (ambientDerivedJoin K M).Normal := by
  dsimp [ambientDerivedJoin, derivedJoin]
  rw [Subgroup.map_sup]
  infer_instance

private theorem derivedJoin_normal
    {L : Type u} [Group L]
    (K : Subgroup L) [K.Normal]
    (M : Subgroup K)
    [((M.map K.subtype : Subgroup L)).Normal] :
    (derivedJoin K M).Normal := by
  apply Subgroup.Normal.of_map_subtype
  exact ambientDerivedJoin_normal K M

private theorem normal_of_ambient_normal
    {L : Type u} [Group L]
    (K : Subgroup L) (M : Subgroup K)
    [((M.map K.subtype : Subgroup L)).Normal] : M.Normal :=
  Subgroup.Normal.of_map_subtype inferInstance

local instance oddFrobeniusQuotientNormalOfNormalMapSubtype
    {L : Type u} [Group L] {K : Subgroup L} {M : Subgroup K}
    [((M.map K.subtype : Subgroup L)).Normal] : M.Normal :=
  normal_of_ambient_normal K M

/-- The quotient of the top subgroup by the transported copy of `M` is
canonically isomorphic to the ordinary quotient `K / M`. -/
private noncomputable def topQuotientEquiv
    {K : Type u} [Group K] (M : Subgroup K) [M.Normal] :
    ((⊤ : Subgroup K) ⧸ M.subgroupOf ⊤) ≃* (K ⧸ M) := by
  let f : (⊤ : Subgroup K) →* K ⧸ M :=
    (QuotientGroup.mk' M).comp (⊤ : Subgroup K).subtype
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective M x
    exact ⟨⟨k, trivial⟩, rfl⟩
  have hker : f.ker = M.subgroupOf (⊤ : Subgroup K) := by
    ext x
    change QuotientGroup.mk' M (x : K) = 1 ↔ (x : K) ∈ M
    exact QuotientGroup.eq_one_iff (x : K)
  exact
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)

private theorem nilpotent_topQuotient
    {K : Type u} [Group K] [Finite K]
    (M : Subgroup K) [M.Normal]
    (hnil : Group.IsNilpotent (K ⧸ M)) :
    Group.IsNilpotent ((⊤ : Subgroup K) ⧸ M.subgroupOf ⊤) := by
  letI : Group.IsNilpotent (K ⧸ M) := hnil
  exact Group.nilpotent_of_mulEquiv (topQuotientEquiv M).symm

/-- Universe-polymorphic specialization to complex characters of the
translation-kernel/representation-kernel identity. -/
private theorem translationKernelIrreducibleCharacterComplex
    {T : Type u} [Group T]
    (chi : IrreducibleCharacter T ℂ) :
    ClassFunction.translationKernel (chi : ClassFunction T ℂ) =
      chi.representation.ρ.ker := by
  apply le_antisymm
  · intro a ha
    rw [MonoidHom.mem_ker]
    let rho : Representation ℂ T chi.representation :=
      chi.representation.ρ
    letI : CategoryTheory.Simple chi.representation :=
      chi.representation_simple
    letI : Representation.IsIrreducible rho :=
      representation_isIrreducible_of_simple_fdRep
        chi.representation
    have htraceGroup (g : T) :
        LinearMap.trace ℂ chi.representation
            ((rho a - 1) * rho g) = 0 := by
      rw [sub_mul, one_mul, map_sub, ← rho.map_mul]
      change rho.character (a * g) - rho.character g = 0
      dsimp only [rho]
      change chi.representation.character (a * g) -
        chi.representation.character g = 0
      rw [chi.representation_character, chi.representation_character]
      exact sub_eq_zero.mpr (ha g)
    have htraceAlgebra (z : ℂ[T]) :
        LinearMap.trace ℂ chi.representation
            ((rho a - 1) * rho.asAlgebraHom z) = 0 := by
      induction z using MonoidAlgebra.induction_on with
      | hM g =>
          simpa only [Representation.asAlgebraHom_of] using
            htraceGroup g
      | hadd x y hx hy =>
          simp only [map_add, mul_add, hx, hy, add_zero]
      | hsmul c x hx =>
          simp only [map_smul, mul_smul_comm, hx, smul_zero]
    have htraceEnd (X : Module.End ℂ chi.representation) :
        LinearMap.trace ℂ chi.representation
            ((rho a - 1) * X) = 0 := by
      obtain ⟨z, rfl⟩ :=
        Representation.IsIrreducible.asAlgebraHom_surjective
          rho X
      exact htraceAlgebra z
    have hzero : rho a - 1 = 0 := by
      let b := Module.finBasis ℂ chi.representation
      apply (LinearMap.toMatrixAlgEquiv b).injective
      rw [map_zero]
      apply (Matrix.ext_iff_trace_mul_right).2
      intro X
      have hX := htraceEnd ((LinearMap.toMatrixAlgEquiv b).symm X)
      rw [LinearMap.trace_eq_matrix_trace ℂ b] at hX
      change
        ((LinearMap.toMatrixAlgEquiv b)
            ((rho a - 1) *
              (LinearMap.toMatrixAlgEquiv b).symm X)).trace = 0 at hX
      simpa only [map_mul, AlgEquiv.apply_symm_apply, Matrix.zero_mul,
        Matrix.trace_zero] using hX
    exact sub_eq_zero.mp hzero
  · intro a ha g
    rw [← chi.representation_character,
      ← chi.representation_character]
    change LinearMap.trace ℂ chi.representation
        (chi.representation.ρ (a * g)) =
      LinearMap.trace ℂ chi.representation (chi.representation.ρ g)
    rw [chi.representation.ρ.map_mul, MonoidHom.mem_ker.mp ha, one_mul]

private theorem irreducible_degree_one_of_commutator_le_kernel
    {K : Type u} [Group K] [Fintype K]
    (chi : IrreducibleCharacter K ℂ)
    (hder : _root_.commutator K ≤
      ClassFunction.translationKernel (chi : ClassFunction K ℂ)) :
    chi 1 = 1 := by
  let rho := chi.representation.ρ
  have hder' : _root_.commutator K ≤ rho.ker := by
    simpa only [rho,
      translationKernelIrreducibleCharacterComplex chi] using hder
  let Q := K ⧸ rho.ker
  let sigmaQ : Representation ℂ Q chi.representation :=
    quotientKerRepresentation rho
  let q : K →* Q := QuotientGroup.mk' rho.ker
  letI : IsMulCommutative Q :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hder'
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  letI : Representation.IsIrreducible (sigmaQ.comp q) := by
    change Representation.IsIrreducible rho
    infer_instance
  letI : Representation.IsIrreducible sigmaQ :=
    representation_isIrreducible_of_comp sigmaQ q
  rw [IrreducibleCharacter.apply_one_eq_finrank,
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative sigmaQ]
  norm_num

/-- Peterfalvi's Hypothesis (6.4): `L` has odd order, `K / M` is
nilpotent, and the quotient by `K' M` is a Frobenius group whose kernel is
the image of `K`.  Ambient normality of `M` is a typeclass hypothesis so
that both quotients are available without carrying proof fields in the
predicate. -/
def odd_Frobenius_quotient
    {L : Type u} [Group L] [Fintype L]
    (K : Subgroup L) [K.Normal]
    (M : Subgroup K)
    [((M.map K.subtype : Subgroup L)).Normal] : Prop :=
  letI : M.Normal := normal_of_ambient_normal K M
  let H1L : Subgroup L := ambientDerivedJoin K M
  letI : H1L.Normal := ambientDerivedJoin_normal K M
  Odd (Nat.card L) ∧
    Group.IsNilpotent (K ⧸ M) ∧
    ∃ E : Subgroup (L ⧸ H1L),
      IsFrobeniusDecomposition
        (K.map (QuotientGroup.mk' H1L)) E

private theorem coherent_derivedJoin_layer
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) [K.Normal]
    (tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (R : ClassFunction L ℂ → Finset (ClassFunction G ℂ))
    (hsub : subcoherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) : Set (ClassFunction L ℂ))
      tau R)
    (M : Subgroup K)
    [((M.map K.subtype : Subgroup L)).Normal] :
    coherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) (derivedJoin K M)) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) tau := by
  let H1 : Subgroup K := derivedJoin K M
  letI : ((H1.map K.subtype : Subgroup L)).Normal :=
    ambientDerivedJoin_normal K M
  apply uniform_degree_coherence
    (subset_subcoherent hsub
      (seqInd_conjC_subset1 K (⊤ : Subgroup K)
        (⊤ : Subgroup K) H1 le_rfl))
  intro phi hphi psi hpsi
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  obtain ⟨eta, heta, rfl⟩ := seqIndP.mp hpsi
  have hchiDer : _root_.commutator K ≤
      ClassFunction.translationKernel (chi : ClassFunction K ℂ) :=
    (show _root_.commutator K ≤ H1 from le_sup_left).trans
      (mem_Iirr_kerD.mp hchi).1
  have hetaDer : _root_.commutator K ≤
      ClassFunction.translationKernel (eta : ClassFunction K ℂ) :=
    (show _root_.commutator K ≤ H1 from le_sup_left).trans
      (mem_Iirr_kerD.mp heta).1
  rw [ClassFunction.induce_one, ClassFunction.induce_one,
    irreducible_degree_one_of_commutator_le_kernel chi hchiDer,
    irreducible_degree_one_of_commutator_le_kernel eta hetaDer]

private theorem relIndex_eq_card_map_quotient
    {A : Type u} [Group A] [Finite A]
    {N H : Subgroup A} (hNnormal : N.Normal) (hNH : N ≤ H) :
    N.relIndex H = Nat.card (H.map (QuotientGroup.mk' N)) := by
  letI : N.Normal := hNnormal
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  let f : H →* A ⧸ N := q.comp H.subtype
  have hker : f.ker = N.subgroupOf H := by
    ext x
    change q (x : A) = 1 ↔ (x : A) ∈ N
    exact QuotientGroup.eq_one_iff (x : A)
  have hrange : f.range = H.map q := by
    dsimp [f]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  calc
    N.relIndex H = (N.subgroupOf H).index := rfl
    _ = f.ker.index := congrArg Subgroup.index hker.symm
    _ = Nat.card f.range := Subgroup.index_ker f
    _ = Nat.card (H.map q) :=
      Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv

/-- The action of a Frobenius complement on every ambient-normal subgroup
of its kernel gives the congruence used in Peterfalvi (6.5). -/
private theorem frobenius_normal_kernel_card_modEq
    {Q : Type u} [Group Q] [Finite Q]
    {K E N : Subgroup Q}
    (hfrob : IsFrobeniusDecomposition K E)
    (hNnormal : N.Normal) (hNK : N ≤ K) :
    Nat.ModEq (Nat.card E) 1 (Nat.card N) := by
  letI : N.Normal := hNnormal
  have hnorm : E ≤ Subgroup.normalizer (N : Set Q) := by
    rw [N.normalizer_eq_top]
    exact le_top
  letI : MulDistribMulAction E N :=
    subgroupConjugationAction N E hnorm
  have hfixed : ∀ e : E, e ≠ 1 → ∀ n : N, e • n = n → n = 1 := by
    intro e he n hn
    let nK : K := ⟨(n : Q), hNK n.property⟩
    have hnK : (e : Q) * (nK : Q) * (e : Q)⁻¹ = (nK : Q) := by
      simpa only [nK,
        coe_subgroupConjugationAction_smul N E hnorm] using
          congrArg Subtype.val hn
    have hnone : nK = 1 := hfrob.fixedPointFree e he nK hnK
    apply Subtype.ext
    change (n : Q) = 1
    have hnone' := congrArg (fun x : K ↦ (x : Q)) hnone
    simpa only [nK, Subgroup.coe_one] using hnone'
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := E) (X := N))
  have hcard : Nat.card N = 1 + t * Nat.card E := by
    simpa [t] using natCard_eq_one_add_fixedOneOrbits_mul_natCard
      (G := E) (X := N) (fun e ↦ smul_one e) hfixed
  rw [hcard]
  exact
    ((Nat.modEq_zero_iff_dvd.mpr
      (dvd_mul_left (Nat.card E) t)).add_left 1).symm

private theorem two_mul_add_one_le_of_odd_modEq_one
    {e m : ℕ} (he : Odd e) (hm : Odd m)
    (hmod : Nat.ModEq e 1 m) (hm1 : 1 < m) :
    2 * e + 1 ≤ m := by
  have hle : 1 ≤ m := hm1.le
  obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd' hle).mp hmod
  have he0 : 0 < e := by
    rcases he with ⟨a, rfl⟩
    omega
  have hd0 : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    subst d
    simp only [mul_zero] at hd
    omega
  have hprodEven : Even (e * d) := by
    rw [← hd]
    exact Nat.Odd.sub_odd hm odd_one
  have hdNotOdd : ¬ Odd d := by
    intro hdOdd
    exact (Nat.not_odd_iff_even.mpr hprodEven) (he.mul hdOdd)
  have hdEven : Even d := Nat.not_odd_iff_even.mp hdNotOdd
  obtain ⟨a, ha⟩ := hdEven
  have hd2 : 2 ≤ d := by
    rw [ha] at hd0 ⊢
    omega
  calc
    2 * e + 1 = e * 2 + 1 := by omega
    _ ≤ e * d + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left e hd2) 1
    _ = m := by omega

private theorem isChiefFactor_of_maximal_normal
    {A : Type u} [Group A] [Finite A]
    {N H : Subgroup A}
    (hHnormal : H.Normal) (hNH : N < H)
    (hNnormal : N.Normal)
    (hmax : ∀ D : Subgroup A, D.Normal → D < H → N ≤ D → D ≤ N) :
    @IsChiefFactor A _ N H hNnormal := by
  letI : N.Normal := hNnormal
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  refine ⟨hNH.le, hHnormal, ?_⟩
  refine ⟨?_, Subgroup.Normal.map hHnormal q hqsurj, ?_⟩
  · intro hmap
    have hHN : H ≤ N := by
      have hker : H ≤ q.ker := (Subgroup.map_eq_bot_iff H).mp hmap
      simpa [q, QuotientGroup.ker_mk'] using hker
    exact (not_le_of_gt hNH) hHN
  · intro D hDnormal hDH hDne
    let B : Subgroup A := D.comap q
    have hBnormal : B.Normal := by
      dsimp [B]
      exact Subgroup.Normal.comap hDnormal q
    have hNB : N ≤ B := by
      dsimp [B, q]
      exact QuotientGroup.le_comap_mk' N D
    have hBH : B ≤ H := by
      have hkerH : q.ker ≤ H := by
        simpa [q, QuotientGroup.ker_mk'] using hNH.le
      calc
        B ≤ (H.map q).comap q := Subgroup.comap_mono hDH
        _ = H := Subgroup.comap_map_eq_self hkerH
    by_contra hHB
    have hnHB : ¬ H ≤ B := by
      intro h
      apply hHB
      exact Subgroup.map_le_iff_le_comap.mpr h
    have hBltH : B < H :=
      lt_of_le_of_ne hBH (fun h ↦ hnHB h.ge)
    have hBN : B ≤ N := hmax B hBnormal hBltH hNB
    have hBN_eq : B = N := le_antisymm hBN hNB
    apply hDne
    calc
      D = B.map q :=
        (Subgroup.map_comap_eq_self_of_surjective hqsurj D).symm
      _ = N.map q := congrArg (fun X : Subgroup A ↦ X.map q) hBN_eq
      _ = ⊥ := QuotientGroup.map_mk'_self N

private noncomputable def subgroupQuotientEquivAmbientImage
    {L : Type u} [Group L]
    (K : Subgroup L) (M : Subgroup K)
    [((M.map K.subtype : Subgroup L)).Normal] :
    (K ⧸ M) ≃*
      K.map (QuotientGroup.mk' (M.map K.subtype)) := by
  let ML : Subgroup L := M.map K.subtype
  let q : L →* L ⧸ ML := QuotientGroup.mk' ML
  let f : K →* K.map q := q.subgroupMap K
  have hf : Function.Surjective f := q.subgroupMap_surjective K
  have hker : f.ker = M := by
    dsimp [f, q, ML]
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact Subgroup.comap_map_eq_self_of_injective
      K.subtype_injective M
  exact
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- Prime-power order for a global minimal normal subgroup, assuming only
that the subgroup itself is solvable. -/
private theorem IsMinimalNormal.exists_prime_isPGroup_of_isSolvable
    {A : Type u} [Group A] [Finite A] {N : Subgroup A}
    [IsSolvable N] (hN : IsMinimalNormal N) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p N := by
  letI : N.Normal := hN.normal
  letI : IsMulCommutative N := hN.isMulCommutative_of_isSolvable
  have hcard : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.mpr hN.ne_bot
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hcard)
  letI : Fact p.Prime := ⟨hp⟩
  let S : Sylow p N := Classical.choice inferInstance
  have hSnon : (S : Subgroup N) ≠ ⊥ := S.ne_bot_of_dvd_card hpdvd
  have hScore : (S : Subgroup N) ≤ pCore p N :=
    le_pCore S.isPGroup' (by infer_instance)
  have hcoreNon : pCore p N ≠ ⊥ := by
    intro hcore
    apply hSnon
    rw [hcore] at hScore
    exact le_bot_iff.mp hScore
  let D : Subgroup A := (pCore p N).map N.subtype
  have hDnormal : D.Normal := by dsimp [D]; infer_instance
  have hDN : D ≤ N := by dsimp [D]; exact Subgroup.map_subtype_le _
  have hDnon : D ≠ ⊥ := by
    dsimp [D]
    intro hD
    apply hcoreNon
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore p N) N.subtype_injective).mp hD
  have hDN_eq : D = N := hN.eq_of_normal_le hDnormal hDN hDnon
  refine ⟨p, hp, ?_⟩
  rw [← hDN_eq]
  exact pCore_isPGroup.map N.subtype

private theorem isPGroup_of_nilpotent_of_abelianization_isPGroup
    {Q : Type u} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (hnil : Group.IsNilpotent Q)
    (hab : IsPGroup p (Q ⧸ _root_.commutator Q)) :
    IsPGroup p Q := by
  letI : Group.IsNilpotent Q := hnil
  let D : Subgroup Q := _root_.commutator Q
  let O : Subgroup Q := pPrimeCore p Q
  let P : Subgroup Q := pCore p Q
  letI : D.Normal := by dsimp [D]; infer_instance
  letI : O.Normal := by dsimp [O]; infer_instance
  letI : P.Normal := by dsimp [P]; infer_instance
  have hcomp : P.IsComplement' O := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      (disjoint_pCore_pPrimeCore (G := Q) (p := p))
    rw [← Subgroup.normal_mul P O,
      sup_pCore_pPrimeCore_eq_top_of_isNilpotent (G := Q) p]
    rfl
  have hOD : O ≤ D := by
    let qD : Q →* Q ⧸ D := QuotientGroup.mk' D
    let Obar : Subgroup (Q ⧸ D) := O.map qD
    have hObarP : IsPGroup p Obar := hab.to_subgroup Obar
    have hObarPrime : IsPPrimeSubgroup p Obar := by
      rw [IsPPrimeSubgroup]
      exact (pPrimeCore_coprime_card (G := Q) (p := p)).coprime_dvd_right
        (Subgroup.card_map_dvd O qD)
    have hObarCore : Obar ≤ pPrimeCore p (Q ⧸ D) := by
      apply le_pPrimeCore hObarPrime
      dsimp [Obar]
      infer_instance
    have hObarBot : Obar = ⊥ := by
      apply le_bot_iff.mp
      rw [← disjoint_iff.mp
        (disjoint_pPrimeCore_of_isPGroup (G := Q ⧸ D) hObarP)]
      exact le_inf le_rfl hObarCore
    have hker : O ≤ qD.ker := (Subgroup.map_eq_bot_iff O).mp hObarBot
    simpa [qD, QuotientGroup.ker_mk'] using hker
  have hObot : O = ⊥ := by
    by_contra hOne
    let qP : Q →* Q ⧸ P := QuotientGroup.mk' P
    have hqPO : Function.Surjective (qP.comp O.subtype) := by
      intro z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P z
      obtain ⟨po, hpo, _⟩ := hcomp.existsUnique g
      refine ⟨po.2, ?_⟩
      change qP (po.2 : Q) = qP g
      rw [← hpo, map_mul]
      have hpone : qP (po.1 : Q) = 1 :=
        (QuotientGroup.eq_one_iff (po.1 : Q)).mpr po.1.property
      rw [hpone, one_mul]
    have hOmap : O.map qP = ⊤ := by
      have hrange : (qP.comp O.subtype).range = O.map qP := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hrange]
      exact MonoidHom.range_eq_top.mpr hqPO
    have hcommTop : _root_.commutator (Q ⧸ P) = ⊤ := by
      apply top_unique
      rw [← hOmap]
      calc
        O.map qP ≤ D.map qP := Subgroup.map_mono hOD
        _ = _ := by
          dsimp [D]
          rw [map_commutator_eq,
            MonoidHom.range_eq_top.mpr
              (QuotientGroup.mk'_surjective P)]
          rfl
    let e : (Q ⧸ P) ≃* O := hcomp.symm.QuotientMulEquiv
    letI : Nontrivial O := O.nontrivial_iff_ne_bot.mpr hOne
    letI : Nontrivial (Q ⧸ P) := e.toEquiv.nontrivial
    exact (ne_of_lt
      (IsSolvable.commutator_lt_top_of_nontrivial (Q ⧸ P))) hcommTop
  have hPtop : P = ⊤ := by
    have hsup := sup_pCore_pPrimeCore_eq_top_of_isNilpotent (G := Q) p
    simpa [P, O, hObot] using hsup
  have htopP : IsPGroup p (⊤ : Subgroup Q) := by
    rw [← hPtop]
    exact pCore_isPGroup
  exact htopP.of_equiv Subgroup.topEquiv

/-- Peterfalvi (6.5).  Unless the layer cut out by `M` is coherent, the
derived join `K' M` is the lower term of a short chief factor, its index is
bounded, and `K / M` is a nonabelian `p`-group in the exceptional
congruence case. -/
theorem non_coherent_chief
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) [K.Normal] [IsSolvable K]
    (tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (R : ClassFunction L ℂ → Finset (ClassFunction G ℂ))
    (hsub : subcoherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) : Set (ClassFunction L ℂ))
      tau R)
    (M : Subgroup K)
    [((M.map K.subtype : Subgroup L)).Normal]
    (hfq : odd_Frobenius_quotient K M) :
    coherent
        (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) M) : Set (ClassFunction L ℂ))
        (nonidentitySet L) tau ∨
      let H1 : Subgroup K := derivedJoin K M
      let H1L : Subgroup L := ambientDerivedJoin K M
      letI : H1L.Normal := ambientDerivedJoin_normal K M
      IsChiefFactor H1L K ∧
        H1.index ≤ 4 * K.index ^ 2 + 1 ∧
        ∃ p : ℕ, p.Prime ∧ IsPGroup p (K ⧸ M) ∧
          ¬ IsMulCommutative (K ⧸ M) ∧
          ¬ K.index ∣ p - 1 := by
  let H1 : Subgroup K := derivedJoin K M
  let H1L : Subgroup L := ambientDerivedJoin K M
  letI : H1.Normal := derivedJoin_normal K M
  letI : H1L.Normal := ambientDerivedJoin_normal K M
  rcases hfq with ⟨hoddL, hnilKM, E, hfrob⟩
  have hMH1 : M ≤ H1 := by
    dsimp [H1, derivedJoin]
    exact le_sup_right
  have hH1LK : H1L ≤ K := by
    dsimp [H1L, ambientDerivedJoin]
    exact Subgroup.map_subtype_le H1
  have hcohH1 : coherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) H1) : Set (ClassFunction L ℂ))
      (nonidentitySet L) tau := by
    exact coherent_derivedJoin_layer K tau R hsub M
  by_cases hM_eq : M = H1
  · left
    simpa only [hM_eq] using hcohH1
  have hMltH1 : M < H1 := lt_of_le_of_ne hMH1 hM_eq
  by_cases hlarge : 4 * K.index ^ 2 + 1 < H1.index
  · left
    letI : (((⊤ : Subgroup K).map K.subtype : Subgroup L)).Normal := by
      rw [← MonoidHom.range_eq_map, K.range_subtype]
      infer_instance
    apply bounded_seqIndD_coherence K tau R hsub M H1
      (⊤ : Subgroup K) hMH1 le_top
    · exact nilpotent_topQuotient M hnilKM
    · exact hcohH1
    · simpa only [Subgroup.relIndex_top_right] using hlarge
  have hindexBound : H1.index ≤ 4 * K.index ^ 2 + 1 :=
    Nat.le_of_not_gt hlarge
  have hindexStrict : H1.index < (2 * K.index + 1) ^ 2 := by
    apply lt_of_le_of_lt hindexBound
    have hepos : 0 < K.index :=
      Nat.pos_of_ne_zero K.index_ne_zero_of_finite
    nlinarith
  let q : L →* L ⧸ H1L := QuotientGroup.mk' H1L
  let Kq : Subgroup (L ⧸ H1L) := K.map q
  have hfrob' : IsFrobeniusDecomposition Kq E := by
    simpa only [Kq, q, H1L] using hfrob
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective H1L
  have hKqIndex : Kq.index = K.index := by
    apply K.index_map_eq hqsurj
    simpa only [q, QuotientGroup.ker_mk'] using hH1LK
  have hEcard : Nat.card E = K.index := by
    calc
      Nat.card E = Kq.index := hfrob'.isComplement.symm.index_eq_card.symm
      _ = K.index := hKqIndex
  have hmod (D : Subgroup L) (hDnormal : D.Normal)
      (hH1D : H1L ≤ D) (hDK : D ≤ K) :
      Nat.ModEq K.index 1 (H1L.relIndex D) := by
    letI : D.Normal := hDnormal
    let Dq : Subgroup (L ⧸ H1L) := D.map q
    have hDqnormal : Dq.Normal := by
      dsimp [Dq]
      exact Subgroup.Normal.map hDnormal q hqsurj
    have hDqKq : Dq ≤ Kq := Subgroup.map_mono hDK
    have horbit := frobenius_normal_kernel_card_modEq
      hfrob' hDqnormal hDqKq
    have hcardDq : H1L.relIndex D = Nat.card Dq :=
      relIndex_eq_card_map_quotient
        (inferInstance : H1L.Normal) hH1D
    rw [hEcard, ← hcardDq] at horbit
    exact horbit
  have hH1LltK : H1L < K := by
    refine lt_of_le_of_ne hH1LK ?_
    intro hEq
    have hKH1 : K ≤ H1L := hEq.ge
    apply hfrob'.kernel_ne_bot
    apply (Subgroup.map_eq_bot_iff K).mpr
    simpa only [q, QuotientGroup.ker_mk'] using hKH1
  have hrelH1K : H1L.relIndex K = H1.index := by
    have hmul := H1L.relIndex_mul_index hH1LK
    dsimp [H1L, ambientDerivedJoin] at hmul
    rw [Subgroup.index_map_subtype] at hmul
    exact Nat.mul_right_cancel
      (Nat.pos_of_ne_zero K.index_ne_zero_of_finite) hmul
  have hchief : IsChiefFactor H1L K := by
    apply isChiefFactor_of_maximal_normal
      (inferInstance : K.Normal) hH1LltK
      (inferInstance : H1L.Normal)
    intro D hDnormal hDltK hH1D
    by_contra hDH1
    have hH1ltD : H1L < D :=
      lt_of_le_of_ne hH1D (fun hEq ↦ hDH1 hEq.ge)
    let a := H1L.relIndex D
    let b := D.relIndex K
    have ha1 : 1 < a := by
      change 1 < (H1L.subgroupOf D).index
      apply Subgroup.one_lt_index_of_ne_top
      intro htop
      apply (not_le_of_gt hH1ltD)
      exact Subgroup.subgroupOf_eq_top.mp htop
    have hb1 : 1 < b := by
      change 1 < (D.subgroupOf K).index
      apply Subgroup.one_lt_index_of_ne_top
      intro htop
      apply (not_le_of_gt hDltK)
      exact Subgroup.subgroupOf_eq_top.mp htop
    have hoddK : Odd (Nat.card K) := odd_natCard_subgroup K hoddL
    have hoddD : Odd (Nat.card D) := odd_natCard_subgroup D hoddL
    have haOdd : Odd a := by
      exact hoddD.of_dvd_nat
        (H1L.relIndex_dvd_card (K := D))
    have hbOdd : Odd b := by
      exact hoddK.of_dvd_nat
        (D.relIndex_dvd_card (K := K))
    have hmodA : Nat.ModEq K.index 1 a :=
      hmod D hDnormal hH1D hDltK.le
    have hmodTotal : Nat.ModEq K.index 1 H1.index := by
      simpa only [hrelH1K] using
        hmod K (inferInstance : K.Normal) hH1LK le_rfl
    have hprod : a * b = H1.index := by
      calc
        a * b = H1L.relIndex K :=
          Subgroup.relIndex_mul_relIndex H1L D K hH1D hDltK.le
        _ = H1.index := hrelH1K
    have hmodB : Nat.ModEq K.index 1 b := by
      have hright : Nat.ModEq K.index (a * b) b := by
        simpa only [one_mul] using (hmodA.mul_right b).symm
      rw [hprod] at hright
      exact hmodTotal.trans hright
    have haLower : 2 * K.index + 1 ≤ a :=
      two_mul_add_one_le_of_odd_modEq_one
        (hoddL.of_dvd_nat K.index_dvd_card)
        haOdd hmodA ha1
    have hbLower : 2 * K.index + 1 ≤ b :=
      two_mul_add_one_le_of_odd_modEq_one
        (hoddL.of_dvd_nat K.index_dvd_card)
        hbOdd hmodB hb1
    have hsquare : (2 * K.index + 1) ^ 2 ≤ H1.index := by
      rw [pow_two, ← hprod]
      exact Nat.mul_le_mul haLower hbLower
    exact (not_lt_of_ge hsquare) hindexStrict
  have hnoncomm : ¬ IsMulCommutative (K ⧸ M) := by
    intro hcomm
    letI : IsMulCommutative (K ⧸ M) := hcomm
    have hderM : _root_.commutator K ≤ M :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
        (inferInstance : IsMulCommutative (K ⧸ M))
    apply hM_eq
    apply le_antisymm hMH1
    dsimp [H1, derivedJoin]
    exact sup_le hderM le_rfl
  have hKqSolvable : IsSolvable Kq := by
    exact isSolvable_of_surjective (q.subgroupMap K)
      (q.subgroupMap_surjective K)
  letI : IsSolvable Kq := hKqSolvable
  have hminKq : IsMinimalNormal Kq := by
    simpa only [Kq, q, H1L] using hchief.quotient_minimal_normal
  obtain ⟨p, hp, hKqP⟩ :=
    IsMinimalNormal.exists_prime_isPGroup_of_isSolvable
      (A := L ⧸ H1L) (N := Kq) hminKq
  letI : Fact p.Prime := ⟨hp⟩
  let eKH1 : (K ⧸ H1) ≃* Kq := by
    simpa only [Kq, q, H1L] using
      subgroupQuotientEquivAmbientImage K H1
  have hKH1P : IsPGroup p (K ⧸ H1) :=
    hKqP.of_equiv eKH1.symm
  let qM : K →* K ⧸ M := QuotientGroup.mk' M
  have hmapDerived : H1.map qM = _root_.commutator (K ⧸ M) := by
    dsimp [H1, derivedJoin]
    rw [Subgroup.map_sup, map_commutator_eq,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective M),
      QuotientGroup.map_mk'_self, sup_bot_eq]
    rfl
  let eAb : ((K ⧸ M) ⧸ _root_.commutator (K ⧸ M)) ≃*
      (K ⧸ H1) :=
    (QuotientGroup.quotientMulEquivOfEq hmapDerived.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient M H1 hMH1)
  have hAbP : IsPGroup p
      ((K ⧸ M) ⧸ _root_.commutator (K ⧸ M)) :=
    hKH1P.of_equiv eAb.symm
  have hKMP : IsPGroup p (K ⧸ M) :=
    isPGroup_of_nilpotent_of_abelianization_isPGroup hnilKM hAbP
  have hH1IndexKq : H1.index = Nat.card Kq := by
    calc
      H1.index = Nat.card (K ⧸ H1) := H1.index_eq_card
      _ = Nat.card Kq := Nat.card_congr eKH1.toEquiv
  have hnotDvd : ¬ K.index ∣ p - 1 := by
    intro hdiv
    obtain ⟨n, hn⟩ := hKqP.exists_card_eq
    have hcardOne : 1 < Nat.card Kq :=
      Kq.one_lt_card_iff_ne_bot.mpr hminKq.ne_bot
    have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      simp only [pow_zero] at hn
      omega
    have hpDvd : p ∣ Nat.card Kq := by
      rw [hn]
      exact dvd_pow_self p hn0
    have hpOdd : Odd p :=
      (odd_natCard_subgroup Kq
        (odd_natCard_quotient H1L hoddL)).of_dvd_nat hpDvd
    have hmodP : Nat.ModEq K.index 1 p :=
      (Nat.modEq_iff_dvd' hp.one_le).mpr hdiv
    have hpLower : 2 * K.index + 1 ≤ p :=
      two_mul_add_one_le_of_odd_modEq_one
        (hoddL.of_dvd_nat K.index_dvd_card)
        hpOdd hmodP hp.one_lt
    have hpowlt : p ^ n < p ^ 2 := by
      rw [← hn, ← hH1IndexKq]
      exact hindexStrict.trans_le (pow_le_pow_left' hpLower 2)
    have hn2 : n < 2 :=
      (Nat.pow_lt_pow_iff_right hp.one_lt).mp hpowlt
    have hn1 : n = 1 := by omega
    have hKqCard : Nat.card Kq = p := by
      rw [hn, hn1, pow_one]
    letI : IsCyclic Kq := isCyclic_of_prime_card hKqCard
    letI : IsCyclic (K ⧸ H1) :=
      isCyclic_of_injective eKH1.toMonoidHom eKH1.injective
    letI : IsCyclic
        ((K ⧸ M) ⧸ _root_.commutator (K ⧸ M)) :=
      isCyclic_of_injective eAb.toMonoidHom eAb.injective
    letI : IsCyclic (K ⧸ M) :=
      Submission.OddOrder.BG.Section06.isCyclic_of_isPGroup_of_isCyclic_abelianization
        hKMP
    exact hnoncomm IsCyclic.isMulCommutative
  right
  change IsChiefFactor H1L K ∧
    H1.index ≤ 4 * K.index ^ 2 + 1 ∧
    ∃ p : ℕ, p.Prime ∧ IsPGroup p (K ⧸ M) ∧
      ¬ IsMulCommutative (K ⧸ M) ∧ ¬ K.index ∣ p - 1
  exact ⟨hchief, hindexBound, p, hp, hKMP, hnoncomm, hnotDvd⟩

private theorem exists_constituent_restrict
    {A : Type u} [Group A] [Fintype A]
    (N : Subgroup A) [Fintype N]
    (phi : IrreducibleCharacter A ℂ) :
    ∃ theta : IrreducibleCharacter N ℂ,
      theta.IsConstituent
        (ClassFunction.restrict N (phi : ClassFunction A ℂ)) := by
  let V : FDRep ℂ N :=
    FDRep.of (phi.representation.ρ.comp N.subtype)
  letI : CategoryTheory.Simple phi.representation :=
    phi.representation_simple
  letI : Nontrivial phi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero phi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  letI : Nontrivial V :=
    inferInstanceAs (Nontrivial phi.representation)
  obtain ⟨theta, htheta⟩ :=
    ClassFunction.exists_irreducible_constituent_of_nontrivial V
  refine ⟨theta, ?_⟩
  have hV : ClassFunction.ofRepresentation V.ρ =
      ClassFunction.restrict N (phi : ClassFunction A ℂ) := by
    rw [FDRep.of_ρ', ← ClassFunction.restrict_ofRepresentation,
      phi.ofRepresentation_representation]
  rwa [hV] at htheta

/-- Universe-polymorphic complex specialization of the nonzero-Hom
criterion for irreducible constituents. -/
private theorem existsNonzeroHomOfIsConstituentComplexLocal
    {T : Type u} [Group T] [Fintype T]
    (V : FDRep ℂ T) (chi : IrreducibleCharacter T ℂ)
    (hchi : chi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    ∃ f : chi.representation ⟶ V, f ≠ 0 := by
  letI : Invertible (Fintype.card T : ℂ) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hpair :
      characterPairing (ClassFunction.ofRepresentation V.ρ)
          (chi : ClassFunction T ℂ) =
        (Module.finrank ℂ (chi.representation ⟶ V) : ℂ) := by
    have hhom :=
      FDRep.scalar_product_char_eq_finrank_equivariant
        chi.representation V
    have hcharV (t : T) :
        V.character t = Representation.character V.ρ t := rfl
    simpa only [characterPairing,
      ClassFunction.ofRepresentation_apply,
      IrreducibleCharacter.representation_character,
      invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card,
      hcharV] using hhom
  have hcast :
      (Module.finrank ℂ (chi.representation ⟶ V) : ℂ) ≠ 0 := by
    rw [← hpair]
    exact hchi
  have hfin : Module.finrank ℂ (chi.representation ⟶ V) ≠ 0 := by
    intro hzero
    apply hcast
    simp [hzero]
  exact Module.finrank_pos_iff_exists_ne_zero.mp
    (Nat.pos_of_ne_zero hfin)

/-- Universe-polymorphic complex form of the kernel equivalence for a
constituent of restriction to a normal subgroup. -/
private theorem subKerConstituentRestrictComplex
    {T : Type u} [Group T] [Fintype T]
    (C A : Subgroup T) [C.Normal] [A.Normal] [Fintype C]
    (hAC : A ≤ C)
    (chi : IrreducibleCharacter T ℂ)
    (psi : IrreducibleCharacter C ℂ)
    (hpsi : psi.IsConstituent
      (ClassFunction.restrict C (chi : ClassFunction T ℂ))) :
    A.subgroupOf C ≤ psi.representation.ρ.ker ↔
      A ≤ chi.representation.ρ.ker := by
  let V : FDRep ℂ C :=
    FDRep.of (chi.representation.ρ.comp C.subtype)
  have hVchar : ClassFunction.ofRepresentation V.ρ =
      ClassFunction.restrict C (chi : ClassFunction T ℂ) := by
    rw [FDRep.of_ρ', ← ClassFunction.restrict_ofRepresentation,
      chi.ofRepresentation_representation]
  have hpsiV : psi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ) := by
    rwa [hVchar]
  obtain ⟨f, hf⟩ :=
    existsNonzeroHomOfIsConstituentComplexLocal V psi hpsiV
  letI : CategoryTheory.Simple psi.representation :=
    psi.representation_simple
  letI : CategoryTheory.Mono f :=
    CategoryTheory.mono_of_nonzero_from_simple hf
  let fR :=
    (CategoryTheory.forget₂ (FDRep ℂ C) (Rep ℂ C)).map f
  have hfinj : Function.Injective fR.hom :=
    (Rep.mono_iff_injective fR).mp inferInstance
  let fLinear : psi.representation →ₗ[ℂ] chi.representation :=
    f.hom.hom.hom
  have hfinjLinear : Function.Injective fLinear := hfinj
  constructor
  · intro hApsi
    letI : Nontrivial psi.representation := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      apply CategoryTheory.id_nonzero psi.representation
      apply CategoryTheory.ConcreteCategory.hom_ext
      intro x
      exact Subsingleton.elim _ _
    obtain ⟨v, hv⟩ := exists_ne (0 : psi.representation)
    let w : chi.representation := fLinear v
    have hw : w ≠ 0 := by
      intro hw0
      exact hv ((fLinear.map_eq_zero_iff hfinjLinear).mp hw0)
    let rho := chi.representation.ρ
    let tau : Representation ℂ A chi.representation :=
      rho.comp A.subtype
    have hwfix : w ∈ tau.invariants := by
      rw [Representation.mem_invariants]
      intro a
      let aC : C := ⟨(a : T), hAC a.property⟩
      have hinter :=
        Representation.IntertwiningMap.isIntertwining
          (ρ := ((CategoryTheory.forget₂
            (FDRep ℂ C) (Rep ℂ C)).obj psi.representation).ρ)
          (σ := ((CategoryTheory.forget₂
            (FDRep ℂ C) (Rep ℂ C)).obj V).ρ)
          (f := fR.hom) aC v
      change fLinear (psi.representation.ρ aC v) =
        rho (a : T) (fLinear v) at hinter
      have haKer : aC ∈ psi.representation.ρ.ker :=
        hApsi a.property
      rw [MonoidHom.mem_ker.mp haKer] at hinter
      change rho (a : T) (fLinear v) = fLinear v
      calc
        rho (a : T) (fLinear v) =
            fLinear ((1 : Module.End ℂ psi.representation) v) := hinter.symm
        _ = fLinear v := by rfl
    let fixed : Subrepresentation rho :=
      { toSubmodule := tau.invariants
        apply_mem_toSubmodule := by
          intro g z hz
          rw [Representation.mem_invariants] at hz ⊢
          intro a
          let a' : A :=
            ⟨g⁻¹ * (a : T) * g,
              by
                simpa using (inferInstance : A.Normal).conj_mem
                  (a : T) a.property g⁻¹⟩
          calc
            rho (a : T) (rho g z) =
                (rho (a : T) * rho g) z := rfl
            _ = rho ((a : T) * g) z := by rw [map_mul]
            _ = rho (g * (a' : T)) z := by
              congr 2
              dsimp only [a']
              group
            _ = (rho g * rho (a' : T)) z := by rw [map_mul]
            _ = rho g (rho (a' : T) z) := rfl
            _ = rho g z := by
              have hz' : rho (a' : T) z = z := hz a'
              rw [hz'] }
    letI : CategoryTheory.Simple chi.representation :=
      chi.representation_simple
    letI : Representation.IsIrreducible rho :=
      representation_isIrreducible_of_simple_fdRep chi.representation
    have hfixed_ne : fixed ≠ ⊥ := by
      intro hbot
      have hwbot : w ∈ (⊥ : Submodule ℂ chi.representation) := by
        have hwmem : w ∈ fixed := hwfix
        rw [hbot] at hwmem
        exact hwmem
      exact hw ((Submodule.mem_bot ℂ).mp hwbot)
    have hfixed : fixed = ⊤ :=
      (eq_bot_or_eq_top fixed).resolve_left hfixed_ne
    intro a ha
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro z
    have hz : z ∈ fixed := by rw [hfixed]; trivial
    exact hz ⟨a, ha⟩
  · intro hAchi c hc
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    apply hfinj
    have hinter :=
      Representation.IntertwiningMap.isIntertwining
        (ρ := ((CategoryTheory.forget₂
          (FDRep ℂ C) (Rep ℂ C)).obj psi.representation).ρ)
        (σ := ((CategoryTheory.forget₂
          (FDRep ℂ C) (Rep ℂ C)).obj V).ρ)
        (f := fR.hom) c v
    change fLinear (psi.representation.ρ c v) =
      chi.representation.ρ (c : T) (fLinear v) at hinter
    have hcAct : chi.representation.ρ (c : T) = 1 := by
      apply MonoidHom.mem_ker.mp
      exact hAchi hc
    change fLinear (psi.representation.ρ c v) = fLinear v
    calc
      fLinear (psi.representation.ρ c v) =
          chi.representation.ρ (c : T) (fLinear v) := hinter
      _ = fLinear v := by rw [hcAct]; rfl

private theorem map_subtype_subgroupOf_eq
    {A : Type u} [Group A] (N : Subgroup A) (D : Subgroup N) :
    (D.map N.subtype).subgroupOf N = D := by
  change (D.map N.subtype).comap N.subtype = D
  exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective D

private theorem inverseLinear_involutive
    {A : Type u} [Group A] [Fintype A]
    (phi : ClassFunction A ℂ) :
    ClassFunction.inverseLinear (ClassFunction.inverseLinear phi) = phi := by
  ext x
  simp

private theorem coherent_center_seqIndD_of_pGroup
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) [K.Normal]
    (tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (R : ClassFunction L ℂ → Finset (ClassFunction G ℂ))
    (hsub : subcoherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) : Set (ClassFunction L ℂ))
      tau R)
    (Z : Subgroup K)
    [((Z.map K.subtype : Subgroup L)).Normal]
    (hZcenter : Z ≤ Subgroup.center K)
    (p : ℕ) (hp : p.Prime) (hKp : IsPGroup p K)
    (hp3 : 3 ≤ p) (hcop : K.index.Coprime p)
    (hirr : ∀ phi ∈ seqIndD (k := ℂ) K Z (⊥ : Subgroup K),
      IsIrreducibleCharacter L ℂ phi) :
    coherent
      (↑(seqIndD (k := ℂ) K Z (⊥ : Subgroup K)) : Set (ClassFunction L ℂ))
      (nonidentitySet L) tau := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let X : Finset (ClassFunction L ℂ) :=
    seqIndD (k := ℂ) K Z (⊥ : Subgroup K)
  have hXcal : X ⊆ seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥ := by
    exact seqInd_sub K Z ⊥
  have hexponent (phi : ClassFunction L ℂ) (hphi : phi ∈ X) :
      ∃ d : ℕ, phi 1 = ((K.index * p ^ d : ℕ) : ℂ) := by
    obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hphi
    obtain ⟨n, hn⟩ := hKp.exists_card_eq
    obtain ⟨d, _, hdegree⟩ := (Nat.dvd_prime_pow hp).mp
      (hn ▸ theta.finrank_representation_dvd_natCard)
    refine ⟨d, ?_⟩
    rw [ClassFunction.induce_one,
      IrreducibleCharacter.apply_one_eq_finrank, hdegree, Nat.cast_mul]
  let d : ClassFunction L ℂ → ℕ := fun phi ↦
    if hphi : phi ∈ X then
      Classical.choose (hexponent phi hphi)
    else 0
  have hd (phi : ClassFunction L ℂ) (hphi : phi ∈ X) :
      phi 1 = ((K.index * p ^ d phi : ℕ) : ℂ) := by
    simpa only [d, dif_pos hphi] using
      Classical.choose_spec (hexponent phi hphi)
  have hdInv (phi : ClassFunction L ℂ) (hphi : phi ∈ X) :
      d (ClassFunction.inverseLinear phi) = d phi := by
    have hphiInv : ClassFunction.inverseLinear phi ∈ X := by
      exact seqInd_inverse_mem K Z ⊥ hphi
    have hleft := hd (ClassFunction.inverseLinear phi) hphiInv
    have hright := hd phi hphi
    rw [ClassFunction.inverseLinear_apply, inv_one] at hleft
    have hnat : K.index * p ^ d (ClassFunction.inverseLinear phi) =
        K.index * p ^ d phi := by
      apply Nat.cast_injective (R := ℂ)
      exact hleft.symm.trans hright
    have hpows : p ^ d (ClassFunction.inverseLinear phi) = p ^ d phi := by
      apply Nat.mul_left_cancel
        (Nat.pos_of_ne_zero K.index_ne_zero_of_finite)
      exact hnat
    exact Nat.pow_right_injective hp.two_le hpows
  let sumP : Finset (ClassFunction L ℂ) → ℕ := fun T ↦
    T.sum fun phi ↦ p ^ (d phi * 2)
  have hsumCast (T : Finset (ClassFunction L ℂ)) (hTX : T ⊆ X) :
      (∑ phi ∈ T, phi 1 ^ 2 / characterPairing phi phi) =
        ((K.index ^ 2 * sumP T : ℕ) : ℂ) := by
    calc
      (∑ phi ∈ T, phi 1 ^ 2 / characterPairing phi phi) =
          ∑ phi ∈ T,
            ((K.index ^ 2 * p ^ (d phi * 2) : ℕ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro phi hphi
        have hphiX : phi ∈ X := hTX hphi
        have hpair : characterPairing phi phi = 1 :=
          IrreducibleCharacter.characterPairing_self
            (⟨phi, hirr phi hphiX⟩ : IrreducibleCharacter L ℂ)
        rw [hpair, div_one, hd phi hphiX]
        simp only [Nat.cast_mul, Nat.cast_pow]
        rw [pow_mul]
        ring
      _ = ((∑ phi ∈ T,
          K.index ^ 2 * p ^ (d phi * 2) : ℕ) : ℂ) := by
        simp only [Nat.cast_sum]
      _ = ((K.index ^ 2 * sumP T : ℕ) : ℂ) := by
        simp only [sumP, Finset.mul_sum]
  have hweight (phi : ClassFunction L ℂ) (hphi : phi ∈ X) :
      coherenceDegreeWeight phi =
        ((K.index ^ 2 * p ^ (d phi * 2) : ℕ) : ℝ) := by
    have hpair : characterPairing phi phi = 1 :=
      IrreducibleCharacter.characterPairing_self
        (⟨phi, hirr phi hphi⟩ : IrreducibleCharacter L ℂ)
    rw [coherenceDegreeWeight, hpair, hd phi hphi]
    norm_num
    have hpPowRe : ((p : ℂ) ^ d phi).re = (p : ℝ) ^ d phi := by
      rw [← Complex.ofReal_natCast p, ← Complex.ofReal_pow]
      rfl
    rw [hpPowRe]
    rw [pow_mul]
    ring
  have hdegreeSum (T : Finset (ClassFunction L ℂ)) (hTX : T ⊆ X) :
      coherenceDegreeSum (↑T : Set (ClassFunction L ℂ))
          (hsub.finite.subset (fun _ h ↦ hXcal (hTX h))) =
        ((K.index ^ 2 * sumP T : ℕ) : ℝ) := by
    let hfin : (↑T : Set (ClassFunction L ℂ)).Finite :=
      hsub.finite.subset (fun _ h ↦ hXcal (hTX h))
    have hto : hfin.toFinset = T := by
      ext phi
      simp [hfin]
    rw [coherenceDegreeSum, hto]
    calc
      (∑ phi ∈ T, coherenceDegreeWeight phi) =
          ∑ phi ∈ T,
            ((K.index ^ 2 * p ^ (d phi * 2) : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro phi hphi
        exact hweight phi (hTX hphi)
      _ = ((∑ phi ∈ T,
          K.index ^ 2 * p ^ (d phi * 2) : ℕ) : ℝ) := by
        simp only [Nat.cast_sum]
      _ = ((K.index ^ 2 * sumP T : ℕ) : ℝ) := by
        simp only [sumP, Finset.mul_sum]
  have hNatSum :
      K.index ^ 2 * sumP X =
        K.index * (Z.index * (Nat.card Z - 1)) := by
    letI : (((⊥ : Subgroup K).map K.subtype : Subgroup L)).Normal := by
      rw [Subgroup.map_bot]
      infer_instance
    apply Nat.cast_injective (R := ℂ)
    calc
      ((K.index ^ 2 * sumP X : ℕ) : ℂ) =
          ∑ phi ∈ X, phi 1 ^ 2 / characterPairing phi phi :=
        (hsumCast X (fun _ h ↦ h)).symm
      _ = (K.index : ℂ) *
          ((Z.index : ℂ) *
            ((((⊥ : Subgroup K).relIndex Z : ℕ) : ℂ) - 1)) :=
        sum_seqIndD_square (k := ℂ) K Z ⊥ bot_le
      _ = ((K.index * (Z.index * (Nat.card Z - 1)) : ℕ) : ℂ) := by
        rw [Subgroup.relIndex_bot_left]
        simp only [Nat.cast_mul,
          Nat.cast_sub (Nat.card_pos (α := Z)), Nat.cast_one]
  let P : ℕ → Prop := fun n ↦
    ∀ Y : Finset (ClassFunction L ℂ), Y.card = n →
      Y ⊆ X →
      cfConjC_closed (↑Y : Set (ClassFunction L ℂ)) →
      (∀ y ∈ Y, ∀ x ∈ X, x ∉ Y → d y ≤ d x) →
      coherent (↑Y : Set (ClassFunction L ℂ))
        (nonidentitySet L) tau
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Y hYcard hYX hYclosed hYorder
        have hYcal : (↑Y : Set (ClassFunction L ℂ)) ⊆
            ↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) := by
          intro phi hphi
          exact hXcal (hYX hphi)
        by_cases huniform :
            ∀ phi ∈ Y, ∀ psi ∈ Y, d phi = d psi
        · apply uniform_degree_coherence
            (subset_subcoherent hsub ⟨hYcal, hYclosed⟩)
          intro phi hphi psi hpsi
          rw [hd phi (hYX hphi), hd psi (hYX hpsi),
            huniform phi hphi psi hpsi]
        · push_neg at huniform
          obtain ⟨phi₀, hphi₀Y, psi₀, hpsi₀Y, hne₀⟩ := huniform
          have hYnon : Y.Nonempty := ⟨phi₀, hphi₀Y⟩
          have hImageNon : (Y.image d).Nonempty := hYnon.image d
          let m : ℕ := (Y.image d).max' hImageNon
          have hmMem : m ∈ Y.image d :=
            Finset.max'_mem (Y.image d) hImageNon
          obtain ⟨chi, hchiY, hchiMax⟩ := Finset.mem_image.mp hmMem
          have hmax (phi : ClassFunction L ℂ) (hphi : phi ∈ Y) :
              d phi ≤ d chi := by
            rw [hchiMax]
            exact Finset.le_max' (Y.image d) (d phi)
              (Finset.mem_image.mpr ⟨phi, hphi, rfl⟩)
          have hexistsLower : ∃ xi ∈ Y, d xi ≠ d chi := by
            by_contra hnone
            push_neg at hnone
            apply hne₀
            rw [hnone phi₀ hphi₀Y, hnone psi₀ hpsi₀Y]
          obtain ⟨xi1, hxi1Y, hxi1ne⟩ := hexistsLower
          have hxi1lt : d xi1 < d chi :=
            lt_of_le_of_ne (hmax xi1 hxi1Y) hxi1ne
          let chiStar : ClassFunction L ℂ :=
            ClassFunction.inverseLinear chi
          have hchiX : chi ∈ X := hYX hchiY
          have hchiStarY : chiStar ∈ Y := hYclosed chi hchiY
          have hdStar : d chiStar = d chi := hdInv chi hchiX
          let Y' : Finset (ClassFunction L ℂ) :=
            (Y.erase chi).erase chiStar
          have hY'Y : Y' ⊆ Y := by
            intro phi hphi
            exact (Finset.mem_erase.mp
              (Finset.mem_erase.mp hphi).2).2
          have hY'X : Y' ⊆ X := hY'Y.trans hYX
          have hchiNot : chi ∉ Y' := by
            simp [Y']
          have hchiStarNot : chiStar ∉ Y' := by
            simp [Y']
          have hxi1neChi : xi1 ≠ chi := by
            intro heq
            subst xi1
            exact (lt_irrefl _ hxi1lt)
          have hxi1neStar : xi1 ≠ chiStar := by
            intro heq
            rw [heq, hdStar] at hxi1lt
            exact (lt_irrefl _ hxi1lt)
          have hxi1Y' : xi1 ∈ Y' := by
            simp only [Y', Finset.mem_erase]
            exact ⟨hxi1neStar, hxi1neChi, hxi1Y⟩
          have hY'closed :
              cfConjC_closed (↑Y' : Set (ClassFunction L ℂ)) := by
            intro phi hphi
            have hphiStarY : ClassFunction.inverseLinear phi ∈ Y :=
              hYclosed phi (hY'Y hphi)
            have hphiStarNeChi :
                ClassFunction.inverseLinear phi ≠ chi := by
              intro heq
              have heq' := congrArg ClassFunction.inverseLinear heq
              rw [inverseLinear_involutive,
                show ClassFunction.inverseLinear chi = chiStar from rfl] at heq'
              exact (Finset.mem_erase.mp hphi).1 heq'
            have hphiStarNeStar :
                ClassFunction.inverseLinear phi ≠ chiStar := by
              intro heq
              have heq' := congrArg ClassFunction.inverseLinear heq
              rw [inverseLinear_involutive,
                show ClassFunction.inverseLinear chiStar = chi from
                  inverseLinear_involutive chi] at heq'
              exact (Finset.mem_erase.mp
                (Finset.mem_erase.mp hphi).2).1 heq'
            change ClassFunction.inverseLinear phi ∈
              (Y.erase chi).erase chiStar
            exact Finset.mem_erase.mpr
              ⟨hphiStarNeStar,
                Finset.mem_erase.mpr
                  ⟨hphiStarNeChi, hphiStarY⟩⟩
          have hY'ssub : Y' ⊂ Y := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨hY'Y, ?_⟩
            intro heq
            have : chi ∈ Y' := by
              rw [heq]
              exact hchiY
            exact hchiNot this
          have hY'card : Y'.card < n := by
            rw [← hYcard]
            exact Finset.card_lt_card hY'ssub
          have hY'order :
              ∀ y ∈ Y', ∀ x ∈ X, x ∉ Y' → d y ≤ d x := by
            intro y hy x hxX hxnot
            have hyY : y ∈ Y := hY'Y hy
            by_cases hxY : x ∈ Y
            · by_cases hxchi : x = chi
              · subst x
                exact hmax y hyY
              by_cases hxstar : x = chiStar
              · subst x
                rw [hdStar]
                exact hmax y hyY
              exact (hxnot (by
                simp only [Y', Finset.mem_erase]
                exact ⟨hxstar, hxchi, hxY⟩)).elim
            · exact hYorder y hyY x hxX hxY
          have hcohY' : coherent
              (↑Y' : Set (ClassFunction L ℂ))
              (nonidentitySet L) tau := by
            exact ih Y'.card hY'card Y' rfl hY'X hY'closed hY'order
          have hdivDegree : ∃ a : ℕ,
              chi 1 = (a : ℂ) * xi1 1 := by
            refine ⟨p ^ (d chi - d xi1), ?_⟩
            rw [hd chi hchiX, hd xi1 (hYX hxi1Y)]
            exact_mod_cast (show
              K.index * p ^ d chi =
                p ^ (d chi - d xi1) *
                  (K.index * p ^ d xi1) by
              calc
                K.index * p ^ d chi =
                    K.index *
                      (p ^ (d chi - d xi1) * p ^ d xi1) := by
                  rw [← pow_add, Nat.sub_add_cancel hxi1lt.le]
                _ = p ^ (d chi - d xi1) *
                    (K.index * p ^ d xi1) := by ring)
          obtain ⟨theta, htheta, hchiInd⟩ := seqIndP.mp hchiX
          have hthetaDegree :
              Module.finrank ℂ theta.representation = p ^ d chi := by
            apply Nat.mul_left_cancel
              (Nat.pos_of_ne_zero K.index_ne_zero_of_finite)
            apply Nat.cast_injective (R := ℂ)
            simp only [Nat.cast_mul]
            rw [← IrreducibleCharacter.apply_one_eq_finrank,
              ← ClassFunction.induce_one, ← hchiInd, hd chi hchiX,
              Nat.cast_mul]
          let V := theta.representation
          let rho : Representation ℂ K V := V.ρ
          letI : CategoryTheory.Simple V := theta.representation_simple
          letI : Representation.IsIrreducible rho :=
            representation_isIrreducible_of_simple_fdRep V
          have hscalar : ∀ z : Z, ∃ c : ℂ,
              rho (z : K) = c • (1 : Module.End ℂ V) := by
            intro z
            let zc : Subgroup.center K :=
              ⟨(z : K), hZcenter z.property⟩
            refine ⟨(schurCenterScalarCharacter rho zc : ℂ), ?_⟩
            ext v
            exact schurCenterScalarCharacter_smul rho zc v
          have hsq : Module.finrank ℂ V ^ 2 ≤ Z.index :=
            Representation.IsIrreducible.finrank_sq_le_index_of_scalar_subgroup
              rho Z hscalar
          have hpWeightLe : p ^ (d chi * 2) ≤ Z.index := by
            rw [pow_mul]
            simpa only [V, hthetaDegree] using hsq
          obtain ⟨zexp, hZindex⟩ := hKp.index Z
          have hpowExp : d chi * 2 ≤ zexp := by
            apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
            rw [← hZindex]
            exact hpWeightLe
          have hZdiv : p ^ (d chi * 2) ∣ Z.index := by
            rw [hZindex]
            exact pow_dvd_pow p hpowExp
          have hProd : p ^ (d chi * 2) ∣
              K.index ^ 2 * sumP X := by
            rw [hNatSum]
            exact dvd_mul_of_dvd_right
              (dvd_mul_of_dvd_left hZdiv (Nat.card Z - 1)) K.index
          have hTotal : p ^ (d chi * 2) ∣ sumP X := by
            have hcopPow :
                (p ^ (d chi * 2)).Coprime (K.index ^ 2) :=
              Nat.Coprime.pow (d chi * 2) 2 hcop.symm
            exact hcopPow.dvd_of_dvd_mul_left hProd
          have hchiLeOutside (x : ClassFunction L ℂ)
              (hxX : x ∈ X) (hxnot : x ∉ Y') : d chi ≤ d x := by
            by_cases hxY : x ∈ Y
            · by_cases hxchi : x = chi
              · subst x
                exact le_rfl
              by_cases hxstar : x = chiStar
              · subst x
                exact hdStar.ge
              exact (hxnot (by
                simp only [Y', Finset.mem_erase]
                exact ⟨hxstar, hxchi, hxY⟩)).elim
            · exact hYorder chi hchiY x hxX hxY
          have hOutside : p ^ (d chi * 2) ∣
              ∑ x ∈ X \ Y', p ^ (d x * 2) := by
            apply Finset.dvd_sum
            intro x hx
            have hx' := Finset.mem_sdiff.mp hx
            exact pow_dvd_pow p (Nat.mul_le_mul_right 2
              (hchiLeOutside x hx'.1 hx'.2))
          have hY'div : p ^ (d chi * 2) ∣ sumP Y' := by
            dsimp [sumP] at hTotal ⊢
            apply (Nat.dvd_add_iff_right hOutside).mpr
            rw [Finset.sum_sdiff hY'X]
            exact hTotal
          have hsumPos : 0 < sumP Y' := by
            dsimp [sumP]
            exact Finset.sum_pos'
              (fun _ _ ↦ Nat.zero_le _)
              ⟨xi1, hxi1Y', pow_pos hp.pos _⟩
          have hweightLeSum : p ^ (d chi * 2) ≤ sumP Y' :=
            Nat.le_of_dvd hsumPos hY'div
          have hpowStrict : 2 * p ^ d xi1 < p ^ d chi := by
            calc
              2 * p ^ d xi1 < p ^ (d xi1 + 1) := by
                rw [pow_succ]
                simpa only [Nat.mul_comm] using
                  Nat.mul_lt_mul_of_pos_right
                    (show 2 < p by omega) (pow_pos hp.pos (d xi1))
              _ ≤ p ^ d chi :=
                Nat.pow_le_pow_right hp.pos (by omega)
          have hstrictNat :
              2 * (K.index * p ^ d chi) *
                  (K.index * p ^ d xi1) <
                K.index ^ 2 * p ^ (d chi * 2) := by
            calc
              2 * (K.index * p ^ d chi) *
                    (K.index * p ^ d xi1) =
                  (K.index ^ 2 * p ^ d chi) *
                    (2 * p ^ d xi1) := by ring
              _ < (K.index ^ 2 * p ^ d chi) * p ^ d chi :=
                Nat.mul_lt_mul_of_pos_left hpowStrict
                  (Nat.mul_pos
                    (pow_pos
                      (Nat.pos_of_ne_zero
                        K.index_ne_zero_of_finite) 2)
                    (pow_pos hp.pos _))
              _ = K.index ^ 2 * p ^ (d chi * 2) := by
                rw [pow_mul]
                ring
          have hstrictReal :
              2 * (chi 1).re * (xi1 1).re <
                ((K.index ^ 2 * p ^ (d chi * 2) : ℕ) : ℝ) := by
            rw [hd chi hchiX, hd xi1 (hYX hxi1Y)]
            norm_num
            exact_mod_cast hstrictNat
          have hY'degree :
              coherenceDegreeSum
                  (↑Y' : Set (ClassFunction L ℂ))
                  (hsub.finite.subset
                    (fun _ h ↦ hXcal (hY'X h))) =
                ((K.index ^ 2 * sumP Y' : ℕ) : ℝ) :=
            hdegreeSum Y' hY'X
          have hextBound :
              2 * (chi 1).re * (xi1 1).re <
                coherenceDegreeSum
                  (↑Y' : Set (ClassFunction L ℂ))
                  (hsub.finite.subset
                    (fun _ h ↦ hXcal (hY'X h))) := by
            rw [hY'degree]
            exact hstrictReal.trans_le (by
              exact_mod_cast
                (Nat.mul_le_mul_left (K.index ^ 2) hweightLeSum))
          have hY'cf : cfConjC_subset
              (↑Y' : Set (ClassFunction L ℂ))
              (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) :
                Set (ClassFunction L ℂ)) :=
            ⟨fun _ h ↦ hXcal (hY'X h), hY'closed⟩
          have hcohUnion : coherent
              ({chi, ClassFunction.inverseLinear chi} ∪
                (↑Y' : Set (ClassFunction L ℂ)))
              (nonidentitySet L) tau := by
            exact extend_coherent hsub hY'cf hxi1Y' (hXcal hchiX) hchiNot
              hcohY' hdivDegree hextBound
          have hUnion :
              {chi, ClassFunction.inverseLinear chi} ∪
                  (↑Y' : Set (ClassFunction L ℂ)) =
                (↑Y : Set (ClassFunction L ℂ)) := by
            ext phi
            simp only [Set.mem_union, Set.mem_insert_iff,
              Set.mem_singleton_iff, Finset.mem_coe, Y',
              Finset.mem_erase, chiStar]
            constructor
            · rintro ((rfl | rfl) | ⟨_, _, hphi⟩)
              · exact hchiY
              · exact hchiStarY
              · exact hphi
            · intro hphi
              by_cases hchi : phi = chi
              · exact Or.inl (Or.inl hchi)
              by_cases hstar : phi = ClassFunction.inverseLinear chi
              · exact Or.inl (Or.inr hstar)
              · exact Or.inr ⟨hstar, hchi, hphi⟩
          rw [hUnion] at hcohUnion
          exact hcohUnion
  apply hP X.card X rfl (fun _ h ↦ h)
  · intro phi hphi
    exact seqInd_inverse_mem K Z ⊥ hphi
  · intro _ _ x hxX hxnot
    exact (hxnot hxX).elim

set_option maxHeartbeats 1000000 in
/-- Peterfalvi (6.6).  If the indicated induced layer consists of ambient
irreducibles, it is precisely the family of irreducibles nontrivial on the
central subgroup `Z`, and that family is coherent. -/
theorem seqIndD_irr_coherence
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) [K.Normal] [IsSolvable K]
    (tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (R : ClassFunction L ℂ → Finset (ClassFunction G ℂ))
    (hsub : subcoherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) : Set (ClassFunction L ℂ))
      tau R)
    (hfq : odd_Frobenius_quotient K (⊥ : Subgroup K))
    (Z : Subgroup K)
    [((Z.map K.subtype : Subgroup L)).Normal]
    (hZne : Z ≠ ⊥) (hZcenter : Z ≤ Subgroup.center K)
    (hirr : ∀ phi ∈ seqIndD (k := ℂ) K Z (⊥ : Subgroup K),
      IsIrreducibleCharacter L ℂ phi) :
    ((↑(seqIndD (k := ℂ) K Z (⊥ : Subgroup K)) : Set (ClassFunction L ℂ)) =
        {phi | ∃ chi : IrreducibleCharacter L ℂ,
          phi = (chi : ClassFunction L ℂ) ∧
            ¬ Z.map K.subtype ≤ ClassFunction.translationKernel phi}) ∧
      coherent
        (↑(seqIndD (k := ℂ) K Z (⊥ : Subgroup K)) :
          Set (ClassFunction L ℂ))
        (nonidentitySet L) tau := by
  classical
  let Za : Subgroup L := Z.map K.subtype
  letI : Za.Normal :=
    (inferInstance : (Z.map K.subtype : Subgroup L).Normal)
  have hZaK : Za ≤ K := by
    dsimp [Za]
    exact Subgroup.map_subtype_le Z
  have hZaSubgroup : Za.subgroupOf K = Z := by
    dsimp [Za]
    exact map_subtype_subgroupOf_eq K Z
  have hset :
      (↑(seqIndD (k := ℂ) K Z (⊥ : Subgroup K)) :
          Set (ClassFunction L ℂ)) =
        {phi | ∃ chi : IrreducibleCharacter L ℂ,
          phi = (chi : ClassFunction L ℂ) ∧
            ¬ Z.map K.subtype ≤
              ClassFunction.translationKernel phi} := by
    ext phi
    constructor
    · intro hphi
      let chi : IrreducibleCharacter L ℂ := ⟨phi, hirr phi hphi⟩
      refine ⟨chi, rfl, ?_⟩
      obtain ⟨theta, htheta, hphiInd⟩ := seqIndP.mp hphi
      have hconst : chi.IsConstituent
          (ClassFunction.induce K
            (theta : ClassFunction K ℂ)) := by
        unfold IrreducibleCharacter.IsConstituent
        change characterPairing
          (ClassFunction.induce K (theta : ClassFunction K ℂ))
          phi ≠ 0
        rw [← hphiInd]
        rw [show characterPairing phi phi = 1 from
          IrreducibleCharacter.characterPairing_self chi]
        exact one_ne_zero
      intro hZaChi
      have hZaChiRep : Za ≤ chi.representation.ρ.ker := by
        have hZaChi' : Za ≤ ClassFunction.translationKernel
            (chi : ClassFunction L ℂ) := by
          simpa only [Za, chi] using hZaChi
        rw [translationKernelIrreducibleCharacterComplex chi] at hZaChi'
        exact hZaChi'
      have hthetaRes : theta.IsConstituent
          (ClassFunction.restrict K (chi : ClassFunction L ℂ)) :=
        (theta.isConstituent_restrict_iff_induce K chi).mpr hconst
      have hZaThetaRep :
          Za.subgroupOf K ≤ theta.representation.ρ.ker :=
        (subKerConstituentRestrictComplex
          K Za hZaK chi theta hthetaRes).mpr hZaChiRep
      have hZTheta : Z ≤ ClassFunction.translationKernel
          (theta : ClassFunction K ℂ) := by
        rw [translationKernelIrreducibleCharacterComplex theta,
          ← hZaSubgroup]
        exact hZaThetaRep
      exact (mem_Iirr_kerD.mp htheta).2 hZTheta
    · rintro ⟨chi, rfl, hZaChi⟩
      obtain ⟨theta, hthetaRes⟩ := exists_constituent_restrict K chi
      have hconstInd : chi.IsConstituent
          (ClassFunction.induce K
            (theta : ClassFunction K ℂ)) :=
        (theta.isConstituent_restrict_iff_induce K chi).mp hthetaRes
      have hZTheta : ¬ Z ≤ ClassFunction.translationKernel
          (theta : ClassFunction K ℂ) := by
        intro hZTheta
        apply hZaChi
        rw [translationKernelIrreducibleCharacterComplex chi]
        apply (subKerConstituentRestrictComplex
          K Za hZaK chi theta hthetaRes).mp
        rw [hZaSubgroup,
          ← translationKernelIrreducibleCharacterComplex theta]
        exact hZTheta
      have htheta : theta ∈ Iirr_kerD (k := ℂ) Z ⊥ := by
        exact mem_Iirr_kerD.mpr ⟨bot_le, hZTheta⟩
      have hInd : ClassFunction.induce K
          (theta : ClassFunction K ℂ) ∈
          seqIndD (k := ℂ) K Z (⊥ : Subgroup K) := by
        exact seqIndP.mpr ⟨theta, htheta, rfl⟩
      let psi : IrreducibleCharacter L ℂ :=
        ⟨ClassFunction.induce K (theta : ClassFunction K ℂ),
          hirr _ hInd⟩
      have hpsi : psi = chi := by
        by_contra hne
        apply hconstInd
        change characterPairing (psi : ClassFunction L ℂ)
          (chi : ClassFunction L ℂ) = 0
        rw [IrreducibleCharacter.characterPairing_eq_ite, if_neg hne]
      have hval := congrArg Subtype.val hpsi
      rw [← hval]
      exact hInd
  refine ⟨hset, ?_⟩
  rcases non_coherent_chief K tau R hsub ⊥ hfq with hcoh | hexception
  · exact subset_coherent (seqInd_sub K Z ⊥) hcoh
  · rcases hexception with
      ⟨_, _, p, hp, hKbotP, _, _⟩
    letI : Fact p.Prime := ⟨hp⟩
    have hKp : IsPGroup p K :=
      hKbotP.of_equiv QuotientGroup.quotientBot
    have hKcardNe : Nat.card K ≠ 1 := by
      intro hKcard
      have hZleK : Nat.card Z ≤ Nat.card K :=
        Nat.le_of_dvd Nat.card_pos Z.card_subgroup_dvd_card
      have hZcard : 1 < Nat.card Z :=
        Z.one_lt_card_iff_ne_bot.mpr hZne
      omega
    have hpK : p ∣ Nat.card K :=
      hKp.card_eq_or_dvd.resolve_left hKcardNe
    have hfqData := hfq
    let H1 : Subgroup K := derivedJoin K (⊥ : Subgroup K)
    let H1L : Subgroup L := ambientDerivedJoin K (⊥ : Subgroup K)
    letI : H1.Normal := derivedJoin_normal K ⊥
    letI : H1L.Normal := ambientDerivedJoin_normal K ⊥
    rcases hfqData with ⟨hoddL, _, E, hfrob⟩
    have hpOdd : Odd p :=
      (odd_natCard_subgroup K hoddL).of_dvd_nat hpK
    have hp3 : 3 ≤ p := hp.odd_iff.mp hpOdd
    let q : L →* L ⧸ H1L := QuotientGroup.mk' H1L
    let Kq : Subgroup (L ⧸ H1L) := K.map q
    have hfrob' : IsFrobeniusDecomposition Kq E := by
      simpa only [Kq, q, H1L] using hfrob
    have hH1LK : H1L ≤ K := by
      dsimp [H1L, ambientDerivedJoin]
      exact Subgroup.map_subtype_le H1
    have hqsurj : Function.Surjective q :=
      QuotientGroup.mk'_surjective H1L
    have hKqIndex : Kq.index = K.index := by
      apply K.index_map_eq hqsurj
      simpa only [q, QuotientGroup.ker_mk'] using hH1LK
    have hEcard : Nat.card E = K.index := by
      calc
        Nat.card E = Kq.index :=
          hfrob'.isComplement.symm.index_eq_card.symm
        _ = K.index := hKqIndex
    let eKH1 : (K ⧸ H1) ≃* Kq := by
      simpa only [Kq, q, H1L] using
        subgroupQuotientEquivAmbientImage K H1
    have hKqP : IsPGroup p Kq :=
      (hKp.to_quotient H1).of_equiv eKH1
    letI : Nontrivial Kq :=
      Kq.nontrivial_iff_ne_bot.mpr hfrob'.kernel_ne_bot
    have hpKq : p ∣ Nat.card Kq :=
      hKqP.card_eq_or_dvd.resolve_left
        (Finite.one_lt_card (α := Kq)).ne'
    have hEcopP : (Nat.card E).Coprime p :=
      (hfrob'.natCard_coprime.coprime_dvd_left hpKq).symm
    have hcop : K.index.Coprime p := by
      simpa only [hEcard] using hEcopP
    exact coherent_center_seqIndD_of_pGroup K tau R hsub Z
      hZcenter p hp hKp hp3 hcop hirr

end

end Submission.OddOrder.PF
