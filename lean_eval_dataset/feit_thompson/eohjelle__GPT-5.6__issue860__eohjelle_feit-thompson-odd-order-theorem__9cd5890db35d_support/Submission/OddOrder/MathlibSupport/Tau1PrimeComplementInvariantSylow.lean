import Submission.OddOrder.BG.Section10.BetaHallStructure
import Submission.OddOrder.BG.Section12.TauDefinitions
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowConjugacy
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall
import Submission.OddOrder.MathlibSupport.NormalPrimeComplementContainment
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient

/-!
# The tau-one prime complement and the invariant Sylow transfer

This file isolates the corrected form of the argument in
`BGsection13.v`, lines 711--743.  Membership in `tau1Primes M` supplies
the indispensable hypothesis `p ∤ |M'|`.  It implies that the ambient
`p'`-core is a normal Hall `p'`-subgroup; for a maximal subgroup, the
beta core lies in its ambient image.

The final theorem packages the subsequent coprime-action argument.  A
Hall witness is represented only by the three facts used by the proof:
it lies in `M`, it centralizes `P`, and its order is divisible by the
selected beta prime.  An invariant Sylow subgroup of
`O_{p'}(M) ∩ N_M(Q)` is promoted through the beta factorization, and
invariant Sylow extension and conjugacy move a rank-one subgroup of
`C_M(P)` into `N(Q)` without leaving `C_M(P)`.
-/

namespace Submission.OddOrder.MathlibSupport

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open scoped IsMulCommutative

noncomputable section

universe u

/-- If `p` does not divide the derived subgroup, then the `p'`-core is a
normal Hall `p'`-subgroup.

Indeed, the derived subgroup lies in the `p'`-core.  The quotient by that
core is therefore abelian, while its own `p'`-core is trivial.  The
nilpotent prime-core Hall theorem then forces the quotient to be a
`p`-group. -/
theorem pPrimeCore_isPrimeComplement_of_not_dvd_commutator
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hcomm : ¬ p ∣ Nat.card (_root_.commutator G)) :
    IsPrimeComplement p (pPrimeCore p G) := by
  classical
  let K : Subgroup G := pPrimeCore p G
  letI : K.Normal := by
    dsimp [K]
    infer_instance
  have hcommPrime : IsPPrimeSubgroup p (_root_.commutator G) := by
    rw [IsPPrimeSubgroup]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hcomm
  have hcommK : _root_.commutator G ≤ K := by
    dsimp [K]
    exact le_pPrimeCore hcommPrime (by infer_instance)
  letI : IsMulCommutative (G ⧸ K) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommK
  letI : Group.IsNilpotent (G ⧸ K) := by infer_instance
  have hHallQuotient :
      IsPrimeComplement p (pPrimeCore p (G ⧸ K)) :=
    pPrimeCore_isPrimeComplement_of_isNilpotent
  have hcoreQuotient : pPrimeCore p (G ⧸ K) = ⊥ := by
    simpa only [K] using
      (pPrimeCore_quotient_self_eq_bot (G := G) (p := p))
  obtain ⟨n, hindex⟩ := hHallQuotient.exists_index_eq_pow
  rw [hcoreQuotient, Subgroup.index_bot] at hindex
  change IsPrimeComplement p K
  exact ⟨(pPrimeCore_coprime_card (G := G) (p := p)).symm,
    ⟨n, K.index_eq_card.trans hindex⟩⟩

/-- The normal Hall `p'`-subgroup attached to a tau-one prime. -/
theorem tau1_pPrimeCore_isPrimeComplement
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau1Primes M) :
    IsPrimeComplement p (pPrimeCore p M) :=
  pPrimeCore_isPrimeComplement_of_not_dvd_commutator hp.2.2.2.2

/-- For a maximal subgroup, the beta core lies in the ambient image of
the tau-one `p'`-core. -/
theorem betaCore_le_map_pPrimeCore_of_tau1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hp : p ∈ tau1Primes M) :
    betaCore M ≤ (pPrimeCore p M).map M.subtype := by
  have hcommPrime : IsPPrimeSubgroup p (_root_.commutator M) := by
    rw [IsPPrimeSubgroup]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp.2.2.2.2
  have hcommCore :
      _root_.commutator M ≤ pPrimeCore p M :=
    le_pPrimeCore hcommPrime (by infer_instance)
  exact (Mbeta_der1 hM).trans (Subgroup.map_mono hcommCore)

/-- The beta-normalizer factorization restricts to the normal Hall
`p'`-subgroup attached to a tau-one prime.  This is the subgroup-lattice
form of the modular-law calculation in `BGsection13.v`, lines 730--734. -/
theorem betaCore_sup_inf_map_pPrimeCore_eq_of_tau1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M Q : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hp : p ∈ tau1Primes M)
    (hfactor :
      betaCore M ⊔ (M ⊓ Subgroup.normalizer (Q : Set G)) = M) :
    betaCore M ⊔
        ((pPrimeCore p M).map M.subtype ⊓
          (M ⊓ Subgroup.normalizer (Q : Set G))) =
      (pPrimeCore p M).map M.subtype := by
  let K : Subgroup G := (pPrimeCore p M).map M.subtype
  let I : Subgroup G := M ⊓ Subgroup.normalizer (Q : Set G)
  have hKM : K ≤ M := by
    dsimp [K]
    exact Subgroup.map_subtype_le _
  have hBK : betaCore M ≤ K := by
    dsimp [K]
    exact betaCore_le_map_pPrimeCore_of_tau1 hM hp
  change betaCore M ⊔ (K ⊓ I) = K
  apply le_antisymm
  · exact sup_le hBK inf_le_left
  · intro x hxK
    have hxM : x ∈ M := hKM hxK
    let BM : Subgroup M := (betaCore M).subgroupOf M
    let IM : Subgroup M := I.subgroupOf M
    have hBMnormal : BM.Normal := by
      simpa [BM] using betaCore_normal M
    letI : BM.Normal := hBMnormal
    have hxSup : x ∈ betaCore M ⊔ I := by
      rw [hfactor]
      exact hxM
    have hxSupM : (⟨x, hxM⟩ : M) ∈ BM ⊔ IM := by
      change (⟨x, hxM⟩ : M) ∈
        (betaCore M).subgroupOf M ⊔ I.subgroupOf M
      rw [← Subgroup.subgroupOf_sup (betaCore_le M) inf_le_left]
      exact hxSup
    rw [Subgroup.mem_sup_of_normal_left] at hxSupM
    obtain ⟨b, hb, i, hi, hbi⟩ := hxSupM
    have hbG : (b : G) ∈ betaCore M := hb
    have hiG : (i : G) ∈ I := hi
    have hbiG : (b : G) * (i : G) = x :=
      congrArg (fun y : M ↦ (y : G)) hbi
    have hiK : (i : G) ∈ K := by
      have hiEq : (i : G) = (b : G)⁻¹ * x := by
        rw [← hbiG]
        simp
      rw [hiEq]
      exact K.mul_mem (K.inv_mem (hBK hbG)) hxK
    rw [← hbiG]
    exact Subgroup.mul_mem_sup hbG ⟨hiK, hiG⟩

/-- Cauchy's theorem in the rank-one subgroup language used below. -/
private theorem exists_rankOne_le_of_prime_dvd_natCard_tau1
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hpK : p ∣ Nat.card K) :
    ∃ P : Subgroup G, P ≤ K ∧ IsElementaryAbelianOfRank p 1 P := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
  let P : Subgroup G := (Subgroup.zpowers x).map K.subtype
  have hcardZ : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hx]
  have hcardP : Nat.card P = p := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcardZ]
  exact ⟨P, Subgroup.map_subtype_le _,
    isElementaryAbelianOfRank_one_of_card_eq_prime hcardP⟩

/-- If a normal subgroup and `I` generate a finite group, then the index
of `I` divides the order of the normal factor. -/
private theorem index_dvd_card_of_sup_eq_top_normal_left_tau1
    {K : Type u} [Group K] [Finite K]
    {N I : Subgroup K} (hN : N.Normal) (hsup : N ⊔ I = ⊤) :
    I.index ∣ Nat.card N := by
  letI : N.Normal := hN
  let J : Subgroup I := (N ⊓ I).subgroupOf I
  have hNindex : N.index = J.index := by
    calc
      N.index = N.relIndex (⊤ : Subgroup K) := N.relIndex_top_right.symm
      _ = N.relIndex (I ⊔ N) := by rw [sup_comm, hsup]
      _ = N.relIndex I := Subgroup.relIndex_sup_right I N
      _ = (N ⊓ I).relIndex I :=
        (Subgroup.inf_relIndex_right N I).symm
      _ = J.index := by rfl
  have hNcard : Nat.card N * J.index = Nat.card K := by
    rw [← hNindex]
    exact N.card_mul_index
  have hIcard : Nat.card I * I.index = Nat.card K :=
    I.card_mul_index
  have hJcard : Nat.card J * J.index = Nat.card I :=
    J.card_mul_index
  have hcancel :
      Nat.card N * J.index =
        (Nat.card J * I.index) * J.index := by
    calc
      Nat.card N * J.index = Nat.card K := hNcard
      _ = Nat.card I * I.index := hIcard.symm
      _ = (Nat.card J * J.index) * I.index := by rw [hJcard]
      _ = (Nat.card J * I.index) * J.index := by ac_rfl
  have hcard : Nat.card N = Nat.card J * I.index :=
    Nat.mul_right_cancel
      (Nat.pos_of_ne_zero J.index_ne_zero_of_finite) hcancel
  exact ⟨Nat.card J, by simpa [mul_comm] using hcard⟩

/-- A Sylow subgroup of the second factor in a normal product is still
Sylow in the whole group at every prime absent from the normal factor. -/
private theorem isSylowSubgroupOf_map_of_normal_sup_tau1
    {G : Type u} [Group G] [Finite G]
    {H N I : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hNH : N ≤ H) (hIH : I ≤ H)
    (hNnormal : (N.subgroupOf H).Normal)
    (hsup : N ⊔ I = H)
    {pi : Set ℕ} (hNpi : IsPiNumber pi (Nat.card N))
    (hpPi : p ∉ pi) (R : Sylow p I) :
    IsSylowSubgroupOf p
      ((R : Subgroup I).map I.subtype) H := by
  let NH : Subgroup H := N.subgroupOf H
  let IH : Subgroup H := I.subgroupOf H
  let Q : Subgroup G := (R : Subgroup I).map I.subtype
  have hQI : Q ≤ I := by
    dsimp [Q]
    exact Subgroup.map_subtype_le (R : Subgroup I)
  have hQH : Q ≤ H := hQI.trans hIH
  have hsupH : NH ⊔ IH = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hNH,
      Subgroup.map_subgroupOf_eq_of_le hIH,
      hsup]
    exact H.range_subtype.symm.trans H.subtype.range_eq_map
  have hNHpi : IsPiNumber pi (Nat.card NH) := by
    rw [natCard_subgroupOf_eq hNH]
    exact hNpi
  have hpNH : ¬ p ∣ Nat.card NH := by
    intro hpCard
    exact hpPi (hNHpi Fact.out hpCard)
  have hpIHindex : ¬ p ∣ IH.index := by
    exact fun hpIndex ↦ hpNH
      (hpIndex.trans
        (index_dvd_card_of_sup_eq_top_normal_left_tau1
          hNnormal hsupH))
  let QH : Subgroup H := Q.subgroupOf H
  let QI : Subgroup I := Q.subgroupOf I
  have hQIeq : QI = (R : Subgroup I) := by
    dsimp [QI, Q]
    exact Subgroup.comap_map_eq_self_of_injective
      I.subtype_injective R
  have hQHp : IsPGroup p QH := by
    exact (R.isPGroup'.map I.subtype).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hpQHindex : ¬ p ∣ QH.index := by
    have hfactor : QH.index = QI.index * IH.index := by
      change Q.relIndex H = Q.relIndex I * I.relIndex H
      exact (Q.relIndex_mul_relIndex I H hQI hIH).symm
    rw [hfactor, hQIeq]
    exact Nat.Prime.not_dvd_mul (Fact.out : p.Prime)
      R.not_dvd_index hpIHindex
  let P : Sylow p H := hQHp.toSylow hpQHindex
  refine ⟨P, ?_⟩
  change Q = QH.map H.subtype
  exact (Subgroup.map_subgroupOf_eq_of_le hQH).symm

/-- Corrected invariant-Sylow transfer used in the proof of
`tau1_mmaxI_asymmetry`.

`H` records the exact consequences of the selected Hall subgroup that are
used here: `H ≤ M`, `H ≤ C_G(P)`, and `r ∣ |H|`.  The other hypotheses
are the two maximal-subgroup memberships, the two tau-one memberships,
the beta-prime selection, the beta factorization, and the normalizing
relation between `P` and `Q`. -/
theorem exists_rankOne_le_centralizerWithin_inf_normalizer_of_tau1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M L H P Q : Subgroup G} {p r : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hL : L ∈ minSimple_max_groups (G := G))
    (hpM : p ∈ tau1Primes M)
    (hpL : p ∈ tau1Primes L)
    (hPM : P ≤ M)
    (hP : IsElementaryAbelianOfRank p 1 P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hrBetaL : r ∈ betaPrimes L)
    (hrNotSigmaM : r ∉ sigmaPrimes M)
    (hHM : H ≤ M)
    (hHC : H ≤ Subgroup.centralizer (P : Set G))
    (hrH : r ∣ Nat.card H)
    (hfactor :
      betaCore M ⊔ (M ⊓ Subgroup.normalizer (Q : Set G)) = M) :
    ∃ R : Subgroup G,
      IsElementaryAbelianOfRank r 1 R ∧
        R ≤ centralizerWithin M P ⊓
          Subgroup.normalizer (Q : Set G) := by
  classical
  letI : Fact p.Prime := ⟨hpM.1⟩
  letI : Fact r.Prime := ⟨hrBetaL.1⟩
  let K : Subgroup G := (pPrimeCore p M).map M.subtype
  let I : Subgroup G := M ⊓ Subgroup.normalizer (Q : Set G)
  let N : Subgroup G := K ⊓ I

  have hKHall : IsPrimeComplement p (pPrimeCore p M) :=
    tau1_pPrimeCore_isPrimeComplement hpM
  have hKM : K ≤ M := by
    dsimp [K]
    exact Subgroup.map_subtype_le _
  have hKnormalM : (K.subgroupOf M).Normal := by
    dsimp [K]
    change (((pPrimeCore p M).map M.subtype).comap M.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have hMnormK : M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKnormalM
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    hPM.trans hMnormK
  have hPnormI : P ≤ Subgroup.normalizer (I : Set G) := by
    apply (le_inf
      (hPM.trans Subgroup.le_normalizer)
      (hPQ.trans Subgroup.le_normalizer)).trans
    exact Subgroup.inf_normalizer_le_normalizer_inf
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := by
    apply (le_inf hPK hPnormI).trans
    exact Subgroup.inf_normalizer_le_normalizer_inf

  have hcopKP : Nat.Coprime (Nat.card K) (Nat.card P) := by
    dsimp [K]
    rw [Subgroup.card_map_of_injective M.subtype_injective,
      hP.card_eq, pow_one]
    exact hKHall.card_coprime
  have hcopNP : Nat.Coprime (Nat.card N) (Nat.card P) :=
    hcopKP.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left)
  have hKsol : IsSolvable K := by
    letI : IsSolvable M := mmax_sol hM
    exact isSolvable_of_injective
      (Subgroup.inclusion hKM) (Subgroup.inclusion_injective hKM)
  have hNsol : IsSolvable N := by
    letI : IsSolvable K := hKsol
    exact isSolvable_of_injective
      (Subgroup.inclusion (show N ≤ K from inf_le_left))
      (Subgroup.inclusion_injective (show N ≤ K from inf_le_left))
  obtain ⟨S, hPS⟩ :=
    exists_sylow_normalized_of_coprime_of_isSolvable
      (p := r) hPN hcopNP hNsol

  have hBK : betaCore M ≤ K := by
    dsimp [K]
    exact betaCore_le_map_pPrimeCore_of_tau1 hM hpM
  have hBnormalK : ((betaCore M).subgroupOf K).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr
    exact hKM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (betaCore_le M)).mp (betaCore_normal M))
  have hfactorK : betaCore M ⊔ N = K := by
    dsimp [N, K, I]
    exact betaCore_sup_inf_map_pPrimeCore_eq_of_tau1 hM hpM hfactor
  have hrNotBetaM : r ∉ betaPrimes M := by
    intro hrBetaM
    exact hrNotSigmaM (beta_sub_sigma hM hrBetaM)
  have hSsylowK : IsSylowSubgroupOf r
      ((S : Subgroup N).map N.subtype) K :=
    isSylowSubgroupOf_map_of_normal_sup_tau1
      hBK inf_le_left hBnormalK hfactorK
      (betaCore_isPiNumber M) hrNotBetaM S
  obtain ⟨SK, hSmap⟩ := hSsylowK
  have hPSK : P ≤ Subgroup.normalizer
      (((SK : Subgroup K).map K.subtype : Subgroup G) : Set G) := by
    rw [← hSmap]
    exact hPS

  have hrp : r ≠ p := by
    intro hrp
    apply hpL.2.1
    rw [← hrp]
    exact beta_sub_sigma hL hrBetaL
  have hHCP : H ≤ centralizerWithin M P :=
    le_inf hHM hHC
  have hrCP : r ∣ Nat.card (centralizerWithin M P) :=
    hrH.trans (Subgroup.card_dvd_of_le hHCP)
  obtain ⟨R, hRCP, hRrank⟩ :=
    exists_rankOne_le_of_prime_dvd_natCard_tau1 hrCP
  have hRM : R ≤ M := hRCP.trans inf_le_left
  have hRC : R ≤ Subgroup.centralizer (P : Set G) :=
    hRCP.trans inf_le_right
  have hRMprime : IsPPrimeSubgroup p (R.subgroupOf M) := by
    rw [IsPPrimeSubgroup, natCard_subgroupOf_eq hRM,
      hRrank.card_eq, pow_one]
    exact (Nat.coprime_primes hpM.1 hrBetaL.1).mpr hrp.symm
  have hRMcore : R.subgroupOf M ≤ pPrimeCore p M :=
    isPPrimeSubgroup_le_normal_primeComplement
      (by infer_instance) hKHall hRMprime
  have hRK : R ≤ K := by
    change R ≤ (pPrimeCore p M).map M.subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le hRM]
    exact Subgroup.map_mono hRMcore
  have hPcentR : P ≤ Subgroup.centralizer (R : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hRC
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    hPcentR.trans (Subgroup.centralizer_le_normalizer (R : Set G))
  obtain ⟨T, hPT, hRT⟩ :=
    exists_normalized_sylow_ge_of_coprime_of_isSolvable
      (p := r) hPK hcopKP hKsol hRK hRrank.isPGroup hPR
  obtain ⟨x, ⟨hxK, hxC⟩, hconj⟩ :=
    exists_mem_inf_centralizer_conj_sylow_of_coprime_of_isSolvable
      hPK hcopKP hKsol SK T hPSK hPT

  let R' : Subgroup G :=
    R.map (MulAut.conj x⁻¹).toMonoidHom
  have hR'rank : IsElementaryAbelianOfRank r 1 R' := by
    dsimp [R']
    exact hRrank.map_of_injective
      (MulAut.conj x⁻¹).toMonoidHom
      (MulAut.conj x⁻¹).injective
  have hR'SK : R' ≤ (SK : Subgroup K).map K.subtype := by
    dsimp [R']
    exact (Subgroup.map_mono hRT).trans_eq hconj.symm
  have hSKN : (SK : Subgroup K).map K.subtype ≤ N := by
    rw [← hSmap]
    exact Subgroup.map_subtype_le _
  have hR'N : R' ≤ N := hR'SK.trans hSKN
  have hR'M : R' ≤ M :=
    hR'N.trans (inf_le_left.trans hKM)
  have hR'NQ : R' ≤ Subgroup.normalizer (Q : Set G) :=
    hR'N.trans (inf_le_right.trans inf_le_right)
  have hxInvNormC : x⁻¹ ∈ Subgroup.normalizer
      (Subgroup.centralizer (P : Set G) : Set G) := by
    exact Subgroup.le_normalizer
      ((Subgroup.centralizer (P : Set G)).inv_mem hxC)
  have hmapC :
      (Subgroup.centralizer (P : Set G)).map
          (MulAut.conj x⁻¹).toMonoidHom =
        Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxInvNormC
  have hR'C : R' ≤ Subgroup.centralizer (P : Set G) := by
    dsimp [R']
    exact (Subgroup.map_mono hRC).trans_eq hmapC
  exact ⟨R', hR'rank,
    le_inf (le_inf hR'M hR'C) hR'NQ⟩

end

end Submission.OddOrder.MathlibSupport
