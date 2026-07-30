import Submission.OddOrder.BG.Section07.NormedConstrainedMeetTrans
import Submission.OddOrder.BG.Section07.PLengthOneNormedConstrained
import Submission.OddOrder.BG.Section10.SigmaElementaryControl
import Submission.OddOrder.BG.Section11.ExceptionalSetup
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension

/-!
# Bender--Glauberman Section 11: the exceptional TI lemmas

This file ports `BGsection11.v: exceptional_TIsigmaJ` and
`exceptional_TI_MsigmaJ` (Lemma 11.1 and Corollary 11.2).  The Sylow
hypotheses in Lemma 11.1 are presented as ambient Sylow subgroups of the
minimal counterexample which lie in the relevant sigma cores.  Since those
cores are Hall both in their maximal subgroup and in the full group, this is
the direct Lean form of the source hypotheses and avoids repeatedly mapping
Sylow subgroups through subgroup inclusions in downstream arguments.
-/

namespace Submission.OddOrder.BG.Section11

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

private theorem subgroup_map_symm_map
    {G : Type u} [Group G] (H : Subgroup G) (e : G ≃* G) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  ext x
  simp

private theorem subgroup_symm_map_map
    {G : Type u} [Group G] (H : Subgroup G) (e : G ≃* G) :
    (H.map e.symm.toMonoidHom).map e.toMonoidHom = H := by
  simpa using subgroup_map_symm_map H e.symm

/-- A `p`-group has singleton prime support. -/
private theorem isPiNumber_singleton_of_isPGroup
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) :
    IsPiNumber ({p} : Set ℕ) (Nat.card P) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn]
  intro q hq hqdiv
  have hqp : q = p :=
    Nat.prime_eq_prime_of_dvd_pow hq Fact.out hqdiv
  exact Set.mem_singleton_iff.mpr hqp

/-- An ambient Sylow subgroup normalized by `A` is maximal among the
`q`-subgroups normalized by `A`. -/
private theorem sylow_mem_max_normed
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime] (A : Subgroup G) (Q : Sylow q G)
    (hAQ : A ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G)) :
    (Q : Subgroup G) ∈
      max_normed_pgroups (A : Set G) ({q} : Set ℕ) := by
  refine ⟨⟨isPiNumber_singleton_of_isPGroup Q.isPGroup', hAQ⟩, ?_⟩
  intro R hR hQR
  have hRp : IsPGroup q R :=
    isPGroup_of_isPiNumber_singleton hR.1
  rw [Q.is_maximal' hRp hQR]

/-- Local adapter for the source step `subHall_Sylow`: a Sylow subgroup of
a Hall subgroup maps to a Sylow subgroup of the whole group. -/
private theorem exists_sylow_eq_map_of_sylow_hall
    {H : Type u} [Group H] [Finite H]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup H} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (P : Sylow p A) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H) = (P : Subgroup A).map A.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup H := (P : Subgroup A).map A.subtype
  have hSp : IsPGroup p S := P.isPGroup'.map A.subtype
  have hpAindex : ¬ p ∣ A.index := by
    intro hpIndex
    exact hA.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpAindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

/-- The join of two `pi`-subgroups is a `pi`-subgroup when the first is
normal. -/
private theorem isPiNumber_card_sup_of_normal_left
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {A B : Subgroup K} (hA : A.Normal)
    (hApi : IsPiNumber pi (Nat.card A))
    (hBpi : IsPiNumber pi (Nat.card B)) :
    IsPiNumber pi (Nat.card (A ⊔ B : Subgroup K)) := by
  letI : A.Normal := hA
  have hrel : A.relIndex (A ⊔ B) = A.relIndex B :=
    Subgroup.relIndex_sup_left B A
  have hsubcard : Nat.card (A.subgroupOf (A ⊔ B)) = Nat.card A :=
    natCard_subgroupOf_eq le_sup_left
  rw [← (A.subgroupOf (A ⊔ B)).card_mul_index, hsubcard]
  change IsPiNumber pi (Nat.card A * A.relIndex (A ⊔ B))
  rw [hrel]
  exact hApi.mul
    (hBpi.of_dvd (Subgroup.relIndex_dvd_card A B))

/-- Relative version of normal Hall containment, with all subgroups kept in
the common ambient group. -/
private theorem isPiNumber_le_normal_isHall
    {G : Type u} [Group G] [Finite G] {pi : Set ℕ}
    {L K X : Subgroup G} (hKL : K ≤ L)
    (hKnormal : (K.subgroupOf L).Normal)
    (hKHall : IsHall pi (K.subgroupOf L))
    (hXL : X ≤ L) (hXpi : IsPiNumber pi (Nat.card X)) :
    X ≤ K := by
  let KL : Subgroup L := K.subgroupOf L
  let XL : Subgroup L := X.subgroupOf L
  have hXpiL :
      IsPiNumber pi (Nat.card XL) := by
    rw [natCard_subgroupOf_eq hXL]
    exact hXpi
  have hsupPi : IsPiNumber pi (Nat.card (KL ⊔ XL : Subgroup L)) :=
    isPiNumber_card_sup_of_normal_left hKnormal
      hKHall.isPiNumber_card hXpiL
  have hKLsup : KL ≤ KL ⊔ XL := le_sup_left
  have hrelPi : IsPiNumber pi (KL.relIndex (KL ⊔ XL)) :=
    hsupPi.of_dvd (Subgroup.relIndex_dvd_card KL (KL ⊔ XL))
  have hrelCompl : IsPiNumber piᶜ (KL.relIndex (KL ⊔ XL)) :=
    hKHall.isPiNumber_index.of_dvd
      (Subgroup.relIndex_dvd_index_of_le hKLsup)
  have hcop : (KL.relIndex (KL ⊔ XL)).Coprime
      (KL.relIndex (KL ⊔ XL)) := hrelPi.coprime_compl hrelCompl
  have hone : KL.relIndex (KL ⊔ XL) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
  have hsub : XL ≤ KL :=
    le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone)
  have hmapped := Subgroup.map_mono hsub (f := L.subtype)
  rw [Subgroup.map_subgroupOf_eq_of_le hXL,
    Subgroup.map_subgroupOf_eq_of_le hKL] at hmapped
  exact hmapped

/-- Centralizers commute with transport by a group equivalence. -/
private theorem centralizer_map_mulEquiv
    {G : Type u} [Group G] (A : Subgroup G) (e : G ≃* G) :
    (Subgroup.centralizer (A : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (A.map e.toMonoidHom : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : e.symm z ∈ A := Subgroup.mem_map_equiv.mp hz
    have hcomm :=
      Subgroup.mem_centralizer_iff.mp hy (e.symm z) hz'
    simpa using congrArg e hcomm
  · intro hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzMap : e z ∈ A.map e.toMonoidHom :=
      (Subgroup.mem_map_iff_mem e.injective).mpr hz
    have hcomm :=
      Subgroup.mem_centralizer_iff.mp hy (e z) hzMap
    simpa using congrArg e.symm hcomm

/-- `BGsection11.v: exceptional_TIsigmaJ` (Bender--Glauberman Lemma 11.1).

The subgroups represented by `Q₁` and `Q₂` are Sylow `q`-subgroups of
the full minimal counterexample lying in the two conjugate sigma cores.
The Hall property of the sigma cores makes this equivalent to the source
hypotheses that they are Sylow in those cores. -/
theorem exceptional_TIsigmaJ
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} {M A₀ A : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hExc : exceptional_FTmaximal p M A₀ A)
    (P : Sylow p M) (hAP : A ≤ ambientSylow M P)
    {q : ℕ} (hq : q.Prime) (Q₁ Q₂ : Sylow q G) (g : G)
    (hg : g ∉ M)
    (hAMg : A ≤ M.map (MulAut.conj g⁻¹).toMonoidHom)
    (hQ₁core : (Q₁ : Subgroup G) ≤ sigmaCore M)
    (hAQ₁ : A ≤
      Subgroup.normalizer ((Q₁ : Subgroup G) : Set G))
    (hQ₂core : (Q₂ : Subgroup G) ≤
      sigmaCore (M.map (MulAut.conj g⁻¹).toMonoidHom))
    (hAQ₂ : A ≤
      Subgroup.normalizer ((Q₂ : Subgroup G) : Set G)) :
    ((Q₁ : Subgroup G) ⊓ (Q₂ : Subgroup G) = ⊥) ∧
      ∀ X : Subgroup G, X ≤ A →
        IsElementaryAbelianOfRank p 1 X →
        centralizerWithin (Q₁ : Subgroup G) X = ⊥ ∨
          centralizerWithin (Q₂ : Subgroup G) X = ⊥ := by
  classical
  letI : Fact p.Prime := ⟨hExc.prime⟩
  by_cases hQ₁bot : (Q₁ : Subgroup G) = ⊥
  · constructor
    · rw [hQ₁bot, bot_inf_eq]
    · intro X _ _
      left
      simp [centralizerWithin, hQ₁bot]
  letI : Fact q.Prime := ⟨hq⟩
  let e : G ≃* G := MulAut.conj g⁻¹
  let Mg : Subgroup G := M.map e.toMonoidHom
  have hQ₁M : (Q₁ : Subgroup G) ≤ M :=
    hQ₁core.trans (sigmaCore_le M)
  have hQ₂Mg : (Q₂ : Subgroup G) ≤ Mg := by
    exact hQ₂core.trans (sigmaCore_le Mg)
  have hqQ₁ : q ∣ Nat.card (Q₁ : Subgroup G) :=
    Q₁.isPGroup'.card_eq_or_dvd.resolve_left
      ((Q₁ : Subgroup G).one_lt_card_iff_ne_bot.mpr hQ₁bot).ne'
  have hqSigma : q ∈ sigmaPrimes M := by
    apply sigmaCore_isPiNumber M hq
    exact hqQ₁.trans (Subgroup.card_dvd_of_le hQ₁core)
  have hqNotA : q ∉ primeSupport (Nat.card A) := by
    intro hqA
    have hqpow : q ∣ p ^ 2 := by
      simpa only [hExc.A_rank_two.card_eq] using hqA.2
    have hqp : q = p :=
      Nat.prime_eq_prime_of_dvd_pow hq hExc.prime hqpow
    rw [hqp] at hqSigma
    exact hExc.sigma_compl hqSigma
  have hQ₁max : (Q₁ : Subgroup G) ∈
      max_normed_pgroups (A : Set G) ({q} : Set ℕ) :=
    sylow_mem_max_normed A Q₁ hAQ₁
  have hQ₂max : (Q₂ : Subgroup G) ∈
      max_normed_pgroups (A : Set G) ({q} : Set ℕ) :=
    sylow_mem_max_normed A Q₂ hAQ₂
  have hAconstrained : NormedConstrained A :=
    plength_1_normed_constrained p A hExc.A_rank_two.ne_bot
      (exceptional_pmaxElem hM hExc P hAP)
      (fun _ hH ↦ mFT_proper_plength1 p hH)
  have noCommon :
      ∀ H : Subgroup G, A ≤ H → H < ⊤ →
        (Q₁ : Subgroup G) ⊓ H ≠ ⊥ →
        (Q₂ : Subgroup G) ⊓ H ≠ ⊥ → False := by
    intro H hAH hHproper hQ₁H hQ₂H
    obtain ⟨k, hk, hQ₂conj⟩ :=
      normed_constrained_meet_trans A (Q₁ : Subgroup G)
        (Q₂ : Subgroup G) H hAconstrained hqNotA hAH hHproper
        hQ₁max hQ₂max hQ₁H hQ₂H
    have hkC : k ∈ Subgroup.centralizer (A : Set G) :=
      primeSetCore_le _ _ hk
    have hkM : k ∈ M := by
      apply hExc.normalizer_A₀_le
      apply Subgroup.centralizer_le_normalizer (A₀ : Set G)
      exact (Subgroup.centralizer_le hExc.A₀_le) hkC
    have hQ₂M : (Q₂ : Subgroup G) ≤ M := by
      rw [hQ₂conj]
      have hmapped := Subgroup.map_mono hQ₁M
        (f := (MulAut.conj k⁻¹).toMonoidHom)
      have hMmap : M.map (MulAut.conj k⁻¹).toMonoidHom = M :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (Subgroup.le_normalizer (M.inv_mem hkM))
      rwa [hMmap] at hmapped
    let Q₂back : Sylow q G :=
      Q₂.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hQ₂backEq : (Q₂back : Subgroup G) =
        (Q₂ : Subgroup G).map e.symm.toMonoidHom := by
      simp only [Q₂back, Sylow.coe_mapSurjective]
    have hQ₂backM : (Q₂back : Subgroup G) ≤ M := by
      rw [hQ₂backEq]
      calc
        (Q₂ : Subgroup G).map e.symm.toMonoidHom ≤
            Mg.map e.symm.toMonoidHom := Subgroup.map_mono hQ₂Mg
        _ = M := by
          exact subgroup_map_symm_map M e
    let Q₂M : Sylow q M := Q₂back.subtype hQ₂backM
    have hQ₂Mambient : ambientSylow M Q₂M =
        (Q₂back : Subgroup G) := by
      dsimp only [Q₂M, ambientSylow]
      rw [Sylow.coe_subtype,
        Subgroup.map_subgroupOf_eq_of_le hQ₂backM]
    have hconjEq :
        (ambientSylow M Q₂M).map e.toMonoidHom =
          (Q₂ : Subgroup G) := by
      rw [hQ₂Mambient, hQ₂backEq]
      exact subgroup_symm_map_map (Q₂ : Subgroup G) e
    have hconjLe :
        (ambientSylow M Q₂M).map e.toMonoidHom ≤ M := by
      rw [hconjEq]
      exact hQ₂M
    apply hg
    exact sigma_Sylow_trans hqSigma Q₂M (by
      simpa [e] using hconjLe)
  constructor
  · by_contra hmeet
    have hQ₁meetM : (Q₁ : Subgroup G) ⊓ M ≠ ⊥ := by
      rw [inf_eq_left.mpr hQ₁M]
      exact hQ₁bot
    have hQ₂meetM : (Q₂ : Subgroup G) ⊓ M ≠ ⊥ := by
      intro hbot
      have hle : (Q₁ : Subgroup G) ⊓ (Q₂ : Subgroup G) ≤
          (Q₂ : Subgroup G) ⊓ M :=
        le_inf inf_le_right (inf_le_left.trans hQ₁M)
      rw [hbot] at hle
      exact hmeet (le_bot_iff.mp hle)
    exact noCommon M hExc.A_le (mmax_proper hM)
      hQ₁meetM hQ₂meetM
  · intro X hXA hX
    by_cases hCX₁ : centralizerWithin (Q₁ : Subgroup G) X = ⊥
    · exact Or.inl hCX₁
    by_cases hCX₂ : centralizerWithin (Q₂ : Subgroup G) X = ⊥
    · exact Or.inr hCX₂
    have hACX : A ≤ Subgroup.centralizer (X : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      letI : IsMulCommutative A := hExc.A_rank_two.commutative
      exact congrArg Subtype.val
        (mul_comm (⟨x, hXA hx⟩ : A) ⟨a, ha⟩)
    have hCXproper : Subgroup.centralizer (X : Set G) < ⊤ :=
      mFT_cent_proper X hX.ne_bot
    exact (noCommon (Subgroup.centralizer (X : Set G)) hACX hCXproper
      (by simpa [centralizerWithin] using hCX₁)
      (by simpa [centralizerWithin] using hCX₂)).elim

/-- `BGsection11.v: exceptional_TI_MsigmaJ` (Corollary 11.2).

The sigma core meets neither a distinct conjugate of its maximal subgroup
nor the centralizer of the corresponding conjugate of `A₀`. -/
theorem exceptional_TI_MsigmaJ
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} {M A₀ A : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hExc : exceptional_FTmaximal p M A₀ A)
    (P : Sylow p M) (hAP : A ≤ ambientSylow M P)
    (g : G) (hg : g ∉ M)
    (hAMg : A ≤ M.map (MulAut.conj g⁻¹).toMonoidHom) :
    sigmaCore M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom = ⊥ ∧
      sigmaCore M ⊓
        Subgroup.centralizer
          (A₀.map (MulAut.conj g⁻¹).toMonoidHom : Set G) = ⊥ := by
  classical
  letI : Fact p.Prime := ⟨hExc.prime⟩
  let e : G ≃* G := MulAut.conj g⁻¹
  let Mg : Subgroup G := M.map e.toMonoidHom
  let S : Subgroup G := sigmaCore M
  let T : Subgroup G := sigmaCore Mg
  let H : Subgroup G := S ⊓ Mg
  have hMgmax : Mg ∈ minSimple_max_groups (G := G) :=
    (mmaxJ M e).mpr hM
  have hMnormS : M ≤ Subgroup.normalizer (S : Set G) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le M)).mp
      (sigmaCore_normal M)
  have hMgnormT : Mg ≤ Subgroup.normalizer (T : Set G) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le Mg)).mp
      (sigmaCore_normal Mg)
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    hExc.A_le.trans hMnormS
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    hAMg.trans hMgnormT
  have hAH : A ≤ Subgroup.normalizer (H : Set G) := by
    exact (le_inf hAS (hAMg.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hHpiM : IsPiNumber (sigmaPrimes M) (Nat.card H) :=
    (sigmaCore_isPiNumber M).of_dvd
      (Subgroup.card_dvd_of_le inf_le_left)
  have hSigmaMg : sigmaPrimes Mg = sigmaPrimes M := by
    simpa [Mg, e] using sigmaPrimes_conj M g⁻¹
  have hHpiMg : IsPiNumber (sigmaPrimes Mg) (Nat.card H) := by
    rw [hSigmaMg]
    exact hHpiM
  have hHT : H ≤ T := by
    apply isPiNumber_le_normal_isHall
      (hKL := sigmaCore_le Mg)
      (hKnormal := sigmaCore_normal Mg)
      (hKHall := Msigma_Hall hMgmax)
      (hXL := inf_le_right)
      hHpiMg
  have hcopSA : (Nat.card S).Coprime (Nat.card A) := by
    apply Nat.coprime_of_dvd
    intro r hr hrS hrA
    have hrSigma : r ∈ sigmaPrimes M :=
      sigmaCore_isPiNumber M hr hrS
    have hrpow : r ∣ p ^ 2 := by
      simpa only [hExc.A_rank_two.card_eq] using hrA
    have hrp : r = p :=
      Nat.prime_eq_prime_of_dvd_pow hr hExc.prime hrpow
    rw [hrp] at hrSigma
    exact hExc.sigma_compl hrSigma
  have hcopTA : (Nat.card T).Coprime (Nat.card A) := by
    apply Nat.coprime_of_dvd
    intro r hr hrT hrA
    have hrSigmaMg : r ∈ sigmaPrimes Mg :=
      sigmaCore_isPiNumber Mg hr hrT
    have hrSigma : r ∈ sigmaPrimes M := by
      rwa [hSigmaMg] at hrSigmaMg
    have hrpow : r ∣ p ^ 2 := by
      simpa only [hExc.A_rank_two.card_eq] using hrA
    have hrp : r = p :=
      Nat.prime_eq_prime_of_dvd_pow hr hExc.prime hrpow
    rw [hrp] at hrSigma
    exact hExc.sigma_compl hrSigma
  have hHbot : H = ⊥ := by
    by_contra hHne
    have hHcard : Nat.card H ≠ 1 :=
      (H.one_lt_card_iff_ne_bot.mpr hHne).ne'
    obtain ⟨q, hq, hqH⟩ := Nat.exists_prime_and_dvd hHcard
    letI : Fact q.Prime := ⟨hq⟩
    have hqSigma : q ∈ sigmaPrimes M :=
      hHpiM hq hqH
    have hqSigmaMg : q ∈ sigmaPrimes Mg :=
      hHpiMg hq hqH
    have hcopHA : (Nat.card H).Coprime (Nat.card A) :=
      hcopSA.coprime_dvd_left
        (Subgroup.card_dvd_of_le inf_le_left)
    have hHproper : H < ⊤ :=
      lt_of_le_of_lt
        (inf_le_left.trans (sigmaCore_le M)) (mmax_proper hM)
    have hSproper : S < ⊤ :=
      lt_of_le_of_lt (sigmaCore_le M) (mmax_proper hM)
    have hTproper : T < ⊤ :=
      lt_of_le_of_lt (sigmaCore_le Mg) (mmax_proper hMgmax)
    obtain ⟨R₀, hAR₀⟩ :=
      exists_sylow_normalized_of_coprime_of_isSolvable
        (p := q) hAH hcopHA (mFT_sol hHproper)
    let Q₀ : Subgroup G := (R₀ : Subgroup H).map H.subtype
    have hQ₀H : Q₀ ≤ H := Subgroup.map_subtype_le (R₀ : Subgroup H)
    have hQ₀S : Q₀ ≤ S := hQ₀H.trans inf_le_left
    have hQ₀T : Q₀ ≤ T := hQ₀H.trans hHT
    have hQ₀p : IsPGroup q Q₀ := R₀.isPGroup'.map H.subtype
    have hAQ₀ : A ≤ Subgroup.normalizer (Q₀ : Set G) := by
      simpa [Q₀] using hAR₀
    have hR₀ne : (R₀ : Subgroup H) ≠ ⊥ :=
      R₀.ne_bot_of_dvd_card hqH
    have hQ₀ne : Q₀ ≠ ⊥ := by
      intro hbot
      apply hR₀ne
      apply (Subgroup.map_eq_bot_iff_of_injective
        (R₀ : Subgroup H) H.subtype_injective).mp
      simpa [Q₀] using hbot
    obtain ⟨R₁, hAR₁, hQ₀R₁⟩ :=
      exists_normalized_sylow_ge_of_coprime_of_isSolvable
        (p := q) hAS hcopSA (mFT_sol hSproper)
        hQ₀S hQ₀p hAQ₀
    obtain ⟨R₂, hAR₂, hQ₀R₂⟩ :=
      exists_normalized_sylow_ge_of_coprime_of_isSolvable
        (p := q) hAT hcopTA (mFT_sol hTproper)
        hQ₀T hQ₀p hAQ₀
    obtain ⟨Q₁, hQ₁eq⟩ :=
      exists_sylow_eq_map_of_sylow_hall hq
        (Msigma_Hall_G hM) hqSigma R₁
    obtain ⟨Q₂, hQ₂eq⟩ :=
      exists_sylow_eq_map_of_sylow_hall hq
        (Msigma_Hall_G hMgmax) hqSigmaMg R₂
    have hQ₁S : (Q₁ : Subgroup G) ≤ S := by
      rw [hQ₁eq]
      exact Subgroup.map_subtype_le (R₁ : Subgroup S)
    have hQ₂T : (Q₂ : Subgroup G) ≤ T := by
      rw [hQ₂eq]
      exact Subgroup.map_subtype_le (R₂ : Subgroup T)
    have hAQ₁ : A ≤
        Subgroup.normalizer ((Q₁ : Subgroup G) : Set G) := by
      rw [hQ₁eq]
      exact hAR₁
    have hAQ₂ : A ≤
        Subgroup.normalizer ((Q₂ : Subgroup G) : Set G) := by
      rw [hQ₂eq]
      exact hAR₂
    have hQ₀Q₁ : Q₀ ≤ (Q₁ : Subgroup G) := by
      rw [hQ₁eq]
      exact hQ₀R₁
    have hQ₀Q₂ : Q₀ ≤ (Q₂ : Subgroup G) := by
      rw [hQ₂eq]
      exact hQ₀R₂
    have hti := (exceptional_TIsigmaJ hM hExc P hAP hq
      Q₁ Q₂ g hg hAMg hQ₁S hAQ₁ hQ₂T hAQ₂).1
    have hQ₀bot : Q₀ ≤ ⊥ := by
      rw [← hti]
      exact le_inf hQ₀Q₁ hQ₀Q₂
    exact hQ₀ne (le_bot_iff.mp hQ₀bot)
  let A₀g : Subgroup G := A₀.map e.toMonoidHom
  have hCA₀M : Subgroup.centralizer (A₀ : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer (A₀ : Set G)).trans
      hExc.normalizer_A₀_le
  have hCA₀gMg : Subgroup.centralizer (A₀g : Set G) ≤ Mg := by
    rw [← centralizer_map_mulEquiv A₀ e]
    exact Subgroup.map_mono hCA₀M
  have hsecond : S ⊓ Subgroup.centralizer (A₀g : Set G) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxH : x ∈ H := ⟨hx.1, hCA₀gMg hx.2⟩
    rw [hHbot] at hxH
    exact hxH
  constructor
  · simpa [H, S, Mg, e] using hHbot
  · simpa [S, A₀g, e] using hsecond

end Submission.OddOrder.BG.Section11
