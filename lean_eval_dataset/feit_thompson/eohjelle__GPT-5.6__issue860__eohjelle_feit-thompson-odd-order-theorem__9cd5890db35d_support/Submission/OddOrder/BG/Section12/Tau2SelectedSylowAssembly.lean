import Submission.OddOrder.BG.Section03.SemiregularConjugation
import Submission.OddOrder.BG.Section12.ComplementExistence
import Submission.OddOrder.BG.Section12.TauDefinitions
import Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal
import Submission.OddOrder.MathlibSupport.PElementCyclic
import Submission.OddOrder.MathlibSupport.PPrimeCore

/-!
# Bender--Glauberman Section 12: assembly of the selected tau-two factors

This file isolates the last, group-theoretic assembly in the proof of
`BGsection12.v: FTtypeF_complement`.  For every nontrivial Sylow subgroup of
the abelian `tau2` Hall factor, the two preceding constructor modules supply
a normal cyclic subgroup with the same exponent and a regular omega-one
subgroup.  We select one such factor for each prime, join them, and adjoin a
Hall `tau2(M)`-complement.

The two conclusions needed by Theorem 12.12 are proved here: the resulting
subgroup has the exponent of `U`, and its conjugation action on `M_sigma` is
semiregular.  No conclusion of Theorem 12.12 is included in the input
package.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open scoped Pointwise

noncomputable section

universe u

/-! ## A cyclic regular factor of one tau-two Sylow subgroup -/

/-- The concrete output of either cyclic-factor construction in the
abelian-Sylow branch of Bender--Glauberman Theorem 12.12.

The Sylow subgroup is intrinsic to `U₂`; `Z` is represented in the common
ambient group.  Its first field therefore also records the required
transport from the intrinsic Sylow subgroup. -/
structure CyclicRegularTau2Factor
    {G : Type u} [Group G] [Finite G]
    (M U U₂ : Subgroup G) {p : ℕ} [Fact p.Prime]
    (P : Sylow p U₂) where
  Z : Subgroup G
  Z_le_sylow :
    Z ≤ (P : Subgroup U₂).map U₂.subtype
  Z_normal_U : (Z.subgroupOf U).Normal
  Z_cyclic : IsCyclic Z
  omega_regular :
    centralizerWithin (sigmaCore M)
      ((omegaOne p Z).map Z.subtype) = ⊥
  exponent_eq :
    Monoid.exponent Z = Monoid.exponent P

/-- A factor constructor for every nontrivial intrinsic Sylow subgroup of
`U₂`.  This is a family of mathematical factor packages, not a bridge to a
target conclusion. -/
abbrev CyclicRegularTau2FactorFamily
    {G : Type u} [Group G] [Finite G]
    (M U U₂ : Subgroup G) :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p U₂),
    (P : Subgroup U₂) ≠ ⊥ →
      CyclicRegularTau2Factor M U U₂ P

/-- The canonical selected Sylow subgroup for a prime. -/
noncomputable def selectedTau2Sylow
    {G : Type u} [Group G] (U₂ : Subgroup G)
    (p : {p : ℕ // p.Prime}) : Sylow (p : ℕ) U₂ :=
  Classical.choice Sylow.nonempty

/-- Select the cyclic regular factor at `p`, using the bottom subgroup only
when the selected Sylow subgroup itself is trivial. -/
noncomputable def selectedTau2CyclicFactor
    {G : Type u} [Group G] [Finite G]
    (M U U₂ : Subgroup G)
    (factors : CyclicRegularTau2FactorFamily M U U₂)
    (p : {p : ℕ // p.Prime}) : Subgroup G := by
  classical
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  let P : Sylow (p : ℕ) U₂ := selectedTau2Sylow U₂ p
  exact if hP : (P : Subgroup U₂) ≠ ⊥ then
    (factors (p : ℕ) P hP).Z
  else ⊥

/-- Join all selected cyclic factors. -/
noncomputable def selectedTau2CyclicJoin
    {G : Type u} [Group G] [Finite G]
    (M U U₂ : Subgroup G)
    (factors : CyclicRegularTau2FactorFamily M U U₂) :
    Subgroup G :=
  ⨆ p : {p : ℕ // p.Prime},
    selectedTau2CyclicFactor M U U₂ factors p

private theorem selectedTau2CyclicFactor_eq
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G}
    (factors : CyclicRegularTau2FactorFamily M U U₂)
    (p : {p : ℕ // p.Prime}) [Fact (p : ℕ).Prime]
    (hP : (selectedTau2Sylow U₂ p : Subgroup U₂) ≠ ⊥) :
    selectedTau2CyclicFactor M U U₂ factors p =
      (factors (p : ℕ) (selectedTau2Sylow U₂ p) hP).Z := by
  simp only [selectedTau2CyclicFactor, dif_pos hP]

private theorem selectedTau2CyclicFactor_eq_bot
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G}
    (factors : CyclicRegularTau2FactorFamily M U U₂)
    (p : {p : ℕ // p.Prime})
    (hP : (selectedTau2Sylow U₂ p : Subgroup U₂) = ⊥) :
    selectedTau2CyclicFactor M U U₂ factors p = ⊥ := by
  classical
  simp [selectedTau2CyclicFactor, hP]

private theorem selectedTau2CyclicFactor_le_sylow
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G}
    (factors : CyclicRegularTau2FactorFamily M U U₂)
    (p : {p : ℕ // p.Prime}) :
    selectedTau2CyclicFactor M U U₂ factors p ≤
      (selectedTau2Sylow U₂ p : Subgroup U₂).map U₂.subtype := by
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  by_cases hP : (selectedTau2Sylow U₂ p : Subgroup U₂) ≠ ⊥
  · rw [selectedTau2CyclicFactor_eq factors p hP]
    exact (factors (p : ℕ) (selectedTau2Sylow U₂ p) hP).Z_le_sylow
  · have hPbot :
        (selectedTau2Sylow U₂ p : Subgroup U₂) = ⊥ :=
        Classical.not_not.mp hP
    rw [selectedTau2CyclicFactor_eq_bot factors p hPbot]
    exact bot_le

private theorem selectedTau2CyclicFactor_le_U₂
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G}
    (factors : CyclicRegularTau2FactorFamily M U U₂)
    (p : {p : ℕ // p.Prime}) :
    selectedTau2CyclicFactor M U U₂ factors p ≤ U₂ :=
  (selectedTau2CyclicFactor_le_sylow factors p).trans
    (Subgroup.map_subtype_le _)

private theorem selectedTau2CyclicFactor_isPGroup
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G}
    (factors : CyclicRegularTau2FactorFamily M U U₂)
    (p : {p : ℕ // p.Prime}) :
    IsPGroup (p : ℕ)
      (selectedTau2CyclicFactor M U U₂ factors p) := by
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  exact (selectedTau2Sylow U₂ p).isPGroup'.map U₂.subtype |>.to_le
    (selectedTau2CyclicFactor_le_sylow factors p)

private theorem selectedTau2CyclicFactor_normal_U
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G}
    (factors : CyclicRegularTau2FactorFamily M U U₂)
    (p : {p : ℕ // p.Prime}) :
    ((selectedTau2CyclicFactor M U U₂ factors p).subgroupOf U).Normal := by
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  by_cases hP : (selectedTau2Sylow U₂ p : Subgroup U₂) ≠ ⊥
  · rw [selectedTau2CyclicFactor_eq factors p hP]
    exact (factors (p : ℕ) (selectedTau2Sylow U₂ p) hP).Z_normal_U
  · have hPbot :
        (selectedTau2Sylow U₂ p : Subgroup U₂) = ⊥ :=
        Classical.not_not.mp hP
    rw [selectedTau2CyclicFactor_eq_bot factors p hPbot]
    infer_instance

private theorem selectedTau2CyclicJoin_le_U₂
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G}
    (factors : CyclicRegularTau2FactorFamily M U U₂) :
    selectedTau2CyclicJoin M U U₂ factors ≤ U₂ := by
  rw [selectedTau2CyclicJoin]
  exact iSup_le fun p ↦ selectedTau2CyclicFactor_le_U₂ factors p

private theorem selectedTau2CyclicJoin_le_U
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G} (hU₂U : U₂ ≤ U)
    (factors : CyclicRegularTau2FactorFamily M U U₂) :
    selectedTau2CyclicJoin M U U₂ factors ≤ U :=
  (selectedTau2CyclicJoin_le_U₂ factors).trans hU₂U

private theorem selectedTau2CyclicJoin_normal_U
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G} (hU₂U : U₂ ≤ U)
    (factors : CyclicRegularTau2FactorFamily M U U₂) :
    ((selectedTau2CyclicJoin M U U₂ factors).subgroupOf U).Normal := by
  let Z₂ : Subgroup G := selectedTau2CyclicJoin M U U₂ factors
  have hZ₂U : Z₂ ≤ U := selectedTau2CyclicJoin_le_U hU₂U factors
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZ₂U]
  refine (show U ≤ ⨅ p : {p : ℕ // p.Prime},
      Subgroup.normalizer
        (selectedTau2CyclicFactor M U U₂ factors p : Set G) by
    intro x hx
    rw [Subgroup.mem_iInf]
    intro p
    have hZU : selectedTau2CyclicFactor M U U₂ factors p ≤ U :=
      (selectedTau2CyclicFactor_le_U₂ factors p).trans hU₂U
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hZU).mp
      (selectedTau2CyclicFactor_normal_U factors p) hx) |>.trans ?_
  simpa only [Z₂, selectedTau2CyclicJoin] using
    (Subgroup.iInf_normalizer_le_normalizer_iSup
      (fun p : {p : ℕ // p.Prime} ↦
        selectedTau2CyclicFactor M U U₂ factors p))

/-! ## Elementary Hall and complement adapters -/

/-- A Sylow subgroup of a Hall subgroup maps to a Sylow subgroup of the
ambient finite group. -/
private theorem exists_sylow_eq_map_of_sylow_hall_selected12
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {H : Subgroup K} (hH : IsHall pi H) (hpPi : p ∈ pi)
    (P : Sylow p H) :
    ∃ Q : Sylow p K,
      (Q : Subgroup K) = (P : Subgroup H).map H.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup K := (P : Subgroup H).map H.subtype
  have hSp : IsPGroup p S := P.isPGroup'.map H.subtype
  have hpHindex : ¬ p ∣ H.index := by
    intro hpIndex
    exact hH.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpHindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

/-- A normalized disjoint pair is complementary in the subgroup it
generates. -/
private theorem subgroupOf_sup_isComplement_selected12
    {G : Type u} [Group G] {H R : Subgroup G}
    (hnorm : R ≤ Subgroup.normalizer (H : Set G))
    (hdis : Disjoint H R) :
    (H.subgroupOf (H ⊔ R)).IsComplement'
      (R.subgroupOf (H ⊔ R)) := by
  let K : Subgroup G := H ⊔ R
  let HK : Subgroup K := H.subgroupOf K
  let RK : Subgroup K := R.subgroupOf K
  have hKnormH : K ≤ Subgroup.normalizer (H : Set G) :=
    sup_le Subgroup.le_normalizer hnorm
  letI : HK.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKnormH
  have hdisK : Disjoint HK RK := by
    rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hxBot : ((x : K) : G) ∈ (⊥ : Subgroup G) :=
        hdis.le_bot ⟨hx.1, hx.2⟩
      exact Subgroup.mem_bot.mp hxBot
    · exact bot_le
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisK
  have htop : HK ⊔ RK = ⊤ := by
    change H.subgroupOf K ⊔ R.subgroupOf K = ⊤
    rw [← Subgroup.subgroupOf_sup
      (show H ≤ K from le_sup_left)
      (show R ≤ K from le_sup_right)]
    exact Subgroup.subgroupOf_self K
  rw [← Subgroup.normal_mul HK RK, htop]
  rfl

/-- Membership of a `pi`-element in a normal `pi`-Hall subgroup. -/
private theorem mem_normal_isHall_of_isPiNumber_order_selected12
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {C K : Subgroup G}
    (hKC : K ≤ C) (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    {x : G} (hxC : x ∈ C)
    (hxPi : IsPiNumber pi (orderOf x)) :
    x ∈ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa [KC] using hKnormal
  let xC : C := ⟨x, hxC⟩
  let qC : C →* C ⧸ KC := QuotientGroup.mk' KC
  have hxPiC : IsPiNumber pi (orderOf xC) := by
    rw [← orderOf_injective C.subtype C.subtype_injective xC]
    exact hxPi
  have horderPi : IsPiNumber pi (orderOf (qC xC)) :=
    hxPiC.of_dvd (orderOf_map_dvd qC xC)
  have horderCompl : IsPiNumber piᶜ (orderOf (qC xC)) := by
    have hIndex : IsPiNumber piᶜ KC.index := by
      simpa [KC] using hKHall.isPiNumber_index
    apply hIndex.of_dvd
    simpa only [KC.index_eq_card] using orderOf_dvd_natCard (qC xC)
  have horderOne : orderOf (qC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (horderPi.coprime_compl horderCompl) dvd_rfl dvd_rfl
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp horderOne
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp (by simpa [qC] using hqOne)
  exact hxKC

/-! ## Exponent preservation -/

/-- The maximal `p`-part of the ambient exponent already occurs in a
`p`-Sylow subgroup of any Hall subgroup whose prime set contains `p`. -/
private theorem pow_factorization_exponent_dvd_exponent_sylow_hall_selected12
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {H : Subgroup K} (hH : IsHall pi H) (hpPi : p ∈ pi)
    (P : Sylow p H) :
    p ^ (Monoid.exponent K).factorization p ∣ Monoid.exponent P := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ⟩ :=
    exists_sylow_eq_map_of_sylow_hall_selected12 hp hH hpPi P
  obtain ⟨g, hgOrder⟩ :=
    hp.exists_orderOf_eq_pow_factorization_exponent (G := K)
  have hgPelt : IsPElement p g := by
    refine ⟨(Monoid.exponent K).factorization p, ?_⟩
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hgOrder]
  obtain ⟨R, hgR⟩ := hgPelt.zpowers_isPGroup.exists_le_sylow
  have hgmemR : g ∈ (R : Subgroup K) :=
    hgR (Subgroup.mem_zpowers g)
  have horderR : orderOf g ∣ Monoid.exponent R := by
    have h := Monoid.order_dvd_exponent (⟨g, hgmemR⟩ : R)
    simpa using
      (orderOf_injective (R : Subgroup K).subtype
        (R : Subgroup K).subtype_injective
        (⟨g, hgmemR⟩ : R)).symm ▸ h
  let ePmap : P ≃* (P : Subgroup H).map H.subtype :=
    (P : Subgroup H).equivMapOfInjective
      H.subtype H.subtype_injective
  let eQmap : Q ≃* (P : Subgroup H).map H.subtype :=
    MulEquiv.subgroupCongr hQ
  have hExpRQ : Monoid.exponent R = Monoid.exponent Q :=
    Monoid.exponent_eq_of_mulEquiv (Sylow.equiv R Q)
  have hExpQP : Monoid.exponent Q = Monoid.exponent P :=
    Monoid.exponent_eq_of_mulEquiv (eQmap.trans ePmap.symm)
  rw [← hgOrder]
  exact horderR.trans (by rw [hExpRQ, hExpQP])

/-- The selected cyclic tau-two factors, together with a complementary
Hall subgroup, preserve the exponent of `U`.

This is the Lean counterpart of the `expU0U` calculation in
`BGsection12.v`.  It is stated independently of semiregularity so both
factor constructors can share the arithmetic assembly. -/
theorem exponent_eq_of_selected_sylow_factors_12_12
    {G : Type u} [Group G] [Finite G]
    {M U U₂ U₃₁ : Subgroup G}
    (hU₂U : U₂ ≤ U)
    (hHallU₂ : IsHall (tau2Primes M) (U₂.subgroupOf U))
    (hU₃₁U : U₃₁ ≤ U)
    (hHallU₃₁ : IsHall (tau2Primes M)ᶜ (U₃₁.subgroupOf U))
    (factors : CyclicRegularTau2FactorFamily M U U₂) :
    Monoid.exponent
        (selectedTau2CyclicJoin M U U₂ factors ⊔ U₃₁ : Subgroup G) =
      Monoid.exponent U := by
  classical
  let Z₂ : Subgroup G := selectedTau2CyclicJoin M U U₂ factors
  let U₀ : Subgroup G := Z₂ ⊔ U₃₁
  have hZ₂U : Z₂ ≤ U := selectedTau2CyclicJoin_le_U hU₂U factors
  have hU₀U : U₀ ≤ U := sup_le hZ₂U hU₃₁U
  have hExpU₀U : Monoid.exponent U₀ ∣ Monoid.exponent U :=
    Monoid.exponent_dvd_of_monoidHom
      (Subgroup.inclusion hU₀U)
      (Subgroup.inclusion_injective hU₀U)
  have hExpUU₀ : Monoid.exponent U ∣ Monoid.exponent U₀ := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    letI : Fact p.Prime := ⟨hp⟩
    cases k with
    | zero => simp
    | succ k =>
      have hExpUne : Monoid.exponent U ≠ 0 :=
        Monoid.exponent_ne_zero_of_finite
      have hkFac : k + 1 ≤ (Monoid.exponent U).factorization p :=
        (hp.pow_dvd_iff_le_factorization hExpUne).mp (by
          simpa [Nat.succ_eq_add_one] using hpk)
      have hkMax :
          p ^ (k + 1) ∣
            p ^ (Monoid.exponent U).factorization p :=
        pow_dvd_pow p hkFac
      by_cases hpTau : p ∈ tau2Primes M
      · let q : {q : ℕ // q.Prime} := ⟨p, hp⟩
        let P : Sylow p U₂ := selectedTau2Sylow U₂ q
        let eU₂ : U₂ ≃* U₂.subgroupOf U :=
          (Subgroup.subgroupOfEquivOfLe hU₂U).symm
        let PH : Sylow p (U₂.subgroupOf U) :=
          Sylow.mapSurjective (f := eU₂.toMonoidHom)
            eU₂.surjective P
        let eP₀ : P ≃* (P : Subgroup U₂).map eU₂.toMonoidHom :=
          (P : Subgroup U₂).equivMapOfInjective
            eU₂.toMonoidHom eU₂.injective
        let eP : P ≃* PH :=
          eP₀.trans (MulEquiv.subgroupCongr (by rfl))
        have hMaxPH :
            p ^ (Monoid.exponent U).factorization p ∣
              Monoid.exponent PH :=
          pow_factorization_exponent_dvd_exponent_sylow_hall_selected12
            hp hHallU₂ hpTau PH
        have hMaxP :
            p ^ (Monoid.exponent U).factorization p ∣
              Monoid.exponent P := by
          rw [Monoid.exponent_eq_of_mulEquiv eP]
          exact hMaxPH
        have hPk : p ^ (k + 1) ∣ Monoid.exponent P :=
          hkMax.trans hMaxP
        have hPne : (P : Subgroup U₂) ≠ ⊥ := by
          intro hPbot
          have hExpPone : Monoid.exponent P = 1 := by
            rw [show (P : Subgroup U₂) = ⊥ from hPbot]
            exact Monoid.exp_eq_one_of_subsingleton
          have hpOne : p ∣ 1 := by
            rw [← hExpPone]
            exact (dvd_pow_self p (Nat.succ_ne_zero k)).trans hPk
          exact hp.not_dvd_one hpOne
        let F : CyclicRegularTau2Factor M U U₂ P :=
          factors p P hPne
        have hFZU₀ : F.Z ≤ U₀ := by
          rw [← selectedTau2CyclicFactor_eq factors q hPne]
          exact (le_iSup
            (fun r : {r : ℕ // r.Prime} ↦
              selectedTau2CyclicFactor M U U₂ factors r) q).trans
            le_sup_left
        have hExpFU₀ : Monoid.exponent F.Z ∣ Monoid.exponent U₀ :=
          Monoid.exponent_dvd_of_monoidHom
            (Subgroup.inclusion hFZU₀)
            (Subgroup.inclusion_injective hFZU₀)
        have hPkF : p ^ (k + 1) ∣ Monoid.exponent F.Z := by
          rw [F.exponent_eq]
          exact hPk
        exact hPkF.trans hExpFU₀
      · have hpCompl : p ∈ (tau2Primes M)ᶜ := hpTau
        let P₃₁ : Sylow p (U₃₁.subgroupOf U) :=
          Classical.choice Sylow.nonempty
        have hMaxP₃₁ :
            p ^ (Monoid.exponent U).factorization p ∣
              Monoid.exponent P₃₁ :=
          pow_factorization_exponent_dvd_exponent_sylow_hall_selected12
            hp hHallU₃₁ hpCompl P₃₁
        have hkP₃₁ : p ^ (k + 1) ∣ Monoid.exponent P₃₁ :=
          hkMax.trans hMaxP₃₁
        have hExpP₃₁H :
          Monoid.exponent P₃₁ ∣
              Monoid.exponent (U₃₁.subgroupOf U) :=
          Monoid.exponent_dvd_of_monoidHom
            (P₃₁ : Subgroup (U₃₁.subgroupOf U)).subtype
            (P₃₁ : Subgroup (U₃₁.subgroupOf U)).subtype_injective
        let eU₃₁ : U₃₁.subgroupOf U ≃* U₃₁ :=
          Subgroup.subgroupOfEquivOfLe hU₃₁U
        have hExpHU₃₁ :
            Monoid.exponent (U₃₁.subgroupOf U) =
              Monoid.exponent U₃₁ :=
          Monoid.exponent_eq_of_mulEquiv eU₃₁
        have hU₃₁U₀ : U₃₁ ≤ U₀ := le_sup_right
        have hExpU₃₁U₀ :
            Monoid.exponent U₃₁ ∣ Monoid.exponent U₀ :=
          Monoid.exponent_dvd_of_monoidHom
            (Subgroup.inclusion hU₃₁U₀)
            (Subgroup.inclusion_injective hU₃₁U₀)
        have hExpHU₀ :
            Monoid.exponent (U₃₁.subgroupOf U) ∣
              Monoid.exponent U₀ := by
          rw [hExpHU₃₁]
          exact hExpU₃₁U₀
        exact hkP₃₁.trans (hExpP₃₁H.trans hExpHU₀)
  exact Nat.dvd_antisymm hExpU₀U hExpUU₀

/-! ## Prime-order elements of the selected join -/

/-- Split the selected join into its factor at `q` and the join of all
other prime factors.  Keeping this lattice calculation separate prevents
the later Sylow argument from carrying the full indexed-supremum proof in
its local context. -/
private theorem selectedTau2CyclicJoin_eq_factor_sup_other
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G}
    (factors : CyclicRegularTau2FactorFamily M U U₂)
    (q : {q : ℕ // q.Prime}) :
    selectedTau2CyclicJoin M U U₂ factors =
      selectedTau2CyclicFactor M U U₂ factors q ⊔
        ⨆ r : {r : {r : ℕ // r.Prime} // r ≠ q},
          selectedTau2CyclicFactor M U U₂ factors r.1 := by
  apply le_antisymm
  · rw [selectedTau2CyclicJoin]
    apply iSup_le
    intro r
    by_cases hrq : r = q
    · subst r
      exact le_sup_left
    · exact (le_iSup
        (fun s : {s : {s : ℕ // s.Prime} // s ≠ q} ↦
          selectedTau2CyclicFactor M U U₂ factors s.1)
        ⟨r, hrq⟩).trans le_sup_right
  · apply sup_le
    · exact le_iSup
        (fun r : {r : ℕ // r.Prime} ↦
          selectedTau2CyclicFactor M U U₂ factors r) q
    · apply iSup_le
      intro r
      exact le_iSup
        (fun s : {s : ℕ // s.Prime} ↦
          selectedTau2CyclicFactor M U U₂ factors s) r.1

/-- Every selected factor away from `q` lies in the mapped `q'`-core of
`U₂`.  This is the normal-coprime half of the Sylow decomposition used
below. -/
private theorem selectedTau2CyclicOtherJoin_le_pPrimeCore
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G} (hU₂U : U₂ ≤ U)
    (factors : CyclicRegularTau2FactorFamily M U U₂)
    (q : {q : ℕ // q.Prime}) :
    (⨆ r : {r : {r : ℕ // r.Prime} // r ≠ q},
        selectedTau2CyclicFactor M U U₂ factors r.1) ≤
      (pPrimeCore (q : ℕ) U₂).map U₂.subtype := by
  apply iSup_le
  intro r
  let R : Subgroup G :=
    selectedTau2CyclicFactor M U U₂ factors r.1
  have hRU₂ : R ≤ U₂ :=
    selectedTau2CyclicFactor_le_U₂ factors r.1
  have hRU : R ≤ U := hRU₂.trans hU₂U
  letI : Fact (r.1 : ℕ).Prime := ⟨r.1.property⟩
  have hRq : IsPGroup (r.1 : ℕ) R :=
    selectedTau2CyclicFactor_isPGroup factors r.1
  have hRqU₂ : IsPGroup (r.1 : ℕ) (R.subgroupOf U₂) :=
    hRq.of_equiv (Subgroup.subgroupOfEquivOfLe hRU₂).symm
  have hRnormalU₂ : (R.subgroupOf U₂).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact hU₂U.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hRU).mp
        (selectedTau2CyclicFactor_normal_U factors r.1))
  have hrq : (r.1 : ℕ) ≠ (q : ℕ) := by
    intro hrq
    apply r.2
    apply Subtype.ext
    exact hrq
  have hRprime : IsPPrimeSubgroup (q : ℕ) (R.subgroupOf U₂) := by
    obtain ⟨n, hcard⟩ := hRqU₂.exists_card_eq
    rw [IsPPrimeSubgroup, hcard]
    exact ((Nat.coprime_primes q.property r.1.property).mpr hrq.symm).pow_right n
  have hRcore : R.subgroupOf U₂ ≤ pPrimeCore (q : ℕ) U₂ :=
    le_pPrimeCore hRprime hRnormalU₂
  change R ≤ (pPrimeCore (q : ℕ) U₂).map U₂.subtype
  rw [← Subgroup.map_subgroupOf_eq_of_le hRU₂]
  exact Subgroup.map_mono hRcore

/-- A prime-order element of the selected join belongs to the selected
cyclic factor for that prime.

For fixed `p`, the join of all factors at primes different from `p` lies in
the mapped `p'`-core of `U₂`.  The `p`-factor is normal in `U`, so the two
parts give a coprime internal product and the `p`-factor is the normal Sylow
subgroup of the whole selected join. -/
private theorem mem_selectedTau2CyclicFactor_of_order_eq_prime
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G} (hU₂U : U₂ ≤ U)
    (factors : CyclicRegularTau2FactorFamily M U U₂)
    {p : ℕ} (hp : p.Prime) {e : G}
    (heZ₂ : e ∈ selectedTau2CyclicJoin M U U₂ factors)
    (heOrder : orderOf e = p) :
    e ∈ selectedTau2CyclicFactor M U U₂ factors ⟨p, hp⟩ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let q : {q : ℕ // q.Prime} := ⟨p, hp⟩
  let P : Sylow p U₂ := selectedTau2Sylow U₂ q
  let Z₂ : Subgroup G := selectedTau2CyclicJoin M U U₂ factors
  have hZ₂U₂ : Z₂ ≤ U₂ := selectedTau2CyclicJoin_le_U₂ factors
  have hpZ₂ : p ∣ Nat.card Z₂ := by
    rw [← heOrder]
    exact Z₂.orderOf_dvd_natCard heZ₂
  have hpU₂ : p ∣ Nat.card U₂ :=
    hpZ₂.trans (Subgroup.card_dvd_of_le hZ₂U₂)
  have hpP : p ∣ Nat.card P := P.dvd_card_of_dvd_card hpU₂
  have hPne : (P : Subgroup U₂) ≠ ⊥ := by
    intro hPbot
    apply hp.not_dvd_one
    simpa [hPbot] using hpP
  let F : CyclicRegularTau2Factor M U U₂ P := factors p P hPne
  let Zp : Subgroup G := F.Z
  have hZpSelected :
      selectedTau2CyclicFactor M U U₂ factors q = Zp := by
    simpa [Zp, F] using
      selectedTau2CyclicFactor_eq factors q hPne
  have hZpU₂ : Zp ≤ U₂ := by
    exact F.Z_le_sylow.trans (Subgroup.map_subtype_le _)
  have hZpU : Zp ≤ U := hZpU₂.trans hU₂U
  have hZpP : IsPGroup p Zp :=
    (P.isPGroup'.map U₂.subtype).to_le F.Z_le_sylow

  let Zother : Subgroup G :=
    ⨆ r : {r : {r : ℕ // r.Prime} // r ≠ q},
      selectedTau2CyclicFactor M U U₂ factors r.1
  have hZ₂decomp : Z₂ = Zp ⊔ Zother := by
    change selectedTau2CyclicJoin M U U₂ factors =
      Zp ⊔
        ⨆ r : {r : {r : ℕ // r.Prime} // r ≠ q},
          selectedTau2CyclicFactor M U U₂ factors r.1
    rw [← hZpSelected]
    exact selectedTau2CyclicJoin_eq_factor_sup_other factors q

  let Op : Subgroup G := (pPrimeCore p U₂).map U₂.subtype
  have hZotherOp : Zother ≤ Op := by
    simpa only [Zother, Op, q] using
      selectedTau2CyclicOtherJoin_le_pPrimeCore hU₂U factors q
  have hpOp : Nat.Coprime p (Nat.card Op) := by
    change Nat.Coprime p
      (Nat.card ((pPrimeCore p U₂).map U₂.subtype))
    rw [Subgroup.card_map_of_injective U₂.subtype_injective]
    exact pPrimeCore_coprime_card
  have hpZother : Nat.Coprime p (Nat.card Zother) :=
    hpOp.coprime_dvd_right (Subgroup.card_dvd_of_le hZotherOp)
  obtain ⟨n, hZpcard⟩ := hZpP.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Zp) (Nat.card Zother) := by
    rw [hZpcard]
    exact hpZother.pow_left n
  have hdis : Disjoint Zp Zother :=
    Subgroup.disjoint_of_coprime_natCard hcop
  have hZotherU : Zother ≤ U := by
    change (⨆ r : {r : {r : ℕ // r.Prime} // r ≠ q},
      selectedTau2CyclicFactor M U U₂ factors r.1) ≤ U
    exact iSup_le fun r ↦
      (selectedTau2CyclicFactor_le_U₂ factors r.1).trans hU₂U
  have hZotherNormZp : Zother ≤ Subgroup.normalizer (Zp : Set G) :=
    hZotherU.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hZpU).mp
        F.Z_normal_U)
  have hcompSup :
      (Zp.subgroupOf (Zp ⊔ Zother)).IsComplement'
        (Zother.subgroupOf (Zp ⊔ Zother)) :=
    subgroupOf_sup_isComplement_selected12 hZotherNormZp hdis
  have hZpZ₂ : Zp ≤ Z₂ := le_sup_left.trans hZ₂decomp.symm.le
  have hZotherZ₂ : Zother ≤ Z₂ :=
    le_sup_right.trans hZ₂decomp.symm.le
  let ZpZ₂ : Subgroup Z₂ := Zp.subgroupOf Z₂
  let ZotherZ₂ : Subgroup Z₂ := Zother.subgroupOf Z₂
  have hcomp : ZpZ₂.IsComplement' ZotherZ₂ := by
    change (Zp.subgroupOf Z₂).IsComplement' (Zother.subgroupOf Z₂)
    rw [hZ₂decomp]
    exact hcompSup
  have hZpZ₂p : IsPGroup p ZpZ₂ :=
    hZpP.of_equiv (Subgroup.subgroupOfEquivOfLe hZpZ₂).symm
  have hpIndex : ¬ p ∣ ZpZ₂.index := by
    rw [hcomp.symm.index_eq_card,
      natCard_subgroupOf_eq hZotherZ₂]
    exact hp.coprime_iff_not_dvd.mp hpZother
  let SZ : Sylow p Z₂ := hZpZ₂p.toSylow hpIndex
  have hSZnormal : (SZ : Subgroup Z₂).Normal := by
    change ZpZ₂.Normal
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    have hZ₂U : Z₂ ≤ U := hZ₂U₂.trans hU₂U
    exact hZ₂U.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hZpU).mp
        F.Z_normal_U)
  let eZ₂ : Z₂ := ⟨e, heZ₂⟩
  have heZ₂Order : orderOf eZ₂ = p := by
    exact (orderOf_injective Z₂.subtype Z₂.subtype_injective eZ₂).symm.trans
      heOrder
  have hePelt : IsPElement p eZ₂ := by
    refine ⟨1, ?_⟩
    apply orderOf_dvd_iff_pow_eq_one.mp
    simpa [heZ₂Order]
  letI : Unique (Sylow p Z₂) :=
    Sylow.unique_of_normal SZ hSZnormal
  obtain ⟨R, hR⟩ := hePelt.zpowers_isPGroup.exists_le_sylow
  have hRSZ : R = SZ := Subsingleton.elim R SZ
  have heSZ : eZ₂ ∈ (SZ : Subgroup Z₂) := by
    rw [← hRSZ]
    exact hR (Subgroup.mem_zpowers eZ₂)
  have heZp : e ∈ Zp := heSZ
  rw [hZpSelected]
  exact heZp

/-! ## Semiregularity -/

private theorem isPiNumber_order_eq_prime_selected12
    {G : Type u} [Group G] {pi : Set ℕ}
    {p : ℕ} (hp : p.Prime) (hpPi : p ∈ pi)
    {e : G} (heOrder : orderOf e = p) :
    IsPiNumber pi (orderOf e) := by
  intro q hq hqOrder
  rw [heOrder] at hqOrder
  rcases (Nat.dvd_prime hp).mp hqOrder with hqOne | hqp
  · exact (hq.ne_one hqOne).elim
  · simpa [hqp] using hpPi

/-- The selected cyclic factors and the complementary Hall subgroup act
semiregularly on `M_sigma`.

The hypothesis `hoff` is exactly the already-established regularity for
elements with order supported outside `tau2(M)`.  In the remaining case a
prime-order element of the relevant centralizer lies in the normal selected
factor at that prime; cyclicity identifies its cyclic subgroup with the
factor's omega-one subgroup. -/
theorem semiregular_of_cyclic_regular_tau2_factors_12_12
    {G : Type u} [Group G] [Finite G]
    {M U U₂ U₃₁ : Subgroup G}
    (hU₂U : U₂ ≤ U)
    (hHallU₂ : IsHall (tau2Primes M) (U₂.subgroupOf U))
    (hU₃₁U : U₃₁ ≤ U)
    (hHallU₃₁ : IsHall (tau2Primes M)ᶜ (U₃₁.subgroupOf U))
    (hoff : ∀ {e : G}, e ∈ U → e ≠ 1 →
      IsPiNumber (tau2Primes M)ᶜ (orderOf e) →
        centralizerWithin (sigmaCore M) (Subgroup.zpowers e) = ⊥)
    (factors : CyclicRegularTau2FactorFamily M U U₂) :
    IsSemiregularConjugation (sigmaCore M)
      (selectedTau2CyclicJoin M U U₂ factors ⊔ U₃₁) := by
  classical
  let Z₂ : Subgroup G := selectedTau2CyclicJoin M U U₂ factors
  let U₀ : Subgroup G := Z₂ ⊔ U₃₁
  have hZ₂U₂ : Z₂ ≤ U₂ := selectedTau2CyclicJoin_le_U₂ factors
  have hZ₂U : Z₂ ≤ U := hZ₂U₂.trans hU₂U
  have hU₀U : U₀ ≤ U := sup_le hZ₂U hU₃₁U
  have hZ₂normalU : (Z₂.subgroupOf U).Normal :=
    selectedTau2CyclicJoin_normal_U hU₂U factors
  have hU₂pi : IsPiNumber (tau2Primes M) (Nat.card U₂) := by
    rw [← natCard_subgroupOf_eq hU₂U]
    exact hHallU₂.isPiNumber_card
  have hZ₂pi : IsPiNumber (tau2Primes M) (Nat.card Z₂) :=
    hU₂pi.of_dvd (Subgroup.card_dvd_of_le hZ₂U₂)
  have hU₃₁pi : IsPiNumber (tau2Primes M)ᶜ (Nat.card U₃₁) := by
    rw [← natCard_subgroupOf_eq hU₃₁U]
    exact hHallU₃₁.isPiNumber_card
  have hcop : Nat.Coprime (Nat.card Z₂) (Nat.card U₃₁) :=
    hZ₂pi.coprime_compl hU₃₁pi
  have hdis : Disjoint Z₂ U₃₁ :=
    Subgroup.disjoint_of_coprime_natCard hcop
  have hU₃₁normZ₂ :
      U₃₁ ≤ Subgroup.normalizer (Z₂ : Set G) :=
    hU₃₁U.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hZ₂U).mp
        hZ₂normalU)
  have hcomp :
      (Z₂.subgroupOf U₀).IsComplement'
        (U₃₁.subgroupOf U₀) :=
    subgroupOf_sup_isComplement_selected12 hU₃₁normZ₂ hdis
  have hZ₂U₀ : Z₂ ≤ U₀ := le_sup_left
  have hU₃₁U₀ : U₃₁ ≤ U₀ := le_sup_right
  have hZ₂normalU₀ : (Z₂.subgroupOf U₀).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact hU₀U.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hZ₂U).mp
        hZ₂normalU)
  have hHallZ₂ : IsHall (tau2Primes M) (Z₂.subgroupOf U₀) := by
    constructor
    · rw [natCard_subgroupOf_eq hZ₂U₀]
      exact hZ₂pi
    · rw [hcomp.symm.index_eq_card,
        natCard_subgroupOf_eq hU₃₁U₀]
      exact hU₃₁pi

  intro a ha x hax
  by_contra hx
  have haxComm : Commute (a : G) (x : G) := by
    rw [Commute]
    calc
      (a : G) * (x : G) =
          ((a : G) * (x : G) * (a : G)⁻¹) * (a : G) := by
            simp [mul_assoc]
      _ = (x : G) * (a : G) := by rw [hax]
  let Cx : Subgroup G :=
    centralizerWithin U₀ (Subgroup.zpowers (x : G))
  have haCx : (a : G) ∈ Cx := by
    refine ⟨a.property, ?_⟩
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact haxComm.symm.zpow_left n
  have hCxne : Cx ≠ ⊥ := by
    intro hCxbot
    apply ha
    apply Subtype.ext
    have haBot : (a : G) ∈ (⊥ : Subgroup G) := by
      rw [← hCxbot]
      exact haCx
    simpa using Subgroup.mem_bot.mp haBot
  have hCxcard : Nat.card Cx ≠ 1 :=
    (Cx.one_lt_card_iff_ne_bot.mpr hCxne).ne'
  obtain ⟨p, hp, hpCx⟩ := Nat.exists_prime_and_dvd hCxcard
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨eCx, heCxOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := Cx) p hpCx
  let e : G := eCx
  have heU₀ : e ∈ U₀ := eCx.property.1
  have heU : e ∈ U := hU₀U heU₀
  have heOrder : orderOf e = p := by
    exact (orderOf_injective Cx.subtype Cx.subtype_injective eCx).trans
      heCxOrder
  have heNe : e ≠ 1 := by
    intro heOne
    apply hp.ne_one
    rw [← heOrder, heOne, orderOf_one]
  have hex : Commute e (x : G) := by
    have hxe : Commute (x : G) e :=
      eCx.property.2 (x : G) (Subgroup.mem_zpowers (x : G))
    exact hxe.symm
  have hxCentE :
      (x : G) ∈
        centralizerWithin (sigmaCore M) (Subgroup.zpowers e) := by
    refine ⟨x.property, ?_⟩
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hex.zpow_left n

  by_cases hpTau : p ∈ tau2Primes M
  · have heZ₂ : e ∈ Z₂ :=
      mem_normal_isHall_of_isPiNumber_order_selected12
        hZ₂U₀ hZ₂normalU₀ hHallZ₂ heU₀
        (isPiNumber_order_eq_prime_selected12 hp hpTau heOrder)
    have heSelected :
        e ∈ selectedTau2CyclicFactor M U U₂ factors ⟨p, hp⟩ :=
      mem_selectedTau2CyclicFactor_of_order_eq_prime
        hU₂U factors hp heZ₂ heOrder
    let q : {q : ℕ // q.Prime} := ⟨p, hp⟩
    let P : Sylow p U₂ := selectedTau2Sylow U₂ q
    have hpZ₂ : p ∣ Nat.card Z₂ := by
      rw [← heOrder]
      exact Z₂.orderOf_dvd_natCard heZ₂
    have hpU₂ : p ∣ Nat.card U₂ :=
      hpZ₂.trans (Subgroup.card_dvd_of_le hZ₂U₂)
    have hpP : p ∣ Nat.card P := P.dvd_card_of_dvd_card hpU₂
    have hPne : (P : Subgroup U₂) ≠ ⊥ := by
      intro hPbot
      apply hp.not_dvd_one
      simpa [hPbot] using hpP
    let F : CyclicRegularTau2Factor M U U₂ P := factors p P hPne
    have hSelectedEq :
        selectedTau2CyclicFactor M U U₂ factors q = F.Z := by
      simpa [F] using selectedTau2CyclicFactor_eq factors q hPne
    have heFZ : e ∈ F.Z := by
      rw [← hSelectedEq]
      exact heSelected
    have hFZp : IsPGroup p F.Z :=
      (P.isPGroup'.map U₂.subtype).to_le F.Z_le_sylow
    have hFZne : F.Z ≠ ⊥ := by
      intro hFZbot
      apply heNe
      exact Subgroup.mem_bot.mp (hFZbot ▸ heFZ)
    letI : IsCyclic F.Z := F.Z_cyclic
    have hFZcard : Nat.card F.Z ≠ 1 := by
      intro hcard
      exact hFZne (Subgroup.card_eq_one.mp hcard)
    have hOmegaCard :
        Nat.card ((omegaOne p F.Z).map F.Z.subtype) = p := by
      rw [Subgroup.card_map_of_injective F.Z.subtype_injective]
      exact card_omegaOne_of_isCyclic_isPGroup hp hFZp hFZcard
    have hcycleOmega :
        Subgroup.zpowers e = (omegaOne p F.Z).map F.Z.subtype := by
      apply Subgroup.eq_of_le_of_card_ge
      · apply Subgroup.zpowers_le.mpr
        let eFZ : F.Z := ⟨e, heFZ⟩
        have heFZOrder : orderOf eFZ = p :=
          (orderOf_injective F.Z.subtype F.Z.subtype_injective eFZ).symm.trans
            heOrder
        have hePow : eFZ ^ p = 1 := by
          apply orderOf_dvd_iff_pow_eq_one.mp
          rw [heFZOrder]
        exact ⟨eFZ, mem_omegaOne_of_pow_eq_one p hePow, rfl⟩
      · rw [hOmegaCard, Nat.card_zpowers, heOrder]
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← F.omega_regular, ← hcycleOmega]
      exact hxCentE
    exact hx (Subtype.ext (by simpa using Subgroup.mem_bot.mp hxBot))
  · have hpCompl : p ∈ (tau2Primes M)ᶜ := hpTau
    have hcent := hoff heU heNe
      (isPiNumber_order_eq_prime_selected12 hp hpCompl heOrder)
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hcent]
      exact hxCentE
    exact hx (Subtype.ext (by simpa using Subgroup.mem_bot.mp hxBot))

/-! ## Final selected-Sylow assembly -/

/-- Choose the complementary `tau2(M)'`-Hall subgroup and assemble the
same-exponent semiregular subgroup used in clause (b) of Theorem 12.12. -/
theorem exists_tau2_selected_sylow_assembly_12_12
    {G : Type u} [Group G] [Finite G]
    {M U U₂ : Subgroup G}
    (hU₂U : U₂ ≤ U)
    (hHallU₂ : IsHall (tau2Primes M) (U₂.subgroupOf U))
    (hUsolvable : IsSolvable U)
    (hoff : ∀ {e : G}, e ∈ U → e ≠ 1 →
      IsPiNumber (tau2Primes M)ᶜ (orderOf e) →
        centralizerWithin (sigmaCore M) (Subgroup.zpowers e) = ⊥)
    (factors : CyclicRegularTau2FactorFamily M U U₂) :
    ∃ U₀ : Subgroup G,
      U₀ ≤ U ∧
      Monoid.exponent U₀ = Monoid.exponent U ∧
      IsSemiregularConjugation (sigmaCore M) U₀ := by
  classical
  obtain ⟨U₃₁, hU₃₁U, hHallU₃₁⟩ :=
    exists_ambient_isHall_of_isSolvable
      hUsolvable (tau2Primes M)ᶜ
  let Z₂ : Subgroup G := selectedTau2CyclicJoin M U U₂ factors
  let U₀ : Subgroup G := Z₂ ⊔ U₃₁
  have hZ₂U : Z₂ ≤ U := selectedTau2CyclicJoin_le_U hU₂U factors
  have hU₀U : U₀ ≤ U := sup_le hZ₂U hU₃₁U
  have hExp : Monoid.exponent U₀ = Monoid.exponent U := by
    exact exponent_eq_of_selected_sylow_factors_12_12
      hU₂U hHallU₂ hU₃₁U hHallU₃₁ factors
  have hSemiregular :
      IsSemiregularConjugation (sigmaCore M) U₀ := by
    exact semiregular_of_cyclic_regular_tau2_factors_12_12
      hU₂U hHallU₂ hU₃₁U hHallU₃₁ hoff factors
  exact ⟨U₀, hU₀U, hExp, hSemiregular⟩

end

end Submission.OddOrder.BG.Section12
