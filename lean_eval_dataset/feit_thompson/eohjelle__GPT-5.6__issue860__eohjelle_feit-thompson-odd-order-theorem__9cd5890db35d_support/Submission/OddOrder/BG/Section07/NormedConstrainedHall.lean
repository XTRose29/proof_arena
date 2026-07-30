import Submission.OddOrder.BG.Section07.CentralCoreAction
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Bender--Glauberman, Section 7: the centralizer core is Hall

This file ports the observation between Hypothesis 7.1 and Lemma 7.1 in
`BGsection7.v`.  If `pi` is the set of prime divisors of `|A|`, then
`O_{pi'}(C_G(A))` is a `pi'`-Hall subgroup of `C_G(A)`.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The join of two normal `pi`-subgroups is again a `pi`-subgroup. -/
private theorem isPiNumber_card_sup_of_normal_left {pi : Set ℕ}
    {H K : Subgroup G} (hHnormal : H.Normal)
    (hH : IsPiNumber pi (Nat.card H))
    (hK : IsPiNumber pi (Nat.card K)) :
    IsPiNumber pi (Nat.card (H ⊔ K : Subgroup G)) := by
  letI : H.Normal := hHnormal
  have hrel : H.relIndex (H ⊔ K) = H.relIndex K :=
    Subgroup.relIndex_sup_left K H
  have hsubcard : Nat.card (H.subgroupOf (H ⊔ K)) = Nat.card H :=
    natCard_subgroupOf_eq le_sup_left
  rw [← (H.subgroupOf (H ⊔ K)).card_mul_index, hsubcard]
  change IsPiNumber pi (Nat.card H * H.relIndex (H ⊔ K))
  rw [hrel]
  exact hH.mul (hK.of_dvd (Subgroup.relIndex_dvd_card H K))

/-- The prime-set core has `pi`-number cardinality. -/
theorem primeSetCore_isPiNumber (pi : Set ℕ) (X : Subgroup G) :
    IsPiNumber pi (Nat.card (primeSetCore pi X)) := by
  classical
  let Good : Subgroup G → Prop := fun K =>
    K ≤ X ∧ (K.subgroupOf X).Normal ∧ IsPiNumber pi (Nat.card K)
  have hbot : Good (⊥ : Subgroup G) := by
    refine ⟨bot_le, ?_, ?_⟩
    · simpa using (inferInstance : (⊥ : Subgroup X).Normal)
    · simpa using (IsPiNumber.one (pi := pi))
  obtain ⟨M, _, hM, hMmax⟩ :=
    Finite.exists_le_maximal (p := Good) hbot
  have hgreatest : ∀ P : Subgroup G, Good P → P ≤ M := by
    intro P hP
    have hsupLe : M ⊔ P ≤ X := sup_le hM.1 hP.1
    have hsupNormal : ((M ⊔ P).subgroupOf X).Normal := by
      rw [Subgroup.subgroupOf_sup hM.1 hP.1]
      letI : (M.subgroupOf X).Normal := hM.2.1
      letI : (P.subgroupOf X).Normal := hP.2.1
      infer_instance
    have hMsubPi : IsPiNumber pi (Nat.card (M.subgroupOf X)) := by
      simpa only [natCard_subgroupOf_eq hM.1] using hM.2.2
    have hPsubPi : IsPiNumber pi (Nat.card (P.subgroupOf X)) := by
      simpa only [natCard_subgroupOf_eq hP.1] using hP.2.2
    have hsupPi : IsPiNumber pi (Nat.card (M ⊔ P : Subgroup G)) := by
      have h := isPiNumber_card_sup_of_normal_left
        (G := X) hM.2.1 hMsubPi hPsubPi
      rw [← Subgroup.subgroupOf_sup hM.1 hP.1,
        natCard_subgroupOf_eq hsupLe] at h
      exact h
    have hGoodSup : Good (M ⊔ P) :=
      ⟨hsupLe, hsupNormal, hsupPi⟩
    exact le_sup_right.trans (hMmax hGoodSup le_sup_left)
  have hcoreEq : primeSetCore pi X = M := by
    apply le_antisymm
    · rw [primeSetCore]
      exact sSup_le fun P hP => hgreatest P hP
    · rw [primeSetCore]
      exact le_sSup hM
  rw [hcoreEq]
  exact hM.2.2

/-- A finite `p`-subgroup has prime support contained in any set containing
`p`. -/
private theorem isPiNumber_card_of_isPGroup {p : ℕ} [Fact p.Prime]
    {pi : Set ℕ} {P : Subgroup G} (hP : IsPGroup p P) (hp : p ∈ pi) :
    IsPiNumber pi (Nat.card P) := by
  obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp hP
  rw [hcard]
  intro q hq hqdiv
  have hqp : q = p :=
    Nat.prime_eq_prime_of_dvd_pow hq Fact.out hqdiv
  simpa [hqp] using hp

/-- The observation preceding Bender--Glauberman Lemma 7.1: under
Hypothesis 7.1, `O_{pi(A)'}(C_G(A))` is a `pi(A)'`-Hall subgroup of
`C_G(A)`.

MathComp statement:
`pi^'.-Hall('C(A)) ('O_pi^'('C(A)))`.
-/
theorem normed_constrained_Hall [IsMinSimpleOddGroup G] (A : Subgroup G)
    (cstrA : NormedConstrained A) :
    IsHall (primeSupport (Nat.card A))ᶜ
      ((centralPrimeComplementCore A).subgroupOf
        (Subgroup.centralizer (A : Set G))) := by
  let pi : Set ℕ := primeSupport (Nat.card A)
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  let K : Subgroup G := centralPrimeComplementCore A
  have hKC : K ≤ C := by
    simpa [K, C, centralPrimeComplementCore] using
      (primeSetCore_le piᶜ C)
  constructor
  · rw [natCard_subgroupOf_eq hKC]
    simpa [K, C, pi, centralPrimeComplementCore] using
      (primeSetCore_isPiNumber piᶜ C)
  · intro p hpPrime hpIndex hpPiConcrete'
    have hpPi' : p ∈ piᶜ := by
      simpa [pi] using hpPiConcrete'
    letI : Fact p.Prime := ⟨hpPrime⟩
    let P : Sylow p C := default
    let PG : Subgroup G := (P : Subgroup C).map C.subtype
    have hPGC : PG ≤ C := by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact y.2
    have hPGp : IsPGroup p PG :=
      P.isPGroup'.map C.subtype
    have hPGpi' : IsPiNumber piᶜ (Nat.card PG) :=
      isPiNumber_card_of_isPGroup hPGp hpPi'
    have hAC : A ≤ Subgroup.centralizer (C : Set G) := by
      apply Subgroup.le_centralizer_iff.mpr
      simpa [C]
    have hAPGnorm : A ≤ Subgroup.normalizer (PG : Set G) :=
      hAC.trans ((Subgroup.centralizer_le hPGC).trans
        (Subgroup.centralizer_le_normalizer (PG : Set G)))
    let J : Subgroup G := A ⊔ C
    have hJnormA : J ≤ Subgroup.normalizer (A : Set G) := by
      exact sup_le Subgroup.le_normalizer
        (by simpa [C] using
          (Subgroup.centralizer_le_normalizer (A : Set G)))
    have hJproper : J < ⊤ :=
      lt_of_le_of_lt hJnormA
        (mFT_norm_proper A cstrA.nontrivial cstrA.proper)
    have hPGJ : PG ≤ J := hPGC.trans le_sup_right
    have hPGcoreJ : PG ≤ primeSetCore piᶜ J :=
      cstrA.constrained J PG le_sup_left hJproper
        ⟨hPGJ, hPGpi', hAPGnorm⟩
    let L : Subgroup G := primeSetCore piᶜ J
    let R : Subgroup G := L ⊓ C
    have hCJ : C ≤ J := le_sup_right
    have hRnormal : (R.subgroupOf C).Normal := by
      letI : (L.subgroupOf J).Normal := by
        simpa [L] using primeSetCore_normal piᶜ J
      have hnormal :=
        Subgroup.inf_subgroupOf_inf_normal_of_left (A' := L) (A := J) C
      change ((L ⊓ C).subgroupOf C).Normal
      rw [inf_eq_right.mpr hCJ] at hnormal
      exact hnormal
    have hRpi' : IsPiNumber piᶜ (Nat.card R) := by
      apply (primeSetCore_isPiNumber piᶜ J).of_dvd
      exact Subgroup.card_dvd_of_le inf_le_left
    have hRleK : R ≤ K := by
      change R ≤ primeSetCore piᶜ C
      rw [primeSetCore]
      exact le_sSup ⟨inf_le_right, hRnormal, hRpi'⟩
    have hPGK : PG ≤ K := by
      intro x hx
      apply hRleK
      exact ⟨by simpa [L] using hPGcoreJ hx, hPGC hx⟩
    have hPK : (P : Subgroup C) ≤ K.subgroupOf C := by
      intro x hx
      change (x : G) ∈ K
      apply hPGK
      exact Subgroup.mem_map_of_mem C.subtype hx
    exact P.not_dvd_index
      (hpIndex.trans (Subgroup.index_dvd_of_le hPK))

end Submission.OddOrder.BG.Section07
