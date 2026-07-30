import Submission.OddOrder.BG.Section07.NormedConstrainedRankTwoTrans
import Submission.OddOrder.BG.Section07.PrimeSetCoreFunctorial
import Submission.OddOrder.BG.Section07.NormedQuotientFixedPoint
import Submission.OddOrder.BG.Section07.NormedTransitiveConsequences
import Submission.OddOrder.MathlibSupport.SubnormalMaximalNormal
import Submission.OddOrder.MathlibSupport.CoprimeHallConjugatorAdjustment

/-!
# Bender--Glauberman, Section 7: transitivity for subnormal supersets

This file ports Bender--Glauberman Theorem 7.4.  Transitivity for the
prime-complement core of `C_G(A)` ascends along a subnormal `pi(A)`-subgroup
`P`; the acting group at the top is the prime-complement core of `C_G(P)`.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport
open scoped Pointwise commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]

/-- Cardinal prime support of a finite `p`-group. -/
private theorem isPiNumber_singleton_of_isPGroup {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) :
    IsPiNumber ({p} : Set ℕ) (Nat.card P) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn]
  intro r hr hrdiv
  have hrp : r = p :=
    Nat.prime_eq_prime_of_dvd_pow hr Fact.out hrdiv
  simp [hrp]

/-- Bender--Glauberman Theorem 7.4. -/
theorem normed_trans_superset [IsMinSimpleOddGroup G]
    {q : ℕ} (A P : Subgroup G)
    (cstrA : NormedConstrained A)
    (hqA : q ∉ primeSupport (Nat.card A))
    (hAP : A ≤ P)
    (hsnAP : (A.subgroupOf P).IsSubnormal)
    (hPpi : IsPiNumber (primeSupport (Nat.card A)) (Nat.card P))
    (htransA : ∀ Q₁ Q₂ : Subgroup G,
      Q₁ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      ∃ k : G, k ∈ centralPrimeComplementCore A ∧
        Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom) :
    let pi := primeSupport (Nat.card A)
    let K := centralPrimeComplementCore A
    let KP := primeSetCore piᶜ (Subgroup.centralizer (P : Set G))
    centralizerWithin K P = KP ∧
      (∀ Q₁ Q₂ : Subgroup G,
        Q₁ ∈ max_normed_pgroups (P : Set G) ({q} : Set ℕ) →
        Q₂ ∈ max_normed_pgroups (P : Set G) ({q} : Set ℕ) →
        ∃ k : G, k ∈ KP ∧ Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom) ∧
      max_normed_pgroups (P : Set G) ({q} : Set ℕ) ⊆
        max_normed_pgroups (A : Set G) ({q} : Set ℕ) ∧
      ∀ Q : Subgroup G,
        Q ∈ max_normed_pgroups (P : Set G) ({q} : Set ℕ) →
        P ⊓ ⁅Subgroup.normalizer (P : Set G), Subgroup.normalizer (P : Set G)⁆ ≤
          ⁅Subgroup.normalizer (Q : Set G), Subgroup.normalizer (Q : Set G)⁆ ∧
        (Subgroup.normalizer (P : Set G) : Set G) =
          (centralizerWithin K P : Set G) *
            ((Subgroup.normalizer (P : Set G) ⊓
              Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) := by
  classical
  let pi : Set ℕ := primeSupport (Nat.card A)
  let K : Subgroup G := centralPrimeComplementCore A
  let Core : Subgroup G → Subgroup G := fun B ↦
    primeSetCore piᶜ (Subgroup.centralizer (B : Set G))
  let Claim : ℕ → Prop := fun n ↦
    ∀ B : Subgroup G,
      Nat.card B = n →
      A ≤ B →
      (A.subgroupOf B).IsSubnormal →
      IsPiNumber pi (Nat.card B) →
      (∀ Q₁ Q₂ : Subgroup G,
        Q₁ ∈ max_normed_pgroups (B : Set G) ({q} : Set ℕ) →
        Q₂ ∈ max_normed_pgroups (B : Set G) ({q} : Set ℕ) →
        ∃ k : G, k ∈ Core B ∧
          Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom) ∧
      max_normed_pgroups (B : Set G) ({q} : Set ℕ) ⊆
        max_normed_pgroups (A : Set G) ({q} : Set ℕ)

  have hClaim : ∀ n, Claim n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [Claim]
      intro B hcard hAB hsnAB hBpi
      by_cases hBA : B = A
      · subst B
        constructor
        · simpa [Core, pi, centralPrimeComplementCore] using htransA
        · exact fun _ hQ ↦ hQ
      obtain ⟨D, hAD, hDB, hsnAD, hDmax⟩ :=
        exists_maximalProperNormal_intermediate_of_isSubnormal
          hAB hsnAB (fun h ↦ hBA h.symm)
      have hDcard : Nat.card D < n := by
        rw [← hcard]
        exact natCard_subgroup_lt_of_lt hDB
      have hDpi : IsPiNumber pi (Nat.card D) :=
        hBpi.of_dvd (Subgroup.card_dvd_of_le hDB.le)
      have hIH := ih (Nat.card D) hDcard D rfl hAD hsnAD hDpi
      change
        (∀ Q₁ Q₂ : Subgroup G,
          Q₁ ∈ max_normed_pgroups (D : Set G) ({q} : Set ℕ) →
          Q₂ ∈ max_normed_pgroups (D : Set G) ({q} : Set ℕ) →
          ∃ k : G, k ∈ Core D ∧
            Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom) ∧
        max_normed_pgroups (D : Set G) ({q} : Set ℕ) ⊆
          max_normed_pgroups (A : Set G) ({q} : Set ℕ) at hIH
      rcases hIH with ⟨htransD, hincDA⟩

      let DB : Subgroup B := D.subgroupOf B
      letI : DB.Normal := by simpa [DB] using hDmax.normal
      have hDBne : DB ≠ ⊥ := by
        intro hbot
        apply cstrA.nontrivial
        apply eq_bot_iff.mpr
        intro a ha
        let aB : B := ⟨a, hDB.le (hAD ha)⟩
        have haDB : aB ∈ DB := hAD ha
        rw [hbot] at haDB
        apply Subgroup.mem_bot.mpr
        exact congrArg Subtype.val (Subgroup.mem_bot.mp haDB)
      letI : IsSimpleGroup (B ⧸ DB) := hDmax.isSimpleGroup_quotient
      letI : IsSolvable (B ⧸ DB) := mFT_quo_sol B DB hDBne
      letI : CommGroup (B ⧸ DB) :=
        { (inferInstance : Group (B ⧸ DB)) with
          mul_comm := IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance }
      let p : ℕ := Nat.card (B ⧸ DB)
      have hp : p.Prime := by
        dsimp [p]
        exact IsSimpleGroup.prime_card
      letI : Fact p.Prime := ⟨hp⟩
      have hquotp : IsPGroup p (B ⧸ DB) := by
        apply IsPGroup.iff_card.mpr
        exact ⟨1, by simp [p]⟩
      have hquotPi : IsPiNumber pi (Nat.card (B ⧸ DB)) :=
        hBpi.of_dvd DB.card_quotient_dvd_card
      have hpPi : p ∈ pi := by
        exact hquotPi hp (by simp [p])

      have hCoreDnormD : Core D ≤ Subgroup.normalizer (D : Set G) := by
        exact (primeSetCore_le piᶜ (Subgroup.centralizer (D : Set G))).trans
          (Subgroup.centralizer_le_normalizer (D : Set G))
      have hfamilyDvd :
          Nat.card {Q : Subgroup G //
            Q ∈ max_normed_pgroups (D : Set G) ({q} : Set ℕ)} ∣
            Nat.card (Core D) :=
        natCard_max_normed_pgroups_dvd_of_transitive
          D (Core D) hCoreDnormD htransD
      have hfamilyPi' : IsPiNumber piᶜ
          (Nat.card {Q : Subgroup G //
            Q ∈ max_normed_pgroups (D : Set G) ({q} : Set ℕ)}) :=
        (primeSetCore_isPiNumber piᶜ
          (Subgroup.centralizer (D : Set G))).of_dvd hfamilyDvd
      have hpNotDvd : ¬ p ∣
          Nat.card {Q : Subgroup G //
            Q ∈ max_normed_pgroups (D : Set G) ({q} : Set ℕ)} := by
        intro hpdiv
        exact (hfamilyPi' hp hpdiv) hpPi
      obtain ⟨Q, hQD, hBnormQ⟩ :=
        exists_max_normed_normalized_of_quotient_isPGroup
          D B hDB.le hquotp hpNotDvd
      have hQdata := mem_max_normed hQD
      obtain ⟨Q₀, hQ₀B, hQQ₀⟩ :=
        max_normed_exists (B : Set G) ({q} : Set ℕ) Q
          hQdata.1 hBnormQ

      by_cases hQ₀bot : Q₀ = ⊥
      · have hQbot : Q = ⊥ := by
          apply le_antisymm
          · simpa [hQ₀bot] using hQQ₀
          · exact bot_le
        have hbotD : (⊥ : Subgroup G) ∈
            max_normed_pgroups (D : Set G) ({q} : Set ℕ) := by
          simpa [hQbot] using hQD
        have hbotA : (⊥ : Subgroup G) ∈
            max_normed_pgroups (A : Set G) ({q} : Set ℕ) :=
          hincDA hbotD
        have hbotB : (⊥ : Subgroup G) ∈
            max_normed_pgroups (B : Set G) ({q} : Set ℕ) := by
          simpa [hQ₀bot] using hQ₀B
        have huniqB := trivg_max_norm B ({q} : Set ℕ) hbotB
        constructor
        · intro Q₁ Q₂ hQ₁ hQ₂
          have hQ₁bot : Q₁ = ⊥ := by
            apply Set.mem_singleton_iff.mp
            rw [← huniqB]
            exact hQ₁
          have hQ₂bot : Q₂ = ⊥ := by
            apply Set.mem_singleton_iff.mp
            rw [← huniqB]
            exact hQ₂
          subst Q₁
          subst Q₂
          exact ⟨1, (Core B).one_mem, by simp⟩
        · intro R hRB
          have hRbot : R = ⊥ := by
            apply Set.mem_singleton_iff.mp
            rw [← huniqB]
            exact hRB
          simpa [hRbot] using hbotA

      have hNontrivialMaxB : ∀ R : Subgroup G,
          R ∈ max_normed_pgroups (B : Set G) ({q} : Set ℕ) →
          R ≠ ⊥ := by
        intro R hRB hRbot
        have hbotB : (⊥ : Subgroup G) ∈
            max_normed_pgroups (B : Set G) ({q} : Set ℕ) := by
          simpa [hRbot] using hRB
        have hQ₀mem : Q₀ ∈ ({⊥} : Set (Subgroup G)) := by
          rw [← trivg_max_norm B ({q} : Set ℕ) hbotB]
          exact hQ₀B
        exact hQ₀bot (Set.mem_singleton_iff.mp hQ₀mem)

      have hincBD : max_normed_pgroups (B : Set G) ({q} : Set ℕ) ⊆
          max_normed_pgroups (D : Set G) ({q} : Set ℕ) := by
        intro Q₁ hQ₁B
        have hQ₁data := mem_max_normed hQ₁B
        have hQ₁ne : Q₁ ≠ ⊥ := hNontrivialMaxB Q₁ hQ₁B
        letI : Fact q.Prime :=
          ⟨prime_of_isPiNumber_singleton_of_ne_bot
            hQ₁data.1 hQ₁ne⟩
        have hQ₁p : IsPGroup q Q₁ :=
          isPGroup_of_isPiNumber_singleton hQ₁data.1
        have hNQ₁proper : Subgroup.normalizer (Q₁ : Set G) < ⊤ :=
          mFT_norm_proper Q₁ hQ₁ne (mFT_pgroup_proper Q₁ hQ₁p)
        have hANQ₁ : A ≤ Subgroup.normalizer (Q₁ : Set G) :=
          hAB.trans hQ₁data.2
        obtain ⟨Q₂, hQ₂D, hQ₁Q₂⟩ :=
          max_normed_exists (D : Set G) ({q} : Set ℕ) Q₁
            hQ₁data.1 (hDB.le.trans hQ₁data.2)
        have hQ₂data := mem_max_normed hQ₂D
        suffices hQ₁eqQ₂ : Q₁ = Q₂ by
          simpa [hQ₁eqQ₂] using hQ₂D
        by_contra hQ₁neQ₂
        have hQ₁ltQ₂ : Q₁ < Q₂ :=
          lt_of_le_of_ne hQ₁Q₂ hQ₁neQ₂
        let Y : Subgroup G :=
          Q₂ ⊓ Subgroup.normalizer (Q₁ : Set G)
        have hQ₁Y : Q₁ ≤ Y :=
          le_inf hQ₁Q₂ Subgroup.le_normalizer
        have hYq : IsPiNumber ({q} : Set ℕ) (Nat.card Y) :=
          hQ₂data.1.of_dvd (Subgroup.card_dvd_of_le inf_le_left)
        have hYpi' : IsPiNumber piᶜ (Nat.card Y) := by
          apply hYq.mono
          intro r hr
          have hrq : r = q := Set.mem_singleton_iff.mp hr
          subst r
          simpa [pi] using hqA
        have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
          exact (le_inf
            (hAD.trans hQ₂data.2)
            (hANQ₁.trans Subgroup.le_normalizer)).trans
              Subgroup.inf_normalizer_le_normalizer_inf
        have hYCore : Y ≤
            primeSetCore piᶜ
              (Subgroup.normalizer (Q₁ : Set G)) := by
          apply cstrA.constrained
            (Subgroup.normalizer (Q₁ : Set G)) Y
            hANQ₁ hNQ₁proper
          exact ⟨inf_le_right, hYpi', hAY⟩
        let L : Subgroup G :=
          primeSetCore piᶜ
            (Subgroup.normalizer (Q₁ : Set G))
        have hQ₁L : Q₁ ≤ L := hQ₁Y.trans hYCore
        have hBL : B ≤ Subgroup.normalizer (L : Set G) := by
          apply le_normalizer_primeSetCore_of_le_normalizer
          exact hQ₁data.2.trans Subgroup.le_normalizer
        have hLpi' : IsPiNumber piᶜ (Nat.card L) :=
          primeSetCore_isPiNumber piᶜ
            (Subgroup.normalizer (Q₁ : Set G))
        have hcopLB : (Nat.card L).Coprime (Nat.card B) := by
          apply Nat.coprime_of_dvd
          intro r hr hrL hrB
          exact (hLpi' hr hrL) (hBpi hr hrB)
        have hsolL : IsSolvable L := by
          have hLle : L ≤ Subgroup.normalizer (Q₁ : Set G) :=
            primeSetCore_le piᶜ
              (Subgroup.normalizer (Q₁ : Set G))
          letI : IsSolvable (Subgroup.normalizer (Q₁ : Set G)) :=
            mFT_sol hNQ₁proper
          exact solvable_of_solvable_injective
            (f := Subgroup.inclusion hLle)
            (Subgroup.inclusion_injective hLle)
        obtain ⟨R, hBnormR, hQ₁R⟩ :=
          exists_normalized_sylow_ge_of_coprime_of_isSolvable_of_isPiNumber
            hBL hcopLB hsolL hQ₁L hQ₁data.1 hQ₁ne hQ₁data.2
        let RG : Subgroup G := (R : Subgroup L).map L.subtype
        have hRGq : IsPiNumber ({q} : Set ℕ) (Nat.card RG) :=
          isPiNumber_singleton_of_isPGroup (R.isPGroup'.map L.subtype)
        have hRGeq : RG = Q₁ := by
          apply le_antisymm
          · exact hQ₁B.2 ⟨hRGq, hBnormR⟩ hQ₁R
          · exact hQ₁R
        let YL : Subgroup L := Y.subgroupOf L
        have hYLq : IsPGroup q YL :=
          (isPGroup_of_isPiNumber_singleton hYq).of_equiv
            (Subgroup.subgroupOfEquivOfLe hYCore).symm
        have hRYL : (R : Subgroup L) ≤ YL := by
          intro r hrR
          have hrRG : ((r : L) : G) ∈ RG := ⟨r, hrR, rfl⟩
          rw [hRGeq] at hrRG
          exact hQ₁Y hrRG
        have hYLeq : YL = (R : Subgroup L) :=
          R.is_maximal' hYLq hRYL
        have hYeq : Y = Q₁ := by
          calc
            Y = YL.map L.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hYCore).symm
            _ = (R : Subgroup L).map L.subtype := by rw [hYLeq]
            _ = Q₁ := hRGeq
        have hQ₁ltY : Q₁ < Y := by
          exact lt_inf_normalizer_of_isPGroup
            (isPGroup_of_isPiNumber_singleton hQ₂data.1)
            hQ₁ltQ₂
        exact hQ₁ltY.ne hYeq.symm

      have hPnormD : B ≤ Subgroup.normalizer (D : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hDB.le).mp hDmax.normal
      have hPnormCD : B ≤
          Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) := by
        have hCDN : Subgroup.centralizer (D : Set G) ≤
            Subgroup.normalizer (D : Set G) :=
          Subgroup.centralizer_le_normalizer (D : Set G)
        have hNnormCD : Subgroup.normalizer (D : Set G) ≤
            Subgroup.normalizer
              (Subgroup.centralizer (D : Set G) : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hCDN).mp
            (Subgroup.normal_subgroupOf_centralizer_normalizer (D : Set G))
        exact hPnormD.trans hNnormCD
      have hPnormCoreD : B ≤ Subgroup.normalizer (Core D : Set G) := by
        exact le_normalizer_primeSetCore_of_le_normalizer piᶜ hPnormCD
      have hCoreDpi' : IsPiNumber piᶜ (Nat.card (Core D)) :=
        primeSetCore_isPiNumber piᶜ
          (Subgroup.centralizer (D : Set G))
      have hcoreCent : centralizerWithin (Core D) B = Core B := by
        have hdefD :=
          centralizerWithin_centralPrimeComplementCore_eq_primeSetCore
            A D cstrA hAD
        have hdefB :=
          centralizerWithin_centralPrimeComplementCore_eq_primeSetCore
            A B cstrA hAB
        calc
          centralizerWithin (Core D) B =
              centralizerWithin (centralizerWithin K D) B := by
            rw [hdefD]
          _ = centralizerWithin K B := by
            dsimp only [centralizerWithin]
            rw [inf_assoc,
              inf_eq_right.mpr (Subgroup.centralizer_le hDB.le)]
          _ = Core B := by
            simpa [Core, K] using hdefB
      have htransB : ∀ Q₁ Q₂ : Subgroup G,
          Q₁ ∈ max_normed_pgroups (B : Set G) ({q} : Set ℕ) →
          Q₂ ∈ max_normed_pgroups (B : Set G) ({q} : Set ℕ) →
          ∃ k : G, k ∈ Core B ∧
            Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom := by
        intro Q₁ Q₂ hQ₁B hQ₂B
        obtain ⟨k, hk, hQ₂⟩ :=
          htransD Q₁ Q₂ (hincBD hQ₁B) (hincBD hQ₂B)
        have hQ₁norm := (mem_max_normed hQ₁B).2
        have hQ₂data := mem_max_normed hQ₂B
        have hQ₂ne := hNontrivialMaxB Q₂ hQ₂B
        letI : Fact q.Prime :=
          ⟨prime_of_isPiNumber_singleton_of_ne_bot
            hQ₂data.1 hQ₂ne⟩
        have hQ₂p : IsPGroup q Q₂ :=
          isPGroup_of_isPiNumber_singleton hQ₂data.1
        have hsol : IsSolvable
            (((Core D ⊔ B) ⊓
              Subgroup.normalizer (Q₂ : Set G) : Subgroup G)) := by
          apply mFT_sol
          exact lt_of_le_of_lt inf_le_right
            (mFT_norm_proper Q₂ hQ₂ne
              (mFT_pgroup_proper Q₂ hQ₂p))
        obtain ⟨x, hx, hQ₂x⟩ :=
          exists_centralizerWithin_conjugator_of_coprime_join
            hPnormCoreD hCoreDpi' hBpi hQ₁norm hQ₂data.2
              hsol hk hQ₂
        refine ⟨x, ?_, hQ₂x⟩
        rw [hcoreCent] at hx
        exact hx
      exact ⟨htransB, fun _ hQB ↦ hincDA (hincBD hQB)⟩

  have hPI := hClaim (Nat.card P) P rfl hAP hsnAP hPpi
  change
    (∀ Q₁ Q₂ : Subgroup G,
      Q₁ ∈ max_normed_pgroups (P : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (P : Set G) ({q} : Set ℕ) →
      ∃ k : G, k ∈ Core P ∧
        Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom) ∧
    max_normed_pgroups (P : Set G) ({q} : Set ℕ) ⊆
      max_normed_pgroups (A : Set G) ({q} : Set ℕ) at hPI
  rcases hPI with ⟨htransP, hincPA⟩
  have hdefP : centralizerWithin K P = Core P := by
    simpa [K, Core] using
      (centralizerWithin_centralPrimeComplementCore_eq_primeSetCore
        A P cstrA hAP)
  refine ⟨hdefP, htransP, hincPA, ?_⟩
  intro Q hQP
  have hCorePle : Core P ≤ Subgroup.normalizer (P : Set G) :=
    (primeSetCore_le piᶜ (Subgroup.centralizer (P : Set G))).trans
      (Subgroup.centralizer_le_normalizer (P : Set G))
  have hcons := normed_transitive_normalizer_consequences
    (pi := pi) (Core P) P hCorePle
      (primeSetCore_centralizer_normal_in_normalizer piᶜ P)
      (primeSetCore_isPiNumber piᶜ
        (Subgroup.centralizer (P : Set G)))
      hPpi htransP hQP
  refine ⟨hcons.1, ?_⟩
  rw [hdefP]
  exact hcons.2

end Submission.OddOrder.BG.Section07
