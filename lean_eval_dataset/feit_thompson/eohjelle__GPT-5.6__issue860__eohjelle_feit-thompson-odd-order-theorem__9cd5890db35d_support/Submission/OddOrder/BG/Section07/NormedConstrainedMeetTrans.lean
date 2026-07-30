import Submission.OddOrder.BG.Section07.NormedConstrainedHall
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowConjugacy
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension
import Submission.OddOrder.MathlibSupport.PGroupNormalizer
import Submission.OddOrder.MathlibSupport.Solvability
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Bender--Glauberman, Section 7: constrained intersection transitivity

This file ports Bender--Glauberman Lemma 7.1,
`normed_constrained_meet_trans`.  Two maximal `q`-subgroups normalized by
`A`, each meeting the same proper overgroup of `A` nontrivially, are
conjugate by the prime-complement core of `C_G(A)`.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- Cardinal prime support of a finite `p`-group. -/
private theorem isPiNumber_singleton_of_isPGroup {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) :
    IsPiNumber ({p} : Set ℕ) (Nat.card P) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn]
  intro q hq hqdiv
  have hqp : q = p :=
    Nat.prime_eq_prime_of_dvd_pow hq Fact.out hqdiv
  simpa [hqp]

/-- An element of a `pi`-number subgroup which also lies in the ambient
group of a normal `pi`-Hall subgroup belongs to that Hall subgroup. -/
private theorem mem_normal_isHall_of_mem_of_isPiNumber
    {pi : Set ℕ} {C K L : Subgroup G}
    (hKC : K ≤ C) (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    (hLpi : IsPiNumber pi (Nat.card L))
    {x : G} (hxC : x ∈ C) (hxL : x ∈ L) : x ∈ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa [KC] using hKnormal
  have hcop : (Nat.card L).Coprime KC.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    have hpPi : p ∈ pi := hLpi hp hpL
    have hpNotPi : p ∈ piᶜ := hKHall.isPiNumber_index hp hpIndex
    exact hpNotPi hpPi
  let xC : C := ⟨x, hxC⟩
  let qC : C →* C ⧸ KC := QuotientGroup.mk' KC
  have horderL : orderOf (qC xC) ∣ Nat.card L := by
    exact (orderOf_map_dvd qC xC).trans (by
      simpa [xC] using L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (qC xC) ∣ KC.index := by
    simpa only [KC.index_eq_card] using orderOf_dvd_natCard (qC xC)
  have horderOne : orderOf (qC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp horderOne
  have hxKC : xC ∈ KC := by
    exact (QuotientGroup.eq_one_iff xC).mp (by simpa [qC] using hqOne)
  exact hxKC

/-- The internal `MulAut.conj`-oriented form of Bender--Glauberman Lemma 7.1. -/
private theorem normed_constrained_meet_trans_mulAutConj [IsMinSimpleOddGroup G]
    {q : ℕ} (A Q₁ Q₂ H : Subgroup G)
    (cstrA : NormedConstrained A)
    (hqA : q ∉ primeSupport (Nat.card A))
    (hAH : A ≤ H) (hHproper : H < ⊤)
    (hQ₁max : Q₁ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ))
    (hQ₂max : Q₂ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ))
    (hQ₁Hne : Q₁ ⊓ H ≠ ⊥) (hQ₂Hne : Q₂ ⊓ H ≠ ⊥) :
    ∃ k : G, k ∈ centralPrimeComplementCore A ∧
      Q₂ = Q₁.map (MulAut.conj k).toMonoidHom := by
  classical
  have hQ₁data := mem_max_normed hQ₁max
  have hQ₁ne : Q₁ ≠ ⊥ := by
    intro hbot
    apply hQ₁Hne
    rw [hbot, bot_inf_eq]
  letI : Fact q.Prime :=
    ⟨prime_of_isPiNumber_singleton_of_ne_bot hQ₁data.1 hQ₁ne⟩
  let Measure : Subgroup G → Subgroup G → ℕ := fun X Y ↦
    Nat.card G - Nat.card (X ⊓ Y : Subgroup G)
  let Claim : ℕ → Prop := fun n ↦
    ∀ (H Q₁ Q₂ : Subgroup G),
      Measure Q₁ Q₂ = n →
      A ≤ H → H < ⊤ →
      Q₁ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      Q₁ ⊓ H ≠ ⊥ → Q₂ ⊓ H ≠ ⊥ →
      ∃ k : G, k ∈ centralPrimeComplementCore A ∧
        Q₂ = Q₁.map (MulAut.conj k).toMonoidHom
  have hClaim : ∀ n, Claim n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H Q₁ Q₂ hmeasure hAH hHproper
        hQ₁max hQ₂max hQ₁Hne hQ₂Hne
      let I : Subgroup G := Q₁ ⊓ Q₂
      have hQ₁data := mem_max_normed hQ₁max
      have hQ₂data := mem_max_normed hQ₂max
      have hQ₁p : IsPGroup q Q₁ :=
        isPGroup_of_isPiNumber_singleton hQ₁data.1
      have hQ₂p : IsPGroup q Q₂ :=
        isPGroup_of_isPiNumber_singleton hQ₂data.1
      have hIp : IsPGroup q I := hQ₁p.to_le inf_le_left
      have hIproper : I < ⊤ := mFT_pgroup_proper I hIp
      have run : ∀ (H : Subgroup G),
          A ≤ H → H < ⊤ →
          Q₁ ⊓ H ≠ ⊥ → Q₂ ⊓ H ≠ ⊥ →
          (I ≠ ⊥ → H = Subgroup.normalizer (I : Set G)) →
          ∃ k : G, k ∈ centralPrimeComplementCore A ∧
            Q₂ = Q₁.map (MulAut.conj k).toMonoidHom := by
        intro H hAH hHproper hQ₁Hne hQ₂Hne hdefH
        let pi : Set ℕ := primeSupport (Nat.card A)
        let L : Subgroup G := primeSetCore piᶜ H
        have hLH : L ≤ H := primeSetCore_le piᶜ H
        have hLpi : IsPiNumber piᶜ (Nat.card L) := by
          simpa [L] using primeSetCore_isPiNumber piᶜ H
        have hAL : A ≤ Subgroup.normalizer (L : Set G) := by
          exact hAH.trans
            ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp
              (by simpa [L] using primeSetCore_normal piᶜ H))
        have hcopLA : (Nat.card L).Coprime (Nat.card A) := by
          apply Nat.coprime_of_dvd
          intro p hp hpL hpA
          have hpNotPi : p ∈ piᶜ := hLpi hp hpL
          have hpPi : p ∈ pi := by
            exact IsPiNumber.primeSupport_self hp hpA
          exact hpNotPi hpPi
        have hsolL : IsSolvable L := by
          letI : IsSolvable H := mFT_sol hHproper
          exact solvable_of_solvable_injective
            (f := Subgroup.inclusion hLH)
            (Subgroup.inclusion_injective hLH)
        have Qsyl : ∀ (Q : Subgroup G),
            Q ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
            Q ⊓ H ≠ ⊥ →
            ∃ P : Sylow q L,
              A ≤ Subgroup.normalizer
                  (((P : Subgroup L).map L.subtype : Subgroup G) : Set G) ∧
                Q ⊓ H ≤ (P : Subgroup L).map L.subtype := by
          intro Q hQmax hQHne
          have hQdata := mem_max_normed hQmax
          let X : Subgroup G := Q ⊓ H
          have hXpi : IsPiNumber ({q} : Set ℕ) (Nat.card X) :=
            hQdata.1.of_dvd (Subgroup.card_dvd_of_le inf_le_left)
          have hAX : A ≤ Subgroup.normalizer (X : Set G) := by
            exact (le_inf hQdata.2
              (hAH.trans Subgroup.le_normalizer)).trans
                Subgroup.inf_normalizer_le_normalizer_inf
          have hXpi' : IsPiNumber piᶜ (Nat.card X) := by
            apply hXpi.mono
            intro p hpq
            have hpEq : p = q := Set.mem_singleton_iff.mp hpq
            subst p
            simpa [pi] using hqA
          have hXL : X ≤ L := by
            apply cstrA.constrained H X hAH hHproper
            exact ⟨inf_le_right, hXpi', hAX⟩
          exact
            exists_normalized_sylow_ge_of_coprime_of_isSolvable_of_isPiNumber
              hAL hcopLA hsolL hXL hXpi hQHne hAX
        obtain ⟨P₁, hAP₁, hQ₁HP₁⟩ := Qsyl Q₁ hQ₁max hQ₁Hne
        obtain ⟨P₂, hAP₂, hQ₂HP₂⟩ := Qsyl Q₂ hQ₂max hQ₂Hne
        let R₁ : Subgroup G := (P₁ : Subgroup L).map L.subtype
        let R₂ : Subgroup G := (P₂ : Subgroup L).map L.subtype
        have hR₁L : R₁ ≤ L := Subgroup.map_subtype_le (P₁ : Subgroup L)
        have hR₂L : R₂ ≤ L := Subgroup.map_subtype_le (P₂ : Subgroup L)
        obtain ⟨h, hhLC, hR₂conj⟩ :=
          exists_mem_inf_centralizer_mulAutConj_sylow_of_coprime_of_isSolvable
            hAL hcopLA hsolL P₂ P₁ hAP₂ hAP₁
        have hhL : h ∈ L := hhLC.1
        have hhC : h ∈ Subgroup.centralizer (A : Set G) := hhLC.2
        have hhH : h ∈ H := hLH hhL
        have hhK : h ∈ centralPrimeComplementCore A := by
          let C : Subgroup G := Subgroup.centralizer (A : Set G)
          let K : Subgroup G := centralPrimeComplementCore A
          have hKC : K ≤ C := by
            simpa [K, C, centralPrimeComplementCore] using
              primeSetCore_le piᶜ C
          apply mem_normal_isHall_of_mem_of_isPiNumber hKC
            (by simpa [K, C] using centralPrimeComplementCore_normal A)
            (by simpa [K, C, pi] using normed_constrained_Hall A cstrA)
            hLpi
          · exact hhC
          · exact hhL
        have hR₂pi : IsPiNumber ({q} : Set ℕ) (Nat.card R₂) :=
          isPiNumber_singleton_of_isPGroup
            (P₂.isPGroup'.map L.subtype)
        obtain ⟨Q₃, hQ₃max, hR₂Q₃⟩ :=
          max_normed_exists (A : Set G) ({q} : Set ℕ) R₂
            hR₂pi hAP₂
        let Q₁h : Subgroup G :=
          Q₁.map (MulAut.conj h).toMonoidHom
        have hQ₁hmax : Q₁h ∈
            max_normed_pgroups (A : Set G) ({q} : Set ℕ) := by
          exact (cent_core_acts_max_norm q A Q₁ h hhK).mpr hQ₁max
        by_cases hQeq : Q₁ = Q₂
        · refine ⟨1, (centralPrimeComplementCore A).one_mem, ?_⟩
          subst Q₂
          ext x
          simp
        have hQ₃Hne : Q₃ ⊓ H ≠ ⊥ := by
          intro hbot
          apply hQ₂Hne
          apply le_antisymm
          · rw [← hbot]
            exact le_inf
              (hQ₂HP₂.trans hR₂Q₃)
              inf_le_right
          · exact bot_le
        have hQ₁hHne : Q₁h ⊓ H ≠ ⊥ := by
          let T : Subgroup G :=
            (Q₁ ⊓ H).map (MulAut.conj h).toMonoidHom
          have hTne : T ≠ ⊥ := by
            intro hbot
            apply hQ₁Hne
            apply (Subgroup.map_injective
              (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective)
            simpa [T] using hbot
          have hHconj : H.map (MulAut.conj h).toMonoidHom = H :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp
              (Subgroup.le_normalizer hhH)
          have hTle : T ≤ Q₁h ⊓ H := by
            dsimp [T, Q₁h]
            exact le_inf
              (Subgroup.map_mono inf_le_left)
              ((Subgroup.map_mono inf_le_right).trans (le_of_eq hHconj))
          intro hbot
          apply hTne
          exact le_antisymm (hTle.trans (le_of_eq hbot)) bot_le
        have hR₂conj' : R₂ =
            R₁.map (MulAut.conj h).toMonoidHom := by
          simpa [R₁, R₂] using hR₂conj
        have hR₁H : R₁ ≤ H := hR₁L.trans hLH
        have hR₂H : R₂ ≤ H := hR₂L.trans hLH
        have hQ₁R₁eq : Q₁ ⊓ R₁ = Q₁ ⊓ H := by
          apply le_antisymm
          · exact inf_le_inf le_rfl hR₁H
          · exact le_inf inf_le_left (by simpa [R₁] using hQ₁HP₁)
        have hQ₂R₂eq : Q₂ ⊓ R₂ = Q₂ ⊓ H := by
          apply le_antisymm
          · exact inf_le_inf le_rfl hR₂H
          · exact le_inf inf_le_left (by simpa [R₂] using hQ₂HP₂)
        have hIltQ₁R₁ : I < Q₁ ⊓ R₁ := by
          by_cases hIbot : I = ⊥
          · rw [hIbot]
            apply bot_lt_iff_ne_bot.mpr
            rwa [hQ₁R₁eq]
          · have hIneQ₁ : I ≠ Q₁ := by
              intro hIQ₁
              have hQ₁Q₂ : Q₁ ≤ Q₂ := by
                rw [← hIQ₁]
                exact inf_le_right
              exact hQeq (hQ₁max.eq_of_le hQ₂max.prop hQ₁Q₂)
            have hIltQ₁ : I < Q₁ :=
              lt_of_le_of_ne inf_le_left hIneQ₁
            calc
              I < Q₁ ⊓ Subgroup.normalizer (I : Set G) :=
                lt_inf_normalizer_of_isPGroup hQ₁p hIltQ₁
              _ = Q₁ ⊓ H := by rw [hdefH hIbot]
              _ = Q₁ ⊓ R₁ := hQ₁R₁eq.symm
        have hIltQ₂R₂ : I < Q₂ ⊓ R₂ := by
          by_cases hIbot : I = ⊥
          · rw [hIbot]
            apply bot_lt_iff_ne_bot.mpr
            rwa [hQ₂R₂eq]
          · have hIneQ₂ : I ≠ Q₂ := by
              intro hIQ₂
              have hQ₂Q₁ : Q₂ ≤ Q₁ := by
                rw [← hIQ₂]
                exact inf_le_left
              have hEq : Q₂ = Q₁ :=
                hQ₂max.eq_of_le hQ₁max.prop hQ₂Q₁
              exact hQeq hEq.symm
            have hIltQ₂ : I < Q₂ :=
              lt_of_le_of_ne inf_le_right hIneQ₂
            calc
              I < Q₂ ⊓ Subgroup.normalizer (I : Set G) :=
                lt_inf_normalizer_of_isPGroup hQ₂p hIltQ₂
              _ = Q₂ ⊓ H := by rw [hdefH hIbot]
              _ = Q₂ ⊓ R₂ := hQ₂R₂eq.symm
        let Ih : Subgroup G := I.map (MulAut.conj h).toMonoidHom
        have hIhLt : Ih < Q₁h ⊓ Q₃ := by
          have hmapped : Ih <
              (Q₁ ⊓ R₁).map (MulAut.conj h).toMonoidHom :=
            (Subgroup.map_lt_map_iff_of_injective
              (MulAut.conj h).injective).mpr hIltQ₁R₁
          have htarget :
              (Q₁ ⊓ R₁).map (MulAut.conj h).toMonoidHom =
                Q₁h ⊓ R₂ := by
            rw [Subgroup.map_inf Q₁ R₁ _ (MulAut.conj h).injective,
              ← hR₂conj']
          rw [htarget] at hmapped
          exact hmapped.trans_le (inf_le_inf le_rfl hR₂Q₃)
        have hcardIh : Nat.card Ih = Nat.card I := by
          dsimp [Ih]
          exact Subgroup.card_map_of_injective (MulAut.conj h).injective
        have hcardGrow₁ : Nat.card I < Nat.card (Q₁h ⊓ Q₃ : Subgroup G) := by
          rw [← hcardIh]
          exact natCard_subgroup_lt_of_lt hIhLt
        have hmeasure₁ : Measure Q₁h Q₃ < n := by
          rw [← hmeasure]
          dsimp [Measure]
          have hnewLe : Nat.card (Q₁h ⊓ Q₃ : Subgroup G) ≤ Nat.card G :=
            Nat.le_of_dvd Nat.card_pos
              (Q₁h ⊓ Q₃ : Subgroup G).card_subgroup_dvd_card
          dsimp [I] at hcardGrow₁
          omega
        have hIltQ₃Q₂ : I < Q₃ ⊓ Q₂ := by
          have hstep : I < Q₂ ⊓ Q₃ :=
            hIltQ₂R₂.trans_le
              (inf_le_inf le_rfl hR₂Q₃)
          simpa [inf_comm] using hstep
        have hcardGrow₂ : Nat.card I < Nat.card (Q₃ ⊓ Q₂ : Subgroup G) :=
          natCard_subgroup_lt_of_lt hIltQ₃Q₂
        have hmeasure₂ : Measure Q₃ Q₂ < n := by
          rw [← hmeasure]
          dsimp [Measure]
          have hnewLe : Nat.card (Q₃ ⊓ Q₂ : Subgroup G) ≤ Nat.card G :=
            Nat.le_of_dvd Nat.card_pos
              (Q₃ ⊓ Q₂ : Subgroup G).card_subgroup_dvd_card
          dsimp [I] at hcardGrow₂
          omega
        obtain ⟨k₃, hk₃K, hQ₃conj⟩ :=
          ih (Measure Q₁h Q₃) hmeasure₁ H Q₁h Q₃ rfl
            hAH hHproper hQ₁hmax hQ₃max hQ₁hHne hQ₃Hne
        obtain ⟨k₂, hk₂K, hQ₂conj⟩ :=
          ih (Measure Q₃ Q₂) hmeasure₂ H Q₃ Q₂ rfl
            hAH hHproper hQ₃max hQ₂max hQ₃Hne hQ₂Hne
        let k : G := k₂ * k₃ * h
        have hkK : k ∈ centralPrimeComplementCore A :=
          (centralPrimeComplementCore A).mul_mem
            ((centralPrimeComplementCore A).mul_mem hk₂K hk₃K) hhK
        refine ⟨k, hkK, ?_⟩
        have hcomp : (MulAut.conj k).toMonoidHom =
            (MulAut.conj k₂).toMonoidHom.comp
              ((MulAut.conj k₃).toMonoidHom.comp
                (MulAut.conj h).toMonoidHom) := by
          ext z
          change (k₂ * k₃ * h) * z * (k₂ * k₃ * h)⁻¹ =
            k₂ * (k₃ * (h * z * h⁻¹) * k₃⁻¹) * k₂⁻¹
          group
        calc
          Q₂ = Q₃.map (MulAut.conj k₂).toMonoidHom := hQ₂conj
          _ = (Q₁h.map (MulAut.conj k₃).toMonoidHom).map
              (MulAut.conj k₂).toMonoidHom := by rw [hQ₃conj]
          _ = Q₁.map
              ((MulAut.conj k₂).toMonoidHom.comp
                ((MulAut.conj k₃).toMonoidHom.comp
                  (MulAut.conj h).toMonoidHom)) := by
            dsimp [Q₁h]
            rw [Subgroup.map_map, Subgroup.map_map, MonoidHom.comp_assoc]
          _ = Q₁.map (MulAut.conj k).toMonoidHom := by rw [hcomp]
      by_cases hIbot : I = ⊥
      · exact run H hAH hHproper hQ₁Hne hQ₂Hne
          (fun hIne ↦ (hIne hIbot).elim)
      · let N : Subgroup G := Subgroup.normalizer (I : Set G)
        have hAN : A ≤ N := by
          exact (le_inf hQ₁data.2 hQ₂data.2).trans
            Subgroup.inf_normalizer_le_normalizer_inf
        have hNproper : N < ⊤ := by
          dsimp [N]
          exact mFT_norm_proper I hIbot hIproper
        have hQ₁Nne : Q₁ ⊓ N ≠ ⊥ := by
          intro hbot
          apply hIbot
          apply le_antisymm
          · rw [← hbot]
            exact le_inf inf_le_left Subgroup.le_normalizer
          · exact bot_le
        have hQ₂Nne : Q₂ ⊓ N ≠ ⊥ := by
          intro hbot
          apply hIbot
          apply le_antisymm
          · rw [← hbot]
            exact le_inf inf_le_right Subgroup.le_normalizer
          · exact bot_le
        exact run N hAN hNproper hQ₁Nne hQ₂Nne (fun _ ↦ rfl)
  exact hClaim (Measure Q₁ Q₂) H Q₁ Q₂ rfl
    hAH hHproper hQ₁max hQ₂max hQ₁Hne hQ₂Hne

/-- Bender--Glauberman Lemma 7.1.  The inverse in the conjugating map matches
MathComp's convention `Q :^ k = k⁻¹ Q k`. -/
theorem normed_constrained_meet_trans [IsMinSimpleOddGroup G]
    {q : ℕ} (A Q₁ Q₂ H : Subgroup G)
    (cstrA : NormedConstrained A)
    (hqA : q ∉ primeSupport (Nat.card A))
    (hAH : A ≤ H) (hHproper : H < ⊤)
    (hQ₁max : Q₁ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ))
    (hQ₂max : Q₂ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ))
    (hQ₁Hne : Q₁ ⊓ H ≠ ⊥) (hQ₂Hne : Q₂ ⊓ H ≠ ⊥) :
    ∃ k : G, k ∈ centralPrimeComplementCore A ∧
      Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom := by
  obtain ⟨y, hyK, hconj⟩ :=
    normed_constrained_meet_trans_mulAutConj A Q₁ Q₂ H cstrA hqA
      hAH hHproper hQ₁max hQ₂max hQ₁Hne hQ₂Hne
  refine ⟨y⁻¹, (centralPrimeComplementCore A).inv_mem hyK, ?_⟩
  simpa using hconj

end Submission.OddOrder.BG.Section07
