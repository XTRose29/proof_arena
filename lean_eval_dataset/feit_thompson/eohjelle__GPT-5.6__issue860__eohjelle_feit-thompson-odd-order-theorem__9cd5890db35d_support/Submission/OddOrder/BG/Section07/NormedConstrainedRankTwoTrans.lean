import Submission.OddOrder.BG.Section07.NormedConstrainedRankThreeTrans

/-!
# Bender--Glauberman, Section 7: rank-two transitivity

This file ports Bender--Glauberman Theorem 7.3,
`normed_constrained_rank2_trans`.  When `q` divides the order of the
centralizer of `A`, rank two in the center of `A` is enough for the
prime-complement core of `C_G(A)` to act transitively on the maximal
`q`-subgroups normalized by `A`.
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
  simp [hqp]

omit [Finite G] in
/-- If a quotient by an ambient subgroup is cyclic while the group is not,
the ambient subgroup is nontrivial. -/
private theorem ne_bot_of_not_isCyclic_of_isCyclic_quotient
    {B C : Subgroup G} (hCnormal : (C.subgroupOf B).Normal)
    (hBnoncyclic : ¬ IsCyclic B)
    (hquotCyclic : IsCyclic (B ⧸ C.subgroupOf B)) : C ≠ ⊥ := by
  letI : (C.subgroupOf B).Normal := hCnormal
  intro hCbot
  subst C
  have hsubBot : (⊥ : Subgroup G).subgroupOf B = (⊥ : Subgroup B) := by
    ext x
    simp
  have hquotBot : IsCyclic (B ⧸ (⊥ : Subgroup B)) :=
    (QuotientGroup.quotientMulEquivOfEq hsubBot).isCyclic.mp hquotCyclic
  apply hBnoncyclic
  exact QuotientGroup.quotientBot.isCyclic.mp hquotBot

/-- Bender--Glauberman Theorem 7.3.  The conclusion is the pairwise form
of transitivity, with MathComp's convention `Q :^ k = k⁻¹ Q k`. -/
theorem normed_constrained_rank2_trans [IsMinSimpleOddGroup G]
    {q : ℕ} (A : Subgroup G)
    (cstrA : NormedConstrained A)
    (hqA : q ∉ primeSupport (Nat.card A))
    (hqCA : q ∣ Nat.card (Subgroup.centralizer (A : Set G)))
    (hRank2 : ∃ (p : ℕ) (B : Subgroup G),
      p.Prime ∧ B ≤ A ∧ A ≤ Subgroup.centralizer (B : Set G) ∧
        IsElementaryAbelianOfRank p 2 B) :
    ∀ Q₁ Q₂ : Subgroup G,
      Q₁ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      ∃ k : G, k ∈ centralPrimeComplementCore A ∧
        Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom := by
  classical
  rintro Q₁ Q₂ hQ₁max hQ₂max
  by_cases hQ₁bot : Q₁ = ⊥
  · have hbotMax : (⊥ : Subgroup G) ∈
        max_normed_pgroups (A : Set G) ({q} : Set ℕ) := by
      simpa [hQ₁bot] using hQ₁max
    have hQ₂bot : Q₂ = ⊥ := by
      have hQ₂mem : Q₂ ∈ ({⊥} : Set (Subgroup G)) := by
        rw [← trivg_max_norm A ({q} : Set ℕ) hbotMax]
        exact hQ₂max
      exact Set.mem_singleton_iff.mp hQ₂mem
    subst Q₁
    subst Q₂
    exact ⟨1, (centralPrimeComplementCore A).one_mem, by simp⟩
  have hQ₂ne : Q₂ ≠ ⊥ := by
    intro hQ₂bot
    have hbotMax : (⊥ : Subgroup G) ∈
        max_normed_pgroups (A : Set G) ({q} : Set ℕ) := by
      simpa [hQ₂bot] using hQ₂max
    have hQ₁mem : Q₁ ∈ ({⊥} : Set (Subgroup G)) := by
      rw [← trivg_max_norm A ({q} : Set ℕ) hbotMax]
      exact hQ₁max
    exact hQ₁bot (Set.mem_singleton_iff.mp hQ₁mem)
  have hQ₁data := mem_max_normed hQ₁max
  letI : Fact q.Prime :=
    ⟨prime_of_isPiNumber_singleton_of_ne_bot hQ₁data.1 hQ₁bot⟩
  obtain ⟨p, B, hp, hBA, hABcentral, hB⟩ := hRank2
  letI : Fact p.Prime := ⟨hp⟩
  let CA : Subgroup G := Subgroup.centralizer (A : Set G)
  let R₀ : Sylow q CA := default
  let R₀G : Subgroup G := (R₀ : Subgroup CA).map CA.subtype
  have hR₀Gp : IsPGroup q R₀G := R₀.isPGroup'.map CA.subtype
  have hR₀GCA : R₀G ≤ CA := Subgroup.map_subtype_le (R₀ : Subgroup CA)
  have hAR₀G : A ≤ Subgroup.normalizer (R₀G : Set G) := by
    have hcentral : A ≤ Subgroup.centralizer (R₀G : Set G) := by
      apply Subgroup.le_centralizer_iff.mpr
      simpa [CA] using hR₀GCA
    exact hcentral.trans (Subgroup.centralizer_le_normalizer (R₀G : Set G))
  obtain ⟨R, hRmax, hR₀GR⟩ :=
    max_normed_exists (A : Set G) ({q} : Set ℕ) R₀G
      (isPiNumber_singleton_of_isPGroup hR₀Gp) hAR₀G
  have hR₀ne : (R₀ : Subgroup CA) ≠ ⊥ := by
    apply R₀.ne_bot_of_dvd_card
    simpa [CA] using hqCA
  have hR₀Gne : R₀G ≠ ⊥ := by
    intro hbot
    apply hR₀ne
    apply (Subgroup.map_eq_bot_iff_of_injective
      (R₀ : Subgroup CA) CA.subtype_injective).mp
    simpa [R₀G] using hbot
  have commonCentralizer : ∀ (Q : Subgroup G),
      Q ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) → Q ≠ ⊥ →
      ∃ H : Subgroup G,
        A ≤ H ∧ H < ⊤ ∧ R ⊓ H ≠ ⊥ ∧ Q ⊓ H ≠ ⊥ := by
    intro Q hQmax hQne
    have hQdata := mem_max_normed hQmax
    have hQp : IsPGroup q Q :=
      isPGroup_of_isPiNumber_singleton hQdata.1
    have hBQ : B ≤ Subgroup.normalizer (Q : Set G) :=
      hBA.trans hQdata.2
    obtain ⟨C, hCB, hCnormal, hBCcyclic, hQCne⟩ :=
      exists_normal_cocyclic_centralizerWithin_ne_bot_of_isPGroup
        B Q hB.commutative hBQ hQp hQne
    have hCne : C ≠ ⊥ :=
      ne_bot_of_not_isCyclic_of_isCyclic_quotient hCnormal
        (hB.not_isCyclic hp) hBCcyclic
    letI : Nontrivial C := C.nontrivial_iff_ne_bot.mpr hCne
    obtain ⟨z : C, hz⟩ := exists_ne (1 : C)
    have hzG : (z : G) ≠ 1 := by
      intro hzOne
      apply hz
      exact Subtype.ext hzOne
    have hzB : (z : G) ∈ B := hCB z.2
    let H : Subgroup G := Subgroup.centralizer ({(z : G)} : Set G)
    have hAH : A ≤ H := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hABcentral ha) z hzB).symm
    have hHproper : H < ⊤ := mFT_cent1_proper hzG
    have hR₀GH : R₀G ≤ H := by
      intro x hx
      change x ∈ Subgroup.centralizer ({(z : G)} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxCA : x ∈ Subgroup.centralizer (A : Set G) := by
        simpa [CA] using hR₀GCA hx
      exact (Subgroup.mem_centralizer_iff.mp hxCA z (hBA hzB)).symm
    have hRHne : R ⊓ H ≠ ⊥ := by
      have hle : R₀G ≤ R ⊓ H := le_inf hR₀GR hR₀GH
      intro hbot
      apply hR₀Gne
      exact eq_bot_iff.mpr (hle.trans (le_of_eq hbot))
    have hQHne : Q ⊓ H ≠ ⊥ := by
      have hle : centralizerWithin Q C ≤ Q ⊓ H := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        change x ∈ Subgroup.centralizer ({(z : G)} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hx.2 z z.2).symm
      intro hbot
      apply hQCne
      exact eq_bot_iff.mpr (hle.trans (le_of_eq hbot))
    exact ⟨H, hAH, hHproper, hRHne, hQHne⟩
  obtain ⟨H₁, hAH₁, hH₁proper, hRH₁ne, hQ₁H₁ne⟩ :=
    commonCentralizer Q₁ hQ₁max hQ₁bot
  obtain ⟨k₁, hk₁, hRconj⟩ :=
    normed_constrained_meet_trans A Q₁ R H₁ cstrA hqA
      hAH₁ hH₁proper hQ₁max hRmax hQ₁H₁ne hRH₁ne
  obtain ⟨H₂, hAH₂, hH₂proper, hRH₂ne, hQ₂H₂ne⟩ :=
    commonCentralizer Q₂ hQ₂max hQ₂ne
  obtain ⟨k₂, hk₂, hQ₂conj⟩ :=
    normed_constrained_meet_trans A R Q₂ H₂ cstrA hqA
      hAH₂ hH₂proper hRmax hQ₂max hRH₂ne hQ₂H₂ne
  refine ⟨k₁ * k₂, (centralPrimeComplementCore A).mul_mem hk₁ hk₂, ?_⟩
  calc
    Q₂ = R.map (MulAut.conj k₂⁻¹).toMonoidHom := hQ₂conj
    _ = (Q₁.map (MulAut.conj k₁⁻¹).toMonoidHom).map
        (MulAut.conj k₂⁻¹).toMonoidHom := by rw [hRconj]
    _ = Q₁.map (MulAut.conj (k₁ * k₂)⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp

end Submission.OddOrder.BG.Section07
