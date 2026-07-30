import Submission.OddOrder.PF.Section02.DadeHypothesis
import Submission.OddOrder.MathlibSupport.PiPrimeCore
import Submission.OddOrder.MathlibSupport.NormalizedTI

/-!
# Peterfalvi 2.3: the canonical Dade signalizer

The primes occurring in the centralizers inside `L` determine a canonical
prime-complement core in each centralizer inside `G`.  Peterfalvi 2.3
identifies the normalized trivial-intersection condition with the vanishing
of this canonical signalizer family.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.MathlibSupport

universe u

variable {Γ : Type u} [Group Γ]

/-- The primes occurring in an `L`-centralizer of an element of `A`. -/
def dadePrimeSet (L : Subgroup Γ) (A : Set Γ) : Set ℕ :=
  {p | ∃ a ∈ A,
    p ∈ primeSupport
      (Nat.card (centralizerWithin L (Subgroup.zpowers a)))}

/-- The canonical Dade signalizer attached to `a`. -/
def DadeSignalizer {G L : Subgroup Γ} {A : Set Γ}
    (_ddA : DadeHypothesis G L A) (a : Γ) : Subgroup Γ :=
  piPrimeCore (dadePrimeSet L A)
    (centralizerWithin G (Subgroup.zpowers a))

private theorem dadeCentralizer_isPiNumber
    {L : Subgroup Γ} {A : Set Γ} {a : Γ} (ha : a ∈ A) :
    IsPiNumber (dadePrimeSet L A)
      (Nat.card (centralizerWithin L (Subgroup.zpowers a))) := by
  intro p hp hpdiv
  exact ⟨a, ha, hp, hpdiv⟩

private theorem dadeWitness_isPiNumber
    {L : Subgroup Γ} {A : Set Γ} {H₀ : Γ → Subgroup Γ}
    (hcop : ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A →
      Nat.Coprime (Nat.card (H₀ a))
        (Nat.card (centralizerWithin L (Subgroup.zpowers b))))
    {a : Γ} (ha : a ∈ A) :
    IsPiNumber (dadePrimeSet L A)ᶜ (Nat.card (H₀ a)) := by
  intro p hp hpH
  change p ∉ dadePrimeSet L A
  rintro ⟨b, hb, hp', hpCL⟩
  exact (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨p, hp, hpH, hpCL⟩) (hcop ha hb)

private theorem natCard_subgroupOf_eq
    {K X : Subgroup Γ} (hKX : K ≤ X) :
    Nat.card (K.subgroupOf X) = Nat.card K :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv

private theorem dadeCentralizer_isHall
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) {a : Γ} (ha : a ∈ A) :
    IsHall (dadePrimeSet L A)
      ((centralizerWithin L (Subgroup.zpowers a)).subgroupOf
        (centralizerWithin G (Subgroup.zpowers a))) := by
  rcases ddA.2.2.2.2 with ⟨H₀, hH₀, hcop⟩
  have hsd := hH₀ ha
  constructor
  · rw [natCard_subgroupOf_eq hsd.2.1]
    exact dadeCentralizer_isPiNumber ha
  · rw [hsd.2.2.2.index_eq_card,
      natCard_subgroupOf_eq hsd.1]
    exact dadeWitness_isPiNumber hcop ha

/-- Every canonical signalizer lies in `G`. -/
theorem Dade_signalizer_sub
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (a : Γ) :
    DadeSignalizer ddA a ≤ G := by
  exact (piPrimeCore_le (dadePrimeSet L A)
    (centralizerWithin G (Subgroup.zpowers a))).trans
      (centralizerWithin_le_left G (Subgroup.zpowers a))

/-- Every canonical signalizer centralizes the powers of its argument. -/
theorem Dade_signalizer_cent
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (a : Γ) :
    DadeSignalizer ddA a ≤
      Subgroup.centralizer (Subgroup.zpowers a : Set Γ) := by
  exact (piPrimeCore_le (dadePrimeSet L A)
    (centralizerWithin G (Subgroup.zpowers a))).trans inf_le_right

/-- Any signalizer family witnessing the Dade hypothesis equals the
canonical family on `A`. -/
theorem def_Dade_signalizer
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (H₁ : Γ → Subgroup Γ)
    (hH₁ : IsDadeSignalizer G L A H₁) :
    ∀ ⦃a⦄, a ∈ A → DadeSignalizer ddA a = H₁ a := by
  intro a ha
  have hsd := hH₁ ha
  have hH₁pi :
      IsPiNumber (dadePrimeSet L A)ᶜ (Nat.card (H₁ a)) := by
    have hindex := (dadeCentralizer_isHall ddA ha).isPiNumber_index
    rw [hsd.2.2.2.index_eq_card,
      natCard_subgroupOf_eq hsd.1] at hindex
    exact hindex
  exact piPrimeCore_eq_of_normal_isComplement
    (dadePrimeSet L A) hsd.1 hsd.2.1 hsd.2.2.1 hH₁pi
      (dadeCentralizer_isPiNumber ha) hsd.2.2.2

/-- The canonical family itself supplies the semidirect-product clause of
the Dade hypothesis. -/
theorem Dade_sdprod
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    IsDadeSignalizer G L A (DadeSignalizer ddA) := by
  rcases ddA.2.2.2.2 with ⟨H₀, hH₀, _⟩
  intro a ha
  rw [def_Dade_signalizer ddA H₀ hH₀ ha]
  exact hH₀ ha

/-- Canonical signalizers have order coprime to every relevant
`L`-centralizer. -/
theorem Dade_coprime
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A →
      Nat.Coprime (Nat.card (DadeSignalizer ddA a))
        (Nat.card (centralizerWithin L (Subgroup.zpowers b))) := by
  intro a ha b hb
  have hHpi :
      IsPiNumber (dadePrimeSet L A)ᶜ
        (Nat.card (DadeSignalizer ddA a)) := by
    simpa [DadeSignalizer] using
      (piPrimeCore_isPiNumber (dadePrimeSet L A)
        (centralizerWithin G (Subgroup.zpowers a)))
  have hCLpi := dadeCentralizer_isPiNumber (L := L) hb
  apply Nat.coprime_of_dvd
  intro p hp hpH hpCL
  exact (hHpi hp hpH) (hCLpi hp hpCL)

/-- Peterfalvi 2.3: `A` is normalized TI relative to `G` and `L` exactly
when it is nonempty and all canonical Dade signalizers vanish. -/
theorem Dade_normedTI_P
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    IsNormalizedTI A G L ↔
      A.Nonempty ∧
        ∀ ⦃a⦄, a ∈ A → DadeSignalizer ddA a = ⊥ := by
  constructor
  · intro hTI
    refine ⟨hTI.1, ?_⟩
    intro a ha
    have hHCG :
        DadeSignalizer ddA a ≤
          centralizerWithin G (Subgroup.zpowers a) := by
      exact piPrimeCore_le (dadePrimeSet L A)
        (centralizerWithin G (Subgroup.zpowers a))
    have hHL : DadeSignalizer ddA a ≤ L :=
      hHCG.trans (hTI.centralizerWithin_zpowers_le ha)
    have hHCL :
        DadeSignalizer ddA a ≤
          centralizerWithin L (Subgroup.zpowers a) := by
      intro x hx
      exact ⟨hHL hx, Dade_signalizer_cent ddA a hx⟩
    have hdis :
        Disjoint (DadeSignalizer ddA a)
          (centralizerWithin L (Subgroup.zpowers a)) :=
      Subgroup.disjoint_of_coprime_natCard
        (Dade_coprime ddA ha ha)
    calc
      DadeSignalizer ddA a =
          DadeSignalizer ddA a ⊓
            centralizerWithin L (Subgroup.zpowers a) :=
        (inf_eq_left.mpr hHCL).symm
      _ = ⊥ := hdis.eq_bot
  · rintro ⟨hA, hbot⟩
    apply isNormalizedTI_iff_mem_conj.mpr
    refine ⟨hA, ddA.2.1, ?_⟩
    intro a ha g hg
    constructor
    · intro hag
      have hsd := Dade_sdprod ddA ha
      have hcomp := hsd.2.2.2
      rw [hbot ha] at hcomp
      have hCLtop :
          (centralizerWithin L (Subgroup.zpowers a)).subgroupOf
              (centralizerWithin G (Subgroup.zpowers a)) = ⊤ := by
        apply Subgroup.isComplement'_bot_left.mp
        simpa using hcomp
      have hCGCL :
          centralizerWithin G (Subgroup.zpowers a) ≤
            centralizerWithin L (Subgroup.zpowers a) :=
        Subgroup.subgroupOf_eq_top.mp hCLtop
      have hclassG :
          g⁻¹ * a * g ∈ conjugacyClassWithin G a := by
        exact ⟨g, hg, rfl⟩
      rcases ddA.2.2.2.1 ha hag hclassG with
        ⟨k, hkL, hkconj⟩
      change k⁻¹ * a * k = g⁻¹ * a * g at hkconj
      let c : Γ := g * k⁻¹
      have hccomm : Commute a c := by
        dsimp [c]
        rw [commute_iff_eq]
        calc
          a * (g * k⁻¹) =
              g * (g⁻¹ * a * g) * k⁻¹ := by group
          _ = g * (k⁻¹ * a * k) * k⁻¹ := by rw [hkconj]
          _ = (g * k⁻¹) * a := by group
      have hcG : c ∈ G := by
        exact G.mul_mem hg (G.inv_mem (ddA.2.1 hkL))
      have hcCG : c ∈ centralizerWithin G (Subgroup.zpowers a) := by
        refine ⟨hcG, ?_⟩
        intro z hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (hccomm.zpow_left n).eq
      have hcL : c ∈ L := (hCGCL hcCG).1
      have hckL : c * k ∈ L := L.mul_mem hcL hkL
      simpa [c] using hckL
    · intro hgL
      exact ((Subgroup.mem_set_normalizer_iff''.mp
        (ddA.1.2 hgL)) a).mp ha

end Submission.OddOrder.PF
