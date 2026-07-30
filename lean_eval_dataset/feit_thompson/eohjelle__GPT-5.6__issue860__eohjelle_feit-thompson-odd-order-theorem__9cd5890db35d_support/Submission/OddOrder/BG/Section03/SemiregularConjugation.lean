import Submission.OddOrder.BG.Section03.FrobeniusRepresentation
import Submission.OddOrder.MathlibSupport.FixedOneMulActionOrbitCount

/-!
Semiregular conjugation actions and their associated Frobenius
decompositions.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]
variable {H R : Subgroup G}

/-- Conjugation by every nonidentity element of `R` fixes only the identity
of `H`. Normalization is kept as a separate hypothesis, matching the source
formalization's action and semiregularity assumptions. -/
def IsSemiregularConjugation (H R : Subgroup G) : Prop :=
  ∀ r : R, r ≠ 1 → ∀ h : H,
    (r : G) * (h : G) * (r : G)⁻¹ = (h : G) → h = 1

namespace IsSemiregularConjugation

/-- Semiregularity restricts to a smaller acted-on subgroup. -/
theorem mono_left {M : Subgroup G} (hMH : M ≤ H)
    (hreg : IsSemiregularConjugation H R) :
    IsSemiregularConjugation M R := by
  intro r hr m hm
  let mH : H := ⟨m, hMH m.property⟩
  have hmH : mH = 1 := hreg r hr mH hm
  apply Subtype.ext
  exact congrArg (fun x : H ↦ (x : G)) hmH

/-- A finite semiregular conjugation action has coprime actor and acted-on
group orders. -/
theorem natCard_coprime [Finite H] [Finite R]
    (hreg : IsSemiregularConjugation H R)
    (hnorm : R ≤ Subgroup.normalizer (H : Set G)) :
    Nat.Coprime (Nat.card H) (Nat.card R) := by
  letI := subgroupConjugationAction H R hnorm
  have hfixed : ∀ r : R, r ≠ 1 → ∀ h : H, r • h = h → h = 1 := by
    intro r hr h hh
    apply hreg r hr h
    simpa only [coe_subgroupConjugationAction_smul H R hnorm] using
      congrArg Subtype.val hh
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := R) (X := H))
  have hcard : Nat.card H = 1 + t * Nat.card R := by
    simpa [t] using natCard_eq_one_add_fixedOneOrbits_mul_natCard
      (G := R) (X := H) (fun r ↦ smul_one r) hfixed
  rw [hcard]
  exact (Nat.coprime_add_mul_right_left 1 (Nat.card R) t).mpr
    (Nat.coprime_one_left (Nat.card R))

/-- If semiregularly interacting subgroups generate the ambient finite group,
they form an internal Frobenius decomposition. -/
theorem isFrobeniusDecomposition [Finite G]
    (hreg : IsSemiregularConjugation H R)
    (hnorm : R ≤ Subgroup.normalizer (H : Set G))
    (hsup : H ⊔ R = ⊤) (hH : H ≠ ⊥) (hR : R ≠ ⊥) :
    IsFrobeniusDecomposition H R := by
  have hnormal : H.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply le_antisymm le_top
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer hnorm
  have hcop : Nat.Coprime (Nat.card H) (Nat.card R) :=
    hreg.natCard_coprime hnorm
  have hdisjoint : Disjoint H R :=
    Subgroup.disjoint_of_coprime_natCard hcop
  have hcomplement : H.IsComplement' R := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjoint
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left H R hnorm, hsup]
    rfl
  exact
    { isComplement := hcomplement
      kernel_normal := hnormal
      kernel_ne_bot := hH
      complement_ne_bot := hR
      fixedPointFree := hreg }

/-- A semiregular normalized pair forms a Frobenius decomposition inside the
subgroup it generates. -/
theorem isFrobeniusDecomposition_sup [Finite G]
    (hreg : IsSemiregularConjugation H R)
    (hnorm : R ≤ Subgroup.normalizer (H : Set G))
    (hH : H ≠ ⊥) (hR : R ≠ ⊥) :
    let J := R ⊔ H
    IsFrobeniusDecomposition (H.subgroupOf J) (R.subgroupOf J) := by
  let J := R ⊔ H
  let HJ := H.subgroupOf J
  let RJ := R.subgroupOf J
  letI : HJ.Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
  have hregJ : IsSemiregularConjugation HJ RJ := by
    intro r hr h hh
    let rR : R := ⟨(r.1 : G), r.2⟩
    let hH' : H := ⟨(h.1 : G), h.2⟩
    have hrR : rR ≠ 1 := by
      simpa [rR, RJ, J] using hr
    have hhG : (rR : G) * (hH' : G) * (rR : G)⁻¹ = (hH' : G) := by
      exact congrArg (fun x : J ↦ (x : G)) hh
    have hhOne : hH' = 1 := hreg rR hrR hH' hhG
    simpa [hH', HJ, J] using hhOne
  have hsupJ : HJ ⊔ RJ = ⊤ := by
    change H.subgroupOf J ⊔ R.subgroupOf J = ⊤
    rw [← Subgroup.subgroupOf_sup (show H ≤ J from le_sup_right)
      (show R ≤ J from le_sup_left)]
    simp [J, sup_comm]
  have hHJ : HJ ≠ ⊥ := by
    intro hbot
    apply hH
    have hmapped := congrArg (fun S : Subgroup J ↦ S.map J.subtype) hbot
    simpa [HJ, J, Subgroup.map_subgroupOf_eq_of_le le_sup_right] using hmapped
  have hRJ : RJ ≠ ⊥ := by
    intro hbot
    apply hR
    have hmapped := congrArg (fun S : Subgroup J ↦ S.map J.subtype) hbot
    simpa [RJ, J, Subgroup.map_subgroupOf_eq_of_le le_sup_left] using hmapped
  have hnormJ : RJ ≤ Subgroup.normalizer (HJ : Set J) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : HJ.Normal)]
    exact le_top
  exact hregJ.isFrobeniusDecomposition hnormJ hsupJ hHJ hRJ

end IsSemiregularConjugation

end Submission.OddOrder.BG.Section03
