import Submission.OddOrder.BG.Section01.Constrained
import Submission.OddOrder.BG.Section01.PStability
import Submission.OddOrder.MathlibSupport.PCoreFunctorial
import Submission.OddOrder.MathlibSupport.PPrimePCoreQuotient
import Submission.OddOrder.MathlibSupport.PPrimePCoreSylow
import Submission.OddOrder.MathlibSupport.SylowIntersection

/-!
P-stable constrained groups are p-abelian-constrained.

This is the mathlib-shaped form of Gorenstein, Proposition 8.1.3, and
`BGsection1.p_stable_abelian_constrained`.
-/

namespace Submission.OddOrder.BG.Section01

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- Every abelian subgroup normal in a Sylow `p`-subgroup lies in the
two-step `p'`, `p` core. -/
def IsPAbelianConstrained (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow p G) (A : Subgroup G),
    IsMulCommutative A →
    A ≤ (S : Subgroup G) →
    (A.subgroupOf (S : Subgroup G)).Normal →
    A ≤ pPrimePCore p G

/-- Gorenstein, Proposition 8.1.3: p-stability upgrades p-constrainedness to
p-abelian-constrainedness. -/
theorem isPAbelianConstrained_of_isPConstrained_of_isPStable {p : ℕ}
    [Fact p.Prime] (hconstrained : IsPConstrained p G)
    (hstable : IsPStable p G) : IsPAbelianConstrained p G := by
  intro S A hAcomm hAS hAnormal
  letI : IsMulCommutative A := hAcomm
  let K₁ : Subgroup G := pPrimeCore p G
  let K₂ : Subgroup G := pPrimePCore p G
  let Q : Sylow p K₂ := normalIntersectionSylow S K₂
  let QG : Subgroup G := sylowInAmbient Q
  have hQG : QG = (S : Subgroup G) ⊓ K₂ := by
    simp [QG, Q, sylowInAmbient]
  have hQmap : QG.map (QuotientGroup.mk' K₁) =
      pCore p (G ⧸ K₁) := by
    rw [hQG]
    simpa [Q, K₁, K₂] using
      sylow_pPrimePCore_map_quotient_eq Q
  have hK₂map : K₂.map (QuotientGroup.mk' K₁) =
      pCore p (G ⧸ K₁) := by
    simpa [K₁, K₂] using pPrimePCore_map_quotient_eq (p := p) (G := G)
  have hK₂decomp : K₁ ⊔ QG = K₂ := by
    have hmaps : QG.map (QuotientGroup.mk' K₁) =
        K₂.map (QuotientGroup.mk' K₁) := hQmap.trans hK₂map.symm
    have hsups := Subgroup.map_eq_map_iff.mp hmaps
    rw [QuotientGroup.ker_mk'] at hsups
    have hK₁K₂ : K₁ ≤ K₂ := by
      exact pPrimeCore_le_pPrimePCore
    rw [sup_of_le_left hK₁K₂] at hsups
    simpa [sup_comm] using hsups
  have hQp : IsPGroup p QG := sylowInAmbient_isPGroup Q
  have hAp : IsPGroup p A := IsPGroup.to_le S.isPGroup' hAS
  have hQS : QG ≤ (S : Subgroup G) := by
    rw [hQG]
    exact inf_le_left
  have hQK₂ : QG ≤ K₂ := by
    rw [hQG]
    exact inf_le_right
  have hAnormalizesQ : A ≤ Subgroup.normalizer (QG : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right, hQG]
    apply le_inf
    · exact (Subgroup.commutator_le_sup A ((S : Subgroup G) ⊓ K₂)).trans
        (sup_le hAS inf_le_left)
    · exact (Subgroup.commutator_mono le_top inf_le_right).trans
        (Subgroup.commutator_le_right (⊤ : Subgroup G) K₂)
  have hSnormalizesA : (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAS).mp hAnormal
  have hQA : ⁅QG, A⁆ ≤ A :=
    (Subgroup.commutator_mono hQS le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hSnormalizesA)
  have hAA : ⁅A, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha b hb
    simpa using congrArg Subtype.val (mul_comm' ⟨b, hb⟩ ⟨a, ha⟩)
  have hquadratic : ⁅⁅QG, A⁆, A⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hQA le_rfl).trans hAA.le
  have hstableA : imageInNormalizerCentralizerQuotient QG A ≤
      pCore p
        ((Subgroup.normalizer (QG : Set G)) ⧸ normalizerCentralizer QG) := by
    apply hstable QG A hQp
    · rw [hK₂decomp]
      infer_instance
    · exact hAp
    · exact hAnormalizesQ
    · exact hquadratic
  let N : Subgroup G := Subgroup.normalizer (QG : Set G)
  let C : Subgroup N := normalizerCentralizer QG
  let qN : N →* N ⧸ C := QuotientGroup.mk' C
  let q₂ : G →* G ⧸ K₂ := QuotientGroup.mk' K₂
  let f₀ : N →* G ⧸ K₂ := q₂.comp N.subtype
  have hCker : C ≤ f₀.ker := by
    intro x hx
    change q₂ (x : G) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hconstrained Q hx
  let f : (N ⧸ C) →* (G ⧸ K₂) := QuotientGroup.lift C f₀ hCker
  have hNsup : N ⊔ K₂ = ⊤ := by
    simpa [N, QG, sylowInAmbient] using Q.normalizer_sup_eq_top
  have hNmap : N.map q₂ = ⊤ := by
    calc
      N.map q₂ = (⊤ : Subgroup G).map q₂ := by
        rw [Subgroup.map_eq_map_iff, QuotientGroup.ker_mk', hNsup, top_sup_eq]
      _ = q₂.range := (MonoidHom.range_eq_map q₂).symm
      _ = ⊤ := q₂.range_eq_top.mpr (QuotientGroup.mk'_surjective K₂)
  have hf₀ : Function.Surjective f₀ := by
    intro y
    have hy : y ∈ N.map q₂ := by
      rw [hNmap]
      exact Subgroup.mem_top y
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨⟨g, hg⟩, rfl⟩
  have hf : Function.Surjective f := by
    exact QuotientGroup.lift_surjective_of_surjective C f₀ hf₀ hCker
  have hfcomp : f.comp qN = f₀ := by
    ext x
    rfl
  have himage :
      (imageInNormalizerCentralizerQuotient QG A).map f = A.map q₂ := by
    calc
      (imageInNormalizerCentralizerQuotient QG A).map f =
          (A.subgroupOf N).map (f.comp qN) := by
        rw [imageInNormalizerCentralizerQuotient, Subgroup.map_map]
      _ = (A.subgroupOf N).map f₀ := by rw [hfcomp]
      _ = (A.subgroupOf N).map (q₂.comp N.subtype) := rfl
      _ = ((A.subgroupOf N).map N.subtype).map q₂ := by
        rw [Subgroup.map_map]
      _ = A.map q₂ := by
        rw [Subgroup.map_subgroupOf_eq_of_le hAnormalizesQ]
  have hAmap : A.map q₂ ≤ pCore p (G ⧸ K₂) := by
    rw [← himage]
    exact (Subgroup.map_mono hstableA).trans
      (map_pCore_le_of_surjective f hf)
  have hAmapBot : A.map q₂ = ⊥ := by
    apply le_bot_iff.mp
    simpa [K₂, pCore_quotient_pPrimePCore_eq_bot] using hAmap
  have hAK₂ : A ≤ q₂.ker := (Subgroup.map_eq_bot_iff A).mp hAmapBot
  simpa [q₂, K₂, QuotientGroup.ker_mk'] using hAK₂

end Submission.OddOrder.BG.Section01
