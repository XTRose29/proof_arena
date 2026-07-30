import Submission.OddOrder.BG.AppendixAB.PuigCenterNormal
import Submission.OddOrder.BG.AppendixAB.PuigInjectiveFunctorial
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient

/-!
The Puig factorization from Bender--Glauberman Appendix B.

This ports `BGappendixAB.Puig_factorization`, Theorem B.4(a).  MathComp's
product equality is represented by the equivalent subgroup join equality.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- `BGappendixAB.Puig_factorization` (Bender--Glauberman Theorem B.4(a)). -/
theorem Puig_factorization {p : ℕ} [Fact p.Prime] [IsSolvable G]
    (hodd : Odd (Nat.card G)) (S : Sylow p G) :
    pPrimeCore p G ⊔
        Subgroup.normalizer (centerWithin (puig (S : Subgroup G)) : Set G) = ⊤ := by
  let D : Subgroup G := pPrimeCore p G
  let Z : Subgroup G := centerWithin (puig (S : Subgroup G))
  letI : D.Characteristic := by
    dsimp [D]
    infer_instance
  letI : D.Normal := by infer_instance
  let q : G →* G ⧸ D := QuotientGroup.mk' D

  have hSD : Disjoint (S : Subgroup G) D := by
    dsimp [D]
    exact disjoint_pPrimeCore_of_isPGroup S.isPGroup'
  have hZleS : Z ≤ (S : Subgroup G) :=
    (centralizerWithin_le_left _ _).trans (puig_le (S : Subgroup G))
  have hqS : Function.Injective fun x : S ↦ q x := by
    intro x y hxy
    have hdiffD : (x : G)⁻¹ * y ∈ D := QuotientGroup.eq.mp hxy
    have hdiffS : (x : G)⁻¹ * y ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem x.property) y.property
    have hdiffBot : (x : G)⁻¹ * y ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hSD]
      exact ⟨hdiffS, hdiffD⟩
    apply Subtype.ext
    exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp hdiffBot)

  have hZmap : Z.map q = centerWithin (puig ((S : Subgroup G).map q)) := by
    simpa [Z] using
      map_centerWithin_puig_eq_of_injective_on q (S : Subgroup G) hqS
  let Sq : Sylow p (G ⧸ D) :=
    S.mapSurjective (QuotientGroup.mk'_surjective D)
  have hSq : (Sq : Subgroup (G ⧸ D)) = (S : Subgroup G).map q := by
    rfl
  have hoddQuotient : Odd (Nat.card (G ⧸ D)) := odd_natCard_quotient D hodd
  have hZmapNormal : (Z.map q).Normal := by
    rw [hZmap, ← hSq]
    simpa [D] using
      (Puig_center_normal hoddQuotient Sq
        (pPrimeCore_quotient_self_eq_bot (G := G) (p := p)))
  letI : (Z.map q).Normal := hZmapNormal

  let N : Subgroup G := D ⊔ Z
  have hNcomap : N = (Z.map q).comap q := by
    dsimp [N, q]
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  letI : N.Normal := by
    rw [hNcomap]
    infer_instance

  have hSN : (S : Subgroup G) ⊓ N = Z := by
    apply le_antisymm
    · intro x hx
      have hxN : x ∈ D ⊔ Z := by simpa [N] using hx.2
      obtain ⟨d, hdD, z, hzZ, hdz⟩ :=
        Subgroup.mem_sup_of_normal_left.mp hxN
      have hzS : z ∈ (S : Subgroup G) := hZleS hzZ
      have hdzS : d * z ∈ (S : Subgroup G) := hdz.symm ▸ hx.1
      have hdS : d ∈ (S : Subgroup G) := by
        simpa [mul_assoc] using
          (S : Subgroup G).mul_mem hdzS ((S : Subgroup G).inv_mem hzS)
      have hdBot : d ∈ (⊥ : Subgroup G) := by
        rw [← disjoint_iff.mp hSD]
        exact ⟨hdS, hdD⟩
      have hdOne : d = 1 := Subgroup.mem_bot.mp hdBot
      have hzx : z = x := by simpa [hdOne] using hdz
      exact hzx ▸ hzZ
    · intro z hz
      refine ⟨hZleS hz, ?_⟩
      dsimp [N]
      exact (show Z ≤ D ⊔ Z from le_sup_right) hz

  let QN : Sylow p N := normalIntersectionSylow S N
  have hQNmap : (QN : Subgroup N).map N.subtype = Z := by
    rw [map_normalIntersectionSylow_eq_inf S N, hSN]
  have hfrattini : Subgroup.normalizer (Z : Set G) ⊔ N = ⊤ := by
    simpa [hQNmap] using QN.normalizer_sup_eq_top
  apply top_unique
  rw [← hfrattini]
  apply sup_le
  · exact le_sup_right
  · dsimp [N]
    exact sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right)

end Submission.OddOrder.BG.AppendixAB
