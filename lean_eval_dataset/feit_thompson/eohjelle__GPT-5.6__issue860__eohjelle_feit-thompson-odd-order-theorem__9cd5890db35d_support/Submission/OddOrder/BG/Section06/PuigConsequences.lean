import Submission.OddOrder.BG.AppendixAB.OddPStableConsequences
import Submission.OddOrder.BG.AppendixAB.PuigFactorization
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient

/-!
Bender--Glauberman Section 6, Theorems 6.1 and 6.2.

Theorem 6.1 is the odd-order solvable specialization of Appendix A
`p`-stability.  Theorem 6.2 packages the two conclusions of Appendix B.4 for
a Sylow subgroup.  MathComp's subgroup products are represented by joins.
-/

namespace Submission.OddOrder.BG.Section06

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- `BGsection6.odd_p_abelian_constrained`, Bender--Glauberman Theorem 6.1. -/
theorem odd_p_abelian_constrained {p : ℕ} [Fact p.Prime] [IsSolvable G]
    (hodd : Odd (Nat.card G)) : IsPAbelianConstrained p G :=
  AppendixAB.odd_isPAbelianConstrained hodd

omit [Finite G] in
/-- The characteristic-center result from Appendix B, exposed under the
Section 6 source name. -/
theorem center_Puig_char :
    (centerWithin (puig (⊤ : Subgroup G))).Characteristic := by
  infer_instance

/-- The trivial-center consequence from Appendix B, exposed under the
Section 6 source name. -/
theorem trivg_center_Puig_pgroup {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G)
    (hcenter : centerWithin (puig (⊤ : Subgroup G)) = ⊥) :
    (⊤ : Subgroup G) = ⊥ :=
  AppendixAB.eq_bot_of_centerWithin_puig_eq_bot
    (p := p) (⊤ : Subgroup G) (hG.to_subgroup ⊤) hcenter

/-- `BGsection6.Puig_factorisation`, the factorization half of Theorem 6.2.
The source product equality is expressed as the equivalent join equality. -/
theorem Puig_factorisation {p : ℕ} [Fact p.Prime] [IsSolvable G]
    (hodd : Odd (Nat.card G)) (S : Sylow p G) :
    pPrimeCore p G ⊔
        Subgroup.normalizer (centerWithin (puig (S : Subgroup G)) : Set G) = ⊤ :=
  AppendixAB.Puig_factorization hodd S

/-- `BGsection6.Puig_center_p'core_normal`, the main statement of Theorem
6.2.  The join is the subgroup product from the source because the `p'`-core
is normal. -/
theorem Puig_center_p'core_normal {p : ℕ} [Fact p.Prime] [IsSolvable G]
    (hodd : Odd (Nat.card G)) (S : Sylow p G) :
    (pPrimeCore p G ⊔ centerWithin (puig (S : Subgroup G))).Normal := by
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
      AppendixAB.map_centerWithin_puig_eq_of_injective_on
        q (S : Subgroup G) hqS

  let Sq : Sylow p (G ⧸ D) :=
    S.mapSurjective (QuotientGroup.mk'_surjective D)
  have hSq : (Sq : Subgroup (G ⧸ D)) = (S : Subgroup G).map q := by
    rfl
  have hoddQuotient : Odd (Nat.card (G ⧸ D)) := odd_natCard_quotient D hodd
  have hZmapNormal : (Z.map q).Normal := by
    rw [hZmap, ← hSq]
    simpa [D] using
      (AppendixAB.Puig_center_normal hoddQuotient Sq
        (pPrimeCore_quotient_self_eq_bot (G := G) (p := p)))
  letI : (Z.map q).Normal := hZmapNormal
  have hcomap : D ⊔ Z = (Z.map q).comap q := by
    dsimp [q]
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  change (D ⊔ Z).Normal
  rw [hcomap]
  infer_instance

/-- `BGsection6.Puig_center_normal`, the special case of Theorem 6.2 when
the `p'`-core is trivial. -/
theorem Puig_center_normal {p : ℕ} [Fact p.Prime] [IsSolvable G]
    (hodd : Odd (Nat.card G)) (S : Sylow p G)
    (hprimeCore : pPrimeCore p G = ⊥) :
    (centerWithin (puig (S : Subgroup G))).Normal :=
  AppendixAB.Puig_center_normal hodd S hprimeCore

end Submission.OddOrder.BG.Section06
