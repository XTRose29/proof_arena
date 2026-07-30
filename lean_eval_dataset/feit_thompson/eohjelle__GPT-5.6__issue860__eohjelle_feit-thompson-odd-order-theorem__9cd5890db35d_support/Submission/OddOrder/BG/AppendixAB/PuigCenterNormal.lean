import Submission.OddOrder.BG.AppendixAB.OddPStableConsequences
import Submission.OddOrder.BG.AppendixAB.PuigRestriction
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.SylowFunctorial
import Submission.OddOrder.MathlibSupport.SylowIntersection

/-!
Normality of the center of the Puig subgroup.

This ports `BGappendixAB.Puig_center_normal`, Bender--Glauberman Theorem
B.4(b).  The subgroup called `C` in the source is the inverse image of the
`p`-core of the quotient by the centralizer of the center of the Puig subgroup
of `O_p(G)`.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- `BGappendixAB.Puig_center_normal` (Bender--Glauberman Theorem B.4(b)). -/
theorem Puig_center_normal {p : ℕ} [Fact p.Prime] [IsSolvable G]
    (hodd : Odd (Nat.card G)) (S : Sylow p G)
    (hprimeCore : pPrimeCore p G = ⊥) :
    (centerWithin (puig (S : Subgroup G))).Normal := by
  let T : Subgroup G := pCore p G
  let L : Subgroup G := puig (S : Subgroup G)
  let Z : Subgroup G := centerWithin L
  let Y : Subgroup G := centerWithin (puig T)
  letI : T.Characteristic := by
    dsimp [T]
    infer_instance
  letI : Y.Characteristic := by
    dsimp [Y]
    infer_instance
  letI : Y.Normal := by infer_instance

  have hPuigComparison := odd_pCore_sylow_puig_sub hodd S hprimeCore
  have hZY : Z ≤ Y := by
    intro z hz
    have hzCentralizer : z ∈ centralizerWithin (S : Subgroup G)
        (puigInf (S : Subgroup G)) := by
      refine ⟨puig_le (S : Subgroup G) hz.1, ?_⟩
      intro x hx
      exact hz.2 x (puigInf_le_puig (S : Subgroup G) hx)
    have hzInfS : z ∈ puigInf (S : Subgroup G) :=
      centralizerWithin_puigInf_le (p := p) (S : Subgroup G) S.isPGroup'
        hzCentralizer
    have hzPuigT : z ∈ puig T :=
      puigInf_le_puig T (hPuigComparison.1 hzInfS)
    refine ⟨hzPuigT, ?_⟩
    intro x hx
    exact hz.2 x (hPuigComparison.2 hx)

  have hYp : IsPGroup p Y :=
    IsPGroup.to_le pCore_isPGroup
      ((centralizerWithin_le_left (puig T) (puig T)).trans (puig_le T))
  have hYS : Y ≤ (S : Subgroup G) :=
    (centralizerWithin_le_left (puig T) (puig T)).trans
      (hPuigComparison.2.trans (puig_le (S : Subgroup G)))
  have hYInfS : Y ≤ puigInf (S : Subgroup G) := by
    rw [puigInf]
    apply normal_abelian_le_puigAt
    · have hcard : 0 < Nat.card (S : Subgroup G) := Nat.card_pos
      omega
    · exact hYS
    · rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : Y.Normal)]
      exact le_top
    · exact fun x y ↦ mul_comm' x y

  have hLgroup : IsPGroup p L :=
    IsPGroup.to_le S.isPGroup' (puig_le (S : Subgroup G))
  have hLgenerated : GeneratedBy (PNormalizedAbelian p Y) L := by
    apply normalizedGenerated_isPGroup hLgroup
    simpa [L, puig_def] using
      normalizedGenerated_mono hYInfS
        (puigGenerated (S : Subgroup G) (puigInf (S : Subgroup G)))

  let CY : Subgroup G := Subgroup.centralizer (Y : Set G)
  letI : CY.Characteristic := by
    dsimp [CY]
    infer_instance
  letI : CY.Normal := by infer_instance
  let C : Subgroup G :=
    (pCore p (G ⧸ CY)).comap (QuotientGroup.mk' CY)
  letI : C.Normal := by
    dsimp [C]
    infer_instance

  have hLC : L ≤ C := by
    change L ≤ (pCore p (G ⧸ CY)).comap (QuotientGroup.mk' CY)
    apply Subgroup.map_le_iff_le_comap.mp
    exact odd_abelianGenerated_quotient_le_pCore hodd hYp hLgenerated

  let Q : Sylow p C := normalIntersectionSylow S C
  let QG : Subgroup G := (Q : Subgroup C).map C.subtype
  have hQG_eq : QG = (S : Subgroup G) ⊓ C := by
    dsimp [QG, Q]
    exact map_normalIntersectionSylow_eq_inf S C
  have hLQG : L ≤ QG := by
    rw [hQG_eq]
    exact le_inf (puig_le (S : Subgroup G)) hLC
  have hQGS : QG ≤ (S : Subgroup G) := by
    rw [hQG_eq]
    exact inf_le_left
  have hPuigQG : puig QG = L :=
    puig_eq_of_puig_le_of_le hQGS hLQG

  let f : C →* pCore p (G ⧸ CY) :=
    ((QuotientGroup.mk' CY).comp C.subtype).codRestrict _ (fun x ↦ x.property)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective CY (y : G ⧸ CY)
    have hxC : x ∈ C := by
      change QuotientGroup.mk' CY x ∈ pCore p (G ⧸ CY)
      rw [hx]
      exact y.property
    refine ⟨⟨x, hxC⟩, ?_⟩
    exact Subtype.ext hx
  have hQmap : (Q : Subgroup C).map f = ⊤ :=
    Sylow.map_eq_top_of_surjective_of_isPGroup Q f hf pCore_isPGroup

  have hCYC : CY ≤ C := by
    intro x hx
    change QuotientGroup.mk' CY x ∈ pCore p (G ⧸ CY)
    have hxOne : QuotientGroup.mk' CY x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [hxOne]
    exact Subgroup.one_mem _
  have hCQCY : C ≤ QG ⊔ CY := by
    intro x hx
    let xC : C := ⟨x, hx⟩
    have hxMap : f xC ∈ (Q : Subgroup C).map f := by
      rw [hQmap]
      exact Subgroup.mem_top _
    obtain ⟨q, hqQ, hqx⟩ := hxMap
    have hquot : QuotientGroup.mk' CY (q : G) = QuotientGroup.mk' CY x := by
      exact congrArg Subtype.val hqx
    have hdiff : (q : G)⁻¹ * x ∈ CY := QuotientGroup.eq.mp hquot
    have hqG : (q : G) ∈ QG := ⟨q, hqQ, rfl⟩
    have hqSup : (q : G) ∈ QG ⊔ CY :=
      (show QG ≤ QG ⊔ CY from le_sup_left) hqG
    have hdiffSup : (q : G)⁻¹ * x ∈ QG ⊔ CY :=
      (show CY ≤ QG ⊔ CY from le_sup_right) hdiff
    have hprod : (q : G) * ((q : G)⁻¹ * x) ∈ QG ⊔ CY :=
      (QG ⊔ CY).mul_mem hqSup hdiffSup
    simpa [mul_assoc] using hprod

  have hfrattini : Subgroup.normalizer (QG : Set G) ⊔ C = ⊤ := by
    simpa [QG] using Q.normalizer_sup_eq_top
  have hgenerate : CY ⊔ Subgroup.normalizer (QG : Set G) = ⊤ := by
    apply top_unique
    rw [← hfrattini]
    apply sup_le
    · exact le_sup_right
    · exact hCQCY.trans (sup_le
        (Subgroup.le_normalizer.trans le_sup_right) le_sup_left)

  have hnormalizerL : Subgroup.normalizer (QG : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hQmapConj : QG.map (MulAut.conj g).toMonoidHom = QG :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    calc
      L.map (MulAut.conj g).toMonoidHom =
          (puig QG).map (MulAut.conj g).toMonoidHom := by rw [hPuigQG]
      _ = puig (QG.map (MulAut.conj g).toMonoidHom) :=
        map_puig_equiv (MulAut.conj g) QG
      _ = puig QG := congrArg puig hQmapConj
      _ = L := hPuigQG
  have hnormalizerZ : Subgroup.normalizer (QG : Set G) ≤
      Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg z hz
    have hz' : z ∈ (Subgroup.center L).map L.subtype := by
      simpa [Z, map_center_eq_centerWithin]
    have := characteristic_map_subtype_invariant_under_normalizer
      L (Subgroup.normalizer (QG : Set G)) (Subgroup.center L)
      hnormalizerL g hg z hz'
    simpa [Z, map_center_eq_centerWithin] using this
  have hcentralizerZ : CY ≤ Subgroup.normalizer (Z : Set G) := by
    exact (Subgroup.centralizer_le hZY).trans
      (Subgroup.centralizer_le_normalizer (Z : Set G))
  have hnormalizerTop : Subgroup.normalizer (Z : Set G) = ⊤ := by
    apply top_unique
    rw [← hgenerate]
    exact sup_le hcentralizerZ hnormalizerZ
  exact Subgroup.normalizer_eq_top_iff.mp hnormalizerTop

end Submission.OddOrder.BG.AppendixAB
