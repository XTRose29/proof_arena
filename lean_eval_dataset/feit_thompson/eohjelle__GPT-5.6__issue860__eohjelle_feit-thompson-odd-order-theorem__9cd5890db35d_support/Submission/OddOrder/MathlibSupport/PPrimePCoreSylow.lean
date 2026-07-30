import Submission.OddOrder.MathlibSupport.PPrimePCore
import Submission.OddOrder.MathlibSupport.SylowFunctorial

/-!
Sylow subgroups of the two-step `p'`, `p` core.

The canonical quotient maps `O_{p',p}(G)` onto
`O_p(G / O_{p'}(G))`.  Consequently every Sylow `p`-subgroup of the former
maps onto the latter.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- The core quotient, with its range restricted to the quotient `p`-core. -/
noncomputable def pPrimePCoreQuotientHom (p : ℕ) (G : Type*) [Group G]
    [Finite G] :
    pPrimePCore p G →* pCore p (G ⧸ pPrimeCore p G) :=
  ((QuotientGroup.mk' (pPrimeCore p G)).comp
      (pPrimePCore p G).subtype).codRestrict _ (fun x ↦ by
    have hx : QuotientGroup.mk' (pPrimeCore p G) (x : G) ∈
        (pPrimePCore p G).map (QuotientGroup.mk' (pPrimeCore p G)) :=
      ⟨x, x.property, rfl⟩
    rw [pPrimePCore_map_quotient_eq] at hx
    exact hx)

theorem pPrimePCoreQuotientHom_surjective :
    Function.Surjective (pPrimePCoreQuotientHom p G) := by
  intro y
  have hy : (y : G ⧸ pPrimeCore p G) ∈
      (pPrimePCore p G).map (QuotientGroup.mk' (pPrimeCore p G)) := by
    rw [pPrimePCore_map_quotient_eq]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨⟨x, hx⟩, ?_⟩
  exact Subtype.ext hxy

theorem sylow_map_pPrimePCoreQuotientHom_eq_top [Fact p.Prime]
    (P : Sylow p (pPrimePCore p G)) :
    (P : Subgroup (pPrimePCore p G)).map
        (pPrimePCoreQuotientHom p G) = ⊤ :=
  Sylow.map_eq_top_of_surjective_of_isPGroup P
    (pPrimePCoreQuotientHom p G) pPrimePCoreQuotientHom_surjective
    pCore_isPGroup

theorem sylow_pPrimePCore_map_quotient_eq [Fact p.Prime]
    (P : Sylow p (pPrimePCore p G)) :
    ((P : Subgroup (pPrimePCore p G)).map
        (pPrimePCore p G).subtype).map
        (QuotientGroup.mk' (pPrimeCore p G)) =
      pCore p (G ⧸ pPrimeCore p G) := by
  let f := pPrimePCoreQuotientHom p G
  let O := pCore p (G ⧸ pPrimeCore p G)
  have hPmap : (P : Subgroup (pPrimePCore p G)).map f = ⊤ := by
    exact sylow_map_pPrimePCoreQuotientHom_eq_top P
  calc
    ((P : Subgroup (pPrimePCore p G)).map
          (pPrimePCore p G).subtype).map
          (QuotientGroup.mk' (pPrimeCore p G)) =
        (P : Subgroup (pPrimePCore p G)).map
          ((QuotientGroup.mk' (pPrimeCore p G)).comp
            (pPrimePCore p G).subtype) := by
      rw [Subgroup.map_map]
    _ = ((P : Subgroup (pPrimePCore p G)).map f).map O.subtype := by
      rw [Subgroup.map_map]
      rfl
    _ = (⊤ : Subgroup O).map O.subtype := by rw [hPmap]
    _ = O.subtype.range := (MonoidHom.range_eq_map O.subtype).symm
    _ = O := O.range_subtype

end Submission.OddOrder.MathlibSupport
