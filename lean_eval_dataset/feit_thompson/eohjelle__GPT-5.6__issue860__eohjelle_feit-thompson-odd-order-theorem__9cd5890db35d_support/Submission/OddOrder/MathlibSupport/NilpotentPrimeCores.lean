import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.Fitting
import Submission.OddOrder.MathlibSupport.Hall
import Submission.OddOrder.MathlibSupport.NilpotentNormalCenter

/-!
Prime cores of finite nilpotent groups.

In a finite nilpotent group the `p`-core is its unique Sylow `p`-subgroup,
and it forms the `p`-part of the direct-product decomposition with the
`p'`-core.  These facts also identify the prime support of the group with
that of its center.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- In a finite nilpotent group, every Sylow subgroup is the `p`-core. -/
theorem pCore_eq_sylow_of_isNilpotent [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    pCore p G = (P : Subgroup G) := by
  apply le_antisymm (pCore_le_sylow P)
  exact le_pCore P.isPGroup' (by infer_instance)

namespace IsPGroup

/-- Every `p`-subgroup of a finite nilpotent group lies in the `p`-core. -/
theorem le_pCore_of_isNilpotent [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P) :
    P ≤ pCore p G := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  rw [pCore_eq_sylow_of_isNilpotent S]
  exact hPS

end IsPGroup

/-- The `p`-core of a finite nilpotent group is nontrivial exactly when `p`
divides the group order. -/
theorem pCore_ne_bot_iff_dvd_card_of_isNilpotent
    [Finite G] [Group.IsNilpotent G]
    (p : ℕ) [Fact p.Prime] :
    pCore p G ≠ ⊥ ↔ p ∣ Nat.card G := by
  constructor
  · intro hcore
    have hpCore : p ∣ Nat.card (pCore p G) :=
      pCore_isPGroup.card_eq_or_dvd.resolve_left
        (fun hcard ↦ hcore (Subgroup.card_eq_one.mp hcard))
    exact hpCore.trans (pCore p G).card_subgroup_dvd_card
  · intro hpG
    let P : Sylow p G := Classical.choice Sylow.nonempty
    rw [pCore_eq_sylow_of_isNilpotent P]
    exact P.ne_bot_of_dvd_card hpG

/-- The `p`-core and the `p'`-core generate a finite nilpotent group. -/
theorem sup_pCore_pPrimeCore_eq_top_of_isNilpotent
    [Finite G] [Group.IsNilpotent G]
    (p : ℕ) [Fact p.Prime] :
    pCore p G ⊔ pPrimeCore p G = ⊤ := by
  have hfit : fittingCore G = ⊤ := by
    apply top_unique
    exact nilpotent_normal_le_fittingCore
      (H := (⊤ : Subgroup G)) (by infer_instance) (by infer_instance)
  apply top_unique
  rw [← hfit, fittingCore]
  apply iSup_le
  intro q
  letI : Fact (q : ℕ).Prime := ⟨q.property⟩
  by_cases hqp : (q : ℕ) = p
  · subst p
    exact le_sup_left
  · exact (pCore_le_pPrimeCore_of_ne (G := G) (p := p)
      (q := (q : ℕ)) (fun hpq ↦ hqp hpq.symm)).trans le_sup_right

/-- The `p`-core centralizes the `p'`-core. Nilpotence is not needed. -/
theorem pCore_le_centralizer_pPrimeCore [Finite G]
    (p : ℕ) [Fact p.Prime] :
    pCore p G ≤ Subgroup.centralizer (pPrimeCore p G : Set G) := by
  have hcomm := Subgroup.commute_of_normal_of_disjoint
    (pCore p G) (pPrimeCore p G) (by infer_instance) (by infer_instance)
    (disjoint_pCore_pPrimeCore (G := G) (p := p))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hcomm x y hx hy).eq.symm

private theorem primeSupport_center_eq_of_isNilpotent
    [Finite G] [Group.IsNilpotent G] :
    primeSupport (Nat.card (Subgroup.center G)) =
      primeSupport (Nat.card G) := by
  ext p
  constructor
  · rintro ⟨hp, hpcenter⟩
    exact ⟨hp, hpcenter.trans (Subgroup.center G).card_subgroup_dvd_card⟩
  · rintro ⟨hp, hpG⟩
    letI : Fact p.Prime := ⟨hp⟩
    have hcore : pCore p G ≠ ⊥ :=
      (pCore_ne_bot_iff_dvd_card_of_isNilpotent (G := G) p).2 hpG
    have hinter : pCore p G ⊓ Subgroup.center G ≠ ⊥ :=
      nilpotent_normal_inf_center_ne_bot (pCore p G) hcore
    have hinterP :
        IsPGroup p (pCore p G ⊓ Subgroup.center G : Subgroup G) :=
      pCore_isPGroup.to_inf_left
    have hpinter :
        p ∣ Nat.card (pCore p G ⊓ Subgroup.center G : Subgroup G) :=
      hinterP.card_eq_or_dvd.resolve_left
        (fun hcard ↦ hinter (Subgroup.card_eq_one.mp hcard))
    exact ⟨hp, hpinter.trans (Subgroup.card_dvd_of_le inf_le_right)⟩

/-- A finite nilpotent ambient subgroup and its center have the same prime
support. -/
theorem primeSupport_centerWithin_eq_of_isNilpotent
    (H : Subgroup G) [Finite H] [Group.IsNilpotent H] :
    primeSupport (Nat.card (centerWithin H)) =
      primeSupport (Nat.card H) := by
  rw [← map_center_eq_centerWithin H,
    Subgroup.card_map_of_injective H.subtype_injective]
  exact primeSupport_center_eq_of_isNilpotent (G := H)

end Submission.OddOrder.MathlibSupport
