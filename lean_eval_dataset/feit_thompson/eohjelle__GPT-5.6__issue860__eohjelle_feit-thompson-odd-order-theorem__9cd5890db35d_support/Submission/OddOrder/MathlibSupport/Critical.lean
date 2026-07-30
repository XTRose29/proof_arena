import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Nilpotent
import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial

/-!
Critical subgroups and the small characteristic-subgroup infrastructure used
in Thompson's critical subgroup theorem.

The predicate `IsCritical` is the mathlib-shaped form of MathComp's
`critical A B`, with the ambient group represented by its type and `A` by a
subgroup.  Thus `centerWithin H` is the center of `H`, transported into the
ambient group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- Intersections of characteristic subgroups are characteristic. -/
instance characteristic_inf (H K : Subgroup G)
    [H.Characteristic] [K.Characteristic] :
    (H ⊓ K).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  rw [Subgroup.map_inf H K e.toMonoidHom e.injective,
    Subgroup.characteristic_iff_map_eq.mp
      (show H.Characteristic from inferInstance) e,
    Subgroup.characteristic_iff_map_eq.mp
      (show K.Characteristic from inferInstance) e]

/-- Joins of characteristic subgroups are characteristic. -/
instance characteristic_sup (H K : Subgroup G)
    [H.Characteristic] [K.Characteristic] :
    (H ⊔ K).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  rw [Subgroup.map_sup,
    Subgroup.characteristic_iff_map_eq.mp
      (show H.Characteristic from inferInstance) e,
    Subgroup.characteristic_iff_map_eq.mp
      (show K.Characteristic from inferInstance) e]

/-- Characteristicity is transitive through a subgroup subtype. -/
instance characteristic_map_subtype (H : Subgroup G) (K : Subgroup H)
    [H.Characteristic] [K.Characteristic] :
    (K.map H.subtype).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  have hmapH : H.map e.toMonoidHom = H :=
    Subgroup.characteristic_iff_map_eq.mp
      (show H.Characteristic from inferInstance) e
  let eH : H ≃* H :=
    (e.subgroupMap H).trans (MulEquiv.subgroupCongr hmapH)
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with ⟨h, hh, rfl⟩
  refine ⟨eH h, ?_, rfl⟩
  exact
    (Subgroup.characteristic_iff_map_le.mp
      (show K.Characteristic from inferInstance) eH)
      (Subgroup.mem_map_of_mem eH.toMonoidHom hh)

/-- The center of a characteristic subgroup, transported into the ambient
group, is characteristic. -/
instance centerWithin_characteristic (H : Subgroup G) [H.Characteristic] :
    (centerWithin H).Characteristic := by
  rw [← map_center_eq_centerWithin H]
  infer_instance

/-- The first omega subgroup of a nontrivial finite `p`-group is nontrivial. -/
theorem omegaOne_ne_bot_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G]
    (hG : IsPGroup p G) (hcard : Nat.card G ≠ 1) :
    omegaOne p G ≠ ⊥ := by
  have hpCard : p ∣ Nat.card G := hG.card_eq_or_dvd.resolve_left hcard
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' p hpCard
  have hxne : x ≠ 1 := by
    intro hx
    rw [hx, orderOf_one] at hxorder
    exact (Fact.out : p.Prime).ne_one hxorder.symm
  have hxpow : x ^ p = 1 := by
    rw [← hxorder]
    exact pow_orderOf_eq_one x
  intro homega
  have hxmem : x ∈ omegaOne p G := mem_omegaOne_of_pow_eq_one p hxpow
  rw [homega] at hxmem
  exact hxne (Subgroup.mem_bot.mp hxmem)

/-- MathComp's `critical H G`: `H` is characteristic, its Frattini subgroup
and the ambient mixed commutator lie in its center, and it is
self-centralizing modulo that center. -/
structure IsCritical (H : Subgroup G) : Prop where
  characteristic : H.Characteristic
  frattini_le_center : frattini H ≤ Subgroup.center H
  commutator_le_center : ⁅(⊤ : Subgroup G), H⁆ ≤ centerWithin H
  centralizer_eq_center :
    Subgroup.centralizer (H : Set G) = centerWithin H

/-- MathComp's `critical_class2`: a critical subgroup has nilpotency class at
most two. -/
theorem critical_class2 {H : Subgroup G} (hH : IsCritical H) :
    Group.nilpotencyClass H ≤ 2 := by
  have hcentral : _root_.commutator H ≤ Subgroup.center H := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hcAmbient : (c : G) ∈ ⁅H, H⁆ := by
      rw [← H.map_subtype_commutator]
      exact Subgroup.mem_map_of_mem H.subtype hc
    have hcWithin : (c : G) ∈ centerWithin H :=
      hH.commutator_le_center
        (Subgroup.commutator_mono le_top le_rfl hcAmbient)
    exact (mem_centerWithin.mp hcWithin).2 (x : G) x.property
  have hbot :
      Subgroup.lowerCentralSeries (⊤ : Subgroup H) 2 = ⊥ := by
    rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ,
      Subgroup.top_lowerCentralSeries_one,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x _
    exact Subgroup.mem_center_iff.mp (hcentral hz) x
  letI : Group.IsNilpotent H :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := H)).mpr ⟨2, hbot⟩
  exact
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le
      (G := H) (n := 2)).mp hbot

end Submission.OddOrder.MathlibSupport
