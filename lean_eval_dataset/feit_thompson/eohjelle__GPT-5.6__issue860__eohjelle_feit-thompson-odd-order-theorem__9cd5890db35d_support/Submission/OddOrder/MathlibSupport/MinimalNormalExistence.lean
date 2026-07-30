import Submission.OddOrder.MathlibSupport.ChiefFactor

/-!
Finite-lattice existence lemmas for minimal normal subgroups and chief
factors.  These are the mathlib-shaped replacement for the `mingroup_exists`
and chief-series selection steps used throughout the MathComp development.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

theorem exists_minimalNormal_le {K : Subgroup G}
    (hKnormal : K.Normal) (hK : K ≠ ⊥) :
    ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ K := by
  let P : Subgroup G → Prop := fun M ↦ M.Normal ∧ M ≤ K ∧ M ≠ ⊥
  have hPK : P K := ⟨hKnormal, le_rfl, hK⟩
  obtain ⟨M, hMK, hMmin⟩ := Finite.exists_le_minimal hPK
  refine ⟨M, ?_, hMK⟩
  refine ⟨hMmin.1.2.2, hMmin.1.1, ?_⟩
  intro N hNnormal hNM hN
  have hPN : P N := ⟨hNnormal, hNM.trans hMK, hN⟩
  exact (hMmin.eq_of_ge hPN hNM).le

/-- Between two distinct normal subgroups of a finite group there is a chief
factor whose upper subgroup remains below the prescribed upper bound. -/
theorem exists_chiefFactor_le {V U : Subgroup G} [V.Normal]
    (hVU : V < U) (hUnormal : U.Normal) :
    ∃ W : Subgroup G, IsChiefFactor V W ∧ W ≤ U := by
  let q := QuotientGroup.mk' V
  have hUimageNormal : (U.map q).Normal :=
    Subgroup.Normal.map hUnormal q (QuotientGroup.mk'_surjective V)
  have hUimage : U.map q ≠ ⊥ := by
    intro himage
    have hUV : U ≤ q.ker := (Subgroup.map_eq_bot_iff U).mp himage
    have hUV' : U ≤ V := by
      simpa [q, QuotientGroup.ker_mk'] using hUV
    exact (not_le_of_gt hVU) hUV'
  obtain ⟨M, hMmin, hMU⟩ :=
    exists_minimalNormal_le hUimageNormal hUimage
  let W : Subgroup G := M.comap q
  have hVW : V ≤ W := by
    dsimp [W]
    intro x hx
    change q x ∈ M
    have hqx : q x = 1 := by
      exact QuotientGroup.eq_one_iff x |>.mpr hx
    rw [hqx]
    exact M.one_mem
  have hWnormal : W.Normal := by
    dsimp [W]
    exact Subgroup.Normal.comap hMmin.normal q
  have hWU : W ≤ U := by
    have hkerU : q.ker ≤ U := by
      simpa [q, QuotientGroup.ker_mk'] using hVU.le
    calc
      W = M.comap q := rfl
      _ ≤ (U.map q).comap q := Subgroup.comap_mono hMU
      _ = U := Subgroup.comap_map_eq_self hkerU
  have hWimage : W.map q = M := by
    dsimp [W]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective V) M
  refine ⟨W, ⟨hVW, hWnormal, ?_⟩, hWU⟩
  rwa [hWimage]

end Submission.OddOrder.MathlibSupport
