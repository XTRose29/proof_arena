import Mathlib

open Representation

namespace Submission

theorem compact_group_semisimple {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : Representation ℝ G V)
    (hρ : Continuous fun p : G × V => ρ p.1 p.2) :
    ρ.IsSemisimpleRepresentation := by
  classical
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  let μ : MeasureTheory.Measure G :=
    MeasureTheory.Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  refine { exists_isCompl := ?_ }
  intro W
  let p : V →ₗ[ℝ] W.toSubmodule := W.toSubmodule.subtype.leftInverse
  have hp (w : W.toSubmodule) : p (w : V) = w := by
    simpa [p] using
      (LinearMap.leftInverse_apply_of_inj W.toSubmodule.ker_subtype w)
  let F : V → G → W.toSubmodule := fun v g =>
    ⟨ρ g (p (ρ g⁻¹ v)), W.apply_mem_toSubmodule g (p (ρ g⁻¹ v)).property⟩
  have hF_cont (v : V) : Continuous (F v) := by
    have hinner : Continuous fun g : G => ρ g⁻¹ v :=
      hρ.comp (continuous_inv.prodMk continuous_const)
    have hpv : Continuous fun g : G => (p (ρ g⁻¹ v) : V) :=
      continuous_subtype_val.comp (p.continuous_of_finiteDimensional.comp hinner)
    exact (hρ.comp (continuous_id.prodMk hpv)).subtype_mk _
  have hF_int (v : V) : MeasureTheory.Integrable (F v) μ := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (hF_cont v).continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ
  have hF_add (x y : V) : F (x + y) = fun g => F x g + F y g := by
    funext g
    apply Subtype.ext
    simp [F]
  have hF_smul (c : ℝ) (x : V) : F (c • x) = fun g => c • F x g := by
    funext g
    apply Subtype.ext
    simp [F]
  let avg : V →ₗ[ℝ] W.toSubmodule :=
    { toFun := fun v => ∫ g, F v g ∂μ
      map_add' := fun x y => by
        rw [hF_add, MeasureTheory.integral_add (hF_int x) (hF_int y)]
      map_smul' := fun c x => by
        rw [hF_smul, MeasureTheory.integral_smul]
        simp only [RingHom.id_apply] }
  have hF_fixed (w : W.toSubmodule) (g : G) : F (w : V) g = w := by
    let w_inv : W.toSubmodule :=
      ⟨ρ g⁻¹ (w : V), W.apply_mem_toSubmodule g⁻¹ w.property⟩
    have hp_inv : p (ρ g⁻¹ (w : V)) = w_inv := by
      change p (w_inv : V) = w_inv
      exact hp w_inv
    apply Subtype.ext
    change ρ g (p (ρ g⁻¹ (w : V)) : V) = (w : V)
    rw [hp_inv]
    exact ρ.self_inv_apply g (w : V)
  have hμ : μ.real Set.univ = 1 := by
    rw [MeasureTheory.Measure.real_def]
    have hμ' : μ Set.univ = 1 := by
      simpa [μ] using
        (MeasureTheory.Measure.haarMeasure_self
          (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G)))
    rw [hμ']
    norm_num
  have havg_fixed (w : W.toSubmodule) : avg (w : V) = w := by
    change (∫ g, F (w : V) g ∂μ) = w
    simp_rw [hF_fixed w]
    rw [MeasureTheory.integral_const, hμ, one_smul]
  have hF_mul (a g : G) (v : V) :
      F (ρ a v) (a * g) = W.toRepresentation a (F v g) := by
    apply Subtype.ext
    simp [F, Subrepresentation.toRepresentation, mul_inv_rev, ← Module.End.mul_apply,
      ← map_mul]
  have havg_equivariant (a : G) (v : V) :
      avg (ρ a v) = W.toRepresentation a (avg v) := by
    let A : W.toSubmodule →L[ℝ] W.toSubmodule :=
      ⟨W.toRepresentation a, (W.toRepresentation a).continuous_of_finiteDimensional⟩
    change (∫ g, F (ρ a v) g ∂μ) = A (∫ g, F v g ∂μ)
    calc
      (∫ g, F (ρ a v) g ∂μ) = ∫ g, F (ρ a v) (a * g) ∂μ :=
        (MeasureTheory.integral_mul_left_eq_self (F (ρ a v)) a).symm
      _ = ∫ g, A (F v g) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun g => hF_mul a g v
      _ = A (∫ g, F v g ∂μ) := A.integral_comp_comm (hF_int v)
  let Q : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker avg
      apply_mem_toSubmodule := fun g v hv => by
        change avg (ρ g v) = 0
        rw [havg_equivariant, hv, map_zero] }
  refine ⟨Q, ?_⟩
  have hcomp : IsCompl W.toSubmodule (LinearMap.ker avg) :=
    LinearMap.isCompl_of_proj havg_fixed
  constructor
  · rw [disjoint_iff_inf_le]
    intro v hv
    change v ∈ (⊥ : Submodule ℝ V)
    apply hcomp.1.le_bot
    exact hv
  · rw [codisjoint_iff_le_sup]
    intro v _
    change v ∈ W.toSubmodule ⊔ LinearMap.ker avg
    exact hcomp.2.top_le Submodule.mem_top

end Submission
