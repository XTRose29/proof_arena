import Mathlib
import Submission.Helpers

open Representation

namespace Submission

/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/


theorem compact_group_semisimple {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : Representation ℝ G V)
    (hρ : Continuous fun p : G × V => ρ p.1 p.2) :
    ρ.IsSemisimpleRepresentation := by
  classical
  -- use Borel measurable structure and normalized Haar measure on the compact group
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  let K : TopologicalSpace.PositiveCompacts G :=
    ⟨⟨(Set.univ : Set G), isCompact_univ⟩, by simp⟩
  let μ : MeasureTheory.Measure G := MeasureTheory.Measure.haarMeasure K
  have μinv : μ.IsMulLeftInvariant := by
    dsimp [μ]
    infer_instance
  letI : μ.IsMulLeftInvariant := μinv
  have μhaar : μ.IsHaarMeasure := by
    dsimp [μ]
    infer_instance
  letI : μ.IsHaarMeasure := μhaar
  have μ_univ : μ Set.univ = 1 := by
    simpa [μ, K] using (MeasureTheory.Measure.haarMeasure_self (K₀ := K))
  -- it is enough to complement any invariant real subspace
  refine ⟨?_⟩
  intro σ
  -- an arbitrary (not invariant) linear projection onto it
  let i : σ.toSubmodule →ₗ[ℝ] V := σ.toSubmodule.subtype
  let π : V →ₗ[ℝ] σ.toSubmodule := i.leftInverse
  have πi (w : σ.toSubmodule) : π (w : V) = w := by
    exact LinearMap.leftInverse_apply_of_inj (Submodule.ker_subtype σ.toSubmodule) w
  -- its conjugates, with this convention so that left Haar invariance suffices
  let F (g : G) (v : V) : σ.toSubmodule :=
    ⟨ρ g ((π (ρ g⁻¹ v) : σ.toSubmodule) : V),
      σ.apply_mem_toSubmodule g (π (ρ g⁻¹ v)).property⟩
  have hFadd (g : G) (x y : V) : F g (x + y) = F g x + F g y := by
    apply Subtype.ext
    simp [F, map_add]
  have hFsmul (g : G) (a : ℝ) (x : V) : F g (a • x) = a • F g x := by
    apply Subtype.ext
    simp [F]
  have hFc (v : V) : Continuous (fun g : G => F g v) := by
    have h1 : Continuous (fun g : G => ρ g⁻¹ v) := by
      exact hρ.comp ((continuous_inv).prodMk continuous_const)
    have hp : Continuous (π : V → σ.toSubmodule) :=
      LinearMap.continuous_of_finiteDimensional π
    have h2 : Continuous (fun g : G => π (ρ g⁻¹ v)) := hp.comp h1
    have h2' : Continuous (fun g : G => ((π (ρ g⁻¹ v) : σ.toSubmodule) : V)) := h2.subtype_val
    have h3 : Continuous
        (fun g : G => ρ g ((π (ρ g⁻¹ v) : σ.toSubmodule) : V)) :=
      hρ.comp (continuous_id.prodMk h2')
    exact h3.subtype_mk _
  have hFi (v : V) : MeasureTheory.Integrable (fun g : G => F g v) μ := by
    exact (hFc v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P : V →ₗ[ℝ] σ.toSubmodule :=
    { toFun := fun v => ∫ g : G, F g v ∂μ
      map_add' := by
        intro x y
        simpa [hFadd] using
          (MeasureTheory.integral_add (hFi x) (hFi y))
      map_smul' := by
        intro a x
        simpa [hFsmul] using
          (MeasureTheory.integral_smul a (fun g : G => F g x) (μ := μ)) }
  have hFw (g : G) (w : σ.toSubmodule) : F g (w : V) = w := by
    apply Subtype.ext
    change ρ g ((π (ρ g⁻¹ (w : V)) : σ.toSubmodule) : V) = (w : V)
    have hi : π (ρ g⁻¹ (w : V)) =
        (⟨ρ g⁻¹ (w : V), σ.apply_mem_toSubmodule g⁻¹ w.property⟩ : σ.toSubmodule) := by
      simpa using (πi (⟨ρ g⁻¹ (w : V), σ.apply_mem_toSubmodule g⁻¹ w.property⟩ : σ.toSubmodule))
    rw [hi]
    change ρ g (ρ g⁻¹ (w : V)) = (w : V)
    calc
      ρ g (ρ g⁻¹ (w : V)) = ρ (g * g⁻¹) (w : V) := by
        rw [ρ.map_mul]
        rfl
      _ = (w : V) := by simp
  have Pret (w : σ.toSubmodule) : P (w : V) = w := by
    change (∫ g : G, F g (w : V) ∂μ) = w
    have hc : (∫ _g : G, w ∂μ) = w := by
      rw [MeasureTheory.integral_const]
      simp [MeasureTheory.Measure.real_def, μ_univ]
    simpa [hFw] using hc
  -- equivariance of the averaged projection
  have hFmul (a k : G) (v : V) :
      F (a * k) (ρ a v) =
        ⟨ρ a ((F k v : σ.toSubmodule) : V),
          σ.apply_mem_toSubmodule a (F k v).property⟩ := by
    apply Subtype.ext
    change ρ (a*k) ((π (ρ (a*k)⁻¹ (ρ a v)) : σ.toSubmodule) : V) =
      ρ a ((F k v : σ.toSubmodule) : V)
    -- elementary cancellation in the representation
    simp [F, mul_inv_rev, ρ.map_mul]
  let L (a : G) : σ.toSubmodule →ₗ[ℝ] σ.toSubmodule :=
    { toFun := fun w => ⟨ρ a (w : V), σ.apply_mem_toSubmodule a w.property⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro c x; ext; simp }
  have Peq (a : G) (v : V) : P (ρ a v) = L a (P v) := by
    change (∫ g : G, F g (ρ a v) ∂μ) = L a (∫ g : G, F g v ∂μ)
    calc
      (∫ g : G, F g (ρ a v) ∂μ) =
          ∫ g : G, F (a * g) (ρ a v) ∂μ := by
            symm
            exact MeasureTheory.integral_mul_left_eq_self
              (fun g : G => F g (ρ a v)) a
      _ = ∫ g : G, L a (F g v) ∂μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with g
            exact hFmul a g v
      _ = L a (∫ g : G, F g v ∂μ) := by
            let La : σ.toSubmodule →L[ℝ] σ.toSubmodule :=
              LinearMap.toContinuousLinearMap (L a)
            simpa [La] using
              (La.integral_comp_comm (hFi v))
  let τ : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker P
      apply_mem_toSubmodule := by
        intro g v hv
        change P (ρ g v) = 0
        have hv' : P v = 0 := (LinearMap.mem_ker).1 hv
        rw [Peq, hv']
        exact map_zero (L g) }
  refine ⟨τ, ?_⟩
  have hc : IsCompl σ.toSubmodule (LinearMap.ker P) :=
    LinearMap.isCompl_of_proj Pret
  constructor
  · -- disjointness
    rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    -- On subrepresentations `toSubmodule` carries bottom and infimum
    -- to the corresponding subspace operations.
    change σ.toSubmodule ⊓ (LinearMap.ker P) = (⊥ : Submodule ℝ V)
    exact (disjoint_iff.mp hc.disjoint)
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    change σ.toSubmodule ⊔ (LinearMap.ker P) = (⊤ : Submodule ℝ V)
    exact (codisjoint_iff.mp hc.codisjoint)


end Submission
