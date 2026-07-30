import Submission.SphereCap

open scoped unitInterval

noncomputable section

namespace Submission.SphereLocalNormal

open Set
open Submission.SphereRegularApprox

variable {m : ℕ}

/-- A cap collapse can be chosen to be constant off any prescribed open
neighborhood of the north-pole fiber. -/
theorem exists_capDatum_constant_off
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    {U : Set (Fin (m + 1) → I)}
    (hU : IsOpen U)
    (hfiber :
      {t |
        q t = -(SphereGenerator.canonicalBasepoint m)} ⊆ U) :
    ∃ d : SphereCap.Datum,
      0 < d.cutoff ∧
      GenLoop.Homotopic q (SphereCap.genLoop d q) ∧
      (∀ t ∉ U, vertical m (q t) ≤ d.cutoff) ∧
      ∀ t ∉ U,
        SphereCap.genLoop d q t =
          SphereGenerator.canonicalBasepoint m := by
  by_cases hK : Uᶜ.Nonempty
  · have hcompact : IsCompact Uᶜ :=
      by
        simpa only [compl_eq_univ_sdiff] using
          isCompact_univ.diff hU
    have hcontinuous :
        Continuous
          (fun t : Fin (m + 1) → I =>
            vertical m (q t)) := by
      fun_prop
    obtain ⟨t₀, ht₀, hmax⟩ :=
      hcompact.exists_isMaxOn hK hcontinuous.continuousOn
    let z : ℝ := vertical m (q t₀)
    have hzlt : z < 1 := by
      have hzle : z ≤ 1 := SphereCap.vertical_le_one (q t₀)
      exact lt_of_le_of_ne hzle fun hz => by
        have hroot :
            q t₀ = -(SphereGenerator.canonicalBasepoint m) :=
          SphereCap.eq_antipode_of_vertical_eq_one (q t₀) hz
        exact ht₀ (hfiber hroot)
    let c : ℝ := (max z 0 + 1) / 2
    have hcpos : 0 < c := by
      have hmaxge : 0 ≤ max z 0 := le_max_right _ _
      dsimp only [c]
      linarith
    have hcneg : -1 < c := by
      linarith
    have hcone : c < 1 := by
      have hmaxlt : max z 0 < 1 :=
        max_lt hzlt (by norm_num)
      dsimp only [c]
      linarith
    let d : SphereCap.Datum :=
      ⟨c, hcneg, hcone⟩
    refine ⟨d, hcpos, SphereCap.genLoop_homotopic d q, ?_, ?_⟩
    · intro t ht
      have htK : t ∈ Uᶜ := ht
      have htz : vertical m (q t) ≤ z :=
        hmax htK
      have hzc : z ≤ c := by
        have hzmax : z ≤ max z 0 := le_max_left _ _
        have hmaxlt : max z 0 < 1 :=
          max_lt hzlt (by norm_num)
        dsimp only [c]
        linarith
      exact htz.trans hzc
    intro t ht
    have htK : t ∈ Uᶜ := ht
    have htz : vertical m (q t) ≤ z :=
      hmax htK
    have hzc : z ≤ c := by
      have hzmax : z ≤ max z 0 := le_max_left _ _
      have hmaxlt : max z 0 < 1 :=
        max_lt hzlt (by norm_num)
      dsimp only [c]
      linarith
    exact SphereCap.map_eq_basepoint_of_vertical_le_cutoff d
      (htz.trans hzc)
  · have hcover : U = Set.univ := by
      rw [← compl_empty_iff]
      exact not_nonempty_iff_eq_empty.mp hK
    let d : SphereCap.Datum :=
      ⟨1 / 2, by norm_num, by norm_num⟩
    refine ⟨d, by norm_num, SphereCap.genLoop_homotopic d q, ?_, ?_⟩
    · intro t ht
      exfalso
      exact ht (by rw [hcover]; trivial)
    intro t ht
    exfalso
    exact ht (by rw [hcover]; trivial)

end Submission.SphereLocalNormal
