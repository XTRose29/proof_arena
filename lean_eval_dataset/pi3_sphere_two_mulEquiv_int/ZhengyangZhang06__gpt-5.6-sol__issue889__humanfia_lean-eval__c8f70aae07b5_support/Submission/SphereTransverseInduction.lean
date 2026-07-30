import Submission.SphereSingleton
import Submission.SphereTransverseFiniteRestrict

open scoped unitInterval

noncomputable section

namespace Submission.SphereTransverseInduction

open Submission.SphereRegularApprox

variable {m : ℕ}

/-- A transverse cubical sphere map with finite antipode fiber is a power of
the canonical generator. -/
theorem exists_zpow_of_finite_antipode_fiber
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (hp : SphereTransverse.Transverse p)
    (hfinite :
      {t | p t =
        -(SphereGenerator.canonicalBasepoint m)}.Finite) :
    ∃ z : ℤ, (Quotient.mk' p :
      HomotopyGroup.Pi (m + 1) (UnitSphere m)
        (SphereGenerator.canonicalBasepoint m)) =
      SphereGenerator.canonicalGeneratorClass m ^ z := by
  let P : ℕ → Prop := fun k =>
    ∀ (q : GenLoop (Fin (m + 1)) (UnitSphere m)
        (SphereGenerator.canonicalBasepoint m))
      (hq : SphereTransverse.Transverse q)
      (hqfinite :
        {t | q t =
          -(SphereGenerator.canonicalBasepoint m)}.Finite),
      hqfinite.toFinset.card = k →
        ∃ z : ℤ, (Quotient.mk' q :
          HomotopyGroup.Pi (m + 1) (UnitSphere m)
            (SphereGenerator.canonicalBasepoint m)) =
          SphereGenerator.canonicalGeneratorClass m ^ z
  apply (Nat.strong_induction_on hfinite.toFinset.card
    (p := P) ?_) p hp hfinite rfl
  intro k ih q hq hqfinite hqcard
  by_cases hk0 : k = 0
  · have havoid :
        ∀ t, q t ≠ -(SphereGenerator.canonicalBasepoint m) := by
      intro t ht
      have hmem : t ∈ hqfinite.toFinset := by
        simpa using ht
      have hpos : 0 < hqfinite.toFinset.card :=
        Finset.card_pos.mpr ⟨t, hmem⟩
      omega
    refine ⟨0, ?_⟩
    rw [zpow_zero]
    exact
      (SphereAvoidance.homotopy_class_eq_const_of_avoids_antipode
        q havoid).trans HomotopyGroup.one_def.symm
  by_cases hk1 : k = 1
  · have hclass :=
      SphereSingleton.class_eq_or_eq_inverse_of_singleton_transverse
        q hqfinite (hqcard.trans hk1) hq
    rcases hclass with hclass | hclass
    · exact ⟨1, by simpa using hclass⟩
    · exact ⟨-1, by simpa using hclass⟩
  have hk2 : 2 ≤ k := by omega
  have hcard2 : 2 ≤ hqfinite.toFinset.card := by
    simpa only [hqcard] using hk2
  obtain ⟨pLeft, pRight, hsplit, hpLeft, hpRight,
      ⟨hLeft, hLeftCard⟩, ⟨hRight, hRightCard⟩⟩ :=
    SphereTransverseFiniteRestrict.exists_restrictions_with_smaller_fibers
      q hq hqfinite.toFinset (fun t => by simp) hcard2
  have hLeftLt : hLeft.toFinset.card < k := by
    simpa only [hqcard] using hLeftCard
  have hRightLt : hRight.toFinset.card < k := by
    simpa only [hqcard] using hRightCard
  obtain ⟨zLeft, hzLeft⟩ :=
    ih hLeft.toFinset.card hLeftLt pLeft hpLeft hLeft rfl
  obtain ⟨zRight, hzRight⟩ :=
    ih hRight.toFinset.card hRightLt pRight hpRight hRight rfl
  refine ⟨zRight + zLeft, ?_⟩
  calc
    (Quotient.mk' q :
        HomotopyGroup.Pi (m + 1) (UnitSphere m)
          (SphereGenerator.canonicalBasepoint m)) =
        Quotient.mk'
          (GenLoop.transAt
            (Classical.arbitrary (Fin (m + 1))) pLeft pRight) :=
      Quotient.sound hsplit
    _ =
        SphereGenerator.canonicalGeneratorClass m ^ zRight *
          SphereGenerator.canonicalGeneratorClass m ^ zLeft := by
      rw [← hzRight, ← hzLeft]
      exact HomotopyGroup.mul_spec.symm
    _ =
        SphereGenerator.canonicalGeneratorClass m ^
          (zRight + zLeft) :=
      (zpow_add _ zRight zLeft).symm

/-- Every class of the diagonal sphere is a power of the canonical
generator. -/
theorem exists_zpow
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    ∃ z : ℤ, (Quotient.mk' q :
      HomotopyGroup.Pi (m + 1) (UnitSphere m)
        (SphereGenerator.canonicalBasepoint m)) =
      SphereGenerator.canonicalGeneratorClass m ^ z := by
  obtain ⟨a, y, hy, hregular, hhomotopic, hfinite⟩ :=
    SphereRegularApprox.exists_regularization q
  obtain ⟨z, hz⟩ :=
    exists_zpow_of_finite_antipode_fiber
      (SphereRegularApprox.regularizedGenLoop a y hy)
      (SphereTransverse.regularizedGenLoop_transverse a hy hregular)
      hfinite
  exact ⟨z, (Quotient.sound hhomotopic).trans hz⟩

theorem canonicalZPowersHom_surjective :
    Function.Surjective
      (zpowersHom
        (HomotopyGroup.Pi (m + 1) (UnitSphere m)
          (SphereGenerator.canonicalBasepoint m))
        (SphereGenerator.canonicalGeneratorClass m)) := by
  intro z
  induction z using Quotient.inductionOn with
  | _ q =>
      obtain ⟨n, hn⟩ := exists_zpow q
      refine ⟨Multiplicative.ofAdd n, ?_⟩
      exact hn.symm

end Submission.SphereTransverseInduction
