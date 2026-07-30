import Submission.SpherePlateau
import Submission.SphereSplit

open scoped unitInterval

noncomputable section

namespace Submission.SphereFiniteCut

open Set
open Submission.SphereRegularApprox

variable {m : ℕ}

abbrev Cube (m : ℕ) :=
  Fin (m + 1) → I

abbrev UnitSphere (m : ℕ) :=
  SphereRegularApprox.UnitSphere m

/-- Two distinct points in a finite subset of a cube can be separated by a
coordinate hyperplane which misses the whole finite subset.  Both open sides
of the cut contain a point, hence both corresponding filtered finsets are
strictly smaller. -/
theorem exists_separating_cut
    (F : Finset (Cube m)) (hF : 2 ≤ F.card) :
    ∃ i : Fin (m + 1), ∃ c : ℝ,
      0 < c ∧ c < 1 ∧
      (∀ t ∈ F, (t i : ℝ) ≠ c) ∧
      (F.filter fun t => (t i : ℝ) < c).card < F.card ∧
      (F.filter fun t => c < (t i : ℝ)).card < F.card := by
  classical
  have hone : 1 < F.card := lt_of_lt_of_le Nat.one_lt_two hF
  obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp hone
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := by
    simpa only [Function.ne_iff] using hst
  have hireal : (s i : ℝ) ≠ (t i : ℝ) := by
    intro h
    exact hi (Subtype.ext h)
  rcases lt_or_gt_of_ne hireal with hst' | hts'
  · obtain ⟨c, hc, hcF⟩ :=
      (Set.Ioo_infinite hst').exists_notMem_finset
        (F.image fun u => (u i : ℝ))
    have hc0 : 0 < c := (s i).property.1.trans_lt hc.1
    have hc1 : c < 1 := hc.2.trans_le (t i).property.2
    have hmiss : ∀ u ∈ F, (u i : ℝ) ≠ c := by
      intro u hu huc
      apply hcF
      exact Finset.mem_image.mpr ⟨u, hu, huc⟩
    refine ⟨i, c, hc0, hc1, hmiss, ?_, ?_⟩
    · apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have hmem :
          t ∈ F.filter (fun u => (u i : ℝ) < c) := by
        rw [heq]
        exact ht
      exact (not_lt_of_ge hc.2.le) (Finset.mem_filter.mp hmem).2
    · apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have hmem :
          s ∈ F.filter (fun u => c < (u i : ℝ)) := by
        rw [heq]
        exact hs
      exact (not_lt_of_ge hc.1.le) (Finset.mem_filter.mp hmem).2
  · obtain ⟨c, hc, hcF⟩ :=
      (Set.Ioo_infinite hts').exists_notMem_finset
        (F.image fun u => (u i : ℝ))
    have hc0 : 0 < c := (t i).property.1.trans_lt hc.1
    have hc1 : c < 1 := hc.2.trans_le (s i).property.2
    have hmiss : ∀ u ∈ F, (u i : ℝ) ≠ c := by
      intro u hu huc
      apply hcF
      exact Finset.mem_image.mpr ⟨u, hu, huc⟩
    refine ⟨i, c, hc0, hc1, hmiss, ?_, ?_⟩
    · apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have hmem :
          s ∈ F.filter (fun u => (u i : ℝ) < c) := by
        rw [heq]
        exact hs
      exact (not_lt_of_ge hc.2.le) (Finset.mem_filter.mp hmem).2
    · apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have hmem :
          t ∈ F.filter (fun u => c < (u i : ℝ)) := by
        rw [heq]
        exact ht
      exact (not_lt_of_ge hc.1.le) (Finset.mem_filter.mp hmem).2

/-- A finite antipode fiber of size at least two admits a separating cut.
After a target plateau deformation the loop is constant on that cut, while
its antipode fiber and its germ near the antipode are unchanged. -/
theorem exists_separating_plateau
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (F : Finset (Cube m))
    (hfiber : ∀ t, t ∈ F ↔
      q t = -(SphereGenerator.canonicalBasepoint m))
    (hcard : 2 ≤ F.card) :
    ∃ i : Fin (m + 1), ∃ c : ℝ,
      ∃ _hc0 : 0 < c, ∃ _hc1 : c < 1,
        ∃ d : SpherePlateau.Datum,
          GenLoop.Homotopic q (SpherePlateau.genLoop d q) ∧
          (∀ t, (t i : ℝ) = c →
            SpherePlateau.genLoop d q t =
              SphereGenerator.canonicalBasepoint m) ∧
          (∀ t, SpherePlateau.genLoop d q t =
              -(SphereGenerator.canonicalBasepoint m) ↔
            q t = -(SphereGenerator.canonicalBasepoint m)) ∧
          (F.filter fun t => (t i : ℝ) < c).card < F.card ∧
          (F.filter fun t => c < (t i : ℝ)).card < F.card ∧
          (∀ t, d.upper ≤ vertical m (q t) →
            SpherePlateau.genLoop d q t = q t) := by
  obtain ⟨i, c, hc0, hc1, hmiss, hleft, hright⟩ :=
    exists_separating_cut F hcard
  let K : Set (Cube m) := {t | (t i : ℝ) = c}
  have hKclosed : IsClosed K := by
    exact isClosed_eq
      (continuous_subtype_val.comp (continuous_apply i))
      continuous_const
  have hKcompact : IsCompact K := hKclosed.isCompact
  have hKavoid :
      ∀ t ∈ K,
        q t ≠ -(SphereGenerator.canonicalBasepoint m) := by
    intro t ht hqt
    exact hmiss t ((hfiber t).mpr hqt) ht
  obtain ⟨d, hdq, hdK, hdnear⟩ :=
    SpherePlateau.exists_datum_constant_on_compact
      q K hKcompact hKavoid
  refine ⟨i, c, hc0, hc1, d, hdq, ?_, ?_,
    hleft, hright, hdnear⟩
  · intro t ht
    exact hdK t ht
  · intro t
    exact SpherePlateau.map_eq_antipode_iff d (q t)

end Submission.SphereFiniteCut
