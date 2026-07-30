import Mathlib

open Set
open scoped Topology

noncomputable section

namespace Submission.Helpers

/-- A punctured open ball in the complex plane is connected. -/
theorem isConnected_ball_diff_singleton_complex
    (a : ℂ) {r : ℝ} (hr : 0 < r) :
    IsConnected (Metric.ball a r \ {a}) := by
  let D : Set (ℝ × ℂ) :=
    Set.Ioo 0 r ×ˢ Metric.sphere (0 : ℂ) 1
  let Φ : ℝ × ℂ → ℂ :=
    fun p ↦ a + (p.1 : ℂ) * p.2
  have hsphere :
    IsConnected (Metric.sphere (0 : ℂ) 1) :=
    isConnected_sphere
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) 0 zero_le_one
  have hD : IsConnected D :=
    (isConnected_Ioo hr).prod hsphere
  have hΦ : Continuous Φ := by
    fun_prop
  have himage :
      Φ '' D = Metric.ball a r \ {a} := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      have huNorm : ‖u‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hu
      have htComplex : (t : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr ht.1.ne'
      have hu0 : u ≠ 0 := by
        intro h
        simp [h] at huNorm
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]
        simpa [Φ, norm_mul, abs_of_pos ht.1, huNorm] using ht.2
      · simp only [mem_singleton_iff]
        intro h
        have hzero : (t : ℂ) * u = 0 := by
          have := congrArg (fun w : ℂ ↦ w - a) h
          simpa [Φ] using this
        exact (mul_ne_zero htComplex hu0) hzero
    · intro z hz
      have hza : z - a ≠ 0 := by
        simpa only [sub_ne_zero] using
          (show z ≠ a by simpa only [mem_singleton_iff] using hz.2)
      let t : ℝ := ‖z - a‖
      have ht : 0 < t := norm_pos_iff.mpr hza
      have htr : t < r := by
        simpa only [t, Metric.mem_ball, dist_eq_norm] using hz.1
      let u : ℂ := (t : ℂ)⁻¹ * (z - a)
      have hu : u ∈ Metric.sphere (0 : ℂ) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]
        dsimp only [u]
        rw [norm_mul, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos ht]
        dsimp only [t]
        field_simp
      refine ⟨⟨t, u⟩, ⟨⟨ht, htr⟩, hu⟩, ?_⟩
      dsimp only [Φ, u]
      have htComplex : (t : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr ht.ne'
      rw [← mul_assoc, mul_inv_cancel₀ htComplex, one_mul]
      ring
  rw [← himage]
  exact hD.image Φ hΦ.continuousOn

/-- Every open neighborhood of the center meets a punctured ball around
that center. -/
theorem puncturedBall_inter_open_nonempty
    (a : ℂ) {r : ℝ} (hr : 0 < r)
    {V : Set ℂ} (hV : IsOpen V) (haV : a ∈ V) :
    ((Metric.ball a r \ {a}) ∩ V).Nonempty := by
  obtain ⟨s, hs, hsV⟩ :=
    Metric.mem_nhds_iff.mp (hV.mem_nhds haV)
  let d : ℝ := min r s / 2
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hdr : d < r := by
    dsimp [d]
    have := min_le_left r s
    linarith
  have hds : d < s := by
    dsimp [d]
    have := min_le_right r s
    linarith
  let z : ℂ := a + d
  have hza : z ≠ a := by
    intro h
    have : (d : ℂ) = 0 := by
      apply add_left_cancel (a := a)
      simpa only [z, add_zero] using h
    exact hd.ne' (Complex.ofReal_eq_zero.mp this)
  refine ⟨z, ⟨?_, by simpa only [mem_singleton_iff]⟩, hsV ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    simpa [z, abs_of_pos hd] using hdr
  · rw [Metric.mem_ball, dist_eq_norm]
    simpa [z, abs_of_pos hd] using hds

/-- Removing one point from a connected open subset of the complex plane
does not disconnect it. -/
theorem IsConnected.diff_singleton_of_isOpen_complex
    {U : Set ℂ} (hU : IsConnected U) (hUopen : IsOpen U)
    {a : ℂ} (ha : a ∈ U) :
    IsConnected (U \ {a}) := by
  obtain ⟨r, hr, hrU⟩ :=
    Metric.mem_nhds_iff.mp (hUopen.mem_nhds ha)
  let P : Set ℂ := Metric.ball a r \ {a}
  have hP : IsConnected P := by
    exact isConnected_ball_diff_singleton_complex a hr
  have hPS : P ⊆ U \ {a} :=
    Set.sdiff_subset_sdiff hrU Subset.rfl
  refine ⟨hP.nonempty.mono hPS, ?_⟩
  intro u v hu hv hcover hsu hsv
  have hPcover : P ⊆ u ∪ v :=
    hPS.trans hcover
  by_cases hPu : (P ∩ u).Nonempty
  · by_cases hPv : (P ∩ v).Nonempty
    · exact
        (hP.isPreconnected u v hu hv hPcover hPu hPv).mono
          (Set.inter_subset_inter_left _ hPS)
    · have hUcover : U ⊆ (u ∪ Metric.ball a r) ∪ v := by
        intro z hz
        by_cases hza : z = a
        · left
          right
          simpa [hza] using hr
        · have hzS : z ∈ U \ {a} :=
            ⟨hz, by simpa only [mem_singleton_iff]⟩
          rcases hcover hzS with hzu | hzv
          · exact Or.inl (Or.inl hzu)
          · exact Or.inr hzv
      have hleft : (U ∩ (u ∪ Metric.ball a r)).Nonempty := by
        rcases hsu with ⟨z, hzS, hzu⟩
        exact ⟨z, hzS.1, Or.inl hzu⟩
      have hright : (U ∩ v).Nonempty := by
        rcases hsv with ⟨z, hzS, hzv⟩
        exact ⟨z, hzS.1, hzv⟩
      obtain ⟨z, hzU, hzuBall, hzv⟩ :=
        hU.isPreconnected
          (u ∪ Metric.ball a r) v
          (hu.union Metric.isOpen_ball) hv
          hUcover hleft hright
      rcases hzuBall with hzu | hzball
      · by_cases hza : z = a
        · subst z
          obtain ⟨w, hwP, hwuv⟩ :=
            puncturedBall_inter_open_nonempty
              a hr (hu.inter hv) ⟨hzu, hzv⟩
          exact ⟨w, hPS hwP, hwuv⟩
        · exact
            ⟨z, ⟨hzU, by simpa only [mem_singleton_iff]⟩,
              hzu, hzv⟩
      · exfalso
        by_cases hza : z = a
        · subst z
          exact hPv
            (puncturedBall_inter_open_nonempty a hr hv hzv)
        · apply hPv
          exact
            ⟨z, ⟨hzball, by simpa only [mem_singleton_iff]⟩, hzv⟩
  · have hUcover : U ⊆ u ∪ (v ∪ Metric.ball a r) := by
      intro z hz
      by_cases hza : z = a
      · right
        right
        simpa [hza] using hr
      · have hzS : z ∈ U \ {a} :=
          ⟨hz, by simpa only [mem_singleton_iff]⟩
        rcases hcover hzS with hzu | hzv
        · exact Or.inl hzu
        · exact Or.inr (Or.inl hzv)
    have hleft : (U ∩ u).Nonempty := by
      rcases hsu with ⟨z, hzS, hzu⟩
      exact ⟨z, hzS.1, hzu⟩
    have hright : (U ∩ (v ∪ Metric.ball a r)).Nonempty := by
      rcases hsv with ⟨z, hzS, hzv⟩
      exact ⟨z, hzS.1, Or.inl hzv⟩
    obtain ⟨z, hzU, hzu, hzvBall⟩ :=
      hU.isPreconnected
        u (v ∪ Metric.ball a r)
        hu (hv.union Metric.isOpen_ball)
        hUcover hleft hright
    rcases hzvBall with hzv | hzball
    · by_cases hza : z = a
      · subst z
        obtain ⟨w, hwP, hwuv⟩ :=
          puncturedBall_inter_open_nonempty
            a hr (hu.inter hv) ⟨hzu, hzv⟩
        exact ⟨w, hPS hwP, hwuv⟩
      · exact
          ⟨z, ⟨hzU, by simpa only [mem_singleton_iff]⟩,
            hzu, hzv⟩
    · exfalso
      by_cases hza : z = a
      · subst z
        exact hPu
          (puncturedBall_inter_open_nonempty a hr hu hzu)
      · apply hPu
        exact
          ⟨z, ⟨hzball, by simpa only [mem_singleton_iff]⟩, hzu⟩

/-- A genuine planar annulus is connected. -/
theorem isConnected_ball_diff_closedBall_complex
    (a : ℂ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) :
    IsConnected
      (Metric.ball a s \ Metric.closedBall a r) := by
  let D : Set (ℝ × ℂ) :=
    Set.Ioo r s ×ˢ Metric.sphere (0 : ℂ) 1
  let Φ : ℝ × ℂ → ℂ :=
    fun p ↦ a + (p.1 : ℂ) * p.2
  have hsphere :
      IsConnected (Metric.sphere (0 : ℂ) 1) :=
    isConnected_sphere
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) 0 zero_le_one
  have hD : IsConnected D :=
    (isConnected_Ioo hrs).prod hsphere
  have hΦ : Continuous Φ := by
    fun_prop
  have himage :
      Φ '' D =
        Metric.ball a s \ Metric.closedBall a r := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      have htpos : 0 < t :=
        hr.trans_lt ht.1
      have huNorm : ‖u‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hu
      constructor
      · rw [Metric.mem_ball, dist_eq_norm]
        simpa [Φ, norm_mul, abs_of_pos htpos, huNorm] using ht.2
      · rw [Metric.mem_closedBall, dist_eq_norm, not_le]
        simpa [Φ, norm_mul, abs_of_pos htpos, huNorm] using ht.1
    · intro z hz
      have hzr : r < ‖z - a‖ := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hz.2
      have hzs : ‖z - a‖ < s := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hz.1
      let t : ℝ := ‖z - a‖
      have htpos : 0 < t :=
        hr.trans_lt hzr
      let u : ℂ := (t : ℂ)⁻¹ * (z - a)
      have hu : u ∈ Metric.sphere (0 : ℂ) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]
        dsimp only [u]
        rw [norm_mul, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos htpos]
        change t⁻¹ * t = 1
        exact inv_mul_cancel₀ (ne_of_gt htpos)
      refine ⟨⟨t, u⟩, ⟨⟨hzr, hzs⟩, hu⟩, ?_⟩
      dsimp only [Φ, u]
      have htComplex : (t : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr htpos.ne'
      rw [← mul_assoc, mul_inv_cancel₀ htComplex, one_mul]
      ring
  rw [← himage]
  exact hD.image Φ hΦ.continuousOn

/-- Removing a closed disk together with a surrounding annular collar from
a connected planar set does not disconnect the remainder. -/
theorem IsConnected.diff_closedBall_of_ball_subset_complex
    {U : Set ℂ} (hU : IsConnected U) (a : ℂ)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s)
    (hball : Metric.ball a s ⊆ U) :
    IsConnected (U \ Metric.closedBall a r) := by
  let P : Set ℂ :=
    Metric.ball a s \ Metric.closedBall a r
  have hP : IsConnected P :=
    isConnected_ball_diff_closedBall_complex a hr hrs
  have hPS : P ⊆ U \ Metric.closedBall a r :=
    Set.sdiff_subset_sdiff hball Subset.rfl
  refine ⟨hP.nonempty.mono hPS, ?_⟩
  intro u v hu hv hcover hsu hsv
  have hPcover : P ⊆ u ∪ v :=
    hPS.trans hcover
  by_cases hPu : (P ∩ u).Nonempty
  · by_cases hPv : (P ∩ v).Nonempty
    · exact
        (hP.isPreconnected u v hu hv hPcover hPu hPv).mono
          (Set.inter_subset_inter_left _ hPS)
    · have hUcover :
          U ⊆
            (u ∪ Metric.ball a s) ∪
              (v ∩ (Metric.closedBall a r)ᶜ) := by
        intro z hz
        by_cases hzD : z ∈ Metric.closedBall a r
        · exact Or.inl (Or.inr
            (Metric.closedBall_subset_ball hrs hzD))
        · have hzS : z ∈ U \ Metric.closedBall a r :=
            ⟨hz, hzD⟩
          rcases hcover hzS with hzu | hzv
          · exact Or.inl (Or.inl hzu)
          · exact Or.inr ⟨hzv, by
              simpa only [mem_compl_iff] using hzD⟩
      have hleft :
          (U ∩ (u ∪ Metric.ball a s)).Nonempty := by
        rcases hsu with ⟨z, hzS, hzu⟩
        exact ⟨z, hzS.1, Or.inl hzu⟩
      have hright :
          (U ∩
            (v ∩ (Metric.closedBall a r)ᶜ)).Nonempty := by
        rcases hsv with ⟨z, hzS, hzv⟩
        exact ⟨z, hzS.1, hzv, by
          simpa only [mem_compl_iff] using hzS.2⟩
      obtain ⟨z, hzU, hzuBall, hzv, hzD⟩ :=
        hU.isPreconnected
          (u ∪ Metric.ball a s)
          (v ∩ (Metric.closedBall a r)ᶜ)
          (hu.union Metric.isOpen_ball)
          (hv.inter Metric.isClosed_closedBall.isOpen_compl)
          hUcover hleft hright
      rcases hzuBall with hzu | hzball
      · exact
          ⟨z, ⟨hzU, by
            simpa only [mem_compl_iff] using hzD⟩, hzu, hzv⟩
      · exfalso
        apply hPv
        exact
          ⟨z, ⟨hzball, by
            simpa only [mem_compl_iff] using hzD⟩, hzv⟩
  · have hUcover :
        U ⊆
          (u ∩ (Metric.closedBall a r)ᶜ) ∪
            (v ∪ Metric.ball a s) := by
      intro z hz
      by_cases hzD : z ∈ Metric.closedBall a r
      · exact Or.inr (Or.inr
          (Metric.closedBall_subset_ball hrs hzD))
      · have hzS : z ∈ U \ Metric.closedBall a r :=
          ⟨hz, hzD⟩
        rcases hcover hzS with hzu | hzv
        · exact Or.inl ⟨hzu, by
            simpa only [mem_compl_iff] using hzD⟩
        · exact Or.inr (Or.inl hzv)
    have hleft :
        (U ∩
          (u ∩ (Metric.closedBall a r)ᶜ)).Nonempty := by
      rcases hsu with ⟨z, hzS, hzu⟩
      exact ⟨z, hzS.1, hzu, by
        simpa only [mem_compl_iff] using hzS.2⟩
    have hright :
        (U ∩ (v ∪ Metric.ball a s)).Nonempty := by
      rcases hsv with ⟨z, hzS, hzv⟩
      exact ⟨z, hzS.1, Or.inl hzv⟩
    obtain ⟨z, hzU, hzleft, hzvBall⟩ :=
      hU.isPreconnected
        (u ∩ (Metric.closedBall a r)ᶜ)
        (v ∪ Metric.ball a s)
        (hu.inter Metric.isClosed_closedBall.isOpen_compl)
        (hv.union Metric.isOpen_ball)
        hUcover hleft hright
    rcases hzleft with ⟨hzu, hzD⟩
    rcases hzvBall with hzv | hzball
    · exact
        ⟨z, ⟨hzU, by
          simpa only [mem_compl_iff] using hzD⟩, hzu, hzv⟩
    · exfalso
      apply hPu
      exact
        ⟨z, ⟨hzball, by
          simpa only [mem_compl_iff] using hzD⟩, hzu⟩

/-- Adjoining a closed disk with a disjoint open collar to a full planar
set preserves connectedness of the complement. -/
theorem isConnected_compl_union_closedBall_complex
    (K : Set ℂ) (hKc : IsConnected (Kᶜ))
    (a : ℂ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s)
    (hball : Metric.ball a s ⊆ Kᶜ) :
    IsConnected ((K ∪ Metric.closedBall a r)ᶜ) := by
  simpa only [compl_union, sdiff_eq] using
    IsConnected.diff_closedBall_of_ball_subset_complex
      hKc a hr hrs hball

/-- The exterior of a closed ball in the complex plane is connected. -/
theorem isConnected_compl_closedBall_complex (a : ℂ) (r : ℝ) :
    IsConnected ((Metric.closedBall a r)ᶜ) := by
  by_cases hr : 0 ≤ r
  · let D : Set (ℝ × ℂ) :=
      Set.Ioi r ×ˢ Metric.sphere (0 : ℂ) 1
    let Φ : ℝ × ℂ → ℂ :=
      fun p ↦ a + (p.1 : ℂ) * p.2
    have hsphere :
      IsConnected (Metric.sphere (0 : ℂ) 1) :=
      isConnected_sphere
        (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) 0 zero_le_one
    have hD : IsConnected D :=
      isConnected_Ioi.prod hsphere
    have hΦ : Continuous Φ := by
      fun_prop
    have himage :
        Φ '' D = (Metric.closedBall a r)ᶜ := by
      apply Set.Subset.antisymm
      · rintro z ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
        have htpos : 0 < t := hr.trans_lt ht
        have huNorm : ‖u‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using hu
        rw [mem_compl_iff, Metric.mem_closedBall, not_le,
          dist_eq_norm]
        simpa [Φ, norm_mul, abs_of_pos htpos, huNorm] using ht
      · intro z hz
        have hzr : r < ‖z - a‖ := by
          simpa only [mem_compl_iff, Metric.mem_closedBall, not_le,
            dist_eq_norm] using hz
        let t : ℝ := ‖z - a‖
        have htpos : 0 < t := lt_of_le_of_lt hr hzr
        let u : ℂ := (t : ℂ)⁻¹ * (z - a)
        have hu : u ∈ Metric.sphere (0 : ℂ) 1 := by
          rw [Metric.mem_sphere, dist_zero_right]
          dsimp only [u]
          rw [norm_mul, norm_inv, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos htpos]
          change t⁻¹ * t = 1
          exact inv_mul_cancel₀ (ne_of_gt htpos)
        refine ⟨⟨t, u⟩, ⟨hzr, hu⟩, ?_⟩
        dsimp only [Φ, u]
        have htComplex : (t : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr htpos.ne'
        rw [← mul_assoc, mul_inv_cancel₀ htComplex, one_mul]
        ring
    rw [← himage]
    exact hD.image Φ hΦ.continuousOn
  · rw [Metric.closedBall_eq_empty.mpr (lt_of_not_ge hr)]
    simpa only [compl_empty] using
      (isConnected_univ : IsConnected (Set.univ : Set ℂ))

/-- Intersecting a full planar compact set with a closed ball preserves
connectedness of the complement. -/
theorem isConnected_compl_inter_closedBall_complex
    (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    (a : ℂ) (r : ℝ) :
    IsConnected ((K ∩ Metric.closedBall a r)ᶜ) := by
  have houtside :
      IsConnected ((Metric.closedBall a r)ᶜ) :=
    isConnected_compl_closedBall_complex a r
  have hmeet :
      (Kᶜ ∩ (Metric.closedBall a r)ᶜ).Nonempty := by
    obtain ⟨R₀, hKR₀⟩ :=
      hK.isBounded.subset_closedBall (0 : ℂ)
    let R : ℝ := max R₀ 1
    have hR : 0 < R :=
      lt_max_of_lt_right zero_lt_one
    have hKR : ∀ z ∈ K, ‖z‖ ≤ R := by
      intro z hz
      have hzR := hKR₀ hz
      rw [Metric.mem_closedBall, dist_zero_right] at hzR
      exact hzR.trans (le_max_left _ _)
    let T : ℝ := R + ‖a‖ + |r| + 1
    have hT : 0 < T := by
      dsimp [T]
      positivity
    let z : ℂ := a + T
    have hTnorm : T ≤ ‖z‖ + ‖a‖ := by
      have hz := norm_sub_le z a
      simpa [z, abs_of_pos hT] using hz
    have hzR : R < ‖z‖ := by
      dsimp [T] at hTnorm
      nlinarith [abs_nonneg r]
    have hzK : z ∉ K := by
      intro hz
      exact (not_lt_of_ge (hKR z hz)) hzR
    have hzdist : dist z a = T := by
      rw [dist_eq_norm]
      simp [z, abs_of_pos hT]
    have hzball : z ∉ Metric.closedBall a r := by
      rw [Metric.mem_closedBall, hzdist]
      dsimp [T]
      nlinarith [hR, norm_nonneg a, le_abs_self r]
    exact
      ⟨z, by simpa only [mem_compl_iff] using hzK,
        by simpa only [mem_compl_iff] using hzball⟩
  have hunion :
      IsConnected (Kᶜ ∪ (Metric.closedBall a r)ᶜ) :=
    IsConnected.union hmeet hKc houtside
  simpa only [compl_inter] using hunion

/-- A Möbius resolvent sends a compact set with connected complement to
another compact set with connected complement. -/
theorem isConnected_compl_resolvent_image
    (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    (a : ℂ) (ha : a ∉ K) :
    IsConnected (((fun z : ℂ ↦ (a - z)⁻¹) '' K)ᶜ) := by
  let U : Set ℂ := Kᶜ
  let r : ℂ → ℂ := fun z ↦ (a - z)⁻¹
  let V : Set ℂ := r '' (U \ {a})
  have haU : a ∈ U := by
    simpa only [U, mem_compl_iff] using ha
  have hUopen : IsOpen U := by
    simpa only [U] using hK.isClosed.isOpen_compl
  have hUpunctured : IsConnected (U \ {a}) :=
    IsConnected.diff_singleton_of_isOpen_complex hKc hUopen haU
  have hrContinuous : ContinuousOn r (U \ {a}) := by
    apply (continuousOn_const.sub continuousOn_id).inv₀
    intro z hz
    exact sub_ne_zero.mpr fun h ↦
      hz.2 (mem_singleton_iff.mpr h.symm)
  have hV : IsConnected V := by
    exact hUpunctured.image r hrContinuous
  have h0closure : 0 ∈ closure V := by
    obtain ⟨R₀, hRK₀⟩ :=
      hK.isBounded.subset_closedBall (0 : ℂ)
    let R : ℝ := max R₀ 1
    have hR : 0 < R :=
      lt_max_of_lt_right zero_lt_one
    have hRK : ∀ z ∈ K, ‖z‖ ≤ R := by
      intro z hz
      have hzR := hRK₀ hz
      rw [Metric.mem_closedBall, dist_zero_right] at hzR
      exact hzR.trans (le_max_left _ _)
    rw [Metric.mem_closure_iff]
    intro e he
    let T : ℝ := R + ‖a‖ + 1 + e⁻¹
    have hT : 0 < T := by
      dsimp [T]
      positivity
    have heT : e⁻¹ < T := by
      dsimp [T]
      nlinarith [hR, norm_nonneg a]
    let z : ℂ := a + T
    have hTnorm : T ≤ ‖z‖ + ‖a‖ := by
      have hz := norm_sub_le z a
      simpa [z, abs_of_pos hT] using hz
    have hzR : R < ‖z‖ := by
      dsimp [T] at hTnorm
      nlinarith [inv_pos.mpr he]
    have hzK : z ∉ K := by
      intro hz
      exact (not_lt_of_ge (hRK z hz)) hzR
    have hza : z ≠ a := by
      intro h
      have hzero : (T : ℂ) = 0 := by
        have := congrArg (fun w : ℂ ↦ w - a) h
        simpa [z] using this
      exact hT.ne' (Complex.ofReal_eq_zero.mp hzero)
    have hInv : T⁻¹ < e :=
      (inv_lt_comm₀ hT he).2 heT
    refine ⟨r z, ?_, ?_⟩
    · exact
        ⟨z, ⟨by simpa only [U, mem_compl_iff] using hzK,
          by simpa only [mem_singleton_iff] using hza⟩, rfl⟩
    · have hdist : dist 0 (r z) = T⁻¹ := by
        rw [dist_zero_left]
        simp [r, z, abs_of_pos hT]
      simpa only [hdist] using hInv
  have hVzero : IsConnected (insert 0 V) := by
    apply hV.subset_closure
    · exact subset_insert 0 V
    · exact insert_subset h0closure subset_closure
  have hcompl :
      ((r '' K)ᶜ : Set ℂ) = insert 0 V := by
    ext ζ
    constructor
    · intro hζ
      by_cases hζ0 : ζ = 0
      · exact hζ0 ▸ mem_insert 0 V
      · apply mem_insert_iff.mpr
        right
        let z : ℂ := a - ζ⁻¹
        have hrz : r z = ζ := by
          simp [r, z]
        have hza : z ≠ a := by
          intro h
          have hzero : ζ⁻¹ = 0 := by
            have := congrArg (fun w : ℂ ↦ a - w) h
            simpa [z] using this
          exact hζ0 (inv_eq_zero.mp hzero)
        have hzK : z ∉ K := by
          intro hz
          exact hζ ⟨z, hz, hrz⟩
        exact
          ⟨z, ⟨by simpa only [U, mem_compl_iff] using hzK,
            by simpa only [mem_singleton_iff] using hza⟩, hrz⟩
    · intro hζ
      rcases mem_insert_iff.mp hζ with rfl | hζV
      · rintro ⟨z, hzK, hz0⟩
        have hza : a - z ≠ 0 :=
          sub_ne_zero.mpr fun h ↦ ha (h ▸ hzK)
        exact (inv_ne_zero hza) hz0
      · rintro ⟨w, hwK, hwr⟩
        obtain ⟨z, hz, rfl⟩ := hζV
        have hEq : a - w = a - z := by
          simpa only [r] using inv_injective hwr
        have hwz : w = z := by
          exact sub_right_inj.mp hEq
        exact hz.1 (hwz ▸ hwK)
  change IsConnected ((r '' K)ᶜ)
  rw [hcompl]
  exact hVzero

end Submission.Helpers
