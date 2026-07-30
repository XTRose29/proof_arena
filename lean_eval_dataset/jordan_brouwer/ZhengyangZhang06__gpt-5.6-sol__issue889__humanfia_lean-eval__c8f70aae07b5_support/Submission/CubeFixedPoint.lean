import Submission.SpernerTheorem

open Set

namespace Submission

def unitCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x i ∈ Icc (0 : ℝ) 1}

theorem unitCube_compact (d : ℕ) : IsCompact (unitCube d) := by
  change IsCompact ((PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
    {x : Fin d → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) 1})
  rw [(PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isCompact_preimage]
  exact isCompact_pi_infinite fun _ => isCompact_Icc

theorem GridVertex.point_mem_unitCube {d N : ℕ} (hN : 0 < N) (v : GridVertex d N) :
    v.point hN ∈ unitCube d := by
  intro i
  constructor
  · simp only [GridVertex.point_apply]
    positivity
  · simp only [GridVertex.point_apply]
    rw [div_le_one (by positivity : (0 : ℝ) < N)]
    exact_mod_cast Nat.le_of_lt_succ (v.coord i).isLt

theorem KuhnSimplex.vertex_coord_abs_sub_le_one {d N : ℕ} (s : KuhnSimplex d N)
    (k l : Fin (d + 1)) (i : Fin d) :
    |((s.vertex k).coord i : ℝ) - (s.vertex l).coord i| ≤ 1 := by
  simp only [KuhnSimplex.vertex_coord]
  split_ifs <;> simp

theorem KuhnSimplex.vertex_point_coord_abs_sub_le {d N : ℕ} (hN : 0 < N)
    (s : KuhnSimplex d N) (k l : Fin (d + 1)) (i : Fin d) :
    |(s.vertex k).point hN i - (s.vertex l).point hN i| ≤ 1 / (N : ℝ) := by
  have hNabs : |(N : ℝ)| = N := abs_of_pos (Nat.cast_pos.mpr hN)
  rw [GridVertex.point_apply, GridVertex.point_apply, ← sub_div, abs_div, hNabs]
  exact (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hN)).2
    (s.vertex_coord_abs_sub_le_one k l i)

theorem abs_apply_le_norm {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |x i| ≤ ‖x‖ := by
  have hi : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  rw [← EuclideanSpace.real_norm_sq_eq] at hi
  nlinarith [abs_nonneg (x i), norm_nonneg x, sq_abs (x i)]

theorem KuhnSimplex.vertex_point_dist_sq_le_div {d N : ℕ} (hN : 0 < N)
    (s : KuhnSimplex d N) (k l : Fin (d + 1)) :
    dist ((s.vertex k).point hN) ((s.vertex l).point hN) ^ 2 ≤ (d : ℝ) / N := by
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hinv_nonneg : 0 ≤ (1 : ℝ) / N := le_of_lt (div_pos zero_lt_one hNreal)
  have hinv_le_one : (1 : ℝ) / N ≤ 1 := by
    rw [div_le_one hNreal]
    exact_mod_cast hN
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, ((s.vertex k).point hN i - (s.vertex l).point hN i) ^ 2 ≤
        ∑ _i : Fin d, ((1 : ℝ) / N) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi := s.vertex_point_coord_abs_sub_le hN k l i
          have hi_sq := (sq_le_sq₀
            (abs_nonneg ((s.vertex k).point hN i - (s.vertex l).point hN i))
            hinv_nonneg).2 hi
          simpa only [sq_abs] using hi_sq
    _ = (d : ℝ) * ((1 : ℝ) / N) ^ 2 := by simp
    _ ≤ (d : ℝ) * ((1 : ℝ) / N) := by
      gcongr
      nlinarith
    _ = (d : ℝ) / N := by ring

noncomputable def fixedPointLabel {d N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (v : GridVertex d N) : CubeLabel d :=
  if hupper : ∃ i, (v.coord i).val = N then
    some (Classical.choose hupper)
  else if hsign : ∃ i, 0 < (v.coord i).val ∧
      0 ≤ v.point hN i - g (v.point hN) i then
    some (Classical.choose hsign)
  else
    none

theorem fixedPointLabel_admissible {d N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    SpernerAdmissible (fixedPointLabel hN g) := by
  constructor
  · intro v hv i
    have hupper : ¬∃ j, (v.coord j).val = N := by
      intro h
      rw [fixedPointLabel, dif_pos h] at hv
      simp at hv
    have hle : (v.coord i).val ≤ N := Nat.le_of_lt_succ (v.coord i).isLt
    exact lt_of_le_of_ne hle fun hi => hupper ⟨i, hi⟩
  · intro v i hv
    by_cases hupper : ∃ j, (v.coord j).val = N
    · have hi : Classical.choose hupper = i := by
        rw [fixedPointLabel, dif_pos hupper] at hv
        exact Option.some.inj hv
      rw [← hi]
      rw [(Classical.choose_spec hupper)]
      exact hN
    · by_cases hsign : ∃ j, 0 < (v.coord j).val ∧
          0 ≤ v.point hN j - g (v.point hN) j
      · have hi : Classical.choose hsign = i := by
          rw [fixedPointLabel, dif_neg hupper, dif_pos hsign] at hv
          exact Option.some.inj hv
        rw [← hi]
        exact (Classical.choose_spec hsign).1
      · rw [fixedPointLabel, dif_neg hupper, dif_neg hsign] at hv
        simp at hv

theorem fixedPointLabel_none_displacement_nonpos {d N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hg_maps : MapsTo g (unitCube d) (unitCube d)) (v : GridVertex d N)
    (hv : fixedPointLabel hN g v = none) (i : Fin d) :
    v.point hN i - g (v.point hN) i ≤ 0 := by
  have hupper : ¬∃ j, (v.coord j).val = N := by
    intro h
    rw [fixedPointLabel, dif_pos h] at hv
    simp at hv
  have hsign : ¬∃ j, 0 < (v.coord j).val ∧
      0 ≤ v.point hN j - g (v.point hN) j := by
    intro h
    rw [fixedPointLabel, dif_neg hupper, dif_pos h] at hv
    simp at hv
  by_cases hi : (v.coord i).val = 0
  · have hg_nonneg := (hg_maps (v.point_mem_unitCube hN) i).1
    simp [GridVertex.point_apply, hi] at hg_nonneg ⊢
    exact hg_nonneg
  · have hcoord : 0 < (v.coord i).val := Nat.pos_of_ne_zero hi
    exact le_of_not_ge fun hnonneg => hsign ⟨i, hcoord, hnonneg⟩

theorem fixedPointLabel_some_displacement_nonneg {d N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hg_maps : MapsTo g (unitCube d) (unitCube d)) (v : GridVertex d N) (i : Fin d)
    (hv : fixedPointLabel hN g v = some i) :
    0 ≤ v.point hN i - g (v.point hN) i := by
  by_cases hupper : ∃ j, (v.coord j).val = N
  · have hi : Classical.choose hupper = i := by
      rw [fixedPointLabel, dif_pos hupper] at hv
      exact Option.some.inj hv
    have hcoord : (v.coord i).val = N := by
      rw [← hi]
      exact Classical.choose_spec hupper
    have hg_le_one := (hg_maps (v.point_mem_unitCube hN) i).2
    have hpoint : v.point hN i = 1 := by
      rw [GridVertex.point_apply, hcoord]
      exact div_self (Nat.cast_ne_zero.mpr hN.ne')
    rw [hpoint]
    linarith
  · by_cases hsign : ∃ j, 0 < (v.coord j).val ∧
        0 ≤ v.point hN j - g (v.point hN) j
    · have hi : Classical.choose hsign = i := by
        rw [fixedPointLabel, dif_neg hupper, dif_pos hsign] at hv
        exact Option.some.inj hv
      rw [← hi]
      exact (Classical.choose_spec hsign).2
    · rw [fixedPointLabel, dif_neg hupper, dif_neg hsign] at hv
      simp at hv

theorem unitCube_fixed_point {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hg_cont : ContinuousOn g (unitCube d))
    (hg_maps : MapsTo g (unitCube d) (unitCube d)) :
    ∃ x ∈ unitCube d, g x = x := by
  by_cases hd : d = 0
  · subst d
    refine ⟨0, by simp [unitCube], ?_⟩
    exact Subsingleton.elim _ _
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    by_contra hfixed
    push Not at hfixed
    let q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => x - g x
    have hq_cont : ContinuousOn q (unitCube d) := continuousOn_id.sub hg_cont
    have hcube_compact : IsCompact (unitCube d) := unitCube_compact d
    obtain ⟨xmin, hxmin, hmin⟩ := hcube_compact.exists_isMinOn
      ⟨0, by simp [unitCube]⟩ hq_cont.norm
    have hmu_pos : 0 < ‖q xmin‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr (hfixed xmin hxmin).symm
    let ε : ℝ := ‖q xmin‖ / ((d : ℝ) + 1)
    have hε : 0 < ε := div_pos hmu_pos (by positivity)
    have hq_uniform := hcube_compact.uniformContinuousOn_of_continuous hq_cont
    obtain ⟨δ, hδ, huniform⟩ :=
      (Metric.uniformContinuousOn_iff.1 hq_uniform) ε hε
    obtain ⟨N, hNlarge⟩ := exists_nat_gt ((d : ℝ) / δ ^ 2)
    have hNreal : (0 : ℝ) < N := by
      have hnonneg : 0 ≤ (d : ℝ) / δ ^ 2 := by positivity
      exact lt_of_le_of_lt hnonneg hNlarge
    have hN : 0 < N := by exact_mod_cast hNreal
    have hdiv : (d : ℝ) / N < δ ^ 2 := by
      rw [div_lt_iff₀ hNreal]
      have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
      have := (div_lt_iff₀ hδsq).1 hNlarge
      nlinarith
    let label := fixedPointLabel hN g
    obtain ⟨s, hs⟩ := SpernerParity.exists_fullyLabeled hN label
      (fixedPointLabel_admissible hN g)
    obtain ⟨knone, hknone⟩ := hs none
    let x := (s.vertex knone).point hN
    have hx : x ∈ unitCube d := GridVertex.point_mem_unitCube hN _
    have hx_nonpos (i : Fin d) : q x i ≤ 0 := by
      exact fixedPointLabel_none_displacement_nonpos hN g hg_maps _ hknone i
    have hx_abs_lt (i : Fin d) : |q x i| < ε := by
      obtain ⟨ki, hki⟩ := hs (some i)
      let y := (s.vertex ki).point hN
      have hy : y ∈ unitCube d := GridVertex.point_mem_unitCube hN _
      have hy_nonneg : 0 ≤ q y i := by
        exact fixedPointLabel_some_displacement_nonneg hN g hg_maps _ i hki
      have hxy_sq := s.vertex_point_dist_sq_le_div hN knone ki
      have hxy : dist x y < δ := by
        have hdist_nonneg : 0 ≤ dist x y := dist_nonneg
        dsimp [x, y] at hxy_sq ⊢
        nlinarith
      have hqxy : dist (q x) (q y) < ε := huniform x hx y hy hxy
      have hcoord : |q x i - q y i| < ε := by
        refine lt_of_le_of_lt ?_ (by simpa [dist_eq_norm] using hqxy)
        have hi := abs_apply_le_norm (q x - q y) i
        change |q x i - q y i| ≤ ‖q x - q y‖ at hi
        exact hi
      rw [abs_of_nonpos (sub_nonpos.mpr ((hx_nonpos i).trans hy_nonneg))] at hcoord
      rw [abs_of_nonpos (hx_nonpos i)]
      linarith
    have hsum_sq : ∑ i, (q x i) ^ 2 < ∑ _i : Fin d, ε ^ 2 := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨⟨0, hdpos⟩, Finset.mem_univ _⟩
      · intro i _
        have hi := hx_abs_lt i
        nlinarith [sq_abs (q x i), abs_nonneg (q x i)]
    have hε_bound : (d : ℝ) * ε ^ 2 < ‖q xmin‖ ^ 2 := by
      dsimp [ε]
      have hden : 0 < (d : ℝ) + 1 := by positivity
      rw [div_pow]
      rw [show (d : ℝ) * (‖q xmin‖ ^ 2 / ((d : ℝ) + 1) ^ 2) =
        (d : ℝ) * ‖q xmin‖ ^ 2 / ((d : ℝ) + 1) ^ 2 by ring]
      rw [div_lt_iff₀ (sq_pos_of_pos hden)]
      have hmu_sq : 0 < ‖q xmin‖ ^ 2 := sq_pos_of_pos hmu_pos
      have hd_nonneg : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hd_lt : (d : ℝ) < ((d : ℝ) + 1) ^ 2 := by nlinarith
      simpa [mul_comm] using mul_lt_mul_of_pos_right hd_lt hmu_sq
    have hnorm_lt : ‖q x‖ < ‖q xmin‖ := by
      have hsq : ‖q x‖ ^ 2 < ‖q xmin‖ ^ 2 := by
        calc
          ‖q x‖ ^ 2 = ∑ i, (q x i) ^ 2 := EuclideanSpace.real_norm_sq_eq _
          _ < ∑ _i : Fin d, ε ^ 2 := hsum_sq
          _ = (d : ℝ) * ε ^ 2 := by simp
          _ < ‖q xmin‖ ^ 2 := hε_bound
      nlinarith [norm_nonneg (q x), norm_nonneg (q xmin)]
    exact (not_lt_of_ge (hmin hx)) hnorm_lt

end Submission
