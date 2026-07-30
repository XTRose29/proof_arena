import Mathlib
namespace Submission

open Set Filter Topology
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 :=
/-ResultProofBegin-/by
  classical
  -- open
  let W : ℝ → ℝ := fun x => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x
  obtain ⟨x₀, hx₀, hW₀⟩ := hW
  have hDW : ∀ x ∈ J, HasDerivAt W (-p x * W x) x := by
    intro x hx
    dsimp [W]
    convert ((hy₁ x hx).mul (hy₂' x hx)).sub ((hy₂ x hx).mul (hy₁' x hx)) using 1 <;> try {rfl} <;> try {ext; rfl} <;> ring
  have hCW : ContinuousOn W J := fun x hx => (hDW x hx).continuousAt.continuousWithinAt
  -- propagation of a zero to the right
  have hright : ∀ {u v : ℝ}, u ≤ v → Set.Icc u v ⊆ J → W u = 0 → W v = 0 := by
    intro u v huv huvJ hu0
    have hp' : ContinuousOn p (Set.Icc u v) := hp.mono huvJ
    obtain ⟨K, hK⟩ := (isCompact_Icc.bddAbove_image hp'.norm)
    have hpK : ∀ t ∈ Set.Icc u v, ‖p t‖ ≤ K := by
      intro t ht
      exact hK (by exact ⟨t, ht, rfl⟩)
    have hcont : ContinuousOn W (Set.Icc u v) := hCW.mono huvJ
    have hder : ∀ t ∈ Set.Ico u v,
        HasDerivWithinAt W (-p t * W t) (Set.Ici t) t := by
      intro t ht
      apply (hDW t (huvJ ⟨ht.1, le_of_lt ht.2⟩)).hasDerivWithinAt
    have hbnd : ∀ t ∈ Set.Ico u v, ‖-p t * W t‖ ≤ K * ‖W t‖ := by
      intro t ht
      have hle := hpK t ⟨ht.1, le_of_lt ht.2⟩
      simpa [norm_mul] using
        (mul_le_mul_of_nonneg_right hle (norm_nonneg (W t)))
    have hall := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := W) (f' := fun t => -p t * W t) (K := K)
      (a := u) (b := v) hcont hder hu0 hbnd
    exact hall v ⟨huv, le_rfl⟩
  -- and to the left, by reflecting the independent variable
  have hleft : ∀ {u v : ℝ}, u ≤ v → Set.Icc u v ⊆ J → W v = 0 → W u = 0 := by
    intro u v huv huvJ hv0
    have hp' : ContinuousOn p (Set.Icc u v) := hp.mono huvJ
    obtain ⟨K, hK⟩ := (isCompact_Icc.bddAbove_image hp'.norm)
    have hpK : ∀ t ∈ Set.Icc u v, ‖p t‖ ≤ K := by
      intro t ht
      exact hK (by exact ⟨t, ht, rfl⟩)
    let F : ℝ → ℝ := fun t => W (-t)
    let F' : ℝ → ℝ := fun t => p (-t) * W (-t)
    have hDF : ∀ t, (-t) ∈ J → HasDerivAt F (F' t) t := by
      intro t ht
      have hcomp := (hDW (-t) ht).comp t (hasDerivAt_neg t)
      change HasDerivAt F (F' t) t
      convert hcomp using 1 <;> try {rfl} <;> simp [F, F'] <;> ring
    have hcont : ContinuousOn F (Set.Icc (-v) (-u)) := by
      intro t ht
      have htu : u ≤ -t := by linarith [ht.2]
      have htv : -t ≤ v := by linarith [ht.1]
      exact (hDF t (huvJ ⟨htu, htv⟩)).continuousAt.continuousWithinAt
    have hder : ∀ t ∈ Set.Ico (-v) (-u),
        HasDerivWithinAt F (F' t) (Set.Ici t) t := by
      intro t ht
      apply (hDF t ?_).hasDerivWithinAt
      apply huvJ
      constructor <;> linarith [ht.1, ht.2]
    have hbnd : ∀ t ∈ Set.Ico (-v) (-u), ‖F' t‖ ≤ K * ‖F t‖ := by
      intro t ht
      have horig : (-t) ∈ Set.Icc u v := by
        constructor <;> linarith [ht.1, ht.2]
      have hle := hpK (-t) horig
      simpa [F, F', norm_mul] using
        (mul_le_mul_of_nonneg_right hle (norm_nonneg (W (-t))))
    have hzero : F (-v) = 0 := by simpa [F] using hv0
    have hall := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := F) (f' := F') (K := K) (a := -v) (b := -u)
      hcont hder hzero hbnd
    have he := hall (-u) (by constructor <;> linarith)
    simpa [F] using he
  have hnW : ∀ x ∈ J, W x ≠ 0 := by
    intro x hx h0
    by_cases hle : x ≤ x₀
    · have := hright hle (hJ_conn.Icc_subset hx hx₀) h0
      exact hW₀ this
    · have hle' : x₀ ≤ x := le_of_lt (lt_of_not_ge hle)
      have hz := hleft hle' (hJ_conn.Icc_subset hx₀ hx) h0
      exact hW₀ hz
  have hJa : a ∈ J := hJ_sub ⟨le_rfl, le_of_lt hab⟩
  have hJb : b ∈ J := hJ_sub ⟨le_of_lt hab, le_rfl⟩
  have hy1c : ContinuousOn y₁ J := fun x hx => (hy₁ x hx).continuousAt.continuousWithinAt
  have hy2c : ContinuousOn y₂ J := fun x hx => (hy₂ x hx).continuousAt.continuousWithinAt
  -- a continuous, nowhere zero function on an interval cannot change sign.
  have Wsign :
      (∀ x ∈ Set.Icc a b, 0 < W x) ∨ (∀ x ∈ Set.Icc a b, W x < 0) := by
    have hna : W a ≠ 0 := hnW a hJa
    rcases lt_or_gt_of_ne hna with haNeg | haPos
    · right
      intro x hx
      have hnx : W x ≠ 0 := hnW x (hJ_sub hx)
      rcases lt_or_gt_of_ne hnx with hxneg | hxpos
      · exact hxneg
      · exfalso
        have hax : a ≤ x := hx.1
        have hc : ContinuousOn W (Set.Icc a x) :=
          hCW.mono (fun t ht => hJ_sub ⟨ht.1, le_trans ht.2 hx.2⟩)
        have hzero_mem : (0:ℝ) ∈ Set.Icc (W a) (W x) := ⟨le_of_lt haNeg, le_of_lt hxpos⟩
        obtain ⟨z, hz, hz0⟩ := (intermediate_value_Icc hax hc) hzero_mem
        exact (hnW z (hJ_sub ⟨hz.1, le_trans hz.2 hx.2⟩)) (by simpa using hz0)
    · left
      intro x hx
      have hnx : W x ≠ 0 := hnW x (hJ_sub hx)
      rcases lt_or_gt_of_ne hnx with hxneg | hxpos
      · exfalso
        have hax : a ≤ x := hx.1
        have hc : ContinuousOn W (Set.Icc a x) :=
          hCW.mono (fun t ht => hJ_sub ⟨ht.1, le_trans ht.2 hx.2⟩)
        have hzero_mem : (0:ℝ) ∈ Set.Icc (W x) (W a) := ⟨le_of_lt hxneg, le_of_lt haPos⟩
        obtain ⟨z, hz, hz0⟩ := (intermediate_value_Icc' hax hc) hzero_mem
        exact (hnW z (hJ_sub ⟨hz.1, le_trans hz.2 hx.2⟩)) (by simpa using hz0)
      · exact hxpos
  let m : ℝ := (a+b)/2
  have hm : m ∈ Set.Ioo a b := by dsimp [m]; constructor <;> linarith
  -- sign of y1 throughout the open interval
  have Ysign :
      (∀ x ∈ Set.Ioo a b, 0 < y₁ x) ∨
      (∀ x ∈ Set.Ioo a b, y₁ x < 0) := by
    have hnm := hne m hm
    rcases lt_or_gt_of_ne hnm with hmneg | hmpos
    · right
      intro x hx
      have hnx := hne x hx
      rcases lt_or_gt_of_ne hnx with hxneg | hxpos
      · exact hxneg
      · exfalso
        have hcseg : ContinuousOn y₁ (Set.uIcc m x) := by
          apply hy1c.mono
          intro t ht
          apply hJ_sub
          have ht' := (Set.mem_uIcc.mp ht)
          rcases ht' with hcase | hcase
          · exact ⟨le_trans (le_of_lt hm.1) hcase.1,
                    le_trans hcase.2 (le_of_lt hx.2)⟩
          · exact ⟨le_trans (le_of_lt hx.1) hcase.1,
                    le_trans hcase.2 (le_of_lt hm.2)⟩
        have hzero_mem : (0:ℝ) ∈ Set.uIcc (y₁ m) (y₁ x) := by
          exact (Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hmneg, le_of_lt hxpos⟩))
        obtain ⟨z,hz,hz0⟩ := (intermediate_value_uIcc hcseg) hzero_mem
        have hzint : z ∈ Set.Ioo a b := by
          rcases Set.mem_uIcc.mp hz with hz' | hz'
          · exact ⟨lt_of_lt_of_le hm.1 hz'.1, lt_of_le_of_lt hz'.2 hx.2⟩
          · exact ⟨lt_of_lt_of_le hx.1 hz'.1, lt_of_le_of_lt hz'.2 hm.2⟩
        exact (hne z hzint) (by simpa using hz0)
    · left
      intro x hx
      have hnx := hne x hx
      rcases lt_or_gt_of_ne hnx with hxneg | hxpos
      · exfalso
        have hcseg : ContinuousOn y₁ (Set.uIcc m x) := by
          apply hy1c.mono
          intro t ht
          apply hJ_sub
          rcases Set.mem_uIcc.mp ht with ht' | ht'
          · exact ⟨le_trans (le_of_lt hm.1) ht'.1,
                    le_trans ht'.2 (le_of_lt hx.2)⟩
          · exact ⟨le_trans (le_of_lt hx.1) ht'.1,
                    le_trans ht'.2 (le_of_lt hm.2)⟩
        have hzero_mem : (0:ℝ) ∈ Set.uIcc (y₁ m) (y₁ x) := by
          exact Set.mem_uIcc.mpr (Or.inr ⟨le_of_lt hxneg, le_of_lt hmpos⟩)
        obtain ⟨z,hz,hz0⟩ := (intermediate_value_uIcc hcseg) hzero_mem
        have hzint : z ∈ Set.Ioo a b := by
          rcases Set.mem_uIcc.mp hz with hz' | hz'
          · exact ⟨lt_of_lt_of_le hm.1 hz'.1, lt_of_le_of_lt hz'.2 hx.2⟩
          · exact ⟨lt_of_lt_of_le hx.1 hz'.1, lt_of_le_of_lt hz'.2 hm.2⟩
        exact (hne z hzint) (by simpa using hz0)
      · exact hxpos
  have hda : deriv y₁ a ≠ 0 := by
    intro h0
    apply hnW a hJa
    simp [W, hza, h0]
  have hdb : deriv y₁ b ≠ 0 := by
    intro h0
    apply hnW b hJb
    simp [W, hzb, h0]
  have hlimA : Tendsto (slope y₁ a) (𝓝[>] a) (𝓝 (deriv y₁ a)) := by
    apply (hasDerivAt_iff_tendsto_slope.mp (hy₁ a hJa)).mono_left
    apply nhdsWithin_mono
    intro t ht
    have hne' : t ≠ a := ne_of_gt ht
    simpa [hne']
  have hlimB : Tendsto (slope y₁ b) (𝓝[<] b) (𝓝 (deriv y₁ b)) := by
    apply (hasDerivAt_iff_tendsto_slope.mp (hy₁ b hJb)).mono_left
    apply nhdsWithin_mono
    intro t ht
    have hne' : t ≠ b := ne_of_lt ht
    simpa [hne']
  have Dsign :
      (0 < deriv y₁ a ∧ deriv y₁ b < 0) ∨
      (deriv y₁ a < 0 ∧ 0 < deriv y₁ b) := by
    rcases Ysign with ypos | yneg
    · left
      have ha0 : 0 ≤ deriv y₁ a := by
        apply ge_of_tendsto hlimA
        filter_upwards [Ioo_mem_nhdsGT hab] with t ht
        rw [slope_fun_def_field, hza]
        have hp' : 0 < y₁ t - 0 := by simpa using ypos t ht
        exact le_of_lt (div_pos hp' (sub_pos.mpr ht.1))
      have hb0 : deriv y₁ b ≤ 0 := by
        apply le_of_tendsto hlimB
        -- the interval on the left of b
        have hmem : Set.Ioo a b ∈ (𝓝[<] b) := Ioo_mem_nhdsLT hab
        filter_upwards [hmem] with t ht
        rw [slope_fun_def_field, hzb]
        have hp' : 0 < y₁ t - 0 := by simpa using ypos t ht
        exact le_of_lt (div_neg_of_pos_of_neg hp' (sub_neg.mpr ht.2))
      exact ⟨lt_of_le_of_ne ha0 hda.symm, lt_of_le_of_ne hb0 hdb⟩
    · right
      have ha0 : deriv y₁ a ≤ 0 := by
        apply le_of_tendsto hlimA
        filter_upwards [Ioo_mem_nhdsGT hab] with t ht
        rw [slope_fun_def_field, hza]
        have hp' : y₁ t - 0 < 0 := by simpa using yneg t ht
        exact le_of_lt (div_neg_of_neg_of_pos hp' (sub_pos.mpr ht.1))
      have hb0 : 0 ≤ deriv y₁ b := by
        apply ge_of_tendsto hlimB
        have hmem : Set.Ioo a b ∈ (𝓝[<] b) := Ioo_mem_nhdsLT hab
        filter_upwards [hmem] with t ht
        rw [slope_fun_def_field, hzb]
        have hp' : y₁ t - 0 < 0 := by simpa using yneg t ht
        exact le_of_lt (div_pos_of_neg_of_neg hp' (sub_neg.mpr ht.2))
      exact ⟨lt_of_le_of_ne ha0 hda, lt_of_le_of_ne hb0 hdb.symm⟩
  have eqWa : W a = -(y₂ a * deriv y₁ a) := by simp [W, hza]
  have eqWb : W b = -(y₂ b * deriv y₁ b) := by simp [W, hzb]
  have Lpp : ∀ {y d : ℝ}, 0 < -(y*d) → 0 < d → y < 0 := by
    intro y d h hd
    have h' : y*d < 0 := by linarith
    rcases (mul_neg_iff.mp h') with hcase | hcase
    · linarith [hcase.2]
    · exact hcase.1
  have Lpn : ∀ {y d : ℝ}, 0 < -(y*d) → d < 0 → 0 < y := by
    intro y d h hd
    have h' : y*d < 0 := by linarith
    rcases (mul_neg_iff.mp h') with hcase | hcase
    · exact hcase.1
    · linarith [hcase.2]
  have Lnp : ∀ {y d : ℝ}, -(y*d) < 0 → 0 < d → 0 < y := by
    intro y d h hd
    have h' : 0 < y*d := by linarith
    rcases (mul_pos_iff.mp h') with hcase | hcase
    · exact hcase.1
    · linarith [hcase.2]
  have Lnn : ∀ {y d : ℝ}, -(y*d) < 0 → d < 0 → y < 0 := by
    intro y d h hd
    have h' : 0 < y*d := by linarith
    rcases (mul_pos_iff.mp h') with hcase | hcase
    · linarith [hcase.2]
    · exact hcase.1
  have Y2ends :
      (y₂ a < 0 ∧ 0 < y₂ b) ∨ (0 < y₂ a ∧ y₂ b < 0) := by
    rcases Dsign with dcase | dcase
    · rcases Wsign with wp | wn
      · left
        have wa := wp a ⟨le_rfl, le_of_lt hab⟩
        have wb := wp b ⟨le_of_lt hab, le_rfl⟩
        rw [eqWa] at wa
        rw [eqWb] at wb
        exact ⟨Lpp wa dcase.1, Lpn wb dcase.2⟩
      · right
        have wa := wn a ⟨le_rfl, le_of_lt hab⟩
        have wb := wn b ⟨le_of_lt hab, le_rfl⟩
        rw [eqWa] at wa
        rw [eqWb] at wb
        exact ⟨Lnp wa dcase.1, Lnn wb dcase.2⟩
    · rcases Wsign with wp | wn
      · right
        have wa := wp a ⟨le_rfl, le_of_lt hab⟩
        have wb := wp b ⟨le_of_lt hab, le_rfl⟩
        rw [eqWa] at wa
        rw [eqWb] at wb
        exact ⟨Lpn wa dcase.1, Lpp wb dcase.2⟩
      · left
        have wa := wn a ⟨le_rfl, le_of_lt hab⟩
        have wb := wn b ⟨le_of_lt hab, le_rfl⟩
        rw [eqWa] at wa
        rw [eqWb] at wb
        exact ⟨Lnn wa dcase.1, Lnp wb dcase.2⟩
  have hcont2ab : ContinuousOn y₂ (Set.Icc a b) := hy2c.mono hJ_sub
  have ExistsRoot : ∃ c ∈ Set.Ioo a b, y₂ c = 0 := by
    rcases Y2ends with ends | ends
    · have hmem : (0:ℝ) ∈ Set.Icc (y₂ a) (y₂ b) := ⟨le_of_lt ends.1, le_of_lt ends.2⟩
      obtain ⟨c, hc, hcz⟩ := (intermediate_value_Icc (le_of_lt hab) hcont2ab) hmem
      have hca : a ≠ c := by
        intro he
        subst c
        linarith
      have hcb : c ≠ b := by
        intro he
        subst c
        linarith
      exact ⟨c, ⟨lt_of_le_of_ne hc.1 hca, lt_of_le_of_ne hc.2 hcb⟩, hcz⟩
    · have hmem : (0:ℝ) ∈ Set.Icc (y₂ b) (y₂ a) := ⟨le_of_lt ends.2, le_of_lt ends.1⟩
      obtain ⟨c, hc, hcz⟩ := (intermediate_value_Icc' (le_of_lt hab) hcont2ab) hmem
      have hca : a ≠ c := by
        intro he
        subst c
        linarith
      have hcb : c ≠ b := by
        intro he
        subst c
        linarith
      exact ⟨c, ⟨lt_of_le_of_ne hc.1 hca, lt_of_le_of_ne hc.2 hcb⟩, hcz⟩
  let R : ℝ → ℝ := fun x => y₂ x / y₁ x
  have hRc : ContinuousOn R (Set.Ioo a b) := by
    intro x hx
    have h2 : ContinuousWithinAt y₂ (Set.Ioo a b) x :=
      (hy₂ x (hJ_sub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).continuousAt.continuousWithinAt
    have h1 : ContinuousWithinAt y₁ (Set.Ioo a b) x :=
      (hy₁ x (hJ_sub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).continuousAt.continuousWithinAt
    change ContinuousWithinAt R (Set.Ioo a b) x
    convert h2.div h1 (hne x hx) using 1 <;> try {rfl}
  have hRd : ∀ x ∈ Set.Ioo a b, HasDerivAt R (W x / (y₁ x)^2) x := by
    intro x hx
    have hjx : x ∈ J := hJ_sub ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have h := (hy₂ x hjx).div (hy₁ x hjx) (hne x hx)
    convert h using 1 <;> try {rfl}
    · ring
  have Rinj : Set.InjOn R (Set.Ioo a b) := by
    rcases Wsign with wp | wn
    · apply (strictMonoOn_of_deriv_pos (convex_Ioo a b) hRc ?_).injOn
      rw [interior_Ioo]
      intro x hx
      rw [(hRd x hx).deriv]
      exact div_pos (wp x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
        (sq_pos_of_ne_zero (hne x hx))
    · apply (strictAntiOn_of_deriv_neg (convex_Ioo a b) hRc ?_).injOn
      rw [interior_Ioo]
      intro x hx
      rw [(hRd x hx).deriv]
      exact div_neg_of_neg_of_pos (wn x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
        (sq_pos_of_ne_zero (hne x hx))
  obtain ⟨c,hc,hcz⟩ := ExistsRoot
  refine ⟨c, ⟨hc,hcz⟩, ?_⟩
  intro d hd
  have heq : R d = R c := by
    simp [R, hd.2, hcz]
  exact Rinj hd.1 hc heq
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
