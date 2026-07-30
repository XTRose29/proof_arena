import Mathlib.Topology.Order.Monotone
import Submission.BridgeComplete

open Set
open Filter
open scoped Topology

namespace Submission.Helpers

def HasFourAlternatingValues (P : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ t₀ t₁ t₂ t₃ : ℝ,
    0 < t₀ ∧ t₀ < t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < P ∧
    f t₀ * f t₁ < 0 ∧ f t₁ * f t₂ < 0 ∧
    f t₂ * f t₃ < 0 ∧ f t₃ * f t₀ < 0

structure WeakMinMaxSignData (P : ℝ) (f : ℝ → ℝ) (a b : ℝ) : Prop where
  left_mem : a ∈ Ico (0 : ℝ) P
  right_mem : b ∈ Ico (0 : ℝ) P
  left_lt_right : a < b
  nonneg : ∀ z ∈ Icc a b, 0 ≤ f z
  nonpos_wrap : ∀ z ∈ Icc b (a + P), f z ≤ 0
  left_zero : f a = 0
  right_zero : f b = 0

structure WeakMaxMinSignData (P : ℝ) (f : ℝ → ℝ) (a b : ℝ) : Prop where
  left_mem : a ∈ Ico (0 : ℝ) P
  right_mem : b ∈ Ico (0 : ℝ) P
  left_lt_right : a < b
  nonpos : ∀ z ∈ Icc a b, f z ≤ 0
  nonneg_wrap : ∀ z ∈ Icc b (a + P), 0 ≤ f z
  left_zero : f a = 0
  right_zero : f b = 0

theorem exists_right_lt_zero {f : ℝ → ℝ} {x y : ℝ}
    (hf : ContinuousAt f x) (hfx : f x < 0) (hxy : x < y) :
    ∃ z ∈ Ioo x y, f z < 0 := by
  have hevent : ∀ᶠ z in 𝓝 x, f z < 0 :=
    hf.eventually_lt continuousAt_const hfx
  obtain ⟨epsilon, hepsilon, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  let d := min epsilon (y - x)
  have hd : 0 < d := lt_min hepsilon (sub_pos.mpr hxy)
  refine ⟨x + d / 2, ⟨by linarith, ?_⟩, ?_⟩
  · have hdle : d ≤ y - x := min_le_right _ _
    linarith
  · apply hnear
    rw [Real.dist_eq, show x + d / 2 - x = d / 2 by ring,
      abs_of_pos (half_pos hd)]
    have hdle : d ≤ epsilon := min_le_left _ _
    linarith

theorem exists_left_lt_zero {f : ℝ → ℝ} {x y : ℝ}
    (hf : ContinuousAt f x) (hfx : f x < 0) (hyx : y < x) :
    ∃ z ∈ Ioo y x, f z < 0 := by
  have hevent : ∀ᶠ z in 𝓝 x, f z < 0 :=
    hf.eventually_lt continuousAt_const hfx
  obtain ⟨epsilon, hepsilon, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  let d := min epsilon (x - y)
  have hd : 0 < d := lt_min hepsilon (sub_pos.mpr hyx)
  refine ⟨x - d / 2, ⟨?_, by linarith⟩, ?_⟩
  · have hdle : d ≤ x - y := min_le_right _ _
    linarith
  · apply hnear
    rw [Real.dist_eq, show x - d / 2 - x = -(d / 2) by ring,
      abs_neg, abs_of_pos (half_pos hd)]
    have hdle : d ≤ epsilon := min_le_left _ _
    linarith

theorem exists_right_pos {f : ℝ → ℝ} {x y : ℝ}
    (hf : ContinuousAt f x) (hfx : 0 < f x) (hxy : x < y) :
    ∃ z ∈ Ioo x y, 0 < f z := by
  have hevent : ∀ᶠ z in 𝓝 x, 0 < f z :=
    continuousAt_const.eventually_lt hf hfx
  obtain ⟨epsilon, hepsilon, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  let d := min epsilon (y - x)
  have hd : 0 < d := lt_min hepsilon (sub_pos.mpr hxy)
  refine ⟨x + d / 2, ⟨by linarith, ?_⟩, ?_⟩
  · have hdle : d ≤ y - x := min_le_right _ _
    linarith
  · apply hnear
    rw [Real.dist_eq, show x + d / 2 - x = d / 2 by ring,
      abs_of_pos (half_pos hd)]
    have hdle : d ≤ epsilon := min_le_left _ _
    linarith

theorem exists_left_pos {f : ℝ → ℝ} {x y : ℝ}
    (hf : ContinuousAt f x) (hfx : 0 < f x) (hyx : y < x) :
    ∃ z ∈ Ioo y x, 0 < f z := by
  have hevent : ∀ᶠ z in 𝓝 x, 0 < f z :=
    continuousAt_const.eventually_lt hf hfx
  obtain ⟨epsilon, hepsilon, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  let d := min epsilon (x - y)
  have hd : 0 < d := lt_min hepsilon (sub_pos.mpr hyx)
  refine ⟨x - d / 2, ⟨?_, by linarith⟩, ?_⟩
  · have hdle : d ≤ x - y := min_le_right _ _
    linarith
  · apply hnear
    rw [Real.dist_eq, show x - d / 2 - x = -(d / 2) by ring,
      abs_neg, abs_of_pos (half_pos hd)]
    have hdle : d ≤ epsilon := min_le_left _ _
    linarith

theorem fourAlternatingValues_of_signs {P : ℝ} {f : ℝ → ℝ}
    {t₀ t₁ t₂ t₃ : ℝ}
    (ht₀ : 0 < t₀) (ht₀₁ : t₀ < t₁) (ht₁₂ : t₁ < t₂)
    (ht₂₃ : t₂ < t₃) (ht₃ : t₃ < P)
    (h₀ : f t₀ < 0) (h₁ : 0 < f t₁) (h₂ : f t₂ < 0)
    (h₃ : 0 < f t₃) : HasFourAlternatingValues P f := by
  refine ⟨t₀, t₁, t₂, t₃, ht₀, ht₀₁, ht₁₂, ht₂₃, ht₃, ?_, ?_, ?_, ?_⟩
  · exact mul_neg_of_neg_of_pos h₀ h₁
  · exact mul_neg_of_pos_of_neg h₁ h₂
  · exact mul_neg_of_neg_of_pos h₂ h₃
  · exact mul_neg_of_pos_of_neg h₃ h₀

theorem fourAlternatingValues_of_opposite_signs {P : ℝ} {f : ℝ → ℝ}
    {t₀ t₁ t₂ t₃ : ℝ}
    (ht₀ : 0 < t₀) (ht₀₁ : t₀ < t₁) (ht₁₂ : t₁ < t₂)
    (ht₂₃ : t₂ < t₃) (ht₃ : t₃ < P)
    (h₀ : 0 < f t₀) (h₁ : f t₁ < 0) (h₂ : 0 < f t₂)
    (h₃ : f t₃ < 0) : HasFourAlternatingValues P f := by
  refine ⟨t₀, t₁, t₂, t₃, ht₀, ht₀₁, ht₁₂, ht₂₃, ht₃, ?_, ?_, ?_, ?_⟩
  · exact mul_neg_of_pos_of_neg h₀ h₁
  · exact mul_neg_of_neg_of_pos h₁ h₂
  · exact mul_neg_of_pos_of_neg h₂ h₃
  · exact mul_neg_of_neg_of_pos h₃ h₀

set_option maxHeartbeats 2000000 in
theorem exists_weak_bridge_sign_data {P : ℝ} {f : ℝ → ℝ}
    (hP : 0 < P) (hf : Continuous f) (hperiod : Function.Periodic f P)
    (hno : ¬ HasFourAlternatingValues P f)
    (hpos : ∃ t ∈ Ioo (0 : ℝ) P, 0 < f t)
    (hneg : ∃ t ∈ Ioo (0 : ℝ) P, f t < 0) :
    (∃ a b, WeakMinMaxSignData P f a b) ∨
      ∃ a b, WeakMaxMinSignData P f a b := by
  let N : Set ℝ := {t | t ∈ Ioo (0 : ℝ) P ∧ f t < 0}
  let Q : Set ℝ := {t | t ∈ Ioo (0 : ℝ) P ∧ 0 < f t}
  have hNne : N.Nonempty := by
    rcases hneg with ⟨t, ht, hft⟩
    exact ⟨t, ht, hft⟩
  have hQne : Q.Nonempty := by
    rcases hpos with ⟨t, ht, hft⟩
    exact ⟨t, ht, hft⟩
  have hNbddBelow : BddBelow N := ⟨0, fun t ht => ht.1.1.le⟩
  have hNbddAbove : BddAbove N := ⟨P, fun t ht => ht.1.2.le⟩
  have hQbddBelow : BddBelow Q := ⟨0, fun t ht => ht.1.1.le⟩
  have hQbddAbove : BddAbove Q := ⟨P, fun t ht => ht.1.2.le⟩
  by_cases hNPN : ∃ x ∈ N, ∃ z ∈ Q, ∃ y ∈ N, x < z ∧ z < y
  · rcases hNPN with ⟨x, hxN, z, hzQ, y, hyN, hxz, hzy⟩
    have hQbetween : ∀ w ∈ Q, x < w ∧ w < y := by
      intro w hwQ
      constructor
      · by_contra hnot
        have hwle : w ≤ x := le_of_not_gt hnot
        have hwne : w ≠ x := by intro h; subst w; linarith [hxN.2, hwQ.2]
        have hwx : w < x := lt_of_le_of_ne hwle hwne
        exact hno (fourAlternatingValues_of_opposite_signs
          hwQ.1.1 hwx hxz hzy hyN.1.2 hwQ.2 hxN.2 hzQ.2 hyN.2)
      · by_contra hnot
        have hywle : y ≤ w := le_of_not_gt hnot
        have hywne : y ≠ w := by intro h; subst w; linarith [hyN.2, hwQ.2]
        have hyw : y < w := lt_of_le_of_ne hywle hywne
        exact hno (fourAlternatingValues_of_signs
          hxN.1.1 hxz hzy hyw hwQ.1.2 hxN.2 hzQ.2 hyN.2 hwQ.2)
    let a := sInf Q
    let b := sSup Q
    have hxa : x ≤ a := le_csInf hQne fun w hw => (hQbetween w hw).1.le
    have hby : b ≤ y := csSup_le hQne fun w hw => (hQbetween w hw).2.le
    have ha0 : 0 < a := hxN.1.1.trans_le hxa
    have hbP : b < P := hby.trans_lt hyN.1.2
    have hab : a < b := by
      rcases hQne with ⟨w, hwQ⟩
      obtain ⟨w', hww', hw'Q⟩ := exists_right_pos hf.continuousAt hwQ.2
        (hQbetween w hwQ).2
      have haw : a ≤ w := csInf_le hQbddBelow hwQ
      have hw'b : w' ≤ b := le_csSup hQbddAbove
        ⟨⟨hwQ.1.1.trans hww'.1, hww'.2.trans hyN.1.2⟩, hw'Q⟩
      exact haw.trans_lt (hww'.1.trans_le hw'b)
    have haP : a < P := hab.trans hbP
    have hQbetweenValues : ∀ p ∈ Q, ∀ q ∈ Q, ∀ t, p < t → t < q →
        0 ≤ f t := by
      intro p hp q hq t hpt htq
      by_contra hnot
      have hft : f t < 0 := lt_of_not_ge hnot
      exact hno (fourAlternatingValues_of_signs hxN.1.1
        (hQbetween p hp).1 hpt htq
        ((hQbetween q hq).2.trans hyN.1.2) hxN.2 hp.2 hft hq.2)
    have hfaNonneg : 0 ≤ f a := by
      have haClosure : a ∈ closure Q := csInf_mem_closure hQne hQbddBelow
      exact (closure_minimal (fun w hw => hw.2.le)
        (isClosed_le continuous_const hf)) haClosure
    have hfbNonneg : 0 ≤ f b := by
      have hbClosure : b ∈ closure Q := csSup_mem_closure hQne hQbddAbove
      exact (closure_minimal (fun w hw => hw.2.le)
        (isClosed_le continuous_const hf)) hbClosure
    have hfa : f a = 0 := by
      apply le_antisymm
      · by_contra hnot
        have hfaPos : 0 < f a := lt_of_not_ge hnot
        obtain ⟨w, hw, hfw⟩ := exists_left_pos hf.continuousAt hfaPos ha0
        have hwQ : w ∈ Q := ⟨⟨hw.1, hw.2.trans haP⟩, hfw⟩
        have haw : a ≤ w := csInf_le hQbddBelow hwQ
        exact (not_lt_of_ge haw) hw.2
      · exact hfaNonneg
    have hfb : f b = 0 := by
      apply le_antisymm
      · by_contra hnot
        have hfbPos : 0 < f b := lt_of_not_ge hnot
        obtain ⟨w, hw, hfw⟩ := exists_right_pos hf.continuousAt hfbPos hbP
        have hwQ : w ∈ Q := ⟨⟨(ha0.trans hab).trans hw.1, hw.2⟩, hfw⟩
        have hwb : w ≤ b := le_csSup hQbddAbove hwQ
        exact (not_lt_of_ge hwb) hw.1
      · exact hfbNonneg
    have hinside : ∀ t ∈ Icc a b, 0 ≤ f t := by
      intro t ht
      rcases ht.1.eq_or_lt with rfl | hat
      · simp [hfa]
      rcases ht.2.eq_or_lt with rfl | htb
      · simp [hfb]
      obtain ⟨p, hpQ, hpt⟩ := (csInf_lt_iff hQbddBelow hQne).mp hat
      obtain ⟨q, hqQ, htq⟩ := (lt_csSup_iff hQbddAbove hQne).mp htb
      exact hQbetweenValues p hpQ q hqQ t hpt htq
    have hleft : ∀ t ∈ Icc (0 : ℝ) a, f t ≤ 0 := by
      intro t ht
      by_contra hnot
      have hft : 0 < f t := lt_of_not_ge hnot
      by_cases ht0 : t = 0
      · subst t
        obtain ⟨w, hw, hfw⟩ := exists_right_pos hf.continuousAt hft
          (hxN.1.1)
        have hwQ : w ∈ Q := ⟨⟨hw.1, hw.2.trans hxN.1.2⟩, hfw⟩
        exact (lt_asymm hw.2 (hQbetween w hwQ).1)
      · have htQ : t ∈ Q := ⟨⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
          ht.2.trans_lt haP⟩, hft⟩
        exact (not_lt_of_ge (csInf_le hQbddBelow htQ))
          (lt_of_le_of_ne ht.2 (by intro h; subst t; linarith [hfa, hft]))
    have hright : ∀ t ∈ Icc b P, f t ≤ 0 := by
      intro t ht
      by_contra hnot
      have hft : 0 < f t := lt_of_not_ge hnot
      by_cases htP : t = P
      · subst t
        have hf0 : f P = f 0 := by simpa using hperiod 0
        rw [hf0] at hft
        obtain ⟨w, hw, hfw⟩ := exists_right_pos hf.continuousAt hft hxN.1.1
        have hwQ : w ∈ Q := ⟨⟨hw.1, hw.2.trans hxN.1.2⟩, hfw⟩
        exact (lt_asymm hw.2 (hQbetween w hwQ).1)
      · have htQ : t ∈ Q := ⟨⟨(ha0.trans hab).trans_le ht.1,
          lt_of_le_of_ne ht.2 htP⟩, hft⟩
        exact (not_lt_of_ge (le_csSup hQbddAbove htQ))
          (lt_of_le_of_ne ht.1 (by intro h; subst t; linarith [hfb, hft]))
    left
    refine ⟨a, b, ⟨⟨ha0.le, haP⟩, ⟨(ha0.trans hab).le, hbP⟩,
      hab, hinside, ?_, hfa, hfb⟩⟩
    intro t ht
    by_cases htP : t ≤ P
    · exact hright t ⟨ht.1, htP⟩
    · have ht' : t - P ∈ Icc (0 : ℝ) a := ⟨by linarith, by linarith [ht.2]⟩
      have hper := hperiod (t - P)
      rw [show t - P + P = t by ring] at hper
      rw [hper]
      exact hleft (t - P) ht'
  · have hf0 : 0 ≤ f 0 := by
      by_contra hnot
      have hf0neg : f 0 < 0 := lt_of_not_ge hnot
      rcases hQne with ⟨z, hzQ⟩
      obtain ⟨x, hx, hfx⟩ := exists_right_lt_zero hf.continuousAt hf0neg hzQ.1.1
      have hfPneg : f P < 0 := by
        rw [show f P = f 0 by simpa using hperiod 0]
        exact hf0neg
      obtain ⟨y, hy, hfy⟩ := exists_left_lt_zero hf.continuousAt hfPneg hzQ.1.2
      exact hNPN ⟨x, ⟨⟨hx.1, hx.2.trans hzQ.1.2⟩, hfx⟩,
        z, hzQ, y, ⟨⟨hzQ.1.1.trans hy.1, hy.2⟩, hfy⟩,
        hx.2, hy.1⟩
    have hfP : 0 ≤ f P := by
      rw [show f P = f 0 by simpa using hperiod 0]
      exact hf0
    let a := sInf N
    let b := sSup N
    have ha0 : 0 ≤ a := le_csInf hNne fun w hw => hw.1.1.le
    have hbP : b ≤ P := csSup_le hNne fun w hw => hw.1.2.le
    have haP : a < P := by
      rcases hNne with ⟨w, hw⟩
      exact (csInf_le hNbddBelow hw).trans_lt hw.1.2
    have hb0 : 0 < b := by
      rcases hNne with ⟨w, hw⟩
      exact hw.1.1.trans_le (le_csSup hNbddAbove hw)
    have hab : a < b := by
      rcases hNne with ⟨w, hwN⟩
      obtain ⟨w', hww', hw'neg⟩ := exists_right_lt_zero hf.continuousAt hwN.2
        hwN.1.2
      have haw : a ≤ w := csInf_le hNbddBelow hwN
      have hw'b : w' ≤ b := le_csSup hNbddAbove
        ⟨⟨hwN.1.1.trans hww'.1, hww'.2⟩, hw'neg⟩
      exact haw.trans_lt (hww'.1.trans_le hw'b)
    have hNbetween : ∀ p ∈ N, ∀ q ∈ N, ∀ t, p < t → t < q →
        f t ≤ 0 := by
      intro p hp q hq t hpt htq
      by_contra hnot
      exact hNPN ⟨p, hp, t,
        ⟨⟨hp.1.1.trans hpt, htq.trans hq.1.2⟩, lt_of_not_ge hnot⟩,
        q, hq, hpt, htq⟩
    have hfaNonpos : f a ≤ 0 := by
      have haClosure : a ∈ closure N := csInf_mem_closure hNne hNbddBelow
      exact (closure_minimal (fun w hw => hw.2.le)
        (isClosed_le hf continuous_const)) haClosure
    have hfbNonpos : f b ≤ 0 := by
      have hbClosure : b ∈ closure N := csSup_mem_closure hNne hNbddAbove
      exact (closure_minimal (fun w hw => hw.2.le)
        (isClosed_le hf continuous_const)) hbClosure
    have hfa : f a = 0 := by
      apply le_antisymm hfaNonpos
      by_cases ha : a = 0
      · simpa [ha] using hf0
      · by_contra hnot
        have hfaneg : f a < 0 := lt_of_not_ge hnot
        obtain ⟨w, hw, hfw⟩ := exists_left_lt_zero hf.continuousAt hfaneg
          (lt_of_le_of_ne ha0 (Ne.symm ha))
        have hwN : w ∈ N := ⟨⟨hw.1, hw.2.trans haP⟩, hfw⟩
        have haw : a ≤ w := csInf_le hNbddBelow hwN
        exact (not_lt_of_ge haw) hw.2
    have hfb : f b = 0 := by
      apply le_antisymm hfbNonpos
      by_cases hb : b = P
      · simpa [hb] using hfP
      · by_contra hnot
        have hfbneg : f b < 0 := lt_of_not_ge hnot
        obtain ⟨w, hw, hfw⟩ := exists_right_lt_zero hf.continuousAt hfbneg
          (lt_of_le_of_ne hbP hb)
        have hwN : w ∈ N := ⟨⟨hb0.trans hw.1, hw.2⟩, hfw⟩
        have hwb : w ≤ b := le_csSup hNbddAbove hwN
        exact (not_lt_of_ge hwb) hw.1
    have hinside : ∀ t ∈ Icc a b, f t ≤ 0 := by
      intro t ht
      rcases ht.1.eq_or_lt with rfl | hat
      · simp [hfa]
      rcases ht.2.eq_or_lt with rfl | htb
      · simp [hfb]
      obtain ⟨p, hpN, hpt⟩ := (csInf_lt_iff hNbddBelow hNne).mp hat
      obtain ⟨q, hqN, htq⟩ := (lt_csSup_iff hNbddAbove hNne).mp htb
      exact hNbetween p hpN q hqN t hpt htq
    have hleft : ∀ t ∈ Icc (0 : ℝ) a, 0 ≤ f t := by
      intro t ht
      by_contra hnot
      have hft : f t < 0 := lt_of_not_ge hnot
      by_cases ht0 : t = 0
      · subst t
        exact (not_lt_of_ge hf0) hft
      · have htN : t ∈ N := ⟨⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
          ht.2.trans_lt haP⟩, hft⟩
        exact (not_lt_of_ge (csInf_le hNbddBelow htN))
          (lt_of_le_of_ne ht.2 (by intro h; subst t; linarith [hfa, hft]))
    have hright : ∀ t ∈ Icc b P, 0 ≤ f t := by
      intro t ht
      by_contra hnot
      have hft : f t < 0 := lt_of_not_ge hnot
      by_cases htP : t = P
      · subst t
        exact (not_lt_of_ge hfP) hft
      · have htN : t ∈ N := ⟨⟨hb0.trans_le ht.1,
          lt_of_le_of_ne ht.2 htP⟩, hft⟩
        exact (not_lt_of_ge (le_csSup hNbddAbove htN))
          (lt_of_le_of_ne ht.1 (by intro h; subst t; linarith [hfb, hft]))
    by_cases hb : b < P
    · right
      refine ⟨a, b, ⟨⟨ha0, haP⟩, ⟨hb0.le, hb⟩, hab, hinside,
        ?_, hfa, hfb⟩⟩
      intro t ht
      by_cases htP : t ≤ P
      · exact hright t ⟨ht.1, htP⟩
      · have ht' : t - P ∈ Icc (0 : ℝ) a := ⟨by linarith, by linarith [ht.2]⟩
        have hper := hperiod (t - P)
        rw [show t - P + P = t by ring] at hper
        rw [hper]
        exact hleft (t - P) ht'
    · have hbEq : b = P := le_antisymm hbP (le_of_not_gt hb)
      have hf0zero : f 0 = 0 := by
        have hper : f P = f 0 := by simpa using hperiod 0
        rw [← hper, ← hbEq, hfb]
      have haPos : 0 < a := by
        rcases hQne with ⟨w, hwQ⟩
        have hwle : w ≤ a := by
          by_contra hnot
          have haw : a < w := lt_of_not_ge hnot
          have hwb : w ≤ b := by rw [hbEq]; exact hwQ.1.2.le
          linarith [hinside w ⟨haw.le, hwb⟩, hwQ.2]
        exact hwQ.1.1.trans_le hwle
      left
      refine ⟨0, a, ⟨⟨le_rfl, hP⟩, ⟨haPos.le, haP⟩, haPos,
        hleft, ?_, hf0zero, hfa⟩⟩
      intro t ht
      have htIcc : t ∈ Icc a b := by
        rw [hbEq]
        simpa only [zero_add] using ht
      exact hinside t htIcc

end Submission.Helpers
