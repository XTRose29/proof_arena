import Submission.MoserGlobal
import Mathlib.Topology.UnitInterval

open Set Function Metric Filter
open scoped ContDiff NNReal Topology unitInterval

namespace Submission.MoserSmoothFlow

noncomputable section

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def stepChain (g : ℕ → V → V) : ℕ → V → V
  | 0 => id
  | n + 1 => g n ∘ stepChain g n

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
@[simp]
theorem stepChain_zero (g : ℕ → V → V) : stepChain g 0 = id := rfl

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
@[simp]
theorem stepChain_succ (g : ℕ → V → V) (n : ℕ) :
    stepChain g (n + 1) = g n ∘ stepChain g n := rfl

section

variable (f : ℝ → V → V) (hf : ContDiff ℝ ∞ (uncurry f))
  (L K : ℝ≥0) (hbound : ∀ t z, ‖f t z‖ ≤ L)
  (hlip : ∀ t, LipschitzWith K (f t))

include f hf L K hbound hlip

def unitEndTime : Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩

def unitTimeOneMap (x : V) : V :=
  Submission.MoserGlobal.unitFlow f hf L K hbound hlip unitEndTime x

theorem unitTimeOneMap_contDiff_nat (n : ℕ) :
    ContDiff ℝ n (unitTimeOneMap f hf L K hbound hlip) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let flow := Submission.MoserGlobal.unitFlow f hf L K hbound hlip
  let data : (p : Icc (0 : ℝ) 1) →
      Submission.MoserFlow.PicardTowerData f p (flow p x) 1 n := fun p =>
    Submission.MoserFlow.localPicardTowerData f hf p (flow p x) 1 n
  let cover : Icc (0 : ℝ) 1 → Set (Icc (0 : ℝ) 1) := fun p =>
    (fun q : Icc (0 : ℝ) 1 => (q : ℝ) - (p : ℝ)) ⁻¹'
        Ioo (-(data p).ε / 2) ((data p).ε / 2) ∩
      (fun q => flow q x) ⁻¹' ball (flow p x) 1
  have hcoverOpen : ∀ p, IsOpen (cover p) := by
    intro p
    apply IsOpen.inter
    · exact isOpen_Ioo.preimage (continuous_subtype_val.sub continuous_const)
    · exact isOpen_ball.preimage
        (Submission.MoserGlobal.unitFlow_continuous f hf L K hbound hlip x)
  have hcoverAll : univ ⊆ ⋃ p, cover p := by
    intro p _hp
    apply mem_iUnion.mpr
    refine ⟨p, ?_⟩
    constructor
    · change -(data p).ε / 2 < (p : ℝ) - p ∧
        (p : ℝ) - p < (data p).ε / 2
      constructor <;> simp only [sub_self] <;> linarith [(data p).hε]
    · exact mem_ball_self (by norm_num)
  obtain ⟨τ, hτ0, hτmono, ⟨m, hm⟩, hsegments⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcoverOpen hcoverAll
  choose center hcenter using hsegments
  let step : (k : ℕ) → Submission.MoserFlow.PicardStepData f
      (τ k) (τ (k + 1)) (flow (center k) x) 1 n := fun k => by
    let d := data (center k)
    have htime : (τ k : ℝ) ≤ τ (k + 1) := hτmono (Nat.le_succ k)
    have hkleft : τ k ∈ Icc (τ k) (τ (k + 1)) := ⟨le_rfl, htime⟩
    have hkright : τ (k + 1) ∈ Icc (τ k) (τ (k + 1)) := ⟨htime, le_rfl⟩
    have hleftRaw := hcenter k hkleft
    change
      (((τ k : ℝ) - center k ∈
          Ioo (-(data (center k)).ε / 2) ((data (center k)).ε / 2)) ∧
        flow (τ k) x ∈ ball (flow (center k) x) 1) at hleftRaw
    have hleft :
        ((τ k : ℝ) - center k ∈ Ioo (-d.ε / 2) (d.ε / 2)) ∧
          flow (τ k) x ∈ ball (flow (center k) x) 1 := by
      simpa only [d] using hleftRaw
    have hrightRaw := hcenter k hkright
    change
      (((τ (k + 1) : ℝ) - center k ∈
          Ioo (-(data (center k)).ε / 2) ((data (center k)).ε / 2)) ∧
        flow (τ (k + 1)) x ∈ ball (flow (center k) x) 1) at hrightRaw
    have hright :
        ((τ (k + 1) : ℝ) - center k ∈ Ioo (-d.ε / 2) (d.ε / 2)) ∧
          flow (τ (k + 1)) x ∈ ball (flow (center k) x) 1 := by
      simpa only [d] using hrightRaw
    have hmin : (center k : ℝ) - d.ε ≤ τ k := by
      linarith [hleft.1.1, d.hε]
    have hmax : (τ (k + 1) : ℝ) ≤ (center k : ℝ) + d.ε := by
      linarith [hright.1.2, d.hε]
    have hlength : (τ (k + 1) : ℝ) - τ k ≤ d.ε := by
      linarith [hleft.1.1, hright.1.2]
    have hspan : max ((τ (k + 1) : ℝ) - τ k) ((τ k : ℝ) - τ k) ≤
        max (((center k : ℝ) + d.ε) - center k)
          ((center k : ℝ) - ((center k : ℝ) - d.ε)) := by
      simpa only [sub_self, max_eq_left (sub_nonneg.mpr htime),
        add_sub_cancel_left, sub_sub_cancel, max_self] using hlength
    exact d.toStep htime hmin hmax hspan
  let maps : ℕ → V → V := fun k => (step k).map
  have hchain : ∀ k : ℕ,
      ContDiffAt ℝ n (stepChain maps k) x ∧
      stepChain maps k =ᶠ[𝓝 x] fun y => flow (τ k) y := by
    intro k
    induction k with
    | zero =>
        constructor
        · exact contDiffAt_id
        · apply Filter.Eventually.of_forall
          intro y
          rw [stepChain_zero, id_eq, hτ0]
          exact (Submission.MoserGlobal.unitFlow_zero_time f hf L K hbound hlip y).symm
    | succ k ih =>
        rcases ih with ⟨hreg, heq⟩
        have hkleft : τ k ∈ Icc (τ k) (τ (k + 1)) :=
          ⟨le_rfl, hτmono (Nat.le_succ k)⟩
        have hxballFlow : flow (τ k) x ∈ ball (flow (center k) x) 1 := by
          exact (hcenter k hkleft).2
        have hxEq : stepChain maps k x = flow (τ k) x := heq.self_of_nhds
        have hxball : stepChain maps k x ∈ ball (flow (center k) x) 1 := by
          rw [hxEq]
          exact hxballFlow
        have hstepAt : ContDiffAt ℝ n (step k).map (stepChain maps k x) :=
          ((step k).map_contDiffOn hf).contDiffAt (isOpen_ball.mem_nhds hxball)
        have hregSucc : ContDiffAt ℝ n (stepChain maps (k + 1)) x := by
          change ContDiffAt ℝ n ((step k).map ∘ stepChain maps k) x
          exact hstepAt.comp x hreg
        have hballEv : ∀ᶠ y in 𝓝 x,
            stepChain maps k y ∈ ball (flow (center k) x) 1 :=
          hreg.continuousAt (isOpen_ball.mem_nhds hxball)
        constructor
        · exact hregSucc
        · filter_upwards [heq, hballEv] with y hyEq hyBall
          change (step k).map (stepChain maps k y) = flow (τ (k + 1)) y
          rw [hyEq]
          have hyBall' : flow (τ k) y ∈ ball (flow (center k) x) 1 := by
            rwa [← hyEq]
          have hyClosed : flow (τ k) y ∈ closedBall (flow (center k) x) 1 :=
            ball_subset_closedBall hyBall'
          change Submission.MoserFlow.solutionAt (step k).hpl (step k).endTime
              (flow (τ k) y) = flow (τ (k + 1)) y
          simpa only [flow, Submission.MoserFlow.PicardStepData.endTime] using
            Submission.MoserGlobal.solutionAt_eq_unitFlow f hf L K hbound hlip
              (τ k).2.1 (τ (k + 1)).2.2 (step k).htime
              (step k).hpl hyClosed rfl (step k).endTime
  obtain ⟨hreg, heq⟩ := hchain m
  have hτm : τ m = (1 : Icc (0 : ℝ) 1) := hm m le_rfl
  have heqEnd : stepChain maps m =ᶠ[𝓝 x]
      unitTimeOneMap f hf L K hbound hlip := by
    filter_upwards [heq] with y hy
    rw [hτm] at hy
    exact hy
  exact hreg.congr_of_eventuallyEq heqEnd.symm

theorem unitTimeOneMap_contDiff :
    ContDiff ℝ ∞ (unitTimeOneMap f hf L K hbound hlip) := by
  rw [contDiff_infty]
  exact unitTimeOneMap_contDiff_nat f hf L K hbound hlip

end

end

end Submission.MoserSmoothFlow
