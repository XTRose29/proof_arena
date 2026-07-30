import Submission.JordanLoop
import Submission.Transversal

open Function Metric Set Topology
open scoped Convex

open LeanEval.Dynamics

namespace Submission.OrbitArc

noncomputable section

/-- A trajectory restricted to an ordered compact time interval and
reparameterized by the unit interval. -/
def orbitArc (γ : ℝ → Plane) {a b : ℝ} (hab : a ≤ b)
    (hγcont : ContinuousOn γ (Icc a b)) :
    Path (γ a) (γ b) where
  toFun u := γ (a + (b - a) * (u : ℝ))
  continuous_toFun :=
    hγcont.comp_continuous
      (continuous_const.add
        (continuous_const.mul continuous_subtype_val))
      (by
        intro u
        constructor
        · exact le_add_of_nonneg_right
            (mul_nonneg (sub_nonneg.mpr hab) u.2.1)
        · have hu := u.2.2
          nlinarith [sub_nonneg.mpr hab])
  source' := by simp
  target' := by simp

@[simp]
theorem orbitArc_apply (γ : ℝ → Plane) {a b : ℝ} (hab : a ≤ b)
    (hγcont : ContinuousOn γ (Icc a b)) (u : unitInterval) :
    orbitArc γ hab hγcont u = γ (a + (b - a) * (u : ℝ)) :=
  rfl

theorem injective_orbitArc (γ : ℝ → Plane) {a b : ℝ} (hab : a < b)
    (hγcont : ContinuousOn γ (Icc a b))
    (hγinj : InjOn γ (Icc a b)) :
    Injective (orbitArc γ hab.le hγcont) := by
  intro u v huv
  apply Subtype.ext
  have huTime : a + (b - a) * (u : ℝ) ∈ Icc a b := by
    constructor
    · exact le_add_of_nonneg_right
        (mul_nonneg (sub_nonneg.mpr hab.le) u.2.1)
    · nlinarith [u.2.2, sub_pos.mpr hab]
  have hvTime : a + (b - a) * (v : ℝ) ∈ Icc a b := by
    constructor
    · exact le_add_of_nonneg_right
        (mul_nonneg (sub_nonneg.mpr hab.le) v.2.1)
    · nlinarith [v.2.2, sub_pos.mpr hab]
  have htime :=
    hγinj huTime hvTime (by simpa only [orbitArc_apply] using huv)
  nlinarith [sub_pos.mpr hab]

theorem range_orbitArc (γ : ℝ → Plane) {a b : ℝ} (hab : a < b)
    (hγcont : ContinuousOn γ (Icc a b)) :
    range (orbitArc γ hab.le hγcont) = γ '' Icc a b := by
  apply Subset.antisymm
  · rintro y ⟨u, rfl⟩
    refine ⟨a + (b - a) * (u : ℝ), ?_, rfl⟩
    constructor
    · exact le_add_of_nonneg_right
        (mul_nonneg (sub_nonneg.mpr hab.le) u.2.1)
    · nlinarith [u.2.2, sub_pos.mpr hab]
  · rintro y ⟨t, ht, rfl⟩
    let u : unitInterval :=
      ⟨(t - a) / (b - a), by
        constructor
        · exact div_nonneg (sub_nonneg.mpr ht.1)
            (sub_nonneg.mpr hab.le)
        · exact (div_le_one (sub_pos.mpr hab)).mpr
            (sub_le_sub_right ht.2 a)⟩
    refine ⟨u, ?_⟩
    rw [orbitArc_apply]
    congr 1
    dsimp [u]
    field_simp [sub_ne_zero.mpr hab.ne.symm]
    ring

/-- The affine transverse coordinate vanishes along the entire segment
joining two points of the same affine transversal. -/
theorem transverseValue_segment_eq_zero
    {v p x y z : Plane}
    (hx : Transversal.transverseValue v p x = 0)
    (hy : Transversal.transverseValue v p y = 0)
    (hz : z ∈ [x -[ℝ] y]) :
    Transversal.transverseValue v p z = 0 := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  unfold Transversal.transverseValue at hx hy ⊢
  rw [show (1 - t) • x + t • y - p =
      (1 - t) • (x - p) + t • (y - p) by
        module]
  rw [map_add, map_smul, map_smul, hx, hy]
  simp

/-- The circle map obtained by following an orbit arc and returning along
the straight segment between its endpoints. -/
def closingLoop
    (γ : ℝ → Plane) {a b : ℝ} (hab : a < b)
    (hγcont : ContinuousOn γ (Icc a b)) :
    C(Circle, Plane) :=
  let α := orbitArc γ hab.le hγcont
  let σ := Path.segment (γ b) (γ a)
  ⟨JordanLoop.onCircle (α.trans σ),
    JordanLoop.continuous_onCircle (α.trans σ)⟩

theorem range_closingLoop
    (γ : ℝ → Plane) {a b : ℝ} (hab : a < b)
    (hγcont : ContinuousOn γ (Icc a b)) :
    range (closingLoop γ hab hγcont) =
      (γ '' Icc a b) ∪ [γ b -[ℝ] γ a] := by
  change
    range
        (JordanLoop.onCircle
          ((orbitArc γ hab.le hγcont).trans
            (Path.segment (γ b) (γ a)))) =
      (γ '' Icc a b) ∪ [γ b -[ℝ] γ a]
  rw [JordanLoop.range_onCircle_eq_path, Path.trans_range,
    range_orbitArc γ hab hγcont, Path.range_segment]

theorem injective_closingLoop
    (γ : ℝ → Plane) {a b : ℝ} (hab : a < b)
    (hγcont : ContinuousOn γ (Icc a b))
    (hγinj : InjOn γ (Icc a b))
    (hinter :
      (γ '' Icc a b) ∩ [γ b -[ℝ] γ a] ⊆ {γ a, γ b}) :
    Injective (closingLoop γ hab hγcont) := by
  let α := orbitArc γ hab.le hγcont
  let σ := Path.segment (γ b) (γ a)
  have hαinj : Injective α :=
    injective_orbitArc γ hab hγcont hγinj
  have hσinj : Injective σ := by
    apply Path.segment_injective_of_ne
    intro hba
    have hab' :=
      hγinj ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hba.symm
    exact hab.ne hab'
  have hinter' : range α ∩ range σ ⊆ {γ a, γ b} := by
    simpa only [α, σ, range_orbitArc γ hab hγcont,
      Path.range_segment] using hinter
  exact
    JordanLoop.injective_onCircle (α.trans σ)
      (JordanLoop.injOn_extend_Ico_trans
        α σ hαinj hσinj hinter')

/-- A trajectory arc between consecutive hits of a transversal, closed by
the straight transversal segment, is a Jordan loop. -/
theorem two_components_of_consecutive_transverse_hits
    (γ : ℝ → Plane) {a b : ℝ} (hab : a < b)
    (hγcont : ContinuousOn γ (Icc a b))
    (hγinj : InjOn γ (Icc a b))
    {v p : Plane}
    (ha : Transversal.transverseValue v p (γ a) = 0)
    (hb : Transversal.transverseValue v p (γ b) = 0)
    (hconsecutive : ∀ t ∈ Icc a b,
      Transversal.transverseValue v p (γ t) = 0 →
        t = a ∨ t = b) :
    Nat.card
        (ConnectedComponents
          (((γ '' Icc a b) ∪ [γ b -[ℝ] γ a])ᶜ : Set Plane)) =
      2 := by
  let α := orbitArc γ hab.le hγcont
  let σ := Path.segment (γ b) (γ a)
  have hαinj : Injective α :=
    injective_orbitArc γ hab hγcont hγinj
  have hσinj : Injective σ := by
    apply Path.segment_injective_of_ne
    intro hba
    have hab' :=
      hγinj ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hba.symm
    exact hab.ne hab'
  have hinter : range α ∩ range σ ⊆ {γ a, γ b} := by
    rintro z ⟨hzα, hzσ⟩
    rw [range_orbitArc γ hab hγcont] at hzα
    rw [Path.range_segment] at hzσ
    obtain ⟨t, ht, rfl⟩ := hzα
    have hzero :=
      transverseValue_segment_eq_zero hb ha hzσ
    rcases hconsecutive t ht hzero with rfl | rfl
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (mem_singleton _)
  have htwo :=
    JordanLoop.two_components_compl_trans α σ hαinj hσinj hinter
  have hrangeα : range α = γ '' Icc a b := by
    dsimp only [α]
    exact range_orbitArc γ hab hγcont
  have hrangeσ : range σ = [γ b -[ℝ] γ a] := by
    dsimp only [σ]
    exact Path.range_segment (γ b) (γ a)
  rw [hrangeα, hrangeσ] at htwo
  exact htwo

end

end Submission.OrbitArc
