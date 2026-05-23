import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Affine


/-!
# Minkowski–Carathéodory theorem in finite-dimensional real normed spaces

For a compact convex set `s` in a finite-dimensional real normed space `E`, every point
`x ∈ s` can be written as a convex combination of at most `Module.finrank ℝ E + 1`
extreme points of `s`.

## Outline

1. **Strict (no-closure) Krein–Milman in finite-dim** (`Minkowski.subset_convexHull_extremePoints`):
   `s ⊆ convexHull ℝ (s.extremePoints ℝ)`. Proved by strong induction on the *intrinsic*
   dimension of `s` (the rank of `(affineSpan ℝ s).direction`):
   * If `x` is itself an extreme point, take `t = {x}`.
   * Otherwise pick `a, b ∈ s` with `x ∈ openSegment ℝ a b`, extend to a maximal chord
     `[a', b'] ⊆ s`. Both `a'` and `b'` lie in `intrinsicFrontier ℝ s` because the chord
     leaves `s` past them. By Hahn–Banach (in `(affineSpan ℝ s).direction`) each lies on
     a proper exposed face whose intrinsic dimension is strictly smaller. Apply IH to
     each face and combine via the convex combination `x = (1-μ)·a' + μ·b'`.
2. **Carathéodory bound**: apply `Polynomial.Caratheodory.minCardFinsetOfMemConvexHull`
   (more precisely the affine-independent finset it produces) to upgrade from the convex
   hull to a finset of size `≤ finrank + 1`.
-/

namespace Submission


open Set Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Minkowski's theorem (finite-dimensional Krein–Milman without closure)

We prove `s ⊆ convexHull ℝ (s.extremePoints ℝ)` by strong induction on the intrinsic
dimension of `s`.
-/

namespace Minkowski

/-- Intrinsic dimension of `s` (the rank of `(affineSpan ℝ s).direction`). -/
private noncomputable def intrinsicDim (s : Set E) : ℕ :=
  Module.finrank ℝ ((affineSpan ℝ s).direction)

/-! #### Chord extension

Given `a ≠ b ∈ s`, the parameters `t : ℝ` for which `lineMap a b t ∈ s` form a closed
bounded convex (hence Icc) subset of `ℝ`.
-/

private lemma exists_chord_endpoints
    {s : Set E} (hs_compact : IsCompact s) (hs_convex : Convex ℝ s)
    {a b : E} (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) :
    ∃ α β : ℝ, α ≤ 0 ∧ 1 ≤ β ∧
      AffineMap.lineMap a b α ∈ s ∧
      AffineMap.lineMap a b β ∈ s ∧
      (∀ t < α, AffineMap.lineMap a b t ∉ s) ∧
      (∀ t > β, AffineMap.lineMap a b t ∉ s) := by
  set φ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a b with hφ
  set T : Set ℝ := φ ⁻¹' s with hT
  have hφ_cont : Continuous φ := AffineMap.lineMap_continuous
  have hT_closed : IsClosed T := hs_compact.isClosed.preimage hφ_cont
  have hT_convex : Convex ℝ T := hs_convex.affine_preimage φ
  have h0_T : (0 : ℝ) ∈ T := by
    show φ 0 ∈ s
    simpa [φ, AffineMap.lineMap_apply_module] using ha
  have h1_T : (1 : ℝ) ∈ T := by
    show φ 1 ∈ s
    simpa [φ, AffineMap.lineMap_apply_module] using hb
  -- Bound T: |t| ≤ (R + ‖a‖) / ‖b - a‖ for s ⊆ closedBall 0 R.
  have hT_bdd : Bornology.IsBounded T := by
    rcases hs_compact.isBounded.subset_closedBall (0 : E) with ⟨R, hR⟩
    have hba : (0 : ℝ) < ‖b - a‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr hab.symm
    refine Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := (R + ‖a‖) / ‖b - a‖)) ?_
    intro t ht
    have hphi : φ t ∈ Metric.closedBall (0 : E) R := hR ht
    rw [Metric.mem_closedBall, dist_zero_right] at hphi
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    have hexp : φ t = t • (b - a) + a := by
      simp [φ, AffineMap.lineMap_apply_module']
    have h_calc : ‖t • (b - a)‖ ≤ R + ‖a‖ := by
      have heq : t • (b - a) = φ t - a := by rw [hexp]; abel
      rw [heq]
      calc ‖φ t - a‖ ≤ ‖φ t‖ + ‖a‖ := norm_sub_le _ _
        _ ≤ R + ‖a‖ := by linarith
    rw [norm_smul, Real.norm_eq_abs] at h_calc
    exact (le_div_iff₀ hba).mpr h_calc
  -- Closed bounded in ℝ ⇒ compact.
  have hT_compact : IsCompact T :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hT_closed, hT_bdd⟩
  have hT_ne : T.Nonempty := ⟨0, h0_T⟩
  set α := sInf T with hα
  set β := sSup T with hβ
  have hα_T : α ∈ T := hT_compact.sInf_mem hT_ne
  have hβ_T : β ∈ T := hT_compact.sSup_mem hT_ne
  have h_α_le_0 : α ≤ 0 := csInf_le hT_bdd.bddBelow h0_T
  have h_1_le_β : 1 ≤ β := le_csSup hT_bdd.bddAbove h1_T
  refine ⟨α, β, h_α_le_0, h_1_le_β, hα_T, hβ_T, ?_, ?_⟩
  · intro t ht hmem
    exact absurd (csInf_le hT_bdd.bddBelow hmem) (not_le.mpr ht)
  · intro t ht hmem
    exact absurd (le_csSup hT_bdd.bddAbove hmem) (not_le.mpr ht)

/-! #### Face at a relative-frontier point

The key step: at a relative-frontier point of `s`, there is a proper extreme face of
`s` containing it, with strictly smaller intrinsic dimension. This is constructed via
Hahn-Banach in `(affineSpan ℝ s).direction`.
-/

/-- A chord endpoint (with the line going outside `s` past it) lies in `intrinsicFrontier s`. -/
private lemma lineMap_min_in_intrinsicFrontier
    {s : Set E} (hs_convex : Convex ℝ s) (hs_closed : IsClosed s)
    {a b : E} (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) {α : ℝ}
    (hα_in : AffineMap.lineMap a b α ∈ s)
    (hα_min : ∀ t < α, AffineMap.lineMap a b t ∉ s) :
    AffineMap.lineMap a b α ∈ intrinsicFrontier ℝ s := by
  -- intrinsicFrontier s = closure s \ intrinsicInterior s; with s closed, = s \ intInt.
  rw [← closure_diff_intrinsicInterior, hs_closed.closure_eq]
  refine ⟨hα_in, ?_⟩
  intro h_int
  rw [mem_intrinsicInterior] at h_int
  obtain ⟨y', hy'_int, hy'_eq⟩ := h_int
  -- Lift line to affineSpan ℝ s.
  have h_a_aff : a ∈ affineSpan ℝ s := subset_affineSpan ℝ s ha
  have h_b_aff : b ∈ affineSpan ℝ s := subset_affineSpan ℝ s hb
  have h_line_aff : ∀ t : ℝ, AffineMap.lineMap a b t ∈ affineSpan ℝ s :=
    fun t => AffineMap.lineMap_mem t h_a_aff h_b_aff
  let line_lift : ℝ → affineSpan ℝ s :=
    fun t => ⟨AffineMap.lineMap a b t, h_line_aff t⟩
  have h_line_α_eq : line_lift α = y' := by
    apply Subtype.ext; simpa [line_lift] using hy'_eq.symm
  have h_line_cont : Continuous line_lift := by
    rw [continuous_induced_rng]; exact AffineMap.lineMap_continuous
  -- y' has open nbhd U in affineSpan ℝ s with U ⊆ preimage of s.
  rw [mem_interior] at hy'_int
  obtain ⟨U, hU_sub, hU_open, hU_mem⟩ := hy'_int
  -- line_lift⁻¹' U is open in ℝ and contains α.
  have h_pre_open : IsOpen (line_lift ⁻¹' U) := hU_open.preimage h_line_cont
  have hα_pre : α ∈ line_lift ⁻¹' U := by
    show line_lift α ∈ U; rw [h_line_α_eq]; exact hU_mem
  -- Get ε > 0 with ball α ε ⊆ line_lift⁻¹' U.
  obtain ⟨ε, hε_pos, h_ε_sub⟩ := Metric.isOpen_iff.mp h_pre_open α hα_pre
  -- Pick t = α - ε/2. Then t < α, line_lift t ∈ U, hence lineMap t ∈ s. Contradiction.
  have hδ_pos : (0 : ℝ) < ε / 2 := by linarith
  have h_t_lt : α - ε / 2 < α := by linarith
  have h_t_in_ball : α - ε / 2 ∈ Metric.ball α ε := by
    rw [Metric.mem_ball]; rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith
  have h_t_in_pre : α - ε / 2 ∈ line_lift ⁻¹' U := h_ε_sub h_t_in_ball
  have h_lineMap_in_s : AffineMap.lineMap a b (α - ε / 2) ∈ s := by
    have h_in_U : line_lift (α - ε / 2) ∈ U := h_t_in_pre
    have h_in_s : (line_lift (α - ε / 2) : E) ∈ s := hU_sub h_in_U
    exact h_in_s
  exact hα_min _ h_t_lt h_lineMap_in_s

/-- Symmetric version for the `β` endpoint, via `lineMap a b t = lineMap b a (1 - t)`. -/
private lemma lineMap_max_in_intrinsicFrontier
    {s : Set E} (hs_convex : Convex ℝ s) (hs_closed : IsClosed s)
    {a b : E} (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) {β : ℝ}
    (hβ_in : AffineMap.lineMap a b β ∈ s)
    (hβ_max : ∀ t > β, AffineMap.lineMap a b t ∉ s) :
    AffineMap.lineMap a b β ∈ intrinsicFrontier ℝ s := by
  -- Reduce to the `min` case using `lineMap a b β = lineMap b a (1 - β)`.
  have h_swap : ∀ t : ℝ, AffineMap.lineMap a b t = AffineMap.lineMap b a (1 - t) := by
    intro t
    simp only [AffineMap.lineMap_apply_module]
    have : (1 - (1 - t)) = t := by ring
    rw [this]; exact add_comm _ _
  rw [h_swap β]
  apply lineMap_min_in_intrinsicFrontier hs_convex hs_closed hab.symm hb ha
  · rw [← h_swap β]; exact hβ_in
  · intro t ht
    have h_eq : AffineMap.lineMap b a t = AffineMap.lineMap a b (1 - t) := by
      have h := h_swap (1 - t)
      rw [show 1 - (1 - t) = t from by ring] at h
      exact h.symm
    rw [h_eq]
    exact hβ_max _ (by linarith)

/-- A continuous linear functional on `E` separating a relative-frontier point `y`
from `intrinsicInterior s`. The functional achieves its max on `s` at `y`, and is
non-constant on `s`. Constructed via Hahn-Banach in `(affineSpan ℝ s).direction`. -/
private lemma exists_separating_functional_at_intrinsicFrontier
    {s : Set E} (hs_compact : IsCompact s) (hs_convex : Convex ℝ s)
    {y : E} (hy_in : y ∈ s) (hy_frontier : y ∈ intrinsicFrontier ℝ s) :
    ∃ l : E →L[ℝ] ℝ, (∀ z ∈ s, l z ≤ l y) ∧ (∃ z ∈ s, l z < l y) := by
  -- y ∉ intrinsicInterior s.
  have hy_not_int : y ∉ intrinsicInterior ℝ s := by
    intro h_int
    have : y ∈ intrinsicClosure ℝ s \ intrinsicInterior ℝ s := by
      rw [intrinsicClosure_diff_intrinsicInterior]; exact hy_frontier
    exact this.2 h_int
  have h_int_ne : (intrinsicInterior ℝ s).Nonempty :=
    Set.Nonempty.intrinsicInterior hs_convex ⟨y, hy_in⟩
  -- Setup V and τ.
  let V : Submodule ℝ E := (affineSpan ℝ s).direction
  let τ : V → E := fun v => (v : E) + y
  have hτ_cont : Continuous τ :=
    continuous_subtype_val.add continuous_const
  let s_V : Set V := τ ⁻¹' s
  have h0_in_s_V : (0 : V) ∈ s_V := by
    show ((0 : V) : E) + y ∈ s; simpa using hy_in
  have h_s_V_closed : IsClosed s_V := hs_compact.isClosed.preimage hτ_cont
  have h_s_V_convex : Convex ℝ s_V := by
    intro u hu v hv α β hα hβ hαβ
    show ((α • u + β • v : V) : E) + y ∈ s
    have h_eq : ((α • u + β • v : V) : E) + y = α • ((u : E) + y) + β • ((v : E) + y) := by
      push_cast
      have h_one : α • y + β • y = y := by rw [← add_smul, hαβ, one_smul]
      calc α • (u : E) + β • (v : E) + y
          = α • (u : E) + β • (v : E) + (α • y + β • y) := by rw [h_one]
        _ = α • ((u : E) + y) + β • ((v : E) + y) := by
            rw [smul_add, smul_add]; abel
    rw [h_eq]
    exact hs_convex hu hv hα hβ hαβ
  -- For z ∈ s, z - y ∈ V.
  have h_z_minus_y_in_V : ∀ z ∈ s, z - y ∈ V := by
    intro z hz
    have hz_aff : z ∈ affineSpan ℝ s := subset_affineSpan ℝ s hz
    have hy_aff : y ∈ affineSpan ℝ s := subset_affineSpan ℝ s hy_in
    have := AffineSubspace.vsub_mem_direction hz_aff hy_aff
    rwa [vsub_eq_sub] at this
  -- KEY: Submodule.span ℝ s_V = ⊤ (in V).
  -- Proof: V.subtype '' s_V = {z - y | z ∈ s} ⊆ V; its span equals vectorSpan s = V.
  -- By Submodule.map injectivity of subtype, span s_V = ⊤.
  have h_span_top : Submodule.span ℝ s_V = ⊤ := by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    apply le_antisymm
    · -- Submodule.span ℝ (V.subtype '' s_V) ≤ V
      rw [Submodule.span_le]
      rintro w ⟨v, _, rfl⟩
      exact v.2
    · -- V ≤ Submodule.span ℝ (V.subtype '' s_V)
      intro v hv_in_V
      -- v ∈ V = vectorSpan ℝ s = Submodule.span ℝ (s -ᵥ s)
      have h_vsp : v ∈ vectorSpan ℝ s := by rw [← direction_affineSpan]; exact hv_in_V
      rw [vectorSpan_def] at h_vsp
      apply (Submodule.span_le.mpr ?_) h_vsp
      rintro w ⟨a, ha, b, hb, rfl⟩
      have h_ay_in_V : a - y ∈ V := h_z_minus_y_in_V a ha
      have h_by_in_V : b - y ∈ V := h_z_minus_y_in_V b hb
      let a_V : V := ⟨a - y, h_ay_in_V⟩
      let b_V : V := ⟨b - y, h_by_in_V⟩
      have h_a_V_in_s_V : a_V ∈ s_V := by
        show ((a_V : E) : E) + y ∈ s
        show (a - y) + y ∈ s
        simpa using ha
      have h_b_V_in_s_V : b_V ∈ s_V := by
        show ((b_V : E) : E) + y ∈ s
        show (b - y) + y ∈ s
        simpa using hb
      have h_a_minus_y_mem : a - y ∈ V.subtype '' s_V := ⟨a_V, h_a_V_in_s_V, rfl⟩
      have h_b_minus_y_mem : b - y ∈ V.subtype '' s_V := ⟨b_V, h_b_V_in_s_V, rfl⟩
      show a -ᵥ b ∈ Submodule.span ℝ (V.subtype '' s_V)
      rw [vsub_eq_sub]
      have h_eq : a - b = (a - y) - (b - y) := by abel
      rw [h_eq]
      exact Submodule.sub_mem _ (Submodule.subset_span h_a_minus_y_mem)
        (Submodule.subset_span h_b_minus_y_mem)
  -- From Submodule.span ℝ s_V = ⊤, derive affineSpan ℝ s_V = ⊤.
  have h_aspan_top : affineSpan ℝ s_V = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h_v_in_span : v ∈ Submodule.span ℝ s_V := by
      rw [h_span_top]; exact Submodule.mem_top
    have h_ins : insert (0 : V) s_V = s_V := Set.insert_eq_self.mpr h0_in_s_V
    have h_set_eq : (affineSpan ℝ s_V : Set V) = (Submodule.span ℝ s_V : Set V) := by
      conv_lhs => rw [← h_ins]
      exact affineSpan_insert_zero s_V
    rw [← SetLike.mem_coe, h_set_eq, SetLike.mem_coe]
    exact h_v_in_span
  -- interior s_V is nonempty (full affine span + finite dim ⟹ nonempty interior).
  have h_int_s_V_ne : (interior s_V).Nonempty :=
    h_s_V_convex.interior_nonempty_iff_affineSpan_eq_top.mpr h_aspan_top
  -- 0 ∉ interior s_V (by transferring y ∉ intrinsicInterior s).
  have h0_not_int : (0 : V) ∉ interior s_V := by
    intro h0_int
    apply hy_not_int
    rw [mem_intrinsicInterior]
    have hy_aff : y ∈ affineSpan ℝ s := subset_affineSpan ℝ s hy_in
    refine ⟨⟨y, hy_aff⟩, ?_, rfl⟩
    rw [mem_interior]
    rw [mem_interior] at h0_int
    obtain ⟨U_V, hU_V_sub, hU_V_open, h0_in_U_V⟩ := h0_int
    rw [Metric.isOpen_iff] at hU_V_open
    obtain ⟨ε, hε_pos, h_ball_sub⟩ := hU_V_open 0 h0_in_U_V
    refine ⟨Metric.ball (⟨y, hy_aff⟩ : ↥(affineSpan ℝ s)) ε, ?_, Metric.isOpen_ball, ?_⟩
    · intro q' hq'
      show (q' : E) ∈ s
      rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] at hq'
      have hq'_E : (q' : E) ∈ affineSpan ℝ s := q'.2
      have hv_in_V : (q' : E) - y ∈ V := by
        have := AffineSubspace.vsub_mem_direction hq'_E hy_aff
        rwa [vsub_eq_sub] at this
      let v_V : V := ⟨(q' : E) - y, hv_in_V⟩
      have h_v_in_ball : v_V ∈ Metric.ball (0 : V) ε := by
        rw [Metric.mem_ball, dist_zero_right]
        show ‖((q' : E) - y : E)‖ < ε
        exact hq'
      have h_v_in_s_V : v_V ∈ s_V := hU_V_sub (h_ball_sub h_v_in_ball)
      have h_τvV_in_s : ((v_V : E) : E) + y ∈ s := h_v_in_s_V
      have h_eq : ((v_V : E) : E) + y = (q' : E) := by
        show ((q' : E) - y) + y = (q' : E); abel
      rw [← h_eq]; exact h_τvV_in_s
    · rw [Metric.mem_ball, dist_self]; exact hε_pos
  -- Hahn-Banach in V: separate {0} from interior s_V (open convex).
  obtain ⟨l_V, h_l_V_lt⟩ : ∃ l_V : V →L[ℝ] ℝ, ∀ z ∈ interior s_V, l_V z < l_V 0 :=
    geometric_hahn_banach_open_point h_s_V_convex.interior isOpen_interior h0_not_int
  -- Density: closure(interior s_V) = s_V.
  have h_closure_eq : closure (interior s_V) = s_V := by
    rw [h_s_V_convex.closure_interior_eq_closure_of_nonempty_interior h_int_s_V_ne]
    exact h_s_V_closed.closure_eq
  -- l_V ≤ l_V 0 on s_V.
  have h_l_V_le : ∀ z ∈ s_V, l_V z ≤ l_V 0 := by
    intro z hz
    rw [← h_closure_eq] at hz
    have h_le_set : closure (interior s_V) ⊆ {w | l_V w ≤ l_V 0} :=
      closure_minimal (fun w hw => (h_l_V_lt w hw).le)
        (isClosed_le l_V.continuous continuous_const)
    exact h_le_set hz
  -- Extend l_V from V to E via Submodule.exists_isCompl.
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ E, IsCompl V W := V.exists_isCompl
  let proj_V : E →ₗ[ℝ] V := V.linearProjOfIsCompl W hW
  let l_E_lin : E →ₗ[ℝ] ℝ := l_V.toLinearMap.comp proj_V
  let l_E : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap l_E_lin
  -- For v ∈ V, proj_V (v : E) = v, hence l_E (v : E) = l_V v.
  have h_proj_id : ∀ v : V, proj_V (v : E) = v :=
    Submodule.linearProjOfIsCompl_apply_left hW
  have h_l_E_apply : ∀ v : V, l_E (v : E) = l_V v := by
    intro v
    show l_E_lin _ = _
    show l_V (proj_V (v : E)) = l_V v
    rw [h_proj_id]
  -- Goal 1: ∀ z ∈ s, l_E z ≤ l_E y.
  refine ⟨l_E, ?_, ?_⟩
  · intro z hz
    have hzy_V : z - y ∈ V := h_z_minus_y_in_V z hz
    let zV : V := ⟨z - y, hzy_V⟩
    have h_zV_in_s_V : zV ∈ s_V := by
      show ((zV : E) : E) + y ∈ s
      show (z - y) + y ∈ s
      rw [sub_add_cancel]; exact hz
    have h_l_V_zV_le : l_V zV ≤ l_V 0 := h_l_V_le zV h_zV_in_s_V
    have h_l_V_zero : l_V (0 : V) = 0 := l_V.map_zero
    rw [h_l_V_zero] at h_l_V_zV_le
    -- l_E z = l_E (z - y) + l_E y; l_E (z - y) = l_V zV ≤ 0; so l_E z ≤ l_E y.
    have h_l_E_sub : l_E (z - y) = l_V zV := by
      have : (zV : E) = z - y := rfl
      rw [← this]; exact h_l_E_apply zV
    have h_l_E_z_split : l_E z = l_E (z - y) + l_E y := by
      conv_lhs => rw [show z = (z - y) + y from by abel]
      exact l_E.map_add _ _
    rw [h_l_E_z_split, h_l_E_sub]
    linarith
  · -- Goal 2: ∃ z ∈ s, l_E z < l_E y.
    obtain ⟨z₀_V, hz₀_int⟩ := h_int_s_V_ne
    have hz₀_in_s_V : z₀_V ∈ s_V := interior_subset hz₀_int
    refine ⟨((z₀_V : E) + y), hz₀_in_s_V, ?_⟩
    have h_l_V_lt_zero : l_V z₀_V < l_V 0 := h_l_V_lt z₀_V hz₀_int
    have h_l_V_zero : l_V (0 : V) = 0 := l_V.map_zero
    rw [h_l_V_zero] at h_l_V_lt_zero
    have h_l_E_split : l_E ((z₀_V : E) + y) = l_E (z₀_V : E) + l_E y := l_E.map_add _ _
    have h_l_E_apply' : l_E (z₀_V : E) = l_V z₀_V := h_l_E_apply z₀_V
    rw [h_l_E_split, h_l_E_apply']
    linarith

/-- For a relative-frontier point of a compact convex set with intrinsic dim `≤ n+1`,
there is a proper extreme face containing it with intrinsic dim `≤ n`. The face is the
arg-max of a non-constant continuous linear functional separating `y` from
`intrinsicInterior s`. -/
private lemma exists_proper_extreme_face_at_intrinsicFrontier
    {s : Set E} (hs_compact : IsCompact s) (hs_convex : Convex ℝ s)
    (n : ℕ) (h_dim : intrinsicDim s ≤ n + 1)
    {y : E} (hy_in : y ∈ s) (hy_frontier : y ∈ intrinsicFrontier ℝ s) :
    ∃ F : Set E, y ∈ F ∧ IsExtreme ℝ s F ∧ IsCompact F ∧ Convex ℝ F ∧
      intrinsicDim F ≤ n := by
  obtain ⟨l, hl_max, z₀, hz₀_in, hl_lt⟩ :=
    exists_separating_functional_at_intrinsicFrontier hs_compact hs_convex hy_in hy_frontier
  -- Define the exposed face F = arg max of l on s.
  set F : Set E := {z ∈ s | ∀ w ∈ s, l w ≤ l z} with hF_def
  refine ⟨F, ⟨hy_in, hl_max⟩, ?_, ?_, ?_, ?_⟩
  · -- F is exposed (hence extreme).
    have h_exposed : IsExposed ℝ s F := fun _ => ⟨l, rfl⟩
    exact h_exposed.isExtreme
  · -- F is compact (closed subset of compact s).
    apply hs_compact.of_isClosed_subset
    · -- F is closed: intersection of s (closed) with closed set "l achieves its max"
      have h_F_eq : F = s ∩ {z | ∀ w ∈ s, l w ≤ l z} := by
        ext z; simp [F]
      rw [h_F_eq]
      apply hs_compact.isClosed.inter
      have h_eq2 : {z : E | ∀ w ∈ s, l w ≤ l z} = ⋂ w ∈ s, {z | l w ≤ l z} := by
        ext z; simp
      rw [h_eq2]
      refine isClosed_biInter (fun w _ => ?_)
      exact isClosed_le continuous_const l.continuous
    · exact fun _ hz => hz.1
  · -- F is convex: intersection of s with a hyperplane (l z = l y) is convex.
    have h_F_eq : F = s ∩ {z | l z = l y} := by
      ext z
      simp only [F, Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨hz, hmax⟩
        refine ⟨hz, le_antisymm (hl_max z hz) (hmax y hy_in)⟩
      · rintro ⟨hz, heq⟩
        refine ⟨hz, fun w hw => ?_⟩
        rw [heq]; exact hl_max w hw
    rw [h_F_eq]
    apply hs_convex.inter
    -- Hyperplane {z | l z = l y} is convex.
    intro u hu v hv α β hα hβ hαβ
    simp only [Set.mem_setOf_eq] at hu hv ⊢
    rw [map_add, l.map_smul, l.map_smul, hu, hv]
    have : (α : ℝ) • l y + β • l y = (α + β) • l y := by
      rw [← add_smul]
    rw [this, hαβ, one_smul]
  · -- intrinsicDim F ≤ n.
    show Module.finrank ℝ ((affineSpan ℝ F).direction) ≤ n
    set V_s : Submodule ℝ E := (affineSpan ℝ s).direction with hV_s_def
    set K_l : Submodule ℝ E := LinearMap.ker (l : E →ₗ[ℝ] ℝ) with hK_l_def
    set V_inter : Submodule ℝ E := V_s ⊓ K_l with hV_inter_def
    -- Step 1: (affineSpan F).direction ≤ V_inter.
    have h_F_in_inter : (affineSpan ℝ F).direction ≤ V_inter := by
      refine le_inf ?_ ?_
      · -- F ⊆ s ⟹ affineSpan F ≤ affineSpan s ⟹ direction ≤ direction
        apply AffineSubspace.direction_le
        exact affineSpan_mono ℝ (fun _ hz => hz.1)
      · rw [direction_affineSpan]
        apply Submodule.span_le.mpr
        rintro v ⟨q, hq, p, hp, rfl⟩
        have hq_eq : l q = l y := le_antisymm (hl_max q hq.1) (hq.2 y hy_in)
        have hp_eq : l p = l y := le_antisymm (hl_max p hp.1) (hp.2 y hy_in)
        show q -ᵥ p ∈ K_l
        rw [hK_l_def, LinearMap.mem_ker]
        change l (q -ᵥ p) = 0
        rw [vsub_eq_sub, l.map_sub, hq_eq, hp_eq, sub_self]
    -- Step 2: z₀ - y ∈ V_s \ K_l.
    have hzy_in_V : z₀ - y ∈ V_s := by
      have h_zaff : z₀ ∈ affineSpan ℝ s := subset_affineSpan ℝ s hz₀_in
      have h_yaff : y ∈ affineSpan ℝ s := subset_affineSpan ℝ s hy_in
      have := AffineSubspace.vsub_mem_direction h_zaff h_yaff
      rwa [vsub_eq_sub] at this
    have hzy_not_ker : z₀ - y ∉ K_l := by
      intro hker
      rw [LinearMap.mem_ker] at hker
      have hL : l (z₀ - y) = 0 := hker
      rw [l.map_sub] at hL
      linarith
    -- Step 3: V_inter < V_s strictly.
    have h_strict_lt : V_inter < V_s := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro h_eq
      have hle : V_s ≤ K_l := by rw [← h_eq]; exact inf_le_right
      exact hzy_not_ker (hle hzy_in_V)
    -- Step 4: finrank lt.
    have h_finrank_lt : Module.finrank ℝ V_inter < Module.finrank ℝ V_s :=
      Submodule.finrank_lt_finrank_of_lt h_strict_lt
    have h_V_s_le : Module.finrank ℝ V_s ≤ n + 1 := h_dim
    have h_F_le_inter :
        Module.finrank ℝ ((affineSpan ℝ F).direction) ≤ Module.finrank ℝ V_inter :=
      Submodule.finrank_mono h_F_in_inter
    omega

/-- The induction-friendly form. Strong induction on the intrinsic dimension. -/
private theorem subset_convexHull_extremePoints_of_intrinsicDim_le (k : ℕ)
    {s : Set E} (h_dim : intrinsicDim s ≤ k)
    (hs_compact : IsCompact s) (hs_convex : Convex ℝ s) :
    s ⊆ convexHull ℝ (s.extremePoints ℝ) := by
  induction k generalizing s with
  | zero =>
    -- intrinsicDim s = 0 ⟹ all points of s are equal.
    intro x hx
    have h0 : intrinsicDim s = 0 := Nat.le_zero.mp h_dim
    have hdir_bot : ((affineSpan ℝ s).direction) = ⊥ :=
      Submodule.finrank_eq_zero.mp h0
    have hall : ∀ p ∈ s, ∀ q ∈ s, p = q := by
      intro p hp q hq
      have hp_aff : p ∈ affineSpan ℝ s := subset_affineSpan ℝ s hp
      have hq_aff : q ∈ affineSpan ℝ s := subset_affineSpan ℝ s hq
      have hvsub : q -ᵥ p ∈ (affineSpan ℝ s).direction :=
        AffineSubspace.vsub_mem_direction hq_aff hp_aff
      rw [hdir_bot, Submodule.mem_bot] at hvsub
      exact (sub_eq_zero.mp hvsub).symm
    have hx_extr : x ∈ s.extremePoints ℝ := by
      rw [mem_extremePoints]
      refine ⟨hx, ?_⟩
      intro x₁ h₁ x₂ h₂ _
      exact ⟨hall x₁ h₁ x hx, hall x₂ h₂ x hx⟩
    exact subset_convexHull _ _ hx_extr
  | succ n IH =>
    intro x hx
    -- Two cases on `x` being extreme.
    by_cases hx_extr : x ∈ s.extremePoints ℝ
    · exact subset_convexHull _ _ hx_extr
    · -- x is non-extreme: there exist a, b ∈ s with x ∈ openSegment a b, a ≠ b.
      have h_openSeg : ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ x ∈ openSegment ℝ a b := by
        by_contra h_neg
        push_neg at h_neg
        apply hx_extr
        rw [mem_extremePoints]
        refine ⟨hx, ?_⟩
        intro x₁ h₁ x₂ h₂ hopen
        by_cases hab : x₁ = x₂
        · subst hab
          rw [openSegment_same, mem_singleton_iff] at hopen
          exact ⟨hopen.symm, hopen.symm⟩
        · exact absurd hopen (h_neg x₁ h₁ x₂ h₂ hab)
      obtain ⟨a, ha, b, hb, hab, hx_open⟩ := h_openSeg
      -- WLOG intrinsicDim s = n+1 (else IH applies directly).
      by_cases hdim_lt : intrinsicDim s ≤ n
      · exact IH hdim_lt hs_compact hs_convex hx
      have hdim_eq : intrinsicDim s = n + 1 := by
        push_neg at hdim_lt; omega
      -- Extend to maximal chord [a', b'] ⊆ s along the line.
      obtain ⟨α, β, hα_le, hβ_ge, hα_in, hβ_in, hα_min, hβ_max⟩ :=
        exists_chord_endpoints hs_compact hs_convex hab ha hb
      set a' := AffineMap.lineMap a b α with ha'_def
      set b' := AffineMap.lineMap a b β with hb'_def
      -- Express x as convex combination (1 - μ)·a' + μ·b' with μ ∈ (0, 1).
      obtain ⟨p, q, hp_pos, hq_pos, hpq_sum, hx_eq⟩ := hx_open
      have hx_lineMap : x = AffineMap.lineMap a b q := by
        rw [AffineMap.lineMap_apply_module]
        have hp_eq : p = 1 - q := by linarith
        rw [← hx_eq, hp_eq]
      have hq_lt_one : q < 1 := by linarith
      have hαβ_lt : α < β := by linarith
      have hβα_pos : 0 < β - α := by linarith
      set μ := (q - α) / (β - α) with hμ_def
      have hμ_pos : 0 < μ := div_pos (by linarith) hβα_pos
      have hμ_lt_one : μ < 1 := (div_lt_one hβα_pos).mpr (by linarith)
      have hμ_nn : 0 ≤ μ := hμ_pos.le
      have hμ_le_one : μ ≤ 1 := hμ_lt_one.le
      have hx_combo : x = (1 - μ) • a' + μ • b' := by
        rw [hx_lineMap]
        simp only [a', b', AffineMap.lineMap_apply_module]
        have hμ_eq : (1 - μ) * α + μ * β = q := by
          rw [hμ_def]; field_simp; ring
        have h_rhs : (1 - q) • a + q • b
            = (1 - ((1 - μ) * α + μ * β)) • a + ((1 - μ) * α + μ * β) • b := by
          rw [hμ_eq]
        rw [h_rhs]
        module
      -- Each chord endpoint is on the relative frontier of `s`,
      -- hence lies in a proper extreme face with intrinsic dim ≤ n,
      -- so IH applies.
      have ha'_frontier : a' ∈ intrinsicFrontier ℝ s :=
        lineMap_min_in_intrinsicFrontier hs_convex hs_compact.isClosed hab ha hb
          hα_in hα_min
      have hb'_frontier : b' ∈ intrinsicFrontier ℝ s :=
        lineMap_max_in_intrinsicFrontier hs_convex hs_compact.isClosed hab ha hb
          hβ_in hβ_max
      obtain ⟨F_a, hF_a_mem, hF_a_extreme, hF_a_compact, hF_a_convex, hF_a_dim⟩ :=
        exists_proper_extreme_face_at_intrinsicFrontier hs_compact hs_convex n
          (hdim_eq ▸ le_refl _) hα_in ha'_frontier
      obtain ⟨F_b, hF_b_mem, hF_b_extreme, hF_b_compact, hF_b_convex, hF_b_dim⟩ :=
        exists_proper_extreme_face_at_intrinsicFrontier hs_compact hs_convex n
          (hdim_eq ▸ le_refl _) hβ_in hb'_frontier
      have ha'_in_F_hull : a' ∈ convexHull ℝ (F_a.extremePoints ℝ) :=
        IH hF_a_dim hF_a_compact hF_a_convex hF_a_mem
      have hb'_in_F_hull : b' ∈ convexHull ℝ (F_b.extremePoints ℝ) :=
        IH hF_b_dim hF_b_compact hF_b_convex hF_b_mem
      have ha'_in_hull : a' ∈ convexHull ℝ (s.extremePoints ℝ) :=
        convexHull_mono hF_a_extreme.extremePoints_subset_extremePoints ha'_in_F_hull
      have hb'_in_hull : b' ∈ convexHull ℝ (s.extremePoints ℝ) :=
        convexHull_mono hF_b_extreme.extremePoints_subset_extremePoints hb'_in_F_hull
      -- Combine via x = (1 - μ) • a' + μ • b' ∈ convexHull {a', b'} ⊆ ...
      have h_pair_sub : ({a', b'} : Set E) ⊆ convexHull ℝ (s.extremePoints ℝ) := by
        intro y hy
        rcases hy with rfl | rfl
        · exact ha'_in_hull
        · exact hb'_in_hull
      have hx_in_pair : x ∈ convexHull ℝ ({a', b'} : Set E) := by
        rw [show ({a', b'} : Set E) = {a', b'} from rfl, hx_combo]
        exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ (by simp))
          (subset_convexHull ℝ _ (by simp)) (by linarith) hμ_nn (by linarith)
      exact (convexHull_min h_pair_sub (convex_convexHull _ _)) hx_in_pair

/-- **Minkowski's theorem.** -/
theorem subset_convexHull_extremePoints {s : Set E}
    (hs_compact : IsCompact s) (hs_convex : Convex ℝ s) :
    s ⊆ convexHull ℝ (s.extremePoints ℝ) :=
  subset_convexHull_extremePoints_of_intrinsicDim_le _ le_rfl hs_compact hs_convex

end Minkowski

/-! ### Section 4: Main theorem -/

/-- **Minkowski–Carathéodory theorem.** In a finite-dimensional real normed space, every
point of a compact convex set is a convex combination of at most `finrank E + 1` extreme
points of the set. -/

theorem mem_convexHull_finset_extremePoints_of_mem_compact_convex
    {s : Set E} {x : E}
    (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (hx : x ∈ s) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ s.extremePoints ℝ ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  -- Step 1: Minkowski → x ∈ convexHull (extremePoints s).
  have h_minkowski : x ∈ convexHull ℝ (s.extremePoints ℝ) :=
    Minkowski.subset_convexHull_extremePoints hscomp hsconv hx
  -- Step 2: Apply Caratheodory to get an affinely independent finset.
  set t := Caratheodory.minCardFinsetOfMemConvexHull h_minkowski with ht_def
  refine ⟨t, ?_, ?_, ?_⟩
  · exact Caratheodory.minCardFinsetOfMemConvexHull_subseteq h_minkowski
  · -- Affine independence ⟹ card ≤ finrank + 1.
    have h_ne : t.Nonempty :=
      Caratheodory.minCardFinsetOfMemConvexHull_nonempty h_minkowski
    haveI : Nonempty t := h_ne.coe_sort
    have h_aff_ind : AffineIndependent ℝ ((↑) : t → E) :=
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull h_minkowski
    have h_finrank :
        Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) + 1
          = Fintype.card t :=
      h_aff_ind.finrank_vectorSpan_add_one
    have h_card_eq : Fintype.card t = t.card := Fintype.card_coe t
    have h_le : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E)))
        ≤ Module.finrank ℝ E :=
      Submodule.finrank_le _
    omega
  · exact Caratheodory.mem_minCardFinsetOfMemConvexHull h_minkowski

end Submission

