import Mathlib

namespace Submission

namespace LeanEval.Geometry.HippocratesLunes

/-!
# Hippocrates' theorem on lunes

`hippocrates_lunes`: for a right triangle, the sum of the areas of the two
Hippocrates lunes equals the area of the triangle. Trusted helpers (`det2`,
`closedHalfDisk`, `hypotenuseSemidisk`, `horizontalLune`, `verticalLune`,
`rightTriangle`, …) are non-holes; the Euclidean squared distance is used
explicitly to avoid the `ℝ × ℝ` sup metric turning disks into squares. Mathlib
has no lune/classical-area result of this kind.
Category-(b) candidate from §166 of the Knill survey.
-/

open MeasureTheory

/-- The coordinate plane. -/
abbrev Plane := ℝ × ℝ

/-- Planar determinant (signed area form). -/
def det2 (u v : Plane) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Midpoint of two points. -/
noncomputable def midpoint (p q : Plane) : Plane := ((p.1 + q.1) / 2, (p.2 + q.2) / 2)

/-- Displacement vector. -/
def vec (p q : Plane) : Plane := (q.1 - p.1, q.2 - p.2)

/-- Squared Euclidean distance (not the product sup metric). -/
def euclideanDistSq (p q : Plane) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Closed half-disk with diameter `p q` on the side selected by `side`. -/
def closedHalfDisk (p q : Plane) (side : ℝ → Prop) : Set Plane :=
  {x | euclideanDistSq x (midpoint p q) ≤ euclideanDistSq p q / 4 ∧
    side (det2 (vec p q) (vec p x))}

/-- The right-angle vertex. -/
def A : Plane := (0, 0)
/-- The leg endpoint on the x-axis. -/
def B (a : ℝ) : Plane := (a, 0)
/-- The leg endpoint on the y-axis. -/
def C (b : ℝ) : Plane := (0, b)

/-- Semicircle on the hypotenuse, on the side of the right-angle vertex. -/
def hypotenuseSemidisk (a b : ℝ) : Set Plane :=
  closedHalfDisk (B a) (C b) (fun t => 0 ≤ t)

/-- The Hippocrates lune on the horizontal leg. -/
def horizontalLune (a b : ℝ) : Set Plane :=
  closedHalfDisk A (B a) (fun t => t ≤ 0) \ hypotenuseSemidisk a b

/-- The Hippocrates lune on the vertical leg. -/
def verticalLune (a b : ℝ) : Set Plane :=
  closedHalfDisk A (C b) (fun t => 0 ≤ t) \ hypotenuseSemidisk a b

/-- The right triangle. -/
def rightTriangle (a b : ℝ) : Set Plane :=
  convexHull ℝ ({A, B a, C b} : Set Plane)



end LeanEval.Geometry.HippocratesLunes

open LeanEval.Geometry.HippocratesLunes
open MeasureTheory
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

open scoped ENNReal
open Set

noncomputable section

private lemma H_mem (a : ℝ) (ha : 0 < a) (z : Plane) :
    z ∈ closedHalfDisk A (B a) (fun t => t ≤ 0) ↔
      z.1^2 + z.2^2 ≤ a*z.1 ∧ z.2 ≤ 0 := by
  rcases z with ⟨x,y⟩
  dsimp [closedHalfDisk, euclideanDistSq, LeanEval.Geometry.HippocratesLunes.midpoint, A, B, vec, det2]
  constructor
  · intro h
    constructor <;> nlinarith
  · intro h
    constructor <;> nlinarith

private lemma V_mem (b : ℝ) (hb : 0 < b) (z : Plane) :
    z ∈ closedHalfDisk A (C b) (fun t => 0 ≤ t) ↔
      z.1^2 + z.2^2 ≤ b*z.2 ∧ z.1 ≤ 0 := by
  rcases z with ⟨x,y⟩
  dsimp [closedHalfDisk, euclideanDistSq, LeanEval.Geometry.HippocratesLunes.midpoint, A, C, vec, det2]
  constructor
  · intro h; constructor <;> nlinarith
  · intro h; constructor <;> nlinarith

private lemma W_mem (a b : ℝ) (z : Plane) :
    z ∈ hypotenuseSemidisk a b ↔
       z.1^2 + z.2^2 ≤ a*z.1 + b*z.2 ∧ b*z.1 + a*z.2 ≤ a*b := by
  rcases z with ⟨x,y⟩
  dsimp [hypotenuseSemidisk, closedHalfDisk, euclideanDistSq, LeanEval.Geometry.HippocratesLunes.midpoint,
    A, B, C, vec, det2]
  constructor
  · intro h; constructor <;> nlinarith
  · intro h; constructor <;> nlinarith


private lemma T_mem (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : Plane) :
    z ∈ rightTriangle a b ↔
      0 ≤ z.1 ∧ 0 ≤ z.2 ∧ b*z.1 + a*z.2 ≤ a*b := by
  let S : Set Plane := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ b*p.1 + a*p.2 ≤ a*b}
  have hconv : Convex ℝ S := by
    intro x hx y hy u v hu hv huv
    change 0 ≤ _ ∧ 0 ≤ _ ∧ _ ≤ _ at hx hy ⊢
    constructor
    · dsimp
      nlinarith [hx.1, hy.1]
    constructor
    · dsimp
      nlinarith [hx.2.1, hy.2.1]
    · dsimp
      calc
        b * (u*x.1 + v*y.1) + a*(u*x.2 + v*y.2) =
            u*(b*x.1 + a*x.2) + v*(b*y.1 + a*y.2) := by ring
        _ ≤ u*(a*b) + v*(a*b) :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2.2 hu)
            (mul_le_mul_of_nonneg_left hy.2.2 hv)
        _ = a*b := by rw [← add_mul, huv, one_mul]
  have hsub : ({A, B a, C b} : Set Plane) ⊆ S := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;>
      dsimp [S, A, B, C] <;> constructor
    · norm_num
    · constructor
      · norm_num
      · nlinarith
    · nlinarith
    · constructor
      · norm_num
      · nlinarith
    · norm_num
    · constructor
      · exact le_of_lt hb
      · nlinarith
  constructor
  · intro hz
    change z ∈ convexHull ℝ ({A, B a, C b}:Set Plane) at hz
    change z ∈ S
    exact (convexHull_min hsub hconv) hz
  · intro hz
    change z ∈ convexHull ℝ ({A, B a, C b}:Set Plane)
    change 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ b*z.1 + a*z.2 ≤ a*b at hz
    -- use weights at 0,1,2
    classical
    let w : Fin 3 → ℝ := ![ (1 - z.1/a - z.2/b), z.1/a, z.2/b ]
    let p : Fin 3 → Plane := ![ A, B a, C b ]
    apply mem_convexHull_of_exists_fintype w p
    · intro i
      fin_cases i
      · dsimp [w]
        have hab : 0 < a*b := mul_pos ha hb
        have : z.1/a + z.2/b ≤ 1 := by
          field_simp
          nlinarith [hz.2.2]
        linarith
      · dsimp [w]
        exact div_nonneg hz.1 (le_of_lt ha)
      · dsimp [w]
        exact div_nonneg hz.2.1 (le_of_lt hb)
    · simp [w, Fin.sum_univ_succ]
    · intro i
      fin_cases i <;> simp [p]
    · ext <;> simp [w, p, A, B, C, Fin.sum_univ_succ] <;>
        field_simp <;> ring


private lemma closedH (a : ℝ) (ha:0<a) : IsClosed (closedHalfDisk A (B a) (fun t => t ≤ 0)) := by
  have h1 : IsClosed {z : Plane | z.1^2 + z.2^2 ≤ a*z.1} :=
    isClosed_le (continuous_fst.pow 2 |>.add (continuous_snd.pow 2))
      (continuous_const.mul continuous_fst)
  have h2 : IsClosed {z : Plane | z.2 ≤ (0:ℝ)} :=
    isClosed_le continuous_snd continuous_const
  have heq : closedHalfDisk A (B a) (fun t => t ≤ 0) =
      {z : Plane | z.1^2 + z.2^2 ≤ a*z.1} ∩ {z | z.2 ≤ (0:ℝ)} := by
    ext z
    exact H_mem a ha z
  rw [heq]
  exact h1.inter h2

private lemma closedV (b : ℝ) (hb:0<b) : IsClosed (closedHalfDisk A (C b) (fun t => 0 ≤ t)) := by
  have h1 : IsClosed {z : Plane | z.1^2 + z.2^2 ≤ b*z.2} :=
    isClosed_le (continuous_fst.pow 2 |>.add (continuous_snd.pow 2))
      (continuous_const.mul continuous_snd)
  have h2 : IsClosed {z : Plane | z.1 ≤ (0:ℝ)} :=
    isClosed_le continuous_fst continuous_const
  have heq : closedHalfDisk A (C b) (fun t => 0 ≤ t) =
      {z : Plane | z.1^2 + z.2^2 ≤ b*z.2} ∩ {z | z.1 ≤ (0:ℝ)} := by
    ext z; exact V_mem b hb z
  rw [heq]; exact h1.inter h2

private lemma closedW (a b : ℝ) : IsClosed (hypotenuseSemidisk a b) := by
  have h1 : IsClosed {z : Plane | z.1^2 + z.2^2 ≤ a*z.1 + b*z.2} :=
    isClosed_le (continuous_fst.pow 2 |>.add (continuous_snd.pow 2))
      ((continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd))
  have h2 : IsClosed {z : Plane | b*z.1 + a*z.2 ≤ a*b} :=
    isClosed_le ((continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)) continuous_const
  have heq : hypotenuseSemidisk a b =
      {z : Plane | z.1^2 + z.2^2 ≤ a*z.1 + b*z.2} ∩ {z | b*z.1 + a*z.2 ≤ a*b} := by
    ext z; exact W_mem a b z
  rw [heq]; exact h1.inter h2

private lemma closedT (a b : ℝ) : IsClosed (rightTriangle a b) := by
  unfold rightTriangle
  exact Set.Finite.isClosed_convexHull ℝ (by simp)

private lemma compactH (a:ℝ) (ha:0<a) : IsCompact (closedHalfDisk A (B a) (fun t => t ≤ 0)) := by
  apply IsCompact.of_isClosed_subset
    (show IsCompact (Set.Icc (0:ℝ) a ×ˢ Set.Icc (-a) 0) from isCompact_Icc.prod isCompact_Icc) (closedH a ha)
  intro z hz
  have h := (H_mem a ha z).1 hz
  constructor
  · constructor <;> nlinarith [sq_nonneg z.1, sq_nonneg z.2,
        mul_pos ha (by linarith : 0 < a)]
  · constructor <;> nlinarith [sq_nonneg z.1, sq_nonneg z.2, sq_nonneg (z.1 - a/2)]

private lemma compactV (b:ℝ) (hb:0<b) : IsCompact (closedHalfDisk A (C b) (fun t => 0 ≤ t)) := by
  apply IsCompact.of_isClosed_subset
    (show IsCompact (Set.Icc (-b) 0 ×ˢ Set.Icc (0:ℝ) b) from isCompact_Icc.prod isCompact_Icc) (closedV b hb)
  intro z hz
  have h := (V_mem b hb z).1 hz
  constructor
  · constructor <;> nlinarith [sq_nonneg z.1, sq_nonneg z.2, sq_nonneg (z.2 - b/2)]
  · constructor <;> nlinarith [sq_nonneg z.1, sq_nonneg z.2, sq_nonneg (z.2 - b/2)]

private lemma compactW (a b:ℝ) (ha:0<a) (hb:0<b) : IsCompact (hypotenuseSemidisk a b) := by
  apply IsCompact.of_isClosed_subset
    (show IsCompact (Set.Icc (-(a+b)) (a+b) ×ˢ Set.Icc (-(a+b)) (a+b)) from isCompact_Icc.prod isCompact_Icc) (closedW a b)
  intro z hz
  have h := (W_mem a b z).1 hz
  constructor <;> constructor <;>
    nlinarith [sq_nonneg (2*z.1-a), sq_nonneg (2*z.2-b),
      sq_nonneg z.1, sq_nonneg z.2, mul_pos ha hb]

private lemma compactT (a b:ℝ) (ha:0<a) (hb:0<b) : IsCompact (rightTriangle a b) := by
  apply IsCompact.of_isClosed_subset
    (show IsCompact (Set.Icc (0:ℝ) a ×ˢ Set.Icc (0:ℝ) b) from isCompact_Icc.prod isCompact_Icc) (closedT a b)
  intro z hz
  have h := (T_mem a b ha hb z).1 hz
  have hx : z.1 ≤ a := by nlinarith
  have hy : z.2 ≤ b := by nlinarith
  exact ⟨⟨h.1, hx⟩, ⟨h.2.1, hy⟩⟩

private lemma null_xline : volume {z : Plane | z.1 = 0} = 0 := by
  have he : {z : Plane | z.1 = 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext z; simp
  rw [he]
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)) _ = _
  rw [Measure.prod_prod]
  simp

private lemma null_yline : volume {z : Plane | z.2 = 0} = 0 := by
  have he : {z : Plane | z.2 = 0} = (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
    ext z; simp
  rw [he]
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)) _ = _
  rw [Measure.prod_prod]
  simp


private def sc (r:ℝ) (z:Plane) : Plane := (r*z.1, r*z.2)
private def vs (r:ℝ) (z:Plane) : Plane := (r*z.2, r*z.1)
private def linW (a b:ℝ) (z:Plane) : Plane := (-a*z.1 + b*z.2, b*z.1 + a*z.2)
private def affW (a b:ℝ) (z:Plane) : Plane := (a + (linW a b z).1, (linW a b z).2)
private def S0 : Set Plane := closedHalfDisk A (B 1) (fun t => t ≤ 0)

private lemma H_image (a:ℝ) (ha:0<a) :
    closedHalfDisk A (B a) (fun t => t ≤ 0) = sc a '' S0 := by
  ext z
  constructor
  · intro hz
    have hh := (H_mem a ha z).1 hz
    have ane : a ≠ 0 := ne_of_gt ha
    refine ⟨(z.1/a, z.2/a), ?_, ?_⟩
    · apply (H_mem 1 (by norm_num) _).2
      dsimp
      constructor
      · have ap : 0 < a^2 := sq_pos_of_pos ha
        field_simp
        nlinarith
      · exact div_nonpos_of_nonpos_of_nonneg hh.2 (le_of_lt ha)
    · dsimp [sc]
      ext <;> dsimp <;> field_simp
  · rintro ⟨u, hu, rfl⟩
    have h := (H_mem 1 (by norm_num) u).1 hu
    apply (H_mem a ha _).2
    dsimp [sc]
    constructor
    · nlinarith [mul_pos ha ha]
    · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) h.2

private lemma V_image (b:ℝ) (hb:0<b) :
    closedHalfDisk A (C b) (fun t => 0 ≤ t) = vs b '' S0 := by
  ext z
  constructor
  · intro hz
    have hh := (V_mem b hb z).1 hz
    have bn : b ≠ 0 := ne_of_gt hb
    refine ⟨(z.2/b, z.1/b), ?_, ?_⟩
    · apply (H_mem 1 (by norm_num) _).2
      dsimp
      constructor
      · field_simp
        nlinarith [mul_pos hb hb]
      · exact div_nonpos_of_nonpos_of_nonneg hh.2 (le_of_lt hb)
    · dsimp [vs]
      ext <;> dsimp <;> field_simp
    
  · rintro ⟨u, hu, rfl⟩
    have h := (H_mem 1 (by norm_num) u).1 hu
    apply (V_mem b hb _).2
    dsimp [vs]
    constructor
    · nlinarith [mul_pos hb hb]
    · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb) h.2

private lemma W_image (a b:ℝ) (ha:0<a) (hb:0<b) :
    hypotenuseSemidisk a b = affW a b '' S0 := by
  have dpos : 0 < a^2 + b^2 := by positivity
  let d := a^2+b^2
  ext z
  constructor
  · intro hz
    have hh := (W_mem a b z).1 hz
    -- inverse linear map (it is its own up to d)
    let X := z.1 - a
    let Y := z.2
    let u : Plane := ((-a*X + b*Y)/d, (b*X + a*Y)/d)
    refine ⟨u, ?_, ?_⟩
    · apply (H_mem 1 (by norm_num) _).2
      change ((-a*X + b*Y)/d)^2 + ((b*X+a*Y)/d)^2 ≤ 1*((-a*X+b*Y)/d) ∧
         (b*X+a*Y)/d ≤ 0
      constructor
      · have : ((-a*X+b*Y)^2 + (b*X+a*Y)^2) = d*(X^2+Y^2) := by
          dsimp [d]; ring
        rw [div_pow, div_pow, ← add_div, this]
        have dne : d ≠ 0 := ne_of_gt dpos
        -- cancel the positive denominator
        have eid : d*(X^2+Y^2)/d^2 = (X^2+Y^2)/d := by
          field_simp
        rw [eid, one_mul, div_le_div_iff_of_pos_right dpos]
        dsimp [X,Y]
        nlinarith [hh.1]
      · apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt dpos)
        dsimp [X,Y]
        nlinarith [hh.2]
    · dsimp [affW, linW, u]
      change (a + (-a*((-a*X+b*Y)/d) + b*((b*X+a*Y)/d)),
        b*((-a*X+b*Y)/d)+a*((b*X+a*Y)/d)) = z
      rcases z with ⟨x,y⟩
      dsimp [X,Y,d]
      have hn : a^2+b^2 ≠ 0 := ne_of_gt dpos
      apply Prod.ext <;> field_simp <;> ring
  · rintro ⟨u, hu, rfl⟩
    have h := (H_mem 1 (by norm_num) u).1 hu
    apply (W_mem a b _).2
    dsimp [affW, linW]
    constructor
    · have hd : 0 ≤ a^2+b^2 := le_of_lt dpos
      nlinarith [h.1]
    · have hd : 0 ≤ a^2+b^2 := le_of_lt dpos
      -- determinant side becomes d * (-u.2)
      nlinarith [h.2]


private lemma meas_low (c:ℝ) :
    MeasurePreserving (fun z : Plane => (z.1, c*z.1 + z.2)) volume volume := by
  change MeasurePreserving _ ((volume:Measure ℝ).prod (volume:Measure ℝ))
    ((volume:Measure ℝ).prod (volume:Measure ℝ))
  convert MeasurePreserving.skew_product (MeasurePreserving.id (volume:Measure ℝ))
    (g := fun x y : ℝ => c*x + y) (by fun_prop)
    (Filter.Eventually.of_forall (fun x =>
      (measurePreserving_add_left (volume:Measure ℝ) (c*x)).map_eq)) using 1
  ext z <;> rfl

private lemma meas_up (c:ℝ) :
    MeasurePreserving (fun z : Plane => (z.1 + c*z.2, z.2)) volume volume := by
  have h := (meas_low c).comp
    (Measure.measurePreserving_swap (μ := (volume:Measure ℝ)) (ν := (volume:Measure ℝ)))
  have h' := (Measure.measurePreserving_swap (μ := (volume:Measure ℝ)) (ν := (volume:Measure ℝ))).comp h
  refine ⟨by fun_prop, ?_⟩
  change Measure.map _ ((volume:Measure ℝ).prod (volume:Measure ℝ)) =
    ((volume:Measure ℝ).prod (volume:Measure ℝ))
  have he : (fun z : ℝ×ℝ => (z.1 + c*z.2, z.2)) =
      (Prod.swap ∘ (fun z : ℝ×ℝ => (z.1, c*z.1 + z.2)) ∘ Prod.swap) := by
    funext z; simp [Function.comp_def, add_comm]
  rw [he]
  exact h'.map_eq

private lemma map_diag (r t:ℝ) (hr:r≠0) (ht:t≠0) :
    Measure.map (fun z : Plane => (r*z.1, t*z.2)) volume =
       (ENNReal.ofReal |r⁻¹| * ENNReal.ofReal |t⁻¹|) • volume := by
  have h := Measure.map_prod_map (volume:Measure ℝ) (volume:Measure ℝ)
    (by fun_prop : Measurable (fun x : ℝ => r*x))
    (by fun_prop : Measurable (fun x : ℝ => t*x))
  change Measure.map (Prod.map (fun x : ℝ => r*x) (fun x : ℝ => t*x))
     ((volume:Measure ℝ).prod (volume:Measure ℝ)) = _ • ((volume:Measure ℝ).prod (volume:Measure ℝ))
  rw [← h]
  rw [Real.map_volume_mul_left hr, Real.map_volume_mul_left ht]
  rw [Measure.prod_smul_left, Measure.prod_smul_right]
  rw [smul_smul]

private lemma map_sc (r:ℝ) (hr:r≠0) :
    Measure.map (sc r) volume =
       (ENNReal.ofReal |r⁻¹| * ENNReal.ofReal |r⁻¹|) • volume := by
  change Measure.map (fun z : (ℝ×ℝ) => (r*z.1, r*z.2)) volume = _
  exact map_diag r r hr hr

private lemma meas_trans (p q:ℝ) :
    MeasurePreserving (fun z : Plane => (p + z.1, q + z.2)) volume volume := by
  have h := measurePreserving_add_left (volume:Measure Plane) (p,q)
  convert h using 1 <;> ext z <;> rfl

private lemma map_comp_eq {f g : Plane → Plane} (hf : Measurable f) (hg : Measurable g) :
    Measure.map (fun z => f (g z)) volume = Measure.map f (Measure.map g volume) := by
  symm
  simpa [Function.comp_def] using
    (Measure.map_map (μ := (volume:Measure Plane)) hf hg)

-- A convenient image formula for a measurable bijection and its inverse.
private lemma volume_image_of_inverse {f g : Plane → Plane}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : Function.LeftInverse g f) (hgf : Function.LeftInverse f g)
    {s : Set Plane} (hs : MeasurableSet s)
    {k : ENNReal} (hm : Measure.map g volume = k • volume) :
    volume (f '' s) = k * volume s := by
  have hi : g ⁻¹' s = f '' s := by
    ext z
    constructor
    · intro hz
      refine ⟨g z, hz, ?_⟩
      exact hgf z
    · rintro ⟨u, hu, rfl⟩
      simpa [hfg u] using hu
  have := Measure.map_apply_of_aemeasurable hg.aemeasurable hs (μ := (volume : Measure Plane))
  -- easier ordinary map_apply
  rw [hm] at this
  simpa [Measure.smul_apply, hi] using this.symm


private def gin (a b : ℝ) (z:Plane) : Plane :=
  ((-a*(z.1-a)+b*z.2)/(a^2+b^2), (b*(z.1-a)+a*z.2)/(a^2+b^2))

private lemma inverse_aff (a b:ℝ) (ha:0<a) (hb:0<b) :
    Function.LeftInverse (gin a b) (affW a b) ∧
    Function.LeftInverse (affW a b) (gin a b) := by
  have hn : a^2+b^2 ≠ 0 := by positivity
  constructor
  · rintro ⟨x,y⟩
    dsimp [gin, affW, linW]
    apply Prod.ext <;> field_simp <;> ring
  · rintro ⟨x,y⟩
    dsimp [gin, affW, linW]
    apply Prod.ext <;> field_simp <;> ring

private lemma map_gin (a b:ℝ) (ha:0<a) (hb:0<b) :
    Measure.map (gin a b) volume = ENNReal.ofReal (a^2+b^2) • volume := by
  let d := a^2+b^2
  have dp : 0 < d := by dsimp [d]; positivity
  have an : a ≠ 0 := ne_of_gt ha
  let c : ℝ := -b/a
  let r : ℝ := -a/d
  let t : ℝ := 1/a
  have rn : r ≠ 0 := by dsimp [r]; exact div_ne_zero (neg_ne_zero.mpr an) (ne_of_gt dp)
  have tn : t ≠ 0 := by dsimp [t]; positivity
  let tr : Plane → Plane := fun z => (-a + z.1, z.2)
  let U : Plane → Plane := fun z => (z.1 + c*z.2, z.2)
  let D : Plane → Plane := fun z => (r*z.1, t*z.2)
  let L : Plane → Plane := fun z => (z.1, c*z.1 + z.2)
  have he : gin a b = (fun z => L (D (U (tr z)))) := by
    funext z
    dsimp [gin, L, D, U, tr, r, t, c, d]
    apply Prod.ext <;> dsimp
    · field_simp; ring
    · field_simp; ring
  rw [he]
  rw [map_comp_eq (meas_low c).measurable (by fun_prop : Measurable (fun z => D (U (tr z))))]
  rw [map_comp_eq (by fun_prop : Measurable D) (by fun_prop : Measurable (fun z => U (tr z)))]
  rw [map_comp_eq (meas_up c).measurable (by fun_prop : Measurable tr)]
  have htr : Measure.map tr volume = volume := by
    change Measure.map (fun z : Plane => (-a+z.1, z.2)) volume = volume
    simpa using (meas_trans (-a) 0).map_eq
  rw [htr]
  rw [(meas_up c).map_eq]
  -- diagonal and last shear
  change Measure.map _ (Measure.map D volume) = _
  change Measure.map (fun z : Plane => (z.1, c*z.1+z.2)) (Measure.map _ volume) = _
  change Measure.map (fun z : Plane => (z.1, c*z.1+z.2))
    (Measure.map (fun z : Plane => (r*z.1, t*z.2)) volume) = _
  rw [map_diag r t rn tn]
  rw [Measure.map_smul]
  rw [(meas_low c).map_eq]
  -- scalar arithmetic
  congr 1
  rw [← ENNReal.ofReal_mul]
  · congr 1
    dsimp [r,t,d]
    rw [inv_div, one_div, inv_inv]
    rw [abs_div]
    simp [abs_of_pos ha, abs_of_pos (by positivity : 0 < a^2+b^2)]; field_simp
  · positivity

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem hippocrates_lunes (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (horizontalLune a b) + volume (verticalLune a b) =
      volume (rightTriangle a b) :=
/-ResultProofBegin-/by
  let H := closedHalfDisk A (B a) (fun t => t ≤ 0)
  let V := closedHalfDisk A (C b) (fun t => 0 ≤ t)
  let W := hypotenuseSemidisk a b
  let T := rightTriangle a b
  let X := H ∩ W
  let Y := V ∩ W
  change volume (H \ W) + volume (V \ W) = volume T
  have mH : MeasurableSet H := (closedH a ha).measurableSet
  have mV : MeasurableSet V := (closedV b hb).measurableSet
  have mW : MeasurableSet W := (closedW a b).measurableSet
  have mT : MeasurableSet T := (closedT a b).measurableSet
  have mX : MeasurableSet X := mH.inter mW
  have mY : MeasurableSet Y := mV.inter mW
  have dec : W = (T ∪ X) ∪ Y := by
    ext z
    constructor
    · intro hz
      have w := (W_mem a b z).1 hz
      by_cases hx : 0 ≤ z.1
      · by_cases hy : 0 ≤ z.2
        · exact Or.inl (Or.inl ((T_mem a b ha hb z).2 ⟨hx,hy,w.2⟩))
        · left; right
          refine ⟨?_, hz⟩
          apply (H_mem a ha z).2
          constructor <;> nlinarith
      · right
        refine ⟨?_, hz⟩
        apply (V_mem b hb z).2
        constructor <;> nlinarith
    · intro hz
      rcases hz with (h|h)
      · rcases h with (ht|hx)
        · have q := (T_mem a b ha hb z).1 ht
          apply (W_mem a b z).2
          refine ⟨?_, q.2.2⟩
          have xle : z.1 ≤ a := by nlinarith
          have yle : z.2 ≤ b := by nlinarith
          nlinarith [mul_nonneg q.1 (sub_nonneg.mpr xle),
            mul_nonneg q.2.1 (sub_nonneg.mpr yle)]
        · exact hx.2
      · exact h.2
  have ax (s : Set Plane) (h : s ⊆ {z : Plane | z.1 = 0}) : volume s = 0 :=
    measure_mono_null h null_xline
  have ay (s : Set Plane) (h : s ⊆ {z : Plane | z.2 = 0}) : volume s = 0 :=
    measure_mono_null h null_yline
  have tx : AEDisjoint volume T X := by
    change volume (T ∩ X) = 0
    apply ay
    intro z hz
    have ht := (T_mem a b ha hb z).1 hz.1
    have hh := (H_mem a ha z).1 hz.2.1
    exact le_antisymm hh.2 ht.2.1
  have ty : AEDisjoint volume T Y := by
    change volume (T ∩ Y) = 0
    apply ax
    intro z hz
    have ht := (T_mem a b ha hb z).1 hz.1
    have hh := (V_mem b hb z).1 hz.2.1
    exact le_antisymm hh.2 ht.1
  have xy : AEDisjoint volume X Y := by
    change volume (X ∩ Y) = 0
    apply ax
    intro z hz
    have h := (V_mem b hb z).1 hz.2.1
    -- X gives horizontal and nonpositive y; both imply origin; enough x=0 using V and H inequality
    have k := (H_mem a ha z).1 hz.1.1
    -- the intersection lies on the vertical axis: the horizontal disk is in x≥0,
    -- while the vertical disk is in x≤0 (already these inequalities follow from
    -- their defining quadratic bounds).  More explicitly the horizontal bound
    -- with the nonpositive `x` furnished by `V` forces `x^2 = 0`.
    change z.1 = 0
    have hxmul : a * z.1 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) h.2
    have hymul : b * z.2 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb) k.2
    have hx_sq : z.1 ^ 2 ≤ 0 := by
      nlinarith [k.1, hxmul, sq_nonneg z.2]
    nlinarith [hx_sq, sq_nonneg z.1]
  have voldec : volume W = (volume T + volume X) + volume Y := by
    rw [dec, measure_union₀ mY.nullMeasurableSet]
    · rw [measure_union₀ mX.nullMeasurableSet tx]
    · exact AEDisjoint.union_left_iff.mpr ⟨ty, xy⟩
  have hsplit : volume H = volume (H \ W) + volume X := by
    have e : H = (H \ W) ∪ X := by
      ext z
      constructor
      · intro h
        by_cases t : z ∈ W
        · exact Or.inr ⟨h,t⟩
        · exact Or.inl ⟨h,t⟩
      · intro h
        rcases h with h|h
        · exact h.1
        · exact h.1
    calc
      volume H = volume ((H \ W) ∪ X) := congrArg (fun s : Set Plane => volume s) e
      _ = volume (H \ W) + volume X :=
        measure_union
          (Set.disjoint_left.mpr (by
            intro z hz1 hz2
            exact hz1.2 hz2.2)) mX
  have vsplit : volume V = volume (V \ W) + volume Y := by
    have e : V = (V \ W) ∪ Y := by
      ext z
      constructor
      · intro h
        by_cases t : z ∈ W
        · exact Or.inr ⟨h,t⟩
        · exact Or.inl ⟨h,t⟩
      · intro h
        rcases h with h|h
        · exact h.1
        · exact h.1
    calc
      volume V = volume ((V \ W) ∪ Y) := congrArg (fun s : Set Plane => volume s) e
      _ = volume (V \ W) + volume Y :=
        measure_union
          (Set.disjoint_left.mpr (by
            intro z hz1 hz2
            exact hz1.2 hz2.2)) mY
  have areah : volume H = ENNReal.ofReal (a^2) * volume S0 := by
    dsimp [H]
    rw [H_image a ha]
    have hfa : Measurable (sc a) := by
      unfold sc
      fun_prop
    have hga : Measurable (sc (a⁻¹)) := by
      unfold sc
      fun_prop
    have hlia : Function.LeftInverse (sc (a⁻¹)) (sc a) := by
      intro z
      dsimp [sc]
      apply Prod.ext <;> dsimp <;> field_simp
    have hria : Function.LeftInverse (sc a) (sc (a⁻¹)) := by
      intro z
      dsimp [sc]
      apply Prod.ext <;> dsimp <;> field_simp
    have hs0 : MeasurableSet S0 := by
      change MeasurableSet (closedHalfDisk A (B 1) (fun t => t ≤ 0))
      exact (closedH 1 (by norm_num)).measurableSet
    have im := volume_image_of_inverse
       (f := sc a) (g := sc (a⁻¹)) hfa hga hlia hria
       (s := S0) hs0
       (k := ENNReal.ofReal |(a⁻¹)⁻¹| * ENNReal.ofReal |(a⁻¹)⁻¹|)
       (map_sc _ (inv_ne_zero (ne_of_gt ha)))
    rw [im]
    congr 1
    rw [inv_inv, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [abs_of_pos ha]; rw [sq]
  have areav : volume V = ENNReal.ofReal (b^2) * volume S0 := by
    dsimp [V]
    rw [V_image b hb]
    -- Swapping the coordinates is measure preserving; the inverse of this
    -- scaled swap is the same swap with the reciprocal scale.
    let f := vs b
    let g := vs (b⁻¹)
    have mi : Measure.map g volume =
        (ENNReal.ofReal |(b⁻¹)⁻¹| * ENNReal.ofReal |(b⁻¹)⁻¹|) • volume := by
      change Measure.map (fun z : Plane => sc (b⁻¹) (Prod.swap z)) volume = _
      rw [map_comp_eq (by unfold sc; fun_prop : Measurable (sc (b⁻¹)))
          (by fun_prop : Measurable (fun z : Plane => Prod.swap z))]
      change Measure.map (sc (b⁻¹))
        (Measure.map Prod.swap ((volume:Measure ℝ).prod (volume:Measure ℝ))) = _
      rw [(Measure.measurePreserving_swap (μ := (volume:Measure ℝ))
        (ν := (volume:Measure ℝ))).map_eq]
      exact map_sc _ (inv_ne_zero (ne_of_gt hb))
    have hmf : Measurable f := by
      change Measurable (fun z : Plane => (b*z.2, b*z.1))
      fun_prop
    have hmg : Measurable g := by
      change Measurable (fun z : Plane => ((b⁻¹)*z.2, (b⁻¹)*z.1))
      fun_prop
    have hlig : Function.LeftInverse g f := by
      intro z
      dsimp [f, g, vs]
      apply Prod.ext <;> dsimp <;> field_simp
    have hrig : Function.LeftInverse f g := by
      intro z
      dsimp [f, g, vs]
      apply Prod.ext <;> dsimp <;> field_simp
    have hs0 : MeasurableSet S0 := by
      change MeasurableSet (closedHalfDisk A (B 1) (fun t => t ≤ 0))
      exact (closedH 1 (by norm_num)).measurableSet
    have im := volume_image_of_inverse
       (f:=f) (g:=g) hmf hmg hlig hrig
       (s:=S0) hs0
       (k := ENNReal.ofReal |(b⁻¹)⁻¹| * ENNReal.ofReal |(b⁻¹)⁻¹|)
       mi
    change volume (f '' S0) = _
    rw [im]
    congr 1
    rw [inv_inv, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [abs_of_pos hb]; rw [sq]
  have areaw : volume W = ENNReal.ofReal (a^2+b^2) * volume S0 := by
    dsimp [W]
    rw [W_image a b ha hb]
    have hmf : Measurable (affW a b) := by
      change Measurable (fun z : Plane =>
        (a + (-a*z.1 + b*z.2), b*z.1 + a*z.2))
      fun_prop
    have hmg : Measurable (gin a b) := by
      change Measurable (fun z : Plane =>
        ((-a*(z.1-a)+b*z.2)/(a^2+b^2),
          (b*(z.1-a)+a*z.2)/(a^2+b^2)))
      fun_prop
    have hs0 : MeasurableSet S0 := by
      change MeasurableSet (closedHalfDisk A (B 1) (fun t => t ≤ 0))
      exact (closedH 1 (by norm_num)).measurableSet
    exact volume_image_of_inverse
       (f := affW a b) (g := gin a b) hmf hmg
       (inverse_aff a b ha hb).1 (inverse_aff a b ha hb).2
       (s := S0) hs0 (k := ENNReal.ofReal (a^2+b^2))
       (map_gin a b ha hb)
  have area : volume W = volume H + volume V := by
    rw [areaw, areah, areav, ← add_mul]
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ a^2) (by positivity : 0 ≤ b^2)]
  have finH : volume H ≠ ⊤ := by
    change volume (closedHalfDisk A (B a) (fun t => t ≤ 0)) ≠ ⊤
    exact (compactH a ha).measure_ne_top
  have finV : volume V ≠ ⊤ := by
    change volume (closedHalfDisk A (C b) (fun t => 0 ≤ t)) ≠ ⊤
    exact (compactV b hb).measure_ne_top
  have finX : volume X ≠ ⊤ := by
    apply measure_ne_top_of_subset (s := H) (t := X)
    · intro z hz
      exact hz.1
    · exact finH
  have finY : volume Y ≠ ⊤ := by
    apply measure_ne_top_of_subset (s := V) (t := Y)
    · intro z hz
      exact hz.1
    · exact finV
  apply (ENNReal.add_left_inj (by exact ENNReal.add_ne_top.mpr ⟨finX,finY⟩)).mp
    (show _ + (volume X + volume Y) = _ + (volume X + volume Y) from ?_)
  calc
    volume (H \ W) + volume (V \ W) + (volume X + volume Y)
        = volume H + volume V := by
            rw [hsplit, vsplit]
            ac_rfl
    _ = volume W := area.symm
    _ = (volume T + volume X) + volume Y := voldec
    _ = volume T + (volume X + volume Y) := by ac_rfl
/-ResultProofEnd-/
/-ResultEnd-/
-- test

end
end Submission
