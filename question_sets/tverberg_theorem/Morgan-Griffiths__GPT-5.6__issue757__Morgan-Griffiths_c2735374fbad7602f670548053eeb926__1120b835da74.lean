import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/tverberg_theorem_65d3218943/Colorful.lean

/-! Proof-only infrastructure: a finite colorful convex hull lemma. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Set Filter

namespace Tverberg65

/-- At a point of a convex set minimizing its squared norm, the supporting
    linear functional points inward.  We state it for real inner product
    spaces; no closedness hypotheses are needed after a minimum is known. -/
lemma inner_ge_of_min_on_convex {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {C : Set V} (hC : Convex ℝ C) {p : V} (hp : p ∈ C)
    (hmin : ∀ q ∈ C, ‖p‖ ^ 2 ≤ ‖q‖ ^ 2)
    {q : V} (hq : q ∈ C) : ‖p‖ ^ 2 ≤ @inner ℝ V _ p q := by
  -- Move a small positive distance from `p` towards `q`.  If the displayed
  -- inequality failed the squared norm would go down.
  by_contra hn
  have hlt : @inner ℝ V _ p q < ‖p‖ ^ 2 := lt_of_not_ge hn
  let δ : ℝ := ‖p‖ ^ 2 - @inner ℝ V _ p q
  have hδ : 0 < δ := sub_pos.mpr hlt
  let M : ℝ := ‖q - p‖ ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let t : ℝ := min 1 (δ / (M + 1))
  have hden : 0 < M + 1 := by linarith
  have hrat : 0 < δ / (M + 1) := div_pos hδ hden
  have htpos : 0 < t := by
    dsimp [t]; exact lt_min (by norm_num) hrat
  have ht1 : t ≤ (1:ℝ) := by dsimp [t]; exact min_le_left _ _
  have htrat : t ≤ δ / (M+1) := by dsimp [t]; exact min_le_right _ _
  have ht0 : 0 ≤ t := le_of_lt htpos
  -- the step is small enough
  have htM : t * M < 2 * δ := by
    have hle : t * (M+1) ≤ δ := (le_div_iff₀ hden).mp htrat
    have hlt' : t * M < δ := by nlinarith
    nlinarith
  let z : V := (1-t) • p + t • q
  have hz : z ∈ C :=
    hC hp hq (sub_nonneg.mpr ht1) ht0 (by ring)
  have hbad : ‖z‖ ^ 2 < ‖p‖ ^ 2 := by
    -- Write it as `p + t • (q-p)`.
    have hz' : z = p + t • (q-p) := by
      dsimp [z]
      module
    rw [hz', norm_add_sq_real]
    have hi : @inner ℝ V _ p (t • (q-p)) =
          t * (@inner ℝ V _ p q - @inner ℝ V _ p p) := by
      rw [inner_smul_right, inner_sub_right]
    have hnrm : ‖t • (q-p)‖ ^ 2 = t^2 * M := by
      rw [norm_smul]
      have habs : |t| = t := abs_of_pos htpos
      dsimp [Real.norm_eq_abs]
      rw [habs]
      dsimp [M]
      ring
    rw [hi, hnrm, real_inner_self_eq_norm_sq p]
    -- now the inequality is scalar algebra from the choice of `t`
    dsimp [δ] at htM ⊢
    nlinarith
  exact (not_lt_of_ge (hmin z hz)) hbad

-- sanity compact-colorful infrastructure follows
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Finite colorful Carathéodory in the exact dimension needed below.
There is one color class for each of `finrank V + 1` indices and all
classes have the same finite nonempty set of choices. -/
theorem colorful_zero
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (X : ι → κ → V)
    (hcard : Fintype.card ι = Module.finrank ℝ V + 1)
    (hzero : ∀ i, (0:V) ∈ convexHull ℝ (Set.range (X i))) :
    ∃ g : ι → κ, (0:V) ∈ convexHull ℝ (Set.range (fun i => X i (g i))) := by
  classical
  let S (g : ι → κ) : Set V := convexHull ℝ (Set.range (fun i => X i (g i)))
  let U : Set V := ⋃ g : (ι → κ), S g
  have hcomp : IsCompact U := by
    dsimp [U]
    apply isCompact_iUnion
    intro g
    exact (Set.finite_range _).isCompact_convexHull ℝ
  have hne : U.Nonempty := by
    classical
    let g : ι → κ := fun _ => Classical.choice ‹Nonempty κ›
    let i : ι := Classical.choice ‹Nonempty ι›
    have hx : X i (g i) ∈ S g := by
      dsimp [S]
      exact subset_convexHull ℝ _ (Set.mem_range_self _)
    exact ⟨_, Set.mem_iUnion.mpr ⟨g, hx⟩⟩
  obtain ⟨p, hpU, hpmin⟩ := hcomp.exists_isMinOn hne
      ((continuous_norm.pow 2).continuousOn)
  -- Choose the colorful simplex attaining this minimizing point.
  rcases Set.mem_iUnion.mp hpU with ⟨g, hp⟩
  -- If the point were nonzero we get a missing color on a supporting face.
  by_contra hcontra
  have hp0 : p ≠ (0:V) := by
    intro hpz
    apply hcontra
    exact ⟨g, hpz ▸ hp⟩
  let c : ℝ := ‖p‖ ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hminS : ∀ z ∈ S g, ‖p‖^2 ≤ ‖z‖^2 := by
    intro z hz
    exact hpmin (Set.mem_iUnion.mpr ⟨g, hz⟩)
  have hsupport : ∀ z ∈ S g, c ≤ @inner ℝ V _ p z := by
    intro z hz
    dsimp [c]
    exact inner_ge_of_min_on_convex (convex_convexHull ℝ _) hp hminS hz
  -- Write the minimizing point using a positive affinely independent set of
  -- vertices.  Positive coefficients ensure all these vertices lie on the
  -- supporting hyperplane.
  obtain ⟨α, hαfin, z, w, hzS, hzaff, hwpos, hwsum, hwbar⟩ :=
    eq_pos_convex_span_of_mem_convexHull hp
  classical
  letI : Fintype α := hαfin
  -- each chosen vertex comes from a color
  have hfind : ∀ a : α, ∃ i : ι, z a = X i (g i) := by
    intro a
    rcases hzS (Set.mem_range_self a) with ⟨i, hi⟩
    exact ⟨i, hi.symm⟩
  choose col hcol using hfind
  have hzinner : ∀ a : α, @inner ℝ V _ p (z a) = c := by
    intro a
    have hge : ∀ a : α, c ≤ @inner ℝ V _ p (z a) := by
      intro b
      exact hsupport _ (subset_convexHull ℝ _ (by
        have := hzS (Set.mem_range_self b)
        exact this))
    -- The positive barycentric average is `p`; if any term were larger the
    -- average would be larger as well.
    have hsuminner : (∑ a : α, w a * (@inner ℝ V _ p (z a))) = c := by
      have H := congrArg (fun u : V => @inner ℝ V _ p u) hwbar
      -- `hwbar` has the average on the left and `p` on the right.
      simpa [inner_sum, inner_smul_right, c,
        real_inner_self_eq_norm_sq] using H
    by_contra hne'
    have hgt : c < @inner ℝ V _ p (z a) :=
      lt_of_le_of_ne (hge a) (Ne.symm hne')
    have hnonneg : ∀ b : α, 0 ≤ w b * (@inner ℝ V _ p (z b) - c) := by
      intro b
      exact mul_nonneg (le_of_lt (hwpos b)) (sub_nonneg.mpr (hge b))
    have hstrict : 0 < w a * (@inner ℝ V _ p (z a) - c) :=
      mul_pos (hwpos a) (sub_pos.mpr hgt)
    have hspos : 0 < ∑ b : α, w b * (@inner ℝ V _ p (z b) - c) :=
      Finset.sum_pos' (fun i _ => hnonneg i) ⟨a, Finset.mem_univ _, hstrict⟩
    have hs0 : (∑ b : α, w b * (@inner ℝ V _ p (z b) - c)) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [hsuminner, hwsum]
      ring
    exact (ne_of_gt hspos) hs0
  -- The supporting hyperplane is a proper affine hyperplane, so an
  -- affine independent family it contains has strictly fewer than the
  -- ambient-dimension-plus-one elements.
  let L : V →ₗ[ℝ] ℝ := ((innerSL ℝ : V →L⋆[ℝ] V →L[ℝ] ℝ) p).toLinearMap
  have hL (v : V) : L v = @inner ℝ V _ p v := rfl
  let H : AffineSubspace ℝ V := AffineSubspace.mk' p (LinearMap.ker L)
  have hzin : Set.range z ⊆ (H : Set V) := by
    rintro _ ⟨a, rfl⟩
    change z a ∈ AffineSubspace.mk' p (LinearMap.ker L)
    rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker]
    rw [LinearMap.map_sub, hL, hL, hzinner a,
      real_inner_self_eq_norm_sq]
    simp [c]
  have hlecard : Fintype.card α ≤ Module.finrank ℝ V + 1 := by
    calc
      Fintype.card α ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
        hzaff.card_le_finrank_succ
      _ ≤ Module.finrank ℝ V + 1 :=
        Nat.add_le_add_right (Submodule.finrank_le _) _
  have hnecard : Fintype.card α ≠ Module.finrank ℝ V + 1 := by
    intro heq
    have htop : affineSpan ℝ (Set.range z) = (⊤ : AffineSubspace ℝ V) :=
      hzaff.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr heq
    have hsub : (⊤ : AffineSubspace ℝ V) ≤ H := by
      rw [← htop]
      exact (affineSpan_le).2 hzin
    have h0mem : (0:V) ∈ H := hsub (AffineSubspace.mem_top ℝ V 0)
    change (0:V) ∈ AffineSubspace.mk' p (LinearMap.ker L) at h0mem
    have hzker : L (0 - p) = 0 := by
      simpa [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker] using h0mem
    have : c = 0 := by
      simpa [LinearMap.map_sub, hL, c, real_inner_self_eq_norm_sq] using hzker
    exact (ne_of_gt hc) this
  have hltα : Fintype.card α < Fintype.card ι := by
    rw [hcard]
    exact lt_of_le_of_ne hlecard hnecard
  have hnotsurj : ¬ Function.Surjective col := by
    intro hs
    exact (not_le_of_gt hltα) (Fintype.card_le_of_surjective col hs)
  -- pick the missing color
  classical
  simp only [Function.Surjective] at hnotsurj
  push_neg at hnotsurj
  rcases hnotsurj with ⟨k, hk⟩
  -- Some point of that color is on the other side of the hyperplane:
  -- otherwise its whole (strict) convex hull would be on the positive side,
  -- whereas its hull contains zero.
  have hxchoice : ∃ b : κ, @inner ℝ V _ p (X k b) ≤ 0 := by
    by_contra hh
    push_neg at hh
    let T : Set V := {v | 0 < @inner ℝ V _ p v}
    have hTconv : Convex ℝ T := by
      intro u hu v hv a b ha hb hab
      change 0 < @inner ℝ V _ p (a • u + b • v)
      have hu' : 0 < @inner ℝ V _ p u := hu
      have hv' : 0 < @inner ℝ V _ p v := hv
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      -- one coefficient can be zero, but their sum is one
      rcases eq_or_ne a 0 with ha0 | ha0
      · subst a
        have hb1 : b = 1 := by linarith
        simp [hb1]
        exact hv'
      · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have h1 : 0 < a * @inner ℝ V _ p u := mul_pos ha' hu'
        have h2 : 0 ≤ b * @inner ℝ V _ p v := mul_nonneg hb (le_of_lt hv')
        exact add_pos_of_pos_of_nonneg h1 h2
    have hrange : Set.range (X k) ⊆ T := by
      rintro _ ⟨b, rfl⟩
      exact hh b
    have hhull : convexHull ℝ (Set.range (X k)) ⊆ T :=
      convexHull_min hrange hTconv
    have hzT := hhull (hzero k)
    change (0:ℝ) < @inner ℝ V _ p (0:V) at hzT
    simp at hzT
  rcases hxchoice with ⟨b, hb⟩
  -- Replace the absent color with this vertex; all supporting vertices, and
  -- hence `p`, are still in the new colorful simplex.
  let g' : ι → κ := fun i => if i = k then b else g i
  have hgcol (a : α) : g' (col a) = g (col a) := by
    dsimp [g']
    split_ifs with h
    · exact False.elim ((hk a) h)
    · rfl
  have hza : ∀ a : α, z a ∈ S g' := by
    intro a
    dsimp [S]
    apply subset_convexHull ℝ _
    refine ⟨col a, ?_⟩
    change X (col a) (g' (col a)) = z a
    rw [hgcol a]
    exact (hcol a).symm
  have hp' : p ∈ S g' := by
    have hs := (convex_convexHull ℝ (Set.range (fun i => X i (g' i)))).sum_mem
      (t := Finset.univ) (w := w) (z := z)
      (fun i hi => le_of_lt (hwpos i)) hwsum
      (fun i hi => hza i)
    simpa [hwbar] using hs
  have hxb : X k b ∈ S g' := by
    dsimp [S]
    apply subset_convexHull ℝ _
    refine ⟨k, ?_⟩
    simp [g']
  have hmin' : ∀ y ∈ S g', ‖p‖^2 ≤ ‖y‖^2 := by
    intro y hy
    exact hpmin (Set.mem_iUnion.mpr ⟨g', hy⟩)
  have hge' : c ≤ @inner ℝ V _ p (X k b) := by
    dsimp [c]
    exact inner_ge_of_min_on_convex (convex_convexHull ℝ _) hp' hmin' hxb
  linarith

end Tverberg65

end

-- END INLINED FILE: Mathlib/Support/tverberg_theorem_65d3218943/Colorful.lean

-- BEGIN INLINED FILE: Mathlib/Support/tverberg_theorem_65d3218943/Reduction.lean

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Set
open Tverberg65

namespace Tverberg65

abbrev TVSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev LiftSpace (r d : ℕ) := EuclideanSpace ℝ (Fin (r-1) × Fin (d+1))

def aug {d n : ℕ} (f : Fin n → TVSpace d) (j : Fin n) (b : Fin (d+1)) : ℝ :=
  if h : b.val < d then f j ⟨b.val, h⟩ else 1

@[simp] lemma aug_last {d n} (f : Fin n → TVSpace d) (j) :
    aug f j (Fin.last d) = 1 := by
  simp [aug, Fin.last, Nat.lt_irrefl]

lemma sub_lt_self_pos {r : ℕ} (hr : 1 ≤ r) : r - 1 < r := by omega

def ca {r : ℕ} (hr : 1 ≤ r) (a : Fin (r-1)) : Fin r :=
  ⟨a.val, lt_trans a.isLt (sub_lt_self_pos hr)⟩
def klast {r : ℕ} (hr : 1 ≤ r) : Fin r := ⟨r-1, sub_lt_self_pos hr⟩

@[simp] lemma ca_val {r} (hr : 1 ≤ r) (a : Fin (r-1)) : (ca hr a).val = a.val := rfl
@[simp] lemma klast_val {r} (hr : 1 ≤ r) : (klast hr).val = r-1 := rfl
lemma ca_lt {r} (hr : 1 ≤ r) (a : Fin (r-1)) : (ca hr a).val < r-1 := a.isLt
lemma klast_not_lt {r} (hr : 1 ≤ r) : ¬ (klast hr).val < r-1 := by simp
lemma eq_klast_of_not_lt {r} (hr : 1 ≤ r) (k : Fin r)
    (h : ¬ k.val < r-1) : k = klast hr := by
  apply Fin.ext
  dsimp [klast]
  omega
lemma ca_inj {r} (hr : 1 ≤ r) {a a' : Fin (r-1)} :
    ca hr a = ca hr a' ↔ a = a' := by
  constructor
  · intro h; exact Fin.ext (Fin.mk.inj_iff.mp h)
  · exact congrArg _

/-- The tensor-like Sarkaria lifting; at a short row only the matching color
has `aug`, while the last color has its negative. -/
def liftPt {d r n : ℕ} (hr : 1 ≤ r) (f : Fin n → TVSpace d)
    (j : Fin n) (k : Fin r) : LiftSpace r d :=
  WithLp.toLp 2 (fun q : Fin (r-1) × Fin (d+1) =>
    if hk : k.val < r-1 then
      if q.1.val = k.val then aug f j q.2 else 0
    else -(aug f j q.2))

@[simp] lemma liftPt_apply {d r n} (hr : 1 ≤ r) (f : Fin n → TVSpace d)
    (j : Fin n) (k : Fin r) (a : Fin (r-1)) (b : Fin (d+1)) :
    liftPt hr f j k (a,b) =
      if hk : k.val < r-1 then
        if a.val = k.val then aug f j b else 0
      else -(aug f j b) := by rfl

/-- Every color class of the lifting contains zero: average all `r` colors
for the same original point. -/
lemma zero_in_lift_color {d r n : ℕ} (hr : 1 ≤ r)
    (f : Fin n → TVSpace d) (j : Fin n) :
    (0 : LiftSpace r d) ∈ convexHull ℝ (Set.range (fun k : Fin r => liftPt hr f j k)) := by
  classical
  -- it is enough that their sum is zero, and take the uniform weights
  have hsum : (∑ k : Fin r, liftPt hr f j k) = 0 := by
    apply PiLp.ext
    rintro ⟨a,b⟩
    -- only `ca a` contributes positively, and `klast` negatively
    -- sum the function by cases, using a single nonzero in the initial rows
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    change (∑ k : Fin r, (liftPt hr f j k (a,b))) = 0
    simp_rw [liftPt_apply]
    -- rewrite as sum of a single positive color plus a single negative color
    have hfun (k : Fin r) :
        (if hk : k.val < r - 1 then (if a.val = k.val then aug f j b else 0)
          else -aug f j b) =
        (if k = ca hr a then aug f j b else 0) +
          (if k = klast hr then -(aug f j b) else 0) := by
      by_cases hk : k.val < r-1
      · by_cases he : a.val = k.val
        · have eqk : k = ca hr a := by apply Fin.ext; exact he.symm
          subst k
          have hne : ca hr a ≠ klast hr := by
            intro h; have := congrArg Fin.val h; dsimp [ca, klast] at this
            omega
          simp [ca_lt hr a, hne]
        · have hne1 : k ≠ ca hr a := by
            intro h
            have e := congrArg Fin.val h
            exact he e.symm
          have hne2 : k ≠ klast hr := by
            intro h
            have e := congrArg Fin.val h
            dsimp [klast] at e
            omega
          simp [hk, he, hne1, hne2]
      · have eqk : k = klast hr := eq_klast_of_not_lt hr k hk
        subst k
        have hne : klast hr ≠ ca hr a := by
          intro h
          have e := congrArg Fin.val h
          dsimp [ca, klast] at e
          omega
        simp [klast_not_lt hr, hne]
    simp_rw [hfun]
    rw [Finset.sum_add_distrib]
    simp
  -- uniform weights
  let w : Fin r → ℝ := fun _ => (r:ℝ)⁻¹
  have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr))
  have hws : (∑ k : Fin r, w k) = 1 := by
    simp [w, hr0]
  have hv : (Finset.univ.affineCombination ℝ (fun k : Fin r => liftPt hr f j k) w) = (0 : LiftSpace r d) := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hws]
    -- constant multiples of the zero sum
    change (∑ k : Fin r, w k • liftPt hr f j k) = _
    change (∑ k : Fin r, (r:ℝ)⁻¹ • liftPt hr f j k) = _
    rw [← Finset.smul_sum]
    simp [hsum]
  -- the convex set contains this affine combination
  rw [convexHull_range_eq_exists_affineCombination]
  exact ⟨Finset.univ, w, (by intro i hi; dsimp [w]; positivity), hws, hv⟩


end Tverberg65

end

-- END INLINED FILE: Mathlib/Support/tverberg_theorem_65d3218943/Reduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/tverberg_theorem_65d3218943/Extraction.lean

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Set
open Tverberg65

namespace Tverberg65

/-- Reading coordinates from a zero lifted colorful simplex produces a common
ordinary weighted barycentre. This is the elementary algebraic half of
Sarkaria's lifting. -/
lemma lift_zero_gives_partition {d r n : ℕ} (hr : 1 ≤ r)
    (f : Fin n → TVSpace d) (g : Fin n → Fin r)
    (hz : (0 : LiftSpace r d) ∈
      convexHull ℝ (Set.range (fun j : Fin n => liftPt hr f j (g j)))) :
    ∃ parts : Fin r → Set (Fin n),
      (∀ i j : Fin r, i ≠ j → Disjoint (parts i) (parts j)) ∧
      (⋃ i : Fin r, parts i) = Set.univ ∧
      ∃ x : TVSpace d, ∀ i : Fin r, x ∈ convexHull ℝ (f '' parts i) := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hz
  rcases hz with ⟨s, w, hw0, hws, hzsum⟩
  have hlin : (∑ j ∈ s, w j • liftPt hr f j (g j)) =
        (0 : LiftSpace r d) := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hws] at hzsum
    exact hzsum
  let fiber (k : Fin r) : Finset (Fin n) :=
    s.filter (fun j => g j = k)
  let tot (k : Fin r) : ℝ := ∑ j ∈ fiber k, w j
  let vec (k : Fin r) : TVSpace d := ∑ j ∈ fiber k, w j • f j
  let t0 : ℝ := tot (klast hr)
  -- useful coordinate of the lifted sum
  have hcoord (a : Fin (r-1)) (b : Fin (d+1)) :
      (∑ j ∈ s,
        w j * (if hk : (g j).val < r-1 then
          (if a.val = (g j).val then aug f j b else 0)
          else -(aug f j b))) = 0 := by
    have hh := congrArg (fun v : LiftSpace r d => v (a,b)) hlin
    -- all these operations are pointwise on the Pi-space hidden in `WithLp`
    simp only [PiLp.zero_apply] at hh
    simpa [WithLp.ofLp_sum, Finset.sum_apply, liftPt_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm] using hh

  have hsplit (a : Fin (r-1)) (b : Fin (d+1)) :
      (∑ j ∈ s,
        w j * (if hk : (g j).val < r-1 then
          (if a.val = (g j).val then aug f j b else 0)
          else -(aug f j b))) =
        (∑ j ∈ fiber (ca hr a), w j * aug f j b) -
          (∑ j ∈ fiber (klast hr), w j * aug f j b) := by
    have hp (j : Fin n) :
        w j * (if hk : (g j).val < r-1 then
          (if a.val = (g j).val then aug f j b else 0)
          else -(aug f j b)) =
        (if g j = ca hr a then w j * aug f j b else 0) -
          (if g j = klast hr then w j * aug f j b else 0) := by
      by_cases hk : (g j).val < r-1
      · by_cases he : a.val = (g j).val
        · have eqk : g j = ca hr a := by
            apply Fin.ext
            exact he.symm
          have hne : g j ≠ klast hr := by
            intro h
            have h' := congrArg Fin.val h
            dsimp [klast] at h'
            omega
          rw [dif_pos hk, if_pos he, if_pos eqk, if_neg hne]
          ring
        · have hne1 : g j ≠ ca hr a := by
            intro h
            have h' := congrArg Fin.val h
            exact he h'.symm
          have hne2 : g j ≠ klast hr := by
            intro h
            have h' := congrArg Fin.val h
            dsimp [klast] at h'
            omega
          rw [dif_pos hk, if_neg he, if_neg hne1, if_neg hne2]
          ring
      · have eqk : g j = klast hr :=
          eq_klast_of_not_lt hr (g j) hk
        have hne : g j ≠ ca hr a := by
          intro h
          have h' := congrArg Fin.val h
          apply hk
          calc (g j).val = a.val := by simpa [ca] using h'
               _ < r-1 := a.isLt
        -- avoid trying to solve it by arithmetic in the final simp
        rw [dif_neg hk, if_neg hne, if_pos eqk]
        ring
    calc
      _ = ∑ j ∈ s,
          ((if g j = ca hr a then w j * aug f j b else 0) -
            (if g j = klast hr then w j * aug f j b else 0)) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hp j
      _ = (∑ j ∈ s, (if g j = ca hr a then w j * aug f j b else 0)) -
            (∑ j ∈ s, (if g j = klast hr then w j * aug f j b else 0)) := by
              rw [Finset.sum_sub_distrib]
      _ = _ := by
        -- filtering the old support is exactly a color fiber
        simp [fiber, Finset.sum_filter]

  have htot_ca (a : Fin (r-1)) : tot (ca hr a) = t0 := by
    have H : (∑ j ∈ fiber (ca hr a), w j * aug f j (Fin.last d)) -
          (∑ j ∈ fiber (klast hr), w j * aug f j (Fin.last d)) = 0 := by
      rw [← hsplit a (Fin.last d)]
      exact hcoord a (Fin.last d)
    simp at H
    dsimp [tot, t0]
    linarith

  let bi (b : Fin d) : Fin (d+1) :=
    ⟨b.val, Nat.lt_succ_of_lt b.isLt⟩
  have aug_b (j : Fin n) (b : Fin d) : aug f j (bi b) = f j b := by
    dsimp [aug, bi]
    simp [b.isLt]
  have hvec_ca (a : Fin (r-1)) : vec (ca hr a) = vec (klast hr) := by
    apply PiLp.ext
    intro b
    have H : (∑ j ∈ fiber (ca hr a), w j * aug f j (bi b)) -
          (∑ j ∈ fiber (klast hr), w j * aug f j (bi b)) = 0 := by
      rw [← hsplit a (bi b)]
      exact hcoord a (bi b)
    simp only [aug_b] at H
    have H' : (∑ j ∈ fiber (ca hr a), w j * f j b) =
        (∑ j ∈ fiber (klast hr), w j * f j b) := sub_eq_zero.mp H
    dsimp [vec]
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    exact H'

  have k_cases (k : Fin r) : k = klast hr ∨
       ∃ a : Fin (r-1), k = ca hr a := by
    by_cases hk : k.val < r-1
    · right
      exact ⟨⟨k.val, hk⟩, by apply Fin.ext; rfl⟩
    · left
      exact eq_klast_of_not_lt hr k hk
  have htot_all (k : Fin r) : tot k = t0 := by
    rcases k_cases k with h | ⟨a, h⟩
    · simp [h, t0]
    · simpa [h] using htot_ca a
  have hvec_all (k : Fin r) : vec k = vec (klast hr) := by
    rcases k_cases k with h | ⟨a, h⟩
    · simp [h]
    · simpa [h] using hvec_ca a
  have hsumtot : (∑ k : Fin r, tot k) = 1 := by
    -- each original index occurs in one and only one filtered fiber
    calc
      (∑ k : Fin r, tot k) =
          ∑ k : Fin r, ∑ j ∈ s, (if g j = k then w j else 0) := by
            simp [tot, fiber, Finset.sum_filter]
      _ = ∑ j ∈ s, ∑ k : Fin r, (if g j = k then w j else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ j ∈ s, w j := by simp
      _ = 1 := hws

  have ht0_nonneg : 0 ≤ t0 := by
    dsimp [t0, tot]
    exact Finset.sum_nonneg (by
      intro j hj
      exact hw0 j ((Finset.mem_filter.mp ((show j ∈ fiber (klast hr) from hj))).1))
  have ht0_ne : t0 ≠ 0 := by
    intro hz
    have H := hsumtot
    simp [htot_all, hz] at H
  have ht0_pos : 0 < t0 := lt_of_le_of_ne ht0_nonneg (Ne.symm ht0_ne)

  -- the normalized weights in any fiber give its common barycentre
  have hconv (k : Fin r) :
      (∑ j ∈ fiber k, (t0⁻¹ * w j) • f j) ∈
        convexHull ℝ (f '' {j : Fin n | g j = k}) := by
    refine (convex_convexHull ℝ _).sum_mem ?_ ?_ ?_
    · intro j hj
      exact mul_nonneg (le_of_lt (inv_pos.mpr ht0_pos))
        (hw0 j ((Finset.mem_filter.mp ((show j ∈ fiber k from hj))).1))
    · calc
        (∑ j ∈ fiber k, t0⁻¹ * w j) =
            t0⁻¹ * (∑ j ∈ fiber k, w j) := by
              rw [Finset.mul_sum]
        _ = t0⁻¹ * tot k := by rfl
        _ = t0⁻¹ * t0 := by rw [htot_all k]
        _ = 1 := inv_mul_cancel₀ ht0_ne
    · intro j hj
      apply subset_convexHull ℝ _
      exact ⟨j, by
        change g j = k
        exact (Finset.mem_filter.mp ((show j ∈ fiber k from hj))).2, rfl⟩
  let x : TVSpace d := t0⁻¹ • vec (klast hr)
  refine ⟨(fun k => {j : Fin n | g j = k}), ?_, ?_, x, ?_⟩
  · intro i k hne
    refine Set.disjoint_left.mpr ?_
    intro j hj hj'
    change g j = i at hj
    change g j = k at hj'
    exact hne (hj.symm.trans hj')
  · ext j
    constructor
    · intro hj
      trivial
    · intro hj
      have hmem : j ∈ ({j : Fin n | g j = g j} : Set (Fin n)) := rfl
      exact Set.mem_iUnion.mpr ⟨g j, hmem⟩
  · intro k
    have heq : x = ∑ j ∈ fiber k, (t0⁻¹ * w j) • f j := by
      change t0⁻¹ • vec (klast hr) = _
      calc
        t0⁻¹ • vec (klast hr) = t0⁻¹ • vec k := by rw [hvec_all k]
        _ = _ := by
          dsimp [vec]
          simp [Finset.smul_sum, smul_smul]
    rw [heq]
    exact hconv k

end Tverberg65

end

-- END INLINED FILE: Mathlib/Support/tverberg_theorem_65d3218943/Extraction.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval.Combinatorics.Tverberg

/-!
# Tverberg's theorem

`tverberg_theorem`: any `(r-1)(d+1)+1` points in `ℝ^d` can be partitioned into
`r` parts whose convex hulls share a common point. Trusted helper
`HasTverbergPartition` (non-hole). Mathlib has Radon's theorem (the `r = 2`
case) but not Tverberg.
Category-(b) candidate from §169 of the Knill survey.
-/

open scoped BigOperators

/-- Euclidean `ℝ^d`. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- An `r`-part Tverberg partition: disjoint parts covering all indices whose
image convex hulls share a common point. -/
def HasTverbergPartition {d r n : ℕ} (f : Fin n → Space d) : Prop :=
  ∃ parts : Fin r → Set (Fin n),
    (∀ i j : Fin r, i ≠ j → Disjoint (parts i) (parts j)) ∧
    (⋃ i : Fin r, parts i) = Set.univ ∧
    ∃ x : Space d, ∀ i : Fin r, x ∈ convexHull ℝ (f '' parts i)



end LeanEval.Combinatorics.Tverberg

open LeanEval.Combinatorics.Tverberg
open scoped BigOperators
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem tverberg_theorem (d r : ℕ) (hr : 1 ≤ r)
    (f : Fin ((r - 1) * (d + 1) + 1) → Space d) :
    HasTverbergPartition (r := r) f :=
/-ResultProofBegin-/by
  classical
  -- choose one point from each lifted color by the colorful lemma
  haveI : Nonempty (Fin r) :=
    (Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one hr))
  haveI : Nonempty (Fin ((r - 1) * (d + 1) + 1)) :=
    Fin.pos_iff_nonempty.mp (by omega)
  have hc : Fintype.card (Fin ((r - 1) * (d + 1) + 1)) =
      Module.finrank ℝ (Tverberg65.LiftSpace r d) + 1 := by
    simp [Tverberg65.LiftSpace]
  have hcolors (j : Fin ((r - 1) * (d + 1) + 1)) :
      (0 : Tverberg65.LiftSpace r d) ∈
        convexHull ℝ (Set.range (fun k : Fin r => Tverberg65.liftPt hr f j k)) :=
    Tverberg65.zero_in_lift_color hr f j
  obtain ⟨g, hg⟩ := Tverberg65.colorful_zero
    (V := Tverberg65.LiftSpace r d)
    (ι := Fin ((r - 1) * (d + 1) + 1)) (κ := Fin r)
    (fun j k => Tverberg65.liftPt hr f j k) hc hcolors
  exact Tverberg65.lift_zero_gives_partition hr f g hg
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
