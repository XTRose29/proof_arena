import Mathlib
import ChallengeDeps

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/BasicSingleton.lean
section
open Set
open scoped Topology
namespace FamiliesProof
open Geometry
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
noncomputable def singletonComplex (z : E) : SimplicialComplex ℝ E where
  faces := {{z}}
  isRelLowerSet_faces := by
    intro s hs
    have hs' : s = {z} := Set.mem_singleton_iff.mp hs
    subst s
    constructor
    · exact Finset.singleton_nonempty _
    · intro t ht htne
      -- any nonempty subset of singleton is singleton
      have h : t = ({z} : Finset E) :=
        (Finset.subset_singleton_iff.mp ht).resolve_left
          (by intro hz; simpa [hz] using htne)
      simpa [h]
  indep := by
    intro s hs
    have hs' : s = {z} := Set.mem_singleton_iff.mp hs
    subst s
    letI : Subsingleton ({z} : Finset E) :=
      ⟨by
        intro a b
        have ha : (a:E) = z := by exact Finset.mem_singleton.mp a.property
        have hb : (b:E) = z := by exact Finset.mem_singleton.mp b.property
        exact Subtype.ext (ha.trans hb.symm)⟩
    exact affineIndependent_of_subsingleton ℝ _
  inter_subset_convexHull := by
    intro s t hs ht
    have hs' : s = {z} := Set.mem_singleton_iff.mp hs
    have ht' : t = {z} := Set.mem_singleton_iff.mp ht
    subst s; subst t
    simp [convexHull_singleton]

lemma singletonComplex_faces (z : E) : (singletonComplex z).faces = {{z}} := rfl
lemma singletonComplex_faces_finite (z : E) : (singletonComplex z).faces.Finite := by
  rw [singletonComplex_faces]
  simp
lemma singletonComplex_space (z : E) : (singletonComplex z).space = ({z} : Set E) := by
  ext x
  simp [Geometry.SimplicialComplex.space, singletonComplex_faces,
    convexHull_singleton]

end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/BasicSingleton.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/LipschitzWeights.lean
section
open Set
open scoped NNReal Topology BigOperators
namespace FamiliesProof
/-- A finite open cover of a compact nonempty metric space has nonnegative
Lipschitz bump functions supported on its members whose sum is uniformly
bounded below by a positive real.  Unlike a partition of unity these bump
functions are not normalised; this form keeps the Lipschitz proof elementary.
It is enough to divide the weighted barycentre by their sum afterwards. -/
theorem finite_lipschitz_bumps
    {J X : Type*} [Fintype J]
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    (V : J → Set X) (ho : ∀ j, IsOpen (V j))
    (hc : ∀ x : X, ∃ j, x ∈ V j) :
  ∃ w : J → (X → ℝ), ∃ b B : ℝ,
    0 < b ∧ 0 ≤ B ∧
    (∀ j, LipschitzWith 1 (w j)) ∧
    (∀ j x, 0 ≤ w j x) ∧
    (∀ j x, x ∉ V j → w j x = 0) ∧
    (∀ x, b ≤ ∑ j : J, w j x) ∧
    (∀ x, ∑ j : J, w j x ≤ B) := by
  classical
  let W : J → (X → ℝ) := fun j =>
    if h : ((V j)ᶜ : Set X).Nonempty
    then fun x => Metric.infDist x ((V j)ᶜ : Set X)
    else fun _ => 1
  have hLip : ∀ j, LipschitzWith 1 (W j) := by
    intro j
    dsimp [W]
    split_ifs with h
    · exact Metric.lipschitz_infDist_pt _
    · exact LipschitzWith.const'
          (α := X) (β := ℝ) 1
  have hnon : ∀ j x, 0 ≤ W j x := by
    intro j x
    dsimp [W]
    split_ifs
    · exact Metric.infDist_nonneg
    · norm_num
  have hout : ∀ j x, x ∉ V j → W j x = 0 := by
    intro j x hx
    dsimp [W]
    split_ifs with he
    · exact Metric.infDist_zero_of_mem (show x ∈ (V j)ᶜ from hx)
    · exact (he ⟨x, hx⟩).elim
  have hpos : ∀ x : X, 0 < ∑ j : J, W j x := by
    intro x
    obtain ⟨j, hxj⟩ := hc x
    have hj : 0 < W j x := by
      dsimp [W]
      split_ifs with he
      · have hh : IsClosed ((V j)ᶜ : Set X) := (ho j).isClosed_compl
        exact (hh.notMem_iff_infDist_pos he).1 (by simpa using hxj)
      · norm_num
    have hterm : W j x ≤ ∑ i ∈ (Finset.univ : Finset J), W i x :=
      Finset.single_le_sum (fun i _ => hnon i x) (Finset.mem_univ j)
    have hle : W j x ≤ ∑ i : J, W i x := by simpa using hterm
    exact lt_of_lt_of_le hj hle
  have hsumLip_aux : ∀ A : Finset J,
      LipschitzWith (A.card : NNReal)
        (fun x : X => ∑ j ∈ A, W j x) := by
    intro A
    classical
    induction A using Finset.induction_on with
    | empty =>
      simpa using (LipschitzWith.const (α := X) (β := ℝ) 0)
    | @insert a S ha hS =>
      have ha' := hLip a
      have hh := ha'.add hS
      simpa [Finset.sum_insert ha, ha,
        Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
          using hh
  have hsumLip : LipschitzWith (Fintype.card J : NNReal)
      (fun x : X => ∑ j : J, W j x) := by
    simpa using hsumLip_aux (Finset.univ : Finset J)
  let S : X → ℝ := fun x => ∑ j : J, W j x
  have hScont : Continuous S := hsumLip.continuous
  obtain ⟨xmin, hxmin, hmin⟩ :=
    isCompact_univ.exists_isMinOn (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
      hScont.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ :=
    isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
      hScont.continuousOn
  refine ⟨W, S xmin, S xmax, ?_, ?_, hLip, hnon, hout, ?_, ?_⟩
  · exact hpos xmin
  · exact le_of_lt (hpos xmax)
  · intro x
    exact hmin (by trivial)
  · intro x
    exact hmax (by trivial)

end FamiliesProof

namespace FamiliesProof
private lemma __LipschitzWeights_abs_div_sub (a c s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
  |a / s - c / t| ≤ |a-c| / s + |c| * |t-s| / (s*t) := by
  have hh : a / s - c / t = ((a-c)*t + c*(t-s))/(s*t) := by
    field_simp
    ring
  rw [hh, abs_div]
  rw [abs_of_pos (mul_pos hs ht)]
  have add : abs ((a-c)*t + c*(t-s)) ≤ abs (a-c) * t + abs c * abs (t-s) := by
    calc
      _ ≤ abs ((a-c)*t) + abs (c*(t-s)) := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_pos ht]
  have hdiv : abs (a-c) * t / (s*t) = abs (a-c) / s := by field_simp
  calc
    abs ((a-c)*t + c*(t-s)) / (s*t) ≤
      (abs (a-c)*t + abs c *abs (t-s))/(s*t) := by
        exact div_le_div_of_nonneg_right add (by positivity)
    _ = abs (a-c)/s + abs c * abs (t-s)/(s*t) := by
       rw [add_div, hdiv]

private lemma __LipschitzWeights_real_bound (a c s t b B n d : ℝ)
 (hb : 0 < b) (hs : b ≤ s) (ht : b ≤ t)
 (hc : 0 ≤ c) (hcB : c ≤ B) (hn : 0 ≤ n) (hB : 0 ≤ B) (hd : 0 ≤ d)
 (ha : abs (a-c) ≤ d) (hst : abs (t-s) ≤ n*d) :
   abs (a/s - c/t) ≤ (1/b + B*n/(b*b))*d := by
 have hs0 : 0 < s := lt_of_lt_of_le hb hs
 have ht0 : 0 < t := lt_of_lt_of_le hb ht
 calc
   _ ≤ abs (a-c)/s + abs c * abs (t-s)/(s*t) := __LipschitzWeights_abs_div_sub _ _ _ _ hs0 ht0
   _ ≤ d/b + B * (n*d) / (b*b) := by
     have h1 : abs (a-c) / s ≤ d / b := by
       apply (div_le_div_iff₀ hs0 hb).2
       calc
         abs (a-c) * b ≤ d * b := by gcongr
         _ ≤ d * s := by gcongr
     have hac : abs c = c := abs_of_nonneg hc
     rw [hac]
     have h2a : c * abs (t-s) ≤ B * (n*d) := by
       calc
         _ ≤ c * (n*d) := mul_le_mul_of_nonneg_left hst hc
         _ ≤ B * (n*d) := mul_le_mul_of_nonneg_right hcB (by positivity)
     have hst0 : 0 < s*t := mul_pos hs0 ht0
     have hbb : 0 < b*b := mul_pos hb hb
     have h2 : c * abs (t-s) / (s*t) ≤ B * (n*d) / (b*b) := by
       apply (div_le_div_iff₀ hst0 hbb).2
       calc
         (c * abs (t-s)) * (b*b) ≤ (B*(n*d))*(b*b) := by gcongr
         _ ≤ (B*(n*d))*(s*t) := by
           have hh : b*b ≤ s*t := by nlinarith
           exact mul_le_mul_of_nonneg_left hh (by positivity)
     linarith
   _ = (1/b + B*n/(b*b))*d := by ring

/-- Normalised version of `finite_lipschitz_bumps`.  We record one common
constant for all coefficients; the geometry of the endpoint then only has
to make the coloured copies close enough compared with this number. -/
theorem finite_lipschitz_partition
    {J X : Type*} [Fintype J]
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    (V : J → Set X) (ho : ∀ j, IsOpen (V j))
    (hc : ∀ x : X, ∃ j, x ∈ V j) :
  ∃ r : J → C(X, ℝ), ∃ C : NNReal,
    (∀ j, LipschitzWith C (r j)) ∧
    (∀ j x, 0 ≤ r j x) ∧
    (∀ j x, x ∉ V j → r j x = 0) ∧
    (∀ x, ∑ j : J, r j x = 1) := by
 classical
 rcases finite_lipschitz_bumps V ho hc with
   ⟨w,b,B,hb,hB,hLip,hnon,hout,hlo,hhi⟩
 let S : X → ℝ := fun x => ∑ j : J, w j x
 let R : J → X → ℝ := fun j x => w j x / S x
 let cc : ℝ := 1 / b + B * (Fintype.card J : ℝ) / (b*b)
 have hcc : 0 ≤ cc := by dsimp [cc]; positivity
 let Cp : NNReal := ⟨cc, hcc⟩
 have hSLip_aux : ∀ A : Finset J,
      LipschitzWith (A.card : NNReal)
        (fun x : X => ∑ j ∈ A, w j x) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      simpa using (LipschitzWith.const (α := X) (β := ℝ) 0)
    | @insert a A ha hA =>
      have hh := (hLip a).add hA
      simpa [Finset.sum_insert ha, ha,
        Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
          using hh
 have hSLip : LipschitzWith (Fintype.card J : NNReal) S := by
    simpa [S] using hSLip_aux (Finset.univ : Finset J)
 have hRLip : ∀ j, LipschitzWith Cp (R j) := by
   intro j
   apply LipschitzWith.of_dist_le_mul
   intro x y
   have hwx := (hLip j).dist_le_mul x y
   have hsxy := hSLip.dist_le_mul x y
   norm_num at hwx
   have hbX : b ≤ S x := hlo x
   have hbY : b ≤ S y := hlo y
   have hcY : w j y ≤ B := le_trans
     (Finset.single_le_sum (fun i _ => hnon i y) (Finset.mem_univ j)) (hhi y)
   have est := __LipschitzWeights_real_bound (w j x) (w j y) (S x) (S y)
      b B (Fintype.card J : ℝ) (dist x y)
      hb hbX hbY (hnon _ _) hcY (by positivity) hB (dist_nonneg)
      (by simpa [Real.dist_eq] using hwx) (by
         simpa [Real.dist_eq, abs_sub_comm] using hsxy)
   change dist (R j x) (R j y) ≤ (Cp : ℝ) * dist x y
   change abs (w j x / S x - w j y / S y) ≤ (Cp : ℝ) * dist x y
   exact est
 let rr : J → C(X, ℝ) := fun j =>
   { toFun := R j,
     continuous_toFun := (hRLip j).continuous }
 refine ⟨rr, Cp, ?_, ?_, ?_, ?_⟩
 · intro j
   exact hRLip j
 · intro j x
   dsimp [rr, R, S]
   exact div_nonneg (hnon _ _) (le_of_lt (lt_of_lt_of_le hb (hlo x)))
 · intro j x hx
   dsimp [rr, R, S]
   rw [hout j x hx, zero_div]
 · intro x
   have hs0 : S x ≠ 0 := ne_of_gt (lt_of_lt_of_le hb (hlo x))
   change (∑ j : J, w j x / S x) = 1
   rw [← Finset.sum_div]
   simpa [S, hs0]
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/LipschitzWeights.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/LowDim.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
/-- Convex hull of any nonempty finite subset of a line is its extremal segment.
Expressed for the ambient line of `Fin 1 → ℝ`; this avoids choosing coordinates in
later low-dimensional branches. -/
lemma convexHull_fin1_eq_segment (s : Finset (Fin 1 → ℝ)) (hs : s.Nonempty) :
    ∃ l r : Fin 1 → ℝ, l ∈ s ∧ r ∈ s ∧
      convexHull ℝ (s : Set (Fin 1 → ℝ)) = segment ℝ l r := by
  classical
  let ev : (Fin 1 → ℝ) → ℝ := fun x => x 0
  have iev : Function.Injective ev := by
    intro a b h; funext i
    have : i = (0 : Fin 1) := Subsingleton.elim _ _
    simpa [this] using h
  letI : LinearOrder (Fin 1 → ℝ) := LinearOrder.lift' ev iev
  let l : Fin 1 → ℝ := s.min' hs
  let r : Fin 1 → ℝ := s.max' hs
  have hls : l ∈ s := Finset.min'_mem s hs
  have hrs : r ∈ s := Finset.max'_mem s hs
  refine ⟨l,r,hls,hrs, ?_⟩
  have hl (x : Fin 1 → ℝ) (hx : x ∈ s) : l 0 ≤ x 0 := by
    change ev l ≤ ev x
    exact Finset.min'_le s _ hx
  have hr (x : Fin 1 → ℝ) (hx : x ∈ s) : x 0 ≤ r 0 := by
    change ev x ≤ ev r
    exact Finset.le_max' s _ hx
  have hlr : l 0 ≤ r 0 := hl _ hrs
  -- the coordinate slab is exactly the segment on this line
  let slab : Set (Fin 1 → ℝ) := {x | l 0 ≤ x 0 ∧ x 0 ≤ r 0}
  have hcv : Convex ℝ slab := by
    -- preimage of an interval under the linear coordinate evaluation
    intro a ha b hb u v hu hv huv
    constructor
    · dsimp [slab] at ha hb ⊢
      have : (u • a + v • b) (0:Fin 1) = u * a 0 + v * b 0 := by simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have ga := mul_nonneg hu (sub_nonneg.mpr ha.1)
      have gb := mul_nonneg hv (sub_nonneg.mpr hb.1)
      calc
        l 0 = u * l 0 + v * l 0 := by rw [← add_mul, huv, one_mul]
        _ ≤ u * a 0 + v * b 0 := by nlinarith [ga, gb]
    · dsimp [slab] at ha hb ⊢
      have : (u • a + v • b) (0:Fin 1) = u * a 0 + v * b 0 := by simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have ga := mul_nonneg hu (sub_nonneg.mpr (sub_le_sub_left ha.2 (r 0)))
      have gb := mul_nonneg hv (sub_nonneg.mpr (sub_le_sub_left hb.2 (r 0)))
      calc
        _ ≤ u * r 0 + v * r 0 := by nlinarith [ga, gb]
        _ = r 0 := by rw [← add_mul, huv, one_mul]
  have hin : convexHull ℝ (s : Set (Fin 1 → ℝ)) ⊆ slab := by
    refine convexHull_min ?_ hcv
    intro x hx
    change x ∈ s at hx
    exact ⟨hl x hx, hr x hx⟩
  have hsegslab : segment ℝ l r = slab := by
    -- one inclusion is cheap; the other uses the scalar parameter explicitly
    ext x
    constructor
    · intro hx
      rcases hx with ⟨u,v,hu,hv,hsu,rfl⟩
      dsimp [slab]
      constructor
      · change l 0 ≤ u*l 0 + v*r 0
        have hh := mul_nonneg hv (sub_nonneg.mpr hlr)
        calc
          _ = l 0 + v * (r 0 - l 0) := by linear_combination (l 0) * hsu
          _ ≥ l 0 := le_add_of_nonneg_right hh
      · change u*l 0 + v*r 0 ≤ r 0
        have hh := mul_nonneg hu (sub_nonneg.mpr hlr)
        calc
          _ = r 0 - u * (r 0 - l 0) := by linear_combination (r 0) * hsu
          _ ≤ r 0 := sub_le_self _ hh
    · intro hx
      have hx' : l 0 ≤ x 0 ∧ x 0 ≤ r 0 := hx
      by_cases hEq : l = r
      · have hcoord : x = l := by
          apply iev
          dsimp [ev]
          have : l 0 = r 0 := congrFun hEq 0
          linarith
        subst x
        exact left_mem_segment ℝ l r
      · have pos : 0 < r 0 - l 0 := by
          have neval : l 0 ≠ r 0 := by
            intro hh
            apply hEq
            apply iev
            exact hh
          have pne := lt_of_le_of_ne hlr neval
          linarith
        let v : ℝ := (x 0 - l 0) / (r 0 - l 0)
        let u : ℝ := (r 0 - x 0) / (r 0 - l 0)
        have hv0 : 0 ≤ v := by dsimp [v]; exact div_nonneg (sub_nonneg.mpr hx'.1) (le_of_lt pos)
        have hu0 : 0 ≤ u := by dsimp [u]; exact div_nonneg (sub_nonneg.mpr hx'.2) (le_of_lt pos)
        have huv : u + v = 1 := by dsimp [u,v]; field_simp; ring
        have comb : u • l + v • r = x := by
          apply iev
          dsimp [ev]
          dsimp [u,v]
          change ((r 0 - x 0) / (r 0 - l 0)) * l 0 + ((x 0 - l 0) / (r 0 - l 0)) * r 0 = x 0
          field_simp
          ring
        exact ⟨u,v,hu0,hv0,huv,comb⟩
  apply Set.Subset.antisymm
  · intro x hx
    have hz := hin hx
    rw [hsegslab]
    exact hz
  · exact (convex_convexHull ℝ (s : Set (Fin 1 → ℝ))).segment_subset
      (subset_convexHull ℝ (s : Set (Fin 1 → ℝ)) (show (l : _) ∈ (s : Set _) from hls))
      (subset_convexHull ℝ (s : Set (Fin 1 → ℝ)) (show (r : _) ∈ (s : Set _) from hrs))
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/LowDim.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/Perturb.lean
section
namespace FamiliesProof

open Set
open scoped NNReal
lemma perturb
 {A X Y : Type*} [MetricSpace A] [MetricSpace X] [CompactSpace X]
 [MetricSpace Y] [Nonempty X]
 (s : A → (X ≃ₜ Y)) (f : A × X → Y)
 (L c : NNReal)
 (heq : ∀ a x, f (a,x) = s a x)
 (hjoint : LipschitzWith L f)
 (hinv : ∀ a, LipschitzWith L (s a).symm)
 (u : X → A) (hucont : Continuous u) (hu : LipschitzWith c u)
 (hlt : L*L*c < 1) :
 ∃ e : X ≃ₜ Y,
   (∀ x, f (u x, x) = e x) ∧
   LipschitzWith (L * max c 1) e ∧
   LipschitzWith (L / (1-L*L*c)) e.symm := by
  -- coe constants
  let h : X → Y := fun x => f (u x, x)
  have hfor : LipschitzWith (L * max c 1) h := by
    apply LipschitzWith.of_dist_le_mul
    intro x x'
    have hh := hjoint.dist_le_mul (x := (u x, x)) (y := (u x', x'))
    -- product metric max
    calc
      dist (h x) (h x') ≤ (L : ℝ) * max (dist (u x) (u x')) (dist x x') := by simpa [h, Prod.dist_eq] using hh
      _ ≤ (L : ℝ) * max ((c : ℝ) * dist x x') (1 * dist x x') :=
        mul_le_mul_of_nonneg_left
          (max_le_max (hu.dist_le_mul x x') (by simp)) L.coe_nonneg
      _ = ((L * max c 1 : NNReal) : ℝ) * dist x x' := by
        push_cast
        rw [← max_mul_of_nonneg _ _ (by exact dist_nonneg)]
        ring
  have hparam : ∀ (a b : A) (y : Y),
      dist ((s a).symm y) ((s b).symm y) ≤
        ((L:ℝ)*(L:ℝ)) * dist a b := by
    intro a b y
    let z : X := (s b).symm y
    have h1 := (hinv a).dist_le_mul y (s a z)
    have h2 := hjoint.dist_le_mul (x := (b, z)) (y := (a, z))
    have ez : s b z = y := (s b).apply_symm_apply y
    have eqza : (s a).symm (s a z) = z := (s a).symm_apply_apply z
    calc
      dist ((s a).symm y) ((s b).symm y) = dist ((s a).symm y) z := by rw [ez.symm]; dsimp [z]; rw [ (s b).symm_apply_apply]
      _ = dist ((s a).symm y) ((s a).symm (s a z)) := by rw [eqza]
      _ ≤ (L:ℝ) * dist y (s a z) := h1
      _ = (L:ℝ) * dist (s b z) (s a z) := by rw [ez]
      _ = (L:ℝ) * dist (f (b,z)) (f (a,z)) := by rw [heq, heq]
      _ ≤ (L:ℝ) * ((L:ℝ) * dist b a) := by
        have hh : dist (f (b,z)) (f (a,z)) ≤ (L:ℝ) * dist b a := by
          simpa using h2
        exact mul_le_mul_of_nonneg_left hh L.coe_nonneg
      _ = ((L:ℝ)*(L:ℝ)) * dist a b := by rw [dist_comm a b]; ring
  have hcontr : ∀ y : Y,
      ContractingWith (L*L*c) (fun x : X => (s (u x)).symm y) := by
    intro y
    refine ⟨hlt, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x x'
    calc
      dist ((s (u x)).symm y) ((s (u x')).symm y) ≤
        ((L:ℝ)*(L:ℝ)) * dist (u x) (u x') := hparam _ _ _
      _ ≤ ((L:ℝ)*(L:ℝ)) * ((c:ℝ) * dist x x') :=
         mul_le_mul_of_nonneg_left (hu.dist_le_mul x x') (by positivity)
      _ = ((L*L*c : NNReal):ℝ) * dist x x' := by push_cast; ring
  have hsur : Function.Surjective h := by
    intro y
    let g : X → X := fun x => (s (u x)).symm y
    have hg : ContractingWith (L*L*c) g := hcontr y
    let x : X := hg.fixedPoint g
    have hx : g x = x := hg.fixedPoint_isFixedPt
    refine ⟨x, ?_⟩
    dsimp [g] at hx
    have xx := congrArg (fun z : X => s (u x) z) hx
    -- hx : symm ... y = x
    have yy : s (u x) x = y := by simpa using xx.symm
    simpa [h, heq] using yy
  have hinj : Function.Injective h := by
    intro x x' hx
    have fx : (fun z : X => (s (u z)).symm (h x)) x = x := by
      dsimp [h]; rw [heq, (s _).symm_apply_apply]
    have fx' : (fun z : X => (s (u z)).symm (h x)) x' = x' := by
      have eq : h x' = h x := hx.symm
      dsimp
      rw [← eq]
      dsimp [h]; rw [heq, (s _).symm_apply_apply]
    have hc := hcontr (h x)
    exact (hc.fixedPoint_unique fx).trans (hc.fixedPoint_unique fx').symm
  let e0 : X ≃ Y := Equiv.ofBijective h ⟨hinj, hsur⟩
  have hcont : Continuous (e0 : X → Y) := by
    change Continuous h
    exact hfor.continuous
  let e : X ≃ₜ Y := e0.toHomeomorphOfContinuousClosed hcont hcont.isClosedMap
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x; rfl
  · exact hfor
  · apply LipschitzWith.of_dist_le_mul
    intro y y'
    have xx : h (e.symm y) = y := e.apply_symm_apply y
    have xx' : h (e.symm y') = y' := e.apply_symm_apply y'
    -- use triangle
    have A1 := (hinv (u (e.symm y))).dist_le_mul y y'
    have A2 := hparam (u (e.symm y)) (u (e.symm y')) y'
    have tri := dist_triangle (e.symm y) ((s (u (e.symm y))).symm y') (e.symm y')
    have id1 : (s (u (e.symm y))).symm y = e.symm y := by
       apply (s (u (e.symm y))).injective
       calc
        (s (u (e.symm y))) ((s (u (e.symm y))).symm y) = y := (s _).apply_symm_apply y
        _ = h (e.symm y) := xx.symm
        _ = (s (u (e.symm y))) (e.symm y) := heq _ _
    have id2 : (s (u (e.symm y'))).symm y' = e.symm y' := by
       apply (s (u (e.symm y'))).injective
       calc
        (s (u (e.symm y'))) ((s (u (e.symm y'))).symm y') = y' := (s _).apply_symm_apply y'
        _ = h (e.symm y') := xx'.symm
        _ = (s (u (e.symm y'))) (e.symm y') := heq _ _
    have hc : ((L*L*c : NNReal) : ℝ) < 1 := by exact_mod_cast hlt
    have hu' := hu.dist_le_mul (e.symm y) (e.symm y')
    have est : dist (e.symm y) (e.symm y') ≤
       (L:ℝ) * dist y y' + ((L*L*c : NNReal):ℝ) * dist (e.symm y) (e.symm y') := by
      calc
       _ ≤ dist (e.symm y) ((s (u (e.symm y))).symm y') +
           dist ((s (u (e.symm y))).symm y') (e.symm y') := tri
       _ = dist ((s (u (e.symm y))).symm y) ((s (u (e.symm y))).symm y') +
           dist ((s (u (e.symm y))).symm y') ((s (u (e.symm y'))).symm y') := by rw [id1, id2]
       _ ≤ (L:ℝ) * dist y y' +
           ((L:ℝ)*(L:ℝ)) * dist (u (e.symm y)) (u (e.symm y')) := add_le_add A1 A2
       _ ≤ (L:ℝ) * dist y y' + ((L:ℝ)*(L:ℝ)) * ((c:ℝ)*dist (e.symm y) (e.symm y')) :=
          by
            have hh := mul_le_mul_of_nonneg_left hu'
              (mul_nonneg L.coe_nonneg L.coe_nonneg)
            exact add_le_add (le_rfl) hh
       _ = _ := by push_cast; ring
    have denom : 0 < (1:ℝ) - ((L*L*c : NNReal):ℝ) := sub_pos.mpr hc
    have res0 : dist (e.symm y) (e.symm y') ≤
        ((L:ℝ) * dist y y') / (1-((L*L*c : NNReal):ℝ)) := by
      apply (le_div_iff₀ denom).2
      nlinarith
    have res : dist (e.symm y) (e.symm y') ≤
        (L:ℝ) / (1-((L*L*c : NNReal):ℝ)) * dist y y' := by
      convert res0 using 1 <;> ring
    convert res using 1
    push_cast
    rw [NNReal.coe_sub (by exact le_of_lt hlt)]
    push_cast
    rfl

end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/Perturb.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/BasicSimplex.lean
section
open Set
open scoped Topology
namespace FamiliesProof
open Geometry
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
-- the elementary full simplex.  Mathlib stores geometric complexes as
-- nonempty downward closed faces; deleting the empty face is part of
-- `ofErase`.
noncomputable def fullSimplex (s : Finset E)
    (hs : AffineIndependent ℝ ((↑) : s → E)) : SimplicialComplex ℝ E :=
  Geometry.SimplicialComplex.ofErase (Set.Iic s)
    (by
      intro t ht
      have ht' : t ⊆ s := ht
      let ι : t ↪ s :=
        { toFun := fun i => ⟨i.1, ht' i.2⟩
          inj' := by intro i j h; exact Subtype.ext (congrArg (fun q : s => (q : E)) h) }
      have h := hs.comp_embedding ι
      exact h)
    (isLowerSet_Iic s)
    (by
      intro t ht u hu
      have ht' : t ⊆ s := ht
      have hu' : u ⊆ s := hu
      have h := hs.convexHull_inter ht' hu'
      -- the independent--coordinates uniqueness lemma is exactly the
      -- geometric gluing axiom of a simplicial complex.
      exact h.ge)

lemma fullSimplex_faces (s : Finset E) (hs : AffineIndependent ℝ ((↑) : s → E)) :
    (fullSimplex s hs).faces = {t : Finset E | t ⊆ s ∧ t.Nonempty} := by
  ext t
  -- `ofErase` erases the empty face
  simp [fullSimplex, Geometry.SimplicialComplex.ofErase, Finset.nonempty_iff_ne_empty]

lemma fullSimplex_faces_finite (s : Finset E) (hs : AffineIndependent ℝ ((↑) : s → E)) :
    (fullSimplex s hs).faces.Finite := by
  classical
  rw [fullSimplex_faces s hs]
  -- all of them are elements of the powerset
  have : {t : Finset E | t ⊆ s ∧ t.Nonempty} ⊆
      ({t : Finset E | t ⊆ s}) := by
    intro t h; exact h.1
  exact (Set.finite_Iic s).subset this

lemma fullSimplex_space (s : Finset E) (hs : AffineIndependent ℝ ((↑) : s → E))
    (hne : s.Nonempty) :
    (fullSimplex s hs).space = convexHull ℝ (s : Set E) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases (Geometry.SimplicialComplex.mem_space_iff).1 hx with ⟨t, ht, hxt⟩
    have hts : t ⊆ s := ((by simpa [fullSimplex_faces s hs] using ht) : t ⊆ s ∧ t.Nonempty).1
    exact (convexHull_mono (by exact_mod_cast hts)) hxt
  · exact (Geometry.SimplicialComplex.convexHull_subset_space
       (K := fullSimplex s hs)
       (by rw [fullSimplex_faces]; exact ⟨Finset.Subset.rfl, hne⟩))
end FamiliesProof


end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/BasicSimplex.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/HullCard.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A finite hull which is neither a point nor a genuine segment has at least three
listed vertices. No independence of the presentation is needed; this is often a
convenient reduction before chamber induction. The nontriviality is phrased on the
subtype to match the parameter polytope. -/
lemma three_le_card_of_nontrivial_nosegment
    (s : Finset E)
    (hne : Nonempty {x : E // x ∈ convexHull ℝ (s : Set E)})
    (hntr : Nontrivial {x : E // x ∈ convexHull ℝ (s : Set E)})
    (hseg : ¬ ∃ l r : E, l ≠ r ∧ convexHull ℝ (s : Set E) = segment ℝ l r) :
    3 ≤ s.card := by
  classical
  have spos : 0 < s.card := by
    have hset : ((s : Set E)).Nonempty :=
      (convexHull_nonempty_iff).1 ⟨hne.some.1, hne.some.property⟩
    exact Finset.card_pos.mpr (by simpa using hset)
  by_contra hlt
  have cle : s.card ≤ 2 := by omega
  have cases12 : s.card = 1 ∨ s.card = 2 := by omega
  rcases cases12 with h | h
  · obtain ⟨z, hs⟩ := Finset.card_eq_one.mp h
    subst s
    have sub : Subsingleton {x : E // x ∈ convexHull ℝ (({z} : Finset E) : Set E)} := by
      constructor
      intro a b
      apply Subtype.ext
      have aa : (a:E) = z := by
        have hh := a.property
        simpa [convexHull_singleton] using hh
      have bb : (b:E) = z := by
        have hh := b.property
        simpa [convexHull_singleton] using hh
      exact aa.trans bb.symm
    exact (not_subsingleton_iff_nontrivial.mpr hntr) sub
  · obtain ⟨l,r,lr, hs⟩ := Finset.card_eq_two.mp h
    subst s
    apply hseg
    refine ⟨l,r,lr,?_⟩
    simpa using (convexHull_pair (𝕜:=ℝ) l r)

end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/HullCard.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/FiniteHullReduction.lean
section
open Set
open scoped Topology
namespace FamiliesProof
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- Erasing a vertex which is already in the convex hull does not change a finite hull.
We keep the statement for `Finset`s: it is the small induction step needed before any
triangulation argument. -/
lemma convexHull_erase_eq (s : Finset E) (v : E)
    (hv : v ∈ convexHull ℝ ((s.erase v : Finset E) : Set E)) :
    convexHull ℝ ((s.erase v : Finset E) : Set E) = convexHull ℝ (s : Set E) := by
  classical
  apply Set.Subset.antisymm
  · exact convexHull_mono (by
      intro x hx
      have hx' : x ∈ s.erase v := hx
      exact (Finset.erase_subset v s) hx')
  · apply convexHull_min
    · intro x hx
      have hxs : x ∈ s := hx
      by_cases h : x = v
      · simpa [h] using hv
      · exact subset_convexHull ℝ (E := E) ((s.erase v : Finset E) : Set E)
          (by
            change x ∈ s.erase v
            exact Finset.mem_erase.mpr ⟨h, hxs⟩)
    · exact convex_convexHull ℝ ((s.erase v : Finset E) : Set E)

/-- One can remove redundant points from a finite spanning set.  The terminal
finite set is in convex position (none of its vertices belongs to the hull
of the other ones).  This considerably isolates the genuine ``polytope''
triangulation step: affine dependences caused by interior points cost
nothing. -/
lemma finiteHull_reduce (s : Finset E) :
    ∃ t : Finset E, t ⊆ s ∧
      convexHull ℝ (t : Set E) = convexHull ℝ (s : Set E) ∧
      ∀ v ∈ t, v ∉ convexHull ℝ ((t.erase v : Finset E) : Set E) := by
  classical
  -- Well founded induction by strict inclusion.  Notice that the statement
  -- remembers inclusion in the original finite set; this is what lets the
  -- IH compose without changing the hull a second time.
  induction s using Finset.strongInduction with
  | _ s ih =>
    by_cases red : ∃ v ∈ s,
        v ∈ convexHull ℝ ((s.erase v : Finset E) : Set E)
    · rcases red with ⟨v, hvS, hv⟩
      have hss : s.erase v ⊂ s := Finset.erase_ssubset hvS
      rcases ih (s.erase v) hss with ⟨t, ht, hHull, hirr⟩
      refine ⟨t, ?_, ?_, hirr⟩
      · exact ht.trans (Finset.erase_subset _ _)
      · exact hHull.trans (convexHull_erase_eq s v hv)
    · push_neg at red
      exact ⟨s, Finset.Subset.rfl, rfl, red⟩

/-- If the irredundant set furnished above is an independent set then no
actual triangulation is needed: the full simplex of its faces is already a
finite geometric complex.  The empty case is kept separate because the
geometric complex erases its empty face. -/
lemma finiteHull_of_irredundant_independent (s : Finset E)
    (hs : AffineIndependent ℝ ((↑) : s → E)) :
    ∃ K : Geometry.SimplicialComplex ℝ E,
      K.faces.Finite ∧ K.space = convexHull ℝ (s : Set E) := by
  classical
  by_cases hne : s.Nonempty
  · exact ⟨fullSimplex s hs, fullSimplex_faces_finite s hs,
      fullSimplex_space s hs hne⟩
  · have h0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst s
    refine ⟨(⊥ : Geometry.SimplicialComplex ℝ E), ?_, ?_⟩
    · rw [Geometry.SimplicialComplex.faces_bot]
      exact Set.finite_empty
    · simp [Geometry.SimplicialComplex.space_bot,
        convexHull_empty]

/-- The finite-hull problem is completely reduced to the honestly hard
case of a polytope all of whose chosen points are exposed as vertices.  In
particular insertions of points which were already in a previous simplex do
not require a subdivision.  This quantified form is useful: later a
triangulation theorem need only address convex-position configurations. -/
lemma finiteHull_reduction_to_convexPosition :
    ( (∀ s : Finset E,
        (∀ v ∈ s, v ∉ convexHull ℝ ((s.erase v : Finset E) : Set E)) →
        ∃ K : Geometry.SimplicialComplex ℝ E,
          K.faces.Finite ∧ K.space = convexHull ℝ (s : Set E)) ) →
      ∀ s : Finset E,
        ∃ K : Geometry.SimplicialComplex ℝ E,
          K.faces.Finite ∧ K.space = convexHull ℝ (s : Set E) := by
  classical
  intro h s
  obtain ⟨t, ht, heq, hirr⟩ := finiteHull_reduce (E:=E) s
  obtain ⟨K, hfin, hsp⟩ := h t hirr
  exact ⟨K, hfin, hsp.trans heq⟩

end FamiliesProof

namespace FamiliesProof
open Set
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]
/-- The elementary Carathéodory cover is finite.  Its members are genuine
simplices; no complex/gluing assertion is hidden in this statement. -/
def candidateFaces (s : Finset E) : Set (Finset E) :=
  {t | t ⊆ s ∧ t.Nonempty ∧ AffineIndependent ℝ ((↑) : t → E)}

lemma candidateFaces_finite (s : Finset E) : (candidateFaces s).Finite := by
  classical
  refine (Set.finite_Iic s).subset ?_
  intro t ht
  exact ht.1

lemma candidateFaces_down {s t u : Finset E} (ht : t ∈ candidateFaces (E:=E) s)
    (hu : u ⊆ t) (hne : u.Nonempty) : u ∈ candidateFaces (E:=E) s := by
  classical
  refine ⟨hu.trans ht.1, hne, ?_⟩
  let emb : u ↪ t :=
    { toFun := fun i => ⟨i, hu i.property⟩
      inj' := by intro i j h; exact Subtype.ext (congrArg (fun x : t => (x:E)) h) }
  exact ht.2.2.comp_embedding emb

/-- Carathéodory gives a finite cover by independent simplices.  The missing
piece in turning this cover into a subdivision is precisely the geometric
intersection axiom; overlapping simplices have not been smuggled in as a
complex. -/
lemma iUnion_candidateFaces (s : Finset E) :
    (⋃ t ∈ candidateFaces (E:=E) s, convexHull ℝ (t : Set E)) =
      convexHull ℝ (s : Set E) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨t, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨ht, hxt⟩
    exact (convexHull_mono (by exact_mod_cast (ht.1 : t ⊆ s))) hxt
  · intro x hx
    rw [convexHull_eq_union] at hx
    rcases Set.mem_iUnion.mp hx with ⟨t, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hts, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hi, hxt⟩
    have hne : t.Nonempty := by
      have hn : (convexHull ℝ (t : Set E)).Nonempty := ⟨x, hxt⟩
      have hsn : (t : Set E).Nonempty := convexHull_nonempty_iff.mp hn
      simpa using hsn
    have hface : t ∈ candidateFaces (E:=E) s := by
      refine ⟨?_, hne, hi⟩
      -- coercion in Carathéodory's index is a set-subset
      intro y hy
      exact hts hy
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨hface, hxt⟩⟩
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/FiniteHullReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/LexTriangulation.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fixed, completely arbitrary, ordering of a finite configuration. Nothing in the
triangulation depends on which one is used. -/
noncomputable def configEquiv (s : Finset E) : s ≃ Fin s.card := by
  classical
  have e := Trunc.out (Fintype.truncEquivFin s)
  simpa using e
noncomputable def configOrder (s : Finset E) : LinearOrder s :=
  LinearOrder.lift' (configEquiv s) (configEquiv s).injective

/-- The first nonzero coordinate of a vector on a finite configuration is positive. -/
def LexPositive (s : Finset E) (d : s → ℝ) : Prop :=
  letI : LinearOrder s := configOrder s
  ∃ i : s, 0 < d i ∧ ∀ j : s, j < i → d j = 0

lemma lexPositive_ne_zero {s : Finset E} {d : s → ℝ}
    (h : LexPositive s d) : d ≠ 0 := by
  rcases h with ⟨i, hi, _⟩
  intro hz
  have : d i = 0 := congrFun hz i
  linarith

lemma lexPositive_or_neg {s : Finset E} (d : s → ℝ)
    (hne : d ≠ 0) :
    LexPositive s d ∨ LexPositive s (fun i => - d i) := by
  classical
  -- install the same (chosen once) finite order as in the definition
  letI : LinearOrder s := configOrder s
  have hex : ∃ i : s, d i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  let T : Finset s := Finset.univ.filter (fun i => d i ≠ 0)
  have hT : T.Nonempty := by
    rcases hex with ⟨i, hi⟩
    exact ⟨i, by simp [T, hi]⟩
  let i : s := T.min' hT
  have hiT : i ∈ T := Finset.min'_mem T hT
  have hi0 : d i ≠ 0 := (Finset.mem_filter.mp hiT).2
  have hbefore : ∀ j : s, j < i → d j = 0 := by
    intro j hj
    by_contra hz
    have hjT : j ∈ T := by simp [T, hz]
    have hle : i ≤ j := Finset.min'_le T j hjT
    exact (not_le_of_gt hj) hle
  by_cases hp : 0 < d i
  · left; exact ⟨i, hp, hbefore⟩
  · right
    have hn : d i < 0 := lt_of_le_of_ne (le_of_not_gt hp) hi0
    exact ⟨i, by linarith, fun j hj => by simp [hbefore j hj]⟩

/-- A vector tangent to a fibre of convex coefficients. -/
def coeffDirection (s : Finset E) (d : s → ℝ) : Prop :=
  (∑ i, d i = 0) ∧ (∑ i, d i • (i:E) = 0)
/-- instantaneous feasibility at the zero coordinates of a support. -/
def outsideNonneg (t : Finset E) {s : Finset E} (d : s → ℝ) : Prop :=
  ∀ i : s, (i:E) ∉ t → 0 ≤ d i
/-- The lexicographic (pulling) faces.  This definition, in terms of coefficients
rather than pictures of crossing simplices, is often a convenient route to the
finite-hull triangulation. -/
def lexFace (s t : Finset E) : Prop :=
  t ⊆ s ∧ ¬ ∃ d : s → ℝ,
      coeffDirection s d ∧ LexPositive s d ∧ outsideNonneg t d

lemma lexFace_down {s t u : Finset E} (ht : lexFace s t)
    (hu : u ⊆ t) : lexFace s u := by
  classical
  refine ⟨hu.trans ht.1, ?_⟩
  rintro ⟨d, hd, hp, hn⟩
  apply ht.2
  refine ⟨d, hd, hp, ?_⟩
  intro i hi
  exact hn i (fun hit => hi (hu hit))

/- A short, and useful independent lemma: a lexicographically preferred support
cannot carry an affine dependence. This is the first place where the coefficient
definition removes the crossing-simplexes obstruction in the naive Caratheodory
cover. -/
lemma lexFace_independent {s t : Finset E} (ht : lexFace s t) :
    AffineIndependent ℝ ((↑) : t → E) := by
  classical
  -- use the finite-support characterization; its weights are already indexed by an
  -- arbitrary sub-finset of `t`.
  rw [affineIndependent_iff]
  intro u w hw hwv i hi
  by_contra hwi
  -- extend those finitely supported weights by zero first to `t`, and then to `s`.
  -- Writing the two extensions explicitly keeps all sums finite, so no topology is
  -- involved in this lemma.
  let wt : t → ℝ := fun a => if ha : a ∈ u then w a else 0
  let d : s → ℝ := fun a =>
    if ha : (a:E) ∈ t then wt ⟨a, ha⟩ else 0
  have hatt : (t.attach : Finset t) = Finset.univ := by ext; simp
  have hsum_t : (∑ a : t, wt a) = ∑ a ∈ u, w a := by
    classical
    -- indicator over the full finset of the subtype
    have hu : u ⊆ (Finset.univ : Finset t) := Finset.subset_univ _
    classical
    calc
      (∑ a : t, wt a) = ∑ a ∈ (Finset.univ : Finset t),
          (if h : a ∈ u then w a else 0) := by rfl
      _ = ∑ a ∈ u, w a := by
        -- split the indicator sum by its filter
        classical
        simp
        rw [hatt, Finset.univ_inter]
  have hsumv_t : (∑ a : t, wt a • (a:E)) = ∑ a ∈ u, w a • (a:E) := by
    classical
    calc
      _ = ∑ a ∈ (Finset.univ : Finset t),
          (if h : a ∈ u then w a else 0) • (a:E) := by rfl
      _ = _ := by
        simp
        rw [hatt, Finset.univ_inter]
  have hsum_s : (∑ a : s, d a) = ∑ a : t, wt a := by
    classical
    let g : E → ℝ := fun a => if h : a ∈ t then wt ⟨a,h⟩ else 0
    have hd (a : s) : d a = g a := rfl
    have hg (a : t) : g (a:E) = wt a := by simp [g]
    calc
      (∑ a : s, d a) = ∑ a : s, g a := by simp_rw [hd]
      _ = ∑ a ∈ s.attach, g (a:E) := by rfl
      _ = ∑ a ∈ s, g a := Finset.sum_attach s g
      _ = ∑ a ∈ t, g a :=
        (Finset.sum_subset ht.1 (by
          intro a ha hb; simp [g, hb])).symm
      _ = ∑ a ∈ t.attach, g (a:E) := (Finset.sum_attach t g).symm
      _ = ∑ a : t, wt a := by
        change (∑ a : t, g (a:E)) = _
        simp_rw [hg]
  have hsumv_s : (∑ a : s, d a • (a:E)) = ∑ a : t, wt a • (a:E) := by
    classical
    let g : E → E := fun a => if h : a ∈ t then wt ⟨a,h⟩ • a else 0
    have hd (a : s) : d a • (a:E) = g a := by
      by_cases h : (a:E) ∈ t <;> simp [d, g, h]
    have hg (a : t) : g (a:E) = wt a • (a:E) := by simp [g]
    calc
      (∑ a : s, d a • (a:E)) = ∑ a : s, g a := by simp_rw [hd]
      _ = ∑ a ∈ s.attach, g (a:E) := by rfl
      _ = ∑ a ∈ s, g a := Finset.sum_attach s g
      _ = ∑ a ∈ t, g a :=
        (Finset.sum_subset ht.1 (by
          intro a ha hb; simp [g, hb])).symm
      _ = ∑ a ∈ t.attach, g (a:E) := (Finset.sum_attach t g).symm
      _ = ∑ a : t, wt a • (a:E) := by
        change (∑ a : t, g (a:E)) = _
        simp_rw [hg]
  have hdir : coeffDirection s d := by
    constructor
    · rw [hsum_s, hsum_t]
      exact hw
    · rw [hsumv_s, hsumv_t]
      exact hwv
  have hdnz : d ≠ 0 := by
    intro hz
    have hz_i := congrFun hz (⟨(i:E), ht.1 (show (i:E) ∈ t from i.property)⟩ : s)
    have wi : w i = 0 := by
      simpa [d, wt, i.property, hi] using hz_i
    exact hwi wi
  rcases lexPositive_or_neg d hdnz with hp | hp
  · exact (ht.2 ⟨d, hdir, hp, by
        intro a ha
        simp [d, ha]⟩).elim
  · let dn : s → ℝ := fun a => - d a
    have hdirn : coeffDirection s dn := by
      constructor
      · simpa [dn, Finset.sum_neg_distrib] using congrArg Neg.neg hdir.1
      · have : -(∑ a : s, d a • (a:E)) = (0:E) := by rw [hdir.2, neg_zero]
        simpa [dn, ← Finset.sum_neg_distrib] using this
    exact (ht.2 ⟨dn, hdirn, hp, by
        intro a ha
        simp [dn, d, ha]⟩).elim

end
end FamiliesProof

namespace FamiliesProof
open Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def lexFaces (s : Finset E) : Set (Finset E) := {t | lexFace s t}
lemma lexFaces_finite (s : Finset E) : (lexFaces s).Finite := by
  classical
  refine (Set.finite_Iic s).subset ?_
  intro t ht
  exact ht.1
lemma lexFaces_lower (s : Finset E) : IsLowerSet (lexFaces s) := by
  intro a b hba ha
  exact lexFace_down ha hba

/-- Two lexicographically selected supports have compatible hulls.  If a point has
two convex representations on selected supports, extend their weights by zero to
the ambient configuration.  Their difference is a direction in the coefficient
fibre; the first nonzero coordinate would be feasible from one of the two supports.
The defining extremality of a `lexFace` therefore forces the two coefficient
vectors to be equal. -/
lemma lexFace_inter {s a b : Finset E} (ha : lexFace s a) (hb : lexFace s b) :
    convexHull ℝ (a : Set E) ∩ convexHull ℝ (b : Set E) ⊆
      convexHull ℝ (a ∩ b : Set E) := by
  classical
  intro x hx
  rcases (Finset.mem_convexHull' (R := ℝ) (s:=a) (x:=x)).1 hx.1 with
    ⟨wa, hwa, hwas, hwax⟩
  rcases (Finset.mem_convexHull' (R := ℝ) (s:=b) (x:=x)).1 hx.2 with
    ⟨wb, hwb, hwbs, hwbx⟩
  let ca : s → ℝ := fun i => if h : (i : E) ∈ a then wa (i:E) else 0
  let cb : s → ℝ := fun i => if h : (i : E) ∈ b then wb (i:E) else 0
  have hsum_ca : (∑ i : s, ca i) = ∑ y ∈ a, wa y := by
    classical
    let g : E → ℝ := fun y => if h : y ∈ a then wa y else 0
    have hc (i : s) : ca i = g (i:E) := rfl
    calc
      (∑ i : s, ca i) = ∑ i : s, g (i:E) := by simp_rw [hc]
      _ = ∑ i ∈ s.attach, g (i:E) := by rfl
      _ = ∑ i ∈ s, g i := Finset.sum_attach s g
      _ = ∑ i ∈ a, g i := (Finset.sum_subset ha.1 (by
        intro i hi hik
        simp [g, hik])).symm
      _ = ∑ i ∈ a, wa i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [g, hi]
  have hsum_cb : (∑ i : s, cb i) = ∑ y ∈ b, wb y := by
    classical
    let g : E → ℝ := fun y => if h : y ∈ b then wb y else 0
    have hc (i : s) : cb i = g (i:E) := rfl
    calc
      (∑ i : s, cb i) = ∑ i : s, g (i:E) := by simp_rw [hc]
      _ = ∑ i ∈ s.attach, g (i:E) := by rfl
      _ = ∑ i ∈ s, g i := Finset.sum_attach s g
      _ = ∑ i ∈ b, g i := (Finset.sum_subset hb.1 (by
        intro i hi hik
        simp [g, hik])).symm
      _ = ∑ i ∈ b, wb i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [g, hi]
  have hsumv_ca : (∑ i : s, ca i • (i:E)) = ∑ y ∈ a, wa y • y := by
    classical
    let g : E → E := fun y => if h : y ∈ a then wa y • y else 0
    have hc (i : s) : ca i • (i:E) = g (i:E) := by
      by_cases h : (i:E) ∈ a <;> simp [ca, g, h]
    calc
      (∑ i : s, ca i • (i:E)) = ∑ i : s, g (i:E) := by simp_rw [hc]
      _ = ∑ i ∈ s.attach, g (i:E) := by rfl
      _ = ∑ i ∈ s, g i := Finset.sum_attach s g
      _ = ∑ i ∈ a, g i := (Finset.sum_subset ha.1 (by
        intro i hi hik
        simp [g, hik])).symm
      _ = ∑ i ∈ a, wa i • i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [g, hi]
  have hsumv_cb : (∑ i : s, cb i • (i:E)) = ∑ y ∈ b, wb y • y := by
    classical
    let g : E → E := fun y => if h : y ∈ b then wb y • y else 0
    have hc (i : s) : cb i • (i:E) = g (i:E) := by
      by_cases h : (i:E) ∈ b <;> simp [cb, g, h]
    calc
      (∑ i : s, cb i • (i:E)) = ∑ i : s, g (i:E) := by simp_rw [hc]
      _ = ∑ i ∈ s.attach, g (i:E) := by rfl
      _ = ∑ i ∈ s, g i := Finset.sum_attach s g
      _ = ∑ i ∈ b, g i := (Finset.sum_subset hb.1 (by
        intro i hi hik
        simp [g, hik])).symm
      _ = ∑ i ∈ b, wb i • i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [g, hi]
  let d : s → ℝ := fun i => cb i - ca i
  have hdir : coeffDirection s d := by
    constructor
    · -- scalar sums
      change (∑ i : s, (cb i - ca i)) = 0
      -- use sum_sub_distrib on univ simp?
      rw [Finset.sum_sub_distrib]
      rw [hsum_cb, hsum_ca, hwbs, hwas]
      simp
    · -- vector sums
      change (∑ i : s, (cb i - ca i) • (i:E)) = 0
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib]
      rw [hsumv_cb, hsumv_ca, hwbx, hwax]
      simp
  have hout_a : outsideNonneg a d := by
    intro i hi
    by_cases hib : (i:E) ∈ b
    · have h := hwb (i:E) hib
      simpa [d, ca, cb, hi, hib] using h
    · simp [d, ca, cb, hi, hib]
  let dn : s → ℝ := fun i => - d i
  have hdirn : coeffDirection s dn := by
    constructor
    · -- neg scalar sum
      simpa [dn, Finset.sum_neg_distrib] using congrArg Neg.neg hdir.1
    · have hh : -(∑ i : s, d i • (i:E)) = (0:E) := by rw [hdir.2, neg_zero]
      -- convert
      simpa [dn, ← Finset.sum_neg_distrib] using hh
  have hout_b : outsideNonneg b dn := by
    intro i hi
    by_cases hia : (i:E) ∈ a
    · have h := hwa (i:E) hia
      simpa [dn, d, ca, cb, hi, hia] using h
    · simp [dn, d, ca, cb, hi, hia]
  have hz : d = 0 := by
    by_contra hn
    rcases lexPositive_or_neg d hn with hp | hp
    · exact (ha.2 ⟨d, hdir, hp, hout_a⟩)
    · exact (hb.2 ⟨dn, hdirn, hp, hout_b⟩)
  have hvanish : ∀ y ∈ a, y ∉ b → wa y = 0 := by
    intro y hya hyb
    let iy : s := ⟨y, ha.1 hya⟩
    have hh := congrFun hz iy
    have hh' : (cb iy - ca iy : ℝ) = 0 := by simpa [d] using hh
    simpa [ca, cb, iy, hya, hyb] using hh'
  have hxint : x ∈ convexHull ℝ ((↑(a ∩ b)) : Set E) := by
    refine (Finset.mem_convexHull' (R := ℝ) (s := a ∩ b) (x:=x)).2 ?_
    refine ⟨wa, ?_, ?_, ?_⟩
    · intro y hy
      have hya : y ∈ a := (Finset.mem_inter.mp hy).1
      exact hwa y hya
    · calc
        (∑ y ∈ a ∩ b, wa y) = ∑ y ∈ a, wa y :=
          Finset.sum_subset Finset.inter_subset_left (by
            intro y hya hyab
            apply hvanish y hya
            intro hyb
            exact hyab (Finset.mem_inter.mpr ⟨hya, hyb⟩))
        _ = 1 := hwas
    · calc
        (∑ y ∈ a ∩ b, wa y • y) = ∑ y ∈ a, wa y • y :=
          Finset.sum_subset Finset.inter_subset_left (by
            intro y hya hyab
            have hv := hvanish y hya (by
              intro hyb
              exact hyab (Finset.mem_inter.mpr ⟨hya, hyb⟩))
            simp [hv])
        _ = x := hwax
  simpa using hxint


/-- The intersection axiom for all lexicographically selected supports. -/
lemma lexFaces_inter (s : Finset E) :
    ∀ᵉ (a ∈ lexFaces s) (b ∈ lexFaces s),
      convexHull ℝ (a : Set E) ∩ convexHull ℝ (b : Set E) ⊆
        convexHull ℝ (a ∩ b : Set E) := by
  intro a ha b hb
  exact lexFace_inter ha hb

/-- Once the intersection statement for coefficient supports is known, the
coefficient complex is already a genuine finite geometric complex. Isolating
this constructor is useful: it is the intersection statement, not mere
Caratheodory coverage, that a triangulation needs. -/
noncomputable def lexComplex (s : Finset E)
    (hinter : ∀ᵉ (a ∈ lexFaces s) (b ∈ lexFaces s),
      convexHull ℝ (a : Set E) ∩ convexHull ℝ (b : Set E) ⊆
        convexHull ℝ (a ∩ b : Set E)) :
    Geometry.SimplicialComplex ℝ E :=
  Geometry.SimplicialComplex.ofErase (lexFaces s)
    (by
      intro a ha
      exact lexFace_independent ha)
    (lexFaces_lower s) hinter
lemma lexComplex_faces (s : Finset E)
    (hinter : ∀ᵉ (a ∈ lexFaces s) (b ∈ lexFaces s),
      convexHull ℝ (a : Set E) ∩ convexHull ℝ (b : Set E) ⊆
        convexHull ℝ (a ∩ b : Set E)) :
    (lexComplex s hinter).faces = {t | lexFace s t ∧ t.Nonempty} := by
  ext t
  simp [lexComplex, lexFaces, Geometry.SimplicialComplex.ofErase,
    Finset.nonempty_iff_ne_empty]
lemma lexComplex_faces_finite (s : Finset E)
    (hinter : ∀ᵉ (a ∈ lexFaces s) (b ∈ lexFaces s),
      convexHull ℝ (a : Set E) ∩ convexHull ℝ (b : Set E) ⊆
        convexHull ℝ (a ∩ b : Set E)) :
    (lexComplex s hinter).faces.Finite := by
  rw [lexComplex_faces s hinter]
  exact (lexFaces_finite s).subset (by intro t ht; exact ht.1)
lemma lexComplex_space (s : Finset E)
    (hinter : ∀ᵉ (a ∈ lexFaces s) (b ∈ lexFaces s),
      convexHull ℝ (a : Set E) ∩ convexHull ℝ (b : Set E) ⊆
        convexHull ℝ (a ∩ b : Set E))
    (hcover : ∀ x ∈ convexHull ℝ (s : Set E),
      ∃ t : Finset E, lexFace s t ∧ t.Nonempty ∧
        x ∈ convexHull ℝ (t : Set E)) :
    (lexComplex s hinter).space = convexHull ℝ (s : Set E) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases (Geometry.SimplicialComplex.mem_space_iff).1 hx with ⟨t, ht, hxt⟩
    have good : lexFace s t :=
      ((by simpa [lexComplex_faces s hinter] using ht) : lexFace s t ∧ t.Nonempty).1
    exact (convexHull_mono (by exact_mod_cast good.1)) hxt
  · intro x hx
    rcases hcover x hx with ⟨t, ht, hn, hxt⟩
    exact (Geometry.SimplicialComplex.mem_space_iff).2
      ⟨t, by rw [lexComplex_faces]; exact ⟨ht, hn⟩, hxt⟩

end
end FamiliesProof


open Set
open scoped BigOperators Topology
noncomputable section
namespace FamiliesProof

def listLex {σ : Type*} (l : List σ) (u v : σ → ℝ) : Prop :=
  match l with
  | [] => False
  | i :: l => v i < u i ∨ (u i = v i ∧ listLex l u v)

lemma exists_listLex_max {σ : Type*} [Fintype σ]
    (l : List σ) {K : Set (σ → ℝ)} (hc : IsCompact K) (hn : K.Nonempty) :
    ∃ c ∈ K, ∀ z ∈ K, ¬ listLex l z c := by
  induction l generalizing K with
  | nil =>
      rcases hn with ⟨c, hc⟩
      refine ⟨c, hc, ?_⟩
      intro z hz
      simp [listLex]
  | cons i l ih =>
      obtain ⟨m, hm, hmax⟩ :=
        hc.exists_isMaxOn hn (continuous_apply i).continuousOn
      let K' : Set (σ → ℝ) := K ∩ {z | z i = m i}
      have hclosed : IsClosed {z : σ → ℝ | z i = m i} :=
        isClosed_eq (continuous_apply i) continuous_const
      have hcomp : IsCompact K' := hc.inter_right hclosed
      have hne : K'.Nonempty := ⟨m, hm, by rfl⟩
      obtain ⟨c, hcmem, hcg⟩ := ih hcomp hne
      refine ⟨c, hcmem.1, ?_⟩
      intro z hz hp
      change c i < z i ∨ (z i = c i ∧ listLex l z c) at hp
      rcases hp with hp | ⟨heq, htail⟩
      · have hzle : z i ≤ m i := hmax hz
        have hci : c i = m i := hcmem.2
        exact (not_lt_of_ge (hci ▸ hzle)) hp
      · apply (hcg z ?_) htail
        refine ⟨hz, ?_⟩
        exact heq.trans hcmem.2
end FamiliesProof
namespace FamiliesProof

lemma listLex_of_witness {σ : Type*} [LinearOrder σ]
    (L : List σ) (hs : L.Pairwise (fun a b => a ≤ b))
    (hnd : L.Nodup) {u v : σ → ℝ} (i : σ) (hi : i ∈ L)
    (hp : v i < u i) (hz : ∀ j : σ, j < i → u j = v j) :
    listLex L u v := by
  induction L with
  | nil => simp at hi
  | cons h t ih =>
      have hs' := (List.pairwise_cons.mp hs)
      have hn' := (List.nodup_cons.mp hnd)
      rcases (List.mem_cons.mp hi) with he | hit
      · subst i
        change v h < u h ∨ (u h = v h ∧ listLex t u v)
        exact Or.inl hp
      · have hle : h ≤ i := hs'.1 i hit
        have hne : h ≠ i := by
          intro hEq
          subst i
          exact hn'.1 hit
        have hlt : h < i := lt_of_le_of_ne hle hne
        have heq : u h = v h := hz h hlt
        change v h < u h ∨ (u h = v h ∧ listLex t u v)
        exact Or.inr ⟨heq, ih hs'.2 hn'.2 hit⟩
end FamiliesProof
namespace FamiliesProof
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma exists_no_lexpositive {s : Finset E} {K : Set (s → ℝ)}
    (hc : IsCompact K) (hn : K.Nonempty) :
    ∃ c ∈ K, ∀ z ∈ K, ¬ LexPositive s (fun i => z i - c i) := by
  classical
  letI : LinearOrder s := configOrder s
  let l : List s := (Finset.univ : Finset s).sort (fun i j => i ≤ j)
  obtain ⟨c, hcK, hmax⟩ := exists_listLex_max l hc hn
  refine ⟨c, hcK, ?_⟩
  intro z hz hp
  rcases hp with ⟨i, hi, hbefore⟩
  have hiL : i ∈ l := by simp [l]
  have hs : l.Pairwise (fun a b => a ≤ b) :=
    Finset.pairwise_sort (Finset.univ : Finset s) (fun a b => a ≤ b)
  have hnd : l.Nodup := Finset.sort_nodup _ _
  apply hmax z hz
  apply listLex_of_witness l hs hnd i hiL
  · dsimp at hi
    linarith
  · intro j hj
    have hzero := hbefore j hj
    dsimp at hzero
    linarith
end FamiliesProof
namespace FamiliesProof
open scoped BigOperators
lemma exists_positive_step {σ : Type*} [Fintype σ]
    (c d : σ → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hout : ∀ i, c i = 0 → 0 ≤ d i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i, 0 ≤ c i + e * d i := by
  classical
  let A : ℝ := ∑ i : σ, |d i| / c i
  have hterm : ∀ i : σ, 0 ≤ |d i| / c i := by
    intro i; exact div_nonneg (abs_nonneg _) (hc i)
  have hA : 0 ≤ A := Finset.sum_nonneg (by intro i hi; exact hterm i)
  let e : ℝ := 1 / (A + 1)
  have he : 0 < e := one_div_pos.mpr (by linarith)
  refine ⟨e, he, ?_⟩
  intro i
  by_cases hci : c i = 0
  · simp [hci, le_of_lt he, hout i hci]
    exact mul_nonneg (le_of_lt he) (hout i hci)
  · have hcp : 0 < c i := lt_of_le_of_ne (hc i) (Ne.symm hci)
    have hle : |d i| / c i ≤ A := by
      dsimp [A]
      -- sum over univ
      exact Finset.single_le_sum (fun j hj => hterm j) (Finset.mem_univ i)
    have hlt : |d i| / c i < A + 1 := lt_of_le_of_lt hle (by linarith)
    have eesm : e * |d i| < c i := by
      have hden : 0 < A + 1 := by linarith
      -- rewrite e
      dsimp [e]
      -- use division comparisons; `1/(A+1) * |d| < c`
      rw [one_div, inv_mul_eq_div]
      -- |d|/(A+1) < c
      apply (div_lt_iff₀ hden).2
      -- |d| < c*(A+1); from hlt
      have := (div_lt_iff₀ hcp).1 hlt
      -- this : |d| < (A+1)* c
      nlinarith
    have hlow : - |d i| ≤ d i := neg_abs_le _
    have hmul : -(e * |d i|) ≤ e * d i := by nlinarith
    linarith
end FamiliesProof
namespace FamiliesProof
open Set
open scoped BigOperators Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Lexicographically extremal coefficient vectors cover the whole finite hull. -/
lemma lexFaces_cover (s : Finset E) :
    ∀ x ∈ convexHull ℝ (s : Set E),
      ∃ t : Finset E, lexFace s t ∧ t.Nonempty ∧
        x ∈ convexHull ℝ (t : Set E) := by
  classical
  intro x hx
  rcases (Finset.mem_convexHull' (R:=ℝ) (s:=s) (x:=x)).1 hx with
    ⟨w, hw, hws, hwx⟩
  let B : (s → ℝ) → E := fun c => ∑ i : s, c i • (i:E)
  let K : Set (s → ℝ) := stdSimplex ℝ s ∩ {c | B c = x}
  have hnon : K.Nonempty := by
    let c0 : s → ℝ := fun i => w (i:E)
    refine ⟨c0, ?_, ?_⟩
    · change (∀ i, 0 ≤ c0 i) ∧ (∑ i : s, c0 i) = 1
      constructor
      · intro i; exact hw (i:E) i.property
      · calc
          (∑ i : s, c0 i) = ∑ y ∈ s, w y := Finset.sum_attach s w
          _ = 1 := hws
    · change (∑ i : s, c0 i • (i:E)) = x
      calc
        (∑ i : s, c0 i • (i:E)) = ∑ y ∈ s, w y • y :=
          Finset.sum_attach s (fun y => w y • y)
        _ = x := hwx
  have hB : Continuous B := by
    dsimp [B]
    fun_prop
  have hcomp : IsCompact K :=
    (isCompact_stdSimplex ℝ s).inter_right
      (isClosed_eq hB continuous_const)
  obtain ⟨c, hcK, hopt⟩ := exists_no_lexpositive hcomp hnon
  have hc : ∀ i : s, 0 ≤ c i := hcK.1.1
  have hcs : (∑ i : s, c i) = 1 := hcK.1.2
  have hcx : (∑ i : s, c i • (i:E)) = x := hcK.2
  let val : E → ℝ := fun y => if h : y ∈ s then c ⟨y,h⟩ else 0
  let t : Finset E := s.filter (fun y => 0 < val y)
  have hvalt (i : s) : val (i:E) = c i := by simp [val]
  have hzero (i : s) (hi : (i:E) ∉ t) : c i = 0 := by
    have hn : ¬ 0 < val (i:E) := by
      intro hp
      exact hi (by simp [t, i.property, hp])
    have hn' : ¬ 0 < c i := by simpa [hvalt] using hn
    exact le_antisymm (le_of_not_gt hn') (hc i)
  have htne : t.Nonempty := by
    by_contra hn
    have hempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz : ∀ i : s, c i = 0 := by
      intro i
      apply hzero i
      simp [hempty]
    have hsum0 : (∑ i : s, c i) = 0 := by simp [hz]
    linarith
  have hts : t ⊆ s := by
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  have htlex : lexFace s t := by
    refine ⟨hts, ?_⟩
    rintro ⟨d, hdir, hp, hout⟩
    have hout' : ∀ i : s, c i = 0 → 0 ≤ d i := by
      intro i hi
      apply hout i
      intro hit
      have hip : 0 < val (i:E) := (Finset.mem_filter.mp hit).2
      have hip' : 0 < c i := by simpa [hvalt] using hip
      linarith
    obtain ⟨e, he, hnon'⟩ := exists_positive_step c d hc hout'
    let z : s → ℝ := fun i => c i + e * d i
    have hzstd : z ∈ stdSimplex ℝ s := by
      change (∀ i, 0 ≤ z i) ∧ (∑ i : s, z i) = 1
      constructor
      · intro i; exact hnon' i
      · dsimp [z]
        simp_rw [Finset.sum_add_distrib]
        -- multiplication sum
        rw [← Finset.mul_sum]
        have hd1 : (∑ i ∈ s.attach, d i) = 0 := by simpa using hdir.1
        have hc1 : (∑ i ∈ s.attach, c i) = 1 := by simpa using hcs
        rw [hd1, mul_zero, add_zero, hc1]
    have hzx : B z = x := by
      dsimp [B]
      dsimp [z]
      -- expand each scalar
      simp_rw [add_smul, mul_smul]
      rw [Finset.sum_add_distrib]
      rw [← Finset.smul_sum]
      have hd2 : (∑ i ∈ s.attach, d i • (i:E)) = 0 := by simpa using hdir.2
      have hc2 : (∑ i ∈ s.attach, c i • (i:E)) = x := by simpa using hcx
      rw [hd2, smul_zero, add_zero, hc2]
    have hzK : z ∈ K := ⟨hzstd, hzx⟩
    apply hopt z hzK
    rcases hp with ⟨i, hip, hbefore⟩
    refine ⟨i, ?_, ?_⟩
    · dsimp [z]
      have : 0 < e * d i := mul_pos he hip
      linarith
    · intro j hj
      have h0 := hbefore j hj
      dsimp [z]
      rw [h0]
      simp
  refine ⟨t, htlex, htne, ?_⟩
  -- get weights on support: val, whose positive part is exactly t
  refine (Finset.mem_convexHull' (R:=ℝ) (s:=t) (x:=x)).2 ?_
  refine ⟨val, ?_, ?_, ?_⟩
  · intro y hy
    exact le_of_lt (Finset.mem_filter.mp hy).2
  · -- sum over t equals over subtype
    calc
      (∑ y ∈ t, val y) = ∑ y ∈ s, val y :=
        Finset.sum_subset hts (by
          intro y hy hyt
          have iz : c (⟨y,hy⟩ : s) = 0 :=
            hzero ⟨y,hy⟩ hyt
          simp [val, hy, iz])
      _ = (∑ i : s, c i) := by
        rw [← Finset.sum_attach]
        simp_rw [hvalt]
        have hatt : (s.attach : Finset s) = Finset.univ := by ext; simp
        rw [hatt]
      _ = 1 := hcs
  · calc
      (∑ y ∈ t, val y • y) = ∑ y ∈ s, val y • y :=
        Finset.sum_subset hts (by
          intro y hy hyt
          have iz : c (⟨y,hy⟩ : s) = 0 :=
            hzero ⟨y,hy⟩ hyt
          simp [val, hy, iz])
      _ = (∑ i : s, c i • (i:E)) := by
        rw [← Finset.sum_attach]
        simp_rw [hvalt]
        have hatt : (s.attach : Finset s) = Finset.univ := by ext; simp
        rw [hatt]
      _ = x := hcx
end FamiliesProof

end

open Set
noncomputable section
namespace FamiliesProof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A finite convex hull has a finite geometric simplicial complex.  The chosen
lexicographic coefficient rule is the pulling triangulation; `lexFace_inter` is
the key compatibility, and compact maximization supplies its cover. -/
lemma exists_finiteComplex_convexHull (s : Finset E) :
    ∃ L : Geometry.SimplicialComplex ℝ E,
      L.faces.Finite ∧ L.space = convexHull ℝ (s : Set E) := by
  classical
  refine ⟨lexComplex s (lexFaces_inter s),
    lexComplex_faces_finite s (lexFaces_inter s), ?_⟩
  exact lexComplex_space s (lexFaces_inter s) (lexFaces_cover s)
end FamiliesProof
end

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/LexTriangulation.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/FaceUnique.lean
section
open Set
open scoped BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/- Uniqueness of globally extended barycentric coefficients on a fixed face.
   No dimension/indexing convention occurs here: zero coordinates on the
   complement are enough, which is exactly what one has on overlapping
   `lexComplex` simplices. -/
lemma independent_face_coeff_eq {s t : Finset E} (hi : AffineIndependent ℝ ((↑) : t → E))
    (ht : t ⊆ s) {u v : s → ℝ}
    (uz : ∀ i : s, (i:E) ∉ t → u i = 0)
    (vz : ∀ i : s, (i:E) ∉ t → v i = 0)
    (us : (∑ i : s, u i) = 1) (vs : (∑ i : s, v i) = 1)
    (ev : (∑ i : s, u i • (i:E)) = (∑ i : s, v i • (i:E))) : u = v := by
  classical
  -- Restrict to the supporting subtype and use affine independence there.
  let ur : t → ℝ := fun i => u ⟨i, ht i.property⟩
  let vr : t → ℝ := fun i => v ⟨i, ht i.property⟩
  have sums (z : s → ℝ) (z0 : ∀ i : s, (i:E) ∉ t → z i = 0) :
      (∑ i : s, z i) = ∑ i : t, z ⟨i, ht i.property⟩ := by
    -- extend to plain finsets before moving to subtypes
    classical
    let f : E → ℝ := fun i => if h : i ∈ s then z ⟨i,h⟩ else 0
    have hs (i : s) : f i = z i := by simp [f]
    have ht' (i : t) : f i = z ⟨i, ht i.property⟩ := by simp [f, ht i.property]
    calc
      (∑ i : s, z i) = ∑ i ∈ s.attach, f (i:E) := by simp [hs]
      _ = ∑ i ∈ s, f i := Finset.sum_attach s f
      _ = ∑ i ∈ t, f i := (Finset.sum_subset ht (by
          intro i hi hit
          simp [f, hi, z0 ⟨i,hi⟩ hit])).symm
      _ = ∑ i ∈ t.attach, f (i:E) := (Finset.sum_attach t f).symm
      _ = ∑ i : t, z ⟨i, ht i.property⟩ := by
        change (∑ i : t, f (i:E)) = _
        simp_rw [ht']
  have sumsV (z : s → ℝ) (z0 : ∀ i : s, (i:E) ∉ t → z i = 0) :
      (∑ i : s, z i • (i:E)) = ∑ i : t, z ⟨i, ht i.property⟩ • (i:E) := by
    let f : E → E := fun i => if h : i ∈ s then z ⟨i,h⟩ • i else 0
    have hs (i : s) : f i = z i • (i:E) := by simp [f]
    have ht' (i : t) : f i = z ⟨i, ht i.property⟩ • (i:E) := by simp [f, ht i.property]
    calc
      (∑ i : s, z i • (i:E)) = ∑ i ∈ s.attach, f (i:E) := by simp [hs]
      _ = ∑ i ∈ s, f i := Finset.sum_attach s f
      _ = ∑ i ∈ t, f i := (Finset.sum_subset ht (by
        intro i hi hit
        simp [f, hi, z0 ⟨i,hi⟩ hit])).symm
      _ = ∑ i ∈ t.attach, f (i:E) := (Finset.sum_attach t f).symm
      _ = ∑ i : t, z ⟨i, ht i.property⟩ • (i:E) := by
        change (∑ i : t, f (i:E)) = _
        simp_rw [ht']
  have urS : (∑ i : t, ur i) = 1 := by
    rw [← sums u uz]
    exact us
  have vrS : (∑ i : t, vr i) = 1 := by
    rw [← sums v vz]
    exact vs
  have evR : (∑ i : t, ur i • (i:E)) = (∑ i : t, vr i • (i:E)) := by
    rw [← sumsV u uz, ← sumsV v vz]
    exact ev
  have H := (affineIndependent_iff.mp hi)
  have zeroS :
      ∑ i ∈ (Finset.univ : Finset t), (ur i - vr i) = 0 := by
    rw [Finset.sum_sub_distrib]
    linarith
  have zeroV :
      ∑ i ∈ (Finset.univ : Finset t), (ur i - vr i) • (i:E) = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr evR
  have agree : ur = vr := by
    funext i
    have h := H (Finset.univ : Finset t) (fun i => ur i - vr i)
      zeroS zeroV i (Finset.mem_univ _)
    linarith
  funext i
  by_cases inT : (i:E) ∈ t
  · have eq := congrFun agree ⟨i, inT⟩
    exact eq
  · rw [uz i inT, vz i inT]
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/FaceUnique.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/IntervalBins.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section

/-- Affine lattice point on `[a,b]` at integer step `i/n`. Defined for every
natural `i`; in the path below only `i ≤ n` occurs. -/
def linePoint (a b : ℝ) (n i : ℕ) : ℝ :=
  a + (b-a) * (i:ℝ) / (n:ℝ)

lemma linePoint_zero (a b : ℝ) (n : ℕ) : linePoint a b n 0 = a := by
  simp [linePoint]
lemma linePoint_end (a b : ℝ) {n : ℕ} (hn : 0 < n) : linePoint a b n n = b := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp [linePoint]
  field_simp
  ring

lemma linePoint_strictMono (a b : ℝ) {n : ℕ} (hn : 0 < n)
    (hab : a < b) {i j : ℕ} :
    linePoint a b n i < linePoint a b n j ↔ i < j := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hc : 0 < (b-a) / (n:ℝ) := div_pos (sub_pos.mpr hab) hn'
  -- write the points as `a + c*i`.
  unfold linePoint
  have hre (r : ℝ) : (b-a) * r / (n:ℝ) = ((b-a)/(n:ℝ))*r := by ring
  rw [hre, hre]
  -- normalize products
  constructor
  · intro h
    have : (i:ℝ) < (j:ℝ) := by
      nlinarith
    exact_mod_cast this
  · intro h
    have h' : (i:ℝ) < j := by exact_mod_cast h
    nlinarith

lemma linePoint_le (a b : ℝ) {n : ℕ} (hn : 0 < n)
    (hab : a < b) {i j : ℕ} :
    linePoint a b n i ≤ linePoint a b n j ↔ i ≤ j := by
  constructor
  · intro h
    by_contra hnij
    have hji : j < i := Nat.lt_of_not_ge hnij
    have := (linePoint_strictMono a b hn hab).2 hji
    linarith
  · intro h
    rcases Nat.eq_or_lt_of_le h with h|h
    · simp [h]
    · exact le_of_lt ((linePoint_strictMono a b hn hab).2 h)

/-- In a subset of a non-degenerate interval edge, a point of the convex hull
at an endpoint (resp. in the open interval) forces the endpoint (resp. both
endpoints) to have actually been among the vertices. This tiny lemma is handy
for constructing a one-dimensional geometric complex without any global
triangulation API. -/
lemma subset_pair_endpoint
    {l r x : ℝ} (hlr : l < r) {t : Finset ℝ}
    (htne : t.Nonempty) (ht : t ⊆ {l,r})
    (hx : x ∈ convexHull ℝ (t : Set ℝ)) :
    (x = l → l ∈ t) ∧ (x = r → r ∈ t) ∧
      (l < x → x < r → l ∈ t ∧ r ∈ t) := by
  classical
  have hbounds : x ∈ Set.Icc l r := by
    have hm : convexHull ℝ (t : Set ℝ) ⊆ convexHull ℝ ({l,r} : Set ℝ) :=
      convexHull_mono (by
        intro y hy
        have hh : y ∈ t := hy
        have hp := ht hh
        simpa using hp)
    have hh := hm hx
    simpa [convexHull_pair, segment_eq_Icc (le_of_lt hlr)] using hh
  have hleft : x = l → l ∈ t := by
    intro hxl
    by_contra hnot
    have hone : t ⊆ {r} := by
      intro y hy
      have hy' := ht hy
      have hor : y = l ∨ y = r := by simpa using hy'
      rcases hor with h|h
      · exact False.elim (hnot (h ▸ hy))
      · simpa [h]
    have hmem : x ∈ convexHull ℝ ({r} : Set ℝ) :=
      (convexHull_mono (by exact_mod_cast hone)) hx
    have : x = r := by simpa [convexHull_singleton] using hmem
    linarith
  have hright : x = r → r ∈ t := by
    intro hxr
    by_contra hnot
    have hone : t ⊆ {l} := by
      intro y hy
      have hy' := ht hy
      have hor : y = l ∨ y = r := by simpa using hy'
      rcases hor with h|h
      · simpa [h]
      · exact False.elim (hnot (h ▸ hy))
    have hmem : x ∈ convexHull ℝ ({l} : Set ℝ) :=
      (convexHull_mono (by exact_mod_cast hone)) hx
    have : x = l := by simpa [convexHull_singleton] using hmem
    linarith
  refine ⟨hleft, hright, ?_⟩
  intro hlx hxr
  have hl : l ∈ t := by
    by_contra hnot
    have hone : t ⊆ {r} := by
      intro y hy
      have hor : y = l ∨ y = r := by simpa using ht hy
      cases hor with
      | inl h => exact False.elim (hnot (h ▸ hy))
      | inr h => simpa [h]
    have hm := (convexHull_mono (by exact_mod_cast hone)) hx
    have : x = r := by simpa [convexHull_singleton] using hm
    linarith
  have hr : r ∈ t := by
    by_contra hnot
    have hone : t ⊆ {l} := by
      intro y hy
      have hor : y = l ∨ y = r := by simpa using ht hy
      cases hor with
      | inl h => simpa [h]
      | inr h => exact False.elim (hnot (h ▸ hy))
    have hm := (convexHull_mono (by exact_mod_cast hone)) hx
    have : x = l := by simpa [convexHull_singleton] using hm
    linarith
  exact ⟨hl, hr⟩

/-- The elementary interval complex with break points `a+(b-a)i/n`.
We record its faces explicitly. This is deliberately independent of the
rather more involved lexicographic triangulation: here every listed point is
a real break point. -/
def intervalComplex (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a < b) :
    Geometry.SimplicialComplex ℝ ℝ where
  faces := {t : Finset ℝ | t.Nonempty ∧ ∃ i < n, t ⊆
    {linePoint a b n i, linePoint a b n (i+1)}}
  isRelLowerSet_faces := by
    intro s hs
    rcases hs with ⟨hsne, i, hi, his⟩
    refine ⟨hsne, ?_⟩
    intro t ht htne
    exact ⟨htne, i, hi, ht.trans his⟩
  indep := by
    classical
    intro t ht
    rcases ht with ⟨htne, i, hi, hit⟩
    let l := linePoint a b n i
    let r := linePoint a b n (i+1)
    have hlr : l ≠ r := ne_of_lt ((linePoint_strictMono a b hn hab).2 (Nat.lt_succ_self _))
    -- Embed `t` in the two independent points.
    let e : t ↪ Fin 2 :=
      { toFun := fun x => if (x:ℝ) = l then 0 else 1
        inj' := by
          intro x y hxy
          have hx : (x:ℝ) = l ∨ (x:ℝ) = r := by simpa [l,r] using (hit x.property)
          have hy : (y:ℝ) = l ∨ (y:ℝ) = r := by simpa [l,r] using (hit y.property)
          apply Subtype.ext
          rcases hx with hx|hx <;> rcases hy with hy|hy
          · exact hx.trans hy.symm
          · -- images 0 and 1 cannot agree
            exfalso
            have bad : r = l := by
              simpa [hx, hy, hlr] using hxy
            exact (hlr bad.symm).elim
          · exfalso
            have bad : r = l := by
              simpa [hx, hy, hlr] using hxy
            exact (hlr bad.symm).elim
          · exact hx.trans hy.symm }
    let v : Fin 2 → ℝ := ![l,r]
    have hv : AffineIndependent ℝ v := affineIndependent_of_ne ℝ hlr
    have hc := hv.comp_embedding e
    -- the composed family is the subtype inclusion
    have heq : (v ∘ (e : t → Fin 2)) = ((↑) : t → ℝ) := by
      funext x
      have hx : (x:ℝ) = l ∨ (x:ℝ) = r := by simpa [l,r] using (hit x.property)
      rcases hx with hx|hx
      · simp [v, e, hx]
      · have hne : (r:ℝ) ≠ l := Ne.symm hlr
        -- `x=r`
        simp [v, e, hx, hne]
    rw [heq] at hc
    exact hc
  inter_subset_convexHull := by
    classical
    intro t u ht hu x hx
    rcases ht with ⟨htne, i, hi, hit⟩
    rcases hu with ⟨hune, j, hj, hju⟩
    have hxi : x ∈ convexHull ℝ (t : Set ℝ) := hx.1
    have hxj : x ∈ convexHull ℝ (u : Set ℝ) := hx.2
    let li := linePoint a b n i
    let ri := linePoint a b n (i+1)
    let lj := linePoint a b n j
    let rj := linePoint a b n (j+1)
    have hli : li < ri := (linePoint_strictMono a b hn hab).2 (Nat.lt_succ_self _)
    have hlj : lj < rj := (linePoint_strictMono a b hn hab).2 (Nat.lt_succ_self _)
    have hti : t ⊆ {li,ri} := by simpa [li,ri] using hit
    have htj : u ⊆ {lj,rj} := by simpa [lj,rj] using hju
    have bx1 : x ∈ Set.Icc li ri := by
      have hm := (convexHull_mono (by exact_mod_cast hti)) hxi
      simpa [convexHull_pair, segment_eq_Icc (le_of_lt hli)] using hm
    have bx2 : x ∈ Set.Icc lj rj := by
      have hm := (convexHull_mono (by exact_mod_cast htj)) hxj
      simpa [convexHull_pair, segment_eq_Icc (le_of_lt hlj)] using hm
    -- If both indices agree the endpoint/open-interval lemma deals with
    -- possible proper subfaces. If not, only the common endpoint can remain.
    rcases lt_trichotomy i j with hij|hij|hij
    · -- i < j
      have hle : i+1 ≤ j := hij
      have hri_le : ri ≤ lj := (linePoint_le a b hn hab).2 hle
      have heqv : x = ri := by
        have hxri : x ≤ ri := bx1.2
        have hxl : lj ≤ x := bx2.1
        have : ri = lj := by
          by_contra hne
          have : ri < lj := lt_of_le_of_ne hri_le hne
          linarith
        linarith
      have hrl : ri = lj := by linarith [bx2.1, bx1.2, hri_le]
      have hmit : ri ∈ t :=
        (subset_pair_endpoint hli htne hti hxi).2.1 heqv
      have hmju : lj ∈ u :=
        (subset_pair_endpoint hlj hune htj hxj).1 (by simpa [heqv, hrl])
      -- a common vertex lies in the hull of the intersection
      have hm : (ri:ℝ) ∈ (t ∩ u : Finset ℝ) := by
        refine Finset.mem_inter.mpr ⟨hmit, ?_⟩
        simpa [hrl] using hmju
      have hm' : x ∈ ((↑t : Set ℝ) ∩ (↑u : Set ℝ)) := by
        simpa [heqv] using hm
      exact subset_convexHull ℝ _ hm' 
    · subst j
      have dat1 := subset_pair_endpoint hli htne hti hxi
      have dat2 := subset_pair_endpoint hli hune (by simpa [li,ri,lj,rj] using htj) hxj
      by_cases hL : x = li
      · have hm : li ∈ (t ∩ u : Finset ℝ) := Finset.mem_inter.mpr ⟨dat1.1 hL,
            dat2.1 hL⟩
        have hm' : x ∈ ((↑t : Set ℝ) ∩ (↑u : Set ℝ)) := by simpa [hL] using hm
        exact subset_convexHull ℝ _ hm' 
      · by_cases hR : x = ri
        · have hm : ri ∈ (t ∩ u : Finset ℝ) := Finset.mem_inter.mpr ⟨dat1.2.1 hR,
              dat2.2.1 hR⟩
          have hm' : x ∈ ((↑t : Set ℝ) ∩ (↑u : Set ℝ)) := by simpa [hR] using hm
          exact subset_convexHull ℝ _ hm' 
        · have hxL : li < x := lt_of_le_of_ne bx1.1 (Ne.symm hL)
          have hxR : x < ri := lt_of_le_of_ne bx1.2 hR
          have hlboth := dat1.2.2 hxL hxR
          have hboth2 := dat2.2.2 hxL hxR
          have bothsub : ({li,ri} : Finset ℝ) ⊆ t ∩ u := by
            intro z hz
            have : z = li ∨ z = ri := by simpa using hz
            rcases this with h|h
            · simpa [h, hlboth.1, hboth2.1]
            · simpa [h, hlboth.2, hboth2.2]
          have hsubsets : ({li,ri} : Set ℝ) ⊆ ((↑t : Set ℝ) ∩ (↑u : Set ℝ)) := by
            intro z hz
            have hz' : z ∈ ({li,ri} : Finset ℝ) := by simpa using hz
            have zz := (Finset.mem_inter.mp (bothsub hz'))
            exact ⟨zz.1, zz.2⟩
          have hmono := convexHull_mono (𝕜:=ℝ) hsubsets
          apply hmono
          simpa [convexHull_pair,
             segment_eq_Icc (le_of_lt hli)] using bx1
    · -- j < i, symmetrically swap the two faces
      have hle : j+1 ≤ i := hij
      have hrj_le : rj ≤ li := (linePoint_le a b hn hab).2 hle
      have heqv : x = li := by
        have hxri : x ≤ rj := bx2.2
        have hxl : li ≤ x := bx1.1
        have : rj = li := by
          by_contra hne
          have : rj < li := lt_of_le_of_ne hrj_le hne
          linarith
        linarith
      have hrl : rj = li := by linarith [bx1.1, bx2.2, hrj_le]
      have hmit : li ∈ t :=
        (subset_pair_endpoint hli htne hti hxi).1 heqv
      have hmju : rj ∈ u :=
        (subset_pair_endpoint hlj hune htj hxj).2.1 (by simpa [heqv, hrl])
      have hm : li ∈ (t ∩ u : Finset ℝ) := by
        refine Finset.mem_inter.mpr ⟨hmit, ?_⟩
        simpa [← hrl] using hmju
      have hm' : x ∈ ((↑t : Set ℝ) ∩ (↑u : Set ℝ)) := by
        simpa [heqv] using hm
      exact subset_convexHull ℝ _ hm' 

lemma intervalComplex_faces (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a < b) :
    (intervalComplex a b n hn hab).faces =
      {t : Finset ℝ | t.Nonempty ∧ ∃ i < n, t ⊆
        {linePoint a b n i, linePoint a b n (i+1)}} := rfl

lemma intervalComplex_faces_finite (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a < b) :
    (intervalComplex a b n hn hab).faces.Finite := by
  classical
  -- all vertices occur among the first `n+1` breakpoints
  let V : Finset ℝ := (Finset.range (n+1)).image (linePoint a b n)
  have hsub : (intervalComplex a b n hn hab).faces ⊆ {t : Finset ℝ | t ⊆ V} := by
    intro t ht
    rcases ht with ⟨_, i, hi, ht⟩
    intro z hz
    have hz' : z = linePoint a b n i ∨ z = linePoint a b n (i+1) := by
      simpa using ht hz
    rcases hz' with h|h
    · subst z
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_lt hi), rfl⟩
    · subst z
      exact Finset.mem_image.mpr ⟨i+1, Finset.mem_range.mpr (Nat.add_lt_add_right hi 1), rfl⟩
  exact (Set.finite_Iic V).subset hsub

/-- Every scalar between the endpoints is between two consecutive breakpoints. -/
lemma exists_between_linePoints (a b x : ℝ) {n : ℕ} (hn : 0 < n)
    (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∃ i < n, x ∈ Set.Icc (linePoint a b n i)
                             (linePoint a b n (i+1)) := by
  classical
  -- take the largest `i ≤ n` with `q_i ≤ x`
  let S : Finset ℕ := (Finset.range (n+1)).filter
    (fun i => linePoint a b n i ≤ x)
  have hS : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S, linePoint_zero, hx.1, Nat.zero_lt_succ]
  let m : ℕ := S.max' hS
  have hmS : m ∈ S := Finset.max'_mem S hS
  have hmn : m < n+1 := (Finset.mem_filter.mp hmS).1 |> Finset.mem_range.mp
  have hmx : linePoint a b n m ≤ x := (Finset.mem_filter.mp hmS).2
  by_cases hmend : m = n
  · -- the final endpoint itself; charge it to the last segment
    have xn : x = b := by
      have hb' : linePoint a b n n = b := linePoint_end a b hn
      have hmxe : linePoint a b n n ≤ x := by simpa [hmend] using hmx
      have : b ≤ x := by simpa [linePoint_end a b hn] using hmxe
      linarith [hx.2]
    let i := n-1
    have hi : i < n := Nat.sub_lt (Nat.zero_lt_of_lt hn) (by decide : 0 < (1:ℕ))
    refine ⟨i, hi, ?_⟩
    have hi1 : i+1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))
    constructor
    · -- previous lattice point ≤ b
      have le := (linePoint_le a b hn hab).2 (Nat.le_of_lt hi |>.trans (Nat.le_refl n))
      -- simpler i ≤ n
      have le' : linePoint a b n i ≤ linePoint a b n n :=
        (linePoint_le a b hn hab).2 (Nat.le_of_lt hi)
      simpa [xn, linePoint_end a b hn] using le'
    · simpa [hi1, xn, linePoint_end a b hn]
  · have hm_lt : m < n := (Nat.lt_succ_iff.mp hmn).lt_of_ne hmend
    refine ⟨m, hm_lt, hmx, ?_⟩
    by_contra hnot
    have hbig : linePoint a b n (m+1) ≤ x := le_of_not_ge hnot
    have hm1mem : m+1 ∈ S := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (Nat.add_lt_add_right hm_lt 1), hbig⟩
    have hlemax : m+1 ≤ m := Finset.le_max' S (m+1) hm1mem
    omega

lemma intervalComplex_space (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a < b) :
    (intervalComplex a b n hn hab).space = Set.Icc a b := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases (Geometry.SimplicialComplex.mem_space_iff).1 hx with ⟨t, ht, hxt⟩
    rcases ht with ⟨_, i, hi, hit⟩
    have hmem : x ∈ Set.Icc (linePoint a b n i) (linePoint a b n (i+1)) := by
      have hm := (convexHull_mono (by exact_mod_cast hit)) hxt
      simpa [convexHull_pair, segment_eq_Icc
        (le_of_lt ((linePoint_strictMono a b hn hab).2 (Nat.lt_succ_self _)))] using hm
    have hle1 : a ≤ linePoint a b n i := by
      simpa [linePoint_zero] using
        ((linePoint_le a b hn hab).2 (Nat.zero_le i))
    have hle2 : linePoint a b n (i+1) ≤ b := by
      have : i+1 ≤ n := hi
      simpa [linePoint_end a b hn] using
        ((linePoint_le a b hn hab).2 this)
    exact ⟨hle1.trans hmem.1, hmem.2.trans hle2⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := exists_between_linePoints a b x hn hab hx
    let t : Finset ℝ := {linePoint a b n i, linePoint a b n (i+1)}
    have ht : t ∈ (intervalComplex a b n hn hab).faces := by
      refine ⟨?_, i, hi, Finset.Subset.rfl⟩
      exact ⟨_, Finset.mem_insert_self _ _⟩
    apply (Geometry.SimplicialComplex.convexHull_subset_space (K := intervalComplex a b n hn hab) ht)
    simpa [t, convexHull_pair, segment_eq_Icc
        (le_of_lt ((linePoint_strictMono a b hn hab).2 (Nat.lt_succ_self _)))] using hxi

lemma intervalComplex_facet_edge (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a < b)
    {t : Finset ℝ} (ht : t ∈ (intervalComplex a b n hn hab).facets) :
    ∃ i < n, t = {linePoint a b n i, linePoint a b n (i+1)} := by
  classical
  have hm := (Geometry.SimplicialComplex.mem_facets).mp ht
  rcases hm.1 with ⟨_, i, hi, hit⟩
  refine ⟨i, hi, ?_⟩
  let u : Finset ℝ := {linePoint a b n i, linePoint a b n (i+1)}
  have hu : u ∈ (intervalComplex a b n hn hab).faces := by
    refine ⟨⟨_, Finset.mem_insert_self _ _⟩, i, hi, Finset.Subset.rfl⟩
  exact hm.2 u hu hit

end
end FamiliesProof

namespace FamiliesProof
open Set
open scoped Topology BigOperators
noncomputable section

/-- Height in bin `i`. It is zero before the bin and one after it. Working with
`min` and `max` instead of a piecewise formula avoids a gluing lemma for
continuous maps. -/
def binHeight (a b : ℝ) (n i : ℕ) (x : ℝ) : ℝ :=
  min 1 (max 0 (((n:ℝ) * (x-a) / (b-a)) - (i:ℝ)))
def binMap (a b : ℝ) (n i : ℕ) (x : ℝ) : ℝ :=
  a + (b-a) * binHeight a b n i x

lemma continuous_binHeight (a b : ℝ) (n i : ℕ) :
    Continuous (binHeight a b n i) := by
  unfold binHeight
  fun_prop
lemma continuous_binMap (a b : ℝ) (n i : ℕ) :
    Continuous (binMap a b n i) := by
  unfold binMap
  exact continuous_const.add (continuous_const.mul (continuous_binHeight a b n i))
lemma binHeight_mem (a b : ℝ) (n i : ℕ) (x : ℝ) :
    binHeight a b n i x ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · dsimp [binHeight]
    exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _
lemma binMap_mem {a b x : ℝ} (hab : a < b) (n i : ℕ) :
    binMap a b n i x ∈ Set.Icc a b := by
  have hh := binHeight_mem a b n i x
  dsimp [binMap]
  constructor
  · have hp : 0 ≤ (b-a) * binHeight a b n i x :=
        mul_nonneg (sub_nonneg.mpr (le_of_lt hab)) hh.1
    linarith
  · have hp := mul_le_mul_of_nonneg_left hh.2 (sub_nonneg.mpr (le_of_lt hab))
    change (b-a) * binHeight a b n i x ≤ (b-a) * (1:ℝ) at hp
    linarith


lemma binHeight_of_le {a b : ℝ} {n : ℕ} (hn : 0 < n) (hab : a < b)
    {i : ℕ} {x : ℝ} (hx : x ≤ linePoint a b n i) :
    binHeight a b n i x = 0 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hb : 0 < b-a := sub_pos.mpr hab
  have hi : (n:ℝ) * (x-a) / (b-a) ≤ (i:ℝ) := by
    dsimp [linePoint] at hx
    apply (div_le_iff₀ hb).2
    -- clear the positive denominator `n` in `hx`
    have hn0 : (0:ℝ) < n := hn'
    -- linear algebra after multiplying by n
    calc
      (n:ℝ) * (x - a) ≤ (n:ℝ) * ((b-a) * (i:ℝ) / (n:ℝ)) := by
        have h := sub_le_sub_right hx a
        exact (mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hn0))
      _ = (i:ℝ) * (b-a) := by field_simp; <;> ring
  have hzero : max (0:ℝ) (((n:ℝ) * (x-a)/(b-a)) - (i:ℝ)) = 0 :=
    max_eq_left (by linarith)
  simp [binHeight, hzero]

lemma binHeight_of_ge {a b : ℝ} {n : ℕ} (hn : 0 < n) (hab : a < b)
    {i : ℕ} {x : ℝ} (hx : linePoint a b n (i+1) ≤ x) :
    binHeight a b n i x = 1 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hb : 0 < b-a := sub_pos.mpr hab
  have hi : ( (i:ℝ) + 1) ≤ (n:ℝ) * (x-a) / (b-a) := by
    apply (le_div_iff₀ hb).2
    dsimp [linePoint] at hx
    have h := sub_le_sub_right hx a
    have h' := (mul_le_mul_of_nonneg_left h (le_of_lt hn'))
    calc
      ((i:ℝ) + 1) * (b-a) = (n:ℝ) * ((b-a) * ((i+1:ℕ):ℝ) / (n:ℝ)) := by
        have hnn : (n:ℝ) ≠ 0 := by positivity
        rw [Nat.cast_add, Nat.cast_one]
        field_simp
      _ ≤ (n:ℝ) * (x-a) := by
        nlinarith
  have hone : 1 ≤ max (0:ℝ) (((n:ℝ) * (x-a)/(b-a)) - (i:ℝ)) := by
    calc
      (1:ℝ) ≤ (((n:ℝ) * (x-a)/(b-a)) - (i:ℝ)) := by linarith
      _ ≤ max (0:ℝ) (((n:ℝ) * (x-a)/(b-a)) - (i:ℝ)) := le_max_right _ _
  exact min_eq_left hone

lemma binMap_of_le {a b : ℝ} {n : ℕ} (hn : 0 < n) (hab : a < b)
    {i : ℕ} {x : ℝ} (hx : x ≤ linePoint a b n i) :
    binMap a b n i x = a := by
  simp [binMap, binHeight_of_le hn hab hx]
lemma binMap_of_ge {a b : ℝ} {n : ℕ} (hn : 0 < n) (hab : a < b)
    {i : ℕ} {x : ℝ} (hx : linePoint a b n (i+1) ≤ x) :
    binMap a b n i x = b := by
  have hz := binHeight_of_ge hn hab hx
  dsimp [binMap]
  rw [hz]
  ring

/-- The ordered bins on a real interval. On its `m`th closed edge all copies
but the `m`th are constant. Moreover they fix both endpoints. This is the
one-dimensional seed for a facewise version: it supplies the real break
points and the actual continuous formula rather than only a closed cover. -/
lemma interval_orderedBins {J : Type*} [Fintype J]
    (e : J ≃ Fin (Fintype.card J))
    {a b : ℝ} (hab : a < b) (hJ : 0 < Fintype.card J) :
    ∃ ψ : J → C(Set.Icc a b, Set.Icc a b),
      (∀ (m : ℕ), m < Fintype.card J → ∀ j : J,
        (e j).val ≠ m → ∀ x y : Set.Icc a b,
          (x.1 ∈ Set.Icc (linePoint a b (Fintype.card J) m)
                           (linePoint a b (Fintype.card J) (m+1))) →
          (y.1 ∈ Set.Icc (linePoint a b (Fintype.card J) m)
                           (linePoint a b (Fintype.card J) (m+1))) →
          ψ j x = ψ j y) ∧
      (∀ j, ψ j ⟨a, ⟨le_rfl, le_of_lt hab⟩⟩ =
              ⟨a, ⟨le_rfl, le_of_lt hab⟩⟩) ∧
      (∀ j, ψ j ⟨b, ⟨le_of_lt hab, le_rfl⟩⟩ =
              ⟨b, ⟨le_of_lt hab, le_rfl⟩⟩) := by
  classical
  let n := Fintype.card J
  let ψ : J → C(Set.Icc a b, Set.Icc a b) := fun j =>
    { toFun := fun x => ⟨binMap a b n (e j).val x.1,
                          binMap_mem hab n (e j).val⟩
      continuous_toFun :=
        ((continuous_binMap a b n (e j).val).comp
          continuous_subtype_val).subtype_mk _ }
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro m hm j hne x y hx hy
    change (⟨binMap a b n (e j).val x.1, _⟩ : Set.Icc a b) = ⟨_, _⟩
    apply Subtype.ext
    dsimp
    rcases lt_or_gt_of_ne hne with hjm|hjm
    · -- this colour's ramp occurred before this edge; it is already `b`.
      have hsucc : (e j).val + 1 ≤ m := hjm
      have lx : linePoint a b n ((e j).val+1) ≤ x.1 :=
        le_trans ((linePoint_le a b hJ hab).2 hsucc) hx.1
      have ly : linePoint a b n ((e j).val+1) ≤ y.1 :=
        le_trans ((linePoint_le a b hJ hab).2 hsucc) hy.1
      rw [binMap_of_ge hJ hab lx, binMap_of_ge hJ hab ly]
    · have hle : m+1 ≤ (e j).val := hjm
      have lx : x.1 ≤ linePoint a b n (e j).val :=
        le_trans hx.2 ((linePoint_le a b hJ hab).2 (by omega))
      have ly : y.1 ≤ linePoint a b n (e j).val :=
        le_trans hy.2 ((linePoint_le a b hJ hab).2 (by omega))
      rw [binMap_of_le hJ hab lx, binMap_of_le hJ hab ly]
  · intro j
    apply Subtype.ext
    change binMap a b n (e j).val a = a
    apply binMap_of_le hJ hab
    simpa [linePoint_zero] using
      ((linePoint_le a b hJ hab).2 (Nat.zero_le (e j).val))
  · intro j
    apply Subtype.ext
    change binMap a b n (e j).val b = b
    apply binMap_of_ge hJ hab
    have hj : (e j).val+1 ≤ n := (e j).isLt
    have hh := ((linePoint_le a b hJ hab).2 hj)
    have hend : linePoint a b n n = b := linePoint_end a b hJ
    rw [hend] at hh
    exact hh
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/IntervalBins.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/LexUniquePos.lean
section
open Set
open scoped BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Extended nonnegative coefficient vectors on any two lexicographic faces representing
the same point agree globally.  This makes it possible to check a subdivision in
one common cumulative-coordinate array even though the original list is dependent. -/
lemma lexFace_coeff_unique {s a b : Finset E} (ha : lexFace s a)
    (hb : lexFace s b) {u v : s → ℝ}
    (upos : ∀ i, 0 ≤ u i) (vpos : ∀ i, 0 ≤ v i)
    (uz : ∀ i : s, (i:E) ∉ a → u i = 0)
    (vz : ∀ i : s, (i:E) ∉ b → v i = 0)
    (us : (∑ i, u i) = 1) (vs : (∑ i, v i) = 1)
    (ev : (∑ i : s, u i • (i:E)) = ∑ i : s, v i • (i:E)) : u = v := by
  classical
  let e : s → ℝ := fun i => v i - u i
  have es : coeffDirection s e := by
    constructor
    · dsimp [e]
      rw [Finset.sum_sub_distrib]
      change (∑ i : s, v i) - (∑ i : s, u i) = 0
      rw [vs, us]
      ring
    · change (∑ i : s, (v i - u i) • (i:E)) = 0
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr ev.symm -- check
  have outA : outsideNonneg a e := by
    intro i hi
    dsimp [e]
    rw [uz i hi]
    simpa using (vpos i)
  let ee : s → ℝ := fun i => - e i
  have ees : coeffDirection s ee := by
    constructor
    · simpa [ee, Finset.sum_neg_distrib] using congrArg Neg.neg es.1
    · have Z : -(∑ i : s, e i • (i:E)) = (0:E) := by rw [es.2, neg_zero]
      simpa [ee, ← Finset.sum_neg_distrib] using Z
  have outB : outsideNonneg b ee := by
    intro i hi
    have vv := vz i hi
    have uu := upos i
    dsimp [ee, e]
    rw [vv]
    linarith
  have ezero : e = 0 := by
    by_contra H
    rcases lexPositive_or_neg e H with ep | ep
    · exact (ha.2 ⟨e, es, ep, outA⟩).elim
    · exact (hb.2 ⟨ee, ees, ep, outB⟩).elim
  funext i
  have h := congrFun ezero i
  dsimp [e] at h
  linarith
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/LexUniquePos.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/BinSimplex.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
/-- The initial cumulative coordinates of an ordered simplex.  We deliberately use
natural cut numbers rather than predecessors in a finite order; a face is then
obtained simply by deleting a zero summand. -/
def cumCoord (d : ℕ) (u : Fin d → ℝ) (m : ℕ) : ℝ :=
  ∑ v ∈ (Finset.univ : Finset (Fin d)).filter (fun v => v.val < m), u v
@[simp] lemma cumCoord_zero (d) (u : Fin d → ℝ) : cumCoord d u 0 = 0 := by
  simp [cumCoord]
lemma continuous_cumCoord (d m : ℕ) : Continuous (cumCoord d · m) := by
  unfold cumCoord
  fun_prop
lemma cumCoord_succ {d m : ℕ} (hm : m < d) (u : Fin d → ℝ) :
    cumCoord d u (m+1) = cumCoord d u m + u ⟨m,hm⟩ := by
  unfold cumCoord
  classical
  have filt : (Finset.univ : Finset (Fin d)).filter (fun v => v.val < m+1) =
      insert ⟨m,hm⟩ ((Finset.univ : Finset (Fin d)).filter (fun v => v.val < m)) := by
    ext v
    simp
    constructor
    · intro h
      by_cases hh : v.val = m
      · left; exact Fin.ext hh
      · right; omega
    · rintro (hv|hv)
      · simpa [hv]
      · omega
  rw [filt, Finset.sum_insert]
  · ring
  · simp
lemma cumCoord_mono {d} {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i) :
    Monotone (cumCoord d u) := by
  intro m n hmn
  unfold cumCoord
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro x hx; simp at hx ⊢; omega)
    (by intro i hi hj; exact hu i)
lemma cumCoord_large {d m : ℕ} (u : Fin d → ℝ) (h : d ≤ m) :
    cumCoord d u m = ∑ i, u i := by
  unfold cumCoord
  classical
  have : (Finset.univ : Finset (Fin d)).filter (fun v => v.val < m) = Finset.univ := by
    ext i
    simp
    exact Nat.lt_of_lt_of_le i.isLt h
  rw [this]

lemma binHeight_mono {n r : ℕ} (hn : 0 < n) : Monotone (binHeight 0 1 n r) := by
  intro x y h
  unfold binHeight
  have : (n:ℝ) * (x - 0) / (1-0) - r ≤ (n:ℝ) * (y-0) / (1-0) - r := by
    have nr : 0 ≤ (n:ℝ) := by exact_mod_cast (Nat.zero_le n)
    norm_num
    exact mul_le_mul_of_nonneg_left h nr
  exact min_le_min_left _ (max_le_max_left _ this)
@[simp] lemma binHeight_zero_arg {n r : ℕ} (hn : 0 < n) :
    binHeight 0 1 n r 0 = 0 := by
  unfold binHeight; simp
lemma binHeight_one_arg {n r : ℕ} (hn : 0 < n) (hr : r < n) :
    binHeight 0 1 n r 1 = 1 := by
  unfold binHeight
  have nat : 1 + r ≤ n := by omega
  have nat' : (1:ℝ) + r ≤ n := by exact_mod_cast nat
  have h : (1:ℝ) ≤ (n:ℝ) - (r:ℝ) := by linarith
  norm_num
  exact h

/-- Barycentric weights for colour `r` on an ordered `(d-1)`-simplex. The
output point is obtained by evaluating these weights at the vertices. This
is the higher-dimensional version of the interval bin formula; importantly the
formula doesn't make any choices on proper faces. -/
def baryStep (d n r : ℕ) (u : Fin d → ℝ) (v : Fin d) : ℝ :=
  binHeight 0 1 n r (cumCoord d u (v.val+1)) -
    binHeight 0 1 n r (cumCoord d u v.val)
lemma continuous_baryStep (d n r : ℕ) (v : Fin d) :
    Continuous (fun u : Fin d → ℝ => baryStep d n r u v) := by
  unfold baryStep
  exact ((continuous_binHeight 0 1 n r).comp (continuous_cumCoord d _)).sub
    ((continuous_binHeight 0 1 n r).comp (continuous_cumCoord d _))
lemma baryStep_nonneg {d n r : ℕ} (hn : 0 < n)
    {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i) (v : Fin d) :
    0 ≤ baryStep d n r u v := by
  unfold baryStep
  exact sub_nonneg.mpr (binHeight_mono hn (cumCoord_mono hu (Nat.le_succ _)))
lemma sum_baryStep {d n r : ℕ} (hd : 0 < d) (hn : 0 < n) (hr : r < n)
    {u : Fin d → ℝ} (hsum : (∑ v, u v) = 1) :
    (∑ v, baryStep d n r u v) = 1 := by
  -- telescoping in the chain of cuts 0,...,d
  let H : ℕ → ℝ := fun m => binHeight 0 1 n r (cumCoord d u m)
  have tel : ∀ m : ℕ, (∑ i ∈ Finset.range m, (H (i+1) - H i)) = H m - H 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hd' : cumCoord d u d = 1 := by rw [cumCoord_large u (le_rfl), hsum]
  change (∑ v : Fin d, (H (v.val+1) - H v.val)) = 1
  rw [Fin.sum_univ_eq_sum_range (fun m => H (m+1) - H m) d]
  rw [tel d]
  simp [H, hd', binHeight_one_arg hn hr, cumCoord_zero, hn]

/-- On a grid chamber, a colour whose bin avoids every cut has zero variation
in every coordinate. This scalar lemma is often the convenient input for the final
finite triangulation. -/
lemma baryStep_eq_of_cuts_eq {d n r : ℕ} {u w : Fin d → ℝ}
    (h : ∀ m < d+1,
      binHeight 0 1 n r (cumCoord d u m) =
      binHeight 0 1 n r (cumCoord d w m)) (v : Fin d) :
    baryStep d n r u v = baryStep d n r w v := by
  unfold baryStep
  rw [h _ (by omega), h _ (by omega)]
end
end FamiliesProof

open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
/-- On the `b`-th chamber for a cumulative coordinate, every bin other
than `b` has already made (or has not yet made) its jump.  This tiny lemma
is the reason the cuts, rather than a Lipschitz approximation to them, are
used: it includes both *closed* endpoints, so adjacent chambers glue. -/
lemma binHeight_eq_of_different_chamber {n r b : ℕ} (hn : 0 < n)
    (hbr : b ≠ r) {x y : ℝ}
    (hx : x ∈ Set.Icc (linePoint 0 1 n b) (linePoint 0 1 n (b+1)))
    (hy : y ∈ Set.Icc (linePoint 0 1 n b) (linePoint 0 1 n (b+1))) :
    binHeight 0 1 n r x = binHeight 0 1 n r y := by
  rcases lt_or_gt_of_ne hbr with hlt|hgt
  · have hle : b+1 ≤ r := hlt
    have lx : x ≤ linePoint 0 1 n r :=
      hx.2.trans ((linePoint_le 0 1 hn (by norm_num)).2 hle)
    have ly : y ≤ linePoint 0 1 n r :=
      hy.2.trans ((linePoint_le 0 1 hn (by norm_num)).2 hle)
    rw [binHeight_of_le hn (by norm_num) lx,
        binHeight_of_le hn (by norm_num) ly]
  · have hle : r+1 ≤ b := hgt
    have lx : linePoint 0 1 n (r+1) ≤ x :=
      ((linePoint_le 0 1 hn (by norm_num)).2 hle).trans hx.1
    have ly : linePoint 0 1 n (r+1) ≤ y :=
      ((linePoint_le 0 1 hn (by norm_num)).2 hle).trans hy.1
    rw [binHeight_of_ge hn (by norm_num) lx,
        binHeight_of_ge hn (by norm_num) ly]

/-- Closed chamber form of the ``only one colour for each cut'' computation.
No positivity of the simplex coordinates is needed in this formulation;
that will be supplied when a geometric grid chamber is built.  In particular
the statement is inherited unchanged when a zero coordinate is deleted on a
face. -/
lemma baryStep_constant_of_chambers {d n r : ℕ} (hn : 0 < n)
    {u w : Fin d → ℝ} {b : ℕ → ℕ}
    (hb : ∀ m, m < d+1 → b m ≠ r)
    (hu : ∀ m, m < d+1 → cumCoord d u m ∈
      Set.Icc (linePoint 0 1 n (b m)) (linePoint 0 1 n (b m + 1)))
    (hw : ∀ m, m < d+1 → cumCoord d w m ∈
      Set.Icc (linePoint 0 1 n (b m)) (linePoint 0 1 n (b m + 1))) :
    ∀ v : Fin d, baryStep d n r u v = baryStep d n r w v := by
  intro v
  apply baryStep_eq_of_cuts_eq (u:=u) (w:=w)
    (fun m hm => binHeight_eq_of_different_chamber hn (hb m hm)
      (hu m hm) (hw m hm))
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/BinSimplex.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/PushInject.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup F] [NormedSpace ℝ F]
attribute [local instance] Classical.propDecidable Classical.decEq

def embFinset (a : E →ᵃ[ℝ] F) (ha : Function.Injective a) (t : Finset E) : Finset F :=
  t.map ⟨a, ha⟩

@[simp] lemma mem_embFinset (a : E →ᵃ[ℝ] F) (ha) (t : Finset E) (x:E) :
    a x ∈ embFinset a ha t ↔ x ∈ t := by
  simp [embFinset, ha.eq_iff]
lemma coe_embFinset (a : E →ᵃ[ℝ] F) (ha) (t : Finset E) :
    (↑(embFinset a ha t) : Set F) = a '' (t : Set E) := by
  ext y; simp [embFinset]
lemma embFinset_nonempty (a : E →ᵃ[ℝ] F) (ha) {t : Finset E} :
    (embFinset a ha t).Nonempty ↔ t.Nonempty := by
  classical
  simp [Finset.nonempty_iff_ne_empty, embFinset]
lemma embFinset_inter (a : E →ᵃ[ℝ] F) (ha) (s t : Finset E) :
    embFinset a ha (s ∩ t) = embFinset a ha s ∩ embFinset a ha t := by
  classical
  ext y
  constructor
  · intro h
    simp [embFinset] at h ⊢
    rcases h with ⟨x,⟨hx,hxt⟩,hxy⟩
    subst y
    exact ⟨⟨x,hx,rfl⟩, ⟨x,hxt,rfl⟩⟩
  · intro h
    simp [embFinset] at h ⊢
    rcases h with ⟨⟨x,hx,hy⟩,⟨z,hz,hw⟩⟩
    subst y
    have : z = x := ha (by simpa using hw)
    subst z
    exact ⟨x, ⟨hx,hz⟩, rfl⟩
lemma embFinset_subset (a : E →ᵃ[ℝ] F) (ha) {s t : Finset E} :
    embFinset a ha s ⊆ embFinset a ha t ↔ s ⊆ t := by
  classical
  constructor
  · intro h x hx
    have := h (show a x ∈ embFinset a ha s from (mem_embFinset _ _ _ _).2 hx)
    exact (mem_embFinset _ _ _ _).1 this
  · intro h y hy
    simp [embFinset] at hy ⊢
    rcases hy with ⟨x,hx,rfl⟩
    exact ⟨x,h hx,rfl⟩

lemma hull_embFinset (a : E →ᵃ[ℝ] F) (ha) (t : Finset E) :
    a '' convexHull ℝ (t : Set E) = convexHull ℝ (embFinset a ha t : Set F) := by
  simpa [coe_embFinset] using a.image_convexHull (t : Set E)

/-- Transport a geometric complex along an injective affine map.  The codomain
complex lives in the whole target space, but of course its space is contained
in the affine image.  This is the convenient version for a segment in a
higher dimensional polytope. -/
def embComplex (a : E →ᵃ[ℝ] F) (ha : Function.Injective a)
    (K : Geometry.SimplicialComplex ℝ E) : Geometry.SimplicialComplex ℝ F where
  faces := embFinset a ha '' K.faces
  isRelLowerSet_faces := by
    classical
    rintro s ⟨u,hu,rfl⟩
    refine ⟨(embFinset_nonempty a ha).2 (K.nonempty_of_mem_faces hu), ?_⟩
    intro t ht htn
    -- every subfinset of the image has a unique inverse image
    let w : Finset E := u.filter (fun x => a x ∈ t)
    have hw : w ⊆ u := Finset.filter_subset _ _
    have hmap : embFinset a ha w = t := by
      ext y
      constructor
      · intro hy
        simp [embFinset, w] at hy ⊢
        rcases hy with ⟨x, ⟨hxu,hxt⟩, hxy⟩
        simpa [← hxy] using hxt
      · intro hy
        have hys : y ∈ embFinset a ha u := ht hy
        simp [embFinset] at hys
        rcases hys with ⟨x,hxu,hxy⟩
        -- note map witness equality orientation
        subst y
        simp [embFinset, w, hxu, hy]
    refine ⟨w, ?_, hmap⟩
    apply K.down_closed hu hw
    apply (embFinset_nonempty a ha).1
    rw [hmap]
    exact htn
  indep := by
    classical
    rintro s ⟨u,hu, rfl⟩
    have hi := K.indep hu
    -- identify subtype of mapped finset with source subtype
    let g : u → embFinset a ha u := fun x => ⟨a x, (mem_embFinset _ _ _ _).2 x.property⟩
    have gi : Function.Injective g := by
      intro x y h; apply Subtype.ext; apply ha
      exact congrArg Subtype.val h
    have gs : Function.Surjective g := by
      intro y
      have hh := (Finset.mem_map.mp y.property)
      rcases hh with ⟨x,hx,hxy⟩
      refine ⟨⟨x,hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy
    let e : u ≃ embFinset a ha u := Equiv.ofBijective g ⟨gi,gs⟩
    have he (x : u) : (e x : F) = a x := rfl
    have hi' : AffineIndependent ℝ (((↑) : u → E) ∘ e.symm) :=
      hi.comp_embedding e.symm.toEmbedding
    have hm := (a.affineIndependent_iff ha).2 hi'
    -- the resulting ordered family is the inclusion of the mapped finset
    have heq : a ∘ (((↑) : u → E) ∘ e.symm) =
        ((↑) : (embFinset a ha u) → F) := by
      funext y
      have := he (e.symm y)
      simpa using this.symm
    rw [heq] at hm
    exact hm
  inter_subset_convexHull := by
    classical
    intro s t hs ht
    rcases hs with ⟨u,hu,rfl⟩
    rcases ht with ⟨v,hv,rfl⟩
    intro y hy
    have ys := hy.1
    have yt := hy.2
    rw [← hull_embFinset a ha u] at ys
    rw [← hull_embFinset a ha v] at yt
    rcases ys with ⟨x,hxu,rfl⟩
    rcases yt with ⟨z,hzv,heq⟩
    have zx : z=x := ha heq
    subst z
    have hx := K.inter_subset_convexHull hu hv ⟨hxu,hzv⟩
    have him := hull_embFinset a ha (u ∩ v)
    have goal' : a x ∈ convexHull ℝ
        (embFinset a ha (u ∩ v) : Set F) := by
      rw [← him]
      exact ⟨x, (by simpa using hx), rfl⟩
    -- coe of intersection
    simpa [embFinset_inter] using goal' 
lemma embComplex_faces_finite (a : E →ᵃ[ℝ] F) (ha : Function.Injective a)
    (K : Geometry.SimplicialComplex ℝ E) (hf : K.faces.Finite) :
    (embComplex a ha K).faces.Finite := by
  change (embFinset a ha '' K.faces).Finite
  exact hf.image _
lemma embComplex_space (a : E →ᵃ[ℝ] F) (ha : Function.Injective a)
    (K : Geometry.SimplicialComplex ℝ E) :
    (embComplex a ha K).space = a '' K.space := by
  classical
  ext y; constructor
  · intro hy
    rcases (Geometry.SimplicialComplex.mem_space_iff).1 hy with ⟨s, ⟨u,hu,rfl⟩,hys⟩
    rw [← hull_embFinset] at hys
    rcases hys with ⟨x,hxu,rfl⟩
    exact ⟨x,(Geometry.SimplicialComplex.mem_space_iff).2 ⟨u,hu,hxu⟩,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    rcases (Geometry.SimplicialComplex.mem_space_iff).1 hx with ⟨u,hu,hxu⟩
    exact (Geometry.SimplicialComplex.mem_space_iff).2
      ⟨embFinset a ha u, ⟨u,hu,rfl⟩, (by rw [← hull_embFinset]; exact ⟨x,hxu,rfl⟩)⟩
lemma embComplex_facet (a : E →ᵃ[ℝ] F) (ha : Function.Injective a)
    (K : Geometry.SimplicialComplex ℝ E) {s}
    (hs : s ∈ (embComplex a ha K).facets) :
    ∃ t ∈ K.facets, s = embFinset a ha t := by
  classical
  have hm := (Geometry.SimplicialComplex.mem_facets).1 hs
  rcases hm.1 with ⟨u,hu,rfl⟩
  refine ⟨u, ?_, rfl⟩
  refine (Geometry.SimplicialComplex.mem_facets).2 ⟨hu, ?_⟩
  intro t ht hut
  have mm := hm.2 (embFinset a ha t) ⟨t,ht,rfl⟩ ((embFinset_subset _ _).2 hut)
  exact Finset.map_injective ⟨a,ha⟩ mm
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/PushInject.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/EmbeddedInterval.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] Classical.propDecidable Classical.decEq
/-- The affine line with endpoints `l,r`, parametrised so that the unit
interval is their closed segment. -/
def lineAffine (l r : E) : ℝ →ᵃ[ℝ] E :=
  { toFun := fun t => (1-t) • l + t • r
    linear :=
      { toFun := fun t => t • (r-l)
        map_add' := by intro x y; simp [add_smul]
        map_smul' := by intro x y; simp [mul_smul] }
    map_vadd' := by intro x y; dsimp; module }
@[simp] lemma lineAffine_apply (l r : E) (x : ℝ) :
    lineAffine l r x = (1-x) • l + x • r := rfl
lemma lineAffine_injective {l r : E} (h : l ≠ r) :
    Function.Injective (lineAffine l r) := by
  intro x y he
  dsimp [lineAffine] at he
  have : (x-y) • (r-l) = (0:ℝ) • (r-l) := by
    -- subtract the displayed equality
    calc
      (x-y) • (r-l) =
          ((1-x) • l + x • r) - ((1-y) • l + y • r) := by module
      _ = 0 := sub_eq_zero.mpr he
      _ = (0:ℝ) • (r-l) := by simp
  have hn : r-l ≠ (0:E) := sub_ne_zero.mpr h.symm
  have hz : (x-y) • (r-l) = (0:E) := by simpa using this
  rcases smul_eq_zero.mp hz with hh|hh
  · exact sub_eq_zero.mp hh
  · exact (hn hh).elim
lemma lineAffine_image_Icc (l r : E) :
    lineAffine l r '' Set.Icc (0:ℝ) 1 = segment ℝ l r := by
  rw [segment_eq_image']
  congr 1
  funext t
  change (1-t) • l + t • r = l + t • (r-l)
  module
/-- Explicit embedded interval complex.  Unlike a triangulation of a hull
by only its vertices, this complex keeps every true break point.  It is useful
when a one dimensional face is processed before the higher dimensional
ordered chambers. -/
def lineComplex (l r : E) (n : ℕ) (hn : 0 < n) (h : l ≠ r) :
    Geometry.SimplicialComplex ℝ E :=
  embComplex (lineAffine l r) (lineAffine_injective h)
    (intervalComplex 0 1 n hn (by norm_num))
lemma lineComplex_faces_finite (l r : E) (n : ℕ) (hn : 0 < n) (h : l ≠ r) :
    (lineComplex l r n hn h).faces.Finite := by
  exact embComplex_faces_finite _ _ _
    (intervalComplex_faces_finite 0 1 n hn (by norm_num))
lemma lineComplex_space (l r : E) (n : ℕ) (hn : 0 < n) (h : l ≠ r) :
    (lineComplex l r n hn h).space = segment ℝ l r := by
  rw [lineComplex, embComplex_space,
      intervalComplex_space 0 1 n hn (by norm_num), lineAffine_image_Icc]
lemma lineComplex_facet (l r : E) (n : ℕ) (hn : 0 < n) (h : l ≠ r)
    {t : Finset E} (ht : t ∈ (lineComplex l r n hn h).facets) :
    ∃ m < n, t = embFinset (lineAffine l r) (lineAffine_injective h)
       { linePoint 0 1 n m, linePoint 0 1 n (m+1) } := by
  rcases embComplex_facet _ _ _ ht with ⟨u,hu,rfl⟩
  rcases intervalComplex_facet_edge 0 1 n hn (by norm_num) hu with ⟨i,hi,rfl⟩
  exact ⟨i,hi,rfl⟩
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/EmbeddedInterval.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/FineInterval.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
/-- On the standard interval, interleave `q` copies of each of `n` colours.
The copy `i` makes one jump in every block and is scaled by `1/q`; hence
all copies agree at the block vertices and stay within `1/q` of one another.
The formula, a finite sum of the ordinary interval bins, avoids any gluing. -/
def cyclicHeight (q n i : ℕ) (x : ℝ) : ℝ :=
  (∑ m ∈ Finset.range q,
    binHeight 0 1 (q*n) (m*n+i) x) / (q : ℝ)

lemma continuous_cyclicHeight (q n i : ℕ) : Continuous (cyclicHeight q n i) := by
  unfold cyclicHeight
  apply Continuous.div_const
  exact continuous_finset_sum _ (fun m hm =>
    continuous_binHeight 0 1 (q*n) (m*n+i))
lemma cyclicHeight_mem {q n i : ℕ} (hq : 0 < q) (x : ℝ) :
    cyclicHeight q n i x ∈ Set.Icc (0:ℝ) 1 := by
  unfold cyclicHeight
  have qq : (0:ℝ) < q := by exact_mod_cast hq
  constructor
  · exact div_nonneg (Finset.sum_nonneg (by
      intro m hm
      exact (binHeight_mem 0 1 (q*n) (m*n+i) x).1)) (le_of_lt qq)
  · apply (div_le_iff₀ qq).2
    have hle : (∑ m ∈ Finset.range q,
      binHeight 0 1 (q*n) (m*n+i) x) ≤
      ∑ m ∈ Finset.range q, (1:ℝ) := by
      exact Finset.sum_le_sum (by
        intro m hm
        exact (binHeight_mem 0 1 (q*n) (m*n+i) x).2)
    simpa using hle
/-- The bins are antitone in their index. This elementary inequality is often
more convenient than invoking the explicit positions of all chambers. -/
lemma binHeight_anti_right (N : ℕ) (x : ℝ) {i j : ℕ} (hij : i ≤ j) :
    binHeight 0 1 N j x ≤ binHeight 0 1 N i x := by
  dsimp [binHeight]
  have hcast : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
  have sub : (N:ℝ) * (x - 0) / (1 - 0) - (j:ℝ) ≤
      (N:ℝ) * (x - 0) / (1 - 0) - (i:ℝ) := by linarith
  exact min_le_min_left _ (max_le_max_left _ sub)
private lemma __FineInterval_sum_shift_tel (N q n i : ℕ) (x : ℝ) :
    (∑ m ∈ Finset.range q,
      binHeight 0 1 N ((m+1)*n+i) x) =
      (∑ m ∈ Finset.range q,
      binHeight 0 1 N (m*n+i) x) -
        binHeight 0 1 N i x +
        binHeight 0 1 N (q*n+i) x := by
  -- with `N` fixed this is just shifting a finite arithmetic progression
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      -- both last terms are the same break point; no property of height used
      ring
-- Adjacent/interleaved copies differ by at most one whole jump.  The proof
-- compares the chains `m*n+i ≤ m*n+j ≤ (m+1)*n+i` term by term and then
-- telescopes the latter.
lemma cyclic_partial_interleave {q n i j : ℕ} (hi : i < n)
    (hj : j < n) (hij : i ≤ j) (x : ℝ) :
    let Si := ∑ m ∈ Finset.range q,
      binHeight 0 1 (q*n) (m*n+i) x
    let Sj := ∑ m ∈ Finset.range q,
      binHeight 0 1 (q*n) (m*n+j) x
    Sj ≤ Si ∧ Si ≤ Sj + 1 := by
  dsimp
  constructor
  · exact Finset.sum_le_sum (by
      intro m hm
      apply binHeight_anti_right
      omega)
  · -- shift the chain, then bound off the first and last terms by `[0,1]`
    have chain :
        (∑ m ∈ Finset.range q,
            binHeight 0 1 (q*n) ((m+1)*n+i) x) ≤
          ∑ m ∈ Finset.range q,
            binHeight 0 1 (q*n) (m*n+j) x := by
      apply Finset.sum_le_sum
      intro m hm
      apply binHeight_anti_right
      -- `j < n` implies the cross-block inequality
      have hidx : m*n + j ≤ m*n + n + i := by omega
      have he : (m+1)*n+i = m*n+n+i := by simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      rw [he]
      exact hidx
    rw [__FineInterval_sum_shift_tel (q*n) q n i] at chain
    have hfirst := (binHeight_mem 0 1 (q*n) i x)
    have hlast := (binHeight_mem 0 1 (q*n) (q*n+i) x)
    rcases hfirst with ⟨hf0,hf1⟩
    rcases hlast with ⟨hl0,hl1⟩
    linarith
lemma cyclicHeight_dist {q n i j : ℕ} (hq : 0 < q)
    (hi : i < n) (hj : j < n) (x : ℝ) :
    |cyclicHeight q n i x - cyclicHeight q n j x| ≤ 1 / (q : ℝ) := by
  have qq : (0:ℝ) < q := by exact_mod_cast hq
  cases le_total i j with
  | inl hij =>
    have hpair := cyclic_partial_interleave (q:=q) hi hj hij x
    dsimp at hpair
    unfold cyclicHeight
    rw [abs_le]
    constructor
    · rw [← sub_div]
      have he : -(1/(q:ℝ)) = (-1)/q := by ring
      rw [he]
      apply (div_le_div_iff_of_pos_right qq).2
      linarith [hpair.1]
    · rw [← sub_div]
      apply (div_le_iff₀ qq).2
      have hunit : (1/(q:ℝ)) * q = 1 := by field_simp
      rw [hunit]
      linarith [hpair.2]
  | inr hji =>
    have hpair := cyclic_partial_interleave (q:=q) hj hi hji x
    dsimp at hpair
    unfold cyclicHeight
    rw [abs_le]
    constructor
    · rw [← sub_div]
      have he : -(1/(q:ℝ)) = (-1)/q := by ring
      rw [he]
      apply (div_le_div_iff_of_pos_right qq).2
      linarith [hpair.2]
    · rw [← sub_div]
      apply (div_le_iff₀ qq).2
      have hunit : (1/(q:ℝ)) * q = 1 := by field_simp
      rw [hunit]
      linarith [hpair.1]

/-- On the `p`th fine edge exactly colour `(p % n)` has a remaining jump.
This form, stated directly on real chambers, is inherited by embeddings. -/
lemma cyclicHeight_constant_of_edge {q n r p : ℕ}
    (hq : 0 < q) (hn : 0 < n) (hp : p < q*n)
    (hne : p % n ≠ r) (hr : r < n)
    {x y : ℝ}
    (hx : x ∈ Set.Icc (linePoint 0 1 (q*n) p)
      (linePoint 0 1 (q*n) (p+1)))
    (hy : y ∈ Set.Icc (linePoint 0 1 (q*n) p)
      (linePoint 0 1 (q*n) (p+1))) :
    cyclicHeight q n r x = cyclicHeight q n r y := by
  unfold cyclicHeight
  apply congrArg (fun t : ℝ => t / (q:ℝ))
  apply Finset.sum_congr rfl
  intro m hm
  apply binHeight_eq_of_different_chamber (n:=q*n) (r:=m*n+r) (b:=p)
    (Nat.mul_pos hq hn)
  · -- if equal, reduction modulo n gives precisely the active colour.
    intro h
    have hmody := congrArg (fun t : ℕ => t % n) h
    have : p % n = r := by
      simpa [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hr] using hmody
    exact hne this
  · exact hx
  · exact hy
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open Set
open scoped BigOperators Topology

def cyclicMap (a b : ℝ) (q n i : ℕ) (x : ℝ) : ℝ :=
  a + (b-a) * cyclicHeight q n i ((x-a)/(b-a))
lemma continuous_cyclicMap (a b : ℝ) (q n i : ℕ) :
    Continuous (cyclicMap a b q n i) := by
  unfold cyclicMap
  apply Continuous.add continuous_const
  apply Continuous.mul continuous_const
  exact (continuous_cyclicHeight q n i).comp
    (Continuous.div_const (continuous_id.sub continuous_const) _)
lemma cyclicMap_mem {a b : ℝ} (hab : a < b) {q n i : ℕ}
    (hq : 0 < q) (x : ℝ) : cyclicMap a b q n i x ∈ Set.Icc a b := by
  have hm := cyclicHeight_mem (n:=n) (i:=i) hq ((x-a)/(b-a))
  unfold cyclicMap
  constructor
  · have h := mul_nonneg (sub_nonneg.mpr (le_of_lt hab)) hm.1
    linarith
  · have h := mul_le_mul_of_nonneg_left hm.2 (sub_nonneg.mpr (le_of_lt hab))
    linarith
lemma cyclicMap_dist {a b : ℝ} (hab : a < b)
    {q n i j : ℕ} (hq : 0 < q) (hi : i < n) (hj : j < n)
    (x : ℝ) :
    |cyclicMap a b q n i x - cyclicMap a b q n j x| ≤
      (b-a) / (q:ℝ) := by
  have hb : 0 ≤ b-a := sub_nonneg.mpr (le_of_lt hab)
  have h := cyclicHeight_dist hq hi hj ((x-a)/(b-a))
  unfold cyclicMap
  rw [show a +(b-a)* cyclicHeight q n i ((x-a)/(b-a)) -
      (a +(b-a)* cyclicHeight q n j ((x-a)/(b-a))) =
      (b-a) * (cyclicHeight q n i ((x-a)/(b-a)) -
                 cyclicHeight q n j ((x-a)/(b-a))) by ring]
  rw [abs_mul]
  rw [abs_of_nonneg hb]
  convert (mul_le_mul_of_nonneg_left h hb) using 1
  any_goals rfl
  any_goals simp [div_eq_mul_inv]
lemma cyclicMap_zero {q n i : ℕ} (hq : 0 < q) (hn : 0 < n)
    (hi : i < n) {a b : ℝ} (hab : a < b) :
    cyclicMap a b q n i a = a := by
  -- every term before the first break is zero
  have h : cyclicHeight q n i 0 = 0 := by
    unfold cyclicHeight
    rw [show (0:ℝ) = 0 by rfl]
    have hp : ∀ m ∈ Finset.range q,
        binHeight 0 1 (q*n) (m*n+i) (0:ℝ) = 0 := by
      intro m hm
      apply binHeight_of_le (Nat.mul_pos hq hn) (by norm_num)
      unfold linePoint
      -- nonnegative position
      have : 0 ≤ ((m*n+i : ℕ) : ℝ) := by positivity
      positivity
    have hz : (∑ m ∈ Finset.range q,
       binHeight 0 1 (q*n) (m*n+i) (0:ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      exact hp m hm
    rw [hz]
    have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    simp
  unfold cyclicMap
  simp [show (a-a)/(b-a)=0 by ring, h]
lemma cyclicMap_one {q n i : ℕ} (hq : 0 < q) (hn : 0 < n)
    (hi : i < n) {a b : ℝ} (hab : a < b) :
    cyclicMap a b q n i b = b := by
  have harg : (b-a)/(b-a) = (1:ℝ) := by
    apply div_self
    exact ne_of_gt (sub_pos.mpr hab)
  have h : cyclicHeight q n i 1 = 1 := by
    unfold cyclicHeight
    have hp : ∀ m ∈ Finset.range q,
        binHeight 0 1 (q*n) (m*n+i) (1:ℝ) = 1 := by
      intro m hm
      have hm' : m < q := Finset.mem_range.mp hm
      apply binHeight_of_ge (Nat.mul_pos hq hn) (by norm_num)
      have h1 : m+1 ≤ q := Nat.succ_le_of_lt hm'
      have h2 : i+1 ≤ n := hi
      have hx : m*n+i+1 ≤ q*n := calc
        m*n+i+1 = m*n+(i+1) := by ring
        _ ≤ m*n+n := Nat.add_le_add_left h2 _
        _ = (m+1)*n := by ring
        _ ≤ q*n := Nat.mul_le_mul_right _ h1
      have hx' := (linePoint_le 0 1 (Nat.mul_pos hq hn) (by norm_num)).2 hx
      simpa [linePoint_end 0 1 (Nat.mul_pos hq hn)] using hx'
    have hs : (∑ _m ∈ Finset.range q, (1:ℝ)) = (q:ℝ) := by simp
    have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    have heq : (∑ m ∈ Finset.range q,
        binHeight 0 1 (q*n) (m*n+i) (1:ℝ)) = (q:ℝ) := calc
      _ = ∑ m ∈ Finset.range q, (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact hp m hm
      _ = _ := hs
    rw [heq]
    simp [hq']
    -- unfolding leaves exactly q/q
  unfold cyclicMap
  rw [harg, h]
  ring
lemma cyclicMap_constant_of_edge {a b : ℝ} (hab : a < b)
    {q n r p : ℕ} (hq : 0 < q) (hn : 0 < n) (hp : p < q*n)
    (hne : p % n ≠ r) (hr : r < n)
    {x y : ℝ}
    (hx : x ∈ Set.Icc (linePoint a b (q*n) p)
      (linePoint a b (q*n) (p+1)))
    (hy : y ∈ Set.Icc (linePoint a b (q*n) p)
      (linePoint a b (q*n) (p+1))) :
    cyclicMap a b q n r x = cyclicMap a b q n r y := by
  unfold cyclicMap
  congr 1
  congr 1
  apply cyclicHeight_constant_of_edge hq hn hp hne hr
  · constructor
    · -- affine coordinate reads the standard grid line exactly
      calc
        linePoint 0 1 (q*n) p =
            ((linePoint a b (q*n) p) - a) / (b-a) := by
              unfold linePoint
              have hq' : (q*n:ℝ) ≠ 0 := by
                exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hq hn))
              have hb' : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
              field_simp
              <;> ring
        _ ≤ (x-a)/(b-a) := by
          exact (div_le_div_iff_of_pos_right (sub_pos.mpr hab)).2
            (sub_le_sub_right hx.1 _)
    · calc
        (x-a)/(b-a) ≤ ((linePoint a b (q*n) (p+1))-a)/(b-a) :=
          (div_le_div_iff_of_pos_right (sub_pos.mpr hab)).2
            (sub_le_sub_right hx.2 _)
        _ = linePoint 0 1 (q*n) (p+1) := by
          unfold linePoint
          have hq' : (q*n:ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hq hn))
          have hb' : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
          field_simp
          <;> ring
  · constructor
    · calc
        linePoint 0 1 (q*n) p =
            ((linePoint a b (q*n) p) - a) / (b-a) := by
              unfold linePoint
              have hq' : (q*n:ℝ) ≠ 0 := by
                exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hq hn))
              have hb' : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
              field_simp
              <;> ring
        _ ≤ (y-a)/(b-a) := by
          exact (div_le_div_iff_of_pos_right (sub_pos.mpr hab)).2
            (sub_le_sub_right hy.1 _)
    · calc
        (y-a)/(b-a) ≤ ((linePoint a b (q*n) (p+1))-a)/(b-a) :=
          (div_le_div_iff_of_pos_right (sub_pos.mpr hab)).2
            (sub_le_sub_right hy.2 _)
        _ = linePoint 0 1 (q*n) (p+1) := by
          unfold linePoint
          have hq' : (q*n:ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hq hn))
          have hb' : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
          field_simp
          <;> ring
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/FineInterval.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/OrderedSimplex.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Evaluation of finitely many simplex coefficients. -/
def simplexEval {d : ℕ} (v : Fin d → E) (u : Fin d → ℝ) : E :=
  ∑ i, u i • v i
lemma continuous_simplexEval {d : ℕ} (v : Fin d → E) :
    Continuous (simplexEval v) := by
  unfold simplexEval
  fun_prop
lemma simplexEval_unit {d : ℕ} (v : Fin d → E) (i : Fin d) :
    simplexEval v (Pi.single i (1:ℝ)) = v i := by
  classical
  simp [simplexEval]

/-- For an affine independent finite family, affine coefficients with mass one
are unique. This small injectivity lemma is a useful replacement for an inverse
barycentric-coordinate API. -/
lemma simplexEval_eq {d : ℕ} {v : Fin d → E}
    (hv : AffineIndependent ℝ v)
    {u w : Fin d → ℝ} (hu : (∑ i, u i)=1) (hw : (∑ i, w i)=1)
    (h : simplexEval v u = simplexEval v w) : u = w := by
  classical
  have H := (affineIndependent_iff.mp hv)
  have hzsum : ∑ i ∈ (Finset.univ : Finset (Fin d)), (u i - w i) = 0 := by
    rw [Finset.sum_sub_distrib]
    have heq : (∑ i, u i) = (∑ i, w i) := hu.trans hw.symm
    linarith
  have hzv : ∑ i ∈ (Finset.univ : Finset (Fin d)), (u i - w i) • v i = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib]
    dsimp [simplexEval] at h
    exact sub_eq_zero.mpr h
  funext i
  have zz := H (Finset.univ : Finset (Fin d)) (fun i => u i - w i)
    hzsum hzv i (Finset.mem_univ _)
  linarith

lemma simplexEval_mem_hull {d : ℕ} (v : Fin d → E)
    {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i) (hs : (∑ i, u i)=1) :
    simplexEval v u ∈ convexHull ℝ (Set.range v) := by
  classical
  -- write as convex combination over a finset of the values (possibly repeated)
  refine Convex.sum_mem (convex_convexHull ℝ (Set.range v))
    (by intro i hi; exact hu i) (by simpa using hs) (by
      intro i hi; exact subset_convexHull ℝ (Set.range v) (Set.mem_range_self _))

end
end FamiliesProof
namespace FamiliesProof -- reopen
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A zero input coordinate contributes a zero ordered-bin coordinate.  In particular
ordered bins never introduce a new vertex on a proper face. -/
lemma baryStep_zero_of_coord_zero {d n r : ℕ} {u : Fin d → ℝ}
    {i : Fin d} (hz : u i = 0) : baryStep d n r u i = 0 := by
  unfold baryStep
  have hs : cumCoord d u (i.val+1) = cumCoord d u i.val := by
    -- insert the single term; this proof avoids monotonicity and works on all points
    rw [cumCoord_succ i.isLt, hz, add_zero]
  rw [hs]
  ring

/-- If two coefficient vectors have the same ordered cumulative cuts for a grid
chamber, their evaluations for a colour outside these cuts agree.  This is the
coordinate-free form used after pushing a standard simplex into ambient space. -/
lemma simplexEval_step_eq_of_chambers {d n r : ℕ} (hn : 0 < n)
    {v : Fin d → E} {u w : Fin d → ℝ} {b : ℕ → ℕ}
    (hb : ∀ m, m < d+1 → b m ≠ r)
    (hu : ∀ m, m < d+1 → cumCoord d u m ∈
      Set.Icc (linePoint 0 1 n (b m)) (linePoint 0 1 n (b m+1)))
    (hw : ∀ m, m < d+1 → cumCoord d w m ∈
      Set.Icc (linePoint 0 1 n (b m)) (linePoint 0 1 n (b m+1))) :
    simplexEval v (baryStep d n r u) = simplexEval v (baryStep d n r w) := by
  unfold simplexEval
  have h := baryStep_constant_of_chambers (d:=d) (n:=n) (r:=r) hn hb hu hw
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i]

lemma continuous_stepEval {d n r : ℕ} (v : Fin d → E) :
    Continuous (fun u : Fin d → ℝ => simplexEval v (baryStep d n r u)) := by
  unfold simplexEval
  exact continuous_finset_sum Finset.univ (by
    intro i hi
    exact (continuous_baryStep _ _ _ i).smul continuous_const)

/-- Ordered-bin evaluation lands back in the simplex. -/
lemma stepEval_mem_hull {d n r : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hr : r < n) (v : Fin d → E) {u : Fin d → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hs : (∑ i, u i)=1) :
    simplexEval v (baryStep d n r u) ∈ convexHull ℝ (Set.range v) := by
  refine simplexEval_mem_hull v (baryStep_nonneg hn hu)
    (sum_baryStep hd hn hr hs)

/-- Membership of a displayed affine combination in an extreme face forces each
vertex with positive weight into the face.  This lemma uses no independence:
it is just the two-term definition of an extreme subset. -/
lemma IsExtreme.mem_of_pos_coeff {d : ℕ} {v : Fin d → E}
    {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i) (hs : (∑ i, u i)=1)
    {A B : Set E} (hv : ∀ i, v i ∈ A) (hcv : Convex ℝ A)
    (hB : IsExtreme ℝ A B) (hmem : simplexEval v u ∈ B)
    (i : Fin d) (hi : 0 < u i) : v i ∈ B := by
  classical
  have hui_le : u i ≤ 1 := by
    calc
      _ ≤ ∑ j, u j := Finset.single_le_sum (fun j hj => hu j) (Finset.mem_univ i)
      _ = 1 := hs
  by_cases hone : u i = 1
  · -- all remaining coordinates are zero
    have hz : ∀ j, j ≠ i → u j = 0 := by
      intro j hj
      have bound : u j + u i ≤ ∑ x, u x := by
        have hneq : j ∈ (Finset.univ.erase i : Finset (Fin d)) := by
          exact Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
        have hle : u j ≤ ∑ x ∈ ((Finset.univ : Finset (Fin d)).erase i), u x :=
          Finset.single_le_sum (fun x hx => hu x) hneq
        have hdecomp : ∑ x, u x = u i +
              ∑ x ∈ ((Finset.univ : Finset (Fin d)).erase i), u x := by
          exact (Finset.add_sum_erase (s:=Finset.univ) (f:=u)
            (Finset.mem_univ i)).symm
        linarith
      have : u j ≤ 0 := by rw [hs, hone] at bound; linarith
      exact le_antisymm this (hu j)
    have hx : simplexEval v u = v i := by
      unfold simplexEval
      classical
      have hh : (∑ j ∈ (Finset.univ : Finset (Fin d)), u j • v j) =
            u i • v i :=
        Finset.sum_eq_single i
          (by intro j hj hji; simp [hz j hji])
          (by simp)
      simpa [hone] using hh
    exact hx ▸ hmem
  · have hlt : u i < 1 := lt_of_le_of_ne hui_le hone
    -- evaluate the other (renormalised) coordinates
    let w : Fin d → ℝ := fun j => if j = i then 0 else u j / (1-u i)
    have honepos : 0 < 1-u i := sub_pos.mpr hlt
    have hwpos : ∀ j, 0 ≤ w j := by
      intro j
      dsimp [w]
      split_ifs
      · exact le_rfl
      · exact div_nonneg (hu j) (le_of_lt honepos)
    have he : ∑ j ∈ ((Finset.univ : Finset (Fin d)).erase i), u j = 1 - u i := by
      calc _ = (∑ j, u j) - u i := Finset.sum_erase_eq_sub (f:=u) (Finset.mem_univ i)
           _ = _ := by rw [hs]
    have hws : (∑ j, w j)=1 := by
      -- pull out the common denominator
      change (∑ j : Fin d, (if j = i then 0 else u j / (1-u i))) = 1
      rw [← Finset.add_sum_erase (s:=Finset.univ)
            (f:= fun j : Fin d => (if j = i then 0 else u j / (1-u i)))
            (Finset.mem_univ i)]
      -- simplify the removed coordinate before moving the denominator out
      simp only [ite_true, add_zero]
      have hrest :
          (∑ j ∈ ((Finset.univ : Finset (Fin d)).erase i),
              (if j = i then 0 else u j / (1-u i))) =
          ∑ j ∈ ((Finset.univ : Finset (Fin d)).erase i),
              u j / (1-u i) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hji : j ≠ i := Finset.ne_of_mem_erase hj
            simp [hji]
      rw [hrest, ← Finset.sum_div, he]
      simpa using div_self (ne_of_gt honepos)
    let y : E := simplexEval v w
    have hyA : y ∈ A := by
      exact hcv.sum_mem (by intro j hj; exact hwpos j) hws (by intro j hj; exact hv j)
    have hxEq : simplexEval v u = AffineMap.lineMap y (v i) (u i) := by
      classical
      dsimp [simplexEval, y, w]
      rw [AffineMap.lineMap_apply_module]
      symm
      -- distribute left factor over all w and collect all coordinates
      -- first convenient component identities
      have comp (j : Fin d) :
          (1 - u i) • (if j = i then (0:ℝ) else u j / (1-u i)) • v j =
            (if j = i then (0:ℝ) else u j) • v j := by
          by_cases hji : j = i
          · simp [hji]
          · have hne : (1-u i) ≠ 0 := ne_of_gt honepos
            simp [hji, smul_smul, hne, mul_div_cancel₀]
      -- realize the `lineMap` expression as split sums
      -- ring-like operation but E-module only
      calc
        (1 - u i) • (∑ j : Fin d, (if j=i then (0:ℝ) else u j/(1-u i)) • v j)
            + u i • v i
          = (∑ j : Fin d,
                  ((1-u i) * (if j=i then (0:ℝ) else u j/(1-u i))) • v j)
              + u i • v i := by rw [Finset.smul_sum]; simp_rw [smul_smul]
        _ = (∑ j : Fin d, (if j=i then (0:ℝ) else u j) • v j)
              + u i • v i := by
            apply congrArg (· + u i • v i)
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j = i
            · simp [hji]
            · have hne : (1-u i) ≠ 0 := ne_of_gt honepos
              simp only [if_neg hji]
              rw [mul_div_cancel₀ _ hne]
        _ = ∑ j : Fin d, u j • v j := by
            have hh :
                (∑ j ∈ (Finset.univ : Finset (Fin d)),
                    (if j=i then (0:ℝ) else u j) • v j) =
                ∑ j ∈ ((Finset.univ : Finset (Fin d)).erase i), u j • v j := by
                  calc
                    _ = ∑ j ∈ ((Finset.univ : Finset (Fin d)).erase i),
                          (if j=i then (0:ℝ) else u j) • v j :=
by
                          rw [← Finset.add_sum_erase (s:=Finset.univ)
                            (f:= fun j : Fin d =>
                              (if j=i then (0:ℝ) else u j) • v j)
                            (Finset.mem_univ i)]
                          simp
                    _ = _ := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      have hji : j ≠ i := Finset.ne_of_mem_erase hj
                      simp [hji]
            rw [hh, add_comm]
            exact (Finset.add_sum_erase (s:=Finset.univ)
              (f:= fun j : Fin d => u j • v j)
              (Finset.mem_univ i))
    have hopen : simplexEval v u ∈ openSegment ℝ y (v i) := by
      rw [hxEq]
      exact lineMap_mem_openSegment ℝ y (v i) ⟨hi, hlt⟩
    exact hB.right_mem_of_mem_openSegment hyA (hv i) hmem hopen

/-- Ordered-bin maps preserve every extreme face of the simplex. -/
lemma stepEval_mem_extreme {d n r : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hr : r < n) {v : Fin d → E} {u : Fin d → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hs : (∑ i, u i)=1)
    {A B : Set E} (hcv : Convex ℝ A) (hv : ∀ i, v i ∈ A)
    (hconB : Convex ℝ B) (hB : IsExtreme ℝ A B) (hmem : simplexEval v u ∈ B) :
    simplexEval v (baryStep d n r u) ∈ B := by
  -- Every new positive coefficient had an old positive coefficient at the same index.
  have hsupp : ∀ i, 0 < baryStep d n r u i → 0 < u i := by
    intro i hi'
    have hi : 0 ≤ u i := hu i
    exact lt_of_le_of_ne hi (by
      intro hz
      have := baryStep_zero_of_coord_zero (d:=d) (n:=n) (r:=r) (u:=u)
        (i:=i) hz.symm
      linarith)
  have hvals : ∀ i, 0 ≤ baryStep d n r u i :=
    baryStep_nonneg hn hu
  -- zero coefficients can be assigned any dummy point of the face
  have hnon : B.Nonempty := ⟨_, hmem⟩
  let z : Fin d → E := fun i =>
    if hz : baryStep d n r u i = 0 then hnon.some else v i
  have hzin : ∀ i, z i ∈ B := by
    intro i
    by_cases hz : baryStep d n r u i = 0
    · exact (by simpa [z, hz] using hnon.some_mem)
    · simpa [z, hz] using
        (IsExtreme.mem_of_pos_coeff hu hs hv hcv hB hmem i
          (hsupp i (lt_of_le_of_ne (hvals i) (Ne.symm hz))))
  -- Replace zero-weight vertices by the dummy so every point lies in `B`; the sum is unchanged.
  have heval : simplexEval v (baryStep d n r u) =
        simplexEval z (baryStep d n r u) := by
      unfold simplexEval
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hz : baryStep d n r u i = 0
      · simp [hz]
      · simp [z, hz]
  rw [heval]
  exact hconB.sum_mem (by intro i hi; exact hvals i)
    (sum_baryStep hd hn hr hs) (by intro i hi; exact hzin i)
end
end FamiliesProof


end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/OrderedSimplex.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/Chambers.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
/-- The closed ordered chamber in coefficient space. Cuts include both endpoints
0 and d, which makes these definitions agree under deleted vertices. -/
def coeffSimplex (d : ℕ) : Set (Fin d → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ (∑ i, u i) = 1}
def coeffChamber (d n : ℕ) (b : Fin (d+1) → ℕ) : Set (Fin d → ℝ) :=
  coeffSimplex d ∩ ⋂ m : Fin (d+1),
    (cumCoord d · m.val) ⁻¹' Set.Icc (linePoint 0 1 n (b m))
      (linePoint 0 1 n (b m + 1))

lemma coeffChamber_mem {d n : ℕ} {b : Fin (d+1) → ℕ} {u : Fin d → ℝ} :
    u ∈ coeffChamber d n b ↔
      (∀ i, 0 ≤ u i) ∧ (∑ i, u i) = 1 ∧ ∀ m : Fin (d+1),
        cumCoord d u m.val ∈ Set.Icc (linePoint 0 1 n (b m))
          (linePoint 0 1 n (b m+1)) := by
  simp [coeffChamber, coeffSimplex]
  aesop
lemma coeffChamber_nonneg {d n} {b : Fin (d+1) → ℕ} {u : Fin d → ℝ}
    (h : u ∈ coeffChamber d n b) (i : Fin d) : 0 ≤ u i :=
  (coeffChamber_mem.mp h).1 i
lemma coeffChamber_mass {d n} {b : Fin (d+1) → ℕ} {u : Fin d → ℝ}
    (h : u ∈ coeffChamber d n b) : (∑ i, u i) = 1 :=
  (coeffChamber_mem.mp h).2.1
lemma coeffChamber_cut {d n} {b : Fin (d+1) → ℕ} {u : Fin d → ℝ}
    (h : u ∈ coeffChamber d n b) (m : Fin (d+1)) :
    cumCoord d u m.val ∈ Set.Icc (linePoint 0 1 n (b m)) (linePoint 0 1 n (b m+1)) :=
  (coeffChamber_mem.mp h).2.2 m

lemma convex_coeffSimplex (d : ℕ) : Convex ℝ (coeffSimplex d) := by
  intro u hu w hw a c ha hc hac
  constructor
  · intro i
    dsimp
    exact add_nonneg (mul_nonneg ha (hu.1 i)) (mul_nonneg hc (hw.1 i))
  · change (∑ i, (a * u i + c * w i)) = 1
    rw [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
    rw [hu.2, hw.2]
    linarith
lemma isClosed_coeffSimplex (d : ℕ) : IsClosed (coeffSimplex d) := by
  have cl (i : Fin d) : IsClosed {u : Fin d → ℝ | 0 ≤ u i} := by
    exact isClosed_le continuous_const (continuous_apply i)
  have cs : IsClosed {u : Fin d → ℝ | (∑ i, u i) = 1} := by
    exact isClosed_eq (by fun_prop) continuous_const
  have : coeffSimplex d =
      (⋂ i : Fin d, {u : Fin d → ℝ | 0 ≤ u i}) ∩ {u : Fin d → ℝ | (∑ i, u i)=1} := by
    ext u
    simp [coeffSimplex]
  rw [this]
  exact (isClosed_iInter cl).inter cs
lemma isCompact_coeffSimplex (d : ℕ) : IsCompact (coeffSimplex d) := by
  -- finite-dimensional Heine-Borel; all coordinates lie between 0 and 1
  have hbdd : Bornology.IsBounded (coeffSimplex d) := by
    -- pi bounded criterion for real-valued functions
    refine Metric.isBounded_iff.mpr ?_
    refine ⟨2, ?_⟩
    intro u hu w hw
    -- sup/Euclidean pi metric estimate coordinates in [0,1]
    have bound (i : Fin d) : |u i - w i| ≤ 1 := by
      have ui0 := hu.1 i
      have wi0 := hw.1 i
      have ui1 : u i ≤ 1 := by
        calc u i ≤ ∑ j ∈ (Finset.univ : Finset (Fin d)), u j :=
              Finset.single_le_sum (fun j hj => hu.1 j) (Finset.mem_univ i)
             _ = 1 := hu.2
      have wi1 : w i ≤ 1 := by
        calc w i ≤ ∑ j ∈ (Finset.univ : Finset (Fin d)), w j :=
              Finset.single_le_sum (fun j hj => hw.1 j) (Finset.mem_univ i)
             _ = 1 := hw.2
      rw [abs_le]
      constructor <;> linarith
    -- dist on Pi = supremum; use max bound
    rw [dist_pi_le_iff (by norm_num : 0 ≤ (2:ℝ))]
    intro i
    have hi := bound i
    rw [Real.dist_eq] -- abs diff
    linarith
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_coeffSimplex d, hbdd⟩

lemma convex_coeffChamber (d n : ℕ) (b : Fin (d+1) → ℕ) :
    Convex ℝ (coeffChamber d n b) := by
  apply Convex.inter (convex_coeffSimplex d)
  apply convex_iInter
  intro m
  let f : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := (cumCoord d · m.val)
      map_add' := by
        intro x y
        simp [cumCoord, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp [cumCoord, Finset.mul_sum] }
  exact Convex.linear_preimage (convex_Icc _ _) f
lemma isClosed_coeffChamber (d n : ℕ) (b : Fin (d+1) → ℕ) :
    IsClosed (coeffChamber d n b) := by
  exact (isClosed_coeffSimplex d).inter
    (isClosed_iInter (fun m =>
      (isClosed_Icc).preimage (continuous_cumCoord d m.val)))
lemma isCompact_coeffChamber (d n : ℕ) (b : Fin (d+1) → ℕ) :
    IsCompact (coeffChamber d n b) := by
  exact (isCompact_coeffSimplex d).of_isClosed_subset
    (isClosed_coeffChamber d n b) (inter_subset_left)

/-- On a chamber all copies except those indexed by its crossed bins are
constant.  This is the exact closed-cell equality (also for endpoints),
not an `interior` statement. -/
lemma step_eq_on_coeffChamber {d n r : ℕ} (hn : 0 < n)
    {b : Fin (d+1) → ℕ} (hb : ∀ m, b m ≠ r)
    {u w : Fin d → ℝ}
    (hu : u ∈ coeffChamber d n b) (hw : w ∈ coeffChamber d n b) :
    ∀ i, baryStep d n r u i = baryStep d n r w i := by
  apply baryStep_constant_of_chambers hn (b:= fun m =>
    if h : m < d+1 then b ⟨m,h⟩ else 0)
  · intro m hm
    simp [hm, hb]
  · intro m hm
    simpa [hm] using coeffChamber_cut hu (⟨m,hm⟩ : Fin (d+1))
  · intro m hm
    simpa [hm] using coeffChamber_cut hw (⟨m,hm⟩ : Fin (d+1))

/-- Ordered evaluation into an arbitrary simplex is constant under the
same chamber condition. -/
lemma stepEval_eq_on_coeffChamber {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {d n r : ℕ} (hn : 0 < n)
    {b : Fin (d+1) → ℕ} (hb : ∀ m, b m ≠ r)
    (v : Fin d → E) {u w : Fin d → ℝ}
    (hu : u ∈ coeffChamber d n b) (hw : w ∈ coeffChamber d n b) :
    simplexEval v (baryStep d n r u) = simplexEval v (baryStep d n r w) := by
  unfold simplexEval
  apply Finset.sum_congr rfl
  intro i hi
  rw [step_eq_on_coeffChamber hn hb hu hw i]

end
end FamiliesProof
namespace FamiliesProof
open Set
open scoped BigOperators
noncomputable section
/-- Only the genuine, internal cuts need to avoid a colour.  Endpoints do not
contribute any variation. This is the useful sharp `card - 1` form of the
closed chamber computation. -/
lemma step_eq_on_coeffChamber_internal {d n r : ℕ} (hn : 0 < n)
    {b : Fin (d+1) → ℕ}
    (hb : ∀ m : Fin (d+1), 0 < m.val → m.val < d → b m ≠ r)
    {u w : Fin d → ℝ}
    (hu : u ∈ coeffChamber d n b) (hw : w ∈ coeffChamber d n b) :
    ∀ i, baryStep d n r u i = baryStep d n r w i := by
  apply baryStep_eq_of_cuts_eq
  intro m hm
  rcases Nat.eq_zero_or_pos m with hzero | hpos
  · subst m
    simp [cumCoord]
  have hle : m ≤ d := by omega
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · have bne : b ⟨m, by omega⟩ ≠ r := hb ⟨m, by omega⟩ hpos hlt
    exact binHeight_eq_of_different_chamber hn bne
      (coeffChamber_cut hu ⟨m, by omega⟩)
      (coeffChamber_cut hw ⟨m, by omega⟩)
  · subst m
    rw [cumCoord_large u (le_rfl), cumCoord_large w (le_rfl)]
    rw [coeffChamber_mass hu, coeffChamber_mass hw]
lemma stepEval_eq_on_coeffChamber_internal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {d n r : ℕ} (hn : 0 < n)
    {b : Fin (d+1) → ℕ}
    (hb : ∀ m : Fin (d+1), 0 < m.val → m.val < d → b m ≠ r)
    (v : Fin d → E) {u w : Fin d → ℝ}
    (hu : u ∈ coeffChamber d n b) (hw : w ∈ coeffChamber d n b) :
    simplexEval v (baryStep d n r u) = simplexEval v (baryStep d n r w) := by
  unfold simplexEval
  apply Finset.sum_congr rfl
  intro i hi
  rw [step_eq_on_coeffChamber_internal hn hb hu hw i]
end
end FamiliesProof

namespace FamiliesProof
open Set
open scoped BigOperators
noncomputable section

/-- Every coefficient with nonnegative mass one determines a closed grid chamber.
The bins only need to be fixed on the internal cuts.  It is convenient to keep
cuts `0` and `d` in the index too: those harmless witnesses allow the same
formula after deleting a vertex on a face. -/
lemma coeffSimplex_exists_chamber {d n : ℕ} (hn : 0 < n)
    {u : Fin d → ℝ} (hu : u ∈ coeffSimplex d) :
    ∃ b : Fin (d+1) → ℕ,
      (∀ m : Fin (d+1), b m < n) ∧ u ∈ coeffChamber d n b := by
  classical
  have hcut : ∀ m : Fin (d+1),
      cumCoord d u m.val ∈ Set.Icc (0:ℝ) 1 := by
    intro m
    have mono := cumCoord_mono hu.1
    have lo : (0:ℝ) ≤ cumCoord d u m.val := by
      have z := mono (Nat.zero_le m.val)
      simpa [cumCoord_zero] using z
    have mm : m.val ≤ d := by omega
    have hi : cumCoord d u m.val ≤ (1:ℝ) := by
      have q := mono mm
      simpa [cumCoord_large (u:=u) (m:=d), hu.2] using q
    exact ⟨lo, hi⟩
  have bins : ∀ m : Fin (d+1), ∃ a : ℕ, a < n ∧
      cumCoord d u m.val ∈ Set.Icc (linePoint 0 1 n a)
        (linePoint 0 1 n (a+1)) := by
    intro m
    simpa using (exists_between_linePoints 0 1 (cumCoord d u m.val)
      hn (by norm_num : (0:ℝ)<1) (hcut m))
  choose b hb hr using bins
  refine ⟨b, hb, ?_⟩
  exact (coeffChamber_mem.mpr ⟨hu.1, hu.2, hr⟩)

/-- Distinct moving colours on a chamber are represented by its internal cuts.
Keeping these as an explicit `Finset.image` is useful: no multiplicity of equal
or endpoint cuts is charged. -/
def chamberInternal (d : ℕ) (b : Fin (d+1) → ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun m : Fin (d+1) => 0 < m.val ∧ m.val < d)).image b

lemma mem_chamberInternal {d r : ℕ} {b : Fin (d+1) → ℕ} :
    r ∈ chamberInternal d b ↔
      ∃ m : Fin (d+1), (0 < m.val ∧ m.val < d) ∧ b m = r := by
  classical
  simp [chamberInternal]

lemma card_chamberInternal_le (d : ℕ) (b : Fin (d+1) → ℕ) :
    (chamberInternal d b).card + 1 ≤ max 1 d := by
  classical
  by_cases hd : d = 0
  · subst d
    unfold chamberInternal
    simp
  have hdpos : 0 < d := Nat.zero_lt_of_ne_zero hd
  let T : Finset (Fin (d+1)) :=
    Finset.univ.filter (fun m : Fin (d+1) => 0 < m.val ∧ m.val < d)
  let z : Fin (d+1) := ⟨0, by omega⟩
  let last : Fin (d+1) := ⟨d, by omega⟩
  let R : Finset (Fin (d+1)) := Finset.univ.erase z
  have sub : T ⊆ R := by
    intro x hx
    have hp := (Finset.mem_filter.mp hx).2
    apply Finset.mem_erase.mpr
    constructor
    · intro h
      have ez := congrArg Fin.val h
      dsimp [z] at ez
      omega
    · simp
  have lastR : last ∈ R := by
    apply Finset.mem_erase.mpr
    constructor
    · intro h
      have ez := congrArg Fin.val h
      dsimp [last,z] at ez
      omega
    · simp
  have lastN : last ∉ T := by
    dsimp [T,last]
    simp
  have strict : T ⊂ R := Finset.ssubset_iff_subset_ne.mpr
    ⟨sub, by intro h; exact lastN (h ▸ lastR)⟩
  have ltcard : T.card < R.card := Finset.card_lt_card strict
  have rc : R.card = d := by
    dsimp [R, z]
    simp
  have tc : (chamberInternal d b).card ≤ T.card := by
    change (T.image b).card ≤ T.card
    exact Finset.card_image_le
  calc
    (chamberInternal d b).card + 1 ≤ T.card + 1 := Nat.add_le_add_right tc 1
    _ ≤ d := by omega
    _ ≤ max 1 d := Nat.le_max_right _ _

/-- Sharp form in positive dimension; this is the number eventually charged to
colours. -/
lemma card_chamberInternal_plus_one {d : ℕ} (hd : 0 < d)
    (b : Fin (d+1) → ℕ) : (chamberInternal d b).card + 1 ≤ d := by
  have h := card_chamberInternal_le d b
  simpa [Nat.max_eq_right (by omega : 1 ≤ d)] using h

/-- Closed chamber equality outside the charged finite set. -/
lemma stepEval_eq_of_not_mem_internal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {d n r : ℕ} (hn : 0 < n)
    {b : Fin (d+1) → ℕ} (hr : r ∉ chamberInternal d b)
    (v : Fin d → E) {u w : Fin d → ℝ}
    (hu : u ∈ coeffChamber d n b) (hw : w ∈ coeffChamber d n b) :
    simplexEval v (baryStep d n r u) = simplexEval v (baryStep d n r w) := by
  apply stepEval_eq_on_coeffChamber_internal hn _ v hu hw
  intro m hm0 hmd heq
  apply hr
  exact mem_chamberInternal.mpr ⟨m, ⟨hm0, hmd⟩, heq⟩

end
end FamiliesProof

namespace FamiliesProof
open Set
open scoped BigOperators
noncomputable section
lemma coeffChamber_subset_simplex (d n : ℕ) (b : Fin (d+1) → ℕ) :
    coeffChamber d n b ⊆ coeffSimplex d := inter_subset_left

/-- Rewrite the grid construction as a finite cover (`Fin`-valued chamber indices),
not the infinite `ℕ`-indexed definition.  Adjacent chambers overlap on their
closed cuts; this formulation makes pasting on their intersections immediate. -/
lemma iUnion_coeffChamber_fin {d n : ℕ} (hn : 0 < n) :
    (⋃ b : Fin (d+1) → Fin n,
      coeffChamber d n (fun m => (b m).val)) = coeffSimplex d := by
  ext u
  constructor
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨b, hb⟩
    exact coeffChamber_subset_simplex _ _ _ hb
  · intro h
    obtain ⟨b, hb_lt, hu⟩ := coeffSimplex_exists_chamber hn h
    let b' : Fin (d+1) → Fin n := fun m => ⟨b m, hb_lt m⟩
    have hu' : u ∈ coeffChamber d n (fun m => (b' m).val) := by
      exact hu
    exact Set.mem_iUnion.mpr ⟨b', hu'⟩

/-- Every geometric grid chamber in coefficient space is closed.  Together with
`iUnion_coeffChamber_fin` this is the finite closed-cover input to a global
pasting construction. -/
lemma coeffChamber_fin_closed {d n : ℕ} (b : Fin (d+1) → Fin n) :
    IsClosed (coeffChamber d n (fun m => (b m).val)) :=
  isClosed_coeffChamber _ _ _

end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/Chambers.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/CyclicSimplex.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The ordered cumulative-coordinate map with colours interleaved `q` times.
Unlike a single ordered bin, all colours now stay within distance `1/q` on
all initial cuts. -/
def cycStep (d q n r : ℕ) (u : Fin d → ℝ) (i : Fin d) : ℝ :=
  cyclicHeight q n r (cumCoord d u (i.val+1)) -
    cyclicHeight q n r (cumCoord d u i.val)
lemma continuous_cycStep (d q n r : ℕ) (i : Fin d) :
    Continuous (fun u : Fin d → ℝ => cycStep d q n r u i) := by
  unfold cycStep
  exact ((continuous_cyclicHeight _ _ _).comp (continuous_cumCoord d _)).sub
    ((continuous_cyclicHeight _ _ _).comp (continuous_cumCoord d _))

lemma cyclicHeight_mono {q n r : ℕ} (_hq : 0 < q) (_hn : 0 < n) :
    Monotone (cyclicHeight q n r) := by
  intro x y hxy
  unfold cyclicHeight
  have hterm (m : ℕ) :
      binHeight 0 1 (q*n) (m*n+r) x ≤
      binHeight 0 1 (q*n) (m*n+r) y := by
    dsimp [binHeight]
    have hs : (q*n:ℝ) * (x - 0) / (1-0) - (m*n+r:ℕ) ≤
      (q*n:ℝ) * (y - 0) / (1-0) - (m*n+r:ℕ) := by
      have hp : 0 ≤ (q*n:ℝ) := by exact_mod_cast (Nat.zero_le (q*n))
      norm_num
      exact mul_le_mul_of_nonneg_left hxy hp
    exact min_le_min_left _ (max_le_max_left _ (by exact_mod_cast hs))
  have qs : 0 ≤ (q:ℝ) := by exact_mod_cast (Nat.zero_le q)
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun m hm => hterm m)) qs
lemma cycStep_nonneg {d q n r : ℕ} (hq : 0 < q) (hn : 0 < n)
    {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i) (v : Fin d) :
    0 ≤ cycStep d q n r u v := by
  unfold cycStep
  exact sub_nonneg.mpr (cyclicHeight_mono hq hn (cumCoord_mono hu (Nat.le_succ _)))

@[simp] lemma cyclicHeight_zero {q n r : ℕ} (hq : 0 < q) :
    cyclicHeight q n r 0 = 0 := by
  unfold cyclicHeight
  have hzero :
      (∑ m ∈ Finset.range q, binHeight 0 1 (q*n) (m*n+r) (0:ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    unfold binHeight
    norm_num
    have mp : (0:ℝ) ≤ m := by exact_mod_cast (Nat.zero_le m)
    have np : (0:ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
    have rp : (0:ℝ) ≤ r := by exact_mod_cast (Nat.zero_le r)
    have le : -(m:ℝ)*n-r ≤ (0:ℝ) := by nlinarith
    have le' : -(r:ℝ) + -((m:ℝ)*n) ≤ (0:ℝ) := by nlinarith
    rw [max_eq_left le']
    norm_num
  rw [hzero]
  simp
@[simp] lemma cyclicHeight_one {q n r : ℕ} (hq : 0 < q) (hn : 0 < n)
    (hr : r < n) : cyclicHeight q n r 1 = 1 := by
  unfold cyclicHeight
  have hterm : ∀ m < q,
      binHeight 0 1 (q*n) (m*n+r) (1:ℝ) = 1 := by
    intro m hm
    rw [binHeight_of_ge (Nat.mul_pos hq hn) (by norm_num)]
    unfold linePoint
    have h : (m*n+r+1:ℕ) ≤ q*n := by
      have hm1 : m+1 ≤ q := hm
      calc
        m*n+r+1 ≤ m*n+n := by omega
        _ = (m+1)*n := by ring
        _ ≤ q*n := Nat.mul_le_mul_right n hm1
    norm_num
    have h' : (m:ℝ) * n + r + 1 ≤ (q:ℝ) * n := by
      exact_mod_cast h
    exact (by
      change ((m:ℝ) * n + (r:ℝ) + 1) / ((q:ℝ)*n) ≤ (1:ℝ)
      apply (div_le_one ?_).2 h'
      have qq : (0:ℝ) < q := by exact_mod_cast hq
      have nn : (0:ℝ) < n := by exact_mod_cast hn
      exact (mul_pos qq nn))
  have hsum :
      (∑ m ∈ Finset.range q,
        binHeight 0 1 (q*n) (m*n+r) (1:ℝ)) = (q:ℝ) := by
    calc
      _ = ∑ m ∈ Finset.range q, (1:ℝ) := by
          apply Finset.sum_congr rfl
          intro m hm
          exact hterm m (Finset.mem_range.mp hm)
      _ = (q:ℝ) := by simp
  rw [hsum]
  have qq : (q:ℝ) ≠ 0 := by exact_mod_cast (Ne.symm (Nat.ne_of_lt hq))
  exact div_self qq

lemma sum_cycStep {d q n r : ℕ} (hd : 0 < d) (hq : 0 < q) (hn : 0 < n)
    (hr : r < n) {u : Fin d → ℝ} (hs : (∑ i, u i) = 1) :
    (∑ i, cycStep d q n r u i) = 1 := by
  let H : ℕ → ℝ := fun m => cyclicHeight q n r (cumCoord d u m)
  have tel : ∀ m : ℕ, (∑ i ∈ Finset.range m, (H (i+1) - H i)) = H m - H 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  have hd' : cumCoord d u d = 1 := by rw [cumCoord_large u (le_rfl), hs]
  change (∑ i : Fin d, (H (i.val+1) - H i.val)) = 1
  rw [Fin.sum_univ_eq_sum_range (fun m => H (m+1)-H m) d, tel d]
  simp [H, hd', cyclicHeight_one hq hn hr, cyclicHeight_zero hq]

lemma cycStep_zero_of_coord_zero {d q n r : ℕ} {u : Fin d → ℝ}
    {i : Fin d} (hz : u i = 0) : cycStep d q n r u i = 0 := by
  unfold cycStep
  have hh : cumCoord d u (i.val+1) = cumCoord d u i.val := by
    rw [cumCoord_succ i.isLt, hz, add_zero]
  rw [hh]
  ring
lemma continuous_cycEval {d q n r : ℕ} (v : Fin d → E) :
    Continuous (fun u : Fin d → ℝ => simplexEval v (cycStep d q n r u)) := by
  unfold simplexEval
  exact continuous_finset_sum _ (fun i hi =>
    (continuous_cycStep _ _ _ _ i).smul continuous_const)
lemma cycEval_mem_hull {d q n r : ℕ} (hd : 0 < d) (hq : 0 < q) (hn : 0 < n)
    (hr : r < n) (v : Fin d → E) {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i)
    (hs : (∑ i, u i)=1) :
    simplexEval v (cycStep d q n r u) ∈ convexHull ℝ (Set.range v) := by
  exact simplexEval_mem_hull v (cycStep_nonneg hq hn hu)
    (sum_cycStep hd hq hn hr hs)
/-- A face-compatible version of `stepEval_mem_extreme`, independent of any
chosen embedding of the simplex. -/
lemma cycEval_mem_extreme {d q n r : ℕ} (hd : 0 < d) (hq : 0 < q) (hn : 0 < n)
    (hr : r < n) {v : Fin d → E} {u : Fin d → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hs : (∑ i, u i)=1)
    {A B : Set E} (hcv : Convex ℝ A) (hv : ∀ i, v i ∈ A)
    (hconB : Convex ℝ B) (hB : IsExtreme ℝ A B)
    (hmem : simplexEval v u ∈ B) :
    simplexEval v (cycStep d q n r u) ∈ B := by
  have vals : ∀ i, 0 ≤ cycStep d q n r u i := cycStep_nonneg hq hn hu
  have supp : ∀ i, 0 < cycStep d q n r u i → 0 < u i := by
    intro i hi'
    have hi : 0 ≤ u i := hu i
    exact lt_of_le_of_ne hi (by
      intro zz
      rw [cycStep_zero_of_coord_zero (d:=d) (q:=q) (n:=n) (r:=r) (u:=u)
        (i:=i) zz.symm] at hi'
      exact (lt_irrefl 0 hi').elim)
  have nonB : B.Nonempty := ⟨_, hmem⟩
  let z : Fin d → E := fun i =>
    if hz : cycStep d q n r u i = 0 then nonB.some else v i
  have zin : ∀ i, z i ∈ B := by
    intro i
    by_cases hz : cycStep d q n r u i = 0
    · simpa [z, hz] using nonB.some_mem
    · simpa [z, hz] using
        (IsExtreme.mem_of_pos_coeff hu hs hv hcv hB hmem i
          (supp i (lt_of_le_of_ne (vals i) (Ne.symm hz))))
  have heval : simplexEval v (cycStep d q n r u) =
      simplexEval z (cycStep d q n r u) := by
    unfold simplexEval
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hz : cycStep d q n r u i = 0
    · simp [hz]
    · simp [z, hz]
  rw [heval]
  exact hconB.sum_mem (by intro i hi; exact vals i)
    (sum_cycStep hd hq hn hr hs) (by intro i hi; exact zin i)
/-- On a simultaneous chamber for all *interior* cuts, only the colours
appearing as residues of those cuts can vary. The two outer coordinates of a
simplex are constants and cause no additional colours. -/
lemma cycStep_constant_of_chambers {d q n r : ℕ} (hq : 0 < q) (hn : 0 < n)
    (hr : r < n)
    {u w : Fin d → ℝ} (hsu : (∑ i, u i)=1) (hsw : (∑ i, w i)=1)
    {b : ℕ → ℕ}
    (hbtop : ∀ m, 0 < m → m < d → b m < q*n)
    (hb : ∀ m, 0 < m → m < d → b m % n ≠ r)
    (hu : ∀ m, 0 < m → m < d → cumCoord d u m ∈
      Set.Icc (linePoint 0 1 (q*n) (b m)) (linePoint 0 1 (q*n) (b m+1)))
    (hw : ∀ m, 0 < m → m < d → cumCoord d w m ∈
      Set.Icc (linePoint 0 1 (q*n) (b m)) (linePoint 0 1 (q*n) (b m+1))) :
    ∀ i, cycStep d q n r u i = cycStep d q n r w i := by
  intro i
  unfold cycStep
  have eqcut : ∀ m, m < d+1 →
      cyclicHeight q n r (cumCoord d u m) =
        cyclicHeight q n r (cumCoord d w m) := by
    intro m hm
    rcases m with (_|m)
    · simp [cumCoord_zero, cyclicHeight_zero hq]
    by_cases he : m+1 = d
    · subst d
      have ueq : cumCoord (m+1) u (m+1) = 1 := by
        rw [cumCoord_large u le_rfl, hsu]
      have weq : cumCoord (m+1) w (m+1) = 1 := by
        rw [cumCoord_large w le_rfl, hsw]
      rw [ueq, weq]
    · apply cyclicHeight_constant_of_edge hq hn (hbtop (m+1) (by omega)
          (by omega : m+1 < d))
        (hb (m+1) (by omega) (by omega)) hr
        (hu (m+1) (by omega) (by omega))
        (hw (m+1) (by omega) (by omega))
  rw [eqcut _ (by omega), eqcut _ (by omega)]
/-- Two interleaved copies of a simplex stay uniformly close. The useful bound
is the sum of norms of its vertices times `2/q`; it is crude but independent
of the chamber and tends to zero. -/
lemma cycStep_coeff_dist {d q n r s : ℕ} (hq : 0 < q)
    (hr : r < n) (hs : s < n) (u : Fin d → ℝ) (i : Fin d) :
    |cycStep d q n r u i - cycStep d q n s u i| ≤ 2 / (q:ℝ) := by
  have first := cyclicHeight_dist (q:=q) hq hr hs (cumCoord d u (i.val+1))
  have second := cyclicHeight_dist (q:=q) hq hr hs (cumCoord d u i.val)
  have triangle := abs_add_le (cyclicHeight q n r (cumCoord d u (i.val+1)) -
      cyclicHeight q n s (cumCoord d u (i.val+1)))
    (-(cyclicHeight q n r (cumCoord d u i.val) -
      cyclicHeight q n s (cumCoord d u i.val)))
  have hh :
      cycStep d q n r u i - cycStep d q n s u i =
        (cyclicHeight q n r (cumCoord d u (i.val+1)) -
          cyclicHeight q n s (cumCoord d u (i.val+1))) +
        -(cyclicHeight q n r (cumCoord d u i.val) -
          cyclicHeight q n s (cumCoord d u i.val)) := by
    unfold cycStep
    ring
  rw [hh]
  calc
    |(cyclicHeight q n r (cumCoord d u (i.val+1)) -
          cyclicHeight q n s (cumCoord d u (i.val+1))) +
        -(cyclicHeight q n r (cumCoord d u i.val) -
          cyclicHeight q n s (cumCoord d u i.val))| ≤
      |cyclicHeight q n r (cumCoord d u (i.val+1)) -
          cyclicHeight q n s (cumCoord d u (i.val+1))| +
      |-(cyclicHeight q n r (cumCoord d u i.val) -
          cyclicHeight q n s (cumCoord d u i.val))| := abs_add_le _ _
    _ = |cyclicHeight q n r (cumCoord d u (i.val+1)) -
          cyclicHeight q n s (cumCoord d u (i.val+1))| +
      |cyclicHeight q n r (cumCoord d u i.val) -
          cyclicHeight q n s (cumCoord d u i.val)| := by rw [abs_neg]
    _ ≤ 1/(q:ℝ) + 1/(q:ℝ) := add_le_add first second
    _ = 2 / (q:ℝ) := by ring

lemma cycEval_dist {d q n r s : ℕ} (hq : 0 < q) (hr : r < n) (hs : s < n)
    (v : Fin d → E) (u : Fin d → ℝ) :
    dist (simplexEval v (cycStep d q n r u))
      (simplexEval v (cycStep d q n s u)) ≤
      ∑ i : Fin d, (2 / (q:ℝ)) * ‖v i‖ := by
  rw [dist_eq_norm]
  unfold simplexEval
  rw [← Finset.sum_sub_distrib]
  -- triangle inequality over all vertices
  calc
    ‖∑ i : Fin d,
          (cycStep d q n r u i • v i - cycStep d q n s u i • v i)‖
      ≤ ∑ i : Fin d,
          ‖cycStep d q n r u i • v i - cycStep d q n s u i • v i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin d, (2 / (q:ℝ)) * ‖v i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← sub_smul, norm_smul]
      have h := cycStep_coeff_dist (d:=d) (q:=q) hq hr hs u i
      change |cycStep d q n r u i - cycStep d q n s u i| * ‖v i‖
        ≤ (2 / (q:ℝ)) * ‖v i‖
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/CyclicSimplex.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/Pasting.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
/-- The useful pasting version for a *finite closed* cover. `continuousOn_iUnion`
uses `LocallyFinite`; writing this out once avoids inadvertently pasting an infinite
closed cover. -/
lemma continuous_of_finite_closed_cover
    {α β τ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [Finite τ] (A : τ → Set α) (hA : ∀ i, IsClosed (A i))
    (hcover : (⋃ i, A i) = Set.univ) (f : α → β)
    (hf : ∀ i, ContinuousOn f (A i)) : Continuous f := by
  have hloc : LocallyFinite A := locallyFinite_of_finite A
  have hu : ContinuousOn f (⋃ i, A i) :=
    hloc.continuousOn_iUnion hA hf
  rw [hcover] at hu
  simpa [continuousOn_univ] using hu

/-- Pasting maps supplied separately on finitely many closed sets.  Equality is
needed only on their intersections; off the cover the definition chooses a
fixed value, but under `hcover` this branch is never taken.

The indexed choice formulation is handy for lex/chamber complexes: every chamber
has an elementary affine formula; the compatibility proof lives entirely on a
common face. -/
lemma finite_closed_paste
    {α β τ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [Finite τ] [DecidableEq τ]
    (A : τ → Set α) (hA : ∀ i, IsClosed (A i))
    (hcover : ∀ x : α, ∃ i, x ∈ A i)
    (g : τ → α → β)
    (hg : ∀ i, ContinuousOn (g i) (A i))
    (hcompat : ∀ i j x, x ∈ A i → x ∈ A j → g i x = g j x) :
    ∃ f : α → β, Continuous f ∧ ∀ i x, x ∈ A i → f x = g i x := by
  classical
  choose ind hind using hcover
  let f : α → β := fun x => g (ind x) x
  have feq : ∀ i x, x ∈ A i → f x = g i x := by
    intro i x hx
    exact hcompat (ind x) i x (hind x) hx
  refine ⟨f, ?_, feq⟩
  have hcU : (⋃ i, A i) = (Set.univ : Set α) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨ind x, hind x⟩
  refine continuous_of_finite_closed_cover A hA hcU f ?_
  intro i
  have eqon : Set.EqOn f (g i) (A i) := fun x hx => feq i x hx
  exact (hg i).congr eqon
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/Pasting.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/SegmentHome.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {k : ℕ}
attribute [local instance] Classical.propDecidable Classical.decEq
/-- recover the affine parameter on a nonvertical coordinate of a line in `ℝᵏ` -/
def lineCoord (l r : Fin k → ℝ) (i : Fin k) (x: Fin k → ℝ) : ℝ :=
  (x i - l i) / (r i - l i)
lemma continuous_lineCoord (l r : Fin k → ℝ) (i: Fin k) :
    Continuous (lineCoord l r i) := by
  unfold lineCoord
  fun_prop
lemma lineCoord_lineAffine (l r : Fin k → ℝ) (i : Fin k) (hi : r i ≠ l i)
    (t : ℝ) : lineCoord l r i (lineAffine l r t) = t := by
  change ((((1-t) • l + t • r) i) - l i) / (r i - l i) = t
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring
lemma exists_lineCoord (l r : Fin k → ℝ) (h : l ≠ r) :
    ∃ i : Fin k, r i ≠ l i := by
  classical
  by_contra H
  push_neg at H
  exact h (funext fun i => (H i).symm)

def intervalToSegment (l r : Fin k → ℝ) (t : Set.Icc (0:ℝ) 1) :
    {x : Fin k → ℝ // x ∈ segment ℝ l r} :=
  ⟨lineAffine l r t.1, by
     rw [← lineAffine_image_Icc]
     exact ⟨t.1,t.2,rfl⟩⟩
lemma intervalToSegment_injective (l r : Fin k → ℝ) (h:l ≠ r) :
    Function.Injective (intervalToSegment l r) := by
  intro x y hxy
  have he : lineAffine l r (x:ℝ) = lineAffine l r (y:ℝ) :=
    congrArg Subtype.val hxy
  exact Subtype.ext (lineAffine_injective h he)
lemma intervalToSegment_surjective (l r : Fin k → ℝ) :
    Function.Surjective (intervalToSegment l r) := by
  intro x
  rcases (show (x.1 : Fin k → ℝ) ∈ lineAffine l r '' Set.Icc (0:ℝ) 1 by
    rw [lineAffine_image_Icc]; exact x.property) with ⟨t,ht,he⟩
  exact ⟨⟨t,ht⟩, Subtype.ext he⟩
lemma continuous_intervalToSegment (l r : Fin k → ℝ) :
    Continuous (intervalToSegment l r) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : Set.Icc (0:ℝ) 1 => lineAffine l r (t:ℝ))
  -- affine plus products
  unfold lineAffine
  dsimp
  fun_prop
/-- The affine parametrisation is a homeomorphism on its interval. Code inverse via a
coordinate, avoiding compactness assumptions on ambient products. -/
def intervalHomeoSegment (l r : Fin k → ℝ) (h : l ≠ r) :
    Set.Icc (0:ℝ) 1 ≃ₜ {x : Fin k → ℝ // x ∈ segment ℝ l r} :=
  { toFun := intervalToSegment l r
    invFun := fun x =>
      let i := Classical.choose (exists_lineCoord l r h)
      ⟨lineCoord l r i x.1, by
         rcases (show x.1 ∈ lineAffine l r '' Set.Icc (0:ℝ) 1 by
           rw [lineAffine_image_Icc]; exact x.2) with ⟨t,ht,he⟩
         have hi : r i ≠ l i := Classical.choose_spec (exists_lineCoord l r h)
         have heq : lineCoord l r i x.1 = t := by
           rw [← he]
           exact lineCoord_lineAffine l r i hi t
         rw [heq]
         exact ht⟩
    left_inv := by
      intro t
      apply Subtype.ext
      exact lineCoord_lineAffine l r _ (Classical.choose_spec (exists_lineCoord l r h)) t.1
    right_inv := by
      intro x
      rcases (show x.1 ∈ lineAffine l r '' Set.Icc (0:ℝ) 1 by
           rw [lineAffine_image_Icc]; exact x.2) with ⟨t,ht,he⟩
      apply Subtype.ext
      change lineAffine l r (lineCoord l r _ x.1) = x.1
      have heq : lineCoord l r (Classical.choose (exists_lineCoord l r h)) x.1 = t := by
        rw [← he]
        exact lineCoord_lineAffine l r _ (Classical.choose_spec (exists_lineCoord l r h)) t
      rw [heq, he]
    continuous_toFun := continuous_intervalToSegment l r
    continuous_invFun := by
      apply Continuous.subtype_mk
      change Continuous (fun x : {x : Fin k → ℝ // x ∈ segment ℝ l r} =>
         lineCoord l r (Classical.choose (exists_lineCoord l r h)) x.1)
      exact (continuous_lineCoord l r (Classical.choose (exists_lineCoord l r h))).comp
        (continuous_subtype_val (p:=fun x : Fin k → ℝ => x ∈ segment ℝ l r)) }
@[simp] lemma intervalHomeoSegment_apply (l r : Fin k → ℝ) (h : l ≠ r)
    (t : Set.Icc (0:ℝ) 1) :
  ((intervalHomeoSegment l r h) t : Fin k → ℝ) = lineAffine l r (t:ℝ) := rfl
@[simp] lemma intervalHomeoSegment_zero (l r : Fin k → ℝ) (h : l ≠ r) :
    intervalHomeoSegment l r h ⟨0, by norm_num⟩ =
      (⟨l, left_mem_segment ℝ l r⟩ : {x : Fin k → ℝ // x ∈ segment ℝ l r}) := by
  apply Subtype.ext
  change (1-(0:ℝ)) • l + (0:ℝ) • r = l
  simp
@[simp] lemma intervalHomeoSegment_one (l r : Fin k → ℝ) (h : l ≠ r) :
    intervalHomeoSegment l r h ⟨1, by norm_num⟩ =
      (⟨r, right_mem_segment ℝ l r⟩ : {x : Fin k → ℝ // x ∈ segment ℝ l r}) := by
  apply Subtype.ext
  change (1-(1:ℝ)) • l + (1:ℝ) • r = r
  simp
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/SegmentHome.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalOrdered.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]
/- Prefix formulas with a finite but non-`Fin` ordered set of vertices.  Unlike
   the various charts used for a simplex these do not mention its dimension.
   This is the convenient way of checking that the cyclic maps on overlapping
   pulling faces have genuinely the **same** restriction, and not just the same
   image. -/
def orderedCut (u : α → ℝ) (a : α) : ℝ :=
  ∑ i ∈ (Finset.univ.filter (fun i : α => i < a)), u i
def orderedCutSucc (u : α → ℝ) (a : α) : ℝ :=
  ∑ i ∈ (Finset.univ.filter (fun i : α => i ≤ a)), u i

def orderedCycStep (q n r : ℕ) (u : α → ℝ) (a : α) : ℝ :=
  cyclicHeight q n r (orderedCutSucc u a) -
    cyclicHeight q n r (orderedCut u a)

lemma continuous_orderedCut (a : α) : Continuous (fun u : α → ℝ => orderedCut u a) := by
  classical
  unfold orderedCut
  fun_prop
lemma continuous_orderedCutSucc (a : α) :
    Continuous (fun u : α → ℝ => orderedCutSucc u a) := by
  classical
  unfold orderedCutSucc
  fun_prop
lemma continuous_orderedCycStep (q n r : ℕ) (a : α) :
    Continuous (fun u : α → ℝ => orderedCycStep q n r u a) := by
  classical
  unfold orderedCycStep
  exact ((continuous_cyclicHeight _ _ _).comp (continuous_orderedCutSucc a)).sub
    ((continuous_cyclicHeight _ _ _).comp (continuous_orderedCut a))

/- Extension by zero along an increasing injection.  `sum` rather than a
   classical `dite` keeps this independent of any chosen inverse. -/
def extendOrder (e : β ↪o α) (u : β → ℝ) (a : α) : ℝ :=
  ∑ i : β, if e i = a then u i else 0

@[simp] lemma extendOrder_image (e : β ↪o α) (u : β → ℝ) (i : β) :
    extendOrder e u (e i) = u i := by
  classical
  unfold extendOrder
  calc
    (∑ j : β, if e j = e i then u j else 0) =
      ∑ j : β, if j = i then u j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases ji : j = i
        · simp [ji]
        · have en : e j ≠ e i := by intro h; exact ji (e.injective h)
          simp [ji, en]
    _ = _ := by simp

lemma extendOrder_off (e : β ↪o α) (u : β → ℝ) (a : α)
    (ha : ∀ i, e i ≠ a) : extendOrder e u a = 0 := by
  classical
  unfold extendOrder
  simp [ha]

/- The prefix sums commute with order embeddings and extension by zero.  When
  a face loses some vertices, all intervening zero coordinates simply vanish.
  This tiny bookkeeping lemma is often what is awkward if simplex charts are
  compared directly. -/
lemma orderedCut_extend_image (e : β ↪o α) (u : β → ℝ) (b : β) :
    orderedCut (extendOrder e u) (e b) = orderedCut u b := by
  classical
  unfold orderedCut extendOrder
  -- Rearrange the double sum, then the inner filtered indicator.
  calc
    (∑ i ∈ (Finset.univ.filter (fun i : α => i < e b)),
      ∑ j : β, if e j = i then u j else 0) =
      ∑ j : β, ∑ i ∈ (Finset.univ.filter (fun i : α => i < e b)),
        (if e j = i then u j else 0) := by
          -- `sum_comm` under the outer filtered finset.
          rw [Finset.sum_comm]
    _ = ∑ j : β, if e j < e b then u j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases lt : e j < e b
      · have hm : e j ∈ (Finset.univ.filter (fun i : α => i < e b)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt⟩
        -- exactly one term survives
        rw [Finset.sum_eq_single (e j)]
        · simp [lt]
        · intro i hi hneq
          have ne' : e j ≠ i := Ne.symm hneq
          simp [ne']
        · simp_all
      · -- no surviving index can equal `e j`.
        have hz : ∀ i ∈ (Finset.univ.filter (fun i : α => i < e b)),
            (if e j = i then u j else (0:ℝ)) = 0 := by
          intro i hi
          have ilt := (Finset.mem_filter.mp hi).2
          have ne : e j ≠ i := by
            intro h
            rw [← h] at ilt
            exact lt ilt
          simp [ne]
        rw [Finset.sum_eq_zero hz]
        simp [lt]
    _ = ∑ j ∈ (Finset.univ.filter (fun j : β => j < b)), u j := by
      classical
      -- transfer strict monotonicity through `e`.
      have tr (j : β) : e j < e b ↔ j < b := by
        exact (e.lt_iff_lt)
      calc
        (∑ j : β, if e j < e b then u j else 0) =
          ∑ j : β, if j < b then u j else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [tr j]
        _ = _ := by
          exact (Finset.sum_filter (s := (Finset.univ : Finset β)) (fun j : β => j < b) u).symm

lemma orderedCutSucc_extend_image (e : β ↪o α) (u : β → ℝ) (b : β) :
    orderedCutSucc (extendOrder e u) (e b) = orderedCutSucc u b := by
  classical
  unfold orderedCutSucc extendOrder
  calc
    (∑ i ∈ (Finset.univ.filter (fun i : α => i ≤ e b)),
      ∑ j : β, if e j = i then u j else 0) =
      ∑ j : β, ∑ i ∈ (Finset.univ.filter (fun i : α => i ≤ e b)),
        (if e j = i then u j else 0) := by rw [Finset.sum_comm]
    _ = ∑ j : β, if e j ≤ e b then u j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases le : e j ≤ e b
      · have hm : e j ∈ (Finset.univ.filter (fun i : α => i ≤ e b)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, le⟩
        rw [Finset.sum_eq_single (e j)]
        · simp [le]
        · intro i hi hneq
          have ne' : e j ≠ i := Ne.symm hneq
          simp [ne']
        · simp_all
      · have hz : ∀ i ∈ (Finset.univ.filter (fun i : α => i ≤ e b)),
            (if e j = i then u j else (0:ℝ)) = 0 := by
          intro i hi
          have ilt := (Finset.mem_filter.mp hi).2
          have ne : e j ≠ i := by
            intro h
            rw [← h] at ilt
            exact le ilt
          simp [ne]
        rw [Finset.sum_eq_zero hz]
        simp [le]
    _ = ∑ j ∈ (Finset.univ.filter (fun j : β => j ≤ b)), u j := by
      -- For an order embedding, non-strict comparisons reflect too.
      have tr (j : β) : e j ≤ e b ↔ j ≤ b := by
        exact e.le_iff_le
      calc
        (∑ j : β, if e j ≤ e b then u j else 0) =
          ∑ j : β, if j ≤ b then u j else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [tr j]
        _ = _ := by
          exact (Finset.sum_filter (s := (Finset.univ : Finset β)) (fun j : β => j ≤ b) u).symm

@[simp] lemma orderedCycStep_extend_image (e : β ↪o α)
    (q n r : ℕ) (u : β → ℝ) (b : β) :
    orderedCycStep q n r (extendOrder e u) (e b) =
      orderedCycStep q n r u b := by
  unfold orderedCycStep
  rw [orderedCutSucc_extend_image, orderedCut_extend_image]

/- If a coordinate is absent, prefix and successor prefix agree; hence the
   corresponding cyclic coordinate is zero. -/
lemma orderedCutSucc_eq_cut_of_zero (u : α → ℝ) (a : α) (hz : u a = 0) :
    orderedCutSucc u a = orderedCut u a := by
  classical
  unfold orderedCutSucc orderedCut
  let S : Finset α := Finset.univ.filter (fun i : α => i ≤ a)
  let T : Finset α := Finset.univ.filter (fun i : α => i < a)
  have hdecomp : S = insert a T := by
    ext i
    by_cases ia : i = a
    · subst i
      simp [S, T]
    · have ltiff : i ≤ a ↔ i < a := by exact lt_iff_le_and_ne.trans (and_iff_left ia) |>.symm
      -- workaround simpler linear order split
      have : i ≤ a ↔ i < a := by omega -- may fail α
      simp [S, T, ia, this]
  change (∑ i ∈ S, u i) = ∑ i ∈ T, u i
  rw [hdecomp]
  simp [T, hz]

lemma orderedCycStep_zero_of_coord_zero (q n r : ℕ)
    (u : α → ℝ) (a : α) (hz : u a = 0) :
    orderedCycStep q n r u a = 0 := by
  unfold orderedCycStep
  rw [orderedCutSucc_eq_cut_of_zero u a hz]
  simp

lemma orderedCycStep_extend_off (e : β ↪o α)
    (q n r : ℕ) (u : β → ℝ) (a : α) (ha : ∀ i, e i ≠ a) :
    orderedCycStep q n r (extendOrder e u) a = 0 := by
  exact orderedCycStep_zero_of_coord_zero q n r _ _ (extendOrder_off e u a ha)
end
end FamiliesProof

namespace FamiliesProof
noncomputable section
open scoped BigOperators
variable {α β E : Type*} [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def orderedEval (v : α → E) (u : α → ℝ) : E := ∑ i, u i • v i

def orderedCycEval (q n r : ℕ) (v : α → E) (u : α → ℝ) : E :=
  orderedEval v (orderedCycStep q n r u)

/- Continuity on all coefficient space, not only the simplex. It is useful for
   pasting restrictions to compact chambers. -/
lemma continuous_orderedCycEval (q n r : ℕ) (v : α → E) :
    Continuous (orderedCycEval q n r v) := by
  unfold orderedCycEval orderedEval
  exact continuous_finset_sum _ (by
    intro i hi
    exact (continuous_orderedCycStep q n r i).smul continuous_const)

lemma orderedEval_extend (e : β ↪o α)
    (v : α → E) (u : β → ℝ) :
    orderedEval v (extendOrder e u) = orderedEval (fun i => v (e i)) u := by
  classical
  unfold orderedEval extendOrder
  -- Rearrange finite sums and keep the one indicator in each column. This
  -- avoids choosing an inverse to `e`.
  calc
    (∑ a : α, (∑ i : β, if e i = a then u i else 0) • v a) =
      ∑ a : α, ∑ i : β, (if e i = a then u i else 0) • v a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_smul]
    _ = ∑ i : β, ∑ a : α, (if e i = a then u i else 0) • v a := by
      rw [Finset.sum_comm]
    _ = ∑ i : β, u i • v (e i) := by
      apply Finset.sum_congr rfl
      intro i hi
      -- once again exactly one term `a = e i` survives.
      classical
      have hem : e i ∈ (Finset.univ : Finset α) := Finset.mem_univ _
      rw [Finset.sum_eq_single (e i)]
      · simp
      · intro a ha hane
        have ne : e i ≠ a := Ne.symm hane
        simp [ne]
      · simp_all

/- The global ordered cyclic evaluation restricts literally to every ordered
   subset of vertices. This is the rigorous form of the informal “zero
   barycentric coordinates remove deleted vertices” gluing step. -/
lemma orderedCycEval_extend (e : β ↪o α)
    (q n r : ℕ) (v : α → E) (u : β → ℝ) :
    orderedCycEval q n r v (extendOrder e u) =
      orderedCycEval q n r (fun i : β => v (e i)) u := by
  classical
  -- cyclic step vector in `α` is itself extension of the cyclic step vector
  -- on `β`: equality on image and zero off image.
  have hstep : orderedCycStep q n r (extendOrder e u) =
      extendOrder e (orderedCycStep q n r u) := by
    funext a
    by_cases hmem : ∃ i, e i = a
    · rcases hmem with ⟨i,rfl⟩
      simp [orderedCycStep_extend_image, extendOrder_image]
    · have hnon : ∀ i, e i ≠ a := by
        intro i hi
        exact hmem ⟨i, hi⟩
      rw [orderedCycStep_extend_off e q n r u a hnon,
        extendOrder_off e _ a hnon]
  unfold orderedCycEval
  rw [hstep]
  exact orderedEval_extend e v (orderedCycStep q n r u)
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open scoped BigOperators
@[simp] lemma orderedCut_fin_eq_cumCoord {d : ℕ}
    (u : Fin d → ℝ) (i : Fin d) :
    orderedCut u i = cumCoord d u i.val := by
  classical
  unfold orderedCut cumCoord
  rfl

@[simp] lemma orderedCutSucc_fin_eq_cumCoord {d : ℕ}
    (u : Fin d → ℝ) (i : Fin d) :
    orderedCutSucc u i = cumCoord d u (i.val + 1) := by
  classical
  unfold orderedCutSucc cumCoord
  -- non-strict comparison is the same as a strict bound by `i+1`
  have hset :
      ((Finset.univ : Finset (Fin d)).filter
        (fun j : Fin d => j ≤ i)) =
      ((Finset.univ : Finset (Fin d)).filter
        (fun j : Fin d => j.val < i.val + 1)) := by
    ext j
    simp
  rw [hset]

@[simp] lemma orderedCycStep_fin_eq_cycStep {d q n r : ℕ}
    (u : Fin d → ℝ) (i : Fin d) :
    orderedCycStep q n r u i = cycStep d q n r u i := by
  unfold orderedCycStep cycStep
  rw [orderedCutSucc_fin_eq_cumCoord, orderedCut_fin_eq_cumCoord]
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
@[simp] lemma orderedEval_fin_eq_simplexEval {d : ℕ}
    (v : Fin d → E) (u : Fin d → ℝ) :
    orderedEval v u = simplexEval v u := rfl
@[simp] lemma orderedCycEval_fin_eq {d q n r : ℕ}
    (v : Fin d → E) (u : Fin d → ℝ) :
    orderedCycEval q n r v u = simplexEval v (cycStep d q n r u) := by
  unfold orderedCycEval
  rw [orderedEval_fin_eq_simplexEval]
  congr 1
  funext i
  exact orderedCycStep_fin_eq_cycStep u i
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalOrdered.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/SegmentCopies.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {k : ℕ}
attribute [local instance] Classical.propDecidable Classical.decEq
/-- Interleaved colour copy on an ambient straight segment. -/
def segmentCopy (l r : Fin k → ℝ) (h:l ≠ r) (q n i : ℕ) (hq : 0 < q) :
    C({x : Fin k → ℝ // x ∈ segment ℝ l r},
      {x : Fin k → ℝ // x ∈ segment ℝ l r}) :=
  { toFun := fun x =>
      let t : ℝ := ((intervalHomeoSegment l r h).symm x : Set.Icc (0:ℝ) 1)
      ⟨lineAffine l r (cyclicHeight q n i t), by
        rw [← lineAffine_image_Icc]
        exact ⟨_, cyclicHeight_mem hq _, rfl⟩⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      change Continuous (fun x : {x : Fin k → ℝ // x ∈ segment ℝ l r} =>
        lineAffine l r (cyclicHeight q n i
          (((intervalHomeoSegment l r h).symm x : Set.Icc (0:ℝ) 1) : ℝ)))
      unfold lineAffine
      dsimp
      have ht : Continuous (fun x : {x : Fin k → ℝ // x ∈ segment ℝ l r} =>
        (((intervalHomeoSegment l r h).symm x : Set.Icc (0:ℝ) 1) : ℝ)) :=
          continuous_subtype_val.comp (intervalHomeoSegment l r h).symm.continuous
      have hc : Continuous (fun x : {x : Fin k → ℝ // x ∈ segment ℝ l r} =>
          cyclicHeight q n i (((intervalHomeoSegment l r h).symm x : Set.Icc (0:ℝ) 1) : ℝ)) :=
        (continuous_cyclicHeight q n i).comp ht
      fun_prop }
@[simp] lemma segmentCopy_val (l r : Fin k → ℝ) (h:l ≠ r)
    (q n i) (hq : 0 < q) (x : {x : Fin k → ℝ // x ∈ segment ℝ l r}) :
    ((segmentCopy l r h q n i hq x) : Fin k → ℝ) =
      lineAffine l r (cyclicHeight q n i
        (((intervalHomeoSegment l r h).symm x : Set.Icc (0:ℝ) 1) : ℝ)) := rfl
lemma segmentCopy_left (l r : Fin k → ℝ) (h:l ≠ r)
    {q n i : ℕ} (hq : 0 < q) (hn : 0 < n) (hi : i < n) :
    segmentCopy l r h q n i hq ⟨l, left_mem_segment ℝ l r⟩ =
      ⟨l, left_mem_segment ℝ l r⟩ := by
  apply Subtype.ext
  simp [segmentCopy_val]
  have he : (intervalHomeoSegment l r h).symm
      (⟨l, left_mem_segment ℝ l r⟩ : {x // x ∈ segment ℝ l r}) =
      (⟨0, by norm_num⟩ : Set.Icc (0:ℝ) 1) := by
    rw [Homeomorph.symm_apply_eq]
    exact (intervalHomeoSegment_zero l r h).symm
  rw [he]
  have hz : cyclicHeight q n i (0:ℝ) = 0 := by
    have := cyclicMap_zero hq hn hi (show (0:ℝ) < 1 by norm_num)
    simpa [cyclicMap] using this
  change lineAffine l r (cyclicHeight q n i (0:ℝ)) = l
  rw [hz]
  dsimp [lineAffine]
  simp
lemma segmentCopy_right (l r : Fin k → ℝ) (h:l ≠ r)
    {q n i : ℕ} (hq : 0 < q) (hn : 0 < n) (hi : i < n) :
    segmentCopy l r h q n i hq ⟨r, right_mem_segment ℝ l r⟩ =
      ⟨r, right_mem_segment ℝ l r⟩ := by
  apply Subtype.ext
  have he : (intervalHomeoSegment l r h).symm
      (⟨r, right_mem_segment ℝ l r⟩ : {x // x ∈ segment ℝ l r}) =
      (⟨1, by norm_num⟩ : Set.Icc (0:ℝ) 1) := by
    rw [Homeomorph.symm_apply_eq]
    exact (intervalHomeoSegment_one l r h).symm
  change lineAffine l r (cyclicHeight q n i
      (((intervalHomeoSegment l r h).symm
      (⟨r, right_mem_segment ℝ l r⟩ : {x // x ∈ segment ℝ l r}) : Set.Icc (0:ℝ) 1) : ℝ)) = r
  rw [he]
  have hz : cyclicHeight q n i (1:ℝ) = 1 := by
    have := cyclicMap_one hq hn hi (show (0:ℝ) < 1 by norm_num)
    simpa [cyclicMap] using this
  rw [hz]
  dsimp [lineAffine]
  simp
/-- Extract the line parameter of a convex hull edge in the embedded line complex. -/
lemma edge_param {l r : Fin k → ℝ} (h:l ≠ r) {N m : ℕ} (hN:0 < N) (hm : m < N)
  {x : Fin k → ℝ}
  (hx : x ∈ convexHull ℝ
    (embFinset (lineAffine l r) (lineAffine_injective h)
      { linePoint 0 1 N m, linePoint 0 1 N (m+1) } : Set (Fin k → ℝ))) :
  let hxS : x ∈ segment ℝ l r := by
        rw [← lineAffine_image_Icc]
        rw [← hull_embFinset (lineAffine l r) (lineAffine_injective h)] at hx
        rcases hx with ⟨t,ht,rfl⟩
        have htseg : t ∈ segment ℝ (linePoint 0 1 N m) (linePoint 0 1 N (m+1)) := by
          simpa [convexHull_pair] using ht
        have hle : linePoint 0 1 N m ≤ linePoint 0 1 N (m+1) :=
          (linePoint_le 0 1 hN (by norm_num)).2 (by omega)
        rw [segment_eq_Icc hle] at htseg
        have lo : (0:ℝ) ≤ linePoint 0 1 N m := by
          simpa [linePoint_zero] using
            ((linePoint_le 0 1 hN (by norm_num)).2 (show 0 ≤ m by omega))
        have up : linePoint 0 1 N (m+1) ≤ (1:ℝ) := by
          simpa [linePoint_end 0 1 hN] using
            ((linePoint_le 0 1 hN (by norm_num)).2 (show m+1 ≤ N by omega))
        exact ⟨t, ⟨lo.trans htseg.1, htseg.2.trans up⟩, rfl⟩
  (((intervalHomeoSegment l r h).symm ⟨x, hxS⟩ : Set.Icc (0:ℝ) 1) : ℝ) ∈
    Set.Icc (linePoint 0 1 N m) (linePoint 0 1 N (m+1)) := by
  dsimp
  rw [← hull_embFinset (lineAffine l r) (lineAffine_injective h)] at hx
  rcases hx with ⟨t,ht,he⟩
  have htseg : t ∈ segment ℝ (linePoint 0 1 N m) (linePoint 0 1 N (m+1)) := by
    simpa [convexHull_pair] using ht
  have hle : linePoint 0 1 N m ≤ linePoint 0 1 N (m+1) :=
    (linePoint_le 0 1 hN (by norm_num)).2 (by omega)
  rw [segment_eq_Icc hle] at htseg
  change lineCoord l r (Classical.choose (exists_lineCoord l r h)) x ∈ _
  have heq : lineCoord l r (Classical.choose (exists_lineCoord l r h)) x = t := by
    rw [← he]
    exact lineCoord_lineAffine l r _ (Classical.choose_spec (exists_lineCoord l r h)) t
  rw [heq]
  exact htseg
lemma segmentCopy_const_edge {l r : Fin k → ℝ} (h:l ≠ r)
  {q n m i : ℕ} (hq : 0 < q) (hn : 0 < n) (hm : m < q*n)
  (hne : m % n ≠ i) (hi : i < n)
  {x y : {z : Fin k → ℝ // z ∈ segment ℝ l r}}
  (hx : (x : Fin k → ℝ) ∈ convexHull ℝ
    (embFinset (lineAffine l r) (lineAffine_injective h)
      { linePoint 0 1 (q*n) m, linePoint 0 1 (q*n) (m+1) } : Set (Fin k → ℝ)))
  (hy : (y : Fin k → ℝ) ∈ convexHull ℝ
    (embFinset (lineAffine l r) (lineAffine_injective h)
      { linePoint 0 1 (q*n) m, linePoint 0 1 (q*n) (m+1) } : Set (Fin k → ℝ))) :
  segmentCopy l r h q n i hq x = segmentCopy l r h q n i hq y := by
  apply Subtype.ext
  simp only [segmentCopy_val]
  congr 1
  exact cyclicHeight_constant_of_edge hq hn hm hne hi
    (edge_param h (Nat.mul_pos hq hn) hm hx)
    (edge_param h (Nat.mul_pos hq hn) hm hy)
lemma segmentCopy_dist {l r : Fin k → ℝ} (h:l ≠ r)
  {q n i j : ℕ} (hq : 0 < q) (hi : i < n) (hj : j < n)
  (x : {z : Fin k → ℝ // z ∈ segment ℝ l r}) :
  dist (segmentCopy l r h q n i hq x) (segmentCopy l r h q n j hq x) ≤
      (1 / (q:ℝ)) * ‖r-l‖ := by
  rw [Subtype.dist_eq, dist_eq_norm]
  simp only [segmentCopy_val]
  have hh := cyclicHeight_dist hq hi hj
    ((((intervalHomeoSegment l r h).symm x : Set.Icc (0:ℝ) 1) : ℝ))
  have eqn (u v : ℝ) : lineAffine l r u - lineAffine l r v = (u-v) • (r-l) := by
    dsimp [lineAffine]
    module
  rw [eqn]
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)
/-- A copy on the segment preserves any convex extreme subset. Endpoints are fixed,
whereas an interior point in an extreme subset forces both endpoints into it. -/
lemma segmentCopy_mem_extreme {l r : Fin k → ℝ} (h:l ≠ r)
  {q n i : ℕ} (hq : 0 < q) (hn : 0 < n) (hi : i < n)
  {B : Set (Fin k → ℝ)} (hc : Convex ℝ B)
  (hB : IsExtreme ℝ (segment ℝ l r) B)
  (x : {z : Fin k → ℝ // z ∈ segment ℝ l r}) (hx : (x:Fin k → ℝ) ∈ B) :
  ((segmentCopy l r h q n i hq x) : Fin k → ℝ) ∈ B := by
  let t : Set.Icc (0:ℝ) 1 := (intervalHomeoSegment l r h).symm x
  have xt : (x : Fin k → ℝ) = lineAffine l r (t:ℝ) := by
    have := (intervalHomeoSegment l r h).apply_symm_apply x
    exact congrArg Subtype.val this.symm
  rcases eq_or_ne (t:ℝ) 0 with t0|t0
  · have xl : x = ⟨l, left_mem_segment ℝ l r⟩ := by
      apply Subtype.ext
      rw [xt, t0]
      dsimp [lineAffine]
      simp
    rw [xl] at hx ⊢
    rw [segmentCopy_left l r h hq hn hi]
    exact hx
  · rcases eq_or_ne (t:ℝ) 1 with t1|t1
    · have xr : x = ⟨r, right_mem_segment ℝ l r⟩ := by
        apply Subtype.ext
        rw [xt, t1]
        dsimp [lineAffine]
        simp
      rw [xr] at hx ⊢
      rw [segmentCopy_right l r h hq hn hi]
      exact hx
    · have ti : (t:ℝ) ∈ Set.Ioo (0:ℝ) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm t0),
         lt_of_le_of_ne t.property.2 t1⟩
      have xo : (x : Fin k → ℝ) ∈ openSegment ℝ l r := by
        rw [openSegment_eq_image]
        refine ⟨(t:ℝ), ti, ?_⟩
        exact xt.symm
      have hl : l ∈ B := hB.left_mem_of_mem_openSegment
        (left_mem_segment ℝ l r) (right_mem_segment ℝ l r) hx xo
      have hr : r ∈ B := hB.right_mem_of_mem_openSegment
        (left_mem_segment ℝ l r) (right_mem_segment ℝ l r) hx xo
      apply hc.segment_subset hl hr
      exact (segmentCopy l r h q n i hq x).property
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/SegmentCopies.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/SimplexCoords.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma finiteHull_range_mem_simplex {d : ℕ} {v : Fin d → E}
    (vi : Function.Injective v) {x : E} (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ u : Fin d → ℝ, u ∈ coeffSimplex d ∧ simplexEval v u = x := by
  classical
  let s : Finset E := Finset.univ.image v
  have sc : (s : Set E) = Set.range v := by
    ext y; simp [s]
  have hxs : x ∈ convexHull ℝ (s : Set E) := by rw [sc]; exact hx
  rcases (Finset.mem_convexHull' (R:=ℝ) (s:=s)).1 hxs with ⟨w,hw,hs,he⟩
  let u : Fin d → ℝ := fun i => w (v i)
  refine ⟨u, ?_, ?_⟩
  · refine ⟨fun i => hw _ (by simp [s]), ?_⟩
    
    have hh := (Finset.sum_image (s:= (Finset.univ : Finset (Fin d)))
      (f:= fun y : E => w y) (g:=v)
      (by intro a ha b hb hab; exact vi hab)).symm
    change (∑ i : Fin d, w (v i)) = 1
    rw [hh]
    exact hs
  · dsimp [simplexEval]
    
    have hh := (Finset.sum_image (s:= (Finset.univ : Finset (Fin d)))
      (f:= fun y : E => w y • y) (g:=v)
      (by intro a ha b hb hab; exact vi hab)).symm
    change (∑ i : Fin d, w (v i) • v i) = x
    rw [hh]
    exact he
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Compact-coordinate homeomorphism for an independent simplex; this avoids
explicit matrices in chamber constructions. -/
def simplexHomeo {d : ℕ} (v : Fin d → E) (hv : AffineIndependent ℝ v) :
    {u : Fin d → ℝ // u ∈ coeffSimplex d} ≃ₜ
      {x : E // x ∈ convexHull ℝ (Set.range v)} := by
  let toF : {u : Fin d → ℝ // u ∈ coeffSimplex d} →
      {x : E // x ∈ convexHull ℝ (Set.range v)} := fun u =>
        ⟨simplexEval v u, simplexEval_mem_hull v u.property.1 u.property.2⟩
  have inj : Function.Injective toF := by
    intro a b h
    apply Subtype.ext
    apply simplexEval_eq hv a.property.2 b.property.2
    exact congrArg Subtype.val h
  have sur : Function.Surjective toF := by
    intro x
    obtain ⟨u,hu,he⟩ := finiteHull_range_mem_simplex hv.injective x.property
    refine ⟨⟨u,hu⟩, ?_⟩
    exact Subtype.ext he
  let e := Equiv.ofBijective toF ⟨inj,sur⟩
  letI : CompactSpace {u : Fin d → ℝ // u ∈ coeffSimplex d} :=
    isCompact_iff_compactSpace.mp (isCompact_coeffSimplex d)
  apply Continuous.homeoOfEquivCompactToT2 (f:=e)
  have hc : Continuous toF := by
    change Continuous (fun u : {u : Fin d → ℝ // u ∈ coeffSimplex d} => _)
    exact ((continuous_simplexEval v).comp continuous_subtype_val).subtype_mk _
  exact hc
@[simp] lemma simplexHomeo_apply {d : ℕ} (v : Fin d → E) (hv : AffineIndependent ℝ v)
    (u : {u : Fin d → ℝ // u ∈ coeffSimplex d}) :
    ((simplexHomeo v hv u : {x : E // x ∈ convexHull ℝ (Set.range v)}) : E) =
      simplexEval v u := rfl
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/SimplexCoords.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalCoeff.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/- It is useful not to choose a chart for a pulling face each time a point of it
is used.  Here are global coefficients on a finite hull, obtained by pasting the
ordinary simplex charts on the lexicographic faces. -/
def faceEnum (t : Finset E) : Fin t.card → E :=
  fun i => ((configEquiv t).symm i : t)
lemma range_faceEnum (t : Finset E) : Set.range (faceEnum t) = (t : Set E) := by
  classical
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ((configEquiv t).symm i).property
  · intro hx
    have h : (⟨x,hx⟩ : t) =
        (configEquiv t).symm (configEquiv t ⟨x,hx⟩) := by simp
    refine ⟨configEquiv t ⟨x,hx⟩, ?_⟩
    simpa [faceEnum] using congrArg (fun y : t => (y:E)) h
lemma faceEnum_indep {s t : Finset E} (ht : lexFace s t) :
    AffineIndependent ℝ (faceEnum t) := by
  classical
  have h := lexFace_independent ht
  -- affine independence is unchanged by enumerating a finite type
  let e : (Fin t.card) ≃ t := (configEquiv t).symm
  have hi : AffineIndependent ℝ (((↑) : t → E) ∘ e) :=
    h.comp_embedding e.toEmbedding
  exact hi

/-- Barycentric coordinates on one selected face, extended by zero to the
ambient configuration.  They have no dependence on the global order; this is
why coefficients can be pasted before installing the cyclic order. -/
def localFaceCoeff (s t : Finset E) (hst : t ⊆ s)
    (hi : AffineIndependent ℝ (faceEnum t)) :
    {x:E // x ∈ convexHull ℝ (t:Set E)} → (s → ℝ) := by
  classical
  exact fun x i =>
  if h : (i:E) ∈ t then
    ((simplexHomeo (faceEnum t) hi).symm
      (⟨x.1, by simpa [range_faceEnum] using x.2⟩ :
        {y:E // y ∈ convexHull ℝ (Set.range (faceEnum t))}) :
      Fin t.card → ℝ) (configEquiv t ⟨i,h⟩)
  else 0

lemma continuous_localFaceCoeff (s t : Finset E) (hst : t ⊆ s)
    (hi : AffineIndependent ℝ (faceEnum t)) :
    Continuous (localFaceCoeff s t hst hi) := by
  classical
  -- coordinatewise continuity
  apply continuous_pi
  intro i
  by_cases h : (i:E) ∈ t
  · simp only [localFaceCoeff]
    simp only [dif_pos h]
    change Continuous (fun x : {x:E // x ∈ convexHull ℝ (t:Set E)} =>
      ((simplexHomeo (faceEnum t) hi).symm
        (⟨x.1, by simpa [range_faceEnum] using x.2⟩ :
          {y:E // y ∈ convexHull ℝ (Set.range (faceEnum t))}) :
        Fin t.card → ℝ) (configEquiv t ⟨i,h⟩))
    have inc : Continuous (fun x : {x:E // x ∈ convexHull ℝ (t:Set E)} =>
        (⟨x.1, by simpa [range_faceEnum] using x.2⟩ :
          {y:E // y ∈ convexHull ℝ (Set.range (faceEnum t))})) :=
      continuous_subtype_val.subtype_mk _
    exact (continuous_apply _).comp
      ((continuous_subtype_val.comp (simplexHomeo (faceEnum t) hi).symm.continuous).comp inc)
  · simp only [localFaceCoeff]
    simp [h]
    exact continuous_const

lemma localFaceCoeff_nonneg (s t : Finset E) (hst : t ⊆ s)
    (hi : AffineIndependent ℝ (faceEnum t))
    (x : {x:E // x ∈ convexHull ℝ (t:Set E)}) (i : s) :
    0 ≤ localFaceCoeff s t hst hi x i := by
  classical
  unfold localFaceCoeff
  split_ifs with h
  · exact ((simplexHomeo (faceEnum t) hi).symm
      (⟨x.1, by simpa [range_faceEnum] using x.2⟩ :
        {y:E // y ∈ convexHull ℝ (Set.range (faceEnum t))})).property.1 _
  · exact le_rfl

lemma localFaceCoeff_zero (s t : Finset E) (hst : t ⊆ s)
    (hi : AffineIndependent ℝ (faceEnum t))
    (x : {x:E // x ∈ convexHull ℝ (t:Set E)}) (i : s)
    (hz : (i:E) ∉ t) : localFaceCoeff s t hst hi x i = 0 := by
  simp [localFaceCoeff, hz]

lemma localFaceCoeff_sum (s t : Finset E) (hst : t ⊆ s)
    (hi : AffineIndependent ℝ (faceEnum t))
    (x : {x:E // x ∈ convexHull ℝ (t:Set E)}) :
    (∑ i : s, localFaceCoeff s t hst hi x i) = 1 := by
  classical
  let u := (simplexHomeo (faceEnum t) hi).symm
      (⟨x.1, by simpa [range_faceEnum] using x.2⟩ :
        {y:E // y ∈ convexHull ℝ (Set.range (faceEnum t))})
  let f : E → ℝ := fun z => if h : z ∈ t then
      (u : Fin t.card → ℝ) (configEquiv t ⟨z,h⟩) else 0
  have hs (i : s) : localFaceCoeff s t hst hi x i = f (i:E) := rfl
  calc
    (∑ i : s, localFaceCoeff s t hst hi x i) = ∑ z ∈ s, f z := by
      change (∑ i : s, _) = _
      calc
        _ = ∑ i : s, f (i:E) := by simp [hs]
        _ = ∑ z ∈ s.attach, f (z:E) := by rfl
        _ = ∑ z ∈ s, f z := Finset.sum_attach s f
    _ = ∑ z ∈ t, f z := (Finset.sum_subset hst (by
      intro i hi hn
      simp [f, hn])).symm
    _ = ∑ z : t, f z := by exact (Finset.sum_attach t f).symm
    _ = ∑ z : t, (u : Fin t.card → ℝ) (configEquiv t z) := by
      apply Finset.sum_congr rfl
      intro z hz
      simp [f]
    _ = ∑ a : Fin t.card, (u : Fin t.card → ℝ) a := by
      exact Equiv.sum_comp (configEquiv t) _
    _ = 1 := u.property.2

lemma localFaceCoeff_eval (s t : Finset E) (hst : t ⊆ s)
    (hi : AffineIndependent ℝ (faceEnum t))
    (x : {x:E // x ∈ convexHull ℝ (t:Set E)}) :
    (∑ i : s, localFaceCoeff s t hst hi x i • (i:E)) = x.1 := by
  classical
  let u := (simplexHomeo (faceEnum t) hi).symm
      (⟨x.1, by simpa [range_faceEnum] using x.2⟩ :
        {y:E // y ∈ convexHull ℝ (Set.range (faceEnum t))})
  let f : E → E := fun z => if h : z ∈ t then
      (u : Fin t.card → ℝ) (configEquiv t ⟨z,h⟩) • z else 0
  have hs (i : s) : localFaceCoeff s t hst hi x i • (i:E) = f (i:E) := by
    by_cases h : (i:E) ∈ t <;> simp [localFaceCoeff, f, h, u]
  calc
    (∑ i : s, localFaceCoeff s t hst hi x i • (i:E)) = ∑ z ∈ s, f z := by
      change (∑ i : s, _) = _
      calc
        _ = ∑ i : s, f (i:E) := by simp [hs]
        _ = ∑ z ∈ s.attach, f (z:E) := by rfl
        _ = ∑ z ∈ s, f z := Finset.sum_attach s f
    _ = ∑ z ∈ t, f z := (Finset.sum_subset hst (by
      intro i hi hn
      simp [f, hn])).symm
    _ = ∑ z : t, f z := by exact (Finset.sum_attach t f).symm
    _ = ∑ z : t, (u : Fin t.card → ℝ) (configEquiv t z) • (z:E) := by
      apply Finset.sum_congr rfl
      intro z hz
      simp [f]
    _ = ∑ a : Fin t.card, (u : Fin t.card → ℝ) a • faceEnum t a := by
      simpa [faceEnum] using (Equiv.sum_comp (configEquiv t)
        (fun a : Fin t.card => (u : Fin t.card → ℝ) a • faceEnum t a))
    _ = x.1 := by
      -- evaluation of the simplex chart
      have H := congrArg Subtype.val
        ((simplexHomeo (faceEnum t) hi).apply_symm_apply
          (⟨x.1, by simpa [range_faceEnum] using x.2⟩ :
              {y:E // y ∈ convexHull ℝ (Set.range (faceEnum t))}))
      exact H
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private def __GlobalCoeff_faceIndex (s : Finset E) :=
  {t : Finset E // t ∈ (lexComplex s (lexFaces_inter s)).faces}
private instance __GlobalCoeff_faceIndex_finite (s : Finset E) : Finite (__GlobalCoeff_faceIndex s) :=
  @Finite.of_fintype _ (Set.Finite.fintype (lexComplex_faces_finite s (lexFaces_inter s)))
private def __GlobalCoeff_fiLex {s : Finset E} (a : __GlobalCoeff_faceIndex s) : lexFace s a.1 :=
  ((by simpa [lexComplex_faces s (lexFaces_inter s)] using a.2) :
    lexFace s a.1 ∧ a.1.Nonempty).1

/-- Continuous barycentric coefficients on a finite hull, supported on each
pulling face. This is the analytic gluing step; later subdivisions need only
refine the closed chambers within these already glued charts. -/
lemma exists_globalCoeff (s : Finset E) :
    let P := {x:E // x ∈ convexHull ℝ (s:Set E)}
    ∃ c : C(P, s → ℝ),
      (∀ x i, 0 ≤ c x i) ∧
      (∀ x, (∑ i : s, c x i) = 1) ∧
      (∀ x, (∑ i : s, c x i • (i:E)) = (x:E)) ∧
      (∀ (a : __GlobalCoeff_faceIndex s) (x:P) (hx : (x:E) ∈ convexHull ℝ (a.1:Set E)),
        c x = localFaceCoeff s a.1 (__GlobalCoeff_fiLex a).1 (faceEnum_indep (__GlobalCoeff_fiLex a))
          ⟨x.1, hx⟩) := by
  classical
  dsimp
  let τ := __GlobalCoeff_faceIndex s
  let A : τ → Set {x:E // x ∈ convexHull ℝ (s:Set E)} := fun a =>
    {x | (x:E) ∈ convexHull ℝ (a.1:Set E)}
  have hclosed (a:τ) : IsClosed (A a) := by
    -- finite convex hull is compact
    exact (Set.Finite.isCompact_convexHull ℝ (finite_mem_finset a.1)).isClosed.preimage continuous_subtype_val
  have hcover (x:{x:E // x ∈ convexHull ℝ (s:Set E)}) : ∃ a, x ∈ A a := by
    obtain ⟨t, ht, hn, hx⟩ := lexFaces_cover s x.1 x.2
    let a : τ := ⟨t, by rw [lexComplex_faces]; exact ⟨ht, hn⟩⟩
    exact ⟨a, hx⟩
  let g : τ → {x:E // x∈ convexHull ℝ (s:Set E)} → (s → ℝ) := fun a x =>
    if h : x ∈ A a then
      localFaceCoeff s a.1 (__GlobalCoeff_fiLex a).1 (faceEnum_indep (__GlobalCoeff_fiLex a)) ⟨x.1, h⟩
    else 0
  have g_inside (a:τ) (x:{x:E // x∈ convexHull ℝ (s:Set E)}) (h:x∈ A a) :
      g a x = localFaceCoeff s a.1 (__GlobalCoeff_fiLex a).1 (faceEnum_indep (__GlobalCoeff_fiLex a)) ⟨x.1,h⟩ := by
    simp [g, h]
  have gc (a:τ) : ContinuousOn (g a) (A a) := by
    apply continuousOn_iff_continuous_restrict.mpr
    let inc : (A a) → {y:E // y ∈ convexHull ℝ (a.1:Set E)} := fun x => ⟨x.1.1, x.2⟩
    have inci : Continuous inc :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have mainC : Continuous (fun x : A a =>
        localFaceCoeff s a.1 (__GlobalCoeff_fiLex a).1 (faceEnum_indep (__GlobalCoeff_fiLex a)) (inc x)) :=
      (continuous_localFaceCoeff s a.1 _ _).comp inci
    have eq : (A a).restrict (g a) = (fun x : A a =>
        localFaceCoeff s a.1 (__GlobalCoeff_fiLex a).1 (faceEnum_indep (__GlobalCoeff_fiLex a)) (inc x)) := by
      funext x
      exact g_inside a x.1 x.2
    rw [eq]
    exact mainC
  have compat (a b:τ) (x:{x:E // x∈ convexHull ℝ (s:Set E)})
      (ha:x∈ A a) (hb:x∈ A b) : g a x = g b x := by
    rw [g_inside a x ha, g_inside b x hb]
    let u : Finset E := a.1 ∩ b.1
    have hu : lexFace s u := lexFace_down (__GlobalCoeff_fiLex a) (Finset.inter_subset_left)
    have hxU : (x:E) ∈ convexHull ℝ (u:Set E) :=
      by
        simpa [u] using (lexFace_inter (__GlobalCoeff_fiLex a) (__GlobalCoeff_fiLex b) ⟨ha,hb⟩)
    let xu : {z:E // z ∈ convexHull ℝ (u:Set E)} := ⟨x.1,hxU⟩
    let cu : s → ℝ :=
      localFaceCoeff s u hu.1 (faceEnum_indep hu) xu
    have equA :
        localFaceCoeff s a.1 (__GlobalCoeff_fiLex a).1 (faceEnum_indep (__GlobalCoeff_fiLex a))
          ⟨x.1,ha⟩ = cu := by
      apply independent_face_coeff_eq (lexFace_independent (__GlobalCoeff_fiLex a)) (__GlobalCoeff_fiLex a).1
      · intro i hi
        exact localFaceCoeff_zero _ _ _ _ _ _ hi
      · intro i hi
        apply localFaceCoeff_zero _ _ _ _ _ _
        intro iu
        exact hi (Finset.inter_subset_left iu)
      · exact localFaceCoeff_sum _ _ _ _ _
      · exact localFaceCoeff_sum _ _ _ _ _
      · rw [localFaceCoeff_eval, localFaceCoeff_eval]
    have equB :
        localFaceCoeff s b.1 (__GlobalCoeff_fiLex b).1 (faceEnum_indep (__GlobalCoeff_fiLex b))
          ⟨x.1,hb⟩ = cu := by
      apply independent_face_coeff_eq (lexFace_independent (__GlobalCoeff_fiLex b)) (__GlobalCoeff_fiLex b).1
      · intro i hi
        exact localFaceCoeff_zero _ _ _ _ _ _ hi
      · intro i hi
        apply localFaceCoeff_zero _ _ _ _ _ _
        intro iu
        exact hi (Finset.inter_subset_right iu)
      · exact localFaceCoeff_sum _ _ _ _ _
      · exact localFaceCoeff_sum _ _ _ _ _
      · rw [localFaceCoeff_eval, localFaceCoeff_eval]
    exact equA.trans equB.symm
  obtain ⟨c0,hc,hval⟩ := finite_closed_paste A hclosed hcover g gc compat
  let c : C({x:E // x∈ convexHull ℝ (s:Set E)}, s → ℝ) := ⟨c0,hc⟩
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro x i
    obtain ⟨a,ha⟩ := hcover x
    change 0 ≤ c0 x i
    rw [hval a x ha]
    rw [g_inside a x ha]
    exact localFaceCoeff_nonneg _ _ _ _ _ _
  · intro x
    obtain ⟨a,ha⟩ := hcover x
    change (∑ i : s, c0 x i) = _
    rw [hval a x ha, g_inside a x ha]
    apply localFaceCoeff_sum
  · intro x
    obtain ⟨a,ha⟩ := hcover x
    change (∑ i : s, c0 x i • (i:E)) = _
    rw [hval a x ha, g_inside a x ha]
    apply localFaceCoeff_eval
  · intro a x hx
    change c0 x = _
    rw [hval a x hx, g_inside a x hx]
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalCoeff.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/SimplexCopies.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A colour copy on an independent simplex, obtained by the interleaved bin
formula in compact inverse coordinates. -/
def simplexCycMap {d q n : ℕ} (hd:0<d) (hq:0<q) (hn:0<n)
    (v : Fin d → E) (hv : AffineIndependent ℝ v) (r : Fin n) :
    C({x : E // x ∈ convexHull ℝ (Set.range v)},
      {x : E // x ∈ convexHull ℝ (Set.range v)}) := by
  let H := simplexHomeo v hv
  let ψ : {u : Fin d → ℝ // u ∈ coeffSimplex d} →
      {x : E // x ∈ convexHull ℝ (Set.range v)} := fun u =>
        ⟨simplexEval v (cycStep d q n r.val u),
          cycEval_mem_hull hd hq hn r.isLt v u.property.1 u.property.2⟩
  exact {
    toFun := fun x => ψ (H.symm x)
    continuous_toFun := by
      have hp : Continuous ψ := by
        exact ((continuous_cycEval (q:=q) (n:=n) (r:=r) v).comp
          continuous_subtype_val).subtype_mk _
      exact hp.comp H.symm.continuous }
@[simp] lemma simplexCycMap_apply {d q n : ℕ} (hd:0<d) (hq:0<q) (hn:0<n)
    (v : Fin d → E) (hv : AffineIndependent ℝ v) (r : Fin n)
    (x : {x : E // x ∈ convexHull ℝ (Set.range v)}) :
    ((simplexCycMap hd hq hn v hv r x) : E) =
      simplexEval v (cycStep d q n r.val ((simplexHomeo v hv).symm x : Fin d → ℝ)) := rfl
/-- Interleaved simplex copies preserve every convex extreme face of the surrounding
set; unlike ordinary charts this includes all proper faces exactly. -/
lemma simplexCycMap_mem_extreme {d q n : ℕ} (hd:0<d) (hq:0<q) (hn:0<n)
    (v : Fin d → E) (hv : AffineIndependent ℝ v) (r : Fin n)
    {B A : Set E} (hA : ∀ i, v i ∈ A) (hcA : Convex ℝ A)
    (hcB : Convex ℝ B) (hB : IsExtreme ℝ A B)
    (x : {x : E // x ∈ convexHull ℝ (Set.range v)}) (hx : (x:E) ∈ B) :
    ((simplexCycMap hd hq hn v hv r x) : E) ∈ B := by
  let u := (simplexHomeo v hv).symm x
  have hxu : simplexEval v (u : Fin d → ℝ) = (x:E) := by
    have hh := congrArg Subtype.val ((simplexHomeo v hv).apply_symm_apply x)
    change simplexEval v (u : Fin d → ℝ) = (x:E) at hh
    exact hh
  exact cycEval_mem_extreme hd hq hn r.isLt u.property.1 u.property.2
    hcA hA hcB hB (by rwa [hxu])

lemma simplexCycMap_dist {d q n : ℕ} (hd:0<d) (hq:0<q) (hn:0<n)
    (v : Fin d → E) (hv : AffineIndependent ℝ v) (r s : Fin n)
    (x : {x : E // x ∈ convexHull ℝ (Set.range v)}) :
    dist (simplexCycMap hd hq hn v hv r x)
      (simplexCycMap hd hq hn v hv s x) ≤
      ∑ i : Fin d, (2 / (q:ℝ)) * ‖v i‖ := by
  -- subtype metric is ambient
  change dist ((simplexCycMap hd hq hn v hv r x : _) : E)
    ((simplexCycMap hd hq hn v hv s x : _) : E) ≤ _
  exact cycEval_dist hq r.isLt s.isLt v
    ((simplexHomeo v hv).symm x : Fin d → ℝ)
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Exact closed-chamber sparsity in inverse coordinates. End cuts do not count,
so a face with `d` nonzero vertices only exposes `d-1` colours. -/
lemma simplexCycMap_const_cuts {d q n : ℕ} (hd:0<d) (hq:0<q) (hn:0<n)
    (v : Fin d → E) (hv : AffineIndependent ℝ v) (r : Fin n)
    (x y : {x : E // x ∈ convexHull ℝ (Set.range v)})
    {b : ℕ → ℕ}
    (hbtop : ∀ m, 0 < m → m < d → b m < q*n)
    (hbavoid : ∀ m, 0 < m → m < d → b m % n ≠ r.val)
    (hxch : ∀ m, 0 < m → m < d →
      cumCoord d ((simplexHomeo v hv).symm x : Fin d → ℝ) m ∈
        Set.Icc (linePoint 0 1 (q*n) (b m)) (linePoint 0 1 (q*n) (b m + 1)))
    (hych : ∀ m, 0 < m → m < d →
      cumCoord d ((simplexHomeo v hv).symm y : Fin d → ℝ) m ∈
        Set.Icc (linePoint 0 1 (q*n) (b m)) (linePoint 0 1 (q*n) (b m + 1))) :
    simplexCycMap hd hq hn v hv r x = simplexCycMap hd hq hn v hv r y := by
  apply Subtype.ext
  change simplexEval v _ = simplexEval v _
  unfold simplexEval
  apply Finset.sum_congr rfl
  intro i hi
  rw [cycStep_constant_of_chambers hq hn r.isLt
    (((simplexHomeo v hv).symm x).property.2)
    (((simplexHomeo v hv).symm y).property.2) hbtop hbavoid hxch hych i]
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/SimplexCopies.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/CycChambers.lean
section
set_option maxHeartbeats 12000000
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Finite closed chambers on a geometric independent simplex.  They are
preimages of the barycentric cut chambers under the coordinate
homeomorphism.  At this stage they are *cells*, not yet a triangulation:
promoting their finite closed cover to a face-compatible geometric complex
is exactly the remaining PL step. -/
def geoChamber {d : ℕ} (v : Fin d → E) (hv : AffineIndependent ℝ v)
    (q : ℕ) (b : Fin (d+1) → ℕ) : Set {x:E // x ∈ convexHull ℝ (Set.range v)} :=
  (simplexHomeo v hv).symm ⁻¹'
    ((↑) : {u : Fin d → ℝ // u ∈ coeffSimplex d} → (Fin d → ℝ)) ⁻¹'
      coeffChamber d q b

lemma geoChamber_closed {d : ℕ} (v : Fin d → E)
    (hv : AffineIndependent ℝ v) (q : ℕ) (b : Fin (d+1) → ℕ) :
    IsClosed (geoChamber v hv q b) := by
  unfold geoChamber
  exact ((isClosed_coeffChamber d q b).preimage continuous_subtype_val).preimage
    (simplexHomeo v hv).symm.continuous

lemma mem_geoChamber {d : ℕ} {v : Fin d → E}
    {hv : AffineIndependent ℝ v} {q : ℕ} {b : Fin (d+1) → ℕ}
    {x : {x:E // x ∈ convexHull ℝ (Set.range v)}} :
    x ∈ geoChamber v hv q b ↔
      ((simplexHomeo v hv).symm x : Fin d → ℝ) ∈ coeffChamber d q b := Iff.rfl

lemma iUnion_geoChamber_fin {d q : ℕ} (hq : 0 < q)
    (v : Fin d → E) (hv : AffineIndependent ℝ v) :
    (⋃ b : Fin (d+1) → Fin q, geoChamber v hv q (fun m => (b m).val)) =
      (Set.univ : Set {x:E // x ∈ convexHull ℝ (Set.range v)}) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have hu : (((simplexHomeo v hv).symm x :
      {u : Fin d → ℝ // u ∈ coeffSimplex d}) : Fin d → ℝ) ∈ coeffSimplex d :=
    ((simplexHomeo v hv).symm x).property
  have cover := (Set.ext_iff.mp (iUnion_coeffChamber_fin (d:=d) hq)
    ((simplexHomeo v hv).symm x : Fin d → ℝ))
  have hb : ((simplexHomeo v hv).symm x : Fin d → ℝ) ∈
      (⋃ b : Fin (d+1) → Fin q,
        coeffChamber d q (fun m => (b m).val)) := cover.mpr hu
  rcases Set.mem_iUnion.mp hb with ⟨b,hb⟩
  exact ⟨b, hb⟩

/-- The colours charged to the internal walls. We charge their residue classes
rather than the (finer) interleaved wall numbers. -/
def chamberColours {d q n : ℕ} (_hn : 0 < n)
    (b : Fin (d+1) → Fin (q*n)) : Finset (Fin n) :=
  (Finset.univ.filter (fun m : Fin (d+1) => 0 < m.val ∧ m.val < d)).image
    (fun m => ⟨(b m).val % n, Nat.mod_lt _ _hn⟩)
lemma mem_chamberColours {d q n : ℕ} {hn : 0 < n}
    {b : Fin (d+1) → Fin (q*n)} {r : Fin n} :
    r ∈ chamberColours hn b ↔
      ∃ m : Fin (d+1), (0 < m.val ∧ m.val < d) ∧ (b m).val % n = r.val := by
  classical
  unfold chamberColours
  simp [Fin.ext_iff]
lemma card_chamberColours_plus_one {d q n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (b : Fin (d+1) → Fin (q*n)) :
    (chamberColours hn b).card + 1 ≤ d := by
  classical
  let T : Finset (Fin (d+1)) :=
    Finset.univ.filter (fun m : Fin (d+1) => 0 < m.val ∧ m.val < d)
  have hc : (chamberColours hn b).card ≤ T.card := by
    change (T.image _).card ≤ T.card
    exact Finset.card_image_le
  let z : Fin (d+1) := ⟨0, by omega⟩
  let last : Fin (d+1) := ⟨d, by omega⟩
  let R : Finset (Fin (d+1)) := Finset.univ.erase z
  have sub : T ⊆ R := by
    intro x hx
    have hp := (Finset.mem_filter.mp hx).2
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro e; have ee := congrArg Fin.val e
    dsimp [z] at ee
    omega
  have lastR : last ∈ R := by
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro e; have ee := congrArg Fin.val e
    dsimp [last,z] at ee
    omega
  have lastN : last ∉ T := by
    dsimp [T,last]
    simp
  have strict : T ⊂ R := Finset.ssubset_iff_subset_ne.mpr
    ⟨sub, by intro h; exact lastN (h ▸ lastR)⟩
  have tc : T.card < R.card := Finset.card_lt_card strict
  have rc : R.card = d := by
    dsimp [R,z]
    simp
  omega

/-- On a fixed finite geometric chamber every copy whose residue is not an
internal wall is exactly constant.  End cuts 0 and d never need be charged. -/
lemma simplexCycMap_const_not_mem {d q n : ℕ} (hd : 0 < d)
    (hq : 0 < q) (hn : 0 < n)
    (v : Fin d → E) (hv : AffineIndependent ℝ v)
    (r : Fin n) (b : Fin (d+1) → Fin (q*n))
    (hr : r ∉ chamberColours hn b)
    {x y : {x:E // x ∈ convexHull ℝ (Set.range v)}}
    (hx : x ∈ geoChamber v hv (q*n) (fun m => (b m).val))
    (hy : y ∈ geoChamber v hv (q*n) (fun m => (b m).val)) :
    simplexCycMap hd hq hn v hv r x =
      simplexCycMap hd hq hn v hv r y := by

  let bins : ℕ → ℕ := fun m => if h : m < d+1 then (b ⟨m,h⟩).val else 0
  apply simplexCycMap_const_cuts hd hq hn v hv r x y (b:=bins)
  · intro m hm0 hmd
    dsimp [bins]
    simp [show m < d+1 by omega, show m ≤ d by omega, (b ⟨m, by omega⟩).isLt]
  · intro m hm0 hmd he
    have e' : (b ⟨m, by omega⟩).val % n = r.val := by
      simpa [bins, show m < d+1 by omega, show m ≤ d by omega] using he
    apply hr
    exact mem_chamberColours.mpr
      ⟨⟨m, by omega⟩, ⟨hm0,hmd⟩, e'⟩
  · intro m hm0 hmd
    simpa [bins, show m < d+1 by omega, show m ≤ d by omega] using
      (coeffChamber_cut (u:=((simplexHomeo v hv).symm x : Fin d → ℝ)) hx ⟨m, by omega⟩)
  · intro m hm0 hmd
    simpa [bins, show m < d+1 by omega, show m ≤ d by omega] using
      (coeffChamber_cut (u:=((simplexHomeo v hv).symm y : Fin d → ℝ)) hy ⟨m, by omega⟩)


/-- Complete finite-closed-cover statement on a simplex.  No affine chart in
the ambient space is needed and the estimate is uniform across chambers. -/
lemma simplexCycMaps_chambers {d q n : ℕ} (hd : 0 < d)
    (hq : 0 < q) (hn : 0 < n)
    (v : Fin d → E) (hv : AffineIndependent ℝ v) :
    let P := {x:E // x ∈ convexHull ℝ (Set.range v)}
    ∃ φ : Fin n → C(P,P),
      (∀ b : Fin (d+1) → Fin (q*n),
        ∃ A : Finset (Fin n), A.card + 1 ≤ d ∧
          ∀ r : Fin n, r ∉ A → ∀ x y : P,
            x ∈ geoChamber v hv (q*n) (fun m => (b m).val) →
            y ∈ geoChamber v hv (q*n) (fun m => (b m).val) →
            φ r x = φ r y) ∧
      (∀ A B : Set E, (∀ i, v i ∈ A) → Convex ℝ A → Convex ℝ B →
        IsExtreme ℝ A B → ∀ r : Fin n, ∀ x : P, (x:E) ∈ B →
          ((φ r x : P) : E) ∈ B) ∧
      (∀ r s : Fin n, ∀ x : P,
        dist (φ r x) (φ s x) ≤ ∑ i : Fin d, (2 / (q:ℝ)) * ‖v i‖) := by
  classical
  dsimp
  refine ⟨fun r => simplexCycMap hd hq hn v hv r, ?_, ?_, ?_⟩
  · intro b
    refine ⟨chamberColours hn b, card_chamberColours_plus_one hd hn b, ?_⟩
    intro r hr x y hx hy
    exact simplexCycMap_const_not_mem hd hq hn v hv r b hr hx hy
  · intro A B ha hc hc' he r x hx
    exact simplexCycMap_mem_extreme hd hq hn v hv r ha hc hc' he x hx
  · intro r s x
    exact simplexCycMap_dist hd hq hn v hv r s x
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/CycChambers.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/FaceCompat.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section

/-! Face compatibility for ordered cumulative-coordinate maps.

A major irritation in pasting the simplex maps is that two neighbouring simplices
are written with different lists of vertices.  The ordered formula is in fact
literal on overlaps: insert zero coordinates into a larger ordered list, and it
doesn't change.  The lemmas below isolate the combinatorial fact at the level of
`Fin`; they use no convexity.
-/

/-- Extension of a coefficient vector along an embedding of finite ordinals. -/
def zeroExtend {a b : ℕ} (e : Fin a ↪ Fin b) (u : Fin a → ℝ) (j : Fin b) : ℝ :=
  if h : j ∈ Set.range e then u (Classical.choose h) else 0

@[simp] lemma zeroExtend_image {a b : ℕ} (e : Fin a ↪ Fin b)
    (u : Fin a → ℝ) (i : Fin a) : zeroExtend e u (e i) = u i := by
  classical
  unfold zeroExtend
  have h : e i ∈ Set.range e := ⟨i,rfl⟩
  rw [dif_pos h]
  have h' := Classical.choose_spec h
  exact congrArg u (e.injective h')

lemma zeroExtend_not_mem {a b : ℕ} (e : Fin a ↪ Fin b)
    (u : Fin a → ℝ) {j : Fin b} (h : j ∉ Set.range e) : zeroExtend e u j = 0 := by
  simp [zeroExtend, h]

lemma zeroExtend_sum {a b : ℕ} (e : Fin a ↪ Fin b)
    (u : Fin a → ℝ) : (∑ j : Fin b, zeroExtend e u j) = ∑ i : Fin a, u i := by
  classical
  -- extend a supported function over the image finset
  let ee : Fin a ↪ Fin b := e
  let S : Finset (Fin b) := Finset.univ.map ee
  calc
    (∑ j : Fin b, zeroExtend e u j)
        = ∑ j ∈ S, zeroExtend e u j := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _) 
            intro j hj hnot
            have hr : j ∉ Set.range e := by
              intro hm
              rcases hm with ⟨i, rfl⟩
              exact hnot (by simp [S, ee])
            simp [zeroExtend_not_mem e u hr]
    _ = ∑ i : Fin a, zeroExtend e u (e i) := by
            classical
            dsimp [S]
            -- map image sum
            simp [ee]
    _ = _ := by simp

lemma simplexEval_zeroExtend {a b : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin a ↪ Fin b) (v : Fin b → E) (u : Fin a → ℝ) :
    simplexEval v (zeroExtend e u) = simplexEval (fun i => v (e i)) u := by
  classical
  unfold simplexEval
  let S : Finset (Fin b) := Finset.univ.map e
  calc
    (∑ j : Fin b, zeroExtend e u j • v j)
       = ∑ j ∈ S, zeroExtend e u j • v j := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _) 
            intro j hj hnot
            have hr : j ∉ Set.range e := by
              intro hm
              rcases hm with ⟨i, rfl⟩
              exact hnot (by simp [S])
            simp [zeroExtend_not_mem e u hr]
    _ = ∑ i : Fin a, zeroExtend e u (e i) • v (e i) := by
            dsimp [S]
            simp
    _ = _ := by simp

/-- Initial sums commute with insertion of zero coordinates. Only strict
monotonicity of the map of ordinals is needed. The cut `m` is deliberately
allowed to equal the last index; this handles both endpoint cuts. -/
lemma cumCoord_zeroExtend_at {a b : ℕ} (e : Fin a ↪ Fin b)
    (he : StrictMono e) (u : Fin a → ℝ) (m : Fin a) :
    cumCoord b (zeroExtend e u) (e m).val = cumCoord a u m.val := by
  classical
  unfold cumCoord
  -- split the ambient filter; outside the image all terms vanish
  let Sb : Finset (Fin b) :=
    (Finset.univ : Finset (Fin b)).filter (fun j => j.val < (e m).val)
  let Sa : Finset (Fin a) :=
    (Finset.univ : Finset (Fin a)).filter (fun i => i.val < m.val)
  have himage : Sb.filter (fun j => j ∈ Set.range e) = Sa.map e := by
    ext j
    simp [Sb, Sa]
    constructor
    · rintro ⟨hj, i, rfl⟩
      refine ⟨i, ?_, rfl⟩
      have : i < m := (he.lt_iff_lt).mp (by exact hj)
      exact this
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, ⟨i,rfl⟩⟩
      have : e i < e m := he hi
      exact this
  -- sum filters to image and use map.
  change (∑ j ∈ Sb, zeroExtend e u j) = ∑ i ∈ Sa, u i
  calc
    (∑ j ∈ Sb, zeroExtend e u j)
       = ∑ j ∈ Sb.filter (fun j => j ∈ Set.range e), zeroExtend e u j := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _) 
          intro j hj hnot
          have hn : j ∉ Set.range e := by
            intro h
            exact hnot (Finset.mem_filter.mpr ⟨hj, h⟩)
          simp [zeroExtend_not_mem e u hn]
    _ = ∑ j ∈ Sa.map e, zeroExtend e u j := by rw [himage]
    _ = ∑ i ∈ Sa, zeroExtend e u (e i) := by simp
    _ = _ := by simp

lemma cumCoord_zeroExtend_after {a b : ℕ} (e : Fin a ↪ Fin b)
    (he : StrictMono e) (u : Fin a → ℝ) (m : Fin a) :
    cumCoord b (zeroExtend e u) ((e m).val + 1) =
      cumCoord a u (m.val + 1) := by
  rw [cumCoord_succ (e m).isLt, cumCoord_succ m.isLt,
    zeroExtend_image]
  rw [cumCoord_zeroExtend_at e he]

/-- At an index not appearing in the list every cumulative-coordinate
step is zero, for either the one-block or cyclic construction. -/
lemma cycStep_zeroExtend_off {a b q n r : ℕ}
    (e : Fin a ↪ Fin b) (u : Fin a → ℝ) {j : Fin b}
    (hj : j ∉ Set.range e) : cycStep b q n r (zeroExtend e u) j = 0 := by
  apply cycStep_zero_of_coord_zero (u:=zeroExtend e u)
    (i:=j)
  simp [zeroExtend, hj]

lemma baryStep_zeroExtend_off {a b n r : ℕ}
    (e : Fin a ↪ Fin b) (u : Fin a → ℝ) {j : Fin b}
    (hj : j ∉ Set.range e) : baryStep b n r (zeroExtend e u) j = 0 := by
  apply baryStep_zero_of_coord_zero (u:=zeroExtend e u)
    (i:=j)
  simp [zeroExtend, hj]

/-- The whole cyclic coefficient vector commutes, not merely its evaluation.
This stronger pointwise version is handy on intersections of independent
simplices, because inverse simplex coordinates are unique. -/
lemma cycStep_zeroExtend_on {a b q n r : ℕ}
    (e : Fin a ↪ Fin b) (he : StrictMono e) (u : Fin a → ℝ) (i : Fin a) :
    cycStep b q n r (zeroExtend e u) (e i) = cycStep a q n r u i := by
  unfold cycStep
  rw [cumCoord_zeroExtend_after e he, cumCoord_zeroExtend_at e he]

lemma baryStep_zeroExtend_on {a b n r : ℕ}
    (e : Fin a ↪ Fin b) (he : StrictMono e) (u : Fin a → ℝ) (i : Fin a) :
    baryStep b n r (zeroExtend e u) (e i) = baryStep a n r u i := by
  unfold baryStep
  rw [cumCoord_zeroExtend_after e he, cumCoord_zeroExtend_at e he]

/-- Evaluation of a step is invariant under zero-extension. -/
lemma cycEval_zeroExtend {a b q n r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin a ↪ Fin b) (he : StrictMono e)
    (v : Fin b → E) (u : Fin a → ℝ) :
    simplexEval v (cycStep b q n r (zeroExtend e u)) =
      simplexEval (fun i => v (e i)) (cycStep a q n r u) := by
  classical
  unfold simplexEval
  let S : Finset (Fin b) := Finset.univ.map e
  calc
    (∑ j : Fin b, cycStep b q n r (zeroExtend e u) j • v j)
       = ∑ j ∈ S, cycStep b q n r (zeroExtend e u) j • v j := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j hj hnot
          have hnmem : j ∉ Set.range e := by
            intro hm; rcases hm with ⟨i,rfl⟩
            exact hnot (by simp [S])
          simp [cycStep_zeroExtend_off e u hnmem]
    _ = ∑ i : Fin a, cycStep b q n r (zeroExtend e u) (e i) • v (e i) := by
          dsimp [S]
          simp
    _ = _ := by simp [cycStep_zeroExtend_on e he]

lemma baryEval_zeroExtend {a b n r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin a ↪ Fin b) (he : StrictMono e)
    (v : Fin b → E) (u : Fin a → ℝ) :
    simplexEval v (baryStep b n r (zeroExtend e u)) =
      simplexEval (fun i => v (e i)) (baryStep a n r u) := by
  classical
  unfold simplexEval
  let S : Finset (Fin b) := Finset.univ.map e
  calc
    (∑ j : Fin b, baryStep b n r (zeroExtend e u) j • v j)
       = ∑ j ∈ S, baryStep b n r (zeroExtend e u) j • v j := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j hj hnot
          have hnmem : j ∉ Set.range e := by
            intro hm; rcases hm with ⟨i,rfl⟩
            exact hnot (by simp [S])
          simp [baryStep_zeroExtend_off e u hnmem]
    _ = ∑ i : Fin a, baryStep b n r (zeroExtend e u) (e i) • v (e i) := by
          dsimp [S]
          simp
    _ = _ := by simp [baryStep_zeroExtend_on e he]

end
end FamiliesProof

namespace FamiliesProof
open scoped BigOperators
open Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma affineIndependent_comp_embedding {a b : ℕ}
    (e : Fin a ↪ Fin b) {v : Fin b → E}
    (hv : AffineIndependent ℝ v) :
    AffineIndependent ℝ (fun i : Fin a => v (e i)) := by
  simpa [Function.comp_def] using hv.comp_embedding e

lemma hull_mono_ordered_embedding {a b : ℕ}
    (e : Fin a ↪ Fin b) (v : Fin b → E) :
    convexHull ℝ (Set.range (fun i : Fin a => v (e i))) ⊆
      convexHull ℝ (Set.range v) := by
  apply convexHull_mono
  rintro z ⟨i, rfl⟩
  exact ⟨e i, rfl⟩

/-- The subtype map from an ordered face to the containing simplex. -/
def faceInclusion {a b : ℕ} (e : Fin a ↪ Fin b) (v : Fin b → E) :
    {x : E // x ∈ convexHull ℝ (Set.range (fun i : Fin a => v (e i)))} →
      {x : E // x ∈ convexHull ℝ (Set.range v)} := fun x =>
        ⟨x, hull_mono_ordered_embedding e v x.property⟩
@[simp] lemma faceInclusion_val {a b : ℕ}
    (e : Fin a ↪ Fin b) (v : Fin b → E)
    (x : {x : E // x ∈ convexHull ℝ (Set.range (fun i : Fin a => v (e i)))}) :
    ((faceInclusion e v x : _) : E) = x := rfl

/- Inverse coordinates on a face are obtained simply by inserting zero. This
contains precisely the arithmetic needed to compare the two local continuous
maps; no choice of the inverse homeomorphism survives. -/
lemma simplexHomeo_face_coords {a b : ℕ} (ha : 0 < a)
    (e : Fin a ↪ Fin b) (he : StrictMono e)
    (v : Fin b → E) (hv : AffineIndependent ℝ v)
    (x : {x : E // x ∈ convexHull ℝ (Set.range (fun i : Fin a => v (e i)))}) :
    let hv' : AffineIndependent ℝ (fun i : Fin a => v (e i)) :=
      affineIndependent_comp_embedding e hv
    let u : Fin a → ℝ :=
      ((simplexHomeo (fun i : Fin a => v (e i)) hv').symm x : Fin a → ℝ)
    ((simplexHomeo v hv).symm (faceInclusion e v x) : Fin b → ℝ) =
      zeroExtend e u := by
  classical
  dsimp
  let vv : Fin a → E := fun i => v (e i)
  have hv' : AffineIndependent ℝ vv := affineIndependent_comp_embedding e hv
  let z := (simplexHomeo vv hv').symm x
  let u : Fin a → ℝ := (z : Fin a → ℝ)
  let U : Fin b → ℝ := zeroExtend e u
  -- inverse simplex coordinates lie in the standard simplex
  have zun : ∀ i, 0 ≤ u i := z.property.1
  have zus : (∑ i, u i) = 1 := z.property.2
  have Un : ∀ j, 0 ≤ U j := by
    intro j
    by_cases h : j ∈ Set.range e
    · rcases h with ⟨i,rfl⟩
      simpa [U] using zun i
    · simp [U, zeroExtend, h]
  have Us : (∑ j, U j) = 1 := by simpa [U, zus] using (zeroExtend_sum e u)
  -- evaluate these proposed coordinates.
  have evz : simplexEval vv u = (x:E) := by
    have hh := congrArg Subtype.val ((simplexHomeo vv hv').apply_symm_apply x)
    change simplexEval vv u = (x : E) at hh
    exact hh
  have evU : simplexEval v U = ((faceInclusion e v x) : E) := by
    change simplexEval v U = (x:E)
    rw [simplexEval_zeroExtend]
    exact evz
  let w := (simplexHomeo v hv).symm (faceInclusion e v x)
  have ws : (∑ i, (w : Fin b → ℝ) i)=1 := w.property.2
  have evw : simplexEval v (w : Fin b → ℝ) = ((faceInclusion e v x) : E) := by
    have hh := congrArg Subtype.val ((simplexHomeo v hv).apply_symm_apply
      (faceInclusion e v x))
    change simplexEval v (w : Fin b → ℝ) = ((faceInclusion e v x) : E) at hh
    exact hh
  have hEq : (w : Fin b → ℝ) = U :=
    simplexEval_eq hv ws Us (evw.trans evU.symm)
  simpa [vv, hv', z, U, u, w]
    using hEq

/-- `simplexCycMap` is literally the same function on a simplex and any
order-preserving face. This is the pasting condition required on closed faces
of an ordered geometric triangulation. -/
lemma simplexCycMap_face {a b q n : ℕ} (ha : 0 < a)
    (hb : 0 < b) (hq : 0 < q) (hn : 0 < n)
    (e : Fin a ↪ Fin b) (he : StrictMono e)
    (v : Fin b → E) (hv : AffineIndependent ℝ v) (r : Fin n)
    (x : {x : E // x ∈ convexHull ℝ (Set.range (fun i : Fin a => v (e i)))}) :
    simplexCycMap hb hq hn v hv r (faceInclusion e v x) =
      faceInclusion e v (simplexCycMap ha hq hn _
        (affineIndependent_comp_embedding e hv) r x) := by
  classical
  apply Subtype.ext
  -- unfold evaluation and replace inverse coordinates
  change simplexEval v (cycStep b q n r.val
       ((simplexHomeo v hv).symm (faceInclusion e v x) : Fin b → ℝ)) =
    simplexEval (fun i : Fin a => v (e i))
      (cycStep a q n r.val
         ((simplexHomeo (fun i : Fin a => v (e i))
            (affineIndependent_comp_embedding e hv)).symm x : Fin a → ℝ))
  rw [simplexHomeo_face_coords ha e he v hv x]
  exact cycEval_zeroExtend e he v _

lemma simplexBaryEval_face {a b n r: ℕ} (ha : 0 < a)
    (e : Fin a ↪ Fin b) (he : StrictMono e)
    (v : Fin b → E) (hv : AffineIndependent ℝ v)
    (x : {x : E // x ∈ convexHull ℝ (Set.range (fun i : Fin a => v (e i)))}) :
    simplexEval v (baryStep b n r
      ((simplexHomeo v hv).symm (faceInclusion e v x) : Fin b → ℝ)) =
    simplexEval (fun i : Fin a => v (e i)) (baryStep a n r
      ((simplexHomeo (fun i : Fin a => v (e i))
        (affineIndependent_comp_embedding e hv)).symm x : Fin a → ℝ)) := by
  rw [simplexHomeo_face_coords ha e he v hv x]
  exact baryEval_zeroExtend e he v _
end
end FamiliesProof

namespace FamiliesProof
open scoped BigOperators
noncomputable section
/-- Number of old coordinates before an ambient cut after inserting zeroes. -/
def faceRank {a b : ℕ} (e : Fin a ↪ Fin b) (t : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin a)).filter (fun i => (e i).val < t)).card
lemma faceRank_le {a b : ℕ} (e : Fin a ↪ Fin b) (t : ℕ) : faceRank e t ≤ a := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

/-- A monotone embedding identifies the filtered segment with `range faceRank`.
The statement uses natural numbers rather than `Fin (b+1)` to include the final
cut and cuts past the last selected vertex. -/
lemma faceRank_filter {a b : ℕ} (e : Fin a ↪ Fin b)
    (he : StrictMono e) (t : ℕ) :
    ((Finset.univ : Finset (Fin a)).filter (fun i => (e i).val < t)) =
      (Finset.univ : Finset (Fin a)).filter (fun i => i.val < faceRank e t) := by
  classical
  let S : Finset (Fin a) :=
    (Finset.univ : Finset (Fin a)).filter (fun i => (e i).val < t)
  have down : ∀ i ∈ S, ∀ j : Fin a, j ≤ i → j ∈ S := by
    intro i hi j hji
    have hi' := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hle : e j ≤ e i := he.monotone hji
    exact lt_of_le_of_lt (by exact_mod_cast hle) hi'
  -- every initial segment of a finite ordinal is given by its cardinal
  ext i
  simp only [S] at down
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, faceRank]
  -- generic count of predecessors argument, in both directions
  constructor
  · intro hi
    -- `{0,...,i}` lies inside this initial segment.
    let I : Finset (Fin a) := (Finset.univ : Finset (Fin a)).filter
      (fun j => j.val ≤ i.val)
    have sub : I ⊆ (Finset.univ : Finset (Fin a)).filter
          (fun j => (e j).val < t) := by
      intro j hj
      have hj' : j ≤ i := by
        exact (Fin.le_iff_val_le_val).2 (Finset.mem_filter.mp hj).2
      exact down i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) j hj'
    have cardI : I.card = i.val + 1 := by
      have hlt : i.val + 1 ≤ a := by omega
      have H := (Fin.card_filter_val_lt (n:=a) (m:=i.val+1))
      rw [min_eq_right hlt] at H
      -- `< i+1` is `≤ i` in nat
      simpa [I, Nat.lt_succ_iff] using H
    have hc := Finset.card_le_card sub
    rw [cardI] at hc
    omega
  · intro hi
    by_contra hnot
    have hlow : t ≤ (e i).val := by omega
    -- all elements of the segment are < i.
    have sub : ((Finset.univ : Finset (Fin a)).filter (fun j => (e j).val < t)) ⊆
        (Finset.univ : Finset (Fin a)).filter (fun j => j.val < i.val) := by
      intro j hj
      have hje := (Finset.mem_filter.mp hj).2
      have hnle : ¬ i ≤ j := by
        intro hle
        have h' : e i ≤ e j := he.monotone hle
        have : (e i).val ≤ (e j).val := by exact h'
        omega
      have hjlt : j < i := lt_of_not_ge hnle
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjlt⟩
    have hc := Finset.card_le_card sub
    have cr : ((Finset.univ : Finset (Fin a)).filter
        (fun j => j.val < i.val)).card = i.val := by
      have H := (Fin.card_filter_val_lt (n:=a) (m:=i.val))
      have hlt : i.val ≤ a := by omega
      rw [min_eq_right hlt] at H
      simpa using H
    rw [cr] at hc
    exact (not_le_of_gt hi) hc

/-- Natural-cut version of `cumCoord_zeroExtend_at`. It describes the plateaux
as well as the selected cuts. -/
lemma cumCoord_zeroExtend_rank {a b : ℕ} (e : Fin a ↪ Fin b)
    (he : StrictMono e) (u : Fin a → ℝ) (t : ℕ) :
    cumCoord b (zeroExtend e u) t = cumCoord a u (faceRank e t) := by
  classical
  unfold cumCoord
  let Sb : Finset (Fin b) := (Finset.univ : Finset (Fin b)).filter
    (fun j => j.val < t)
  let Sa : Finset (Fin a) := (Finset.univ : Finset (Fin a)).filter
    (fun i => i.val < faceRank e t)
  have im : Sb.filter (fun j => j ∈ Set.range e) = Sa.map e := by
    ext j
    simp [Sb, Sa]
    constructor
    · rintro ⟨hj, i, rfl⟩
      refine ⟨i, ?_, rfl⟩
      have hif : i ∈ ((Finset.univ : Finset (Fin a)).filter
          (fun i => (e i).val < t)) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      rw [faceRank_filter e he] at hif
      exact (Finset.mem_filter.mp hif).2
    · rintro ⟨i, hi, rfl⟩
      have hif : i ∈ ((Finset.univ : Finset (Fin a)).filter
          (fun i => (e i).val < t)) := by
        rw [faceRank_filter e he]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      exact ⟨(Finset.mem_filter.mp hif).2, ⟨i,rfl⟩⟩
  change (∑ j ∈ Sb, zeroExtend e u j) = ∑ i ∈ Sa, u i
  calc
    _ = ∑ j ∈ Sb.filter (fun j => j ∈ Set.range e), zeroExtend e u j := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hn
      have hn' : j ∉ Set.range e := by
        intro h
        exact hn (Finset.mem_filter.mpr ⟨hj,h⟩)
      simp [zeroExtend_not_mem e u hn']
    _ = ∑ j ∈ Sa.map e, zeroExtend e u j := by rw [im]
    _ = ∑ i ∈ Sa, zeroExtend e u (e i) := by simp
    _ = _ := by simp

end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/FaceCompat.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalBound.lean
section
open Set
open scoped BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/- Uniform bound for all faces of a finite configuration. This avoids choosing a
   new grid size on each pulling simplex. -/
lemma norm_sum_face_le {s t : Finset E} (h : t ⊆ s) :
    (∑ i ∈ t, ‖i‖) ≤ ∑ i ∈ s, ‖i‖ := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h (by
    intro i hi hj
    exact norm_nonneg _)
lemma scaled_norm_sum_face_le {s t : Finset E} (h : t ⊆ s) {q : ℕ} (hq : 0 < q) :
    (∑ i : t, (2 / (q:ℝ)) * ‖(i:E)‖) ≤
      (2 / (q:ℝ)) * (∑ i ∈ s, ‖i‖) := by
  have Q : (0:ℝ) ≤ (2 / (q:ℝ)) := by positivity
  -- first remove the constant from the sum of a subtype.
  calc
    (∑ i : t, (2 / (q:ℝ)) * ‖(i:E)‖) =
      (2 / (q:ℝ)) * (∑ i : t, ‖(i:E)‖) := by rw [Finset.mul_sum]
    _ = (2 / (q:ℝ)) * (∑ i ∈ t.attach, ‖(i:E)‖) := rfl
    _ = (2 / (q:ℝ)) * (∑ i ∈ t, ‖i‖) := by
        rw [Finset.sum_attach]
    _ ≤ (2 / (q:ℝ)) * (∑ i ∈ s, ‖i‖) := by
      gcongr
lemma simplexCycMap_dist_uniform
    {s t : Finset E} (ht : t ⊆ s)
    {d q n : ℕ} (hd : 0 < d) (hq : 0 < q) (hn : 0 < n)
    (e : Fin d ≃ t) (r r' : Fin n)
    (hi : AffineIndependent ℝ (fun i : Fin d => (e i : E)))
    (x : {x : E // x ∈ convexHull ℝ (Set.range (fun i : Fin d => (e i : E)))}) :
    dist (simplexCycMap hd hq hn (fun i : Fin d => (e i : E)) hi r x)
      (simplexCycMap hd hq hn (fun i : Fin d => (e i : E)) hi r' x) ≤
      (2 / (q:ℝ)) * (∑ i ∈ s, ‖i‖) := by
  refine le_trans (simplexCycMap_dist hd hq hn _ hi r r' x) ?_
  have H := scaled_norm_sum_face_le (s:=s) (t:=t) ht hq
  -- reindex the finite equivalence.
  calc
    (∑ i : Fin d, (2 / (q:ℝ)) * ‖(e i : E)‖) =
      (∑ i : t, (2 / (q:ℝ)) * ‖(i:E)‖) := by
        exact Fintype.sum_equiv e (fun i : Fin d => (2 / (q:ℝ)) * ‖(e i : E)‖)
          (fun i : t => (2 / (q:ℝ)) * ‖(i:E)‖) (fun _ => rfl)
    _ ≤ (2 / (q:ℝ)) * (∑ i ∈ s, ‖i‖) := H
lemma exists_uniform_grid (s : Finset E) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ, 0 < q ∧ (2 / (q:ℝ)) * (∑ i ∈ s, ‖i‖) ≤ δ := by
  let a : ℝ := 2 * (∑ i ∈ s, ‖i‖) / δ
  obtain ⟨q,hqgt⟩ : ∃ q : ℕ, a < q := exists_nat_gt a
  refine ⟨max 1 q, by omega, ?_⟩
  have hsum : 0 ≤ ∑ i ∈ s, ‖i‖ := Finset.sum_nonneg (by
    intro i hi; exact norm_nonneg _)
  have qq : (0:ℝ) < (max 1 q : ℕ) := by exact_mod_cast (show 0 < max 1 q by omega)
  calc
    (2 / (max 1 q : ℕ)) * (∑ i ∈ s, ‖i‖) =
      (2 * (∑ i ∈ s, ‖i‖)) / (max 1 q : ℕ) := by ring
    _ ≤ δ := by
      apply (div_le_iff₀ qq).2
      have : 2 * (∑ i ∈ s, ‖i‖) / δ < (max 1 q : ℕ) := by
        calc
          _ = a := rfl
          _ < q := hqgt
          _ ≤ (max 1 q : ℕ) := by exact_mod_cast (Nat.le_max_right 1 q)
      have hh := (div_lt_iff₀ hδ).1 this
      nlinarith
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalBound.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalCopies.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The cyclic copy map written on a whole finite hull in a chosen coefficient
section.  The coefficients need not be independent. This global formula has
literal support on every extreme face and gives continuity before any geometric
subdivision is chosen. -/
def globalCopy (s : Finset E)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) (r : Fin n) :
    let P := {x:E // x ∈ convexHull ℝ (s:Set E)}
    (P → E) :=
  fun x =>
    simplexEval (faceEnum s)
      (cycStep s.card q n r.val
        (fun i : Fin s.card => c x ((configEquiv s).symm i)))

lemma continuous_globalCopy (s : Finset E)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) (r : Fin n) :
    Continuous (globalCopy s c q n hq hn r) := by
  unfold globalCopy
  exact (continuous_cycEval (v:= faceEnum s)).comp
    (continuous_pi (fun i =>
      (continuous_apply ((configEquiv s).symm i)).comp c.continuous))

lemma globalCopy_mem_hull (s : Finset E)
    (hd : 0 < s.card)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (c0 : ∀ x i, 0 ≤ c x i) (c1 : ∀ x, (∑ i : s, c x i) = 1)
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) (r : Fin n)
    (x : {x:E // x ∈ convexHull ℝ (s:Set E)}) :
    globalCopy s c q n hq hn r x ∈ convexHull ℝ (s:Set E) := by
  unfold globalCopy
  have H : simplexEval (faceEnum s)
      (cycStep s.card q n r.val (fun i : Fin s.card =>
        c x ((configEquiv s).symm i))) ∈
      convexHull ℝ (Set.range (faceEnum s)) := by
    apply cycEval_mem_hull hd hq hn r.isLt (faceEnum s)
    · intro i; exact c0 x _
    ·
      exact (Equiv.sum_comp (configEquiv s).symm
        (fun z : s => c x z)).trans (c1 x)
  rwa [range_faceEnum] at H

/-- If `B` is a convex extreme face of the full hull, every global cyclic copy
of a point in `B` remains in `B`. No chart or chamber is needed for this fact. -/
lemma globalCopy_mem_extreme (s : Finset E)
    (hd : 0 < s.card)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (c0 : ∀ x i, 0 ≤ c x i) (c1 : ∀ x, (∑ i : s, c x i) = 1)
    (ceval : ∀ x, (∑ i : s, c x i • (i:E)) = (x:E))
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) (r : Fin n)
    {B : Set E} (hBc : Convex ℝ B)
    (hB : IsExtreme ℝ (convexHull ℝ (s:Set E)) B)
    (x : {x:E // x ∈ convexHull ℝ (s:Set E)}) (hx : (x:E) ∈ B) :
    globalCopy s c q n hq hn r x ∈ B := by
  let u : Fin s.card → ℝ := fun i => c x ((configEquiv s).symm i)
  have hu : ∀ i, 0 ≤ u i := fun i => c0 _ _
  have hs : (∑ i, u i) = 1 := by
    change (∑ i : Fin s.card, c x ((configEquiv s).symm i)) = _
    exact (Equiv.sum_comp (configEquiv s).symm
      (fun z : s => c x z)).trans (c1 x)
  have he : simplexEval (faceEnum s) u = (x:E) := by
    unfold simplexEval
    -- rewrite the evaluation by the enumeration equivalence
    calc
      (∑ i : Fin s.card, u i • faceEnum s i) =
          ∑ i : Fin s.card, c x ((configEquiv s).symm i) •
            (((configEquiv s).symm i : s) : E) := by rfl
      _ = ∑ z : s, c x z • (z:E) := by
        exact Equiv.sum_comp (configEquiv s).symm
          (fun z : s => c x z • (z:E))
      _ = (x:E) := ceval x
  have hv : ∀ i : Fin s.card, faceEnum s i ∈ convexHull ℝ (s:Set E) := by
    intro i
    apply subset_convexHull ℝ (s:Set E)
    exact ((configEquiv s).symm i).property
  have hh := cycEval_mem_extreme (E:=E)
    hd hq hn r.isLt (v:=faceEnum s) (u:=u) hu hs
    (convex_convexHull ℝ (s:Set E)) hv hBc hB (he ▸ hx)
  exact hh

/-- Bundled form of the copies, available as soon as a finite nonempty hull
is given. Their restrictions to boundary faces are automatic. -/
def globalCopyMap (s : Finset E) (hd : 0 < s.card)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (c0 : ∀ x i, 0 ≤ c x i) (c1 : ∀ x, (∑ i : s, c x i) = 1)
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) (r : Fin n) :
    C({x:E // x ∈ convexHull ℝ (s:Set E)},
      {x:E // x ∈ convexHull ℝ (s:Set E)}) where
  toFun x := ⟨globalCopy s c q n hq hn r x,
    globalCopy_mem_hull s hd c c0 c1 q n hq hn r x⟩
  continuous_toFun := (continuous_globalCopy s c q n hq hn r).subtype_mk _

end
end FamiliesProof

namespace FamiliesProof
noncomputable section
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma globalCopy_dist (s : Finset E)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) (r r' : Fin n)
    (x : {x:E // x ∈ convexHull ℝ (s:Set E)}) :
    dist (globalCopy s c q n hq hn r x)
      (globalCopy s c q n hq hn r' x) ≤
      (2/(q:ℝ)) * (∑ i ∈ s, ‖i‖) := by
  unfold globalCopy
  calc
    dist (simplexEval (faceEnum s)
        (cycStep s.card q n ↑r fun i => c x ((configEquiv s).symm i)))
      (simplexEval (faceEnum s)
        (cycStep s.card q n ↑r' fun i => c x ((configEquiv s).symm i))) ≤
        ∑ i : Fin s.card, (2/(q:ℝ))*‖faceEnum s i‖ :=
          cycEval_dist hq r.isLt r'.isLt _ _
    _ = ∑ z : s, (2/(q:ℝ))*‖(z:E)‖ := by
      exact Equiv.sum_comp (configEquiv s).symm
        (fun z : s => (2/(q:ℝ))*‖(z:E)‖)
    _ = (2/(q:ℝ)) * ∑ z : s, ‖(z:E)‖ := by rw [Finset.mul_sum]
    _ = (2/(q:ℝ)) * (∑ z ∈ s.attach, ‖(z:E)‖) := rfl
    _ = (2/(q:ℝ)) * (∑ z ∈ s, ‖z‖) := by rw [Finset.sum_attach]
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open Set
open scoped BigOperators Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def globalChamber (s : Finset E)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (N : ℕ) (b : Fin (s.card+1) → ℕ) :
    Set {x:E // x ∈ convexHull ℝ (s:Set E)} :=
  {x | (fun i : Fin s.card => c x ((configEquiv s).symm i)) ∈
      coeffChamber s.card N b}
lemma globalChamber_closed (s : Finset E)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (N : ℕ) (b : Fin (s.card+1) → ℕ) :
    IsClosed (globalChamber s c N b) := by
  unfold globalChamber
  apply IsClosed.preimage _ (isClosed_coeffChamber _ _ _)
  exact continuous_pi fun i =>
    (continuous_apply ((configEquiv s).symm i)).comp c.continuous
lemma globalChamber_cover (s : Finset E)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (c0 : ∀ x i, 0 ≤ c x i) (c1 : ∀ x, (∑ i : s, c x i) = 1)
    (N : ℕ) (hN : 0 < N)
    (x:{x:E // x∈ convexHull ℝ (s:Set E)}) :
    ∃ b : Fin (s.card+1) → Fin N,
      x ∈ globalChamber s c N (fun m => (b m).val) := by
  let u : Fin s.card → ℝ := fun i => c x ((configEquiv s).symm i)
  have hu : u ∈ coeffSimplex s.card := by
    constructor
    · intro i; exact c0 _ _
    · exact (Equiv.sum_comp (configEquiv s).symm
        (fun z : s => c x z)).trans (c1 x)
  rcases coeffSimplex_exists_chamber hN hu with ⟨b,hb,hc⟩
  let b' : Fin (s.card+1) → Fin N := fun m => ⟨b m, hb m⟩
  refine ⟨b', ?_⟩
  exact hc
lemma globalCopy_const_chamber (s : Finset E)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) (r : Fin n)
    (b : Fin (s.card+1) → Fin (q*n))
    (hr : r ∉ chamberColours hn b)
    {x y : {x:E // x∈ convexHull ℝ (s:Set E)}}
    (hx : x ∈ globalChamber s c (q*n) (fun m => (b m).val))
    (hy : y ∈ globalChamber s c (q*n) (fun m => (b m).val)) :
    globalCopy s c q n hq hn r x = globalCopy s c q n hq hn r y := by
  let u : Fin s.card → ℝ := fun i => c x ((configEquiv s).symm i)
  let w : Fin s.card → ℝ := fun i => c y ((configEquiv s).symm i)
  let bins : ℕ → ℕ := fun m => if h : m < s.card+1 then (b ⟨m,h⟩).val else 0
  have su := coeffChamber_mass hx
  have sw := coeffChamber_mass hy
  have step : ∀ i,
      cycStep s.card q n r.val u i = cycStep s.card q n r.val w i := by
    apply cycStep_constant_of_chambers hq hn r.isLt su sw (b:=bins)
    · intro m hm hmd
      have hlt : m < s.card+1 := by omega
      have be : bins m = (b ⟨m,hlt⟩).val := by
        dsimp [bins]
        split <;> rename_i h
        · rfl
        · exact False.elim (h hlt)
      rw [be]
      exact (b ⟨m,hlt⟩).isLt
    · intro m hm hmd hbad
      have hlt : m < s.card+1 := by omega
      have be : bins m = (b ⟨m,hlt⟩).val := by
        dsimp [bins]
        split <;> rename_i h
        · rfl
        · exact False.elim (h hlt)
      apply hr
      apply mem_chamberColours.mpr
      refine ⟨⟨m,hlt⟩, ⟨hm,hmd⟩, ?_⟩
      simpa [be] using hbad
    · intro m hm hmd
      have hlt : m < s.card+1 := by omega
      have be : bins m = (b ⟨m,hlt⟩).val := by
        dsimp [bins]
        split <;> rename_i h
        · rfl
        · exact False.elim (h hlt)
      rw [be]
      exact coeffChamber_cut hx ⟨m, hlt⟩
    · intro m hm hmd
      have hlt : m < s.card+1 := by omega
      have be : bins m = (b ⟨m,hlt⟩).val := by
        dsimp [bins]
        split <;> rename_i h
        · rfl
        · exact False.elim (h hlt)
      rw [be]
      exact coeffChamber_cut hy ⟨m, hlt⟩
  unfold globalCopy
  unfold simplexEval
  apply Finset.sum_congr rfl
  intro i hi
  rw [step i]
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalCopies.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalCyclic.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The positions of a selected support in the fixed global enumeration. -/
noncomputable def facePos (s t : Finset E) : Finset (Fin s.card) := by
  classical exact Finset.univ.filter (fun i => faceEnum s i ∈ t)

lemma facePos_card {s t : Finset E} (h : t ⊆ s) : (facePos s t).card = t.card := by
  classical
  let e : (Fin s.card) ≃ s := (configEquiv s).symm
  let U : Finset s := Finset.univ.filter (fun i : s => (i:E) ∈ t)
  let incl : t ↪ s :=
    ⟨fun x => ⟨(x:E), h x.property⟩,
     by
       intro a b hh
       have e0 : (a:E) = (b:E) := congrArg (fun z : s => (z:E)) hh
       exact Subtype.ext e0⟩
  have Ueq : U = Finset.univ.map incl := by
    ext x
    constructor
    · intro hx
      have hxt : (x:E) ∈ t := (Finset.mem_filter.mp hx).2
      simpa [incl] using (show ∃ z : t, (⟨(z:E), h z.property⟩ : s)=x
        from ⟨⟨x,hxt⟩, Subtype.ext rfl⟩)
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨z,hz,ze⟩
      have ze' : (z:E) = (x:E) := congrArg Subtype.val ze
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [← ze'] using z.property
  have mapU : (facePos s t).map e.toEmbedding = U := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨i,hi,eq⟩
      have ii : faceEnum s i ∈ t := (Finset.mem_filter.mp hi).2
      have ee : (x:E) = faceEnum s i := by
        simpa [e, faceEnum] using congrArg Subtype.val eq.symm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [ee] using ii⟩
    · intro hx
      have xt : (x:E) ∈ t := (Finset.mem_filter.mp hx).2
      let i : Fin s.card := (configEquiv s) x
      have ie : e i = x := (Equiv.symm_apply_apply _ _)
      apply Finset.mem_map.mpr
      refine ⟨i, ?_, ie⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [e, faceEnum, i] using xt
  calc
    _ = ((facePos s t).map e.toEmbedding).card := (Finset.card_map _).symm
    _ = U.card := congrArg Finset.card mapU
    _ = (Finset.univ.map incl).card := congrArg Finset.card Ueq
    _ = t.card := by simp

/-- Increasing positions of a face, in the order inherited from the ambient
configuration (not the arbitrary order `configEquiv t`). -/
def faceInc (s t : Finset E) : Fin (facePos s t).card ↪ Fin s.card :=
  (Finset.orderEmbOfFin (facePos s t) rfl).toEmbedding

lemma faceInc_mono (s t : Finset E) : StrictMono (faceInc s t) :=
  (Finset.orderEmbOfFin (facePos s t) rfl).strictMono

lemma mem_faceInc {s t : Finset E} (i : Fin (facePos s t).card) :
    faceEnum s (faceInc s t i) ∈ t := by
  classical
  have h : faceInc s t i ∈ facePos s t :=
    by
      change ((Finset.orderIsoOfFin (facePos s t) rfl) i : Fin s.card) ∈ facePos s t
      exact ((Finset.orderIsoOfFin (facePos s t) rfl) i).property
  change _ ∈ Finset.univ.filter (fun j => faceEnum s j ∈ t) at h
  exact (Finset.mem_filter.mp h).2

lemma range_faceInc {s t : Finset E} :
    Set.range (faceInc s t) = (↑(facePos s t) : Set (Fin s.card)) := by
  classical
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    change ((Finset.orderIsoOfFin (facePos s t) rfl) i : Fin s.card) ∈ facePos s t
    exact ((Finset.orderIsoOfFin (facePos s t) rfl) i).property
  · intro hx
    -- inverse of the order iso to the subtype
    let j : (facePos s t) := ⟨x, hx⟩
    let i : Fin (facePos s t).card :=
      (Finset.orderIsoOfFin (facePos s t) rfl).symm j
    refine ⟨i, ?_⟩
    have := (Finset.orderIsoOfFin (facePos s t) rfl).apply_symm_apply j
    exact congrArg Subtype.val this

/-- Enumeration of a face in inherited order. -/
def inheritedFace (s t : Finset E) : Fin (facePos s t).card → E :=
  fun i => faceEnum s (faceInc s t i)
lemma range_inheritedFace {s t : Finset E} (ht : t ⊆ s) :
    Set.range (inheritedFace s t) = (t : Set E) := by
  classical
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact mem_faceInc i
  · intro hx
    have xs : x ∈ (s:Set E) := ht hx
    have rr := (range_faceEnum s).symm.subset
    obtain ⟨i, hi⟩ := (Set.ext_iff.mp (range_faceEnum s) x).2 xs
    subst x
    have hpos : i ∈ facePos s t := by
      exact (show i ∈ Finset.univ.filter (fun j => faceEnum s j ∈ t) from Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
    rcases (Set.ext_iff.mp (range_faceInc (s:=s) (t:=t)) i).2 hpos with ⟨j,hj⟩
    refine ⟨j, ?_⟩
    simpa [inheritedFace, hj]

lemma inheritedFace_indep {s t : Finset E} (ht : lexFace s t) :
    AffineIndependent ℝ (inheritedFace s t) := by
  classical
  have hi0 := lexFace_independent ht
  let g : Fin (facePos s t).card ↪ t :=
    ⟨fun i => ⟨inheritedFace s t i, mem_faceInc i⟩, by
      intro a b hab
      have hc : faceEnum s (faceInc s t a) = faceEnum s (faceInc s t b) :=
        congrArg (fun z : t => (z:E)) hab
      have hc' : ((configEquiv s).symm (faceInc s t a)) =
          ((configEquiv s).symm (faceInc s t b)) := Subtype.ext hc
      have inds : (faceInc s t a) = (faceInc s t b) :=
        (configEquiv s).symm.injective hc'
      exact (faceInc s t).injective inds⟩
  have hh := hi0.comp_embedding g
  exact hh

/-- Local coefficients supplied by `globalCoeff` on a lex face equal the
zero-extended independent simplex coordinates in inherited order.  This
is the key algebraic bridge for doing all cyclic steps in one global list;
the ambient finite configuration need not be independent. -/
lemma globalCoeff_zeroExtend_face
    (s t : Finset E) (ht : lexFace s t)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (hc : ∀ (x : {x:E // x ∈ convexHull ℝ (s:Set E)})
      (_hx : (x:E) ∈ convexHull ℝ (t:Set E)),
      c x = localFaceCoeff s t ht.1 (faceEnum_indep ht)
        ⟨x.1, _hx⟩)
    (x : {x:E // x ∈ convexHull ℝ (s:Set E)})
    (hx : (x:E) ∈ convexHull ℝ (t:Set E)) :
    let a := (facePos s t).card
    let inc := faceInc s t
    let w : Fin a → E := inheritedFace s t
    let hi : AffineIndependent ℝ w := inheritedFace_indep ht
    let ux : {z:E // z ∈ convexHull ℝ (Set.range w)} :=
      ⟨x.1, by rw [range_inheritedFace ht.1]; exact hx⟩
    let u : Fin a → ℝ :=
      ((simplexHomeo w hi).symm ux : Fin a → ℝ)
    (fun i : Fin s.card => c x ((configEquiv s).symm i)) =
      zeroExtend inc u := by
  classical
  -- set up the compressed simplex and its coefficients
  dsimp
  let w : Fin (facePos s t).card → E := inheritedFace s t
  let hi : AffineIndependent ℝ w := inheritedFace_indep ht
  let ux : {z:E // z∈ convexHull ℝ (Set.range w)} :=
    ⟨x.1, by rw [range_inheritedFace ht.1]; exact hx⟩
  let u : Fin (facePos s t).card → ℝ :=
    ((simplexHomeo w hi).symm ux : Fin (facePos s t).card → ℝ)
  let inc := faceInc s t
  let V : s → ℝ := fun z => zeroExtend inc u (configEquiv s z)
  let U : s → ℝ := localFaceCoeff s t ht.1 (faceEnum_indep ht) ⟨x.1,hx⟩
  have vz : ∀ i : s, (i:E) ∉ t → V i = 0 := by
    intro i hit
    have no : (configEquiv s i : Fin s.card) ∉ Set.range inc := by
      intro h
      rcases h with ⟨j,hj⟩
      have eq : i = (⟨inheritedFace s t j, ht.1 (mem_faceInc j)⟩ : s) := by
        apply (configEquiv s).injective
        simpa [inc, inheritedFace, faceEnum] using hj.symm
      exact hit (eq ▸ (mem_faceInc j))
    exact zeroExtend_not_mem inc u no
  have uz : ∀ i : s, (i:E) ∉ t → U i = 0 := by
    intro i hit
    exact localFaceCoeff_zero _ _ _ _ _ _ hit
  have us : (∑ i : s, U i) = 1 := localFaceCoeff_sum _ _ _ _ _
  have vs : (∑ i : s, V i) = 1 := by
    change (∑ i : s, zeroExtend inc u (configEquiv s i)) = _
    rw [Equiv.sum_comp (configEquiv s) (fun j : Fin s.card => zeroExtend inc u j)]
    rw [zeroExtend_sum]
    exact ((simplexHomeo w hi).symm ux).property.2
  have evU : (∑ i : s, U i • (i:E)) = (x:E) :=
    localFaceCoeff_eval _ _ _ _ _
  have evV : (∑ i : s, V i • (i:E)) = (x:E) := by
    change (∑ i : s, zeroExtend inc u (configEquiv s i) • (i:E)) = _
    have hchange : (fun i : s =>
        zeroExtend inc u (configEquiv s i) • (i:E)) =
        (fun i : s =>
          (fun j : Fin s.card => zeroExtend inc u j • faceEnum s j) (configEquiv s i)) := by
            funext i
            simp [faceEnum]
    rw [hchange, Equiv.sum_comp (configEquiv s)
      (fun j : Fin s.card => zeroExtend inc u j • faceEnum s j)]
    change simplexEval (faceEnum s) (zeroExtend inc u) = _
    rw [simplexEval_zeroExtend]
    change simplexEval w u = _
    have hh := congrArg Subtype.val ((simplexHomeo w hi).apply_symm_apply ux)
    exact hh
  have eqUV : U = V :=
    independent_face_coeff_eq (lexFace_independent ht) ht.1 uz vz us vs (evU.trans evV.symm)
  funext i
  have hcx := congrFun (hc x hx) ((configEquiv s).symm i)
  have ee := congrFun eqUV ((configEquiv s).symm i)
  change c x ((configEquiv s).symm i) = _
  rw [hcx]
  change U ((configEquiv s).symm i) = _
  rw [ee]
  change zeroExtend inc u (configEquiv s ((configEquiv s).symm i)) = _
  rw [(configEquiv s).apply_symm_apply]
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalCyclic.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalFaceCopies.lean
section
open Set
open scoped Topology BigOperators
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/- A face chart for the global cyclic copies.  Unlike a gluing assertion this
   is an *equality in the ambient vector space*. Thus continuous copies may be
   defined once using `globalCopyMap`; no pasting choices are left for a
   subdivision. -/
lemma globalCopy_eq_inheritedFace
    (s t : Finset E) (ht : lexFace s t)
    (c : C({x:E // x ∈ convexHull ℝ (s:Set E)}, s → ℝ))
    (hc : ∀ (x : {x:E // x ∈ convexHull ℝ (s:Set E)})
      (_hx : (x:E) ∈ convexHull ℝ (t:Set E)),
      c x = localFaceCoeff s t ht.1 (faceEnum_indep ht) ⟨x.1, _hx⟩)
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) (ha : 0 < (facePos s t).card)
    (r : Fin n)
    (x : {x:E // x ∈ convexHull ℝ (s:Set E)})
    (hx : (x:E) ∈ convexHull ℝ (t:Set E)) :
    let w := inheritedFace s t
    let hi : AffineIndependent ℝ w := inheritedFace_indep ht
    let ux : {z:E // z ∈ convexHull ℝ (Set.range w)} :=
      ⟨x.1, by rw [range_inheritedFace ht.1]; exact hx⟩
    globalCopy s c q n hq hn r x =
      ((simplexCycMap ha hq hn w hi r ux :
        {z:E // z ∈ convexHull ℝ (Set.range w)}) : E) := by
  classical
  dsimp
  let w := inheritedFace s t
  let hi : AffineIndependent ℝ w := inheritedFace_indep ht
  let ux : {z:E // z ∈ convexHull ℝ (Set.range w)} :=
    ⟨x.1, by rw [range_inheritedFace ht.1]; exact hx⟩
  let u : Fin (facePos s t).card → ℝ :=
    ((simplexHomeo w hi).symm ux : Fin (facePos s t).card → ℝ)
  let inc : Fin (facePos s t).card ↪ Fin s.card := faceInc s t
  have coeff : (fun i : Fin s.card => c x ((configEquiv s).symm i)) =
      zeroExtend inc u := by
    exact globalCoeff_zeroExtend_face s t ht c hc x hx
  change simplexEval (faceEnum s)
      (cycStep s.card q n r.val
        (fun i : Fin s.card => c x ((configEquiv s).symm i))) = _
  -- the image of the global evaluation over the zero extension is the small
  -- simplex evaluation in its inherited order
  rw [coeff]
  have H := cycEval_zeroExtend (q:=q) (n:=n) (r:=r.val)
      (faceInc s t) (faceInc_mono s t) (faceEnum s) u
  -- the right hand side is definitionally the cyclic simplex map
  change simplexEval (faceEnum s)
      (cycStep s.card q n r.val (zeroExtend inc u)) =
    simplexEval w (cycStep (facePos s t).card q n r.val u)
  exact H
end
end FamiliesProof

namespace FamiliesProof
noncomputable section
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- No dimension hypothesis has to be chosen on a (nonempty) pulling face. -/
lemma facePos_card_pos {s t : Finset E} (hs : t ⊆ s) (ht : t.Nonempty) :
    0 < (facePos s t).card := by
  rw [facePos_card hs]
  exact Finset.card_pos.mpr ht
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GlobalFaceCopies.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridBasic.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
/-- Lattice barycentric vertices on d ordered points, of denominator n.
Using bounded naturals keeps the parameter a finite type. -/
def GridVert (d n : ℕ) := {a : Fin d → Fin (n+1) // ∑ i, (a i).val = n}
noncomputable instance (d n) : Fintype (GridVert d n) := by
  classical
  unfold GridVert
  infer_instance
instance (d n) : DecidableEq (GridVert d n) := Classical.decEq _
variable {d n : ℕ}
def gp (a : GridVert d n) (m : ℕ) : ℕ :=
    ∑ i ∈ (Finset.univ.filter (fun i : Fin d => i.val < m)), (a.1 i).val
@[simp] lemma gp_zero (a : GridVert d n) : gp a 0 = 0 := by simp [gp]
lemma gp_large (a : GridVert d n) {m : ℕ} (hm : d ≤ m) : gp a m = n := by
  simp [gp, Finset.filter_true_of_mem, show ∀ i : Fin d, i ∈ (Finset.univ : Finset (Fin d)) → i.val < m from fun i hi => lt_of_lt_of_le i.isLt hm, a.property]

/-- cumulative-product order and cubical spread. -/
def gpLe (a b : GridVert d n) : Prop := ∀ m : ℕ, gp a m ≤ gp b m
def gpNear (a b : GridVert d n) : Prop := ∀ m : ℕ, gp a m ≤ gp b m + 1
@[refl] lemma gpLe_rfl (a : GridVert d n) : gpLe a a := fun m => le_rfl
@[trans] lemma gpLe_trans {a b c : GridVert d n} (h : gpLe a b) (h' : gpLe b c) : gpLe a c := fun m => (h m).trans (h' m)
def gpClose (a b : GridVert d n) : Prop := gpNear a b ∧ gpNear b a
lemma gpClose_symm {a b : GridVert d n} (h : gpClose a b) : gpClose b a := ⟨h.2,h.1⟩
def gu (a : GridVert d n) : Fin d → ℝ := fun i => (a.1 i).val / (n:ℝ)
lemma gu_nonneg (a : GridVert d n) : ∀ i, 0 ≤ gu a i := by
  intro i; dsimp [gu]; positivity
lemma gu_mass (hn : 0 < n) (a : GridVert d n) : (∑ i, gu a i) = 1 := by
  simp [gu, div_eq_mul_inv, ← Finset.sum_mul]
  rw [← Nat.cast_sum]
  rw [a.property]
  norm_num [Nat.ne_of_gt hn]
lemma gu_simplex (hn : 0 < n) (a : GridVert d n) : gu a ∈ coeffSimplex d :=
 ⟨gu_nonneg a, gu_mass hn a⟩
lemma gu_inj (hn : 0 < n) : Function.Injective (@gu d n) := by
  intro a b h
  have hval : ∀ i : Fin d, (a.val i).val = (b.val i).val := by
    intro i
    have e := congrFun h i
    dsimp [gu] at e
    have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have ee : ((a.val i).val:ℝ) = ((b.val i).val:ℝ) := by
      exact (div_left_inj' hn').mp e
    exact_mod_cast ee
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact hval i
lemma cum_gu (a : GridVert d n) (m : ℕ) :
    cumCoord d (gu a) m = (gp a m : ℝ) / (n:ℝ) := by
  classical
  simp [cumCoord, gp, gu]
  rw [Finset.sum_div]

end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridBasic.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/RefineOne.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma mem_coeffChamber_one {d : ℕ} {u : Fin d → ℝ}
  (hu : u ∈ coeffSimplex d) : u ∈ coeffChamber d 1 (fun _ => 0) := by
  apply coeffChamber_mem.mpr
  refine ⟨hu.1, hu.2, fun m => ?_⟩
  have mono := cumCoord_mono hu.1
  have lo : (0:ℝ) ≤ cumCoord d u m.val := by
    have z := mono (Nat.zero_le m.val)
    simpa [cumCoord_zero] using z
  have mm : m.val ≤ d := by omega
  have hi : cumCoord d u m.val ≤ 1 := by
    have q := mono mm
    simpa [cumCoord_large (u:=u) (m:=d), hu.2] using q
  norm_num [linePoint]
  exact ⟨lo,hi⟩

/-- Degenerate single-bin case of the global chamber refinement; no subdivision
is needed, the pulling complex itself does the job. -/
lemma chamber_refine_one (s : Finset E) :
    ∃ M : Geometry.SimplicialComplex ℝ E,
      M.faces.Finite ∧
      M.space = convexHull ℝ (s : Set E) ∧
      ∀ D ∈ M.facets,
        ∃ (t : Finset E) (ht : lexFace s t) (hne : t.Nonempty)
          (b : Fin ((facePos s t).card+1) → Fin 1),
          ∀ x : E, x ∈ convexHull ℝ (D : Set E) →
            ∃ hx : x ∈ convexHull ℝ (Set.range (inheritedFace s t)),
              (⟨x,hx⟩ : {z : E // z ∈ convexHull ℝ
                (Set.range (inheritedFace s t))}) ∈
                geoChamber (inheritedFace s t)
                  (inheritedFace_indep ht) 1 (fun m => (b m).val) := by
  classical
  -- Pulling faces cover the hull (the lex proof is independent of dimension).
  have hinter := lexFaces_inter s
  have hcover := lexFaces_cover s
  let M := lexComplex s hinter
  refine ⟨M, lexComplex_faces_finite s hinter,
    lexComplex_space s hinter hcover, ?_⟩
  intro D hD
  have hface : D ∈ M.faces := (Geometry.SimplicialComplex.mem_facets.mp hD).1
  have htD : lexFace s D ∧ D.Nonempty := by
    simpa [M, lexComplex_faces s hinter] using hface
  refine ⟨D, htD.1, htD.2, (fun _ => 0), ?_⟩
  intro x hx
  have hx' : x ∈ convexHull ℝ (Set.range (inheritedFace s D)) := by
    simpa [range_inheritedFace htD.1.1] using hx
  refine ⟨hx', ?_⟩
  have hu := ((simplexHomeo (inheritedFace s D)
       (inheritedFace_indep htD.1)).symm
       (⟨x,hx'⟩ : {z : E // z ∈ convexHull ℝ
          (Set.range (inheritedFace s D))})).property
  exact mem_coeffChamber_one hu

lemma lexFace_self_of_indep {s : Finset E} (hi : AffineIndependent ℝ ((↑) : s → E)) :
    lexFace s s := by
  classical
  refine ⟨fun a => id, ?_⟩
  intro H
  rcases H with ⟨u, hu, hp, _⟩
  rcases hp with ⟨i, hip, _⟩
  have hz := (affineIndependent_iff.mp hi) (Finset.univ : Finset s) u
      (by simpa using hu.1) (by simpa using hu.2) i (Finset.mem_univ _)
  linarith

lemma chamber_refine_empty (n : ℕ) :
    ∃ M : Geometry.SimplicialComplex ℝ E,
      M.faces.Finite ∧ M.space = convexHull ℝ ((∅ : Finset E) : Set E) ∧
      ∀ D ∈ M.facets,
        ∃ (t : Finset E) (ht : lexFace ∅ t) (hne : t.Nonempty)
          (b : Fin ((facePos (∅ : Finset E) t).card+1) → Fin n),
          ∀ x : E, x ∈ convexHull ℝ (D : Set E) →
            ∃ hx : x ∈ convexHull ℝ (Set.range (inheritedFace (∅ : Finset E) t)),
              (⟨x,hx⟩ : {y : E // y ∈ convexHull ℝ
                (Set.range (inheritedFace (∅ : Finset E) t))}) ∈
                geoChamber (inheritedFace (∅ : Finset E) t)
                  (inheritedFace_indep ht) n (fun m => (b m).val) := by
  classical
  refine ⟨⊥, ?_, ?_, ?_⟩
  · rw [Geometry.SimplicialComplex.faces_bot]
    exact Set.toFinite _
  · simp [Geometry.SimplicialComplex.space_bot]
  · intro D hD
    have hf := (Geometry.SimplicialComplex.mem_facets.mp hD).1
    rw [Geometry.SimplicialComplex.faces_bot] at hf
    exact hf.elim

lemma chamber_refine_singleton (z : E) (n : ℕ) (hn : 0 < n) :
    ∃ M : Geometry.SimplicialComplex ℝ E,
      M.faces.Finite ∧ M.space = convexHull ℝ (({z} : Finset E) : Set E) ∧
      ∀ D ∈ M.facets,
        ∃ (t : Finset E) (ht : lexFace {z} t) (hne : t.Nonempty)
          (b : Fin ((facePos {z} t).card+1) → Fin n),
          ∀ x : E, x ∈ convexHull ℝ (D : Set E) →
            ∃ hx : x ∈ convexHull ℝ (Set.range (inheritedFace {z} t)),
              (⟨x,hx⟩ : {y : E // y ∈ convexHull ℝ
                (Set.range (inheritedFace {z} t))}) ∈
                geoChamber (inheritedFace {z} t)
                  (inheritedFace_indep ht) n (fun m => (b m).val) := by
  classical
  refine ⟨singletonComplex z, singletonComplex_faces_finite z, ?_, ?_⟩
  · simp [singletonComplex_space, convexHull_singleton]
  · intro D hD
    have hface := (Geometry.SimplicialComplex.mem_facets.mp hD).1
    have eq : D = {z} := by simpa [singletonComplex_faces] using hface
    obtain ⟨t,ht,hne,hz⟩ := lexFaces_cover ({z} : Finset E) z
      (by simp [convexHull_singleton])
    have hz' : z ∈ convexHull ℝ (Set.range (inheritedFace {z} t)) := by
      simpa [range_inheritedFace ht.1] using hz
    let xx : {y : E // y ∈ convexHull ℝ (Set.range (inheritedFace {z} t))} :=
      ⟨z,hz'⟩
    have hu := ((simplexHomeo (inheritedFace {z} t)
       (inheritedFace_indep ht)).symm xx).property
    obtain ⟨b,hb,hbc⟩ := coeffSimplex_exists_chamber hn hu
    let bb : Fin ((facePos {z} t).card+1) → Fin n := fun m => ⟨b m, hb m⟩
    refine ⟨t,ht,hne,bb,?_⟩
    intro x hx
    have xeq : x = z := by
      have : x ∈ ({z} : Set E) := by simpa [eq, convexHull_singleton] using hx
      simpa using this
    subst x
    refine ⟨hz', ?_⟩
    exact hbc
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/RefineOne.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridOrder.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {d n : ℕ}
/-- The cumulative array remembers a composition. Differences of consecutive prefix sums
recover every part. This rather elementary lemma is useful when grid vertices of two
faces meet; one can compare prefixes instead of the barycentric vector itself. -/
lemma gp_succ (a : GridVert d n) {m : ℕ} (hm : m < d) :
    gp a (m+1) = gp a m + (a.1 ⟨m,hm⟩).val := by
  classical
  unfold gp
  have filt : (Finset.univ : Finset (Fin d)).filter (fun v => v.val < m+1) =
        insert ⟨m,hm⟩ ((Finset.univ : Finset (Fin d)).filter (fun v => v.val < m)) := by
    ext v
    simp
    constructor
    · intro h
      by_cases h' : v.val = m
      · left; exact Fin.ext h'
      · right; omega
    · intro h
      rcases h with h|h
      · simpa [h]
      · omega
  rw [filt, Finset.sum_insert]
  · omega
  · simp

lemma gp_inj {a b : GridVert d n} (h : ∀ m : ℕ, gp a m = gp b m) : a = b := by
  classical
  apply Subtype.ext
  funext i
  apply Fin.ext
  have A := gp_succ a i.isLt
  have B := gp_succ b i.isLt
  rw [h, h] at A
  simpa using (Nat.add_left_cancel (A.symm.trans B))

lemma gpLe_antisymm {a b : GridVert d n} (h : gpLe a b) (h' : gpLe b a) : a = b :=
  gp_inj (fun m => Nat.le_antisymm (h m) (h' m))

lemma gp_mono (a : GridVert d n) : Monotone (gp a) := by
  classical
  intro m l h
  unfold gp
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp at hi ⊢
    omega
  · intro i hi hj
    exact Nat.zero_le _

lemma gp_le_all (a : GridVert d n) (m : ℕ) : gp a m ≤ n := by
  have h := gp_mono a (show m ≤ max m d by omega)
  rw [gp_large a (m:= max m d) (by omega)] at h
  exact h

lemma gp_of_gu {a b : GridVert d n} (hn : 0 < n) :
    gu a = gu b ↔ a = b := ⟨fun h => gu_inj hn h, congrArg _⟩

lemma gp_close_of_le_succ {a b : GridVert d n}
    (h₁ : gpLe a b) (h₂ : gpNear b a) : gpClose a b := by
  -- A pair in the same elementary cube has both prefix arrays at distance ≤1.
  refine ⟨?_, h₂⟩
  intro m
  exact Nat.le_add_right_of_le (h₁ m)

/-- Prefix inequalities detect the standard chamber of a lattice vertex. Unlike the
coverage argument, this direction has no floor/rounding choices. -/
lemma gu_mem_coeffChamber (hn : 0 < n) (a : GridVert d n) :
    gu a ∈ coeffChamber d n
      (fun m : Fin (d+1) => gp a m.val) := by
  apply coeffChamber_mem.mpr
  refine ⟨gu_nonneg a, gu_mass hn a, ?_⟩
  intro m
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [cum_gu]
  unfold linePoint
  constructor
  · simp
  · change (gp a m.val : ℝ) / (n:ℝ) ≤
      ((0:ℝ) + (1-0) * ((gp a m.val + 1:ℕ):ℝ) / (n:ℝ))
    norm_num
    exact (div_le_div_iff_of_pos_right hn').2 (by exact_mod_cast (Nat.le_add_right _ _))

/-- All vertices of a chain in one elementary prefix cube already lie in a single
closed cumulative-coordinate chamber. This is the easy half of the still missing
Freudenthal refinement: once a finite chain triangulation has been installed its
faces automatically satisfy the Morrison--Walker cuts. -/
lemma gu_chain_same_chamber (hn : 0 < n) (p : GridVert d n)
    {a : GridVert d n}
    (hlo : gpLe p a) (hhi : gpNear a p) :
    gu a ∈ coeffChamber d n
      (fun m : Fin (d+1) => gp p m.val) := by
  apply coeffChamber_mem.mpr
  refine ⟨gu_nonneg a, gu_mass hn a, ?_⟩
  intro m
  rw [cum_gu]
  unfold linePoint
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  constructor
  · norm_num
    exact (div_le_div_iff_of_pos_right hn').2 (by exact_mod_cast hlo m.val)
  · change (gp a m.val : ℝ) / (n:ℝ) ≤
      ((0:ℝ) + (1-0) * ((gp p m.val + 1:ℕ):ℝ) / (n:ℝ))
    norm_num
    exact (div_le_div_iff_of_pos_right hn').2 (by exact_mod_cast hhi m.val)

end
end FamiliesProof

namespace FamiliesProof
open Set
open scoped BigOperators
noncomputable section
variable {d n : ℕ}
/-- Convex closure of a cube-chain in coefficient space is contained in the same
closed chamber. The missing combinatorial triangulation can thus reason only about
finite chains of `GridVert`; no analytic closure argument remains. -/
lemma convexHull_gu_chain_same_chamber (hn : 0 < n) (p : GridVert d n)
    (A : Finset (GridVert d n))
    (hlo : ∀ a ∈ A, gpLe p a) (hhi : ∀ a ∈ A, gpNear a p) :
    convexHull ℝ ((fun a => gu a) '' (A : Set (GridVert d n))) ⊆
      coeffChamber d n (fun m : Fin (d+1) => gp p m.val) := by
  -- Linear inequalities defining a chamber are convex.
  refine convexHull_min ?_ (convex_coeffChamber d n _)
  intro x hx
  rcases hx with ⟨a, ha, rfl⟩
  exact gu_chain_same_chamber hn p (hlo a ha) (hhi a ha)
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridOrder.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridFaceHull.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {d n : ℕ}
/-- Evaluation along fixed vertices, as a linear map on coefficient vectors. -/
def gridEvalLinear (v : Fin d → E) : (Fin d → ℝ) →ₗ[ℝ] E :=
{ toFun := simplexEval v
  map_add' := by intro a b; simp [simplexEval, Finset.sum_add_distrib, add_smul]
  map_smul' := by
    intro c a
    change (∑ i : Fin d, (c * a i) • v i) = c • ∑ i : Fin d, a i • v i
    simp_rw [mul_smul]
    exact (Finset.smul_sum).symm }

lemma chainHull_eval_in_chamber (hn : 0 < n) (v : Fin d → E)
    (hv : AffineIndependent ℝ v)
    (p : GridVert d n) (A : Finset (GridVert d n))
    (hlo : ∀ a ∈ A, gpLe p a) (hhi : ∀ a ∈ A, gpNear a p)
    {x : E}
    (hx : x ∈ convexHull ℝ ((simplexEval v ∘ gu) '' (A : Set (GridVert d n)))) :
    ∃ hx0 : x ∈ convexHull ℝ (Set.range v),
      (⟨x,hx0⟩ : {y : E // y ∈ convexHull ℝ (Set.range v)}) ∈
        geoChamber v hv n (fun m : Fin (d+1) => gp p m.val) := by
  classical
  let B : Set (Fin d → ℝ) := coeffChamber d n (fun m : Fin (d+1) => gp p m.val)
  let L : (Fin d → ℝ) →ₗ[ℝ] E := gridEvalLinear v
  have hcB : Convex ℝ B := convex_coeffChamber d n _
  have hlift : x ∈ L '' B := by
    have him : Convex ℝ (L '' B) := hcB.linear_image L
    refine (convexHull_min ?_ him) hx
    intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    refine ⟨gu a, gu_chain_same_chamber hn p (hlo a ha) (hhi a ha), ?_⟩
    rfl
  rcases hlift with ⟨u, hu, ex⟩
  have hu0 : u ∈ coeffSimplex d :=
    (coeffChamber_mem.mp hu).1 |> fun h => ⟨h,(coeffChamber_mem.mp hu).2.1⟩
  have hx0 : x ∈ convexHull ℝ (Set.range v) := by
    -- evaluation of any simplex coefficients lies in its hull
    rw [← ex]
    exact simplexEval_mem_hull v hu0.1 hu0.2
  refine ⟨hx0, ?_⟩
  apply (mem_geoChamber).2
  -- simplex coordinates on an independent face are unique.
  have eqU : (((simplexHomeo v hv).symm (⟨x,hx0⟩ :
      {y:E // y ∈ convexHull ℝ (Set.range v)}) :
        {u : Fin d → ℝ // u ∈ coeffSimplex d}) : Fin d → ℝ) = u := by
    apply simplexEval_eq hv
      (((simplexHomeo v hv).symm
        (⟨x,hx0⟩ : {y:E // y ∈ convexHull ℝ (Set.range v)})).property.2) hu0.2
    -- inverse homeomorphism evaluates back to the point
    have z := (simplexHomeo v hv).apply_symm_apply
      (⟨x,hx0⟩ : {y:E // y ∈ convexHull ℝ (Set.range v)})
    
    have z' := congrArg Subtype.val z
    change simplexEval v
      (((simplexHomeo v hv).symm
        (⟨x,hx0⟩ : {y:E // y ∈ convexHull ℝ (Set.range v)})).1) = _
    have ex' : simplexEval v u = x := ex
    change simplexEval v
      (((simplexHomeo v hv).symm
        (⟨x,hx0⟩ : {y:E // y ∈ convexHull ℝ (Set.range v)})).1) = x at z'
    exact z'.trans ex'.symm
  change (((simplexHomeo v hv).symm
      (⟨x,hx0⟩ : {y:E // y ∈ convexHull ℝ (Set.range v)}) :
        {u : Fin d → ℝ // u ∈ coeffSimplex d}) : Fin d → ℝ) ∈ _
  rw [eqU]
  exact hu
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridFaceHull.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridMin.lean
section
open Set
open scoped BigOperators
namespace FamiliesProof
noncomputable section
variable {d n : ℕ}
/- In a finite prefix-chain, there is a least element.  Keeping the witness
rather than choosing a linear order on `GridVert` makes this usable when
several ordered faces meet. -/
lemma chain_has_least (A : Finset (GridVert d n)) (hA : A.Nonempty)
    (hcmp : ∀ a ∈ A, ∀ b ∈ A, gpLe a b ∨ gpLe b a) :
    ∃ p ∈ A, ∀ a ∈ A, gpLe p a := by
  classical
  induction A using Finset.induction with
  | empty => simp at hA
  | @insert a A ha ih =>
    by_cases hE : A.Nonempty
    · have hc : ∀ x ∈ A, ∀ y ∈ A, gpLe x y ∨ gpLe y x := by
        intro x hx y hy
        exact hcmp x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
      obtain ⟨p,hp,hpl⟩ := ih hE hc
      have hp' : p ∈ insert a A := Finset.mem_insert_of_mem hp
      rcases hcmp a (Finset.mem_insert_self ..) p hp' with ap|pa
      · refine ⟨a,Finset.mem_insert_self .., ?_⟩
        intro x hx
        rcases (Finset.mem_insert.mp hx) with h|h
        · subst x
          exact gpLe_rfl a
        · exact gpLe_trans ap (hpl x h)
      · refine ⟨p,hp', ?_⟩
        intro x hx
        rcases (Finset.mem_insert.mp hx) with h|h
        · simpa [h] using pa
        · exact hpl x h
    · have hAE : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
      subst A
      refine ⟨a, by simp, ?_⟩
      intro x hx
      simp at hx
      simpa [hx] using (gpLe_rfl a)

lemma chain_has_cube_anchor (A : Finset (GridVert d n)) (hA : A.Nonempty)
    (hcmp : ∀ a ∈ A, ∀ b ∈ A, gpLe a b ∨ gpLe b a)
    (hclose : ∀ a ∈ A, ∀ b ∈ A, gpNear a b) :
    ∃ p ∈ A, (∀ a ∈ A, gpLe p a) ∧ (∀ a ∈ A, gpNear a p) := by
  obtain ⟨p,hp,hlo⟩ := chain_has_least A hA hcmp
  exact ⟨p,hp,hlo,fun a ha => hclose a ha p hp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Every simplex all of whose lattice vertices form a chain in a single
prefix cube is cut by one of the Morrison--Walker chambers.  The input no
longer singles out an anchor; a least chain vertex is the canonical choice. -/
lemma chainHull_eval_exists_chamber (hn : 0 < n) (v : Fin d → E)
    (hv : AffineIndependent ℝ v)
    (A : Finset (GridVert d n)) (hA : A.Nonempty)
    (hcmp : ∀ a ∈ A, ∀ b ∈ A, gpLe a b ∨ gpLe b a)
    (hclose : ∀ a ∈ A, ∀ b ∈ A, gpNear a b) :
    ∃ p : GridVert d n,
      ∀ x ∈ convexHull ℝ ((simplexEval v ∘ gu) '' (A : Set (GridVert d n))),
      ∃ hx0 : x ∈ convexHull ℝ (Set.range v),
        (⟨x,hx0⟩ : {y : E // y ∈ convexHull ℝ (Set.range v)}) ∈
          geoChamber v hv n (fun m : Fin (d+1) => gp p m.val) := by
  obtain ⟨p,hp,hlo,hhi⟩ := chain_has_cube_anchor A hA hcmp hclose
  refine ⟨p, ?_⟩
  intro x hx
  exact chainHull_eval_in_chamber hn v hv p A hlo hhi hx
end
end FamiliesProof

namespace FamiliesProof
noncomputable section
open Set
variable {d n : ℕ}
lemma gp_exists_ne {a b : GridVert d n} (h : a ≠ b) :
    ∃ m : ℕ, m < d ∧ gp a m ≠ gp b m := by
  classical
  by_contra! H
  apply h
  apply gp_inj
  intro m
  by_cases hm : m < d
  · exact H m hm
  · rw [gp_large a (Nat.le_of_not_gt hm), gp_large b (Nat.le_of_not_gt hm)]

lemma gp_lt_some {a b : GridVert d n} (h : gpLe a b) (hne : a ≠ b) :
    ∃ m : ℕ, m < d ∧ gp a m < gp b m := by
  obtain ⟨m,hm,hneq⟩ := gp_exists_ne hne
  exact ⟨m,hm,lt_of_le_of_ne (h m) hneq⟩

/-- The threshold support of a lattice point in a prefix cube. -/
def toggles (p a : GridVert d n) : Fin d → Prop := fun i => gp p i.val < gp a i.val
instance (p a : GridVert d n) : DecidablePred (toggles p a) := Classical.decPred _
def toggleSet (p a : GridVert d n) : Finset (Fin d) := Finset.univ.filter (toggles p a)
@[simp] lemma mem_toggleSet (p a : GridVert d n) (i : Fin d) :
    i ∈ toggleSet p a ↔ gp p i.val < gp a i.val := by simp [toggleSet,toggles]

lemma gp_eq_or_succ {p a : GridVert d n}
    (hlo : gpLe p a) (hi : gpNear a p) (m : ℕ) :
    gp a m = gp p m ∨ gp a m = gp p m + 1 := by
  have l := hlo m
  have u := hi m
  omega

lemma gp_toggle_val {p a : GridVert d n}
    (hlo : gpLe p a) (hi : gpNear a p) (i : Fin d) :
    gp a i.val = gp p i.val + (if i ∈ toggleSet p a then 1 else 0) := by
  rcases gp_eq_or_succ hlo hi i.val with h|h
  · have hnot : i ∉ toggleSet p a := by intro C; rw [mem_toggleSet] at C; omega
    simpa [hnot] using h
  · have hin : i ∈ toggleSet p a := by rw [mem_toggleSet]; omega
    simp [hin, h]

lemma toggleSet_mono {p a b : GridVert d n}
    (loA : gpLe p a) (hiA : gpNear a p)
    (loB : gpLe p b) (hiB : gpNear b p)
    (hab : gpLe a b) :
    toggleSet p a ⊆ toggleSet p b := by
  intro i hi
  rw [mem_toggleSet] at hi ⊢
  exact lt_of_lt_of_le hi (hab i.val)
/- Toggles remember the whole lattice point once the anchor is fixed. -/
lemma toggleSet_inj (p : GridVert d n)
    {a b : GridVert d n}
    (loA : gpLe p a) (hiA : gpNear a p)
    (loB : gpLe p b) (hiB : gpNear b p)
    (h : toggleSet p a = toggleSet p b) : a = b := by
  apply gp_inj
  intro m
  by_cases hm : m < d
  · let i : Fin d := ⟨m,hm⟩
    have A := gp_toggle_val loA hiA i
    have B := gp_toggle_val loB hiB i
    rw [h] at A
    exact A.trans B.symm
  · rw [gp_large a (Nat.le_of_not_gt hm), gp_large b (Nat.le_of_not_gt hm)]
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open Set
variable {d n : ℕ}
def clipGP (n x : ℕ) : ℕ := min x (n-1)
lemma clipGP_lt (hn : 0 < n) (x : ℕ) : clipGP n x < n := by unfold clipGP; omega
lemma chain_clip_bounds (hn : 0 < n) (p a : GridVert d n)
    (lo : gpLe p a) (hi : gpNear a p) (m : ℕ) :
    clipGP n (gp p m) ≤ gp a m ∧ gp a m ≤ clipGP n (gp p m) + 1 := by
  have za := gp_le_all a m
  have h := lo m
  have h' := hi m
  unfold clipGP
  omega
lemma gu_chain_same_chamber_clip (hn : 0 < n) (p : GridVert d n)
    {a : GridVert d n} (lo : gpLe p a) (hi : gpNear a p) :
    gu a ∈ coeffChamber d n (fun m : Fin (d+1) => clipGP n (gp p m.val)) := by
  apply coeffChamber_mem.mpr
  refine ⟨gu_nonneg a, gu_mass hn a, ?_⟩
  intro m
  rw [cum_gu]
  unfold linePoint
  have hb := chain_clip_bounds hn p a lo hi m.val
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  constructor
  · norm_num
    exact (div_le_div_iff_of_pos_right hn').2 (by exact_mod_cast hb.1)
  · change (gp a m.val : ℝ) / (n:ℝ) ≤
      ((0:ℝ) + (1-0) * ((clipGP n (gp p m.val) + 1:ℕ):ℝ) / (n:ℝ))
    norm_num
    exact (div_le_div_iff_of_pos_right hn').2 (by exact_mod_cast hb.2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def chamberBin (hn : 0 < n) (p : GridVert d n) : Fin (d+1) → Fin n :=
  fun m => ⟨clipGP n (gp p m.val), clipGP_lt hn _⟩
lemma chainHull_eval_in_chamber_clip (hn : 0 < n) (v : Fin d → E)
    (hv : AffineIndependent ℝ v)
    (p : GridVert d n) (A : Finset (GridVert d n))
    (hlo : ∀ a ∈ A, gpLe p a) (hhi : ∀ a ∈ A, gpNear a p)
    {x : E}
    (hx : x ∈ convexHull ℝ ((simplexEval v ∘ gu) '' (A : Set (GridVert d n)))) :
    ∃ hx0 : x ∈ convexHull ℝ (Set.range v),
      (⟨x,hx0⟩ : {y : E // y ∈ convexHull ℝ (Set.range v)}) ∈
        geoChamber v hv n (fun m => ((chamberBin hn p) m).val) := by
  classical
  let B : Set (Fin d → ℝ) := coeffChamber d n (fun m : Fin (d+1) => clipGP n (gp p m.val))
  let L : (Fin d → ℝ) →ₗ[ℝ] E := gridEvalLinear v
  have hcB : Convex ℝ B := convex_coeffChamber d n _
  have hlift : x ∈ L '' B := by
    have him : Convex ℝ (L '' B) := hcB.linear_image L
    refine (convexHull_min ?_ him) hx
    intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    refine ⟨gu a, gu_chain_same_chamber_clip hn p (hlo a ha) (hhi a ha), ?_⟩
    rfl
  rcases hlift with ⟨u, hu, ex⟩
  have hu0 : u ∈ coeffSimplex d :=
    (coeffChamber_mem.mp hu).1 |> fun h => ⟨h,(coeffChamber_mem.mp hu).2.1⟩
  have hx0 : x ∈ convexHull ℝ (Set.range v) := by
    rw [← ex]
    exact simplexEval_mem_hull v hu0.1 hu0.2
  refine ⟨hx0, ?_⟩
  apply (mem_geoChamber).2
  have eqU : (((simplexHomeo v hv).symm (⟨x,hx0⟩ :
      {y:E // y ∈ convexHull ℝ (Set.range v)}) :
        {u : Fin d → ℝ // u ∈ coeffSimplex d}) : Fin d → ℝ) = u := by
    apply simplexEval_eq hv
      (((simplexHomeo v hv).symm
        (⟨x,hx0⟩ : {y:E // y ∈ convexHull ℝ (Set.range v)})).property.2) hu0.2
    have z := (simplexHomeo v hv).apply_symm_apply
      (⟨x,hx0⟩ : {y:E // y ∈ convexHull ℝ (Set.range v)})
    have z' := congrArg Subtype.val z
    change simplexEval v
      (((simplexHomeo v hv).symm
        (⟨x,hx0⟩ : {y:E // y ∈ convexHull ℝ (Set.range v)})).1) = _
    have ex' : simplexEval v u = x := ex
    change simplexEval v
      (((simplexHomeo v hv).symm
        (⟨x,hx0⟩ : {y:E // y ∈ convexHull ℝ (Set.range v)})).1) = x at z'
    exact z'.trans ex'.symm
  change (((simplexHomeo v hv).symm
      (⟨x,hx0⟩ : {y:E // y ∈ convexHull ℝ (Set.range v)}) :
        {u : Fin d → ℝ // u ∈ coeffSimplex d}) : Fin d → ℝ) ∈ _
  rw [eqU]
  exact hu
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open Set
variable {d n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma chainHull_eval_exists_chamberBin (hn : 0 < n) (v : Fin d → E)
    (hv : AffineIndependent ℝ v)
    (A : Finset (GridVert d n)) (hA : A.Nonempty)
    (hcmp : ∀ a ∈ A, ∀ b ∈ A, gpLe a b ∨ gpLe b a)
    (hclose : ∀ a ∈ A, ∀ b ∈ A, gpNear a b) :
    ∃ b : Fin (d+1) → Fin n,
      ∀ x ∈ convexHull ℝ ((simplexEval v ∘ gu) '' (A : Set (GridVert d n))),
      ∃ hx0 : x ∈ convexHull ℝ (Set.range v),
        (⟨x,hx0⟩ : {y : E // y ∈ convexHull ℝ (Set.range v)}) ∈
          geoChamber v hv n (fun m => (b m).val) := by
  obtain ⟨p,hp,hlo,hhi⟩ := chain_has_cube_anchor A hA hcmp hclose
  refine ⟨chamberBin hn p, ?_⟩
  intro x hx
  exact chainHull_eval_in_chamber_clip hn v hv p A hlo hhi hx
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridMin.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridReduction.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Reduction of the geometric chamber refinement to the genuinely finite grid
triangulation. A `D` contained in the convex hull of a prefix-chain of lattice
vertices of a single pulling face automatically lies in one of the closed
cumulative-coordinate chambers of that face.  The chamber index is valued in
`Fin n`, not in `ℕ`: at an upper-boundary vertex the least prefix can equal `n`;
`chainHull_eval_exists_chamberBin` clips the anchor instead of trying to coerce it.
This is the reusable half of the outstanding Freudenthal PL construction. -/
lemma gridChain_facets_are_chambers
    (s : Finset E) (n : ℕ) (hn : 0 < n)
    (M : Geometry.SimplicialComplex ℝ E)
    (hfac : ∀ D ∈ M.facets,
      ∃ (t : Finset E)
        (ht : lexFace s t)
        (hne : t.Nonempty)
        (A : Finset (GridVert (facePos s t).card n)),
        A.Nonempty ∧
        (∀ a ∈ A, ∀ b ∈ A, gpLe a b ∨ gpLe b a) ∧
        (∀ a ∈ A, ∀ b ∈ A, gpNear a b) ∧
        ∀ x : E, x ∈ convexHull ℝ (D : Set E) →
          x ∈ convexHull ℝ
            ((simplexEval (inheritedFace s t) ∘ gu) ''
              (A : Set (GridVert (facePos s t).card n)))) :
    ∀ D ∈ M.facets,
      ∃ (t : Finset E)
        (ht : lexFace s t)
        (hne : t.Nonempty)
        (b : Fin ((facePos s t).card+1) → Fin n),
        ∀ x : E,
          x ∈ convexHull ℝ (D : Set E) →
            ∃ hx : x ∈ convexHull ℝ (Set.range (inheritedFace s t)),
              (⟨x,hx⟩ : {z : E // z ∈ convexHull ℝ
                (Set.range (inheritedFace s t))}) ∈
                geoChamber (inheritedFace s t)
                  (inheritedFace_indep ht) n (fun m => (b m).val) := by
  classical
  intro D hD
  obtain ⟨t, ht, hne, A, hA, hcmp, hnear, hsub⟩ := hfac D hD
  obtain ⟨b, hb⟩ := chainHull_eval_exists_chamberBin hn
    (inheritedFace s t) (inheritedFace_indep ht) A hA hcmp hnear
  refine ⟨t, ht, hne, b, ?_⟩
  intro x hx
  exact hb x (hsub x hx)

/-- Packaging version: once only the finite grid-chain complex is supplied,
the analytic chamber-refinement statement follows without any gluing of local
charts. The pointwise cover by chambers alone is not enough; the `chain`
field asks exactly for the finite geometric complex left in the PL step. -/
lemma gridChain_refinement_reduction
    (s : Finset E) (n : ℕ) (hn : 0 < n)
    (hex : ∃ M : Geometry.SimplicialComplex ℝ E,
      M.faces.Finite ∧
      M.space = convexHull ℝ (s : Set E) ∧
      ∀ D ∈ M.facets,
        ∃ (t : Finset E)
          (ht : lexFace s t)
          (hne : t.Nonempty)
          (A : Finset (GridVert (facePos s t).card n)),
          A.Nonempty ∧
          (∀ a ∈ A, ∀ b ∈ A, gpLe a b ∨ gpLe b a) ∧
          (∀ a ∈ A, ∀ b ∈ A, gpNear a b) ∧
          ∀ x : E, x ∈ convexHull ℝ (D : Set E) →
            x ∈ convexHull ℝ
              ((simplexEval (inheritedFace s t) ∘ gu) ''
                (A : Set (GridVert (facePos s t).card n)))) :
    ∃ M : Geometry.SimplicialComplex ℝ E,
      M.faces.Finite ∧
      M.space = convexHull ℝ (s : Set E) ∧
      ∀ D ∈ M.facets,
        ∃ (t : Finset E)
          (ht : lexFace s t)
          (hne : t.Nonempty)
          (b : Fin ((facePos s t).card+1) → Fin n),
          ∀ x : E,
            x ∈ convexHull ℝ (D : Set E) →
              ∃ hx : x ∈ convexHull ℝ (Set.range (inheritedFace s t)),
                (⟨x,hx⟩ : {z : E // z ∈ convexHull ℝ
                  (Set.range (inheritedFace s t))}) ∈
                  geoChamber (inheritedFace s t)
                    (inheritedFace_indep ht) n (fun m => (b m).val) := by
  classical
  obtain ⟨M,hMf,hMs,hchain⟩ := hex
  exact ⟨M,hMf,hMs, gridChain_facets_are_chambers s n hn M hchain⟩
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/ContinuousRefine.lean
section

open Set
open scoped BigOperators Topology
open Geometry
namespace FamiliesProof
noncomputable section
variable {k n q : ℕ}
/- Given a chamber refinement of the pulling complex, all the analytic/cartesian
   work needed for the continuous sparse-copies branch is formal.  The copies
   are literally `globalCopy` for the global pasted coefficient section.  This
   lemma is stated at the ambient hull level so it does not depend on the
   challenge's `Subdivision`/`closedCell` structures. -/
lemma hullCopies_of_chamberRefine
    (s : Finset (Fin k → ℝ)) (hspos : 0 < s.card)
    (hq : 0 < q) (hn : 0 < n)
    (hex : ∃ M : SimplicialComplex ℝ (Fin k → ℝ),
      M.faces.Finite ∧ M.space = convexHull ℝ (s : Set (Fin k → ℝ)) ∧
      ∀ D ∈ M.facets,
        ∃ (t : Finset (Fin k → ℝ))
          (ht : lexFace s t)
          (hne : t.Nonempty)
          (b : Fin ((facePos s t).card+1) → Fin (q*n)),
          ∀ x : Fin k → ℝ,
            x ∈ convexHull ℝ (D : Set (Fin k → ℝ)) →
              ∃ hx : x ∈ convexHull ℝ (Set.range (inheritedFace s t)),
                (⟨x,hx⟩ : {z : Fin k → ℝ // z ∈ convexHull ℝ
                  (Set.range (inheritedFace s t))}) ∈
                  geoChamber (inheritedFace s t)
                    (inheritedFace_indep ht) (q*n) (fun m => (b m).val)) :
    let H := {x : Fin k → ℝ // x ∈ convexHull ℝ (s : Set (Fin k → ℝ))}
    ∃ (φ : Fin n → C(H,H)) (M : SimplicialComplex ℝ (Fin k → ℝ)),
      M.faces.Finite ∧ M.space = convexHull ℝ (s : Set (Fin k → ℝ)) ∧
      (∀ D ∈ M.facets,
        ∃ A : Finset (Fin n), A.card ≤ k ∧
          ∀ j, j ∉ A → ∀ p p' : H,
            (p : Fin k → ℝ) ∈ convexHull ℝ (D : Set (Fin k → ℝ)) →
            (p' : Fin k → ℝ) ∈ convexHull ℝ (D : Set (Fin k → ℝ)) →
              φ j p = φ j p') ∧
      (∀ (B : Set (Fin k → ℝ)), Convex ℝ B →
        IsExtreme ℝ (convexHull ℝ (s : Set (Fin k → ℝ))) B →
          ∀ (j : Fin n) (p : H), (p : Fin k → ℝ) ∈ B →
            ((φ j p : H) : Fin k → ℝ) ∈ B) := by
  classical
  dsimp
  -- global coefficient section on the whole finite hull
  rcases exists_globalCoeff s with ⟨cg,cpos,csum,ceval,cface⟩
  obtain ⟨M,hMf,hMs,hfaces⟩ := hex
  let φ : Fin n → C({x : Fin k → ℝ // x ∈ convexHull ℝ (s : Set (Fin k → ℝ))},
        {x : Fin k → ℝ // x ∈ convexHull ℝ (s : Set (Fin k → ℝ))}) := fun r =>
    globalCopyMap s hspos cg cpos csum q n hq hn r
  refine ⟨φ, M, hMf, hMs, ?_, ?_⟩
  · intro D hD
    rcases hfaces D hD with ⟨t,ht,htne,b,hDb⟩
    let A : Finset (Fin n) := chamberColours hn b
    have htpos : 0 < (facePos s t).card := facePos_card_pos ht.1 htne
    refine ⟨A, ?_, ?_⟩
    · have hA := card_chamberColours_plus_one htpos hn b
      -- a pulling face in `Fin k` contains at most k+1 vertices
      have hdim : (facePos s t).card ≤ k+1 := by
        have hi := inheritedFace_indep ht
        have hv := AffineIndependent.card_le_finrank_succ hi
        simp at hv
        have hle := Submodule.finrank_le
          (vectorSpan ℝ (Set.range (inheritedFace s t)))
        have heq : Module.finrank ℝ (Fin k → ℝ) = k := by
          simpa using (Module.finrank_fin_fun ℝ (n:=k))
        omega
      dsimp [A]
      omega
    · intro j hj p p' hp hp'
      have hpx := hDb (p : Fin k → ℝ) hp
      have hpy := hDb (p' : Fin k → ℝ) hp'
      rcases hpx with ⟨hxt,hxc⟩
      rcases hpy with ⟨hyt,hyc⟩
      have hxt' : (p : Fin k → ℝ) ∈ convexHull ℝ (t : Set (Fin k → ℝ)) := by
        simpa [range_inheritedFace ht.1] using hxt
      have hyt' : (p' : Fin k → ℝ) ∈ convexHull ℝ (t : Set (Fin k → ℝ)) := by
        simpa [range_inheritedFace ht.1] using hyt
      -- on this pulling face the global formula is exactly the inherited
      -- cyclic map (the global coefficients restrict to local simplex
      -- coordinates).  Its chamber constancy is already closed-chamber
      -- constancy, so no relative interiors or choices are involved.
      apply Subtype.ext
      change globalCopy s cg q n hq hn j p =
        globalCopy s cg q n hq hn j p'
      rw [globalCopy_eq_inheritedFace s t ht cg
            (by
              intro x hx
              simpa using
                (cface (⟨t, by
                  rw [lexComplex_faces]
                  exact ⟨ht, htne⟩⟩) x hx))
            q n hq hn htpos j p hxt']
      rw [globalCopy_eq_inheritedFace s t ht cg
            (by
              intro x hx
              simpa using
                (cface (⟨t, by
                  rw [lexComplex_faces]
                  exact ⟨ht, htne⟩⟩) x hx))
            q n hq hn htpos j p' hyt']
      exact congrArg Subtype.val
        (simplexCycMap_const_not_mem htpos hq hn
          (inheritedFace s t) (inheritedFace_indep ht) j b hj hxc hyc)
  · intro B hBc hExt j p hp
    -- preservation on every genuine extreme face is pointwise; nothing
    -- about chambers is needed.
    exact globalCopy_mem_extreme s hspos cg cpos csum ceval q n
      hq hn j hBc hExt p hp
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/ContinuousRefine.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridEval.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {d n : ℕ}
/-- Embedding of the barycentric grid of an independent face into ambient space.
The mass-one hypothesis on `gu` is what turns affine independence into
injectivity. Using `map` instead of `image` preserves cardinalities of chain
supports. -/
noncomputable def gridEvalEmb (hn : 0 < n) (v : Fin d → E)
    (hv : AffineIndependent ℝ v) : GridVert d n ↪ E :=
{ toFun := simplexEval v ∘ gu
  inj' := by
    intro a b e
    apply gu_inj hn
    exact simplexEval_eq hv (gu_mass hn a) (gu_mass hn b) e }
@[simp] lemma gridEvalEmb_apply (hn : 0 < n) (v : Fin d → E)
    (hv : AffineIndependent ℝ v) (a : GridVert d n) :
    gridEvalEmb hn v hv a = simplexEval v (gu a) := rfl

lemma coe_gridEvalEmb_map (hn : 0 < n) (v : Fin d → E)
    (hv : AffineIndependent ℝ v) (A : Finset (GridVert d n)) :
    ((A.map (gridEvalEmb hn v hv) : Finset E) : Set E) =
      (simplexEval v ∘ gu) '' (A : Set (GridVert d n)) := by
  simpa [gridEvalEmb] using (Finset.coe_map (gridEvalEmb hn v hv) A)
lemma card_gridEvalEmb_map (hn : 0 < n) (v : Fin d → E)
    (hv : AffineIndependent ℝ v) (A : Finset (GridVert d n)) :
    (A.map (gridEvalEmb hn v hv)).card = A.card := by simpa using (Finset.card_map (gridEvalEmb hn v hv) A)

/-- A named, local finite family of grid-chain supports. `close` is demanded in
both directions via the universally quantified form; hence one cube works on
all prefixes, including at a zero coordinate. Empty chains are included to
make erasing/subsetting convenient when `ofErase` is used. -/
def coeffChains (d n : ℕ) : Set (Finset (GridVert d n)) :=
  {A | (∀ a ∈ A, ∀ b ∈ A, gpLe a b ∨ gpLe b a) ∧
       (∀ a ∈ A, ∀ b ∈ A, gpNear a b)}
lemma coeffChains_empty (d n : ℕ) :
    (∅ : Finset (GridVert d n)) ∈ coeffChains d n := by
  simp [coeffChains]
lemma coeffChains_down {A B : Finset (GridVert d n)}
    (hA : A ∈ coeffChains d n) (hB : B ⊆ A) : B ∈ coeffChains d n := by
  constructor
  · intro a ha b hb; exact hA.1 a (hB ha) b (hB hb)
  · intro a ha b hb; exact hA.2 a (hB ha) b (hB hb)
lemma coeffChains_finite (d n : ℕ) : (coeffChains d n).Finite := by
  classical
  exact Set.toFinite _

lemma gridHull_subset_face (hn : 0 < n) (v : Fin d → E)
    (hv : AffineIndependent ℝ v) (A : Finset (GridVert d n)) :
    convexHull ℝ ((A.map (gridEvalEmb hn v hv) : Finset E) : Set E) ⊆
      convexHull ℝ (Set.range v) := by
  rw [coe_gridEvalEmb_map hn v hv A]
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro x hx
  rcases hx with ⟨a,ha,rfl⟩
  exact simplexEval_mem_hull v (gu_nonneg a) (gu_mass hn a)

/- Prefix comparisons are preserved on every sub-support. Packaging the
witnesses now avoids reopening the chain minima inside a geometric facet. -/
lemma mapped_coeffChain_chamber (hn : 0 < n) (v : Fin d → E)
    (hv : AffineIndependent ℝ v)
    (A : Finset (GridVert d n)) (hA : A ∈ coeffChains d n)
    (hne : A.Nonempty) :
    ∃ b : Fin (d+1) → Fin n,
      ∀ x ∈ convexHull ℝ ((A.map (gridEvalEmb hn v hv) : Finset E) : Set E),
        ∃ hx : x ∈ convexHull ℝ (Set.range v),
          (⟨x,hx⟩ : {y : E // y ∈ convexHull ℝ (Set.range v)}) ∈
            geoChamber v hv n (fun m => (b m).val) := by
  have hc : ∀ a ∈ A, ∀ b ∈ A, gpLe a b ∨ gpLe b a := hA.1
  have hh : ∀ a ∈ A, ∀ b ∈ A, gpNear a b := hA.2
  obtain ⟨b,hb⟩ := chainHull_eval_exists_chamberBin hn v hv A hne hc hh
  refine ⟨b, ?_⟩
  intro x hx
  exact hb x (by
    rw [coe_gridEvalEmb_map hn v hv A] at hx
    exact hx)
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridEval.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridAbstract.lean
section
open Set
open scoped BigOperators Topology
open Geometry
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- `ofErase` reduction of the Freudenthal step. It records *exactly* which
purely finite facts remain about prefix chains. In particular facets need not
be selected or oriented: if every nonempty support in a lower chain family
comes from one pulling face then any maximal support does as well. This
constructor tends to avoid a second, accidental, maximality condition. -/
lemma gridSupports_makeComplex
    (s : Finset E) (n : ℕ) (hn : 0 < n)
    (G : Set (Finset E))
    (Gfin : G.Finite)
    (Glow : IsLowerSet G)
    (Gind : ∀ D ∈ G, AffineIndependent ℝ ((↑) : D → E))
    (Ginter : ∀ D ∈ G, ∀ B ∈ G,
      convexHull ℝ (D : Set E) ∩ convexHull ℝ (B : Set E) ⊆
        convexHull ℝ ((D : Set E) ∩ (B : Set E)))
    (Gcover : ∀ x ∈ convexHull ℝ (s : Set E),
      ∃ D ∈ G, D.Nonempty ∧ x ∈ convexHull ℝ (D : Set E))
    (Ginside : ∀ D ∈ G,
      convexHull ℝ (D : Set E) ⊆ convexHull ℝ (s : Set E))
    (Gchain : ∀ D ∈ G, D.Nonempty →
      ∃ (t : Finset E) (ht : lexFace s t) (hte : t.Nonempty)
        (A : Finset (GridVert (facePos s t).card n)),
        A.Nonempty ∧ A ∈ coeffChains _ _ ∧
        D = A.map (gridEvalEmb hn
          (inheritedFace s t) (inheritedFace_indep ht))) :
    ∃ M : SimplicialComplex ℝ E,
      M.faces.Finite ∧
      M.space = convexHull ℝ (s : Set E) ∧
      ∀ D ∈ M.facets,
        ∃ (t : Finset E) (ht : lexFace s t) (hte : t.Nonempty)
          (A : Finset (GridVert (facePos s t).card n)),
          A.Nonempty ∧
          (∀ a ∈ A, ∀ b ∈ A, gpLe a b ∨ gpLe b a) ∧
          (∀ a ∈ A, ∀ b ∈ A, gpNear a b) ∧
          ∀ x : E, x ∈ convexHull ℝ (D : Set E) →
            x ∈ convexHull ℝ
             ((simplexEval (inheritedFace s t) ∘ gu) ''
               (A : Set (GridVert (facePos s t).card n))) := by
  classical
  let M : SimplicialComplex ℝ E :=
    SimplicialComplex.ofErase G Gind Glow (by
      intro D hD B hB
      simpa only [Finset.coe_inter] using Ginter D hD B hB)
  have face_eq : M.faces = G \ {∅} := by
    dsimp [M]
    rw [SimplicialComplex.ofErase_faces]
  have finM : M.faces.Finite := by
    rw [face_eq]
    exact Gfin.subset Set.diff_subset
  refine ⟨M, finM, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      rcases (SimplicialComplex.mem_space_iff).1 hx with ⟨D,hD,hxD⟩
      apply Ginside D ?_ hxD
      have hD' : D ∈ (G \ {∅}) := by simpa [face_eq] using hD
      exact hD'.1
    · intro x hx
      rcases Gcover x hx with ⟨D,hD,hne,hxD⟩
      apply (SimplicialComplex.mem_space_iff).2
      have hnot : D ∉ ({∅} : Set (Finset E)) := by
        intro C
        have : D = ∅ := by simpa using C
        exact (Finset.nonempty_iff_ne_empty.mp hne) this
      refine ⟨D, ?_, hxD⟩
      rw [face_eq]
      exact ⟨hD,hnot⟩
  · intro D hD
    have hf : D ∈ M.faces := hD.1
    have hf' : D ∈ G \ ({∅} : Set (Finset E)) := by
      rw [← face_eq]; exact hf
    have dne : D.Nonempty := by
      have no : D ≠ ∅ := by intro e; exact hf'.2 (by simpa [e])
      exact Finset.nonempty_iff_ne_empty.mpr no
    obtain ⟨t,ht,hte,A,hA,hAc,eq⟩ := Gchain D hf'.1 dne
    refine ⟨t,ht,hte,A,hA,hAc.1,hAc.2, ?_⟩
    intro x hx
    rw [eq, coe_gridEvalEmb_map hn (inheritedFace s t)
      (inheritedFace_indep ht) A] at hx
    exact hx
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridAbstract.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridConstruct.lean
section
open Set
open scoped BigOperators Topology
open Geometry
namespace FamiliesProof
noncomputable section
variable {d n : ℕ}
-- cumulative coordinate of a weighted relation
lemma cum_sum_gu (hn : 0 < n) (U : Finset (GridVert d n))
    (w : GridVert d n → ℝ)
    (h : ∑ a ∈ U, w a • gu a = (0 : Fin d → ℝ)) (m:ℕ) :
    ∑ a ∈ U, w a * (gp a m : ℝ) = 0 := by
  classical
  have eq := congrArg (fun u : Fin d → ℝ => cumCoord d u m) h
  simp [cumCoord] at eq
  have eq' : ∑ a ∈ U, w a * (((gp a m : ℝ) / (n : ℝ))) = 0 := by
    calc
      _ = ∑ a ∈ U, ∑ i ∈ (Finset.univ.filter (fun i : Fin d => i.val < m)),
          w a * gu a i := by
            apply Finset.sum_congr rfl; intro a ha
            rw [← Finset.mul_sum]
            congr 1
            exact (cum_gu a m).symm
      _ = ∑ i ∈ (Finset.univ.filter (fun i : Fin d => i.val < m)),
          ∑ a ∈ U, w a * gu a i := by
            -- commute double sums
            exact Finset.sum_comm
      _ = 0 := eq
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (∑ a ∈ U, w a * (gp a m : ℝ)) =
        (n:ℝ) * (∑ a ∈ U, w a * (((gp a m : ℝ)/(n:ℝ)))) := by
          -- distribute n
          -- each term cancels denominator
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a ha
          -- denominator cancellation
          field_simp
    _ = 0 := by rw [eq']; simp

lemma chain_weights_zero (hn : 0 < n) (U : Finset (GridVert d n))
    (hc : ∀ a ∈ U, ∀ b ∈ U, gpLe a b ∨ gpLe b a)
    (hnear : ∀ a ∈ U, ∀ b ∈ U, gpNear a b)
    (w : GridVert d n → ℝ)
    (hs : ∑ a ∈ U, w a = 0)
    (hv : ∑ a ∈ U, w a • gu a = (0 : Fin d → ℝ)) :
    ∀ a ∈ U, w a = 0 := by
  classical
  induction U using Finset.strongInduction with
  | H U ih =>
    by_cases hU : U.Nonempty
    · obtain ⟨p,hp,hpl⟩ := chain_has_least U hU hc
      by_cases hrest : (U.erase p).Nonempty
      · have subr : U.erase p ⊂ U := Finset.erase_ssubset hp
        have hcr : ∀ a ∈ U.erase p, ∀ b ∈ U.erase p, gpLe a b ∨ gpLe b a := by
          intro a ha b hb; exact hc a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
        obtain ⟨q,hq,hql⟩ := chain_has_least (U.erase p) hrest hcr
        have hpq : gpLe p q := hpl q (Finset.mem_of_mem_erase hq)
        have hpne : p ≠ q := by
          intro e; subst q; exact (Finset.mem_erase.mp hq).1 rfl
        obtain ⟨m,hm,hm_lt⟩ := gp_lt_some hpq hpne
        -- every other prefix has the same value at this coordinate
        have same : ∀ a ∈ U.erase p, gp a m = gp q m := by
          intro a ha
          have qa := hql a ha
          have nearap := hnear a (Finset.mem_of_mem_erase ha) p hp m
          have hpqlt : gp p m < gp q m := hm_lt
          have qle : gp q m ≤ gp a m := qa m
          have qup : gp q m ≤ gp p m + 1 := hnear q (Finset.mem_of_mem_erase hq) p hp m
          have up : gp a m ≤ gp p m + 1 := nearap
          omega
        have scalar := cum_sum_gu hn U w hv m
        have splitS := Finset.sum_erase_add U (fun a => w a) hp
        have splitV := Finset.sum_erase_add U (fun a => w a * (gp a m : ℝ)) hp
        have restconst : ∑ a ∈ U.erase p, w a * (gp a m : ℝ) =
            (∑ a ∈ U.erase p, w a) * (gp q m : ℝ) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          rw [same a ha]
        rw [restconst] at splitV
        rw [hs] at splitS
        rw [scalar] at splitV
        have wp : w p = 0 := by
          have ltval : (gp p m : ℝ) < (gp q m : ℝ) := by
            exact_mod_cast hm_lt
          nlinarith
        have hs' : ∑ a ∈ U.erase p, w a = 0 := by
          linarith
        have hv' : ∑ a ∈ U.erase p, w a • gu a = (0 : Fin d → ℝ) := by
          have eq := Finset.sum_erase_add U (fun a => w a • gu a) hp
          rw [hv, wp] at eq
          simpa using eq
        have hr := ih (U.erase p) subr hcr
          (fun a ha b hb => hnear a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb))
          hs' hv'
        intro a ha
        by_cases e : a = p
        · simpa [e] using wp
        · exact hr a (Finset.mem_erase.mpr ⟨e,ha⟩)
      · have er : U.erase p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrest
        have up : U = {p} := by
          exact ((Finset.erase_eq_empty_iff U p).1 er |>.resolve_left (by
            intro e; rw [e] at hp; simp at hp))
        intro a ha
        have ep : a = p := by simpa [up] using ha
        subst a
        simpa [up] using hs
    · intro a ha
      exact (hU ⟨a,ha⟩).elim


lemma coeffChains_affineIndependent (hn : 0 < n)
    (A : Finset (GridVert d n)) (hA : A ∈ coeffChains d n) :
    AffineIndependent ℝ (fun a : A => gu (a : GridVert d n)) := by
  classical
  rw [affineIndependent_iff]
  intro U w hs hv i hi
  let emb : A ↪ GridVert d n := Function.Embedding.subtype _
  let V : Finset (GridVert d n) := U.map emb
  let W : GridVert d n → ℝ := fun a => if ha : a ∈ A then w ⟨a,ha⟩ else 0
  have hs' : ∑ a ∈ V, W a = 0 := by
    simpa [V, W, emb] using hs
  have hv' : ∑ a ∈ V, W a • gu a = (0 : Fin d → ℝ) := by
    simpa [V, W, emb] using hv
  have hsub : V ⊆ A := by
    intro a ha
    rcases Finset.mem_map.mp ha with ⟨a',ha',rfl⟩
    exact a'.property
  have hcv : ∀ a ∈ V, ∀ b ∈ V, gpLe a b ∨ gpLe b a := by
    intro a ha b hb
    exact hA.1 a (hsub ha) b (hsub hb)
  have hnv : ∀ a ∈ V, ∀ b ∈ V, gpNear a b := by
    intro a ha b hb
    exact hA.2 a (hsub ha) b (hsub hb)
  have zz := chain_weights_zero hn V hcv hnv W hs' hv'
  have him : ((i : A) : GridVert d n) ∈ V := by
    exact Finset.mem_map.mpr ⟨i,hi,rfl⟩
  simpa [W] using zz (i : GridVert d n) him

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma mappedChain_affineIndependent (hn : 0 < n)
    (v : Fin d → E) (hv : AffineIndependent ℝ v)
    (A : Finset (GridVert d n)) (hA : A ∈ coeffChains d n) :
    AffineIndependent ℝ
      ((↑) : (A.map (gridEvalEmb hn v hv)) → E) := by
  classical
  rw [affineIndependent_iff]
  intro U w hs hvec i hi
  -- pull the finite support back across the embedding
  let emb := gridEvalEmb hn v hv
  let inv : (A.map emb) → A := fun x =>
    ⟨Classical.choose (Finset.mem_map.mp x.property),
      (Classical.choose_spec (Finset.mem_map.mp x.property)).1⟩
  have inv_eq (x : (A.map emb)) :
      emb ((inv x : A) : GridVert d n) = (x : E) :=
    (Classical.choose_spec (Finset.mem_map.mp x.property)).2
  have inv_inj : Function.Injective inv := by
    intro x y h
    apply Subtype.ext
    have := congrArg (fun z : A => emb (z : GridVert d n)) h
    simpa [inv_eq] using this
  let eInv : (A.map emb) ↪ A := ⟨inv, inv_inj⟩
  let U' : Finset A := U.map eInv
  let w' : A → ℝ := fun a => if ha : a ∈ U' then
      w (⟨emb (a : GridVert d n), by
          exact Finset.mem_map.mpr ⟨(a : GridVert d n), a.property, rfl⟩⟩ : (A.map emb)) else 0
  have w_inv : ∀ (x : (A.map emb)), x ∈ U → w' (eInv x) = w x := by
    intro x hx
    have him : eInv x ∈ U' := Finset.mem_map.mpr ⟨x,hx,rfl⟩
    dsimp [w']
    simp [him]
    congr 1
    apply Subtype.ext
    exact inv_eq x
  have hs' : ∑ a ∈ U', w' a = 0 := by
    rw [show U' = U.map eInv from rfl]
    rw [Finset.sum_map]
    calc
      _ = ∑ x ∈ U, w x := by apply Finset.sum_congr rfl; intro j hj; exact w_inv j hj
      _ = 0 := hs
  -- linear combination in coefficient space vanishes, by injectivity on mass-one
  -- evaluate its coordinates using independence of v and the zero total mass
  have coeffzero : ∑ a ∈ U', w' a • gu (a : GridVert d n) =
        (0 : Fin d → ℝ) := by
    -- affine independence of `v`: enough that evaluation is zero and sum is zero.
    have mapped : ∑ a ∈ U', w' a • simplexEval v (gu (a : GridVert d n)) =
          (0:E) := by
      rw [show U' = U.map eInv from rfl]
      rw [Finset.sum_map]
      calc
        _ = ∑ x ∈ U, w x • (x:E) := by
          apply Finset.sum_congr rfl; intro j hj
          rw [w_inv j hj]
          congr 1
          exact inv_eq j
        _ = 0 := by simpa using hvec
    have evzero : ∑ j : Fin d,
        ( (∑ a ∈ U', w' a • gu (a : GridVert d n)) j) • v j = 0 := by
      rw [← mapped]
      -- distribute evaluation across finite sums
      simp [simplexEval, Finset.smul_sum, mul_smul, Finset.sum_smul]
      -- swap sums
      rw [Finset.sum_comm]

    -- linear independence at mass zero
    have masszero : ∑ j : Fin d,
        ((∑ a ∈ U', w' a • gu (a : GridVert d n)) j) = 0 := by
      -- each grid vector has mass one
      calc
        _ = ∑ a ∈ U', w' a * (∑ j : Fin d, gu (a : GridVert d n) j) := by
          simp [Finset.mul_sum]
          rw [Finset.sum_comm]
        _ = ∑ a ∈ U', w' a := by
          apply Finset.sum_congr rfl; intro a ha
          rw [gu_mass hn]
          ring
        _ = 0 := hs'

    -- uniqueness characterization of independent family
    have z := (affineIndependent_iff.mp hv)
      (Finset.univ : Finset (Fin d))
      (fun j => ((∑ a ∈ U', w' a • gu (a : GridVert d n)) j))
      (by simpa using masszero) (by simpa using evzero)
    funext j
    have := z j (Finset.mem_univ j)
    simpa using this
  have aff := (affineIndependent_iff.mp (coeffChains_affineIndependent hn A hA))
      U' w' hs' coeffzero
  -- use corresponding inverse index
  let ai : A := inv i
  have hai : ai ∈ U' := by
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
  have wi := aff ai hai
  simpa [w', hai, ai, inv_eq] using wi

end
end FamiliesProof
namespace FamiliesProof
open Set Geometry
open scoped BigOperators Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- finite lower family of mapped prefix cubes.  Proving its cover and
intersection is the remaining combinatorial triangulation step. -/
def mappedChains (s : Finset E) (n : ℕ) (hn : 0 < n) : Set (Finset E) :=
  {D | ∃ (t : Finset E) (ht : lexFace s t)
       (A : Finset (GridVert (facePos s t).card n)),
       A ∈ coeffChains _ _ ∧
       D = A.map (gridEvalEmb hn (inheritedFace s t)
         (inheritedFace_indep ht))}
lemma mappedChains_finite (s : Finset E) (n:ℕ) (hn:0<n) :
    (mappedChains s n hn).Finite := by
  classical
  let T : Set (Finset E) := lexFaces s
  let V : (t : Finset E) → Set (Finset E) := fun t =>
    if ht : lexFace s t then
      (fun A : Finset (GridVert (facePos s t).card n) =>
        A.map (gridEvalEmb hn (inheritedFace s t) (inheritedFace_indep ht))) ''
          coeffChains (facePos s t).card n
    else ∅
  have vf : ∀ t ∈ T, (V t).Finite := by
    intro t ht
    dsimp [V]
    split_ifs
    · exact Set.Finite.image _ (coeffChains_finite _ _)
    · exact Set.finite_empty
  have fin := Set.Finite.biUnion (lexFaces_finite s) vf
  apply fin.subset
  intro D hD
  rcases hD with ⟨t,ht,A,hA,eq⟩
  apply Set.mem_iUnion_of_mem t
  apply Set.mem_iUnion_of_mem (show t ∈ T from ht)
  dsimp [V]
  split_ifs with h
  exact ⟨A,hA,eq.symm⟩
lemma mappedChains_lower (s : Finset E) (n:ℕ) (hn:0<n) :
    IsLowerSet (mappedChains s n hn) := by
  classical
  intro D D' sub hD
  rcases hD with ⟨t,ht,A,hA,rfl⟩
  let emb := gridEvalEmb hn (inheritedFace s t) (inheritedFace_indep ht)
  let B : Finset (GridVert (facePos s t).card n) :=
    A.filter (fun a => emb a ∈ D')
  refine ⟨t,ht,B, coeffChains_down hA ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_filter.mp ha).1
  · ext x
    constructor
    · intro hx
      have hbig : x ∈ A.map emb := sub hx
      rcases Finset.mem_map.mp hbig with ⟨a,ha,ex⟩
      exact Finset.mem_map.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, by simpa [ex] using hx⟩, ex⟩
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨a, ha, ex⟩
      have hd := (Finset.mem_filter.mp ha).2
      simpa [emb, ex] using hd
lemma mappedChains_ind (s : Finset E) (n : ℕ) (hn:0<n) :
    ∀ D ∈ mappedChains s n hn,
       AffineIndependent ℝ ((↑) : D → E) := by
  classical
  intro D hD
  rcases hD with ⟨t,ht,A,hA,rfl⟩
  exact mappedChain_affineIndependent hn _ _ A hA
lemma mappedChains_inside (s : Finset E) (n : ℕ) (hn:0<n) :
    ∀ D ∈ mappedChains s n hn,
      convexHull ℝ (D:Set E) ⊆ convexHull ℝ (s:Set E) := by
  classical
  intro D hD
  rcases hD with ⟨t,ht,A,hA,rfl⟩
  exact (gridHull_subset_face hn (inheritedFace s t) (inheritedFace_indep ht) A) |>.trans
    (by rw [range_inheritedFace ht.1]; exact convexHull_mono (by exact_mod_cast ht.1))

lemma gridVert_card_pos {d n : ℕ} (hn : 0 < n) (a : GridVert d n) : 0 < d := by
  classical
  by_contra! h
  have hd : d = 0 := Nat.eq_zero_of_not_pos (by omega : ¬ 0 < d)
  have ha := a.property
  subst d
  have ha' : (∑ i : Fin 0, (a.1 i).val) = n := a.property
  simp at ha'
  omega
lemma mappedChains_chain (s : Finset E) (n : ℕ) (hn:0<n) :
    ∀ D ∈ mappedChains s n hn, D.Nonempty →
      ∃ (t : Finset E) (ht : lexFace s t) (hte : t.Nonempty)
        (A : Finset (GridVert (facePos s t).card n)),
        A.Nonempty ∧ A ∈ coeffChains _ _ ∧
        D = A.map (gridEvalEmb hn (inheritedFace s t)
          (inheritedFace_indep ht)) := by
  classical
  intro D hD ne
  rcases hD with ⟨t,ht,A,hA,eq⟩
  have Ane : A.Nonempty := by
    rw [eq] at ne
    obtain ⟨x,hx⟩ := ne
    rcases Finset.mem_map.mp hx with ⟨a,ha,e⟩
    exact ⟨a,ha⟩
  have pos : 0 < (facePos s t).card :=
    gridVert_card_pos hn (Classical.choose Ane)
  have tc : t.card = (facePos s t).card := (facePos_card ht.1).symm
  have tne : t.Nonempty := Finset.card_pos.mp (by simpa [tc] using pos)
  exact ⟨t,ht,tne,A,Ane,hA,eq⟩
end
end FamiliesProof
namespace FamiliesProof
open Set Geometry
open scoped BigOperators Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The exact two geometric assertions missing for the canonical finite
Freudenthal candidate.  All finiteness, lowering, independence, and chamber
fields are discharged here once these are supplied. -/
lemma mappedChains_reduction (s : Finset E) (n:ℕ) (hn:0<n)
    (inter : ∀ D ∈ mappedChains s n hn, ∀ B ∈ mappedChains s n hn,
      convexHull ℝ (D:Set E) ∩ convexHull ℝ (B:Set E) ⊆
        convexHull ℝ ((D:Set E) ∩ (B:Set E)))
    (cover : ∀ x ∈ convexHull ℝ (s:Set E),
      ∃ D ∈ mappedChains s n hn, D.Nonempty ∧ x ∈ convexHull ℝ (D:Set E)) :
    ∃ M : SimplicialComplex ℝ E,
      M.faces.Finite ∧
      M.space = convexHull ℝ (s : Set E) ∧
      ∀ D ∈ M.facets,
        ∃ (t : Finset E)
          (ht : lexFace s t)
          (hne : t.Nonempty)
          (A : Finset (GridVert (facePos s t).card n)),
          A.Nonempty ∧
          (∀ a ∈ A, ∀ b ∈ A, gpLe a b ∨ gpLe b a) ∧
          (∀ a ∈ A, ∀ b ∈ A, gpNear a b) ∧
          ∀ x : E, x ∈ convexHull ℝ (D : Set E) →
            x ∈ convexHull ℝ
              ((simplexEval (inheritedFace s t) ∘ gu) ''
                (A : Set (GridVert (facePos s t).card n))) := by
  classical
  exact gridSupports_makeComplex s n hn (mappedChains s n hn)
    (mappedChains_finite s n hn)
    (mappedChains_lower s n hn)
    (mappedChains_ind s n hn)
    inter cover (mappedChains_inside s n hn)
    (mappedChains_chain s n hn)
end
end FamiliesProof
namespace FamiliesProof
open Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- all denominator points along every pulling face are themselves supports of
our candidate. Useful for reducing coverage to the coefficient rounding lemma. -/
lemma singleton_grid_mem (s : Finset E) (n:ℕ) (hn:0<n)
    {t : Finset E} (ht : lexFace s t)
    (a : GridVert (facePos s t).card n) :
    {gridEvalEmb hn (inheritedFace s t) (inheritedFace_indep ht) a}
      ∈ mappedChains s n hn := by
  classical
  let A : Finset (GridVert (facePos s t).card n) := {a}
  refine ⟨t,ht,A, ?_, ?_⟩
  · constructor
    · intro x hx y hy
      have xa : x = a := Finset.mem_singleton.mp hx
      have ya : y = a := Finset.mem_singleton.mp hy
      subst x; subst y
      exact Or.inl (gpLe_rfl a)
    · intro x hx y hy
      have xa : x = a := Finset.mem_singleton.mp hx
      have ya : y = a := Finset.mem_singleton.mp hy
      subst x; subst y
      intro m; exact Nat.le_add_right_of_le (le_rfl)
  · simp [A]
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridConstruct.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridInter.lean
section
open Set
open scoped BigOperators Topology
namespace FamiliesProof
attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {d n : ℕ}
/-- On one fixed independent pulling face, the only missing input for
intersection of mapped supports is the analogous coefficient statement.
This is useful since the coefficient problem is a cubical problem, with no
ambient vector space involved. -/
lemma gridSameFace_inter_of_coeff
    (hn : 0 < n) (v : Fin d → E) (hv : AffineIndependent ℝ v)
    (A B : Finset (GridVert d n))
    (hcoeff :
      convexHull ℝ (gu '' (A : Set (GridVert d n))) ∩
          convexHull ℝ (gu '' (B : Set (GridVert d n))) ⊆
        convexHull ℝ (gu '' ((↑(A ∩ B)) : Set (GridVert d n)))) :
    convexHull ℝ ((A.map (gridEvalEmb hn v hv) : Finset E) : Set E) ∩
        convexHull ℝ ((B.map (gridEvalEmb hn v hv) : Finset E) : Set E) ⊆
      convexHull ℝ (((A ∩ B).map (gridEvalEmb hn v hv) : Finset E) : Set E) := by
  classical
  let L : (Fin d → ℝ) →ₗ[ℝ] E := gridEvalLinear v
  have funL (u : Fin d → ℝ) : L u = simplexEval v u := rfl
  have coe (C : Finset (GridVert d n)) :
      ((C.map (gridEvalEmb hn v hv) : Finset E) : Set E) =
        L '' (gu '' (C : Set (GridVert d n))) := by
    rw [coe_gridEvalEmb_map hn v hv C]
    exact (Set.image_image L gu (C : Set (GridVert d n))).symm
  have lift (C : Finset (GridVert d n)) :
      convexHull ℝ ((C.map (gridEvalEmb hn v hv) : Finset E) : Set E) =
        L '' convexHull ℝ (gu '' (C : Set (GridVert d n))) := by
    rw [coe C]
    exact (L.image_convexHull _).symm
  have ins (C : Finset (GridVert d n)) :
      convexHull ℝ (gu '' (C : Set (GridVert d n))) ⊆ coeffSimplex d := by
    refine convexHull_min ?_ (convex_coeffSimplex d)
    intro u hu
    rcases hu with ⟨a,ha,rfl⟩
    exact gu_simplex hn a
  intro x hx
  rw [lift A] at hx
  rw [lift B] at hx
  rcases hx.1 with ⟨u,hu,eu⟩
  rcases hx.2 with ⟨w,hw,ew⟩
  have uw : u = w := by
    apply simplexEval_eq hv ((ins A) hu).2 ((ins B) hw).2
    simpa [funL] using eu.trans ew.symm
  subst w
  rw [lift (A ∩ B)]
  exact ⟨u, hcoeff ⟨hu,hw⟩, eu⟩
end
end FamiliesProof
namespace FamiliesProof
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable section
variable {d n : ℕ}
/-- If the two coefficient supports live in a single chain, intersection is
just the affine-independent simplex axiom. The delicate part of the
Freudenthal argument is to show that the positive vertices in two
representations indeed form such a chain. -/
lemma coeffChains_inter_of_union
    (hn : 0 < n) (A B : Finset (GridVert d n))
    (hU : A ∪ B ∈ coeffChains d n) :
    convexHull ℝ (gu '' (A : Set (GridVert d n))) ∩
          convexHull ℝ (gu '' (B : Set (GridVert d n))) ⊆
      convexHull ℝ (gu '' ((↑(A ∩ B)) : Set (GridVert d n))) := by
  classical
  let emb : GridVert d n ↪ (Fin d → ℝ) := ⟨gu, gu_inj hn⟩
  let U : Finset (GridVert d n) := A ∪ B
  let T : Finset (Fin d → ℝ) := U.map emb
  let T₁ : Finset (Fin d → ℝ) := A.map emb
  let T₂ : Finset (Fin d → ℝ) := B.map emb
  have hAi : T₁ ⊆ T := Finset.map_subset_map.mpr (Finset.subset_union_left)
  have hBi : T₂ ⊆ T := Finset.map_subset_map.mpr (Finset.subset_union_right)
  let toU : U → T := fun a => ⟨emb a, Finset.mem_map.mpr ⟨a,a.property,rfl⟩⟩
  have toi : Function.Injective toU := by
    intro a b e
    exact Subtype.ext (emb.injective (congrArg Subtype.val e))
  have tos : Function.Surjective toU := by
    intro z
    rcases Finset.mem_map.mp z.property with ⟨a,ha,eq⟩
    refine ⟨⟨a,ha⟩, Subtype.ext eq⟩
  let e : T ≃ U := (Equiv.ofBijective toU ⟨toi,tos⟩).symm
  have hval (z : T) : gu (e z : GridVert d n) = (z : Fin d → ℝ) := by
    have h := (Equiv.ofBijective toU ⟨toi,tos⟩).apply_symm_apply z
    exact congrArg Subtype.val h
  have hi0 : AffineIndependent ℝ (fun a : U => gu (a : GridVert d n)) :=
    coeffChains_affineIndependent hn U hU
  have hi1 := hi0.comp_embedding e.toEmbedding
  have hi : AffineIndependent ℝ ((↑) : T → (Fin d → ℝ)) := by
    have fun_eq : (fun a : U => gu (a : GridVert d n)) ∘ (e.toEmbedding : T → U) =
        ((↑) : T → (Fin d → ℝ)) := by
      funext z; exact hval z
    rw [fun_eq] at hi1
    exact hi1
  have H := hi.convexHull_inter hAi hBi
  have set1 : (T₁ : Set (Fin d → ℝ)) = gu '' (A : Set (GridVert d n)) := by
    exact Finset.coe_map emb A
  have set2 : (T₂ : Set (Fin d → ℝ)) = gu '' (B : Set (GridVert d n)) := by
    exact Finset.coe_map emb B
  have setI : ((T₁ : Set (Fin d → ℝ)) ∩ T₂) =
      gu '' ((↑(A ∩ B)) : Set (GridVert d n)) := by
    rw [← Finset.coe_inter]
    rw [← Finset.map_inter]
    exact Finset.coe_map emb (A ∩ B)
  rw [setI, set1, set2] at H
  exact fun _ h => H.symm ▸ h
end
end FamiliesProof
namespace FamiliesProof
open Set
attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Intersection for two mapped supports on the same pulling face reduces
literally to the coefficient lemma; `map_inter` keeps the common vertices.
-/
lemma mappedSameFace_inter_of_coeff
    (s t : Finset E) (ht : lexFace s t) (n : ℕ) (hn : 0 < n)
    (A B : Finset (GridVert (facePos s t).card n))
    (hcoeff :
      convexHull ℝ (gu '' (A : Set (GridVert (facePos s t).card n))) ∩
          convexHull ℝ (gu '' (B : Set (GridVert (facePos s t).card n))) ⊆
        convexHull ℝ (gu '' ((↑(A ∩ B)) :
            Set (GridVert (facePos s t).card n)))) :
    let emb := gridEvalEmb hn (inheritedFace s t) (inheritedFace_indep ht)
    convexHull ℝ ((A.map emb : Finset E) : Set E) ∩
      convexHull ℝ ((B.map emb : Finset E) : Set E) ⊆
        convexHull ℝ ((((A.map emb) ∩ (B.map emb) : Finset E)) : Set E) := by
  classical
  dsimp
  have h := gridSameFace_inter_of_coeff hn (inheritedFace s t)
        (inheritedFace_indep ht) A B hcoeff
  simpa [Finset.map_inter] using h
end
end FamiliesProof
namespace FamiliesProof
open Set
open scoped BigOperators
noncomputable section
variable {d n : ℕ}
/-- Extractable prefix means from an equality of weighted coefficient
vectors.  Prefix means are the ordering coordinates of a cube chain. -/
lemma sum_gp_eq_of_sum_gu
    {A B : Finset (GridVert d n)} {w z : GridVert d n → ℝ}
    (eqv : (∑ a ∈ A, w a • gu a) = (∑ b ∈ B, z b • gu b)) (m : ℕ) :
    (∑ a ∈ A, w a * ((gp a m : ℝ) / (n:ℝ))) =
      ∑ b ∈ B, z b * ((gp b m : ℝ) / (n:ℝ)) := by
  classical
  have h := congrArg (fun u : Fin d → ℝ => cumCoord d u m) eqv

  have conv (C : Finset (GridVert d n)) (f : GridVert d n → ℝ) :
      (∑ a ∈ C, f a * ((gp a m : ℝ)/(n:ℝ))) =
        ∑ i ∈ (Finset.univ.filter (fun i : Fin d => i.val < m)),
          ∑ a ∈ C, f a * gu a i := by
    calc
      _ = ∑ a ∈ C, ∑ i ∈ (Finset.univ.filter (fun i : Fin d => i.val < m)),
          f a * gu a i := by
            apply Finset.sum_congr rfl; intro a ha
            rw [← Finset.mul_sum]
            rw [← cum_gu]
            rfl
      _ = _ := Finset.sum_comm
  simpa [cumCoord, conv] using h
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridInter.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridRound.lean
section
open Set Geometry
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
/-- Partial sums telescope. The small version with natural differences is useful for
building lattice vertices from their prefix cuts. -/
lemma sum_range_succ_sub (p : ℕ → ℕ) (hmon : Monotone p) (r : ℕ) :
    (∑ i ∈ Finset.range r, (p (i+1) - p i)) = p r - p 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have h0 : p 0 ≤ p r := hmon (Nat.zero_le r)
    have h1 : p r ≤ p (r+1) := hmon (Nat.le_succ r)
    have hr : r.succ = r+1 := rfl
    --
    omega
/-- Build the barycentric denominator vector with prescribed cumulative integer
cuts. The input is naturally indexed by all naturals, but only `[0,d]` matters. -/
def gpOfCuts {d n : ℕ} (p : ℕ → ℕ) (hmon : Monotone p)
    (hz : p 0 = 0) (hend : p d = n) : GridVert d n := by
  let a : Fin d → Fin (n+1) := fun i =>
    ⟨p (i.val+1) - p i.val, by
      have hi : i.val + 1 ≤ d := i.isLt
      have hbd : p (i.val+1) ≤ n := hend ▸ hmon hi
      omega⟩
  refine ⟨a, ?_⟩
  -- forget the bounds and telescope
  change (∑ i : Fin d, (p (i.val+1) - p i.val)) = n
  change (∑ i : Fin d, (fun j : Fin d => p (j.val+1)-p j.val) i) = n
  simpa using ( (Fin.sum_univ_eq_sum_range (fun i => p (i+1)-p i) d).trans (sum_range_succ_sub p hmon d) |>.trans (by simp [hz, hend]))
@[simp] lemma gp_gpOfCuts {d n : ℕ} (p : ℕ → ℕ) (hmon : Monotone p)
    (hz : p 0 = 0) (hend : p d = n) {m : ℕ} (hm : m ≤ d) :
    gp (gpOfCuts p hmon hz hend) m = p m := by
  classical
  unfold gp
  have filt : (Finset.univ.filter (fun i : Fin d => i.val < m)).sum
      (fun i => ((gpOfCuts p hmon hz hend).1 i).val) =
      ∑ i ∈ Finset.range m, (p (i+1) - p i) := by
    classical
    let e : Fin m ↪ Fin d :=
      ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hm⟩,
       by
        intro x y h
        have hh : x.val = y.val := congrArg (fun z : Fin d => z.val) h
        exact Fin.ext hh⟩
    have heq : Finset.univ.filter (fun i : Fin d => i.val < m) =
        Finset.univ.map e := by
      ext i
      simp
      constructor
      · intro h
        refine ⟨⟨i.val, h⟩, ?_⟩
        apply Fin.ext
        rfl
      · rintro ⟨j, hj⟩
        have v : j.val = i.val := congrArg (fun z : Fin d => z.val) hj
        simpa [v] using j.isLt
    rw [heq, Finset.sum_map]
    exact Fin.sum_univ_eq_sum_range (fun i => p (i+1)-p i) m
  rw [filt, sum_range_succ_sub p hmon m, hz, Nat.sub_zero]
@[simp] lemma gp_gpOfCuts_large {d n : ℕ} (p : ℕ → ℕ) (hmon : Monotone p)
    (hz : p 0 = 0) (hend : p d = n) {m : ℕ} (hm : d ≤ m) :
    gp (gpOfCuts p hmon hz hend) m = n := gp_large _ hm

/-- Difference-at-most-one cuts produce the cubical condition. -/
lemma gpOfCuts_le {d n : ℕ} {p q : ℕ → ℕ}
    (hp : Monotone p) (hq : Monotone q)
    (pz : p 0 = 0) (qz : q 0 = 0)
    (pe : p d = n) (qe : q d = n)
    (h : ∀ m ≤ d, p m ≤ q m) :
    gpLe (gpOfCuts p hp pz pe) (gpOfCuts q hq qz qe) := by
  intro m
  by_cases hm : m ≤ d
  · simpa [gp_gpOfCuts p hp pz pe hm, gp_gpOfCuts q hq qz qe hm] using h m hm
  · have md : d ≤ m := le_of_not_ge hm
    simp [gp_gpOfCuts_large p hp pz pe md, gp_gpOfCuts_large q hq qz qe md]
lemma gpOfCuts_near {d n : ℕ} {p q : ℕ → ℕ}
    (hp : Monotone p) (hq : Monotone q)
    (pz : p 0 = 0) (qz : q 0 = 0)
    (pe : p d = n) (qe : q d = n)
    (h : ∀ m ≤ d, p m ≤ q m + 1) :
    gpNear (gpOfCuts p hp pz pe) (gpOfCuts q hq qz qe) := by
  intro m
  by_cases hm : m ≤ d
  · simpa [gp_gpOfCuts p hp pz pe hm, gp_gpOfCuts q hq qz qe hm] using h m hm
  · have md : d ≤ m := le_of_not_ge hm
    simp [gp_gpOfCuts_large p hp pz pe md, gp_gpOfCuts_large q hq qz qe md]
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridRound.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/ChainAverages.lean
section
open Set
open scoped BigOperators
namespace FamiliesProof
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
/-- A positive weighted average of integer levels is strictly below a strict bound
seen by one support point. Kept in this scalar form so order calculations for two
Freudenthal chains don't depend on embeddings of faces. -/
lemma weighted_lt_of_point {α : Type*} [DecidableEq α]
    (C : Finset α) (w : α → ℝ) (f : α → ℕ) (K : ℕ)
    (hw : ∀ a ∈ C, 0 < w a)
    (hbound : ∀ a ∈ C, f a ≤ K)
    {p : α} (hp : p ∈ C) (hlt : f p < K) :
    (∑ a ∈ C, w a * (f a : ℝ)) < (∑ a ∈ C, w a) * K := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_lt_sum
  · intro a ha
    have wc : 0 ≤ w a := le_of_lt (hw a ha)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbound a ha) wc
  · refine ⟨p, hp, ?_⟩
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hlt) (hw p hp)
lemma weighted_gt_of_point {α : Type*} [DecidableEq α]
    (C : Finset α) (w : α → ℝ) (f : α → ℕ) (K : ℕ)
    (hw : ∀ a ∈ C, 0 < w a)
    (hbound : ∀ a ∈ C, K ≤ f a)
    {p : α} (hp : p ∈ C) (hlt : K < f p) :
    (∑ a ∈ C, w a) * K < (∑ a ∈ C, w a * (f a : ℝ)) := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_lt_sum
  · intro a ha
    have wc : 0 ≤ w a := le_of_lt (hw a ha)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbound a ha) wc
  · refine ⟨p, hp, ?_⟩
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hlt) (hw p hp)
variable {d n : ℕ}
/-- Positive supports representing the same coefficient vector have prefix
values at distance at most one across the two chains. This is the cubical part
of intersection, before deciding a common total order. -/
lemma chain_support_cross_near
    {A B : Finset (GridVert d n)} {w z : GridVert d n → ℝ}
    (hAc : A ∈ coeffChains d n) (hBc : B ∈ coeffChains d n)
    (hw : ∀ a ∈ A, 0 < w a) (hz : ∀ b ∈ B, 0 < z b)
    (hw1 : ∑ a ∈ A, w a = 1) (hz1 : ∑ b ∈ B, z b = 1)
    (eqgp : ∀ m : ℕ,
      (∑ a ∈ A, w a * (gp a m : ℝ)) =
        ∑ b ∈ B, z b * (gp b m : ℝ)) :
    ∀ p ∈ A, ∀ q ∈ B, gpNear p q ∧ gpNear q p := by
  classical
  have near : ∀ (A B : Finset (GridVert d n)) (w z : GridVert d n → ℝ),
      A ∈ coeffChains d n → B ∈ coeffChains d n →
      (∀ a ∈ A, 0 < w a) → (∀ b ∈ B, 0 < z b) →
      (∑ a ∈ A, w a = 1) → (∑ b ∈ B, z b = 1) →
      (∀ m : ℕ, (∑ a ∈ A, w a * (gp a m : ℝ)) =
        ∑ b ∈ B, z b * (gp b m : ℝ)) →
      ∀ p ∈ A, ∀ q ∈ B, gpNear p q := by
    intro A B w z hAc hBc hw hz hw1 hz1 eqgp p hp q hq m
    have Ale (a : GridVert d n) (ha : a ∈ A) : gp a m ≤ gp p m + 1 :=
      hAc.2 a ha p hp m
    have Ble (b : GridVert d n) (hb : b ∈ B) : gp b m ≤ gp q m + 1 :=
      hBc.2 b hb q hq m
    have Ap : (∑ a ∈ A, w a * (gp a m : ℝ)) <
        (gp p m + 1 : ℕ) := by
      have t := weighted_lt_of_point A w (fun a => gp a m) (gp p m + 1)
        hw Ale hp (by omega)
      rw [hw1] at t
      norm_num at t ⊢
      exact t
    have Bp : (∑ b ∈ B, z b * (gp b m : ℝ)) <
        (gp q m + 1 : ℕ) := by
      have t := weighted_lt_of_point B z (fun b => gp b m) (gp q m + 1)
        hz Ble hq (by omega)
      rw [hz1] at t
      norm_num at t ⊢
      exact t
    have Age (a : GridVert d n) (ha : a ∈ A) :
        gp p m ≤ gp a m + 1 := hAc.2 p hp a ha m
    by_contra bad
    have hgap : gp q m + 1 < gp p m := by omega
    have A_lower (a : GridVert d n) (ha : a ∈ A) : gp p m - 1 ≤ gp a m := by
      have aa := Age a ha
      omega
    have hs : gp p m - 1 < gp p m := by omega
    have Astrict : (gp p m - 1 : ℕ) <
        (∑ a ∈ A, w a * (gp a m : ℝ)) := by
      have t := weighted_gt_of_point A w (fun a => gp a m) (gp p m - 1)
          hw A_lower hp hs
      rw [hw1] at t
      norm_num at t ⊢
      exact t
    rw [eqgp m] at Astrict
    have val : (gp p m - 1 : ℕ) < gp q m + 1 := by exact_mod_cast (lt_trans Astrict Bp)
    omega
  intro p hp q hq
  exact ⟨near A B w z hAc hBc hw hz hw1 hz1 eqgp p hp q hq,
    near B A z w hBc hAc hz hw hz1 hw1 (fun m => (eqgp m).symm) q hq p hp⟩
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/ChainAverages.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridRestrict.lean
section
open Set
open scoped BigOperators
namespace FamiliesProof
attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable section

/-- The barycentric grid on a sublist, inserted with zero entries into a list. -/
def gridZeroExtend {a b n : ℕ} (e : Fin a ↪ Fin b) (p : GridVert a n) : GridVert b n := by
  classical
  let f : Fin b → Fin (n+1) := fun j =>
    if h : j ∈ Set.range e then p.1 (Classical.choose h) else (0 : Fin (n+1))
  have im (i : Fin a) : f (e i) = p.1 i := by
    dsimp [f]
    have h : e i ∈ Set.range e := ⟨i,rfl⟩
    rw [dif_pos h]
    exact congrArg p.1 (e.injective (Classical.choose_spec h))
  have off (j : Fin b) (h : j ∉ Set.range e) : (f j).val = 0 := by
    dsimp [f]
    rw [dif_neg h]
    rfl
  refine ⟨f, ?_⟩
  -- Sum over the image; entries outside are zero (this proof also works when
  -- the small ordinal is empty).
  let S : Finset (Fin b) := Finset.univ.map e
  calc
    (∑ j : Fin b, (f j).val) = ∑ j ∈ S, (f j).val := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hn'
      have hnot : j ∉ Set.range e := by
        intro h; rcases h with ⟨i,rfl⟩
        exact hn' (by simp [S])
      simp [off j hnot]
    _ = ∑ i : Fin a, (f (e i)).val := by simp [S]
    _ = ∑ i : Fin a, (p.1 i).val := by simp [im]
    _ = n := p.property

@[simp] lemma gridZeroExtend_image {a b n : ℕ} (e : Fin a ↪ Fin b)
    (p : GridVert a n) (i : Fin a) :
    (gridZeroExtend e p).1 (e i) = p.1 i := by
  classical
  unfold gridZeroExtend
  dsimp
  have h : e i ∈ Set.range e := ⟨i,rfl⟩
  rw [dif_pos h]
  exact congrArg p.1 (e.injective (Classical.choose_spec h))

lemma gridZeroExtend_off {a b n : ℕ} (e : Fin a ↪ Fin b)
    (p : GridVert a n) (j : Fin b) (h : j ∉ Set.range e) :
    ((gridZeroExtend e p).1 j).val = 0 := by
  classical
  unfold gridZeroExtend
  dsimp
  rw [dif_neg h]
  rfl
lemma gridZeroExtend_off_fin {a b n : ℕ} (e : Fin a ↪ Fin b)
    (p : GridVert a n) (j : Fin b) (h : j ∉ Set.range e) :
    (gridZeroExtend e p).1 j = 0 := by
  apply Fin.ext
  exact gridZeroExtend_off e p j h

lemma gu_gridZeroExtend {a b n : ℕ} (e : Fin a ↪ Fin b)
    (p : GridVert a n) :
    gu (gridZeroExtend e p) = zeroExtend e (gu p) := by
  classical
  funext j
  by_cases h : j ∈ Set.range e
  · rcases h with ⟨i,rfl⟩
    simp [gu, gridZeroExtend_image]
  · simp [gu, zeroExtend, h, gridZeroExtend_off e p j h]

/-- Distinct grid vertices stay distinct after insertion of zero coordinates. -/
lemma gridZeroExtend_injective {a b n : ℕ} (e : Fin a ↪ Fin b) :
    Function.Injective (gridZeroExtend (n:=n) e) := by
  intro p q h
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : GridVert b n => z.1 (e i)) h
  simpa using hi

def gridZeroEmb {a b n : ℕ} (e : Fin a ↪ Fin b) : GridVert a n ↪ GridVert b n :=
  ⟨gridZeroExtend e, gridZeroExtend_injective e⟩

@[simp] lemma gridZeroEmb_apply {a b n : ℕ} (e : Fin a ↪ Fin b)
    (p : GridVert a n) : gridZeroEmb (n:=n) e p = gridZeroExtend e p := rfl

/-- A grid point of the large list is on the subface precisely when all
its other coordinates vanish.  This is stronger than a statement about
real coordinates: it identifies the unique *grid vertex* on the face. -/
lemma gridZeroExtend_exists_unique {a b n : ℕ} (e : Fin a ↪ Fin b)
    (p : GridVert b n)
    (hz : ∀ j : Fin b, j ∉ Set.range e → gu p j = 0) :
    ∃! q : GridVert a n, gridZeroExtend e q = p := by
  classical
  have hz' (j : Fin b) (h : j ∉ Set.range e) : (p.1 j).val = 0 := by
    have hh := hz j h
    by_cases hn : n = 0
    · subst n
      have bound := (p.1 j).isLt
      simp at bound ⊢
    · dsimp [gu] at hh
      have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
      have z : ((p.1 j).val : ℝ) = 0 := (div_eq_zero_iff).mp hh |>.resolve_right hn'
      exact_mod_cast z
  let qf : Fin a → Fin (n+1) := fun i => p.1 (e i)
  have sumq : (∑ i : Fin a, (qf i).val) = n := by
    let S : Finset (Fin b) := Finset.univ.map e
    have hsum : (∑ j : Fin b, (p.1 j).val) = ∑ i : Fin a, (p.1 (e i)).val := by
      calc
        (∑ j : Fin b, (p.1 j).val) = ∑ j ∈ S, (p.1 j).val := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j hj hn'
          have hnot : j ∉ Set.range e := by
            intro h; rcases h with ⟨i,rfl⟩
            exact hn' (by simp [S])
          simp [hz' j hnot]
        _ = _ := by simp [S]
    simpa [qf, p.property] using hsum.symm
  let q : GridVert a n := ⟨qf, sumq⟩
  have qp : gridZeroExtend e q = p := by
    apply Subtype.ext
    funext j
    by_cases h : j ∈ Set.range e
    · rcases h with ⟨i,rfl⟩
      simp [q, qf]
    · exact Fin.ext (by simpa [gridZeroExtend_off e q j h] using (hz' j h).symm)
  refine ⟨q, qp, ?_⟩
  intro r hr
  exact gridZeroExtend_injective e (hr.trans qp.symm)

lemma gu_face_iff {a b n : ℕ} (hn : 0 < n) (e : Fin a ↪ Fin b)
    (p : GridVert b n) :
    (∀ j : Fin b, j ∉ Set.range e → gu p j = 0) ↔
      ∃! q : GridVert a n, gu p = zeroExtend e (gu q) := by
  classical
  constructor
  · intro h
    rcases gridZeroExtend_exists_unique e p h with ⟨q,hq,_⟩
    refine ⟨q, ?_, ?_⟩
    · change gu p = zeroExtend e (gu q)
      rw [← gu_gridZeroExtend e q, hq]
    · intro r hr
      -- equality of real coordinates is injective for n>0
      have z : gu (gridZeroExtend e r) = gu p := by
        rw [gu_gridZeroExtend e r, ← hr]
      exact gridZeroExtend_injective e (gu_inj hn (z.trans (congrArg gu hq.symm)))
  · rintro ⟨q,hq,uq⟩ j hj
    rw [hq]
    exact zeroExtend_not_mem e _ hj

/-- Cumulative grid prefixes on a subface: ambient cuts see the rank of the
cut in the smaller list. -/
lemma gp_gridZeroExtend_rank {a b n : ℕ} (hn : 0 < n)
    (e : Fin a ↪ Fin b) (he : StrictMono e) (p : GridVert a n) (t : ℕ) :
    gp (gridZeroExtend e p) t = gp p (faceRank e t) := by
  have h : ((gp (gridZeroExtend e p) t : ℕ) : ℝ) / (n : ℝ) =
      ((gp p (faceRank e t) : ℕ) : ℝ) / (n : ℝ) := by
    rw [← cum_gu, ← cum_gu, gu_gridZeroExtend,
        cumCoord_zeroExtend_rank e he]
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc : ((gp (gridZeroExtend e p) t : ℕ) : ℝ) =
      ((gp p (faceRank e t) : ℕ) : ℝ) := (div_left_inj' hn').mp h
  exact_mod_cast hc

/-- Every small prefix can be read at the ambient selected cut. -/
lemma gp_gridZeroExtend_at {a b n : ℕ} (hn : 0 < n)
    (e : Fin a ↪ Fin b) (he : StrictMono e) (p : GridVert a n) (i : Fin a) :
    gp (gridZeroExtend e p) (e i).val = gp p i.val := by
  have h : ((gp (gridZeroExtend e p) (e i).val : ℕ) : ℝ) / (n : ℝ) =
      ((gp p i.val : ℕ) : ℝ) / (n : ℝ) := by
    rw [← cum_gu, ← cum_gu, gu_gridZeroExtend, cumCoord_zeroExtend_at e he]
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc : ((gp (gridZeroExtend e p) (e i).val : ℕ) : ℝ) = ((gp p i.val : ℕ) : ℝ) :=
    (div_left_inj' hn').mp h
  exact_mod_cast hc

lemma gpLe_gridZeroExtend_iff {a b n : ℕ} (hn : 0 < n)
    (e : Fin a ↪ Fin b) (he : StrictMono e)
    (p q : GridVert a n) :
    gpLe (gridZeroExtend e p) (gridZeroExtend e q) ↔ gpLe p q := by
  constructor
  · intro h m
    by_cases hm : m < a
    · let i : Fin a := ⟨m, hm⟩
      simpa [gp_gridZeroExtend_at hn e he p i,
        gp_gridZeroExtend_at hn e he q i] using h (e i).val
    · have hm' : a ≤ m := by omega
      rw [gp_large p hm', gp_large q hm']
  · intro h t
    simpa [gp_gridZeroExtend_rank hn e he p t,
      gp_gridZeroExtend_rank hn e he q t] using h (faceRank e t)

lemma gpNear_gridZeroExtend_iff {a b n : ℕ} (hn : 0 < n)
    (e : Fin a ↪ Fin b) (he : StrictMono e)
    (p q : GridVert a n) :
    gpNear (gridZeroExtend e p) (gridZeroExtend e q) ↔ gpNear p q := by
  constructor
  · intro h m
    by_cases hm : m < a
    · let i : Fin a := ⟨m, hm⟩
      simpa [gp_gridZeroExtend_at hn e he p i,
        gp_gridZeroExtend_at hn e he q i] using h (e i).val
    · have hm' : a ≤ m := by omega
      rw [gp_large p hm', gp_large q hm']
      omega
  · intro h t
    simpa [gp_gridZeroExtend_rank hn e he p t,
      gp_gridZeroExtend_rank hn e he q t] using h (faceRank e t)

/-- Mapping an ordered face along its zero embedding preserves (and reflects)
our cubical-chain family exactly. -/
lemma coeffChains_map_gridZeroEmb_iff {a b n : ℕ} (hn : 0 < n)
    (e : Fin a ↪ Fin b) (he : StrictMono e)
    (A : Finset (GridVert a n)) :
    A.map (gridZeroEmb e) ∈ coeffChains b n ↔ A ∈ coeffChains a n := by
  classical
  constructor <;> intro h <;> constructor
  · intro p hp q hq
    have h' := h.1 (gridZeroExtend e p)
      (Finset.mem_map.mpr ⟨p,hp,rfl⟩) (gridZeroExtend e q)
      (Finset.mem_map.mpr ⟨q,hq,rfl⟩)
    rcases h' with z | z
    · exact Or.inl ((gpLe_gridZeroExtend_iff hn e he _ _).mp z)
    · exact Or.inr ((gpLe_gridZeroExtend_iff hn e he _ _).mp z)
  · intro p hp q hq
    have h' := h.2 (gridZeroExtend e p)
      (Finset.mem_map.mpr ⟨p,hp,rfl⟩) (gridZeroExtend e q)
      (Finset.mem_map.mpr ⟨q,hq,rfl⟩)
    exact (gpNear_gridZeroExtend_iff hn e he _ _).mp h'
  · intro p hp q hq
    obtain ⟨p0,hp0,ep⟩ := (Finset.mem_map).1 hp
    obtain ⟨q0,hq0,eq⟩ := (Finset.mem_map).1 hq
    subst p
    subst q
    rcases h.1 p0 hp0 q0 hq0 with z | z
    · exact Or.inl ((gpLe_gridZeroExtend_iff hn e he _ _).mpr z)
    · exact Or.inr ((gpLe_gridZeroExtend_iff hn e he _ _).mpr z)
  · intro p hp q hq
    obtain ⟨p0,hp0,ep⟩ := (Finset.mem_map).1 hp
    obtain ⟨q0,hq0,eq⟩ := (Finset.mem_map).1 hq
    subst p
    subst q
    exact (gpNear_gridZeroExtend_iff hn e he _ _).mpr (h.2 p0 hp0 q0 hq0)

/-- A chain all of whose active vertices are on a face is the zero-image of a
unique small chain. -/
lemma coeffChains_restrict_to_face {a b n : ℕ} (hn : 0 < n)
    (e : Fin a ↪ Fin b) (he : StrictMono e)
    (A : Finset (GridVert b n)) (hA : A ∈ coeffChains b n)
    (hz : ∀ p ∈ A, ∀ j : Fin b, j ∉ Set.range e → gu p j = 0) :
    ∃ B : Finset (GridVert a n),
      B ∈ coeffChains a n ∧ B.map (gridZeroEmb e) = A := by
  classical
  let B : Finset (GridVert a n) :=
    Finset.univ.filter (fun q => gridZeroExtend e q ∈ A)
  have eqA : B.map (gridZeroEmb e) = A := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨q,hq,rfl⟩
      exact (Finset.mem_filter.mp hq).2
    · intro hp
      rcases gridZeroExtend_exists_unique e p (hz p hp) with ⟨q,hq,_⟩
      subst p
      exact Finset.mem_map.mpr ⟨q, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hp⟩, rfl⟩
  refine ⟨B, ?_, eqA⟩
  apply (coeffChains_map_gridZeroEmb_iff hn e he B).mp
  rw [eqA]
  exact hA

section Evaluation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Embedded grid vertices do not depend on whether the ambient ordered face
or its subface is used. -/
lemma gridEvalEmb_zeroExtend {a b n : ℕ} (hn : 0 < n)
    (e : Fin a ↪ Fin b) (v : Fin b → E)
    (hv : AffineIndependent ℝ v) (p : GridVert a n) :
    gridEvalEmb hn v hv (gridZeroExtend e p) =
      gridEvalEmb hn (fun i => v (e i))
        (affineIndependent_comp_embedding e hv) p := by
  change simplexEval v (gu (gridZeroExtend e p)) =
    simplexEval (fun i => v (e i)) (gu p)
  rw [gu_gridZeroExtend, simplexEval_zeroExtend]

lemma map_gridEvalEmb_gridZeroEmb {a b n : ℕ} (hn : 0 < n)
    (e : Fin a ↪ Fin b) (v : Fin b → E)
    (hv : AffineIndependent ℝ v) (A : Finset (GridVert a n)) :
    (A.map (gridZeroEmb e)).map (gridEvalEmb hn v hv) =
      A.map (gridEvalEmb hn (fun i => v (e i))
        (affineIndependent_comp_embedding e hv)) := by
  classical
  -- both maps are the same composite embedding
  ext x
  constructor
  · intro hx
    obtain ⟨p,hp,eq⟩ := (Finset.mem_map).1 hx
    obtain ⟨q,hq,eq'⟩ := (Finset.mem_map).1 hp
    have val : gridEvalEmb hn
          (fun i => v (e i)) (affineIndependent_comp_embedding e hv) q = x := by
      rw [← gridEvalEmb_zeroExtend hn e v hv q]
      change gridEvalEmb hn v hv (gridZeroExtend e q) = x
      calc
        _ = gridEvalEmb hn v hv p := congrArg (gridEvalEmb hn v hv) eq'
        _ = x := eq
    exact (Finset.mem_map).2 ⟨q,hq,val⟩
  · intro hx
    obtain ⟨q,hq,eq⟩ := (Finset.mem_map).1 hx
    have mem' : gridZeroExtend e q ∈ A.map (gridZeroEmb e) :=
      (Finset.mem_map).2 ⟨q,hq,rfl⟩
    have val : gridEvalEmb hn v hv (gridZeroExtend e q) = x :=
      (gridEvalEmb_zeroExtend hn e v hv q).trans eq
    exact (Finset.mem_map).2 ⟨gridZeroExtend e q, mem', val⟩
end Evaluation
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridRestrict.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridThreshold.lean
section
open Set Geometry
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {d n : ℕ}
/-- cumulative coordinate multiplied by the denominator. It lives in `[0,n]` on the
probability simplex. -/
def cutval (n : ℕ) (u : Fin d → ℝ) (m : ℕ) : ℝ := (n:ℝ) * cumCoord d u m
lemma cutval_mono {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i) : Monotone (cutval n u) := by
  intro i j h
  dsimp [cutval]
  gcongr
  exact cumCoord_mono hu h
lemma cutval_zero (u : Fin d → ℝ) : cutval n u 0 = 0 := by simp [cutval]
lemma cutval_end (u : Fin d → ℝ) (hs : ∑ i, u i = 1) : cutval n u d = n := by
  simp [cutval, cumCoord_large u (le_rfl), hs]
lemma cutval_large (u : Fin d → ℝ) (hs : ∑ i, u i = 1) {m : ℕ} (hm : d ≤ m) :
    cutval n u m = n := by simp [cutval, cumCoord_large u hm, hs]
lemma cutval_nonneg {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i) (m : ℕ) :
    0 ≤ cutval n u m := (cutval_mono (n:=n) hu (Nat.zero_le m)) |>.trans' (by simp [cutval])
-- simpler invocation
lemma floor_frac_bounds (a : ℝ) (ha : 0 ≤ a) :
    (0:ℝ) ≤ a - (Nat.floor a : ℕ) ∧ a - (Nat.floor a : ℕ) < 1 := by
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le ha)
  · have := Nat.lt_floor_add_one a
    exact by exact_mod_cast (sub_lt_iff_lt_add'.mpr this)
/-- round up those cuts whose fractional part is at least threshold `t`. -/
def thresholdCuts (n : ℕ) (u : Fin d → ℝ) (t : ℝ) (m : ℕ) : ℕ :=
    Nat.floor (cutval n u m) + if t ≤ cutval n u m - (Nat.floor (cutval n u m):ℕ) then 1 else 0
lemma thresholdCuts_between {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i) (t : ℝ) (m : ℕ) :
    Nat.floor (cutval n u m) ≤ thresholdCuts n u t m ∧
    thresholdCuts n u t m ≤ Nat.floor (cutval n u m) + 1 := by
  dsimp [thresholdCuts]
  split_ifs <;> omega
lemma thresholdCuts_zero {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i)
    (t : ℝ) (ht : 0 < t) : thresholdCuts n u t 0 = 0 := by
  have fl : Nat.floor (cutval n u 0) = 0 := by simp [cutval]
  simp [thresholdCuts, cutval_zero, fl, not_le.mpr ht]
lemma thresholdCuts_end {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i)
    (hs : ∑ i, u i = 1) (t : ℝ) (ht : 0 < t) : thresholdCuts n u t d = n := by
  simp [thresholdCuts, cutval_end (n:=n) u hs, not_le.mpr ht]
/-- Moving the threshold down only raises a cut. -/
lemma thresholdCuts_anti {u : Fin d → ℝ} {s t : ℝ} (h : s ≤ t) (m : ℕ) :
    thresholdCuts n u t m ≤ thresholdCuts n u s m := by
  dsimp [thresholdCuts]
  split_ifs with a b
  · exact le_rfl
  · exact (b (h.trans a)).elim
  · omega
  · exact le_rfl
lemma thresholdCuts_near' {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i)
    (s t : ℝ) (m : ℕ) : thresholdCuts n u s m ≤ thresholdCuts n u t m + 1 := by
  have l := thresholdCuts_between (n:=n) hu s m
  have r := thresholdCuts_between (n:=n) hu t m
  omega
lemma thresholdCuts_mono {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i)
    (t : ℝ) : Monotone (thresholdCuts n u t) := by
  intro i j hij
  dsimp [thresholdCuts]
  have hi0 : 0 ≤ cutval n u i := cutval_nonneg (n:=n) hu i
  have hj0 : 0 ≤ cutval n u j := cutval_nonneg (n:=n) hu j
  have vv : cutval n u i ≤ cutval n u j := cutval_mono (n:=n) hu hij
  have ff : Nat.floor (cutval n u i) ≤ Nat.floor (cutval n u j) := Nat.floor_mono vv
  split_ifs with h1 h2
  all_goals try omega
  -- only case left: left raises while right does not. Their floors cannot be equal.
  have ne : Nat.floor (cutval n u i) ≠ Nat.floor (cutval n u j) := by
    intro e
    apply h2
    have : cutval n u i - (Nat.floor (cutval n u i):ℕ) ≤
        cutval n u j - (Nat.floor (cutval n u j):ℕ) := by rw [e]; linarith
    exact h1.trans this
  omega
/-- The canonical vertex at a level threshold. -/
def thresholdVert (n : ℕ) (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hs : ∑ i, u i = 1) (t : ℝ) (ht : 0 < t) : GridVert d n :=
  gpOfCuts (thresholdCuts n u t) (thresholdCuts_mono hu t)
    (thresholdCuts_zero hu t ht) (thresholdCuts_end hu hs t ht)
lemma thresholdVert_gp (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hs : ∑ i, u i = 1) (t : ℝ) (ht : 0 < t) {m : ℕ} (hm : m ≤ d) :
    gp (thresholdVert n u hu hs t ht) m = thresholdCuts n u t m := by
  unfold thresholdVert
  apply gp_gpOfCuts _ _ _ _ hm
lemma thresholdVert_le {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i)
    (hs : ∑ i, u i = 1) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) (h : s ≤ t) :
    gpLe (thresholdVert n u hu hs t ht0) (thresholdVert n u hu hs s hs0) := by
  unfold thresholdVert
  exact gpOfCuts_le (thresholdCuts_mono hu t) (thresholdCuts_mono hu s)
    (thresholdCuts_zero hu t ht0) (thresholdCuts_zero hu s hs0)
    (thresholdCuts_end hu hs t ht0) (thresholdCuts_end hu hs s hs0)
    (fun m hm => thresholdCuts_anti h m)
lemma thresholdVert_near {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i)
    (hs : ∑ i, u i = 1) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) :
    gpNear (thresholdVert n u hu hs s hs0) (thresholdVert n u hu hs t ht0) := by
  unfold thresholdVert
  exact gpOfCuts_near (thresholdCuts_mono hu s) (thresholdCuts_mono hu t)
    (thresholdCuts_zero hu s hs0) (thresholdCuts_zero hu t ht0)
    (thresholdCuts_end hu hs s hs0) (thresholdCuts_end hu hs t ht0)
    (fun m hm => thresholdCuts_near' hu s t m)
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open Set Geometry
open scoped BigOperators Topology
variable {d n : ℕ}
/-- Positive list of the only thresholds at which a rounding can jump. Including `1`
accounts for the initial (all floors) vertex. -/
def fracLevel (n : ℕ) (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (m : Fin (d+1)) : {x : ℝ // 0 < x} :=
  if h : 0 < cutval n u m.val - (Nat.floor (cutval n u m.val) : ℕ) then
    ⟨cutval n u m.val - (Nat.floor (cutval n u m.val) : ℕ), h⟩ else ⟨1, zero_lt_one⟩
noncomputable def thresholdSupport (n : ℕ) (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hs : ∑ i, u i = 1) : Finset (GridVert d n) :=
  Finset.univ.image (fun m : Fin (d+1) =>
    thresholdVert n u hu hs (fracLevel n u hu m) (fracLevel n u hu m).property)
lemma thresholdSupport_chain (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hs : ∑ i, u i = 1) : thresholdSupport n u hu hs ∈ coeffChains d n := by
  classical
  constructor
  · intro a ha b hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    rcases le_total (fracLevel n u hu i).val (fracLevel n u hu j).val with h|h
    · exact Or.inr (thresholdVert_le hu hs (fracLevel n u hu i).property
        (fracLevel n u hu j).property h)
    · exact Or.inl (thresholdVert_le hu hs (fracLevel n u hu j).property
        (fracLevel n u hu i).property h)
  · intro a ha b hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    exact thresholdVert_near hu hs _ _
lemma thresholdSupport_nonempty (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hs : ∑ i, u i = 1) : (thresholdSupport n u hu hs).Nonempty := by
  classical
  have hd : 0 < d := by
    by_contra z
    have : d = 0 := Nat.eq_zero_of_not_pos z
    subst d
    simp at hs
  let i : Fin (d+1) := ⟨0, by omega⟩
  exact ⟨thresholdVert n u hu hs (fracLevel n u hu i) (fracLevel n u hu i).property,
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridThreshold.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/CoeffStep.lean
section
open Set Geometry
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {d n : ℕ}
/-- Distinct positive thresholds of a coefficient vector.  Zero fractional
parts are replaced by `1`; consequently the last interval is present even if
all cuts are integral. -/
def levelSet (n : ℕ) (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) : Finset ℝ :=
  Finset.univ.image (fun m : Fin (d+1) => (fracLevel n u hu m).val)
def levelList (n : ℕ) (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) : List ℝ :=
  (levelSet n u hu).sort (· ≤ ·)
lemma mem_level_pos {u : Fin d → ℝ} {hu : ∀ i, 0 ≤ u i} {t : ℝ}
    (h : t ∈ levelSet n u hu) : 0 < t := by
  classical
  obtain ⟨m,_, hm⟩ := Finset.mem_image.mp h
  rw [← hm]
  exact (fracLevel n u hu m).property
lemma mem_level_le_one {u : Fin d → ℝ} {hu : ∀ i, 0 ≤ u i} {t : ℝ}
    (h : t ∈ levelSet n u hu) : t ≤ 1 := by
  classical
  obtain ⟨m,_, hm⟩ := Finset.mem_image.mp h
  rw [← hm]
  unfold fracLevel
  split_ifs with z
  · exact le_of_lt (floor_frac_bounds _ (cutval_nonneg (n:=n) hu _ )).2
  · exact le_rfl
lemma one_mem_level (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (1:ℝ) ∈ levelSet n u hu := by
  classical
  unfold levelSet
  let i : Fin (d+1) := ⟨0, by omega⟩
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  dsimp [i, fracLevel]
  simp [cutval]
def leftEnd (L : List ℝ) (i : Fin L.length) : ℝ :=
  if _h : i.val = 0 then 0 else L.get ⟨i.val-1, by omega⟩
def intWeight (L : List ℝ) (i : Fin L.length) : ℝ := L.get i - leftEnd L i
lemma levelList_sorted (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (levelList n u hu).Pairwise (fun x y : ℝ => x < y) := by
  classical
  exact List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort (levelSet n u hu))
lemma levelList_mem (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (i : Fin (levelList n u hu).length) :
    (levelList n u hu).get i ∈ levelSet n u hu := by
  classical
  have h := List.get_mem (levelList n u hu) i
  exact (Finset.mem_sort (· ≤ ·)).mp h
lemma levelList_pos (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (i : Fin (levelList n u hu).length) :
    0 < (levelList n u hu).get i :=
  mem_level_pos (n:=n) (levelList_mem (n:=n) u hu i)
lemma intWeight_nonneg_list {L : List ℝ} (hs : L.Pairwise (fun x y : ℝ => x < y))
    (hp : ∀ x ∈ L, 0 < x) (i : Fin L.length) : 0 ≤ intWeight L i := by
  classical
  unfold intWeight leftEnd
  split_ifs with z
  · simpa using (le_of_lt (hp _ (List.get_mem L i)))
  · have li : (⟨i.val-1, by omega⟩ : Fin L.length) < i := by
      change i.val - 1 < i.val
      omega
    have hget : L.get ⟨i.val-1, by omega⟩ < L.get i :=
      (List.pairwise_iff_get.mp hs) _ _ li
    linarith
lemma intWeight_nonneg (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (i : Fin (levelList n u hu).length) :
    0 ≤ intWeight (levelList n u hu) i :=
  intWeight_nonneg_list (levelList_sorted (n:=n) u hu)
    (fun x hx => mem_level_pos (n:=n) (u:=u) (hu:=hu)
      ((Finset.mem_sort (· ≤ ·)).mp (by simpa [levelList] using hx))) i
-- algebraic telescoping independent of sorting
lemma sum_sub_previous (v : ℕ → ℝ) : ∀ N : ℕ,
    (∑ i ∈ Finset.range N, (v i - if i=0 then 0 else v (i-1))) =
      if N=0 then 0 else v (N-1) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases z : N = 0 <;> simp [z]
lemma sum_intWeight (L : List ℝ) :
    ∑ i : Fin L.length, intWeight L i =
      if h : L = [] then 0 else L.getLast (by simpa using h) := by
  classical
  let v : ℕ → ℝ := fun i => if h : i < L.length then L.get ⟨i,h⟩ else 0
  let term : ℕ → ℝ := fun i => if h : i < L.length then intWeight L ⟨i,h⟩ else 0
  have term_eq (i : ℕ) (hi : i < L.length) :
      term i = v i - if i=0 then 0 else v (i-1) := by
    dsimp [term, v]
    simp [hi, intWeight, leftEnd]
    by_cases z : i = 0
    · simp [z]
    · have hi' : i-1 < L.length := by omega
      simp [z, hi']
  have range_eq : (∑ i ∈ Finset.range L.length, term i) =
      ∑ i ∈ Finset.range L.length, (v i - if i=0 then 0 else v (i-1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact term_eq i (Finset.mem_range.mp hi)
  have fin_eq : (∑ i : Fin L.length, intWeight L i) =
      ∑ i ∈ Finset.range L.length, term i := by
    rw [← Fin.sum_univ_eq_sum_range term L.length]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [term]
    simp
  rw [fin_eq, range_eq, sum_sub_previous]
  by_cases z : L.length = 0
  · have e : L = [] := List.length_eq_zero_iff.mp z
    simp [e]
  · have pos : 0 < L.length := Nat.pos_of_ne_zero z
    have ge : L ≠ [] := List.ne_nil_of_length_pos pos
    simp [z, ge]
    dsimp [v]
    have lt : L.length - 1 < L.length := by omega
    simp [lt]
    rw [List.getLast_eq_getElem]
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open scoped BigOperators
variable {d n : ℕ}
lemma levelList_ne (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) :
    levelList n u hu ≠ [] := by
  classical
  intro e
  have hx : (1:ℝ) ∈ levelList n u hu :=
    (Finset.mem_sort (· ≤ ·)).mpr (one_mem_level (n:=n) u hu)
  simpa [e] using hx
lemma levelList_last (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (levelList n u hu).getLast (levelList_ne (n:=n) u hu) = 1 := by
  classical
  let L := levelList n u hu
  let ne : L ≠ [] := levelList_ne (n:=n) u hu
  have one : (1:ℝ) ∈ L :=
    (Finset.mem_sort (· ≤ ·)).mpr (one_mem_level (n:=n) u hu)
  have leall : ∀ x ∈ L, x ≤ (1:ℝ) := by
    intro x hx
    apply mem_level_le_one (n:=n) (u:=u) (hu:=hu)
    exact (Finset.mem_sort (· ≤ ·)).mp hx
  rcases List.get_of_mem one with ⟨i,hi⟩
  have maxIn : L.getLast ne ∈ L := List.getLast_mem ne
  have a := leall _ maxIn
  have lelast : L.get i ≤ L.getLast ne := by
    -- sorted list; the last has maximal index
    have idx : i.val ≤ L.length - 1 := by omega
    rcases Nat.lt_or_eq_of_le idx with lt|eq
    · have ltfin : i < ⟨L.length-1, by
          have : 0 < L.length := List.length_pos_of_ne_nil ne
          omega⟩ := by
            change i.val < L.length-1
            exact lt
      have sortedL : L.Pairwise (fun x y : ℝ => x < y) :=
        levelList_sorted (n:=n) u hu
      have hh := (List.pairwise_iff_get.mp sortedL) _ _ ltfin
      have lastget : L.get ⟨L.length-1, by
          have := List.length_pos_of_ne_nil ne
          omega⟩ = L.getLast ne := by
        simp [List.getLast_eq_getElem, List.get_eq_getElem]
      rw [lastget] at hh
      exact le_of_lt hh
    · have ei : i = ⟨L.length-1, by
          have : 0 < L.length := List.length_pos_of_ne_nil ne
          omega⟩ := Fin.ext eq
      rw [ei]
      simp [List.getLast_eq_getElem, List.get_eq_getElem]
  have b : (1:ℝ) ≤ L.getLast ne := hi ▸ lelast
  exact le_antisymm a b
lemma sum_level_weights (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (∑ i : Fin (levelList n u hu).length,
      intWeight (levelList n u hu) i) = 1 := by
  classical
  simpa [levelList_ne (n:=n) u hu]
    using (sum_intWeight (levelList n u hu)).trans
      (by simp [levelList_ne (n:=n) u hu, levelList_last (n:=n) u hu])
/-- Every genuine fractional value is one of the threshold levels. Integer
coordinates have fraction zero and never switch on (their floor term is
already exact). -/
lemma frac_mem_level {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i)
    (m : Fin (d+1))
    (hpos : 0 < cutval n u m.val - (Nat.floor (cutval n u m.val):ℕ)) :
    cutval n u m.val - (Nat.floor (cutval n u m.val):ℕ) ∈ levelSet n u hu := by
  classical
  unfold levelSet
  apply Finset.mem_image.mpr
  refine ⟨m, Finset.mem_univ _, ?_⟩
  simp [fracLevel, hpos]
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/CoeffStep.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridCoverReduction.lean
section
open Set Geometry
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def simplexLinear {d : ℕ} (v : Fin d → E) : (Fin d → ℝ) →ₗ[ℝ] E :=
{ toFun := simplexEval v
  map_add' := by intro x y; simp [simplexEval, add_smul, Finset.sum_add_distrib]
  map_smul' := by intro c x; simp [simplexEval, mul_smul, Finset.smul_sum] }
@[simp] lemma simplexLinear_apply {d} (v : Fin d → E) (u) :
   simplexLinear v u = simplexEval v u := rfl
lemma eval_mem_mappedHull {d n : ℕ} (v : Fin d → E)
    (A : Finset (GridVert d n)) {u : Fin d → ℝ}
    (h : u ∈ convexHull ℝ (gu '' (A : Set (GridVert d n)))) :
    simplexEval v u ∈ convexHull ℝ ((simplexEval v ∘ gu) '' (A : Set (GridVert d n))) := by
  have im : simplexEval v u ∈
      simplexLinear v '' convexHull ℝ (gu '' (A : Set (GridVert d n))) := ⟨u,h,rfl⟩
  rw [LinearMap.image_convexHull] at im
  simpa [simplexLinear, Function.comp_def, Set.image_image] using im
/-- Coverage of the global pulling grid reduces to the clean coefficient-space rounding
lemma. No assertions about ambient faces or homeomorphisms remain in it. -/
lemma mappedChains_cover_of_coeff
    (n : ℕ) (hn : 0 < n)
    (round : ∀ (d : ℕ) (u : Fin d → ℝ),
      u ∈ coeffSimplex d →
      ∃ A : Finset (GridVert d n), A.Nonempty ∧ A ∈ coeffChains d n ∧
        u ∈ convexHull ℝ (gu '' (A : Set (GridVert d n))))
    (s : Finset E) :
    ∀ x ∈ convexHull ℝ (s : Set E),
      ∃ D ∈ mappedChains s n hn, D.Nonempty ∧
        x ∈ convexHull ℝ (D : Set E) := by
  classical
  intro x hx
  obtain ⟨t,ht,tne,hxt⟩ := lexFaces_cover s x hx
  have hx' : x ∈ convexHull ℝ (Set.range (inheritedFace s t)) := by
    simpa [range_inheritedFace ht.1] using hxt
  let z : {y : E // y ∈ convexHull ℝ (Set.range (inheritedFace s t))} := ⟨x,hx'⟩
  let u := (simplexHomeo (inheritedFace s t) (inheritedFace_indep ht)).symm z
  obtain ⟨A,Ane,Ac, hu⟩ := round _ (u : Fin (facePos s t).card → ℝ) u.property
  let D : Finset E := A.map (gridEvalEmb hn (inheritedFace s t)
    (inheritedFace_indep ht))
  refine ⟨D, ?_, ?_, ?_⟩
  · exact ⟨t,ht,A,Ac,rfl⟩
  · obtain ⟨a,ha⟩ := Ane
    exact ⟨gridEvalEmb hn (inheritedFace s t) (inheritedFace_indep ht) a,
      Finset.mem_map.mpr ⟨a,ha,rfl⟩⟩
  · dsimp [D]
    rw [coe_gridEvalEmb_map]
    have eu : simplexEval (inheritedFace s t) (u : Fin (facePos s t).card → ℝ) = x := by
      have := simplexHomeo_apply (inheritedFace s t) (inheritedFace_indep ht) u
      change (((simplexHomeo (inheritedFace s t) (inheritedFace_indep ht)) u : {y : E // y ∈ convexHull ℝ (Set.range (inheritedFace s t))}) : E) = _ at this
      exact this.trans (congrArg Subtype.val ((simplexHomeo _ _).apply_symm_apply z))
    rw [← eu]
    exact eval_mem_mappedHull _ A hu
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridCoverReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridPartialCover.lean
section
open Set Geometry
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section
/- A first, robust part of the missing coefficient-cover assertion.  At a
   denominator vertex no choice of a top-dimensional chamber is necessary:
   the singleton is already one of the prefix chains.  This formulation is
   convenient since later rounding arguments can discharge the hypothesis
   by exhibiting an integral representative. -/
lemma coeffChains_singleton {d n : ℕ} (a : GridVert d n) :
    ({a} : Finset (GridVert d n)) ∈ coeffChains d n := by
  classical
  constructor
  · intro x hx y hy
    have hx' : x = a := Finset.mem_singleton.mp hx
    have hy' : y = a := Finset.mem_singleton.mp hy
    subst x
    subst y
    exact Or.inl (gpLe_rfl a)
  · intro x hx y hy
    have hx' : x = a := Finset.mem_singleton.mp hx
    have hy' : y = a := Finset.mem_singleton.mp hy
    subst x
    subst y
    intro m
    exact Nat.le_add_right_of_le (le_rfl)

lemma round_on_grid {d n : ℕ} {u : Fin d → ℝ}
    (a : GridVert d n) (hu : u = gu a) :
    ∃ A : Finset (GridVert d n), A.Nonempty ∧ A ∈ coeffChains d n ∧
      u ∈ convexHull ℝ (gu '' (A : Set (GridVert d n))) := by
  classical
  refine ⟨{a}, ⟨a, by simp⟩, coeffChains_singleton a, ?_⟩
  subst u
  apply subset_convexHull (𝕜 := ℝ)
  exact ⟨a, by simp, rfl⟩

/- Conversely the denominator-one grid already fills the whole coefficient
   simplex.  Although the main theorem removes this terminal case before the
   Freudenthal block, keeping it at coefficient level makes explicit that the
   obstruction starts with denominator two. -/
lemma gp_one_bound {d : ℕ} (a : GridVert d 1) (m : ℕ) : gp a m ≤ 1 := by
  by_cases h : m ≤ d
  · unfold gp
    have hsub :
        (Finset.univ.filter (fun i : Fin d => i.val < m)).sum
            (fun i => (a.1 i).val) ≤
        Finset.univ.sum (fun i : Fin d => (a.1 i).val) :=
      Finset.sum_le_sum_of_subset_of_nonneg (by intro z hz; simp)
        (by intro i hi hj; exact Nat.zero_le _)
    simpa [a.property] using hsub
  · have hh : d ≤ m := le_of_not_ge h
    simp [gp_large a hh]

lemma unit_coord {d : ℕ} (a : GridVert d 1) :
    ∃ ia : Fin d, ∀ i : Fin d, (a.1 i).val = if i = ia then 1 else 0 := by
  classical
  let w : Fin d →₀ ℕ := (Finsupp.equivFunOnFinite).symm (fun i : Fin d => (a.1 i).val)
  have weval : ∀ i : Fin d, w i = (a.1 i).val := by
    intro i
    change (Finsupp.equivFunOnFinite
      ((Finsupp.equivFunOnFinite : (Fin d →₀ ℕ) ≃ (Fin d → ℕ)).symm
        (fun i : Fin d => (a.1 i).val))) i = _
    exact congrFun (Equiv.apply_symm_apply
      (Finsupp.equivFunOnFinite : (Fin d →₀ ℕ) ≃ (Fin d → ℕ))
      (fun i : Fin d => (a.1 i).val)) i
  have mass : w.sum (fun _ n => n) = 1 := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa [weval] using a.property
  rcases (Finsupp.sum_eq_one_iff w).mp mass with ⟨i,eq⟩
  refine ⟨i, ?_⟩
  intro j
  rw [← weval]
  rw [eq]
  classical
  by_cases h : j = i
  · subst j; simp
  · simp [Finsupp.single_apply, h]

lemma gp_unit_formula {d : ℕ} (a : GridVert d 1)
    (i : Fin d) (hi : ∀ j : Fin d, (a.1 j).val = if j = i then 1 else 0)
    (m : ℕ) : gp a m = if i.val < m then 1 else 0 := by
  classical
  unfold gp
  simp_rw [hi]
  by_cases h : i.val < m
  · calc
      _ = ∑ j ∈ (Finset.univ.filter (fun j : Fin d => j.val < m)),
            (if j = i then 1 else 0) := rfl
      _ = 1 := by
        rw [Finset.sum_eq_single i]
        · simp [h]
        · intro b hb ne; simp [ne]
        · intro hn; have : i ∈ (Finset.univ.filter (fun j : Fin d => j.val < m)) := by simp [h]
          exact (hn this).elim
      _ = _ := by simp [h]
  · calc
      _ = ∑ j ∈ (Finset.univ.filter (fun j : Fin d => j.val < m)),
          (if j = i then 1 else 0) := rfl
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have jne : j ≠ i := by
          intro e; subst j
          exact h ((Finset.mem_filter.mp hj).2)
        simp [jne]
      _ = _ := by simp [h]

lemma coeffChains_univ_one (d : ℕ) :
    (Finset.univ : Finset (GridVert d 1)) ∈ coeffChains d 1 := by
  classical
  constructor
  · intro a ha b hb
    obtain ⟨ia,hia⟩ := unit_coord a
    obtain ⟨ib,hib⟩ := unit_coord b
    rcases le_total ia.val ib.val with h|h
    · right
      intro m
      simp [gp_unit_formula a ia hia, gp_unit_formula b ib hib]
      split_ifs <;> omega
    · left
      intro m
      simp [gp_unit_formula a ia hia, gp_unit_formula b ib hib]
      split_ifs <;> omega
  · intro a ha b hb m
    exact (gp_one_bound a m).trans (by omega)

end
end FamiliesProof

namespace FamiliesProof
open Set Geometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Hence the cover statement for `mappedChains` holds on every denominator
vertex of every pulling face.  This is a useful dense skeleton of the missing
Freudenthal cover lemma; no ambient-independence coercions are involved. -/
lemma mappedChains_vertex {s : Finset E} {n : ℕ} (hn : 0 < n)
    {t : Finset E} (ht : lexFace s t)
    (a : GridVert (facePos s t).card n) :
    ∃ D ∈ mappedChains s n hn, D.Nonempty ∧
      simplexEval (inheritedFace s t) (gu a) ∈ convexHull ℝ (D : Set E) := by
  classical
  let z : E := gridEvalEmb hn (inheritedFace s t) (inheritedFace_indep ht) a
  have mem := singleton_grid_mem s n hn ht a
  refine ⟨{z}, ?_, by simp, ?_⟩
  · simpa [z] using mem
  · have hz : simplexEval (inheritedFace s t) (gu a) = z := rfl
    rw [hz]
    have : z ∈ ({z} : Set E) := Set.mem_singleton z
    simpa using ((subset_convexHull ℝ ({z} : Set E)) this)
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridPartialCover.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridSubface.lean
section
open Set
open scoped BigOperators
namespace FamiliesProof
attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nested pair of inherited faces are nested as *ordered* lists.  The
embedding does not use the arbitrary order picked for the smaller Finset. -/
lemma exists_inheritedFace_embedding (s t u : Finset E) (hu : u ⊆ t) :
  ∃ e : Fin (facePos s u).card ↪ Fin (facePos s t).card,
    StrictMono e ∧
      (∀ i, inheritedFace s t (e i) = inheritedFace s u i) := by
  classical
  have pos_sub : facePos s u ⊆ facePos s t := by
    intro j hj
    apply Finset.mem_filter.mpr
    have hj' := Finset.mem_filter.mp hj
    exact ⟨Finset.mem_univ _, hu hj'.2⟩
  have meminc (i : Fin (facePos s u).card) :
      faceInc s u i ∈ facePos s u := by
    have rr := range_faceInc (s:=s) (t:=u)
    have : faceInc s u i ∈ Set.range (faceInc s u) := ⟨i,rfl⟩
    rwa [rr] at this
  have hit (i : Fin (facePos s u).card) :
      ∃ j : Fin (facePos s t).card, faceInc s t j = faceInc s u i := by
    have hmem : faceInc s u i ∈ facePos s t := pos_sub (meminc i)
    have rr := range_faceInc (s:=s) (t:=t)
    have : faceInc s u i ∈ Set.range (faceInc s t) := by rwa [rr]
    simpa using this
  choose g hg using hit
  have gin : Function.Injective g := by
    intro i j eq
    have hh : faceInc s u i = faceInc s u j := by
      rw [← hg i, ← hg j, eq]
    exact (faceInc s u).injective hh
  let e : Fin (facePos s u).card ↪ Fin (facePos s t).card := ⟨g, gin⟩
  have emap (i:Fin (facePos s u).card) : faceInc s t (e i) = faceInc s u i := hg i
  have mono : StrictMono e := by
    intro i j hij
    have hij' : faceInc s u i < faceInc s u j := (faceInc_mono s u) hij
    have tt : faceInc s t (e i) < faceInc s t (e j) := by rwa [emap i, emap j]
    -- reflect order of the strictly monotone embedding
    exact (faceInc_mono s t).lt_iff_lt.mp tt
  refine ⟨e, mono, ?_⟩
  intro i
  dsimp [inheritedFace]
  rw [emap]

end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridSubface.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridSubfaceCoeff.lean
section
open Set
open scoped BigOperators
namespace FamiliesProof
attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable section

/-- In coefficient space, intersecting the convex hull of a finite grid set
with a coordinate face just discards grid points off that face.
Strict positivity is not needed: we pass to the positive support of a
representation. -/
lemma guHull_restrict_face {a b n : ℕ} (hn : 0 < n)
    (e : Fin a ↪ Fin b)
    (A : Finset (GridVert b n)) {u : Fin b → ℝ}
    (hA : u ∈ convexHull ℝ (gu '' (A : Set (GridVert b n))))
    (hz : ∀ j : Fin b, j ∉ Set.range e → u j = 0) :
    let F := A.filter (fun p => ∀ j : Fin b, j ∉ Set.range e → gu p j = 0)
    u ∈ convexHull ℝ (gu '' (F : Set (GridVert b n))) := by
  classical
  dsimp
  let emb : GridVert b n ↪ (Fin b → ℝ) := ⟨gu, gu_inj hn⟩
  let D : Finset (Fin b → ℝ) := A.map emb
  have Dhull : u ∈ convexHull ℝ (D : Set (Fin b → ℝ)) := by
    have eqD : (D : Set (Fin b → ℝ)) = gu '' (A : Set (GridVert b n)) :=
      Finset.coe_map emb A
    rwa [eqD]
  rcases (Finset.mem_convexHull' (R:=ℝ) (s:=D) (x:=u)).1 Dhull with
    ⟨c,hc0,hc1,hcv⟩
  let w : GridVert b n → ℝ := fun p => c (gu p)
  have w0 : ∀ p ∈ A, 0 ≤ w p := by
    intro p hp
    exact hc0 _ ((Finset.mem_map).2 ⟨p,hp,rfl⟩)
  have w1 : ∑ p ∈ A, w p = 1 := by
    simpa [D, emb, w] using hc1
  have wv : ∑ p ∈ A, w p • gu p = u := by
    simpa [D, emb, w] using hcv
  let P : Finset (GridVert b n) := A.filter (fun p => 0 < w p)
  have PA : P ⊆ A := Finset.filter_subset _ _
  have Pin : P ⊆ A.filter
      (fun p => ∀ j : Fin b, j ∉ Set.range e → gu p j = 0) := by
    intro p hp
    have pp := (Finset.mem_filter).1 hp
    apply Finset.mem_filter.mpr
    refine ⟨pp.1, ?_⟩
    intro j hj
    have eqc : ∑ q ∈ A, w q * gu q j = 0 := by
      have eq := congrFun wv j
      simpa [Finset.sum_apply, hz j hj] using eq
    have each : w p * gu p j = 0 := by
      by_contra bad
      have pos : 0 < w p * gu p j :=
        lt_of_le_of_ne (mul_nonneg (w0 p pp.1) (gu_nonneg p j)) (Ne.symm bad)
      have le' : w p * gu p j ≤ ∑ q ∈ A, w q * gu q j := by
        apply Finset.single_le_sum (fun q hq => mul_nonneg (w0 q hq) (gu_nonneg q j)) pp.1
      rw [eqc] at le'
      exact (not_lt_of_ge le') pos
    exact (mul_eq_zero.mp each).resolve_left (ne_of_gt pp.2)
  have zero_out : ∀ p ∈ A, p ∉ P → w p = 0 := by
    intro p hp hpnot
    have no : ¬ 0 < w p := by
      intro h
      exact hpnot ((Finset.mem_filter).2 ⟨hp,h⟩)
    exact le_antisymm (le_of_not_gt no) (w0 p hp)
  have w1P : ∑ p ∈ P, w p = 1 := by
    calc
      _ = ∑ p ∈ A, w p := by
        apply Finset.sum_subset PA
        exact zero_out
      _ = 1 := w1
  have wvP : ∑ p ∈ P, w p • gu p = u := by
    calc
      _ = ∑ p ∈ A, w p • gu p := by
        apply Finset.sum_subset PA
        intro p hp hnot
        simp [zero_out p hp hnot]
      _ = u := wv
  have inP : u ∈ convexHull ℝ (gu '' (P : Set (GridVert b n))) := by
    let DP : Finset (Fin b → ℝ) := P.map emb
    have m : u ∈ convexHull ℝ (DP : Set (Fin b → ℝ)) := by
      apply (Finset.mem_convexHull' (R:=ℝ) (s:=DP) (x:=u)).2
      refine ⟨c, ?_, ?_, ?_⟩
      · intro y hy
        rcases (Finset.mem_map).1 hy with ⟨p,hp,rfl⟩
        exact w0 p (PA hp)
      · simpa [DP, emb, w] using w1P
      · simpa [DP, emb, w] using wvP
    simpa [DP, Finset.coe_map, emb] using m
  refine convexHull_mono ?_ inP
  intro z hz'
  rcases hz' with ⟨p,hp,rfl⟩
  exact ⟨p, Pin hp, rfl⟩

end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridSubfaceCoeff.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/CoeffRound.lean
section
open Set Geometry
open scoped BigOperators Topology
namespace FamiliesProof
noncomputable section

/-- first `r` interval weights telescope to the `r` th endpoint. -/
lemma sum_intWeight_range (L : List ℝ) (r : ℕ) (hr : r ≤ L.length) :
    let term : ℕ → ℝ := fun i => if hi : i < L.length then intWeight L ⟨i,hi⟩ else 0
    (∑ i ∈ Finset.range r, term i) =
      if h0 : r = 0 then 0 else L.get ⟨r-1, by omega⟩ := by
  classical
  dsimp
  -- auxiliary functions of the values and differences
  let v : ℕ → ℝ := fun i => if h : i < L.length then L.get ⟨i,h⟩ else 0
  let term : ℕ → ℝ := fun i => if h : i < L.length then intWeight L ⟨i,h⟩ else 0
  have term_eq (i : ℕ) (hi : i < L.length) :
      term i = v i - if i = 0 then 0 else v (i-1) := by
    dsimp [term, v]
    simp [hi, intWeight, leftEnd]
    by_cases z : i = 0
    · simp [z]
    · have hi' : i - 1 < L.length := by omega
      simp [z, hi']
  have conv : (∑ i ∈ Finset.range r, term i) =
      ∑ i ∈ Finset.range r, (v i - if i=0 then 0 else v (i-1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact term_eq i (lt_of_lt_of_le (Finset.mem_range.mp hi) hr)
  rw [conv, sum_sub_previous]
  split_ifs with z
  · rfl
  · dsimp [v]
    have lt : r - 1 < L.length := by omega
    simp [lt]

end
end FamiliesProof

namespace FamiliesProof
noncomputable section
lemma sorted_get_le_iff {L : List ℝ}
    (hs : L.Pairwise (fun x y : ℝ => x < y))
    (i j : Fin L.length) : L.get i ≤ L.get j ↔ i.val ≤ j.val := by
  constructor
  · intro h
    by_contra bad
    have ltji : j < i := by
      change j.val < i.val
      omega
    have lt : L.get j < L.get i := (List.pairwise_iff_get.mp hs) _ _ ltji
    linarith
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact le_of_lt ((List.pairwise_iff_get.mp hs) _ _ (by simpa using hlt))
    · have e : i = j := Fin.ext heq
      simp [e]

lemma sum_weight_below_level {L : List ℝ}
    (hs : L.Pairwise (fun x y : ℝ => x < y)) (k : Fin L.length) :
    (∑ i : Fin L.length,
      intWeight L i * (if L.get i ≤ L.get k then (1:ℝ) else 0)) = L.get k := by
  classical
  let term : ℕ → ℝ := fun i => if hi : i < L.length then intWeight L ⟨i,hi⟩ else 0
  have first :
      (∑ i : Fin L.length,
        intWeight L i * (if L.get i ≤ L.get k then (1:ℝ) else 0)) =
      ∑ i : Fin L.length, if i.val < k.val + 1 then intWeight L i else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    have iff := sorted_get_le_iff hs i k
    by_cases h : i.val < k.val + 1
    · have hle : i.val ≤ k.val := by omega
      have hv : L.get i ≤ L.get k := iff.mpr hle
      simp only [if_pos hv, if_pos h, mul_one]
    · have hn : ¬ i.val ≤ k.val := by omega
      have hv : ¬ L.get i ≤ L.get k := by intro h'; exact hn (iff.mp h')
      simp only [if_neg hv, mul_zero, if_neg h]
  rw [first]
  have second :
      (∑ i : Fin L.length, if i.val < k.val + 1 then intWeight L i else 0) =
        ∑ r ∈ Finset.range L.length, (if r < k.val+1 then term r else 0) := by
    calc
      _ = ∑ i : Fin L.length,
          (fun r : ℕ => if r < k.val+1 then term r else 0) i.val := by
            apply Finset.sum_congr rfl
            intro i hi
            have lt : i.val < L.length := i.isLt
            simp [term, lt]
      _ = _ := by simpa using (Fin.sum_univ_eq_sum_range (fun r : ℕ => if r < k.val+1 then term r else (0:ℝ)) L.length)
  rw [second]
  have hr : k.val + 1 ≤ L.length := by omega
  let small : Finset ℕ := Finset.range (k.val+1)
  let big : Finset ℕ := Finset.range L.length
  have sub : small ⊆ big := Finset.range_mono hr
  let f : ℕ → ℝ := fun r => if r < k.val+1 then term r else 0
  have subseteq : (∑ r ∈ small, f r) = ∑ r ∈ big, f r := by
    apply Finset.sum_subset sub
    intro x hx xnot
    have hnlt : ¬ x < k.val+1 := by
      intro lt
      exact xnot (by simpa [small] using lt)
    simp only [f, if_neg hnlt]
  have eqsmall : (∑ r ∈ small, f r) = ∑ r ∈ small, term r := by
    apply Finset.sum_congr rfl
    intro i hi
    have ilt : i < k.val+1 := Finset.mem_range.mp (by simpa [small] using hi)
    simp only [f, if_pos ilt]
  change (∑ r ∈ big, f r) = _
  rw [← subseteq, eqsmall]
  dsimp [small]
  have tel := sum_intWeight_range L (k.val+1) hr
  dsimp at tel
  have one0 : k.val+1 ≠ 0 := by omega
  simpa [term, one0] using tel
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
lemma sum_weight_below {L : List ℝ}
    (hs : L.Pairwise (fun x y : ℝ => x < y))
    (hp : ∀ x ∈ L, 0 < x) (r : ℝ)
    (hr : r = 0 ∨ r ∈ L) :
    (∑ i : Fin L.length,
      intWeight L i * (if L.get i ≤ r then (1:ℝ) else 0)) = r := by
  classical
  rcases hr with z | mem
  · subst r
    have all : ∀ i : Fin L.length, ¬ L.get i ≤ (0:ℝ) := by
      intro i
      exact not_le_of_gt (hp _ (List.get_mem _ _))
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (all i), mul_zero]
  · obtain ⟨k,hk⟩ := List.get_of_mem mem
    rw [← hk]
    exact sum_weight_below_level hs k
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open scoped BigOperators
variable {d n : ℕ}
lemma sum_weight_thresholdCuts (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hsu : ∑ i, u i = 1) (m : Fin (d+1)) :
    let L := levelList n u hu
    (∑ i : Fin L.length,
      intWeight L i * (thresholdCuts n u (L.get i) m.val : ℝ)) =
      cutval n u m.val := by
  classical
  dsimp
  let L := levelList n u hu
  let y : ℝ := cutval n u m.val
  let r : ℝ := y - (Nat.floor y : ℕ)
  have hr : r = 0 ∨ r ∈ L := by
    by_cases hp : 0 < r
    · right
      have mem : r ∈ levelSet n u hu := by
        apply frac_mem_level (n:=n) (u:=u) hu m
        exact hp
      exact (Finset.mem_sort (· ≤ ·)).mpr mem
    · have nn := (floor_frac_bounds y (cutval_nonneg (n:=n) hu m.val)).1
      left
      dsimp [r,y]
      exact le_antisymm (le_of_not_gt hp) nn
  have hsL : L.Pairwise (fun x y : ℝ => x < y) := levelList_sorted (n:=n) u hu
  have hpL : ∀ x ∈ L, 0 < x := by
    intro x hx
    apply mem_level_pos (n:=n) (u:=u) (hu:=hu)
    exact (Finset.mem_sort (· ≤ ·)).mp hx
  have below : (∑ i : Fin L.length,
      intWeight L i * (if L.get i ≤ r then (1:ℝ) else 0)) = r :=
    sum_weight_below hsL hpL r hr
  have conv (i : Fin L.length) :
      (thresholdCuts n u (L.get i) m.val : ℝ) =
        (Nat.floor y : ℕ) + (if L.get i ≤ r then (1:ℝ) else 0) := by
    dsimp [thresholdCuts, y, r]
    by_cases h : L.get i ≤ cutval n u m.val - ↑(Nat.floor (cutval n u m.val))
    · simp [h]
    · simp [h]
  -- now distribute the constant part
  change (∑ i : Fin L.length,
      intWeight L i * (thresholdCuts n u (L.get i) m.val : ℝ)) = _
  simp_rw [conv]
  have mass : (∑ i : Fin L.length, intWeight L i) = 1 := by
    dsimp [L]
    exact sum_level_weights u hu
  calc
    (∑ i : Fin L.length,
      intWeight L i * ((Nat.floor y : ℕ) +
        (if L.get i ≤ r then (1:ℝ) else 0))) =
        (Nat.floor y : ℕ) * (∑ i : Fin L.length, intWeight L i) +
        ∑ i : Fin L.length,
          intWeight L i * (if L.get i ≤ r then (1:ℝ) else 0) := by
            simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
              Finset.sum_mul]
            ring_nf
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (Nat.floor y : ℕ) + r := by rw [mass, below]; ring
    _ = cutval n u m.val := by dsimp [r, y]; ring
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open scoped BigOperators
lemma cumCoord_fin_sum_smul {d e : ℕ} (w : Fin e → ℝ)
    (v : Fin e → (Fin d → ℝ)) (m : ℕ) :
    cumCoord d (∑ i : Fin e, w i • v i) m =
      ∑ i : Fin e, w i * cumCoord d (v i) m := by
  classical
  simp [cumCoord, Finset.mul_sum]
  rw [Finset.sum_comm]
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open scoped BigOperators
variable {d n : ℕ}
lemma weighted_cum_gu_eq (hn : 0 < n)
    (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hsu : ∑ i, u i = 1) (m : Fin (d+1)) :
    let L := levelList n u hu
    cumCoord d
      (∑ i : Fin L.length, intWeight L i •
        gu (thresholdVert n u hu hsu (L.get i) (levelList_pos (n:=n) u hu i)))
      m.val = cumCoord d u m.val := by
  classical
  dsimp
  let L := levelList n u hu
  let tv : (i : Fin L.length) → GridVert d n := fun i =>
    thresholdVert n u hu hsu (L.get i) (levelList_pos (n:=n) u hu i)
  have cut : (∑ i : Fin L.length,
      intWeight L i * (thresholdCuts n u (L.get i) m.val : ℝ)) =
      cutval n u m.val := by
    exact sum_weight_thresholdCuts u hu hsu m
  have hnm : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have gp_eq (i : Fin L.length) :
      cumCoord d (gu (tv i)) m.val =
        (thresholdCuts n u (L.get i) m.val : ℝ) / (n:ℝ) := by
    rw [cum_gu]
    congr 1
    exact_mod_cast (thresholdVert_gp u hu hsu _ (levelList_pos (n:=n) u hu i)
      (show m.val ≤ d by omega))
  change cumCoord d (∑ i : Fin L.length, intWeight L i • gu (tv i)) m.val = _
  rw [cumCoord_fin_sum_smul]
  simp_rw [gp_eq]
  calc
    (∑ i : Fin L.length,
      intWeight L i * ((thresholdCuts n u (L.get i) m.val : ℝ) / (n:ℝ))) =
      (∑ i : Fin L.length,
        intWeight L i * (thresholdCuts n u (L.get i) m.val : ℝ)) / (n:ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = cutval n u m.val / (n:ℝ) := by rw [cut]
    _ = cumCoord d u m.val := by
      simp [cutval, hnm]
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open scoped BigOperators
variable {d n : ℕ}
lemma weighted_gu_eq (hn : 0 < n)
    (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hsu : ∑ i, u i = 1) :
    let L := levelList n u hu
    (∑ i : Fin L.length, intWeight L i •
      gu (thresholdVert n u hu hsu (L.get i) (levelList_pos (n:=n) u hu i))) = u := by
  classical
  dsimp
  let L := levelList n u hu
  let vv : Fin d → ℝ :=
    ∑ i : Fin L.length, intWeight L i •
      gu (thresholdVert n u hu hsu (L.get i) (levelList_pos (n:=n) u hu i))
  change vv = u
  funext j
  let m0 : Fin (d+1) := ⟨j.val, by omega⟩
  let m1 : Fin (d+1) := ⟨j.val+1, by omega⟩
  have e0 : cumCoord d vv j.val = cumCoord d u j.val := by
    have := weighted_cum_gu_eq (n:=n) hn u hu hsu m0
    simpa [vv, L, m0] using this
  have e1 : cumCoord d vv (j.val+1) = cumCoord d u (j.val+1) := by
    have := weighted_cum_gu_eq (n:=n) hn u hu hsu m1
    simpa [vv, L, m1] using this
  rw [cumCoord_succ j.isLt vv, cumCoord_succ j.isLt u, e0] at e1
  linarith
end
end FamiliesProof
namespace FamiliesProof
noncomputable section
variable {d n : ℕ}
lemma level_vertex_mem_support
    (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hsu : ∑ i, u i = 1)
    (i : Fin (levelList n u hu).length) :
    thresholdVert n u hu hsu ((levelList n u hu).get i)
      (levelList_pos (n:=n) u hu i) ∈ thresholdSupport n u hu hsu := by
  classical
  have mem := levelList_mem (n:=n) u hu i
  rcases Finset.mem_image.mp mem with ⟨m, hm, eq⟩
  apply Finset.mem_image.mpr
  refine ⟨m, by simpa using hm, ?_⟩
  dsimp
  -- all positivity proofs are irrelevant
  congr

end
end FamiliesProof
namespace FamiliesProof
noncomputable section
open Set Geometry
open scoped BigOperators
variable {d n : ℕ}
lemma threshold_round_mem (hn : 0 < n)
    (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hsu : ∑ i, u i = 1) :
    u ∈ convexHull ℝ
      (gu '' ((thresholdSupport n u hu hsu : Finset (GridVert d n)) :
        Set (GridVert d n))) := by
  classical
  let L := levelList n u hu
  let tv : Fin L.length → GridVert d n := fun i =>
    thresholdVert n u hu hsu (L.get i) (levelList_pos (n:=n) u hu i)
  have total : (∑ i : Fin L.length, intWeight L i • gu (tv i)) = u := by
    exact weighted_gu_eq (n:=n) hn u hu hsu
  have hz (i : Fin L.length) : gu (tv i) ∈
      gu '' ((thresholdSupport n u hu hsu : Finset (GridVert d n)) :
        Set (GridVert d n)) := by
    refine ⟨tv i, ?_, rfl⟩
    exact level_vertex_mem_support u hu hsu i
  have cv := convex_convexHull ℝ
      (gu '' ((thresholdSupport n u hu hsu : Finset (GridVert d n)) :
        Set (GridVert d n)))
  have mem := cv.sum_mem (t := (Finset.univ : Finset (Fin L.length)))
    (w := fun i : Fin L.length => intWeight L i)
    (z := fun i : Fin L.length => gu (tv i))
    (by
      intro i hi
      dsimp [L]
      exact intWeight_nonneg u hu i)
    (by simpa [L] using (sum_level_weights (n:=n) u hu))
    (by
      intro i hi
      exact subset_convexHull ℝ _ (hz i))
  let S : Set (Fin d → ℝ) := convexHull ℝ
        (gu '' ((thresholdSupport n u hu hsu : Finset (GridVert d n)) :
          Set (GridVert d n)))
  change u ∈ S
  have mm : (∑ i : Fin L.length, intWeight L i • gu (tv i)) ∈ S := by
    simpa [S] using mem
  exact (congrArg (fun x : Fin d → ℝ => x ∈ S) total).mp mm


lemma coeff_round (n : ℕ) (hn : 0 < n) (d : ℕ)
    (u : Fin d → ℝ) (hu : u ∈ coeffSimplex d) :
    ∃ A : Finset (GridVert d n), A.Nonempty ∧ A ∈ coeffChains d n ∧
      u ∈ convexHull ℝ (gu '' (A : Set (GridVert d n))) := by
  classical
  refine ⟨thresholdSupport n u hu.1 hu.2,
    thresholdSupport_nonempty u hu.1 hu.2,
    thresholdSupport_chain u hu.1 hu.2, ?_⟩
  exact threshold_round_mem hn u hu.1 hu.2
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/CoeffRound.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridSubfaceHull.lean
section
open Set
open scoped BigOperators
namespace FamiliesProof
attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ambient version of `guHull_restrict_face`: on independent simplex
coordinates, a point lying in a subface can use only grid vertices on that
subface in any grid-cell hull. -/
lemma gridHull_restrict_face {a b n : ℕ} (hn : 0 < n) (ha : 0 < a)
    (e : Fin a ↪ Fin b)
    (v : Fin b → E) (hv : AffineIndependent ℝ v)
    (A : Finset (GridVert b n)) {x : E}
    (hxA : x ∈ convexHull ℝ
      ((A.map (gridEvalEmb hn v hv) : Finset E) : Set E))
    (hxf : x ∈ convexHull ℝ (Set.range (fun i : Fin a => v (e i)))) :
    let F := A.filter (fun p => ∀ j : Fin b, j ∉ Set.range e → gu p j = 0)
    x ∈ convexHull ℝ ((F.map (gridEvalEmb hn v hv) : Finset E) : Set E) := by
  classical
  dsimp
  let L : (Fin b → ℝ) →ₗ[ℝ] E := gridEvalLinear v
  have lift (C : Finset (GridVert b n)) :
      convexHull ℝ ((C.map (gridEvalEmb hn v hv) : Finset E) : Set E) =
        L '' convexHull ℝ (gu '' (C : Set (GridVert b n))) := by
    have coe : ((C.map (gridEvalEmb hn v hv) : Finset E) : Set E) =
        L '' (gu '' (C : Set (GridVert b n))) := by
      rw [coe_gridEvalEmb_map hn v hv C]
      exact (Set.image_image L gu (C : Set (GridVert b n))).symm
    rw [coe]
    exact (L.image_convexHull _).symm
  rw [lift A] at hxA
  rcases hxA with ⟨u,hu,eu⟩
  have usimplex : u ∈ coeffSimplex b := by
    apply convexHull_min ?_ (convex_coeffSimplex b) hu
    intro w hw
    rcases hw with ⟨p,hp,rfl⟩
    exact gu_simplex hn p
  let hv' : AffineIndependent ℝ (fun i : Fin a => v (e i)) :=
    affineIndependent_comp_embedding e hv
  let xx : {z:E // z ∈ convexHull ℝ (Set.range (fun i : Fin a => v (e i)))} :=
    ⟨x,hxf⟩
  let r := ((simplexHomeo (fun i : Fin a => v (e i)) hv').symm xx :
    {u : Fin a → ℝ // u ∈ coeffSimplex a})
  have rr : simplexEval (fun i : Fin a => v (e i)) (r : Fin a → ℝ) = x := by
    exact congrArg Subtype.val
      ((simplexHomeo (fun i : Fin a => v (e i)) hv').apply_symm_apply xx)
  have rsum : (∑ i, (r : Fin a → ℝ) i) = 1 := r.property.2
  have esum : (∑ j : Fin b, zeroExtend e (r : Fin a → ℝ) j) = 1 := by
    rw [zeroExtend_sum]
    exact rsum
  have ueq : u = zeroExtend e (r : Fin a → ℝ) := by
    apply simplexEval_eq hv usimplex.2 esum
    have z : simplexEval v u = x := eu
    change simplexEval v u = x at z
    rw [simplexEval_zeroExtend]
    exact z.trans rr.symm
  have uoff : ∀ j : Fin b, j ∉ Set.range e → u j = 0 := by
    intro j hj
    rw [ueq]
    exact zeroExtend_not_mem e _ hj
  have uu := guHull_restrict_face hn e A hu uoff
  rw [lift]
  exact ⟨u, uu, eu⟩
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridSubfaceHull.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridSubfaceTransport.lean
section
open Set
namespace FamiliesProof
attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A chain and a point on its ordered subface can both be pulled back to that
subface. The mapped small chain is *literally* a subset of the original
ambient chain; retaining this is convenient when two faces are intersected. -/
lemma exists_chain_on_subface {a b n : ℕ} (hn : 0 < n)
    (ha : 0 < a) (e : Fin a ↪ Fin b) (he : StrictMono e)
    (v : Fin b → E) (hv : AffineIndependent ℝ v)
    (A : Finset (GridVert b n)) (hAc : A ∈ coeffChains b n)
    {x : E}
    (hxA : x ∈ convexHull ℝ
      ((A.map (gridEvalEmb hn v hv) : Finset E) : Set E))
    (hxf : x ∈ convexHull ℝ (Set.range (fun i : Fin a => v (e i)))) :
    ∃ B : Finset (GridVert a n),
      B ∈ coeffChains a n ∧
      B.map (gridEvalEmb hn (fun i => v (e i))
        (affineIndependent_comp_embedding e hv))
          ⊆ A.map (gridEvalEmb hn v hv) ∧
      x ∈ convexHull ℝ
        ((B.map (gridEvalEmb hn (fun i => v (e i))
          (affineIndependent_comp_embedding e hv)) : Finset E) : Set E) := by
  classical
  let F := A.filter (fun p => ∀ j : Fin b, j ∉ Set.range e → gu p j = 0)
  have Fsub : F ⊆ A := Finset.filter_subset _ _
  have Fc : F ∈ coeffChains b n := coeffChains_down hAc Fsub
  have Fzero : ∀ p ∈ F, ∀ j : Fin b, j ∉ Set.range e → gu p j = 0 := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have xF : x ∈ convexHull ℝ
      ((F.map (gridEvalEmb hn v hv) : Finset E) : Set E) :=
    gridHull_restrict_face hn ha e v hv A hxA hxf
  obtain ⟨B,hBc,eF⟩ := coeffChains_restrict_to_face hn e he F Fc Fzero
  refine ⟨B,hBc,?_,?_⟩
  · rw [← map_gridEvalEmb_gridZeroEmb hn e v hv B]
    rw [eF]
    exact Finset.map_subset_map.mpr Fsub
  · rw [← map_gridEvalEmb_gridZeroEmb hn e v hv B]
    rwa [eF]
end
end FamiliesProof
namespace FamiliesProof
open Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Any finite hull through a point has a nonempty support. -/
lemma nonempty_of_mem_hull_fin {t : Finset E} {x : E}
    (hx : x ∈ convexHull ℝ (t : Set E)) : t.Nonempty := by
  classical
  by_contra h
  have : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  subst t
  simpa [convexHull_empty] using hx
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/GridSubfaceTransport.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/MappedCompat.lean
section
open Set
open scoped BigOperators
namespace FamiliesProof
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- On one fixed pulling face it suffices to prove that the union of the two
(strictly positive) grid supports is an order chain. This is often the easy way to
reuse admissibility calculations: `map_inter` is literal for embeddings; it is not
a set-theoretic choice of preimages. -/
lemma mappedFace_inter_of_union {n : ℕ} (hn : 0 < n)
    (s t : Finset E) (ht : lexFace s t)
    (A B : Finset (GridVert (facePos s t).card n))
    (hU : A ∪ B ∈ coeffChains (facePos s t).card n) :
    let e := gridEvalEmb hn (inheritedFace s t) (inheritedFace_indep ht)
    convexHull ℝ ((A.map e : Finset E) : Set E) ∩
        convexHull ℝ ((B.map e : Finset E) : Set E) ⊆
      convexHull ℝ (((A.map e) ∩ (B.map e) : Finset E) : Set E) := by
  classical
  dsimp
  apply mappedSameFace_inter_of_coeff s t ht n hn A B
  exact coeffChains_inter_of_union hn A B hU
/-- A direct form useful after discarding zero coefficients in two convex
representations of an interior point. `near` is the delicate consequence of
positivity, so it is packaged in `chain_support_cross_near`; no equality of
prefix sums of naturals is required. -/
lemma near_for_same_weighted_vector
    {d n : ℕ} (hn : 0 < n)
    {A B : Finset (GridVert d n)} {w z : GridVert d n → ℝ}
    (hAc : A ∈ coeffChains d n) (hBc : B ∈ coeffChains d n)
    (hw : ∀ a ∈ A, 0 < w a) (hz : ∀ b ∈ B, 0 < z b)
    (hw1 : ∑ a ∈ A, w a = 1) (hz1 : ∑ b ∈ B, z b = 1)
    (vec : (∑ a ∈ A, w a • gu a) = (∑ b ∈ B, z b • gu b)) :
    ∀ p ∈ A, ∀ q ∈ B, gpNear p q ∧ gpNear q p := by
  classical
  apply chain_support_cross_near hAc hBc hw hz hw1 hz1
  intro m
  -- compare means in coordinate `m`; no division once `n` is cleared
  have same := sum_gp_eq_of_sum_gu vec m
  have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have rem (C : Finset (GridVert d n)) (f : GridVert d n → ℝ) :
      (∑ a ∈ C, f a * ((gp a m : ℝ) / (n : ℝ))) =
        (∑ a ∈ C, f a * (gp a m : ℝ)) / n := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [rem A w, rem B z] at same
  exact (div_left_inj' n0).mp same
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/MappedCompat.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/ChainUnion.lean
section
open Set
open scoped BigOperators
namespace FamiliesProof
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Positive barycentric representations of one coefficient point on two
Freudenthal chains have compatible supports.  Equivalently the support of
both representations is one chain again.  This is the common ordered-face
input in the intersection argument; no ambient geometry is involved.

The little argument is sometimes useful in this form.  Equality of the
vector gives equality of all prefix means.  `near_for_same_weighted_vector`
makes every pair of vertices differ by at most one on every prefix.  Were a
vertex `p` of the first chain and `q` of the second incomparable, there would
be two prefixes on which respectively `p=q+1` and `q=p+1`. On the first
chain, comparison with `p` says the indicators of these two increments can
never both be present; `p` has neither, giving strict inequality of their
average with one. On the second chain comparison with `q` says at least one
is present; `q` has both, giving strict opposite inequality. Prefix means and
masses identify the two averages, a contradiction. -/
lemma coeffChains_union_of_same_vector
    {d n : ℕ} (hn : 0 < n)
    {A B : Finset (GridVert d n)} {w z : GridVert d n → ℝ}
    (hAc : A ∈ coeffChains d n) (hBc : B ∈ coeffChains d n)
    (hw : ∀ a ∈ A, 0 < w a) (hz : ∀ b ∈ B, 0 < z b)
    (hw1 : ∑ a ∈ A, w a = 1) (hz1 : ∑ b ∈ B, z b = 1)
    (vec : (∑ a ∈ A, w a • gu a) = (∑ b ∈ B, z b • gu b)) :
    A ∪ B ∈ coeffChains d n := by
  classical
  have cross : ∀ p ∈ A, ∀ q ∈ B, gpNear p q ∧ gpNear q p :=
    near_for_same_weighted_vector hn hAc hBc hw hz hw1 hz1 vec
  have samegp (m : ℕ) :
      (∑ a ∈ A, w a * (gp a m : ℝ)) = ∑ b ∈ B, z b * (gp b m : ℝ) := by
    have same := sum_gp_eq_of_sum_gu vec m
    have n0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have rem (C : Finset (GridVert d n)) (f : GridVert d n → ℝ) :
        (∑ a ∈ C, f a * ((gp a m : ℝ) / (n : ℝ))) =
          (∑ a ∈ C, f a * (gp a m : ℝ)) / n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [rem A w, rem B z] at same
    exact (div_left_inj' n0).mp same
  have crossComp : ∀ p ∈ A, ∀ q ∈ B, gpLe p q ∨ gpLe q p := by
    intro p hp q hq
    by_cases hpq : gpLe p q
    · exact Or.inl hpq
    by_cases hqp : gpLe q p
    · exact Or.inr hqp
    exfalso
    have bad1 : ∃ m, gp q m < gp p m := by
      have bad : ¬ ∀ m : ℕ, gp p m ≤ gp q m := hpq
      rcases Classical.not_forall.mp bad with ⟨m,hm⟩
      exact ⟨m, lt_of_not_ge hm⟩
    have bad2 : ∃ m, gp p m < gp q m := by
      have bad : ¬ ∀ m : ℕ, gp q m ≤ gp p m := hqp
      rcases Classical.not_forall.mp bad with ⟨m,hm⟩
      exact ⟨m, lt_of_not_ge hm⟩
    obtain ⟨i,hi⟩ := bad1
    obtain ⟨j,hj⟩ := bad2
    have ne := cross p hp q hq
    have ei : gp p i = gp q i + 1 := by
      have le := ne.1 i
      omega
    have ej : gp q j = gp p j + 1 := by
      have le := ne.2 j
      omega
    let α : GridVert d n → ℝ := fun r => (gp p i : ℝ) - (gp r i : ℝ)
    let β : GridVert d n → ℝ := fun r => (gp r j : ℝ) - (gp p j : ℝ)
    have Abounds (r : GridVert d n) (hr : r ∈ A) :
        gp r i ≤ gp p i ∧ gp p i ≤ gp r i + 1 ∧
        gp p j ≤ gp r j ∧ gp r j ≤ gp p j + 1 := by
      have Aiup := (cross r hr q hq).1 i
      have Aidn := hAc.2 p hp r hr i
      have Ajdn := (cross r hr q hq).2 j
      have Ajup := hAc.2 r hr p hp j
      constructor
      · omega
      constructor
      · exact Aidn
      constructor
      · omega
      · exact Ajup
    have Bbounds (r : GridVert d n) (hr : r ∈ B) :
        gp r i ≤ gp p i ∧ gp p i ≤ gp r i + 1 ∧
        gp p j ≤ gp r j ∧ gp r j ≤ gp p j + 1 := by
      have Biup := hBc.2 r hr q hq i
      have Bidn := (cross p hp r hr).1 i
      have Bjdn := hBc.2 q hq r hr j
      have Bjup := (cross p hp r hr).2 j
      constructor
      · omega
      constructor
      · exact Bidn
      constructor
      · omega
      · exact Bjup
    have Aα0 (r : GridVert d n) (hr : r ∈ A) : 0 ≤ α r := by
      dsimp [α]
      have hu : (gp r i : ℝ) ≤ (gp p i : ℝ) := by
        exact_mod_cast (Abounds r hr).1
      linarith
    have Aα1 (r : GridVert d n) (hr : r ∈ A) : α r ≤ 1 := by
      dsimp [α]
      have hu : (gp p i : ℝ) ≤ (gp r i : ℝ) + 1 := by
        exact_mod_cast (Abounds r hr).2.1
      linarith
    have Aβ0 (r : GridVert d n) (hr : r ∈ A) : 0 ≤ β r := by
      dsimp [β]
      have hu : (gp p j : ℝ) ≤ (gp r j : ℝ) := by
        exact_mod_cast (Abounds r hr).2.2.1
      linarith
    have Aβ1 (r : GridVert d n) (hr : r ∈ A) : β r ≤ 1 := by
      dsimp [β]
      have hu : (gp r j : ℝ) ≤ (gp p j : ℝ) + 1 := by
        exact_mod_cast (Abounds r hr).2.2.2
      linarith
    have Bα0 (r : GridVert d n) (hr : r ∈ B) : 0 ≤ α r := by
      dsimp [α]
      have hu : (gp r i : ℝ) ≤ (gp p i : ℝ) := by
        exact_mod_cast (Bbounds r hr).1
      linarith
    have Bα1 (r : GridVert d n) (hr : r ∈ B) : α r ≤ 1 := by
      dsimp [α]
      have hu : (gp p i : ℝ) ≤ (gp r i : ℝ) + 1 := by
        exact_mod_cast (Bbounds r hr).2.1
      linarith
    have Bβ0 (r : GridVert d n) (hr : r ∈ B) : 0 ≤ β r := by
      dsimp [β]
      have hu : (gp p j : ℝ) ≤ (gp r j : ℝ) := by
        exact_mod_cast (Bbounds r hr).2.2.1
      linarith
    have Bβ1 (r : GridVert d n) (hr : r ∈ B) : β r ≤ 1 := by
      dsimp [β]
      have hu : (gp r j : ℝ) ≤ (gp p j : ℝ) + 1 := by
        exact_mod_cast (Bbounds r hr).2.2.2
      linarith
    have Ale1 (r : GridVert d n) (hr : r ∈ A) : α r + β r ≤ 1 := by
      rcases hAc.1 r hr p hp with ord | ord
      · have le' : (gp r j : ℝ) ≤ (gp p j : ℝ) := by
          exact_mod_cast (ord j)
        have b0 : β r ≤ 0 := by dsimp [β]; linarith
        linarith [Aα1 r hr, Aβ0 r hr]
      · have le' : (gp p i : ℝ) ≤ (gp r i : ℝ) := by
          exact_mod_cast (ord i)
        have a0 : α r ≤ 0 := by dsimp [α]; linarith
        linarith [Aα0 r hr, Aβ1 r hr]
    have Bge1 (r : GridVert d n) (hr : r ∈ B) :
        1 ≤ α r + β r := by
      rcases hBc.1 r hr q hq with ord | ord
      · have le' : (gp r i : ℝ) ≤ (gp q i : ℝ) := by
          exact_mod_cast (ord i)
        have eit : (gp p i : ℝ) = (gp q i : ℝ) + 1 := by
          exact_mod_cast ei
        have a1 : (1:ℝ) ≤ α r := by dsimp [α]; linarith
        linarith [Bβ0 r hr]
      · have le' : (gp q j : ℝ) ≤ (gp r j : ℝ) := by
          exact_mod_cast (ord j)
        have ejt : (gp q j : ℝ) = (gp p j : ℝ) + 1 := by
          exact_mod_cast ej
        have b1 : (1:ℝ) ≤ β r := by dsimp [β]; linarith
        linarith [Bα0 r hr]
    have Ap0 : α p = 0 := by dsimp [α]; ring
    have Bp0 : β p = 0 := by dsimp [β]; ring
    have Aq1 : α q = 1 := by
      dsimp [α]
      have eit : (gp p i : ℝ) = (gp q i : ℝ) + 1 := by
        exact_mod_cast ei
      linarith
    have Bq1 : β q = 1 := by
      dsimp [β]
      have ejt : (gp q j : ℝ) = (gp p j : ℝ) + 1 := by
        exact_mod_cast ej
      linarith
    have Asumlt :
        (∑ r ∈ A, w r * (α r + β r)) <
          ∑ r ∈ A, w r * (1:ℝ) := by
      apply Finset.sum_lt_sum
      · intro r hr
        have hh := Ale1 r hr
        have ww := le_of_lt (hw r hr)
        nlinarith
      · refine ⟨p, hp, ?_⟩
        rw [Ap0, Bp0]
        have ww := hw p hp
        norm_num
        linarith
    have Bsumlt :
        (∑ r ∈ B, z r * (1:ℝ)) <
          ∑ r ∈ B, z r * (α r + β r) := by
      apply Finset.sum_lt_sum
      · intro r hr
        have hh := Bge1 r hr
        have ww := le_of_lt (hz r hr)
        nlinarith
      · refine ⟨q, hq, ?_⟩
        rw [Aq1, Bq1]
        have zz := hz q hq
        norm_num
        linarith
    have Asumlt' : (∑ r ∈ A, w r * (α r + β r)) < 1 := by
      simpa [hw1] using Asumlt
    have Bsumlt' : (1:ℝ) < (∑ r ∈ B, z r * (α r + β r)) := by
      simpa [hz1] using Bsumlt
    have eqsum :
        (∑ r ∈ A, w r * (α r + β r)) =
          ∑ r ∈ B, z r * (α r + β r) := by
      dsimp [α, β]
      have gp_i := samegp i
      have gp_j := samegp j
      -- expand the affine expression, then prefixes and masses identify it
      have form (C : Finset (GridVert d n)) (f : GridVert d n → ℝ) :
          (∑ r ∈ C, f r *
            (((gp p i : ℝ) - (gp r i : ℝ)) +
             ((gp r j : ℝ) - (gp p j : ℝ)))) =
            (gp p i : ℝ) * (∑ r ∈ C, f r) -
              (∑ r ∈ C, f r * (gp r i : ℝ)) +
              (∑ r ∈ C, f r * (gp r j : ℝ)) -
              (gp p j : ℝ) * (∑ r ∈ C, f r) := by
        classical
        -- sums distribute over the four summands
        simp only [mul_add, mul_sub, Finset.sum_add_distrib,
          Finset.sum_sub_distrib]
        -- each sum of the constant factors is a product with the mass
        rw [show (∑ r ∈ C, f r * (gp p i : ℝ)) =
              (gp p i : ℝ) * (∑ r ∈ C, f r) by
                simpa [mul_comm] using (Finset.mul_sum C f (gp p i : ℝ)).symm]
        rw [show (∑ r ∈ C, f r * (gp p j : ℝ)) =
              (gp p j : ℝ) * (∑ r ∈ C, f r) by
                simpa [mul_comm] using (Finset.mul_sum C f (gp p j : ℝ)).symm]
        ring
      rw [form A w, form B z]
      rw [hw1, hz1, gp_i, gp_j]
    linarith
  refine ⟨?_, ?_⟩
  · intro p hp q hq
    rcases Finset.mem_union.mp hp with hpa | hpb
    · rcases Finset.mem_union.mp hq with hqa | hqb
      · exact hAc.1 p hpa q hqa
      · exact crossComp p hpa q hqb
    · rcases Finset.mem_union.mp hq with hqa | hqb
      · rcases crossComp q hqa p hpb with h | h
        · exact Or.inr h
        · exact Or.inl h
      · exact hBc.1 p hpb q hqb
  · intro p hp q hq
    rcases Finset.mem_union.mp hp with hpa | hpb
    · rcases Finset.mem_union.mp hq with hqa | hqb
      · exact hAc.2 p hpa q hqa
      · exact (cross p hpa q hqb).1
    · rcases Finset.mem_union.mp hq with hqa | hqb
      · exact (cross q hqa p hpb).2
      · exact hBc.2 p hpb q hqb
end
end FamiliesProof
namespace FamiliesProof
open Set
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
/-- Any point in a finite grid hull has a representation with every retained
coefficient strictly positive.  Passing to the retained support is important:
`coeffChains_union_of_same_vector` works on positive chains. -/
lemma coeff_hull_positive_support {d n : ℕ} (hn : 0 < n)
    {A : Finset (GridVert d n)} {u : Fin d → ℝ}
    (hu : u ∈ convexHull ℝ (gu '' (A : Set (GridVert d n)))) :
    ∃ (A' : Finset (GridVert d n)) (w : GridVert d n → ℝ),
      A' ⊆ A ∧
      (∀ a ∈ A', 0 < w a) ∧
      (∑ a ∈ A', w a = 1) ∧
      (∑ a ∈ A', w a • gu a = u) := by
  classical
  let e : GridVert d n ↪ (Fin d → ℝ) := ⟨gu, gu_inj hn⟩
  have eset : (((A.map e) : Finset (Fin d → ℝ)) : Set (Fin d → ℝ)) =
      gu '' (A : Set (GridVert d n)) := by
    simpa [e] using (Finset.coe_map e A)
  have hu' : u ∈ convexHull ℝ
      (((A.map e) : Finset (Fin d → ℝ)) : Set (Fin d → ℝ)) := by
    simpa [eset] using hu
  rcases (Finset.mem_convexHull' (R:=ℝ)).mp hu' with ⟨w', h0, h1, hvec⟩
  let w : GridVert d n → ℝ := fun a => w' (gu a)
  let A' : Finset (GridVert d n) := A.filter (fun a => w a ≠ 0)
  have hA' : A' ⊆ A := Finset.filter_subset _ _
  have hp : ∀ a ∈ A', 0 < w a := by
    intro a ha
    have haA : a ∈ A := hA' ha
    have hnz : w a ≠ 0 := (Finset.mem_filter.mp ha).2
    have haM : (gu a) ∈ (A.map e : Finset (Fin d → ℝ)) := by
      exact Finset.mem_map.mpr ⟨a, haA, rfl⟩
    have hz := h0 (gu a) haM
    dsimp [w] at hz hnz ⊢
    exact lt_of_le_of_ne hz (Ne.symm hnz)
  have hmassA : (∑ a ∈ A, w a) = 1 := by
    classical
    simpa [w, e] using h1
  have hvecA : (∑ a ∈ A, w a • gu a) = u := by
    classical
    simpa [w, e] using hvec
  have filt (F : GridVert d n → (Fin d → ℝ))
      (hzero : ∀ a ∈ A, w a = 0 → F a = 0) :
      (∑ a ∈ A', F a) = ∑ a ∈ A, F a := by
    classical
    dsimp [A']
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : w a = 0
    · simp [h, hzero a ha h]
    · simp [h]
  have filtR (F : GridVert d n → ℝ)
      (hzero : ∀ a ∈ A, w a = 0 → F a = 0) :
      (∑ a ∈ A', F a) = ∑ a ∈ A, F a := by
    classical
    dsimp [A']
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : w a = 0
    · simp [h, hzero a ha h]
    · simp [h]
  refine ⟨A', w, hA', hp, ?_, ?_⟩
  · have : (∑ a∈A', w a) = ∑ a ∈ A, w a := filtR w (by intros; assumption)
    simpa [hmassA] using this
  · have : (∑ a ∈ A', w a • gu a) = ∑ a∈A, w a • gu a := by
      apply filt
      intro a ha hz
      simp [hz]
    simpa [hvecA] using this
end
end FamiliesProof
namespace FamiliesProof
open Set
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
private lemma __ChainUnion_coeff_mem_hull_of_weights {d n : ℕ}
    {S : Finset (GridVert d n)} {u : Fin d → ℝ}
    (w : GridVert d n → ℝ) (hpos : ∀ a ∈ S, 0 < w a)
    (h1 : ∑ a∈S, w a = 1)
    (hv : ∑ a∈S, w a • gu a = u) :
    u ∈ convexHull ℝ (gu '' (S : Set (GridVert d n))) := by
  classical
  refine mem_convexHull_of_exists_fintype (ι:= S)
    (fun a : S => w a)
    (fun a : S => gu (a : GridVert d n)) ?_ ?_ ?_ ?_
  · intro i; exact le_of_lt (hpos i (by simpa using i.property))
  · -- subtype and attached sum have the same terms
    calc
      (∑ i : S, w (i : GridVert d n)) =
          ∑ i ∈ S.attach, w (i : GridVert d n) := by
            have hatt : (S.attach : Finset S) = Finset.univ := by ext; simp
            rw [hatt]
      _ = ∑ i ∈ S, w i := Finset.sum_attach S w
      _ = 1 := h1
  · intro i
    refine ⟨i, i.property, rfl⟩
  · calc
      (∑ i : S, w (i : GridVert d n) • gu (i : GridVert d n)) =
          ∑ i ∈ S.attach, w (i : GridVert d n) • gu (i : GridVert d n) := by
            have hatt : (S.attach : Finset S) = Finset.univ := by ext; simp
            rw [hatt]
      _ = ∑ i ∈ S, w i • gu i :=
        Finset.sum_attach S (fun i => w i • gu i)
      _ = u := hv

/-- The coefficient-chain simplices form a genuine complex, in particular
pairwise intersections are their common-vertex hull.  The previous lemma on
positive supports is the boundary-case input: after throwing away zero
coefficients the two supports must already be one chain. -/
lemma coeffChains_inter {d n : ℕ} (hn : 0 < n)
    {A B : Finset (GridVert d n)}
    (hA : A ∈ coeffChains d n) (hB : B ∈ coeffChains d n) :
    convexHull ℝ (gu '' (A : Set (GridVert d n))) ∩
        convexHull ℝ (gu '' (B : Set (GridVert d n))) ⊆
      convexHull ℝ (gu '' ((↑(A ∩ B)) : Set (GridVert d n))) := by
  classical
  intro u hu
  obtain ⟨A', w, hA'sub, hwpos, hw1, hwv⟩ :=
    coeff_hull_positive_support hn hu.1
  obtain ⟨B', z, hB'sub, hzpos, hz1, hzv⟩ :=
    coeff_hull_positive_support hn hu.2
  have hA'c : A' ∈ coeffChains d n := coeffChains_down hA hA'sub
  have hB'c : B' ∈ coeffChains d n := coeffChains_down hB hB'sub
  have hU : A' ∪ B' ∈ coeffChains d n :=
    coeffChains_union_of_same_vector hn hA'c hB'c hwpos hzpos hw1 hz1 (hwv.trans hzv.symm)
  have huA' : u ∈ convexHull ℝ (gu '' (A' : Set (GridVert d n))) :=
    __ChainUnion_coeff_mem_hull_of_weights w hwpos hw1 hwv
  have huB' : u ∈ convexHull ℝ (gu '' (B' : Set (GridVert d n))) :=
    __ChainUnion_coeff_mem_hull_of_weights z hzpos hz1 hzv
  have hi' : u ∈ convexHull ℝ (gu '' ((↑(A' ∩ B')) : Set (GridVert d n))) :=
    coeffChains_inter_of_union hn A' B' hU ⟨huA', huB'⟩
  refine convexHull_mono ?_ hi'
  rintro y ⟨a, ha, rfl⟩
  have ha' : a ∈ (A' ∩ B') := ha
  refine ⟨a, ?_, rfl⟩
  have haa : a ∈ A' := (Finset.mem_inter.mp ha').1
  have hbb : a ∈ B' := (Finset.mem_inter.mp ha').2
  exact Finset.mem_inter.mpr ⟨hA'sub haa, hB'sub hbb⟩
end
end FamiliesProof
namespace FamiliesProof
open Set
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Same ordered face, no positive-support choices required in the statement.
Use `coeffChains_inter` on that face and lift through the independent
`gridEvalEmb`. -/
lemma mappedFace_inter {n : ℕ} (hn : 0 < n)
    (s t : Finset E) (ht : lexFace s t)
    {A B : Finset (GridVert (facePos s t).card n)}
    (hA : A ∈ coeffChains (facePos s t).card n)
    (hB : B ∈ coeffChains (facePos s t).card n) :
    let e := gridEvalEmb hn (inheritedFace s t) (inheritedFace_indep ht)
    convexHull ℝ ((A.map e : Finset E) : Set E) ∩
      convexHull ℝ ((B.map e : Finset E) : Set E) ⊆
    convexHull ℝ (((A.map e) ∩ (B.map e) : Finset E) : Set E) := by
  classical
  dsimp
  exact mappedSameFace_inter_of_coeff s t ht n hn A B
    (coeffChains_inter hn hA hB)
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/ChainUnion.lean

-- BEGIN INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/CrossFaceInter.lean
section
open Set Geometry
open scoped BigOperators Topology
namespace FamiliesProof
attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The pulled grid chains over all faces glue as a complex.  When two
chains start on different pulling faces, first restrict both through the
intersection pulling face using zero barycentric coordinates there; on that
common ordered face it is the usual coefficient-chain compatibility. -/
lemma mappedChains_inter_all (s : Finset E) (n : ℕ) (hn : 0 < n) :
    ∀ D ∈ mappedChains s n hn, ∀ B ∈ mappedChains s n hn,
      convexHull ℝ (D : Set E) ∩ convexHull ℝ (B : Set E) ⊆
        convexHull ℝ ((D : Set E) ∩ (B : Set E)) := by
  classical
  intro D hD B hB
  rcases hD with ⟨t, ht, A, hAc, rfl⟩
  rcases hB with ⟨u, hu, C, hCc, rfl⟩
  intro x hx
  have xt : x ∈ convexHull ℝ (t : Set E) := by
    have m := (gridHull_subset_face hn (inheritedFace s t)
      (inheritedFace_indep ht) A) hx.1
    simpa [range_inheritedFace ht.1] using m
  have xu : x ∈ convexHull ℝ (u : Set E) := by
    have m := (gridHull_subset_face hn (inheritedFace s u)
      (inheritedFace_indep hu) C) hx.2
    simpa [range_inheritedFace hu.1] using m
  let w : Finset E := t ∩ u
  have xw : x ∈ convexHull ℝ (w : Set E) := by
    have m := lexFace_inter ht hu ⟨xt, xu⟩
    simpa [w] using m
  have wne : w.Nonempty := nonempty_of_mem_hull_fin xw
  have wsubt : w ⊆ t := by intro y hy; exact (Finset.mem_inter.mp hy).1
  have wsubu : w ⊆ u := by intro y hy; exact (Finset.mem_inter.mp hy).2
  have hw : lexFace s w := lexFace_down ht wsubt
  have apos : 0 < (facePos s w).card := by
    rw [facePos_card hw.1]
    exact Finset.card_pos.mpr wne
  obtain ⟨et, etmono, eteq⟩ := exists_inheritedFace_embedding s t w wsubt
  obtain ⟨er, ermono, ereq⟩ := exists_inheritedFace_embedding s u w wsubu
  have xwt : x ∈ convexHull ℝ
      (Set.range (fun i : Fin (facePos s w).card => inheritedFace s t (et i))) := by
    have funEq : (fun i : Fin (facePos s w).card => inheritedFace s t (et i)) =
        inheritedFace s w := funext eteq
    rw [funEq, range_inheritedFace hw.1]
    exact xw
  have xwu : x ∈ convexHull ℝ
      (Set.range (fun i : Fin (facePos s w).card => inheritedFace s u (er i))) := by
    have funEq : (fun i : Fin (facePos s w).card => inheritedFace s u (er i)) =
        inheritedFace s w := funext ereq
    rw [funEq, range_inheritedFace hw.1]
    exact xw
  obtain ⟨At, hAtc, hAtsub, xAt⟩ :=
    exists_chain_on_subface hn apos et etmono (inheritedFace s t)
      (inheritedFace_indep ht) A hAc hx.1 xwt
  obtain ⟨Cu, hCuc, hCusub, xCu⟩ :=
    exists_chain_on_subface hn apos er ermono (inheritedFace s u)
      (inheritedFace_indep hu) C hCc hx.2 xwu
  have funEt : (fun i : Fin (facePos s w).card => inheritedFace s t (et i)) =
      inheritedFace s w := funext eteq
  have funEr : (fun i : Fin (facePos s w).card => inheritedFace s u (er i)) =
      inheritedFace s w := funext ereq
  -- normalize the two small embeddings to the inherited one of `w`
  have subAt : At.map (gridEvalEmb hn (inheritedFace s w)
        (inheritedFace_indep hw)) ⊆
       A.map (gridEvalEmb hn (inheritedFace s t) (inheritedFace_indep ht)) := by
    simpa [funEt] using hAtsub
  have inAt : x ∈ convexHull ℝ
      ((At.map (gridEvalEmb hn (inheritedFace s w)
        (inheritedFace_indep hw)) : Finset E) : Set E) := by
    simpa [funEt] using xAt
  have subCu : Cu.map (gridEvalEmb hn (inheritedFace s w)
        (inheritedFace_indep hw)) ⊆
       C.map (gridEvalEmb hn (inheritedFace s u) (inheritedFace_indep hu)) := by
    simpa [funEr] using hCusub
  have inCu : x ∈ convexHull ℝ
      ((Cu.map (gridEvalEmb hn (inheritedFace s w)
        (inheritedFace_indep hw)) : Finset E) : Set E) := by
    simpa [funEr] using xCu
  have intersmall : x ∈ convexHull ℝ
      (((At.map (gridEvalEmb hn (inheritedFace s w)
          (inheritedFace_indep hw))) ∩
        (Cu.map (gridEvalEmb hn (inheritedFace s w)
          (inheritedFace_indep hw))) : Finset E) : Set E) :=
    (mappedFace_inter hn s w hw hAtc hCuc) ⟨inAt, inCu⟩
  -- the common vertices retained in the small chains are vertices of both
  -- original cells.
  refine convexHull_mono ?_ intersmall
  intro z hz
  have hz' : z ∈ (At.map (gridEvalEmb hn (inheritedFace s w)
          (inheritedFace_indep hw)) ∩
        Cu.map (gridEvalEmb hn (inheritedFace s w)
          (inheritedFace_indep hw)) : Finset E) := hz
  have hza := subAt (Finset.mem_inter.mp hz').1
  have hzc := subCu (Finset.mem_inter.mp hz').2
  exact ⟨hza, hzc⟩
end
end FamiliesProof

end
-- END INLINED FILE: Mathlib/Support/families_of_maps_b01_acadb87e4b/CrossFaceInter.lean

namespace Submission

open _root_.FamiliesOfMapsB01
open _root_.FamiliesOfMapsB01.Subdivision

-- BEGIN INLINED MAIN PRELUDE

set_option maxHeartbeats 12000000
/-!
# Adapting families of maps to open covers (Morrison–Walker, *The Blob Complex*)

# Adapting families of maps to open covers (Morrison–Walker, *The Blob Complex*)

Lemma B.0.1 of Morrison and Walker, *The Blob Complex* (arXiv:1009.5025,
Appendix B, pp. 93–96): <https://arxiv.org/pdf/1009.5025>.

Given a continuous family `f : P × X → T` parametrised by a convex linear
polyhedron `P ⊆ ℝᵏ` and a partition of unity subordinate to an open cover
`U` of a compact space `X`, the lemma produces a homotopy `F` from `f` to
a family that is *adapted* to `U` on each closed cell of a polyhedral
subdivision of `P`, with support preserved both absolutely and along
boundary subpolyhedra.

Two holes:

* `FamiliesOfMapsB01.continuous` — the continuous case (clauses 1–3 of
  the paper). The polyhedral-subdivision conclusion is what makes
  Lemma B.0.2 (the chain-level deformation retract) a chain-complex
  consequence: each closed cell is a generator of `C∗(Maps(X → T))` and
  adjacent cells share `(k−1)`-faces with cancelling orientations.

* `FamiliesOfMapsB01.biLipschitz` — the bi-Lipschitz variant of clause 4.
  Each slice `f (p, ·)` is bundled as a homeomorphism `X ≃ₜ T` (so
  surjectivity is part of the data), the paper's joint Lipschitz
  hypothesis ("`f` is Lipschitz in the `P` direction as well") is
  imposed via `LipschitzWith L f.toFun`, and the conclusion produces the
  same bundled bi-Lipschitz homeomorphism structure on every slice
  `F (t, p, ·)`.

The smooth-diffeomorphism / immersion / PL variants are omitted. The
paper does *not* prove the analogous statement for plain (merely
continuous) homeomorphisms, and we do not state it.

The trusted supporting definitions (`Supported`, `AdaptedTo`,
`IsPolyhedron`, `Subdivision`, `closedCell`, `IsBoundarySubpolyhedron`)
are factored into `ChallengeDeps.lean` automatically by the multi-hole
generator.

This statement was corrected on 2026-06-14: the original
`IsBoundarySubpolyhedron` admitted any convex hull of frontier points,
including single non-vertex points of `∂P`, for which condition 4's
support hypothesis is vacuous and spuriously forced the homotopy to
freeze those points in time — making the lemma false. Lorenzo Luccioli,
using Harmonic's Aristotle, gave a formal disproof. The repair restricts
boundary subpolyhedra to genuine faces of `P` (`IsExtreme ℝ P`), matching
the paper's "convex linear subpolyhedron of `∂P`". Thanks to both.
-/

open Set unitInterval Geometry
open scoped Topology

namespace FamiliesOfMapsB01

variable {k : ℕ} {ι X T : Type*}
  [TopologicalSpace X] [TopologicalSpace T]













/-- **Lemma B.0.1** of Morrison–Walker, *The Blob Complex*
(arXiv:1009.5025, §B), continuous case. -/
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

/-ResultBegin-/
theorem continuous
    {P : Set (Fin k → ℝ)} (_hP : IsPolyhedron P)
    [CompactSpace X]
    (U : ι → Set X) (_hUopen : ∀ α, IsOpen (U α))
    (ρ : PartitionOfUnity ι X univ) (_hρ : ρ.IsSubordinate U)
    (f : C(P × X, T)) :
    ∃ F : C(I × P × X, T),
      (∀ p : P, ∀ x : X, F (0, p, x) = f (p, x)) ∧
      (∃ K : Subdivision P,
         ∀ D ∈ K.complex.facets,
            AdaptedTo U k
              (fun q : closedCell P D × X => F (1, q.1.1, q.2))) ∧
      (∀ S : Set X, Supported (f := f.toFun) S →
          Supported (fun q : (I × P) × X => F (q.1.1, q.1.2, q.2)) S) ∧
      (∀ Q : Set P, IsBoundarySubpolyhedron Q →
        ∀ S' : Set X,
          Supported (fun q : Q × X => f (q.1.1, q.2)) S' →
            Supported (fun q : (I × Q) × X => F (q.1.1, q.1.2.1, q.2)) S') :=
/-ResultProofBegin-/ by
  classical
  -- The construction is a motion of the compact parameter polytope.  All
  -- uses of the target family below are by precomposition; this isolates the
  -- geometric content.
  have hmotion :
      ∃ (G : C(I × P × X, P)) (K : Subdivision P),
        (∀ p : P, ∀ x : X, G (0, p, x) = p) ∧
        (∀ D ∈ K.complex.facets,
           ∃ A : Finset ι, A.card ≤ k ∧
             ∀ p p' : closedCell P D, ∀ x : X,
               x ∉ (⋃ α ∈ A, U α) →
                 G (1, p.1, x) = G (1, p'.1, x)) ∧
        (∀ Q : Set P, IsBoundarySubpolyhedron Q →
           ∀ t : I, ∀ p : P, p ∈ Q → ∀ x : X,
             G (t, p, x) ∈ Q) := by
    by_cases hnon : Nontrivial P
    · -- The nontrivial polytope has a couple of useful genuine terminal
      -- cases as well.  They are stated using honest mathlib complexes.
      letI : Nontrivial P := hnon
      have hk : k ≠ 0 := by
        intro hz
        subst k
        have hs : Subsingleton P := by
          constructor
          intro p q
          apply Subtype.ext
          funext i
          exact Fin.elim0 i
        exact not_subsingleton_iff_nontrivial.mpr hnon hs
      have simplex_tri :
          (∃ s : Finset (Fin k → ℝ),
              P = convexHull ℝ (s : Set _) ∧
                AffineIndependent ℝ ((↑) : s → (Fin k → ℝ))) →
            Nonempty (Subdivision P) := by
        rintro ⟨s, hsP, hsi⟩
        have hsne' : (convexHull ℝ (s : Set (Fin k → ℝ))).Nonempty := by
          let p : P := Classical.choice (inferInstance : Nonempty P)
          exact ⟨(p : Fin k → ℝ), hsP ▸ p.property⟩
        have hsne : s.Nonempty := by
          have hh : (s : Set (Fin k → ℝ)).Nonempty :=
            convexHull_nonempty_iff.mp hsne'
          simpa using hh
        exact ⟨{
          complex := FamiliesProof.fullSimplex s hsi
          faces_finite := FamiliesProof.fullSimplex_faces_finite s hsi
          space_eq := (FamiliesProof.fullSimplex_space s hsi hsne).trans hsP.symm }⟩
      -- Before any motion is attempted there is a rather elementary but
      -- important reduction on the polyhedral side.  Points of the finite
      -- presentation which already lie in the hull of the other points need
      -- not be triangulated at all.  Keeping this data on hand prevents that
      -- artefactual degeneracy from being confused with the real gluing
      -- issue for polytopes in convex position.
      obtain ⟨s₀, hs₀⟩ := _hP
      obtain ⟨v, hvs, hvhull, hvvertex⟩ :=
        FamiliesProof.finiteHull_reduce (E := (Fin k → ℝ)) s₀
      have hvP : P = convexHull ℝ (v : Set (Fin k → ℝ)) :=
        hs₀.trans hvhull.symm
      -- The pulling rule has now supplied the missing *geometric-complex*
      -- input.  This is substantially stronger than the Caratheodory cover
      -- below: selected coefficient supports meet in their common face.
      -- Thus every finite hull, even with dependent vertices, has an
      -- honest mathlib subdivision.
      have full_triangulation : Nonempty (Subdivision P) := by
        obtain ⟨L, hfin, hspace⟩ :=
          FamiliesProof.exists_finiteComplex_convexHull
            (E := (Fin k → ℝ)) v
        exact ⟨{ complex := L,
                 faces_finite := hfin,
                 space_eq := hspace.trans hvP.symm }⟩
      have vertices_simplex
          (hi : AffineIndependent ℝ ((↑) : v → (Fin k → ℝ))) :
          Nonempty (Subdivision P) :=
        simplex_tri ⟨v, hvP, hi⟩
      -- Explicit universal reduction for possible later triangulation
      -- input.  The only genuinely missing finite-hull theorem may be
      -- stated for configurations none of whose vertices is in the hull of
      -- the rest; erasing an interior listed point preserves the hull.  This
      -- is stronger than assuming the given presenting set itself is
      -- independent.
      have subdivision_of_convexPosition
          (H : ∀ s : Finset (Fin k → ℝ),
            (∀ w ∈ s, w ∉ convexHull ℝ
              ((s.erase w : Finset (Fin k → ℝ)) : Set (Fin k → ℝ))) →
            ∃ L : SimplicialComplex ℝ (Fin k → ℝ),
              L.faces.Finite ∧
                L.space = convexHull ℝ (s : Set (Fin k → ℝ))) :
          Nonempty (Subdivision P) := by
        obtain ⟨L, hfin, hspace⟩ :=
          FamiliesProof.finiteHull_reduction_to_convexPosition
            (E := (Fin k → ℝ)) H s₀
        exact ⟨{ complex := L,
                 faces_finite := hfin,
                 space_eq := hspace.trans hs₀.symm }⟩
      have candidate_finite :
          (FamiliesProof.candidateFaces (E := (Fin k → ℝ)) v).Finite :=
        FamiliesProof.candidateFaces_finite v
      -- Carathéodory supplies a genuine finite cover by independent
      -- simplices, even when the vertices of the hull are dependent.  Of
      -- course this cover is not yet a *geometric complex*: two of these
      -- larger simplexes can meet in a diagonal.  The next equalities are
      -- often the most useful input for a later gluing/refinement argument.
      have candidate_cover :
          (⋃ w ∈ FamiliesProof.candidateFaces (E := (Fin k → ℝ)) v,
              convexHull ℝ (w : Set (Fin k → ℝ))) = P :=
        (FamiliesProof.iUnion_candidateFaces v).trans hvP.symm
      have candidate_lower :
          ∀ {a b : Finset (Fin k → ℝ)},
            a ∈ FamiliesProof.candidateFaces (E := (Fin k → ℝ)) v →
            b ⊆ a → b.Nonempty →
              b ∈ FamiliesProof.candidateFaces (E := (Fin k → ℝ)) v := by
        intro a b ha hb hn
        exact FamiliesProof.candidateFaces_down ha hb hn
      -- Compactness does give an honest finite *open* subcover; one
      -- still has to make the number of varying colours on each cell at
      -- most `k` by moving vertices.  This lemma is independent of any
      -- nonexistent triangulation API.
      have cover_fin : ∃ B : Finset ι,
          (Set.univ : Set X) ⊆ ⋃ α ∈ B, U α := by
        have hcover : (Set.univ : Set X) ⊆ ⋃ α, U α := by
          intro x hx
          obtain ⟨i, hi⟩ := ρ.exists_pos hx
          have hn : ρ i x ≠ 0 := ne_of_gt hi
          have ht : x ∈ tsupport (ρ i) :=
            subset_tsupport _ (by
              change x ∈ Function.support (ρ i)
              exact hn)
          have hu : x ∈ U i := _hρ i ht
          exact Set.mem_iUnion.mpr ⟨i, hu⟩
        exact isCompact_univ.elim_finite_subcover U _hUopen hcover
      by_cases ready : Nonempty (Subdivision P) ∧
          ∃ A : Finset ι, A.card ≤ k ∧
            (Set.univ : Set X) ⊆ ⋃ α ∈ A, U α
      · rcases ready with ⟨⟨K⟩, A, hA, hcov⟩
        let G : C(I × P × X, P) :=
          { toFun := fun z => z.2.1
            continuous_toFun := continuous_fst.comp continuous_snd }
        refine ⟨G, K, ?_, ?_, ?_⟩
        · intro p x
          rfl
        · intro D hD
          refine ⟨A, hA, ?_⟩
          intro p p' x hx
          have h : x ∈ (⋃ α ∈ A, U α) := hcov (by trivial)
          exact (hx h).elim
        · intro Q hQ t p hp x
          -- a stationary motion fixes every face
          change p ∈ Q
          exact hp
      · -- all that remains is the moving-vertices construction.  In
        -- particular, if the hull is an independent simplex then
        -- `simplex_tri` above supplies the missing subdivision; so any
        -- obstruction here is a real large-cover obstruction, not a
        -- nonexistent import for the empty complex. We make that reduction
        -- explicit; it is a useful strong induction hypothesis for a later
        -- triangulation of finite convex hulls.
        have hull_obstruction (hnt : ¬ Nonempty (Subdivision P)) :
            ¬ AffineIndependent ℝ ((↑) : v → (Fin k → ℝ)) := by
          intro hi
          exact hnt (vertices_simplex hi)
        have blocked :
            (¬ ∃ A : Finset ι, A.card ≤ k ∧
                (Set.univ : Set X) ⊆ ⋃ α ∈ A, U α) ∨
              ¬ AffineIndependent ℝ ((↑) : v → (Fin k → ℝ)) := by
          classical
          by_cases hcov : ∃ A : Finset ι, A.card ≤ k ∧
                (Set.univ : Set X) ⊆ ⋃ α ∈ A, U α
          · right
            intro hsi
            exact ready ⟨vertices_simplex hsi, hcov⟩
          · exact Or.inl hcov
        obtain ⟨B, hB⟩ := cover_fin
        have alternative :
            (¬ Nonempty (Subdivision P)) ∨
              (∀ A : Finset ι, A.card ≤ k →
                ¬ (Set.univ : Set X) ⊆ ⋃ α ∈ A, U α) := by
          classical
          by_cases htri : Nonempty (Subdivision P)
          · right
            intro A hA hc
            exact ready ⟨htri, ⟨A, hA, hc⟩⟩
          · exact Or.inl htri
        -- In particular it is no longer the first disjunct above: the pulling
        -- complex gives a genuine subdivision without any independence
        -- assumption on the presented vertices.
        have no_small_cover :
            ∀ A : Finset ι, A.card ≤ k →
              ¬ (Set.univ : Set X) ⊆ ⋃ α ∈ A, U α := by
          intro A hA hcov
          exact ready ⟨full_triangulation, ⟨A, hA, hcov⟩⟩
        have large_cover (htri : Nonempty (Subdivision P)) : k < B.card := by
          exact Nat.lt_of_not_ge (fun h => no_small_cover B h hB)
        -- With intersection and coverage of the pulling faces discharged, the
        -- remaining statement is precisely the moving-colours construction.
        -- Unlike the old finite-hull cover this branch now always has a fixed
        -- finite geometric base complex.
        -- It is useful to separate off the elementary (and slightly
        -- fiddly) topological part of the argument.  There is no regularity
        -- requirement on the motion in the parameter direction: once an
        -- endpoint, with the required face condition, has been built, the
        -- straight segment from `p` to that endpoint is the required motion.
        --
        -- Notice that the face hypothesis in the endpoint below really is
        -- needed.  Merely knowing that the values of the endpoint are in
        -- `P` would only give a homotopy in `P`; it would say nothing about
        -- support along a face of the boundary.
        have endpoint :
            ∃ (g : C(P × X, P)) (L : Subdivision P),
              (∀ D ∈ L.complex.facets,
                 ∃ A : Finset ι, A.card ≤ k ∧
                   ∀ p p' : closedCell P D, ∀ x : X,
                     x ∉ (⋃ α ∈ A, U α) →
                       g (p.1, x) = g (p'.1, x)) ∧
              (∀ Q : Set P, IsBoundarySubpolyhedron Q →
                 ∀ p : P, p ∈ Q → ∀ x : X, g (p, x) ∈ Q) := by
          -- On a compact space a locally finite partition has in fact only
          -- finitely many nonzero members.  This reduction is useful here:
          -- the still geometric problem after it is a *finite*
          -- moving-colours problem; no compactness or infinite sums remain.
          let W : Set ι := {i | (Function.support (ρ i)).Nonempty}
          have hW : W.Finite := by
            simpa [W] using ρ.locallyFinite.finite_nonempty_of_compact
          let C : Finset ι := hW.toFinset
          have hz : ∀ i, i ∉ C → ∀ x : X, ρ i x = 0 := by
            intro i hi x
            by_contra hn
            have hiW : i ∈ W := by
              refine ⟨x, ?_⟩
              exact hn
            exact hi (by simpa [C] using hiW)
          have hsum : ∀ x : X, ∑ i ∈ C, ρ i x = 1 := by
            intro x
            have hsub : Function.support (fun i => ρ i x) ⊆ (↑C : Set ι) := by
              intro i hi
              have hiW : i ∈ W := ⟨x, hi⟩
              have hic : i ∈ C := by simpa [C] using hiW
              exact hic
            calc
              (∑ i ∈ C, ρ i x) = ∑ᶠ i, ρ i x :=
                (finsum_eq_sum_of_support_subset _ hsub).symm
              _ = 1 := ρ.sum_eq_one (by simp)
          have hzeroU : ∀ i, ∀ x : X, x ∉ U i → ρ i x = 0 := by
            intro i x hx
            by_contra hn
            have hs : x ∈ Function.support (ρ i) := hn
            have ht : x ∈ tsupport (ρ i) := subset_tsupport _ hs
            exact hx (_hρ i ht)
          have hCcover :
              (Set.univ : Set X) ⊆ ⋃ i ∈ C, U i := by
            intro x hx
            obtain ⟨i, hi⟩ := ρ.exists_pos (by trivial : x ∈ (Set.univ : Set X))
            have hic : i ∈ C := by
              by_contra hin
              have h0 : ρ i x = 0 := hz i hin x
              linarith
            have hxu : x ∈ U i := by
              by_contra hxn
              have h0 : ρ i x = 0 := hzeroU i x hxn
              linarith
            exact Set.mem_iUnion_of_mem i
              (Set.mem_iUnion_of_mem hic hxu)
          have hkactive : k < C.card :=
            Nat.lt_of_not_ge (fun hle => no_small_cover C hle hCcover)
          -- Replace the ambient index type by the finite type of its active
          -- indices.  This avoids an artificial infinitary gluing issue:
          -- zero colours never have to be
          -- inserted in a moving chain.  The map from the finite conclusion
          -- back to `ι` is proved, including the union-of-supports assertion,
          -- just below.
          let J := {i : ι // i ∈ C}
          let V : J → Set X := fun i => U i.val
          let r : J → C(X, ℝ) := fun i => ρ i.val
          have hkJ : k < Fintype.card J := by
            change k < Fintype.card {i : ι // i ∈ C}
            simpa using hkactive
          have hr0 : ∀ i : J, ∀ x : X, x ∉ V i → r i x = 0 := by
            intro i x hx
            exact hzeroU i.val x hx
          have hrnonneg : ∀ i : J, ∀ x : X, 0 ≤ r i x := by
            intro i x
            exact ρ.nonneg i.val x
          have hrsum : ∀ x : X, ∑ i : J, r i x = 1 := by
            intro x
            -- The `univ` finset of the subtype is the `attach` of `C`.
            change (∑ i : {i : ι // i ∈ C}, ρ i.val x) = 1
            change
              (∑ i ∈ (Finset.univ : Finset {i : ι // i ∈ C}),
                ρ i.val x) = 1
            rw [Finset.univ_eq_attach C,
              Finset.sum_attach C (fun i => ρ i x)]
            exact hsum x
          -- This is the remaining, genuinely geometric, finite-colour step.
          -- Its indices form a finite type and the functions in it are
          -- continuous, non-negative, sum to one, and vanish off their
          -- indicated open set (`hr0`, `hrnonneg`, `hrsum`).  What is not a
          -- formal consequence of compactness is to lay their transitions
          -- out on a sufficiently fine *geometric subdivision*, with at most
          -- `k` transitions in a top simplex, while respecting all faces.  A
          -- proof of that finite moving-colours step is independent of the
          -- straight-line homotopy below.
          have finite_endpoint :
              ∃ (g : C(P × X, P)) (M : Subdivision P),
                (∀ D ∈ M.complex.facets,
                   ∃ A : Finset J, A.card ≤ k ∧
                     ∀ p p' : closedCell P D, ∀ x : X,
                       x ∉ (⋃ j ∈ A, V j) →
                         g (p.1, x) = g (p'.1, x)) ∧
                (∀ Q : Set P, IsBoundarySubpolyhedron Q →
                   ∀ p : P, p ∈ Q → ∀ x : X, g (p, x) ∈ Q) := by
            /- The analytic/topological part of the finite-colour construction is
               separate from its (finite) PL assertion.  It is useful to isolate
               the latter in a form not mentioning the partition, or even `X`.

               Give every active colour `j` its own copy `φ j : P → P`.  On a
               final simplex all but at most `k` of these copies are to be
               *constant*.  Each copy sends every boundary face to itself.  This
               is exactly the elementary PL ``one bin per colour'' problem: on an
               ordered simplex cut the cumulative barycentric coordinates into
               `card J` equal bins.  Only a bin hit by one of the `d` break points
               varies on a grid simplex (`d ≤ k`).  The cuts agree on faces.

               Nothing about the functions `r j` is involved in this PL lemma;
               in particular it is strictly smaller than the endpoint statement
               (there is no parameter space or open cover).  Once these vertex
               maps exist, the endpoint is their convex combination with weights
               `r j x`.  Keeping this as the sole combinatorial obstruction avoids
               hiding any analytic assumption in a triangulation assertion. -/
            have sparse_vertices :
                ∃ (φ : J → C(P, P)) (M : Subdivision P),
                  (∀ D ∈ M.complex.facets,
                    -- there are only `card D - 1` genuine breakpoints on a
                    -- simplex.  Keeping the sharp, intrinsic version here is
                    -- important for later facewise induction; the ambient `k`
                    -- does not occur in the PL problem.
                    ∃ A : Finset J, A.card ≤ k ∧
                      ∀ j ∉ A, ∀ p p' : closedCell P D,
                        φ j p.1 = φ j p'.1) ∧
                  (∀ Q : Set P, IsBoundarySubpolyhedron Q →
                    ∀ j : J, ∀ p : P, p ∈ Q → φ j p ∈ Q) := by
              classical
              -- Zero-dimensional complexes are a useful base case for the
              -- finite PL assertion.  It also records precisely why the
              -- interesting case starts with a genuine edge: on a singleton
              -- simplex the identity copy is already constant.
              by_cases hzdim :
                  ∃ M : Subdivision P,
                    ∀ D ∈ M.complex.facets, D.card = 1
              · rcases hzdim with ⟨M, hMone⟩
                let φ : J → C(P, P) := fun _ => ContinuousMap.id P
                refine ⟨φ, M, ?_, ?_⟩
                · intro D hD
                  let A : Finset J := ∅
                  have hD1 : D.card = 1 := hMone D hD
                  refine ⟨A, ?_, ?_⟩
                  · simp [A]
                  · intro j hj p p'
                    dsimp [φ]
                    -- The two parameters of a singleton closed cell have the
                    -- same ambient point.  Notice that `closedCell` uses the
                    -- convex hull (not membership in the vertex finset).
                    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hD1
                    subst D
                    apply Subtype.ext
                    have hp :
                        (p.1 : Fin k → ℝ) = z := by
                      have hm := p.property
                      change (p.1 : Fin k → ℝ) ∈
                        convexHull ℝ (({z} : Finset (Fin k → ℝ)) :
                          Set (Fin k → ℝ)) at hm
                      simpa [convexHull_singleton] using hm
                    have hp' :
                        (p'.1 : Fin k → ℝ) = z := by
                      have hm := p'.property
                      change (p'.1 : Fin k → ℝ) ∈
                        convexHull ℝ (({z} : Finset (Fin k → ℝ)) :
                          Set (Fin k → ℝ)) at hm
                      simpa [convexHull_singleton] using hm
                    exact hp.trans hp'.symm
                · intro Q hQ j p hp
                  change p ∈ Q
                  exact hp
              · -- The empty / one-colour case is another genuine base case
                -- of the combinatorial assertion.  Here the identity copy
                -- can be charged to the only colour on every non-vertex
                -- simplex.  This proof does *not* assert that a facet has
                -- top dimension; facets of finite complexes may be vertices.
                by_cases hone : Fintype.card J ≤ 1
                · rcases full_triangulation with ⟨M⟩
                  let φ : J → C(P, P) := fun _ => ContinuousMap.id P
                  refine ⟨φ, M, ?_, ?_⟩
                  · intro D hD
                    have hpos : 0 < D.card :=
                      Finset.card_pos.mpr
                        (M.complex.nonempty_of_mem_faces hD.1)
                    by_cases hD1 : D.card = 1
                    · let A : Finset J := ∅
                      refine ⟨A, by simp [A], ?_⟩
                      intro j hj p p'
                      dsimp [φ]
                      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hD1
                      subst D
                      apply Subtype.ext
                      have hp : (p.1 : Fin k → ℝ) = z := by
                        have hm := p.property
                        change (p.1 : Fin k → ℝ) ∈
                          convexHull ℝ (({z} : Finset (Fin k → ℝ)) :
                            Set (Fin k → ℝ)) at hm
                        simpa [convexHull_singleton] using hm
                      have hp' : (p'.1 : Fin k → ℝ) = z := by
                        have hm := p'.property
                        change (p'.1 : Fin k → ℝ) ∈
                          convexHull ℝ (({z} : Finset (Fin k → ℝ)) :
                            Set (Fin k → ℝ)) at hm
                        simpa [convexHull_singleton] using hm
                      exact hp.trans hp'.symm
                    · refine ⟨(Finset.univ : Finset J), ?_, ?_⟩
                      · -- `1` moving copy, hence the sharp `+1` bound.
                        have hone' : Fintype.card J ≤ k :=
                          le_trans hone (by omega)
                        simpa using hone'
                      · intro j hj
                        exact (hj (Finset.mem_univ j)).elim
                  · intro Q hQ j p hp
                    change p ∈ Q
                    exact hp
                · -- At least two colours on a positive-dimensional complex:
                  -- the outstanding ordered-bins refinement.  This is now the
                  -- very first genuinely moving PL case.
                  have hmany : 2 ≤ Fintype.card J := by omega
                  -- A last easy terminal case is worth removing here.  Notice that
                  -- the condition quantifies only over *inhabited* faces: `∅` is an
                  -- extreme subset too.  If all the nonempty boundary faces have a
                  -- common point, the constant copies already do the job.  The
                  -- remaining case below has two genuinely incompatible boundary
                  -- faces (and is where the ordered-bin construction is needed).
                  by_cases hstar : ∃ z : P, ∀ Q : Set P,
                    IsBoundarySubpolyhedron Q → Q.Nonempty → z ∈ Q
                  · rcases hstar with ⟨z, hz⟩
                    rcases full_triangulation with ⟨M⟩
                    let φ : J → C(P,P) := fun _ => ContinuousMap.const P z
                    refine ⟨φ, M, ?_, ?_⟩
                    · intro D hD
                      refine ⟨(∅ : Finset J), ?_, ?_⟩
                      · simp
                      · intro j hj p q
                        rfl
                    · intro Q hQ j p hp
                      change z ∈ Q
                      exact hz Q hQ ⟨p, hp⟩
                  · have separated : ∀ z : P, ∃ Q : Set P,
                        IsBoundarySubpolyhedron Q ∧ Q.Nonempty ∧ z ∉ Q := by
                        intro z
                        have zz : ¬ (∀ Q : Set P,
                          IsBoundarySubpolyhedron Q → Q.Nonempty → z ∈ Q) := by
                          intro h
                          exact hstar ⟨z, h⟩
                        push_neg at zz
                        simpa using zz
                    -- The actual one-dimensional ordered bins (including the
                    -- continuous min/max formula) are available at this stage; in
                    -- particular the obstruction is *not* selection of break
                    -- points on a single real edge. We spell this seed out because
                    -- the pulling complex suppresses interior collinear vertices.
                    -- What is still needed is their compatible transport to all
                    -- barycentric faces of `M`.
                    let eJ : J ≃ Fin (Fintype.card J) :=
                      Fintype.equivFin J
                    have interval_seed (a b : ℝ) (hab : a < b) :
                        ∃ ψ : J → C(Set.Icc a b, Set.Icc a b),
                          (∀ (m : ℕ), m < Fintype.card J → ∀ j : J,
                            (eJ j).val ≠ m → ∀ x y : Set.Icc a b,
                              x.1 ∈ Set.Icc
                                  (FamiliesProof.linePoint a b (Fintype.card J) m)
                                  (FamiliesProof.linePoint a b (Fintype.card J) (m+1)) →
                              y.1 ∈ Set.Icc
                                  (FamiliesProof.linePoint a b (Fintype.card J) m)
                                  (FamiliesProof.linePoint a b (Fintype.card J) (m+1)) →
                              ψ j x = ψ j y) ∧
                          (∀ j, ψ j ⟨a, ⟨le_rfl, le_of_lt hab⟩⟩ =
                              ⟨a, ⟨le_rfl, le_of_lt hab⟩⟩) ∧
                          (∀ j, ψ j ⟨b, ⟨le_of_lt hab, le_rfl⟩⟩ =
                              ⟨b, ⟨le_of_lt hab, le_rfl⟩⟩) := by
                        have hn : 0 < Fintype.card J := lt_of_lt_of_le (by decide : 0 < 2) hmany
                        exact FamiliesProof.interval_orderedBins eJ hab hn
                    -- If the maximal simplices already have room for all of the
                    -- colours there is no PL construction at all.  This happens, for
                    -- example, to a full dimensional single simplex with not more
                    -- colours than its dimension.  It is important to split this case
                    -- using the *cardinalities of the facets* rather than `k`: a
                    -- polytope in `ℝ^k` may have arbitrarily small affine dimension.
                    -- On such a subdivision take all the copies to be the identity
                    -- and charge every colour to every facet.  This observation also
                    -- removes this case from the eventual ordered-grid lemma.
                    by_cases roomy : ∃ N : Subdivision P,
                        ∀ D ∈ N.complex.facets, Fintype.card J + 1 ≤ D.card
                    · rcases roomy with ⟨N,hN⟩
                      let φ : J → C(P,P) := fun _ => ContinuousMap.id P
                      refine ⟨φ, N, ?_, ?_⟩
                      · intro D hD
                        refine ⟨(Finset.univ : Finset J), ?_, ?_⟩
                        · have hiD : AffineIndependent ℝ ((↑) : D → (Fin k → ℝ)) :=
                            N.complex.indep hD.1
                          have hspan : Module.finrank ℝ
                              (vectorSpan ℝ (Set.range ((↑) : D → (Fin k → ℝ)))) ≤ k := by
                            calc
                              _ ≤ Module.finrank ℝ (Fin k → ℝ) := Submodule.finrank_le _
                              _ = k := by simp
                          have hc : D.card ≤ k + 1 := by
                            have hle := AffineIndependent.card_le_finrank_succ hiD
                            have hle' := le_trans hle (Nat.add_le_add_right hspan 1)
                            simpa using hle'
                          have eqcard : (Finset.univ : Finset J).card = Fintype.card J := Finset.card_univ
                          rw [eqcard]
                          have hh := hN D hD
                          omega
                        · intro j hj
                          exact (hj (Finset.mem_univ j)).elim
                      · intro Q hQ j p hp
                        change p ∈ Q
                        exact hp
                    · -- Thus every available triangulation has a maximal simplex
                      -- of affine dimension `< card J`; the unused colours there
                      -- must genuinely be made constant.  The interval seed above
                      -- deals with one such simplex in dimension one.  The missing
                      -- construction is the face compatible ordered-grid lift for
                      -- these low-dimensional maximal faces.
                      --
                      -- The scalar part of that lift is worth recording with its
                      -- closed endpoints.  If cumulative barycentric coordinates
                      -- of two points lie in the same grid chamber, every colour
                      -- other than the colour of a crossed wall has *equal*, not
                      -- merely close, weights at those points.  This is precisely
                      -- the fact required to descend `φ` to a closed simplex (the
                      -- cells in this statement are closed).  Notice especially the
                      -- `m < d+1` including the zero and final cut; formulas using
                      -- `d-1` leave a gap at the boundary.  It is independent of a
                      -- vertex ordering and is inherited upon deleting zero
                      -- coordinates on a face.
                      have chamber_seed (d n r₀ : ℕ) (hn : 0 < n)
                          (u w : Fin d → ℝ) (bins : ℕ → ℕ)
                          (havoid : ∀ m, m < d+1 → bins m ≠ r₀)
                          (hu : ∀ m, m < d+1 →
                            FamiliesProof.cumCoord d u m ∈ Set.Icc
                              (FamiliesProof.linePoint 0 1 n (bins m))
                              (FamiliesProof.linePoint 0 1 n (bins m + 1)))
                          (hw : ∀ m, m < d+1 →
                            FamiliesProof.cumCoord d w m ∈ Set.Icc
                              (FamiliesProof.linePoint 0 1 n (bins m))
                              (FamiliesProof.linePoint 0 1 n (bins m + 1))) :
                          ∀ t : Fin d,
                            FamiliesProof.baryStep d n r₀ u t =
                              FamiliesProof.baryStep d n r₀ w t := by
                        exact FamiliesProof.baryStep_constant_of_chambers hn
                          havoid hu hw
                      -- Also every such ordered weight is nonnegative and has
                      -- mass one. Combining these into affine combinations now
                      -- needs no positivity workaround; all that remains is the
                      -- finite grid *complex* with these closed chambers and their
                      -- intersections.
                      have simplex_mass (d n r₀ : ℕ) (hd : 0 < d)
                          (hn : 0 < n) (hr₀ : r₀ < n)
                          (u : Fin d → ℝ) (hnon : ∀ i, 0 ≤ u i)
                          (hs : (∑ i, u i) = 1) :
                          (∀ i, 0 ≤ FamiliesProof.baryStep d n r₀ u i) ∧
                            (∑ i, FamiliesProof.baryStep d n r₀ u i) = 1 := by
                        exact ⟨FamiliesProof.baryStep_nonneg hn hnon,
                          FamiliesProof.sum_baryStep hd hn hr₀ hs⟩
                      -- In dimension one the required cuts do form a genuine
                      -- *embedded* complex, not just a cover by hulls. This avoids
                      -- the common mistake of using the pulling complex of the two
                      -- endpoints (which discards all collinear grid vertices). The
                      -- push-along-an-injective-affine-map lemma works in the full
                      -- ambient `ℝᵏ`, so an edge need not be coordinatized first.
                      have embedded_edge_seed
                          (l r₁ : Fin k → ℝ) (hlr : l ≠ r₁)
                          (n : ℕ) (hn : 0 < n) :
                          ∃ Kedge : SimplicialComplex ℝ (Fin k → ℝ),
                            Kedge.faces.Finite ∧
                            Kedge.space = segment ℝ l r₁ ∧
                            (∀ D ∈ Kedge.facets,
                              ∃ m < n,
                                D = FamiliesProof.embFinset
                                  (FamiliesProof.lineAffine l r₁)
                                  (FamiliesProof.lineAffine_injective hlr)
                                  { FamiliesProof.linePoint 0 1 n m,
                                    FamiliesProof.linePoint 0 1 n (m+1) }) := by
                        refine ⟨FamiliesProof.lineComplex l r₁ n hn hlr,
                          FamiliesProof.lineComplex_faces_finite l r₁ n hn hlr,
                          FamiliesProof.lineComplex_space l r₁ n hn hlr, ?_⟩
                        intro D hD
                        exact FamiliesProof.lineComplex_facet l r₁ n hn hlr hD
                      -- The full edge case, including preservation of arbitrary genuine
                      -- boundary faces, already runs in the ambient `ℝ^k`: use one block
                      -- of the interleaved height construction.  Its line complex contains
                      -- each breakpoint as an honest vertex.
                      by_cases hseg : ∃ l r : Fin k → ℝ, l ≠ r ∧ P = segment ℝ l r
                      · rcases hseg with ⟨l,r,hlr,hPr⟩
                        cases hPr
                        let n : ℕ := Fintype.card J
                        have hn : 0 < n := by
                          dsimp [n]
                          omega
                        let e : J ≃ Fin n := Fintype.equivFin J
                        let N : ℕ := 1*n
                        have hN : 0 < N := Nat.mul_pos (by decide) hn
                        let phi : J → C({x : Fin k → ℝ // x ∈ segment ℝ l r},
                          {x : Fin k → ℝ // x ∈ segment ℝ l r}) := fun j =>
                            FamiliesProof.segmentCopy l r hlr 1 n (e j).val (by decide)
                        let M : Subdivision (segment ℝ l r) :=
                          { complex := FamiliesProof.lineComplex l r N hN hlr
                            faces_finite := FamiliesProof.lineComplex_faces_finite l r N hN hlr
                            space_eq := FamiliesProof.lineComplex_space l r N hN hlr }
                        refine ⟨phi, M, ?_, ?_⟩
                        · intro D hD
                          change D ∈ (FamiliesProof.lineComplex l r N hN hlr).facets at hD
                          rcases FamiliesProof.lineComplex_facet l r N hN hlr hD
                            with ⟨m,hm,rfl⟩
                          let active : J := e.symm ⟨m % n, Nat.mod_lt _ hn⟩
                          refine ⟨{active}, ?_, ?_⟩
                          · -- an embedded nondegenerate pair has two vertices
                            have hpne : FamiliesProof.linePoint 0 1 N m ≠
                                  FamiliesProof.linePoint 0 1 N (m+1) := by
                              intro h
                              unfold FamiliesProof.linePoint at h
                              have nz : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
                              field_simp [nz] at h
                              have : (m:ℝ) ≠ (m+1:ℕ) := by exact_mod_cast (by omega : m ≠ m+1)
                              exact this (by linarith)
                            have hc : ({FamiliesProof.linePoint 0 1 N m,
                                FamiliesProof.linePoint 0 1 N (m+1)} : Finset ℝ).card = 2 :=
                              Finset.card_pair hpne
                            have cardEmb :
                                (FamiliesProof.embFinset (FamiliesProof.lineAffine l r)
                                  (FamiliesProof.lineAffine_injective hlr)
                                  {FamiliesProof.linePoint 0 1 N m,
                                   FamiliesProof.linePoint 0 1 N (m+1)}).card = 2 := by
                                calc
                                  _ = ({FamiliesProof.linePoint 0 1 N m,
                                      FamiliesProof.linePoint 0 1 N (m+1)} : Finset ℝ).card := by
                                        apply Finset.card_map
                                  _ = 2 := hc
                            have hkone : (1:ℕ) ≤ k := Nat.one_le_iff_ne_zero.mpr hk
                            simpa using hkone
                          · intro j hj p p' 
                            have jne : m % n ≠ (e j).val := by
                              intro heq
                              have hh : j = active := by
                                dsimp [active]
                                apply e.injective
                                apply Fin.val_inj.mp
                                simpa using heq.symm
                              exact hj (Finset.mem_singleton.mpr hh)
                            change _
                            exact FamiliesProof.segmentCopy_const_edge hlr
                              (q:=1) (n:=n) (m:=m) (i:=(e j).val)
                              (by decide) hn (by simpa [N] using hm) jne (e j).isLt
                              p.property p'.property
                        · intro Q hQ j p hp
                          rcases hQ with ⟨⟨w,hw⟩, hfront,hExt⟩
                          have hp' : (p : Fin k → ℝ) ∈
                              (((↑) : {x : Fin k → ℝ // x ∈ segment ℝ l r} → Fin k → ℝ) '' Q) :=
                                ⟨p,hp,rfl⟩
                          have hcB : Convex ℝ
                              (((↑) : {x : Fin k → ℝ // x ∈ segment ℝ l r} → Fin k → ℝ) '' Q) := by
                            rw [hw]
                            exact convex_convexHull ℝ _
                          have hb := FamiliesProof.segmentCopy_mem_extreme hlr
                            (q:=1) (n:=n) (i:=(e j).val)
                            (by decide) hn (e j).isLt hcB hExt p hp'
                          change (phi j p : Fin k → ℝ) ∈
                            (((↑) : {x : Fin k → ℝ // x ∈ segment ℝ l r} → Fin k → ℝ) '' Q) at hb
                          rcases hb with ⟨z,hz,hzz⟩
                          have : z = phi j p := Subtype.ext hzz
                          simpa [this] using hz
                      · -- There is likewise no leftover case when the ambient
                        -- coordinate space is a line.  A finite hull in `Fin 1 → ℝ`
                        -- is the segment between its extremal coordinates (proved in
                        -- `LowDim`); the nontriviality of `P` makes the endpoints
                        -- distinct, contradicting `hseg` above.  Keeping this reduction
                        -- here is useful because the outstanding chamber-pasting
                        -- problem now starts in genuine dimension at least two on both
                        -- quantitative and qualitative sides.
                        have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
                        by_cases hle1 : k ≤ 1
                        · have hkEq : k = 1 := Nat.le_antisymm hle1 hkpos
                          subst k
                          exfalso
                          apply hseg
                          -- reuse the reduced vertex set; the original presentation was
                          -- destructed near the beginning of this branch.
                          let s : Finset (Fin 1 → ℝ) := v
                          have hsP : P = convexHull ℝ (s : Set (Fin 1 → ℝ)) := hvP
                          have sn : s.Nonempty := by
                            have hnP :
                                (convexHull ℝ (s : Set (Fin 1 → ℝ))).Nonempty := by
                              let p : P := Classical.choice
                                (inferInstance : Nonempty P)
                              exact ⟨p.1, by simpa [← hsP] using p.property⟩
                            have hn' : ((s : Set (Fin 1 → ℝ))).Nonempty :=
                              (convexHull_nonempty_iff).1 hnP
                            simpa using hn'
                          obtain ⟨l₁, r₂, hl, hr, hull⟩ :=
                            FamiliesProof.convexHull_fin1_eq_segment s sn
                          have hdiff : l₁ ≠ r₂ := by
                            intro he
                            have peq :
                                (P : Set (Fin 1 → ℝ)) = ({l₁} : Set (Fin 1 → ℝ)) := by
                              rw [hsP, hull, he, segment_same]
                            have hsPsub : Subsingleton P := by
                              constructor
                              intro a b
                              apply Subtype.ext
                              have aa : (a : Fin 1 → ℝ) = l₁ :=
                                Set.mem_singleton_iff.mp (by simpa [peq] using a.property)
                              have bb : (b : Fin 1 → ℝ) = l₁ :=
                                Set.mem_singleton_iff.mp (by simpa [peq] using b.property)
                              exact aa.trans bb.symm
                            exact (not_subsingleton_iff_nontrivial.mpr hnon) hsPsub
                          exact ⟨l₁, r₂, hdiff, hsP.trans hull⟩
                        · -- simultaneous ordered grids on truly higher faces; from now on
                          -- every unsolved chamber has ambient dimension at least two.
                          have ktwo : 2 ≤ k := by omega
                          have vnon : Nonempty {x : Fin k → ℝ //
                              x ∈ convexHull ℝ (v : Set (Fin k → ℝ))} := by
                            let p : P := Classical.choice (inferInstance : Nonempty P)
                            exact ⟨p.1, by simpa [← hvP] using p.property⟩
                          have vntr : Nontrivial {x : Fin k → ℝ //
                              x ∈ convexHull ℝ (v : Set (Fin k → ℝ))} := by
                            simpa [hvP] using hnon
                          have vseg : ¬ ∃ l r : Fin k → ℝ, l ≠ r ∧
                              convexHull ℝ (v : Set (Fin k → ℝ)) = segment ℝ l r := by
                            intro z
                            obtain ⟨l,r,h,eq⟩ := z
                            exact hseg ⟨l,r,h,hvP.trans eq⟩
                          have card_at_least_three : 3 ≤ v.card :=
                            FamiliesProof.three_le_card_of_nontrivial_nosegment
                              v vnon vntr vseg
                          -- On each independent simplex the maps themselves, and their
                          -- exact closed-chamber constancy, no longer have to be built.
                          -- This local statement is uniform also for lower faces. The still
                          -- missing datum is a *single simplicial refinement* of all these
                          -- geometric closed chambers across the pulling complex.
                          have local_closed_chambers (d n : ℕ) (hd : 0 < d)
                              (hn : 0 < n) (w : Fin d → (Fin k → ℝ))
                              (hi : AffineIndependent ℝ w) :
                              let W := {x : (Fin k → ℝ) //
                                x ∈ convexHull ℝ (Set.range w)}
                              ∃ ψ : Fin n → C(W,W),
                                ∀ b : Fin (d+1) → Fin n,
                                  ∃ A : Finset (Fin n), A.card + 1 ≤ d ∧
                                    ∀ r : Fin n, r ∉ A → ∀ x y : W,
                                      x ∈ FamiliesProof.geoChamber w hi n
                                        (fun m => (b m).val) →
                                      y ∈ FamiliesProof.geoChamber w hi n
                                        (fun m => (b m).val) → ψ r x = ψ r y := by
                            intro
                            rcases FamiliesProof.simplexCycMaps_chambers hd (q:=1)
                              (by decide : 0 < (1:ℕ)) hn w hi with ⟨ψ,hψ,_,_⟩
                            refine ⟨ψ, ?_⟩
                            intro b
                            let b' : Fin (d+1) → Fin (1*n) := fun i =>
                              ⟨(b i).val, by simpa using (b i).isLt⟩
                            rcases hψ b' with ⟨A,hA,hc⟩
                            refine ⟨A, hA, ?_⟩
                            intro r hr x y hx hy
                            apply hc r hr x y
                            · simpa [b'] using hx
                            · simpa [b'] using hy

                          -- The lexicographic hull has global continuous barycentric
                          -- coordinates, not merely choices of representatives.  Pasting the
                          -- local charts was another potential obstruction in this branch; the
                          -- compact closed-face pasting/uniqueness argument is recorded in
                          -- `GlobalCoeff`. Thus only a *refining complex* of chambers remains.
                          rcases FamiliesProof.exists_globalCoeff v with
                            ⟨cglobal, cglobal_pos, cglobal_sum,
                              cglobal_eval, cglobal_face⟩
                          -- Local cyclic copies do agree *literally* on an ordered
                          -- face; zero coordinates can be inserted without changing
                          -- the cumulative cut. This discharges the pasting-of-maps
                          -- issue independently of the unsolved grid-complex step.
                          have ordered_face_restriction
                              {a b n : ℕ} (ha : 0 < a) (hb : 0 < b)
                              (hn0 : 0 < n)
                              (inc : Fin a ↪ Fin b) (hinc : StrictMono inc)
                              (z : Fin b → (Fin k → ℝ))
                              (hz : AffineIndependent ℝ z) (r0 : Fin n)
                              (x : {y : (Fin k → ℝ) //
                                y ∈ convexHull ℝ (Set.range
                                  (fun i : Fin a => z (inc i)))}) :
                              FamiliesProof.simplexCycMap hb
                                  (by decide : 0 < (1:ℕ)) hn0 z hz r0
                                    (FamiliesProof.faceInclusion inc z x) =
                                FamiliesProof.faceInclusion inc z
                                  (FamiliesProof.simplexCycMap ha
                                    (by decide : 0 < (1:ℕ)) hn0
                                    (fun i : Fin a => z (inc i))
                                    (FamiliesProof.affineIndependent_comp_embedding
                                      inc hz) r0 x) := by
                            exact FamiliesProof.simplexCycMap_face ha hb
                              (by decide : 0 < (1 : ℕ)) hn0 inc hinc z hz r0 x

                          have hcardJpos : 0 < Fintype.card J := by omega
                          -- remaining purely coefficient-grid Freudenthal datum
                          have chamber_refine :
                              ∃ M : SimplicialComplex ℝ (Fin k → ℝ),
                                M.faces.Finite ∧
                                M.space = convexHull ℝ (v : Set (Fin k → ℝ)) ∧
                                ∀ D ∈ M.facets,
                                  ∃ (t : Finset (Fin k → ℝ))
                                    (ht : FamiliesProof.lexFace v t)
                                    (hne : t.Nonempty)
                                    (b : Fin ((FamiliesProof.facePos v t).card+1) →
                                      Fin (1 * Fintype.card J)),
                                    ∀ x : Fin k → ℝ,
                                      x ∈ convexHull ℝ (D : Set (Fin k → ℝ)) →
                                      ∃ hx : x ∈ convexHull ℝ
                                          (Set.range (FamiliesProof.inheritedFace v t)),
                                        (⟨x,hx⟩ : {z : Fin k → ℝ // z ∈ convexHull ℝ
                                          (Set.range (FamiliesProof.inheritedFace v t))}) ∈
                                          FamiliesProof.geoChamber
                                            (FamiliesProof.inheritedFace v t)
                                            (FamiliesProof.inheritedFace_indep ht)
                                            (1 * Fintype.card J)
                                            (fun m => (b m).val) := by
                            have hN : 0 < (1 * Fintype.card J) := by simpa using hcardJpos
                            apply FamiliesProof.gridChain_refinement_reduction
                              v (1 * Fintype.card J) hN
                            have remains :
                                ((∀ D ∈ FamiliesProof.mappedChains v
                                      (1 * Fintype.card J) hN,
                                    ∀ B ∈ FamiliesProof.mappedChains v
                                      (1 * Fintype.card J) hN,
                                      convexHull ℝ (D : Set (Fin k → ℝ)) ∩
                                        convexHull ℝ (B : Set (Fin k → ℝ)) ⊆
                                        convexHull ℝ ((D : Set (Fin k → ℝ)) ∩
                                          (B : Set (Fin k → ℝ)))) ∧
                                  (∀ x ∈ convexHull ℝ (v : Set (Fin k → ℝ)),
                                    ∃ D ∈ FamiliesProof.mappedChains v
                                      (1 * Fintype.card J) hN,
                                      D.Nonempty ∧ x ∈ convexHull ℝ
                                        (D : Set (Fin k → ℝ)))) := by
                              have round_all : ∀ (d : ℕ) (u : Fin d → ℝ),
                                  u ∈ FamiliesProof.coeffSimplex d →
                                  ∃ A : Finset (FamiliesProof.GridVert d
                                    (1 * Fintype.card J)), A.Nonempty ∧
                                    A ∈ FamiliesProof.coeffChains d
                                      (1 * Fintype.card J) ∧
                                    u ∈ convexHull ℝ
                                      (FamiliesProof.gu ''
                                        (A : Set (FamiliesProof.GridVert d
                                          (1 * Fintype.card J)))) := by
                                intro d u hu
                                exact FamiliesProof.coeff_round
                                  (1 * Fintype.card J) hN d u hu
                              refine ⟨?_, FamiliesProof.mappedChains_cover_of_coeff
                                (1 * Fintype.card J) hN round_all v⟩
                              -- Only the pairwise geometric intersection survives in
                              -- this common candidate. The threshold averaging proof is
                              -- independent of metrics and handles this branch verbatim.
                              have hard : ∀ D ∈ FamiliesProof.mappedChains v
                                  (1 * Fintype.card J) hN, D.Nonempty →
                                  ∀ B ∈ FamiliesProof.mappedChains v
                                    (1 * Fintype.card J) hN, B.Nonempty →
                                  convexHull ℝ (D : Set (Fin k → ℝ)) ∩
                                    convexHull ℝ (B : Set (Fin k → ℝ)) ⊆
                                    convexHull ℝ ((D : Set (Fin k → ℝ)) ∩
                                      (B : Set (Fin k → ℝ))) := by
                                intro D hD hdn B hB hbn
                                classical
                                by_cases ok : ∃ (t : Finset (Fin k → ℝ))
                                    (ht : FamiliesProof.lexFace v t)
                                    (A C : Finset (FamiliesProof.GridVert
                                      (FamiliesProof.facePos v t).card
                                        (1 * Fintype.card J))),
                                      A ∪ C ∈ FamiliesProof.coeffChains
                                        (FamiliesProof.facePos v t).card
                                          (1 * Fintype.card J) ∧
                                      D = A.map (FamiliesProof.gridEvalEmb hN
                                        (FamiliesProof.inheritedFace v t)
                                          (FamiliesProof.inheritedFace_indep ht)) ∧
                                      B = C.map (FamiliesProof.gridEvalEmb hN
                                        (FamiliesProof.inheritedFace v t)
                                          (FamiliesProof.inheritedFace_indep ht))
                                · obtain ⟨t,ht,A,C,hU,eD,eB⟩ := ok
                                  subst D
                                  subst B
                                  simpa [Finset.coe_inter] using
                                    (FamiliesProof.mappedFace_inter_of_union
                                      hN v t ht A C hU)
                                · -- Different pulling faces restrict to their
                                  -- common ordered subface.  On that face the
                                  -- positive coefficient supports form one
                                  -- Freudenthal chain.
                                  exact
                                    (FamiliesProof.mappedChains_inter_all v
                                      (1 * Fintype.card J) hN) D hD B hB

                              intro D hD B hB
                              classical
                              by_cases hd : D.Nonempty
                              · by_cases hb : B.Nonempty
                                · exact hard D hD hd B hB hb
                                · have bz : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
                                  subst B
                                  simp [convexHull_empty]
                              · have dz : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hd
                                subst D
                                simp [convexHull_empty]


                            exact FamiliesProof.mappedChains_reduction
                              v (1 * Fintype.card J) hN remains.1 remains.2

                          rcases FamiliesProof.hullCopies_of_chamberRefine v
                              (by exact lt_of_lt_of_le (by decide : 0<3) card_at_least_three)
                              (by decide : 0 < (1:ℕ)) hcardJpos chamber_refine with
                            ⟨φfin,M0,hMfin,hMspace,hMfac,hMext⟩
                          let eJ' : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
                          cases hvP
                          refine ⟨(fun j => φfin (eJ' j)),
                            {complex:=M0, faces_finite:=hMfin,
                              space_eq:=hMspace}, ?_, ?_⟩
                          · intro D hD
                            rcases hMfac D hD with ⟨A0,hA0,hconst0⟩
                            let A : Finset J := A0.map eJ'.symm.toEmbedding
                            refine ⟨A, ?_, ?_⟩
                            · change (A0.map eJ'.symm.toEmbedding).card ≤ k
                              simpa using hA0
                            · intro j hj p p'
                              have hnot : eJ' j ∉ A0 := by
                                intro hm
                                apply hj
                                exact Finset.mem_map.mpr ⟨eJ' j, hm, by simp⟩
                              exact hconst0 (eJ' j) hnot p.1 p'.1 p.property p'.property
                          · intro Q hQ j p hp
                            rcases hQ with ⟨⟨u,hu⟩,_,hEx⟩
                            have hBc : Convex ℝ
                                (((↑) : {x : Fin k → ℝ // x ∈
                                  convexHull ℝ (v : Set (Fin k → ℝ))} →
                                  Fin k → ℝ) '' Q) := by
                              rw [hu]
                              exact convex_convexHull ℝ _
                            have hpim : (p : Fin k → ℝ) ∈
                                (((↑) : {x : Fin k → ℝ // x ∈
                                  convexHull ℝ (v : Set (Fin k → ℝ))} →
                                  Fin k → ℝ) '' Q) := ⟨p,hp,rfl⟩
                            change (φfin (eJ' j) p :
                              {x : Fin k → ℝ // x ∈
                                convexHull ℝ (v : Set (Fin k → ℝ))}) ∈ Q
                            have hz := hMext _ hBc hEx (eJ' j) p hpim
                            rcases hz with ⟨z,hz,ee⟩
                            have eqp : z = φfin (eJ' j) p := Subtype.ext ee
                            simpa [eqp] using hz

            rcases sparse_vertices with ⟨φ, M, hconst, hφface⟩
            have hconvP' : Convex ℝ P := by
              rw [hvP]
              exact convex_convexHull ℝ _
            -- First take the weighted sum in the ambient vector space.  Membership
            -- in `P` is a plain finite convexity lemma; packaging into a subtype at
            -- the end makes both continuity and the face assertion painless.
            let vfun : P × X → (Fin k → ℝ) := fun z =>
              ∑ j : J, (r j z.2) •
                ((φ j z.1 : P) : Fin k → ℝ)
            have hvmem : ∀ z : P × X, vfun z ∈ P := by
              intro z
              dsimp [vfun]
              have hn : ∀ j ∈ (Finset.univ : Finset J),
                    0 ≤ r j z.2 := by
                intro j hj
                exact hrnonneg j z.2
              have hs : (∑ j ∈ (Finset.univ : Finset J), r j z.2) = 1 := by
                simpa using (hrsum z.2)
              exact hconvP'.sum_mem hn hs (by
                intro j hj
                exact (φ j z.1).property)
            have hvcontinuous : Continuous vfun := by
              -- a finite sum of the scalar product of two continuous functions
              -- (there is deliberately no local-finiteness argument here).
              dsimp [vfun]
              have hterm : ∀ j : J,
                  Continuous (fun z : P × X =>
                    (r j z.2) • ((φ j z.1 : P) : Fin k → ℝ)) := by
                intro j
                have hr' : Continuous (fun z : P × X => r j z.2) :=
                  (r j).continuous.comp continuous_snd
                have hφ' : Continuous (fun z : P × X =>
                    ((φ j z.1 : P) : Fin k → ℝ)) :=
                  continuous_subtype_val.comp
                    ((φ j).continuous.comp continuous_fst)
                exact hr'.smul hφ'
              -- `∑ j : J` is notation for the `univ` finset sum.
              exact continuous_finset_sum (Finset.univ : Finset J)
                (by
                  intro j hj
                  exact hterm j)
            let g : C(P × X, P) :=
              { toFun := fun z => ⟨vfun z, hvmem z⟩
                continuous_toFun := hvcontinuous.subtype_mk _ }
            refine ⟨g, M, ?_, ?_⟩
            · intro D hD
              rcases hconst D hD with ⟨A, hA, hstatic⟩
              -- a face of a geometric complex in `ℝ^k` contains at most
              -- `k+1` vertices.  Thus `card D - 1` is indeed no larger than
              -- the bound in the statement, even for lower-dimensional
              -- polytopes.
              have hiD : AffineIndependent ℝ ((↑) : D → (Fin k → ℝ)) :=
                M.complex.indep hD.1
              have hspan :
                  Module.finrank ℝ
                    (vectorSpan ℝ (Set.range ((↑) : D → (Fin k → ℝ)))) ≤ k := by
                calc
                  _ ≤ Module.finrank ℝ (Fin k → ℝ) := Submodule.finrank_le _
                  _ = k := by simp
              have hDcard : D.card ≤ k + 1 := by
                have hle :=
                  AffineIndependent.card_le_finrank_succ hiD
                have hle' := le_trans hle (Nat.add_le_add_right hspan 1)
                simpa using hle'
              have hAk : A.card ≤ k := hA
              refine ⟨A, hAk, ?_⟩
              intro p p' x hx
              -- Outside the selected bins the coefficient of a varying copy is
              -- zero.  All other copies are literally constant on this simplex.
              apply Subtype.ext
              change vfun (p.1, x) = vfun (p'.1, x)
              dsimp [vfun]
              apply Finset.sum_congr rfl
              intro j hj
              classical
              by_cases hjA : j ∈ A
              · have hxj : x ∉ V j := by
                  intro hmem
                  apply hx
                  exact Set.mem_iUnion_of_mem j
                    (Set.mem_iUnion_of_mem hjA hmem)
                have h0 : r j x = 0 := hr0 j x hxj
                simp [h0]
              · have hc := hstatic j hjA p p'
                -- equality of the two points in this copy is enough in the
                -- ambient vector space as well.
                rw [hc]
            · intro Q hQ p hp x
              -- The image of a boundary subpolyhedron is a convex hull.  Hence a
              -- convex combination of points of that face is again in the face;
              -- no ``extreme point of a segment'' argument is needed here.
              rcases hQ.1 with ⟨sQ, hsQ⟩
              let Bq : Set (Fin k → ℝ) :=
                ((↑) : P → Fin k → ℝ) '' Q
              have hBconv : Convex ℝ Bq := by
                change Convex ℝ (((↑) : P → Fin k → ℝ) '' Q)
                rw [hsQ]
                exact convex_convexHull ℝ _
              have hBin : vfun (p, x) ∈ Bq := by
                dsimp [vfun]
                have hn : ∀ j ∈ (Finset.univ : Finset J),
                      0 ≤ r j x := by
                    intro j hj; exact hrnonneg j x
                have hs : (∑ j ∈ (Finset.univ : Finset J), r j x) = 1 := by
                    simpa using (hrsum x)
                apply hBconv.sum_mem hn hs
                intro j hj
                change ((φ j p : P) : Fin k → ℝ) ∈ Bq
                exact ⟨φ j p, hφface Q
                    ⟨⟨sQ, hsQ⟩, hQ.2⟩ j p hp, rfl⟩
              rcases hBin with ⟨q, hq, hqv⟩
              have hqp : (g (p, x) : P) = q := by
                apply Subtype.ext
                -- unfolding once, the value of `g` is exactly the ambient sum.
                change vfun (p, x) = (q : Fin k → ℝ)
                exact hqv.symm
              simpa [hqp] using hq
          obtain ⟨g, M, hcell, hface⟩ := finite_endpoint
          refine ⟨g, M, ?_, hface⟩
          intro D hD
          obtain ⟨A, hA, hsame⟩ := hcell D hD
          let e : J ↪ ι :=
            ⟨(fun j => j.val), (fun a b h => Subtype.ext h)⟩
          let A' : Finset ι := A.map e
          have hcard : A'.card = A.card := by
            simp [A']
          have hsubsets : (⋃ j ∈ A, V j) ⊆ ⋃ i ∈ A', U i := by
            intro x hx
            rcases Set.mem_iUnion.mp hx with ⟨j, hx⟩
            rcases Set.mem_iUnion.mp hx with ⟨hj, hxj⟩
            have him : j.val ∈ A' := by
              exact Finset.mem_map.mpr ⟨j, hj, rfl⟩
            exact Set.mem_iUnion_of_mem j.val
              (Set.mem_iUnion_of_mem him hxj)
          refine ⟨A', ?_, ?_⟩
          · simpa [hcard] using hA
          · intro p p' x hx'
            exact hsame p p' x (fun hxj => hx' (hsubsets hxj))
        rcases endpoint with ⟨g, L, hgcell, hgface⟩
        have hconvP : Convex ℝ P := by
          rw [hvP]
          exact convex_convexHull ℝ _
        -- We deliberately write the segment in barycentric rather than
        -- `lineMap` form.  In this form continuity follows immediately from
        -- the product and scalar-multiplication lemmas and the endpoint
        -- equalities at `0` and `1` are `simp` lemmas.
        let u : I × P × X → (Fin k → ℝ) := fun z =>
          (1 - (z.1 : ℝ)) • (z.2.1 : Fin k → ℝ) +
            (z.1 : ℝ) • (g (z.2.1, z.2.2) : Fin k → ℝ)
        have humem : ∀ z : I × P × X, u z ∈ P := by
          intro z
          exact (convex_iff_add_mem.mp hconvP
            z.2.1.property (g (z.2.1, z.2.2)).property
            (sub_nonneg.mpr (unitInterval.le_one z.1))
            (unitInterval.nonneg z.1)
            (by ring))
        have hucont : Continuous u := by
          have ht : Continuous (fun z : I × P × X => (z.1 : ℝ)) :=
            continuous_subtype_val.comp continuous_fst
          have hp' : Continuous
              (fun z : I × P × X => (z.2.1 : Fin k → ℝ)) :=
            continuous_subtype_val.comp
              (continuous_fst.comp continuous_snd)
          have hg' : Continuous
              (fun z : I × P × X =>
                (g (z.2.1, z.2.2) : Fin k → ℝ)) :=
            continuous_subtype_val.comp (g.continuous.comp continuous_snd)
          exact (continuous_const.sub ht).smul hp' |>.add (ht.smul hg')
        let G : C(I × P × X, P) :=
          { toFun := fun z => ⟨u z, humem z⟩
            continuous_toFun := hucont.subtype_mk _ }
        refine ⟨G, L, ?_, ?_, ?_⟩
        · intro p x
          apply Subtype.ext
          simp [G, u]
        · intro D hD
          obtain ⟨A, hA, hAe⟩ := hgcell D hD
          refine ⟨A, hA, ?_⟩
          intro p p' x hx'
          have h := hAe p p' x hx'
          -- At the end of the segment the old parameter has coefficient
          -- zero; consequently this is exactly the endpoint assertion.
          simpa [G, u] using h
        · intro Q hQ t p hp x
          let J : Set (Fin k → ℝ) := ((↑) : P → (Fin k → ℝ)) '' Q
          have hJconv : Convex ℝ J := by
            rcases hQ.1 with ⟨s, hs⟩
            change Convex ℝ (((↑) : P → (Fin k → ℝ)) '' Q)
            rw [hs]
            exact convex_convexHull ℝ _
          have hpJ : (p : Fin k → ℝ) ∈ J := ⟨p, hp, rfl⟩
          have hepJ : (g (p, x) : Fin k → ℝ) ∈ J :=
            ⟨g (p, x), hgface Q hQ p hp x, rfl⟩
          have hm :
              (1 - (t : ℝ)) • (p : Fin k → ℝ) +
                  (t : ℝ) • (g (p, x) : Fin k → ℝ) ∈ J :=
            (convex_iff_add_mem.mp hJconv hpJ hepJ
              (sub_nonneg.mpr (unitInterval.le_one t))
              (unitInterval.nonneg t) (by ring))
          obtain ⟨q, hqin, hq⟩ := hm
          have heq : G (t, p, x) = q := by
            apply Subtype.ext
            -- `hq` says that the value in the ambient vector space is `q`.
            simpa [G, u] using hq.symm
          rw [heq]
          exact hqin
    · letI : Subsingleton P := not_nontrivial_iff_subsingleton.mp hnon
      let G : C(I × P × X, P) :=
        { toFun := fun z => z.2.1
          continuous_toFun := continuous_fst.comp continuous_snd }
      have exK : Nonempty (Subdivision P) := by
        by_cases hp : (P : Set (Fin k → ℝ)).Nonempty
        · obtain ⟨z, hz⟩ := hp
          let p : P := ⟨z, hz⟩
          have hset : P = ({z} : Set (Fin k → ℝ)) := by
            ext w
            constructor
            · intro hw
              have hEq : (⟨w, hw⟩ : P) = p := Subsingleton.elim _ _
              have e : w = z :=
                congrArg (fun q : P => (q : Fin k → ℝ)) hEq
              simpa [e]
            · intro hw
              have e : w = z := Set.mem_singleton_iff.mp hw
              simpa [e] using hz
          exact ⟨{
            complex := FamiliesProof.singletonComplex z
            faces_finite := FamiliesProof.singletonComplex_faces_finite z
            space_eq := by
              simpa [hset] using
                (FamiliesProof.singletonComplex_space z) }⟩
        · have hp' : P = (∅ : Set (Fin k → ℝ)) :=
            Set.not_nonempty_iff_eq_empty.mp hp
          exact ⟨{
            complex := (⊥ : Geometry.SimplicialComplex ℝ (Fin k → ℝ))
            faces_finite := by
              rw [Geometry.SimplicialComplex.faces_bot]
              exact Set.finite_empty
            space_eq := by
              simpa [hp'] using
                (Geometry.SimplicialComplex.space_bot
                  (𝕜 := ℝ) (E := (Fin k → ℝ))) }⟩
      obtain ⟨K⟩ := exK
      refine ⟨G, K, ?_, ?_, ?_⟩
      · intro p x
        rfl
      · intro D hD
        refine ⟨∅, ?_, ?_⟩
        · simp
        · intro p p' x hx
          change (p.1 : P) = p'.1
          exact Subsingleton.elim _ _
      · intro Q hQ t p hp x
        change p ∈ Q
        exact hp
  obtain ⟨G, K, hGzero, hGone, hGface⟩ := hmotion
  have hx : Continuous (fun z : I × P × X => z.2.2) :=
    continuous_snd.comp continuous_snd
  let GX : C(I × P × X, P × X) :=
    { toFun := fun z => (G z, z.2.2)
      continuous_toFun := G.continuous.prodMk hx }
  let F : C(I × P × X, T) := f.comp GX
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro p x
    change f (G (0, p, x), x) = f (p, x)
    rw [hGzero p x]
  · refine ⟨K, ?_⟩
    intro D hD
    obtain ⟨A, hAk, hA⟩ := hGone D hD
    refine ⟨A, hAk, ?_⟩
    intro p p' x hx'
    change f (G (1, p.1, x), x) = f (G (1, p'.1, x), x)
    rw [hA p p' x hx']
  · intro S hf
    intro a b x hx'
    change f (G (a.1, a.2, x), x) = f (G (b.1, b.2, x), x)
    exact hf _ _ x hx'
  · intro Q hQ S' hf
    intro a b x hx'
    change f (G (a.1, a.2.1, x), x) = f (G (b.1, b.2.1, x), x)
    let qa : Q := ⟨G (a.1, a.2.1, x),
      hGface Q hQ a.1 a.2.1 a.2.2 x⟩
    let qb : Q := ⟨G (b.1, b.2.1, x),
      hGface Q hQ b.1 b.2.1 b.2.2 x⟩
    exact hf qa qb x hx'
/-ResultProofEnd-/
/-ResultEnd-/
/-- **Lemma B.0.1**, bi-Lipschitz variant (part 4 of the paper). -/
/-ResultBegin-/
theorem biLipschitz
    {X T : Type*} [MetricSpace X] [MetricSpace T] [CompactSpace X]
    {P : Set (Fin k → ℝ)} (_hP : IsPolyhedron P)
    {ι : Type*}
    (U : ι → Set X) (_hUopen : ∀ α, IsOpen (U α))
    (ρ : PartitionOfUnity ι X univ) (_hρ : ρ.IsSubordinate U)
    (f : C(P × X, T))
    (slice : P → (X ≃ₜ T))
    (_h_slice_eq : ∀ p : P, ∀ x : X, f (p, x) = slice p x)
    (L : NNReal)
    (_hf_joint     : LipschitzWith L f.toFun)
    (_hf_slice_inv : ∀ p : P, LipschitzWith L (slice p).symm) :
    ∃ F : C(I × P × X, T), ∃ L' : NNReal, ∃ Slice : I × P → (X ≃ₜ T),
      (∀ p : P, ∀ x : X, F (0, p, x) = f (p, x)) ∧
      (∀ t : I, ∀ p : P, ∀ x : X, F (t, p, x) = Slice (t, p) x) ∧
      (∃ K : Subdivision P,
         ∀ D ∈ K.complex.facets,
            AdaptedTo U k
              (fun q : closedCell P D × X => F (1, q.1.1, q.2))) ∧
      (∀ S : Set X, Supported (f := f.toFun) S →
          Supported (fun q : (I × P) × X => F (q.1.1, q.1.2, q.2)) S) ∧
      (∀ Q : Set P, IsBoundarySubpolyhedron Q →
        ∀ S' : Set X,
          Supported (fun q : Q × X => f (q.1.1, q.2)) S' →
            Supported (fun q : (I × Q) × X => F (q.1.1, q.1.2.1, q.2)) S') ∧
      (∀ tp : I × P, LipschitzWith L' (Slice tp)) ∧
      (∀ tp : I × P, LipschitzWith L' (Slice tp).symm) :=
/-ResultProofBegin-/ by
  classical
  -- A triangulation itself is not an issue on the Lipschitz side; the
  -- pulling triangulation of a finite hull is enough.  Isolating it here is
  -- useful even for the stationary cases below.
  have exK : Nonempty (Subdivision P) := by
    obtain ⟨s, hs⟩ := _hP
    obtain ⟨M, hMf, hMs⟩ :=
      FamiliesProof.exists_finiteComplex_convexHull
        (E := (Fin k → ℝ)) s
    exact ⟨{ complex := M,
             faces_finite := hMf,
             space_eq := hMs.trans hs.symm }⟩
  -- A restriction of a jointly Lipschitz family to a fibre is Lipschitz
  -- with the same constant.  Thus any motion which only changes the
  -- parameter (not `x`) automatically gives the forward estimate; no
  -- compactness argument is involved here.
  have hfwd : ∀ p : P, LipschitzWith L (slice p) := by
    intro p
    -- use the metric characterisation, since the section `x ↦ (p,x)` is
    -- an isometry for the max product metric
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := _hf_joint.dist_le_mul (x := (p, x)) (y := (p, y))
    simpa [_h_slice_eq] using h
  -- If a subcover already has at most `k` members no vertices have to move.
  -- This is a genuine terminal case of (4): the original slices, and their
  -- inverses, are exactly the required ones.
  by_cases hsmall :
      ∃ A : Finset ι, A.card ≤ k ∧
        (Set.univ : Set X) ⊆ ⋃ i ∈ A, U i
  · obtain ⟨A, hAk, hAcov⟩ := hsmall
    obtain ⟨K⟩ := exK
    let F : C(I × P × X, T) :=
      f.comp
        { toFun := fun z : I × P × X => (z.2.1, z.2.2)
          continuous_toFun :=
            (continuous_fst.comp continuous_snd).prodMk
              (continuous_snd.comp continuous_snd) }
    let Sl : I × P → (X ≃ₜ T) := fun z => slice z.2
    refine ⟨F, L, Sl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p x
      rfl
    · intro t p x
      change f (p, x) = slice p x
      exact _h_slice_eq p x
    · refine ⟨K, ?_⟩
      intro D hD
      refine ⟨A, hAk, ?_⟩
      intro p p' x hx
      have hx' : x ∈ (⋃ i ∈ A, U i) := hAcov (by trivial)
      exact (hx hx').elim
    · intro S hs
      intro a b x hx
      change f (a.2, x) = f (b.2, x)
      exact hs _ _ x hx
    · intro Q hQ S' hs
      intro a b x hx
      change f (a.2.1, x) = f (b.2.1, x)
      exact hs (a.2) (b.2) x hx
    · intro tp
      exact hfwd tp.2
    · intro tp
      exact _hf_slice_inv tp.2
  · -- The other easy terminal case, often obscured by the quantitative
    -- statement, is a subsingleton parameter polytope.  No matter how many
    -- colours the cover has, a cell contains at most one parameter; hence
    -- the empty set of colours works.  In particular this also settles the
    -- zero-dimensional (`k = 0`) portion of the Lipschitz theorem.
    by_cases hntr : Nontrivial P
    · letI : Nontrivial P := hntr
      -- A nontrivial subset of `ℝ⁰` cannot occur.  Recording the honest
      -- inequality on the ambient dimension is convenient in the remaining
      -- fragmentation case (for example a one-element subcover is then a
      -- *small* subcover).
      have hk0 : k ≠ 0 := by
        intro hz
        have hsP' : Subsingleton P := by
          constructor
          intro p q
          apply Subtype.ext
          subst k
          funext i
          exact Fin.elim0 i
        exact (not_subsingleton_iff_nontrivial.mpr hntr) hsP'
      have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      -- Another completely stationary case is worth removing here.  The
      -- support conclusion only concerns variation in the *parameter*; if
      -- the original family has none, the empty set of colours works on
      -- every simplex, independently of the cover.
      by_cases hpar : ∀ p p' : P, ∀ x : X, f (p, x) = f (p', x)
      · obtain ⟨K⟩ := exK
        let F : C(I × P × X, T) :=
          f.comp
            { toFun := fun z : I × P × X => (z.2.1, z.2.2)
              continuous_toFun :=
                (continuous_fst.comp continuous_snd).prodMk
                  (continuous_snd.comp continuous_snd) }
        let Sl : I × P → (X ≃ₜ T) := fun z => slice z.2
        refine ⟨F, L, Sl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro p x
          rfl
        · intro t p x
          change f (p, x) = slice p x
          exact _h_slice_eq p x
        · refine ⟨K, ?_⟩
          intro D hD
          refine ⟨(∅ : Finset ι), ?_, ?_⟩
          · simp
          · intro p p' x hx
            change f (p.1, x) = f (p'.1, x)
            exact hpar _ _ _
        · intro S hs
          intro a b x hx
          change f (a.2, x) = f (b.2, x)
          exact hs _ _ x hx
        · intro Q hQ S' hs
          intro a b x hx
          change f (a.2.1, x) = f (b.2.1, x)
          exact hs (a.2) (b.2) x hx
        · intro tp
          exact hfwd tp.2
        · intro tp
          exact _hf_slice_inv tp.2
      · -- A final stationary case is slightly less obvious than `hpar`.
        -- The family may vary, but all of its variation might already be
        -- supported in at most `k` members of the cover.  In that situation
        -- every cell is adapted before the construction begins (and this is
        -- weaker than a small subcover of *all* of `X`).
        by_cases hsupp :
            ∃ A : Finset ι, A.card ≤ k ∧
              Supported (f := f.toFun) (⋃ i ∈ A, U i)
        · obtain ⟨A, hAk, hAf⟩ := hsupp
          obtain ⟨K⟩ := exK
          let F : C(I × P × X, T) :=
            f.comp
              { toFun := fun z : I × P × X => (z.2.1, z.2.2)
                continuous_toFun :=
                  (continuous_fst.comp continuous_snd).prodMk
                    (continuous_snd.comp continuous_snd) }
          let Sl : I × P → (X ≃ₜ T) := fun z => slice z.2
          refine ⟨F, L, Sl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro p x
            rfl
          · intro t p x
            change f (p, x) = slice p x
            exact _h_slice_eq p x
          · refine ⟨K, ?_⟩
            intro D hD
            refine ⟨A, hAk, ?_⟩
            intro p p' x hx
            change f (p.1, x) = f (p'.1, x)
            exact hAf _ _ x hx
          · intro S hs
            intro a b x hx
            change f (a.2, x) = f (b.2, x)
            exact hs _ _ x hx
          · intro Q hQ S' hs
            intro a b x hx
            change f (a.2.1, x) = f (b.2.1, x)
            exact hs (a.2) (b.2) x hx
          · intro tp
            exact hfwd tp.2
          · intro tp
            exact _hf_slice_inv tp.2
        · -- Some quantitative degeneracies in this branch collapse back
          -- to `hpar`.  With constant zero there can be no two values at
          -- all in a jointly Lipschitz family.
          have hL0 : L ≠ 0 := by
            intro hzero
            apply hpar
            intro p p' x
            have hh :=
              _hf_joint.dist_le_mul (x := (p, x)) (y := (p', x))
            have hh' : dist (f (p, x)) (f (p', x)) ≤ 0 := by
              simpa [hzero] using hh
            exact dist_le_zero.mp hh'
          -- For the same reason a subsingleton domain has no such branch.
          -- We use a single fibre equivalence to transport that fact to the
          -- codomain--this does not require nonemptiness of `X`.
          have hXn : Nontrivial X := by
            apply not_subsingleton_iff_nontrivial.mp
            intro hsx
            letI : Subsingleton X := hsx
            let p0 : P := Classical.choice (inferInstance : Nonempty P)
            have hst : Subsingleton T := by
              constructor
              intro a b
              have e : (slice p0).symm a = (slice p0).symm b :=
                Subsingleton.elim _ _
              have ee := congrArg (fun x : X => slice p0 x) e
              simpa using ee
            letI : Subsingleton T := hst
            apply hpar
            intro p p' x
            exact Subsingleton.elim _ _
          -- There are no genuinely varying finite domains either.  A finite
          -- metric space (and any space homeomorphic to it) is discrete and
          -- totally disconnected, whereas a convex parameter set is
          -- preconnected.  A continuous map from the latter to the former
          -- therefore has singleton image.
          by_cases hfiniteX : Finite X
          · letI : Finite X := hfiniteX
            let p0 : P := Classical.choice (inferInstance : Nonempty P)
            letI : Finite T := Finite.of_equiv X (slice p0).toEquiv
            have hcP : Convex ℝ (P : Set (Fin k → ℝ)) := by
              obtain ⟨s, hs⟩ := _hP
              rw [hs]
              exact convex_convexHull ℝ _
            letI : PreconnectedSpace P :=
              isPreconnected_iff_preconnectedSpace.mp hcP.isPreconnected
            have hpconst : ∀ p p' : P, ∀ x : X,
                f (p, x) = f (p', x) := by
              intro p p' x
              have hg : Continuous (fun q : P => f (q, x)) :=
                f.continuous.comp (continuous_id.prodMk continuous_const)
              have himg : IsPreconnected
                  (Set.range (fun q : P => f (q, x))) :=
                isPreconnected_range hg
              exact himg.subsingleton ⟨p, rfl⟩ ⟨p', rfl⟩
            exact (hpar hpconst).elim
          · letI : Infinite X := not_finite_iff_infinite.mp hfiniteX
            -- More generally all totally disconnected domains disappear for
            -- the same reason; no finiteness is used in the image argument.
            -- A fibre equivalence transports total disconnectedness to `T`.
            by_cases htdX : TotallyDisconnectedSpace X
            · letI : TotallyDisconnectedSpace X := htdX
              let p0 : P := Classical.choice (inferInstance : Nonempty P)
              letI : TotallyDisconnectedSpace T :=
                Homeomorph.totallyDisconnectedSpace (slice p0)
              have hcP : Convex ℝ (P : Set (Fin k → ℝ)) := by
                obtain ⟨s, hs⟩ := _hP
                rw [hs]
                exact convex_convexHull ℝ _
              letI : PreconnectedSpace P :=
                isPreconnected_iff_preconnectedSpace.mp hcP.isPreconnected
              have hpconst : ∀ p p' : P, ∀ x : X,
                  f (p, x) = f (p', x) := by
                intro p p' x
                have hg : Continuous (fun q : P => f (q, x)) :=
                  f.continuous.comp (continuous_id.prodMk continuous_const)
                have himg : IsPreconnected
                    (Set.range (fun q : P => f (q, x))) :=
                  isPreconnected_range hg
                exact himg.subsingleton ⟨p, rfl⟩ ⟨p', rfl⟩
              exact (hpar hpconst).elim
            ·
              -- Just as in the continuous reduction, infinitary colours are
              -- a red herring here.  Compactness of the *partition* (not a
              -- choice of a finite subcover) shows that only finitely many
              -- functions are nonzero.  Keeping their finite type, together
              -- with its size inequality, is the clean starting point for the
              -- remaining homeomorphism-fragmentation problem.
              have no_small_cover :
                  ∀ A : Finset ι, A.card ≤ k →
                    ¬ (Set.univ : Set X) ⊆ ⋃ i ∈ A, U i := by
                intro A hA hc
                exact hsmall ⟨A, hA, hc⟩
              let W : Set ι := {i | (Function.support (ρ i)).Nonempty}
              have hW : W.Finite := by
                simpa [W] using ρ.locallyFinite.finite_nonempty_of_compact
              let C : Finset ι := hW.toFinset
              have hzero : ∀ i, i ∉ C → ∀ x : X, ρ i x = 0 := by
                intro i hi x
                by_contra hn
                have hiW : i ∈ W := by
                  refine ⟨x, ?_⟩
                  exact hn
                exact hi (by simpa [C] using hiW)
              have hzeroU : ∀ i, ∀ x : X, x ∉ U i → ρ i x = 0 := by
                intro i x hx
                by_contra hn
                have hs : x ∈ Function.support (ρ i) := hn
                have ht : x ∈ tsupport (ρ i) := subset_tsupport _ hs
                exact hx (_hρ i ht)
              have hCcover :
                  (Set.univ : Set X) ⊆ ⋃ i ∈ C, U i := by
                intro x hx
                obtain ⟨i, hi⟩ := ρ.exists_pos
                  (by trivial : x ∈ (Set.univ : Set X))
                have hic : i ∈ C := by
                  by_contra hin
                  have hz := hzero i hin x
                  linarith
                have hxu : x ∈ U i := by
                  by_contra hxn
                  have hz := hzeroU i x hxn
                  linarith
                exact Set.mem_iUnion_of_mem i
                  (Set.mem_iUnion_of_mem hic hxu)
              have hkactive : k < C.card :=
                Nat.lt_of_not_ge (fun hle =>
                  no_small_cover C hle hCcover)
              let J := {i : ι // i ∈ C}
              let V : J → Set X := fun i => U i.val
              let r : J → C(X, ℝ) := fun i => ρ i.val
              have hkJ : k < Fintype.card J := by
                change k < Fintype.card {i : ι // i ∈ C}
                simpa using hkactive
              have hr0 : ∀ i : J, ∀ x : X, x ∉ V i → r i x = 0 := by
                intro i x hx
                exact hzeroU i.val x hx
              have hrnonneg : ∀ i : J, ∀ x : X, 0 ≤ r i x := by
                intro i x
                exact ρ.nonneg i.val x
              have hsumC : ∀ x : X, ∑ i ∈ C, ρ i x = 1 := by
                intro x
                have hsub : Function.support (fun i => ρ i x) ⊆ (↑C : Set ι) := by
                  intro i hi
                  have hiW : i ∈ W := ⟨x, hi⟩
                  have hic : i ∈ C := by simpa [C] using hiW
                  exact hic
                calc
                  (∑ i ∈ C, ρ i x) = ∑ᶠ i, ρ i x :=
                    (finsum_eq_sum_of_support_subset _ hsub).symm
                  _ = 1 := ρ.sum_eq_one (by simp)
              have hrsum : ∀ x : X, ∑ i : J, r i x = 1 := by
                intro x
                change (∑ i : {i : ι // i ∈ C}, ρ i.val x) = 1
                change
                  (∑ i ∈
                      (Finset.univ : Finset {i : ι // i ∈ C}),
                        ρ i.val x) = 1
                rw [Finset.univ_eq_attach C,
                  Finset.sum_attach C (fun i => ρ i x)]
                exact hsumC x
              -- In this branch the uniform bi-Lipschitz constants are
              -- genuinely at least one.  This little cancellation is handy
              -- for any later small-perturbation argument: the inverse
              -- estimate has to be used as well as the forward one.
              have hLone : (1 : ℝ) ≤ (L : ℝ) := by
                letI : Nontrivial X := hXn
                obtain ⟨x, y, hxy⟩ := exists_pair_ne X
                let p0 : P := Classical.choice
                  (inferInstance : Nonempty P)
                have hpos : 0 < dist x y := dist_pos.mpr hxy
                have hfor := (hfwd p0).dist_le_mul x y
                have hinv := (_hf_slice_inv p0).dist_le_mul
                  (slice p0 x) (slice p0 y)
                have hinv' : dist x y ≤ (L : ℝ) *
                    dist (slice p0 x) (slice p0 y) := by
                  simpa using hinv
                have hnon : 0 ≤ (L : ℝ) := L.coe_nonneg
                have hmul : (L : ℝ) *
                      dist (slice p0 x) (slice p0 y) ≤
                    (L : ℝ) * ((L : ℝ) * dist x y) :=
                  mul_le_mul_of_nonneg_left hfor hnon
                have hcomp : dist x y ≤
                    (L : ℝ) * ((L : ℝ) * dist x y) :=
                  le_trans hinv' hmul
                have hcomp' : (1 : ℝ) * dist x y ≤
                    ((L : ℝ) * (L : ℝ)) * dist x y := by
                  simpa [mul_assoc] using hcomp
                have hsquare : (1 : ℝ) ≤ (L : ℝ) * (L : ℝ) :=
                  le_of_mul_le_mul_right hcomp' hpos
                nlinarith
              -- Thus the first genuinely moving Lipschitz case is *finite*:
              -- a positive-dimensional nontrivial parameter polytope, a
              -- nontrivial metric domain and positive Lipschitz constant, and a
              -- finite family of more than `k` active colours.  It must fragment
              -- a path of actual homeomorphisms; the barycentric endpoint of the
              -- continuous lemma is not a bundled equivalence.
              -- isolate the remaining problem as a genuinely geometric,
              -- small-in-the-variable-of-`X` motion inside the parameter
              -- polytope.  Once such a motion is obtained all the analytic
              -- assertions of (4), including surjectivity, follow from the
              -- contraction argument, without any differentiation on `X`.
              -- Notice in particular the strict `L^2 c < 1`: continuity of
              -- a partition of unity does not by itself give this estimate.
              have small_motion :
                  ∃ c : NNReal, L*L*c < 1 ∧
                    ∃ G : C(I × P × X, P), ∃ M : Subdivision P,
                      (∀ p : P, ∀ x : X, G (0,p,x) = p) ∧
                      (∀ D ∈ M.complex.facets,
                        ∃ A : Finset ι, A.card ≤ k ∧
                          ∀ (p p' : closedCell P D) (x : X),
                            x ∉ (⋃ i ∈ A, U i) →
                              G (1, p.1, x) = G (1, p'.1, x)) ∧
                      (∀ Q : Set P, IsBoundarySubpolyhedron Q →
                        ∀ t : I, ∀ p : P, p ∈ Q → ∀ x : X,
                          G (t,p,x) ∈ Q) ∧
                      (∀ t : I, ∀ p : P,
                        LipschitzWith c (fun x : X => G (t,p,x))) := by
                -- It is enough to construct the endpoint of the motion.  The
                -- straight segment in a convex polytope keeps every face and
                -- never increases the fibrewise Lipschitz bound.
                have hconv : Convex ℝ (P : Set (Fin k → ℝ)) := by
                  obtain ⟨v,hv⟩ := _hP
                  rw [hv]
                  exact convex_convexHull ℝ _
                have small_endpoint :
                    ∃ c : NNReal, L*L*c < 1 ∧
                      ∃ g : C(P × X, P), ∃ M : Subdivision P,
                        (∀ D ∈ M.complex.facets,
                          ∃ A : Finset ι, A.card ≤ k ∧
                            ∀ (p p' : closedCell P D) (x : X),
                              x ∉ (⋃ i ∈ A, U i) →
                                g (p.1,x) = g (p'.1,x)) ∧
                        (∀ Q : Set P, IsBoundarySubpolyhedron Q →
                          ∀ p : P, p ∈ Q → ∀ x : X, g (p,x) ∈ Q) ∧
                        (∀ p : P,
                          LipschitzWith c (fun x : X => g (p,x))) := by
                      -- Replace the purely continuous coefficients by the standard
                      -- distance-to-the-complement coefficients.  Their common
                      -- Lipschitz constant is the only analytic input needed below.
                      -- `hXn` supplies the instance (and hence nonemptiness) in this branch.
                      letI : Nontrivial X := hXn
                      have vcov : ∀ x : X, ∃ j : J, x ∈ V j := by
                        intro x
                        have xx := hCcover (show x ∈ (Set.univ : Set X) by trivial)
                        rcases Set.mem_iUnion.mp xx with ⟨i, xx⟩
                        rcases Set.mem_iUnion.mp xx with ⟨hi, hx⟩
                        refine ⟨⟨i, hi⟩, ?_⟩
                        exact hx
                      obtain ⟨lam, K₀, hlamLip, hlamNon, hlamOut, hlamSum⟩ :=
                        FamiliesProof.finite_lipschitz_partition V
                          (fun j => _hUopen j.val) vcov
                      have Jne : Nonempty J :=
                        Fintype.card_pos_iff.mp (lt_of_le_of_lt (Nat.zero_le _) hkJ)
                      let j₀ : J := Classical.choice Jne
                      -- This statement is now entirely finite-dimensional PL
                      -- geometry.  Notice that it no longer mentions `X`, the
                      -- partition of unity, or the target maps.  In addition to
                      -- the qualitative sparse copies, they must have arbitrarily
                      -- small pairwise displacement; ordinary edge bins do not yet
                      -- supply this face-compatible refinement.
                      have fine_copies : ∀ δ : ℝ, 0 < δ →
                            ∃ φ : J → C(P,P), ∃ M : Subdivision P,
                              (∀ D ∈ M.complex.facets,
                                ∃ A : Finset J, A.card ≤ k ∧
                                  ∀ j : J, j ∉ A →
                                    ∀ p p' : closedCell P D,
                                      φ j p.1 = φ j p'.1) ∧
                              (∀ Q : Set P, IsBoundarySubpolyhedron Q →
                                ∀ j : J, ∀ p : P, p ∈ Q → φ j p ∈ Q) ∧
                              (∀ j : J, ∀ p : P,
                                dist (φ j p) (φ j₀ p) ≤ δ) := by
                        -- Genuine remaining PL problem: arbitrarily fine
                        -- face-compatible ordered-bin copies.  It depends only
                        -- on the finite colour set and the convex polytope.
                        -- The Lipschitz/metric part below is now completely
                        -- formal and will consume any such copies.
                        intro δ hδ
                        by_cases hstar : ∃ z : P, ∀ Q : Set P,
                            IsBoundarySubpolyhedron Q → Q.Nonempty → z ∈ Q
                        · rcases hstar with ⟨z,hz⟩
                          obtain ⟨M⟩ := exK
                          let phi : J → C(P,P) := fun _ => ContinuousMap.const P z
                          refine ⟨phi,M,?_,?_,?_⟩
                          · intro D hD
                            refine ⟨(∅ : Finset J), ?_, ?_⟩
                            · simp
                            · intro j hj p p'
                              rfl
                          · intro Q hQ j p hp
                            change z ∈ Q
                            exact hz Q hQ ⟨p,hp⟩
                          · intro j p
                            change dist z z ≤ δ
                            simp [le_of_lt hδ]
                        · -- The remaining cases begin only when some genuine
                          -- edge occurs in the parameter polytope.  It is useful to
                          -- discharge all zero-dimensional subdivisions: in that
                          -- case every facet is a vertex and the identity maps are
                          -- already (arbitrarily close) copies.  This quantitative
                          -- observation is stronger than the analogous stationary
                          -- case above since it occurs after the arbitrary `δ` has
                          -- been fixed.
                          by_cases hzdim : ∃ M : Subdivision P,
                              ∀ D ∈ M.complex.facets, D.card = 1
                          · rcases hzdim with ⟨M,hM⟩
                            let phi : J → C(P,P) := fun _ => ContinuousMap.id P
                            refine ⟨phi,M,?_,?_,?_⟩
                            · intro D hD
                              refine ⟨(∅ : Finset J), by simp, ?_⟩
                              intro j hj p p'
                              dsimp [phi]
                              obtain ⟨z,hz⟩ := Finset.card_eq_one.mp (hM D hD)
                              subst D
                              apply Subtype.ext
                              have hp : (p.1 : Fin k → ℝ) = z := by
                                have hm := p.property
                                change (p.1 : Fin k → ℝ) ∈
                                  convexHull ℝ (({z} : Finset (Fin k → ℝ)) :
                                    Set (Fin k → ℝ)) at hm
                                simpa [convexHull_singleton] using hm
                              have hp' : (p'.1 : Fin k → ℝ) = z := by
                                have hm := p'.property
                                change (p'.1 : Fin k → ℝ) ∈
                                  convexHull ℝ (({z} : Finset (Fin k → ℝ)) :
                                    Set (Fin k → ℝ)) at hm
                                simpa [convexHull_singleton] using hm
                              exact hp.trans hp'.symm
                            · intro Q hQ j p hp
                              change p ∈ Q
                              exact hp
                            · intro j p
                              change dist p p ≤ δ
                              simpa using (le_of_lt hδ)
                          · -- A non-degenerate straight segment can already be treated in
                            -- its full ambient space.  The interleaved copies make one jump per
                            -- fine edge; all other colours are literally constant.
                            by_cases hseg : ∃ l r : Fin k → ℝ, l ≠ r ∧
                                P = segment ℝ l r
                            · rcases hseg with ⟨l,r,hlr,hPr⟩
                              subst P
                              let n : ℕ := Fintype.card J
                              have hn : 0 < n := by
                                dsimp [n]
                                exact Fintype.card_pos_iff.mpr Jne
                              let e : J ≃ Fin n := Fintype.equivFin J
                              obtain ⟨q,hqbig⟩ : ∃ q : ℕ, ‖r-l‖ / δ < q :=
                                exists_nat_gt (‖r-l‖ / δ)
                              have hq : 0 < q := by
                                have hnon : 0 ≤ ‖r-l‖ / δ := by positivity
                                exact_mod_cast (lt_of_le_of_lt hnon hqbig)
                              let phi : J → C({x : Fin k → ℝ // x ∈ segment ℝ l r},
                                  {x : Fin k → ℝ // x ∈ segment ℝ l r}) := fun j =>
                                    FamiliesProof.segmentCopy l r hlr q n (e j).val hq
                              let N : ℕ := q*n
                              have hN : 0 < N := Nat.mul_pos hq hn
                              let M : Subdivision (segment ℝ l r) :=
                                { complex := FamiliesProof.lineComplex l r N hN hlr
                                  faces_finite := FamiliesProof.lineComplex_faces_finite l r N hN hlr
                                  space_eq := FamiliesProof.lineComplex_space l r N hN hlr }
                              refine ⟨phi, M, ?_, ?_, ?_⟩
                              · intro D hD
                                change D ∈ (FamiliesProof.lineComplex l r N hN hlr).facets at hD
                                rcases FamiliesProof.lineComplex_facet l r N hN hlr hD
                                  with ⟨m,hm,rfl⟩
                                let active : J := e.symm ⟨m % n, Nat.mod_lt _ hn⟩
                                refine ⟨{active}, ?_, ?_⟩
                                · have kpos : 0 < k := by
                                    by_contra hh
                                    have kz : k = 0 := Nat.eq_zero_of_not_pos hh
                                    subst k
                                    exact hlr (Subsingleton.elim _ _)
                                  simp
                                  omega
                                · intro j hj p p'
                                  have jne : m % n ≠ (e j).val := by
                                    intro heq
                                    have : j = active := by
                                      dsimp [active]
                                      apply e.injective
                                      apply Fin.val_inj.mp
                                      simpa using heq.symm
                                    exact hj (Finset.mem_singleton.mpr this)
                                  -- Membership in the closed cell is exactly membership in the
                                  -- embedded edge convex hull.
                                  exact FamiliesProof.segmentCopy_const_edge hlr hq hn hm jne
                                    (e j).isLt p.property p'.property
                              · intro Q hQ j p hp
                                rcases hQ with ⟨⟨w,hw⟩, hfront, hExt⟩
                                change (phi j p : {x : Fin k → ℝ // x ∈ segment ℝ l r}) ∈ Q
                                have hp' : (p : Fin k → ℝ) ∈
                                    (((↑) : {x : Fin k → ℝ // x ∈ segment ℝ l r} → Fin k → ℝ) '' Q) :=
                                      ⟨p, hp, rfl⟩
                                have hcB : Convex ℝ
                                    (((↑) : {x : Fin k → ℝ // x ∈ segment ℝ l r} → Fin k → ℝ) '' Q) := by
                                  rw [hw]
                                  exact convex_convexHull ℝ _
                                have hb := FamiliesProof.segmentCopy_mem_extreme hlr hq hn
                                  (e j).isLt hcB hExt p hp'
                                change (phi j p : Fin k → ℝ) ∈
                                  (((↑) : {x : Fin k → ℝ // x ∈ segment ℝ l r} → Fin k → ℝ) '' Q) at hb
                                rcases hb with ⟨z,hz,heq⟩
                                have : z = phi j p := Subtype.ext heq
                                simpa [this] using hz
                              · intro j p
                                have hbd := FamiliesProof.segmentCopy_dist hlr hq
                                  (e j).isLt (e j₀).isLt p
                                change dist (phi j p) (phi j₀ p) ≤ δ
                                calc dist (phi j p) (phi j₀ p) ≤ (1/(q:ℝ)) * ‖r-l‖ := hbd
                                _ ≤ δ := by
                                  have qq : (0:ℝ) < q := by exact_mod_cast hq
                                  calc
                                    (1/(q:ℝ)) * ‖r-l‖ = ‖r-l‖ / q := by ring
                                    _ ≤ δ := (div_le_iff₀ qq).2 (by
                                      have := hqbig
                                      have hd : 0 < δ := hδ
                                      have hh := ((div_lt_iff₀ hd).1 hqbig)
                                      nlinarith)
                            · -- There is no leftover case on a line: every finite hull in
                              -- `ℝ ^ (Fin 1)` is its extremal segment. This eliminates a
                              -- deceptively awkward edge branch before building genuine grids.
                              by_cases hle1 : k ≤ 1
                              · have hkEq : k = 1 := Nat.le_antisymm hle1 hkpos
                                subst k
                                exfalso
                                apply hseg
                                obtain ⟨s, hsP⟩ := _hP
                                have sn : s.Nonempty := by
                                  have hnP : (convexHull ℝ (s : Set (Fin 1 → ℝ))).Nonempty := by
                                    let p : P := Classical.choice (inferInstance : Nonempty P)
                                    exact ⟨p.1, by simpa [← hsP] using p.property⟩
                                  have hn' : ((s : Set (Fin 1 → ℝ))).Nonempty :=
                                    (convexHull_nonempty_iff).1 hnP
                                  simpa using hn'
                                obtain ⟨l,r,hl,hr,hull⟩ :=
                                  FamiliesProof.convexHull_fin1_eq_segment s sn
                                have lr : l ≠ r := by
                                  intro he
                                  have peq : (P : Set (Fin 1 → ℝ)) = ({l} : Set (Fin 1 → ℝ)) := by
                                    rw [hsP, hull, he, segment_same]
                                  have hsPsub : Subsingleton P := by
                                    constructor
                                    intro a b
                                    apply Subtype.ext
                                    have aa : (a : Fin 1 → ℝ) = l :=
                                      Set.mem_singleton_iff.mp (by simpa [peq] using a.property)
                                    have bb : (b : Fin 1 → ℝ) = l :=
                                      Set.mem_singleton_iff.mp (by simpa [peq] using b.property)
                                    exact aa.trans bb.symm
                                  exact (not_subsingleton_iff_nontrivial.mpr hntr) hsPsub
                                exact ⟨l,r,lr, hsP.trans hull⟩
                              · -- higher-dimensional or bent-face polytopes need simultaneous
                                -- barycentric grids after all low-dimensional hulls have gone.
                                have ktwo : 2 ≤ k := by omega
                                -- Removing repeated/collinear vertices is not the issue here:
                                -- every presentation of the remaining polytope has at least
                                -- three vertices already. The obstruction is a triangulation,
                                -- not a low-cardinality convex hull.
                                obtain ⟨s, hs⟩ := _hP
                                have hsne : Nonempty {x : Fin k → ℝ //
                                    x ∈ convexHull ℝ (s : Set (Fin k → ℝ))} := by
                                  let p : P := Classical.choice (inferInstance : Nonempty P)
                                  exact ⟨p.1, by simpa [← hs] using p.property⟩
                                have hntr' : Nontrivial {x : Fin k → ℝ //
                                    x ∈ convexHull ℝ (s : Set (Fin k → ℝ))} := by
                                  simpa [hs] using hntr
                                have hsseg : ¬ ∃ l r : Fin k → ℝ, l ≠ r ∧
                                    convexHull ℝ (s : Set (Fin k → ℝ)) = segment ℝ l r := by
                                  intro e
                                  obtain ⟨l,r,lr,h⟩ := e
                                  apply hseg
                                  exact ⟨l,r,lr, hs.trans h⟩
                                have manyVertices : 3 ≤ s.card :=
                                  FamiliesProof.three_le_card_of_nontrivial_nosegment
                                    s hsne hntr' hsseg
                                -- In an independent simplex the interleaved construction and
                                -- its finite closed chambers are fully available (including
                                -- the quantitative estimate). What is still needed here is the
                                -- *geometric complex* refining those closed chambers on all
                                -- the lexicographic facets simultaneously.
                                have local_simplex (d q n : ℕ) (hd : 0 < d)
                                    (hq : 0 < q) (hn : 0 < n)
                                    (w : Fin d → (Fin k → ℝ))
                                    (hi : AffineIndependent ℝ w) :
                                    let W := {x : (Fin k → ℝ) //
                                      x ∈ convexHull ℝ (Set.range w)}
                                    ∃ ψ : Fin n → C(W,W),
                                      ∀ b : Fin (d+1) → Fin (q*n),
                                        ∃ A : Finset (Fin n), A.card + 1 ≤ d ∧
                                          ∀ r : Fin n, r ∉ A → ∀ x y : W,
                                            x ∈ FamiliesProof.geoChamber w hi (q*n)
                                              (fun m => (b m).val) →
                                            y ∈ FamiliesProof.geoChamber w hi (q*n)
                                              (fun m => (b m).val) → ψ r x = ψ r y := by
                                  intro
                                  rcases FamiliesProof.simplexCycMaps_chambers hd hq hn w hi with
                                    ⟨ψ,hψ,_,_⟩
                                  exact ⟨ψ,hψ⟩
                                -- The quantitative grid parameter can be selected once for
                                -- the *whole finite configuration*, rather than separately on
                                -- each pulling face.  This removes a real analytic obstruction:
                                -- there is no compactness choice to make while pasting.  What
                                -- remains below is only the compatible geometric subdivision.
                                obtain ⟨qstar, hqstar, hqδ⟩ :=
                                  FamiliesProof.exists_uniform_grid s hδ
                                have face_displacement
                                    {t : Finset (Fin k → ℝ)} (ht : t ⊆ s)
                                    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
                                    (enum : Fin d ≃ t)
                                    (hi : AffineIndependent ℝ
                                      (fun i : Fin d => (enum i : Fin k → ℝ)))
                                    (a b : Fin n)
                                    (x : {x : (Fin k → ℝ) //
                                      x ∈ convexHull ℝ (Set.range
                                        (fun i : Fin d => (enum i : Fin k → ℝ)))}) :
                                    dist
                                      (FamiliesProof.simplexCycMap hd hqstar hn
                                        (fun i : Fin d => (enum i : Fin k → ℝ)) hi a x)
                                      (FamiliesProof.simplexCycMap hd hqstar hn
                                        (fun i : Fin d => (enum i : Fin k → ℝ)) hi b x)
                                      ≤ δ := by
                                  exact le_trans
                                    (FamiliesProof.simplexCycMap_dist_uniform
                                      (s:=s) (t:=t) ht hd hqstar hn enum a b hi x)
                                    hqδ
                                -- As on the qualitative side the coefficient gluing over
                                -- the entire pulling complex is continuous already; no choice
                                -- of support can introduce a discontinuity.  The outstanding
                                -- step here is a *simplicial* common refinement with the
                                -- quantitative chambers.
                                rcases FamiliesProof.exists_globalCoeff s with
                                  ⟨cglobal, cglobal_pos, cglobal_sum,
                                    cglobal_eval, cglobal_face⟩
                                have ordered_face_restriction_quant
                                    {a b n : ℕ} (ha : 0 < a) (hb : 0 < b)
                                    (hn0 : 0 < n)
                                    (inc : Fin a ↪ Fin b) (hinc : StrictMono inc)
                                    (z : Fin b → (Fin k → ℝ))
                                    (hz : AffineIndependent ℝ z) (r0 : Fin n)
                                    (x : {y : (Fin k → ℝ) //
                                      y ∈ convexHull ℝ (Set.range
                                        (fun i : Fin a => z (inc i)))}) :
                                    FamiliesProof.simplexCycMap hb hqstar hn0 z hz r0
                                        (FamiliesProof.faceInclusion inc z x) =
                                      FamiliesProof.faceInclusion inc z
                                        (FamiliesProof.simplexCycMap ha hqstar hn0
                                          (fun i : Fin a => z (inc i))
                                          (FamiliesProof.affineIndependent_comp_embedding
                                            inc hz) r0 x) := by
                                  exact FamiliesProof.simplexCycMap_face ha hb hqstar hn0
                                    inc hinc z hz r0 x
                                -- There is no pasting-of-copies problem left. On a pulling
                                -- face the single global formula (built with the pasted
                                -- coefficients) is literally the cyclic simplex map in
                                -- inherited order.  Thus it is enough that the eventual
                                -- finite geometric complex refine the scalar cut chambers;
                                -- neither continuity nor equality of definitions on their
                                -- intersections are additional obligations.
                                have hcardJpos : 0 < Fintype.card J :=
                                  lt_of_le_of_lt (Nat.zero_le _) hkJ
                                have inherited_global_formula
                                    {t : Finset (Fin k → ℝ)} (ht : FamiliesProof.lexFace s t)
                                    (c : C({x : (Fin k → ℝ) // x ∈ convexHull ℝ (s : Set (Fin k → ℝ))},
                                      s → ℝ))
                                    (hc : ∀ (x : {x : (Fin k → ℝ) //
                                        x ∈ convexHull ℝ (s : Set (Fin k → ℝ))})
                                      (hx : (x : Fin k → ℝ) ∈ convexHull ℝ (t : Set (Fin k → ℝ))),
                                      c x = FamiliesProof.localFaceCoeff s t ht.1
                                        (FamiliesProof.faceEnum_indep ht) ⟨x.1, hx⟩)
                                    (ha' : 0 < (FamiliesProof.facePos s t).card)
                                    (r0 : Fin (Fintype.card J))
                                    (x : {x : (Fin k → ℝ) //
                                      x ∈ convexHull ℝ (s : Set (Fin k → ℝ))})
                                    (hx : (x : Fin k → ℝ) ∈ convexHull ℝ (t : Set (Fin k → ℝ))) :
                                    let w := FamiliesProof.inheritedFace s t
                                    let hi : AffineIndependent ℝ w :=
                                      FamiliesProof.inheritedFace_indep ht
                                    let ux : {z : (Fin k → ℝ) //
                                        z ∈ convexHull ℝ (Set.range w)} :=
                                      ⟨x.1, by
                                        rw [FamiliesProof.range_inheritedFace ht.1]
                                        exact hx⟩
                                    FamiliesProof.globalCopy s c qstar (Fintype.card J) hqstar hcardJpos r0 x =
                                      ((FamiliesProof.simplexCycMap ha' hqstar hcardJpos
                                        w hi r0 ux : _) : (Fin k → ℝ)) := by
                                  exact FamiliesProof.globalCopy_eq_inheritedFace s t ht c hc
                                    qstar (Fintype.card J) hqstar hcardJpos ha' r0 x hx
                                -- At this point only a geometric refinement of finitely many
                                -- closed scalar chambers is required.  We formulate it without
                                -- any reference to maps, support or metrics.  This is strictly
                                -- the PL part of the argument: every facet of a geometric
                                -- complex is contained in one pulling face and in a single
                                -- cumulative-coordinate chamber of that face.
                                have chamber_refine :
                                    ∃ M : SimplicialComplex ℝ (Fin k → ℝ),
                                      M.faces.Finite ∧
                                      M.space = convexHull ℝ (s : Set (Fin k → ℝ)) ∧
                                      ∀ D ∈ M.facets,
                                        ∃ (t : Finset (Fin k → ℝ))
                                          (ht : FamiliesProof.lexFace s t)
                                          (hne : t.Nonempty)
                                          (b : Fin ((FamiliesProof.facePos s t).card+1) →
                                            Fin (qstar * Fintype.card J)),
                                          ∀ x : Fin k → ℝ,
                                            x ∈ convexHull ℝ (D : Set (Fin k → ℝ)) →
                                            ∃ hx : x ∈ convexHull ℝ
                                                (Set.range (FamiliesProof.inheritedFace s t)),
                                              (⟨x,hx⟩ : {z : Fin k → ℝ // z ∈ convexHull ℝ
                                                (Set.range (FamiliesProof.inheritedFace s t))}) ∈
                                                FamiliesProof.geoChamber
                                                  (FamiliesProof.inheritedFace s t)
                                                  (FamiliesProof.inheritedFace_indep ht)
                                                  (qstar * Fintype.card J)
                                                  (fun m => (b m).val) := by
                                  -- Every point is in one of these finitely many closed
                                  -- cells already.  The only strengthening still needed is
                                  -- to make that cover into a *geometric complex*.  Recording
                                  -- the pointwise cover avoids folding a selection assertion
                                  -- into that PL step.
                                  have hN : 0 < qstar * Fintype.card J :=
                                    Nat.mul_pos hqstar hcardJpos
                                  have point_cover (x : Fin k → ℝ)
                                      (hx : x ∈ convexHull ℝ (s : Set (Fin k → ℝ))) :
                                      ∃ (t : Finset (Fin k → ℝ))
                                        (ht : FamiliesProof.lexFace s t)
                                        (hne : t.Nonempty)
                                        (b : Fin ((FamiliesProof.facePos s t).card+1) →
                                          Fin (qstar * Fintype.card J))
                                        (hxt : x ∈ convexHull ℝ
                                          (Set.range (FamiliesProof.inheritedFace s t))),
                                        (⟨x,hxt⟩ : {z : Fin k → ℝ // z ∈ convexHull ℝ
                                          (Set.range (FamiliesProof.inheritedFace s t))}) ∈
                                          FamiliesProof.geoChamber
                                            (FamiliesProof.inheritedFace s t)
                                            (FamiliesProof.inheritedFace_indep ht)
                                            (qstar * Fintype.card J)
                                            (fun m => (b m).val) := by
                                    obtain ⟨t, ht, hne, hxt⟩ :=
                                      FamiliesProof.lexFaces_cover s x hx
                                    have hxt' : x ∈ convexHull ℝ
                                        (Set.range (FamiliesProof.inheritedFace s t)) := by
                                      simpa [FamiliesProof.range_inheritedFace ht.1] using hxt
                                    have hU := FamiliesProof.iUnion_geoChamber_fin hN
                                      (FamiliesProof.inheritedFace s t)
                                      (FamiliesProof.inheritedFace_indep ht)
                                    have hm : (⟨x,hxt'⟩ : {z : Fin k → ℝ // z ∈
                                        convexHull ℝ (Set.range
                                          (FamiliesProof.inheritedFace s t))}) ∈
                                        (Set.univ : Set {z : Fin k → ℝ // z ∈
                                          convexHull ℝ (Set.range
                                            (FamiliesProof.inheritedFace s t))}) :=
                                      Set.mem_univ _
                                    rw [← hU] at hm
                                    rcases Set.mem_iUnion.mp hm with ⟨b,hb⟩
                                    exact ⟨t, ht, hne, b, hxt', hb⟩
                                  by_cases honeN : qstar * Fintype.card J = 1
                                  · obtain ⟨M,hMf,hMs,hMc⟩ :=
                                      FamiliesProof.chamber_refine_one s
                                    refine ⟨M, hMf, hMs, ?_⟩
                                    intro D hD
                                    obtain ⟨t, ht, hne, b, hb⟩ := hMc D hD
                                    let b' : Fin ((FamiliesProof.facePos s t).card+1) →
                                        Fin (qstar * Fintype.card J) := fun m =>
                                          ⟨0, by omega⟩
                                    refine ⟨t, ht, hne, b', ?_⟩
                                    intro x hx
                                    obtain ⟨hx', hg⟩ := hb x hx
                                    refine ⟨hx', ?_⟩
                                    -- all elements of `Fin 1` have value zero
                                    have bz : (fun m : Fin ((FamiliesProof.facePos s t).card+1) =>
                                        (b m).val) = (fun _ => 0) := by
                                      funext m
                                      exact congrArg Fin.val (Fin.eq_zero (b m))
                                    simpa [b', bz, honeN] using hg
                                  · -- On every prefix-chain in one elementary simplex cube
                                    -- there is now a *Fin n*-valued chamber, even at the upper
                                    -- boundary.  The latter subtlety is important: the least
                                    -- prefix itself has value `n` at an upper face, so coercing it
                                    -- to `Fin n` would be wrong.  `GridMin` clips it and proves the
                                    -- convex-hull assertion (`gridChain_facets_are_chambers`).
                                    -- Thus here the analytic/chart part reduces exactly to the
                                    -- pure finite Freudenthal complex of such chains.
                                    apply FamiliesProof.gridChain_refinement_reduction
                                      s (qstar * Fintype.card J) hN
                                    -- Remaining PL datum: a finite geometric complex all of
                                    -- whose facets are chains of prefix grid vertices on a
                                    -- pulling face.  Notice that this goal no longer mentions
                                    -- chambers, homeomorphisms, cuts, or any copy maps.  Both the
                                    -- face gluing and the possible upper-boundary value `n` are
                                    -- now explicit combinatorics of `GridVert`.
                                    -- Canonical finite candidate: push every chain of
                                    -- comparable denominator vertices along every pulling face.
                                    -- Finiteness, lowering, independence, and the chamber field
                                    -- are all encoded by `mappedChains_reduction`.  The residual
                                    -- two assertions are the actual geometric Freudenthal lemma:
                                    -- intersections of nested-chain hulls and coverage by them.
                                    -- For every coefficient vector the threshold vertices already
                                    -- form a bona fide close chain.  This records the rounding
                                    -- part independently of the outstanding hull/intersection
                                    -- assertion and is reusable in coefficient-space proofs.
                                    have roundedChains : ∀ (d : ℕ) (u : Fin d → ℝ),
                                        u ∈ FamiliesProof.coeffSimplex d →
                                        ∃ A : Finset (FamiliesProof.GridVert d
                                          (qstar * Fintype.card J)),
                                          A.Nonempty ∧ A ∈ FamiliesProof.coeffChains d
                                            (qstar * Fintype.card J) := by
                                      intro d u hu
                                      exact ⟨FamiliesProof.thresholdSupport
                                        (qstar * Fintype.card J) u hu.1 hu.2,
                                          FamiliesProof.thresholdSupport_nonempty u hu.1 hu.2,
                                          FamiliesProof.thresholdSupport_chain u hu.1 hu.2⟩
                                    have remains :
                                        ( (∀ D ∈ FamiliesProof.mappedChains s
                                            (qstar * Fintype.card J) hN,
                                            ∀ B ∈ FamiliesProof.mappedChains s
                                              (qstar * Fintype.card J) hN,
                                              convexHull ℝ (D : Set (Fin k → ℝ)) ∩
                                                convexHull ℝ (B : Set (Fin k → ℝ)) ⊆
                                                convexHull ℝ ((D : Set (Fin k → ℝ)) ∩
                                                  (B : Set (Fin k → ℝ)))) ∧
                                          (∀ x ∈ convexHull ℝ (s : Set (Fin k → ℝ)),
                                            ∃ D ∈ FamiliesProof.mappedChains s
                                              (qstar * Fintype.card J) hN,
                                              D.Nonempty ∧
                                                x ∈ convexHull ℝ (D : Set (Fin k → ℝ)))) := by
                                      -- Coverage for a global pulling grid is completely
                                      -- reduced to its coefficient-space rounding. In
                                      -- particular this recovers every denominator vertex
                                      -- without any chart or face argument.
                                      have cover_of_round
                                          (round : ∀ (d : ℕ) (u : Fin d → ℝ),
                                            u ∈ FamiliesProof.coeffSimplex d →
                                            ∃ A : Finset (FamiliesProof.GridVert d
                                              (qstar * Fintype.card J)), A.Nonempty ∧
                                              A ∈ FamiliesProof.coeffChains d
                                                (qstar * Fintype.card J) ∧
                                              u ∈ convexHull ℝ
                                                (FamiliesProof.gu ''
                                                  (A : Set (FamiliesProof.GridVert d
                                                    (qstar * Fintype.card J))))) :
                                          ∀ x ∈ convexHull ℝ (s : Set (Fin k → ℝ)),
                                            ∃ D ∈ FamiliesProof.mappedChains s
                                              (qstar * Fintype.card J) hN,
                                              D.Nonempty ∧ x ∈ convexHull ℝ
                                                (D : Set (Fin k → ℝ)) := by
                                        exact FamiliesProof.mappedChains_cover_of_coeff
                                          (qstar * Fintype.card J) hN round s
                                      have round_grid
                                          (d : ℕ)
                                          (a : FamiliesProof.GridVert d
                                            (qstar * Fintype.card J)) :
                                          ∃ A : Finset (FamiliesProof.GridVert d
                                            (qstar * Fintype.card J)), A.Nonempty ∧
                                            A ∈ FamiliesProof.coeffChains d
                                              (qstar * Fintype.card J) ∧
                                            FamiliesProof.gu a ∈ convexHull ℝ
                                              (FamiliesProof.gu ''
                                                (A : Set (FamiliesProof.GridVert d
                                                  (qstar * Fintype.card J)))) := by
                                        exact FamiliesProof.round_on_grid a rfl
                                      have thresholdWeights :
                                          ∀ (d : ℕ) (u : Fin d → ℝ)
                                            (hu : u ∈ FamiliesProof.coeffSimplex d),
                                            let L := FamiliesProof.levelList
                                              (qstar * Fintype.card J) u hu.1
                                            L ≠ [] ∧
                                              (∀ i : Fin L.length,
                                                0 ≤ FamiliesProof.intWeight L i) ∧
                                              (∑ i : Fin L.length,
                                                FamiliesProof.intWeight L i) = 1 := by
                                        intro d u hu
                                        dsimp
                                        exact ⟨FamiliesProof.levelList_ne u hu.1,
                                          FamiliesProof.intWeight_nonneg u hu.1,
                                          FamiliesProof.sum_level_weights u hu.1⟩
                                      -- The threshold average is exactly the input
                                      -- coefficient vector, not just a neighboring lattice
                                      -- point.  Positivity of `qstar * card J` is important
                                      -- in this telescoping equality (`weighted_gu_eq`).
                                      have round_all : ∀ (d : ℕ) (u : Fin d → ℝ),
                                          u ∈ FamiliesProof.coeffSimplex d →
                                          ∃ A : Finset (FamiliesProof.GridVert d
                                            (qstar * Fintype.card J)), A.Nonempty ∧
                                            A ∈ FamiliesProof.coeffChains d
                                              (qstar * Fintype.card J) ∧
                                            u ∈ convexHull ℝ
                                              (FamiliesProof.gu ''
                                                (A : Set (FamiliesProof.GridVert d
                                                  (qstar * Fintype.card J)))) := by
                                        intro d u hu
                                        exact FamiliesProof.coeff_round
                                          (qstar * Fintype.card J) hN d u hu
                                      have cover : ∀ x ∈ convexHull ℝ
                                          (s : Set (Fin k → ℝ)),
                                          ∃ D ∈ FamiliesProof.mappedChains s
                                            (qstar * Fintype.card J) hN,
                                            D.Nonempty ∧ x ∈ convexHull ℝ
                                              (D : Set (Fin k → ℝ)) :=
                                        cover_of_round round_all
                                      refine ⟨?_, cover⟩
                                      -- The outstanding assertion is now only the
                                      -- intersection axiom for the pushed order chains;
                                      -- coverage (previously conflated with it) follows
                                      -- from the exact threshold convex combination above.
                                      -- Peel off empty supports and the same-face
                                      -- compatibility case.  `map_inter` is literal for
                                      -- the embedding, so a union coefficient chain gives
                                      -- the desired ambient equality immediately.
                                      have hard : ∀ D ∈ FamiliesProof.mappedChains s
                                          (qstar * Fintype.card J) hN, D.Nonempty →
                                          ∀ B ∈ FamiliesProof.mappedChains s
                                            (qstar * Fintype.card J) hN, B.Nonempty →
                                          convexHull ℝ (D : Set (Fin k → ℝ)) ∩
                                            convexHull ℝ (B : Set (Fin k → ℝ)) ⊆
                                            convexHull ℝ ((D : Set (Fin k → ℝ)) ∩
                                              (B : Set (Fin k → ℝ))) := by
                                        -- the independent case available directly is
                                        -- `mappedFace_inter_of_union`; the remaining
                                        -- nonempty supports may live on different
                                        -- pulling faces.
                                        intro D hD hdn B hB hbn
                                        classical
                                        by_cases ok : ∃ (t : Finset (Fin k → ℝ))
                                            (ht : FamiliesProof.lexFace s t)
                                            (A C : Finset (FamiliesProof.GridVert
                                              (FamiliesProof.facePos s t).card
                                                (qstar * Fintype.card J))),
                                              A ∪ C ∈ FamiliesProof.coeffChains
                                                (FamiliesProof.facePos s t).card
                                                  (qstar * Fintype.card J) ∧
                                              D = A.map (FamiliesProof.gridEvalEmb hN
                                                (FamiliesProof.inheritedFace s t)
                                                  (FamiliesProof.inheritedFace_indep ht)) ∧
                                              B = C.map (FamiliesProof.gridEvalEmb hN
                                                (FamiliesProof.inheritedFace s t)
                                                  (FamiliesProof.inheritedFace_indep ht))
                                        · obtain ⟨t,ht,A,C,hU,eD,eB⟩ := ok
                                          subst D
                                          subst B
                                          simpa [Finset.coe_inter] using
                                            (FamiliesProof.mappedFace_inter_of_union
                                              hN s t ht A C hU)
                                        · -- First pass to the common pulling face;
                                          -- the zero-coordinate transport and the
                                          -- coefficient-chain intersection on that
                                          -- ordered face handle the boundary case.
                                          exact
                                            (FamiliesProof.mappedChains_inter_all s
                                              (qstar * Fintype.card J) hN) D hD B hB

                                      intro D hD B hB
                                      classical
                                      by_cases hd : D.Nonempty
                                      · by_cases hb : B.Nonempty
                                        · exact hard D hD hd B hB hb
                                        · have bz : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
                                          subst B
                                          simp [convexHull_empty]
                                      · have dz : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hd
                                        subst D
                                        simp [convexHull_empty]


                                    exact FamiliesProof.mappedChains_reduction
                                      s (qstar * Fintype.card J) hN remains.1 remains.2
                                obtain ⟨M0,hMfinite,hMspace,hMfac⟩ := chamber_refine
                                -- The global coefficient section already glues all local
                                -- formulas.  In particular the copies can be bundled on the
                                -- original hull before any subdivision is chosen.
                                have hspos : 0 < s.card := by
                                  exact lt_of_lt_of_le (by decide : 0 < 3) manyVertices
                                let eJ : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
                                let phi0 : J → C({x : Fin k → ℝ // x ∈
                                    convexHull ℝ (s : Set (Fin k → ℝ))},
                                    {x : Fin k → ℝ // x ∈
                                      convexHull ℝ (s : Set (Fin k → ℝ))}) := fun j =>
                                      FamiliesProof.globalCopyMap s hspos cglobal
                                        cglobal_pos cglobal_sum qstar (Fintype.card J)
                                        hqstar hcardJpos (eJ j)
                                -- transport the bundled maps across the definitional
                                -- presentation of the polytope.
                                subst P
                                refine ⟨phi0,
                                  { complex := M0
                                    faces_finite := hMfinite
                                    space_eq := hMspace }, ?_, ?_, ?_⟩
                                · intro D hD
                                  rcases hMfac D hD with ⟨t,ht,htne,b,hDb⟩
                                  let A0 : Finset (Fin (Fintype.card J)) :=
                                    FamiliesProof.chamberColours hcardJpos b
                                  let A : Finset J := A0.map eJ.symm.toEmbedding
                                  have htpos : 0 < (FamiliesProof.facePos s t).card :=
                                    FamiliesProof.facePos_card_pos ht.1 htne
                                  refine ⟨A, ?_, ?_⟩
                                  · have hA0 := FamiliesProof.card_chamberColours_plus_one
                                        htpos hcardJpos b
                                    have hAkdim : (FamiliesProof.facePos s t).card ≤ k+1 := by
                                      -- no simplex in `Fin k → ℝ` has more than `k+1`
                                      have hi := FamiliesProof.inheritedFace_indep ht
                                      
                                      have hv := AffineIndependent.card_le_finrank_succ hi
                                      simp at hv
                                      have hle := Submodule.finrank_le
                                        (vectorSpan ℝ (Set.range (FamiliesProof.inheritedFace s t)))
                                      have heq : Module.finrank ℝ (Fin k → ℝ) = k := by
                                        simpa using (Module.finrank_fin_fun ℝ (n:=k))
                                      omega
                                    -- `map` along an embedding preserves cardinality.
                                    change (A0.map eJ.symm.toEmbedding).card ≤ k
                                    rw [Finset.card_map]
                                    dsimp [A0]
                                    omega
                                  · intro j hj p p'
                                    -- each cell lies in the chosen pulling face; hence the
                                    -- global formula is the inherited cyclic simplex formula.
                                    have hpx := hDb (p.1 : Fin k → ℝ) p.property
                                    have hpy := hDb (p'.1 : Fin k → ℝ) p'.property
                                    rcases hpx with ⟨hxt, hxc⟩
                                    rcases hpy with ⟨hyt, hyc⟩
                                    have hxt' : (p.1 : Fin k → ℝ) ∈
                                        convexHull ℝ (t : Set (Fin k → ℝ)) := by
                                      simpa [FamiliesProof.range_inheritedFace ht.1] using hxt
                                    have hyt' : (p'.1 : Fin k → ℝ) ∈
                                        convexHull ℝ (t : Set (Fin k → ℝ)) := by
                                      simpa [FamiliesProof.range_inheritedFace ht.1] using hyt
                                    have hnot : eJ j ∉
                                        FamiliesProof.chamberColours hcardJpos b := by
                                      intro hm
                                      apply hj
                                      apply Finset.mem_map.mpr
                                      exact ⟨eJ j, hm, by simp⟩
                                    apply Subtype.ext
                                    change FamiliesProof.globalCopy s cglobal qstar
                                        (Fintype.card J) hqstar hcardJpos (eJ j) p.1 =
                                      FamiliesProof.globalCopy s cglobal qstar
                                        (Fintype.card J) hqstar hcardJpos (eJ j) p'.1
                                    rw [inherited_global_formula ht cglobal
                                        (by
                                          intro x hx
                                          -- the global chart supplied by the pasting lemma
                                          simpa using
                                            (cglobal_face
                                              (⟨t, by
                                                -- faces of the pulling complex are exactly
                                                -- nonempty lex faces
                                                rw [FamiliesProof.lexComplex_faces]
                                                exact ⟨ht, htne⟩⟩) x hx))
                                        htpos (eJ j) p.1 hxt']
                                    rw [inherited_global_formula ht cglobal
                                        (by
                                          intro x hx
                                          simpa using
                                            (cglobal_face
                                              (⟨t, by
                                                rw [FamiliesProof.lexComplex_faces]
                                                exact ⟨ht, htne⟩⟩) x hx))
                                        htpos (eJ j) p'.1 hyt']
                                    exact congrArg Subtype.val
                                      (FamiliesProof.simplexCycMap_const_not_mem
                                        htpos hqstar hcardJpos
                                        (FamiliesProof.inheritedFace s t)
                                        (FamiliesProof.inheritedFace_indep ht)
                                        (eJ j) b hnot hxc hyc)
                                · intro Q hQ j p hp
                                  rcases hQ with ⟨⟨u,hu⟩, _hfront, hExt⟩
                                  have hcQ : Convex ℝ
                                      (((↑) : {x : Fin k → ℝ // x ∈
                                          convexHull ℝ (s : Set (Fin k → ℝ))} →
                                          Fin k → ℝ) '' Q) := by
                                    rw [hu]
                                    exact convex_convexHull ℝ _
                                  change (phi0 j p :
                                    {x : Fin k → ℝ // x ∈
                                      convexHull ℝ (s : Set (Fin k → ℝ))}) ∈ Q
                                  have hpim : (p : Fin k → ℝ) ∈
                                      (((↑) : {x : Fin k → ℝ // x ∈
                                          convexHull ℝ (s : Set (Fin k → ℝ))} →
                                          Fin k → ℝ) '' Q) := ⟨p, hp, rfl⟩
                                  have hz := FamiliesProof.globalCopy_mem_extreme s hspos
                                      cglobal cglobal_pos cglobal_sum cglobal_eval
                                      qstar (Fintype.card J) hqstar hcardJpos (eJ j)
                                      hcQ hExt p hpim
                                  rcases hz with ⟨z,hz,heq⟩
                                  have : z = phi0 j p := Subtype.ext heq
                                  simpa [this] using hz
                                · intro j p
                                  change dist
                                    (FamiliesProof.globalCopyMap s hspos cglobal
                                      cglobal_pos cglobal_sum qstar (Fintype.card J)
                                      hqstar hcardJpos (eJ j) p)
                                    (FamiliesProof.globalCopyMap s hspos cglobal
                                      cglobal_pos cglobal_sum qstar (Fintype.card J)
                                      hqstar hcardJpos (eJ j₀) p) ≤ δ
                                  -- the uniform estimate is independent of chambers.
                                  exact le_trans
                                    (FamiliesProof.globalCopy_dist s cglobal qstar
                                      (Fintype.card J) hqstar hcardJpos (eJ j)
                                      (eJ j₀) p)
                                    hqδ

                      have tiny_copies :
                          ∃ ε : NNReal,
                            L * L * ((Fintype.card J : NNReal) * K₀ * ε) < 1 ∧
                            ∃ φ : J → C(P,P), ∃ M : Subdivision P,
                              (∀ D ∈ M.complex.facets,
                                ∃ A : Finset J, A.card ≤ k ∧
                                  ∀ j : J, j ∉ A →
                                    ∀ p p' : closedCell P D,
                                      φ j p.1 = φ j p'.1) ∧
                              (∀ Q : Set P, IsBoundarySubpolyhedron Q →
                                ∀ j : J, ∀ p : P, p ∈ Q → φ j p ∈ Q) ∧
                              (∀ j : J, ∀ p : P,
                                dist (φ j p) (φ j₀ p) ≤ (ε : ℝ)) := by
                        let a : ℝ := ((L * L *
                          ((Fintype.card J : NNReal) * K₀) : NNReal) : ℝ)
                        have an : 0 ≤ a := by dsimp [a]; positivity
                        let er : ℝ := 1 / (a + 1)
                        have erpos : 0 < er := by dsimp [er]; positivity
                        let ε : NNReal := ⟨er, le_of_lt erpos⟩
                        rcases fine_copies er erpos with ⟨φ,M,hf,hb',hh⟩
                        refine ⟨ε, ?_, φ, M, hf, hb', ?_⟩
                        · have heq : ((L * L *
                              ((Fintype.card J : NNReal) * K₀ * ε)) : NNReal) =
                              (L * L * ((Fintype.card J : NNReal) * K₀)) * ε := by ring
                          rw [heq]
                          have realineq : a * (1 / (a+1)) < 1 := by
                            have hh : 0 < a+1 := by linarith
                            calc
                              a * (1 / (a+1)) = a / (a+1) := by ring
                              _ < 1 := (div_lt_one hh).mpr (by linarith)
                          exact_mod_cast realineq
                        · intro j p
                          exact hh j p
                      rcases tiny_copies with ⟨ε, hε, φ, M, hsparse, hface, hclose⟩
                      let c : NNReal := (Fintype.card J : NNReal) * K₀ * ε
                      let vv : P × X → (Fin k → ℝ) := fun z =>
                        ∑ j : J, (lam j z.2) •
                          ((φ j z.1 : P) : Fin k → ℝ)
                      have vmem : ∀ z : P × X, vv z ∈ P := by
                        intro z
                        dsimp [vv]
                        exact hconv.sum_mem (fun j _ => hlamNon j z.2)
                          (by simpa using hlamSum z.2)
                          (by intro j _; exact (φ j z.1).property)
                      have vcont : Continuous vv := by
                        dsimp [vv]
                        exact continuous_finset_sum (Finset.univ : Finset J)
                          (by
                            intro j _
                            exact ((lam j).continuous.comp continuous_snd).smul
                              (continuous_subtype_val.comp
                                ((φ j).continuous.comp continuous_fst)))
                      let g : C(P × X,P) :=
                        { toFun := fun z => ⟨vv z, vmem z⟩
                          continuous_toFun := vcont.subtype_mk _ }
                      refine ⟨c, ?_, g, M, ?_, ?_, ?_⟩
                      · simpa [c, mul_assoc] using hε
                      · intro D hD
                        rcases hsparse D hD with ⟨A,hA,hst⟩
                        let e : J ↪ ι :=
                          ⟨(fun j => j.val), (fun a b h => Subtype.ext h)⟩
                        let A' : Finset ι := A.map e
                        have hcard : A'.card = A.card := Finset.card_map _
                        refine ⟨A', ?_, ?_⟩
                        · simpa [hcard] using hA
                        · intro p p' x hx
                          have xx : ∀ j : J, j ∈ A → x ∉ V j := by
                            intro j hj bad
                            apply hx
                            have him : j.val ∈ A' :=
                              Finset.mem_map.mpr ⟨j, hj, rfl⟩
                            exact Set.mem_iUnion_of_mem j.val
                              (Set.mem_iUnion_of_mem him bad)
                          apply Subtype.ext
                          change vv (p.1,x) = vv (p'.1,x)
                          dsimp [vv]
                          apply Finset.sum_congr rfl
                          intro j hj
                          by_cases ja : j ∈ A
                          · rw [hlamOut j x (xx j ja)]
                            simp
                          · have z := hst j ja p p'
                            rw [z]
                      · intro Q hQ p hp x
                        let Bq : Set (Fin k → ℝ) :=
                          ((↑) : P → Fin k → ℝ) '' Q
                        have Bc : Convex ℝ Bq := by
                          rcases hQ.1 with ⟨s, hs⟩
                          change Convex ℝ (((↑) : P → (Fin k → ℝ)) '' Q)
                          rw [hs]
                          exact convex_convexHull ℝ _
                        have zz : vv (p,x) ∈ Bq := by
                          dsimp [vv]
                          refine Bc.sum_mem (fun j _ => hlamNon j x)
                            (by simpa using hlamSum x) ?_
                          intro j _
                          exact ⟨φ j p, hface Q hQ j p hp, rfl⟩
                        obtain ⟨q,hq,hqe⟩ := zz
                        have eq : g (p,x) = q := by
                          apply Subtype.ext
                          change vv (p,x) = (q : Fin k → ℝ)
                          exact hqe.symm
                        simpa [eq] using hq
                      · intro p
                        -- cancellation against one base colour exposes the
                        -- small displacement.  This estimate is valid in any
                        -- normed ambient model of the polyhedron.
                        apply LipschitzWith.of_dist_le_mul
                        intro x y
                        change dist (g (p,x)) (g (p,y)) ≤ (c : ℝ) * dist x y
                        rw [Subtype.dist_eq]
                        change dist (vv (p,x)) (vv (p,y)) ≤ (c : ℝ) * dist x y
                        rw [dist_eq_norm]
                        have cancel : ∀ z : X,
                            (∑ j : J, (lam j z - lam j y)) =
                              (0:ℝ) := by
                          intro z
                          simp [Finset.sum_sub_distrib, hlamSum]
                        let bvec : Fin k → ℝ := (φ j₀ p : P)
                        have eqsum :
                          vv (p,x) - vv (p,y) =
                            ∑ j : J, (lam j x - lam j y) •
                              (((φ j p : P) : Fin k → ℝ) - bvec) := by
                          dsimp [vv]
                          -- a linear combination whose coefficients sum to zero
                          classical
                          have hz :
                              (∑ j : J, (lam j x - lam j y)) • bvec =
                                (0 : Fin k → ℝ) := by simp [cancel]
                          calc
                            (∑ j : J, (lam j x) • ((φ j p : P) : Fin k → ℝ)) -
                                (∑ j : J, (lam j y) • ((φ j p : P) : Fin k → ℝ)) =
                              ∑ j : J,
                                ((lam j x) • ((φ j p : P) : Fin k → ℝ) -
                                 (lam j y) • ((φ j p : P) : Fin k → ℝ)) := by
                                   rw [Finset.sum_sub_distrib]
                            _ = ∑ j : J,
                                (lam j x - lam j y) • ((φ j p : P) : Fin k → ℝ) := by
                                  apply Finset.sum_congr rfl
                                  intro j _
                                  rw [sub_smul]
                            _ = (∑ j : J,
                                (lam j x - lam j y) • ((φ j p : P) : Fin k → ℝ)) -
                                  (∑ j : J, (lam j x - lam j y)) • bvec := by
                                  rw [hz, sub_zero]
                            _ = ∑ j : J, (lam j x - lam j y) •
                                      (((φ j p : P) : Fin k → ℝ) - bvec) := by
                                  rw [Finset.sum_smul]
                                  rw [← Finset.sum_sub_distrib]
                                  apply Finset.sum_congr rfl
                                  intro j _
                                  rw [smul_sub]
                        rw [eqsum]
                        calc
                          ‖∑ j : J, (lam j x - lam j y) •
                              (((φ j p : P) : Fin k → ℝ) - bvec)‖ ≤
                              ∑ j : J, ‖(lam j x - lam j y) •
                                (((φ j p : P) : Fin k → ℝ) - bvec)‖ :=
                            norm_sum_le _ _
                          _ ≤ ∑ j : J,
                                (((K₀ : ℝ) * dist x y) * (ε : ℝ)) := by
                            apply Finset.sum_le_sum
                            intro j hj
                            rw [norm_smul, Real.norm_eq_abs]
                            exact mul_le_mul
                              (by
                                have := (hlamLip j).dist_le_mul x y
                                simpa [Real.dist_eq] using this)
                              (by
                                have hh := hclose j p
                                simpa [bvec, dist_eq_norm,
                                  Subtype.dist_eq] using hh)
                              (norm_nonneg _) (by positivity)
                          _ = (c : ℝ) * dist x y := by
                            simp [c]
                            push_cast
                            ring
                rcases small_endpoint with ⟨c,hc,g,M,hM,hb,hgl⟩
                let uu : I × P × X → (Fin k → ℝ) := fun z =>
                  (1-(z.1:ℝ)) • (z.2.1 : Fin k → ℝ) +
                     (z.1:ℝ) • (g (z.2.1,z.2.2) : Fin k → ℝ)
                have uumem : ∀ z : I × P × X, uu z ∈ P := by
                  intro z
                  apply convex_iff_add_mem.mp hconv z.2.1.property
                    (g (z.2.1,z.2.2)).property
                    (sub_nonneg.mpr (unitInterval.le_one z.1))
                    (unitInterval.nonneg z.1)
                  ring
                have uucont : Continuous uu := by
                  have ht : Continuous (fun z : I × P × X => (z.1:ℝ)) :=
                     continuous_subtype_val.comp continuous_fst
                  have hp : Continuous (fun z : I × P × X => (z.2.1 : Fin k → ℝ)) :=
                     continuous_subtype_val.comp
                         (continuous_fst.comp continuous_snd)
                  have hg' : Continuous (fun z : I × P × X =>
                      (g (z.2.1,z.2.2) : Fin k → ℝ)) :=
                     continuous_subtype_val.comp (g.continuous.comp continuous_snd)
                  exact (continuous_const.sub ht).smul hp |>.add (ht.smul hg')
                let GG : C(I × P × X, P) :=
                   { toFun := fun z => ⟨uu z, uumem z⟩
                     continuous_toFun := uucont.subtype_mk _ }
                refine ⟨c,hc,GG,M,?_,?_,?_,?_⟩
                · intro p x
                  apply Subtype.ext
                  simp [GG, uu]
                · intro D hD
                  rcases hM D hD with ⟨A,hA,hAA⟩
                  refine ⟨A,hA,?_⟩
                  intro p p' x hx'
                  simpa [GG, uu] using hAA p p' x hx'
                · intro Q hQ t p hp x
                  have hv1 : (p : Fin k → ℝ) ∈
                       ((↑) : P → (Fin k → ℝ)) '' Q := ⟨p,hp,rfl⟩
                  have hv2 : (g (p,x) : Fin k → ℝ) ∈
                       ((↑) : P → (Fin k → ℝ)) '' Q :=
                         ⟨g (p,x),hb Q hQ p hp x,rfl⟩
                  have cc : Convex ℝ (((↑) : P → (Fin k → ℝ)) '' Q) := by
                    rcases hQ.1 with ⟨ss,hss⟩
                    rw [hss]
                    exact convex_convexHull ℝ _
                  obtain ⟨q,hq,e⟩ := (convex_iff_add_mem.mp cc hv1 hv2
                    (sub_nonneg.mpr (unitInterval.le_one t))
                    (unitInterval.nonneg t) (by ring))
                  have eq : GG (t,p,x) = q := by
                    apply Subtype.ext
                    change uu (t,p,x) = _
                    exact e.symm
                  rw [eq]
                  exact hq
                · intro t p
                  apply LipschitzWith.of_dist_le_mul
                  intro x y
                  have hgxy := (hgl p).dist_le_mul x y
                  change dist (uu (t,p,x)) (uu (t,p,y)) ≤
                    (c:ℝ) * dist x y
                  calc
                    _ = dist ((t:ℝ) • (g (p,x) : Fin k → ℝ))
                          ((t:ℝ) • (g (p,y) : Fin k → ℝ)) :=
                        dist_add_left _ _ _
                    _ = (t:ℝ) * dist (g (p,x)) (g (p,y)) := by
                       rw [dist_smul₀, Real.norm_of_nonneg
                          (unitInterval.nonneg t)]
                       rfl
                    _ ≤ (t:ℝ) * ((c:ℝ) * dist x y) :=
                       mul_le_mul_of_nonneg_left hgxy
                         (unitInterval.nonneg t)
                    _ ≤ 1 * ((c:ℝ) * dist x y) := by
                       apply mul_le_mul_of_nonneg_right
                         (unitInterval.le_one t)
                       exact mul_nonneg c.coe_nonneg dist_nonneg
                    _ = _ := by ring
              rcases small_motion with
                ⟨c, hc, G, M, hG0, hcell, hface, hG_lip⟩
              let GX : C(I × P × X, P × X) :=
                 { toFun := fun z => (G z,z.2.2)
                   continuous_toFun := G.continuous.prodMk
                       (continuous_snd.comp continuous_snd) }
              let FF : C(I × P × X, T) := f.comp GX
              letI : Nonempty X := hXn.to_nonempty
              have pointwise : ∀ tp : I × P,
                   ∃ e : X ≃ₜ T,
                     (∀ x : X, FF (tp.1,tp.2,x) = e x) ∧
                     LipschitzWith (L * max c 1) e ∧
                     LipschitzWith (L / (1-L*L*c)) e.symm := by
                   intro tp
                   apply FamiliesProof.perturb (s := slice)
                       (f := (f : P × X → T)) (L := L) (c := c)
                       _h_slice_eq _hf_joint _hf_slice_inv
                       (fun x : X => G (tp.1,tp.2,x))
                       (G.continuous.comp
                          (continuous_const.prodMk (continuous_const.prodMk
                            continuous_id))) (hG_lip tp.1 tp.2) hc
              choose Sl hSl hSlfor hSlinv using pointwise
              let Lb : NNReal := max (L * max c 1) (L / (1-L*L*c))
              refine ⟨FF, Lb, Sl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro p x
                change f (G (0,p,x), x) = f (p,x)
                rw [hG0 p x]
              · intro t p x
                exact hSl (t,p) x
              · refine ⟨M, ?_⟩
                intro D hD
                rcases hcell D hD with ⟨A,hA,hAA⟩
                refine ⟨A,hA,?_⟩
                intro p p' x hx'
                change f (G (1,p.1,x),x) = f (G (1,p'.1,x),x)
                rw [hAA p p' x hx']
              · intro S hS a b x hx'
                change f (G (a.1,a.2,x),x) = f (G (b.1,b.2,x),x)
                exact hS _ _ _ hx'
              · intro Q hQ S hS a b x hx'
                change f (G (a.1,a.2.1,x),x) = f (G (b.1,b.2.1,x),x)
                let qa : Q := ⟨G (a.1,a.2.1,x), hface Q hQ _ _ a.2.2 x⟩
                let qb : Q := ⟨G (b.1,b.2.1,x), hface Q hQ _ _ b.2.2 x⟩
                exact hS qa qb _ hx'
              · intro tp
                exact (hSlfor tp).weaken (le_max_left _ _)
              · intro tp
                exact (hSlinv tp).weaken (le_max_right _ _)
    · letI : Subsingleton P :=
        not_nontrivial_iff_subsingleton.mp hntr
      obtain ⟨K⟩ := exK
      let F : C(I × P × X, T) :=
        f.comp
          { toFun := fun z : I × P × X => (z.2.1, z.2.2)
            continuous_toFun :=
              (continuous_fst.comp continuous_snd).prodMk
                (continuous_snd.comp continuous_snd) }
      let Sl : I × P → (X ≃ₜ T) := fun z => slice z.2
      refine ⟨F, L, Sl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro p x
        rfl
      · intro t p x
        change f (p, x) = slice p x
        exact _h_slice_eq p x
      · refine ⟨K, ?_⟩
        intro D hD
        refine ⟨(∅ : Finset ι), ?_, ?_⟩
        · simp
        · intro p p' x hx
          change f (p.1, x) = f (p'.1, x)
          have he : (p.1 : P) = p'.1 := Subsingleton.elim _ _
          rw [he]
      · intro S hs
        intro a b x hx
        change f (a.2, x) = f (b.2, x)
        -- This also follows from subsingletonness; using the stated support
        -- hypothesis keeps the argument identical to the stationary case.
        exact hs _ _ x hx
      · intro Q hQ S' hs
        intro a b x hx
        change f (a.2.1, x) = f (b.2.1, x)
        exact hs (a.2) (b.2) x hx
      · intro tp
        exact hfwd tp.2
      · intro tp
        exact _hf_slice_inv tp.2
/-ResultProofEnd-/
/-ResultEnd-/
end FamiliesOfMapsB01

end Submission
