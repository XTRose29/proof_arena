import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical

namespace Submission

/-ResultProofDefinitionsBegin-/

-- elementary lemmas about the counter.  It is much more convenient to use its
-- definition on the (nonzero) filtered tail.
lemma sc_zero_cons (xs : List ℝ) : signChanges (0 :: xs) = signChanges xs := by
  simp [signChanges]

lemma sc_cons_nil (x : ℝ) (xs : List ℝ)
    (hx : x ≠ 0) (hxs : xs.filter (· ≠ 0) = []) :
    signChanges (x :: xs) = 0 := by
  unfold signChanges
  have hcons : (x :: xs).filter (· ≠ (0:ℝ)) = x :: xs.filter (· ≠ (0:ℝ)) := by
    simp [hx]
  rw [hcons, hxs]
  rfl

lemma sc_cons_of_filter (x : ℝ) (xs : List ℝ) (y : ℝ) (zs : List ℝ)
    (hx : x ≠ 0) (hxs : xs.filter (· ≠ 0) = y :: zs) :
    signChanges (x :: xs) = (if x*y < 0 then 1 else 0) + signChanges xs := by
  unfold signChanges
  have hcons : (x :: xs).filter (· ≠ (0:ℝ)) = x :: xs.filter (· ≠ (0:ℝ)) := by
    simp [hx]
  rw [hcons, hxs]
  by_cases h : x*y < 0 <;> simp [h, Nat.add_comm]

lemma sc_prefix_aux (u v : List ℝ)
    (hval : signChanges u = signChanges v)
    (hhd : (u.filter (· ≠ (0:ℝ))).head? = (v.filter (· ≠ (0:ℝ))).head?)
    (pre : List ℝ) :
    signChanges (pre ++ u) = signChanges (pre ++ v) ∧
      ((pre ++ u).filter (· ≠ (0:ℝ))).head? =
        ((pre ++ v).filter (· ≠ (0:ℝ))).head? := by
  induction pre with
  | nil => exact ⟨hval,hhd⟩
  | cons x pre ih =>
    simp only [List.cons_append]
    rcases ih with ⟨hv, hh⟩
    by_cases hx : x = (0:ℝ)
    · subst x
      constructor
      · simpa [sc_zero_cons] using hv
      · simpa using hh
    · -- both filtered tails have the same first item
      have hx' : x ≠ (0:ℝ) := hx
      generalize hU : (pre ++ u).filter (· ≠ (0:ℝ)) = fu at hv hh ⊢
      generalize hV : (pre ++ v).filter (· ≠ (0:ℝ)) = fv at hv hh ⊢
      cases fu with
      | nil =>
        cases fv with
        | nil =>
          have h1 := sc_cons_nil x (pre ++ u) hx' hU
          have h2 := sc_cons_nil x (pre ++ v) hx' hV
          constructor
          · simpa [h1,h2] using h1.trans h2.symm
          · simp [hx, hU, hV]
        | cons z zs =>
          -- impossible heads
          simp [hU, hV] at hh
      | cons z zs =>
        cases fv with
        | nil =>
          simp [hU, hV] at hh
        | cons w ws =>
          have hz : z = w := by simpa [hU, hV] using hh
          subst w
          have h1 := sc_cons_of_filter x (pre ++ u) z zs hx' hU
          have h2 := sc_cons_of_filter x (pre ++ v) z ws hx' hV
          constructor
          · rw [h1, h2, hv]
          · simp [hx, hU, hV]


lemma sc_middle (a b z : ℝ) (t : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a*b < 0) :
    signChanges (a :: z :: b :: t) = signChanges (a :: b :: t) := by
  by_cases hz0 : z = (0:ℝ)
  · subst z
    unfold signChanges
    have hf : (a :: (0:ℝ) :: b :: t).filter (· ≠ (0:ℝ)) =
        (a :: b :: t).filter (· ≠ (0:ℝ)) := by
      simp only [List.filter_cons]
      simp
    rw [hf]
  · have hbt : (b::t).filter (· ≠ (0:ℝ)) = b :: t.filter (· ≠ (0:ℝ)) := by
      simp [hb]
    have hzt : (z::b::t).filter (· ≠ (0:ℝ)) = z :: (b::t).filter (· ≠ (0:ℝ)) := by
      simp [hz0]
    rw [sc_cons_of_filter a (z::b::t) z _ ha hzt,
        sc_cons_of_filter z (b::t) b _ hz0 hbt,
        sc_cons_of_filter a (b::t) b _ ha hbt]
    rcases (mul_neg_iff.mp hab) with hp | hp
    · rcases hp with ⟨ha', hb'⟩
      rcases (lt_or_gt_of_ne hz0) with hz | hz
      · have h1 : a*z < 0 := mul_neg_of_pos_of_neg ha' hz
        have h2p : 0 < z*b := mul_pos_of_neg_of_neg hz hb'
        have h2 : ¬ z*b < 0 := not_lt_of_ge (le_of_lt h2p)
        simp [h1, h2, hab, Nat.add_assoc]
      · have h1p : 0 < a*z := mul_pos ha' hz
        have h1 : ¬ a*z < 0 := not_lt_of_ge (le_of_lt h1p)
        have h2 : z*b < 0 := mul_neg_of_pos_of_neg hz hb'
        simp [h1, h2, hab, Nat.add_assoc]
    · rcases hp with ⟨ha', hb'⟩
      rcases (lt_or_gt_of_ne hz0) with hz | hz
      · have h1p : 0 < a*z := mul_pos_of_neg_of_neg ha' hz
        have h1 : ¬ a*z < 0 := not_lt_of_ge (le_of_lt h1p)
        have h2 : z*b < 0 := mul_neg_of_neg_of_pos hz hb'
        simp [h1, h2, hab, Nat.add_assoc]
      · have h1 : a*z < 0 := mul_neg_of_neg_of_pos ha' hz
        have h2p : 0 < z*b := mul_pos hz hb'
        have h2 : ¬ z*b < 0 := not_lt_of_ge (le_of_lt h2p)
        simp [h1, h2, hab, Nat.add_assoc]

lemma sc_middle_pref (pre t : List ℝ) (a b z : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a*b < 0) :
    signChanges (pre ++ a :: z :: b :: t) =
      signChanges (pre ++ a :: b :: t) := by
  have hv := sc_middle a b z t ha hb hab
  have hh : ((a::z::b::t).filter (· ≠ (0:ℝ))).head? =
      ((a::b::t).filter (· ≠ (0:ℝ))).head? := by simp [ha]
  exact (sc_prefix_aux _ _ hv hh pre).1


lemma eq_on_interval_of_eventuallyEq
    (f : ℝ → ℕ) {u v : ℝ} (huv : u ≤ v)
    (h : ∀ x ∈ Set.Icc u v, ∀ᶠ y in nhds x, f y = f x) :
    f u = f v := by
  have hc : ContinuousOn f (Set.Icc u v) := by
    intro x hx
    have he : (fun _ : ℝ => f x) =ᶠ[nhds x] f :=
      by
      filter_upwards [h x hx] with y hy
      exact hy.symm
    exact (ContinuousAt.congr (x := x) continuousAt_const he).continuousWithinAt
  have hi : IsPreconnected (f '' Set.Icc u v) :=
    isPreconnected_Icc.image _ hc
  have hs := hi.subsingleton
  exact hs ⟨u, ⟨le_rfl, huv⟩, rfl⟩ ⟨v, ⟨huv, le_rfl⟩, rfl⟩


lemma squarefree_no_common (p : ℝ[X]) (hp : Squarefree p) (x : ℝ) :
    p.eval x = 0 → p.derivative.eval x ≠ 0 := by
  intro hx hd
  have hsep : p.Separable := PerfectField.separable_iff_squarefree.mpr hp
  have hc : IsCoprime p p.derivative := (Polynomial.separable_def p).mp hsep
  rcases hc with ⟨u,v,hu⟩
  have he := congrArg (Polynomial.eval x) hu
  simp [Polynomial.eval_add, Polynomial.eval_mul, hx, hd] at he


lemma eval_next_at_root (f g : ℝ[X]) (x : ℝ) (hg : g.eval x = 0) :
    f.eval x = - (-(f % g)).eval x := by
  have h := EuclideanDomain.mod_add_div f g
  have he := congrArg (Polynomial.eval x) h
  -- remainder plus a multiple of g evaluates to the remainder.
  -- this is valid as well when g=0.
  simp [Polynomial.eval_add, Polynomial.eval_mul, hg] at he ⊢
  linarith

lemma nocommon_step (f g : ℝ[X])
    (hfg : ∀ x : ℝ, ¬ (f.eval x = 0 ∧ g.eval x = 0)) :
    ∀ x : ℝ, ¬ (g.eval x = 0 ∧ (-(f % g)).eval x = 0) := by
  intro x hx
  have hfz : f.eval x = 0 := by
    have h := eval_next_at_root f g x hx.1
    rw [hx.2] at h
    simpa using h
  exact hfg x ⟨hfz, hx.1⟩


def NoAdj (f g : ℝ[X]) : Prop := ∀ x : ℝ, ¬ (f.eval x = 0 ∧ g.eval x = 0)

@[simp] lemma sturmAux_ne_nil (a b : ℝ[X]) (n : ℕ) :
    (sturmAux a b n).head? = some a := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    by_cases h : b = 0 <;> simp [sturmAux, h]

lemma chain_aux (a b : ℝ[X]) (n : ℕ) (hfg : NoAdj a b) :
    List.IsChain NoAdj (sturmAux a b n) := by
  induction n generalizing a b with
  | zero => simp [sturmAux, List.IsChain]
  | succ n ih =>
    by_cases hb : b = 0
    · simp [sturmAux, hb, List.IsChain]
    · have hnext : NoAdj b (-(a % b)) := nocommon_step a b hfg
      have ht := ih b (-(a % b)) hnext
      -- the tail always starts with b
      cases hlist : sturmAux b (-(a % b)) n with
      | nil =>
        have := sturmAux_ne_nil b (-(a%b)) n
        simp [hlist] at this
      | cons c l =>
        have hc : c = b := by
          have hm := sturmAux_ne_nil b (-(a%b)) n
          rw [hlist] at hm
          simpa using Option.some.inj hm
        subst c
        have ht' : List.IsChain NoAdj (b :: l) := by simpa [hlist] using ht
        simpa [sturmAux, hb, hlist, List.chain_cons] using
          (List.IsChain.cons_cons hfg ht')


def Trip : List ℝ[X] → Prop
 | f :: g :: h :: t =>
     (∀ x : ℝ, g.eval x = 0 → f.eval x = - h.eval x) ∧ Trip (g :: h :: t)
 | _ => True

lemma trip_aux (a b : ℝ[X]) (n : ℕ) : Trip (sturmAux a b n) := by
  induction n generalizing a b with
  | zero => simp [sturmAux, Trip]
  | succ n ih =>
    by_cases hb : b = 0
    · simp [sturmAux, hb, Trip]
    · cases n with
      | zero =>
        simp [sturmAux, hb, Trip]
      | succ k =>
        by_cases hr : -(a % b) = 0
        · simp [sturmAux, hb, hr, Trip]
        · have ht := ih b (-(a % b))
          -- the first triple is the defining remainder relation
          rw [sturmAux, if_neg hr] at ht
          rw [sturmAux, if_neg hb]
          rw [sturmAux, if_neg hr]
          generalize hL : sturmAux (-(a % b))
              (-(b % -(a % b))) k = L at ht ⊢
          cases L with
          | nil =>
             have hm := sturmAux_ne_nil (-(a%b)) (-(b % -(a%b))) k
             rw [hL] at hm
             simp at hm
          | cons d l =>
             have hd : d = -(a%b) := by
               have hm := sturmAux_ne_nil (-(a%b)) (-(b % -(a%b))) k
               rw [hL] at hm
               simpa using Option.some.inj hm
             subst d
             change (∀ x : ℝ, b.eval x = 0 →
                a.eval x = - (-(a % b)).eval x) ∧
                  Trip (b :: (-(a%b)) :: l)
             exact ⟨fun x hx => eval_next_at_root a b x hx, ht⟩


def LastNR : List ℝ[X] → Prop
 | [] => False
 | [f] => ∀ x : ℝ, f.eval x ≠ 0
 | f :: g :: l => LastNR (g::l)

lemma lastNR_cons {f : ℝ[X]} {l : List ℝ[X]} (hl : l ≠ []) :
    LastNR (f::l) = LastNR l := by
  cases l <;> simp_all [LastNR]

lemma aux_last (a b : ℝ[X]) (n : ℕ)
    (hno : NoAdj a b)
    (hdegree : b = 0 ∨ b.natDegree < a.natDegree)
    (hfuel : a.natDegree + 1 ≤ n) : LastNR (sturmAux a b n) := by
  induction n generalizing a b with
  | zero => simp at hfuel
  | succ n ih =>
    by_cases hb : b = 0
    · have hn : ∀ x : ℝ, a.eval x ≠ 0 := by
        intro x hx
        exact hno x ⟨hx, by simp [hb]⟩
      simpa [sturmAux, hb, LastNR] using hn
    · have hba : b.natDegree < a.natDegree := hdegree.resolve_left hb
      have hfa : a.natDegree ≤ n := by omega
      have hfb : b.natDegree + 1 ≤ n := by omega
      let r : ℝ[X] := -(a % b)
      have hno' : NoAdj b r := nocommon_step a b hno
      have hdeg' : r = 0 ∨ r.natDegree < b.natDegree := by
        by_cases hbn : b.natDegree = 0
        · left
          have hunit : IsUnit b :=
            (Polynomial.isUnit_iff_degree_eq_zero).2 (by
              rw [Polynomial.degree_eq_natDegree hb, hbn]
              rfl)
          dsimp [r]
          have hm : a % b = 0 := (EuclideanDomain.mod_eq_zero).2 hunit.dvd
          simp [hm]
        · right
          dsimp [r]
          rw [Polynomial.natDegree_neg]
          exact Polynomial.natDegree_mod_lt _ hbn
      have ht := ih b r hno' hdeg' hfb
      have hne : sturmAux b r n ≠ [] := by
        intro h
        have hm := sturmAux_ne_nil b r n
        rw [h] at hm
        simp at hm
      rw [sturmAux, if_neg hb]
      rw [lastNR_cons hne]
      exact ht


/-- Two real numbers have the same nonzero (strict) sign.  This is the
convenient version of "same sign" for neighbourhood arguments: being in the
same one of the two open half-lines is an open condition. -/
def SameStrictSign (u v : ℝ) : Prop :=
  (u < 0 ∧ v < 0) ∨ (0 < u ∧ 0 < v)

lemma sss_ne_left {u v : ℝ} (h : SameStrictSign u v) : u ≠ 0 := by
  rcases h with h | h
  · exact ne_of_lt h.1
  · exact ne_of_gt h.1

lemma sss_ne_right {u v : ℝ} (h : SameStrictSign u v) : v ≠ 0 := by
  rcases h with h | h
  · exact ne_of_lt h.2
  · exact ne_of_gt h.2

/-- Changing each of two factors to a number having the same nonzero sign
preserves the predicate that their product is negative. -/
lemma sss_mul_neg_iff {u u' v v' : ℝ}
    (hu : SameStrictSign u u') (hv : SameStrictSign v v') :
    (u * v < 0 ↔ u' * v' < 0) := by
  rcases hu with ⟨hu, hu'⟩ | ⟨hu, hu'⟩ <;>
    rcases hv with ⟨hv, hv'⟩ | ⟨hv, hv'⟩
  · have h₁p : 0 < u * v := mul_pos_of_neg_of_neg hu hv
    have h₂p : 0 < u' * v' := mul_pos_of_neg_of_neg hu' hv'
    have h₁ : ¬ u * v < 0 := not_lt_of_ge (le_of_lt h₁p)
    have h₂ : ¬ u' * v' < 0 := not_lt_of_ge (le_of_lt h₂p)
    simp [h₁, h₂]
  · have h₁ : u * v < 0 := mul_neg_of_neg_of_pos hu hv
    have h₂ : u' * v' < 0 := mul_neg_of_neg_of_pos hu' hv'
    simp [h₁, h₂]
  · have h₁ : u * v < 0 := mul_neg_of_pos_of_neg hu hv
    have h₂ : u' * v' < 0 := mul_neg_of_pos_of_neg hu' hv'
    simp [h₁, h₂]
  · have h₁p : 0 < u * v := mul_pos hu hv
    have h₂p : 0 < u' * v' := mul_pos hu' hv'
    have h₁ : ¬ u * v < 0 := not_lt_of_ge (le_of_lt h₁p)
    have h₂ : ¬ u' * v' < 0 := not_lt_of_ge (le_of_lt h₂p)
    simp [h₁, h₂]

/-- If all the entries of a fixed list of polynomials stay in the same
(nonzero) half-line at two points, its sign-change count at those points is
identical.  Zeros never have to be thrown away in this lemma; that is the main
reason for using strict signs. -/
lemma signChanges_map_eq_of_sameStrictSign (L : List ℝ[X]) (x y : ℝ)
    (h : ∀ q ∈ L, SameStrictSign (q.eval x) (q.eval y)) :
    signChanges (L.map (fun q : ℝ[X] => q.eval x)) =
      signChanges (L.map (fun q : ℝ[X] => q.eval y)) := by
  induction L with
  | nil => rfl
  | cons q t ih =>
    have hq : SameStrictSign (q.eval x) (q.eval y) := h q (by simp)
    have ht : ∀ r ∈ t, SameStrictSign (r.eval x) (r.eval y) := by
      intro r hr
      exact h r (by simp [hr])
    have ih' := ih ht
    -- The filtered tails are just the tails themselves: no entry is zero.
    have htx : ((t.map (fun r : ℝ[X] => r.eval x)).filter
          (· ≠ (0:ℝ))) = t.map (fun r : ℝ[X] => r.eval x) := by
      apply List.filter_eq_self.mpr
      intro z hz
      obtain ⟨r, hr, rfl⟩ := (List.mem_map.mp hz)
      have hn : r.eval x ≠ 0 := sss_ne_left (ht r hr)
      simp [hn]
    have hty : ((t.map (fun r : ℝ[X] => r.eval y)).filter
          (· ≠ (0:ℝ))) = t.map (fun r : ℝ[X] => r.eval y) := by
      apply List.filter_eq_self.mpr
      intro z hz
      obtain ⟨r, hr, rfl⟩ := (List.mem_map.mp hz)
      have hn : r.eval y ≠ 0 := sss_ne_right (ht r hr)
      simp [hn]
    cases t with
    | nil =>
      -- A singleton has no adjacent pair.
      unfold signChanges
      have hx0 : q.eval x ≠ 0 := sss_ne_left hq
      have hy0 : q.eval y ≠ 0 := sss_ne_right hq
      simp [hx0, hy0]
    | cons r t =>
      -- On a nonempty tail use the head-of-filter recurrence.  The induction
      -- hypothesis supplies the count of the tail; the product test on the
      -- newly exposed adjacent pair is unchanged by `sss_mul_neg_iff`.
      have hr : SameStrictSign (r.eval x) (r.eval y) := ht r (by simp)
      have hx0 : q.eval x ≠ 0 := sss_ne_left hq
      have hy0 : q.eval y ≠ 0 := sss_ne_right hq
      have hfx : (((r :: t).map (fun s : ℝ[X] => s.eval x)).filter
            (· ≠ (0:ℝ))) = r.eval x :: t.map (fun s : ℝ[X] => s.eval x) := by
        simpa using htx
      have hfy : (((r :: t).map (fun s : ℝ[X] => s.eval y)).filter
            (· ≠ (0:ℝ))) = r.eval y :: t.map (fun s : ℝ[X] => s.eval y) := by
        simpa using hty
      have hxrec :=
        sc_cons_of_filter (q.eval x)
          ((r :: t).map (fun s : ℝ[X] => s.eval x))
          (r.eval x) (t.map (fun s : ℝ[X] => s.eval x)) hx0 hfx
      have hyrec :=
        sc_cons_of_filter (q.eval y)
          ((r :: t).map (fun s : ℝ[X] => s.eval y))
          (r.eval y) (t.map (fun s : ℝ[X] => s.eval y)) hy0 hfy
      -- make the conses in the maps explicit for the recurrence.
      simp only [List.map_cons] at hxrec hyrec ih' ⊢
      rw [hxrec, hyrec, ih']
      have hm := sss_mul_neg_iff hq hr
      by_cases hh : q.eval x * r.eval x < 0
      · have hh' : q.eval y * r.eval y < 0 := hm.mp hh
        simp [hh, hh']
      · have hh' : ¬ q.eval y * r.eval y < 0 := fun hh' => hh (hm.mpr hh')
        simp [hh, hh']

/-- A nonzero value of each member of a *finite* list of real polynomials
remains in its same strict half-line on one common neighbourhood of the
point.  This is just continuity of polynomial evaluation, with the
neighbourhoods intersected along the list. -/
lemma eventually_all_sameStrictSign (L : List ℝ[X]) (x : ℝ)
    (hx : ∀ q ∈ L, q.eval x ≠ 0) :
    ∀ᶠ y in nhds x, ∀ q ∈ L, SameStrictSign (q.eval x) (q.eval y) := by
  induction L with
  | nil =>
      simp
  | cons q t ih =>
      have hq0 : q.eval x ≠ 0 := hx q (by simp)
      have ht0 : ∀ r ∈ t, r.eval x ≠ 0 := by
        intro r hr
        exact hx r (by simp [hr])
      have iht : ∀ᶠ y in nhds x,
          ∀ r ∈ t, SameStrictSign (r.eval x) (r.eval y) := ih ht0
      have hc : ContinuousAt (fun z : ℝ => q.eval z) x :=
        Polynomial.continuousAt q
      have ihq : ∀ᶠ y in nhds x, SameStrictSign (q.eval x) (q.eval y) := by
        rcases (lt_or_gt_of_ne hq0) with hneg | hpos
        · have ev : ∀ᶠ y in nhds x, q.eval y < (0:ℝ) :=
            hc.eventually_lt continuousAt_const hneg
          filter_upwards [ev] with y hy
          exact Or.inl ⟨hneg, hy⟩
        · have ev : ∀ᶠ y in nhds x, (0:ℝ) < q.eval y :=
            continuousAt_const.eventually_lt hc hpos
          filter_upwards [ev] with y hy
          exact Or.inr ⟨hpos, hy⟩
      filter_upwards [ihq, iht] with y hqy hty
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with hr | hr
      · simpa [hr] using hqy
      · exact hty r hr

/-- Consequently the Sturm variation is locally constant at any point at
which no member of the fixed Sturm list is zero.  Finiteness of the list is
essential here (it is why one can use `filter_upwards` in the preceding
lemma). -/
lemma sigma_eventually_eq_of_forall_ne (p : ℝ[X]) (x : ℝ)
    (hx : ∀ q ∈ sturmChain p, q.eval x ≠ 0) :
    ∀ᶠ y in nhds x, sigma p y = sigma p x := by
  have he := eventually_all_sameStrictSign (sturmChain p) x hx
  filter_upwards [he] with y hy
  unfold sigma
  exact (signChanges_map_eq_of_sameStrictSign (sturmChain p) x y hy).symm



-- Dropping the first entry of a list cannot destroy its triple conditions.
lemma trip_tail_of_cons {q : ℝ[X]} {t : List ℝ[X]}
    (h : Trip (q :: t)) : Trip t := by
  cases t with
  | nil => simp [Trip]
  | cons b u =>
    cases u with
    | nil => simp [Trip]
    | cons c v =>
      exact h.2

/-- Combinatorial local part of Sturm's rule away from a root of the first
member.  At `x` the first and the last entries are non-zero, and every zero
of an interior entry has opposite neighbours (`Trip`).  If all entries which
*are* non-zero at `x` keep their strict signs at `y`, the count at `y` is the
same.  Entries zero at `x` may do anything.  In the proof they are deleted
one at a time with `sc_middle`.

`LastNR` is a convenient way of saying that we never run off the right end
when deleting such an entry; it is inherited by nonempty tails. -/
lemma signChanges_eval_eq_of_good (L : List ℝ[X]) (x y : ℝ)
    (htrip : Trip L) (hlast : LastNR L)
    (hfirst : ∀ q : ℝ[X], L.head? = some q → q.eval x ≠ 0)
    (hsgn : ∀ q ∈ L, q.eval x ≠ 0 →
      SameStrictSign (q.eval x) (q.eval y)) :
    signChanges (L.map (fun q : ℝ[X] => q.eval x)) =
      signChanges (L.map (fun q : ℝ[X] => q.eval y)) := by
  -- Strong induction on the length is useful since deletion of a zero in
  -- position two recurses on the list starting in position three.
  classical
  induction hlen : L.length using Nat.strong_induction_on generalizing L with
  | h n IH =>
    cases L with
    | nil =>
      -- `LastNR []` is false.
      simp [LastNR] at hlast
    | cons q t =>
      have hq0 : q.eval x ≠ 0 := hfirst q (by simp)
      have hqsgn : SameStrictSign (q.eval x) (q.eval y) :=
        hsgn q (by simp) hq0
      have hqy0 : q.eval y ≠ 0 := sss_ne_right hqsgn
      cases t with
      | nil =>
        unfold signChanges
        simp [hq0, hqy0]
      | cons r u =>
        -- Facts inherited by tails.
        have hlast_tail : LastNR (r :: u) := by
          simpa [LastNR] using hlast
        have htrip_tail : Trip (r :: u) :=
          trip_tail_of_cons htrip
        have hsgn_tail : ∀ z ∈ (r :: u), z.eval x ≠ 0 →
              SameStrictSign (z.eval x) (z.eval y) := by
          intro z hz hn
          exact hsgn z (by simp [hz]) hn
        by_cases hr0 : r.eval x = 0
        · -- There must be an entry after `r`, since the last one never
          -- vanishes.
          cases u with
          | nil =>
            have hh : r.eval x ≠ 0 := by
              simpa [LastNR] using (show ∀ z : ℝ, r.eval z ≠ 0 from hlast_tail) x
            exact (hh hr0).elim
          | cons s v =>
            have htri : (∀ z : ℝ, r.eval z = 0 →
                  q.eval z = - s.eval z) := htrip.1
            have hnegreln : q.eval x = - s.eval x := htri x hr0
            have hs0 : s.eval x ≠ 0 := by
              intro hh
              apply hq0
              rw [hnegreln, hh]
              simp
            have hssgn : SameStrictSign (s.eval x) (s.eval y) :=
              hsgn s (by simp) hs0
            have hsy0 : s.eval y ≠ 0 := sss_ne_right hssgn
            have hminusx : q.eval x * s.eval x < 0 := by
              -- the two neighbouring values are nonzero opposites
              rw [hnegreln]
              rcases (lt_or_gt_of_ne hs0) with hsneg | hspos
              · have hp : 0 < (- s.eval x) := neg_pos.mpr hsneg
                exact mul_neg_of_pos_of_neg hp hsneg
              · have hn : (- s.eval x) < 0 := neg_neg_of_pos hspos
                exact mul_neg_of_neg_of_pos hn hspos
            have hminusy : q.eval y * s.eval y < 0 :=
              (sss_mul_neg_iff hqsgn hssgn).mp hminusx
            -- Delete the middle zero (and at `y` its unconstrained value).
            have hxdel :
                signChanges (q.eval x :: r.eval x :: s.eval x ::
                    (v.map (fun z : ℝ[X] => z.eval x))) =
                  signChanges (q.eval x :: s.eval x ::
                    (v.map (fun z : ℝ[X] => z.eval x))) :=
              sc_middle _ _ _ _ hq0 hs0 hminusx
            have hydel :
                signChanges (q.eval y :: r.eval y :: s.eval y ::
                    (v.map (fun z : ℝ[X] => z.eval y))) =
                  signChanges (q.eval y :: s.eval y ::
                    (v.map (fun z : ℝ[X] => z.eval y))) :=
              sc_middle _ _ _ _ hqy0 hsy0 hminusy
            -- Recurse on the tail that begins with `s`.
            have hlt : (s :: v).length < n := by
              -- `n` is the length of `q :: r :: s :: v`.
              cases hlen
              simp
            have htrip_ss : Trip (s :: v) :=
              trip_tail_of_cons htrip_tail
            have hlast_ss : LastNR (s :: v) := by
              simpa [LastNR] using hlast_tail
            have hsgn_ss : ∀ z ∈ (s :: v), z.eval x ≠ 0 →
                  SameStrictSign (z.eval x) (z.eval y) := by
              intro z hz hn
              exact hsgn z (by simp [hz]) hn
            have htail_eq :=
              IH ((s :: v).length) hlt (s :: v) htrip_ss hlast_ss
                (by
                  intro z hz
                  have : z = s := by simpa using Option.some.inj hz.symm
                  simpa [this] using hs0)
                hsgn_ss rfl
            -- Attach `q` in front of that tail.  Its adjacent test with
            -- `s` is negative on both sides.
            have hfx : (((s :: v).map (fun z : ℝ[X] => z.eval x)).filter
                  (· ≠ (0:ℝ))) =
                    s.eval x :: (v.map (fun z : ℝ[X] => z.eval x)).filter
                        (· ≠ (0:ℝ)) := by
              simp [hs0]
            have hfy : (((s :: v).map (fun z : ℝ[X] => z.eval y)).filter
                  (· ≠ (0:ℝ))) =
                    s.eval y :: (v.map (fun z : ℝ[X] => z.eval y)).filter
                        (· ≠ (0:ℝ)) := by
              simp [hsy0]
            have hxrec := sc_cons_of_filter (q.eval x)
                ((s :: v).map (fun z : ℝ[X] => z.eval x)) (s.eval x)
                ((v.map (fun z : ℝ[X] => z.eval x)).filter (· ≠ (0:ℝ)))
                hq0 hfx
            have hyrec := sc_cons_of_filter (q.eval y)
                ((s :: v).map (fun z : ℝ[X] => z.eval y)) (s.eval y)
                ((v.map (fun z : ℝ[X] => z.eval y)).filter (· ≠ (0:ℝ)))
                hqy0 hfy
            -- Expose the maps of the original and the shortened lists.
            simp only [List.map_cons] at hxrec hyrec htail_eq ⊢
            rw [hxdel, hydel, hxrec, hyrec, htail_eq]
            simp [hminusx, hminusy]
        · have hr0' : r.eval x ≠ 0 := hr0
          have hrsgn : SameStrictSign (r.eval x) (r.eval y) :=
            hsgn_tail r (by simp) hr0'
          have hry0 : r.eval y ≠ 0 := sss_ne_right hrsgn
          -- ordinary head step, with a recursive call on the full tail
          have hlt : (r :: u).length < n := by
            cases hlen
            simp
          have htail_eq :=
            IH ((r :: u).length) hlt (r :: u) htrip_tail hlast_tail
              (by
                intro z hz
                have : z = r := by simpa using Option.some.inj hz.symm
                simpa [this] using hr0')
              hsgn_tail rfl
          have hfx : (((r :: u).map (fun z : ℝ[X] => z.eval x)).filter
                (· ≠ (0:ℝ))) =
                  r.eval x :: (u.map (fun z : ℝ[X] => z.eval x)).filter
                        (· ≠ (0:ℝ)) := by
            simp [hr0']
          have hfy : (((r :: u).map (fun z : ℝ[X] => z.eval y)).filter
                (· ≠ (0:ℝ))) =
                  r.eval y :: (u.map (fun z : ℝ[X] => z.eval y)).filter
                        (· ≠ (0:ℝ)) := by
            simp [hry0]
          have hxrec := sc_cons_of_filter (q.eval x)
              ((r :: u).map (fun z : ℝ[X] => z.eval x)) (r.eval x)
              ((u.map (fun z : ℝ[X] => z.eval x)).filter (· ≠ (0:ℝ)))
              hq0 hfx
          have hyrec := sc_cons_of_filter (q.eval y)
              ((r :: u).map (fun z : ℝ[X] => z.eval y)) (r.eval y)
              ((u.map (fun z : ℝ[X] => z.eval y)).filter (· ≠ (0:ℝ)))
              hqy0 hfy
          have hm := sss_mul_neg_iff hqsgn hrsgn
          simp only [List.map_cons] at hxrec hyrec htail_eq ⊢
          rw [hxrec, hyrec, htail_eq]
          by_cases hh : q.eval x * r.eval x < 0
          · have hh' : q.eval y * r.eval y < 0 := hm.mp hh
            simp [hh, hh']
          · have hh' : ¬ q.eval y * r.eval y < 0 :=
              fun hh' => hh (hm.mpr hh')
            simp [hh, hh']



lemma eventually_nonzero_sameStrictSign (L : List ℝ[X]) (x : ℝ) :
    ∀ᶠ y in nhds x, ∀ q ∈ L, q.eval x ≠ 0 →
      SameStrictSign (q.eval x) (q.eval y) := by
  induction L with
  | nil => simp
  | cons q t ih =>
    by_cases hq0 : q.eval x = 0
    · filter_upwards [ih] with y hy
      intro r hr hr0
      have hr' : r = q ∨ r ∈ t := (List.mem_cons.mp hr)
      rcases hr' with rfl | hr'
      · exact (hr0 hq0).elim
      · exact hy r hr' hr0
    · have hc : ContinuousAt (fun z : ℝ => q.eval z) x :=
          Polynomial.continuousAt q
      have he : ∀ᶠ y in nhds x,
          SameStrictSign (q.eval x) (q.eval y) := by
        rcases (lt_or_gt_of_ne hq0) with hneg | hpos
        · have he' : ∀ᶠ y in nhds x, q.eval y < (0:ℝ) :=
            hc.eventually_lt continuousAt_const hneg
          filter_upwards [he'] with y hy
          exact Or.inl ⟨hneg, hy⟩
        · have he' : ∀ᶠ y in nhds x, (0:ℝ) < q.eval y :=
            continuousAt_const.eventually_lt hc hpos
          filter_upwards [he'] with y hy
          exact Or.inr ⟨hpos, hy⟩
      filter_upwards [he, ih] with y hY hy
      intro r hr hr0
      have hr' : r = q ∨ r ∈ t := (List.mem_cons.mp hr)
      rcases hr' with rfl | hr'
      · exact hY
      · exact hy r hr' hr0

/-- Full local constancy at a point which is not a root of the first
polynomial of a genuine Sturm list.  Interior zeros of the list cause no
problem, since their neighbours are opposite. -/
lemma sigma_eventually_eq_of_not_root (p : ℝ[X]) (hp : Squarefree p)
    (hn : p.natDegree ≠ 0) (x : ℝ) (hx : p.eval x ≠ 0) :
    ∀ᶠ y in nhds x, sigma p y = sigma p x := by
  have hno : NoAdj p (p.derivative) := by
    intro z hh
    exact (squarefree_no_common p hp z hh.1) hh.2
  let L : List ℝ[X] := sturmChain p
  have htrip : Trip L := by
    dsimp [L, sturmChain]
    exact trip_aux p (derivative p) (p.natDegree + 2)
  have hlast : LastNR L := by
    dsimp [L, sturmChain]
    have hd : (derivative p).natDegree < p.natDegree :=
      Polynomial.natDegree_derivative_lt hn
    have hf : p.natDegree + 1 ≤ p.natDegree + 2 := by omega
    exact aux_last p (derivative p) (p.natDegree + 2) hno (Or.inr hd) hf
  have hfirst : ∀ q : ℝ[X], L.head? = some q → q.eval x ≠ 0 := by
    intro q hq
    have hm : L.head? = some p := by
      dsimp [L, sturmChain]
      exact sturmAux_ne_nil p (derivative p) (p.natDegree + 2)
    have he : q = p := Option.some.inj (hq.symm.trans hm)
    simpa [he] using hx
  have he := eventually_nonzero_sameStrictSign L x
  filter_upwards [he] with y hy
  unfold sigma
  change signChanges (L.map (fun q : ℝ[X] => q.eval y)) =
    signChanges (L.map (fun q : ℝ[X] => q.eval x))
  exact (signChanges_eval_eq_of_good L x y htrip hlast hfirst hy).symm



lemma sigma_jump_at_root (p : ℝ[X]) (hp : Squarefree p)
    (hn : p.natDegree ≠ 0) (x : ℝ) (hx : p.eval x = 0) :
    ∀ᶠ y in nhds x,
      (y < x → sigma p y = sigma p x + 1) ∧
      (x < y → sigma p y = sigma p x) := by
  have hd0 : (derivative p).eval x ≠ 0 := squarefree_no_common p hp x hx
  have hdpol : derivative p ≠ 0 := by
    intro h; rw [h] at hd0; simp at hd0
  -- The list really has a second entry here.
  let T : List ℝ[X] :=
      sturmAux (derivative p) (-(p % derivative p)) (p.natDegree + 1)
  have hTne : T ≠ [] := by
    intro h
    have ht := sturmAux_ne_nil (derivative p) (-(p % derivative p))
      (p.natDegree + 1)
    change (T.head?) = some (derivative p) at ht
    rw [h] at ht
    simpa using ht
  obtain ⟨U, hTU⟩ : ∃ U : List ℝ[X], T = derivative p :: U := by
    cases hc : T with
    | nil => exact (hTne hc).elim
    | cons r u =>
      have hm := sturmAux_ne_nil (derivative p) (-(p % derivative p))
        (p.natDegree + 1)
      change T.head? = some (derivative p) at hm
      rw [hc] at hm
      have he : r = derivative p := by simpa using Option.some.inj hm
      exact ⟨u, by simpa [he] using hc⟩
  have hL : sturmChain p = p :: T := by
    unfold sturmChain
    have he : p.natDegree + 2 = (p.natDegree + 1) + 1 := by omega
    rw [he, sturmAux, if_neg hdpol]
  have htripL : Trip (sturmChain p) := by
    unfold sturmChain
    exact trip_aux p (derivative p) (p.natDegree + 2)
  have htripT : Trip T := by
    rw [hL] at htripL
    exact trip_tail_of_cons htripL
  have hno : NoAdj p (derivative p) := by
    intro z hz
    exact (squarefree_no_common p hp z hz.1) hz.2
  have hlastL : LastNR (sturmChain p) := by
    unfold sturmChain
    exact aux_last p (derivative p) (p.natDegree + 2) hno
      (Or.inr (Polynomial.natDegree_derivative_lt hn)) (by omega)
  have hlastT : LastNR T := by
    rw [hL, lastNR_cons hTne] at hlastL
    exact hlastL
  have hfirstT : ∀ z : ℝ[X], T.head? = some z → z.eval x ≠ 0 := by
    intro z hz
    rw [hTU] at hz
    have he : z = derivative p := by simpa using Option.some.inj hz.symm
    simpa [he] using hd0
  have htail_ev : ∀ᶠ y in nhds x,
      signChanges (T.map (fun f : ℝ[X] => f.eval y)) =
        signChanges (T.map (fun f : ℝ[X] => f.eval x)) := by
    filter_upwards [eventually_nonzero_sameStrictSign T x] with y hy
    exact (signChanges_eval_eq_of_good T x y htripT hlastT hfirstT hy).symm
  -- A factorisation at the simple root computes the sign of the first pair.
  have hdiv : X - C x ∣ p :=
    (Polynomial.dvd_iff_isRoot).2 ((Polynomial.IsRoot.def).2 hx)
  rcases (dvd_iff_exists_eq_mul_right.mp hdiv) with ⟨q, hq⟩
  have hdq : (derivative p).eval x = q.eval x := by
    rw [hq, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub]
  have hq0 : q.eval x ≠ 0 := by
    rw [hdq] at hd0
    exact hd0
  have hqsignev : ∀ᶠ y in nhds x,
      SameStrictSign (q.eval x) (q.eval y) ∧
        SameStrictSign ((derivative p).eval x) ((derivative p).eval y) := by
    have he := eventually_all_sameStrictSign [q, derivative p] x (by
      intro r hr
      simp at hr
      rcases hr with rfl | rfl
      · exact hq0
      · exact hd0)
    filter_upwards [he] with y hy
    have h₁ : SameStrictSign (q.eval x) (q.eval y) := hy q (by simp)
    have h₂ : SameStrictSign ((derivative p).eval x) ((derivative p).eval y) :=
      hy (derivative p) (by simp)
    exact ⟨h₁, h₂⟩
  -- At the point itself the zero first entry is simply ignored.
  have hsigx : sigma p x =
        signChanges (T.map (fun f : ℝ[X] => f.eval x)) := by
    unfold sigma
    rw [hL]
    simp [hx, sc_zero_cons]
  filter_upwards [htail_ev, hqsignev] with y htail hsg
  have hdy0 : (derivative p).eval y ≠ 0 := sss_ne_right hsg.2
  have hqy0 : q.eval y ≠ 0 := sss_ne_right hsg.1
  have hqdpos : 0 < q.eval y * (derivative p).eval y := by
    rcases hsg.1 with hqneg | hqpos
    · -- both centre values are the same, by `hdq`
      have hdnegx : (derivative p).eval x < 0 := by simpa [hdq] using hqneg.1
      rcases hsg.2 with hdneg | hdpos
      · exact mul_pos_of_neg_of_neg hqneg.2 hdneg.2
      · exact (False.elim ((not_lt_of_ge (le_of_lt hdpos.1)) hdnegx))
    · have hdposx : 0 < (derivative p).eval x := by simpa [hdq] using hqpos.1
      rcases hsg.2 with hdneg | hdpos
      · exact (False.elim ((not_lt_of_ge (le_of_lt hdposx)) hdneg.1))
      · exact mul_pos hqpos.2 hdpos.2
  have hform : p.eval y = (y - x) * q.eval y := by
    rw [hq]
    simp [Polynomial.eval_mul, Polynomial.eval_sub]
  constructor
  · intro hyx
    have hyx' : y - x < 0 := sub_neg.mpr hyx
    have hpyn : p.eval y ≠ 0 := by
      rw [hform]
      exact mul_ne_zero (ne_of_lt hyx') hqy0
    have hneg : p.eval y * (derivative p).eval y < 0 := by
      rw [hform]
      rw [mul_assoc]
      exact mul_neg_of_neg_of_pos hyx' hqdpos
    have hfilt : ((T.map (fun f : ℝ[X] => f.eval y)).filter
          (· ≠ (0:ℝ))) = (derivative p).eval y ::
            (U.map (fun f : ℝ[X] => f.eval y)).filter (· ≠ (0:ℝ)) := by
      simp [hTU, hdy0]
    have hrec := sc_cons_of_filter (p.eval y)
        (T.map (fun f : ℝ[X] => f.eval y)) ((derivative p).eval y)
        ((U.map (fun f : ℝ[X] => f.eval y)).filter (· ≠ (0:ℝ))) hpyn hfilt
    unfold sigma
    -- rewrite the count at `y`; at `x` drop its leading zero.
    rw [hL]
    simp only [List.map_cons]
    rw [hrec]
    simp [hneg]
    -- Leave the tail written at `x`.
    -- the goal only involves raw lists now after the unfolding above.
    have hxraw :
        signChanges (p.eval x :: T.map (fun f : ℝ[X] => f.eval x)) =
          signChanges (T.map (fun f : ℝ[X] => f.eval x)) :=
      sc_zero_cons _ |> (fun hh => by simpa [hx] using hh)
    rw [hxraw, ← htail]
    omega
  · intro hyx
    have hyx' : 0 < y - x := sub_pos.mpr hyx
    have hpyn : p.eval y ≠ 0 := by
      rw [hform]
      exact mul_ne_zero (ne_of_gt hyx') hqy0
    have hpos : 0 < p.eval y * (derivative p).eval y := by
      rw [hform]
      rw [mul_assoc]
      exact mul_pos hyx' hqdpos
    have hnneg : ¬ p.eval y * (derivative p).eval y < 0 :=
      not_lt_of_ge (le_of_lt hpos)
    have hfilt : ((T.map (fun f : ℝ[X] => f.eval y)).filter
          (· ≠ (0:ℝ))) = (derivative p).eval y ::
            (U.map (fun f : ℝ[X] => f.eval y)).filter (· ≠ (0:ℝ)) := by
      simp [hTU, hdy0]
    have hrec := sc_cons_of_filter (p.eval y)
        (T.map (fun f : ℝ[X] => f.eval y)) ((derivative p).eval y)
        ((U.map (fun f : ℝ[X] => f.eval y)).filter (· ≠ (0:ℝ))) hpyn hfilt
    unfold sigma
    rw [hL]
    simp only [List.map_cons]
    rw [hrec]
    simp [hnneg]
    have hxraw :
        signChanges (p.eval x :: T.map (fun f : ℝ[X] => f.eval x)) =
          signChanges (T.map (fun f : ℝ[X] => f.eval x)) :=
      sc_zero_cons _ |> (fun hh => by simpa [hx] using hh)
    rw [hxraw]
    exact htail



lemma eventually_order_except (S : Finset ℝ) (x : ℝ) :
    ∀ᶠ y in nhds x, ∀ z ∈ S, z ≠ x → (z ≤ y ↔ z ≤ x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert z S hz ih =>
    by_cases he : z = x
    · subst z
      simpa using ih
    · have ev : ∀ᶠ y in nhds x, z ≤ y ↔ z ≤ x := by
        rcases lt_or_gt_of_ne he with hzx | hzx
        · have hh : ∀ᶠ y in nhds x, (fun _ : ℝ => z) y < id y :=
            continuousAt_const.eventually_lt continuousAt_id hzx
          filter_upwards [hh] with y hy
          constructor <;> intro _
          · exact le_of_lt hzx
          · exact le_of_lt hy
        · have hh : ∀ᶠ y in nhds x, id y < (fun _ : ℝ => z) y :=
            continuousAt_id.eventually_lt continuousAt_const hzx
          filter_upwards [hh] with y hy
          have hxnot : ¬ z ≤ x := not_le_of_gt hzx
          have hynot : ¬ z ≤ y := not_le_of_gt hy
          simp [hxnot, hynot]
      filter_upwards [ev, ih] with y hy htail
      intro w hw hn
      have hw' : w = z ∨ w ∈ S := by simpa using hw
      rcases hw' with rfl | hw'
      · exact hy
      · exact htail w hw' hn

lemma cnt_insert_erase_root (S : Finset ℝ) {x z : ℝ} (hx : x ∈ S) :
    (S.filter (fun t => t ≤ z)).card =
      if x ≤ z then ((S.erase x).filter (fun t => t ≤ z)).card + 1
      else ((S.erase x).filter (fun t => t ≤ z)).card := by
  classical
  conv_lhs =>
    rw [← Finset.insert_erase hx, Finset.filter_insert]
  by_cases h : x ≤ z
  · have hh : x ∉ (S.erase x).filter (fun t => t ≤ z) := by simp
    simp [h, Finset.card_insert_of_notMem hh]
  · simp [h]

/-- Adding the number of roots already passed (with the root itself counted)
to `sigma` removes all jumps. -/
lemma corrected_locally_constant (p : ℝ[X]) (hp : Squarefree p)
    (hp0 : p ≠ 0) (hn : p.natDegree ≠ 0) :
    ∀ x : ℝ, ∀ᶠ y in nhds x,
      sigma p y + ((p.roots.toFinset).filter (fun z => z ≤ y)).card =
        sigma p x + ((p.roots.toFinset).filter (fun z => z ≤ x)).card := by
  classical
  intro x
  let S : Finset ℝ := p.roots.toFinset
  have hroot (z : ℝ) : z ∈ S ↔ p.eval z = 0 := by
    dsimp [S]
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0,
        Polynomial.IsRoot.def]
  by_cases hxS : x ∈ S
  · have hx0 : p.eval x = 0 := (hroot x).mp hxS
    have hf := sigma_jump_at_root p hp hn x hx0
    have ho := eventually_order_except (S.erase x) x
    filter_upwards [hf, ho] with y hy hord
    have hcardT : ((S.erase x).filter (fun z => z ≤ y)).card =
          ((S.erase x).filter (fun z => z ≤ x)).card := by
      congr 1
      ext z
      by_cases hz : z ∈ S.erase x
      · have hnz : z ≠ x := by
          exact fun hh => (Finset.ne_of_mem_erase hz) hh
        have hi := hord z hz hnz
        simp [Finset.mem_filter, hz, hi]
      · simp [Finset.mem_filter, hz]
    change sigma p y + (S.filter (fun z => z ≤ y)).card =
      sigma p x + (S.filter (fun z => z ≤ x)).card
    have hxform := cnt_insert_erase_root S hxS (z := x)
    have hyform := cnt_insert_erase_root S hxS (z := y)
    rcases lt_trichotomy y x with hlt | heq | hgt
    · have hnle : ¬ x ≤ y := not_le_of_gt hlt
      simp [hnle] at hyform
      simp at hxform
      have hf' := hy.1 hlt
      omega
    · subst y
      rfl
    · have hle : x ≤ y := le_of_lt hgt
      simp [hle] at hyform
      simp at hxform
      have hf' := hy.2 hgt
      omega
  · have hx0 : p.eval x ≠ 0 := fun hh => hxS ((hroot x).mpr hh)
    have hf := sigma_eventually_eq_of_not_root p hp hn x hx0
    have ho := eventually_order_except S x
    filter_upwards [hf, ho] with y hy hord
    change sigma p y + (S.filter (fun z => z ≤ y)).card =
      sigma p x + (S.filter (fun z => z ≤ x)).card
    have hcard : (S.filter (fun z => z ≤ y)).card =
          (S.filter (fun z => z ≤ x)).card := by
      congr 1
      ext z
      by_cases hz : z ∈ S
      · have hnz : z ≠ x := by
          intro hh; subst z; exact hxS hz
        have hi := hord z hz hnz
        simp [Finset.mem_filter, hz, hi]
      · simp [Finset.mem_filter, hz]
    rw [hy, hcard]

/-ResultProofDefinitionsEnd-/


theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  have hp0 : p ≠ 0 := by
    intro h; subst p; simpa using ha
  by_cases hn : p.natDegree = 0
  · have he : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn
    have hc : p.coeff 0 ≠ (0:ℝ) := by
      intro h
      apply hp0
      rw [he, h]
      simp
    have hd : p.derivative = 0 := by rw [he]; simp
    have hch : sturmChain p = [p] := by
      unfold sturmChain
      rw [hd]
      cases p.natDegree <;> rfl
    have hs : ∀ x : ℝ, sigma p x = 0 := by
      intro x
      unfold sigma
      rw [hch]
      change signChanges [p.eval x] = 0
      by_cases hh : p.eval x = 0
      · unfold signChanges
        have hf : ([p.eval x].filter (· ≠ (0:ℝ))) = [] := by
          simp only [List.filter_cons, List.filter_nil]
          simp [hh]
        rw [hf]
        rfl
      · unfold signChanges
        have hfilter : ([p.eval x].filter (· ≠ (0:ℝ))) = [p.eval x] := by
          simp [hh]
        rw [hfilter]
        rfl
    have hr : p.roots = 0 := by
      rw [he]
      simp [hc]
    simp [hr, hs]
  · -- the locally constant corrected function connects the endpoints.
    classical
    let S : Finset ℝ := p.roots.toFinset
    have hroot (z : ℝ) : z ∈ S ↔ p.eval z = 0 := by
      dsimp [S]
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0,
          Polynomial.IsRoot.def]
    let g : ℝ → ℕ := fun z =>
      sigma p z + (S.filter (fun t => t ≤ z)).card
    have hloc : ∀ z ∈ Set.Icc a b, ∀ᶠ y in nhds z, g y = g z := by
      intro z hz
      have he := corrected_locally_constant p hp hp0 hn z
      change ∀ᶠ y in nhds z,
        sigma p y + (S.filter (fun t => t ≤ y)).card =
          sigma p z + (S.filter (fun t => t ≤ z)).card
      simpa [S] using he
    have hcb : g a = g b :=
      eq_on_interval_of_eventuallyEq g (le_of_lt hab) hloc
    change sigma p a + (S.filter (fun z => z ≤ a)).card =
        sigma p b + (S.filter (fun z => z ≤ b)).card at hcb
    let A : Finset ℝ := S.filter (fun z => z ≤ a)
    let M : Finset ℝ := S.filter (fun z => a < z ∧ z < b)
    have haS : a ∉ S := fun hh => ha ((hroot a).mp hh)
    have hbS : b ∉ S := fun hh => hb ((hroot b).mp hh)
    have hUnion : S.filter (fun z => z ≤ b) = A ∪ M := by
      ext z
      dsimp [A, M]
      simp only [Finset.mem_filter, Finset.mem_union]
      change (z ∈ S ∧ z ≤ b) ↔
        (z ∈ S ∧ z ≤ a) ∨ (z ∈ S ∧ a < z ∧ z < b)
      constructor
      · intro hz
        have hznb : z ≠ b := by
          intro he; subst z; exact hbS hz.1
        have hlt : z < b := lt_of_le_of_ne hz.2 hznb
        by_cases hza : z ≤ a
        · exact Or.inl ⟨hz.1, hza⟩
        · exact Or.inr ⟨hz.1, lt_of_not_ge hza, hlt⟩
      · intro hz
        rcases hz with hz | hz
        · exact ⟨hz.1, le_trans hz.2 (le_of_lt hab)⟩
        · exact ⟨hz.1, le_of_lt hz.2.2⟩
    have hdisj : Disjoint A M := by
      rw [Finset.disjoint_left]
      intro z hzA hzM
      have hzA' : z ≤ a := (Finset.mem_filter.mp hzA).2
      have hzM' : a < z := (Finset.mem_filter.mp hzM).2.1
      exact (not_lt_of_ge hzA' hzM')
    have hcards : (S.filter (fun z => z ≤ b)).card = A.card + M.card := by
      rw [hUnion]
      exact Finset.card_union_of_disjoint hdisj
    change ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card = _
    change M.card = sigma p a - sigma p b
    change sigma p a + A.card = sigma p b +
        (S.filter (fun z => z ≤ b)).card at hcb
    omega


end Submission
