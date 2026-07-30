import ChallengeDeps
import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Clip.lean
section
open scoped Topology
namespace ShadowingPerturb
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Radial cut-off.  It is convenient because it needs no choice of compact
ball projections and works in every normed space. -/
noncomputable def clip (R : ℝ) (x : F) : F :=
  if ‖x‖ ≤ R then x else (R / ‖x‖) • x

lemma clip_of_norm_le {R : ℝ} {x : F} (h : ‖x‖ ≤ R) :
    clip R x = x := by simp [clip, h]

lemma clip_of_lt_norm {R : ℝ} {x : F} (h : R < ‖x‖) :
    clip R x = (R / ‖x‖) • x := by simp [clip, not_le.mpr h]

lemma clip_norm_le (R : ℝ) (hR : 0 ≤ R) (x : F) :
    ‖clip R x‖ ≤ R := by
  by_cases hx : ‖x‖ ≤ R
  · simpa [clip, hx]
  · have hx' : R < ‖x‖ := lt_of_not_ge hx
    have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hx'
    rw [clip_of_lt_norm hx']
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hR (le_of_lt hxpos))]
    have hxne : ‖x‖ ≠ 0 := ne_of_gt hxpos
    rw [div_mul_cancel₀ _ hxne]

-- the scalar estimate used in the mixed case of radial clipping
private lemma __Clip_mixed_scalar {X Y R : ℝ}
    (hR : 0 < R) (hX : R < X) (hY0 : 0 ≤ Y) (hY : Y ≤ R) :
    (1 - R/X) * Y ≤ X - Y := by
  have hXp : 0 < X := lt_trans hR hX
  apply (le_of_sub_nonneg ?_)
  -- multiplying by `X` removes the only denominator. The remaining
  -- polynomial is `(X-Y)^2 + Y*(R-Y)`.
  apply (mul_nonneg_iff_of_pos_right hXp).1
    -- use a common denominator via `field_simp`
    -- target gets simplified below
  field_simp
  nlinarith [sq_nonneg (X-Y), mul_nonneg hY0 (sub_nonneg.mpr hY)]

private lemma __Clip_out_scalar {X Y R : ℝ}
    (hR : 0 < R) (hX : R < X) (hY : R < Y) (hXY : Y ≤ X) :
    0 ≤ R/Y - R/X ∧ R/Y - R/X ≤ 1 := by
  constructor
  · have hpX : 0 < X := lt_trans hR hX
    have hpY : 0 < Y := lt_trans hR hY
    exact sub_nonneg.mpr ((div_le_div_iff_of_pos_left hR hpX hpY).2 hXY)
  · have hpY : 0 < Y := lt_trans hR hY
    have hnon : 0 ≤ R/X :=
      div_nonneg (le_of_lt hR) (le_of_lt (lt_trans hR hX))
    have hRY : R/Y ≤ 1 := (div_le_iff₀ hpY).2 (by linarith)
    linarith

/-- The radial cut-off is two-Lipschitz, in any normed space.  The slack
constant (rather than a Hilbert metric-projection theorem) is enough for the
fixed point argument. -/
lemma clip_sub_le (R : ℝ) (hR : 0 < R) (x y : F) :
    ‖clip R x - clip R y‖ ≤ 2 * ‖x-y‖ := by
  have hR0 : 0 ≤ R := le_of_lt hR
  by_cases hx : ‖x‖ ≤ R
  · by_cases hy : ‖y‖ ≤ R
    · simpa [clip_of_norm_le hx, clip_of_norm_le hy]
      using (show ‖x-y‖ ≤ 2*‖x-y‖ from
        (by nlinarith [norm_nonneg (x-y)]))
    · have hy' : R < ‖y‖ := lt_of_not_ge hy
      -- use the reverse mixed case below; doing it explicitly keeps the
      -- lemma valid without an inner product.
      rw [norm_sub_rev]
      rw [clip_of_lt_norm hy', clip_of_norm_le hx]
      let a : ℝ := R / ‖y‖
      have hYp : 0 < ‖y‖ := lt_trans hR hy'
      have ha0 : 0 ≤ a := div_nonneg hR0 (le_of_lt hYp)
      have ha1 : a ≤ 1 := (div_le_iff₀ hYp).2 (by linarith)
      have heq : a • y - x = a • (y-x) + (a-1) • x := by
        module
      rw [show (R / ‖y‖) = a from rfl]
      rw [heq]
      have htri := norm_add_le (a • (y-x)) ((a-1) • x)
      have hab : ‖(a-1 : ℝ)‖ = 1-a := by
        rw [Real.norm_of_nonpos (sub_nonpos.mpr ha1)]
        ring
      have hna : ‖(a:ℝ)‖ = a := Real.norm_of_nonneg ha0
      have hmix : (1 - R/‖y‖) * ‖x‖ ≤ ‖y‖ - ‖x‖ :=
        __Clip_mixed_scalar hR hy' (norm_nonneg _) hx
      have hnormdiff : ‖y‖ - ‖x‖ ≤ ‖y-x‖ :=
        norm_sub_norm_le _ _
      have hd : (1-a)*‖x‖ ≤ ‖y-x‖ := by
        change (1-R/‖y‖)*‖x‖ ≤ _
        exact hmix.trans hnormdiff
      have had : a * ‖y-x‖ ≤ ‖y-x‖ :=
        (mul_le_of_le_one_left (norm_nonneg _) ha1)
      calc
        ‖a • (y-x) + (a-1) • x‖
            ≤ ‖a • (y-x)‖ + ‖(a-1) • x‖ := htri
        _ = a * ‖y-x‖ + (1-a)*‖x‖ := by
          rw [norm_smul, norm_smul, hna, hab]
        _ ≤ 2 * ‖y-x‖ := by linarith
        _ = 2 * ‖x-y‖ := by rw [norm_sub_rev]
  · have hx' : R < ‖x‖ := lt_of_not_ge hx
    by_cases hy : ‖y‖ ≤ R
    · rw [clip_of_lt_norm hx', clip_of_norm_le hy]
      let a : ℝ := R/‖x‖
      have hXp : 0 < ‖x‖ := lt_trans hR hx'
      have ha0 : 0 ≤ a := div_nonneg hR0 (le_of_lt hXp)
      have ha1 : a ≤ 1 := (div_le_iff₀ hXp).2 (by linarith)
      rw [show (R/‖x‖) = a from rfl]
      have heq : a • x - y = a • (x-y) + (a-1) • y := by
        module
      rw [heq]
      have hab : ‖(a-1 : ℝ)‖ = 1-a := by
        rw [Real.norm_of_nonpos (sub_nonpos.mpr ha1)]
        ring
      have hna : ‖(a:ℝ)‖ = a := Real.norm_of_nonneg ha0
      have hmix : (1 - R/‖x‖) * ‖y‖ ≤ ‖x‖ - ‖y‖ :=
        __Clip_mixed_scalar hR hx' (norm_nonneg _) hy
      have hdiff : ‖x‖ - ‖y‖ ≤ ‖x-y‖ := norm_sub_norm_le _ _
      have hd : (1-a)*‖y‖ ≤ ‖x-y‖ := by
        change (1-R/‖x‖)*‖y‖ ≤ _
        exact hmix.trans hdiff
      have had : a * ‖x-y‖ ≤ ‖x-y‖ :=
        mul_le_of_le_one_left (norm_nonneg _) ha1
      calc
        ‖a • (x-y) + (a-1) • y‖
            ≤ ‖a • (x-y)‖ + ‖(a-1) • y‖ := norm_add_le _ _
        _ = a * ‖x-y‖ + (1-a)*‖y‖ := by
          rw [norm_smul, norm_smul, hna, hab]
        _ ≤ 2 * ‖x-y‖ := by linarith
    · have hy' : R < ‖y‖ := lt_of_not_ge hy
      have hout : ∀ (u v : F), R < ‖u‖ → R < ‖v‖ → ‖v‖ ≤ ‖u‖ →
          ‖clip R u-clip R v‖ ≤ 2*‖u-v‖ := by
        intro u v hu hv huv
        rw [clip_of_lt_norm hu, clip_of_lt_norm hv]
        let a : ℝ := R/‖u‖
        let b : ℝ := R/‖v‖
        have hup : 0 < ‖u‖ := lt_trans hR hu
        have hvp : 0 < ‖v‖ := lt_trans hR hv
        have ha0 : 0 ≤ a := div_nonneg hR0 (le_of_lt hup)
        have ha1 : a ≤ 1 := (div_le_iff₀ hup).2 (by linarith)
        have hba : 0 ≤ b-a :=
          sub_nonneg.mpr ((div_le_div_iff_of_pos_left hR hup hvp).2 huv)
        rw [show R/‖u‖ = a from rfl, show R/‖v‖ = b from rfl]
        have heq : a • u - b • v =
              a • (u-v) + (a-b) • v := by module
        rw [heq]
        have hab : ‖(a-b : ℝ)‖ = b-a := by
          rw [Real.norm_of_nonpos (by linarith [hba] : a-b ≤ 0)]
          ring
        have hna : ‖(a:ℝ)‖ = a := Real.norm_of_nonneg ha0
        have hterm : (b-a)*‖v‖ =
              a * (‖u‖-‖v‖) := by
          dsimp [a,b]
          field_simp
          <;> ring
        have hdiff : ‖u‖ - ‖v‖ ≤ ‖u-v‖ := norm_sub_norm_le _ _
        have hsmall : (b-a)*‖v‖ ≤ ‖u-v‖ := by
          rw [hterm]
          exact (mul_le_of_le_one_left (sub_nonneg.mpr huv) ha1).trans hdiff
        have hmain : a*‖u-v‖ ≤ ‖u-v‖ :=
          mul_le_of_le_one_left (norm_nonneg _) ha1
        calc
          ‖a • (u-v) + (a-b) • v‖
              ≤ ‖a • (u-v)‖ + ‖(a-b) • v‖ := norm_add_le _ _
          _ = a*‖u-v‖ + (b-a)*‖v‖ := by
            rw [norm_smul, norm_smul, hna, hab]
          _ ≤ 2*‖u-v‖ := by linarith
      by_cases hYX : ‖y‖ ≤ ‖x‖
      · exact hout x y hx' hy' hYX
      · have hXY : ‖x‖ ≤ ‖y‖ := le_of_lt (lt_of_not_ge hYX)
        have hh := hout y x hy' hx' hXY
        simpa [norm_sub_rev] using hh
end ShadowingPerturb

end
-- END INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Clip.lean

-- BEGIN INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Foundation.lean
section

/- Elementary differential facts about a `C^1` homeomorphism which are used in
hyperbolic estimates.  We keep these independent of the particular formulation of a
hyperbolic set. -/
namespace ShadowingFoundation
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivatives of a differentiable homeomorphism and its inverse are inverse
linear maps.  The formulation with application avoids choices of linear equivalences. -/
lemma fderiv_symm_apply_fderiv (f : F ≃ₜ F)
    (hf : Differentiable ℝ (f : F → F))
    (hg : Differentiable ℝ (f.symm : F → F))
    (z v : F) :
    fderiv ℝ (f.symm : F → F) (f z)
        (fderiv ℝ (f : F → F) z v) = v := by
  have hcomp : (f.symm : F → F) ∘ (f : F → F) = (id : F → F) := by
    funext x
    exact f.symm_apply_apply x
  have h := fderiv_comp (𝕜 := ℝ) (f := (f : F → F)) z
      (g := (f.symm : F → F)) (hg (f z)) (hf z)
  -- evaluate the chain rule at `v`
  have heq :
      (fderiv ℝ (f.symm : F → F) (f z) ∘L
        fderiv ℝ (f : F → F) z) = ContinuousLinearMap.id ℝ F := by
    -- for real spaces `∘SL` in the chain rule is definitionally `∘L`
    simpa [hcomp, fderiv_id] using h.symm
  have hv := congrArg (fun q : F →L[ℝ] F => q v) heq
  exact hv

/-- The other order of the inverse derivative identity. -/
lemma fderiv_apply_symm_fderiv (f : F ≃ₜ F)
    (hf : Differentiable ℝ (f : F → F))
    (hg : Differentiable ℝ (f.symm : F → F))
    (z v : F) :
    fderiv ℝ (f : F → F) (f.symm z)
        (fderiv ℝ (f.symm : F → F) z v) = v := by
  -- apply the first statement to the inverse homeomorphism
  simpa using
    (fderiv_symm_apply_fderiv (f := f.symm) (hf := hg) (hg := hf)
      z v)

/-- Iterates of the forward and inverse maps cancel. -/
lemma iterate_symm_apply_iterate (f : F ≃ₜ F) (n : ℕ) (z : F) :
    ((f.symm : F → F)^[n]) (((f : F → F)^[n]) z) = z := by
  -- It is convenient to induct using `Function.iterate_succ_apply`.
  induction n with
  | zero => simp
  | succ n ih =>
      -- our iterate convention puts the first application on the right; repeated
      -- copies of the same function commute.
      -- rewrite the forward successor as applying `f` at the end and the backward
      -- successor at the end as well using `iterate_succ_apply'`.
      -- `Function.iterate_succ_apply` is `[n] (f z)`; for the inverse we need the
      -- variant that applies it last.
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
      rw [f.symm_apply_apply]
      exact ih

lemma iterate_apply_symm_iterate (f : F ≃ₜ F) (n : ℕ) (z : F) :
    ((f : F → F)^[n]) (((f.symm : F → F)^[n]) z) = z := by
  simpa using (iterate_symm_apply_iterate (f := f.symm) n z)

/-- The differential of an iterate also cancels with the differential of the
opposite iterate, at the matching base point. -/
lemma fderiv_symmIter_apply_fderivIter (f : F ≃ₜ F)
    (hf : Differentiable ℝ (f : F → F))
    (hg : Differentiable ℝ (f.symm : F → F))
    (n : ℕ) (z v : F) :
    fderiv ℝ ((f.symm : F → F)^[n]) (((f : F → F)^[n]) z)
      (fderiv ℝ ((f : F → F)^[n]) z v) = v := by
  -- `f^[n]` is again differentiable and has inverse `(f.symm)^[n]`; the
  -- statement follows from the ordinary chain rule and the preceding cancellation.
  have hf' : Differentiable ℝ ((f : F → F)^[n]) := hf.iterate n
  have hg' : Differentiable ℝ ((f.symm : F → F)^[n]) := hg.iterate n
  let A : F →L[ℝ] F := fderiv ℝ ((f : F → F)^[n]) z
  let B : F →L[ℝ] F := fderiv ℝ ((f.symm : F → F)^[n]) (((f : F → F)^[n]) z)
  have hchain := fderiv_comp (𝕜 := ℝ)
    (f := ((f : F → F)^[n])) z
    (g := ((f.symm : F → F)^[n]))
    (hg' _) (hf' z)
  have hfun : ((f.symm : F → F)^[n]) ∘ ((f : F → F)^[n]) = id := by
    funext w
    exact iterate_symm_apply_iterate f n w
  have hlin : B ∘L A = ContinuousLinearMap.id ℝ F := by
    simpa [A, B, hfun, fderiv_id] using hchain.symm
  exact congrArg (fun q : F →L[ℝ] F => q v) hlin

lemma fderiv_iter_apply_fderiv_symmIter (f : F ≃ₜ F)
    (hf : Differentiable ℝ (f : F → F))
    (hg : Differentiable ℝ (f.symm : F → F))
    (n : ℕ) (z v : F) :
    fderiv ℝ ((f : F → F)^[n]) (((f.symm : F → F)^[n]) z)
      (fderiv ℝ ((f.symm : F → F)^[n]) z v) = v := by
  simpa using fderiv_symmIter_apply_fderivIter (f := f.symm)
    (hf := hg) (hg := hf) n z v

end ShadowingFoundation

namespace ShadowingFoundation
open scoped Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If a family of subspaces is preserved by the derivative, it is preserved by
all iterates.  It is useful to record the exact `Submodule.map` statement as well
as just membership. -/
lemma map_fderiv_iterate {f : F → F}
    (hf : Differentiable ℝ f)
    {K : Set F} (hK : ∀ ⦃x⦄, x ∈ K → f x ∈ K)
    (S : F → Submodule ℝ F)
    (hS : ∀ ⦃x⦄, x ∈ K →
      (S x).map (fderiv ℝ f x : F →ₗ[ℝ] F) = S (f x)) :
    ∀ (n : ℕ) ⦃x : F⦄, x ∈ K →
      (S x).map (fderiv ℝ (f^[n]) x : F →ₗ[ℝ] F) = S ((f^[n]) x) := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simpa [fderiv_id] using (Submodule.map_id (S x))
  | succ n ih =>
      intro x hx
      have hx' : (f^[n]) x ∈ K := by
        -- membership is propagated by induction on n, independently of subspaces
        clear ih
        induction n with
        | zero => simpa using hx
        | succ n ih' =>
            rw [Function.iterate_succ_apply']
            exact hK ih'
      -- derivative of the successor iterate.  We use the form `f ∘ f^[n]`.
      have hder :
          fderiv ℝ (f^[n.succ]) x =
            (fderiv ℝ f ((f^[n]) x)).comp
              (fderiv ℝ (f^[n]) x) := by
        -- the usual chain rule gives `∘L` which is `comp`
        rw [Function.iterate_succ']
        simpa using (fderiv_comp (𝕜 := ℝ)
          (f := f^[n]) x (g := f)
          (hf ((f^[n]) x)) ((hf.iterate n) x))
      rw [hder]
      -- rewrite map of a composition as successive maps
      change (Submodule.map
        ((fderiv ℝ f ((f^[n]) x)).comp
          (fderiv ℝ (f^[n]) x) : F →ₗ[ℝ] F) (S x)) = _
      rw [ContinuousLinearMap.toLinearMap_comp, Submodule.map_comp]
      rw [ih hx]
      rw [hS hx']
      rw [Function.iterate_succ_apply']

end ShadowingFoundation
namespace ShadowingFoundation
/-- A constant which is bounded by every member of a geometrically decaying
sequence is zero.  This elementary order/limit observation is handy for
hyperbolic estimates. The other two factors may be any real numbers. -/
lemma eq_zero_of_le_geom {r a C Q : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ha : 0 ≤ a)
    (h : ∀ n : ℕ, a ≤ C * r ^ n * Q) : a = 0 := by
  have hlim0 :
      Filter.Tendsto (fun n : ℕ => C * r ^ n * Q)
        Filter.atTop (nhds 0) := by
    have hr := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hc := hr.const_mul C
    have hd := hc.mul_const Q
    simpa using hd
  have hnonpos : a ≤ (0 : ℝ) :=
    ge_of_tendsto hlim0 (Filter.Eventually.of_forall h)
  exact le_antisymm hnonpos ha
end ShadowingFoundation

end
-- END INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Foundation.lean

-- BEGIN INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Green.lean
section

/- A small, self contained ``Green operator'' for one-sided sequences.
The usual analytic shadowing proof needs to invert the difference equation
`e_{n+1}-L_n e_n=w_n`.  This lemma isolates the linear part: along an
*exact* hyperbolic splitting it has a uniformly bounded right inverse.  Notice the
future sum on the unstable part; on a one sided sequence it is this choice (not
an arbitrary initial condition) which stays bounded.

Everything is stated for continuous linear maps. This avoids choosing bases, and
can be used for a varying splitting. -/
open scoped Topology BigOperators
namespace ShadowingGreen

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- The Green operator for a sequence for which the splitting is exactly
preserved.  `p n` is the stable projection at time `n`, `L n` is the
forward differential and `B n` is its inverse on the unstable summand.
No bounded operator norm is hidden in the conclusion; the two bounds on `p`
are precisely the angle constant. -/
theorem exists_bounded_solution_exact
    (p L B : ℕ → F →L[ℝ] F)
    (w : ℕ → F) (A c C : ℝ)
    (hA : 0 ≤ A) (hc0 : 0 ≤ c) (hc1 : c < 1) (hC : 0 ≤ C)
    (hp_bound : ∀ n (v : F), ‖p n v‖ ≤ A * ‖v‖)
    (hq_bound : ∀ n (v : F), ‖v - p n v‖ ≤ A * ‖v‖)
    (hpp : ∀ n (v : F), p n (p n v) = p n v)
    (hw : ∀ n, ‖w n‖ ≤ C)
    (hstable : ∀ n (v : F), p n v = v →
        p (n+1) (L n v) = L n v ∧ ‖L n v‖ ≤ c * ‖v‖)
    (hLunstable : ∀ n (v : F), p n v = 0 → p (n+1) (L n v) = 0)
    (hBunstable : ∀ n (v : F), p (n+1) v = 0 →
        p n (B n v) = 0 ∧ ‖B n v‖ ≤ c * ‖v‖)
    (hleft : ∀ n (v : F), p (n+1) v = 0 → L n (B n v) = v)
    -- the other inverse equality is not needed for existence, but is true in
    -- applications; it is intentionally not made an assumption.
    : ∃ e : ℕ → F,
        (∀ n, ‖e n‖ ≤ 2 * (A * C / (1-c))) ∧
        (∀ n, e (n+1) - L n (e n) = w n) ∧
        p 0 (e 0) = 0 := by
  have hcpos : 0 < 1 - c := sub_pos.mpr hc1
  have hAC : 0 ≤ A * C := mul_nonneg hA hC
  have hM : 0 ≤ A * C / (1-c) := div_nonneg hAC (le_of_lt hcpos)
  -- the stable (past) part is just a finite recurrence with zero stable
  -- initial condition.
  let s : ℕ → F := fun n =>
    Nat.rec (motive := fun _ => F) 0
      (fun k t => L k t + p (k+1) (w k)) n
  have s_zero : s 0 = 0 := rfl
  have s_succ (n : ℕ) : s (n+1) = L n (s n) + p (n+1) (w n) := by
    rfl
  have hs_mem : ∀ n, p n (s n) = s n := by
    intro n
    induction n with
    | zero => simp [s, map_zero]
    | succ n ih =>
      rw [s_succ]
      rw [map_add]
      have hh := (hstable n (s n) ih).1
      rw [hh]
      rw [hpp]
  have hs_norm : ∀ n, ‖s n‖ ≤ A * C / (1-c) := by
    intro n
    induction n with
    | zero =>
        simp [s, hM]
    | succ n ih =>
      have h1 := (hstable n (s n) (hs_mem n)).2
      have h2 : ‖p (n+1) (w n)‖ ≤ A * C :=
        (hp_bound (n+1) (w n)).trans
          (mul_le_mul_of_nonneg_left (hw n) hA)
      have htop : ‖s (n+1)‖ ≤ c * ‖s n‖ + A * C := by
        calc
          ‖s (n+1)‖ = ‖L n (s n) + p (n+1) (w n)‖ := by rw [s_succ]
          _ ≤ ‖L n (s n)‖ + ‖p (n+1) (w n)‖ := norm_add_le _ _
          _ ≤ c * ‖s n‖ + A * C := add_le_add h1 h2
      have hstep : c * ‖s n‖ ≤ c * (A * C / (1-c)) :=
        mul_le_mul_of_nonneg_left ih hc0
      calc
        ‖s (n+1)‖ ≤ c * ‖s n‖ + A * C := htop
        _ ≤ c * (A*C/(1-c)) + A*C := by
          simpa [add_comm] using (add_le_add_right hstep (A*C))
        _ = A * C / (1-c) := by
          field_simp
          ring
  -- Unstable summands.  `term k n` is the contribution at time `n` of the
  -- error at time `n+k`; it has gone through `k+1` inverse unstable maps.
  let q : ℕ → F → F := fun n v => v - p n v
  have hq_mem (n : ℕ) (v : F) : p n (q n v) = 0 := by
    dsimp [q]
    rw [map_sub, hpp]
    exact sub_self _
  let term : ℕ → ℕ → F := fun k =>
    Nat.rec (motive := fun _ => ℕ → F)
      (fun n => B n (q (n+1) (w n)))
      (fun _ f n => B n (f (n+1))) k
  have term_zero (n : ℕ) : term 0 n = B n (q (n+1) (w n)) := rfl
  have term_succ (k n : ℕ) : term (k+1) n = B n (term k (n+1)) := rfl
  have hterm_mem : ∀ k n, p n (term k n) = 0 := by
    intro k
    induction k with
    | zero =>
        intro n
        exact (hBunstable n _ (hq_mem (n+1) (w n))).1
    | succ k ih =>
        intro n
        rw [term_succ]
        exact (hBunstable n _ (ih (n+1))).1
  have hterm_norm : ∀ k n, ‖term k n‖ ≤ c^(k+1) * (A*C) := by
    intro k
    induction k with
    | zero =>
        intro n
        rw [term_zero]
        have hq : ‖q (n+1) (w n)‖ ≤ A*C :=
          (hq_bound (n+1) (w n)).trans
            (mul_le_mul_of_nonneg_left (hw n) hA)
        have hb := (hBunstable n _ (hq_mem (n+1) (w n))).2
        calc
          ‖B n (q (n+1) (w n))‖ ≤ c * ‖q (n+1) (w n)‖ := hb
          _ ≤ c * (A*C) := mul_le_mul_of_nonneg_left hq hc0
          _ = c^(0+1) * (A*C) := by ring
    | succ k ih =>
        intro n
        rw [term_succ]
        have hb := (hBunstable n _ (hterm_mem k (n+1))).2
        calc
          ‖B n (term k (n+1))‖ ≤ c * ‖term k (n+1)‖ := hb
          _ ≤ c * (c^(k+1) * (A*C)) :=
            mul_le_mul_of_nonneg_left (ih (n+1)) hc0
          _ = c^((k+1)+1) * (A*C) := by ring
  -- geometric majorant and a useful closed form for its sum
  have hgeom0 : Summable (fun k : ℕ => c^k : ℕ → ℝ) := by
    -- (The type ascription is only to keep the scalar field real.)
    exact summable_geometric_of_lt_one hc0 hc1
  have hmaj : Summable (fun k : ℕ => c^(k+1) * (A*C)) := by
    have hg : Summable (fun k : ℕ => (c*(A*C)) * c^k) :=
      Summable.mul_left (c*(A*C)) hgeom0
    -- commute the fixed scalar to the right
    convert hg using 1 <;> ext k <;> ring
  have hmaj_val : (∑' k : ℕ, c^(k+1) * (A*C)) =
        c*(A*C)/(1-c) := by
    calc
      (∑' k : ℕ, c^(k+1) * (A*C)) =
          ∑' k : ℕ, (c*(A*C)) * c^k := by congr 1 <;> funext k <;> ring
      _ = (c*(A*C)) * (∑' k : ℕ, c^k) := by rw [tsum_mul_left]
      _ = (c*(A*C)) * (1-c)⁻¹ := by rw [tsum_geometric_of_lt_one hc0 hc1]
      _ = c*(A*C)/(1-c) := by rw [div_eq_mul_inv]
  have hsum : ∀ n, Summable (fun k : ℕ => term k n) := by
    intro n
    exact Summable.of_norm_bounded hmaj (fun k => hterm_norm k n)
  have hsum_norm : ∀ n, ‖∑' k : ℕ, term k n‖ ≤ c*(A*C)/(1-c) := by
    intro n
    calc
      ‖∑' k : ℕ, term k n‖
          ≤ ∑' k : ℕ, ‖term k n‖ :=
            norm_tsum_le_tsum_norm
              (Summable.of_nonneg_of_le (fun k : ℕ => norm_nonneg _)
                (fun k => hterm_norm k n) hmaj)
      _ ≤ ∑' k : ℕ, c^(k+1) * (A*C) :=
        Summable.tsum_le_tsum (fun k => hterm_norm k n)
          (Summable.of_nonneg_of_le (fun k : ℕ => norm_nonneg _)
            (fun k => hterm_norm k n) hmaj) hmaj
      _ = c*(A*C)/(1-c) := hmaj_val
  let S : ℕ → F := fun n => ∑' k : ℕ, term k n
  have hS_mem (n : ℕ) : p n (S n) = 0 := by
    dsimp [S]
    rw [(p n).map_tsum (hsum n)]
    simp [hterm_mem]
  have hS_norm (n : ℕ) : ‖S n‖ ≤ c*(A*C)/(1-c) := hsum_norm n
  -- peel off the first term of the future series
  have hS_rec (n : ℕ) : S n = B n (q (n+1) (w n) + S (n+1)) := by
    have htt := (hsum n).sum_add_tsum_nat_add 1
    have htail : (∑' i : ℕ, term (i + 1) n) = B n (S (n+1)) := by
      -- pulling a continuous linear map through a summable series is the only
      -- analytic step in the recursion
      rw [(B n).map_tsum (hsum (n+1))]
      -- `map_tsum` reads in the other direction after the rewrite
      -- after `map_tsum` both series have the same terms
    have hfirst : (∑ i ∈ Finset.range 1, term i n) = B n (q (n+1) (w n)) := by
      simp [term_zero]
    -- use linearity to package the two summands
    have hh : (∑ i ∈ Finset.range 1, term i n) +
          (∑' i : ℕ, term (i+1) n) = S n := by
      simpa [S, Nat.add_comm] using (hsum n).sum_add_tsum_nat_add 1
    -- the displayed recursion follows by substituting the two pieces
    rw [hfirst, htail] at hh
    rw [map_add]
    exact hh.symm
  let u : ℕ → F := fun n => - S n
  have hu_mem (n : ℕ) : p n (u n) = 0 := by
    dsimp [u]
    rw [map_neg, hS_mem]
    exact neg_zero
  have hu_norm (n : ℕ) : ‖u n‖ ≤ A*C/(1-c) := by
    have hsmall := hS_norm n
    have hle : c*(A*C)/(1-c) ≤ A*C/(1-c) := by
      have hmul : c * (A*C) ≤ A*C := by
        have := (mul_le_mul_of_nonneg_right (le_of_lt hc1) hAC)
        simpa using this
      exact (div_le_div_iff_of_pos_right hcpos).2 hmul
    simpa [u] using hsmall.trans hle
  have hu_recB (n : ℕ) : u n =
        B n (u (n+1) - q (n+1) (w n)) := by
    have hs' := hS_rec n
    dsimp [u]
    rw [hs']
    -- distribute the minus across a linear map
    rw [← map_neg]
    congr 1
    -- purely additive (the other occurrences of `u` are already unfolded)
    abel
  have hu_rec (n : ℕ) : L n (u n) = u (n+1) - q (n+1) (w n) := by
    rw [hu_recB]
    apply hleft n
    -- both pieces are in the unstable summand
    rw [map_sub, hu_mem, hq_mem, sub_zero]
  refine ⟨fun n => s n + u n, ?_, ?_, ?_⟩
  · intro n
    have ht : ‖s n + u n‖ ≤ ‖s n‖ + ‖u n‖ := norm_add_le _ _
    have hbounds : ‖s n‖ + ‖u n‖ ≤
          A*C/(1-c) + A*C/(1-c) :=
      add_le_add (hs_norm n) (hu_norm n)
    calc
      ‖s n + u n‖ ≤ A*C/(1-c) + A*C/(1-c) := ht.trans hbounds
      _ = 2 * (A*C/(1-c)) := by ring
  · intro n
    have hu' := hu_rec n
    have hs' := s_succ n
    -- add the stable and unstable recurrences and use `q v = v-p v`.
    change (s (n+1) + u (n+1)) - L n (s n + u n) = _
    rw [hs']
    rw [map_add]
    dsimp [q] at hu'
    -- linear, so the rest is just commutative group arithmetic
    rw [hu']
    abel
  · simp [s_zero, hu_mem]


/-- On a one sided sequence the preceding construction fixed the stable
initial condition (`p 0 (e 0)=0`).  With that convention the bounded solution
is unique.  This small fact is useful: it makes the chosen Green solver linear,
even if it was introduced by choice. -/
theorem bounded_hom_solution_zero
    (p L B : ℕ → F →L[ℝ] F) (c C : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hC : 0 ≤ C)
    (hLunstable : ∀ n (v : F), p n v = 0 → p (n+1) (L n v) = 0)
    (hBL : ∀ n (v : F), p n v = 0 → B n (L n v) = v)
    (hBcontract : ∀ n (v : F), p (n+1) v = 0 →
        ‖B n v‖ ≤ c * ‖v‖)
    (e : ℕ → F)
    (he : ∀ n, e (n+1) = L n (e n))
    (he0 : p 0 (e 0) = 0)
    (hebd : ∀ n, ‖e n‖ ≤ C) :
    ∀ n, e n = 0 := by
  have hemem : ∀ n, p n (e n) = 0 := by
    intro n
    induction n with
    | zero => exact he0
    | succ n ih =>
        rw [he n]
        exact hLunstable n _ ih
  have heback (n : ℕ) : e n = B n (e (n+1)) := by
    rw [he n]
    exact (hBL n _ (hemem n)).symm
  have hpow : ∀ k : ℕ, ∀ n : ℕ, ‖e n‖ ≤ c^k * C := by
    intro k
    induction k with
    | zero =>
        intro n
        simpa using hebd n
    | succ k ih =>
        intro n
        calc
          ‖e n‖ = ‖B n (e (n+1))‖ := by rw [heback n]
          _ ≤ c * ‖e (n+1)‖ := hBcontract n _ (hemem (n+1))
          _ ≤ c * (c^k * C) :=
            mul_le_mul_of_nonneg_left (ih (n+1)) hc0
          _ = c^(k+1) * C := by ring
  intro n
  have hlim : Filter.Tendsto (fun k : ℕ => c^k * C)
        Filter.atTop (nhds (0:ℝ)) := by
    have hc := tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
    simpa using hc.mul_const C
  have hzle : ‖e n‖ ≤ (0:ℝ) :=
    ge_of_tendsto hlim
      (Filter.Eventually.of_forall (fun k => hpow k n))
  exact norm_eq_zero.mp (le_antisymm hzle (norm_nonneg _))


/-- The bounded solutions can be chosen coherently as a bounded, Lipschitz
Green solver.  We record the norm difference (the input normally comes with
the sup norm); this avoids rebuilding the two infinite series during a
Picard argument. -/
theorem exists_green_solver
    (p L B : ℕ → F →L[ℝ] F) (A c : ℝ)
    (hA : 0 ≤ A) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hp_bound : ∀ n (v : F), ‖p n v‖ ≤ A * ‖v‖)
    (hq_bound : ∀ n (v : F), ‖v - p n v‖ ≤ A * ‖v‖)
    (hpp : ∀ n (v : F), p n (p n v) = p n v)
    (hstable : ∀ n (v : F), p n v = v →
        p (n+1) (L n v) = L n v ∧ ‖L n v‖ ≤ c * ‖v‖)
    (hLunstable : ∀ n (v : F), p n v = 0 → p (n+1) (L n v) = 0)
    (hBunstable : ∀ n (v : F), p (n+1) v = 0 →
        p n (B n v) = 0 ∧ ‖B n v‖ ≤ c * ‖v‖)
    (hleft : ∀ n (v : F), p (n+1) v = 0 → L n (B n v) = v)
    (hright : ∀ n (v : F), p n v = 0 → B n (L n v) = v) :
    ∃ G : (BoundedContinuousFunction ℕ F) →
          (BoundedContinuousFunction ℕ F),
      (∀ w n, G w (n+1) - L n (G w n) = w n) ∧
      (∀ w, p 0 (G w 0) = 0) ∧
      (∀ w, ‖G w‖ ≤ 2 * (A * ‖w‖ / (1-c))) ∧
      (∀ u v, ‖G u - G v‖ ≤ 2 * (A * ‖u-v‖ / (1-c))) := by
  classical
  -- Existence with a canonical boundary condition for each bounded forcing.
  have hex (w : BoundedContinuousFunction ℕ F) :
      ∃ e : BoundedContinuousFunction ℕ F,
        (∀ n, e (n+1) - L n (e n) = w n) ∧
        p 0 (e 0) = 0 ∧
        ‖e‖ ≤ 2 * (A * ‖w‖ / (1-c)) := by
    have h0 : 0 ≤ ‖w‖ := norm_nonneg _
    obtain ⟨z,hz,hr,hz0⟩ := exists_bounded_solution_exact
        (p:=p) (L:=L) (B:=B) (w:= fun n => w n)
        (A:=A) (c:=c) (C:=‖w‖)
        hA hc0 hc1 h0 hp_bound hq_bound hpp
          (fun n => BoundedContinuousFunction.norm_coe_le_norm w n)
          hstable hLunstable hBunstable hleft
    let ee : BoundedContinuousFunction ℕ F :=
      BoundedContinuousFunction.ofNormedAddCommGroupDiscrete z
        (2 * (A * ‖w‖ / (1-c))) hz
    refine ⟨ee, ?_, ?_, ?_⟩
    · intro n
      change z (n+1) - L n (z n) = w n
      exact hr n
    · change p 0 (z 0) = 0
      exact hz0
    · have hnon : 0 ≤ 2 * (A * ‖w‖ / (1-c)) := by
        have hp : 0 ≤ 1-c := le_of_lt (sub_pos.mpr hc1)
        positivity
      exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
        (ee.continuous) hnon hz
  choose G hrec hp0 hnorm using hex
  refine ⟨G, hrec, hp0, hnorm, ?_⟩
  intro u v
  -- Difference of two chosen solutions is the chosen solution of the
  -- difference.  Prove it by the bounded homogeneous uniqueness lemma.
  let h : BoundedContinuousFunction ℕ F := (G u - G v) - G (u-v)
  have hrec0 (n : ℕ) : h (n+1) = L n (h n) := by
    have h1 := hrec u n
    have h2 := hrec v n
    have h3 := hrec (u-v) n
    change (G u (n+1) - G v (n+1)) - G (u-v) (n+1) =
        L n ((G u n - G v n) - G (u-v) n)
    change G u (n+1) - L n (G u n) = u n at h1
    change G v (n+1) - L n (G v n) = v n at h2
    change G (u-v) (n+1) - L n (G (u-v) n) =
      u n - v n at h3
    rw [map_sub, map_sub]
    -- eliminate all source terms
    have h1' : G u (n+1) = L n (G u n) + u n :=
      (sub_eq_iff_eq_add').1 h1
    have h2' : G v (n+1) = L n (G v n) + v n :=
      (sub_eq_iff_eq_add').1 h2
    have h3' : G (u-v) (n+1) = L n (G (u-v) n) + (u n - v n) :=
      (sub_eq_iff_eq_add').1 h3
    rw [h1', h2', h3']
    abel

  have hpz : p 0 (h 0) = 0 := by
    change p 0 ((G u 0 - G v 0) - G (u-v) 0) = 0
    rw [map_sub, map_sub, hp0, hp0, hp0]
    abel
  have hzero : ∀ n, h n = 0 :=
    bounded_hom_solution_zero (p:=p) (L:=L) (B:=B)
      (c:=c) (C:=‖h‖) hc0 hc1 (norm_nonneg _)
      hLunstable hright (fun n v hv => (hBunstable n v hv).2)
      (fun n => h n) hrec0 hpz
      (fun n => BoundedContinuousFunction.norm_coe_le_norm h n)
  have heq : G u - G v = G (u-v) := by
    ext n
    have hh := hzero n
    change (G u n - G v n) - G (u-v) n = 0 at hh
    exact sub_eq_zero.mp hh
  rw [heq]
  exact hnorm (u-v)
end ShadowingGreen

end
-- END INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Green.lean

-- BEGIN INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Uniform.lean
section

namespace ShadowingFoundation
open scoped Topology
open Filter Set

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A continuous function has a modulus uniform at the points of a compact set;
no compactness of a whole neighbourhood is required.  The second argument is
allowed to range in the ambient space.  This slightly asymmetric formulation
is often convenient for Taylor estimates near a compact set. -/
lemma compact_uniform_close {K : Set F} (hK : IsCompact K)
    (g : F → G) (hg : Continuous g) :
    ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧
      ∀ z : F, z ∈ K → ∀ t : F, ‖t - z‖ < r → ‖g t - g z‖ < η := by
  classical
  intro η hη
  by_contra hn
  have hfail : ∀ r : ℝ, 0 < r →
      ∃ z : F, ∃ hz : z ∈ K, ∃ t : F,
        ‖t - z‖ < r ∧ η ≤ ‖g t - g z‖ := by
    intro r hr
    have hh : ¬ (∀ z : F, z ∈ K → ∀ t : F,
          ‖t - z‖ < r → ‖g t - g z‖ < η) := by
      intro hall
      apply hn
      exact ⟨r, hr, fun z hz t ht => hall z hz t ht⟩
    push_neg at hh
    rcases hh with ⟨z,hz,t,ht,hg'⟩
    exact ⟨z,hz,t,ht,hg'⟩
  have hrn (n : ℕ) : 0 < (1:ℝ) / ((n:ℝ) + 1) := by positivity
  choose z hz t hzt hbad using
    (fun n : ℕ => hfail ((1:ℝ) / ((n:ℝ) + 1)) (hrn n))
  obtain ⟨w, hw, φ, hφ, hzlim⟩ := hK.tendsto_subseq hz
  have hnorm0 : Tendsto (fun n : ℕ => ‖t n - z n‖)
        atTop (nhds (0:ℝ)) := by
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact le_of_lt (hzt n)
  have hnorm0' : Tendsto (fun j : ℕ => ‖t (φ j) - z (φ j)‖)
        atTop (nhds (0:ℝ)) := by
    simpa [Function.comp_def] using hnorm0.comp hφ.tendsto_atTop
  have hdiff : Tendsto (fun j : ℕ => t (φ j) - z (φ j))
        atTop (nhds (0 : F)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm0'
  have hztlim : Tendsto (fun j : ℕ => z (φ j)) atTop (nhds w) := by
    simpa [Function.comp_def] using hzlim
  have htlim : Tendsto (fun j : ℕ => t (φ j)) atTop (nhds w) := by
    have hh := hdiff.add hztlim
    simpa [sub_add_cancel] using hh
  have hg1 : Tendsto (fun j : ℕ => g (t (φ j))) atTop (nhds (g w)) :=
    (hg.tendsto w).comp htlim
  have hg2 : Tendsto (fun j : ℕ => g (z (φ j))) atTop (nhds (g w)) :=
    (hg.tendsto w).comp hztlim
  have hzero : Tendsto (fun j : ℕ => ‖g (t (φ j)) - g (z (φ j))‖)
        atTop (nhds (0:ℝ)) := by
    have hh := (hg1.sub hg2).norm
    simpa using hh
  have hη0 : η ≤ (0:ℝ) :=
    ge_of_tendsto hzero (Filter.Eventually.of_forall (fun j => hbad (φ j)))
  exact (not_le_of_gt hη) hη0

/-- Uniform first-order Taylor estimate for a `C^1` map along a compact set.
We use a closed scalar bound rather than little-o; it is robust under the
finite sums in the sequence shadowing argument. -/
lemma contDiff_compact_first_order {K : Set F} (hK : IsCompact K)
    (f : F → G) (hf : ContDiff ℝ 1 f) :
    ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧
      ∀ z : F, z ∈ K → ∀ t : F, ‖t - z‖ < r →
        ‖f t - f z - fderiv ℝ f z (t - z)‖ ≤ η * ‖t - z‖ := by
  classical
  intro η hη
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  obtain ⟨r, hr, hclose⟩ :=
    compact_uniform_close (F := F) (G := F →L[ℝ] G) hK
      (fderiv ℝ f) hdc η hη
  refine ⟨r, hr, ?_⟩
  intro z hz t htz
  let A : F →L[ℝ] G := fderiv ℝ f z
  let q : F → G := fun u => f u - A u
  have hqder (u : F) : HasFDerivAt q (fderiv ℝ f u - A) u := by
    -- the second summand is a continuous linear map
    convert
      (((hf.differentiable (by norm_num)) u).hasFDerivAt.sub
        A.hasFDerivAt) using 1
    ext x
    rfl
  have hqdiff (u : F) : DifferentiableAt ℝ q u := (hqder u).differentiableAt
  have hqfder (u : F) : fderiv ℝ q u = fderiv ℝ f u - A :=
    (hqder u).fderiv
  have hbound : ∀ u ∈ segment ℝ z t, ‖fderiv ℝ q u‖ ≤ η := by
    intro u hu
    have hdist : ‖u - z‖ < r :=
      lt_of_le_of_lt (norm_sub_le_of_mem_segment hu) htz
    have hlt : ‖fderiv ℝ f u - fderiv ℝ f z‖ < η :=
      hclose z hz u hdist
    -- use the derivative formula of q
    simpa [hqfder, A] using (le_of_lt hlt)
  have hmv : ‖q t - q z‖ ≤ η * ‖t - z‖ :=
    (convex_segment z t).norm_image_sub_le_of_norm_fderiv_le
      (fun u hu => hqdiff u) hbound (left_mem_segment ℝ z t)
        (right_mem_segment ℝ z t)
  have heq : q t - q z = f t - f z - fderiv ℝ f z (t - z) := by
    dsimp [q, A]
    -- it remains the linearity of the distinguished derivative
    rw [map_sub]
    abel
  simpa [heq] using hmv

end ShadowingFoundation

namespace ShadowingFoundation
open scoped Topology
open Set Filter
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The version of `contDiff_compact_first_order` used in a fixed point
argument: the nonlinear remainder, based at a point of the compact set, is
uniformly Lipschitz on a small ball.  Having two moving endpoints rather than
one is essential for a contraction argument. -/
lemma contDiff_compact_lipschitz_remainder {K : Set F} (hK : IsCompact K)
    (f : F → G) (hf : ContDiff ℝ 1 f) :
    ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧
      ∀ z : F, z ∈ K → ∀ x y : F,
        ‖x - z‖ < r → ‖y - z‖ < r →
        ‖(f x - f z - fderiv ℝ f z (x - z)) -
           (f y - f z - fderiv ℝ f z (y - z))‖
            ≤ η * ‖x - y‖ := by
  classical
  intro η hη
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  obtain ⟨r, hr, hclose⟩ :=
    compact_uniform_close (F := F) (G := F →L[ℝ] G) hK
      (fderiv ℝ f) hdc η hη
  refine ⟨r, hr, ?_⟩
  intro z hz x y hx hy
  let A : F →L[ℝ] G := fderiv ℝ f z
  let q : F → G := fun u => f u - A u
  have hxball : x ∈ Metric.ball z r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hyball : y ∈ Metric.ball z r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hseg : segment ℝ y x ⊆ Metric.ball z r :=
    (convex_ball z r).segment_subset hyball hxball
  have hqder (u : F) : HasFDerivAt q (fderiv ℝ f u - A) u := by
    convert (((hf.differentiable (by norm_num)) u).hasFDerivAt.sub
        A.hasFDerivAt) using 1
    ext v
    rfl
  have hqfder (u : F) : fderiv ℝ q u = fderiv ℝ f u - A :=
    (hqder u).fderiv
  have hbound : ∀ u ∈ segment ℝ y x, ‖fderiv ℝ q u‖ ≤ η := by
    intro u hu
    have hball := hseg hu
    have hd : ‖u - z‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hball
    have hlt := hclose z hz u hd
    rw [hqfder]
    exact le_of_lt hlt
  have hmv : ‖q x - q y‖ ≤ η * ‖x - y‖ :=
    (convex_segment y x).norm_image_sub_le_of_norm_fderiv_le
      (fun u hu => (hqder u).differentiableAt)
      hbound (left_mem_segment ℝ y x) (right_mem_segment ℝ y x)
  have heq : (f x - f z - fderiv ℝ f z (x - z)) -
           (f y - f z - fderiv ℝ f z (y - z)) = q x - q y := by
    dsimp [q, A]
    rw [map_sub, map_sub]
    abel
  rw [heq]
  exact hmv
end ShadowingFoundation

end
-- END INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Uniform.lean

-- BEGIN INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Perturb.lean
section

/-! Elementary perturbation and fixed-point lemmas for the sequence Green
operator. These are deliberately phrased just with sup norms.  A useful
feature is that no measurability/topology hypotheses are needed on a function
of `ℕ`: the domain is discrete. -/
open scoped Topology
open Function
namespace ShadowingPerturb
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A Lipschitz right inverse for the difference operator turns a uniformly
Lipschitz nonlinear error into an honest solution.  We state the smallness
condition with a real number `q`; using its associated `NNReal` for Banach's
fixed point theorem is a small but annoying coercion each time this argument
is used. -/
theorem exists_solution_of_green
    (L : ℕ → F →L[ℝ] F)
    (G : BoundedContinuousFunction ℕ F →
          BoundedContinuousFunction ℕ F)
    (M k : ℝ) (hM : 0 ≤ M) (hk : 0 ≤ k) (hsmall : M*k < 1)
    (hrec : ∀ w n, G w (n+1) - L n (G w n) = w n)
    (hG : ∀ u v, ‖G u - G v‖ ≤ M * ‖u-v‖)
    (W : BoundedContinuousFunction ℕ F →
          BoundedContinuousFunction ℕ F)
    (hW : ∀ u v, ‖W u - W v‖ ≤ k * ‖u-v‖) :
    ∃ e : BoundedContinuousFunction ℕ F,
      (∀ n, e (n+1) - L n (e n) = W e n) := by
  classical
  let q : ℝ := M*k
  have hq0 : 0 ≤ q := by dsimp [q]; exact mul_nonneg hM hk
  let Q : NNReal := ⟨q, hq0⟩
  have hQlt : Q < 1 := by
    change q < (1:ℝ)
    exact hsmall
  let Phi : (BoundedContinuousFunction ℕ F) →
        BoundedContinuousFunction ℕ F := fun u => G (W u)
  have hLip : LipschitzWith Q Phi := by
    refine LipschitzWith.of_dist_le_mul ?_
    -- on an additive normed group, the metric is the norm of a difference
    intro u v
    -- `LipschitzWith` on an emetric space is expressed using distance; its
    -- metric version reduces coercions to a real multiplication.
    have h1 : ‖G (W u) - G (W v)‖ ≤ M * ‖W u - W v‖ := hG _ _
    have h2 : ‖W u - W v‖ ≤ k * ‖u-v‖ := hW _ _
    have h3 : M * ‖W u-W v‖ ≤ M * (k*‖u-v‖) :=
      mul_le_mul_of_nonneg_left h2 hM
    have hh : ‖G (W u) - G (W v)‖ ≤ (M*k) * ‖u-v‖ := by
      calc
        ‖G (W u) - G (W v)‖ ≤ M * ‖W u - W v‖ := h1
        _ ≤ M * (k * ‖u-v‖) := h3
        _ = (M*k) * ‖u-v‖ := by ring
    -- unfold the metric instance for bounded functions
    -- `Q` coerces to the real `q`.
    simp only [dist_eq_norm_sub]
    change ‖G (W u) - G (W v)‖ ≤ (M*k) * ‖u-v‖
    exact hh
  have hcontr : ContractingWith Q Phi := ⟨hQlt, hLip⟩
  let e : BoundedContinuousFunction ℕ F :=
    ContractingWith.fixedPoint Phi hcontr
  refine ⟨e, ?_⟩
  have he : Phi e = e := hcontr.fixedPoint_isFixedPt
  have hev (i : ℕ) : G (W e) i = e i := by
    have hh : G (W e) = e := by simpa [Phi] using he
    exact DFunLike.congr_fun hh i
  intro n
  have hr := hrec (W e) n
  change e (n+1) - L n (e n) = _
  rw [← hev (n+1), ← hev n]
  exact hr


/-- The simple intertwiner between two nearby projections.  It does not use
an inverse: algebraically it already sends the first range/kernel to the
second ones. -/
def changeProj (p r : F →L[ℝ] F) : F →L[ℝ] F :=
  p.comp r + (1-p).comp (1-r)

lemma changeProj_apply (p r : F →L[ℝ] F) (x : F) :
    changeProj p r x = p (r x) + (x-r x-p (x-r x)) := by
  -- Keeping this expanded version is often more useful than the abstract
  -- formula when estimating norms.
  simp [changeProj, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- `abel` avoids depending on the precise normal form of `simp` for maps.
  -- (the leftover terms live in `F`, not in the endomorphism algebra)
  <;> abel

lemma changeProj_eq (p r : F →L[ℝ] F) [DecidableEq F]
    (hp : ∀ x : F, p (p x) = p x)
    (hr : ∀ x : F, r (r x) = r x) (x : F) :
    changeProj p r (r x) = p (r x) := by
  simp [changeProj, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, hp, hr]

-- Same facts without the needless `[DecidableEq F]`; kept as a convenient
-- rewriting lemma during construction of a transported cocycle.
lemma changeProj_range (p r : F →L[ℝ] F)
    (hp : ∀ x : F, p (p x) = p x)
    (hr : ∀ x : F, r (r x) = r x) (x : F) :
    changeProj p r (r x) = p (changeProj p r x) := by
  -- both sides are `p (r x)`
  simp [changeProj, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, hp (r x), hp x,
    hr x]

lemma changeProj_kernel (p r : F →L[ℝ] F)
    (hp : ∀ x : F, p (p x) = p x)
    (hr : ∀ x : F, r (r x) = r x)
    {x : F} (hx : r x = 0) :
    p (changeProj p r x) = 0 := by
  -- use the commutation formula rather than expanding twice
  rw [← changeProj_range p r hp hr]
  simp [hx]

/-- Pointwise deviation of the intertwiner from the identity. The form with
only a bound on `r` is enough to make the Neumann argument uniform. -/
lemma changeProj_sub_id_bound (p r : F →L[ℝ] F)
    (k M : ℝ)
    (hridem : ∀ x : F, r (r x) = r x)
    (hclose : ∀ x : F, ‖p x - r x‖ ≤ k * ‖x‖)
    (hrb : ∀ x : F, ‖r x‖ ≤ M * ‖x‖)
    (hk' : 0 ≤ k) (hM' : 0 ≤ M) (x : F) :
    ‖changeProj p r x - x‖ ≤ (k * (2*M+1)) * ‖x‖ := by
  have hid : changeProj p r x - x =
        (p ( (2:ℝ) • r x - x) - r ((2:ℝ) • r x - x)) := by
    simp [changeProj, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, map_sub, map_smul, hridem x]
    -- this is merely the standard formula
    <;> module
  rw [hid]
  have h1 := hclose ((2:ℝ) • r x - x)
  have h2 : ‖(2:ℝ) • r x - x‖ ≤ (2*M+1) * ‖x‖ := by
    calc
      ‖(2:ℝ) • r x - x‖ ≤ ‖(2:ℝ) • r x‖ + ‖x‖ := norm_sub_le _ _
      _ = 2 * ‖r x‖ + ‖x‖ := by norm_num [norm_smul]
      _ ≤ 2 * (M*‖x‖) + ‖x‖ := by linarith [hrb x]
      _ = (2*M+1)*‖x‖ := by ring
  calc
    ‖p ((2:ℝ) • r x - x) - r ((2:ℝ) • r x - x)‖
        ≤ k * ‖(2:ℝ) • r x - x‖ := h1
    _ ≤ k * ((2*M+1) * ‖x‖) :=
      mul_le_mul_of_nonneg_left h2 hk'
    _ = (k*(2*M+1)) * ‖x‖ := by ring

end ShadowingPerturb

namespace ShadowingPerturb
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A quantitative Neumann lemma phrased pointwise.  The lower bound for the
inverse follows from the triangle inequality, so no delicate norm estimate for
an inverse in a Banach algebra is needed. -/
theorem inverse_of_almost_id (C : F →L[ℝ] F)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hst : ∀ x : F, ‖C x - x‖ ≤ θ * ‖x‖) :
    ∃ I : F →L[ℝ] F,
      (∀ x, C (I x) = x) ∧ (∀ x, I (C x) = x) ∧
      (∀ x, ‖I x‖ ≤ (1/(1-θ))*‖x‖) ∧
      (∀ x, ‖C x‖ ≤ (1+θ)*‖x‖) := by
  classical
  let t : F →L[ℝ] F := 1-C
  have htpoint (x : F) : ‖t x‖ ≤ θ * ‖x‖ := by
    change ‖x - C x‖ ≤ _
    rw [norm_sub_rev]
    exact hst x
  have ht : ‖t‖ < (1:ℝ) :=
    lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound t hθ0 htpoint) hθ1
  let u : (F →L[ℝ] F)ˣ := Units.oneSub t ht
  have hu : (u : F →L[ℝ] F) = C := by
    change (1-t : F →L[ℝ] F) = C
    dsimp [t]
    abel
  let I : F →L[ℝ] F := (u⁻¹ : (F →L[ℝ] F)ˣ)
  have hCI : (C * I : F →L[ℝ] F) = 1 := by
    change C * (↑(u⁻¹) : F →L[ℝ] F) = 1
    rw [← hu]
    exact Units.mul_inv u
  have hIC : (I * C : F →L[ℝ] F) = 1 := by
    change (↑(u⁻¹) : F →L[ℝ] F) * C = 1
    rw [← hu]
    exact Units.inv_mul u
  have hCI' (x : F) : C (I x) = x := by
    have := DFunLike.congr_fun hCI x
    simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using this
  have hIC' (x : F) : I (C x) = x := by
    have := DFunLike.congr_fun hIC x
    simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using this
  refine ⟨I, hCI', hIC', ?_, ?_⟩
  · intro x
    have hp := hst (I x)
    have tri : ‖I x‖ ≤ ‖x‖ + ‖C (I x) - I x‖ := by
      -- write `I x` as `x - (C(I x)-I x)`
      have hh : I x = x - (C (I x) - I x) := by
        rw [hCI']
        abel
      calc
        ‖I x‖ = ‖x - (C (I x) - I x)‖ := congrArg norm hh
        _ ≤ ‖x‖ + ‖C (I x) - I x‖ := norm_sub_le _ _
    have key : (1-θ)*‖I x‖ ≤ ‖x‖ := by
      have hh : ‖C (I x) - I x‖ ≤ θ*‖I x‖ := hp
      calc
        (1-θ)*‖I x‖ = ‖I x‖ - θ*‖I x‖ := by ring
        _ ≤ ‖I x‖ - ‖C (I x)-I x‖ := sub_le_sub_left hh _
        _ ≤ ‖x‖ := (sub_le_iff_le_add).2 (by
            -- the triangle estimate just obtained
            simpa [add_comm] using tri)
    have hpθ : 0 < 1-θ := sub_pos.mpr hθ1
    have hh : ‖I x‖ ≤ ‖x‖ / (1-θ) :=
      (le_div_iff₀ hpθ).2 (by
        -- `key` has the factors in the other order
        simpa [mul_comm] using key)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  · intro x
    have ht' := hst x
    calc
      ‖C x‖ ≤ ‖x‖ + ‖C x - x‖ := by
        have hz : C x = x + (C x - x) := by abel
        calc
          ‖C x‖ = ‖x + (C x - x)‖ := congrArg norm hz
          _ ≤ ‖x‖ + ‖C x - x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + θ*‖x‖ := add_le_add (le_rfl) ht'
      _ = (1+θ)*‖x‖ := by ring
end ShadowingPerturb

namespace ShadowingPerturb
open scoped Topology
open Function
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite piece of a pseudo-orbit which starts sufficiently close to the
compact invariant set stays close at its last time to the corresponding true
orbit.  The input sequence is completely arbitrary (we will repeatedly shift
it); there is no compactness assumption on its intermediate points.  This is
often the clean way to pass from one-step errors to blocking. -/
lemma finite_pseudo_close {K : Set F} (hK : IsCompact K)
    (f : F → F) (hf : Continuous f) (hmap : Set.MapsTo f K K) :
    ∀ (N : ℕ) (a : ℝ), 0 < a →
      ∃ s : ℝ, 0 < s ∧ ∃ e : ℝ, 0 < e ∧
        ∀ z : F, z ∈ K → ∀ u : ℕ → F,
          ‖u 0-z‖ < s →
          (∀ i < N, ‖u (i+1) - f (u i)‖ < e) →
          ‖u N - (f^[N]) z‖ < a := by
  have hziter (n : ℕ) : ∀ z : F, z ∈ K → (f^[n]) z ∈ K := by
    induction n with
    | zero =>
      intro z hz
      simpa using hz
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      exact hmap (ih z hz)
  intro N
  induction N with
  | zero =>
      intro a ha
      refine ⟨a, ha, a, ha, ?_⟩
      intro z hz u hu hstep
      simpa using hu
  | succ N ih =>
      intro a ha
      have ha2 : 0 < a/2 := by linarith
      obtain ⟨rho, hrho, hclose⟩ :=
        ShadowingFoundation.compact_uniform_close (F:=F) (G:=F)
          hK f hf (a/2) ha2
      obtain ⟨s, hs, e0, he0, hold⟩ := ih rho hrho
      let e : ℝ := min e0 (a/2)
      have he : 0 < e := lt_min he0 ha2
      refine ⟨s, hs, e, he, ?_⟩
      intro z hz u hu hsteps
      have hfirst :
          ‖u N - (f^[N]) z‖ < rho := by
        apply hold z hz u hu
        intro i hi
        exact lt_of_lt_of_le (hsteps i (Nat.lt_trans hi (Nat.lt_succ_self _)))
          (min_le_left _ _)
      have hz1 : (f^[N]) z ∈ K := hziter N z hz
      have hFclose : ‖f (u N) - f ((f^[N]) z)‖ < a/2 :=
        hclose _ hz1 _ hfirst
      have hlast' : ‖u (N+1) - f (u N)‖ < e :=
        hsteps N (Nat.lt_succ_self _)
      have hlast : ‖u (N+1) - f (u N)‖ < a/2 :=
        lt_of_lt_of_le hlast' (min_le_right _ _)
      calc
        ‖u (N+1) - (f^[N+1]) z‖ =
            ‖(u (N+1) - f (u N)) + (f (u N) - f ((f^[N]) z))‖ := by
              rw [Function.iterate_succ_apply']
              congr 1
              abel
        _ ≤ ‖u (N+1) - f (u N)‖ +
                ‖f (u N) - f ((f^[N]) z)‖ := norm_add_le _ _
        _ < a := by linarith

end ShadowingPerturb

end
-- END INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Perturb.lean

-- BEGIN INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Step.lean
section

open scoped Topology
open Function
namespace ShadowingPerturb
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite pseudo trajectory starting *at* a point of a compact set follows
that point's true iterate.  No invariance is required: at the `i`th step one
uses compactness of the image under the first `i` iterates.  This is the
version needed when the broken base points themselves are not in the
hyperbolic compact set. -/
lemma finite_pseudo_same (f : F → F) (hf : Continuous f) (C : Set F)
    (hC : IsCompact C) :
    ∀ (N : ℕ) (a : ℝ), 0 < a →
      ∃ e : ℝ, 0 < e ∧
        ∀ z : F, z ∈ C → ∀ u : ℕ → F,
          u 0 = z →
          (∀ i < N, ‖u (i+1) - f (u i)‖ < e) →
          ‖u N - (f^[N]) z‖ < a := by
  intro N
  induction N with
  | zero =>
      intro a ha
      refine ⟨1, by norm_num, ?_⟩
      intro z hz u hu hstep
      simpa [hu]
  | succ N ih =>
      intro a ha
      have ha2 : 0 < a/2 := by linarith
      have hfN : Continuous ((f : F → F)^[N]) := hf.iterate _
      have hCN : IsCompact (((f : F → F)^[N]) '' C) :=
        hC.image hfN
      obtain ⟨rho, hrho, hclose⟩ :=
        ShadowingFoundation.compact_uniform_close (F:=F) (G:=F)
          hCN f hf (a/2) ha2
      obtain ⟨e0, he0, hold⟩ := ih rho hrho
      let e : ℝ := min e0 (a/2)
      have he : 0 < e := lt_min he0 ha2
      refine ⟨e, he, ?_⟩
      intro z hz u hu hsteps
      have hfirst : ‖u N - (f^[N]) z‖ < rho := by
        apply hold z hz u hu
        intro i hi
        exact lt_of_lt_of_le (hsteps i (Nat.lt_trans hi (Nat.lt_succ_self _)))
          (min_le_left _ _)
      have hzN : (f^[N]) z ∈ (f^[N]) '' C := ⟨z, hz, rfl⟩
      have hfNclose : ‖f (u N) - f ((f^[N]) z)‖ < a/2 :=
        hclose _ hzN _ hfirst
      have hlast' : ‖u (N+1) - f (u N)‖ < e :=
        hsteps N (Nat.lt_succ_self _)
      have hlast : ‖u (N+1) - f (u N)‖ < a/2 :=
        lt_of_lt_of_le hlast' (min_le_right _ _)
      calc
        ‖u (N+1) - (f^[N+1]) z‖ =
            ‖(u (N+1) - f (u N)) + (f (u N) - f ((f^[N]) z))‖ := by
              rw [Function.iterate_succ_apply']
              congr 1
              abel
        _ ≤ ‖u (N+1) - f (u N)‖ + ‖f (u N) - f ((f^[N]) z)‖ :=
              norm_add_le _ _
        _ < a := by linarith

/-- A handy compact thickening in a proper normed group. We use the image of
`C × closedBall 0 R` rather than neighborhoods in order to avoid any closed
neighborhood API. -/
lemma isCompact_thickening [ProperSpace F] {C : Set F} (hC : IsCompact C)
    (R : ℝ) :
    IsCompact ((fun t : F × F => t.1 + t.2) ''
      (C ×ˢ Metric.closedBall (0:F) R)) := by
  have hpair : IsCompact (C ×ˢ Metric.closedBall (0:F) R) :=
    hC.prod (ProperSpace.isCompact_closedBall (0:F) R)
  exact hpair.image (continuous_fst.add continuous_snd)

lemma mem_thickening_of {C : Set F} {R : ℝ}
    {x z : F} (hz : z ∈ C) (h : ‖x-z‖ < R) :
    x ∈ ((fun t : F × F => t.1 + t.2) ''
      (C ×ˢ Metric.closedBall (0:F) R)) := by
  refine ⟨(z, x-z), ?_, ?_⟩
  · refine ⟨hz, ?_⟩
    -- closed ball uses distance to zero
    have hh : ‖x-z‖ ≤ R := le_of_lt h
    simpa [Metric.mem_closedBall, dist_zero_right] using hh
  · simp

/-- Uniform version for all the intermediate times of a fixed block.  The
compact set is only a set of *starts*. -/
lemma finite_pseudo_all (f : F → F) (hf : Continuous f) (C : Set F)
    (hC : IsCompact C) :
    ∀ (N : ℕ) (a : ℝ), 0 < a →
      ∃ e : ℝ, 0 < e ∧
        ∀ z : F, z ∈ C → ∀ u : ℕ → F,
          u 0 = z →
          (∀ j, ‖u (j+1) - f (u j)‖ < e) →
          ∀ i ≤ N, ‖u i - (f^[i]) z‖ < a := by
  intro N
  induction N with
  | zero =>
      intro a ha
      exact ⟨1, by norm_num, fun z hz u hu hstep i hi => by
        have iz : i = 0 := Nat.eq_zero_of_le_zero hi
        subst i
        simpa [hu] using ha⟩
  | succ N ih =>
      intro a ha
      have ha2 : 0 < a/2 := by linarith
      have hfN : Continuous ((f : F → F)^[N]) := hf.iterate _
      have hCN : IsCompact (((f : F → F)^[N]) '' C) := hC.image hfN
      obtain ⟨rho0, hr0, hnear⟩ :=
        ShadowingFoundation.compact_uniform_close (F:=F) (G:=F)
          hCN f hf (a/2) ha2
      let rho : ℝ := min rho0 a
      have hr : 0 < rho := lt_min hr0 ha
      obtain ⟨e0, he0, hprev⟩ := ih rho hr
      let e : ℝ := min e0 (a/2)
      have he : 0 < e := lt_min he0 ha2
      refine ⟨e, he, ?_⟩
      intro z hz u hu hstep i hi
      by_cases hiN : i ≤ N
      · have hp : ∀ j, ‖u (j+1)-f (u j)‖ < e0 := fun j =>
          lt_of_lt_of_le (hstep j) (min_le_left _ _)
        exact lt_of_lt_of_le (hprev z hz u hu hp i hiN) (min_le_right _ _)
      · have ie : i = N+1 := by omega
        subst i
        have hp : ∀ j, ‖u (j+1)-f (u j)‖ < e0 := fun j =>
          lt_of_lt_of_le (hstep j) (min_le_left _ _)
        have hN : ‖u N - (f^[N]) z‖ < rho0 :=
          lt_of_lt_of_le (hprev z hz u hu hp N (le_rfl)) (min_le_left _ _)
        have hzN : (f^[N]) z ∈ (f^[N]) '' C := ⟨z, hz, rfl⟩
        have hclose : ‖f (u N) - f ((f^[N]) z)‖ < a/2 :=
          hnear _ hzN _ hN
        have hlast : ‖u (N+1) - f (u N)‖ < a/2 :=
          lt_of_lt_of_le (hstep N) (min_le_right _ _)
        calc
          ‖u (N+1) - (f^[N+1]) z‖ =
              ‖(u (N+1)-f (u N)) + (f (u N)-f ((f^[N]) z))‖ := by
                rw [Function.iterate_succ_apply']
                congr 1
                abel
          _ ≤ ‖u (N+1)-f (u N)‖ + ‖f (u N)-f ((f^[N]) z)‖ := norm_add_le _ _
          _ < a := by linarith

/-- Finite uniform continuity for all iterates up to one fixed length. -/
lemma finite_iterate_close_all (f : F → F) (hf : Continuous f)
    (C : Set F) (hC : IsCompact C) :
    ∀ (N : ℕ) (a : ℝ), 0 < a →
      ∃ s : ℝ, 0 < s ∧ ∀ z : F, z ∈ C → ∀ t : F,
        ‖t-z‖ < s → ∀ i ≤ N, ‖((f^[i]) t) - (f^[i]) z‖ < a := by
  intro N
  induction N with
  | zero =>
      intro a ha
      exact ⟨a, ha, fun z hz t ht i hi => by
        have iz : i = 0 := Nat.eq_zero_of_le_zero hi
        subst i
        simpa using ht⟩
  | succ N ih =>
      intro a ha
      obtain ⟨s0, hs0, hprev⟩ := ih a ha
      have hnextcont : Continuous ((f : F → F)^[N+1]) := hf.iterate _
      obtain ⟨s1, hs1, hnext⟩ :=
        ShadowingFoundation.compact_uniform_close (F:=F) (G:=F)
          hC ((f : F → F)^[N+1]) hnextcont a ha
      refine ⟨min s0 s1, lt_min hs0 hs1, ?_⟩
      intro z hz t hzt i hi
      by_cases hle : i ≤ N
      · exact hprev z hz t (lt_of_lt_of_le hzt (min_le_left _ _)) i hle
      · have ie : i = N+1 := by omega
        subst i
        exact hnext z hz t (lt_of_lt_of_le hzt (min_le_right _ _))

end ShadowingPerturb

end
-- END INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Step.lean

-- BEGIN INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Fixed.lean
section
open scoped Topology
namespace ShadowingPerturb
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local notation "Seq" => BoundedContinuousFunction ℕ F

/-- Banach fixed point with the a-priori bound that is useful in the clipped
shadowing argument.  Keeping the equation `e = G (W e)` (not merely the
recurrence it implies) retains this estimate. -/
theorem exists_fixed_of_lipschitz
    (G : Seq → Seq) (M : ℝ) (hM : 0 ≤ M)
    (hGb : ∀ w, ‖G w‖ ≤ M * ‖w‖)
    (hGlip : ∀ u v, ‖G u - G v‖ ≤ M * ‖u-v‖)
    (W : Seq → Seq) (k : ℝ) (hk : 0 ≤ k)
    (hW : ∀ u v, ‖W u - W v‖ ≤ k * ‖u-v‖)
    (hsmall : M*k < 1) :
    ∃ e : Seq, e = G (W e) ∧
      ‖e‖ ≤ (M/(1-M*k))*‖W (0 : Seq)‖ := by
  classical
  let Q : NNReal := ⟨M*k, mul_nonneg hM hk⟩
  have hQ : Q < 1 := by change M*k < (1:ℝ); exact hsmall
  let f : Seq → Seq := fun u => G (W u)
  have hLip : LipschitzWith Q f := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    -- exactly as for the Green fixed point, unfold the metric of bounded
    -- functions to a norm of a difference.
    simp only [dist_eq_norm_sub]
    change ‖G (W u) - G (W v)‖ ≤ (M*k) * ‖u-v‖
    calc
      ‖G (W u) - G (W v)‖ ≤ M * ‖W u-W v‖ := hGlip _ _
      _ ≤ M * (k*‖u-v‖) := mul_le_mul_of_nonneg_left (hW _ _) hM
      _ = (M*k)*‖u-v‖ := by ring
  have hcontr : ContractingWith Q f := ⟨hQ, hLip⟩
  let e : Seq := ContractingWith.fixedPoint f hcontr
  have he : e = G (W e) := by
    have hh := hcontr.fixedPoint_isFixedPt
    exact (show f e = e from hh).symm
  refine ⟨e, he, ?_⟩
  have h0 : ‖(0 : Seq)‖ = 0 := norm_zero
  have hdiff : ‖W e - W (0 : Seq)‖ ≤ k * ‖e‖ := by
    have ht := hW e (0 : Seq)
    simpa using ht
  have hWe : ‖W e‖ ≤ k * ‖e‖ + ‖W (0 : Seq)‖ := by
    calc
      ‖W e‖ = ‖(W e - W (0 : Seq)) + W (0 : Seq)‖ := by
        congr 1
        abel
      _ ≤ ‖W e - W (0 : Seq)‖ + ‖W (0 : Seq)‖ := norm_add_le _ _
      _ ≤ k*‖e‖ + ‖W (0 : Seq)‖ := by linarith
  have heb : ‖e‖ ≤ M * ‖W e‖ := by
    calc
      ‖e‖ = ‖G (W e)‖ := congrArg norm he
      _ ≤ M * ‖W e‖ := hGb _
  have key : (1-M*k)*‖e‖ ≤ M * ‖W (0 : Seq)‖ := by
    have hh : M * ‖W e‖ ≤ M * (k*‖e‖ + ‖W (0 : Seq)‖) :=
      mul_le_mul_of_nonneg_left hWe hM
    have total := heb.trans hh
    nlinarith
  have hp : 0 < 1-M*k := sub_pos.mpr hsmall
  have h' : ‖e‖ ≤ (M * ‖W (0 : Seq)‖) / (1-M*k) :=
    (le_div_iff₀ hp).2 (by
      simpa [mul_comm] using key)
  calc
    ‖e‖ ≤ (M * ‖W (0 : Seq)‖) / (1-M*k) := h'
    _ = (M/(1-M*k))*‖W (0 : Seq)‖ := by ring
end ShadowingPerturb

end
-- END INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Fixed.lean

-- BEGIN INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Transport.lean
section

open scoped Topology
open Function

/-! A small transport lemma for the Green operator.  When the range at the
right hand endpoint of a step is only *near* the next projection, first
change the target projection by the elementary intertwiner `changeProj`.
This isolates the only loss of constants in the broken-orbit argument. -/
namespace ShadowingPerturb

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- Transport a hyperbolic one-step cocycle across a changing projection.
Here `p n` is the projection at the chosen centres and `r n` is the
projection at the *image* of centre `n`.  The original derivative `L n`
preserves `p n` and `r n`; similarly `B n` goes backwards from `r n`.
If `r n` and `p (n+1)` are close, composition with
`changeProj (p (n+1)) (r n)` gives an exactly invariant cocycle.

Besides the Green solver we retain the pointwise closeness of its new linear
part.  This is the term moved to the nonlinear side later. -/
theorem exists_green_solver_transport
    (p r L B : ℕ → F →L[ℝ] F)
    (A c e θ c' : ℝ)
    (hA : 0 ≤ A) (hc : 0 ≤ c)
    (he : 0 ≤ e)
    (hθdef : θ = e * (2*A+1)) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hc'0 : 0 ≤ c') (hc'1 : c' < 1)
    (hplus : (1+θ)*c ≤ c')
    (hminus : (1/(1-θ))*c ≤ c')
    (hp_bound : ∀ n (v : F), ‖p n v‖ ≤ A * ‖v‖)
    (hq_bound : ∀ n (v : F), ‖v - p n v‖ ≤ A * ‖v‖)
    (hr_bound : ∀ n (v : F), ‖r n v‖ ≤ A * ‖v‖)
    (hpp : ∀ n (v : F), p n (p n v) = p n v)
    (hrr : ∀ n (v : F), r n (r n v) = r n v)
    (hclose : ∀ n (v : F), ‖p (n+1) v - r n v‖ ≤ e * ‖v‖)
    (hstable : ∀ n (v : F), p n v = v →
        r n (L n v) = L n v ∧ ‖L n v‖ ≤ c * ‖v‖)
    (hLunstable : ∀ n (v : F), p n v = 0 → r n (L n v) = 0)
    (hBunstable : ∀ n (v : F), r n v = 0 →
        p n (B n v) = 0 ∧ ‖B n v‖ ≤ c * ‖v‖)
    (hleft : ∀ n (v : F), r n v = 0 → L n (B n v) = v)
    (hright : ∀ n (v : F), p n v = 0 → B n (L n v) = v) :
    ∃ Lt : ℕ → F →L[ℝ] F,
      (∀ n (v : F), ‖Lt n v - L n v‖ ≤ θ * ‖L n v‖) ∧
      ∃ G : (BoundedContinuousFunction ℕ F) →
            (BoundedContinuousFunction ℕ F),
        (∀ w n, G w (n+1) - Lt n (G w n) = w n) ∧
        (∀ w, p 0 (G w 0) = 0) ∧
        (∀ w, ‖G w‖ ≤ 2 * (A * ‖w‖ / (1-c'))) ∧
        (∀ u v, ‖G u - G v‖ ≤ 2 * (A * ‖u-v‖ / (1-c'))) := by
  classical
  -- The bridge at edge `n`.
  let J : ℕ → F →L[ℝ] F := fun n => changeProj (p (n+1)) (r n)
  have hJsmall (n : ℕ) (x : F) : ‖J n x - x‖ ≤ θ * ‖x‖ := by
    -- the lemma is phrased in the other orientation; reverse the norm in
    -- `hclose` once.
    have hc0 : ∀ y : F, ‖p (n+1) y - r n y‖ ≤ e * ‖y‖ := fun y => hclose n y
    -- `r` is idempotent and has the `A` bound.
    simpa [J, hθdef] using
      (changeProj_sub_id_bound (p := p (n+1)) (r := r n)
        e A (hrr n) hc0 (hr_bound n) he hA x)
  -- It is an isomorphism since it is uniformly within `θ < 1` of the
  -- identity.  We only need the pointwise inverse equations and the two
  -- elementary bounds, so choose it without installing equivalence data.
  have hJinv (n : ℕ) : ∃ I : F →L[ℝ] F,
        (∀ x, J n (I x) = x) ∧ (∀ x, I (J n x) = x) ∧
        (∀ x, ‖I x‖ ≤ (1/(1-θ))*‖x‖) ∧
        (∀ x, ‖J n x‖ ≤ (1+θ)*‖x‖) := by
    exact inverse_of_almost_id (J n) θ hθ0 hθ1 (hJsmall n)
  choose I hJI hIJ hIbd hJbd using hJinv
  -- `J` sends the old range/kernel to the new ones.
  have hJrange (n : ℕ) (x : F) : J n (r n x) = p (n+1) (J n x) := by
    exact changeProj_range (p (n+1)) (r n) (hpp (n+1)) (hrr n) x
  have hJker (n : ℕ) {x : F} (hx : r n x = 0) :
      p (n+1) (J n x) = 0 := by
    exact changeProj_kernel (p (n+1)) (r n) (hpp (n+1)) (hrr n) hx
  have hJran' (n : ℕ) {x : F} (hx : r n x = x) :
      p (n+1) (J n x) = J n x := by
    -- replace `r n x` in the intertwining identity.
    have hh := hJrange n x
    simpa [hx] using hh.symm
  -- Conversely the inverse sends the new subspaces into the old ones; the
  -- two inverse equations let us cancel `J` without a separate injectivity
  -- instance.
  have hIran (n : ℕ) {x : F} (hx : p (n+1) x = x) :
      r n (I n x) = I n x := by
    have heqJ : J n (r n (I n x)) = J n (I n x) := by
      calc
        J n (r n (I n x)) = p (n+1) (J n (I n x)) := hJrange n (I n x)
        _ = p (n+1) x := by rw [hJI n x]
        _ = x := hx
        _ = J n (I n x) := (hJI n x).symm
    have heqI := congrArg (fun t : F => I n t) heqJ
    simpa only [hIJ n (r n (I n x)), hIJ n (I n x)] using heqI
  have hIker (n : ℕ) {x : F} (hx : p (n+1) x = 0) :
      r n (I n x) = 0 := by
    have hzero : J n (r n (I n x)) = J n (0 : F) := by
      calc
        J n (r n (I n x)) = p (n+1) (J n (I n x)) := hJrange n (I n x)
        _ = p (n+1) x := by rw [hJI n x]
        _ = 0 := hx
        _ = J n (0 : F) := by simp
    have hcancel := congrArg (fun t : F => I n t) hzero
    simpa only [hIJ n (r n (I n x)), hIJ n 0, map_zero] using hcancel
  let Lt : ℕ → F →L[ℝ] F := fun n => (J n).comp (L n)
  let Bt : ℕ → F →L[ℝ] F := fun n => (B n).comp (I n)
  have hLtclose (n : ℕ) (v : F) :
      ‖Lt n v - L n v‖ ≤ θ * ‖L n v‖ := by
    exact hJsmall n (L n v)
  refine ⟨Lt, hLtclose, ?_⟩
  -- Verify the four exact-invariance hypotheses of the Green operator for
  -- the transported cocycle.
  have hst' (n : ℕ) (v : F) (hv : p n v = v) :
      p (n+1) (Lt n v) = Lt n v ∧ ‖Lt n v‖ ≤ c' * ‖v‖ := by
    have hs := hstable n v hv
    constructor
    · change p (n+1) (J n (L n v)) = J n (L n v)
      exact hJran' n hs.1
    · change ‖J n (L n v)‖ ≤ _
      calc
        ‖J n (L n v)‖ ≤ (1+θ) * ‖L n v‖ := hJbd n _
        _ ≤ (1+θ) * (c * ‖v‖) :=
          mul_le_mul_of_nonneg_left hs.2 (by linarith [hθ0])
        _ = ((1+θ)*c) * ‖v‖ := by ring
        _ ≤ c' * ‖v‖ :=
          mul_le_mul_of_nonneg_right hplus (norm_nonneg _)
  have hLu' (n : ℕ) (v : F) (hv : p n v = 0) :
      p (n+1) (Lt n v) = 0 := by
    change p (n+1) (J n (L n v)) = 0
    exact hJker n (hLunstable n v hv)
  have hBu' (n : ℕ) (v : F) (hv : p (n+1) v = 0) :
      p n (Bt n v) = 0 ∧ ‖Bt n v‖ ≤ c' * ‖v‖ := by
    have hk : r n (I n v) = 0 := hIker n hv
    have hu := hBunstable n (I n v) hk
    constructor
    · exact hu.1
    · change ‖B n (I n v)‖ ≤ _
      calc
        ‖B n (I n v)‖ ≤ c * ‖I n v‖ := hu.2
        _ ≤ c * ((1/(1-θ))* ‖v‖) :=
          mul_le_mul_of_nonneg_left (hIbd n v) hc
        _ = ((1/(1-θ))*c) * ‖v‖ := by ring
        _ ≤ c' * ‖v‖ :=
          mul_le_mul_of_nonneg_right hminus (norm_nonneg _)
  have hleft' (n : ℕ) (v : F) (hv : p (n+1) v = 0) :
      Lt n (Bt n v) = v := by
    change J n (L n (B n (I n v))) = v
    rw [hleft n (I n v) (hIker n hv)]
    exact hJI n v
  have hright' (n : ℕ) (v : F) (hv : p n v = 0) :
      Bt n (Lt n v) = v := by
    change B n (I n (J n (L n v))) = v
    rw [hIJ n (L n v)]
    exact hright n v hv
  exact ShadowingGreen.exists_green_solver
    (p := p) (L := Lt) (B := Bt)
    (A := A) (c := c') hA hc'0 hc'1 hp_bound hq_bound hpp
    hst' hLu' hBu' hleft' hright'

end ShadowingPerturb

end
-- END INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Transport.lean

-- BEGIN INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Nonlinear.lean
section

open scoped Topology
namespace ShadowingPerturb
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "Seq" => BoundedContinuousFunction ℕ F

/-- Package a clipped pointwise remainder as a map on bounded sequences.  This
little lemma is useful in the last analytic step of shadowing.  The remainders
need only be Lipschitz on the fixed ball; `clip` globalizes them.  Notice the
factor two, the price paid for working in an arbitrary norm rather than using
Hilbert projections onto balls. -/
theorem make_clipped_remainder
    (s b η l : ℝ) (hs : 0 < s) (hb : 0 ≤ b) (hη : 0 ≤ η) (hl : 0 ≤ l)
    (d : ℕ → F) (rem : ℕ → F → F) (Q : ℕ → F →L[ℝ] F)
    (hd : ∀ n, ‖d n‖ ≤ b)
    (hrem0 : ∀ n, rem n 0 = 0)
    (hremLip : ∀ n (u v : F), ‖u‖ ≤ s → ‖v‖ ≤ s →
      ‖rem n u - rem n v‖ ≤ η * ‖u-v‖)
    (hQ : ∀ n (u : F), ‖Q n u‖ ≤ l * ‖u‖) :
    ∃ W : Seq → Seq,
      (∀ e n, W e n = d n + rem n (clip s (e n)) + Q n (clip s (e n))) ∧
      (‖W (0 : Seq)‖ ≤ b) ∧
      (∀ u v, ‖W u - W v‖ ≤ (2*(η+l)) * ‖u-v‖) := by
  classical
  have hs0 : 0 ≤ s := le_of_lt hs
  have hsum0 : 0 ≤ b + (η+l)*s := by positivity
  let val : Seq → ℕ → F := fun e n =>
    d n + rem n (clip s (e n)) + Q n (clip s (e n))
  have hvalbd (e : Seq) (n : ℕ) : ‖val e n‖ ≤ b + (η+l)*s := by
    have hc : ‖clip s (e n)‖ ≤ s := clip_norm_le s hs0 _
    have hc0 : ‖(0:F)‖ ≤ s := by simpa using hs0
    have hr : ‖rem n (clip s (e n))‖ ≤ η * ‖clip s (e n)‖ := by
      have hh := hremLip n (clip s (e n)) 0 hc hc0
      simpa [hrem0] using hh
    have hq := hQ n (clip s (e n))
    calc
      ‖val e n‖ ≤ ‖d n‖ + ‖rem n (clip s (e n))‖ + ‖Q n (clip s (e n))‖ := by
        dsimp [val]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_rfl))
      _ ≤ b + (η * ‖clip s (e n)‖) + (l * ‖clip s (e n)‖) :=
        add_le_add (add_le_add (hd n) hr) hq
      _ ≤ b + (η*s) + (l*s) := by
        have h1 := mul_le_mul_of_nonneg_left hc hη
        have h2 := mul_le_mul_of_nonneg_left hc hl
        linarith
      _ = b + (η+l)*s := by ring
  let W : Seq → Seq := fun e =>
    BoundedContinuousFunction.ofNormedAddCommGroup (val e)
      continuous_of_discreteTopology _ (hvalbd e)
  have hWval (e : Seq) (n : ℕ) : W e n = val e n := rfl
  refine ⟨W, ?_, ?_, ?_⟩
  · intro e n; rfl
  · -- at zero the clipped variables vanish
    apply (BoundedContinuousFunction.norm_le hb).2
    intro n
    change ‖d n + rem n (clip s ((0:Seq) n)) + Q n (clip s ((0:Seq) n))‖ ≤ b
    have hcz : clip s (0:F) = 0 := clip_of_norm_le (by simpa using hs0)
    simpa [hcz, hrem0] using (hd n)
  · intro a c
    have hK0 : 0 ≤ 2*(η+l) := by positivity
    apply (BoundedContinuousFunction.norm_le
      (mul_nonneg hK0 (norm_nonneg (a-c)))).2
    intro n
    -- a difference of values at this coordinate.  The error `d` cancels.
    let x : F := clip s (a n)
    let y : F := clip s (c n)
    have hx : ‖x‖ ≤ s := clip_norm_le s hs0 _
    have hy : ‖y‖ ≤ s := clip_norm_le s hs0 _
    have hxy : ‖x-y‖ ≤ 2 * ‖a n - c n‖ :=
      clip_sub_le s hs (a n) (c n)
    have hcoord : ‖a n - c n‖ ≤ ‖a-c‖ := by
      have hh := BoundedContinuousFunction.norm_coe_le_norm (a-c) n
      simpa using hh
    change ‖(W a - W c) n‖ ≤ _
    change ‖(d n + rem n x + Q n x) - (d n + rem n y + Q n y)‖ ≤ _
    have heq : (d n + rem n x + Q n x) -
            (d n + rem n y + Q n y)
          = (rem n x - rem n y) + Q n (x-y) := by
      rw [map_sub]
      abel
    rw [heq]
    have hr := hremLip n x y hx hy
    have hq := hQ n (x-y)
    calc
      ‖(rem n x - rem n y) + Q n (x-y)‖
          ≤ ‖rem n x - rem n y‖ + ‖Q n (x-y)‖ := norm_add_le _ _
      _ ≤ η*‖x-y‖ + l*‖x-y‖ := add_le_add hr hq
      _ = (η+l)*‖x-y‖ := by ring
      _ ≤ (η+l) * (2*‖a n - c n‖) :=
        mul_le_mul_of_nonneg_left hxy (by linarith)
      _ ≤ (η+l) * (2*‖a-c‖) := by
        have := mul_le_mul_of_nonneg_left hcoord (by positivity : 0 ≤ 2*(η+l))
        -- same factors in a different order
        nlinarith
      _ = (2*(η+l))*‖a-c‖ := by ring
end ShadowingPerturb

end
-- END INLINED FILE: Mathlib/Support/anosov_bowen_shadowing_b308abc37b/Nonlinear.lean

-- BEGIN INLINED MAIN PRELUDE
set_option maxHeartbeats 4000000

open LeanEval.Dynamics.HyperbolicShadowingProblem
open scoped Topology

variable {d : ℕ}
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem hyperbolic_has_shadowing (T : E d ≃ₜ E d) (K : Set (E d))
    (_hKc : IsCompact K) (_hK : IsHyperbolic T K) :
    HasShadowing (T : E d → E d) K :=
/-ResultProofBegin-/by
  classical
  -- The zero dimensional and empty cases are immediate; they also let us isolate the
  -- genuinely hyperbolic part of the assertion.
  by_cases hdim : d = 0
  · subst d
    refine ⟨Set.univ, isOpen_univ, (by intro z hz; trivial), ?_⟩
    intro δ hδ
    refine ⟨1, by norm_num, ?_⟩
    intro x hx hp
    refine ⟨x 0, ?_⟩
    intro n
    have heq : x n = ((T : E 0 → E 0)^[n]) (x 0) := Subsingleton.elim _ _
    rw [heq, sub_self, norm_zero]
    exact hδ
  · by_cases he : K = (∅ : Set (E d))
    · subst K
      refine ⟨∅, isOpen_empty, by intro z hz; exact False.elim hz, ?_⟩
      intro δ hδ
      refine ⟨1, by norm_num, ?_⟩
      intro x hx hp
      exact False.elim ((hx 0))
    ·
      -- Some elementary consequences of a hyperbolic structure, in particular that the
      -- invariant set is invariant under both iterates.  They are useful when applying
      -- the estimates at different base points.
      rcases _hK with ⟨H⟩
      have hf : Differentiable ℝ (T : E d → E d) :=
        H.contDiff_fwd.differentiable (by norm_num)
      have hg : Differentiable ℝ (T.symm : E d → E d) :=
        H.contDiff_bwd.differentiable (by norm_num)
      have him (x : E d) (hx : x ∈ K) : T x ∈ K := by
        rw [← H.invariant]
        exact ⟨x, hx, rfl⟩
      have hpre (x : E d) (hx : x ∈ K) : T.symm x ∈ K := by
        have hx' : x ∈ (T : E d → E d) '' K := by
          rw [H.invariant]
          exact hx
        obtain ⟨z, hz, hzx⟩ := hx'
        -- apply the inverse map to `T z = x`
        have h' := congrArg (fun w : E d => T.symm w) hzx
        have zeq : z = T.symm x := by simpa using h'
        simpa [← zeq] using hz
      have hiter (x : E d) (hx : x ∈ K) :
          ∀ n : ℕ, ((T : E d → E d)^[n]) x ∈ K := by
        intro n
        induction n with
        | zero => simpa using hx
        | succ n ih =>
            -- apply `T` to the previous iterate
            rw [Function.iterate_succ_apply']
            exact him _ ih
      have hiterpre (x : E d) (hx : x ∈ K) :
          ∀ n : ℕ, ((T.symm : E d → E d)^[n]) x ∈ K := by
        intro n
        induction n with
        | zero => simpa using hx
        | succ n ih =>
            rw [Function.iterate_succ_apply']
            exact hpre _ ih
      have hsiter (n : ℕ) (x : E d) (hx : x ∈ K) :
          (H.stable x).map
              (fderiv ℝ ((T : E d → E d)^[n]) x : E d →ₗ[ℝ] E d) =
            H.stable (((T : E d → E d)^[n]) x) := by
        exact ShadowingFoundation.map_fderiv_iterate hf
          (fun _ hx => him _ hx) H.stable
          (fun _ hx => H.stable_invariant _ hx) n hx
      have hupiter (n : ℕ) (x : E d) (hx : x ∈ K) :
          (H.unstable x).map
              (fderiv ℝ ((T : E d → E d)^[n]) x : E d →ₗ[ℝ] E d) =
            H.unstable (((T : E d → E d)^[n]) x) := by
        exact ShadowingFoundation.map_fderiv_iterate hf
          (fun _ hx => him _ hx) H.unstable
          (fun _ hx => H.unstable_invariant _ hx) n hx
      -- In particular the unstable spaces are taken backwards by the inverse
      -- derivative as well.  This follows from the chain rule for a smooth
      -- homeomorphism; it is often implicit in the definition.
      have hupre (x : E d) (hx : x ∈ K) :
          (H.unstable x).map
              (fderiv ℝ (T.symm : E d → E d) x : E d →ₗ[ℝ] E d) =
            H.unstable (T.symm x) := by
        let A : E d →L[ℝ] E d := fderiv ℝ (T : E d → E d) (T.symm x)
        let B : E d →L[ℝ] E d := fderiv ℝ (T.symm : E d → E d) x
        have hxpre : T.symm x ∈ K := hpre x hx
        have hab : (H.unstable (T.symm x)).map (A : E d →ₗ[ℝ] E d) =
              H.unstable x := by
          simpa [A] using H.unstable_invariant (T.symm x) hxpre
        change (H.unstable x).map (B : E d →ₗ[ℝ] E d) = _
        -- eliminate both maps by the bijectivity of the derivatives
        apply le_antisymm
        · intro v hv
          rcases (Submodule.mem_map.mp hv) with ⟨u, hu, huv⟩
          have hu' : u ∈ (H.unstable (T.symm x)).map
              (A : E d →ₗ[ℝ] E d) := by simpa [hab] using hu
          rcases (Submodule.mem_map.mp hu') with ⟨w, hw, hwu⟩
          have hcancel : B (A w) = w := by
            simpa [A, B] using
              (ShadowingFoundation.fderiv_symm_apply_fderiv
                (f := T) hf hg (T.symm x) w)
          have hvw : v = w := by
            calc
              v = B u := by symm; exact huv
              _ = B (A w) := (congrArg B hwu).symm
              _ = w := hcancel
          simpa [hvw] using hw
        · intro w hw
          have haw : A w ∈ H.unstable x := by
            rw [← hab]
            exact Submodule.mem_map_of_mem hw
          -- it is the image of `A w`; inverse differentiation recovers `w`.
          apply Submodule.mem_map.mpr
          refine ⟨A w, haw, ?_⟩
          simpa [A, B] using
            (ShadowingFoundation.fderiv_symm_apply_fderiv
              (f := T) hf hg (T.symm x) w)
      have hupreiter (n : ℕ) (x : E d) (hx : x ∈ K) :
          (H.unstable x).map
              (fderiv ℝ ((T.symm : E d → E d)^[n]) x : E d →ₗ[ℝ] E d) =
            H.unstable (((T.symm : E d → E d)^[n]) x) := by
        exact ShadowingFoundation.map_fderiv_iterate hg
          (fun _ hx => hpre _ hx) H.unstable (fun _ hx => hupre _ hx) n hx
      have hspre (x : E d) (hx : x ∈ K) :
          (H.stable x).map
              (fderiv ℝ (T.symm : E d → E d) x : E d →ₗ[ℝ] E d) =
            H.stable (T.symm x) := by
        let A : E d →L[ℝ] E d := fderiv ℝ (T : E d → E d) (T.symm x)
        let B : E d →L[ℝ] E d := fderiv ℝ (T.symm : E d → E d) x
        have hxpre : T.symm x ∈ K := hpre x hx
        have hab : (H.stable (T.symm x)).map (A : E d →ₗ[ℝ] E d) =
              H.stable x := by
          simpa [A] using H.stable_invariant (T.symm x) hxpre
        change (H.stable x).map (B : E d →ₗ[ℝ] E d) = _
        apply le_antisymm
        · intro v hv
          rcases (Submodule.mem_map.mp hv) with ⟨u, hu, huv⟩
          have hu' : u ∈ (H.stable (T.symm x)).map
              (A : E d →ₗ[ℝ] E d) := by simpa [hab] using hu
          rcases (Submodule.mem_map.mp hu') with ⟨w, hw, hwu⟩
          have hcancel : B (A w) = w := by
            simpa [A, B] using
              (ShadowingFoundation.fderiv_symm_apply_fderiv
                (f := T) hf hg (T.symm x) w)
          have hvw : v = w := by
            calc
              v = B u := by symm; exact huv
              _ = B (A w) := (congrArg B hwu).symm
              _ = w := hcancel
          simpa [hvw] using hw
        · intro w hw
          have haw : A w ∈ H.stable x := by
            rw [← hab]
            exact Submodule.mem_map_of_mem hw
          apply Submodule.mem_map.mpr
          refine ⟨A w, haw, ?_⟩
          simpa [A, B] using
            (ShadowingFoundation.fderiv_symm_apply_fderiv
              (f := T) hf hg (T.symm x) w)
      have hspreiter (n : ℕ) (x : E d) (hx : x ∈ K) :
          (H.stable x).map
              (fderiv ℝ ((T.symm : E d → E d)^[n]) x : E d →ₗ[ℝ] E d) =
            H.stable (((T.symm : E d → E d)^[n]) x) := by
        exact ShadowingFoundation.map_fderiv_iterate hg
          (fun _ hx => hpre _ hx) H.stable (fun _ hx => hspre _ hx) n hx
      have hs_lower (n : ℕ) (x : E d) (hx : x ∈ K)
          (v : E d) (hv : v ∈ H.stable x) :
          ‖v‖ ≤ H.const * H.rate ^ n *
            ‖fderiv ℝ ((T.symm : E d → E d)^[n]) x v‖ := by
        let w : E d := fderiv ℝ ((T.symm : E d → E d)^[n]) x v
        have hw : w ∈ H.stable (((T.symm : E d → E d)^[n]) x) := by
          rw [← hspreiter n x hx]
          exact Submodule.mem_map_of_mem hv
        have hb := H.contract_stable (((T.symm : E d → E d)^[n]) x)
          (hiterpre x hx n) w hw n
        have hc :
            fderiv ℝ ((T : E d → E d)^[n])
                (((T.symm : E d → E d)^[n]) x) w = v := by
          dsimp [w]
          exact ShadowingFoundation.fderiv_iter_apply_fderiv_symmIter
            (f := T) hf hg n x v
        simpa [w, hc] using hb
      -- A form of the expanding estimate which follows immediately from the
      -- contracting estimate for the inverse.  This lower bound is what is
      -- needed to distinguish the two summands without any angle assumption.
      have hu_lower (n : ℕ) (x : E d) (hx : x ∈ K)
          (v : E d) (hv : v ∈ H.unstable x) :
          ‖v‖ ≤ H.const * H.rate ^ n *
            ‖fderiv ℝ ((T : E d → E d)^[n]) x v‖ := by
        let w : E d := fderiv ℝ ((T : E d → E d)^[n]) x v
        have hw : w ∈ H.unstable (((T : E d → E d)^[n]) x) := by
          rw [← hupiter n x hx]
          exact Submodule.mem_map_of_mem hv
        have hb := H.contract_unstable (((T : E d → E d)^[n]) x)
          (hiter x hx n) w hw n
        have hc :
            fderiv ℝ ((T.symm : E d → E d)^[n])
                (((T : E d → E d)^[n]) x) w = v := by
          dsimp [w]
          exact ShadowingFoundation.fderiv_symmIter_apply_fderivIter
            (f := T) hf hg n x v
        simpa [w, hc] using hb
      -- Characterization at a base point which does not refer to the chosen
      -- complement: a vector on which all forward differentials stay bounded
      -- must belong to the stable summand.  Only the pointwise estimates are
      -- needed for this useful fact.
      have hstable_of_bounded (x : E d) (hx : x ∈ K)
          (v : E d)
          (hb : ∃ M : ℝ, ∀ n : ℕ,
            ‖fderiv ℝ ((T : E d → E d)^[n]) x v‖ ≤ M) :
          v ∈ H.stable x := by
        rcases hb with ⟨M, hM⟩
        rcases (Submodule.codisjoint_iff_exists_add_eq.mp
          (H.isCompl_stable_unstable x hx).codisjoint v) with
          ⟨s, u, hs, hu, hsu⟩
        have vsu : v = s + u := hsu.symm
        have ueq : u = v - s := by rw [vsu]; abel
        have hul (n : ℕ) :
            ‖fderiv ℝ ((T : E d → E d)^[n]) x u‖ ≤
              M + H.const * ‖s‖ := by
          let L : E d →L[ℝ] E d := fderiv ℝ ((T : E d → E d)^[n]) x
          have hsbd := H.contract_stable x hx s hs n
          have hp : H.rate ^ n ≤ (1 : ℝ) :=
            pow_le_one₀ (le_of_lt H.rate_pos) (le_of_lt H.rate_lt_one)
          have hce : H.const * H.rate ^ n * ‖s‖ ≤ H.const * ‖s‖ := by
            calc
              H.const * H.rate ^ n * ‖s‖ ≤ H.const * 1 * ‖s‖ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hp (le_of_lt H.const_pos))
                  (norm_nonneg _)
              _ = H.const * ‖s‖ := by ring
          calc
            ‖fderiv ℝ ((T : E d → E d)^[n]) x u‖ =
                ‖L v - L s‖ := by simp [L, ueq]
            _ ≤ ‖L v‖ + ‖L s‖ := norm_sub_le _ _
            _ ≤ M + (H.const * H.rate ^ n * ‖s‖) :=
              add_le_add (hM n) hsbd
            _ ≤ M + H.const * ‖s‖ := add_le_add_right hce M
        have hule (n : ℕ) :
            ‖u‖ ≤ H.const * H.rate ^ n * (M + H.const * ‖s‖) := by
          calc
            ‖u‖ ≤ H.const * H.rate ^ n *
                ‖fderiv ℝ ((T : E d → E d)^[n]) x u‖ :=
              hu_lower n x hx u hu
            _ ≤ H.const * H.rate ^ n * (M + H.const * ‖s‖) :=
              mul_le_mul_of_nonneg_left (hul n)
                (mul_nonneg (le_of_lt H.const_pos)
                  (pow_nonneg (le_of_lt H.rate_pos) n))
        have hun : ‖u‖ = (0 : ℝ) :=
          ShadowingFoundation.eq_zero_of_le_geom
            (le_of_lt H.rate_pos) H.rate_lt_one (norm_nonneg _) hule
        have uz : u = 0 := norm_eq_zero.mp hun
        simpa [vsu, uz] using hs
      have hstable_iff_bounded (x : E d) (hx : x ∈ K) (v : E d) :
          v ∈ H.stable x ↔
            ∃ M : ℝ, ∀ n : ℕ,
              ‖fderiv ℝ ((T : E d → E d)^[n]) x v‖ ≤ M := by
        constructor
        · intro hv
          refine ⟨H.const * ‖v‖, ?_⟩
          intro n
          refine (H.contract_stable x hx v hv n).trans ?_
          have hp : H.rate ^ n ≤ (1 : ℝ) :=
            pow_le_one₀ (le_of_lt H.rate_pos) (le_of_lt H.rate_lt_one)
          calc
            H.const * H.rate ^ n * ‖v‖ ≤ H.const * 1 * ‖v‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hp (le_of_lt H.const_pos))
                (norm_nonneg _)
            _ = H.const * ‖v‖ := by ring
        · exact hstable_of_bounded x hx v
      have hcontiter (n : ℕ) : ContDiff ℝ 1 ((T : E d → E d)^[n]) := by
        induction n with
        | zero => simpa using (contDiff_id : ContDiff ℝ (1 : WithTop ℕ∞) (id : E d → E d))
        | succ n ih =>
          rw [Function.iterate_succ']
          exact H.contDiff_fwd.comp ih
      -- Sequential closedness of the stable bundle on `K`.  The formulation by
      -- bounded orbits above avoids choosing projections.
      have hstable_limit (a b : ℕ → E d) (x v : E d)
          (haK : ∀ j, a j ∈ K)
          (hbS : ∀ j, b j ∈ H.stable (a j))
          (hax : Filter.Tendsto a Filter.atTop (nhds x))
          (hbv : Filter.Tendsto b Filter.atTop (nhds v))
          (hx : x ∈ K) : v ∈ H.stable x := by
        apply hstable_of_bounded x hx v
        refine ⟨H.const * ‖v‖, ?_⟩
        intro n
        have hfdcon : Continuous
            (fderiv ℝ ((T : E d → E d)^[n])) :=
          (hcontiter n).continuous_fderiv (by norm_num)
        have hfa : Filter.Tendsto
            (fun j => fderiv ℝ ((T : E d → E d)^[n]) (a j))
              Filter.atTop
              (nhds (fderiv ℝ ((T : E d → E d)^[n]) x)) :=
          (hfdcon.tendsto x).comp hax
        have hap : Filter.Tendsto
            (fun j => fderiv ℝ ((T : E d → E d)^[n]) (a j) (b j))
              Filter.atTop
              (nhds (fderiv ℝ ((T : E d → E d)^[n]) x v)) := by
          have hp := hfa.prodMk_nhds hbv
          have heval : Continuous
              (fun p : (E d →L[ℝ] E d) × E d => p.1 p.2) :=
            continuous_fst.clm_apply continuous_snd
          simpa [Function.comp_def] using (heval.tendsto _).comp hp
        have hleft : Filter.Tendsto
            (fun j => ‖fderiv ℝ ((T : E d → E d)^[n]) (a j) (b j)‖)
              Filter.atTop
              (nhds ‖fderiv ℝ ((T : E d → E d)^[n]) x v‖) := hap.norm
        have hbn : Filter.Tendsto (fun j => ‖b j‖)
              Filter.atTop (nhds ‖v‖) := hbv.norm
        have hright : Filter.Tendsto
            (fun j => H.const * H.rate ^ n * ‖b j‖)
              Filter.atTop (nhds (H.const * H.rate ^ n * ‖v‖)) :=
          hbn.const_mul (H.const * H.rate ^ n)
        have hineq :
            ‖fderiv ℝ ((T : E d → E d)^[n]) x v‖ ≤
              H.const * H.rate ^ n * ‖v‖ :=
          le_of_tendsto_of_tendsto hleft hright
            (Filter.Eventually.of_forall (fun j =>
              H.contract_stable (a j) (haK j) (b j) (hbS j) n))
        refine hineq.trans ?_
        have hp : H.rate ^ n ≤ (1 : ℝ) :=
          pow_le_one₀ (le_of_lt H.rate_pos) (le_of_lt H.rate_lt_one)
        calc
          H.const * H.rate ^ n * ‖v‖ ≤ H.const * 1 * ‖v‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hp (le_of_lt H.const_pos))
                (norm_nonneg _)
          _ = H.const * ‖v‖ := by ring
      have hunstable_of_bounded (x : E d) (hx : x ∈ K)
          (v : E d)
          (hb : ∃ M : ℝ, ∀ n : ℕ,
            ‖fderiv ℝ ((T.symm : E d → E d)^[n]) x v‖ ≤ M) :
          v ∈ H.unstable x := by
        rcases hb with ⟨M, hM⟩
        rcases (Submodule.codisjoint_iff_exists_add_eq.mp
          (H.isCompl_stable_unstable x hx).codisjoint v) with
          ⟨s, u, hs, hu, hsu⟩
        have vsu : v = s + u := hsu.symm
        have seq : s = v - u := by rw [vsu]; abel
        have hsl (n : ℕ) :
            ‖fderiv ℝ ((T.symm : E d → E d)^[n]) x s‖ ≤
              M + H.const * ‖u‖ := by
          let L : E d →L[ℝ] E d := fderiv ℝ ((T.symm : E d → E d)^[n]) x
          have hubd := H.contract_unstable x hx u hu n
          have hp : H.rate ^ n ≤ (1 : ℝ) :=
            pow_le_one₀ (le_of_lt H.rate_pos) (le_of_lt H.rate_lt_one)
          have hce : H.const * H.rate ^ n * ‖u‖ ≤ H.const * ‖u‖ := by
            calc
              H.const * H.rate ^ n * ‖u‖ ≤ H.const * 1 * ‖u‖ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hp (le_of_lt H.const_pos))
                  (norm_nonneg _)
              _ = H.const * ‖u‖ := by ring
          calc
            ‖fderiv ℝ ((T.symm : E d → E d)^[n]) x s‖ =
                ‖L v - L u‖ := by simp [L, seq]
            _ ≤ ‖L v‖ + ‖L u‖ := norm_sub_le _ _
            _ ≤ M + (H.const * H.rate ^ n * ‖u‖) :=
              add_le_add (hM n) hubd
            _ ≤ M + H.const * ‖u‖ := add_le_add_right hce M
        have hsle (n : ℕ) :
            ‖s‖ ≤ H.const * H.rate ^ n * (M + H.const * ‖u‖) := by
          calc
            ‖s‖ ≤ H.const * H.rate ^ n *
                ‖fderiv ℝ ((T.symm : E d → E d)^[n]) x s‖ :=
              hs_lower n x hx s hs
            _ ≤ H.const * H.rate ^ n * (M + H.const * ‖u‖) :=
              mul_le_mul_of_nonneg_left (hsl n)
                (mul_nonneg (le_of_lt H.const_pos)
                  (pow_nonneg (le_of_lt H.rate_pos) n))
        have hsn : ‖s‖ = (0 : ℝ) :=
          ShadowingFoundation.eq_zero_of_le_geom
            (le_of_lt H.rate_pos) H.rate_lt_one (norm_nonneg _) hsle
        have sz : s = 0 := norm_eq_zero.mp hsn
        simpa [vsu, sz] using hu
      have hunstable_iff_bounded (x : E d) (hx : x ∈ K) (v : E d) :
          v ∈ H.unstable x ↔
            ∃ M : ℝ, ∀ n : ℕ,
              ‖fderiv ℝ ((T.symm : E d → E d)^[n]) x v‖ ≤ M := by
        constructor
        · intro hv
          refine ⟨H.const * ‖v‖, ?_⟩
          intro n
          refine (H.contract_unstable x hx v hv n).trans ?_
          have hp : H.rate ^ n ≤ (1 : ℝ) :=
            pow_le_one₀ (le_of_lt H.rate_pos) (le_of_lt H.rate_lt_one)
          calc
            H.const * H.rate ^ n * ‖v‖ ≤ H.const * 1 * ‖v‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hp (le_of_lt H.const_pos))
                (norm_nonneg _)
            _ = H.const * ‖v‖ := by ring
        · exact hunstable_of_bounded x hx v
      have hcontpreiter (n : ℕ) :
          ContDiff ℝ 1 ((T.symm : E d → E d)^[n]) := by
        induction n with
        | zero => simpa using (contDiff_id : ContDiff ℝ (1 : WithTop ℕ∞) (id : E d → E d))
        | succ n ih =>
          rw [Function.iterate_succ']
          exact H.contDiff_bwd.comp ih
      have hunstable_limit (a b : ℕ → E d) (x v : E d)
          (haK : ∀ j, a j ∈ K)
          (hbS : ∀ j, b j ∈ H.unstable (a j))
          (hax : Filter.Tendsto a Filter.atTop (nhds x))
          (hbv : Filter.Tendsto b Filter.atTop (nhds v))
          (hx : x ∈ K) : v ∈ H.unstable x := by
        apply hunstable_of_bounded x hx v
        refine ⟨H.const * ‖v‖, ?_⟩
        intro n
        have hfdcon : Continuous
            (fderiv ℝ ((T.symm : E d → E d)^[n])) :=
          (hcontpreiter n).continuous_fderiv (by norm_num)
        have hfa : Filter.Tendsto
            (fun j => fderiv ℝ ((T.symm : E d → E d)^[n]) (a j))
              Filter.atTop
              (nhds (fderiv ℝ ((T.symm : E d → E d)^[n]) x)) :=
          (hfdcon.tendsto x).comp hax
        have hap : Filter.Tendsto
            (fun j => fderiv ℝ ((T.symm : E d → E d)^[n]) (a j) (b j))
              Filter.atTop
              (nhds (fderiv ℝ ((T.symm : E d → E d)^[n]) x v)) := by
          have hp := hfa.prodMk_nhds hbv
          have heval : Continuous
              (fun p : (E d →L[ℝ] E d) × E d => p.1 p.2) :=
            continuous_fst.clm_apply continuous_snd
          simpa [Function.comp_def] using (heval.tendsto _).comp hp
        have hleft : Filter.Tendsto
            (fun j => ‖fderiv ℝ ((T.symm : E d → E d)^[n]) (a j) (b j)‖)
              Filter.atTop
              (nhds ‖fderiv ℝ ((T.symm : E d → E d)^[n]) x v‖) := hap.norm
        have hbn : Filter.Tendsto (fun j => ‖b j‖)
              Filter.atTop (nhds ‖v‖) := hbv.norm
        have hright : Filter.Tendsto
            (fun j => H.const * H.rate ^ n * ‖b j‖)
              Filter.atTop (nhds (H.const * H.rate ^ n * ‖v‖)) :=
          hbn.const_mul (H.const * H.rate ^ n)
        have hineq :
            ‖fderiv ℝ ((T.symm : E d → E d)^[n]) x v‖ ≤
              H.const * H.rate ^ n * ‖v‖ :=
          le_of_tendsto_of_tendsto hleft hright
            (Filter.Eventually.of_forall (fun j =>
              H.contract_unstable (a j) (haK j) (b j) (hbS j) n))
        refine hineq.trans ?_
        have hp : H.rate ^ n ≤ (1 : ℝ) :=
          pow_le_one₀ (le_of_lt H.rate_pos) (le_of_lt H.rate_lt_one)
        calc
          H.const * H.rate ^ n * ‖v‖ ≤ H.const * 1 * ‖v‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hp (le_of_lt H.const_pos))
                (norm_nonneg _)
          _ = H.const * ‖v‖ := by ring
      -- The only vector with bounded differential behaviour in *both* time
      -- directions is zero; this is a convenient infinitesimal expansivity
      -- consequence of complementarity.
      have hzero_of_bibounded (x : E d) (hx : x ∈ K)
          (v : E d)
          (hfwd : ∃ M : ℝ, ∀ n : ℕ,
            ‖fderiv ℝ ((T : E d → E d)^[n]) x v‖ ≤ M)
          (hbwd : ∃ M : ℝ, ∀ n : ℕ,
            ‖fderiv ℝ ((T.symm : E d → E d)^[n]) x v‖ ≤ M) :
          v = 0 := by
        have hsv : v ∈ H.stable x := hstable_of_bounded x hx v hfwd
        have huv : v ∈ H.unstable x := hunstable_of_bounded x hx v hbwd
        have hi : v ∈ H.stable x ⊓ H.unstable x := by
          exact ⟨hsv, huv⟩
        have hz : v ∈ (⊥ : Submodule ℝ (E d)) :=
          (Disjoint.le_bot (H.isCompl_stable_unstable x hx).disjoint) hi
        exact (Submodule.mem_bot ℝ).mp hz
      -- The splitting on the compact set has a uniform angle.  We spell out
      -- the useful estimate (rather than using continuity of projections):
      -- it follows just from the two closed-graph statements above.
      have hangle0 : ∃ A : ℝ,
          ∀ (x : E d), x ∈ K →
          ∀ (s : E d), s ∈ H.stable x →
          ∀ (u : E d), u ∈ H.unstable x →
            ‖s‖ + ‖u‖ ≤ A * ‖s + u‖ := by
        by_contra! hbadall
        -- Choose a decomposition whose angle is worse than `n+1`.
        have hbad : ∀ n : ℕ, ∃ (x : E d), x ∈ K ∧
            ∃ (s : E d), s ∈ H.stable x ∧
            ∃ (u : E d), u ∈ H.unstable x ∧
              ( (n:ℝ) + 1) * ‖s + u‖ < ‖s‖ + ‖u‖ := by
          intro n
          obtain ⟨x, hx, s, hs, u, hu, hlt⟩ := hbadall ((n:ℝ) + 1)
          exact ⟨x, hx, s, hs, u, hu, hlt⟩
        choose a haK b hbS c hcS hbad' using hbad
        let l : ℕ → ℝ := fun n => ‖b n‖ + ‖c n‖
        have hlpos (n : ℕ) : 0 < l n := by
          have hn : 0 ≤ ((n:ℝ) + 1) * ‖b n + c n‖ :=
            mul_nonneg (by positivity) (norm_nonneg _)
          exact lt_of_le_of_lt hn (hbad' n)
        have hlne (n : ℕ) : l n ≠ 0 := ne_of_gt (hlpos n)
        -- normalize the two summands.  They then live in fixed compact unit balls.
        let b' : ℕ → E d := fun n => (l n)⁻¹ • b n
        let c' : ℕ → E d := fun n => (l n)⁻¹ • c n
        have hbmem (n : ℕ) : b' n ∈ H.stable (a n) := by
          exact (H.stable (a n)).smul_mem ((l n)⁻¹) (hbS n)
        have hcmem (n : ℕ) : c' n ∈ H.unstable (a n) := by
          exact (H.unstable (a n)).smul_mem ((l n)⁻¹) (hcS n)
        have hinvnorm (n : ℕ) : ‖(l n)⁻¹‖ = (l n)⁻¹ := by
          exact Real.norm_of_nonneg (le_of_lt (inv_pos.mpr (hlpos n)))
        have hbnorm (n : ℕ) : ‖b' n‖ = (l n)⁻¹ * ‖b n‖ := by
          simp [b', norm_smul, hinvnorm]
        have hcnorm (n : ℕ) : ‖c' n‖ = (l n)⁻¹ * ‖c n‖ := by
          simp [c', norm_smul, hinvnorm]
        have hnormsum (n : ℕ) : ‖b' n‖ + ‖c' n‖ = (1 : ℝ) := by
          rw [hbnorm n, hcnorm n]
          calc
            (l n)⁻¹ * ‖b n‖ + (l n)⁻¹ * ‖c n‖
                = (l n)⁻¹ * (‖b n‖ + ‖c n‖) := by ring
            _ = (l n)⁻¹ * l n := by rfl
            _ = 1 := inv_mul_cancel₀ (hlne n)
        have hble (n : ℕ) : ‖b' n‖ ≤ (1 : ℝ) := by
          have hc0 : 0 ≤ ‖c' n‖ := norm_nonneg _
          have := hnormsum n
          linarith
        have hcle (n : ℕ) : ‖c' n‖ ≤ (1 : ℝ) := by
          have hb0 : 0 ≤ ‖b' n‖ := norm_nonneg _
          have := hnormsum n
          linarith
        have hballb (n : ℕ) : b' n ∈ Metric.closedBall (0 : E d) 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hble n
        have hballc (n : ℕ) : c' n ∈ Metric.closedBall (0 : E d) 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hcle n
        have hadd (n : ℕ) : b' n + c' n = (l n)⁻¹ • (b n + c n) := by
          simp [b', c', smul_add]
        have haddnorm (n : ℕ) : ‖b' n + c' n‖ = (l n)⁻¹ * ‖b n + c n‖ := by
          rw [hadd n, norm_smul, hinvnorm]
        have hsmall (n : ℕ) : ‖b' n + c' n‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
          have hnpos : 0 < (n : ℝ) + 1 := by exact_mod_cast (Nat.succ_pos n)
          have hi : 0 < l n := hlpos n
          have hbadi := hbad' n
          rw [haddnorm n]
          -- Divide the strict failure first by `l`, then by `n+1`.
          have h1 : ((n : ℝ) + 1) * ((l n)⁻¹ * ‖b n + c n‖) < 1 := by
            calc
              ((n : ℝ) + 1) * ((l n)⁻¹ * ‖b n + c n‖)
                  = (l n)⁻¹ * (((n:ℝ) + 1) * ‖b n + c n‖) := by ring
              _ < (l n)⁻¹ * l n :=
                (mul_lt_mul_of_pos_left hbadi (inv_pos.mpr hi))
              _ = 1 := inv_mul_cancel₀ (hlne n)
          have h2 : (l n)⁻¹ * ‖b n + c n‖ < (1:ℝ) / ((n:ℝ)+1) :=
            (lt_div_iff₀ hnpos).2 (by
              have := h1
              nlinarith)
          exact le_of_lt h2
        have hsumt : Filter.Tendsto (fun n : ℕ => ‖b' n + c' n‖)
              Filter.atTop (nhds (0:ℝ)) := by
          refine squeeze_zero (fun n => norm_nonneg _) hsmall ?_
          exact tendsto_one_div_add_atTop_nhds_zero_nat
        let q : ℕ → (E d × (E d × E d)) := fun n => (a n, (b' n, c' n))
        have hqmem (n : ℕ) :
            q n ∈ K ×ˢ (Metric.closedBall (0 : E d) 1 ×ˢ
                        Metric.closedBall (0 : E d) 1) := by
          exact ⟨haK n, hballb n, hballc n⟩
        have hcomp : IsCompact
            (K ×ˢ (Metric.closedBall (0 : E d) 1 ×ˢ
                   Metric.closedBall (0 : E d) 1)) :=
          _hKc.prod
            ((ProperSpace.isCompact_closedBall (0 : E d) 1).prod
              (ProperSpace.isCompact_closedBall (0 : E d) 1))
        obtain ⟨z, hz, φ, hφ, hq⟩ := hcomp.tendsto_subseq hqmem
        rcases z with ⟨z, sb, ub⟩
        rcases hz with ⟨hzK, hsbball, hubball⟩
        have hza : Filter.Tendsto (fun j : ℕ => a (φ j)) Filter.atTop (nhds z) := by
          have hp := (continuous_fst.tendsto (z, (sb, ub))).comp hq
          simpa [q, Function.comp_def] using hp
        have hzb : Filter.Tendsto (fun j : ℕ => b' (φ j)) Filter.atTop (nhds sb) := by
          have hp :=
            ((continuous_fst.comp continuous_snd).tendsto (z, (sb, ub))).comp hq
          simpa [q, Function.comp_def] using hp
        have hzc : Filter.Tendsto (fun j : ℕ => c' (φ j)) Filter.atTop (nhds ub) := by
          have hp :=
            ((continuous_snd.comp continuous_snd).tendsto (z, (sb, ub))).comp hq
          simpa [q, Function.comp_def] using hp
        have hsLim : sb ∈ H.stable z :=
          hstable_limit (fun j => a (φ j)) (fun j => b' (φ j)) z sb
            (fun j => haK (φ j)) (fun j => hbmem (φ j)) hza hzb hzK
        have huLim : ub ∈ H.unstable z :=
          hunstable_limit (fun j => a (φ j)) (fun j => c' (φ j)) z ub
            (fun j => haK (φ j)) (fun j => hcmem (φ j)) hza hzc hzK
        have haddt : Filter.Tendsto (fun j : ℕ => b' (φ j) + c' (φ j))
              Filter.atTop (nhds (sb + ub)) := hzb.add hzc
        have hnormsub : Filter.Tendsto (fun j : ℕ => ‖b' (φ j) + c' (φ j)‖)
              Filter.atTop (nhds (0:ℝ)) := hsumt.comp hφ.tendsto_atTop
        have hzu : sb + ub = 0 := by
          have ht := haddt.norm
          have heq : ‖sb + ub‖ = (0:ℝ) := tendsto_nhds_unique ht hnormsub
          exact norm_eq_zero.mp heq
        have hequ : ub = - sb := by
          exact (eq_neg_of_add_eq_zero_right hzu)
        have hsmemu : sb ∈ H.unstable z := by
          -- use that `-sb = ub` lies in the same subspace
          have : - sb ∈ H.unstable z := by simpa [hequ] using huLim
          exact (H.unstable z).neg_mem_iff.mp this
        have hs0 : sb = 0 := by
          have hi : sb ∈ H.stable z ⊓ H.unstable z := ⟨hsLim, hsmemu⟩
          have hz0 : sb ∈ (⊥ : Submodule ℝ (E d)) :=
            (Disjoint.le_bot (H.isCompl_stable_unstable z hzK).disjoint) hi
          exact (Submodule.mem_bot ℝ).mp hz0
        have hu0 : ub = 0 := by simpa [hs0] using hequ
        have hsumlim : Filter.Tendsto (fun j : ℕ => ‖b' (φ j)‖ + ‖c' (φ j)‖)
              Filter.atTop (nhds (‖sb‖ + ‖ub‖)) := hzb.norm.add hzc.norm
        have hsumone : Filter.Tendsto (fun j : ℕ => ‖b' (φ j)‖ + ‖c' (φ j)‖)
              Filter.atTop (nhds (1:ℝ)) := by
          have heq : (fun j : ℕ => ‖b' (φ j)‖ + ‖c' (φ j)‖) = fun _ => (1:ℝ) := by
            funext j
            exact hnormsum (φ j)
          rw [heq]
          exact tendsto_const_nhds
        have gone : (1:ℝ) = 0 := by
          have hh : ‖sb‖ + ‖ub‖ = (1:ℝ) := tendsto_nhds_unique hsumlim hsumone
          -- either orientation is enough
          simpa [hs0, hu0] using hh.symm
        exact one_ne_zero gone
      have hangle : ∃ A : ℝ, 0 < A ∧
          ∀ (x : E d), x ∈ K →
          ∀ (s : E d), s ∈ H.stable x →
          ∀ (u : E d), u ∈ H.unstable x →
            ‖s‖ + ‖u‖ ≤ A * ‖s + u‖ := by
        rcases hangle0 with ⟨A, hA⟩
        refine ⟨max A 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
        intro x hx s hs u hu
        have h0 := hA x hx s hs u hu
        exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      rcases hangle with ⟨Aangle, hAangle, hangleA⟩
      -- A convenient bounded-decomposition formulation; this is the operator-norm
      -- bound for the two algebraic projections, without choosing those maps.
      have hdecompose (x : E d) (hx : x ∈ K) (v : E d) :
          ∃ s : E d, s ∈ H.stable x ∧
            ∃ u : E d, u ∈ H.unstable x ∧ v = s + u ∧
              ‖s‖ ≤ Aangle * ‖v‖ ∧ ‖u‖ ≤ Aangle * ‖v‖ := by
        rcases (Submodule.codisjoint_iff_exists_add_eq.mp
          (H.isCompl_stable_unstable x hx).codisjoint v) with
          ⟨s, u, hs, hu, hsum⟩
        refine ⟨s, hs, u, hu, hsum.symm, ?_, ?_⟩
        · have htot := hangleA x hx s hs u hu
          have hsnon : 0 ≤ ‖u‖ := norm_nonneg _
          have h1 : ‖s‖ ≤ ‖s‖ + ‖u‖ := le_add_of_nonneg_right hsnon
          have h2 : ‖s‖ + ‖u‖ ≤ Aangle * ‖v‖ := by simpa [hsum] using htot
          exact h1.trans h2
        · have htot := hangleA x hx s hs u hu
          have hunon : 0 ≤ ‖s‖ := norm_nonneg _
          have h1 : ‖u‖ ≤ ‖s‖ + ‖u‖ := le_add_of_nonneg_left hunon
          have h2 : ‖s‖ + ‖u‖ ≤ Aangle * ‖v‖ := by simpa [hsum] using htot
          exact h1.trans h2
      have hdecompose_unique (x : E d) (hx : x ∈ K)
          (s u s' u' : E d)
          (hs : s ∈ H.stable x) (hu : u ∈ H.unstable x)
          (hs' : s' ∈ H.stable x) (hu' : u' ∈ H.unstable x)
          (hEq : s + u = s' + u') : s = s' ∧ u = u' := by
        have hd : s - s' = u' - u := by
          calc
            s - s' = (s + u) - (s' + u) := by abel
            _ = (s' + u') - (s' + u) := by rw [hEq]
            _ = u' - u := by abel
        have hmS : s - s' ∈ H.stable x := (H.stable x).sub_mem hs hs'
        have hmU : s - s' ∈ H.unstable x := by
          rw [hd]
          exact (H.unstable x).sub_mem hu' hu
        have hbot : s - s' ∈ (⊥ : Submodule ℝ (E d)) :=
          (Disjoint.le_bot (H.isCompl_stable_unstable x hx).disjoint) ⟨hmS, hmU⟩
        have hz : s - s' = 0 := (Submodule.mem_bot ℝ).mp hbot
        have hss : s = s' := sub_eq_zero.mp hz
        refine ⟨hss, ?_⟩
        -- cancel the equal stable parts in the displayed equality
        simpa [hss] using hEq
      -- The algebraic projection can therefore be used with a uniform norm.
      -- We record it as a plain linear map: in finite dimension its continuity
      -- is automatic when it is later converted to a continuous linear map.
      let P (x : E d) (hx : x ∈ K) : E d →ₗ[ℝ] E d :=
        (H.stable x).projection (H.unstable x)
          (H.isCompl_stable_unstable x hx)
      have hPmem (x : E d) (hx : x ∈ K) (v : E d) :
          P x hx v ∈ H.stable x := by
        dsimp [P]
        exact Submodule.projection_apply_mem
          (H.isCompl_stable_unstable x hx) v
      have hPother (x : E d) (hx : x ∈ K) (v : E d) :
          v - P x hx v ∈ H.unstable x := by
        dsimp [P]
        exact Submodule.sub_projection_mem
          (H.isCompl_stable_unstable x hx) v
      have hPnorm (x : E d) (hx : x ∈ K) (v : E d) :
          ‖P x hx v‖ ≤ Aangle * ‖v‖ := by
        let s : E d := P x hx v
        let u : E d := v - s
        have hs : s ∈ H.stable x := by
          dsimp [s]
          exact hPmem x hx v
        have hu : u ∈ H.unstable x := by
          dsimp [u, s]
          exact hPother x hx v
        have hsu : v = s + u := by
          dsimp [u]
          abel
        have htot := hangleA x hx s hs u hu
        have h1 : ‖s‖ ≤ ‖s‖ + ‖u‖ :=
          le_add_of_nonneg_right (norm_nonneg _)
        have h2 : ‖s‖ + ‖u‖ ≤ Aangle * ‖v‖ := by
          rw [hsu]
          exact htot
        exact h1.trans h2
      have hPother_norm (x : E d) (hx : x ∈ K) (v : E d) :
          ‖v - P x hx v‖ ≤ Aangle * ‖v‖ := by
        let ss : E d := P x hx v
        let uu : E d := v - ss
        have hs : ss ∈ H.stable x := by
          dsimp [ss]
          exact hPmem x hx v
        have hu : uu ∈ H.unstable x := by
          dsimp [uu, ss]
          exact hPother x hx v
        have hsum : v = ss + uu := by
          dsimp [uu]
          abel
        have ht := hangleA x hx ss hs uu hu
        have hle : ‖uu‖ ≤ ‖ss‖ + ‖uu‖ :=
          le_add_of_nonneg_left (norm_nonneg _)
        have hbound : ‖ss‖ + ‖uu‖ ≤ Aangle * ‖v‖ := by
          rw [hsum]
          exact ht
        exact hle.trans hbound
      -- Closedness proved above also gives sequential continuity of the
      -- projections on `K`.  The proof uses compactness of one fixed ball and
      -- uniqueness of the stable--unstable decomposition; it is useful since
      -- no continuity was assumed in the definition of the splitting.
      have hPseq (a : ℕ → E d) (x : E d)
          (ha : ∀ j, a j ∈ K) (hx : x ∈ K)
          (hax : Filter.Tendsto a Filter.atTop (nhds x))
          (v : E d) :
          Filter.Tendsto (fun j => P (a j) (ha j) v)
            Filter.atTop (nhds (P x hx v)) := by
        -- A countably generated-filter criterion: every subsequence has a
        -- (convergent) subsubsequence to the desired value.
        refine Filter.tendsto_of_subseq_tendsto (l := Filter.atTop)
          (f := nhds (P x hx v)) ?_
        intro ns hns
        let bs : ℕ → E d := fun j => P (a (ns j)) (ha (ns j)) v
        have hball (j : ℕ) : bs j ∈ Metric.closedBall (0 : E d)
            (Aangle * ‖v‖) := by
          have hbd := hPnorm (a (ns j)) (ha (ns j)) v
          simpa [bs, Metric.mem_closedBall, dist_zero_right] using hbd
        obtain ⟨w, hw, ψ, hψmono, hψ⟩ :=
          (ProperSpace.isCompact_closedBall (0 : E d) (Aangle * ‖v‖)).tendsto_subseq hball
        have hbase : Filter.Tendsto (fun j : ℕ => a (ns (ψ j)))
              Filter.atTop (nhds x) := by
          have hnsa : Filter.Tendsto (fun j : ℕ => a (ns j))
                Filter.atTop (nhds x) := hax.comp hns
          exact hnsa.comp hψmono.tendsto_atTop
        have hbw : Filter.Tendsto (fun j : ℕ => bs (ψ j))
              Filter.atTop (nhds w) := by
          simpa [Function.comp_def] using hψ
        have hbw' : Filter.Tendsto
              (fun j : ℕ => P (a (ns (ψ j))) (ha (ns (ψ j))) v)
              Filter.atTop (nhds w) := by
          simpa [bs] using hbw
        have hwm : w ∈ H.stable x := by
          refine hstable_limit
            (fun j : ℕ => a (ns (ψ j)))
            (fun j : ℕ => P (a (ns (ψ j))) (ha (ns (ψ j))) v)
            x w (fun j => ha (ns (ψ j)))
              (fun j => hPmem (a (ns (ψ j))) (ha (ns (ψ j))) v)
              hbase hbw' hx
        have hubase : Filter.Tendsto
            (fun j : ℕ => v - P (a (ns (ψ j))) (ha (ns (ψ j))) v)
              Filter.atTop (nhds (v - w)) :=
          (tendsto_const_nhds.sub hbw')
        have hwother : v - w ∈ H.unstable x := by
          refine hunstable_limit
            (fun j : ℕ => a (ns (ψ j)))
            (fun j : ℕ => v - P (a (ns (ψ j))) (ha (ns (ψ j))) v)
            x (v - w) (fun j => ha (ns (ψ j)))
              (fun j => hPother (a (ns (ψ j))) (ha (ns (ψ j))) v)
              hbase hubase hx
        have hxeq : w = P x hx v := by
          have hsx := hPmem x hx v
          have hux := hPother x hx v
          have heq : w + (v - w) = P x hx v + (v - P x hx v) := by
            abel
          exact (hdecompose_unique x hx w (v-w) (P x hx v)
            (v - P x hx v) hwm hwother hsx hux heq).1
        refine ⟨ψ, ?_⟩
        simpa [hxeq] using hbw'
      have hPseqa (a b : ℕ → E d) (x v : E d)
          (ha : ∀ j, a j ∈ K) (hx : x ∈ K)
          (hax : Filter.Tendsto a Filter.atTop (nhds x))
          (hbv : Filter.Tendsto b Filter.atTop (nhds v)) :
          Filter.Tendsto (fun j => P (a j) (ha j) (b j))
            Filter.atTop (nhds (P x hx v)) := by
        have hdiffbase : Filter.Tendsto (fun j : ℕ => b j - v)
            Filter.atTop (nhds (0 : E d)) := by
          convert hbv.sub_const v using 2
          simp
        have hdnorm : Filter.Tendsto (fun j : ℕ => ‖b j - v‖)
              Filter.atTop (nhds (0:ℝ)) :=
          (tendsto_zero_iff_norm_tendsto_zero.mp hdiffbase)
        have hscaled : Filter.Tendsto (fun j : ℕ => Aangle * ‖b j - v‖)
              Filter.atTop (nhds (0:ℝ)) := by
          have hh := hdnorm.const_mul Aangle
          simpa using hh
        have hpdiffnorm : Filter.Tendsto
              (fun j : ℕ => ‖P (a j) (ha j) (b j - v)‖)
              Filter.atTop (nhds (0:ℝ)) := by
          refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hscaled
          exact hPnorm (a j) (ha j) (b j - v)
        have hpdiff : Filter.Tendsto
              (fun j : ℕ => P (a j) (ha j) (b j - v))
              Filter.atTop (nhds (0 : E d)) :=
          tendsto_zero_iff_norm_tendsto_zero.mpr hpdiffnorm
        have hpfix := hPseq a x ha hx hax v
        have haddlim : Filter.Tendsto
              (fun j : ℕ => P (a j) (ha j) v +
                            P (a j) (ha j) (b j - v))
              Filter.atTop (nhds (P x hx v + (0:E d))) :=
          hpfix.add hpdiff
        convert haddlim using 2
        · rw [← (P (a _) (ha _) ).map_add]
          congr 1 <;> abel
        · simp
      -- The sequential statement has the following useful uniform version.
      -- On the compact set the projections at two sufficiently close base
      -- points are uniformly close on the unit ball.  We keep the formulation
      -- without operator norms; the compact-ball argument also makes the
      -- subsequent perturbation estimates independent of a chosen basis.
      have hPunif : ∀ η : ℝ, 0 < η →
          ∃ ρ : ℝ, 0 < ρ ∧
            ∀ (p : E d) (hp : p ∈ K) (q : E d) (hq : q ∈ K),
              ‖p - q‖ < ρ →
              ∀ v : E d, ‖v‖ ≤ (1:ℝ) →
                ‖P p hp v - P q hq v‖ < η := by
        intro η hη
        by_contra hno
        have hfail : ∀ r : ℝ, 0 < r →
            ∃ p : E d, ∃ hp : p ∈ K,
            ∃ q : E d, ∃ hq : q ∈ K,
              ‖p - q‖ < r ∧
              ∃ v : E d, ‖v‖ ≤ (1:ℝ) ∧
                η ≤ ‖P p hp v - P q hq v‖ := by
          intro r hr
          have hn : ¬ (∀ (p : E d) (hp : p ∈ K)
              (q : E d) (hq : q ∈ K),
                ‖p - q‖ < r → ∀ v : E d, ‖v‖ ≤ (1:ℝ) →
                    ‖P p hp v - P q hq v‖ < η) := by
            intro hall
            apply hno
            exact ⟨r, hr, hall⟩
          -- put the failure in a choice-friendly, positive form
          push_neg at hn
          exact hn
        have hrn (n : ℕ) : 0 < (1:ℝ) / ((n:ℝ) + 1) := by
          positivity
        choose p hp q hq hpq v hv hge using
          (fun n : ℕ => hfail ((1:ℝ) / ((n:ℝ) + 1)) (hrn n))
        have hvball (n : ℕ) : v n ∈ Metric.closedBall (0 : E d) 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hv n
        let t : ℕ → E d × (E d × E d) :=
          fun n => (p n, (q n, v n))
        have htmem (n : ℕ) : t n ∈
            K ×ˢ (K ×ˢ Metric.closedBall (0 : E d) 1) := by
          exact ⟨hp n, hq n, hvball n⟩
        have htcomp : IsCompact
            (K ×ˢ (K ×ˢ Metric.closedBall (0 : E d) 1)) :=
          _hKc.prod (_hKc.prod
            (ProperSpace.isCompact_closedBall (0 : E d) 1))
        obtain ⟨zz, hzz, φ, hφmono, htlim⟩ :=
          htcomp.tendsto_subseq htmem
        rcases zz with ⟨z, zq, zv⟩
        rcases hzz with ⟨hzK, hzqK, hzvball⟩
        have hpbase : Filter.Tendsto (fun j : ℕ => p (φ j))
            Filter.atTop (nhds z) := by
          have hh := (continuous_fst.tendsto (z, (zq, zv))).comp htlim
          simpa [t, Function.comp_def] using hh
        have hqbase : Filter.Tendsto (fun j : ℕ => q (φ j))
            Filter.atTop (nhds zq) := by
          have hh := ((continuous_fst.comp continuous_snd).tendsto
            (z, (zq, zv))).comp htlim
          simpa [t, Function.comp_def] using hh
        have hvbase : Filter.Tendsto (fun j : ℕ => v (φ j))
            Filter.atTop (nhds zv) := by
          have hh := ((continuous_snd.comp continuous_snd).tendsto
            (z, (zq, zv))).comp htlim
          simpa [t, Function.comp_def] using hh
        have hdist0 : Filter.Tendsto (fun n : ℕ => ‖p n - q n‖)
            Filter.atTop (nhds (0:ℝ)) := by
          refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
            tendsto_one_div_add_atTop_nhds_zero_nat
          exact le_of_lt (hpq n)
        have hdist0' : Filter.Tendsto (fun j : ℕ => ‖p (φ j) - q (φ j)‖)
            Filter.atTop (nhds (0:ℝ)) := by
          simpa [Function.comp_def] using hdist0.comp hφmono.tendsto_atTop
        have hzqeq : zq = z := by
          have hl : Filter.Tendsto (fun j : ℕ => ‖p (φ j) - q (φ j)‖)
              Filter.atTop (nhds ‖z - zq‖) := (hpbase.sub hqbase).norm
          have hzero : ‖z - zq‖ = (0:ℝ) := tendsto_nhds_unique hl hdist0'
          have he : z - zq = 0 := norm_eq_zero.mp hzero
          exact (sub_eq_zero.mp he).symm
        have hqbase' : Filter.Tendsto (fun j : ℕ => q (φ j))
            Filter.atTop (nhds z) := by simpa [hzqeq] using hqbase
        have hzqK' : z ∈ K := by simpa [hzqeq] using hzqK
        have hlimp : Filter.Tendsto
            (fun j : ℕ => P (p (φ j)) (hp (φ j)) (v (φ j)))
            Filter.atTop (nhds (P z hzK zv)) :=
          hPseqa (fun j => p (φ j)) (fun j => v (φ j)) z zv
            (fun j => hp (φ j)) hzK hpbase hvbase
        have hlimq0 : Filter.Tendsto
            (fun j : ℕ => P (q (φ j)) (hq (φ j)) (v (φ j)))
            Filter.atTop (nhds (P z hzK zv)) := by
          have hh := hPseqa (fun j => q (φ j)) (fun j => v (φ j)) z zv
            (fun j => hq (φ j)) hzqK' hqbase' hvbase
          simpa using hh
        have hlimzero : Filter.Tendsto
            (fun j : ℕ =>
              ‖P (p (φ j)) (hp (φ j)) (v (φ j)) -
                P (q (φ j)) (hq (φ j)) (v (φ j))‖)
            Filter.atTop (nhds (0:ℝ)) := by
          have hh := (hlimp.sub hlimq0).norm
          simpa using hh
        have heta0 : η ≤ (0:ℝ) :=
          ge_of_tendsto hlimzero
            (Filter.Eventually.of_forall (fun j => hge (φ j)))
        exact (not_le_of_gt hη) heta0
      -- By homogeneity the same modulus controls the whole operator.  Using
      -- a non-strict conclusion avoids a needless zero-vector exception later
      -- on when these estimates are multiplied.
      have hPunifLin : ∀ η : ℝ, 0 < η →
          ∃ ρ : ℝ, 0 < ρ ∧
            ∀ (p : E d) (hp : p ∈ K) (q : E d) (hq : q ∈ K),
              ‖p - q‖ < ρ →
              ∀ v : E d,
                ‖P p hp v - P q hq v‖ ≤ η * ‖v‖ := by
        intro η hη
        obtain ⟨ρ, hρ, hunit⟩ := hPunif η hη
        refine ⟨ρ, hρ, ?_⟩
        intro p hp q hq hpq v
        by_cases hv0 : v = 0
        · subst v
          simp
        · have hvpos : 0 < ‖v‖ := (norm_pos_iff.mpr hv0)
          let w : E d := (‖v‖)⁻¹ • v
          have hwone : ‖w‖ = (1:ℝ) := by
            dsimp [w]
            rw [norm_smul]
            have hinv : ‖(‖v‖)⁻¹‖ = (‖v‖)⁻¹ := by
              exact Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hvpos))
            rw [hinv]
            exact inv_mul_cancel₀ (ne_of_gt hvpos)
          have hwu : ‖w‖ ≤ (1:ℝ) := le_of_eq hwone
          have hsmall := hunit p hp q hq hpq w hwu
          have hback : ‖v‖ • w = v := by
            dsimp [w]
            rw [smul_smul]
            simp [ne_of_gt hvpos]
          have hscale : P p hp v - P q hq v =
                ‖v‖ • (P p hp w - P q hq w) := by
            calc
              P p hp v - P q hq v =
                  P p hp (‖v‖ • w) - P q hq (‖v‖ • w) := by rw [hback]
              _ = _ := by
                rw [(P p hp).map_smul, (P q hq).map_smul, smul_sub]
          rw [hscale, norm_smul]
          have hvnorm : ‖(‖v‖ : ℝ)‖ = ‖v‖ := Real.norm_of_nonneg (norm_nonneg _)
          rw [hvnorm]
          have hh : ‖v‖ * ‖P p hp w - P q hq w‖ ≤ ‖v‖ * η :=
            mul_le_mul_of_nonneg_left (le_of_lt hsmall) (norm_nonneg _)
          calc
            ‖v‖ * ‖P p hp w - P q hq w‖ ≤ ‖v‖ * η := hh
            _ = η * ‖v‖ := by ring
      -- A uniform Taylor estimate, with the base point in `K`, is available
      -- for any of the (finitely many at a time) iterates.  In later blocking
      -- arguments it is important that this is proved for `T^[m]` itself,
      -- not only for `T`; its linear part is the iterated derivative in the
      -- hyperbolic estimates above.
      have hfTaylor (m : ℕ) : ∀ η : ℝ, 0 < η →
          ∃ r : ℝ, 0 < r ∧
            ∀ z : E d, z ∈ K → ∀ t : E d, ‖t - z‖ < r →
              ‖((T : E d → E d)^[m]) t - ((T : E d → E d)^[m]) z -
                  fderiv ℝ ((T : E d → E d)^[m]) z (t - z)‖
                ≤ η * ‖t - z‖ := by
        intro η hη
        exact ShadowingFoundation.contDiff_compact_first_order
          (F := E d) (G := E d) _hKc _ (hcontiter m) η hη
      have hgTaylor (m : ℕ) : ∀ η : ℝ, 0 < η →
          ∃ r : ℝ, 0 < r ∧
            ∀ z : E d, z ∈ K → ∀ t : E d, ‖t - z‖ < r →
              ‖((T.symm : E d → E d)^[m]) t -
                  ((T.symm : E d → E d)^[m]) z -
                  fderiv ℝ ((T.symm : E d → E d)^[m]) z (t - z)‖
                ≤ η * ‖t - z‖ := by
        intro η hη
        exact ShadowingFoundation.contDiff_compact_first_order
          (F := E d) (G := E d) _hKc _ (hcontpreiter m) η hη
      -- The algebraic projections commute with every iterate on the
      -- invariant set.  Notice the proof uses both summands: just `map` of
      -- the stable space would only give an inclusion.  The displayed
      -- identities are what a Green operator along a broken orbit is built
      -- from.
      have hfLip (m : ℕ) : ∀ η : ℝ, 0 < η →
          ∃ r : ℝ, 0 < r ∧ ∀ z : E d, z ∈ K → ∀ x y : E d,
            ‖x-z‖ < r → ‖y-z‖ < r →
            ‖(((T : E d → E d)^[m]) x - ((T : E d → E d)^[m]) z -
                fderiv ℝ ((T : E d → E d)^[m]) z (x-z)) -
              (((T : E d → E d)^[m]) y - ((T : E d → E d)^[m]) z -
                fderiv ℝ ((T : E d → E d)^[m]) z (y-z))‖
              ≤ η * ‖x-y‖ := by
        intro η hη
        exact ShadowingFoundation.contDiff_compact_lipschitz_remainder
          (F := E d) (G := E d) _hKc _ (hcontiter m) η hη
      have hgLip (m : ℕ) : ∀ η : ℝ, 0 < η →
          ∃ r : ℝ, 0 < r ∧ ∀ z : E d, z ∈ K → ∀ x y : E d,
            ‖x-z‖ < r → ‖y-z‖ < r →
            ‖(((T.symm : E d → E d)^[m]) x -
                ((T.symm : E d → E d)^[m]) z -
                fderiv ℝ ((T.symm : E d → E d)^[m]) z (x-z)) -
              (((T.symm : E d → E d)^[m]) y -
                ((T.symm : E d → E d)^[m]) z -
                fderiv ℝ ((T.symm : E d → E d)^[m]) z (y-z))‖
              ≤ η * ‖x-y‖ := by
        intro η hη
        exact ShadowingFoundation.contDiff_compact_lipschitz_remainder
          (F := E d) (G := E d) _hKc _ (hcontpreiter m) η hη
      have hPcomm (m : ℕ) (z : E d) (hz : z ∈ K) (w : E d) :
          P (((T : E d → E d)^[m]) z) (hiter z hz m)
              (fderiv ℝ ((T : E d → E d)^[m]) z w) =
            fderiv ℝ ((T : E d → E d)^[m]) z (P z hz w) := by
        let L : E d →L[ℝ] E d :=
          fderiv ℝ ((T : E d → E d)^[m]) z
        let z' : E d := ((T : E d → E d)^[m]) z
        let hz' : z' ∈ K := hiter z hz m
        have hs : L (P z hz w) ∈ H.stable z' := by
          change _ ∈ H.stable (((T : E d → E d)^[m]) z)
          rw [← hsiter m z hz]
          exact Submodule.mem_map_of_mem (hPmem z hz w)
        have hu : L (w - P z hz w) ∈ H.unstable z' := by
          change _ ∈ H.unstable (((T : E d → E d)^[m]) z)
          rw [← hupiter m z hz]
          exact Submodule.mem_map_of_mem (hPother z hz w)
        have hsplit : L w = L (P z hz w) + L (w - P z hz w) := by
          rw [L.map_sub]
          abel
        have hp0 : P z' hz' (L w) ∈ H.stable z' := hPmem z' hz' (L w)
        have hp1 : L w - P z' hz' (L w) ∈ H.unstable z' :=
          hPother z' hz' (L w)
        have he : P z' hz' (L w) + (L w - P z' hz' (L w)) =
            L (P z hz w) + L (w - P z hz w) := by
          rw [← hsplit]
          abel
        have hres := hdecompose_unique z' hz'
          (P z' hz' (L w)) (L w - P z' hz' (L w))
          (L (P z hz w)) (L (w - P z hz w))
          hp0 hp1 hs hu he
        exact hres.1
      have hPcomm_pre (m : ℕ) (z : E d) (hz : z ∈ K) (w : E d) :
          P (((T.symm : E d → E d)^[m]) z) (hiterpre z hz m)
              (fderiv ℝ ((T.symm : E d → E d)^[m]) z w) =
            fderiv ℝ ((T.symm : E d → E d)^[m]) z (P z hz w) := by
        let L : E d →L[ℝ] E d :=
          fderiv ℝ ((T.symm : E d → E d)^[m]) z
        let z' : E d := ((T.symm : E d → E d)^[m]) z
        let hz' : z' ∈ K := hiterpre z hz m
        have hs : L (P z hz w) ∈ H.stable z' := by
          change _ ∈ H.stable (((T.symm : E d → E d)^[m]) z)
          rw [← hspreiter m z hz]
          exact Submodule.mem_map_of_mem (hPmem z hz w)
        have hu : L (w - P z hz w) ∈ H.unstable z' := by
          change _ ∈ H.unstable (((T.symm : E d → E d)^[m]) z)
          rw [← hupreiter m z hz]
          exact Submodule.mem_map_of_mem (hPother z hz w)
        have hsplit : L w = L (P z hz w) + L (w - P z hz w) := by
          rw [L.map_sub]
          abel
        have hp0 : P z' hz' (L w) ∈ H.stable z' := hPmem z' hz' (L w)
        have hp1 : L w - P z' hz' (L w) ∈ H.unstable z' :=
          hPother z' hz' (L w)
        have he : P z' hz' (L w) + (L w - P z' hz' (L w)) =
            L (P z hz w) + L (w - P z hz w) := by
          rw [← hsplit]
          abel
        have hres := hdecompose_unique z' hz'
          (P z' hz' (L w)) (L w - P z' hz' (L w))
          (L (P z hz w)) (L (w - P z hz w))
          hp0 hp1 hs hu he
        exact hres.1
      have hPid (z : E d) (hz : z ∈ K) (w : E d)
          (hw : w ∈ H.stable z) : P z hz w = w := by
        dsimp [P]
        have hh := Submodule.projection_apply_left
          (H.isCompl_stable_unstable z hz)
          (⟨w, hw⟩ : H.stable z)
        exact hh
      have hPzero (z : E d) (hz : z ∈ K) (w : E d)
          (hw : w ∈ H.unstable z) : P z hz w = 0 := by
        have hs : P z hz w ∈ H.stable z := hPmem z hz w
        have hu : w - P z hz w ∈ H.unstable z := hPother z hz w
        have heq : P z hz w + (w - P z hz w) = (0 : E d) + w := by
          abel
        have hzq := (hdecompose_unique z hz
          (P z hz w) (w - P z hz w) 0 w hs hu
            ((H.stable z).zero_mem) hw heq).1
        exact hzq
      have hD_bound (m : ℕ) : ∃ D : ℝ, 0 < D ∧
          ∀ z : E d, z ∈ K → ∀ v : E d,
            ‖fderiv ℝ ((T : E d → E d)^[m]) z v‖ ≤ D * ‖v‖ := by
        have hdc : Continuous (fderiv ℝ ((T : E d → E d)^[m])) :=
          (hcontiter m).continuous_fderiv (by norm_num)
        have hnormc : Continuous
            (fun z : E d => ‖fderiv ℝ ((T : E d → E d)^[m]) z‖) :=
          hdc.norm
        rcases (_hKc.bddAbove_image hnormc.continuousOn) with ⟨D0, hD0⟩
        refine ⟨max D0 1, lt_of_lt_of_le (by norm_num)
          (le_max_right _ _), ?_⟩
        intro z hz v
        calc
          ‖fderiv ℝ ((T : E d → E d)^[m]) z v‖
              ≤ ‖fderiv ℝ ((T : E d → E d)^[m]) z‖ * ‖v‖ :=
                ContinuousLinearMap.le_opNorm _ _
          _ ≤ max D0 1 * ‖v‖ :=
            mul_le_mul_of_nonneg_right
              ((hD0 ⟨z, hz, rfl⟩).trans (le_max_left _ _))
              (norm_nonneg _)
      have hG_bound (m : ℕ) : ∃ D : ℝ, 0 < D ∧
          ∀ z : E d, z ∈ K → ∀ v : E d,
            ‖fderiv ℝ ((T.symm : E d → E d)^[m]) z v‖ ≤ D * ‖v‖ := by
        have hdc : Continuous (fderiv ℝ ((T.symm : E d → E d)^[m])) :=
          (hcontpreiter m).continuous_fderiv (by norm_num)
        have hnormc : Continuous
            (fun z : E d => ‖fderiv ℝ ((T.symm : E d → E d)^[m]) z‖) :=
          hdc.norm
        rcases (_hKc.bddAbove_image hnormc.continuousOn) with ⟨D0, hD0⟩
        refine ⟨max D0 1, lt_of_lt_of_le (by norm_num)
          (le_max_right _ _), ?_⟩
        intro z hz v
        calc
          ‖fderiv ℝ ((T.symm : E d → E d)^[m]) z v‖
              ≤ ‖fderiv ℝ ((T.symm : E d → E d)^[m]) z‖ * ‖v‖ :=
                ContinuousLinearMap.le_opNorm _ _
          _ ≤ max D0 1 * ‖v‖ :=
            mul_le_mul_of_nonneg_right
              ((hD0 ⟨z, hz, rfl⟩).trans (le_max_left _ _))
              (norm_nonneg _)
      have hchooseBlock (e : ℝ) (hepos : 0 < e) :
          ∃ m : ℕ, H.const * H.rate ^ m < e := by
        have hdiv : 0 < e / H.const := div_pos hepos H.const_pos
        obtain ⟨m, hm⟩ :=
          exists_pow_lt_of_lt_one hdiv H.rate_lt_one
        refine ⟨m, ?_⟩
        have hh := mul_lt_mul_of_pos_left hm H.const_pos
        calc
          H.const * H.rate ^ m < H.const * (e / H.const) := hh
          _ = e := by field_simp [ne_of_gt H.const_pos]
      have hopen_tube (r : ℝ) :
          IsOpen {x : E d | ∃ z : E d, z ∈ K ∧ ‖x-z‖ < r} := by
        have heq : {x : E d | ∃ z : E d, z ∈ K ∧ ‖x-z‖ < r} =
            ⋃ z : {z : E d // z ∈ K}, Metric.ball (z : E d) r := by
          ext x
          constructor
          · intro hx
            rcases hx with ⟨z, hz, hxz⟩
            refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
            exact Metric.mem_ball.mpr (by simpa [dist_eq_norm] using hxz)
          · intro hx
            rcases Set.mem_iUnion.mp hx with ⟨z, hz⟩
            refine ⟨(z : E d), z.property, ?_⟩
            have hh := Metric.mem_ball.mp hz
            simpa [dist_eq_norm] using hh
        rw [heq]
        exact isOpen_iUnion (fun z : {z : E d // z ∈ K} => Metric.isOpen_ball)
      have hsub_tube {r : ℝ} (hr : 0 < r) :
          K ⊆ {x : E d | ∃ z : E d, z ∈ K ∧ ‖x-z‖ < r} := by
        intro z hz
        exact ⟨z, hz, by simpa using hr⟩
      -- Work henceforth on a fixed block with genuinely small hyperbolicity
      -- constant.  Blocking is necessary here: the definition bounds the
      -- first iterate by `const * rate`, which need not itself be below one.
      -- The rest of the shadowing construction can therefore use an ordinary
      -- contraction on block sequences.
      let γ : ℝ := 1 / (100 * (Aangle + 1))
      have hγ : 0 < γ := by
        dsimp [γ]
        have hp : 0 < Aangle + 1 := by linarith
        positivity
      obtain ⟨mraw, hmraw⟩ := hchooseBlock γ hγ
      -- choose a positive block length; enlarging only improves the estimate
      let m : ℕ := mraw + 1
      have hmpos : 0 < m := by dsimp [m]; omega
      have hm : H.const * H.rate ^ m < γ := by
        have hposraw : 0 < H.const * H.rate ^ mraw :=
          mul_pos H.const_pos (pow_pos H.rate_pos _)
        calc
          H.const * H.rate ^ m = (H.const * H.rate ^ mraw) * H.rate := by
            dsimp [m]
            rw [pow_succ]
            ring
          _ < H.const * H.rate ^ mraw := by
            have hh := H.rate_lt_one
            nlinarith
          _ < γ := hmraw
      obtain ⟨D, hD, hDb⟩ := hD_bound m
      let η : ℝ := γ / ((D + 1) * (Aangle + 1))
      have hη : 0 < η := by
        dsimp [η]
        have hp : 0 < (D+1)*(Aangle+1) := mul_pos (by linarith) (by linarith)
        exact div_pos hγ hp
      obtain ⟨ρ, hρpos, hρproj⟩ := hPunifLin η hη
      obtain ⟨r, hrpos, hrLip⟩ := hfLip m η hη
      -- On a finite block very small one-step errors really go to a small
      -- end error, uniformly over the compact set.  No point of the broken
      -- path is assumed to lie in the compact set.  This elementary lemma is
      -- a useful guard when passing from time one to the blocked map.
      have halpha : 0 < min ρ r / 4 :=
        div_pos (lt_min hρpos hrpos) (by norm_num)
      obtain ⟨sblock, hsblock, eblock, heblock, hblock⟩ :=
        ShadowingPerturb.finite_pseudo_close (F := E d)
          _hKc (T : E d → E d) H.contDiff_fwd.continuous
          (fun ⦃x⦄ hx => him x hx) m (min ρ r / 4) halpha
      -- This explicit tube is convenient when selecting a base point of `K`
      -- for every member of a broken orbit.  Shrinking it also below the
      -- finite-block modulus keeps a pseudoorbit endpoint close to
      -- `T^[m]` of its centre.
      let R : ℝ := min (min ρ r) sblock / 100
      have hR : 0 < R := by
        dsimp [R]
        exact div_pos (lt_min (lt_min hρpos hrpos) hsblock) (by norm_num)
      have hRblock : R < sblock := by
        dsimp [R]
        have hle : min (min ρ r) sblock ≤ sblock := min_le_right _ _
        have hp : 0 < sblock := hsblock
        nlinarith
      have hRrho : R < ρ := by
        dsimp [R]
        have hle : min (min ρ r) sblock ≤ ρ :=
          (min_le_left _ _).trans (min_le_left _ _)
        nlinarith [hρpos]
      refine ⟨{x : E d | ∃ z : E d, z ∈ K ∧ ‖x-z‖ < R},
        hopen_tube R, hsub_tube hR, ?_⟩
      intro δ hδ
      -- It suffices to do the block construction on the fixed small ball;
      -- a more accurate shadow is of course a `δ`-shadow as well.
      let δ₀ : ℝ := min δ R / 2
      have hδ₀ : 0 < δ₀ := by
        dsimp [δ₀]
        exact div_pos (lt_min hδ hR) (by norm_num)
      have hδlt : δ₀ < δ := by
        dsimp [δ₀]
        have hle : min δ R ≤ δ := min_le_left _ _
        nlinarith
      suffices hcore : ∃ ε > 0, ∀ x : ℕ → E d,
          (∀ n, x n ∈ {t : E d | ∃ z : E d, z ∈ K ∧ ‖t-z‖ < R}) →
          IsPseudoOrbit (T : E d → E d) ε x →
          ∃ y : E d, ∀ n : ℕ,
            ‖x n - (T : E d → E d)^[n] y‖ < δ₀ by
        rcases hcore with ⟨ε, hε, hsh⟩
        refine ⟨ε, hε, ?_⟩
        intro x hx hp
        rcases hsh x hx hp with ⟨y, hy⟩
        exact ⟨y, fun n => lt_trans (hy n) hδlt⟩
      have hcenters : ∀ x : ℕ → E d,
          (∀ n, x n ∈ {t : E d | ∃ z : E d, z ∈ K ∧ ‖t-z‖ < R}) →
          ∃ a : ℕ → E d, (∀ n, a n ∈ K) ∧
            (∀ n, ‖x n - a n‖ < R) := by
        intro x hx
        have hx' : ∀ n : ℕ, ∃ z : E d,
            z ∈ K ∧ ‖x n - z‖ < R := hx
        choose a haK ha using hx'
        exact ⟨a, haK, ha⟩
      have hbroken : ∀ (ε : ℝ) (x a : ℕ → E d),
          IsPseudoOrbit (T : E d → E d) ε x →
          (∀ n, ‖x n - a n‖ < R) →
          ∀ n, ‖a (n+1) - T (a n)‖ ≤
            R + ε + ‖T (x n) - T (a n)‖ := by
        intro ε x a hp ha n
        have htri : ‖a (n+1) - T (a n)‖ ≤
            (‖a (n+1) - x (n+1)‖ +
              ‖x (n+1) - T (x n)‖) +
              ‖T (x n) - T (a n)‖ := by
          have heq : a (n+1) - T (a n) =
              (a (n+1) - x (n+1)) +
                (x (n+1) - T (x n)) +
                (T (x n) - T (a n)) := by
            abel
          rw [heq]
          exact (norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) (le_refl _))
        have hfirst : ‖a (n+1) - x (n+1)‖ ≤ R := by
          rw [norm_sub_rev]
          exact le_of_lt (ha (n+1))
        have hsecond : ‖x (n+1) - T (x n)‖ ≤ ε := by
          exact le_of_lt (hp n)
        calc
          ‖a (n+1) - T (a n)‖ ≤
              (‖a (n+1) - x (n+1)‖ +
                ‖x (n+1) - T (x n)‖) +
                ‖T (x n) - T (a n)‖ := htri
          _ ≤ (R + ε) + ‖T (x n) - T (a n)‖ :=
              add_le_add (add_le_add hfirst hsecond) (le_refl _)
          _ = R + ε + ‖T (x n) - T (a n)‖ := by ring
      -- The remaining lemma is the bounded-sequence inverse for the block
      -- map on the above tube (and interpolation in the `m` intermediate
      -- times).  All constants needed by it have now been made strict:
      -- `const*rate^m < γ`, the projection modulus `hρproj`, and the
      -- Lipschitz nonlinear remainder `hrLip`.
      -- The following is the linear Green inverse on an *exact* block
      -- orbit in `K`.  It is the piece of the fixed point argument which is
      -- genuinely infinite dimensional (the future unstable series).  The
      -- lemma in `ShadowingGreen` states it without choosing coordinates; here
      -- we check that an orbit of `T^[m]` supplies all its hypotheses.  This
      -- also records explicitly which part is left to perturb for a broken
      -- orbit.
      obtain ⟨z₀, hz₀⟩ : ∃ z : E d, z ∈ K := Set.nonempty_iff_ne_empty.mpr he
      let Fm : E d → E d := (T : E d → E d)^[m]
      let zm : ℕ → E d := fun k => (Fm^[k]) z₀
      have hzm0 : zm 0 = z₀ := by simp [zm]
      have hzms (n : ℕ) : zm (n+1) = Fm (zm n) := by
        simp [zm, Function.iterate_succ_apply']
      have hzm : ∀ n : ℕ, zm n ∈ K := by
        intro n
        induction n with
        | zero => simpa [hzm0] using hz₀
        | succ n ih =>
          rw [hzms]
          exact hiter _ ih m
      let pp : ℕ → E d →L[ℝ] E d := fun n =>
        LinearMap.toContinuousLinearMap (P (zm n) (hzm n))
      let LL : ℕ → E d →L[ℝ] E d := fun n =>
        fderiv ℝ ((T : E d → E d)^[m]) (zm n)
      let BB : ℕ → E d →L[ℝ] E d := fun n =>
        fderiv ℝ ((T.symm : E d → E d)^[m])
          (((T : E d → E d)^[m]) (zm n))
      let cc : ℝ := H.const * H.rate ^ m
      have hcc0 : 0 ≤ cc :=
        mul_nonneg (le_of_lt H.const_pos)
          (pow_nonneg (le_of_lt H.rate_pos) m)
      have hγ1 : γ < 1 := by
        dsimp [γ]
        have ha' : 0 < Aangle + 1 := by linarith
        have hbig : 1 < 100 * (Aangle + 1) := by nlinarith
        exact (div_lt_one (by nlinarith : (0:ℝ)<100*(Aangle+1))).2 hbig
      have hcc1 : cc < 1 := lt_trans hm hγ1
      have hpp_bound (n : ℕ) (v : E d) :
          ‖pp n v‖ ≤ Aangle * ‖v‖ := by
        change ‖P (zm n) (hzm n) v‖ ≤ _
        exact hPnorm (zm n) (hzm n) v
      have hqq_bound (n : ℕ) (v : E d) :
          ‖v - pp n v‖ ≤ Aangle * ‖v‖ := by
        change ‖v - P (zm n) (hzm n) v‖ ≤ _
        exact hPother_norm (zm n) (hzm n) v
      have hppp (n : ℕ) (v : E d) : pp n (pp n v) = pp n v := by
        change P (zm n) (hzm n) (P (zm n) (hzm n) v) = _
        exact hPid (zm n) (hzm n) _
          (hPmem (zm n) (hzm n) v)
      have hzms' (n : ℕ) :
          ((T : E d → E d)^[m]) (zm n) = zm (n+1) := by
        simpa [Fm] using (hzms n).symm
      have hstab_block (n : ℕ) (v : E d) (hv : pp n v = v) :
          pp (n+1) (LL n v) = LL n v ∧ ‖LL n v‖ ≤ cc * ‖v‖ := by
        have hvS : v ∈ H.stable (zm n) := by
          have hh := hPmem (zm n) (hzm n) v
          change P (zm n) (hzm n) v = v at hv
          simpa [hv] using hh
        have hLS : fderiv ℝ ((T : E d → E d)^[m]) (zm n) v ∈
              H.stable (zm (n+1)) := by
          rw [← hzms' n, ← hsiter m (zm n) (hzm n)]
          exact Submodule.mem_map_of_mem hvS
        constructor
        · change P (zm (n+1)) (hzm (n+1))
                (fderiv ℝ ((T : E d → E d)^[m]) (zm n) v) = _
          exact hPid (zm (n+1)) (hzm (n+1)) _ hLS
        · change ‖fderiv ℝ ((T : E d → E d)^[m]) (zm n) v‖
                ≤ cc * ‖v‖
          exact H.contract_stable (zm n) (hzm n) v hvS m
      have hLun_block (n : ℕ) (v : E d) (hv : pp n v = 0) :
          pp (n+1) (LL n v) = 0 := by
        have hvU : v ∈ H.unstable (zm n) := by
          have hh := hPother (zm n) (hzm n) v
          change P (zm n) (hzm n) v = 0 at hv
          simpa [hv] using hh
        have hLU : fderiv ℝ ((T : E d → E d)^[m]) (zm n) v ∈
              H.unstable (zm (n+1)) := by
          rw [← hzms' n, ← hupiter m (zm n) (hzm n)]
          exact Submodule.mem_map_of_mem hvU
        change P (zm (n+1)) (hzm (n+1))
              (fderiv ℝ ((T : E d → E d)^[m]) (zm n) v) = 0
        exact hPzero (zm (n+1)) (hzm (n+1)) _ hLU
      have hBun_block (n : ℕ) (v : E d) (hv : pp (n+1) v = 0) :
          pp n (BB n v) = 0 ∧ ‖BB n v‖ ≤ cc * ‖v‖ := by
        have hvU : v ∈ H.unstable (zm (n+1)) := by
          have hh := hPother (zm (n+1)) (hzm (n+1)) v
          change P (zm (n+1)) (hzm (n+1)) v = 0 at hv
          simpa [hv] using hh
        have hz' := hiter (zm n) (hzm n) m
        have hpre_eq :
            ((T.symm : E d → E d)^[m])
              (((T : E d → E d)^[m]) (zm n)) = zm n :=
          ShadowingFoundation.iterate_symm_apply_iterate T m (zm n)
        have hmemB :
            fderiv ℝ ((T.symm : E d → E d)^[m])
              (((T : E d → E d)^[m]) (zm n)) v ∈ H.unstable (zm n) := by
          have hvU' : v ∈ H.unstable (((T : E d → E d)^[m]) (zm n)) := by
            simpa [hzms' n] using hvU
          have hh :
              fderiv ℝ ((T.symm : E d → E d)^[m])
                (((T : E d → E d)^[m]) (zm n)) v ∈
                H.unstable (((T.symm : E d → E d)^[m])
                  (((T : E d → E d)^[m]) (zm n))) := by
            rw [← hupreiter m
              (((T : E d → E d)^[m]) (zm n)) hz']
            exact Submodule.mem_map_of_mem hvU'
          simpa only [hpre_eq] using hh
        constructor
        · change P (zm n) (hzm n)
            (fderiv ℝ ((T.symm : E d → E d)^[m])
              (((T : E d → E d)^[m]) (zm n)) v) = 0
          exact hPzero (zm n) (hzm n) _ hmemB
        · change ‖fderiv ℝ ((T.symm : E d → E d)^[m])
              (((T : E d → E d)^[m]) (zm n)) v‖ ≤ cc * ‖v‖
          have hc' := H.contract_unstable
              (((T : E d → E d)^[m]) (zm n)) hz' v
              (by simpa [hzms' n] using hvU) m
          exact hc'
      have hleft_block (n : ℕ) (v : E d) (hv : pp (n+1) v = 0) :
          LL n (BB n v) = v := by
        change fderiv ℝ ((T : E d → E d)^[m]) (zm n)
            (fderiv ℝ ((T.symm : E d → E d)^[m])
              (((T : E d → E d)^[m]) (zm n)) v) = v
        have hpre_eq :
            ((T.symm : E d → E d)^[m])
              (((T : E d → E d)^[m]) (zm n)) = zm n :=
          ShadowingFoundation.iterate_symm_apply_iterate T m (zm n)
        simpa [hpre_eq] using
          (ShadowingFoundation.fderiv_iter_apply_fderiv_symmIter
            (f := T) hf hg m (((T : E d → E d)^[m]) (zm n)) v)
      have hgreen_block (w₀ : ℕ → E d) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
          (hw₀ : ∀ n, ‖w₀ n‖ ≤ C₀) :
          ∃ e : ℕ → E d,
            (∀ n, ‖e n‖ ≤ 2 * (Aangle * C₀ / (1-cc))) ∧
            (∀ n, e (n+1) - LL n (e n) = w₀ n) ∧
            pp 0 (e 0) = 0 := by
        exact ShadowingGreen.exists_bounded_solution_exact
          (p := pp) (L := LL) (B := BB) (w := w₀)
          (A := Aangle) (c := cc) (C := C₀)
          (le_of_lt hAangle) hcc0 hcc1 hC₀
          hpp_bound hqq_bound hppp hw₀
          (fun n v hv => hstab_block n v hv)
          (fun n v hv => hLun_block n v hv)
          (fun n v hv => hBun_block n v hv)
          (fun n v hv => hleft_block n v hv)
      have hright_block (n : ℕ) (v : E d) (hv : pp n v = 0) :
          BB n (LL n v) = v := by
        change fderiv ℝ ((T.symm : E d → E d)^[m])
          (((T : E d → E d)^[m]) (zm n))
            (fderiv ℝ ((T : E d → E d)^[m]) (zm n) v) = v
        exact ShadowingFoundation.fderiv_symmIter_apply_fderivIter
          (f := T) hf hg m (zm n) v
      -- The version on bounded functions is often more convenient than the
      -- raw series: it is a Lipschitz right inverse of the exact block
      -- difference operator.  Keeping it here also isolates the one truly
      -- infinite summation from the later perturbation argument.
      have hgreen_solver_block :
          ∃ GG : (BoundedContinuousFunction ℕ (E d)) →
                (BoundedContinuousFunction ℕ (E d)),
            (∀ w n, GG w (n+1) - LL n (GG w n) = w n) ∧
            (∀ w, pp 0 (GG w 0) = 0) ∧
            (∀ w, ‖GG w‖ ≤ 2 * (Aangle * ‖w‖ / (1-cc))) ∧
            (∀ u v, ‖GG u - GG v‖ ≤
              2 * (Aangle * ‖u-v‖ / (1-cc))) := by
        exact ShadowingGreen.exists_green_solver
          (p := pp) (L := LL) (B := BB)
          (A := Aangle) (c := cc)
          (le_of_lt hAangle) hcc0 hcc1
          hpp_bound hqq_bound hppp
          (fun n v hv => hstab_block n v hv)
          (fun n v hv => hLun_block n v hv)
          (fun n v hv => hBun_block n v hv)
          (fun n v hv => hleft_block n v hv)
          (fun n v hv => hright_block n v hv)
      have hgreen_fixed_exact (k : ℝ) (hk : 0 ≤ k)
          (hksmall : (2*Aangle/(1-cc))*k < 1)
          (W : BoundedContinuousFunction ℕ (E d) →
                BoundedContinuousFunction ℕ (E d))
          (hW : ∀ u v, ‖W u - W v‖ ≤ k * ‖u-v‖) :
          ∃ e : BoundedContinuousFunction ℕ (E d),
            ∀ n, e (n+1) - LL n (e n) = W e n := by
        rcases hgreen_solver_block with ⟨GG, hGG, hGG0, hGGn, hGGd⟩
        have hden : 0 < 1-cc := sub_pos.mpr hcc1
        have hM0 : 0 ≤ (2*Aangle/(1-cc)) := by positivity
        have hGlip : ∀ u v,
            ‖GG u - GG v‖ ≤ (2*Aangle/(1-cc)) * ‖u-v‖ := by
          intro u v
          convert hGGd u v using 1 <;> ring
        exact ShadowingPerturb.exists_solution_of_green
          (L := LL) (G := GG)
          (M := 2*Aangle/(1-cc)) (k := k)
          hM0 hk (by simpa using hksmall)
          hGG hGlip W hW
      -- A broken block path still has to be reduced to the exact one above.
      -- First make the elementary finite-block reduction.  Notice its small
      -- constant depends on `m`; uniform continuity for one iterate would
      -- not suffice here, and no intermediate point lies in `K`.
      have hRr : R < r := by
        dsimp [R]
        have hle : min (min ρ r) sblock ≤ r :=
          (min_le_left _ _).trans (min_le_right _ _)
        nlinarith [hrpos]
      let Ct : Set (E d) :=
        (fun q : E d × E d => q.1 + q.2) ''
          (K ×ˢ Metric.closedBall (0 : E d) R)
      have hCt : IsCompact Ct :=
        ShadowingPerturb.isCompact_thickening _hKc R
      have hxCt (n : ℕ) (x : ℕ → E d)
          (hx : ∀ i, x i ∈ {t:E d | ∃ z:E d, z ∈ K ∧ ‖t-z‖ < R}) :
          x n ∈ Ct := by
        obtain ⟨z,hz,hzn⟩ := hx n
        exact ShadowingPerturb.mem_thickening_of hz hzn
      have hdel4 : 0 < δ₀/4 := by linarith
      obtain ⟨si, hsi, hiteri⟩ :=
        ShadowingPerturb.finite_iterate_close_all (F:=E d)
          (T : E d → E d) H.contDiff_fwd.continuous Ct hCt m (δ₀/4) hdel4
      -- clipping radius for the unknown correction at block starts
      let t0 : ℝ := min (r-R) (min si (δ₀/4)) / 4
      have ht0 : 0 < t0 := by
        dsimp [t0]
        have : 0 < r-R := sub_pos.mpr hRr
        exact div_pos (lt_min this (lt_min hsi hdel4)) (by norm_num)
      have ht_r : R + t0 < r := by
        have hh : t0 ≤ (r-R)/4 := by
          dsimp [t0]
          nlinarith [min_le_left (r-R) (min si (δ₀/4))]
        nlinarith [hRr]
      have ht_i : t0 ≤ si := by
        dsimp [t0]
        have hh := (min_le_right (r-R) (min si (δ₀/4))).trans
          (min_le_left si (δ₀/4))
        nlinarith [hsi]
      have ht_del : t0 ≤ δ₀/4 := by
        dsimp [t0]
        have hh := (min_le_right (r-R) (min si (δ₀/4))).trans
          (min_le_right si (δ₀/4))
        nlinarith [hdel4]
      -- allowable end defect of the broken `xx` block
      let b0 : ℝ := t0 / (100 * (Aangle+1))
      have hb0 : 0 < b0 := by dsimp [b0]; positivity
      obtain ⟨ee, hee, hpall⟩ :=
        ShadowingPerturb.finite_pseudo_all (F:=E d)
          (T : E d → E d) H.contDiff_fwd.continuous Ct hCt m b0 hb0
      let eps0 : ℝ := min (min eblock ee) (δ₀/100)
      have heps0 : 0 < eps0 := by
        dsimp [eps0]
        exact lt_min (lt_min heblock hee) (by positivity)
      refine ⟨eps0, heps0, ?_⟩
      intro xx hxx hpx
      obtain ⟨aa, haa, hxaa⟩ := hcenters xx hxx
      have heps_le : eps0 ≤ eblock := by
        dsimp [eps0]
        exact (min_le_left _ _).trans (min_le_left _ _)
      have heps_ee : eps0 ≤ ee := by
        dsimp [eps0]
        exact (min_le_left _ _).trans (min_le_right _ _)
      have hblock_path (k : ℕ) :
          ‖xx (m*k + m) - ((T : E d → E d)^[m]) (aa (m*k))‖
              < min ρ r / 4 := by
        let u : ℕ → E d := fun i => xx (m*k + i)
        have hstart : ‖u 0 - aa (m*k)‖ < sblock := by
          change ‖xx (m*k+0) - aa (m*k)‖ < sblock
          simpa using (lt_trans (hxaa (m*k)) hRblock)
        have hstep : ∀ i < m,
            ‖u (i+1) - T (u i)‖ < eblock := by
          intro i hi
          dsimp [u]
          have hh := hpx (m*k+i)
          have hlt : ‖xx (m*k+i+1) - T (xx (m*k+i))‖ < eps0 := by
            simpa [add_assoc] using hh
          exact lt_of_lt_of_le hlt heps_le
        have hh := hblock (aa (m*k)) (haa (m*k)) u hstart hstep
        simpa [u, add_assoc] using hh
      -- Consequently the two fibres that have to be matched at a block
      -- break really are within the modulus of continuity of `P`.
      have hjoin (k : ℕ) :
          ‖((T : E d → E d)^[m]) (aa (m*k)) - aa (m*(k+1))‖ < ρ := by
        have hb := hblock_path k
        have htail := hxaa (m*(k+1))
        have hind : m*k + m = m*(k+1) := by ring
        rw [hind] at hb
        have htri : ‖((T : E d → E d)^[m]) (aa (m*k)) -
                  aa (m*(k+1))‖ ≤
              ‖((T : E d → E d)^[m]) (aa (m*k)) - xx (m*(k+1))‖ +
                ‖xx (m*(k+1)) - aa (m*(k+1))‖ := by
          have heq : ((T : E d → E d)^[m]) (aa (m*k)) -
                aa (m*(k+1)) =
              (((T : E d → E d)^[m]) (aa (m*k)) - xx (m*(k+1))) +
                (xx (m*(k+1)) - aa (m*(k+1))) := by abel
          rw [heq]
          exact norm_add_le _ _
        have hb' : ‖((T : E d → E d)^[m]) (aa (m*k)) -
              xx (m*(k+1))‖ < min ρ r / 4 := by
          rwa [norm_sub_rev]
        have halphale : min ρ r / 4 ≤ ρ / 4 := by
          have h := min_le_left ρ r
          nlinarith
        have hRR : R ≤ ρ / 100 := by
          dsimp [R]
          have h := (min_le_left (min ρ r) sblock).trans
            (min_le_left ρ r)
          nlinarith
        calc
          ‖((T : E d → E d)^[m]) (aa (m*k)) - aa (m*(k+1))‖
              ≤ ‖((T : E d → E d)^[m]) (aa (m*k))-xx (m*(k+1))‖ +
                  ‖xx (m*(k+1)) - aa (m*(k+1))‖ := htri
          _ < ρ := by nlinarith
      have hjoin_proj (k : ℕ) (v : E d) :
          ‖P (((T : E d → E d)^[m]) (aa (m*k)))
                (hiter (aa (m*k)) (haa (m*k)) m) v -
            P (aa (m*(k+1))) (haa (m*(k+1))) v‖ ≤ η * ‖v‖ := by
        exact hρproj _ (hiter (aa (m*k)) (haa (m*k)) m) _ (haa (m*(k+1))) (hjoin k) v
      -- Package the derivative cocycle along the (broken) centres.  Unlike the
      -- preliminary `zm` calculation this one genuinely has its fibres at
      -- `aa (m*k)`; at the right endpoint the range is at `Fm (aa (m*k))`.
      let pa : ℕ → E d →L[ℝ] E d := fun k =>
        LinearMap.toContinuousLinearMap (P (aa (m*k)) (haa (m*k)))
      let ra : ℕ → E d →L[ℝ] E d := fun k =>
        LinearMap.toContinuousLinearMap
          (P (((T : E d → E d)^[m]) (aa (m*k)))
            (hiter (aa (m*k)) (haa (m*k)) m))
      let La : ℕ → E d →L[ℝ] E d := fun k =>
        fderiv ℝ ((T : E d → E d)^[m]) (aa (m*k))
      let Ba : ℕ → E d →L[ℝ] E d := fun k =>
        fderiv ℝ ((T.symm : E d → E d)^[m])
          (((T : E d → E d)^[m]) (aa (m*k)))
      let θa : ℝ := η * (2*Aangle+1)
      have hθa0 : 0 ≤ θa := by
        dsimp [θa]
        exact mul_nonneg (le_of_lt hη) (by linarith)
      -- The deliberately large numeric slack in `γ` makes the transport
      -- harmless; we record the blunt constants `1/2` instead of optimizing
      -- them.  This is much simpler to feed to Green.
      have hη_le : η ≤ 1 / (100 * (Aangle+1)) := by
        have hpD : 1 ≤ (D+1)*(Aangle+1) := by
          nlinarith [hAangle, hD]
        dsimp [η, γ]
        have hden : 0 < (100:ℝ) * (Aangle+1) := by positivity
        calc
          (1 / (100 * (Aangle+1))) / ((D+1)*(Aangle+1))
              ≤ (1 / (100 * (Aangle+1))) / 1 :=
                (div_le_div_of_nonneg_left (by positivity) (by norm_num) hpD)
          _ = _ := by ring
      have hθasmall : θa < (1/40 : ℝ) := by
        have hA1 : 0 < Aangle + 1 := by linarith
        have htw : 0 < (2*Aangle+1) := by linarith
        have hle := mul_le_mul_of_nonneg_right hη_le (le_of_lt htw)
        have hcalc : (1 / (100 * (Aangle+1))) * (2*Aangle+1)
              < (1/40 : ℝ) := by
          have hp : 0 < (100:ℝ) * (Aangle+1) := by positivity
          -- very wasteful (the true bound is `1/50`).
          calc
            (1 / (100 * (Aangle+1))) * (2*Aangle+1) =
                (2*Aangle+1) / (100*(Aangle+1)) := by ring
            _ < (1/40 : ℝ) := (div_lt_iff₀ hp).2 (by nlinarith)
        have hle' : θa ≤ (1 / (100 * (Aangle+1))) * (2*Aangle+1) := by
          dsimp [θa]
          exact hle
        exact lt_of_le_of_lt hle' hcalc
      have hθa1 : θa < 1 := lt_trans hθasmall (by norm_num)
      have hcc_le : cc ≤ 1 / (100*(Aangle+1)) := by
        have hh : cc < 1 / (100*(Aangle+1)) := by
          simpa [γ] using hm
        exact le_of_lt hh
      have hplus_a : (1+θa) * cc ≤ (1/2 : ℝ) := by
        have ht : θa ≤ (1/40 : ℝ) := le_of_lt hθasmall
        have hcA : 0 < Aangle+1 := by linarith
        have hden : 0 < (100:ℝ) * (Aangle+1) := by positivity
        have hc0' := hcc0
        have hcalc40 : (1+(1/40:ℝ)) *
            (1/(100*(Aangle+1))) < (1/2:ℝ) := by
          -- at `A=0` it is already about .01
          have : (1:ℝ) ≤ Aangle+1 := by linarith
          exact by
            calc
              (1+(1/40:ℝ)) * (1/(100*(Aangle+1)))
                  ≤ (1+(1/40:ℝ)) * (1/100) := by
                    have hsmall : 1/(100*(Aangle+1)) ≤ (1/100:ℝ) := by
                      apply (div_le_div_iff_of_pos_left (by norm_num)
                        (by positivity) (by norm_num)).2
                      nlinarith
                    exact mul_le_mul_of_nonneg_left hsmall (by norm_num)
              _ < (1/2:ℝ) := by norm_num
        calc
          (1+θa)*cc ≤ (1+(1/40:ℝ))*cc :=
            mul_le_mul_of_nonneg_right (by linarith) hcc0
          _ ≤ (1+(1/40:ℝ)) * (1/(100*(Aangle+1))) :=
            mul_le_mul_of_nonneg_left hcc_le (by norm_num)
          _ ≤ (1/2:ℝ) := le_of_lt hcalc40
      have hminus_a : (1/(1-θa))*cc ≤ (1/2 : ℝ) := by
        have ht : θa ≤ (1/40 : ℝ) := le_of_lt hθasmall
        have hθpos : 0 < 1-θa := sub_pos.mpr hθa1
        have hbnd : 1/(1-θa) ≤ (40/39:ℝ) := by
          apply (div_le_iff₀ hθpos).2
          -- multiply out, using `θ ≤ 1/40`
          nlinarith
        have hcalc : (40/39:ℝ) * (1/(100*(Aangle+1))) < (1/2:ℝ) := by
          have hsmall : 1/(100*(Aangle+1)) ≤ (1/100:ℝ) := by
            apply (div_le_div_iff_of_pos_left (by norm_num)
              (by positivity) (by norm_num)).2
            nlinarith [hAangle]
          calc
            (40/39:ℝ)*(1/(100*(Aangle+1))) ≤ (40/39:ℝ)*(1/100) :=
              mul_le_mul_of_nonneg_left hsmall (by norm_num)
            _ < (1/2:ℝ) := by norm_num
        calc
          (1/(1-θa))*cc ≤ (40/39:ℝ)*cc :=
            mul_le_mul_of_nonneg_right hbnd hcc0
          _ ≤ (40/39:ℝ) * (1/(100*(Aangle+1))) :=
            mul_le_mul_of_nonneg_left hcc_le (by norm_num)
          _ ≤ (1/2:ℝ) := le_of_lt hcalc
      have hpa (k : ℕ) (v : E d) : ‖pa k v‖ ≤ Aangle * ‖v‖ := by
        exact hPnorm (aa (m*k)) (haa (m*k)) v
      have hqa (k : ℕ) (v : E d) : ‖v-pa k v‖ ≤ Aangle * ‖v‖ := by
        exact hPother_norm (aa (m*k)) (haa (m*k)) v
      have hra (k : ℕ) (v : E d) : ‖ra k v‖ ≤ Aangle * ‖v‖ := by
        exact hPnorm _ (hiter (aa (m*k)) (haa (m*k)) m) v
      have hppa (k : ℕ) (v : E d) : pa k (pa k v) = pa k v := by
        exact hPid (aa (m*k)) (haa (m*k)) _
          (hPmem (aa (m*k)) (haa (m*k)) v)
      have hrra (k : ℕ) (v : E d) : ra k (ra k v) = ra k v := by
        exact hPid _ (hiter (aa (m*k)) (haa (m*k)) m) _
          (hPmem _ (hiter (aa (m*k)) (haa (m*k)) m) v)
      have hpa_close (k : ℕ) (v : E d) :
          ‖pa (k+1) v - ra k v‖ ≤ η * ‖v‖ := by
        rw [norm_sub_rev]
        exact hjoin_proj k v
      have hsta (k : ℕ) (v : E d) (hv : pa k v = v) :
          ra k (La k v) = La k v ∧ ‖La k v‖ ≤ cc * ‖v‖ := by
        have hvS : v ∈ H.stable (aa (m*k)) := by
          have hh := hPmem (aa (m*k)) (haa (m*k)) v
          change P (aa (m*k)) (haa (m*k)) v = v at hv
          rw [hv] at hh
          exact hh
        have hLS : fderiv ℝ ((T : E d → E d)^[m]) (aa (m*k)) v ∈
              H.stable (((T : E d → E d)^[m]) (aa (m*k))) := by
          rw [← hsiter m (aa (m*k)) (haa (m*k))]
          exact Submodule.mem_map_of_mem hvS
        constructor
        · exact hPid _ (hiter (aa (m*k)) (haa (m*k)) m) _ hLS
        · exact H.contract_stable _ (haa (m*k)) v hvS m
      have hLua (k : ℕ) (v : E d) (hv : pa k v = 0) :
          ra k (La k v) = 0 := by
        have hvU : v ∈ H.unstable (aa (m*k)) := by
          have hh := hPother (aa (m*k)) (haa (m*k)) v
          change P (aa (m*k)) (haa (m*k)) v = 0 at hv
          simpa [hv] using hh
        have huM : fderiv ℝ ((T : E d → E d)^[m]) (aa (m*k)) v ∈
            H.unstable (((T : E d → E d)^[m]) (aa (m*k))) := by
          rw [← hupiter m (aa (m*k)) (haa (m*k))]
          exact Submodule.mem_map_of_mem hvU
        exact hPzero _ (hiter (aa (m*k)) (haa (m*k)) m) _ huM
      have hBua (k : ℕ) (v : E d) (hv : ra k v = 0) :
          pa k (Ba k v) = 0 ∧ ‖Ba k v‖ ≤ cc * ‖v‖ := by
        have hz' := hiter (aa (m*k)) (haa (m*k)) m
        have hvU : v ∈ H.unstable
              (((T : E d → E d)^[m]) (aa (m*k))) := by
          have hh := hPother _ hz' v
          change P (((T : E d → E d)^[m]) (aa (m*k))) hz' v = 0 at hv
          simpa [hv] using hh
        have hpre_eq :
            ((T.symm : E d → E d)^[m])
              (((T : E d → E d)^[m]) (aa (m*k))) = aa (m*k) :=
          ShadowingFoundation.iterate_symm_apply_iterate T m _
        have hvB : fderiv ℝ ((T.symm : E d → E d)^[m])
              (((T : E d → E d)^[m]) (aa (m*k))) v ∈
              H.unstable (aa (m*k)) := by
          have hh : fderiv ℝ ((T.symm : E d → E d)^[m])
              (((T : E d → E d)^[m]) (aa (m*k))) v ∈
              H.unstable (((T.symm : E d → E d)^[m])
                (((T : E d → E d)^[m]) (aa (m*k)))) := by
            rw [← hupreiter m _ hz']
            exact Submodule.mem_map_of_mem hvU
          simpa only [hpre_eq] using hh
        constructor
        · exact hPzero (aa (m*k)) (haa (m*k)) _ hvB
        · exact H.contract_unstable _ hz' v hvU m
      have hlefta (k : ℕ) (v : E d) (hv : ra k v = 0) :
          La k (Ba k v) = v := by
        change fderiv ℝ ((T : E d → E d)^[m]) (aa (m*k))
              (fderiv ℝ ((T.symm : E d → E d)^[m])
                (((T : E d → E d)^[m]) (aa (m*k))) v) = v
        have hpre_eq : ((T.symm : E d → E d)^[m])
              (((T : E d → E d)^[m]) (aa (m*k))) = aa (m*k) :=
            ShadowingFoundation.iterate_symm_apply_iterate T m _
        simpa [hpre_eq] using
          (ShadowingFoundation.fderiv_iter_apply_fderiv_symmIter
            (f := T) hf hg m (((T : E d → E d)^[m]) (aa (m*k))) v)
      have hrighta (k : ℕ) (v : E d) (hv : pa k v = 0) :
          Ba k (La k v) = v := by
        exact ShadowingFoundation.fderiv_symmIter_apply_fderivIter
          (f := T) hf hg m (aa (m*k)) v
      have hgreen_broken_lin :
          ∃ Lt : ℕ → E d →L[ℝ] E d,
            (∀ n v, ‖Lt n v - La n v‖ ≤ θa * ‖La n v‖) ∧
            ∃ GG : (BoundedContinuousFunction ℕ (E d)) →
                    (BoundedContinuousFunction ℕ (E d)),
              (∀ w n, GG w (n+1) - Lt n (GG w n) = w n) ∧
              (∀ w, pa 0 (GG w 0) = 0) ∧
              (∀ w, ‖GG w‖ ≤ 2 * (Aangle * ‖w‖ / (1-(1/2:ℝ)))) ∧
              (∀ u v, ‖GG u - GG v‖ ≤
                2 * (Aangle * ‖u-v‖ / (1-(1/2:ℝ)))) := by
        exact ShadowingPerturb.exists_green_solver_transport
          (p := pa) (r := ra) (L := La) (B := Ba)
          (A := Aangle) (c := cc) (e := η) (θ := θa) (c' := (1/2:ℝ))
          (le_of_lt hAangle) hcc0 (le_of_lt hη) rfl hθa0 hθa1
          (by norm_num) (by norm_num)
          hplus_a hminus_a hpa hqa hra hppa hrra hpa_close
          hsta hLua hBua hlefta hrighta
      -- `hjoin_proj` is the missing off-diagonal term.  Transport the
      -- complement along it (or use `changeProj`/`inverse_of_almost_id`),
      -- then feed the resulting small Lipschitz remainder to
      -- `hgreen_fixed_exact` for the block sequence.
      rcases hgreen_broken_lin with ⟨Lt, hLt, GG, hGGrec, hGG0, hGGb, hGGl⟩
      let xb : ℕ → E d := fun k => xx (m*k)
      have hxbmem (k : ℕ) : xb k ∈ Ct := hxCt (m*k) xx hxx
      have hdef (k : ℕ) :
          ‖((T : E d → E d)^[m]) (xb k) - xb (k+1)‖ < b0 := by
        let u : ℕ → E d := fun i => xx (m*k+i)
        have hu0 : u 0 = xb k := by simp [u, xb]
        have hstep : ∀ j, ‖u (j+1) - T (u j)‖ < ee := by
          intro j
          dsimp [u]
          exact lt_of_lt_of_le (by simpa [add_assoc] using hpx (m*k+j)) heps_ee
        have hh := hpall (xb k) (hxbmem k) u hu0 hstep m (le_rfl)
        have hmadd : m*k + m = m*(k+1) := by ring
        dsimp [u] at hh
        rw [hmadd] at hh
        simpa [xb, norm_sub_rev] using hh
      let dn : ℕ → E d := fun k =>
        ((T : E d → E d)^[m]) (xb k) - xb (k+1)
      have hdn (k : ℕ) : ‖dn k‖ ≤ b0 := le_of_lt (hdef k)
      let rrn : ℕ → E d → E d := fun k v =>
        (((T : E d → E d)^[m]) (xb k + v) -
            ((T : E d → E d)^[m]) (xb k)) - La k v
      have hrr0 (k : ℕ) : rrn k 0 = 0 := by simp [rrn]
      have hrrLip (k : ℕ) (u v : E d)
          (hu : ‖u‖ ≤ t0) (hv : ‖v‖ ≤ t0) :
          ‖rrn k u - rrn k v‖ ≤ η * ‖u-v‖ := by
        have hxu : ‖(xb k + u) - aa (m*k)‖ < r := by
          have htri : ‖(xb k + u) - aa (m*k)‖ ≤
                ‖xb k - aa (m*k)‖ + ‖u‖ := by
            have heq : (xb k + u) - aa (m*k) =
                  (xb k - aa (m*k)) + u := by abel
            rw [heq]
            exact norm_add_le _ _
          have hbase : ‖xb k - aa (m*k)‖ < R := by
            simpa [xb] using hxaa (m*k)
          exact lt_of_le_of_lt htri (by nlinarith [ht_r])
        have hxv : ‖(xb k + v) - aa (m*k)‖ < r := by
          have htri : ‖(xb k + v) - aa (m*k)‖ ≤
                ‖xb k - aa (m*k)‖ + ‖v‖ := by
            have heq : (xb k + v) - aa (m*k) =
                  (xb k - aa (m*k)) + v := by abel
            rw [heq]
            exact norm_add_le _ _
          have hbase : ‖xb k - aa (m*k)‖ < R := by
            simpa [xb] using hxaa (m*k)
          exact lt_of_le_of_lt htri (by nlinarith [ht_r])
        have hh := hrLip (aa (m*k)) (haa (m*k))
              (xb k + u) (xb k + v) hxu hxv
        -- the base remainder at `xb` cancels
        change ‖rrn k u - rrn k v‖ ≤ _
        dsimp [rrn]
        dsimp [La]
        have heq :
            ((((T : E d → E d)^[m]) (xb k + u) -
              ((T : E d → E d)^[m]) (xb k) -
              fderiv ℝ ((T : E d → E d)^[m]) (aa (m*k)) u) -
             (((T : E d → E d)^[m]) (xb k + v) -
              ((T : E d → E d)^[m]) (xb k) -
              fderiv ℝ ((T : E d → E d)^[m]) (aa (m*k)) v)) =
            ((((T : E d → E d)^[m]) (xb k + u) -
                ((T : E d → E d)^[m]) (aa (m*k)) -
                fderiv ℝ ((T : E d → E d)^[m]) (aa (m*k))
                  ((xb k + u) - aa (m*k))) -
             (((T : E d → E d)^[m]) (xb k + v) -
                ((T : E d → E d)^[m]) (aa (m*k)) -
                fderiv ℝ ((T : E d → E d)^[m]) (aa (m*k))
                  ((xb k + v) - aa (m*k)))) := by
              rw [map_sub, map_add, map_sub, map_add]
              -- linearity moves the common `xb-aa` out
              abel
        rw [heq]
        have h := hh
        convert h using 1
        congr 1
        abel
      let Qn : ℕ → E d →L[ℝ] E d := fun k => La k - Lt k
      have hQn (k : ℕ) (v : E d) :
          ‖Qn k v‖ ≤ (θa * D) * ‖v‖ := by
        have hclose := hLt k v
        have hdb := hDb (aa (m*k)) (haa (m*k)) v
        change ‖(La k - Lt k) v‖ ≤ _
        rw [ContinuousLinearMap.sub_apply, norm_sub_rev]
        calc
          ‖Lt k v - La k v‖ ≤ θa * ‖La k v‖ := hclose
          _ ≤ θa * (D * ‖v‖) :=
            mul_le_mul_of_nonneg_left hdb hθa0
          _ = (θa * D) * ‖v‖ := by ring
      have hl0 : 0 ≤ θa * D := mul_nonneg hθa0 (le_of_lt hD)
      obtain ⟨WW, hWW, hWW0, hWWlip⟩ :=
        ShadowingPerturb.make_clipped_remainder (F:=E d)
          t0 b0 η (θa*D) ht0 (le_of_lt hb0) (le_of_lt hη) hl0
          dn rrn Qn hdn hrr0 hrrLip hQn
      let M0 : ℝ := 4*Aangle
      have hM0p : 0 ≤ M0 := by dsimp [M0]; linarith
      have hGGb' : ∀ w, ‖GG w‖ ≤ M0 * ‖w‖ := by
        intro w
        convert hGGb w using 1 <;> norm_num [M0] <;> ring
      have hGGl' : ∀ u v, ‖GG u - GG v‖ ≤ M0 * ‖u-v‖ := by
        intro u v
        convert hGGl u v using 1 <;> norm_num [M0] <;> ring
      let kap : ℝ := 2*(η + θa*D)
      have hkap : 0 ≤ kap := by dsimp [kap]; positivity
      have hsmallkap : M0 * kap < 1 := by
        dsimp [M0, kap, θa, η, γ]
        have ha : 0 < Aangle+1 := by linarith
        have hd : 0 < D+1 := by linarith
        -- generous constants: this is below sixteen percent
        field_simp
        nlinarith [hAangle, hD, mul_pos ha hd]
      obtain ⟨ef, hef, hefbd⟩ :=
        ShadowingPerturb.exists_fixed_of_lipschitz (F:=E d)
          GG M0 hM0p hGGb' hGGl' WW kap hkap
          (by simpa [kap] using hWWlip)
          hsmallkap
      let M0 : ℝ := 4*Aangle
      have hM0p : 0 ≤ M0 := by dsimp [M0]; linarith
      have hGGb' : ∀ w, ‖GG w‖ ≤ M0 * ‖w‖ := by
        intro w
        convert hGGb w using 1 <;> norm_num [M0] <;> ring
      have hGGl' : ∀ u v, ‖GG u - GG v‖ ≤ M0 * ‖u-v‖ := by
        intro u v
        convert hGGl u v using 1 <;> norm_num [M0] <;> ring
      let kap : ℝ := 2*(η + θa*D)
      have hkap : 0 ≤ kap := by dsimp [kap]; positivity
      have hsmallkap : M0 * kap < 1 := by
        dsimp [M0, kap, θa, η, γ]
        have ha : 0 < Aangle+1 := by linarith
        have hd : 0 < D+1 := by linarith
        -- generous constants: this is below sixteen percent
        field_simp
        nlinarith [hAangle, hD, mul_pos ha hd]
      obtain ⟨ef, hef, hefbd⟩ :=
        ShadowingPerturb.exists_fixed_of_lipschitz (F:=E d)
          GG M0 hM0p hGGb' hGGl' WW kap hkap
          (by simpa [kap] using hWWlip)
          hsmallkap
      have hqhalf : M0 * kap < (1/2:ℝ) := by
        dsimp [M0, kap, θa, η, γ]
        have ha : 0 < Aangle+1 := by linarith
        have hd : 0 < D+1 := by linarith
        field_simp
        nlinarith [hAangle, hD, mul_pos ha hd]
      have hdenkap : 0 < 1-M0*kap := sub_pos.mpr hsmallkap
      have hefbd' : ‖ef‖ ≤ (M0/(1-M0*kap))*b0 :=
        (hefbd.trans
          (mul_le_mul_of_nonneg_left hWW0
            (div_nonneg hM0p (le_of_lt hdenkap))))
      have helt : ‖ef‖ < t0 := by
        have hMq : M0 ≤ 4*Aangle := by rfl
        have hfrac : M0/(1-M0*kap) ≤ 8*Aangle := by
          have hden2 : (1/2:ℝ) < 1-M0*kap := by linarith [hqhalf]
          dsimp [M0]
          rw [div_le_iff₀ hdenkap]
          nlinarith [hAangle]
        have htbound : (8*Aangle)*b0 < t0 := by
          dsimp [b0]
          have ha : 0 < Aangle+1 := by linarith
          field_simp
          nlinarith [ht0, hAangle]
        exact lt_of_le_of_lt (hefbd'.trans
          (mul_le_mul_of_nonneg_right hfrac (le_of_lt hb0))) htbound
      have hepoint (n : ℕ) : ‖ef n‖ < t0 :=
        lt_of_le_of_lt (BoundedContinuousFunction.norm_coe_le_norm ef n) helt
      have heclip (n : ℕ) : ShadowingPerturb.clip t0 (ef n) = ef n :=
        ShadowingPerturb.clip_of_norm_le (le_of_lt (hepoint n))
      have hrecE (n : ℕ) :
          ef (n+1) - Lt n (ef n) = WW ef n := by
        have he1 : ef (n+1) = GG (WW ef) (n+1) :=
          congrArg (fun u : BoundedContinuousFunction ℕ (E d) => u (n+1)) hef
        have he0' : ef n = GG (WW ef) n :=
          congrArg (fun u : BoundedContinuousFunction ℕ (E d) => u n) hef
        calc
          ef (n+1) - Lt n (ef n) =
              GG (WW ef) (n+1) - Lt n (GG (WW ef) n) := by rw [he1, he0']
          _ = WW ef n := hGGrec (WW ef) n
      have htrueblock (n : ℕ) :
          xb (n+1) + ef (n+1) =
            ((T : E d → E d)^[m]) (xb n + ef n) := by
        have hh := hrecE n
        rw [hWW ef n, heclip n] at hh
        change ef (n+1) - Lt n (ef n) =
          (((T : E d → E d)^[m]) (xb n) - xb (n+1)) +
            ((((T : E d → E d)^[m]) (xb n + ef n) -
                ((T : E d → E d)^[m]) (xb n)) - La n (ef n)) +
              ((La n - Lt n) (ef n)) at hh
        rw [ContinuousLinearMap.sub_apply] at hh
        -- all linear terms cancel
        have hres : xb (n+1) + ef (n+1) =
            ((T : E d → E d)^[m]) (xb n + ef n) := by
          calc
            xb (n+1) + ef (n+1) =
                xb (n+1) + (ef (n+1) - Lt n (ef n)) + Lt n (ef n) := by abel
            _ = xb (n+1) +
                  ((((T : E d → E d)^[m]) (xb n) - xb (n+1)) +
                    ((((T : E d → E d)^[m]) (xb n + ef n) -
                        ((T : E d → E d)^[m]) (xb n)) - La n (ef n)) +
                      ((La n) (ef n) - (Lt n) (ef n))) + Lt n (ef n) := by rw [hh]
            _ = ((T : E d → E d)^[m]) (xb n + ef n) := by abel
        exact hres
      let y : E d := xb 0 + ef 0
      have hyblock (k : ℕ) :
          ((((T : E d → E d)^[m])^[k])) y = xb k + ef k := by
        induction k with
        | zero => simp [y]
        | succ k ih =>
            rw [Function.iterate_succ_apply', ih]
            exact (htrueblock k).symm
      have hyTblock (k : ℕ) :
          ((T : E d → E d)^[m*k]) y = xb k + ef k := by
        rw [Function.iterate_mul]
        exact hyblock k
      have hpblock (k i : ℕ) (hi : i ≤ m) :
          ‖xx (m*k + i) - ((T : E d → E d)^[i]) (xb k)‖ < b0 := by
        let u : ℕ → E d := fun j => xx (m*k+j)
        have hu0 : u 0 = xb k := by simp [u, xb]
        have hstep : ∀ j, ‖u (j+1) - T (u j)‖ < ee := by
          intro j
          dsimp [u]
          exact lt_of_lt_of_le (by simpa [add_assoc] using hpx (m*k+j)) heps_ee
        have hh := hpall (xb k) (hxbmem k) u hu0 hstep i hi
        simpa [u] using hh
      have hiterclose (k i : ℕ) (hi : i ≤ m) :
          ‖((T : E d → E d)^[i]) (xb k + ef k) -
              ((T : E d → E d)^[i]) (xb k)‖ < δ₀/4 := by
        have hstart : ‖(xb k + ef k) - xb k‖ < si := by
          have hp : ‖ef k‖ < t0 := hepoint k
          have hp' : ‖ef k‖ < si := lt_of_lt_of_le hp ht_i
          simpa using hp'
        exact hiteri (xb k) (hxbmem k) (xb k + ef k) hstart i hi
      have hbdsmall : b0 < δ₀/4 := by
        dsimp [b0]
        have ha : 0 < Aangle + 1 := by linarith
        have hdenb : 0 < (100:ℝ) * (Aangle+1) := by positivity
        apply (div_lt_iff₀ hdenb).2
        nlinarith [ht_del, hδ₀, hAangle]
      have hclose_block (k i : ℕ) (hi : i ≤ m) :
          ‖xx (m*k+i) - ((T : E d → E d)^[m*k+i]) y‖ < δ₀ := by
        have hi1 := hpblock k i hi
        have hi2' := hiterclose k i hi
        have hi2 : ‖((T : E d → E d)^[i]) (xb k) -
              ((T : E d → E d)^[i]) (xb k + ef k)‖ < δ₀/4 := by
          rwa [norm_sub_rev]
        have hyi : ((T : E d → E d)^[m*k+i]) y =
            ((T : E d → E d)^[i]) (xb k + ef k) := by
          calc
            ((T : E d → E d)^[m*k+i]) y =
                ((T : E d → E d)^[i])
                  (((T : E d → E d)^[m*k]) y) := by
                    simpa [Nat.add_comm] using
                      (Function.iterate_add_apply (T : E d → E d) i (m*k) y)
            _ = ((T : E d → E d)^[i]) (xb k + ef k) := by
              rw [hyTblock k]
        rw [hyi]
        calc
          ‖xx (m*k+i) - ((T : E d → E d)^[i]) (xb k + ef k)‖
              ≤ ‖xx (m*k+i) - ((T : E d → E d)^[i]) (xb k)‖ +
                ‖((T : E d → E d)^[i]) (xb k) -
                  ((T : E d → E d)^[i]) (xb k + ef k)‖ := by
                    have heq : xx (m*k+i) -
                          ((T : E d → E d)^[i]) (xb k + ef k) =
                        (xx (m*k+i) - ((T : E d → E d)^[i]) (xb k)) +
                          (((T : E d → E d)^[i]) (xb k) -
                            ((T : E d → E d)^[i]) (xb k + ef k)) := by abel
                    rw [heq]
                    exact norm_add_le _ _
          _ < δ₀ := by linarith
      refine ⟨y, ?_⟩
      intro n
      let k : ℕ := n / m
      let i : ℕ := n % m
      have hil : i < m := by
        dsimp [i]
        exact Nat.mod_lt _ hmpos
      have hi : i ≤ m := Nat.le_of_lt hil
      have hsplit : m*k+i = n := by
        dsimp [k, i]
        simpa [Nat.add_comm] using (Nat.mod_add_div n m)
      have hfin := hclose_block k i hi
      rw [hsplit] at hfin
      exact hfin
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
