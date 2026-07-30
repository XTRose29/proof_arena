import ChallengeDeps
import Mathlib
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Polynomial.CauchyBound

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/Circle.lean
section

namespace KnotSupport

noncomputable section

abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- the standard parametrized unit circle, with redundant zero coordinate -/
def circleVec (t : ℝ) (i : Fin 3) : ℝ :=
  if i = (0 : Fin 3) then Real.cos t
  else if i = (1 : Fin 3) then Real.sin t
  else 0

def circle (t : ℝ) : R3 :=
  WithLp.toLp 2 (circleVec t)

lemma circle_apply (t : ℝ) (i : Fin 3) : (circle t).ofLp i = circleVec t i := rfl

lemma circle_zero (t : ℝ) : (circle t).ofLp (0 : Fin 3) = Real.cos t := by
  simp [circle, circleVec]
lemma circle_one (t : ℝ) : (circle t).ofLp (1 : Fin 3) = Real.sin t := by
  simp [circle, circleVec]

lemma circle_smooth : ContDiff ℝ (⊤ : ℕ∞) circle := by
  unfold circle
  -- smoothness can be checked componentwise on a finite product
  rw [contDiff_piLp]
  intro i
  -- after the `toLp`, this is just one of three scalar functions
  change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => circleVec t i)
  unfold circleVec
  split_ifs <;> fun_prop

lemma circle_periodic (t : ℝ) : circle (t + 2 * Real.pi) = circle t := by
  -- coordinates of a PiLp determine it
  apply (PiLp.continuousLinearEquiv (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ)).injective
  funext i
  -- `ofLp` of our vector is the vector itself
  change (circleVec (t + 2 * Real.pi) i) = circleVec t i
  unfold circleVec
  split_ifs <;> simp [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The cosine/sine pair is injective on `[0,2π)`.  Stated for later
    use in the injectivity of `circle`. -/
lemma cos_sin_inj_Ico {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (hc : Real.cos s = Real.cos t)
    (hn : Real.sin s = Real.sin t) : s = t := by
  have ha : (s : Real.Angle) = (t : Real.Angle) :=
    Real.Angle.cos_sin_inj hc hn
  have hh : ∃ k : ℤ, s - t = 2 * Real.pi * k :=
    (Real.Angle.angle_eq_iff_two_pi_dvd_sub).1 ha
  rcases hh with ⟨k, hk⟩
  have hT : 0 < (2 * Real.pi : ℝ) := Real.two_pi_pos
  have hlow : -(2 * Real.pi) < s - t := by linarith [hs.1, ht.2]
  have hupp : s - t < (2 * Real.pi) := by linarith [hs.2, ht.1]
  have klow : (-1 : ℝ) < (k : ℝ) := by
    -- divide by the positive period
    nlinarith
  have kupp : (k : ℝ) < 1 := by
    nlinarith
  have klow' : (-1 : ℤ) < k := by exact_mod_cast klow
  have kupp' : k < (1 : ℤ) := by exact_mod_cast kupp
  have kz : k = 0 := by omega
  have hst : s - t = 0 := by simpa [kz] using hk
  linarith

lemma circle_injOn : Set.InjOn circle (Set.Ico (0 : ℝ) (2 * Real.pi)) := by
  intro s hs t ht h
  have h0 := congrArg (fun q : R3 => q.ofLp (0 : Fin 3)) h
  have h1 := congrArg (fun q : R3 => q.ofLp (1 : Fin 3)) h
  change Real.cos s = Real.cos t at h0
  change Real.sin s = Real.sin t at h1
  exact cos_sin_inj_Ico hs ht h0 h1

/-- The derivative of the circle is nowhere zero.  Proving this through
coordinate projections avoids any choice of norm on the finite product. -/
lemma circle_immersion (t : ℝ) : deriv circle t ≠ 0 := by
  intro hz
  have hdiff : DifferentiableAt ℝ circle t :=
    (circle_smooth.differentiable (by simp)).differentiableAt
  have hd : HasDerivAt circle (deriv circle t) t := hdiff.hasDerivAt
  -- apply the two coordinate projections to this derivative
  let p0 : R3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  let p1 : R3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3)
  have hcomp0 : HasDerivAt (p0 ∘ circle) (p0 (deriv circle t)) t :=
    (p0.hasFDerivAt).comp_hasDerivAt t hd
  have hcomp1 : HasDerivAt (p1 ∘ circle) (p1 (deriv circle t)) t :=
    (p1.hasFDerivAt).comp_hasDerivAt t hd
  have hcomp0' : HasDerivAt (fun x : ℝ => Real.cos x) (p0 (deriv circle t)) t := by
    simpa [p0, Function.comp_def, circle, circleVec] using hcomp0
  have hcomp1' : HasDerivAt (fun x : ℝ => Real.sin x) (p1 (deriv circle t)) t := by
    simpa [p1, Function.comp_def, circle, circleVec] using hcomp1
  have hv0 : p0 (deriv circle t) = -Real.sin t :=
    hcomp0'.unique (Real.hasDerivAt_cos t)
  have hv1 : p1 (deriv circle t) = Real.cos t :=
    hcomp1'.unique (Real.hasDerivAt_sin t)
  have hs : Real.sin t = 0 := by
    have z : p0 (deriv circle t) = 0 := by rw [hz]; rfl
    linarith
  have hc : Real.cos t = 0 := by
    have z : p1 (deriv circle t) = 0 := by rw [hz]; rfl
    linarith
  have hunit := Real.sin_sq_add_cos_sq t
  rw [hs, hc] at hunit
  norm_num at hunit


end

end KnotSupport

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/Circle.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/Complement.lean
section

namespace KnotSupport

/-- A homeomorphism of ambient spaces taking `A` onto `B` restricts to a
homeomorphism of their complements. Speaks only about the elementary
`MapsTo` formulation so it can be used before packaging the ambient map as
`Homeomorph`. -/
def complementHomeomorph {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → Y) (G : Y → X) (A : Set X) (B : Set Y)
    (l : ∀ x, G (F x) = x) (r : ∀ y, F (G y) = y)
    (hF : Continuous F) (hG : Continuous G)
    (mF : Set.MapsTo F A B) (mG : Set.MapsTo G B A) :
    (Aᶜ : Set X) ≃ₜ (Bᶜ : Set Y) := by
  have cF : ∀ x : X, x ∈ Aᶜ → F x ∈ Bᶜ := by
    intro x hx hxb
    have hxA := mG hxb
    have hnot : x ∉ A := by simpa using hx
    exact hnot ((l x) ▸ hxA)
  have cG : ∀ y : Y, y ∈ Bᶜ → G y ∈ Aᶜ := by
    intro y hy hya
    have hyB := mF hya
    have hnot : y ∉ B := by simpa using hy
    exact hnot ((r y) ▸ hyB)
  let f : (Aᶜ : Set X) → (Bᶜ : Set Y) :=
    fun z => ⟨F z, cF z z.property⟩
  let g : (Bᶜ : Set Y) → (Aᶜ : Set X) :=
    fun z => ⟨G z, cG z z.property⟩
  have lf : ∀ x, g (f x) = x := by
    intro x
    apply Subtype.ext
    exact l x
  have rg : ∀ y, f (g y) = y := by
    intro y
    apply Subtype.ext
    exact r y
  exact
    { toFun := f
      invFun := g
      left_inv := lf
      right_inv := rg
      continuous_toFun := by
        exact (hF.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := by
        exact (hG.comp continuous_subtype_val).subtype_mk _ }

end KnotSupport

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/Complement.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/Fundamental.lean
section
/-! Some very small invariant lemmas about the invariant we use below.

`FundamentalGroup` in mathlib is the vertex group of the fundamental
groupoid.  We use the proposition that all vertex groups are abelian.  Keeping
it a predicate rather than a type class is handy: no choice of a base point of
an (open) complement ever enters the statements.  In particular this eliminates
the usual harmless but rather painful change-of-base-point bookkeeping.
-/
noncomputable section
open CategoryTheory
open scoped FundamentalGroupoid
namespace KnotSupport

/-- All fundamental groups of `X`, at all basepoints, are abelian. -/
def FGAbelian (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (p q : FundamentalGroup X x), p * q = q * p

/-- It is important here to use the vertex group, rather than a chosen
presentation of loops.  A homeomorphism is an equivalence of fundamental
groupoids, in particular it is *full* on the endomorphisms of the image of an
object.  Thus it is onto on vertex groups.  This little argument is independent
of path connectedness and of base points. -/
theorem FGAbelian.homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (h : FGAbelian X) : FGAbelian Y := by
  intro y
  rcases e.surjective y with ⟨x, rfl⟩
  intro p q
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.toHomotopyEquiv
  let f : C(X,Y) := ⟨e, e.continuous⟩
  have sur : Function.Surjective (FundamentalGroup.map f x) := by
    intro r
    -- `equivOfHomotopyEquiv` uses this very continuous map as its
    -- underlying functor.  A functor in an equivalence is full.
    exact E.functor.map_surjective r
  rcases sur p with ⟨a, ha⟩
  rcases sur q with ⟨b, hb⟩
  calc
    p * q = (FundamentalGroup.map f x) a *
          (FundamentalGroup.map f x) b := by rw [ha, hb]
    _ = (FundamentalGroup.map f x) (a*b) := by rw [map_mul]
    _ = (FundamentalGroup.map f x) (b*a) := by rw [h x a b]
    _ = (FundamentalGroup.map f x) b *
          (FundamentalGroup.map f x) a := by rw [map_mul]
    _ = q * p := by rw [ha, hb]

/-- Separating complements can therefore be done with the very weak
invariant `FGAbelian`; no information about a base point is needed. -/
theorem no_homeomorph_of_FGAbelian {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (hX : FGAbelian X) (hY : ¬ FGAbelian Y) :
    ¬ Nonempty (X ≃ₜ Y) := by
  rintro ⟨e⟩
  exact hY (hX.homeomorph e)

end KnotSupport

namespace KnotSupport
open CategoryTheory
open scoped FundamentalGroupoid
/-- A convenient pointed form.  In a path connected space one can compute at
one point; this lemma only assumes the paths that are actually needed. -/
theorem FGAbelian_of_paths {X : Type*} [TopologicalSpace X]
    (x0 : X) (hp : ∀ x : X, Nonempty (Path x0 x))
    (h0 : ∀ a b : FundamentalGroup X x0, a*b=b*a) : FGAbelian X := by
  intro x a b
  rcases hp x with ⟨p⟩
  let E : FundamentalGroup X x0 ≃* FundamentalGroup X x :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath p
  rcases E.surjective a with ⟨a0, rfl⟩
  rcases E.surjective b with ⟨b0, rfl⟩
  simpa using congrArg E (h0 a0 b0)

/-- Conversely this base-point-free form of the invariant can be
refuted at any chosen point. -/
theorem not_FGAbelian_of_pair {X : Type*} [TopologicalSpace X]
    (x : X) (a b : FundamentalGroup X x) (h : a*b ≠ b*a) :
    ¬ FGAbelian X := by
  intro H
  exact h (H x a b)
end KnotSupport


namespace KnotSupport
open CategoryTheory
open scoped FundamentalGroupoid
/- The Eckmann--Hilton argument for a topological group, at its unit.
This avoids having to calculate the fundamental group of a circle separately
when a retract is given as a topological group.  Notice the annoying order of
`*` in a vertex group (`End.mul` is opposite categorical composition); this is
why the small `trans` calculation is made explicitly. -/
set_option maxHeartbeats 800000
variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
local notation "Q" => Path.Homotopic.Quotient (1:G) 1
theorem fundamentalGroup_one_comm (a b : FundamentalGroup G (1:G)) : a*b=b*a := by
  -- use quotient definitions
  change b ≫ a = a ≫ b
  change (b.trans a) = (a.trans b)
  let m : C(G×G,G) := ⟨fun z => z.1*z.2, continuous_mul⟩
  let hh : m ((1:G),1) = 1 := by dsimp [m]; simp
  let M : FundamentalGroup (G×G) ((1:G),1) →*
        FundamentalGroup G 1 := FundamentalGroup.mapOfEq m hh
  let S : Q → Q → Q := fun p q => M (Path.Homotopic.prod p q)
  have SI (p : Q) : S p (.refl _) = p := by
    induction p using Quotient.inductionOn with | _ r => ?_
    change S (Path.Homotopic.Quotient.mk r)
      (Path.Homotopic.Quotient.mk (Path.refl (1:G))) = _
    dsimp [S]
    rw [← Path.Homotopic.Quotient.mk_refl]
    rw [Path.Homotopic.prod_lift]
    change M (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk _)) = _
    rw [FundamentalGroup.mapOfEq_apply]
    apply Path.Homotopic.Quotient.eq.mpr
    have peq : (((r.prod (Path.refl (1:G))).map
          (show Continuous (fun z : G×G => z.1*z.2) from continuous_mul)).cast
            (by simp) (by simp)) = r := by
      apply Path.ext
      funext t
      simp [Path.cast, Function.comp_def]
    convert Path.Homotopic.refl r using 1

  have IS (p : Q) : S (.refl _) p = p := by
    induction p using Quotient.inductionOn with | _ r => ?_
    change S (Path.Homotopic.Quotient.mk (Path.refl (1:G)))
      (Path.Homotopic.Quotient.mk r) = _
    dsimp [S]
    rw [← Path.Homotopic.Quotient.mk_refl]
    rw [Path.Homotopic.prod_lift]
    change M (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk _)) = _
    rw [FundamentalGroup.mapOfEq_apply]
    apply Path.Homotopic.Quotient.eq.mpr
    have peq : (((Path.refl (1:G)).prod r).map
          (show Continuous (fun z : G×G => z.1*z.2) from continuous_mul)).cast
            (by simp) (by simp) = r := by
      apply Path.ext
      funext t
      simp [Path.cast, Function.comp_def]
    convert Path.Homotopic.refl r using 1

  -- multiplication of quotients by a continuous map respects concatenation;
  -- use the monoid hom M to avoid casts.
  have inter (p q r s : Q) :
      (S p q).trans (S r s) = S (p.trans r) (q.trans s) := by
    -- since in an end group multiplication is opposite to trans,
    -- the monoid law gives this order too (using swapped operands)
    change (M (Path.Homotopic.prod p q)).trans
          (M (Path.Homotopic.prod r s)) = _
    change (M (Path.Homotopic.prod r s) *
          M (Path.Homotopic.prod p q)) = _
    rw [← M.map_mul]
    change M ((Path.Homotopic.prod p q).trans
          (Path.Homotopic.prod r s)) = _
    rw [Path.Homotopic.comp_prod_eq_prod_comp]
  -- Eckmann--Hilton
  let e0 : Q := Path.Homotopic.Quotient.refl (1:G)
  calc
    b.trans a = (S b e0).trans (S e0 a) := by rw [SI, IS]
    _ = S (b.trans e0) (e0.trans a) := inter _ _ _ _
    _ = S b a := by rw [Path.Homotopic.Quotient.trans_refl,
          Path.Homotopic.Quotient.refl_trans]
    _ = S (e0.trans b) (a.trans e0) := by
          rw [Path.Homotopic.Quotient.refl_trans,
             Path.Homotopic.Quotient.trans_refl]
    _ = (S e0 a).trans (S b e0) :=
          (inter _ _ _ _).symm
    _ = a.trans b := by rw [SI, IS]

end KnotSupport

end

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/Fundamental.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/Trefoil.lean
section

namespace KnotSupport
noncomputable section

/-- The $(2,3)$ curve on the standard torus of major radius `2`.
    Meridian angle is `2 t` and longitude angle is `3 t`. -/
def torVec (t : ℝ) (i : Fin 3) : ℝ :=
  if i = (0 : Fin 3) then (2 + Real.cos (2*t)) * Real.cos (3*t)
  else if i = (1 : Fin 3) then (2 + Real.cos (2*t)) * Real.sin (3*t)
  else Real.sin (2*t)

def trefoil (t : ℝ) : R3 := WithLp.toLp 2 (torVec t)

@[simp] lemma trefoil_zero (t : ℝ) :
    (trefoil t).ofLp (0 : Fin 3) = (2 + Real.cos (2*t)) * Real.cos (3*t) := by
  simp [trefoil, torVec]
@[simp] lemma trefoil_one (t : ℝ) :
    (trefoil t).ofLp (1 : Fin 3) = (2 + Real.cos (2*t)) * Real.sin (3*t) := by
  simp [trefoil, torVec]
@[simp] lemma trefoil_two (t : ℝ) :
    (trefoil t).ofLp (2 : Fin 3) = Real.sin (2*t) := by
  change torVec t (2 : Fin 3) = _
  simp [torVec, show (2:Fin 3) ≠ 0 by decide, show (2:Fin 3) ≠ 1 by decide]

lemma trefoil_smooth : ContDiff ℝ (⊤ : ℕ∞) trefoil := by
  unfold trefoil
  rw [contDiff_piLp]
  intro i
  change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => torVec t i)
  unfold torVec
  split_ifs <;> fun_prop

private lemma __Trefoil_sin2per (t : ℝ) : Real.sin (2 * (t + 2 * Real.pi)) = Real.sin (2*t) := by
  convert Real.sin_add_nat_mul_two_pi (2*t) 2 using 1
  norm_num
  congr 1 <;> ring
private lemma __Trefoil_cos2per (t : ℝ) : Real.cos (2 * (t + 2 * Real.pi)) = Real.cos (2*t) := by
  convert Real.cos_add_nat_mul_two_pi (2*t) 2 using 1
  norm_num
  congr 1 <;> ring
private lemma __Trefoil_sin3per (t : ℝ) : Real.sin (3 * (t + 2 * Real.pi)) = Real.sin (3*t) := by
  convert Real.sin_add_nat_mul_two_pi (3*t) 3 using 1
  norm_num
  congr 1 <;> ring
private lemma __Trefoil_cos3per (t : ℝ) : Real.cos (3 * (t + 2 * Real.pi)) = Real.cos (3*t) := by
  convert Real.cos_add_nat_mul_two_pi (3*t) 3 using 1
  norm_num
  congr 1 <;> ring

lemma trefoil_periodic (t : ℝ) : trefoil (t + 2*Real.pi) = trefoil t := by
  apply (PiLp.continuousLinearEquiv (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ)).injective
  funext i
  change torVec (t + 2*Real.pi) i = torVec t i
  unfold torVec
  split_ifs <;> simp [__Trefoil_sin2per, __Trefoil_cos2per, __Trefoil_sin3per, __Trefoil_cos3per]

private lemma __Trefoil_radial_pos (t : ℝ) : 0 < 2 + Real.cos (2*t) := by
  have h := Real.neg_one_le_cos (2*t)
  linarith

/-- Two congruences, of coprime frequencies 2 and 3, recover the
original parameter on the fundamental interval. -/
private lemma __Trefoil_two_three_inj {s t : ℝ} (hs : s ∈ Set.Ico (0:ℝ) (2*Real.pi))
    (ht : t ∈ Set.Ico (0:ℝ) (2*Real.pi))
    (h2c : Real.cos (2*s) = Real.cos (2*t))
    (h2s : Real.sin (2*s) = Real.sin (2*t))
    (h3c : Real.cos (3*s) = Real.cos (3*t))
    (h3s : Real.sin (3*s) = Real.sin (3*t)) : s = t := by
  have a2 : ((2*s : ℝ) : Real.Angle) = (2*t : ℝ) :=
    Real.Angle.cos_sin_inj h2c h2s
  have a3 : ((3*s : ℝ) : Real.Angle) = (3*t : ℝ) :=
    Real.Angle.cos_sin_inj h3c h3s
  rcases (Real.Angle.angle_eq_iff_two_pi_dvd_sub).1 a2 with ⟨k, hk⟩
  rcases (Real.Angle.angle_eq_iff_two_pi_dvd_sub).1 a3 with ⟨l, hl⟩
  have hd : ∃ n : ℤ, s - t = 2*Real.pi*n := by
    refine ⟨2*k-l, ?_⟩
    calc
      s-t = 2*(2*s-2*t) - (3*s-3*t) := by ring
      _ = 2*((2*Real.pi)*(k:ℝ)) - ((2*Real.pi)*(l:ℝ)) := by rw [hk, hl]
      _ = (2*Real.pi) * ( (2:ℝ)*(k:ℝ) - (l:ℝ)) := by ring
      _ = (2*Real.pi) * ( (↑(2*k-l) : ℤ) : ℝ) := by push_cast; ring
  rcases hd with ⟨n, hn⟩
  have hT : 0 < (2*Real.pi:ℝ) := Real.two_pi_pos
  have hlow : -(2*Real.pi) < s-t := by linarith [hs.1, ht.2]
  have hupp : s-t < (2*Real.pi) := by linarith [hs.2, ht.1]
  have nl : (-1:ℝ) < (n:ℝ) := by nlinarith
  have nu : (n:ℝ) < 1 := by nlinarith
  have nl' : (-1:ℤ) < n := by exact_mod_cast nl
  have nu' : n < (1:ℤ) := by exact_mod_cast nu
  have nz : n = 0 := by omega
  have : s-t=0 := by simpa [nz] using hn
  linarith

lemma trefoil_injOn : Set.InjOn trefoil (Set.Ico (0:ℝ) (2*Real.pi)) := by
  intro s hs t ht eqv
  have hx := congrArg (fun q : R3 => q.ofLp (0 : Fin 3)) eqv
  have hy := congrArg (fun q : R3 => q.ofLp (1 : Fin 3)) eqv
  have hz := congrArg (fun q : R3 => q.ofLp (2 : Fin 3)) eqv
  simp only [trefoil_zero] at hx
  simp only [trefoil_one] at hy
  simp only [trefoil_two] at hz
  have us := Real.sin_sq_add_cos_sq (3*s)
  have ut := Real.sin_sq_add_cos_sq (3*t)
  have urads : (2+Real.cos (2*s))^2 = (2+Real.cos (2*t))^2 := by
    calc
      (2+Real.cos (2*s))^2 = (2+Real.cos (2*s))^2 *
          (Real.sin (3*s)^2 + Real.cos (3*s)^2) := by rw [us]; ring
      _ = ((2+Real.cos (2*s))*Real.cos (3*s))^2 +
          ((2+Real.cos (2*s))*Real.sin (3*s))^2 := by ring
      _ = ((2+Real.cos (2*t))*Real.cos (3*t))^2 +
          ((2+Real.cos (2*t))*Real.sin (3*t))^2 := by rw [hx,hy]
      _ = (2+Real.cos (2*t))^2 *
          (Real.sin (3*t)^2 + Real.cos (3*t)^2) := by ring
      _ = (2+Real.cos (2*t))^2 := by rw [ut]; ring
  have rp : 0 < 2+Real.cos (2*s) := __Trefoil_radial_pos s
  have rq : 0 < 2+Real.cos (2*t) := __Trefoil_radial_pos t
  have rc : Real.cos (2*s) = Real.cos (2*t) := by
    have : 2+Real.cos (2*s) = 2+Real.cos (2*t) := by nlinarith
    linarith
  have c3 : Real.cos (3*s) = Real.cos (3*t) := by
    rw [rc] at hx
    nlinarith
  have s3 : Real.sin (3*s) = Real.sin (3*t) := by
    rw [rc] at hy
    nlinarith
  exact __Trefoil_two_three_inj hs ht rc hz c3 s3

/- short derivative computations for three coordinates -/
private lemma __Trefoil_hasD_sin2 (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (2*x)) (2*Real.cos (2*t)) t := by
  convert (Real.hasDerivAt_sin (2*t)).comp t
      (HasDerivAt.const_mul (2:ℝ) (hasDerivAt_id t)) using 1
  · rfl
  · rfl
  · simp [Function.comp_def]
  · ring

private lemma __Trefoil_hasD_cos2 (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (2*x)) (-2*Real.sin (2*t)) t := by
  convert (Real.hasDerivAt_cos (2*t)).comp t
      (HasDerivAt.const_mul (2:ℝ) (hasDerivAt_id t)) using 1
  · rfl
  · rfl
  · simp [Function.comp_def]
  · ring
private lemma __Trefoil_hasD_sin3 (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (3*x)) (3*Real.cos (3*t)) t := by
  convert (Real.hasDerivAt_sin (3*t)).comp t
      (HasDerivAt.const_mul (3:ℝ) (hasDerivAt_id t)) using 1
  · rfl
  · rfl
  · simp [Function.comp_def]
  · ring
private lemma __Trefoil_hasD_cos3 (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (3*x)) (-3*Real.sin (3*t)) t := by
  convert (Real.hasDerivAt_cos (3*t)).comp t
      (HasDerivAt.const_mul (3:ℝ) (hasDerivAt_id t)) using 1
  · rfl
  · rfl
  · simp [Function.comp_def]
  · ring
private lemma __Trefoil_hasD_x (t : ℝ) :
    HasDerivAt (fun x : ℝ => (2+Real.cos (2*x))*Real.cos (3*x))
      ((-2*Real.sin (2*t))*Real.cos (3*t) +
        (2+Real.cos (2*t))*(-3*Real.sin (3*t))) t := by
  convert ((__Trefoil_hasD_cos2 t).const_add 2).mul (__Trefoil_hasD_cos3 t) using 1
  · rfl
  · rfl
  · rfl
private lemma __Trefoil_hasD_y (t : ℝ) :
    HasDerivAt (fun x : ℝ => (2+Real.cos (2*x))*Real.sin (3*x))
      ((-2*Real.sin (2*t))*Real.sin (3*t) +
        (2+Real.cos (2*t))*(3*Real.cos (3*t))) t := by
  convert ((__Trefoil_hasD_cos2 t).const_add 2).mul (__Trefoil_hasD_sin3 t) using 1
  · rfl
  · rfl
  · rfl

lemma trefoil_immersion (t : ℝ) : deriv trefoil t ≠ 0 := by
  intro hzero
  have hdiff : DifferentiableAt ℝ trefoil t :=
    (trefoil_smooth.differentiable (by simp)).differentiableAt
  have hd : HasDerivAt trefoil (deriv trefoil t) t := hdiff.hasDerivAt
  let p0 : R3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  let p1 : R3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3)
  let p2 : R3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have d0 : HasDerivAt (p0 ∘ trefoil) (p0 (deriv trefoil t)) t :=
    (p0.hasFDerivAt).comp_hasDerivAt t hd
  have d1 : HasDerivAt (p1 ∘ trefoil) (p1 (deriv trefoil t)) t :=
    (p1.hasFDerivAt).comp_hasDerivAt t hd
  have d2 : HasDerivAt (p2 ∘ trefoil) (p2 (deriv trefoil t)) t :=
    (p2.hasFDerivAt).comp_hasDerivAt t hd
  have d0' : p0 (deriv trefoil t) =
        ((-2*Real.sin (2*t))*Real.cos (3*t) + (2+Real.cos (2*t))*(-3*Real.sin (3*t))) := by
    have : HasDerivAt (fun x : ℝ => (2+Real.cos (2*x))*Real.cos (3*x))
          (p0 (deriv trefoil t)) t := by
      simpa [p0, Function.comp_def] using d0
    exact this.unique (__Trefoil_hasD_x t)
  have d1' : p1 (deriv trefoil t) =
        ((-2*Real.sin (2*t))*Real.sin (3*t) + (2+Real.cos (2*t))*(3*Real.cos (3*t))) := by
    have : HasDerivAt (fun x : ℝ => (2+Real.cos (2*x))*Real.sin (3*x))
          (p1 (deriv trefoil t)) t := by
      simpa [p1, Function.comp_def] using d1
    exact this.unique (__Trefoil_hasD_y t)
  have d2' : p2 (deriv trefoil t) = 2*Real.cos (2*t) := by
    have : HasDerivAt (fun x : ℝ => Real.sin (2*x)) (p2 (deriv trefoil t)) t := by
      simpa [p2, Function.comp_def] using d2
    exact this.unique (__Trefoil_hasD_sin2 t)
  have z0 : p0 (deriv trefoil t) = 0 := by rw [hzero]; rfl
  have z1 : p1 (deriv trefoil t) = 0 := by rw [hzero]; rfl
  have z2 : p2 (deriv trefoil t) = 0 := by rw [hzero]; rfl
  have c2 : Real.cos (2*t) = 0 := by linarith
  have trig2 := Real.sin_sq_add_cos_sq (2*t)
  have trig3 := Real.sin_sq_add_cos_sq (3*t)
  -- taking the radial component of the two planar derivative equations gives
  -- `-2 sin (2t) = 0`, impossible when `cos (2t)=0`.
  nlinarith

end
end KnotSupport

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/Trefoil.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/UnknotInversion.lean
section

/-! Inversion at a point of the round circle.
This is a useful (and elementary) reduction of the unknot calculation. -/
noncomputable section
open scoped Topology FundamentalGroupoid ComplexConjugate
open CategoryTheory
namespace KnotSupport

-- a point of the circle
abbrev e : R3 := circle 0

lemma e_coord (i : Fin 3) : (e).ofLp i = if i = (0 : Fin 3) then 1 else 0 := by
  fin_cases i <;> simp [e, circle, circleVec]
@[simp] lemma e0 : (e).ofLp (0 : Fin 3) = 1 := by simpa using e_coord (0 : Fin 3)
@[simp] lemma e1 : (e).ofLp (1 : Fin 3) = 0 := by simpa using e_coord (1 : Fin 3)
@[simp] lemma e2 : (e).ofLp (2 : Fin 3) = 0 := by simpa using e_coord (2 : Fin 3)

/-- Euclidean inversion, with an arbitrary value at the origin.  We only use
it on the punctured space. -/
def j (x : R3) : R3 := (‖x‖ ^ 2)⁻¹ • x

lemma j_ne (x : R3) (hx : x ≠ 0) : j x ≠ 0 := by
  unfold j
  exact smul_ne_zero (inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))) hx
lemma j_norm (x : R3) (hx : x ≠ 0) : ‖j x‖ = (‖x‖)⁻¹ := by
  unfold j
  rw [norm_smul]
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hp))]
  field_simp

@[simp] lemma j_j (x : R3) (hx : x ≠ 0) : j (j x) = x := by
  unfold j
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnj : ‖(‖x‖ ^ 2)⁻¹ • x‖ = (‖x‖)⁻¹ := j_norm x hx
  rw [hnj, smul_smul]
  have : ((‖x‖⁻¹) ^ 2)⁻¹ * (‖x‖ ^ 2)⁻¹ = (1:ℝ) := by field_simp
  rw [this, one_smul]

lemma j_cont : ContinuousOn j ({0}ᶜ : Set R3) := by
  unfold j
  fun_prop (disch := aesop)

@[simp] lemma j_coord (x : R3) (i : Fin 3) : (j x).ofLp i = (‖x‖^2)⁻¹ * x.ofLp i := by
  rfl
@[simp] lemma sub_coord (x y : R3) (i : Fin 3) : (x-y).ofLp i = x.ofLp i - y.ofLp i := by rfl
@[simp] lemma add_coord (x y : R3) (i : Fin 3) : (x+y).ofLp i = x.ofLp i + y.ofLp i := by rfl
@[simp] lemma zero_coord (i : Fin 3) : (0 : R3).ofLp i = 0 := by rfl

/-- The range of the standard parametrisation is exactly the Euclidean unit
circle in the first two coordinates. -/
lemma mem_circle_iff (x : R3) : x ∈ Set.range circle ↔
    x.ofLp (2:Fin 3) = 0 ∧ x.ofLp (0:Fin 3)^2 + x.ofLp (1:Fin 3)^2 = 1 := by
  constructor
  · rintro ⟨t, rfl⟩
    constructor
    · dsimp [circle, circleVec]
    · dsimp [circle, circleVec]; simp [Real.cos_sq_add_sin_sq]
  · rintro ⟨h2,hunit⟩
    let z : ℂ := ⟨x.ofLp 0, x.ofLp 1⟩
    have hzsq : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simpa [z, pow_two] using hunit
    have hz : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
    have hzne : z ≠ 0 := by intro zz; simp [zz] at hz
    refine ⟨Complex.arg z, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · change Real.cos (Complex.arg z) = x.ofLp 0
      rw [Complex.cos_arg hzne, hz]
      simp [z]
    · change Real.sin (Complex.arg z) = x.ofLp 1
      rw [Complex.sin_arg, hz]
      simp [z]
    · change (0:ℝ) = x.ofLp 2
      exact h2.symm


def OnLine (y : R3) : Prop := y.ofLp (0:Fin 3) = -(1/2:ℝ) ∧ y.ofLp (2:Fin 3) = 0

abbrev LP : Type := {y : R3 // y ≠ 0 ∧ ¬ OnLine y}

lemma norm_sq_three (x : R3) : ‖x‖^2 = x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 := by
  simpa [Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq x)

lemma line_image (x : R3) (hx : x ≠ e) :
    OnLine (j (x-e)) ↔ x ∈ Set.range circle := by
  have hv : x-e ≠ 0 := sub_ne_zero.mpr hx
  have hn : ‖x-e‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  have hnorm := norm_sq_three (x-e)
  -- make the three coordinate formula very explicit; the subsequent algebra
  -- is only two lines with this version of the norm.
  simp [sub_coord, e0, e1, e2] at hnorm
  rw [mem_circle_iff]
  constructor
  · intro h
    rcases h with ⟨h0,h2⟩
    simp [j, sub_coord, e0] at h0
    simp [j, sub_coord, e2] at h2
    have hz : x.ofLp 2 = 0 := by
      rcases h2 with h | h
      · exact False.elim (hv h)
      · exact h
    have hnorm' := hnorm
    rw [hz] at hnorm'
    have heq : ‖x-e‖^2 = 2 * (1-x.ofLp 0) := by
      field_simp at h0
      linarith
    rw [heq] at hnorm'
    constructor
    · exact hz
    · nlinarith
  · rintro ⟨h2,hu⟩
    unfold OnLine
    have hnorm' := hnorm
    rw [h2] at hnorm'
    have heq : ‖x-e‖^2 = 2 * (1-x.ofLp 0) := by nlinarith
    constructor
    · change (j (x-e)).ofLp 0 = -(1/2:ℝ)
      simp [j, sub_coord, e0]
      field_simp
      linarith
    · change (‖x-e‖^2)⁻¹ * (x.ofLp 2 - 0) = 0
      simp [h2]

lemma e_mem : e ∈ Set.range circle := ⟨0, rfl⟩

/-- Inversion at `e` sends the complement of the circle to the complement
of a straight line and an extra point.  The extra point is important: it is
the old point at infinity. -/
def circleToLP : ((Set.range circle)ᶜ : Set R3) → LP := fun x => by
  have hx : (x:R3) ≠ e := by
    intro q
    have : (x:R3) ∈ Set.range circle := q ▸ e_mem
    exact x.property this
  refine ⟨j ((x:R3) - e), j_ne _ (sub_ne_zero.mpr hx), ?_⟩
  exact (line_image _ hx).not.mpr x.property

def LPToCircle : LP → ((Set.range circle)ᶜ : Set R3) := fun y => by
  have hy : (y:R3) ≠ 0 := y.property.1
  have hj : j (y:R3) ≠ 0 := j_ne _ hy
  have hne : e + j (y:R3) ≠ e := by
    intro h
    have : j (y:R3) = 0 := by
      apply add_left_cancel (a := e)
      simpa using h 
    exact hj this
  refine ⟨e + j (y:R3), ?_⟩
  have hnot : ¬ OnLine (y:R3) := y.property.2
  -- apply line_image and the involution
  have hh := line_image (e + j (y:R3)) hne
  -- its left side simplifies to OnLine y
  have hs : j ((e + j (y:R3))-e) = (y:R3) := by
    simpa using (j_j (y:R3) hy)
  rw [hs] at hh
  exact hh.not.mp hnot

@[simp] lemma LP_left (x : ((Set.range circle)ᶜ : Set R3)) :
    LPToCircle (circleToLP x) = x := by
  apply Subtype.ext
  dsimp [LPToCircle, circleToLP]
  change e + j (j ((x:R3)-e)) = x
  rw [j_j]
  · abel
  · intro h
    have hx : (x:R3) = e := sub_eq_zero.mp h
    exact x.property (hx ▸ e_mem)

@[simp] lemma LP_right (y : LP) : circleToLP (LPToCircle y) = y := by
  apply Subtype.ext
  dsimp [LPToCircle, circleToLP]
  change j ((e + j (y:R3))-e) = y
  simpa using j_j (y:R3) y.property.1

lemma continuous_j_comp {X : Type*} [TopologicalSpace X]
    (f : X → R3) (hc : Continuous f) (hz : ∀ x, f x ≠ 0) :
    Continuous (fun x => j (f x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  unfold j
  apply ContinuousAt.smul
  · apply ContinuousAt.inv₀
    · fun_prop
    · exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hz x))
  · exact hc.continuousAt

noncomputable def invHomeo : ((Set.range circle)ᶜ : Set R3) ≃ₜ LP where
  toFun := circleToLP
  invFun := LPToCircle
  left_inv := LP_left
  right_inv := LP_right
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun x : ((Set.range circle)ᶜ : Set R3) => j ((x:R3)-e))
    apply continuous_j_comp
    · fun_prop
    · intro x h
      have q : (x:R3) = e := sub_eq_zero.mp h
      exact x.property (q ▸ e_mem)
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun y : LP => e + j (y:R3))
    apply Continuous.const_add
    apply continuous_j_comp
    · fun_prop
    · intro y; exact y.property.1

/-- The exact form in which the geometric reduction is used. -/
theorem FGAbelian_circle_of_LP (h : FGAbelian LP) :
    FGAbelian ((Set.range circle)ᶜ : Set R3) :=
  (-- FGAbelian.homeomorph is written in the forward direction
   FGAbelian.homeomorph invHomeo.symm h)

end KnotSupport
namespace KnotSupport
/-- Canonical cylinder coordinates for the straight-line complement.  This
version (without the old point at infinity deleted) really *is* a product.
It avoids any pictures in subsequent uses of van Kampen. -/
abbrev Zstar := {z : ℂ // z ≠ 0}
abbrev Cyl := Multiplicative ℝ × Zstar

/-- complex transverse coordinate to the line -/
def w (x : R3) : ℂ := ⟨x.ofLp 0 + 1/2, x.ofLp 2⟩
lemma w_ne_iff (x : R3) : w x ≠ 0 ↔ ¬ OnLine x := by
  unfold w OnLine
  constructor
  · intro h hw
    apply h
    apply Complex.ext <;> dsimp <;> linarith [hw.1, hw.2]
  · intro h hw
    apply h
    have re := congrArg Complex.re hw
    have im := congrArg Complex.im hw
    dsimp at re im
    constructor <;> linarith

abbrev Lc : Type := {x : R3 // ¬ OnLine x}
instance : TopologicalSpace Lc := instTopologicalSpaceSubtype

def toCyl (x : Lc) : Cyl :=
  (Multiplicative.ofAdd ((x:R3).ofLp 1), ⟨w x, (w_ne_iff x).2 x.property⟩)

def v (a b c : ℝ) : R3 := WithLp.toLp 2 ![a,b,c]
@[simp] lemma vcoord (a b c : ℝ) :
    (v a b c).ofLp 0 = a ∧ (v a b c).ofLp 1 = b ∧ (v a b c).ofLp 2 = c := by
  simp [v]

lemma wxv (z : ℂ) (r : ℝ) : w (v (z.re-1/2) r z.im) = z := by
  apply Complex.ext <;> dsimp [w, v] <;> linarith

def fromCyl (u : Cyl) : Lc := by
  let x : R3 := v ((u.2:ℂ).re - 1/2) (Multiplicative.toAdd u.1) (u.2:ℂ).im
  refine ⟨x, (w_ne_iff x).1 ?_⟩
  have h : w x = (u.2:ℂ) := wxv (u.2:ℂ) _
  rw [h]
  exact u.2.property

end KnotSupport
end

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/UnknotInversion.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/LPModel.lean
section

/-! Coordinates for the elementary space left by inversion of the round
circle.  There are two slightly different spaces in this calculation; it is
quite easy to confuse them.  `Lc` is just the complement of the line.  It is
a product `ℝ × (ℂ\{0})`.  The value at infinity of the inversion has *not*
been filled in: in `LP` one point of this product, namely `(0,1/2)`, is still
missing.

None of the lemmas below use a choice of an angle.  This is useful when these
coordinates are used on paths.
-/
noncomputable section
open scoped Topology FundamentalGroupoid ComplexConjugate
open CategoryTheory
namespace KnotSupport

/-- The cylinder charts really are inverse maps.  Kept as equalities of the
subtypes; they are handy for using `Homeomorph.subtype` below. -/
@[simp] theorem from_toCyl (x : Lc) : fromCyl (toCyl x) = x := by
  apply Subtype.ext
  -- it is less brittle to compare the three real coordinates than vectors of
  -- length three
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [fromCyl, toCyl, v, w] <;> ring

@[simp] theorem to_fromCyl (u : Cyl) : toCyl (fromCyl u) = u := by
  -- The first coordinate is only a type synonym.  Writing `cases u` here
  -- makes the coercions in `Multiplicative.toAdd` transparent to `rfl`.
  rcases u with ⟨r,z⟩
  apply Prod.ext
  · change Multiplicative.ofAdd (Multiplicative.toAdd r) = r
    rfl
  · apply Subtype.ext
    change w (v ((z:ℂ).re - 1/2) (Multiplicative.toAdd r) (z:ℂ).im) = (z:ℂ)
    exact wxv (z:ℂ) (Multiplicative.toAdd r)

lemma continuous_w : Continuous w := by
  have he : w = (fun x : R3 =>
      Complex.equivRealProdCLM.symm
        ( x.ofLp (0:Fin 3) + (1/2:ℝ),
          x.ofLp (2:Fin 3))) := by
    funext x
    -- use the product coordinates of a complex number
    apply_fun Complex.equivRealProdCLM
    rfl
  rw [he]
  apply Complex.equivRealProdCLM.symm.continuous.comp
  exact Continuous.prodMk
    (( (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (0:Fin 3))).add
      continuous_const)
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2:Fin 3))

lemma continuous_v {X : Type*} [TopologicalSpace X]
    {a b c : X → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) :
    Continuous (fun t => v (a t) (b t) (c t)) := by
  unfold v
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (continuous_pi (fun i => ?_))
  fin_cases i
  · simpa using ha
  · simpa using hb
  · simpa using hc

lemma continuous_toCyl : Continuous toCyl := by
  -- The subtypes carry the induced topology.  Give the two coordinates
  -- separately so no subspace continuity lemma is hidden in this chart.
  apply Continuous.prodMk
  · change Continuous (fun x : Lc =>
        Multiplicative.ofAdd ((x:R3).ofLp (1 : Fin 3)))
    exact continuous_ofAdd.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (1:Fin 3)).comp
        continuous_subtype_val)
  · apply Continuous.subtype_mk
    exact continuous_w.comp continuous_subtype_val

lemma continuous_fromCyl : Continuous fromCyl := by
  apply Continuous.subtype_mk
  change Continuous (fun u : Cyl =>
    v ((u.2:ℂ).re - 1/2) (Multiplicative.toAdd u.1)
      (u.2:ℂ).im)
  apply continuous_v
  · exact (Complex.continuous_re.comp
          (continuous_subtype_val.comp continuous_snd)).sub continuous_const
  · exact continuous_toAdd.comp continuous_fst
  · exact Complex.continuous_im.comp
          (continuous_subtype_val.comp continuous_snd)

/-- The honest chart for the line complement.  This should not be used for
`LP` without deleting the point `cylPoint`. -/
noncomputable def lcHomeo : Lc ≃ₜ Cyl where
  toFun := toCyl
  invFun := fromCyl
  left_inv := from_toCyl
  right_inv := to_fromCyl
  continuous_toFun := continuous_toCyl
  continuous_invFun := continuous_fromCyl

/-- `1/2`, regarded as a non-zero transverse complex coordinate. -/
noncomputable def zh : Zstar :=
  ⟨(1/2 : ℂ), by norm_num⟩
/-- The puncture in the cylinder.  Additive coordinate zero is the unit of
`Multiplicative ℝ`. -/
noncomputable def cylPoint : Cyl := (Multiplicative.ofAdd 0, zh)

lemma fromCyl_eq_zero (u : Cyl) :
    (fromCyl u : R3) = 0 ↔ u = cylPoint := by
  constructor
  · intro h
    -- read the three real coordinates of the equality.  In the transverse
    -- coordinates it says exactly `z = (1/2,0)`.
    have h0 := congrArg (fun x : R3 => x.ofLp (0:Fin 3)) h
    have h1 := congrArg (fun x : R3 => x.ofLp (1:Fin 3)) h
    have h2 := congrArg (fun x : R3 => x.ofLp (2:Fin 3)) h
    change (u.2:ℂ).re - 1/2 = 0 at h0
    change Multiplicative.toAdd u.1 = 0 at h1
    change (u.2:ℂ).im = 0 at h2
    -- two subtype extensionalities and the inverse of `ofAdd`
    apply Prod.ext
    · -- the type synonym is transparent after applying `toAdd`
      apply Multiplicative.toAdd.injective
      simpa [cylPoint] using h1
    · apply Subtype.ext
      apply Complex.ext
      · change (u.2:ℂ).re = (1/2:ℂ).re
        -- `norm_num` also normalises the `ofReal` coercion
        norm_num
        linarith
      · change (u.2:ℂ).im = (1/2:ℂ).im
        norm_num
        linarith
  · intro h
    rw [h]
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [fromCyl, cylPoint, zh, v]

/-- Removing the origin before the line is removed is the same as removing
`cylPoint` from the cylinder.  Notice the use of `¬ (u=cylPoint)`, not
`u.2 ≠ 0`: the latter has already been enforced by `Zstar`. -/
noncomputable def lpHomeo : LP ≃ₜ {u : Cyl // u ≠ cylPoint} := by
  -- first change a point of `LP` to a point of `Lc` with a predicate; this
  -- avoids any coercion gymnastics with two nested subspaces.
  let E : LP ≃ₜ {x : Lc // (x:R3) ≠ 0} :=
    { toFun := fun x => ⟨⟨(x:R3), x.property.2⟩, x.property.1⟩
      invFun := fun x => ⟨(x.1:R3), x.property, x.1.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      continuous_toFun :=
        by
          apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          fun_prop
      continuous_invFun :=
        by
          apply Continuous.subtype_mk
          fun_prop }
  refine E.trans (lcHomeo.subtype ?_)
  intro x
  -- state it through the inverse chart; the equalities of the chart were
  -- proved above, rather than by a choice of representatives.
  constructor
  · intro hx h
    have : (fromCyl (toCyl x) : R3) = 0 :=
      (fromCyl_eq_zero (toCyl x)).2 h
    exact hx (by simpa using this)
  · intro hx h0
    have : toCyl x = cylPoint :=
      (fromCyl_eq_zero (toCyl x)).1 (by
        simpa using h0)
    exact hx this

end KnotSupport

namespace KnotSupport
open scoped Topology FundamentalGroupoid ComplexConjugate
open CategoryTheory
/-- `Zstar` is the group of nonzero complex numbers.  We had used a subtype
instead of `ℂˣ` in the coordinates in order not to carry an inverse in every
formula. -/
instance zstarGroup : Group Zstar where
  mul a b := ⟨(a:ℂ) * (b:ℂ), mul_ne_zero a.property b.property⟩
  one := ⟨1, one_ne_zero⟩
  inv a := ⟨(a:ℂ)⁻¹, inv_ne_zero a.property⟩
  mul_assoc a b c := by ext; exact mul_assoc (a:ℂ) b c
  one_mul a := by ext; exact one_mul (a:ℂ)
  mul_one a := by ext; exact mul_one (a:ℂ)
  inv_mul_cancel a := by ext; exact inv_mul_cancel₀ a.property

@[simp] lemma zstar_mul_val (a b : Zstar) : ((a*b : Zstar) : ℂ) = (a:ℂ)*(b:ℂ) := rfl
@[simp] lemma zstar_one_val : ((1 : Zstar) : ℂ) = 1 := rfl
@[simp] lemma zstar_inv_val (a : Zstar) : ((a⁻¹ : Zstar) : ℂ) = (a:ℂ)⁻¹ := rfl

instance zstarContinuousMul : ContinuousMul Zstar := by
  constructor
  change Continuous (fun p : Zstar × Zstar => p.1 * p.2)
  apply Continuous.subtype_mk
  change Continuous (fun p : Zstar × Zstar => (p.1:ℂ) * (p.2:ℂ))
  exact (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

instance zstarContinuousInv : ContinuousInv Zstar := by
  constructor
  change Continuous (fun a : Zstar => a⁻¹)
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro a
  change ContinuousAt (fun a : Zstar => ((a:ℂ)⁻¹)) a
  have hc : ContinuousAt (fun a : Zstar => (a:ℂ)) a :=
    continuous_subtype_val.continuousAt
  exact hc.inv₀ a.property

instance zstarIsTopologicalGroup : IsTopologicalGroup Zstar := by
  constructor

/-- Epimorphisms are not what is wanted for the deletion of a point.  The
right statement is injectivity: an equality of loops which uses the filled
point can be changed to one avoiding it.  This small lemma records exactly
this direction and is deliberately at all basepoints. -/
theorem FGAbelian_of_injective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y))
    (hi : ∀ x : X, Function.Injective (FundamentalGroup.map f x))
    (hY : FGAbelian Y) : FGAbelian X := by
  intro x a b
  apply hi x
  simpa [map_mul] using (hY (f x)
      ((FundamentalGroup.map f x) a) ((FundamentalGroup.map f x) b))

/-- In a topological group each vertex group is abelian, not just the vertex
at the unit.  Translation is useful here: it avoids any connectedness
hypothesis on the ambient group. -/
theorem FGAbelian_topologicalGroup (G : Type*) [TopologicalSpace G]
    [Group G] [IsTopologicalGroup G] : FGAbelian G := by
  intro x a b
  let e : G ≃ₜ G := Homeomorph.mulLeft x⁻¹
  let F : C(G,G) := ⟨e, e.continuous⟩
  have hunit : F x = (1:G) := by
    change x⁻¹ * x = 1
    simp
  -- we use `mapOfEq` once to get exactly an endomorphism of the unit vertex
  let M : FundamentalGroup G x →* FundamentalGroup G (1:G) :=
    FundamentalGroup.mapOfEq F hunit
  have inj : Function.Injective M := by
    -- the functor of a homeomorphism is faithful at each pair of objects
    let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.toHomotopyEquiv
    -- alternatively use its `faithful` field; the functor is definitionally
    -- the same map before the harmless cast of endpoints
    intro u v h
    -- remove the casts in `mapOfEq` and apply faithfulness
    change _ at h
    -- equality of the underlying morphisms is unchanged by the cast.  It is
    -- a `eqToHom`-transport, hence cancellable.
    -- use injectivity of transport then `map_injective` from the equivalence
    have hm : (FundamentalGroup.map F x) u =
              (FundamentalGroup.map F x) v := by
      -- `mapOfEq` is conjugating both sides by the same isomorphism.
      exact ((eqToIso <| congr_arg FundamentalGroupoid.mk hunit).conj).injective h
    exact E.functor.map_injective hm
  apply inj
  have hc := fundamentalGroup_one_comm (G:=G) (M a) (M b)
  simpa [map_mul] using hc

/-- In particular the *unpunctured* cylinder is harmless.  This lemma is
often a useful test that the point at infinity has not accidentally been
filled. -/
theorem FGAbelian_cyl : FGAbelian Cyl :=
  FGAbelian_topologicalGroup Cyl

/-- Fill the missing point.  This is the exact injectivity assertion a loop
argument for the puncture must prove. -/
def cylInclusion : C({u : Cyl // u ≠ cylPoint}, Cyl) :=
  ⟨fun u => (u:Cyl), continuous_subtype_val⟩

theorem FGAbelian_LP_of_cyl_injective
    (h : ∀ x : {u : Cyl // u ≠ cylPoint},
      Function.Injective (FundamentalGroup.map cylInclusion x)) :
    FGAbelian LP := by
  have hsub : FGAbelian {u : Cyl // u ≠ cylPoint} :=
    FGAbelian_of_injective cylInclusion h FGAbelian_cyl
  exact FGAbelian.homeomorph lpHomeo.symm hsub

end KnotSupport
namespace KnotSupport
open scoped Topology FundamentalGroupoid ComplexConjugate unitInterval
open CategoryTheory

/-- A harmless transverse value used while moving through level zero. -/
noncomputable def zi : Zstar := ⟨Complex.I, by norm_num⟩
lemma zi_ne_zh : zi ≠ zh := by
  intro h
  have hh := congrArg Complex.im (congrArg Subtype.val h)
  norm_num [zi, zh] at hh

/-- Straight paths in the first (additive, though written multiplicatively)
coordinate. -/
noncomputable def rline (a b : Multiplicative ℝ) : Path a b where
  toFun t := Multiplicative.ofAdd ((1-(t:ℝ)) * Multiplicative.toAdd a +
                            (t:ℝ) * Multiplicative.toAdd b)
  continuous_toFun := by
    apply continuous_ofAdd.comp
    fun_prop
  source'  := by change (1-(0:ℝ))* Multiplicative.toAdd a + 0 *
      Multiplicative.toAdd b = Multiplicative.toAdd a; ring
  target' := by change (1-(1:ℝ))* Multiplicative.toAdd a + 1 *
      Multiplicative.toAdd b = Multiplicative.toAdd b; ring

/-- `Zstar` is path connected.  Use the standard fact for complex units; no
argument function appears in our later paths. -/
noncomputable def zpath (a b : Zstar) : Path a b := by
  let E : ℂˣ ≃ₜ Zstar := unitsHomeomorphNeZero
  simpa using
    (PathConnectedSpace.somePath (E.symm a) (E.symm b)).map E.continuous

/-- Lift a path once a proof it misses the puncture is supplied. -/
noncomputable def avoidPath {a b : Cyl} (p : Path a b)
    (ha : a ≠ cylPoint) (hb : b ≠ cylPoint)
    (hp : ∀ t, p t ≠ cylPoint) :
    Path (⟨a, ha⟩ : {u : Cyl // u ≠ cylPoint}) ⟨b,hb⟩ where
  toFun := fun t => ⟨p t, hp t⟩
  continuous_toFun := Continuous.subtype_mk p.continuous (fun t => hp t)
  source' := by apply Subtype.ext; exact p.source
  target' := by apply Subtype.ext; exact p.target

lemma prod_ne_point_left {r : Multiplicative ℝ} (hr : r ≠ Multiplicative.ofAdd 0)
    (z : Zstar) : (r,z) ≠ cylPoint := by
  intro h
  exact hr (congrArg Prod.fst h)
lemma prod_ne_point_right (r : Multiplicative ℝ) {z : Zstar} (hz : z ≠ zh) :
    (r,z) ≠ cylPoint := by
  intro h
  exact hz (congrArg Prod.snd h)

/-- The elementary paths used with the cylinder cover.  This lemma is more
useful than a bare assertion of connectedness: if the first coordinate is the
zero level, move it first; otherwise change the transverse value to `I`,
move the first coordinate, and only then change back.  Thus no drawn path
silently crosses `(0,1/2)`. -/
noncomputable def cylBase : {u : Cyl // u ≠ cylPoint} :=
  ⟨(Multiplicative.ofAdd (1:ℝ), zh), by
    apply prod_ne_point_left
    intro h
    exact one_ne_zero (Multiplicative.ofAdd.injective h)⟩

lemma cylPoint_paths (x : {u : Cyl // u ≠ cylPoint}) :
    Nonempty (Path cylBase x) := by
  classical
  rcases x with ⟨⟨r,z⟩, hx⟩
  by_cases hzero : r = Multiplicative.ofAdd 0
  · -- here `z` is not the bad transverse value, so it is safe to change
    -- the height first
    have hz : z ≠ zh := by
      intro q
      apply hx
      exact Prod.ext hzero q
    let p : Path (r,z) (Multiplicative.ofAdd (1:ℝ), z) :=
      (rline r (Multiplicative.ofAdd (1:ℝ))).prod (Path.refl z)
    have hp : ∀ t, p t ≠ cylPoint := by
      intro t
      apply prod_ne_point_right _ hz
    have h1 : (Multiplicative.ofAdd (1:ℝ), z) ≠ cylPoint := by
      apply prod_ne_point_left
      intro h
      exact one_ne_zero (Multiplicative.ofAdd.injective h)
    let P : Path (⟨(r,z), hx⟩ : {u : Cyl // u ≠ cylPoint}) ⟨_, h1⟩ :=
      avoidPath p hx h1 hp
    let q : Path (Multiplicative.ofAdd (1:ℝ), z)
        (Multiplicative.ofAdd (1:ℝ), zh) :=
      (Path.refl _).prod (zpath z zh)
    have hq : ∀ t, q t ≠ cylPoint := by
      intro t
      apply prod_ne_point_left
      intro h
      exact one_ne_zero (Multiplicative.ofAdd.injective h)
    let Q : Path (⟨_, h1⟩ : {u : Cyl // u ≠ cylPoint}) cylBase :=
      avoidPath q h1 cylBase.property hq
    exact ⟨(P.trans Q).symm⟩
  · -- off the zero height we can change the transverse coordinate first.
    have hzi : zi ≠ zh := zi_ne_zh
    have hr : r ≠ Multiplicative.ofAdd 0 := hzero
    have ha : (r, zi) ≠ cylPoint := prod_ne_point_left hr _
    let p : Path (r,z) (r,zi) := (Path.refl r).prod (zpath z zi)
    have hp : ∀ t, p t ≠ cylPoint := by
      intro t
      apply prod_ne_point_left hr
    let P : Path (⟨(r,z), hx⟩ : {u : Cyl // u ≠ cylPoint}) ⟨_,ha⟩ :=
      avoidPath p hx ha hp
    have h1 : (Multiplicative.ofAdd (1:ℝ), zi) ≠ cylPoint :=
      prod_ne_point_right _ hzi
    let q : Path (r,zi) (Multiplicative.ofAdd (1:ℝ),zi) :=
      (rline r (Multiplicative.ofAdd (1:ℝ))).prod (Path.refl zi)
    have hq : ∀ t, q t ≠ cylPoint := by
      intro t
      apply prod_ne_point_right _ hzi
    let Q : Path (⟨_,ha⟩ : {u : Cyl // u ≠ cylPoint}) ⟨_,h1⟩ :=
      avoidPath q ha h1 hq
    let s : Path (Multiplicative.ofAdd (1:ℝ), zi)
        (Multiplicative.ofAdd (1:ℝ), zh) :=
      (Path.refl _).prod (zpath zi zh)
    have hs : ∀ t, s t ≠ cylPoint := by
      intro t
      apply prod_ne_point_left
      intro h
      exact one_ne_zero (Multiplicative.ofAdd.injective h)
    let S : Path (⟨_,h1⟩ : {u : Cyl // u ≠ cylPoint}) cylBase :=
      avoidPath s h1 cylBase.property hs
    exact ⟨(P.trans (Q.trans S)).symm⟩

end KnotSupport
namespace KnotSupport
open scoped FundamentalGroupoid Topology
open CategoryTheory
/-- A convenient formulation of the last (two dimensional) obstruction.  To
show that filling the removed point is injective on the base vertex group it
suffices to change a homotopy of two *actual* based squares to one missing the
point.  This quotient-induction lemma prevents any endpoint casts from being
hidden in that future approximation argument.  Here the endpoints are the
chosen point of `cylPoint_paths`, not arbitrary free loops. -/
theorem cylInclusion_base_injective_of_homotopies
 (H : ∀ (p q : Path cylBase cylBase),
   (p.map cylInclusion.continuous).Homotopic
      (q.map cylInclusion.continuous) → p.Homotopic q) :
 Function.Injective (FundamentalGroup.map cylInclusion cylBase) := by
  intro a b hh
  induction a using Quotient.inductionOn with | _ p => ?_
  induction b using Quotient.inductionOn with | _ q => ?_
  apply Path.Homotopic.Quotient.eq.mpr
  apply H p q
  apply Path.Homotopic.Quotient.eq.mp
  exact hh
end KnotSupport

end

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/LPModel.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/TrefoilCoordinates.lean
section

/-! Coordinates for the torus parametrisation, and a useful map to the
cusp-discriminant complement.  Points of the standard torus are described by
`xi=(radius-2)+z i` and `eta=(x+y i)/max radius 1`.  The harmless `max`
extends the angular coordinate across the axis.  A small algebra observation
is very convenient: the equation `xi^3=eta^2` cuts out *exactly* the
parametrised (2,3) curve, not a surface or a filled-in curve. -/
namespace KnotSupport
noncomputable section
open scoped ComplexConjugate

/-- cylindrical radius -/
def torRad (p : R3) : ℝ :=
  Real.sqrt (((p.ofLp (0 : Fin 3))^2) + ((p.ofLp (1 : Fin 3))^2))

@[simp] lemma torRad_nonneg (p : R3) : 0 ≤ torRad p := Real.sqrt_nonneg _

@[continuity, fun_prop]
lemma torRad_cont : Continuous torRad := by
  unfold torRad
  fun_prop

/-- transverse coordinate to the round torus -/
def torXi (p : R3) : ℂ :=
  ⟨torRad p - 2, p.ofLp (2 : Fin 3)⟩

/-- angular coordinate, shrunk linearly inside the cylinder of radius one.
This way it is defined and continuous on all of `ℝ³`.  On the knot the
radius is at least one, so it is the usual unit angular coordinate. -/
def torEta (p : R3) : ℂ :=
  ⟨p.ofLp (0 : Fin 3) / max (torRad p) 1,
   p.ofLp (1 : Fin 3) / max (torRad p) 1⟩

@[simp] lemma torXi_re (p : R3) : (torXi p).re = torRad p - 2 := rfl
@[simp] lemma torXi_im (p : R3) : (torXi p).im = p.ofLp (2 : Fin 3) := rfl
@[simp] lemma torEta_re (p : R3) :
    (torEta p).re = p.ofLp (0 : Fin 3) / max (torRad p) 1 := rfl
@[simp] lemma torEta_im (p : R3) :
    (torEta p).im = p.ofLp (1 : Fin 3) / max (torRad p) 1 := rfl

lemma maxRad_pos (p : R3) : 0 < max (torRad p) 1 :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

@[continuity, fun_prop]
lemma torXi_cont : Continuous torXi := by
  unfold torXi
  change Continuous (fun p : R3 =>
    Complex.equivRealProdCLM.symm ((torRad p - 2), p.ofLp (2 : Fin 3)))
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((torRad_cont.sub continuous_const).prodMk (by fun_prop))

@[continuity, fun_prop]
lemma torEta_cont : Continuous torEta := by
  unfold torEta
  have hn : ∀ p : R3, max (torRad p) 1 ≠ 0 := fun p => ne_of_gt (maxRad_pos p)
  change Continuous (fun p : R3 =>
    Complex.equivRealProdCLM.symm
      ((p.ofLp (0:Fin 3) / max (torRad p) 1),
       (p.ofLp (1:Fin 3) / max (torRad p) 1)))
  apply Complex.equivRealProdCLM.symm.continuous.comp
  fun_prop

/-- The open discriminant complement of a depressed cubic.  No topology of
polynomials is required: just this very elementary open subset of `ℂ²`. -/
def CubicGood : Type := {w : ℂ × ℂ // w.1 ^ (3:ℕ) ≠ w.2 ^ (2:ℕ)}

instance : TopologicalSpace CubicGood := inferInstanceAs (TopologicalSpace {w : ℂ × ℂ // w.1 ^ (3:ℕ) ≠ w.2 ^ (2:ℕ)})

/-- The cylindrical coefficients. -/
def torCoeff (p : R3) : ℂ × ℂ := (torXi p, torEta p)

lemma torCoeff_cont : Continuous torCoeff := by
  unfold torCoeff; fun_prop

private lemma __TrefoilCoordinates_rad_sq (p : R3) :
    (torRad p)^2 = (p.ofLp (0 : Fin 3))^2 + (p.ofLp (1 : Fin 3))^2 := by
  unfold torRad
  apply Real.sq_sqrt
  positivity

lemma norm_torEta (p : R3) : ‖torEta p‖ = torRad p / max (torRad p) 1 := by
  have hm : 0 < max (torRad p) 1 := maxRad_pos p
  have hR : 0 ≤ torRad p := torRad_nonneg p
  -- compare nonnegative squares, avoiding a nested square root
  have hsq : ‖torEta p‖ ^ 2 = (torRad p / max (torRad p) 1)^2 := by
    rw [Complex.sq_norm]
    rw [Complex.normSq_apply]
    -- the radius square is exactly x^2+y^2
    change (p.ofLp (0 : Fin 3) / max (torRad p) 1) *
          (p.ofLp (0 : Fin 3) / max (torRad p) 1) +
          (p.ofLp (1 : Fin 3) / max (torRad p) 1) *
          (p.ofLp (1 : Fin 3) / max (torRad p) 1) = _
    rw [div_pow]
    have hr := __TrefoilCoordinates_rad_sq p
    -- use a common positive denominator
    field_simp
    nlinarith
  nlinarith [norm_nonneg (torEta p), div_nonneg hR (le_of_lt hm)]

/-- Outside the unit cylinder `eta` is an honest unit angular coordinate. -/
lemma norm_torEta_of_one_le {p : R3} (h : 1 ≤ torRad p) : ‖torEta p‖ = 1 := by
  rw [norm_torEta, max_eq_left h]
  exact div_self (ne_of_gt (lt_of_lt_of_le (by norm_num) h))

lemma norm_torEta_of_lt_one {p : R3} (h : torRad p < 1) : ‖torEta p‖ = torRad p := by
  rw [norm_torEta, max_eq_right (le_of_lt h)]
  ring

/-- If the radius were smaller than one the two moduli cannot be on the
cubic discriminant.  This is the useful reason for shrinking the angular
coordinate at the axis. -/
lemma rad_one_le_of_disc {p : R3} (h : torXi p ^ (3:ℕ) = torEta p ^ (2:ℕ)) :
    1 ≤ torRad p := by
  by_contra hn
  have hr : torRad p < 1 := lt_of_not_ge hn
  have nxi : (1:ℝ) < ‖torXi p‖ := by
    -- the real part already has absolute value `2-radius`
    have hx : |(torXi p).re| = 2 - torRad p := by
      rw [torXi_re]
      have : torRad p - 2 < 0 := by linarith
      rw [abs_of_neg this]
      ring
    have bound : |(torXi p).re| ≤ ‖torXi p‖ := by
      simpa using (Complex.abs_re_le_norm (torXi p))
    linarith
  have neta : ‖torEta p‖ < 1 := by rw [norm_torEta_of_lt_one hr]; exact hr
  have hn' := congrArg norm h
  rw [norm_pow, norm_pow] at hn'
  have hxpos : 0 ≤ ‖torXi p‖ := norm_nonneg _
  have hepos : 0 ≤ ‖torEta p‖ := norm_nonneg _
  have big : (1:ℝ) < ‖torXi p‖ ^ (3:ℕ) := one_lt_pow₀ nxi (by decide)
  have small : ‖torEta p‖ ^ (2:ℕ) < (1:ℝ) := pow_lt_one₀ hepos neta (by decide)
  linarith

lemma norm_xi_one_of_disc {p : R3} (h : torXi p ^ (3:ℕ) = torEta p ^ (2:ℕ)) :
    ‖torXi p‖ = 1 := by
  have hr := rad_one_le_of_disc h
  have ne : ‖torEta p‖ = 1 := norm_torEta_of_one_le hr
  have hh := congrArg norm h
  rw [norm_pow, norm_pow, ne] at hh
  have hx : 0 ≤ ‖torXi p‖ := norm_nonneg _
  have upper : ‖torXi p‖ ≤ (1:ℝ) := by
    apply le_of_not_gt
    intro gt
    have z := one_lt_pow₀ gt (by decide : (3:ℕ) ≠ 0)
    nlinarith
  have lower : (1:ℝ) ≤ ‖torXi p‖ := by
    apply le_of_not_gt
    intro lt
    have z := pow_lt_one₀ hx lt (by decide : (3:ℕ) ≠ 0)
    nlinarith
  exact le_antisymm upper lower

lemma eta_ne_zero_of_disc {p : R3} (h : torXi p ^ (3:ℕ) = torEta p ^ (2:ℕ)) :
    torEta p ≠ 0 := by
  have he : ‖torEta p‖ = 1 := norm_torEta_of_one_le (rad_one_le_of_disc h)
  exact fun z => by simpa [z] using he

/-- A group calculation behind the parametrisation.  On the unit circle the
single relation `u^3=v^2` gives a common parameter: use `e=u^2/v`.  Working
in a field avoids any choices of roots. -/
lemma unit_parameter {u v : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : u ^ (3:ℕ) = v ^ (2:ℕ)) :
    let e := u ^ (2:ℕ) / v
    ‖e‖ = 1 ∧ e ^ (2:ℕ) = u ∧ e ^ (3:ℕ) = v := by
  dsimp
  have vu : v ≠ 0 := by
    intro z
    simpa [z] using hv
  have hunitu : u ≠ 0 := by intro z; simpa [z] using hu
  constructor
  · rw [norm_div, norm_pow, hu, hv]
    norm_num
  constructor
  · calc
      (u^2 / v) ^ (2:ℕ) = u^4 / v^2 := by ring
      _ = u := by
        apply (div_eq_iff (pow_ne_zero _ vu)).2
        calc
          u^4 = u * (u^3) := by ring
          _ = u * (v^2) := by rw [h]
  · calc
      (u^2 / v) ^ (3:ℕ) = u^6 / v^3 := by ring
      _ = v := by
        apply (div_eq_iff (pow_ne_zero _ vu)).2
        calc
          u^6 = (u^3)^2 := by ring
          _ = (v^2)^2 := by rw [h]
          _ = v * (v^3) := by ring

/-- `exp(arg e * i)` is literally a unit complex number `e`. Keeping this
little norm-one specialization separate makes the coordinate proof below
much less dependent on trigonometric inverse conventions. -/
lemma exp_arg_of_norm_one {e : ℂ} (he : ‖e‖ = 1) :
    Complex.exp ((e.arg : ℂ) * Complex.I) = e := by
  have h := Complex.norm_mul_exp_arg_mul_I e
  rw [he] at h
  simpa using h

lemma exp_real_mul_I (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) =
      (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  simpa using (Complex.exp_mul_I (x : ℂ))

@[simp] lemma re_exp_real_mul_I (x : ℝ) :
    (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := by
  rw [exp_real_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
@[simp] lemma im_exp_real_mul_I (x : ℝ) :
    (Complex.exp ((x : ℂ) * Complex.I)).im = Real.sin x := by
  rw [exp_real_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

lemma exp_arg_pow {e : ℂ} (he : ‖e‖ = 1) (n : ℕ) :
    Complex.exp (((n:ℝ) * e.arg : ℝ) * Complex.I) = e ^ n := by
  calc
    Complex.exp (((n:ℝ) * e.arg : ℝ) * Complex.I)
        = Complex.exp ((n:ℂ) * ((e.arg:ℂ) * Complex.I)) := by
            congr 1
            push_cast
            ring
    _ = (Complex.exp ((e.arg:ℂ) * Complex.I)) ^ n := Complex.exp_nat_mul _ _
    _ = e ^ n := by rw [exp_arg_of_norm_one he]

/-- Membership in the discriminant implies that point is on the parametrised
curve.  Notice the use of the single norm-one number `u^2/v`; no argument
compatibility or integer congruence lemma is hidden here. -/
theorem trefoil_of_disc {p : R3}
    (h : torXi p ^ (3:ℕ) = torEta p ^ (2:ℕ)) :
    ∃ t : ℝ, trefoil t = p := by
  have hr : 1 ≤ torRad p := rad_one_le_of_disc h
  have hu : ‖torXi p‖ = 1 := norm_xi_one_of_disc h
  have hv : ‖torEta p‖ = 1 := norm_torEta_of_one_le hr
  let e : ℂ := torXi p ^ (2:ℕ) / torEta p
  have ee := unit_parameter hu hv h
  change ‖e‖ = 1 ∧ e ^ (2:ℕ) = torXi p ∧ e ^ (3:ℕ) = torEta p at ee
  rcases ee with ⟨en, e2, e3⟩
  let t : ℝ := e.arg
  have E2 : Complex.exp (((2:ℝ)*t : ℝ) * Complex.I) = torXi p := by
    simpa [t] using (exp_arg_pow en 2).trans e2
  have E3 : Complex.exp (((3:ℝ)*t : ℝ) * Complex.I) = torEta p := by
    simpa [t] using (exp_arg_pow en 3).trans e3
  have c2 : Real.cos (2*t) = torRad p - 2 := by
    have A := congrArg Complex.re E2
    calc
      Real.cos (2*t) =
          (Complex.exp (((2*t:ℝ):ℂ) * Complex.I)).re :=
            (re_exp_real_mul_I (2*t)).symm
      _ = (Complex.exp (((2:ℝ)*t : ℝ) * Complex.I)).re := by
            norm_num
      _ = torRad p - 2 := A
  have s2 : Real.sin (2*t) = p.ofLp (2 : Fin 3) := by
    have A := congrArg Complex.im E2
    calc
      Real.sin (2*t) =
          (Complex.exp (((2*t:ℝ):ℂ) * Complex.I)).im :=
            (im_exp_real_mul_I (2*t)).symm
      _ = (Complex.exp (((2:ℝ)*t : ℝ) * Complex.I)).im := by norm_num
      _ = p.ofLp (2:Fin 3) := A
  have c3' : Real.cos (3*t) = p.ofLp (0 : Fin 3) / torRad p := by
    have A := congrArg Complex.re E3
    calc
      Real.cos (3*t) =
          (Complex.exp (((3*t:ℝ):ℂ) * Complex.I)).re :=
            (re_exp_real_mul_I (3*t)).symm
      _ = (Complex.exp (((3:ℝ)*t : ℝ) * Complex.I)).re := by norm_num
      _ = p.ofLp (0:Fin 3) / torRad p := by simpa [max_eq_left hr] using A
  have s3' : Real.sin (3*t) = p.ofLp (1 : Fin 3) / torRad p := by
    have A := congrArg Complex.im E3
    calc
      Real.sin (3*t) =
          (Complex.exp (((3*t:ℝ):ℂ) * Complex.I)).im :=
            (im_exp_real_mul_I (3*t)).symm
      _ = (Complex.exp (((3:ℝ)*t : ℝ) * Complex.I)).im := by norm_num
      _ = p.ofLp (1:Fin 3) / torRad p := by simpa [max_eq_left hr] using A
  refine ⟨t, ?_⟩
  -- Equality of Euclidean points is componentwise.
  apply PiLp.ext
  intro i
  fin_cases i
  · -- x coordinate
    have rp : (torRad p) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hr)
    have R : 2 + Real.cos (2*t) = torRad p := by linarith
    change (torVec t (0 : Fin 3)) = _
    simp [torVec]
    rw [R]
    -- use c3'
    rw [c3']
    field_simp
  · have rp : (torRad p) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hr)
    have R : 2 + Real.cos (2*t) = torRad p := by linarith
    change (torVec t (1 : Fin 3)) = _
    simp [torVec]
    rw [R, s3']
    field_simp
  · change (torVec t (2 : Fin 3)) = _
    simpa [torVec] using s2

/-- Conversely each point of the parametrisation satisfies the one cubic
relation. -/
lemma disc_trefoil (t : ℝ) : torXi (trefoil t) ^ (3:ℕ) = torEta (trefoil t) ^ (2:ℕ) := by
  -- radius is the positive standard torus radius
  have Rpos : 0 < (2 + Real.cos (2*t)) := by
    have le := Real.neg_one_le_cos (2*t)
    linarith
  have R : torRad (trefoil t) = 2 + Real.cos (2*t) := by
    -- compare nonnegative square roots
    have rr := __TrefoilCoordinates_rad_sq (trefoil t)
    rw [trefoil_zero, trefoil_one] at rr
    have idn :
        ((2 + Real.cos (2*t)) * Real.cos (3*t))^2 +
          ((2 + Real.cos (2*t)) * Real.sin (3*t))^2 =
            (2 + Real.cos (2*t))^2 := by
      rw [mul_pow, mul_pow]
      nlinarith [Real.sin_sq_add_cos_sq (3*t)]
    have sq := rr.trans idn
    have nn := torRad_nonneg (trefoil t)
    nlinarith
  have R1 : 1 ≤ torRad (trefoil t) := by
    rw [R]
    have le := Real.neg_one_le_cos (2*t)
    linarith
  let e : ℂ := Complex.exp ((t : ℂ) * Complex.I)
  have e2 : e ^ (2:ℕ) = torXi (trefoil t) := by
    apply Complex.ext
    · have E := re_exp_real_mul_I (2*t)
      have pow : Complex.exp (((2:ℝ)*t : ℝ) * Complex.I) = e^2 := by
        dsimp [e]
        symm
        calc
          Complex.exp ((t:ℂ) * Complex.I) ^ (2:ℕ)
              = Complex.exp ((2:ℂ) * ((t:ℂ) * Complex.I)) := (Complex.exp_nat_mul _ _).symm
          _ = Complex.exp (((2:ℝ)*t : ℝ) * Complex.I) := by
                congr 1
                push_cast
                ring
      rw [pow] at E
      simpa [torXi_re, R] using E
    · have E := im_exp_real_mul_I (2*t)
      have pow : Complex.exp (((2:ℝ)*t : ℝ) * Complex.I) = e^2 := by
        dsimp [e]
        symm
        calc
          Complex.exp ((t:ℂ) * Complex.I) ^ (2:ℕ)
              = Complex.exp ((2:ℂ) * ((t:ℂ) * Complex.I)) := (Complex.exp_nat_mul _ _).symm
          _ = Complex.exp (((2:ℝ)*t : ℝ) * Complex.I) := by
                congr 1
                push_cast
                ring
      rw [pow] at E
      simpa [torXi_im, trefoil_two] using E
  have e3 : e ^ (3:ℕ) = torEta (trefoil t) := by
    apply Complex.ext
    · have E := re_exp_real_mul_I (3*t)
      have pow : Complex.exp (((3:ℝ)*t : ℝ) * Complex.I) = e^3 := by
        dsimp [e]
        symm
        calc
          Complex.exp ((t:ℂ) * Complex.I) ^ (3:ℕ)
              = Complex.exp ((3:ℂ) * ((t:ℂ) * Complex.I)) := (Complex.exp_nat_mul _ _).symm
          _ = Complex.exp (((3:ℝ)*t : ℝ) * Complex.I) := by
                congr 1
                push_cast
                ring
      rw [pow] at E
      -- divide the positive radial factor out
      change (e^3).re = _
      have R1' : 1 ≤ 2 + Real.cos (2*t) := by rw [← R]; exact R1
      simpa [torEta_re, trefoil_zero, R, max_eq_left R1', ne_of_gt Rpos]
        using E
    · have E := im_exp_real_mul_I (3*t)
      have pow : Complex.exp (((3:ℝ)*t : ℝ) * Complex.I) = e^3 := by
        dsimp [e]
        symm
        calc
          Complex.exp ((t:ℂ) * Complex.I) ^ (3:ℕ)
              = Complex.exp ((3:ℂ) * ((t:ℂ) * Complex.I)) := (Complex.exp_nat_mul _ _).symm
          _ = Complex.exp (((3:ℝ)*t : ℝ) * Complex.I) := by
                congr 1
                push_cast
                ring
      rw [pow] at E
      change (e^3).im = _
      have R1' : 1 ≤ 2 + Real.cos (2*t) := by rw [← R]; exact R1
      simpa [torEta_im, trefoil_one, R, max_eq_left R1', ne_of_gt Rpos]
        using E
  -- e^2 cubed is e^3 squared
  rw [← e2, ← e3]
  ring

/-- Exact fibre description, often the most useful form. -/
theorem disc_iff_trefoil (p : R3) :
    torXi p ^ (3:ℕ) = torEta p ^ (2:ℕ) ↔ p ∈ Set.range trefoil := by
  constructor
  · intro h
    rcases trefoil_of_disc h with ⟨t,ht⟩
    exact ⟨t, ht⟩
  · rintro ⟨t, rfl⟩
    exact disc_trefoil t

abbrev TrefoilExterior :=
  ↥((Set.range trefoil : Set R3)ᶜ)

/-- A continuous and completely explicit map from the actual complement in
`ℝ³` to the cubic discriminant complement.  Later a root covering of the
latter can be used just as a detector; no extension across infinity is
needed. -/
def trefoilCoeffs (p : TrefoilExterior) : CubicGood :=
  ⟨torCoeff p.1, by
    intro h
    have z : (p.1 ∈ Set.range trefoil) := (disc_iff_trefoil p.1).1 h
    exact p.2 z⟩

lemma trefoilCoeffs_cont : Continuous trefoilCoeffs := by
  apply Continuous.subtype_mk
  exact torCoeff_cont.comp continuous_subtype_val

end
end KnotSupport

namespace KnotSupport
noncomputable section

/-- The very simple half-plane slice `eta=1`. All three fibres of the
projection `u^3=1` are visible in this one slice of the *actual* exterior.
It is useful for drawing the eventual meridians: there is no transfer of a
path from an abstract knot here. -/
def cubicSlice (u : ℂ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i = (0:Fin 3) then 2 + u.re
    else if i = (1:Fin 3) then 0
    else u.im)

@[simp] lemma cubicSlice_zero (u : ℂ) :
    (cubicSlice u).ofLp (0:Fin 3) = 2 + u.re := by simp [cubicSlice]
@[simp] lemma cubicSlice_one (u : ℂ) :
    (cubicSlice u).ofLp (1:Fin 3) = 0 := by simp [cubicSlice]
@[simp] lemma cubicSlice_two (u : ℂ) :
    (cubicSlice u).ofLp (2:Fin 3) = u.im := by
  simp [cubicSlice, show (2:Fin 3) ≠ 0 by decide,
       show (2:Fin 3) ≠ 1 by decide]

lemma cubicSlice_rad {u : ℂ} (hu : -1 < u.re) :
    torRad (cubicSlice u) = 2 + u.re := by
  unfold torRad
  rw [cubicSlice_zero, cubicSlice_one]
  simp
  have z : 0 ≤ 2 + u.re := by linarith
  rw [Real.sqrt_sq z]

lemma cubicSlice_one_le {u : ℂ} (hu : -1 < u.re) :
    1 ≤ torRad (cubicSlice u) := by
  rw [cubicSlice_rad hu]
  linarith

lemma xi_cubicSlice {u : ℂ} (hu : -1 < u.re) :
    torXi (cubicSlice u) = u := by
  apply Complex.ext
  · simp [cubicSlice_rad hu, torXi_re]
  · simp

lemma eta_cubicSlice {u : ℂ} (hu : -1 < u.re) :
    torEta (cubicSlice u) = 1 := by
  have hr : 1 ≤ 2 + u.re := by linarith
  have pos : 0 < 2 + u.re := lt_of_lt_of_le (by norm_num) hr
  apply Complex.ext
  · simp [torEta_re, cubicSlice_rad hu, max_eq_left hr,
         ne_of_gt pos]
  · simp

/-- The slice misses the curve precisely when it misses one of the three
roots. -/
lemma slice_not_range {u : ℂ} (hu : -1 < u.re) (hn : u^ (3:ℕ) ≠ (1:ℂ)) :
    cubicSlice u ∉ Set.range trefoil := by
  intro h
  have D := (disc_iff_trefoil (cubicSlice u)).2 h
  rw [xi_cubicSlice hu, eta_cubicSlice hu] at D
  simp at D
  exact hn D

/-- The open half-plane with its three punctures. -/
abbrev CubicSliceDomain := {u : ℂ // -1 < u.re ∧ u ^ (3:ℕ) ≠ (1:ℂ)}

/-- Embedding of that plane into the true exterior. -/
def sliceExterior (u : CubicSliceDomain) : TrefoilExterior :=
  ⟨cubicSlice u.1, slice_not_range u.2.1 u.2.2⟩

lemma cubicSlice_cont : Continuous cubicSlice := by
  unfold cubicSlice
  change Continuous (fun u : ℂ =>
    (PiLp.continuousLinearEquiv (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ)).symm
      (fun i : Fin 3 => if i = (0:Fin 3) then 2 + u.re
       else if i = (1:Fin 3) then 0 else u.im))
  apply (PiLp.continuousLinearEquiv (𝕜 := ℝ) 2
      (fun _ : Fin 3 => ℝ)).symm.continuous.comp
  apply (continuous_pi_iff).2
  intro i
  change Continuous (fun u : ℂ => if i = (0:Fin 3) then 2 + u.re
       else if i = (1:Fin 3) then 0 else u.im)
  split_ifs <;> fun_prop

lemma sliceExterior_cont : Continuous sliceExterior := by
  apply Continuous.subtype_mk
  exact cubicSlice_cont.comp continuous_subtype_val

@[simp] lemma coeff_slice (u : CubicSliceDomain) :
    (trefoilCoeffs (sliceExterior u)).1 = (u.1, (1:ℂ)) := by
  change (torXi (cubicSlice u.1), torEta (cubicSlice u.1)) = _
  rw [xi_cubicSlice u.2.1, eta_cubicSlice u.2.1]

end
end KnotSupport
namespace KnotSupport
noncomputable section

def cubicBase : CubicSliceDomain :=
  ⟨(2:ℂ), by
    constructor
    · norm_num
    · norm_num⟩

@[simp] lemma cubicBase_val : (cubicBase : ℂ) = 2 := rfl
end
end KnotSupport

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/TrefoilCoordinates.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/PunctureReduction.lean
section
noncomputable section
open scoped FundamentalGroupoid Topology unitInterval ComplexConjugate
open CategoryTheory
namespace KnotSupport

/-- The projection to the transverse nonzero complex coordinate.  Keeping the
three very small maps below as continuous maps makes using `Path.map` quite
painless. -/
def cylZ : C(Cyl, Zstar) :=
  ⟨fun u => u.2, continuous_snd⟩

def punctZ : C({u : Cyl // u ≠ cylPoint}, Zstar) :=
  ⟨fun u => (u : Cyl).2, continuous_snd.comp continuous_subtype_val⟩

/-- The positive horizontal slice is entirely away from the puncture. -/
def oneCyl : C(Zstar, {u : Cyl // u ≠ cylPoint}) where
  toFun z := ⟨(Multiplicative.ofAdd (1 : ℝ), z), by
    apply prod_ne_point_left
    intro h
    exact one_ne_zero (Multiplicative.ofAdd.injective h)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Continuous.prodMk continuous_const continuous_id

@[simp] lemma oneCyl_val (z : Zstar) :
    (oneCyl z : Cyl) = (Multiplicative.ofAdd (1:ℝ), z) := rfl
@[simp] lemma punctZ_oneCyl (z : Zstar) : punctZ (oneCyl z) = z := rfl
@[simp] lemma cylInclusion_oneCyl (z : Zstar) :
    cylInclusion (oneCyl z) = (Multiplicative.ofAdd (1:ℝ), z) := rfl
@[simp] lemma cylZ_cylInclusion (u : {u : Cyl // u ≠ cylPoint}) :
    cylZ (cylInclusion u) = punctZ u := rfl

@[simp] lemma punctZ_base : punctZ cylBase = zh := rfl
@[simp] lemma oneCyl_zh : oneCyl zh = cylBase := by
  -- both proofs of missing the point are irrelevant
  apply Subtype.ext
  rfl

/-- A convenient name for the positive representative of a based path.  Its
endpoints are judgmentally closed up by `oneCyl_zh` below rather than by
transporting arbitrary endpoints. -/
def onOne (p : Path cylBase cylBase) : Path cylBase cylBase :=
  ((p.map punctZ.continuous).map oneCyl.continuous).cast
    (by simpa using oneCyl_zh) (by simpa using oneCyl_zh)

-- Sometimes it is cleaner to make the two endpoints explicit once.
@[simp] lemma onOne_apply (p : Path cylBase cylBase) (t : I) :
    onOne p t = oneCyl (punctZ (p t)) := rfl

@[simp] lemma inclusion_onOne_apply (p : Path cylBase cylBase) (t : I) :
    cylInclusion (onOne p t) =
      (Multiplicative.ofAdd (1:ℝ), punctZ (p t)) := rfl

/-- A path homotopy in the `Zstar` coordinate lifts verbatim to the positive
slice.  This is the little dimensional saving that is useful in the
puncture calculation: the square which is still hard never needs to be
approximated. -/
theorem onOne_homotopic {p q : Path cylBase cylBase}
    (h : (p.map punctZ.continuous).Homotopic
         (q.map punctZ.continuous)) :
    (onOne p).Homotopic (onOne q) := by
  -- Mapping a homotopy and then changing the (definitionally equal)
  -- endpoints is built into `pathCast`.
  have h' := h.map oneCyl
  have e : cylBase = oneCyl (punctZ cylBase) := by
    simpa using oneCyl_zh.symm
  -- do the endpoint transport on the homotopy, not on the
  -- representative paths separately
  exact Path.Homotopic.pathCast h' e e

/-- The same hypothesis is often supplied for the filled paths.  Projecting
such a square is safe -- only its one dimensional normalisation is at issue.
-/
theorem onOne_homotopic_of_filled {p q : Path cylBase cylBase}
    (h : (p.map cylInclusion.continuous).Homotopic
          (q.map cylInclusion.continuous)) :
    (onOne p).Homotopic (onOne q) := by
  have hz := h.map cylZ
  -- the two transverse-coordinate paths have literally the same
  -- functions. Their endpoints are both `zh`.
  have ep :
      ((p.map cylInclusion.continuous).map cylZ.continuous) =
         p.map punctZ.continuous := by
    ext t
    rfl
  have eq_ :
      ((q.map cylInclusion.continuous).map cylZ.continuous) =
         q.map punctZ.continuous := by
    ext t
    rfl
  rw [ep, eq_] at hz
  exact onOne_homotopic hz

/-- Only the other, one dimensional, part of the puncture calculation
remains after projection.  `Positive p` says that a path is already in the
safe open half of the cylinder. -/
def Positive (p : Path cylBase cylBase) : Prop :=
  ∀ t : I, 0 < Multiplicative.toAdd (((p t : {u : Cyl // u ≠ cylPoint}) : Cyl).1)

lemma convex_to_one_pos {r s : ℝ} (hr : 0 < r) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < (1-s)*r + s*1 := by
  by_cases h : s = 1
  · subst s; norm_num
  · have hlt : s < 1 := lt_of_le_of_ne hs1 h
    have hmul : 0 < (1-s)*r := mul_pos (sub_pos.mpr hlt) hr
    have hn : 0 ≤ s*(1:ℝ) := by simpa using hs0
    nlinarith

/-- On a positive path there is no avoidance issue at all.  Interpolate the
height to one while leaving the transverse coordinate unchanged. The proof is
spelled out because later one must not make this interpolation on a general
path--it would cross the deleted point. -/
def positiveHomotopy (p : Path cylBase cylBase) (hp : Positive p) :
    p.Homotopy (onOne p) where
  toFun := fun x =>
    ⟨(Multiplicative.ofAdd
        ((1-(x.1:ℝ)) * Multiplicative.toAdd (((p x.2 :
             {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (x.1:ℝ)*1),
       punctZ (p x.2)), by
      apply prod_ne_point_left
      intro heq
      have hreal :
          (1-(x.1:ℝ)) * Multiplicative.toAdd (((p x.2 :
             {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (x.1:ℝ)*1 = 0 := by
        -- read the impossible height after cancelling the type synonym
        exact Multiplicative.ofAdd.injective heq
      have hs0 : 0 ≤ (x.1:ℝ) := x.1.property.1
      have hs1 : (x.1:ℝ) ≤ 1 := x.1.property.2
      have good := convex_to_one_pos (hp x.2) hs0 hs1
      linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply continuous_ofAdd.comp
      have cs : Continuous (fun x : I × I => (x.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have cr : Continuous (fun x : I × I =>
          Multiplicative.toAdd (((p x.2 :
             {u : Cyl // u ≠ cylPoint}) : Cyl).1)) :=
        continuous_toAdd.comp
          (continuous_fst.comp
            (continuous_subtype_val.comp
              (p.continuous.comp continuous_snd)))
      exact ((continuous_const.sub cs).mul cr).add (cs.mul continuous_const)
    · exact punctZ.continuous.comp (p.continuous.comp continuous_snd)
  map_zero_left := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      simp
    · rfl
  map_one_left := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      simp [onOne_apply]
    · rfl
  prop' := by
    intro s t ht
    rcases ht with ht | ht
    · -- bottom endpoint of the path variable
      subst t
      apply Subtype.ext
      apply Prod.ext
      · apply Multiplicative.toAdd.injective
        change (1-(s:ℝ))* Multiplicative.toAdd ((((p (0:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (s:ℝ)*1 =
            Multiplicative.toAdd ((((p (0:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1)
        rw [p.source]
        change (1-(s:ℝ))*1 + (s:ℝ)*1 = (1:ℝ)
        ring
      · -- its transverse value is the base value
        change punctZ (p (0:I)) = (((p (0:I) : {u : Cyl // u ≠ cylPoint}) : Cyl).2)
        rfl
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      apply Prod.ext
      · apply Multiplicative.toAdd.injective
        change (1-(s:ℝ))* Multiplicative.toAdd ((((p (1:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (s:ℝ)*1 =
            Multiplicative.toAdd ((((p (1:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1)
        rw [p.target]
        change (1-(s:ℝ))*1 + (s:ℝ)*1 = (1:ℝ)
        ring
      · change punctZ (p (1:I)) = (((p (1:I) : {u : Cyl // u ≠ cylPoint}) : Cyl).2)
        rfl

theorem homotopic_onOne_of_positive (p : Path cylBase cylBase)
    (hp : Positive p) : p.Homotopic (onOne p) :=
  ⟨positiveHomotopy p hp⟩

/-- The remaining loop assertion is purely one-dimensional.  If each based
loop can be moved to *some* positive based loop, all two-dimensional squares
come for free by looking at the transverse coordinate of the filled square. -/
theorem puncture_homotopy_of_positive_replacement
    (move : ∀ p : Path cylBase cylBase,
       ∃ r : Path cylBase cylBase, Positive r ∧ p.Homotopic r) :
    ∀ (p q : Path cylBase cylBase),
      (p.map cylInclusion.continuous).Homotopic
        (q.map cylInclusion.continuous) → p.Homotopic q := by
  intro p q h
  obtain ⟨p', hp', ep⟩ := move p
  obtain ⟨q', hq', eq⟩ := move q
  have hp1 : p'.Homotopic (onOne p') := homotopic_onOne_of_positive p' hp'
  have hq1 : q'.Homotopic (onOne q') := homotopic_onOne_of_positive q' hq'
  -- transfer the given square through the excursions (which are all in the
  -- punctured space and hence can be filled), then project it.
  have hf :
      (p'.map cylInclusion.continuous).Homotopic
        (q'.map cylInclusion.continuous) :=
    (ep.symm.map cylInclusion).trans (h.trans (eq.map cylInclusion))
  have hm : (onOne p').Homotopic (onOne q') :=
    onOne_homotopic_of_filled hf
  exact ep.trans (hp1.trans (hm.trans (hq1.symm.trans eq.symm)))

/-- Weakly positive heights are also harmless.  At homotopy time zero the
original point supplies the missing disequality; at every later time the
height is strictly positive. -/
def Nonnegative (p : Path cylBase cylBase) : Prop :=
  ∀ t : I, 0 ≤ Multiplicative.toAdd (((p t : {u : Cyl // u ≠ cylPoint}) : Cyl).1)

lemma convex_to_one_pos_of_nonneg {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s)
    (hs1 : s ≤ 1) : 0 < (1-s)*r + s*1 := by
  have h1 : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have h2 : 0 ≤ (1-s)*r := mul_nonneg h1 hr
  nlinarith

def nonnegativeHomotopy (p : Path cylBase cylBase) (hp : Nonnegative p) :
    p.Homotopy (onOne p) where
  toFun := fun x =>
    ⟨(Multiplicative.ofAdd
        ((1-(x.1:ℝ)) * Multiplicative.toAdd (((p x.2 :
             {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (x.1:ℝ)*1),
       punctZ (p x.2)), by
      by_cases hs : (x.1:ℝ) = 0
      · -- at time zero this is just the old point
        intro bad
        apply (p x.2).property
        have hb1 := congrArg Prod.fst bad
        have hb2 := congrArg Prod.snd bad
        apply Prod.ext
        · -- multiply-cancel the height synonyms
          apply Multiplicative.toAdd.injective
          simpa [hs] using congrArg Multiplicative.toAdd hb1
        · exact hb2
      · apply prod_ne_point_left
        intro heq
        have hreal :
          (1-(x.1:ℝ)) * Multiplicative.toAdd (((p x.2 :
             {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (x.1:ℝ)*1 = 0 :=
          Multiplicative.ofAdd.injective heq
        have hspos : 0 < (x.1:ℝ) :=
          lt_of_le_of_ne x.1.property.1 (Ne.symm hs)
        have good := convex_to_one_pos_of_nonneg (hp x.2) hspos x.1.property.2
        linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply continuous_ofAdd.comp
      have cs : Continuous (fun x : I × I => (x.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have cr : Continuous (fun x : I × I =>
          Multiplicative.toAdd (((p x.2 :
             {u : Cyl // u ≠ cylPoint}) : Cyl).1)) :=
        continuous_toAdd.comp
          (continuous_fst.comp
            (continuous_subtype_val.comp
              (p.continuous.comp continuous_snd)))
      exact ((continuous_const.sub cs).mul cr).add (cs.mul continuous_const)
    · exact punctZ.continuous.comp (p.continuous.comp continuous_snd)
  map_zero_left := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      simp
    · rfl
  map_one_left := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      simp [onOne_apply]
    · rfl
  prop' := by
    intro s t ht
    rcases ht with ht | ht
    · subst t
      apply Subtype.ext
      apply Prod.ext
      · apply Multiplicative.toAdd.injective
        change (1-(s:ℝ))* Multiplicative.toAdd ((((p (0:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (s:ℝ)*1 =
            Multiplicative.toAdd ((((p (0:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1)
        rw [p.source]
        change (1-(s:ℝ))*1 + (s:ℝ)*1 = (1:ℝ)
        ring
      · change punctZ (p (0:I)) = (((p (0:I) : {u : Cyl // u ≠ cylPoint}) : Cyl).2)
        rfl
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      apply Prod.ext
      · apply Multiplicative.toAdd.injective
        change (1-(s:ℝ))* Multiplicative.toAdd ((((p (1:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (s:ℝ)*1 =
            Multiplicative.toAdd ((((p (1:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1)
        rw [p.target]
        change (1-(s:ℝ))*1 + (s:ℝ)*1 = (1:ℝ)
        ring
      · change punctZ (p (1:I)) = (((p (1:I) : {u : Cyl // u ≠ cylPoint}) : Cyl).2)
        rfl

/-- Thus instead of strict positivity it is enough to make a loop merely
nonnegative.  This variant is often simpler for collar arguments near the
boundary of the point. -/
theorem puncture_homotopy_of_nonnegative_replacement
    (move : ∀ p : Path cylBase cylBase,
       ∃ r : Path cylBase cylBase, Nonnegative r ∧ p.Homotopic r) :
    ∀ (p q : Path cylBase cylBase),
      (p.map cylInclusion.continuous).Homotopic
        (q.map cylInclusion.continuous) → p.Homotopic q := by
  apply puncture_homotopy_of_positive_replacement
  intro p
  obtain ⟨r, hr, hpr⟩ := move p
  refine ⟨onOne r, ?_, hpr.trans ?_⟩
  · intro t
    change 0 < (1 : ℝ)
    norm_num
  · exact ⟨nonnegativeHomotopy r hr⟩

/-- `CleanBelow` describes the only possible dangerous values of a path
when its height is pushed upwards.  Values below the deleted level must not
have the exceptional transverse coordinate.  At height zero this is already
part of the subtype, and above zero there is no obstruction. -/
def CleanBelow (p : Path cylBase cylBase) : Prop :=
  ∀ t : I, Multiplicative.toAdd (((p t : {u : Cyl // u ≠ cylPoint}) : Cyl).1) < 0 →
    punctZ (p t) ≠ zh

def cleanHomotopy (p : Path cylBase cylBase) (hp : CleanBelow p) :
    p.Homotopy (onOne p) where
  toFun := fun x =>
    ⟨(Multiplicative.ofAdd
        ((1-(x.1:ℝ)) * Multiplicative.toAdd (((p x.2 :
             {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (x.1:ℝ)*1),
       punctZ (p x.2)), by
      -- Suppose the interpolated point were the puncture.  Its
      -- transverse coordinate is unchanged.  A positive old height cannot
      -- interpolate to zero; a zero old height was already admissible; and a
      -- negative one is exactly the hypothesis `CleanBelow`.
      intro bad
      have hb1 := congrArg Prod.fst bad
      have hb2 := congrArg Prod.snd bad
      have hreal :
          (1-(x.1:ℝ)) * Multiplicative.toAdd (((p x.2 :
             {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (x.1:ℝ)*1 = 0 :=
        Multiplicative.ofAdd.injective hb1
      have hz : punctZ (p x.2) = zh := hb2
      let r : ℝ := Multiplicative.toAdd (((p x.2 :
             {u : Cyl // u ≠ cylPoint}) : Cyl).1)
      have hnotpos : ¬ 0 < r := by
        intro hr
        have good := convex_to_one_pos hr x.1.property.1 x.1.property.2
        exact (ne_of_gt good) hreal
      have hle : r ≤ 0 := le_of_not_gt hnotpos
      rcases hle.eq_or_lt with hzero | hneg
      · -- if the old height was zero, `p` itself excluded this coordinate
        apply (p x.2).property
        apply Prod.ext
        · change ((p x.2 : {u : Cyl // u ≠ cylPoint}) : Cyl).1 =
              Multiplicative.ofAdd 0
          apply Multiplicative.toAdd.injective
          exact hzero
        · exact hz
      · exact (hp x.2 hneg) hz⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply continuous_ofAdd.comp
      have cs : Continuous (fun x : I × I => (x.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have cr : Continuous (fun x : I × I =>
          Multiplicative.toAdd (((p x.2 :
             {u : Cyl // u ≠ cylPoint}) : Cyl).1)) :=
        continuous_toAdd.comp
          (continuous_fst.comp
            (continuous_subtype_val.comp
              (p.continuous.comp continuous_snd)))
      exact ((continuous_const.sub cs).mul cr).add (cs.mul continuous_const)
    · exact punctZ.continuous.comp (p.continuous.comp continuous_snd)
  map_zero_left := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      simp
    · rfl
  map_one_left := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      simp [onOne_apply]
    · rfl
  prop' := by
    intro s t ht
    rcases ht with ht | ht
    · subst t
      apply Subtype.ext
      apply Prod.ext
      · apply Multiplicative.toAdd.injective
        change (1-(s:ℝ))* Multiplicative.toAdd ((((p (0:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (s:ℝ)*1 =
            Multiplicative.toAdd ((((p (0:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1)
        rw [p.source]
        change (1-(s:ℝ))*1 + (s:ℝ)*1 = (1:ℝ)
        ring
      · change punctZ (p (0:I)) = (((p (0:I) : {u : Cyl // u ≠ cylPoint}) : Cyl).2)
        rfl
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      apply Prod.ext
      · apply Multiplicative.toAdd.injective
        change (1-(s:ℝ))* Multiplicative.toAdd ((((p (1:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1) + (s:ℝ)*1 =
            Multiplicative.toAdd ((((p (1:I)) : {u : Cyl // u ≠ cylPoint}) : Cyl).1)
        rw [p.target]
        change (1-(s:ℝ))*1 + (s:ℝ)*1 = (1:ℝ)
        ring
      · change punctZ (p (1:I)) = (((p (1:I) : {u : Cyl // u ≠ cylPoint}) : Cyl).2)
        rfl


/-- Reducing the relative square all the way to a one dimensional cleaning
of its boundary. No regularity of the given square is required. -/
theorem puncture_homotopy_of_clean_replacement
    (move : ∀ p : Path cylBase cylBase,
       ∃ r : Path cylBase cylBase, CleanBelow r ∧ p.Homotopic r) :
    ∀ (p q : Path cylBase cylBase),
      (p.map cylInclusion.continuous).Homotopic
        (q.map cylInclusion.continuous) → p.Homotopic q := by
  apply puncture_homotopy_of_positive_replacement
  intro p
  obtain ⟨r, hr, hpr⟩ := move p
  refine ⟨onOne r, ?_, hpr.trans ?_⟩
  · intro t
    change 0 < (1:ℝ)
    norm_num
  · exact ⟨cleanHomotopy r hr⟩

/-- The offending transverse values of a particular path are separated away
from level zero.  This elementary compactness point is easy to miss: the set
of such times is closed in the unit interval; approaching a limit at height
zero would put the old path through the deleted point.  Later detours may
therefore be made in a *strictly* negative band. -/
def cylHeight (p : Path cylBase cylBase) (t : I) : ℝ :=
  Multiplicative.toAdd (((p t : {u : Cyl // u ≠ cylPoint}) : Cyl).1)

lemma continuous_cylHeight (p : Path cylBase cylBase) :
    Continuous (cylHeight p) := by
  exact continuous_toAdd.comp
    (continuous_fst.comp
      (continuous_subtype_val.comp p.continuous))

lemma continuous_punctZ_path (p : Path cylBase cylBase) :
    Continuous (fun t : I => punctZ (p t)) :=
  punctZ.continuous.comp p.continuous

lemma height_ne_zero_of_exceptional (p : Path cylBase cylBase)
    (t : I) (ht : punctZ (p t) = zh) : cylHeight p t ≠ 0 := by
  intro hz0
  apply (p t).property
  apply Prod.ext
  · change ((p t : {u : Cyl // u ≠ cylPoint}) : Cyl).1 =
        Multiplicative.ofAdd 0
    apply Multiplicative.toAdd.injective
    exact hz0
  · exact ht

theorem exceptional_has_margin (p : Path cylBase cylBase) :
    ∃ d : ℝ, 0 < d ∧
      ∀ t : I, punctZ (p t) = zh → d ≤ |cylHeight p t| := by
  classical
  let K : Set I := {t | punctZ (p t) = zh}
  have hKclosed : IsClosed K := by
    change IsClosed ((fun t : I => punctZ (p t)) ⁻¹' ({zh} : Set Zstar))
    exact isClosed_singleton.preimage (continuous_punctZ_path p)
  have hK : IsCompact K := hKclosed.isCompact
  by_cases hn : K.Nonempty
  · have hf : Continuous (fun t : I => |cylHeight p t|) :=
      (continuous_cylHeight p).abs
    obtain ⟨t0, ht0, hmin⟩ := hK.exists_isMinOn hn hf.continuousOn
    have hval : 0 < |cylHeight p t0| :=
      abs_pos.mpr (height_ne_zero_of_exceptional p t0 ht0)
    refine ⟨|cylHeight p t0|, hval, ?_⟩
    intro t ht
    exact hmin ht
  · refine ⟨1, by norm_num, ?_⟩
    intro t ht
    exfalso
    apply hn
    exact ⟨t, ht⟩

theorem exceptional_negative_band (p : Path cylBase cylBase) :
    ∃ d : ℝ, 0 < d ∧
      ∀ t : I, cylHeight p t < 0 → punctZ (p t) = zh →
          cylHeight p t ≤ -d := by
  obtain ⟨d, hd, hall⟩ := exceptional_has_margin p
  refine ⟨d, hd, ?_⟩
  intro t hneg hzh
  have h := hall t hzh
  have ha : |cylHeight p t| = -(cylHeight p t) :=
    abs_of_neg hneg
  rw [ha] at h
  linarith

lemma transverse_pair_avoid (p : Path cylBase cylBase)
    (t : I) (z : Zstar)
    (hz : cylHeight p t = 0 → z ≠ zh) :
    (((((p t : {u : Cyl // u ≠ cylPoint}) : Cyl).1), z) : Cyl) ≠ cylPoint := by
  intro bad
  have h1 := congrArg Prod.fst bad
  have h2 := congrArg Prod.snd bad
  apply (hz ?_) h2
  change Multiplicative.toAdd ((((p t : {u : Cyl // u ≠ cylPoint}) : Cyl).1)) = 0
  change ((p t : {u : Cyl // u ≠ cylPoint}) : Cyl).1 =
       Multiplicative.ofAdd 0 at h1
  exact (by simpa using congrArg Multiplicative.toAdd h1)

/-- A precise interface for the as yet one-dimensional detour.  The height
coordinate never needs to be changed.  It is enough to supply a homotopy of
the transverse *path*.  Over the zero slice it must avoid `zh`; in the final
path it must do so at all negative heights.  Notice that the old square no
longer appears here at all. -/
theorem exists_clean_of_transverse
    (p : Path cylBase cylBase)
    (Z : C(I × I, Zstar))
    (z0 : ∀ t : I, Z (0,t) = punctZ (p t))
    (zend0 : ∀ s : I, Z (s,0) = zh)
    (zend1 : ∀ s : I, Z (s,1) = zh)
    (zedge : ∀ s t : I, cylHeight p t = 0 → Z (s,t) ≠ zh)
    (zclean : ∀ t : I, cylHeight p t < 0 → Z (1,t) ≠ zh) :
    ∃ r : Path cylBase cylBase, CleanBelow r ∧ p.Homotopic r := by
  let r : Path cylBase cylBase :=
    { toFun := fun t =>
        ⟨(((((p t : {u : Cyl // u ≠ cylPoint}) : Cyl).1), Z (1,t)) : Cyl),
          transverse_pair_avoid p t (Z (1,t)) (zedge 1 t)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.prodMk
        · exact continuous_fst.comp
              (continuous_subtype_val.comp p.continuous)
        · exact Z.continuous.comp (Continuous.prodMk continuous_const continuous_id)
      source' := by
        apply Subtype.ext
        apply Prod.ext
        · change ((p (0:I) : {u : Cyl // u ≠ cylPoint}) : Cyl).1 =
               (((cylBase : {u : Cyl // u ≠ cylPoint}) : Cyl).1)
          exact congrArg (fun u : {u : Cyl // u ≠ cylPoint} =>
               ((u : Cyl).1)) p.source
        · change Z (1,0) = zh
          exact zend0 1
      target' := by
        apply Subtype.ext
        apply Prod.ext
        · change ((p (1:I) : {u : Cyl // u ≠ cylPoint}) : Cyl).1 =
               (((cylBase : {u : Cyl // u ≠ cylPoint}) : Cyl).1)
          exact congrArg (fun u : {u : Cyl // u ≠ cylPoint} =>
               ((u : Cyl).1)) p.target
        · change Z (1,1) = zh
          exact zend1 1 }
  refine ⟨r, ?_, ?_⟩
  · intro t hn
    change Z (1,t) ≠ zh
    apply zclean
    exact hn
  · -- keep the old height throughout this homotopy
    refine ⟨{
      toFun := fun x =>
        ⟨(((((p x.2 : {u : Cyl // u ≠ cylPoint}) : Cyl).1),
                   Z (x.1,x.2)) : Cyl),
          transverse_pair_avoid p x.2 (Z (x.1,x.2))
             (zedge x.1 x.2)⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · apply Continuous.subtype_mk
      apply Continuous.prodMk
      · exact continuous_fst.comp
              (continuous_subtype_val.comp (p.continuous.comp continuous_snd))
      · exact Z.continuous
    · intro t
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact z0 t
    · intro t
      rfl
    · intro s t ht
      rcases ht with ht | ht
      · subst t
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · -- the relative endpoints follow the old path
          change Z (s,0) = (((p (0:I) : {u : Cyl // u ≠ cylPoint}) : Cyl).2)
          rw [p.source]
          exact zend0 s
      · rw [Set.mem_singleton_iff] at ht
        subst t
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · change Z (s,1) = (((p (1:I) : {u : Cyl // u ≠ cylPoint}) : Cyl).2)
          rw [p.target]
          exact zend1 s

lemma no_exception_near_zero {p : Path cylBase cylBase} {d : ℝ}
    (hd : 0 < d)
    (hband : ∀ t : I, cylHeight p t < 0 → punctZ (p t) = zh →
          cylHeight p t ≤ -d) :
    ∀ t : I, -d < cylHeight p t →
       cylHeight p t ≤ 0 → punctZ (p t) ≠ zh := by
  intro t hlo hhi hzh
  by_cases hz : cylHeight p t = 0
  · exact height_ne_zero_of_exceptional p t hzh hz
  · have hn : cylHeight p t < 0 := lt_of_le_of_ne hhi hz
    have hb := hband t hn hzh
    exact (not_le_of_gt hlo) hb

/-- There is no cross-dimensional issue when the path was already clean. This
simple branch is useful when decomposing excursions. -/
theorem transverse_of_clean (p : Path cylBase cylBase) (hp : CleanBelow p) :
    ∃ Z : C(I × I, Zstar),
      (∀ t, Z (0,t) = punctZ (p t)) ∧
      (∀ s, Z (s,0) = zh) ∧
      (∀ s, Z (s,1) = zh) ∧
      (∀ s t, cylHeight p t = 0 → Z (s,t) ≠ zh) ∧
      (∀ t, cylHeight p t < 0 → Z (1,t) ≠ zh) := by
  let Z : C(I × I, Zstar) :=
    ⟨fun x => punctZ (p x.2),
      (continuous_punctZ_path p).comp continuous_snd⟩
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; rfl
  · intro s
    change punctZ (p (0:I)) = zh
    rw [p.source]
    rfl
  · intro s
    change punctZ (p (1:I)) = zh
    rw [p.target]
    rfl
  · intro s t ht hbad
    exact (height_ne_zero_of_exceptional p t hbad) ht
  · intro t hn
    exact hp t hn

end KnotSupport

end

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/PunctureReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/TrefoilDetector.lean
section

/-! A precise target for a computation in the cubic plane.  A covering is
used only as a detector for two *drawn* loops; no assertion about a
presentation or surjectivity of a fundamental group is smuggled into the
reduction.  In particular this lemma is useful even for a covering much
larger than the root covering. -/
open CategoryTheory
open scoped FundamentalGroupoid
namespace KnotSupport
noncomputable section

/-- Monodromy is a useful way of disproving commutativity without making any
path representatives choices in a fundamental group. Multiplication in a
vertex group is reverse path-concatenation. -/
theorem not_FGAbelian_of_covering_detector
    {X D E : Type*} [TopologicalSpace X] [TopologicalSpace D]
      [TopologicalSpace E]
    (f : C(X,D)) {pr : E → D} (cov : IsCoveringMap pr)
    (x : X) (e : E) (he : pr e = f x)
    (a b : Path x x)
    (hne : cov.monodromy
          ((Path.Homotopic.Quotient.mk (b.trans a)).map f) ⟨e, he⟩ ≠
        cov.monodromy
          ((Path.Homotopic.Quotient.mk (a.trans b)).map f) ⟨e, he⟩) :
    ¬ FGAbelian X := by
  apply not_FGAbelian_of_pair x
    (FundamentalGroup.fromPath (.mk a))
    (FundamentalGroup.fromPath (.mk b))
  intro eq
  apply hne
  have eq' : (Path.Homotopic.Quotient.mk (b.trans a)) =
             (Path.Homotopic.Quotient.mk (a.trans b)) := by exact eq
  have eq'' := congrArg (fun u : Path.Homotopic.Quotient x x =>
     cov.monodromy (u.map f)) eq'
  have eq3 := congrFun eq'' (⟨e, he⟩ : (Set.preimage pr ({f x} : Set D)))
  simpa using eq3

/-- The half-plane map as a continuous map. -/
def sliceCM : C(CubicSliceDomain, TrefoilExterior) :=
  ⟨sliceExterior, sliceExterior_cont⟩

def coeffCM : C(TrefoilExterior, CubicGood) :=
  ⟨trefoilCoeffs, trefoilCoeffs_cont⟩

/-- It is enough to draw the two loops in the one half-plane `v=1` and
calculate their lifts in a cover of the depressed cubics.  This is often much
more convenient than choosing meridians in a quotient of loops in a
three-manifold. Notice that `q` below is a covering of the fixed, explicit
open subset `u^3≠v^2` of `ℂ²`; it has no mention of the knot. -/
theorem trefoil_not_FGAbelian_of_slice_monodromy
    {E : Type*} [TopologicalSpace E]
    {pr : E → CubicGood} (cov : IsCoveringMap pr)
    (u : CubicSliceDomain) (e : E)
    (he : pr e = trefoilCoeffs (sliceExterior u))
    (A B : Path u u)
    (hne : cov.monodromy
        ((Path.Homotopic.Quotient.mk
          (((B.map sliceExterior_cont).trans (A.map sliceExterior_cont)))).map
            coeffCM) ⟨e, he⟩ ≠
      cov.monodromy
        ((Path.Homotopic.Quotient.mk
          (((A.map sliceExterior_cont).trans (B.map sliceExterior_cont)))).map
            coeffCM) ⟨e, he⟩) :
    ¬ FGAbelian TrefoilExterior := by
  exact not_FGAbelian_of_covering_detector coeffCM cov
    (sliceExterior u) e he
    (A.map sliceExterior_cont) (B.map sliceExterior_cont) hne

end
end KnotSupport

namespace KnotSupport
noncomputable section

/-- Splitting cover of depressed cubics with one marked root. This is the
canonical three-sheeted detector suggested by the slice `v=1`. The local
covering assertion is deliberately separate from the topological reduction
above. -/
def CubicRoot : Type :=
  {z : CubicGood × ℂ //
    z.2 ^ (3:ℕ) - (3:ℂ) * (z.1.1.1) * z.2 + (2:ℂ) * (z.1.1.2) = 0}

instance : TopologicalSpace CubicRoot := inferInstanceAs
  (TopologicalSpace
    {z : CubicGood × ℂ //
      z.2 ^ (3:ℕ) - (3:ℂ) * (z.1.1.1) * z.2 + (2:ℂ) * (z.1.1.2) = 0})

def rootPr : CubicRoot → CubicGood := fun z => z.1.1

end
end KnotSupport

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/TrefoilDetector.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/CubicCover.lean
section

open Set Function Filter Topology
noncomputable section
namespace KnotSupport

/-- Writing a depressed cubic as first coordinate plus the marked root.  The equation
`z^3-3uz+2v=0` can be solved for `v`; this elementary triangular polynomial is useful
for the local calculation. -/
def cubicMap (x : ℂ × ℂ) : ℂ × ℂ :=
  (x.1, ((3:ℂ) * x.1 * x.2 - x.2^3) / 2)

def cubicGoodSet : Set (ℂ × ℂ) := {x | x.1 ^ (3:ℕ) ≠ x.2 ^ (2:ℕ)}

@[fun_prop] lemma cubicMap_cont : Continuous cubicMap := by
  unfold cubicMap
  fun_prop

@[simp] lemma cubicMap_fst (x : ℂ × ℂ) : (cubicMap x).1 = x.1 := rfl
@[simp] lemma cubicMap_snd (x : ℂ × ℂ) :
    (cubicMap x).2 = ((3:ℂ) * x.1 * x.2 - x.2^3) / 2 := rfl

lemma critical_not_good {x : ℂ × ℂ} (h : cubicMap x ∈ cubicGoodSet) :
    x.1 ≠ x.2^2 := by
  intro hx
  have hv : (cubicMap x).2 = x.2^3 := by
    dsimp [cubicMap]
    rw [hx]
    ring
  have hu : (cubicMap x).1 = x.2^2 := by simpa [cubicMap, hx]
  exact h (by
    rw [hu, hv]
    ring)

/-- The complex-linear derivative of the triangular polynomial. -/
def cubicLin (x : ℂ × ℂ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun d := (d.1, ((3:ℂ)* x.2 / 2) * d.1 +
                    (((3:ℂ) * x.1 - 3 * x.2^2) / 2) * d.2)
  map_add' a b := by ext <;> dsimp <;> ring
  map_smul' c a := by ext <;> dsimp <;> ring

/-- The continuous version (finite dimensional, the formula is manifestly continuous). -/
def cubicCLM (x : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  { cubicLin x with
    cont := by
      -- both coordinates are elementary linear combinations
      fun_prop }

@[simp] lemma cubicCLM_apply (x d : ℂ × ℂ) :
    cubicCLM x d = (d.1, ((3:ℂ)* x.2 / 2) * d.1 +
                    (((3:ℂ) * x.1 - 3 * x.2^2) / 2) * d.2) := rfl

@[fun_prop] lemma cubicMap_smooth : ContDiff ℂ (⊤ : ℕ∞) cubicMap := by
  unfold cubicMap
  fun_prop

/-- Direct differentiation of the triangular formula. -/
lemma cubicMap_deriv (x : ℂ × ℂ) : HasFDerivAt cubicMap (cubicCLM x) x := by
  have h1 : HasFDerivAt (fun q : ℂ × ℂ => q.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) x := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : ℂ × ℂ => q.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) x := hasFDerivAt_snd
  have hmul := (h1.const_mul (3:ℂ)).mul h2
  have hp := h2.pow 3
  have hv := hmul.sub hp
  have hv' := hv.mul_const ( (2:ℂ)⁻¹ )
  have H := h1.prodMk hv'
  convert H using 1 <;> try {rfl}
  · apply ContinuousLinearMap.ext
    rintro ⟨a,b⟩
    ext <;> dsimp [cubicCLM, cubicLin] <;> simp <;> ring



private lemma __CubicCover_cubic_b_ne {x : ℂ × ℂ} (h : x.1 ≠ x.2^2) :
    (((3:ℂ) * x.1 - 3 * x.2^2) / 2) ≠ 0 := by
  intro e
  have e' : x.1 = x.2^2 := by
    apply (mul_left_cancel₀ (by norm_num : (3:ℂ) ≠ 0))
    -- clear denominator in the displayed equality
    have := e
    field_simp at this
    -- 3*x.1 - 3*x.2^2 = 0
    linear_combination this
  exact h e'

/-- Off the critical locus the derivative is an isomorphism. We keep an explicit inverse
so that the inverse function theorem below doesn't need matrix automation. -/
def cubicCLE (x : ℂ × ℂ) (h : x.1 ≠ x.2^2) :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := by
  let a : ℂ := (3:ℂ) * x.2 / 2
  let b : ℂ := ((3:ℂ) * x.1 - 3 * x.2^2) / 2
  have hb : b ≠ 0 := __CubicCover_cubic_b_ne h
  let L : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) := cubicLin x
  let inv : (ℂ × ℂ) → (ℂ × ℂ) := fun y => (y.1, (y.2 - a*y.1) / b)
  let E : (ℂ × ℂ) ≃ₗ[ℂ] (ℂ × ℂ) :=
    LinearEquiv.mk L inv (by
      intro y
      rcases y with ⟨u,z⟩
      dsimp [inv, L, cubicLin]
      change (u, ((a*u + b*z) - a*u) / b) = (u,z)
      ext <;> dsimp <;> field_simp <;> ring)
      (by
        intro y
        rcases y with ⟨u,v⟩
        dsimp [inv, L, cubicLin]
        change (u, a*u + b*((v-a*u)/b)) = (u,v)
        ext <;> dsimp <;> field_simp <;> ring)
  exact ContinuousLinearEquiv.mk E (by
    change Continuous (fun y : ℂ × ℂ =>
        (y.1, ((3:ℂ)*x.2/2)*y.1 +
          (((3:ℂ)*x.1-3*x.2^2)/2)*y.2))
    fun_prop)
    (by
      change Continuous (fun y : ℂ × ℂ => (y.1, (y.2 - a*y.1)/b))
      fun_prop)

@[simp] lemma cubicCLE_coe (x : ℂ × ℂ) (h : x.1 ≠ x.2^2) :
    (cubicCLE x h : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) = cubicCLM x := by
  apply ContinuousLinearMap.ext
  rintro ⟨u,z⟩
  rfl

/-- Every noncritical point of the triangular polynomial has a local inverse. -/
lemma cubicMap_local (x : ℂ × ℂ) (hx : cubicMap x ∈ cubicGoodSet) :
    ∃ φ : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ),
      x ∈ φ.source ∧ (φ : (ℂ × ℂ) → (ℂ × ℂ)) = cubicMap := by
  have hn := critical_not_good hx
  let E := cubicCLE x hn
  have der : HasFDerivAt cubicMap (E : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) x := by
    rw [cubicCLE_coe]
    exact cubicMap_deriv x
  let φ := (cubicMap_smooth.contDiffAt).toOpenPartialHomeomorph cubicMap der (by
    exact (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0))
  refine ⟨φ, ?_, rfl⟩
  exact ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _


open Polynomial
private def __CubicCover_cubPoly (y : ℂ × ℂ) : ℂ[X] :=
  X^3 - C ((3:ℂ)*y.1) * X + C ((2:ℂ)*y.2)

private lemma __CubicCover_cubPoly_monic (y : ℂ × ℂ) : (__CubicCover_cubPoly y).Monic := by
  unfold __CubicCover_cubPoly
  monicity <;> norm_num

private lemma __CubicCover_cubPoly_eval (y : ℂ × ℂ) (z : ℂ) :
    (__CubicCover_cubPoly y).eval z = z^3 - 3*y.1*z + 2*y.2 := by
  simp [__CubicCover_cubPoly]

lemma cubicMap_fiber_finite (y : ℂ × ℂ) :
    (cubicMap ⁻¹' ({y} : Set (ℂ × ℂ))).Finite := by
  let S : Set (ℂ × ℂ) := ({y.1} : Set ℂ) ×ˢ ((__CubicCover_cubPoly y).rootSet ℂ)
  have hs : S.Finite := (Set.finite_singleton _).prod ((__CubicCover_cubPoly y).rootSet_finite ℂ)
  apply hs.subset
  intro x hx
  have eqy : cubicMap x = y := hx
  have h1 : x.1 = y.1 := by simpa [cubicMap] using congrArg Prod.fst eqy
  have h2 : ((3:ℂ)*x.1*x.2 - x.2^3)/2 = y.2 := congrArg Prod.snd eqy
  have hz : (__CubicCover_cubPoly y).eval x.2 = 0 := by
    rw [__CubicCover_cubPoly_eval]
    rw [← h1]
    linear_combination -2 * h2
  refine ⟨by simpa [h1], (Polynomial.mem_rootSet.mpr ⟨(__CubicCover_cubPoly_monic y).ne_zero, ?_⟩)⟩
  simpa using hz


lemma cubicMap_closed : IsClosedMap cubicMap := by
  apply IsProperMap.isClosedMap
  apply (isProperMap_iff_isCompact_preimage).2
  refine ⟨cubicMap_cont, ?_⟩
  intro K hK
  have hb1 := (hK.image (continuous_fst)).isBounded.subset_closedBall (0:ℂ)
  have hb2 := (hK.image (continuous_snd)).isBounded.subset_closedBall (0:ℂ)
  obtain ⟨R, hR⟩ := hb1
  obtain ⟨S, hS⟩ := hb2
  apply Metric.isCompact_iff_isClosed_bounded.2
  constructor
  · exact hK.isClosed.preimage cubicMap_cont
  · apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ × ℂ)).2
    refine ⟨max R (3*R+2*S+1), ?_⟩
    intro x hx
    have xu : ‖x.1‖ ≤ R := by
      have kx : x.1 ∈ Prod.fst '' K := ⟨cubicMap x, hx, rfl⟩
      have m := hR kx
      simpa using m
    have xv : ‖(cubicMap x).2‖ ≤ S := by
      have kx : (cubicMap x).2 ∈ Prod.snd '' K := ⟨cubicMap x, hx, rfl⟩
      have m := hS kx
      simpa using m
    have alg : x.2^3 = (3:ℂ)*x.1*x.2 - 2*(cubicMap x).2 := by
      dsimp [cubicMap]
      ring
    have ineq : ‖x.2‖^3 ≤ 3*‖x.1‖*‖x.2‖ + 2*‖(cubicMap x).2‖ := by
      calc
        ‖x.2‖^3 = ‖x.2^3‖ := by rw [norm_pow]
        _ = ‖(3:ℂ)*x.1*x.2 - 2*(cubicMap x).2‖ := by rw [alg]
        _ ≤ ‖(3:ℂ)*x.1*x.2‖ + ‖(2:ℂ)*(cubicMap x).2‖ := norm_sub_le _ _
        _ = 3*‖x.1‖*‖x.2‖ + 2*‖(cubicMap x).2‖ := by
          rw [norm_mul, norm_mul, norm_mul]
          norm_num
    have zbound : ‖x.2‖ ≤ 3*R+2*S+1 := by
      by_contra bad
      have zbig : 3*R+2*S+1 < ‖x.2‖ := lt_of_not_ge bad
      have nonnegU := norm_nonneg x.1
      have nonnegV := norm_nonneg (cubicMap x).2
      have nonnegZ := norm_nonneg x.2
      have RU : 0 ≤ R := le_trans nonnegU xu
      have SV : 0 ≤ S := le_trans nonnegV xv
      have zz : 3*‖x.1‖*‖x.2‖ + 2*‖(cubicMap x).2‖ ≤
          3*R*‖x.2‖ + 2*S := by
        gcongr
      have iz := le_trans ineq zz
      have one : 1 ≤ ‖x.2‖ := by nlinarith
      have temp : 3*R*‖x.2‖ + 2*S ≤ (3*R+2*S)*‖x.2‖ := by nlinarith
      have square : 3*R+2*S < ‖x.2‖^2 := by nlinarith
      have mul := mul_lt_mul_of_pos_right square (by linarith : 0 < ‖x.2‖)
      nlinarith
    change dist x 0 ≤ _
    rw [Prod.dist_eq]
    change max (dist x.1 0) (dist x.2 0) ≤ _
    simpa [dist_zero_right] using
      (max_le (le_max_of_le_left xu) (le_max_of_le_right zbound))


lemma cubicMap_cover_on : IsCoveringMapOn cubicMap cubicGoodSet := by
  apply cubicMap_closed.isCoveringMapOn_of_openPartialHomeomorph
  · intro x hx
    exact cubicMap_fiber_finite x
  · intro e he
    exact cubicMap_local e he


end KnotSupport

end

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/CubicCover.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/PathDetour.lean
section
noncomputable section
open scoped Topology unitInterval ComplexConjugate
open Set
namespace KnotSupport

/-! An elementary polygonal detour lemma.  The parameter of the last
remaining puncture argument is only an interval.  It is useful to record a
small, quantitative form of the familiar fact that a path in a plane can be
made to miss a prescribed point. -/

def cdet (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re
def cperp (u : ℂ) : ℂ := ⟨-u.im, u.re⟩

private lemma __PathDetour_cperp_re (u : ℂ) : (cperp u).re = -u.im := rfl
private lemma __PathDetour_cperp_im (u : ℂ) : (cperp u).im = u.re := rfl

private lemma __PathDetour_norm_cperp (u : ℂ) : ‖cperp u‖ = ‖u‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp [Complex.normSq, cperp]
  ring

private lemma __PathDetour_cdet_perp (u : ℂ) : cdet u (cperp u) = u.re^2 + u.im^2 := by
  simp [cdet, cperp]
  ring

private lemma __PathDetour_re_smul (x : ℝ) (z : ℂ) : ((x : ℂ) * z).re = x * z.re := by
  simp [Complex.mul_re]
private lemma __PathDetour_im_smul (x : ℝ) (z : ℂ) : ((x : ℂ) * z).im = x * z.im := by
  simp [Complex.mul_im]

private lemma __PathDetour_cdet_add_right (u v w : ℂ) : cdet u (v+w) = cdet u v + cdet u w := by
  simp [cdet]
  ring
private lemma __PathDetour_cdet_sub_right (u v w : ℂ) : cdet u (v-w) = cdet u v - cdet u w := by
  simp [cdet]
  ring
private lemma __PathDetour_cdet_smul_right (u v : ℂ) (x : ℝ) :
    cdet u ((x:ℂ)*v) = x * cdet u v := by
  simp [cdet, Complex.mul_re, Complex.mul_im]
  ring
private lemma __PathDetour_cdet_self (u : ℂ) : cdet u u = 0 := by unfold cdet; ring
private lemma __PathDetour_cdet_zero_right (u : ℂ) : cdet u 0 = 0 := by simp [cdet]

private lemma __PathDetour_normsq_pos {u : ℂ} (hu : u ≠ 0) : 0 < u.re^2 + u.im^2 := by
  have : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  convert this using 1 <;> simp [Complex.normSq] <;> ring

/-- One can choose the next vertex as close as desired to a given point, and
not collinear with the last vertex and the forbidden point.  The two tiny
perpendicular displacements are a convenient constructive density proof. -/
private lemma __PathDetour_nextVertex (a z v : ℂ) (hv : v ≠ a) {e : ℝ} (he : 0 < e) :
    ∃ w : ℂ, ‖w-z‖ < e ∧ w ≠ a ∧ cdet (v-a) (w-a) ≠ 0 := by
  let u : ℂ := v-a
  have hu : u ≠ 0 := sub_ne_zero.mpr hv
  have hsq : 0 < u.re^2 + u.im^2 := __PathDetour_normsq_pos hu
  let q : ℝ := e / (4 * (‖u‖ + 1))
  have hnu : 0 ≤ ‖u‖ := norm_nonneg _
  have hden : 0 < (4:ℝ) * (‖u‖ + 1) := by positivity
  have hq : 0 < q := div_pos he hden
  let w₁ : ℂ := z + (q : ℂ) * cperp u
  let w₂ : ℂ := z + ((2*q : ℝ) : ℂ) * cperp u
  have hsmall : 2*q*‖u‖ < e := by
    dsimp [q]
    -- the factor is strictly below one even when `u` is large
    have hlt : ‖u‖ < ‖u‖ + 1 := by linarith
    calc
      2 * (e / (4 * (‖u‖ + 1))) * ‖u‖ = e * (‖u‖ / (2*(‖u‖+1))) := by field_simp; ring
      _ < e := by
        have : ‖u‖ / (2*(‖u‖+1)) < (1:ℝ) := by
          apply (div_lt_one (by positivity)).2
          linarith
        have hn : 0 ≤ ‖u‖ / (2*(‖u‖+1)) := by positivity
        nlinarith
  have hn1 : ‖w₁ - z‖ < e := by
    dsimp [w₁]
    rw [add_sub_cancel_left]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, __PathDetour_norm_cperp]
    nlinarith
  have hn2 : ‖w₂ - z‖ < e := by
    dsimp [w₂]
    rw [add_sub_cancel_left]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2*q), __PathDetour_norm_cperp]
    nlinarith
  have hd1 : cdet u (w₁-a) = cdet u (z-a) + q*(u.re^2+u.im^2) := by
    change cdet u ((z + (q:ℂ)*cperp u) - a) = _
    rw [show (z + (q:ℂ)*cperp u) - a = (z-a) + (q:ℂ)*cperp u by ring]
    rw [__PathDetour_cdet_add_right, __PathDetour_cdet_smul_right, __PathDetour_cdet_perp]
  have hd2 : cdet u (w₂-a) = cdet u (z-a) + (2*q)*(u.re^2+u.im^2) := by
    change cdet u ((z + ((2*q:ℝ):ℂ)*cperp u) - a) = _
    rw [show (z + ((2*q:ℝ):ℂ)*cperp u) - a = (z-a) + ((2*q:ℝ):ℂ)*cperp u by ring]
    rw [__PathDetour_cdet_add_right, __PathDetour_cdet_smul_right, __PathDetour_cdet_perp]
  by_cases h : cdet u (w₁-a) = 0
  · refine ⟨w₂, hn2, ?_, ?_⟩
    · intro hw
      -- noncollinearity implies this as well
      have : cdet u (w₂-a) ≠ 0 := by
        rw [hd1] at h
        rw [hd2]
        nlinarith
      simpa [hw, sub_self, __PathDetour_cdet_zero_right] using this
    · rw [show v-a = u from rfl]
      rw [hd1] at h
      rw [hd2]
      nlinarith
  · refine ⟨w₁, hn1, ?_, ?_⟩
    · intro hw
      apply h
      simp [hw, sub_self, __PathDetour_cdet_zero_right]
    · exact h

/-- For the first interior vertex there is no previous direction. -/
private lemma __PathDetour_firstVertex (a z : ℂ) {e : ℝ} (he : 0 < e) :
    ∃ w : ℂ, ‖w-z‖ < e ∧ w ≠ a := by
  by_cases h : z ≠ a
  · exact ⟨z, by simpa using he, h⟩
  · let w : ℂ := z + (e/2 : ℝ)
    refine ⟨w, ?_, ?_⟩
    · dsimp [w]
      rw [add_sub_cancel_left]
      norm_cast
      rw [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < e/2)]
      linarith
    · intro hw
      have hz : z = a := not_ne_iff.mp h
      change z + (e/2 : ℝ) = a at hw
      rw [hz] at hw
      have hh : ((e/2:ℝ):ℂ) = 0 := by
        calc
          ((e/2:ℝ):ℂ) = (a + ((e/2:ℝ):ℂ)) - a := by ring
          _ = a-a := congrArg (fun x : ℂ => x-a) hw
          _ = 0 := sub_self a
      have hhreal : (e/2:ℝ) = 0 := by exact_mod_cast hh
      linarith

/-- If two direction vectors are not collinear, the open line segment cannot
contain the origin. -/
private lemma __PathDetour_segment_ne {u v : ℂ} (hd : cdet u v ≠ 0)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (((1-x : ℝ):ℂ)*u + (x:ℂ)*v) ≠ 0 := by
  intro hh
  have hdet := congrArg (fun y : ℂ => cdet u y) hh
  rw [__PathDetour_cdet_add_right, __PathDetour_cdet_smul_right, __PathDetour_cdet_self, __PathDetour_cdet_smul_right,
      __PathDetour_cdet_zero_right] at hdet
  by_cases hx : x = 0
  · subst x
    have := hd
    -- a zero first vector would force zero determinant, but the displayed
    -- equation at x=0 says exactly that.
    simp at hh
    subst u
    exact hd (by simp [cdet])
  · have hp : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    exact (mul_ne_zero hp.ne' hd) (by simpa using hdet)

private def __PathDetour_hat (n k : ℕ) (x : ℝ) : ℝ :=
  max 0 (1 - |(n:ℝ)*x - (k:ℝ)|)

private lemma __PathDetour_hat_cont (n k : ℕ) : Continuous (__PathDetour_hat n k) := by
  unfold __PathDetour_hat
  fun_prop

private def __PathDetour_poly (n : ℕ) (w : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), ((__PathDetour_hat n k x : ℝ) : ℂ) * w k

private lemma __PathDetour_poly_cont (n : ℕ) (w : ℕ → ℂ) : Continuous (__PathDetour_poly n w) := by
  unfold __PathDetour_poly
  apply continuous_finset_sum
  intro k hk
  exact ((Complex.continuous_ofReal.comp (__PathDetour_hat_cont n k)).mul continuous_const)

-- The two hats meeting a mesh interval.
private lemma __PathDetour_hat_left {n j : ℕ} (hn : 0 < n)
    {x : ℝ} (hlo : (j:ℝ)/(n:ℝ) ≤ x)
    (hhi : x ≤ (j+1:ℕ)/(n:ℝ)) :
    __PathDetour_hat n j x = (j+1:ℕ) - (n:ℝ)*x := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have A : (j:ℝ) ≤ (n:ℝ)*x := by
    have aa := (div_le_iff₀ hn').1 hlo
    nlinarith
  have B : (n:ℝ)*x ≤ (j:ℝ)+1 := by
    have aa := (le_div_iff₀ hn').1 hhi
    push_cast at aa
    nlinarith
  have C : 0 ≤ (n:ℝ)*x - (j:ℝ) := sub_nonneg.mpr A
  have D : (n:ℝ)*x - (j:ℝ) ≤ 1 := by linarith
  unfold __PathDetour_hat
  rw [abs_of_nonneg C]
  rw [max_eq_right]
  all_goals push_cast
  all_goals linarith

private lemma __PathDetour_hat_right {n j : ℕ} (hn : 0 < n)
    {x : ℝ} (hlo : (j:ℝ)/(n:ℝ) ≤ x)
    (hhi : x ≤ (j+1:ℕ)/(n:ℝ)) :
    __PathDetour_hat n (j+1) x = (n:ℝ)*x - (j:ℝ) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have A : (j:ℝ) ≤ (n:ℝ)*x := by
    have aa := (div_le_iff₀ hn').1 hlo
    nlinarith
  have B' := (le_div_iff₀ hn').1 hhi
  have B : (n:ℝ)*x ≤ (j:ℝ)+1 := by
    push_cast at B'
    nlinarith
  have C : (n:ℝ)*x - (j+1:ℕ) ≤ 0 := by
    push_cast
    linarith
  have D : 0 ≤ (n:ℝ)*x - (j:ℝ) := sub_nonneg.mpr A
  have E : (n:ℝ)*x - (j:ℝ) ≤ 1 := by linarith
  unfold __PathDetour_hat
  rw [abs_of_nonpos C]
  have : 1 - -((n:ℝ)*x - (j+1:ℕ)) = (n:ℝ)*x - (j:ℝ) := by
    push_cast
    ring
  rw [this, max_eq_right D]

private lemma __PathDetour_hat_far {n j k : ℕ} (hn : 0 < n)
    {x : ℝ} (hlo : (j:ℝ)/(n:ℝ) ≤ x)
    (hhi : x ≤ (j+1:ℕ)/(n:ℝ))
    (hk : k ≠ j) (hk' : k ≠ j+1) : __PathDetour_hat n k x = 0 := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have A : (j:ℝ) ≤ (n:ℝ)*x := by
    have := (div_le_iff₀ hn').1 hlo
    nlinarith
  have B0 := (le_div_iff₀ hn').1 hhi
  have B : (n:ℝ)*x ≤ (j:ℝ)+1 := by
    push_cast at B0
    nlinarith
  have sides : k+1 ≤ j ∨ j+2 ≤ k := by omega
  unfold __PathDetour_hat
  apply max_eq_left
  rcases sides with left | right
  · have Lnat : (k:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast left
    have hxk : 0 ≤ (n:ℝ)*x - (k:ℝ) := by linarith
    rw [abs_of_nonneg hxk]
    linarith
  · have Lnat : (j:ℝ)+2 ≤ (k:ℝ) := by exact_mod_cast right
    have hxk : (n:ℝ)*x - (k:ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hxk]
    linarith

private lemma __PathDetour_poly_interval {n j : ℕ} (hn : 0 < n) (hj : j < n)
    (w : ℕ → ℂ) {x : ℝ} (hlo : (j:ℝ)/(n:ℝ) ≤ x)
    (hhi : x ≤ (j+1:ℕ)/(n:ℝ)) :
    __PathDetour_poly n w x = (((j+1:ℕ):ℝ) - (n:ℝ)*x) * w j +
                 (((n:ℝ)*x - (j:ℝ)) : ℝ) * w (j+1) := by
  classical
  let term : ℕ → ℂ := fun k => (__PathDetour_hat n k x : ℂ) * w k
  have hnmem : j ∈ Finset.range (n+1) := by simp; omega
  have hnmem' : j+1 ∈ Finset.range (n+1) := by simp; omega
  have hjne : j ≠ j+1 := by omega
  have hsub : ({j,j+1} : Finset ℕ) ⊆ Finset.range (n+1) := by
    intro k hk
    simp at hk ⊢
    omega
  have hz : ∀ k ∈ Finset.range (n+1), k ∉ ({j,j+1} : Finset ℕ) → term k = 0 := by
    intro k hk hnmem
    -- peel membership
    have h1 : k ≠ j := by
      intro h; subst k; exact hnmem (by simp)
    have h2 : k ≠ j+1 := by
      intro h; subst k; exact hnmem (by simp)
    have := __PathDetour_hat_far (n:=n) (j:=j) (k:=k) hn hlo hhi h1 h2
    dsimp [term]
    simp [this]
  have sums := Finset.sum_subset hsub hz
  change (∑ k ∈ Finset.range (n+1), term k) = _
  rw [← sums]
  simp [term, __PathDetour_hat_left hn hlo hhi, __PathDetour_hat_right hn hlo hhi, hjne]

lemma polygon_vertices (a : ℂ) (f : ℕ → ℂ) {e : ℝ} (he : 0 < e) (n : ℕ) (hn : 2 ≤ n) :
    ∃ w : ℕ → ℂ,
      w 0 = a ∧ w n = a ∧
      (∀ k, 0 < k → k < n → ‖w k - f k‖ < e) ∧
      (∀ k, 0 < k → k < n → w k ≠ a) ∧
      (∀ k, 0 < k → k+1 < n → cdet (w k-a) (w (k+1)-a) ≠ 0) := by
  classical
  choose b hbclose hbne using __PathDetour_firstVertex a (f 1) he
  let S := {z : ℂ // z ≠ a}
  let step : ℕ → S → S := fun k v =>
    ⟨Classical.choose (__PathDetour_nextVertex a (f (k+2)) v.1 v.2 he),
      (Classical.choose_spec (__PathDetour_nextVertex a (f (k+2)) v.1 v.2 he)).2.1⟩
  let u : ℕ → S := fun k => Nat.rec (motive:= fun _ => S) (⟨b,hbne⟩)
      (fun i last => step i last) k
  have u0 : (u 0 : ℂ) = b := rfl
  have usucc (k : ℕ) : u (k+1) = step k (u k) := by
    simp [u]
  have uspec (k : ℕ) : ‖(u (k+1) : ℂ) - f (k+2)‖ < e ∧
      cdet ((u k:ℂ)-a) ((u (k+1):ℂ)-a) ≠ 0 := by
    rw [usucc]
    exact ⟨(Classical.choose_spec (__PathDetour_nextVertex a (f (k+2)) (u k).1 (u k).2 he)).1,
           (Classical.choose_spec (__PathDetour_nextVertex a (f (k+2)) (u k).1 (u k).2 he)).2.2⟩
  let w : ℕ → ℂ := fun k => if h0 : k = 0 then a else if hk : k < n then (u (k-1) : ℂ) else a
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · simp [w]
  · have hn0 : ¬ n = 0 := by omega
    simp [w, hn0]
  · intro k hpos hlt
    have hk0 : k ≠ 0 := Nat.ne_of_gt hpos
    simp [w, hk0, hlt]
    rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨i, rfl⟩
    cases i with
    | zero => simpa [u0] using hbclose
    | succ i => simpa [Nat.add_assoc] using (uspec i).1
  · intro k hpos hlt
    have hk0 : k ≠ 0 := Nat.ne_of_gt hpos
    simp [w, hk0, hlt]
    exact (u (k-1)).2
  · intro k hpos hlt
    have hk0 : k ≠ 0 := Nat.ne_of_gt hpos
    have hkn : k < n := by omega
    have hk'0 : k+1 ≠ 0 := by omega
    simp [w, hk0, hkn, hk'0, hlt]
    rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨i, rfl⟩
    simpa [Nat.add_assoc] using (uspec i).2

private lemma __PathDetour_mesh_interval {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ j < n, (j:ℝ)/(n:ℝ) ≤ x ∧ x ≤ (j+1:ℕ)/(n:ℝ) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  by_cases hxn : x < 1
  · let j := ⌊(n:ℝ)*x⌋₊
    have hnon : 0 ≤ (n:ℝ)*x := mul_nonneg (le_of_lt hn') hx0
    have hjn : j < n := (Nat.floor_lt hnon).2 (by
      change (n:ℝ)*x < (n:ℝ)
      nlinarith)
    refine ⟨j, hjn, ?_, ?_⟩
    · apply (div_le_iff₀ hn').2
      have hle := Nat.floor_le hnon
      change (j:ℝ) ≤ (n:ℝ)*x at hle
      nlinarith
    · apply (le_div_iff₀ hn').2
      have hlt := Nat.lt_floor_add_one ((n:ℝ)*x)
      change (n:ℝ)*x < (j:ℝ) + 1 at hlt
      push_cast
      nlinarith
  · have hx : x = 1 := le_antisymm hx1 (le_of_not_gt hxn)
    subst x
    refine ⟨n-1, by omega, ?_, ?_⟩
    · apply (div_le_iff₀ hn').2
      have : (n-1:ℕ) ≤ n := by omega
      norm_cast
      nlinarith
    · have hne : n ≠ 0 := by omega
      have heq : n-1+1 = n := by omega
      simp [heq, hn.ne']


open scoped unitInterval
/-- Reduction from a small planar perturbation to the transverse square. No
compact-extension issue remains: straight homotopy is small enough. -/
theorem transverse_of_detour (r : Path cylBase cylBase)
    (g : C(I, ℂ))
    (g0 : g 0 = (zh:ℂ)) (g1 : g 1 = (zh:ℂ))
    (small0 : ∀ t : I,
       ‖g t - (punctZ (r t):ℂ)‖ < ‖(punctZ (r t):ℂ)‖)
    (smalle : ∀ t : I, cylHeight r t = 0 →
       ‖g t - (punctZ (r t):ℂ)‖ < ‖(punctZ (r t):ℂ) - (zh:ℂ)‖)
    (avoid : ∀ t : I, (0:ℝ) < t → (t:ℝ) < 1 → g t ≠ (zh:ℂ)) :
    ∃ Z : C(I × I, Zstar),
      (∀ t, Z (0,t) = punctZ (r t)) ∧
      (∀ s, Z (s,0) = zh) ∧
      (∀ s, Z (s,1) = zh) ∧
      (∀ s t, cylHeight r t = 0 → Z (s,t) ≠ zh) ∧
      (∀ t, cylHeight r t < 0 → Z (1,t) ≠ zh) := by
  let f : I → ℂ := fun t => (punctZ (r t):ℂ)
  have fc : Continuous f :=
    continuous_subtype_val.comp (punctZ.continuous.comp r.continuous)
  let G : I × I → ℂ := fun x => ((1-(x.1:ℝ):ℝ):ℂ) * f x.2 +
                                  ((x.1:ℝ):ℂ) * g x.2
  have Gsub (x : I × I) : G x - f x.2 = ((x.1:ℝ):ℂ) * (g x.2 - f x.2) := by
    dsimp [G]; push_cast; ring
  have Gsmall (x : I × I) : ‖G x - f x.2‖ < ‖f x.2‖ := by
    rw [Gsub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg x.1.property.1]
    have h := small0 x.2
    change ‖g x.2 - f x.2‖ < ‖f x.2‖ at h
    have hz : 0 < ‖f x.2‖ :=
      (norm_pos_iff.mpr (Subtype.property (punctZ (r x.2))))
    have xs := x.1.property.2
    nlinarith [norm_nonneg (g x.2 - f x.2)]
  have Gn (x : I × I) : G x ≠ 0 := by
    intro he
    have hs := Gsmall x
    rw [he, zero_sub, norm_neg] at hs
    exact (lt_irrefl _ hs)
  let Z : C(I × I, Zstar) :=
    ⟨fun x => ⟨G x, Gn x⟩,
      by
        apply Continuous.subtype_mk
        dsimp [G]
        have cs : Continuous (fun x : I × I => (x.1:ℝ)) :=
          continuous_subtype_val.comp continuous_fst
        exact (((Complex.continuous_ofReal.comp (continuous_const.sub cs)).mul
                 (fc.comp continuous_snd)).add
                 ((Complex.continuous_ofReal.comp cs).mul
                   (g.continuous.comp continuous_snd)))⟩
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    apply Subtype.ext
    simp [Z, G, f]
  · intro ss
    apply Subtype.ext
    change ((1-(ss:ℝ):ℝ):ℂ)*(punctZ (r (0:I)):ℂ) +
           ((ss:ℝ):ℂ)*g 0 = (zh:ℂ)
    rw [g0, r.source]
    change ((1-(ss:ℝ):ℝ):ℂ)*(zh:ℂ) + ((ss:ℝ):ℂ)*(zh:ℂ) = (zh:ℂ)
    push_cast; ring
  · intro ss
    apply Subtype.ext
    change ((1-(ss:ℝ):ℝ):ℂ)*(punctZ (r (1:I)):ℂ) +
           ((ss:ℝ):ℂ)*g 1 = (zh:ℂ)
    rw [g1, r.target]
    change ((1-(ss:ℝ):ℝ):ℂ)*(zh:ℂ) + ((ss:ℝ):ℂ)*(zh:ℂ) = (zh:ℂ)
    push_cast; ring
  · intro ss t ht bad
    have be : G (ss,t) = (zh:ℂ) := congrArg Subtype.val bad
    have hs := smalle t ht
    change ‖g t - f t‖ < ‖f t - (zh:ℂ)‖ at hs
    have eq : G (ss,t) - f t = ((ss:ℝ):ℂ)*(g t - f t) := Gsub (ss,t)
    have less : ‖G (ss,t) - f t‖ < ‖f t - (zh:ℂ)‖ := by
      rw [eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
           abs_of_nonneg ss.property.1]
      have ss1 := ss.property.2
      have non := norm_nonneg (g t - f t)
      have targ := norm_nonneg (f t - (zh:ℂ))
      nlinarith
    rw [be] at less
    rw [norm_sub_rev] at less
    exact (lt_irrefl _ less)
  · intro t hn bad
    have be : g t = (zh:ℂ) := by
      have := congrArg Subtype.val bad
      simpa [Z, G] using this
    apply (avoid t) _ _ be
    · by_contra h0
      have tz : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt h0) t.property.1)
      subst t
      have hh : cylHeight r 0 = 1 := by unfold cylHeight; rw [r.source]; rfl
      linarith
    · by_contra h1'
      have tz : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt h1'))
      subst t
      have hh : cylHeight r 1 = 1 := by unfold cylHeight; rw [r.target]; rfl
      linarith



private def __PathDetour_meshPt (n : ℕ) (hn : 0 < n) (k : ℕ) : I :=
  ⟨((min k n : ℕ) : ℝ) / (n : ℝ), by
    have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    constructor
    · positivity
    · apply (div_le_iff₀ hn').2
      have hle : min k n ≤ n := Nat.min_le_right _ _
      have hh : ((min k n : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hle
      simpa using hh⟩

private lemma __PathDetour_meshPt_val_of_le {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k ≤ n) :
    ((__PathDetour_meshPt n hn k : I) : ℝ) = (k:ℝ)/(n:ℝ) := by
  simp [__PathDetour_meshPt, min_eq_left hk]

private lemma __PathDetour_meshPt_zero {n : ℕ} (hn : 0 < n) : __PathDetour_meshPt n hn 0 = (0:I) := by
  apply Subtype.ext
  simp [__PathDetour_meshPt]

private lemma __PathDetour_meshPt_last {n : ℕ} (hn : 0 < n) : __PathDetour_meshPt n hn n = (1:I) := by
  apply Subtype.ext
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [__PathDetour_meshPt, hn']

private lemma __PathDetour_mesh_distance_left {n j : ℕ} (hn : 0 < n) (hj : j < n)
    {x : I} (hlo : (j:ℝ)/(n:ℝ) ≤ (x:ℝ))
    (hhi : (x:ℝ) ≤ (j+1:ℕ)/(n:ℝ)) :
    dist (__PathDetour_meshPt n hn j) x ≤ 1/(n:ℝ) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  change |(((__PathDetour_meshPt n hn j : I):ℝ) - (x:ℝ))| ≤ _
  rw [__PathDetour_meshPt_val_of_le hn (Nat.le_of_lt hj)]
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  have hcast : (((j+1:ℕ):ℝ)/(n:ℝ)) = (j:ℝ)/(n:ℝ) + 1/(n:ℝ) := by
    push_cast; ring
  rw [hcast] at hhi
  linarith

private lemma __PathDetour_mesh_distance_right {n j : ℕ} (hn : 0 < n) (hj : j < n)
    {x : I} (hlo : (j:ℝ)/(n:ℝ) ≤ (x:ℝ))
    (hhi : (x:ℝ) ≤ (j+1:ℕ)/(n:ℝ)) :
    dist (__PathDetour_meshPt n hn (j+1)) x ≤ 1/(n:ℝ) := by
  have hj1 : j+1 ≤ n := by omega
  change |(((__PathDetour_meshPt n hn (j+1) : I):ℝ) - (x:ℝ))| ≤ _
  rw [__PathDetour_meshPt_val_of_le hn hj1]
  rw [abs_of_nonneg (sub_nonneg.mpr hhi)]
  have hcast : (((j+1:ℕ):ℝ)/(n:ℝ)) = (j:ℝ)/(n:ℝ) + 1/(n:ℝ) := by
    push_cast; ring
  rw [hcast]
  linarith

/-- A path in the plane can be moved an arbitrarily small amount, fixing its
endpoints, so that that marked value is assumed only at the endpoints.  The
quantitative form is useful here because the straight homotopy then misses
both remaining forbidden values. -/
theorem planar_detour
    (f : C(I, ℂ)) (a : ℂ) (f0 : f 0 = a) (f1 : f 1 = a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(I,ℂ), g 0 = a ∧ g 1 = a ∧
      (∀ t : I, ‖g t - f t‖ < ε) ∧
      (∀ t : I, (0:ℝ) < t → (t:ℝ) < 1 → g t ≠ a) := by
  classical
  have uf : UniformContinuous f :=
    CompactSpace.uniformContinuous_of_continuous f.continuous
  have e4 : 0 < ε/4 := by linarith
  obtain ⟨δ, hδ, hcontrol⟩ :=
    (Metric.uniformContinuous_iff.mp uf) (ε/4) e4
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  let n : ℕ := m + 2
  have hn : 0 < n := by dsimp [n]; omega
  have hn2 : 2 ≤ n := by dsimp [n]; omega
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have one_small : (1:ℝ)/(n:ℝ) < δ := by
    have ha : (0:ℝ) < (m:ℝ)+1 := by positivity
    have hb : (m:ℝ)+1 ≤ (n:ℝ) := by
      dsimp [n]
      push_cast
      linarith
    have le := one_div_le_one_div_of_le ha hb
    have castm : (m:ℝ) + 1 = ((m+1:ℕ):ℝ) := by simp
    have hh : (1:ℝ) / ((m:ℝ)+1) < δ := by
      simpa using hm
    exact lt_of_le_of_lt le hh
  let targets : ℕ → ℂ := fun k => f (__PathDetour_meshPt n hn k)
  obtain ⟨w, w0, wn, wclose, wne, wed⟩ :=
    polygon_vertices a targets e4 n hn2
  have wbound : ∀ k : ℕ, k ≤ n → ‖w k - f (__PathDetour_meshPt n hn k)‖ < ε/4 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with kz | kp
    · subst k
      rw [w0, __PathDetour_meshPt_zero hn, f0]
      simpa using e4
    · by_cases kn : k = n
      · subst k
        rw [wn, __PathDetour_meshPt_last hn, f1]
        simpa using e4
      · have kl : k < n := lt_of_le_of_ne hk kn
        simpa [targets] using wclose k kp kl
  let g : C(I,ℂ) :=
    ⟨fun t => __PathDetour_poly n w (t:ℝ), (__PathDetour_poly_cont n w).comp continuous_subtype_val⟩
  have ginterval {x : I} {j : ℕ} (hj : j < n)
      (hlo : (j:ℝ)/(n:ℝ) ≤ (x:ℝ))
      (hhi : (x:ℝ) ≤ (j+1:ℕ)/(n:ℝ)) :
      g x = (((1 - ((n:ℝ)*(x:ℝ) - (j:ℝ)) : ℝ):ℂ)) * w j +
            (((((n:ℝ)*(x:ℝ) - (j:ℝ)) : ℝ):ℂ)) * w (j+1) := by
    change __PathDetour_poly n w (x:ℝ) = _
    rw [__PathDetour_poly_interval hn hj w hlo hhi]
    push_cast
    ring
  have close (x : I) : ‖g x - f x‖ < ε := by
    obtain ⟨j, hj, hlo, hhi⟩ := __PathDetour_mesh_interval hn x.property.1 x.property.2
    let τ : ℝ := (n:ℝ)*(x:ℝ) - (j:ℝ)
    have A : 0 ≤ τ := by
      have := (div_le_iff₀ hn').1 hlo
      dsimp [τ]
      linarith
    have B : τ ≤ 1 := by
      have gg := (le_div_iff₀ hn').1 hhi
      push_cast at gg
      dsimp [τ]
      linarith
    have dj : dist (__PathDetour_meshPt n hn j) x < δ :=
      lt_of_le_of_lt (__PathDetour_mesh_distance_left hn hj hlo hhi) one_small
    have dj1 : dist (__PathDetour_meshPt n hn (j+1)) x < δ :=
      lt_of_le_of_lt (__PathDetour_mesh_distance_right hn hj hlo hhi) one_small
    have fj := hcontrol dj
    have fk := hcontrol dj1
    have Fj : ‖f (__PathDetour_meshPt n hn j) - f x‖ < ε/4 := by simpa [dist_eq_norm] using fj
    have Fk : ‖f (__PathDetour_meshPt n hn (j+1)) - f x‖ < ε/4 := by simpa [dist_eq_norm] using fk
    have Wj := wbound j (Nat.le_of_lt hj)
    have Wk := wbound (j+1) (by omega)
    have Tj : ‖w j - f x‖ < ε/2 := by
      calc
        ‖w j - f x‖ = ‖(w j - f (__PathDetour_meshPt n hn j)) +
                            (f (__PathDetour_meshPt n hn j) - f x)‖ := by ring_nf
        _ ≤ ‖w j - f (__PathDetour_meshPt n hn j)‖ +
                            ‖f (__PathDetour_meshPt n hn j) - f x‖ := norm_add_le _ _
        _ < ε/2 := by linarith
    have Tk : ‖w (j+1) - f x‖ < ε/2 := by
      calc
        ‖w (j+1) - f x‖ = ‖(w (j+1) - f (__PathDetour_meshPt n hn (j+1))) +
                            (f (__PathDetour_meshPt n hn (j+1)) - f x)‖ := by ring_nf
        _ ≤ ‖w (j+1) - f (__PathDetour_meshPt n hn (j+1))‖ +
                            ‖f (__PathDetour_meshPt n hn (j+1)) - f x‖ := norm_add_le _ _
        _ < ε/2 := by linarith
    have ge := ginterval hj hlo hhi
    change __PathDetour_poly n w (x:ℝ) = _ at ge
    change ‖__PathDetour_poly n w (x:ℝ) - f x‖ < ε
    calc
      ‖__PathDetour_poly n w (x:ℝ) - f x‖ =
          ‖((1-τ : ℝ):ℂ)*(w j - f x) +
             ((τ : ℝ):ℂ)*(w (j+1) - f x)‖ := by
                rw [ge]
                dsimp [τ]
                push_cast
                ring
      _ ≤ ‖((1-τ : ℝ):ℂ)*(w j - f x)‖ +
             ‖((τ : ℝ):ℂ)*(w (j+1) - f x)‖ := norm_add_le _ _
      _ = (1-τ)*‖w j - f x‖ + τ*‖w (j+1) - f x‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
                Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (sub_nonneg.mpr B), abs_of_nonneg A]
      _ < ε := by
            have aux : (1-τ)*‖w j - f x‖ + τ*‖w (j+1) - f x‖ < ε/2 := by
              by_cases tlast : τ = 1
              · rw [tlast]
                norm_num
                exact Tk
              · have lt1 : τ < 1 := lt_of_le_of_ne B tlast
                have aa := mul_lt_mul_of_pos_left Tj (sub_pos.mpr lt1)
                have bb := mul_le_mul_of_nonneg_left (le_of_lt Tk) A
                nlinarith
            linarith
  refine ⟨g, ?_, ?_, close, ?_⟩
  · change __PathDetour_poly n w (0:ℝ) = a
    have hi := __PathDetour_poly_interval hn (show 0 < n from hn) w
        (show ((0:ℕ):ℝ)/(n:ℝ) ≤ (0:ℝ) by simp)
        (show (0:ℝ) ≤ (0+1:ℕ)/(n:ℝ) by positivity)
    simpa [w0] using hi
  · have jlast : n-1 < n := by omega
    have heq : n-1+1 = n := by omega
    have lo : ((n-1:ℕ):ℝ)/(n:ℝ) ≤ (1:ℝ) := by
      apply (div_le_iff₀ hn').2
      have hh : (((n-1:ℕ):ℝ)) ≤ (n:ℝ) := by
        exact_mod_cast (show n-1 ≤ n by omega)
      simpa using hh
    have hi' : (1:ℝ) ≤ (((n-1+1:ℕ):ℝ)/(n:ℝ)) := by
      simp [heq, ne_of_gt hn']
    change __PathDetour_poly n w (1:ℝ) = a
    have hpoly := __PathDetour_poly_interval hn jlast w lo hi'
    rw [heq] at hpoly
    have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hn'
    rw [hpoly]
    push_cast
    simp [wn, Nat.cast_sub (by omega : 1 ≤ n)]
  · intro x xpos xone bad
    obtain ⟨j, hj, hlo, hhi⟩ := __PathDetour_mesh_interval hn x.property.1 x.property.2
    let τ : ℝ := (n:ℝ)*(x:ℝ) - (j:ℝ)
    have A : 0 ≤ τ := by
      have := (div_le_iff₀ hn').1 hlo
      dsimp [τ]
      linarith
    have B : τ ≤ 1 := by
      have gg := (le_div_iff₀ hn').1 hhi
      push_cast at gg
      dsimp [τ]
      linarith
    have ge := ginterval hj hlo hhi
    change __PathDetour_poly n w (x:ℝ) = _ at ge
    have eqbad : (( (1-τ : ℝ):ℂ)) * w j + ((τ:ℝ):ℂ)*w (j+1) = a := by
      dsimp [g] at bad
      rw [ge] at bad
      exact bad
    by_cases jzero : j = 0
    · subst j
      have Tp : 0 < τ := by
        dsimp [τ]
        have : 0 < (x:ℝ) := xpos
        change 0 < (n:ℝ)*(x:ℝ) - (↑(0:ℕ):ℝ)
        norm_num
        positivity
      have w1 : w 1 ≠ a := wne 1 (by omega) (by omega)
      have ev := congrArg (fun z : ℂ => z - a) eqbad
      push_cast at ev
      rw [w0] at ev
      have tz : ((τ:ℝ):ℂ) * (w 1 - a) = 0 := by
        push_cast at ev ⊢
        calc
          (τ:ℂ) * (w 1 - a) = (1-(τ:ℂ))*a + (τ:ℂ)*w 1 - a := by ring
          _ = 0 := ev.trans (sub_self a)
      exact w1 (by
        have : (τ:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt Tp)
        exact sub_eq_zero.mp ((mul_eq_zero.mp tz).resolve_left this))
    · by_cases jlast : j+1 = n
      · have Tm : τ < 1 := by
          dsimp [τ]
          have hh : (x:ℝ) < 1 := xone
          have jeq : ((j:ℝ)+1) = (n:ℝ) := by exact_mod_cast jlast
          nlinarith
        have jp : 0 < j := Nat.pos_of_ne_zero jzero
        have wj : w j ≠ a := wne j jp hj
        have ev := congrArg (fun z : ℂ => z - a) eqbad
        have wn' : w (j+1) = a := by simpa [jlast] using wn
        rw [wn'] at ev
        have tz : (((1-τ:ℝ):ℂ)) * (w j-a) = 0 := by
          push_cast at ev ⊢
          calc
            (1-(τ:ℂ))*(w j-a) = (1-(τ:ℂ))*w j + (τ:ℂ)*a - a := by ring
            _ = 0 := ev.trans (sub_self a)
        exact wj (by
          have : (((1-τ:ℝ):ℂ)) ≠ 0 := by
            exact_mod_cast (ne_of_gt (sub_pos.mpr Tm))
          exact sub_eq_zero.mp ((mul_eq_zero.mp tz).resolve_left this))
      · have jp : 0 < j := Nat.pos_of_ne_zero jzero
        have jinside : j+1 < n := lt_of_le_of_ne (by omega : j+1 ≤ n) jlast
        have det := wed j jp jinside
        have seg := __PathDetour_segment_ne det A B
        apply seg
        have ev := congrArg (fun z : ℂ => z-a) eqbad
        push_cast at ev
        -- turn the affine combination into the expression of `__PathDetour_segment_ne`
        have last : (((1-τ:ℝ):ℂ))*(w j-a) + ((τ:ℝ):ℂ)*(w (j+1)-a) = 0 := by
          push_cast at ev ⊢
          calc
            (1-(τ:ℂ))*(w j-a) + (τ:ℂ)*(w (j+1)-a) =
                (1-(τ:ℂ))*w j + (τ:ℂ)*w (j+1) - a := by ring
            _ = 0 := by simpa using ev
        exact last


/-- Completion of the relative puncture step.  Only the one dimensional
boundary of the square is ever changed.  Compactness supplies room around
zero and, on the zero height slice, around the second marked value; the
small planar polygon misses that value at all other parameters. -/
theorem detour_transverse (r : Path cylBase cylBase) :
    ∃ Z : C(I × I, Zstar),
      (∀ t, Z (0,t) = punctZ (r t)) ∧
      (∀ s, Z (s,0) = zh) ∧
      (∀ s, Z (s,1) = zh) ∧
      (∀ s t, cylHeight r t = 0 → Z (s,t) ≠ zh) ∧
      (∀ t, cylHeight r t < 0 → Z (1,t) ≠ zh) := by
  classical
  let f : C(I,ℂ) :=
    ⟨fun t => (punctZ (r t) : ℂ),
      continuous_subtype_val.comp (continuous_punctZ_path r)⟩
  have f0 : f 0 = (zh:ℂ) := by
    change (punctZ (r (0:I)):ℂ) = (zh:ℂ)
    rw [r.source]
    rfl
  have f1 : f 1 = (zh:ℂ) := by
    change (punctZ (r (1:I)):ℂ) = (zh:ℂ)
    rw [r.target]
    rfl
  -- positive distance from the origin, on the whole parameter interval
  have min0 : ∃ c : ℝ, 0 < c ∧ ∀ t : I, c ≤ ‖f t‖ := by
    have K : IsCompact (Set.univ : Set I) := isCompact_univ
    obtain ⟨x, hx, hmin⟩ :=
      K.exists_isMinOn (by exact ⟨(0:I), Set.mem_univ _⟩)
        (show ContinuousOn (fun t : I => ‖f t‖) Set.univ from
          (f.continuous.norm).continuousOn)
    refine ⟨‖f x‖, ?_, ?_⟩
    · apply norm_pos_iff.mpr
      exact Subtype.property (punctZ (r x))
    · intro t
      exact hmin (Set.mem_univ _)
  obtain ⟨c, hc, hc_all⟩ := min0
  let S : Set I := {t | cylHeight r t = 0}
  have Sclosed : IsClosed S := by
    dsimp [S]
    exact isClosed_eq (continuous_cylHeight r) continuous_const
  -- the zero-height slice, if present, is compact as well and cannot have
  -- the coordinate `zh` (that was the removed point itself).
  have room : ∃ e : ℝ, 0 < e ∧
        e < c ∧
        ∀ t : I, cylHeight r t = 0 → e < ‖f t - (zh:ℂ)‖ := by
    by_cases hs : S.Nonempty
    · have comp : IsCompact S := Sclosed.isCompact
      obtain ⟨x, hx, hmin⟩ := comp.exists_isMinOn hs
          (show ContinuousOn (fun t : I => ‖f t - (zh:ℂ)‖) S from
            (f.continuous.sub continuous_const).norm.continuousOn)
      have xp : 0 < ‖f x - (zh:ℂ)‖ := by
        apply norm_pos_iff.mpr
        intro zz
        have zz' : punctZ (r x) = zh := by
          apply Subtype.ext
          exact sub_eq_zero.mp zz
        exact (height_ne_zero_of_exceptional r x zz') hx
      refine ⟨(min c ‖f x - (zh:ℂ)‖)/2, ?_, ?_, ?_⟩
      · have : 0 < min c ‖f x - (zh:ℂ)‖ := lt_min hc xp
        linarith
      · have le := min_le_left c ‖f x - (zh:ℂ)‖
        nlinarith
      · intro t ht
        have tin : t ∈ S := ht
        have bound : ‖f x - (zh:ℂ)‖ ≤ ‖f t - (zh:ℂ)‖ := hmin tin
        have le := min_le_right c ‖f x - (zh:ℂ)‖
        have posit : 0 < ‖f t - (zh:ℂ)‖ := lt_of_lt_of_le xp bound
        nlinarith
    · refine ⟨c/2, by linarith, by linarith, ?_⟩
      intro t ht
      exfalso
      apply hs
      exact ⟨t, ht⟩
  obtain ⟨e, he, hec, heS⟩ := room
  obtain ⟨g, g0, g1, small, avoid⟩ := planar_detour f (zh:ℂ) f0 f1 he
  apply transverse_of_detour r g g0 g1
  · intro t
    have sm := small t
    have low := hc_all t
    change ‖g t - (punctZ (r t):ℂ)‖ <
      ‖(punctZ (r t):ℂ)‖
    change ‖g t - f t‖ < ‖f t‖ at *
    exact lt_of_lt_of_le sm (le_trans (le_of_lt hec) low)
  · intro t ht
    have sm := small t
    have spec := heS t ht
    change ‖g t - (punctZ (r t):ℂ)‖ <
      ‖(punctZ (r t):ℂ) - (zh:ℂ)‖
    change ‖g t - f t‖ < ‖f t - (zh:ℂ)‖ at *
    exact lt_trans sm spec
  · exact avoid

end KnotSupport

end

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/PathDetour.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/CubicBraid.lean
section

open Set Function Filter Topology
noncomputable section
namespace KnotSupport

abbrev CubicSource := {x : ℂ × ℂ // cubicMap x ∈ cubicGoodSet}

/-- Incidence roots are the graph of the triangular polynomial over the good set. -/
def rootChart : CubicRoot ≃ₜ CubicSource := by
  let f : CubicRoot → CubicSource := fun e =>
    ⟨(e.1.1.1.1, e.1.2), by
      -- root equation solves for the second coefficient
      have hz := e.2
      change ( _ ^ (3:ℕ) ≠ _ ^ (2:ℕ))
      -- value of the map equals original good pair
      have eqv : cubicMap (e.1.1.1.1, e.1.2) = e.1.1.1 := by
        apply Prod.ext
        · rfl
        · change ((3:ℂ)*e.1.1.1.1*e.1.2 - e.1.2^3)/2 = e.1.1.1.2
          change e.1.2^3 - 3*e.1.1.1.1*e.1.2 + 2*e.1.1.1.2 = 0 at hz
          linear_combination -(hz)/2
      simpa [eqv] using e.1.1.property⟩
  let g : CubicSource → CubicRoot := fun x =>
    ⟨(⟨cubicMap x.1, x.2⟩, x.1.2), by
      dsimp [cubicMap]
      ring⟩
  have fg : Function.LeftInverse g f := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · have hz := e.2
        change ((3:ℂ)*e.1.1.1.1*e.1.2 - e.1.2^3)/2 = e.1.1.1.2
        change e.1.2^3 - 3*e.1.1.1.1*e.1.2 + 2*e.1.1.1.2 = 0 at hz
        linear_combination -(hz)/2
    · rfl
  have gf : Function.RightInverse g f := by
    intro x
    apply Subtype.ext
    rfl
  exact
    { toFun := f, invFun := g, left_inv := fg, right_inv := gf
      continuous_toFun := by
        -- the coordinates are projections
        unfold f
        fun_prop
      continuous_invFun := by
        unfold g cubicMap
        fun_prop }

lemma rootChart_pr (e : CubicRoot) :
    (cubicGoodSet.restrictPreimage cubicMap) (rootChart e) = rootPr e := by
  -- the equation of a root
  apply Subtype.ext
  rcases e with ⟨⟨w,z⟩, hz⟩
  change cubicMap (w.1.1, z) = w.1
  apply Prod.ext
  · rfl
  · change ((3:ℂ)*w.1.1*z - z^3)/2 = w.1.2
    change z^3 - 3*w.1.1*z + 2*w.1.2 = 0 at hz
    linear_combination -(hz)/2

lemma root_cover : IsCoveringMap rootPr := by
  have h0 : IsCoveringMap (cubicGoodSet.restrictPreimage cubicMap) :=
    cubicMap_cover_on.isCoveringMap_restrictPreimage
  have h := h0.comp_homeomorph rootChart
  have funextp : (cubicGoodSet.restrictPreimage cubicMap) ∘ rootChart = rootPr :=
    funext rootChart_pr
  --
  exact funextp ▸ h

end KnotSupport


namespace KnotSupport
noncomputable section

/-- A rational regular value in the slice, with a displayed sheet.  The cubic
`z^3-5z+2` has the root `2`; using this value makes the eventual drawing of
both meridians unambiguous. -/
def braidBase : CubicSliceDomain :=
  ⟨( (5:ℂ)/3), by
    constructor
    · norm_num
    · norm_num⟩

@[simp] lemma braidBase_val : (braidBase : ℂ) = (5:ℂ)/3 := rfl

def rootTwo : CubicRoot :=
  ⟨(⟨(( (5:ℂ)/3), (1:ℂ)), by norm_num⟩, (2:ℂ)), by norm_num⟩

lemma rootTwo_over : rootPr rootTwo =
    trefoilCoeffs (sliceExterior braidBase) := by
  apply Subtype.ext
  change ((( (5:ℂ)/3), (1:ℂ))) = (trefoilCoeffs (sliceExterior braidBase)).1
  simpa using (coeff_slice braidBase).symm

end
end KnotSupport

namespace KnotSupport
noncomputable section
private lemma __CubicBraid_sqrt2sq : (Real.sqrt 2)^2 = (2:ℝ) := by norm_num
/-- The other two displayed sheets above `braidBase`. Naming them avoids any
choice of polynomial roots in a path-lifting computation. -/
def rootNear : CubicRoot := by
  let x : ℝ := -1 + Real.sqrt 2
  have hx : x^3 - 5*x + 2 = 0 := by
    have h := __CubicBraid_sqrt2sq
    have h3 := congrArg (fun y : ℝ => y * Real.sqrt 2) h
    dsimp [x]
    ring_nf
    nlinarith
  refine ⟨(⟨(( (5:ℂ)/3), (1:ℂ)), by norm_num⟩, (x:ℂ)), ?_⟩
  -- the depressed cubic is `z^3-5z+2`
  norm_num
  exact_mod_cast hx

def rootFar : CubicRoot := by
  let x : ℝ := -1 - Real.sqrt 2
  have hx : x^3 - 5*x + 2 = 0 := by
    have h := __CubicBraid_sqrt2sq
    have h3 := congrArg (fun y : ℝ => y * Real.sqrt 2) h
    dsimp [x]
    ring_nf
    nlinarith
  refine ⟨(⟨(( (5:ℂ)/3), (1:ℂ)), by norm_num⟩, (x:ℂ)), ?_⟩
  norm_num
  exact_mod_cast hx
lemma rootNear_over : rootPr rootNear =
    trefoilCoeffs (sliceExterior braidBase) := by
  apply Subtype.ext
  change ((( (5:ℂ)/3), (1:ℂ))) = (trefoilCoeffs (sliceExterior braidBase)).1
  simpa using (coeff_slice braidBase).symm
lemma rootFar_over : rootPr rootFar =
    trefoilCoeffs (sliceExterior braidBase) := by
  apply Subtype.ext
  change ((( (5:ℂ)/3), (1:ℂ))) = (trefoilCoeffs (sliceExterior braidBase)).1
  simpa using (coeff_slice braidBase).symm
lemma rootNear_ne_rootFar : rootNear ≠ rootFar := by
  intro h
  have h' := congrArg (fun e : CubicRoot => (e.1.2).re) h
  change -1 + Real.sqrt 2 = -1 - Real.sqrt 2 at h'
  have pos : 0 < Real.sqrt 2 := by positivity
  linarith
lemma rootTwo_ne_rootNear : rootTwo ≠ rootNear := by
  intro h
  have h' := congrArg (fun e : CubicRoot => (e.1.2).re) h
  change (2:ℝ) = -1 + Real.sqrt 2 at h'
  have hsq := __CubicBraid_sqrt2sq
  nlinarith
lemma rootTwo_ne_rootFar : rootTwo ≠ rootFar := by
  intro h
  have h' := congrArg (fun e : CubicRoot => (e.1.2).re) h
  change (2:ℝ) = -1 - Real.sqrt 2 at h'
  have hp : 0 ≤ Real.sqrt 2 := by positivity
  linarith
end
end KnotSupport

end

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/CubicBraid.lean

-- BEGIN INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/BraidMonodromy.lean
section
open Set Function Filter Topology
open scoped unitInterval
noncomputable section
namespace KnotSupport

private lemma __BraidMonodromy_sqrt2sq' : (Real.sqrt 2)^2 = (2:ℝ) := by norm_num
private lemma __BraidMonodromy_sqrt2_gt : (1:ℝ) < Real.sqrt 2 := by nlinarith [__BraidMonodromy_sqrt2sq', Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)]

-- rational projection of the triangular cubic on v=1
def braidU (z : ℂ) : ℂ := (z^3 + 2) / (3*z)

lemma braidU_re (a b : ℝ) (hn : (a:ℂ) + b*Complex.I ≠ 0) :
    (braidU ((a:ℂ) + (b:ℂ)*Complex.I)).re =
      (a^2 - b^2 + 2*a/(a^2+b^2))/3 := by
  -- rewrite as z^2/3 + 2/(3z)
  have hz : (braidU ((a:ℂ) + (b:ℂ)*Complex.I)) =
      (((a:ℂ) + b*Complex.I)^2 + 2/((a:ℂ)+b*Complex.I))/3 := by
    unfold braidU
    field_simp
  rw [hz]
  simp [Complex.div_re, Complex.normSq, Complex.mul_re,
    Complex.add_re, Complex.add_im, pow_two]


lemma braidU_good {z : ℂ} (hz : z ≠ 0)
    (h1 : z^3 ≠ (1:ℂ)) (h8 : z^3 ≠ (-8:ℂ)) :
    (braidU z)^3 ≠ (1:ℂ) := by
  intro h
  have H : (z^3-1)^2 * (z^3+8) = (0:ℂ) := by
    unfold braidU at h
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.mp H with h' | h'
  · apply h1
    have h0 := (sq_eq_zero_iff).mp h'
    linear_combination h0
  · apply h8
    linear_combination h'

end KnotSupport

namespace KnotSupport
open scoped ComplexConjugate
private def __BraidMonodromy_nR : ℝ := -1 + Real.sqrt 2
private def __BraidMonodromy_fR : ℝ := -1 - Real.sqrt 2
private lemma __BraidMonodromy_npos : 0 < __BraidMonodromy_nR := by dsimp [__BraidMonodromy_nR]; linarith [__BraidMonodromy_sqrt2_gt]
private lemma __BraidMonodromy_nlt : __BraidMonodromy_nR < 1/2 := by dsimp [__BraidMonodromy_nR]; nlinarith [__BraidMonodromy_sqrt2sq']
private lemma __BraidMonodromy_flt : __BraidMonodromy_fR < -2 := by dsimp [__BraidMonodromy_fR]; linarith [__BraidMonodromy_sqrt2_gt]
private lemma __BraidMonodromy_freal_ne : (__BraidMonodromy_fR)^3 ≠ (-8:ℝ) := by
  dsimp [__BraidMonodromy_fR]
  have h:= __BraidMonodromy_sqrt2sq'
  have hp := __BraidMonodromy_sqrt2_gt
  nlinarith
private lemma __BraidMonodromy_nreal_ne1 : (__BraidMonodromy_nR)^3 ≠ (1:ℝ) := by
 dsimp [__BraidMonodromy_nR]; have h:=__BraidMonodromy_sqrt2sq'; have hp:=__BraidMonodromy_sqrt2_gt; nlinarith
private lemma __BraidMonodromy_nreal_ne8 : (__BraidMonodromy_nR)^3 ≠ (-8:ℝ) := by
 dsimp [__BraidMonodromy_nR]; have h:=__BraidMonodromy_sqrt2sq'; have hp:=__BraidMonodromy_sqrt2_gt; nlinarith
private lemma __BraidMonodromy_freal_ne1 : (__BraidMonodromy_fR)^3 ≠ (1:ℝ) := by
 dsimp [__BraidMonodromy_fR]; have h:=__BraidMonodromy_sqrt2sq'; have hp:=__BraidMonodromy_sqrt2_gt; nlinarith


private def __BraidMonodromy_zA : Path (2:ℂ) (__BraidMonodromy_nR:ℂ) :=
  (Path.segment (2:ℂ) ((2:ℂ) + (1/2:ℝ)*Complex.I)).trans
   ((Path.segment ((2:ℂ) + (1/2:ℝ)*Complex.I)
      ((__BraidMonodromy_nR:ℂ)+(1/2:ℝ)*Complex.I)).trans
    (Path.segment ((__BraidMonodromy_nR:ℂ)+(1/2:ℝ)*Complex.I) (__BraidMonodromy_nR:ℂ)))
private def __BraidMonodromy_zB : Path (2:ℂ) (__BraidMonodromy_fR:ℂ) :=
  (Path.segment (2:ℂ) ((2:ℂ) + (1:ℝ)*Complex.I)).trans
   ((Path.segment ((2:ℂ)+(1:ℝ)*Complex.I) ((__BraidMonodromy_fR:ℂ)+(1:ℝ)*Complex.I)).trans
    (Path.segment ((__BraidMonodromy_fR:ℂ)+(1:ℝ)*Complex.I) (__BraidMonodromy_fR:ℂ)))

private lemma __BraidMonodromy_zA_cases (t : I) :
 ∃ a b : ℝ, __BraidMonodromy_zA t = (a:ℂ)+(b:ℂ)*Complex.I ∧
  ((a=2 ∧ 0 ≤ b ∧ b ≤ 1/2) ∨
   (__BraidMonodromy_nR ≤ a ∧ a ≤ 2 ∧ b=1/2) ∨
   (a=__BraidMonodromy_nR ∧ 0 ≤ b ∧ b ≤ 1/2)) := by
  have ht : __BraidMonodromy_zA t ∈ Set.range (Path.segment (2:ℂ) ((2:ℂ)+(1/2:ℝ)*Complex.I)) ∪
       (Set.range (Path.segment ((2:ℂ)+(1/2:ℝ)*Complex.I) ((__BraidMonodromy_nR:ℂ)+(1/2:ℝ)*Complex.I)) ∪
        Set.range (Path.segment ((__BraidMonodromy_nR:ℂ)+(1/2:ℝ)*Complex.I) (__BraidMonodromy_nR:ℂ))) := by
    simpa [__BraidMonodromy_zA, Path.trans_range] using (show __BraidMonodromy_zA t ∈ Set.range __BraidMonodromy_zA from ⟨t,rfl⟩)
  rcases ht with ht|ht|ht
  · rcases ht with ⟨s,hs⟩
    refine ⟨2, (s:ℝ)/2, ?_, Or.inl ⟨rfl, ?_, ?_⟩⟩
    · rw [← hs, Path.segment_apply, AffineMap.lineMap_apply_module]
      simp [Complex.real_smul]; push_cast; ring
    · exact div_nonneg s.2.1 (by norm_num)
    · linarith [s.2.2]
  · rcases ht with ⟨s,hs⟩
    refine ⟨(1-(s:ℝ))*2 + (s:ℝ)*__BraidMonodromy_nR, 1/2, ?_, Or.inr (Or.inl ⟨?_, ?_, rfl⟩)⟩
    · rw [← hs, Path.segment_apply, AffineMap.lineMap_apply_module]
      simp [Complex.real_smul]; push_cast; ring
    · have := __BraidMonodromy_npos
      have sn0 := s.2.1; have sn1 := s.2.2
      nlinarith [__BraidMonodromy_nlt]
    · have sn0 := s.2.1; have sn1 := s.2.2
      nlinarith [__BraidMonodromy_nlt]
  · rcases ht with ⟨s,hs⟩
    refine ⟨__BraidMonodromy_nR, (1-(s:ℝ))/2, ?_, Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)⟩
    · rw [← hs, Path.segment_apply, AffineMap.lineMap_apply_module]
      simp [Complex.real_smul]; push_cast; ring
    · linarith [s.2.2]
    · linarith [s.2.1]

private lemma __BraidMonodromy_zB_cases (t : I) :
 ∃ a b : ℝ, __BraidMonodromy_zB t = (a:ℂ)+(b:ℂ)*Complex.I ∧
  ((a=2 ∧ 0 ≤ b ∧ b ≤ 1) ∨
   (b=1) ∨
   (a=__BraidMonodromy_fR ∧ 0 ≤ b ∧ b ≤ 1)) := by
  have ht : __BraidMonodromy_zB t ∈ Set.range (Path.segment (2:ℂ) ((2:ℂ)+(1:ℝ)*Complex.I)) ∪
       (Set.range (Path.segment ((2:ℂ)+(1:ℝ)*Complex.I) ((__BraidMonodromy_fR:ℂ)+(1:ℝ)*Complex.I)) ∪
        Set.range (Path.segment ((__BraidMonodromy_fR:ℂ)+(1:ℝ)*Complex.I) (__BraidMonodromy_fR:ℂ))) := by
    simpa [__BraidMonodromy_zB, Path.trans_range] using (show __BraidMonodromy_zB t ∈ Set.range __BraidMonodromy_zB from ⟨t,rfl⟩)
  rcases ht with ht|ht|ht
  · rcases ht with ⟨s,hs⟩
    refine ⟨2, (s:ℝ), ?_, Or.inl ⟨rfl, s.2.1, s.2.2⟩⟩
    rw [← hs, Path.segment_apply, AffineMap.lineMap_apply_module]
    simp [Complex.real_smul]; push_cast; ring
  · rcases ht with ⟨s,hs⟩
    refine ⟨(1-(s:ℝ))*2 + (s:ℝ)*__BraidMonodromy_fR, 1, ?_, Or.inr (Or.inl rfl)⟩
    rw [← hs, Path.segment_apply, AffineMap.lineMap_apply_module]
    simp [Complex.real_smul]; push_cast; ring
  · rcases ht with ⟨s,hs⟩
    refine ⟨__BraidMonodromy_fR, (1-(s:ℝ)), ?_, Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)⟩
    · rw [← hs, Path.segment_apply, AffineMap.lineMap_apply_module]
      simp [Complex.real_smul]; push_cast; ring
    · linarith [s.2.2]
    · linarith [s.2.1]

private lemma __BraidMonodromy_cube_im (a b : ℝ) :
 (((a:ℂ)+(b:ℂ)*Complex.I)^3).im = b*(3*a^2-b^2) := by
 simp [pow_succ, Complex.mul_re, Complex.mul_im]
 ring

private lemma __BraidMonodromy_basic_small (a b : ℝ) (ha : __BraidMonodromy_nR ≤ a) (hA : a ≤ 2)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1/2) (hends : b=0 → a=__BraidMonodromy_nR ∨ a=2) :
    let z : ℂ := (a:ℂ)+(b:ℂ)*Complex.I
    z ≠ 0 ∧ z^3 ≠ (1:ℂ) ∧ z^3 ≠ (-8:ℂ) ∧
    0 < (braidU z).re := by
  dsimp
  have apos : 0 < a := lt_of_lt_of_le __BraidMonodromy_npos ha
  have denpos : 0 < a^2+b^2 := by positivity
  have bsmall : b^2 ≤ (1/2:ℝ)^2 := by nlinarith
  have alow : (2/5:ℝ) < __BraidMonodromy_nR := by dsimp [__BraidMonodromy_nR]; nlinarith [__BraidMonodromy_sqrt2sq', __BraidMonodromy_sqrt2_gt]
  have rel : 0 < a^2 - b^2 + 2*a/(a^2+b^2) := by
    have lowa : (2/5:ℝ) < a := lt_of_lt_of_le alow ha
    have term : 0 < 2*a/(a^2+b^2) := by positivity
    -- crude lower bound a²-b² > -1/4, term >? use a<=2 bound denominator
    have denle : a^2+b^2 ≤ (17/4:ℝ) := by nlinarith
    have termlow : (16/85:ℝ) < 2*a/(a^2+b^2) := by
      apply (lt_div_iff₀ denpos).2
      nlinarith
    have mainlow : -(9/100:ℝ) < a^2-b^2 := by nlinarith
    linarith
  have zne : (a:ℂ)+(b:ℂ)*Complex.I ≠ 0 := by
    intro e
    have := congrArg Complex.re e
    simp at this
    linarith
  refine ⟨zne, ?_, ?_, ?_⟩
  · by_cases hb : b = 0
    · subst b
      intro hh
      have hr : (a:ℝ)^3 = 1 := by simpa [pow_succ, Complex.mul_re] using congrArg Complex.re hh
      rcases hends rfl with he|he
      · exact __BraidMonodromy_nreal_ne1 (he ▸ hr)
      · norm_num [he] at hr
    · intro h
      have im := congrArg Complex.im h
      rw [__BraidMonodromy_cube_im] at im
      simp at im
      have bp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
      have aa : (2/5:ℝ) < a := lt_of_lt_of_le alow ha
      have posa : 0 < 3*a^2-b^2 := by nlinarith
      rcases im with e|e
      · exact (ne_of_gt bp) e
      · exact (ne_of_gt posa) e
  · by_cases hb : b = 0
    · subst b
      intro hh
      have hr : (a:ℝ)^3 = (-8:ℝ) := by simpa [pow_succ, Complex.mul_re] using congrArg Complex.re hh
      rcases hends rfl with he|he
      · exact __BraidMonodromy_nreal_ne8 (he ▸ hr)
      · norm_num [he] at hr
    · intro h
      have im := congrArg Complex.im h
      rw [__BraidMonodromy_cube_im] at im
      simp at im
      have bp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
      have aa : (2/5:ℝ) < a := lt_of_lt_of_le alow ha
      have posa : 0 < 3*a^2-b^2 := by nlinarith
      rcases im with e|e
      · exact (ne_of_gt bp) e
      · exact (ne_of_gt posa) e
  · rw [braidU_re _ _ zne]
    linarith

private lemma __BraidMonodromy_safeA (t : I) :
 let z := __BraidMonodromy_zA t
 z ≠ 0 ∧ z^3 ≠ (1:ℂ) ∧ z^3 ≠ (-8:ℂ) ∧ 0 < (braidU z).re := by
  obtain ⟨a,b, eq, h⟩ := __BraidMonodromy_zA_cases t
  dsimp
  rw [eq]
  rcases h with h|h|h
  · exact __BraidMonodromy_basic_small a b (by rw [h.1]; linarith [__BraidMonodromy_nlt]) (by rw [h.1]) h.2.1 h.2.2
       (fun bz => Or.inr h.1)
  · exact __BraidMonodromy_basic_small a b h.1 h.2.1 (by rw [h.2.2]; norm_num)
       (by rw [h.2.2])
       (by intro bad; exfalso; rw [h.2.2] at bad; norm_num at bad)
  · exact __BraidMonodromy_basic_small a b (by rw [h.1]) (by rw [h.1]; linarith [__BraidMonodromy_nlt]) h.2.1 h.2.2
       (fun bz => Or.inl h.1)

end KnotSupport

namespace KnotSupport
noncomputable section

/-- Safe the second polygon. Its projection is in the right half of the
coefficient slice. -/
private lemma __BraidMonodromy_safeB (t : I) :
 let z := __BraidMonodromy_zB t
 z ≠ 0 ∧ z^3 ≠ (1:ℂ) ∧ z^3 ≠ (-8:ℂ) ∧ -1 < (braidU z).re := by
  obtain ⟨a,b, eq, h⟩ := __BraidMonodromy_zB_cases t
  have main (cases :
      (a=2 ∧ 0 ≤ b ∧ b ≤ 1) ∨ (b=1) ∨ (a=__BraidMonodromy_fR ∧ 0 ≤ b ∧ b ≤ 1)) :
      let z : ℂ := (a:ℂ)+(b:ℂ)*Complex.I
      z ≠ 0 ∧ z^3 ≠ (1:ℂ) ∧ z^3 ≠ (-8:ℂ) ∧ -1 < (braidU z).re := by
    dsimp
    have denpos : 0 < a^2+b^2 := by
      rcases cases with c|c|c
      · rw [c.1]; nlinarith
      · rw [c]; nlinarith
      · rw [c.1]; nlinarith [__BraidMonodromy_flt]
    have zne : (a:ℂ)+(b:ℂ)*Complex.I ≠ 0 := by
      intro E
      have R := congrArg Complex.re E
      have Im := congrArg Complex.im E
      simp at R Im
      nlinarith
    have rebd : -3 < a^2-b^2 + 2*a/(a^2+b^2) := by
      rcases cases with c|c|c
      · rcases c with ⟨rfl,h0,h1⟩
        have bp : b^2 ≤ (1:ℝ) := by nlinarith
        have : 0 ≤ 2*(2:ℝ)/(2^2+b^2) := by positivity
        nlinarith
      · subst b
        have den : 0 < a^2+1 := by positivity
        have pp : 0 < (a^2)^2 + 3*a^2 + 2*a + 2 := by
          nlinarith [sq_nonneg (a + (1/3:ℝ))]
        have L : (-3:ℝ)*(a^2+1) < (a^2-1)*(a^2+1)+2*a := by
          nlinarith
        have LL : (-3:ℝ) < ((a^2-1)*(a^2+1)+2*a)/(a^2+1) :=
          (lt_div_iff₀ den).2 L
        convert LL using 1 <;> field_simp <;> ring
      · -- a very negative vertical side
        rcases c with ⟨rfl,h0,h1⟩
        have aa : __BraidMonodromy_fR < -2 := __BraidMonodromy_flt
        have bp : (b:ℝ)^2 ≤ 1 := by nlinarith
        have term : (-2:ℝ) < 2*__BraidMonodromy_fR/(__BraidMonodromy_fR^2+b^2) := by
          apply (lt_div_iff₀ (by nlinarith [sq_nonneg b, sq_nonneg __BraidMonodromy_fR] : 0 < __BraidMonodromy_fR^2+b^2)).2
          nlinarith [sq_nonneg b, sq_nonneg (__BraidMonodromy_fR+1)]
        nlinarith
    refine ⟨zne, ?_, ?_, ?_⟩
    · by_cases hb : b=0
      · subst b
        intro hh
        have hr : (a:ℝ)^3 = 1 := by simpa [pow_succ, Complex.mul_re] using congrArg Complex.re hh
        rcases cases with c|c|c
        · norm_num [c.1] at hr
        · norm_num at c
        · exact __BraidMonodromy_freal_ne1 (c.1 ▸ hr)
      · intro hh
        have im := congrArg Complex.im hh
        rw [__BraidMonodromy_cube_im] at im
        simp at im
        rcases im with be|be
        · exact hb be
        · -- b nonzero, so a²=b²/3. use the real part
          have re := congrArg Complex.re hh
          have rr : a^3 - 3*a*b^2 = 1 := by
            have rr0 : (a*a-b*b)*a - (a*b+b*a)*b = (1:ℝ) := by
              simpa [pow_succ, Complex.mul_re, Complex.mul_im] using re
            nlinarith
          rcases cases with c|c|c
          · rw [c.1] at be; nlinarith [c.2.2]
          · rw [c] at be rr
            nlinarith [sq_nonneg (a+ (1/3:ℝ))]
          · rw [c.1] at be
            have aa : __BraidMonodromy_fR < -2 := __BraidMonodromy_flt
            nlinarith [c.2.2]
    · by_cases hb : b=0
      · subst b
        intro hh
        have hr : (a:ℝ)^3 = (-8:ℝ) := by simpa [pow_succ, Complex.mul_re] using congrArg Complex.re hh
        rcases cases with c|c|c
        · norm_num [c.1] at hr
        · norm_num at c
        · exact __BraidMonodromy_freal_ne (c.1 ▸ hr)
      · intro hh
        have im := congrArg Complex.im hh
        rw [__BraidMonodromy_cube_im] at im
        simp at im
        rcases im with be|be
        · exact hb be
        · have re := congrArg Complex.re hh
          have rr : a^3 - 3*a*b^2 = (-8:ℝ) := by
            have rr0 : (a*a-b*b)*a - (a*b+b*a)*b = (-8:ℝ) := by
              simpa [pow_succ, Complex.mul_re, Complex.mul_im] using re
            nlinarith
          rcases cases with c|c|c
          · rw [c.1] at be; nlinarith [c.2.2]
          · rw [c] at be rr
            nlinarith [sq_nonneg (a-3)]
          · rw [c.1] at be
            have aa := __BraidMonodromy_flt
            nlinarith [c.2.2]
    · rw [braidU_re _ _ zne]
      linarith
  dsimp
  rw [eq]
  exact main h

end
end KnotSupport

namespace KnotSupport
noncomputable section
private def __BraidMonodromy_Delta (z : ℂ) : ℂ := z^2 + 8/z

private lemma __BraidMonodromy_Delta_re (a b : ℝ) (hne : (a:ℂ)+(b:ℂ)*Complex.I ≠ 0) :
 (__BraidMonodromy_Delta ((a:ℂ)+(b:ℂ)*Complex.I)).re =
     a^2 - b^2 + 8*a/(a^2+b^2) := by
  unfold __BraidMonodromy_Delta
  simp [Complex.div_re, Complex.normSq, Complex.mul_re,
    Complex.add_re, Complex.add_im, pow_two]

private lemma __BraidMonodromy_DeltaA_pos (t : I) : 0 < (__BraidMonodromy_Delta (__BraidMonodromy_zA t)).re := by
  obtain ⟨a,b,eq,h⟩ := __BraidMonodromy_zA_cases t
  rw [eq]
  have ha : __BraidMonodromy_nR ≤ a := by rcases h with h|h|h <;> nlinarith [h.1, __BraidMonodromy_nlt]
  have ha2 : a ≤ 2 := by rcases h with h|h|h <;> nlinarith [h.1, __BraidMonodromy_nlt]
  have hb0 : 0 ≤ b := by rcases h with h|h|h <;> nlinarith [h.2.1]
  have hb1 : b ≤ 1/2 := by rcases h with h|h|h <;> nlinarith [h.2.2]
  have apos : 0 < a := lt_of_lt_of_le __BraidMonodromy_npos ha
  have denpos : 0 < a^2+b^2 := by positivity
  have zne : (a:ℂ)+(b:ℂ)*Complex.I ≠ 0 := by
    intro E
    have r := congrArg Complex.re E
    simp at r
    linarith
  rw [__BraidMonodromy_Delta_re a b zne]
  have term : 0 < 8*a/(a^2+b^2) := by positivity
  have denle : a^2+b^2 ≤ (17/4:ℝ) := by nlinarith
  have alow : (2/5:ℝ) < a := lt_of_lt_of_le (by
    dsimp [__BraidMonodromy_nR] at ha ⊢
    nlinarith [__BraidMonodromy_sqrt2sq', __BraidMonodromy_sqrt2_gt]) ha
  have termlow : (32/17:ℝ)*a ≤ 8*a/(a^2+b^2) := by
    apply (le_div_iff₀ denpos).2
    nlinarith
  nlinarith

private lemma __BraidMonodromy_DeltaA_sqrt_cont : Continuous (fun t : I => Complex.sqrt (__BraidMonodromy_Delta (__BraidMonodromy_zA t))) := by
  have cz : Continuous (fun t : I => __BraidMonodromy_zA t) := (__BraidMonodromy_zA).continuous
  have dcont : Continuous (fun t : I => __BraidMonodromy_Delta (__BraidMonodromy_zA t)) := by
    unfold __BraidMonodromy_Delta
    exact (cz.pow 2).add (continuous_const.div cz (fun t => (__BraidMonodromy_safeA t).1))
  apply continuous_iff_continuousAt.2
  intro t
  apply (Complex.continuousAt_sqrt (Or.inl (le_of_lt (__BraidMonodromy_DeltaA_pos t)))).comp_of_eq
    (dcont.continuousAt) rfl

end
end KnotSupport

namespace KnotSupport
noncomputable section
private lemma __BraidMonodromy_zA_zero : __BraidMonodromy_zA 0 = (2:ℂ) := by simp [__BraidMonodromy_zA]
private lemma __BraidMonodromy_zA_one : __BraidMonodromy_zA 1 = (__BraidMonodromy_nR:ℂ) := by simp [__BraidMonodromy_zA]
private lemma __BraidMonodromy_zB_zero : __BraidMonodromy_zB 0 = (2:ℂ) := by simp [__BraidMonodromy_zB]
private lemma __BraidMonodromy_zB_one : __BraidMonodromy_zB 1 = (__BraidMonodromy_fR:ℂ) := by simp [__BraidMonodromy_zB]
private lemma __BraidMonodromy_u_two : braidU (2:ℂ) = (5:ℂ)/3 := by norm_num [braidU]
private lemma __BraidMonodromy_nRF : (__BraidMonodromy_nR:ℂ)^3 - 5*(__BraidMonodromy_nR:ℂ) + 2 = 0 := by
  have h:=__BraidMonodromy_sqrt2sq'
  have h3 := congrArg (fun y : ℝ => y * Real.sqrt 2) h
  have hh : __BraidMonodromy_nR^3 - 5*__BraidMonodromy_nR + 2 = (0:ℝ) := by
    dsimp [__BraidMonodromy_nR]
    ring_nf
    nlinarith
  exact_mod_cast hh
private lemma __BraidMonodromy_fRF : (__BraidMonodromy_fR:ℂ)^3 - 5*(__BraidMonodromy_fR:ℂ) + 2 = 0 := by
  have h:=__BraidMonodromy_sqrt2sq'
  have h3 := congrArg (fun y : ℝ => y * Real.sqrt 2) h
  have hh : __BraidMonodromy_fR^3 - 5*__BraidMonodromy_fR + 2 = (0:ℝ) := by
    dsimp [__BraidMonodromy_fR]
    ring_nf
    nlinarith
  exact_mod_cast hh
private lemma __BraidMonodromy_u_near : braidU (__BraidMonodromy_nR:ℂ) = (5:ℂ)/3 := by
  have hn : (__BraidMonodromy_nR:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt __BraidMonodromy_npos)
  unfold braidU
  field_simp
  linear_combination __BraidMonodromy_nRF
private lemma __BraidMonodromy_u_far : braidU (__BraidMonodromy_fR:ℂ) = (5:ℂ)/3 := by
  have hn : (__BraidMonodromy_fR:ℂ) ≠ 0 := by
    exact_mod_cast (by have := __BraidMonodromy_flt; intro h; rw [h] at this; norm_num at this : __BraidMonodromy_fR ≠ 0)
  unfold braidU
  field_simp
  linear_combination __BraidMonodromy_fRF

end
end KnotSupport

namespace KnotSupport
noncomputable section
/-- Projection of the two drawn lifts to the coefficient half-plane. -/
private def __BraidMonodromy_loopA : Path braidBase braidBase where
  toFun t := ⟨braidU (__BraidMonodromy_zA t),
    lt_trans (by norm_num) (__BraidMonodromy_safeA t).2.2.2,
    braidU_good (__BraidMonodromy_safeA t).1 (__BraidMonodromy_safeA t).2.1 (__BraidMonodromy_safeA t).2.2.1⟩
  continuous_toFun := by
    have cz : Continuous (fun t : I => __BraidMonodromy_zA t) := __BraidMonodromy_zA.continuous
    have bc : Continuous (fun t : I => braidU (__BraidMonodromy_zA t)) := by
      unfold braidU
      exact ((cz.pow 3).add continuous_const).div
        (continuous_const.mul cz)
        (by intro t
            exact mul_ne_zero (by norm_num) (__BraidMonodromy_safeA t).1)
    fun_prop
  source' := by apply Subtype.ext; change braidU (__BraidMonodromy_zA 0) = (5:ℂ)/3; rw [__BraidMonodromy_zA_zero, __BraidMonodromy_u_two]
  target' := by apply Subtype.ext; change braidU (__BraidMonodromy_zA 1) = _; rw [__BraidMonodromy_zA_one,__BraidMonodromy_u_near]; rfl
private def __BraidMonodromy_loopB : Path braidBase braidBase where
  toFun t := ⟨braidU (__BraidMonodromy_zB t),
    (__BraidMonodromy_safeB t).2.2.2,
    braidU_good (__BraidMonodromy_safeB t).1 (__BraidMonodromy_safeB t).2.1 (__BraidMonodromy_safeB t).2.2.1⟩
  continuous_toFun := by
    have cz : Continuous (fun t : I => __BraidMonodromy_zB t) := __BraidMonodromy_zB.continuous
    have bc : Continuous (fun t : I => braidU (__BraidMonodromy_zB t)) := by
      unfold braidU
      exact ((cz.pow 3).add continuous_const).div
        (continuous_const.mul cz)
        (by intro t
            exact mul_ne_zero (by norm_num) (__BraidMonodromy_safeB t).1)
    fun_prop
  source' := by apply Subtype.ext; change braidU (__BraidMonodromy_zB 0) = (5:ℂ)/3; rw [__BraidMonodromy_zB_zero, __BraidMonodromy_u_two]
  target' := by apply Subtype.ext; change braidU (__BraidMonodromy_zB 1) = _; rw [__BraidMonodromy_zB_one,__BraidMonodromy_u_far]; rfl

-- a coefficient associated to a value of the marked root
private def __BraidMonodromy_goodOf (z : ℂ) (hz : z ≠ 0)
    (h1 : z^3 ≠ (1:ℂ)) (h8 : z^3 ≠ (-8:ℂ)) : CubicGood :=
  ⟨(braidU z, (1:ℂ)), by simpa using braidU_good hz h1 h8⟩
private lemma __BraidMonodromy_root_eq_braid (z : ℂ) (hz : z ≠ 0) :
    z^3 - 3*(braidU z)*z + 2*(1:ℂ) = 0 := by
  unfold braidU
  field_simp
  ring

-- displayed lift of A and B, carrying root two
private def __BraidMonodromy_liftA : Path rootTwo rootNear where
  toFun t := ⟨(⟨(braidU (__BraidMonodromy_zA t), (1:ℂ)),
      (by simpa using braidU_good (__BraidMonodromy_safeA t).1 (__BraidMonodromy_safeA t).2.1 (__BraidMonodromy_safeA t).2.2.1)⟩, __BraidMonodromy_zA t),
      __BraidMonodromy_root_eq_braid _ (__BraidMonodromy_safeA t).1⟩
  continuous_toFun := by
    have cz : Continuous (fun t : I => __BraidMonodromy_zA t) := __BraidMonodromy_zA.continuous
    have bc : Continuous (fun t : I => braidU (__BraidMonodromy_zA t)) := by
      unfold braidU
      exact ((cz.pow 3).add continuous_const).div
        (continuous_const.mul cz)
        (by intro t
            exact mul_ne_zero (by norm_num) (__BraidMonodromy_safeA t).1)
    fun_prop
  source' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · change braidU (__BraidMonodromy_zA 0) = (5:ℂ)/3; rw [__BraidMonodromy_zA_zero, __BraidMonodromy_u_two]
      · rfl
    · exact __BraidMonodromy_zA_zero
  target' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · change braidU (__BraidMonodromy_zA 1) = (5:ℂ)/3; rw [__BraidMonodromy_zA_one, __BraidMonodromy_u_near]
      · rfl
    · change __BraidMonodromy_zA 1 = (↑((-1+ Real.sqrt 2:ℝ)) : ℂ)
      exact __BraidMonodromy_zA_one
private def __BraidMonodromy_liftB : Path rootTwo rootFar where
  toFun t := ⟨(⟨(braidU (__BraidMonodromy_zB t), (1:ℂ)),
      (by simpa using braidU_good (__BraidMonodromy_safeB t).1 (__BraidMonodromy_safeB t).2.1 (__BraidMonodromy_safeB t).2.2.1)⟩, __BraidMonodromy_zB t),
      __BraidMonodromy_root_eq_braid _ (__BraidMonodromy_safeB t).1⟩
  continuous_toFun := by
    have cz : Continuous (fun t : I => __BraidMonodromy_zB t) := __BraidMonodromy_zB.continuous
    have bc : Continuous (fun t : I => braidU (__BraidMonodromy_zB t)) := by
      unfold braidU
      exact ((cz.pow 3).add continuous_const).div
        (continuous_const.mul cz)
        (by intro t
            exact mul_ne_zero (by norm_num) (__BraidMonodromy_safeB t).1)
    fun_prop
  source' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · change braidU (__BraidMonodromy_zB 0) = (5:ℂ)/3; rw [__BraidMonodromy_zB_zero, __BraidMonodromy_u_two]
      · rfl
    · exact __BraidMonodromy_zB_zero
  target' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · change braidU (__BraidMonodromy_zB 1) = (5:ℂ)/3; rw [__BraidMonodromy_zB_one, __BraidMonodromy_u_far]
      · rfl
    · change __BraidMonodromy_zB 1 = (↑((-1- Real.sqrt 2:ℝ)) : ℂ)
      exact __BraidMonodromy_zB_one
end
end KnotSupport

namespace KnotSupport
noncomputable section
private def __BraidMonodromy_wA (t : I) : ℂ := (-(__BraidMonodromy_zA t) - Complex.sqrt (__BraidMonodromy_Delta (__BraidMonodromy_zA t)))/2
private lemma __BraidMonodromy_wA_cont : Continuous __BraidMonodromy_wA := by
  unfold __BraidMonodromy_wA
  have cz : Continuous (fun t : I => __BraidMonodromy_zA t) := __BraidMonodromy_zA.continuous
  exact ((cz.neg).sub __BraidMonodromy_DeltaA_sqrt_cont).div_const 2
private lemma __BraidMonodromy_sqrt_sq_pos (x : ℂ) (h : 0 < x.re) :
    Complex.sqrt (x^2) = x := by
  simpa [Complex.sqrt] using (Complex.sq_cpow_two_inv (x:=x) h)
private lemma __BraidMonodromy_da_two : Complex.sqrt (__BraidMonodromy_Delta (2:ℂ)) = ((2 * Real.sqrt 2 : ℝ):ℂ) := by
  have hh : __BraidMonodromy_Delta (2:ℂ) = (((2 * Real.sqrt 2:ℝ):ℂ)^2) := by
    unfold __BraidMonodromy_Delta
    norm_num
    have h : (8:ℝ) = (2 * Real.sqrt 2 :ℝ)^2 := by
      rw [mul_pow, Real.sq_sqrt] <;> norm_num
    have hc := congrArg (fun x : ℝ => (x:ℂ)) h
    norm_num at hc ⊢
    exact hc
  rw [hh, __BraidMonodromy_sqrt_sq_pos]
  norm_num
private lemma __BraidMonodromy_da_near : Complex.sqrt (__BraidMonodromy_Delta (__BraidMonodromy_nR:ℂ)) = ((3 + Real.sqrt 2 : ℝ):ℂ) := by
  have hn : (__BraidMonodromy_nR:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt __BraidMonodromy_npos)
  have hhR : __BraidMonodromy_nR^2 + 8/__BraidMonodromy_nR = (3 + Real.sqrt 2:ℝ)^2 := by
    have sq := __BraidMonodromy_sqrt2sq'
    have sq3 := congrArg (fun a : ℝ => a * Real.sqrt 2) sq
    have hn' := __BraidMonodromy_npos
    dsimp [__BraidMonodromy_nR] at *
    field_simp
    ring_nf
    nlinarith
  have hh : __BraidMonodromy_Delta (__BraidMonodromy_nR:ℂ) = (((3 + Real.sqrt 2:ℝ):ℂ)^2) := by
    unfold __BraidMonodromy_Delta
    exact_mod_cast hhR
  rw [hh, __BraidMonodromy_sqrt_sq_pos]
  norm_num
  linarith [__BraidMonodromy_sqrt2_gt]
private lemma __BraidMonodromy_wA_zero : __BraidMonodromy_wA 0 = (__BraidMonodromy_fR:ℂ) := by
  unfold __BraidMonodromy_wA
  rw [__BraidMonodromy_zA_zero, __BraidMonodromy_da_two]
  dsimp [__BraidMonodromy_fR]
  push_cast
  ring
private lemma __BraidMonodromy_wA_one : __BraidMonodromy_wA 1 = (__BraidMonodromy_fR:ℂ) := by
  unfold __BraidMonodromy_wA
  rw [__BraidMonodromy_zA_one, __BraidMonodromy_da_near]
  dsimp [__BraidMonodromy_fR, __BraidMonodromy_nR]
  push_cast
  ring
-- algebraic companion root for every nonzero marked root
private lemma __BraidMonodromy_wA_root (t : I) :
    (__BraidMonodromy_wA t)^3 - 3*(braidU (__BraidMonodromy_zA t))*(__BraidMonodromy_wA t) + 2*(1:ℂ) = 0 := by
  have hn : __BraidMonodromy_zA t ≠ 0 := (__BraidMonodromy_safeA t).1
  let z : ℂ := __BraidMonodromy_zA t
  let s : ℂ := Complex.sqrt (__BraidMonodromy_Delta (__BraidMonodromy_zA t))
  have hz : z ≠ 0 := hn
  have key : z * s^2 - z^3 - 8 = 0 := by
    have sq : s^2 = __BraidMonodromy_Delta z := by
      dsimp [s, z]
      simp [Complex.sqrt]
    rw [sq]
    unfold __BraidMonodromy_Delta
    field_simp
    ring
  dsimp [__BraidMonodromy_wA, braidU]
  simp only [mul_one]
  change ((-z-s)/2)^3 - 3*((z^3+2)/(3*z))*((-z-s)/2)+2=0
  field_simp
  linear_combination (-(3*z+s)) * key

end
end KnotSupport
namespace KnotSupport
noncomputable section
private def __BraidMonodromy_liftFix : Path rootFar rootFar where
  toFun t := ⟨(⟨(braidU (__BraidMonodromy_zA t), (1:ℂ)),
    (by simpa using braidU_good (__BraidMonodromy_safeA t).1 (__BraidMonodromy_safeA t).2.1 (__BraidMonodromy_safeA t).2.2.1)⟩,
      __BraidMonodromy_wA t), __BraidMonodromy_wA_root t⟩
  continuous_toFun := by
    have cz : Continuous (fun t : I => __BraidMonodromy_zA t) := __BraidMonodromy_zA.continuous
    have bc : Continuous (fun t : I => braidU (__BraidMonodromy_zA t)) := by
      unfold braidU
      exact ((cz.pow 3).add continuous_const).div (continuous_const.mul cz)
        (by intro t; exact mul_ne_zero (by norm_num) (__BraidMonodromy_safeA t).1)
    have wc := __BraidMonodromy_wA_cont
    fun_prop
  source' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · change braidU (__BraidMonodromy_zA 0) = (5:ℂ)/3; rw [__BraidMonodromy_zA_zero,__BraidMonodromy_u_two]
      · rfl
    · exact __BraidMonodromy_wA_zero
  target' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · change braidU (__BraidMonodromy_zA 1) = (5:ℂ)/3; rw [__BraidMonodromy_zA_one,__BraidMonodromy_u_near]
      · rfl
    · exact __BraidMonodromy_wA_one

-- the three lifted paths project to the claimed coefficient paths
private def __BraidMonodromy_sliceCoeff : CubicSliceDomain → CubicGood :=
  fun u => trefoilCoeffs (sliceExterior u)
private lemma __BraidMonodromy_sliceCoeff_cont : Continuous __BraidMonodromy_sliceCoeff := trefoilCoeffs_cont.comp sliceExterior_cont
private lemma __BraidMonodromy_sliceCoeff_eq (u : CubicSliceDomain) :
    __BraidMonodromy_sliceCoeff u = ⟨(u.1,(1:ℂ)), by simpa using u.2.2⟩ := by
  apply Subtype.ext
  exact coeff_slice u

private lemma __BraidMonodromy_map_liftA : __BraidMonodromy_liftA.map root_cover.continuous =
    (__BraidMonodromy_loopA.map __BraidMonodromy_sliceCoeff_cont).cast rootTwo_over rootNear_over := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change (braidU (__BraidMonodromy_zA t), (1:ℂ)) = (__BraidMonodromy_sliceCoeff (__BraidMonodromy_loopA t)).1
  unfold __BraidMonodromy_sliceCoeff
  rw [coeff_slice]
  rfl
private lemma __BraidMonodromy_map_liftB : __BraidMonodromy_liftB.map root_cover.continuous =
    (__BraidMonodromy_loopB.map __BraidMonodromy_sliceCoeff_cont).cast rootTwo_over rootFar_over := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change (braidU (__BraidMonodromy_zB t), (1:ℂ)) = (__BraidMonodromy_sliceCoeff (__BraidMonodromy_loopB t)).1
  unfold __BraidMonodromy_sliceCoeff
  rw [coeff_slice]
  rfl
private lemma __BraidMonodromy_map_liftFix : __BraidMonodromy_liftFix.map root_cover.continuous =
    (__BraidMonodromy_loopA.map __BraidMonodromy_sliceCoeff_cont).cast rootFar_over rootFar_over := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change (braidU (__BraidMonodromy_zA t), (1:ℂ)) = (__BraidMonodromy_sliceCoeff (__BraidMonodromy_loopA t)).1
  unfold __BraidMonodromy_sliceCoeff
  rw [coeff_slice]
  rfl
end
end KnotSupport
namespace KnotSupport
noncomputable section
private lemma __BraidMonodromy_uncast_monodromy {x y : CubicRoot} {b c : CubicGood}
    (hx : rootPr x = b) (hy : rootPr y = c) (P : Path b c)
    (L : Path x y) (hL : L.map root_cover.continuous = P.cast hx hy) :
    root_cover.monodromy (.mk P) ⟨x,hx⟩ = ⟨y,hy⟩ := by
  subst b
  subst c
  have hm := root_cover.monodromy_map (.mk L)
  change root_cover.monodromy (.mk (L.map root_cover.continuous)) _ = _ at hm
  have h : L.map root_cover.continuous = P := by simpa using hL
  simpa [h]
      using hm
private lemma __BraidMonodromy_monoA :
 root_cover.monodromy (.mk (__BraidMonodromy_loopA.map __BraidMonodromy_sliceCoeff_cont))
    ⟨rootTwo, rootTwo_over⟩ = ⟨rootNear, rootNear_over⟩ := by
  exact __BraidMonodromy_uncast_monodromy rootTwo_over rootNear_over _ __BraidMonodromy_liftA __BraidMonodromy_map_liftA
private lemma __BraidMonodromy_monoB :
 root_cover.monodromy (.mk (__BraidMonodromy_loopB.map __BraidMonodromy_sliceCoeff_cont))
    ⟨rootTwo, rootTwo_over⟩ = ⟨rootFar, rootFar_over⟩ := by
  exact __BraidMonodromy_uncast_monodromy rootTwo_over rootFar_over _ __BraidMonodromy_liftB __BraidMonodromy_map_liftB
private lemma __BraidMonodromy_monoFix :
 root_cover.monodromy (.mk (__BraidMonodromy_loopA.map __BraidMonodromy_sliceCoeff_cont))
    ⟨rootFar, rootFar_over⟩ = ⟨rootFar, rootFar_over⟩ := by
  exact __BraidMonodromy_uncast_monodromy rootFar_over rootFar_over _ __BraidMonodromy_liftFix __BraidMonodromy_map_liftFix
end
end KnotSupport
namespace KnotSupport
noncomputable section
lemma map_slice_A : (__BraidMonodromy_loopA.map sliceExterior_cont).map trefoilCoeffs_cont =
    __BraidMonodromy_loopA.map __BraidMonodromy_sliceCoeff_cont := by rfl
lemma map_slice_B : (__BraidMonodromy_loopB.map sliceExterior_cont).map trefoilCoeffs_cont =
    __BraidMonodromy_loopB.map __BraidMonodromy_sliceCoeff_cont := by rfl

/-- The two explicit loops have noncommuting root continuations. -/
theorem cubic_braid_hne :
 root_cover.monodromy
      ((Path.Homotopic.Quotient.mk
        (((__BraidMonodromy_loopB.map sliceExterior_cont).trans
          (__BraidMonodromy_loopA.map sliceExterior_cont)))).map coeffCM)
        ⟨rootTwo, rootTwo_over⟩ ≠
 root_cover.monodromy
      ((Path.Homotopic.Quotient.mk
        (((__BraidMonodromy_loopA.map sliceExterior_cont).trans
          (__BraidMonodromy_loopB.map sliceExterior_cont)))).map coeffCM)
        ⟨rootTwo, rootTwo_over⟩ := by
  intro eq0
  have left : root_cover.monodromy
       ((Path.Homotopic.Quotient.mk (__BraidMonodromy_loopB.map __BraidMonodromy_sliceCoeff_cont)).trans
        (Path.Homotopic.Quotient.mk (__BraidMonodromy_loopA.map __BraidMonodromy_sliceCoeff_cont)))
       ⟨rootTwo, rootTwo_over⟩ = ⟨rootFar, rootFar_over⟩ := by
    rw [root_cover.monodromy_trans_apply]
    rw [__BraidMonodromy_monoB, __BraidMonodromy_monoFix]
  have rightNe : root_cover.monodromy
       ((Path.Homotopic.Quotient.mk (__BraidMonodromy_loopA.map __BraidMonodromy_sliceCoeff_cont)).trans
        (Path.Homotopic.Quotient.mk (__BraidMonodromy_loopB.map __BraidMonodromy_sliceCoeff_cont)))
       ⟨rootTwo, rootTwo_over⟩ ≠ ⟨rootFar, rootFar_over⟩ := by
    rw [root_cover.monodromy_trans_apply, __BraidMonodromy_monoA]
    intro bad
    -- If the `B` continuation also took the near root to the far
    -- root, it could not already take the root `2` to the same far
    -- root.  Monodromy in a covering is bijective on each fibre.
    have inj := (root_cover.monodromy_bijective
      (Path.Homotopic.Quotient.mk (__BraidMonodromy_loopB.map __BraidMonodromy_sliceCoeff_cont))).1
    have eqa : (⟨rootNear, rootNear_over⟩ :
        (rootPr ⁻¹' ({__BraidMonodromy_sliceCoeff braidBase} : Set CubicGood))) =
       ⟨rootTwo, rootTwo_over⟩ := by
      apply inj
      -- the two images are both the far sheet, by `bad` and by
      -- the displayed lift of `B` starting at 2
      simpa [__BraidMonodromy_monoB] using bad
    have er := congrArg (fun v :
        (rootPr ⁻¹' ({__BraidMonodromy_sliceCoeff braidBase} : Set CubicGood)) => v.1) eqa
    exact rootTwo_ne_rootNear er.symm
  apply rightNe
  -- The paths in the statement live first in the exterior. Mapping
  -- their representatives by the coefficient map is definitionally the
  -- same as taking the two coefficient paths; `mk_map` and `mk_trans`
  -- remove the quotient bookkeeping.
  -- hence `eq0` identifies exactly the two coefficient continuations.
  have hBA :
      ((Path.Homotopic.Quotient.mk
        ((__BraidMonodromy_loopB.map sliceExterior_cont).trans
             (__BraidMonodromy_loopA.map sliceExterior_cont))).map coeffCM) =
      ((Path.Homotopic.Quotient.mk (__BraidMonodromy_loopB.map __BraidMonodromy_sliceCoeff_cont)).trans
       (Path.Homotopic.Quotient.mk (__BraidMonodromy_loopA.map __BraidMonodromy_sliceCoeff_cont))) := by
    rw [← Path.Homotopic.Quotient.mk_map]
    rw [Path.map_trans]
    change Path.Homotopic.Quotient.mk
      (((__BraidMonodromy_loopB.map sliceExterior_cont).map trefoilCoeffs_cont).trans
       ((__BraidMonodromy_loopA.map sliceExterior_cont).map trefoilCoeffs_cont)) = _
    rw [map_slice_A, map_slice_B]
    rfl
  have hAB :
      ((Path.Homotopic.Quotient.mk
        ((__BraidMonodromy_loopA.map sliceExterior_cont).trans
             (__BraidMonodromy_loopB.map sliceExterior_cont))).map coeffCM) =
      ((Path.Homotopic.Quotient.mk (__BraidMonodromy_loopA.map __BraidMonodromy_sliceCoeff_cont)).trans
       (Path.Homotopic.Quotient.mk (__BraidMonodromy_loopB.map __BraidMonodromy_sliceCoeff_cont))) := by
    rw [← Path.Homotopic.Quotient.mk_map]
    rw [Path.map_trans]
    change Path.Homotopic.Quotient.mk
      (((__BraidMonodromy_loopA.map sliceExterior_cont).map trefoilCoeffs_cont).trans
       ((__BraidMonodromy_loopB.map sliceExterior_cont).map trefoilCoeffs_cont)) = _
    rw [map_slice_A, map_slice_B]
    rfl
  have eq1 : root_cover.monodromy
       ((Path.Homotopic.Quotient.mk (__BraidMonodromy_loopB.map __BraidMonodromy_sliceCoeff_cont)).trans
        (Path.Homotopic.Quotient.mk (__BraidMonodromy_loopA.map __BraidMonodromy_sliceCoeff_cont)))
       ⟨rootTwo, rootTwo_over⟩ =
       root_cover.monodromy
       ((Path.Homotopic.Quotient.mk (__BraidMonodromy_loopA.map __BraidMonodromy_sliceCoeff_cont)).trans
        (Path.Homotopic.Quotient.mk (__BraidMonodromy_loopB.map __BraidMonodromy_sliceCoeff_cont)))
       ⟨rootTwo, rootTwo_over⟩ := by
    rw [hBA] at eq0
    rw [hAB] at eq0
    exact eq0

  exact eq1.symm.trans left

/-- convenient existence package -/
theorem braid_witness :
    ∃ (A B : Path braidBase braidBase),
 root_cover.monodromy
      ((Path.Homotopic.Quotient.mk
        (((B.map sliceExterior_cont).trans
          (A.map sliceExterior_cont)))).map coeffCM)
        ⟨rootTwo, rootTwo_over⟩ ≠
 root_cover.monodromy
      ((Path.Homotopic.Quotient.mk
        (((A.map sliceExterior_cont).trans
          (B.map sliceExterior_cont)))).map coeffCM)
        ⟨rootTwo, rootTwo_over⟩ :=
  ⟨__BraidMonodromy_loopA, __BraidMonodromy_loopB, cubic_braid_hne⟩
end
end KnotSupport

end

end
-- END INLINED FILE: Mathlib/Support/exists_nonisotopic_knots_e941e76034/BraidMonodromy.lean

-- BEGIN INLINED MAIN PRELUDE



open LeanEval.KnotTheory
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem exists_nonisotopic_knots : ∃ K₁ K₂ : Knot, ¬ K₁.Isotopic K₂ :=
/-ResultProofBegin-/by
  -- Work with completely explicit (embedded, with non-zero velocity) curves.
  -- All of the analytic details needed to construct these objects are separated
  -- in support; the remaining obstruction is purely topological.
  let U : Knot :=
    { curve := KnotSupport.circle
      smooth := KnotSupport.circle_smooth
      periodic := KnotSupport.circle_periodic
      injOn := KnotSupport.circle_injOn
      immersion := KnotSupport.circle_immersion }
  let T : Knot :=
    { curve := KnotSupport.trefoil
      smooth := KnotSupport.trefoil_smooth
      periodic := KnotSupport.trefoil_periodic
      injOn := KnotSupport.trefoil_injOn
      immersion := KnotSupport.trefoil_immersion }
  refine ⟨U, T, ?_⟩
  -- isolate the topological obstruction without any reference to the
  -- parametrization or to differentiability.  This is strictly weaker than
  -- no ambient isotopy: a smooth isotopy at time 1 gives such a homeomorphism.
  have different_complements :
      ¬ Nonempty
        (↥((Set.range KnotSupport.circle : Set (EuclideanSpace ℝ (Fin 3)))ᶜ)
          ≃ₜ
        ↥((Set.range KnotSupport.trefoil : Set (EuclideanSpace ℝ (Fin 3)))ᶜ)) := by
    -- Work with a deliberately weak, base-point free invariant.  This way
    -- this step needs neither an extension of a homeomorphism across the
    -- removed curve nor any change-of-base-point choices.
    have fundamental_calculation :
        KnotSupport.FGAbelian
          ↥((Set.range KnotSupport.circle :
              Set (EuclideanSpace ℝ (Fin 3)))ᶜ) ∧
        ¬ KnotSupport.FGAbelian
          ↥((Set.range KnotSupport.trefoil :
              Set (EuclideanSpace ℝ (Fin 3)))ᶜ) := by
      -- Inversion in the point `(1,0,0)` changes the first of these
      -- computations substantially.  Its target is literally the complement
      -- of a straight line and one point, with no quotients or choices of
      -- angles.  The point must not be dropped (it is the old point at
      -- infinity). `invHomeo` proves this by an involutive Euclidean
      -- inversion and also identifies the range of the parametrised circle.
      -- Thus the only remaining calculation for the unknot is for this very
      -- elementary model `LP`.
      have lower :
          KnotSupport.FGAbelian KnotSupport.LP ∧
          ¬ KnotSupport.FGAbelian
            ↥((Set.range KnotSupport.trefoil :
                Set (EuclideanSpace ℝ (Fin 3)))ᶜ) := by
        constructor
        · -- Do not accidentally fill the old point at infinity here.  The
          -- plain line complement has a topological-group structure, but
          -- `LP` is its cylinder with precisely `(0,1/2)` deleted.
          -- `lpHomeo` supplies exactly this subspace chart.  The elementary
          -- paths `cylPoint_paths` first leave the zero-height slice before
          -- changing the transverse value.  Thus change of base point is not
          -- part of the remaining loop calculation.
          have hsub :
              KnotSupport.FGAbelian
                {u : KnotSupport.Cyl // u ≠ KnotSupport.cylPoint} := by
            apply KnotSupport.FGAbelian_of_paths
              KnotSupport.cylBase KnotSupport.cylPoint_paths
            intro a b
            -- Filling the point gives the honest cylinder.  Its vertex
            -- groups commute since it is a topological group.  The remaining
            -- issue in this *one* based calculation is that deleting a point
            -- in this three dimensional cylinder is injective on based
            -- loops (a relative, not a free, statement).
            have hinj : Function.Injective
                (FundamentalGroup.map KnotSupport.cylInclusion
                  KnotSupport.cylBase) := by
              -- Remove the algebraic quotient.  This isolates the relative
              -- two-dimensional avoidance assertion for honest loops; there
              -- are no endpoint `eqToHom` casts in this version.
              refine
                KnotSupport.cylInclusion_base_injective_of_homotopies ?_
              intro p q h
              -- The filled square is used only for its transverse path.  A
              -- precise one-dimensional reduction is proved in support.
              refine
                KnotSupport.puncture_homotopy_of_clean_replacement
                  ?_ p q h
              intro r
              -- Bad transverse values of this particular loop lie in a
              -- compact band strictly below zero.  Thus a local detour of a
              -- path, not a perturbation of a whole arbitrary square, is the
              -- remaining issue.
              obtain ⟨d, hd, hband⟩ :=
                KnotSupport.exceptional_negative_band r
              have collar : ∀ t : Set.Icc (0:ℝ) 1,
                    -d < KnotSupport.cylHeight r t →
                    KnotSupport.cylHeight r t ≤ 0 →
                    KnotSupport.punctZ (r t) ≠ KnotSupport.zh :=
                KnotSupport.no_exception_near_zero hd hband
              have transverse :
                  ∃ Z : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1,
                            KnotSupport.Zstar),
                    (∀ t, Z (0,t) = KnotSupport.punctZ (r t)) ∧
                    (∀ s, Z (s,0) = KnotSupport.zh) ∧
                    (∀ s, Z (s,1) = KnotSupport.zh) ∧
                    (∀ s t, KnotSupport.cylHeight r t = 0 →
                               Z (s,t) ≠ KnotSupport.zh) ∧
                    (∀ t, KnotSupport.cylHeight r t < 0 →
                               Z (1,t) ≠ KnotSupport.zh) := by
                by_cases already : KnotSupport.CleanBelow r
                · exact KnotSupport.transverse_of_clean r already
                · -- The nontrivial case is now a path (one real
                  -- parameter) in `ℂ*`, on the strictly negative compact
                  -- band above.  No arbitrary square in the ambient
                  -- cylinder has to be approximated.
                  classical
                  unfold KnotSupport.CleanBelow at already
                  push_neg at already
                  obtain ⟨tbad, hneg, hzbad⟩ := already
                  have htbad : KnotSupport.cylHeight r tbad ≤ -d :=
                    hband tbad hneg hzbad
                  -- A small polygonal motion of the transverse boundary,
                  -- rather than any motion of the square in the cylinder,
                  -- is the convenient way to handle this band.  Its
                  -- construction in support fixes the endpoints, stays
                  -- closer than the two compact margins, and misses `zh`
                  -- at every interior parameter.
                  exact KnotSupport.detour_transverse r
              rcases transverse with ⟨Z,z0,zs,ze,zedge,zclean⟩
              exact KnotSupport.exists_clean_of_transverse r Z z0 zs ze
                zedge zclean
            apply hinj
            simpa [map_mul] using
              (KnotSupport.FGAbelian_cyl
                (KnotSupport.cylInclusion KnotSupport.cylBase)
                ((FundamentalGroup.map KnotSupport.cylInclusion
                    KnotSupport.cylBase) a)
                ((FundamentalGroup.map KnotSupport.cylInclusion
                    KnotSupport.cylBase) b))
          exact KnotSupport.FGAbelian.homeomorph
            KnotSupport.lpHomeo.symm hsub
        · -- The torus parametrisation has especially simple *global*
          -- cylindrical coefficients. `torXi` is `(radius-2,z)`, while
          -- `torEta` is the unit angular coordinate (shrunk linearly across
          -- the axis).  The actual subset removed from `ℝ³` is exactly the
          -- single discriminant fibre `xi^3=eta^2`; there is no identification
          -- at infinity here.  `disc_iff_trefoil` proves both directions,
          -- using the useful group calculation `e = xi^2/eta` to choose its
          -- parameter.  Consequently `trefoilCoeffs` is a continuous map
          -- from this very complement to the open set of good depressed
          -- cubics.
          --
          -- It suffices to compute monodromy in the root cover of that
          -- open set.  In fact the loops need only be drawn in the half
          -- plane `eta=1`: `sliceExterior` embeds
          -- `{u.re > -1, u^3 ≠ 1}` into the true complement, on which the
          -- coefficient map is literally `u ↦ (u,1)` (`coeff_slice`).
          -- Thus the only outstanding trefoil-specific fact is the familiar
          -- one-variable cubic-root continuation calculation below, not a
          -- presentation or a free-homotopy assertion about its exterior.
          have cubic_monodromy :
              ∃ (cov : IsCoveringMap KnotSupport.rootPr)
                (u : KnotSupport.CubicSliceDomain)
                (e : KnotSupport.CubicRoot),
                ∃ he : KnotSupport.rootPr e =
                    KnotSupport.trefoilCoeffs (KnotSupport.sliceExterior u),
                ∃ (A B : Path u u),
                  cov.monodromy
                    ((Path.Homotopic.Quotient.mk
                      (((B.map KnotSupport.sliceExterior_cont).trans
                         (A.map KnotSupport.sliceExterior_cont)))).map
                        KnotSupport.coeffCM) ⟨e, he⟩ ≠
                  cov.monodromy
                    ((Path.Homotopic.Quotient.mk
                      (((A.map KnotSupport.sliceExterior_cont).trans
                         (B.map KnotSupport.sliceExterior_cont)))).map
                        KnotSupport.coeffCM) ⟨e, he⟩ := by
            -- This is now an entirely planar calculation: choose 2 as the
            -- base value in the half plane, and take small circles about two
            -- of the roots of `u^3=1`. Their analytic continuations in
            -- `λ^3-3uλ+2=0` exchange different pairs of roots.
            -- The triangular root polynomial itself is now dealt with without any
            -- polynomial-roots continuity black box.  In `CubicCover` it is written
            -- `(u,z) ↦ (u,(3uz-z^3)/2)`; it is closed (uniform cubic estimate), has
            -- finite fibers, and its derivative is an explicit continuous linear
            -- equivalence off `u=z^2`.  Thus the inverse function theorem and the
            -- finite-fiber closed-map criterion give an honestly evenly covered
            -- neighborhood of every good value.  What remains here is transporting
            -- that cover through the incidence chart and the two global braid lifts.
            have chart_cover : IsCoveringMapOn KnotSupport.cubicMap
                KnotSupport.cubicGoodSet := KnotSupport.cubicMap_cover_on
            -- Restrict the triangular chart to good coefficients.  It is important
            -- here to prove an *actual* cover, not just local charts: the incidence
            -- type used for monodromy has as total space the marked roots and as base
            -- the subtype of good coefficients.  `rootChart` identifies it with the
            -- restricted preimage of `cubicMap`; composing its cover with this
            -- homeomorphism yields the fixed detector.
            have cov : IsCoveringMap KnotSupport.rootPr :=
              KnotSupport.root_cover
            -- At this point no gluing/local-chart assertion remains in the root
            -- computation.  It is one explicit braid in the v=1 half-plane for
            -- this three-sheeted cover.
            have braid :
                ∃ (u : KnotSupport.CubicSliceDomain)
                  (e : KnotSupport.CubicRoot),
                  ∃ he : KnotSupport.rootPr e =
                    KnotSupport.trefoilCoeffs (KnotSupport.sliceExterior u),
                  ∃ (A B : Path u u),
                    cov.monodromy
                      ((Path.Homotopic.Quotient.mk
                        (((B.map KnotSupport.sliceExterior_cont).trans
                           (A.map KnotSupport.sliceExterior_cont)))).map
                            KnotSupport.coeffCM) ⟨e, he⟩ ≠
                    cov.monodromy
                      ((Path.Homotopic.Quotient.mk
                        (((A.map KnotSupport.sliceExterior_cont).trans
                           (B.map KnotSupport.sliceExterior_cont)))).map
                            KnotSupport.coeffCM) ⟨e, he⟩ := by
              -- normalize the base value as well.  `z=2` is literally a root
              -- above `(5/3,1)`, so fibres in the last computation contain no
              -- choices of polynomial roots.
              refine ⟨KnotSupport.braidBase, KnotSupport.rootTwo,
                KnotSupport.rootTwo_over, ?_⟩
              exact KnotSupport.braid_witness
            rcases braid with ⟨u,e,he,A,B,h⟩
            exact ⟨cov,u,e,he,A,B,h⟩
          rcases cubic_monodromy with ⟨cov,u,e,he,A,B,hne⟩
          exact KnotSupport.trefoil_not_FGAbelian_of_slice_monodromy
            cov u e he A B hne
      exact ⟨KnotSupport.FGAbelian_circle_of_LP lower.1, lower.2⟩
    exact KnotSupport.no_homeomorph_of_FGAbelian
      fundamental_calculation.1 fundamental_calculation.2
  have no_flat :
      ¬ ∃ (F G :
          (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3))),
          (∀ x, G (F x) = x) ∧ (∀ x, F (G x) = x) ∧
          Continuous F ∧ Continuous G ∧
          Set.MapsTo F (Set.range KnotSupport.circle)
            (Set.range KnotSupport.trefoil) ∧
          Set.MapsTo G (Set.range KnotSupport.trefoil)
            (Set.range KnotSupport.circle) := by
    rintro ⟨F, G, il, ir, cF, cG, mF, mG⟩
    exact different_complements
      ⟨KnotSupport.complementHomeomorph F G
          (Set.range KnotSupport.circle)
          (Set.range KnotSupport.trefoil)
          il ir cF cG mF mG⟩

  intro iso
  rcases iso with ⟨Φ, σ, hlast⟩
  have hF : Continuous (Φ.H 1) := by
    have hc : Continuous (fun x :
        (EuclideanSpace ℝ (Fin 3)) =>
        ( (1 : ℝ), x)) := by fun_prop
    exact Φ.smooth.continuous.comp hc
  have hG : Continuous (Φ.Hinv 1) := by
    have hc : Continuous (fun x :
        (EuclideanSpace ℝ (Fin 3)) =>
        ( (1 : ℝ), x)) := by fun_prop
    exact Φ.smooth_inv.continuous.comp hc
  apply no_flat
  refine ⟨Φ.H 1, Φ.Hinv 1, Φ.inv_left 1, Φ.inv_right 1,
    hF, hG, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨t, rfl⟩
    refine ⟨σ.f t, ?_⟩
    simpa [U, T] using (hlast t).symm
  · intro y hy
    rcases hy with ⟨u, rfl⟩
    refine ⟨σ.finv u, ?_⟩
    have h := hlast (σ.finv u)
    have h' : Φ.H 1 (KnotSupport.circle (σ.finv u)) =
            KnotSupport.trefoil u := by
        simpa [U, T, σ.right_inv u] using h
    have hx := congrArg (Φ.Hinv 1) h'
    calc
      KnotSupport.circle (σ.finv u) =
          Φ.Hinv 1 (Φ.H 1 (KnotSupport.circle (σ.finv u))) :=
            (Φ.inv_left 1 (KnotSupport.circle (σ.finv u))).symm
      _ = Φ.Hinv 1 (KnotSupport.trefoil u) := hx
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
