import ChallengeDeps
import Submission.Helpers

namespace Submission

namespace SourceDefinitions
namespace LeanEval
namespace KnotTheory

/-!
# Smooth knots, links, ambient isotopy, and chirality

Minimal definitions to support the three knot-theory benchmark problems
(`Linking`, `NonIsotopicKnots`, `Chiral`). Mathlib has essentially no knot
theory, so we set up just enough infrastructure to state the questions
faithfully in terms of smooth maps `S¹ → ℝ³` and ambient isotopies of `ℝ³`.

A *knot* is a smooth, 2π-periodic, injective immersion `ℝ → ℝ³`. A
*two-component link* is a pair of knots with disjoint images. An *ambient
isotopy* is a smooth one-parameter family of diffeomorphisms of `ℝ³`
starting at the identity, presented here as a forward map and an inverse
map jointly smooth in `(t, x)`.

The parametrization is part of the data, so each knot or link component
comes with an orientation induced from the standard orientation on `S¹`.
Accordingly, isotopy is understood in the oriented sense: an ambient isotopy
must carry the parametrized components of the source to those of the target,
up to orientation-preserving reparametrization of the source circle. A knot
is *chiral* here in this same orientation-sensitive sense: it is not isotopic
to its mirror image (under reflection through the `xy`-plane).

These definitions trade some Mathlib idiomaticity for being self-contained
and easy to read; in particular, we do not go through `Diffeomorph` or
`ContMDiff` on a manifold structure for `ℝ³`, since `ContDiff ℝ ⊤` over the
ambient normed space says exactly what we need.
-/

/-- The ambient space `ℝ³`, as a Euclidean inner-product space. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- An oriented smooth knot in `ℝ³`: a 2π-periodic, smooth, injective immersion.
The orientation is the one induced by the parametrization. -/
structure Knot where
  /-- The parametrizing map. -/
  curve : ℝ → R3
  /-- The map is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) curve
  /-- The map has period `2π`. -/
  periodic : ∀ t, curve (t + 2 * Real.pi) = curve t
  /-- The map is injective on a fundamental period. -/
  injOn : Set.InjOn curve (Set.Ico 0 (2 * Real.pi))
  /-- The map is an immersion (its derivative is everywhere nonzero). -/
  immersion : ∀ t, deriv curve t ≠ 0

/-- An oriented two-component smooth link in `ℝ³`: a pair of oriented knots
with disjoint images. -/
structure TwoLink where
  /-- The first component. -/
  K : Knot
  /-- The second component. -/
  L : Knot
  /-- The two components have disjoint images in `ℝ³`. -/
  disjoint : Disjoint (Set.range K.curve) (Set.range L.curve)

/-- A smooth ambient isotopy of `ℝ³`: a one-parameter family `H t : ℝ³ → ℝ³`
of diffeomorphisms, jointly smooth in `(t, x)`, starting at the identity.
The inverse family `Hinv` is also jointly smooth. -/
structure AmbientIsotopy where
  /-- The forward family. -/
  H : ℝ → R3 → R3
  /-- The inverse family. -/
  Hinv : ℝ → R3 → R3
  /-- The forward family is jointly smooth in `(t, x)`. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H)
  /-- The inverse family is jointly smooth in `(t, x)`. -/
  smooth_inv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Hinv)
  /-- `Hinv t` is a left inverse of `H t`. -/
  inv_left : ∀ t x, Hinv t (H t x) = x
  /-- `Hinv t` is a right inverse of `H t`. -/
  inv_right : ∀ t x, H t (Hinv t x) = x
  /-- The isotopy starts at the identity. -/
  start : H 0 = id

structure CircleReparam where
  /-- A lift `ℝ → ℝ` of a circle self-map. -/
  f : ℝ → ℝ
  /-- A lifted inverse. -/
  finv : ℝ → ℝ
  /-- The lift is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  /-- The inverse lift is smooth. -/
  smooth_inv : ContDiff ℝ (⊤ : ℕ∞) finv
  /-- `finv` is a left inverse to `f`. -/
  left_inv : ∀ t, finv (f t) = t
  /-- `finv` is a right inverse to `f`. -/
  right_inv : ∀ t, f (finv t) = t
  /-- The lift descends to a map of `S¹ = ℝ / 2πℤ`. -/
  periodic : ∀ t, f (t + 2 * Real.pi) = f t + 2 * Real.pi
  /-- The inverse lift also descends to `S¹`. -/
  periodic_inv : ∀ t, finv (t + 2 * Real.pi) = finv t + 2 * Real.pi
  /-- The induced circle map preserves orientation. -/
  mono : StrictMono f

/-- Two oriented knots are ambient-isotopic if some ambient isotopy of `ℝ³`
carries the parametrized knot `K₁` to the parametrized knot `K₂`, up to an
orientation-preserving smooth reparametrization of the source circle. -/
def Knot.Isotopic (K₁ K₂ : Knot) : Prop :=
  ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam, ∀ t, Φ.H 1 (K₁.curve t) = K₂.curve (σ.f t)

/-- Two oriented two-component links are ambient-isotopic if a single ambient
isotopy carries each oriented component of the first link to the
corresponding oriented component of the second. -/
def TwoLink.Isotopic (L₁ L₂ : TwoLink) : Prop :=
  ∃ Φ : AmbientIsotopy, ∃ σ τ : CircleReparam,
    (∀ t, Φ.H 1 (L₁.K.curve t) = L₂.K.curve (σ.f t)) ∧
    (∀ t, Φ.H 1 (L₁.L.curve t) = L₂.L.curve (τ.f t))

/-- Reflection through the `xy`-plane in `ℝ³`: `(x, y, z) ↦ (x, y, -z)`. -/
def reflectZ (p : R3) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 => if i = 2 then -p.ofLp i else p.ofLp i)

/-- A knot is *chiral* if it is not ambient-isotopic, in the
orientation-sensitive sense used in this benchmark, to its mirror image (the
reflection of the image through the `xy`-plane). -/
def Knot.Chiral (K : Knot) : Prop :=
  ¬ ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
    ∀ t, Φ.H 1 (K.curve t) = reflectZ (K.curve (σ.f t))

end KnotTheory
end LeanEval
end SourceDefinitions

open LeanEval.KnotTheory
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

-- A concrete round circle.  These small analytic lemmas are useful when
-- working with concrete links: the convention about the half--open
-- interval is sometimes slightly inconvenient, so we record the elementary
-- injectivity argument here.
noncomputable def roundCurve (a : ℝ) (t : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 => ![Real.cos t, Real.sin t, a] i)

@[simp] lemma roundCurve_0 (a t : ℝ) : (roundCurve a t).ofLp (0 : Fin 3) = Real.cos t := by
  rfl
@[simp] lemma roundCurve_1 (a t : ℝ) : (roundCurve a t).ofLp (1 : Fin 3) = Real.sin t := by
  rfl
@[simp] lemma roundCurve_2 (a t : ℝ) : (roundCurve a t).ofLp (2 : Fin 3) = a := by
  rfl

lemma roundCurve_smooth (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (roundCurve a) := by
  -- `PiLp` has the same componentwise smoothness lemma as a finite product.
  apply (contDiff_piLp (p := (2 : ENNReal))).2
  intro i
  fin_cases i
  · simpa [roundCurve] using (Real.contDiff_cos : ContDiff ℝ (⊤ : ℕ∞) Real.cos)
  · simpa [roundCurve] using (Real.contDiff_sin : ContDiff ℝ (⊤ : ℕ∞) Real.sin)
  · simpa [roundCurve] using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => a))

@[simp] lemma roundCurve_periodic (a : ℝ) (t : ℝ) :
    roundCurve a (t + 2 * Real.pi) = roundCurve a t := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [roundCurve, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma roundCurve_immersion (a : ℝ) (t : ℝ) : deriv (roundCurve a) t ≠ 0 := by
  have hf : DifferentiableAt ℝ (roundCurve a) t :=
    (roundCurve_smooth a).differentiable (by simp) t
  intro hz
  -- If the vector derivative vanished, both planar coordinates would have
  -- zero derivative.  They are `-sin` and `cos`, which cannot do this
  -- simultaneously.
  have coord (i : Fin 3) :
      HasDerivAt (fun u : ℝ => (roundCurve a u).ofLp i)
        ((PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) i) (deriv (roundCurve a) t)) t := by
    have ho : HasFDerivAt
        (fun x : R3 => (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) i) x)
        (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) i) (roundCurve a t) :=
      (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) i).hasFDerivAt
    have h := ho.comp t hf.hasDerivAt.hasFDerivAt
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using h.hasDerivAt
  have h0 := (coord (0 : Fin 3)).deriv
  have h1 := (coord (1 : Fin 3)).deriv
  have h0' : - Real.sin t = 0 := by
    simpa [roundCurve, hz] using (h0.trans (by simp [hz] :
      ((PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) (0 : Fin 3))
        (deriv (roundCurve a) t)) = 0))
  have h1' : Real.cos t = 0 := by
    simpa [roundCurve, hz] using (h1.trans (by simp [hz] :
      ((PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) (1 : Fin 3))
        (deriv (roundCurve a) t)) = 0))
  have hs : Real.sin t = 0 := by linarith
  have sq := Real.sin_sq_add_cos_sq t
  rw [hs, h1'] at sq
  norm_num at sq

-- Simultaneous sine and cosine are injective on a half open period.
lemma sincos_inj_Ico {x y : ℝ}
    (hx0 : 0 ≤ x) (hxP : x < 2 * Real.pi)
    (hy0 : 0 ≤ y) (hyP : y < 2 * Real.pi)
    (hc : Real.cos x = Real.cos y) (hs : Real.sin x = Real.sin y) : x = y := by
  rcases (Real.cos_eq_cos_iff).1 hc with ⟨k, hk | hk⟩
  · have hk' : y = (k : ℝ) * (2 * Real.pi) + x := by
      -- the library writes the period as `2*k*pi`.
      nlinarith
    have hp : 0 < Real.pi := Real.pi_pos
    have hlt : (k : ℝ) < 1 := by nlinarith
    have hlo : -(1 : ℝ) < (k : ℝ) := by nlinarith
    have hltz : k < (1 : ℤ) := (Int.cast_lt (R := ℝ)).1 (by exact_mod_cast hlt)
    have hloz : (-1 : ℤ) < k := (Int.cast_lt (R := ℝ)).1 (by exact_mod_cast hlo)
    have hz : k = 0 := by omega
    simp [hk', hz]
  · have hk' : y = (k : ℝ) * (2 * Real.pi) - x := by
      nlinarith
    have hsyneg : Real.sin y = - Real.sin x := by
      simpa [hk'] using (Real.sin_int_mul_two_pi_sub x k)
    have hsx : Real.sin x = 0 := by linarith
    obtain ⟨n, hn⟩ := (Real.sin_eq_zero_iff).1 hsx
    -- Both `x` and `y` are integral multiples of `π`; the multiplier of
    -- `y` is `2*k-n`.
    have hxrep : x = (n : ℝ) * Real.pi := hn.symm
    let m : ℤ := 2 * k - n
    have hyrep : y = (m : ℝ) * Real.pi := by
      dsimp [m]
      rw [hk', hxrep]
      push_cast
      ring
    have hp : 0 < Real.pi := Real.pi_pos
    have hn0r : (0 : ℝ) ≤ (n : ℝ) := by nlinarith [hx0]
    have hnltr : (n : ℝ) < 2 := by nlinarith [hxP]
    have hm0r : (0 : ℝ) ≤ (m : ℝ) := by nlinarith [hy0]
    have hmltr : (m : ℝ) < 2 := by nlinarith [hyP]
    have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast hn0r
    have hnlt : n < (2 : ℤ) := by exact_mod_cast hnltr
    have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast hm0r
    have hmlt : m < (2 : ℤ) := by exact_mod_cast hmltr
    have hmn : m = n := by
      dsimp [m] at hm0 hmlt ⊢
      omega
    rw [hxrep, hyrep, hmn]

lemma roundCurve_injOn (a : ℝ) : Set.InjOn (roundCurve a) (Set.Ico 0 (2 * Real.pi)) := by
  intro x hx y hy hxy
  apply sincos_inj_Ico hx.1 hx.2 hy.1 hy.2
  · simpa using congrArg (fun v : R3 => v.ofLp (0 : Fin 3)) hxy
  · simpa using congrArg (fun v : R3 => v.ofLp (1 : Fin 3)) hxy

/-- The unit circle parallel to the `xy` plane, at height `a`. -/
noncomputable def roundKnot (a : ℝ) : Knot where
  curve := roundCurve a
  smooth := roundCurve_smooth a
  periodic := roundCurve_periodic a
  injOn := roundCurve_injOn a
  immersion := roundCurve_immersion a

@[simp] lemma roundKnot_curve (a t : ℝ) : (roundKnot a).curve t = roundCurve a t := rfl

lemma roundCurve_disjoint {a b : ℝ} (hab : a ≠ b) :
    Disjoint (Set.range (roundKnot a).curve) (Set.range (roundKnot b).curve) := by
  rw [Set.disjoint_left]
  intro v hv hw
  rcases hv with ⟨s, rfl⟩
  rcases hw with ⟨t, h⟩
  have h' := congrArg (fun w : R3 => w.ofLp (2 : Fin 3)) h
  exact hab (by simpa using h'.symm)

noncomputable def parallelLink (a b : ℝ) (h : a ≠ b) : TwoLink where
  K := roundKnot a
  L := roundKnot b
  disjoint := roundCurve_disjoint h

/-- A meridian circle for the round one.  It lies in the plane `y=0`,
    centered at `(1,0,0)`. -/
noncomputable def meridCurve (t : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 => ![1 + Real.cos t, 0, Real.sin t] i)

@[simp] lemma meridCurve_0 (t : ℝ) : (meridCurve t).ofLp (0 : Fin 3) = 1 + Real.cos t := by rfl
@[simp] lemma meridCurve_1 (t : ℝ) : (meridCurve t).ofLp (1 : Fin 3) = 0 := by rfl
@[simp] lemma meridCurve_2 (t : ℝ) : (meridCurve t).ofLp (2 : Fin 3) = Real.sin t := by rfl

lemma meridCurve_smooth : ContDiff ℝ (⊤ : ℕ∞) meridCurve := by
  apply (contDiff_piLp (p := (2 : ENNReal))).2
  intro i
  fin_cases i
  · simpa [meridCurve] using
      ((contDiff_const.add Real.contDiff_cos) :
        ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => 1 + Real.cos t))
  · simpa [meridCurve] using
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℝ)))
  · simpa [meridCurve] using
      (Real.contDiff_sin : ContDiff ℝ (⊤ : ℕ∞) Real.sin)

@[simp] lemma meridCurve_periodic (t : ℝ) : meridCurve (t + 2 * Real.pi) = meridCurve t := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [meridCurve, Real.sin_add_two_pi, Real.cos_add_two_pi]

lemma meridCurve_injOn : Set.InjOn meridCurve (Set.Ico 0 (2 * Real.pi)) := by
  intro x hx y hy hxy
  apply sincos_inj_Ico hx.1 hx.2 hy.1 hy.2
  · have h := congrArg (fun v : R3 => v.ofLp (0 : Fin 3)) hxy
    simpa using (add_left_cancel h)
  · simpa using congrArg (fun v : R3 => v.ofLp (2 : Fin 3)) hxy

lemma meridCurve_immersion (t : ℝ) : deriv meridCurve t ≠ 0 := by
  have hf : DifferentiableAt ℝ meridCurve t :=
    meridCurve_smooth.differentiable (by simp) t
  intro hz
  have coord (i : Fin 3) :
      HasDerivAt (fun u : ℝ => (meridCurve u).ofLp i)
        ((PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) i) (deriv meridCurve t)) t := by
    have ho : HasFDerivAt
        (fun x : R3 => (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) i) x)
        (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) i) (meridCurve t) :=
      (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) i).hasFDerivAt
    have h := ho.comp t hf.hasDerivAt.hasFDerivAt
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using h.hasDerivAt
  have h0 := (coord (0 : Fin 3)).deriv
  have h2 := (coord (2 : Fin 3)).deriv
  have h0' : - Real.sin t = 0 := by
    convert (h0.trans (by simp [hz] :
      ((PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) (0 : Fin 3))
        (deriv meridCurve t)) = 0)) using 1
    -- derivative of `1 + cos`
    simp [meridCurve]
  have h2' : Real.cos t = 0 := by
    simpa [meridCurve, hz] using (h2.trans (by simp [hz] :
      ((PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 3 => ℝ) (2 : Fin 3))
        (deriv meridCurve t)) = 0))
  have hs : Real.sin t = 0 := by linarith
  have sq := Real.sin_sq_add_cos_sq t
  rw [hs, h2'] at sq
  norm_num at sq

noncomputable def meridKnot : Knot where
  curve := meridCurve
  smooth := meridCurve_smooth
  periodic := meridCurve_periodic
  injOn := meridCurve_injOn
  immersion := meridCurve_immersion

lemma hopf_disjoint :
    Disjoint (Set.range (roundKnot 0).curve) (Set.range meridKnot.curve) := by
  rw [Set.disjoint_left]
  intro v hv hw
  rcases hv with ⟨s, rfl⟩
  rcases hw with ⟨t, hEq⟩
  have hx := congrArg (fun w : R3 => w.ofLp (0 : Fin 3)) hEq
  have hy := congrArg (fun w : R3 => w.ofLp (1 : Fin 3)) hEq
  have hz := congrArg (fun w : R3 => w.ofLp (2 : Fin 3)) hEq
  change 1 + Real.cos t = Real.cos s at hx
  change (0 : ℝ) = Real.sin s at hy
  change Real.sin t = (0 : ℝ) at hz
  have hss := Real.sin_sq_add_cos_sq s
  have htt := Real.sin_sq_add_cos_sq t
  rw [← hy] at hss
  rw [hz] at htt
  norm_num at hss htt
  rcases hss with hss | hss <;> rcases htt with htt | htt <;> nlinarith

noncomputable def hopfLink : TwoLink where
  K := roundKnot 0
  L := meridKnot
  disjoint := hopf_disjoint
noncomputable def unitParam (t : ℝ) : ℂ := (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I
lemma unitParam_cont : Continuous unitParam := by
  unfold unitParam
  fun_prop
@[simp] lemma unitParam_periodic (t : ℝ) : unitParam (t + 2 * Real.pi) = unitParam t := by
  simp [unitParam, Real.sin_add_two_pi, Real.cos_add_two_pi]

/-- One elementary bit of the usual linking argument is just the familiar
fact that the meridian has degree one.  Using the covering `ℝ → Circle`
lets us state it without singular integrals. The domain of a filling can be
all of `ℂ`: restricting it to the unit circle already gives the
contradiction. -/
lemma no_circle_filling (τ : CircleReparam) :
    ¬ ∃ g : ℂ → Circle, Continuous g ∧
        ∀ t : ℝ, g (unitParam t) = Circle.exp (τ.f t) := by
  rintro ⟨g, hg, hbd⟩
  let gc : C(ℂ, Circle) := ⟨g, hg⟩
  have he : Circle.exp ((g 0 : ℂ).arg) = gc (0 : ℂ) := by
    simpa [gc] using Circle.exp_arg (g 0)
  obtain ⟨G, hG0, hGlift⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      gc (0 : ℂ) ((g 0 : ℂ).arg) he |>.exists
  -- Express the discrepancy between a lift on the boundary and the
  -- prescribed argument.
  let d : ℝ → ℝ := fun t => (G (unitParam t) - τ.f t) / (2 * Real.pi)
  have hdc : Continuous d := by
    dsimp [d]
    have h1 : Continuous (fun t : ℝ => G (unitParam t)) :=
      G.continuous.comp unitParam_cont
    have h2 : Continuous τ.f := τ.smooth.continuous
    exact h1.sub h2 |>.div_const _
  have hInt (t : ℝ) : ∃ m : ℤ, d t = (m : ℝ) := by
    have ee : Circle.exp (G (unitParam t)) = Circle.exp (τ.f t) := by
      have e1 : Circle.exp (G (unitParam t)) = gc (unitParam t) := by
        have q := congrFun hGlift (unitParam t)
        exact q
      exact e1.trans (hbd t)
    obtain ⟨m, hm⟩ := (Circle.exp_eq_exp).1 ee
    refine ⟨m, ?_⟩
    dsimp [d]
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    apply (div_eq_iff hp).2
    linarith
  have hper : d (2 * Real.pi) = d 0 - 1 := by
    dsimp [d]
    have hU : unitParam (2 * Real.pi) = unitParam 0 := by
      convert unitParam_periodic 0 using 1 <;> ring
    rw [hU]
    have ht := τ.periodic 0
    -- `0 + ...` has the same slightly unnormalised period in the structure.
    have ht' : τ.f (2 * Real.pi) = τ.f 0 + 2 * Real.pi := by
      convert ht using 1 <;> ring
    rw [ht']
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  obtain ⟨m0, hm0⟩ := hInt 0
  have hp0 : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt (by positivity)
  have middle_mem : (m0 : ℝ) - (1/2 : ℝ) ∈ Set.Icc (d (2 * Real.pi)) (d 0) := by
    rw [hper, hm0]
    constructor <;> norm_num <;> linarith
  obtain ⟨t, htI, htval⟩ :=
    (intermediate_value_Icc' hp0 hdc.continuousOn) middle_mem
  obtain ⟨m, hm⟩ := hInt t
  rw [hm] at htval
  have contra : (m : ℝ) = (m0 : ℝ) - (1/2 : ℝ) := htval
  have contra' : (2:ℝ) * (m : ℝ) = 2 * (m0 : ℝ) - 1 := by linarith
  have conZ : (2:ℤ) * m = 2 * m0 - 1 := by exact_mod_cast contra'
  omega
noncomputable def meridVal (p : R3) : ℂ :=
  ((Real.sqrt ((p.ofLp (0 : Fin 3))^2 + (p.ofLp (1 : Fin 3))^2) - 1 : ℝ) : ℂ) +
    (p.ofLp (2 : Fin 3) : ℂ) * Complex.I

lemma meridVal_cont : Continuous meridVal := by
  unfold meridVal
  fun_prop

noncomputable def valCircle (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), (mem_sphere_zero_iff_norm).2 (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hz))⟩
lemma coe_valCircle (z : ℂ) (hz : z ≠ 0) :
  (valCircle z hz : ℂ) = z / (‖z‖ : ℂ) := rfl
lemma meridVal_zero_on_curve (p : R3) (hp : meridVal p = 0) :
    p ∈ Set.range (roundKnot 0).curve := by
  let x : ℝ := p.ofLp (0 : Fin 3)
  let y : ℝ := p.ofLp (1 : Fin 3)
  let z : ℝ := p.ofLp (2 : Fin 3)
  have hr : Real.sqrt (x^2 + y^2) = 1 := by
    have h := congrArg Complex.re hp
    simp [meridVal] at h
    dsimp [x, y]
    linarith
  have hz : z = 0 := by
    have h := congrArg Complex.im hp
    simp [meridVal] at h
    dsimp [z]
    linarith
  have hsnon : 0 ≤ x^2 + y^2 := by positivity
  have hxy : x^2 + y^2 = 1 := by nlinarith [Real.sq_sqrt hsnon]
  let w : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have wnorm : ‖w‖ = (1:ℝ) := by
    rw [Complex.norm_def]
    have : Complex.normSq w = x^2 + y^2 := by
      simp [Complex.normSq_apply, w]
      ring
    rw [this, hxy]
    norm_num
  let ww : Circle := ⟨w, (mem_sphere_zero_iff_norm).2 wnorm⟩
  obtain ⟨t, ht⟩ := Circle.exp_surjective ww
  have ht' : Complex.exp ((t : ℂ) * Complex.I) = w := by
    simpa [ww] using congrArg (fun u : Circle => (u : ℂ)) ht
  rw [Complex.exp_mul_I] at ht'
  have hcos : Real.cos t = x := by
    have h := congrArg Complex.re ht'
    norm_num [w] at h
    exact h
  have hsin : Real.sin t = y := by
    have h := congrArg Complex.im ht'
    norm_num [w] at h
    exact h
  refine ⟨t, ?_⟩
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hcos.trans (by rfl)
  · exact hsin.trans (by rfl)
  · simpa [z] using hz.symm
lemma meridVal_meridCurve (t : ℝ) :
    meridVal (meridCurve t) = unitParam t := by
  dsimp [meridVal, meridCurve, unitParam]
  have hcoslo : 0 ≤ 1 + Real.cos t := by
    have := Real.neg_one_le_cos t
    linarith
  have hs : Real.sqrt ((1 + Real.cos t)^2 + (0:ℝ)^2) =
        1 + Real.cos t := by
    norm_num
    rw [Real.sqrt_sq hcoslo]
  rw [hs]
  norm_num
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem exists_nonisotopic_link : ∃ L₁ L₂ : TwoLink, ¬ L₁.Isotopic L₂ :=
/-ResultProofBegin-/by
  classical
  let hu : (0 : ℝ) ≠ 2 := by norm_num
  refine ⟨parallelLink 0 2 hu, hopfLink, ?_⟩
  rintro ⟨Φ, σ, τ, hK, hL⟩
  -- The parallel circle bounds its horizontal disk in the complement of
  -- the first component.  Pushing this disk through `Φ.H 1` and applying
  -- the meridional angular coordinate of the complement of the round
  -- circle would fill the degree-one meridian of `hopfLink`.
  apply no_circle_filling τ
  -- Fill the parallel component by its horizontal disk (indeed the whole
  -- plane at height two).  No point of this plane is on the other
  -- component; after an ambient diffeomorphism this remains so.
  let D : ℂ → R3 := fun z =>
    WithLp.toLp 2 (fun i : Fin 3 => ![z.re, z.im, (2 : ℝ)] i)
  have hD0 (z : ℂ) : (D z).ofLp (0 : Fin 3) = z.re := by rfl
  have hD1 (z : ℂ) : (D z).ofLp (1 : Fin 3) = z.im := by rfl
  have hD2 (z : ℂ) : (D z).ofLp (2 : Fin 3) = (2 : ℝ) := by rfl
  have hDc : Continuous D := by
    dsimp [D]
    fun_prop
  have hDb (t : ℝ) : D (unitParam t) = roundCurve 2 t := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [D, roundCurve, unitParam,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_im]
  -- Unpack the two component equations of the assumed isotopy.
  have hK' (t : ℝ) :
      Φ.H 1 (roundCurve 0 t) = roundCurve 0 (σ.f t) := by
    simpa [parallelLink, hopfLink, roundKnot_curve] using hK t
  have hL' (t : ℝ) :
      Φ.H 1 (roundCurve 2 t) = meridCurve (τ.f t) := by
    simpa [parallelLink, hopfLink, roundKnot_curve, meridKnot] using hL t
  have hPc : Continuous (fun x : R3 => Φ.H 1 x) := by
    have hs := Φ.smooth.continuous
    have hp : Continuous (fun x : R3 => ((1 : ℝ), x)) :=
      continuous_const.prodMk continuous_id
    convert hs.comp hp using 1 <;> rfl
  let v : ℂ → ℂ := fun z => meridVal (Φ.H 1 (D z))
  have hvc : Continuous v := by
    dsimp [v]
    exact meridVal_cont.comp (hPc.comp hDc)
  have hv0 (z : ℂ) : v z ≠ 0 := by
    dsimp [v]
    intro hzero
    obtain ⟨u, hu'⟩ := meridVal_zero_on_curve (Φ.H 1 (D z)) hzero
    have hu : roundCurve 0 u = Φ.H 1 (D z) := by
      simpa [roundKnot_curve] using hu'
    have hpreim : Φ.H 1 (roundCurve 0 (σ.finv u)) =
          roundCurve 0 u := by
      simpa [σ.right_inv] using (hK' (σ.finv u))
    have heq : Φ.H 1 (roundCurve 0 (σ.finv u)) = Φ.H 1 (D z) :=
      hpreim.trans hu
    have heq0 := congrArg (fun w : R3 => Φ.Hinv 1 w) heq
    have heq1 : roundCurve 0 (σ.finv u) = D z := by
      simpa [Φ.inv_left] using heq0
    have hz' := congrArg (fun w : R3 => w.ofLp (2 : Fin 3)) heq1
    have hz'' : (0 : ℝ) = 2 := by
      simpa [roundCurve, hD2] using hz'
    norm_num at hz''
  refine ⟨(fun z : ℂ => valCircle (v z) (hv0 z)), ?_, ?_⟩
  · -- Normalizing a nowhere zero continuous complex function is continuous.
    have hnormc : Continuous (fun z : ℂ => (‖v z‖ : ℂ)) :=
      Complex.continuous_ofReal.comp hvc.norm
    have hnorm0 (z : ℂ) : (‖v z‖ : ℂ) ≠ 0 :=
      (Complex.ofReal_ne_zero).2 ((norm_ne_zero_iff).2 (hv0 z))
    have hco : Continuous (fun z : ℂ => v z / (‖v z‖ : ℂ)) := by
      change Continuous (v / fun z : ℂ => (‖v z‖ : ℂ))
      exact hvc.div hnormc hnorm0
    have hcod : Continuous
        (fun z : ℂ => ((valCircle (v z) (hv0 z) : Circle) : ℂ)) := by
      simpa [coe_valCircle] using hco
    exact
      (continuous_induced_rng
        (f := fun w : Circle => (w : ℂ))
        (g := fun z : ℂ => valCircle (v z) (hv0 z))).2
        (by simpa [Function.comp_def] using hcod)
  · intro t
    apply Circle.ext
    have hvb : v (unitParam t) = unitParam (τ.f t) := by
      dsimp [v]
      rw [hDb, hL', meridVal_meridCurve]
    change v (unitParam t) / (‖v (unitParam t)‖ : ℂ) =
      (↑(Circle.exp (τ.f t)) : ℂ)
    have hunit (s : ℝ) : ‖unitParam s‖ = (1 : ℝ) := by
      simpa [unitParam, Complex.ofReal_cos, Complex.ofReal_sin] using
        (Complex.norm_cos_add_sin_mul_I s)
    rw [hvb, hunit]
    simp
    simpa [unitParam] using (Complex.exp_ofReal_mul_I (τ.f t)).symm/-ResultProofEnd-/
/-ResultEnd-/

end Submission
