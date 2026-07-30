import Mathlib

namespace Submission.Winding

open Function Set

noncomputable section

/-- One period of the complex exponential. -/
private def expPeriod : ℂ := 2 * (Real.pi : ℂ) * Complex.I

private theorem expPeriod_ne_zero : expPeriod ≠ 0 := by
  simp [expPeriod, Real.pi_ne_zero]

/-- A lift of a loop through the complex exponential, together with its endpoint displacement. -/
def HasWinding (g : C(Circle, ℂ)) (n : ℤ) : Prop :=
  ∃ L : C(ℝ, ℂ),
    (∀ t, Complex.exp (L t) = g (Circle.exp t)) ∧
      L Real.pi = L (-Real.pi) + (n : ℂ) * expPeriod

theorem exists_hasWinding (g : C(Circle, ℂ)) (hg : ∀ z, g z ≠ 0) :
    ∃ n : ℤ, HasWinding g n := by
  let f : C(ℝ, ℂ) := g.comp Circle.exp
  have hf0 : f 0 ≠ 0 := hg _
  obtain ⟨L, hL, _huniq⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
      (a₀ := (0 : ℝ)) (e₀ := Complex.log (f 0)) (Complex.exp_log hf0)
      (fun t ↦ by
        change f t ≠ 0
        simpa [f] using hg (Circle.exp t))
  have hlift (t : ℝ) : Complex.exp (L t) = g (Circle.exp t) := by
    simpa only [f, ContinuousMap.coe_comp, ContinuousMap.coe_mk, Function.comp_apply]
      using congrFun hL.2 t
  have hcircle : Circle.exp Real.pi = Circle.exp (-Real.pi) := by
    apply Circle.exp_eq_exp.mpr
    refine ⟨1, by norm_num; ring⟩
  have hexp : Complex.exp (L Real.pi) = Complex.exp (L (-Real.pi)) := by
    rw [hlift, hlift, hcircle]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  exact ⟨n, L, hlift, by simpa only [expPeriod] using hn⟩

private theorem exp_int_mul_period (n : ℤ) :
    Complex.exp ((n : ℂ) * expPeriod) = 1 := by
  rw [Complex.exp_int_mul]
  simp [expPeriod, Complex.exp_mul_I]

theorem hasWinding_unique {g : C(Circle, ℂ)} {n m : ℤ}
    (hg : ∀ z, g z ≠ 0) (hn : HasWinding g n) (hm : HasWinding g m) : n = m := by
  obtain ⟨L, hLlift, hLend⟩ := hn
  obtain ⟨K, hKlift, hKend⟩ := hm
  have hexp0 : Complex.exp (L 0) = Complex.exp (K 0) := by
    rw [hLlift, hKlift]
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp0
  let K' : C(ℝ, ℂ) :=
    ⟨fun t ↦ K t + (k : ℂ) * expPeriod, K.continuous.add continuous_const⟩
  have hK'lift (t : ℝ) : Complex.exp (K' t) = g (Circle.exp t) := by
    rw [show K' t = K t + (k : ℂ) * expPeriod by rfl, Complex.exp_add,
      exp_int_mul_period, mul_one, hKlift]
  let f : C(ℝ, ℂ) := g.comp Circle.exp
  have he0 : Complex.exp (L 0) = f 0 := by simpa [f] using hLlift 0
  obtain ⟨_F, _hF, huniq⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
      (a₀ := (0 : ℝ)) (e₀ := L 0) he0
      (fun t ↦ by
        change f t ≠ 0
        simpa [f] using hg (Circle.exp t))
  have hLK : L = K' := huniq L ⟨rfl, by
    funext t
    simpa [f] using hLlift t⟩ |>.trans <| (huniq K' ⟨by
      change K 0 + (k : ℂ) * expPeriod = L 0
      simpa only [expPeriod] using hk.symm, by
      funext t
      simpa [f] using hK'lift t⟩).symm
  have hdiff : L Real.pi - L (-Real.pi) = K Real.pi - K (-Real.pi) := by
    have := congrArg (fun Q : C(ℝ, ℂ) ↦ Q Real.pi - Q (-Real.pi)) hLK
    simpa only [K', ContinuousMap.coe_mk, add_sub_add_right_eq_sub] using this
  rw [hLend, hKend] at hdiff
  simp only [add_sub_cancel_left] at hdiff
  have hcast : (n : ℂ) = (m : ℂ) :=
    mul_right_cancel₀ expPeriod_ne_zero hdiff
  exact_mod_cast hcast

/-- The winding number of a nonvanishing continuous map on the circle. -/
def winding (g : C(Circle, ℂ)) (hg : ∀ z, g z ≠ 0) : ℤ :=
  Classical.choose (exists_hasWinding g hg)

theorem winding_spec (g : C(Circle, ℂ)) (hg : ∀ z, g z ≠ 0) :
    HasWinding g (winding g hg) :=
  Classical.choose_spec (exists_hasWinding g hg)

theorem winding_eq_of_hasWinding {g : C(Circle, ℂ)} (hg : ∀ z, g z ≠ 0)
    {n : ℤ} (hn : HasWinding g n) : winding g hg = n :=
  hasWinding_unique hg (winding_spec g hg) hn

theorem winding_congr {g h : C(Circle, ℂ)} (hgh : g = h)
    (hg : ∀ z, g z ≠ 0) (hh : ∀ z, h z ≠ 0) :
    winding g hg = winding h hh := by
  subst h
  rfl

/-- Two logarithmic lifts on a simply connected, locally path-connected
space which agree at one point agree everywhere. -/
theorem continuousMap_eq_of_exp_eq {A : Type*} [TopologicalSpace A]
    [SimplyConnectedSpace A] [LocPathConnectedSpace A]
    (f g : C(A, ℂ)) (a₀ : A) (h₀ : f a₀ = g a₀)
    (hexp : ∀ a, Complex.exp (f a) = Complex.exp (g a)) : f = g := by
  let target : C(A, {z : ℂ // z ≠ 0}) :=
    { toFun := fun a => ⟨Complex.exp (f a), Complex.exp_ne_zero _⟩
      continuous_toFun := Continuous.subtype_mk
        (Complex.continuous_exp.comp f.continuous) _ }
  obtain ⟨F, hF, huniq⟩ :=
    Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
      target a₀ (f a₀) (by rfl)
  have hf : f a₀ = f a₀ ∧
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ :
        {z : ℂ // z ≠ 0})) ∘ f = target := by
    refine ⟨rfl, ?_⟩
    ext a
    rfl
  have hg : g a₀ = f a₀ ∧
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ :
        {z : ℂ // z ≠ 0})) ∘ g = target := by
    refine ⟨h₀.symm, ?_⟩
    funext a
    apply Subtype.ext
    exact (hexp a).symm
  exact (huniq f hf).trans (huniq g hg).symm

/-- The endpoint displacement of a logarithmic lift is the same on every
interval of length `2π`. -/
theorem HasWinding.add_two_pi {g : C(Circle, ℂ)} {n : ℤ}
    (h : HasWinding g n) (t : ℝ) :
    h.choose (t + 2 * Real.pi) = h.choose t + (n : ℂ) * expPeriod := by
  let L : C(ℝ, ℂ) := h.choose
  have hLlift : ∀ u, Complex.exp (L u) = g (Circle.exp u) := h.choose_spec.1
  have hLend : L Real.pi = L (-Real.pi) + (n : ℂ) * expPeriod :=
    h.choose_spec.2
  let A : C(ℝ, ℂ) :=
    ⟨fun u => L (u + 2 * Real.pi), L.continuous.comp
      (continuous_id.add continuous_const)⟩
  let B : C(ℝ, ℂ) :=
    L + ContinuousMap.const ℝ ((n : ℂ) * expPeriod)
  have hbase : A (-Real.pi) = B (-Real.pi) := by
    change L (-Real.pi + 2 * Real.pi) = L (-Real.pi) + (n : ℂ) * expPeriod
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    exact hLend
  have hexp (u : ℝ) : Complex.exp (A u) = Complex.exp (B u) := by
    change Complex.exp (L (u + 2 * Real.pi)) =
      Complex.exp (L u + (n : ℂ) * expPeriod)
    rw [Complex.exp_add, exp_int_mul_period, mul_one, hLlift, hLlift]
    congr 1
    apply Circle.exp_eq_exp.mpr
    refine ⟨1, by norm_num⟩
  have hAB := continuousMap_eq_of_exp_eq A B (-Real.pi) hbase hexp
  have ht := congrArg (fun Q : C(ℝ, ℂ) => Q t) hAB
  simpa only [A, B, ContinuousMap.coe_mk, ContinuousMap.add_apply,
    ContinuousMap.const_apply] using ht

/-- Precomposition by an orientation-preserving rotation of the circle. -/
def rotateMap (g : C(Circle, ℂ)) (c : ℝ) : C(Circle, ℂ) :=
  g.comp
    { toFun := fun z => Circle.exp c * z
      continuous_toFun := continuous_const.mul continuous_id }

@[simp]
theorem rotateMap_exp (g : C(Circle, ℂ)) (c t : ℝ) :
    rotateMap g c (Circle.exp t) = g (Circle.exp (t + c)) := by
  change g (Circle.exp c * Circle.exp t) = _
  congr 1
  apply Subtype.ext
  simp only [Circle.coe_mul, Circle.coe_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem winding_rotateMap (g : C(Circle, ℂ)) (hg : ∀ z, g z ≠ 0) (c : ℝ) :
    winding (rotateMap g c) (fun _ => hg _) = winding g hg := by
  let n := winding g hg
  let hspec := winding_spec g hg
  let L : C(ℝ, ℂ) := hspec.choose
  have hLlift : ∀ t, Complex.exp (L t) = g (Circle.exp t) :=
    hspec.choose_spec.1
  let K : C(ℝ, ℂ) :=
    ⟨fun t => L (t + c), L.continuous.comp (continuous_id.add continuous_const)⟩
  apply winding_eq_of_hasWinding
  refine ⟨K, ?_, ?_⟩
  · intro t
    change Complex.exp (L (t + c)) = rotateMap g c (Circle.exp t)
    rw [hLlift, rotateMap_exp]
  · change L (Real.pi + c) =
      L (-Real.pi + c) + (n : ℂ) * expPeriod
    have hshift := HasWinding.add_two_pi hspec (-Real.pi + c)
    rw [show -Real.pi + c + 2 * Real.pi = Real.pi + c by ring] at hshift
    simpa only [n] using hshift

/-- An explicit logarithm on the standard angular interval computes winding. -/
theorem winding_eq_of_intervalLog (g : C(Circle, ℂ)) (hg : ∀ z, g z ≠ 0)
    (n : ℤ) (L : C(Set.Icc (-Real.pi) Real.pi, ℂ))
    (hL : ∀ t, Complex.exp (L t) = g (Circle.exp (t : ℝ)))
    (hend : L ⟨Real.pi, by linarith [Real.pi_pos], le_rfl⟩ =
      L ⟨-Real.pi, le_rfl, by linarith [Real.pi_pos]⟩ +
        (n : ℂ) * expPeriod) :
    winding g hg = n := by
  let J : Set ℝ := Set.Icc (-Real.pi) Real.pi
  letI : ContractibleSpace J :=
    (convex_Icc (-Real.pi) Real.pi).contractibleSpace
      ⟨0, by constructor <;> linarith [Real.pi_pos]⟩
  letI : LocPathConnectedSpace J :=
    (convex_Icc (-Real.pi) Real.pi).locPathConnectedSpace
  obtain ⟨K, hKlift, hKend⟩ := winding_spec g hg
  let d₀ : J := ⟨-Real.pi, le_rfl, by linarith [Real.pi_pos]⟩
  let d₁ : J := ⟨Real.pi, by linarith [Real.pi_pos], le_rfl⟩
  have hexp0 : Complex.exp (L d₀) = Complex.exp (K (-Real.pi)) := by
    simpa only [d₀] using (hL d₀).trans (hKlift (-Real.pi)).symm
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp0
  let K' : C(J, ℂ) :=
    { toFun := fun t => K (t : ℝ) + (k : ℂ) * expPeriod
      continuous_toFun :=
        (K.continuous.comp continuous_subtype_val).add continuous_const }
  have hbase : L d₀ = K' d₀ := by
    change L d₀ = K (-Real.pi) + (k : ℂ) * expPeriod
    simpa only [expPeriod] using hk
  have hexp (t : J) : Complex.exp (L t) = Complex.exp (K' t) := by
    rw [hL, show K' t = K (t : ℝ) + (k : ℂ) * expPeriod by rfl,
      Complex.exp_add, exp_int_mul_period, mul_one, hKlift]
  have hmaps := continuousMap_eq_of_exp_eq L K' d₀ hbase hexp
  have hdiff : L d₁ - L d₀ = K Real.pi - K (-Real.pi) := by
    have h₁ := congrArg (fun Q : C(J, ℂ) => Q d₁) hmaps
    have h₀ := congrArg (fun Q : C(J, ℂ) => Q d₀) hmaps
    rw [h₁, h₀]
    simp only [K', d₁, d₀, ContinuousMap.coe_mk, add_sub_add_right_eq_sub]
  have hend' : L d₁ = L d₀ + (n : ℂ) * expPeriod := by
    simpa only [d₁, d₀] using hend
  rw [hend', hKend] at hdiff
  simp only [add_sub_cancel_left] at hdiff
  have hcast : (n : ℂ) = (winding g hg : ℂ) :=
    mul_right_cancel₀ expPeriod_ne_zero hdiff
  exact_mod_cast hcast.symm

/-- A continuous logarithm of a circle-valued nonzero map. -/
def HasLog (g : C(Circle, ℂ)) : Prop :=
  ∃ l : C(Circle, ℂ), ∀ z, Complex.exp (l z) = g z

private abbrev AngleInterval := Set.Icc (-Real.pi) Real.pi

private def angleIntervalExp : C(AngleInterval, Circle) :=
  ⟨fun t ↦ Circle.exp t, Circle.exp.continuous.comp continuous_subtype_val⟩

private theorem angleIntervalExp_surjective : Function.Surjective angleIntervalExp := by
  intro z
  refine ⟨⟨Complex.arg (z : ℂ), (Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩, ?_⟩
  exact Circle.exp_arg z

private theorem angleIntervalExp_isQuotientMap :
    Topology.IsQuotientMap angleIntervalExp :=
  IsQuotientMap.of_surjective_continuous angleIntervalExp_surjective
    angleIntervalExp.continuous

/-- Continuity of a function on the circle can be checked after composition
with the standard real exponential parametrization. -/
theorem continuous_of_comp_circleExp {X : Type*} [TopologicalSpace X]
    {f : Circle → X} (hf : Continuous (f ∘ Circle.exp)) : Continuous f := by
  apply angleIntervalExp_isQuotientMap.continuous_iff.mpr
  change Continuous (fun t : AngleInterval => f (Circle.exp (t : ℝ)))
  exact hf.comp continuous_subtype_val

private theorem lift_descends_of_endpoints_eq (L : C(ℝ, ℂ))
    (hend : L Real.pi = L (-Real.pi)) :
    ∃ l : C(Circle, ℂ), ∀ z, l z = L (Complex.arg (z : ℂ)) := by
  let lfun : Circle → ℂ := fun z ↦ L (Complex.arg (z : ℂ))
  have hl_exp (t : AngleInterval) : lfun (angleIntervalExp t) = L t := by
    by_cases ht : (t : ℝ) = -Real.pi
    · have hexp : Circle.exp (t : ℝ) = Circle.exp Real.pi := by
        rw [ht]
        apply Circle.exp_eq_exp.mpr
        refine ⟨-1, by norm_num; ring⟩
      have harg : Complex.arg ((Circle.exp (t : ℝ) : Circle) : ℂ) = Real.pi := by
        rw [hexp]
        exact Circle.invOn_arg_exp.1 ⟨by linarith [Real.pi_pos], le_rfl⟩
      change L (Complex.arg ((Circle.exp (t : ℝ) : Circle) : ℂ)) = L t
      calc
        L (Complex.arg ((Circle.exp (t : ℝ) : Circle) : ℂ)) = L Real.pi := congrArg L harg
        _ = L (-Real.pi) := hend
        _ = L t := congrArg L ht.symm
    · have htmem : (t : ℝ) ∈ Set.Ioc (-Real.pi) Real.pi :=
        ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht), t.2.2⟩
      have harg : Complex.arg ((Circle.exp (t : ℝ) : Circle) : ℂ) = t :=
        Circle.invOn_arg_exp.1 htmem
      change L (Complex.arg ((Circle.exp (t : ℝ) : Circle) : ℂ)) = L t
      exact congrArg L harg
  have hcomp : Continuous (lfun ∘ angleIntervalExp) := by
    rw [show lfun ∘ angleIntervalExp = fun t : AngleInterval ↦ L t by
      funext t
      exact hl_exp t]
    exact L.continuous.comp continuous_subtype_val
  have hlcont : Continuous lfun := angleIntervalExp_isQuotientMap.continuous_iff.mpr hcomp
  exact ⟨⟨lfun, hlcont⟩, fun _ ↦ rfl⟩

theorem hasLog_iff_winding_eq_zero (g : C(Circle, ℂ)) (hg : ∀ z, g z ≠ 0) :
    HasLog g ↔ winding g hg = 0 := by
  constructor
  · rintro ⟨l, hl⟩
    apply winding_eq_of_hasWinding hg
    refine ⟨l.comp Circle.exp, ?_, ?_⟩
    · intro t
      simpa using hl (Circle.exp t)
    · simp only [ContinuousMap.coe_comp, Function.comp_apply, Int.cast_zero, zero_mul, add_zero]
      congr 1
      apply Circle.exp_eq_exp.mpr
      refine ⟨1, by norm_num; ring⟩
  · intro hw
    obtain ⟨L, hL, hend⟩ := winding_spec g hg
    rw [hw] at hend
    simp only [Int.cast_zero, zero_mul, add_zero] at hend
    obtain ⟨l, hl⟩ := lift_descends_of_endpoints_eq L hend
    refine ⟨l, fun z ↦ ?_⟩
    rw [hl, hL, Circle.exp_arg]

theorem hasWinding_mul {g h : C(Circle, ℂ)} {n m : ℤ}
    (hg : HasWinding g n) (hh : HasWinding h m) : HasWinding (g * h) (n + m) := by
  obtain ⟨G, hGlift, hGend⟩ := hg
  obtain ⟨H, hHlift, hHend⟩ := hh
  refine ⟨G + H, ?_, ?_⟩
  · intro t
    simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, Complex.exp_add,
      hGlift, hHlift]
  · simp only [ContinuousMap.add_apply, hGend, hHend, Int.cast_add]
    ring

theorem winding_mul (g h : C(Circle, ℂ)) (hg : ∀ z, g z ≠ 0) (hh : ∀ z, h z ≠ 0) :
    winding (g * h) (fun z ↦ mul_ne_zero (hg z) (hh z)) = winding g hg + winding h hh := by
  apply winding_eq_of_hasWinding
  exact hasWinding_mul (winding_spec g hg) (winding_spec h hh)

/-- Pointwise integer powers of a nonvanishing continuous complex map. -/
def zpowMap (g : C(Circle, ℂ)) (hg : ∀ z, g z ≠ 0) (n : ℤ) : C(Circle, ℂ) :=
  ⟨fun z ↦ g z ^ n, g.continuous.zpow₀ n fun z ↦ Or.inl (hg z)⟩

@[simp]
theorem zpowMap_apply (g : C(Circle, ℂ)) (hg : ∀ z, g z ≠ 0) (n : ℤ) (z : Circle) :
    zpowMap g hg n z = g z ^ n := rfl

theorem zpowMap_ne_zero (g : C(Circle, ℂ)) (hg : ∀ z, g z ≠ 0) (n : ℤ) (z : Circle) :
    zpowMap g hg n z ≠ 0 := zpow_ne_zero n (hg z)

theorem hasWinding_zpow {g : C(Circle, ℂ)} {d : ℤ} (hg : ∀ z, g z ≠ 0)
    (hd : HasWinding g d) (n : ℤ) : HasWinding (zpowMap g hg n) (n * d) := by
  obtain ⟨G, hGlift, hGend⟩ := hd
  let L : C(ℝ, ℂ) := ⟨fun t ↦ (n : ℂ) * G t, continuous_const.mul G.continuous⟩
  refine ⟨L, ?_, ?_⟩
  · intro t
    change Complex.exp ((n : ℂ) * G t) = g (Circle.exp t) ^ n
    rw [Complex.exp_int_mul, hGlift]
  · change (n : ℂ) * G Real.pi =
      (n : ℂ) * G (-Real.pi) + ((n * d : ℤ) : ℂ) * expPeriod
    rw [hGend]
    push_cast
    ring

theorem winding_zpow (g : C(Circle, ℂ)) (hg : ∀ z, g z ≠ 0) (n : ℤ) :
    winding (zpowMap g hg n) (zpowMap_ne_zero g hg n) = n * winding g hg := by
  apply winding_eq_of_hasWinding
  exact hasWinding_zpow hg (winding_spec g hg) n

/-- The tautological inclusion of the unit circle into the complex plane. -/
def circleCoe : C(Circle, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem circleCoe_apply (z : Circle) : circleCoe z = (z : ℂ) := rfl

theorem circleCoe_ne_zero (z : Circle) : circleCoe z ≠ 0 := Circle.coe_ne_zero z

theorem winding_circleCoe : winding circleCoe circleCoe_ne_zero = 1 := by
  apply winding_eq_of_hasWinding
  let L : C(ℝ, ℂ) := ⟨fun t ↦ (t : ℂ) * Complex.I, by fun_prop⟩
  refine ⟨L, ?_, ?_⟩
  · intro t
    rfl
  · dsimp only [L, ContinuousMap.coe_mk]
    dsimp [expPeriod]
    push_cast
    ring

theorem winding_circleCoe_zpow (n : ℤ) :
    winding (zpowMap circleCoe circleCoe_ne_zero n)
      (zpowMap_ne_zero circleCoe circleCoe_ne_zero n) = n := by
  rw [winding_zpow, winding_circleCoe, mul_one]

/-- The loop obtained by viewing a parametrized circle from a point off its range. -/
def aroundMap (r : C(Circle, ℂ)) (x : ℂ) : C(Circle, ℂ) :=
  r - ContinuousMap.const Circle x

@[simp]
theorem aroundMap_apply (r : C(Circle, ℂ)) (x : ℂ) (z : Circle) :
    aroundMap r x z = r z - x := rfl

theorem aroundMap_ne_zero (r : C(Circle, ℂ)) {x : ℂ} (hx : x ∉ Set.range r)
    (z : Circle) : aroundMap r x z ≠ 0 := by
  intro h
  apply hx
  exact ⟨z, sub_eq_zero.mp h⟩

/-- Winding number of a loop about a point in its complement. -/
def windingAround (r : C(Circle, ℂ)) (x : ℂ) (hx : x ∉ Set.range r) : ℤ :=
  winding (aroundMap r x) (aroundMap_ne_zero r hx)

theorem windingAround_eq_of_dist_lt_infDist (r : C(Circle, ℂ))
    {x y : ℂ} (hx : x ∉ Set.range r) (hy : y ∉ Set.range r)
    (hxy : dist x y < Metric.infDist x (Set.range r)) :
    windingAround r y hy = windingAround r x hx := by
  let gx := aroundMap r x
  let gy := aroundMap r y
  have hgx : ∀ z, gx z ≠ 0 := aroundMap_ne_zero r hx
  have hgy : ∀ z, gy z ≠ 0 := aroundMap_ne_zero r hy
  let q : C(Circle, ℂ) :=
    ⟨fun z ↦ (r z - y) / (r z - x),
      (r.continuous.sub continuous_const).div₀ (r.continuous.sub continuous_const)
        fun z ↦ sub_ne_zero.mpr fun h ↦ hx ⟨z, h⟩⟩
  have hqeq (z : Circle) : q z = 1 + (x - y) / (r z - x) := by
    change (r z - y) / (r z - x) = 1 + (x - y) / (r z - x)
    field_simp [sub_ne_zero.mpr fun h ↦ hx ⟨z, h⟩]
    ring
  have hrange : (Set.range r).Nonempty := Set.range_nonempty r
  have hsmall (z : Circle) : ‖(x - y) / (r z - x)‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr <| sub_ne_zero.mpr fun h ↦ hx ⟨z, h⟩)]
    have hle : Metric.infDist x (Set.range r) ≤ dist x (r z) :=
      (Metric.le_infDist hrange).mp le_rfl ⟨z, rfl⟩
    simpa only [dist_eq_norm, norm_sub_rev] using hxy.trans_le hle
  have hqslit (z : Circle) : q z ∈ Complex.slitPlane := by
    rw [hqeq]
    exact Complex.mem_slitPlane_of_norm_lt_one (hsmall z)
  have hq0 (z : Circle) : q z ≠ 0 := Complex.slitPlane_ne_zero (hqslit z)
  have hqlog : HasLog q :=
    ⟨⟨fun z ↦ Complex.log (q z), q.continuous.clog hqslit⟩,
      fun z ↦ Complex.exp_log (hq0 z)⟩
  have hqwind : winding q hq0 = 0 :=
    (hasLog_iff_winding_eq_zero q hq0).mp hqlog
  have hmaps : gy = gx * q := by
    ext z
    change r z - y = (r z - x) * ((r z - y) / (r z - x))
    field_simp [sub_ne_zero.mpr fun h ↦ hx ⟨z, h⟩]
  calc
    winding gy hgy =
        winding (gx * q) (fun z ↦ mul_ne_zero (hgx z) (hq0 z)) :=
      winding_congr hmaps hgy _
    _ = winding gx hgx := by
      rw [winding_mul gx q hgx hq0, hqwind, add_zero]

/-- Winding number on the complement, bundled on the complement subtype. -/
def windingOnCompl (r : C(Circle, ℂ)) : ((Set.range r)ᶜ : Set ℂ) → ℤ :=
  fun x ↦ windingAround r x x.2

theorem windingOnCompl_isLocallyConstant (r : C(Circle, ℂ)) :
    IsLocallyConstant (windingOnCompl r) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  let d := Metric.infDist (x : ℂ) (Set.range r)
  have hrange : (Set.range r).Nonempty := Set.range_nonempty r
  have hclosed : IsClosed (Set.range r) := (isCompact_range r.continuous).isClosed
  have hd : 0 < d := (hclosed.notMem_iff_infDist_pos hrange).mp x.2
  let U : Set ((Set.range r)ᶜ : Set ℂ) :=
    Subtype.val ⁻¹' Metric.ball (x : ℂ) d
  refine ⟨U, Metric.isOpen_ball.preimage continuous_subtype_val, ?_, ?_⟩
  · exact Metric.mem_ball_self hd
  · intro y hy
    have hxy : dist (x : ℂ) (y : ℂ) < d := by
      simpa only [U, Set.mem_preimage, Metric.mem_ball, dist_comm] using hy
    exact windingAround_eq_of_dist_lt_infDist r x.2 y.2 hxy

theorem windingAround_eq_of_mem_connectedComponentIn (r : C(Circle, ℂ))
    {x y : ℂ} (hx : x ∈ (Set.range r)ᶜ) (hy : y ∈ (Set.range r)ᶜ)
    (hyx : y ∈ connectedComponentIn (Set.range r)ᶜ x) :
    windingAround r y hy = windingAround r x hx := by
  let xs : ((Set.range r)ᶜ : Set ℂ) := ⟨x, hx⟩
  let ys : ((Set.range r)ᶜ : Set ℂ) := ⟨y, hy⟩
  have hys : ys ∈ connectedComponent xs := by
    rw [connectedComponentIn_eq_image hx] at hyx
    obtain ⟨z, hz, hzy⟩ := hyx
    have hzy' : z = ys := Subtype.ext hzy
    simpa only [hzy'] using hz
  exact (windingOnCompl_isLocallyConstant r).apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hys mem_connectedComponent

end

end Submission.Winding
