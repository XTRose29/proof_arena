import ChallengeDeps

-- BEGIN INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/AnalyticUpgrade.lean

/-!
Two small, but sometimes useful, convergence facts about formal
multilinear series.  They prevent replacing the analytic ODE step by an
unjustified "smooth hence analytic" assertion: what is needed there is a
coefficient bound.
-/
open Set Filter
open scoped ENNReal NNReal Topology
namespace CKSupport
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A positive geometric bound on the *operator norms* of homogeneous
coefficients gives an honest ball on which the sum is analytic. -/
lemma analyticOnNhd_sum_of_geometric
    [CompleteSpace F] (p : FormalMultilinearSeries ℝ E F)
    (r : ℝ≥0) (C : ℝ) (hr : 0 < r)
    (hp : ∀ n : ℕ, ‖p n‖ * (r : ℝ)^n ≤ C) :
    (0 : ℝ≥0∞) < p.radius ∧
      ((r : ℝ≥0∞) ≤ p.radius) ∧
      AnalyticOnNhd ℝ p.sum (Metric.eball (0:E) (r:ℝ≥0∞)) := by
  have hle : (r : ℝ≥0∞) ≤ p.radius :=
    p.le_radius_of_bound C hp
  have hco : (0:ℝ≥0∞) < (r:ℝ≥0∞) := ENNReal.coe_pos.2 hr
  have hpos : (0:ℝ≥0∞) < p.radius := lt_of_lt_of_le hco hle
  have full : AnalyticOnNhd ℝ p.sum (Metric.eball (0:E) p.radius) :=
    (p.hasFPowerSeriesOnBall hpos).analyticOnNhd
  refine ⟨hpos, hle, ?_⟩
  intro x hx
  exact full x (Metric.eball_subset_eball hle hx)

lemma analyticOnNhd_sum_of_geometric_nnnorm
    [CompleteSpace F] (p : FormalMultilinearSeries ℝ E F)
    (r C : ℝ≥0) (hr : 0 < r)
    (hp : ∀ n : ℕ, ‖p n‖₊ * r^n ≤ C) :
    (0 : ℝ≥0∞) < p.radius ∧
      ((r:ℝ≥0∞) ≤ p.radius) ∧
      AnalyticOnNhd ℝ p.sum (Metric.eball (0:E) (r:ℝ≥0∞)) := by
  apply analyticOnNhd_sum_of_geometric p r (C:ℝ) hr
  intro n
  exact_mod_cast hp n

/-- In particular composition preserves positivity of radius.  This is
purely a formal-series statement; it does not solve a differential
recurrence for an inner series. -/
lemma comp_radius_pos
    (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F)
    (hq : 0 < q.radius) (hp : 0 < p.radius) :
    (0 : ℝ≥0∞) < (q.comp p).radius := by
  rcases FormalMultilinearSeries.comp_summable_nnreal q p hq hp with
    ⟨r, hr, H⟩
  have hle : (r : ℝ≥0∞) ≤ (q.comp p).radius :=
    FormalMultilinearSeries.le_comp_radius_of_summable q p r H
  exact lt_of_lt_of_le (ENNReal.coe_pos.2 hr) hle

end CKSupport

-- END INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/AnalyticUpgrade.lean

-- BEGIN INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/Chart.lean

/-!
Elementary characteristic-chart calculations for the scalar
Cauchy problem.  No existence assertion about a chart is made in this
file; it is just a useful, and fairly inexpensive, reduction.  The
point of writing this separately is that the inverse-chart calculation
only uses the chain rule.  In particular it is independent of any ODE
existence or convergence theorem.
-/
open Set Filter
open scoped Topology
namespace CKSupport
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The initial point in space--time--height.  The association of the
three products in mathlib is to the right: `X × ℝ × ℝ = X × (ℝ × ℝ)`. -/
def initialPoint (u0 : X → ℝ) (x : X) : X × ℝ × ℝ := (x,0,u0 x)

/-- The characteristic vector field.  Its first component has the minus
sign: a characteristic for `u_t = F . Du + f` is `(-F,1,f)`. -/
def charField (F : X × ℝ × ℝ → X) (f : X × ℝ × ℝ → ℝ) :
    X × ℝ × ℝ → X × ℝ × ℝ :=
  fun p => (- F p, (1:ℝ), f p)

lemma analyticOnNhd_charField
    (F : X × ℝ × ℝ → X) (f : X × ℝ × ℝ → ℝ)
    (hF : AnalyticOnNhd ℝ F (univ : Set (X × ℝ × ℝ)))
    (hf : AnalyticOnNhd ℝ f (univ : Set (X × ℝ × ℝ))) :
    AnalyticOnNhd ℝ (charField F f) univ := by
  intro p hp
  have hFa : AnalyticAt ℝ F p := hF p (Set.mem_univ _)
  have hfa : AnalyticAt ℝ f p := hf p (Set.mem_univ _)
  have hneg : AnalyticAt ℝ (fun q : X × ℝ × ℝ => - F q) p := by
    change AnalyticAt ℝ (-F) p
    exact hFa.neg
  have hone : AnalyticAt ℝ (fun _q : X × ℝ × ℝ => (1:ℝ)) p :=
    analyticAt_const
  -- products are right associated
  change AnalyticAt ℝ (fun p : X × ℝ × ℝ =>
      (- F p, (1:ℝ), f p)) p
  exact hneg.prod (hone.prod hfa)

/-- Pure calculus reduction.  If an analytic characteristic chart and
its analytic inverse have been produced, then `Z ∘ Ψ` solves the PDE.

This statement intentionally makes no reference to how the chart was
constructed.  It is convenient in attempts at the analytic ODE theorem:
that hard part can supply any sufficiently small open sets. -/
lemma solution_of_local_chart
    (F : X × ℝ × ℝ → X) (f : X × ℝ × ℝ → ℝ)
    (u0 : X → ℝ) (x0 : X)
    (U V : Set (X × ℝ))
    (Phi Psi : X × ℝ → X × ℝ) (Z : X × ℝ → ℝ)
    (hU : IsOpen U) (hV : IsOpen V)
    (hbase : (x0,(0:ℝ)) ∈ U)
    (hPsi : ∀ p ∈ U, Psi p ∈ V)
    (hPhi : ∀ y ∈ V, Phi y ∈ U)
    (hleft : ∀ p ∈ U, Phi (Psi p) = p)
    (hright : ∀ y ∈ V, Psi (Phi y) = y)
    (aPsi : AnalyticOnNhd ℝ Psi U)
    (aPhi : AnalyticOnNhd ℝ Phi V)
    (aZ   : AnalyticOnNhd ℝ Z V)
    (dPhi : ∀ y ∈ V,
      fderiv ℝ Phi y ((0:X),(1:ℝ)) =
        (- F ((Phi y).1, (Phi y).2, Z y), (1:ℝ)))
    (dZ : ∀ y ∈ V,
      fderiv ℝ Z y ((0:X),(1:ℝ)) =
        f ((Phi y).1, (Phi y).2, Z y))
    (iPsi : ∀ x : X, (x,(0:ℝ)) ∈ U -> Psi (x,0) = (x,0))
    (iZ : ∀ x : X, (x,(0:ℝ)) ∈ U -> Z (x,0) = u0 x) :
    ∃ (u : X × ℝ → ℝ),
      u = Z ∘ Psi ∧ AnalyticOnNhd ℝ u U ∧
      (∀ x : X, (x,(0:ℝ)) ∈ U -> u (x,0) = u0 x) ∧
      (∀ p ∈ U,
        fderiv ℝ u p ((0:X),(1:ℝ)) =
          fderiv ℝ u p (F (p.1,p.2,u p),(0:ℝ)) +
            f (p.1,p.2,u p)) := by
  let u : X × ℝ → ℝ := Z ∘ Psi
  have au : AnalyticOnNhd ℝ u U :=
    aZ.comp aPsi (by
      intro x hx
      exact hPsi x hx)
  refine ⟨u, rfl, au, ?_, ?_⟩
  · intro x hx
    change Z (Psi (x,0)) = u0 x
    rw [iPsi x hx]
    exact iZ x hx
  · intro p hp
    -- abbreviations for the point in parameter space and the two tangent
    -- directions.  Using the identity `Psi ∘ Phi = id` is a little easier
    -- than expanding the derivative of an inverse matrix.
    let y : X × ℝ := Psi p
    have hy : y ∈ V := hPsi p hp
    have hpy : Phi y = p := hleft p hp
    have ayPhi : AnalyticAt ℝ Phi y := aPhi y hy
    have ayZ : AnalyticAt ℝ Z y := aZ y hy
    have apPsi : AnalyticAt ℝ Psi p := aPsi p hp
    have adPhi : DifferentiableAt ℝ Phi y := ayPhi.differentiableAt
    have adZ : DifferentiableAt ℝ Z y := ayZ.differentiableAt
    have adPsi : DifferentiableAt ℝ Psi p := apPsi.differentiableAt
    have adu : DifferentiableAt ℝ u p :=
      (au p hp).differentiableAt

    -- differentiate the local right inverse at `y`.  We avoid a global
    -- derivative of an equality by using `Filter.EventuallyEq` on the open
    -- set `V`.
    have ev_id : (Psi ∘ Phi) =ᶠ[𝓝 y] id := by
      have hmem : V ∈ 𝓝 y := hV.mem_nhds hy
      filter_upwards [hmem] with z hz
      exact hright z hz
    have hderiv_id :
        fderiv ℝ (Psi ∘ Phi) y =
          fderiv ℝ (id : X × ℝ → X × ℝ) y :=
      Filter.EventuallyEq.fderiv_eq ev_id
    -- Above `apPsi` is at `p`, while `Phi y = p`.
    -- First put it at the endpoint required by `fderiv_comp`.
    have adPsi' : DifferentiableAt ℝ Psi (Phi y) := by
      simpa [hpy] using adPsi
    have comp_deriv' : fderiv ℝ (Psi ∘ Phi) y =
        fderiv ℝ Psi (Phi y) ∘L fderiv ℝ Phi y := by
      exact fderiv_comp y adPsi' adPhi

    have right_inverse_deriv :
        fderiv ℝ Psi p ∘L fderiv ℝ Phi y =
          ContinuousLinearMap.id ℝ (X × ℝ) := by
      calc
        fderiv ℝ Psi p ∘L fderiv ℝ Phi y =
            fderiv ℝ (Psi ∘ Phi) y := by
              simpa [hpy] using comp_deriv'.symm
        _ = fderiv ℝ (id : X × ℝ → X × ℝ) y := hderiv_id
        _ = ContinuousLinearMap.id ℝ (X × ℝ) := fderiv_id

    let e : X × ℝ := ((0:X),(1:ℝ))
    let Fv : X := F (p.1,p.2,u p)
    have hZval : Z y = u p := rfl
      -- `u p` is definitionally `Z (Psi p)`
    have hDPhi : fderiv ℝ Phi y e = (-Fv,(1:ℝ)) := by
      simpa [e, Fv, hpy, hZval] using dPhi y hy
    have hDZ : fderiv ℝ Z y e = f (p.1,p.2,u p) := by
      simpa [e, hpy, hZval] using dZ y hy

    have hright_vec :
        fderiv ℝ Psi p (fderiv ℝ Phi y e) = e := by
      have := congrArg (fun T : (X × ℝ →L[ℝ] X × ℝ) => T e)
        right_inverse_deriv
      simpa using this
    have hright_vec' :
        fderiv ℝ Psi p (-Fv,(1:ℝ)) = e := by
      simpa [hDPhi] using hright_vec

    -- Chain rule for `u=Z ∘ Psi`.
    have hduchain : fderiv ℝ u p =
        fderiv ℝ Z (Psi p) ∘L fderiv ℝ Psi p := by
      exact fderiv_comp p
        ((aZ (Psi p) (hPsi p hp)).differentiableAt)
        ((aPsi p hp).differentiableAt)
    have hvaldu : fderiv ℝ u p (-Fv,(1:ℝ)) =
            f (p.1,p.2,u p) := by
      rw [hduchain]
      -- a composition is evaluated componentwise
      change fderiv ℝ Z (Psi p)
          (fderiv ℝ Psi p (-Fv,(1:ℝ))) = _
      rw [hright_vec']
      exact hDZ

    -- Express `(-Fv,1)` as `(0,1) - (Fv,0)` and use linearity.
    have hlin :
      fderiv ℝ u p (-Fv,(1:ℝ)) =
        fderiv ℝ u p ((0:X),(1:ℝ)) -
          fderiv ℝ u p (Fv,(0:ℝ)) := by
      have hv : ((-Fv,(1:ℝ)) : X × ℝ) =
          ((0:X),(1:ℝ)) - (Fv,(0:ℝ)) := by
            ext <;> simp
      rw [hv, map_sub]
    have : fderiv ℝ u p ((0:X),(1:ℝ)) =
          fderiv ℝ u p (Fv,(0:ℝ)) + f (p.1,p.2,u p) := by
      have hEq : fderiv ℝ u p ((0:X),(1:ℝ)) -
            fderiv ℝ u p (Fv,(0:ℝ)) = f (p.1,p.2,u p) := by
          rw [← hlin]
          exact hvaldu
      linarith
    simpa [Fv] using this

end CKSupport

-- END INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/Chart.lean

-- BEGIN INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/FiberUnique.lean
open Set Filter
open scoped Topology
namespace CKSupport

/-- Uniqueness on an open real interval for an autonomous ODE when the
vector field is `C¹` only near the first curve.  This local version is handy
for characteristics whose right hand side is built from germs. -/
lemma ode_unique_of_local_contDiff
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (G : Y → Y) (α β : ℝ → Y) (a b t₀ : ℝ)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hα : ∀ t ∈ Set.Ioo a b, HasDerivAt α (G (α t)) t)
    (hβ : ∀ t ∈ Set.Ioo a b, HasDerivAt β (G (β t)) t)
    (hlocal : ∀ t ∈ Set.Ioo a b, ContDiffAt ℝ 1 G (α t))
    (heq : α t₀ = β t₀) :
    Set.EqOn α β (Set.Ioo a b) := by
  -- On a preconnected set, a locally constant truth value is constant.
  let P : ℝ → ℝ → Prop :=
    fun x y => (α x = β x ↔ α y = β y)
  have hnear : ∀ x ∈ Set.Ioo a b, ∀ᶠ y in 𝓝[Set.Ioo a b] x, P x y := by
    intro x hx
    have ca : ContinuousAt α x := (hα x hx).continuousAt
    have cb : ContinuousAt β x := (hβ x hx).continuousAt
    by_cases hxy : α x = β x
    · obtain ⟨K, s, hs, hKs⟩ := (hlocal x hx).exists_lipschitzOnWith
      have ea : ∀ᶠ t in 𝓝 x, α t ∈ s := ca.preimage_mem_nhds hs
      have eb : ∀ᶠ t in 𝓝 x, β t ∈ s :=
        cb.preimage_mem_nhds (by simpa [hxy] using hs)
      have ei : ∀ᶠ t in 𝓝 x, t ∈ Set.Ioo a b :=
        isOpen_Ioo.mem_nhds hx
      have eha : ∀ᶠ t in 𝓝 x,
          HasDerivAt α (G (α t)) t ∧ α t ∈ s := by
        filter_upwards [ei, ea] with t ht hst
        exact ⟨hα t ht, hst⟩
      have ehb : ∀ᶠ t in 𝓝 x,
          HasDerivAt β (G (β t)) t ∧ β t ∈ s := by
        filter_upwards [ei, eb] with t ht hst
        exact ⟨hβ t ht, hst⟩
      have ee : α =ᶠ[𝓝 x] β :=
        ODE_solution_unique_of_eventually
          (v := fun _ : ℝ => G) (s := fun _ : ℝ => s) (K := K)
          (Filter.Eventually.of_forall (fun _ => hKs)) eha ehb hxy
      have ee' : ∀ᶠ y in 𝓝[Set.Ioo a b] x, α y = β y :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds ee
      filter_upwards [ee'] with y hy
      exact ⟨fun _ => hy, fun _ => hxy⟩
    · have en : ∀ᶠ y in 𝓝 x, α y ≠ β y :=
        (ca.ne_iff_eventually_ne cb).1 hxy
      have en' : ∀ᶠ y in 𝓝[Set.Ioo a b] x, α y ≠ β y :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds en
      filter_upwards [en'] with y hy
      exact ⟨fun h => (hxy h).elim, fun h => (hy h).elim⟩
  have htrans : ∀ x y z, x ∈ Set.Ioo a b → y ∈ Set.Ioo a b →
      z ∈ Set.Ioo a b → P x y → P y z → P x z := by
    intro x y z hx hy hz h1 h2
    exact h1.trans h2
  have hsymm : ∀ x y, x ∈ Set.Ioo a b → y ∈ Set.Ioo a b → P x y → P y x := by
    intro x y hx hy h
    exact h.symm
  intro t ht
  have hrel : P t₀ t :=
    isPreconnected_Ioo.induction₂ P hnear htrans hsymm ht₀ ht
  exact (hrel.mp heq)
end CKSupport

namespace CKSupport
/-- Chain rule along a characteristic of one height, tested on another
solution.  The discrepancy is a single spatial derivative. -/
lemma hasDerivAt_along_chart
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X × ℝ × ℝ → X) (f : X × ℝ × ℝ → ℝ)
    (Zline : ℝ → ℝ) (Pline : ℝ → (X × ℝ))
    (v : (X × ℝ) → ℝ) (t : ℝ)
    (hP : HasDerivAt Pline
      (- F ((Pline t).1, (Pline t).2, Zline t), (1:ℝ)) t)
    (hv : DifferentiableAt ℝ v (Pline t))
    (hpde : fderiv ℝ v (Pline t) ((0:X),(1:ℝ)) =
      fderiv ℝ v (Pline t)
        (F ((Pline t).1,(Pline t).2, v (Pline t)), (0:ℝ)) +
          f ((Pline t).1,(Pline t).2, v (Pline t))) :
    HasDerivAt (fun s : ℝ => v (Pline s))
      (f ((Pline t).1,(Pline t).2, v (Pline t)) +
        fderiv ℝ v (Pline t)
          (F ((Pline t).1,(Pline t).2, v (Pline t)) -
            F ((Pline t).1,(Pline t).2, Zline t), (0:ℝ))) t := by
  have hchain := hv.hasFDerivAt.comp_hasDerivAt t hP
  change HasDerivAt (v ∘ Pline) _ t at hchain
  change HasDerivAt (v ∘ Pline) _ t
  convert hchain using 1
  -- only linearity of the Fréchet derivative is used here
  let L : (X × ℝ) →L[ℝ] ℝ := fderiv ℝ v (Pline t)
  let A : X := F ((Pline t).1,(Pline t).2, v (Pline t))
  let B : X := F ((Pline t).1,(Pline t).2, Zline t)
  let c : ℝ := f ((Pline t).1,(Pline t).2, v (Pline t))
  have hp : L ((0:X),(1:ℝ)) = L (A,(0:ℝ)) + c := by
    simpa [L, A, c] using hpde
  change c + L (A - B, (0:ℝ)) = L (- B,(1:ℝ))
  have e1 : ((-B,(1:ℝ)) : X × ℝ) =
      ((0:X),(1:ℝ)) - (B,(0:ℝ)) := by ext <;> simp
  have e2 : ((A-B,(0:ℝ)) : X × ℝ) =
      (A,(0:ℝ)) - (B,(0:ℝ)) := by ext <;> simp
  rw [e1, e2, map_sub, map_sub, hp]
  ring
end CKSupport

namespace CKSupport
/-- The scalar comparison ODE, with time adjoined as a state.  Along a fixed
characteristic of height `Zline`, another solution has height derivative equal
 to the second component below. -/
noncomputable def comparisonField
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X × ℝ × ℝ → X) (f : X × ℝ × ℝ → ℝ)
    (v : (X × ℝ) → ℝ)
    (Pline : ℝ → (X × ℝ)) (Zline : ℝ → ℝ) :
    (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
  ((1:ℝ),
    f ((Pline w.1).1, (Pline w.1).2, w.2) +
      fderiv ℝ v (Pline w.1)
        (F ((Pline w.1).1,(Pline w.1).2,w.2) -
          F ((Pline w.1).1,(Pline w.1).2,Zline w.1), (0:ℝ)))

lemma contDiffAt_comparisonField
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X × ℝ × ℝ → X) (f : X × ℝ × ℝ → ℝ)
    (v : (X × ℝ) → ℝ)
    (Pline : ℝ → (X × ℝ)) (Zline : ℝ → ℝ)
    (t z : ℝ)
    (hP : ContDiffAt ℝ 1 Pline t)
    (hZ : ContDiffAt ℝ 1 Zline t)
    (hdv : ContDiffAt ℝ 1 (fderiv ℝ v) (Pline t))
    (hF : ∀ q : X × ℝ × ℝ, ContDiffAt ℝ 1 F q)
    (hf : ∀ q : X × ℝ × ℝ, ContDiffAt ℝ 1 f q) :
    ContDiffAt ℝ 1 (comparisonField F f v Pline Zline) (t,z) := by
  -- pull all ingredients back to the product `(time,height)`
  have hpw : ContDiffAt ℝ 1 (fun w : ℝ × ℝ => Pline w.1) (t,z) := by
    convert hP.comp (x:=(t,z)) contDiffAt_fst using 1 <;> rfl
  have hzw : ContDiffAt ℝ 1 (fun w : ℝ × ℝ => Zline w.1) (t,z) := by
    convert hZ.comp (x:=(t,z)) contDiffAt_fst using 1 <;> rfl
  have hq : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ =>
        ((Pline w.1).1, (Pline w.1).2, w.2)) (t,z) := by
    exact hpw.fst.prodMk (hpw.snd.prodMk contDiffAt_snd)
  have hq0 : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ =>
        ((Pline w.1).1, (Pline w.1).2, Zline w.1)) (t,z) := by
    exact hpw.fst.prodMk (hpw.snd.prodMk hzw)
  have hFa : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ => F ((Pline w.1).1,(Pline w.1).2,w.2)) (t,z) := by
    convert (hF ((Pline t).1,(Pline t).2,z)).comp (x:=(t,z)) hq using 1 <;> rfl
  have hFb : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ => F ((Pline w.1).1,(Pline w.1).2,Zline w.1)) (t,z) := by
    convert (hF ((Pline t).1,(Pline t).2,Zline t)).comp (x:=(t,z)) hq0 using 1 <;> rfl
  have hfc : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ => f ((Pline w.1).1,(Pline w.1).2,w.2)) (t,z) := by
    convert (hf ((Pline t).1,(Pline t).2,z)).comp (x:=(t,z)) hq using 1 <;> rfl
  have harg : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ =>
        (F ((Pline w.1).1,(Pline w.1).2,w.2) -
          F ((Pline w.1).1,(Pline w.1).2,Zline w.1), (0:ℝ))) (t,z) := by
    exact hFa.sub hFb |>.prodMk contDiffAt_const
  have hlin : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ => fderiv ℝ v (Pline w.1)) (t,z) := by
    convert hdv.comp (x:=(t,z)) hpw using 1 <;> rfl
  have happ : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ =>
        fderiv ℝ v (Pline w.1)
          (F ((Pline w.1).1,(Pline w.1).2,w.2) -
            F ((Pline w.1).1,(Pline w.1).2,Zline w.1), (0:ℝ))) (t,z) :=
    hlin.clm_apply harg
  exact (contDiffAt_const (𝕜:=ℝ)).prodMk (hfc.add happ)
end CKSupport
namespace CKSupport
lemma hasDerivAt_comparison_Z
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X × ℝ × ℝ → X) (f : X × ℝ × ℝ → ℝ)
    (v : (X × ℝ) → ℝ)
    (Pline : ℝ → (X × ℝ)) (Zline : ℝ → ℝ) (t : ℝ)
    (hZ : HasDerivAt Zline
      (f ((Pline t).1,(Pline t).2,Zline t)) t) :
    HasDerivAt (fun s : ℝ => (s, Zline s))
      (comparisonField F f v Pline Zline (t, Zline t)) t := by
  have h := (hasDerivAt_id t).prodMk hZ
  have he : comparisonField F f v Pline Zline (t, Zline t) =
      ((1:ℝ), f ((Pline t).1,(Pline t).2,Zline t)) := by
    dsimp [comparisonField]
    have hz :
        (F ((Pline t).1, (Pline t).2, Zline t) -
              F ((Pline t).1, (Pline t).2, Zline t), (0:ℝ)) =
            (0 : X × ℝ) := by ext <;> simp
    rw [hz]
    rw [map_zero]
    simp
  rw [he]
  simpa using h

lemma hasDerivAt_comparison_v
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X × ℝ × ℝ → X) (f : X × ℝ × ℝ → ℝ)
    (v : (X × ℝ) → ℝ)
    (Pline : ℝ → (X × ℝ)) (Zline : ℝ → ℝ) (t : ℝ)
    (hv : HasDerivAt (fun s : ℝ => v (Pline s))
      (f ((Pline t).1,(Pline t).2, v (Pline t)) +
        fderiv ℝ v (Pline t)
          (F ((Pline t).1,(Pline t).2, v (Pline t)) -
            F ((Pline t).1,(Pline t).2, Zline t), (0:ℝ))) t) :
    HasDerivAt (fun s : ℝ => (s, v (Pline s)))
      (comparisonField F f v Pline Zline (t, v (Pline t))) t := by
  exact (hasDerivAt_id t).prodMk hv
end CKSupport

-- END INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/FiberUnique.lean

-- BEGIN INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/FormalTimeIntegral.lean
open Set Filter
open scoped BigOperators ENNReal NNReal Topology
namespace CKSupport
noncomputable section
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The two complementary projections on parameter and time. Keeping both in the
same product is convenient for multilinear expansions. -/
def qPart : Y × ℝ →L[ℝ] (Y × ℝ) :=
  (ContinuousLinearMap.inl ℝ Y ℝ).comp (ContinuousLinearMap.fst ℝ Y ℝ)
def tPart : Y × ℝ →L[ℝ] (Y × ℝ) :=
  (ContinuousLinearMap.inr ℝ Y ℝ).comp (ContinuousLinearMap.snd ℝ Y ℝ)
@[simp] lemma qPart_apply (z : Y × ℝ) : qPart (Y:=Y) z = (z.1,0) := rfl
@[simp] lemma tPart_apply (z : Y × ℝ) : tPart (Y:=Y) z = (0,z.2) := rfl
lemma qPart_add_tPart (z:Y×ℝ) : qPart (Y:=Y) z + tPart (Y:=Y) z = z := by
  ext <;> simp
lemma norm_qPart_le : ‖qPart (Y:=Y)‖ ≤ (1:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  simp [Prod.norm_def]
lemma norm_tPart_le : ‖tPart (Y:=Y)‖ ≤ (1:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  simp [Prod.norm_def]

variable {n : ℕ}
/-- In a homogeneous map, ask the entries in `s` to be time entries and the
others to be parameter entries. -/
def splitCoeff (r : (Y × ℝ)[×n]→L[ℝ] Y) (s : Finset (Fin n)) :
    (Y × ℝ)[×n]→L[ℝ] Y :=
  r.compContinuousLinearMap (fun i => if i ∈ s then tPart (Y:=Y) else qPart (Y:=Y))

@[simp] lemma splitCoeff_apply (r : (Y × ℝ)[×n]→L[ℝ] Y) (s : Finset (Fin n))
    (v : Fin n → (Y×ℝ)) :
    splitCoeff r s v = r (fun i => if i ∈ s then (0,(v i).2) else ((v i).1,0)) := by
  classical
  simp only [splitCoeff, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

lemma sum_splitCoeff_apply (r : (Y × ℝ)[×n]→L[ℝ] Y)
    (z : Y×ℝ) :
    (∑ s : Finset (Fin n), splitCoeff r s) (fun _ => z) = r (fun _ => z) := by
  classical
  have H := r.map_add_univ (fun _ : Fin n => tPart (Y:=Y) z)
          (fun _ : Fin n => qPart (Y:=Y) z)
  have hleft : ((fun _ : Fin n => tPart (Y:=Y) z) +
          (fun _ : Fin n => qPart (Y:=Y) z)) = (fun _ : Fin n => z) := by
    funext i
    -- addition is coordinatewise; the order in H is time then parameter
    have hz := qPart_add_tPart (Y:=Y) z
    simpa [add_comm] using hz
  rw [hleft] at H
  rw [ContinuousMultilinearMap.sum_apply]
  -- the summands are the piecewise time/parameter vectors
  -- unfold the two kinds of piecewise vector using membership
  have Hp : (∑ s : Finset (Fin n),
        r (fun i => if i ∈ s then (0,z.2) else (z.1,0))) =
        (∑ s : Finset (Fin n),
          r (s.piecewise (fun _ : Fin n => tPart (Y:=Y) z)
                         (fun _ : Fin n => qPart (Y:=Y) z))) := by
    apply Finset.sum_congr rfl
    intro s hs
    apply congrArg r
    funext i
    by_cases hi : i ∈ s
    · simp [Finset.piecewise, hi]
    · simp [Finset.piecewise, hi]
  simpa [splitCoeff_apply, Hp] using Hp.trans H.symm

lemma splitCoeff_apply_diag (r : (Y × ℝ)[×n]→L[ℝ] Y)
    (s : Finset (Fin n)) (q:Y) (t:ℝ) :
    splitCoeff r s (fun _ => (q,t)) =
      t ^ s.card • r (fun i => if i ∈ s then (0,1) else (q,0)) := by
  classical
  -- separate the scalar time in every marked slot
  let c : Fin n → ℝ := fun i => if i ∈ s then t else 1
  let w : Fin n → (Y×ℝ) := fun i => if i ∈ s then (0,1) else (q,0)
  have h := r.map_smul_univ c w
  have hc : (∏ i : Fin n, c i) = t ^ s.card := by
    classical
    dsimp [c]
    rw [Finset.prod_ite]
    simp
  rw [hc] at h
  rw [splitCoeff_apply]
  convert h using 1
  · congr 1
    funext i
    by_cases hi : i ∈ s <;> simp [c,w,hi]

/-- A single antiderivative term. The first slot supplies a time scalar; the
other `n` slots are fed to the selected component of the homogeneous map. -/
def antTerm (r : (Y × ℝ)[×n]→L[ℝ] Y) (s : Finset (Fin n)) :
    (Y × ℝ)[×(n+1)]→L[ℝ] Y :=
  ContinuousLinearMap.uncurryLeft
    (ContinuousLinearMap.smulRight
      (ContinuousLinearMap.snd ℝ Y ℝ) (splitCoeff r s))

@[simp] lemma antTerm_apply_diag (r : (Y × ℝ)[×n]→L[ℝ] Y)
    (s : Finset (Fin n)) (z:Y×ℝ) :
    antTerm r s (fun _ => z) = z.2 • splitCoeff r s (fun _ => z) := by
  classical
  simp [antTerm, ContinuousLinearMap.uncurryLeft_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousMultilinearMap.smul_apply, Fin.tail]

/-- Formal antiderivative in the time coordinate for a homogeneous map. The
coefficient `1/(k+1)` is attached to the component with `k` time slots. -/
def timeAnt (r : (Y × ℝ)[×n]→L[ℝ] Y) :
    (Y × ℝ)[×(n+1)]→L[ℝ] Y :=
  ∑ s : Finset (Fin n), (1 / ((s.card:ℝ) + 1)) • antTerm r s

lemma splitCoeff_norm_le (r : (Y × ℝ)[×n]→L[ℝ] Y)
    (s : Finset (Fin n)) : ‖splitCoeff r s‖ ≤ ‖r‖ := by
  classical
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le r
    (fun i : Fin n => if i ∈ s then tPart (Y:=Y) else qPart (Y:=Y))).trans ?_
  have hp : (∏ i : Fin n,
      ‖(if i ∈ s then tPart (Y:=Y) else qPart (Y:=Y))‖) ≤ (1:ℝ) := by
    apply Finset.prod_le_one
    · intro i hi; exact norm_nonneg _
    · intro i hi
      split_ifs
      · exact norm_tPart_le (Y:=Y)
      · exact norm_qPart_le (Y:=Y)
  simpa using (mul_le_mul_of_nonneg_left hp (norm_nonneg r))

lemma antTerm_bound (r : (Y × ℝ)[×n]→L[ℝ] Y)
    (s : Finset (Fin n)) (v : Fin (n+1) → Y×ℝ) :
    ‖antTerm r s v‖ ≤ ‖r‖ * ∏ i : Fin (n+1), ‖v i‖ := by
  classical
  rw [antTerm, ContinuousLinearMap.uncurryLeft_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousMultilinearMap.smul_apply]
  calc
    _ = ‖(v 0).2‖ * ‖(splitCoeff r s) (Fin.tail v)‖ := by rw [norm_smul]; rfl
    _ ≤ ‖v 0‖ * (‖r‖ * ∏ i : Fin n, ‖v i.succ‖) := by
      gcongr
      · simp [Prod.norm_def]
      calc
        ‖(splitCoeff r s) (Fin.tail v)‖ ≤
            ‖splitCoeff r s‖ * ∏ i : Fin n, ‖(Fin.tail v) i‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ ‖r‖ * ∏ i : Fin n, ‖v i.succ‖ := by
          dsimp [Fin.tail]
          gcongr
          exact splitCoeff_norm_le r s
    _ = ‖r‖ * ∏ i : Fin (n+1), ‖v i‖ := by
      rw [Fin.prod_univ_succ]
      ring

lemma timeAnt_norm_le (r : (Y × ℝ)[×n]→L[ℝ] Y) :
    ‖timeAnt r‖ ≤ (2:ℝ)^n * ‖r‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [timeAnt, ContinuousMultilinearMap.sum_apply]
  calc
    ‖∑ s : Finset (Fin n),
      (((1 / ((s.card:ℝ)+1)) • antTerm r s) v)‖
        ≤ ∑ s : Finset (Fin n),
           ‖(((1 / ((s.card:ℝ)+1)) • antTerm r s) v)‖ := by
             simpa using norm_sum_le (Finset.univ)
                 (fun s : Finset (Fin n) =>
                   (((1 / ((s.card:ℝ)+1)) • antTerm r s) v))
    _ ≤ ∑ _s : Finset (Fin n),
           (‖r‖ * ∏ i : Fin (n+1), ‖v i‖) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [ContinuousMultilinearMap.smul_apply, norm_smul]
      calc
        ‖(1 / ((s.card:ℝ)+1) : ℝ)‖ * ‖antTerm r s v‖
            ≤ 1 * (‖r‖ * ∏ i : Fin (n+1), ‖v i‖) := by
                apply mul_le_mul
                · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/((s.card:ℝ)+1))]
                  have h : (1:ℝ) ≤ (s.card:ℝ) + 1 := by exact_mod_cast (Nat.le_add_left 1 s.card)
                  exact (div_le_one (by positivity)).2 h
                · exact antTerm_bound r s v
                · exact norm_nonneg _
                · norm_num
        _ = _ := by ring
    _ = (2:ℝ)^n * (‖r‖ * ∏ i : Fin (n+1), ‖v i‖) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    _ = ((2:ℝ)^n * ‖r‖) * ∏ i : Fin (n+1), ‖v i‖ := by ring

lemma timeAnt_apply_diag (r : (Y × ℝ)[×n]→L[ℝ] Y)
    (q:Y) (t:ℝ) :
    timeAnt r (fun _ => (q,t)) =
      ∑ s : Finset (Fin n),
        (t ^ (s.card+1) / ((s.card:ℝ)+1)) •
          r (fun i => if i ∈ s then (0,1) else (q,0)) := by
  classical
  simp only [timeAnt, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, antTerm_apply_diag,
    splitCoeff_apply_diag]
  apply Finset.sum_congr rfl
  intro s hs
  -- just the scalar arithmetic; put the extra `t` together with the powers
  simp [smul_smul]
  congr 1
  simp [pow_succ]
  ring

lemma timeAnt_hasDerivAt (r : (Y × ℝ)[×n]→L[ℝ] Y)
    (q:Y) (t:ℝ) :
    HasDerivAt (fun u : ℝ => timeAnt r (fun _ => (q,u)))
      (r (fun _ => (q,t))) t := by
  classical
  let R : Finset (Fin n) → Y := fun s =>
    r (fun i => if i ∈ s then (0,1) else (q,0))
  have hscalar (k : ℕ) :
      HasDerivAt (fun u : ℝ => u^(k+1) / ((k:ℝ)+1)) (t^k) t := by
    have H := ( (hasDerivAt_pow (k+1) t).div_const ((k:ℝ)+1))
    change HasDerivAt (fun x : ℝ => x ^ (k+1) / ((k:ℝ)+1))
       ((↑(k+1) * t ^ (k+1-1)) / ((k:ℝ)+1)) t at H
    convert H using 1
    · have hk : ( (k:ℝ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
      field_simp
      simp [Nat.cast_add]
      ring

  have hs : ∀ s ∈ (Finset.univ : Finset (Finset (Fin n))),
      HasDerivAt
        (fun u : ℝ => (u^(s.card+1) / ((s.card:ℝ)+1)) • R s)
        ((t^s.card) • R s) t := by
    intro s hs
    exact (hscalar s.card).smul_const (R s)
  have hsum := HasDerivAt.sum hs
  have hsplit := sum_splitCoeff_apply (Y:=Y) r (q,t)
  have hdiag : (∑ s : Finset (Fin n), (t^s.card) • R s) =
      r (fun _ : Fin n => (q,t)) := by
    -- split every slot and use multilinearity for powers of time
    rw [ContinuousMultilinearMap.sum_apply] at hsplit
    -- rewrite each summand with the version that still has `splitCoeff`
    calc
      (∑ s : Finset (Fin n), (t^s.card) • R s) =
          ∑ s : Finset (Fin n), splitCoeff r s (fun _ => (q,t)) := by
            apply Finset.sum_congr rfl
            intro s hs
            simpa [R] using (splitCoeff_apply_diag r s q t).symm
      _ = r (fun _ : Fin n => (q,t)) := hsplit
  rw [hdiag] at hsum
  convert hsum using 1
  funext u
  simpa [R] using timeAnt_apply_diag r q u


/-- the degree-one boundary term `q`. -/
def odeBoundary : (Y × ℝ)[×1]→L[ℝ] Y :=
  (ContinuousMultilinearMap.ofSubsingleton ℝ (Y×ℝ) Y (0:Fin 1))
    (ContinuousLinearMap.fst ℝ Y ℝ)

@[simp] lemma odeBoundary_apply (z : Fin 1 → Y×ℝ) :
    odeBoundary z = (z 0).1 := rfl
lemma odeBoundary_norm_le : ‖odeBoundary (Y:=Y)‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro v
  have hprod : ‖v 0‖ = ∏ i : Fin 1, ‖v i‖ := by
    simp
  simpa [odeBoundary_apply, ← hprod, Prod.norm_def]

/-- Truncation keeping exactly the already constructed coefficients. -/
def fmsLt (b : FormalMultilinearSeries ℝ (Y×ℝ) Y) (N : ℕ) :
    FormalMultilinearSeries ℝ (Y×ℝ) Y :=
  fun k => if k < N then b k else 0

/-- Coefficients prescribed by the characteristic ODE.  `odeSeries p` is the
formal displacement in `(q,t)` for `w' = p(w)`, `w(q,0)=q`. The definition is
triangular: the `N`th coefficient of a composition only asks for positive
coefficients up to `N`. No convergence assertion is hidden here. -/
def odeSeries (p : FormalMultilinearSeries ℝ Y Y) :
    FormalMultilinearSeries ℝ (Y×ℝ) Y :=
  fun N => Nat.strongRec (motive := fun N => ((Y×ℝ)[×N]→L[ℝ] Y))
    (fun n prev =>
      match n with
      | 0 => 0
      | k+1 =>
        let b : FormalMultilinearSeries ℝ (Y×ℝ) Y :=
          fun j => if h : j < k+1 then prev j h else 0
        timeAnt ((p.comp b) k) +
          (if h : k = 0 then h ▸ odeBoundary (Y:=Y) else 0)) N

@[simp] lemma odeSeries_zero (p : FormalMultilinearSeries ℝ Y Y) :
    odeSeries p 0 = 0 := by
  rw [odeSeries, Nat.strongRec_eq]

lemma odeSeries_succ (p : FormalMultilinearSeries ℝ Y Y) (k:ℕ) :
    odeSeries p (k+1) =
      timeAnt ((p.comp (fmsLt (odeSeries p) (k+1))) k) +
        (if h : k=0 then h ▸ odeBoundary (Y:=Y) else 0) := by
  rw [odeSeries, Nat.strongRec_eq]
  dsimp
  rfl

lemma odeSeries_succ_norm (p : FormalMultilinearSeries ℝ Y Y) (k:ℕ) :
    ‖odeSeries p (k+1)‖ ≤
       (2:ℝ)^k * ‖(p.comp (fmsLt (odeSeries p) (k+1))) k‖ +
          (if k=0 then 1 else 0) := by
  cases k with
  | zero =>
    rw [odeSeries_succ]
    dsimp
    exact le_trans (norm_add_le _ _)
      (add_le_add (timeAnt_norm_le _) (odeBoundary_norm_le (Y:=Y)))
  | succ k =>
    rw [odeSeries_succ]
    simp [Nat.succ_ne_zero]
    exact timeAnt_norm_le _

end
end CKSupport

-- END INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/FormalTimeIntegral.lean

-- BEGIN INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/Majorant.lean

/-!
A very small quantitative consequence of `AnalyticAt`.  It is useful in
ODE attempts because it puts all coefficient choices on one concrete
ball.  Notice that the conclusion is about **coefficients** of a series,
not just about pointwise boundedness of the represented function.
-/
open Set Filter NNReal ENNReal
open scoped ENNReal NNReal Topology
namespace CKSupport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shrinking the ball given by analyticity gives a positive real radius;
on every smaller closed radial scale the operator norms of its homogeneous
coefficients have a uniform geometric bound.  Keeping the radius in
`NNReal` avoids conversions in later majorants. -/
lemma geometric_bound_of_analyticAt {g : E → F} {x : E}
    (h : AnalyticAt ℝ g x) :
    ∃ (p : FormalMultilinearSeries ℝ E F) (ρ : ℝ≥0) (C : ℝ),
      0 < ρ ∧ 0 < C ∧
      HasFPowerSeriesOnBall g p x (ρ : ℝ≥0∞) ∧
      (∀ n : ℕ, ‖p n‖ * (ρ : ℝ) ^ n ≤ C) := by
  rcases h with ⟨p, r, hr⟩
  -- choose a strictly smaller real radius; `r` is only an extended real
  -- number in `HasFPowerSeriesOnBall`.
  obtain ⟨ρ, hρ0, hρr⟩ := (ENNReal.lt_iff_exists_nnreal_btwn).1 hr.r_pos
  have hρpos : 0 < ρ := (ENNReal.coe_pos).1 hρ0
  have hρrad : (ρ : ℝ≥0∞) < p.radius := lt_of_lt_of_le hρr hr.r_le
  rcases p.norm_mul_pow_le_of_lt_radius hρrad with ⟨C, hC, hbound⟩
  refine ⟨p, ρ, C, hρpos, hC, hr.mono hρ0 hρr.le, ?_⟩
  intro n
  simpa using hbound n

/-- A more familiar division form of the same estimate.  It is often the
one used when comparing with a scalar radius of convergence. -/
lemma coeff_le_div_of_geometric
    (p : FormalMultilinearSeries ℝ E F) (ρ : ℝ≥0) (C : ℝ)
    (hρ : 0 < ρ)
    (hp : ∀ n : ℕ, ‖p n‖ * (ρ : ℝ)^n ≤ C) (n : ℕ) :
    ‖p n‖ ≤ C / (ρ : ℝ)^n := by
  have hpow : 0 < (ρ : ℝ)^n := by
    positivity
  exact (le_div_iff₀ hpow).2 (hp n)

/-- Conversely it is sometimes convenient to retain a purely nonnegative
coefficient inequality.  Passing to `NNReal` loses no information. -/
lemma nnnorm_le_mul_inv_pow_of_mul_pow
    (p : FormalMultilinearSeries ℝ E F) (ρ A : ℝ≥0)
    (hρ : 0 < ρ)
    (hp : ∀ n : ℕ, ‖p n‖ * (ρ : ℝ)^n ≤ (A:ℝ)) :
    ∀ n : ℕ, ‖p n‖₊ ≤ A * ρ⁻¹ ^ n := by
  intro n
  have hnpos : 0 < (ρ : ℝ)^n := by positivity
  have hle : ‖p n‖ ≤ (A:ℝ) / (ρ:ℝ)^n := (le_div_iff₀ hnpos).2 (hp n)
  -- coerce the statement to reals; all operations here are nonnegative.
  apply NNReal.coe_le_coe.1 ?_ 
  -- wait, `NNReal.coe_le_coe.1` has the direction from reals; easiest is
  -- `exact_mod_cast` after putting both sides in real form.
  simpa [div_eq_mul_inv] using hle


/-- Evaluation estimate for a represented power series with a geometric
coefficient bound.  It is important that the hypothesis is a `HasSum` at
`w`; this lemma is purely an estimate and asserts no convergence on the
boundary of the ball. -/
lemma norm_fpowerSeries_le_geometric
    (p : FormalMultilinearSeries ℝ E F) (ρ : ℝ≥0) (C : ℝ)
    (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hp : ∀ n : ℕ, ‖p n‖ * (ρ : ℝ)^n ≤ C)
    {w : E} (hw : ‖w‖ < (ρ : ℝ)) {a : F}
    (ha : HasSum (fun n : ℕ => p n (fun _ : Fin n => w)) a) :
    ‖a‖ ≤ C / (1 - ‖w‖ / (ρ : ℝ)) := by
  let q : ℝ := ‖w‖ / (ρ : ℝ)
  have hr : 0 < (ρ : ℝ) := by exact_mod_cast hρ
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (norm_nonneg _) (le_of_lt hr)
  have hqlt : q < 1 := (div_lt_one hr).2 hw
  have hqnorm : ‖q‖ < (1:ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hqlt
  have hbnd : ∀ n : ℕ,
      ‖p n (fun _ : Fin n => w)‖ ≤ C * q^n := by
    intro n
    have hpowρ : 0 < (ρ : ℝ)^n := by positivity
    have hcoef : ‖p n‖ ≤ C / (ρ : ℝ)^n :=
      (le_div_iff₀ hpowρ).2 (hp n)
    calc
      ‖p n (fun _ : Fin n => w)‖ ≤
          ‖p n‖ * ∏ _i : Fin n, ‖w‖ :=
        ContinuousMultilinearMap.le_opNorm (p n) _
      _ = ‖p n‖ * ‖w‖^n := by rw [Fin.prod_const]
      _ ≤ (C / (ρ:ℝ)^n) * ‖w‖^n :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = C * q^n := by
        dsimp [q]
        rw [div_pow]
        ring
  have hgeom0 : HasSum (fun n : ℕ => q^n) ((1 - q)⁻¹) :=
    hasSum_geometric_of_norm_lt_one hqnorm
  have hgeom : HasSum (fun n : ℕ => C * q^n) (C * (1 - q)⁻¹) :=
    hgeom0.mul_left C
  calc
    ‖a‖ ≤ C * (1 - q)⁻¹ := ha.norm_le_of_bounded hgeom hbnd
    _ = C / (1 - ‖w‖/(ρ:ℝ)) := by
       simp [q, div_eq_mul_inv]

/-- The half-radius version is often the self-map constant in Picard
estimates. -/
lemma norm_fpowerSeries_le_two_mul
    (p : FormalMultilinearSeries ℝ E F) (ρ : ℝ≥0) (C : ℝ)
    (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hp : ∀ n : ℕ, ‖p n‖ * (ρ : ℝ)^n ≤ C)
    {w : E} (hw : ‖w‖ ≤ (ρ : ℝ) / 2) {a : F}
    (ha : HasSum (fun n : ℕ => p n (fun _ : Fin n => w)) a) :
    ‖a‖ ≤ 2*C := by
  have hr : 0 < (ρ : ℝ) := by exact_mod_cast hρ
  have hwlt : ‖w‖ < (ρ:ℝ) := lt_of_le_of_lt hw (by linarith)
  have hmain := norm_fpowerSeries_le_geometric p ρ C hρ hC hp hwlt ha
  have hq : ‖w‖ / (ρ : ℝ) ≤ (1/2:ℝ) := (div_le_iff₀ hr).2 (by
    nlinarith [hw])
  have hq0 : 0 ≤ ‖w‖ / (ρ:ℝ) := div_nonneg (norm_nonneg _) (le_of_lt hr)
  have hden : 0 < 1 - ‖w‖ / (ρ:ℝ) := by linarith
  calc
    ‖a‖ ≤ C / (1 - ‖w‖ / (ρ:ℝ)) := hmain
    _ ≤ 2*C := by
      have hden2 : (1/2:ℝ) ≤ 1 - ‖w‖ / (ρ:ℝ) := by linarith
      -- multiply by the positive denominator
      apply (div_le_iff₀ hden).2
      nlinarith

end CKSupport

-- END INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/Majorant.lean

-- BEGIN INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/OdeUniqueness.lean
open Set Filter
open scoped Topology
namespace CKSupport
/-- A `C¹` autonomous vector field has unique trajectories on any open time interval,
without a global Lipschitz hypothesis, in a proper normed space.  Mathlib's basic
ODE uniqueness theorem asks for a fixed Lipschitz set; for a given compact piece
of two candidate curves we can take a large closed ball. -/
lemma ode_unique_of_contDiff
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [ProperSpace Y]
    (G : Y → Y) (hG : ContDiff ℝ 1 G)
    (α β : ℝ → Y) (a b t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hα : ∀ t ∈ Set.Ioo a b, HasDerivAt α (G (α t)) t)
    (hβ : ∀ t ∈ Set.Ioo a b, HasDerivAt β (G (β t)) t)
    (heq : α t₀ = β t₀) :
    Set.EqOn α β (Set.Ioo a b) := by
  intro t ht
  -- insert a slightly larger closed interval, to keep both endpoints away
  -- from the ends of the interval where the equation is known
  let A : ℝ := (a + min t t₀) / 2
  let B : ℝ := (max t t₀ + b) / 2
  have hmin : a < min t t₀ := lt_min ht.1 ht₀.1
  have hmax : max t t₀ < b := max_lt ht.2 ht₀.2
  have hA₁ : a < A := by dsimp [A]; linarith
  have hA₂ : A < min t t₀ := by dsimp [A]; linarith
  have hB₁ : max t t₀ < B := by dsimp [B]; linarith
  have hB₂ : B < b := by dsimp [B]; linarith
  have hsub : Set.Icc A B ⊆ Set.Ioo a b := by
    intro s hs
    constructor
    · exact lt_of_lt_of_le hA₁ hs.1
    · exact lt_of_le_of_lt hs.2 hB₂
  have hsub' : Set.Ioo A B ⊆ Set.Ioo a b := by
    intro s hs
    exact hsub ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hctα : ContinuousOn α (Set.Icc A B) := by
    intro s hs
    exact (hα s (hsub hs)).continuousAt.continuousWithinAt
  have hctβ : ContinuousOn β (Set.Icc A B) := by
    intro s hs
    exact (hβ s (hsub hs)).continuousAt.continuousWithinAt
  have hkα : IsCompact (α '' Set.Icc A B) :=
    IsCompact.image_of_continuousOn isCompact_Icc hctα
  have hkβ : IsCompact (β '' Set.Icc A B) :=
    IsCompact.image_of_continuousOn isCompact_Icc hctβ
  have hbdd : Bornology.IsBounded
      ((α '' Set.Icc A B) ∪ (β '' Set.Icc A B)) :=
    hkα.isBounded.union hkβ.isBounded
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : Y)
  -- the closed ball is convex and compact, hence the field is Lipschitz there
  obtain ⟨K, hK⟩ : ∃ K : NNReal, LipschitzOnWith K G (Metric.closedBall (0:Y) R) :=
    ContDiffOn.exists_lipschitzOnWith (s := Metric.closedBall (0:Y) R)
      (hG.contDiffOn) (by norm_num : (1:WithTop ℕ∞) ≠ 0)
      (convex_closedBall _ _) (isCompact_closedBall _ _)
  have ht0' : t₀ ∈ Set.Ioo A B := by
    constructor
    · exact lt_of_lt_of_le hA₂ (min_le_right _ _)
    · exact lt_of_le_of_lt (le_max_right _ _) hB₁
  have ht' : t ∈ Set.Icc A B := by
    constructor
    · exact le_trans (le_of_lt hA₂) (min_le_left _ _)
    · exact le_trans (le_max_left _ _) (le_of_lt hB₁)
  apply (ODE_solution_unique_of_mem_Icc
    (v := fun _ : ℝ => G) (s := fun _ : ℝ => Metric.closedBall (0:Y) R)
    (K := K) (f := α) (g := β) (a:=A) (b:=B) (t₀:=t₀)
    (fun _ _ => hK) ht0' hctα
    (fun s hs => hα s (hsub' hs))
    ?_ hctβ (fun s hs => hβ s (hsub' hs)) ?_ heq) ht'
  · intro s hs
    apply hR
    exact Or.inl ⟨s, ⟨le_of_lt hs.1, le_of_lt hs.2⟩, rfl⟩
  · intro s hs
    apply hR
    exact Or.inr ⟨s, ⟨le_of_lt hs.1, le_of_lt hs.2⟩, rfl⟩


open Classical in
/-- One can make the Picard curves into a *well-defined function* of the initial
point, locally.  No assertion about continuity of this function of two
variables is being made; the analytic-dependence theorem has to prove that
separately.  The last clause is often useful for identifying a constructed
power-series curve with the Picard one. -/
lemma exists_local_flow_unique_of_contDiff
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [CompleteSpace Y] [ProperSpace Y]
    (G : Y → Y) (hG : ContDiff ℝ 1 G) (c : Y) :
    ∃ r > (0:ℝ), ∃ ε > (0:ℝ), ∃ A : Y → ℝ → Y,
      ∀ y ∈ Metric.closedBall c r,
        A y 0 = y ∧
        (∀ t ∈ Set.Ioo (-(ε:ℝ)) ε,
          HasDerivAt (A y) (G (A y t)) t) ∧
        ∀ β : ℝ → Y, β 0 = y →
          (∀ t ∈ Set.Ioo (-(ε:ℝ)) ε,
            HasDerivAt β (G (β t)) t) →
          Set.EqOn (A y) β (Set.Ioo (-(ε:ℝ)) ε) := by
  have hc : ContDiffAt ℝ 1 G c := (contDiff_iff_contDiffAt.mp hG c)
  obtain ⟨r, hr, e, he, H⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
      hc (0:ℝ)
  choose curve hnode Hcurve using H
  -- `curve` is chosen simultaneously.  This packages the pointwise
  -- existence theorem as a genuine two-variable function.
  let A : Y → ℝ → Y := fun y =>
    if h : y ∈ Metric.closedBall c r then curve y h else (fun _ => y)
  refine ⟨r, hr, e, he, A, ?_⟩
  intro y hy
  have hval : A y = curve y hy := by
    dsimp [A]
    split
    · congr 1
    · rename_i bad
      exact False.elim (bad hy)
  have h0 : A y 0 = y := by rw [hval]; exact hnode y hy
  refine ⟨h0, ?_, ?_⟩
  · intro t ht
    -- the library interval is `(0-e,0+e)`
    rw [hval]
    exact Hcurve y hy t (by simpa using ht)
  · intro β hβ0 hβ
    apply ode_unique_of_contDiff (Y:=Y) G hG (A y) β (-e) e 0
      (by constructor <;> linarith)
    · intro t ht
      rw [hval]
      exact Hcurve y hy t (by simpa using ht)
    · intro t ht
      exact hβ t ht
    · calc
        A y 0 = y := h0
        _ = β 0 := hβ0.symm
end CKSupport

-- END INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/OdeUniqueness.lean

-- BEGIN INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/LocalFlow.lean
open Set Filter
open scoped Topology
namespace CKSupport
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/- Elementary lemmas for passing from a (displacement) flow germ to the
finite-dimensional characteristic chart.  Keeping the displacement centred at
`(x₀,0,u₀ x₀)` makes the inverse-function derivative triangular. -/

variable (u0 : X → ℝ) (x0 : X)

/-- insert the analytic initial graph, in displacement coordinates -/
def initDisp (x : X) : X × ℝ × ℝ := initialPoint u0 x - initialPoint u0 x0

/-- insert graph-displacement and time -/
def initPar (y : X × ℝ) : (X × ℝ × ℝ) × ℝ := (initDisp u0 x0 y.1, y.2)

@[simp] lemma initDisp_self : initDisp u0 x0 x0 = 0 := by
  simp [initDisp]
@[simp] lemma initPar_self : initPar u0 x0 (x0, (0:ℝ)) = 0 := by
  simp [initPar]

lemma analyticAt_initDisp {x : X} (hu : AnalyticAt ℝ u0 x) (c : X) :
    AnalyticAt ℝ (initDisp u0 c) x := by
  -- graph is `(x,(0,u₀ x))`
  have hgraph : AnalyticAt ℝ (fun x : X => (x, (0:ℝ), u0 x)) x :=
    (show AnalyticAt ℝ (fun x : X => x) x from (by change AnalyticAt ℝ id x; exact analyticAt_id)).prod
      ((analyticAt_const : AnalyticAt ℝ (fun _ : X => (0:ℝ)) x).prod hu)
  change AnalyticAt ℝ (fun t : X =>
    (t, (0:ℝ), u0 t) - (c,(0:ℝ),u0 c)) x
  convert hgraph.sub (analyticAt_const :
      AnalyticAt ℝ (fun _ : X => initialPoint u0 c) x) using 1
  ext t <;> rfl


lemma analyticAt_initPar {y : X×ℝ} (hu : AnalyticAt ℝ u0 y.1) (c : X) :
    AnalyticAt ℝ (initPar u0 c) y := by
  have hq : AnalyticAt ℝ (fun y : X × ℝ => initDisp u0 c y.1) y :=
    (analyticAt_initDisp (u0:=u0) (x:=y.1) hu c).comp analyticAt_fst
  exact hq.prod analyticAt_snd

variable {u0 x0}

/-- A graph-displacement flow, its projection and height. -/
def graphFlow (B : ((X × ℝ × ℝ) × ℝ) → (X × ℝ × ℝ))
    (u0 : X → ℝ) (x0 : X) (y : X × ℝ) : X × ℝ × ℝ :=
  initialPoint u0 x0 + B (initPar u0 x0 y)

def graphPhi (B : ((X × ℝ × ℝ) × ℝ) → (X × ℝ × ℝ))
    (u0 : X → ℝ) (x0 : X) (y : X × ℝ) : X × ℝ :=
  ((graphFlow B u0 x0 y).1, (graphFlow B u0 x0 y).2.1)

def graphZ (B : ((X × ℝ × ℝ) × ℝ) → (X × ℝ × ℝ))
    (u0 : X → ℝ) (x0 : X) (y : X × ℝ) : ℝ :=
  (graphFlow B u0 x0 y).2.2

@[simp] lemma graphFlow_zero (B : ((X × ℝ × ℝ) × ℝ) → (X × ℝ × ℝ))
    (hB : ∀ q, B (q,0) = q) (x : X) :
    graphFlow B u0 x0 (x,0) = initialPoint u0 x := by
  dsimp [graphFlow, initPar]
  rw [hB]
  simp [initDisp]
@[simp] lemma graphPhi_zero (B : ((X × ℝ × ℝ) × ℝ) → (X × ℝ × ℝ))
    (hB : ∀ q, B (q,0) = q) (x : X) :
    graphPhi B u0 x0 (x,0) = (x,0) := by
  simp [graphPhi, graphFlow_zero (u0:=u0) (x0:=x0) B hB,
    initialPoint]
@[simp] lemma graphZ_zero (B : ((X × ℝ × ℝ) × ℝ) → (X × ℝ × ℝ))
    (hB : ∀ q, B (q,0) = q) (x : X) :
    graphZ B u0 x0 (x,0) = u0 x := by
  simp [graphZ, graphFlow_zero (u0:=u0) (x0:=x0) B hB,
    initialPoint]

/- A continuously linear triangular shear; using a genuine equivalence avoids
norm estimates in applying the inverse function theorem. -/
variable [FiniteDimensional ℝ X]

def shearLinear (a : X) : (X × ℝ) ≃ₗ[ℝ] (X × ℝ) :=
{ toFun := fun z => (z.1 - z.2 • a, z.2)
  invFun := fun z => (z.1 + z.2 • a, z.2)
  map_add' := by
    intro v w; ext <;> dsimp
    simp [add_smul]
    <;> try abel
  map_smul' := by
    intro r v; ext <;> dsimp
    simp [mul_smul, smul_sub]
  left_inv := by
    intro v; ext <;> dsimp
    abel
  right_inv := by
    intro v; ext <;> dsimp
    abel }

noncomputable def shear (a : X) : (X × ℝ) ≃L[ℝ] (X × ℝ) :=
  (shearLinear a).toContinuousLinearEquiv

@[simp] lemma shear_apply (a : X) (z : X × ℝ) :
    (shear a) z = (z.1 - z.2 • a, z.2) := rfl

/- Derivatives along the two distinguished types of tangent vector.  These are
stated for an arbitrary differentiability point; at the centre only the time
vector-field value is needed. -/

end CKSupport

namespace CKSupport
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma fderiv_initPar_time {u0 : X → ℝ} {x0:X} {y:X×ℝ}
    (hu : AnalyticAt ℝ u0 y.1) :
    fderiv ℝ (initPar u0 x0) y ((0:X),(1:ℝ)) =
       ((0 : X × ℝ × ℝ),(1:ℝ)) := by
  have ha : AnalyticAt ℝ (initDisp u0 x0) y.1 :=
    analyticAt_initDisp u0 hu x0
  have haq : DifferentiableAt ℝ (initDisp u0 x0) y.1 := ha.differentiableAt
  have hq : DifferentiableAt ℝ (fun z : X × ℝ => initDisp u0 x0 z.1) y :=
    haq.comp y differentiableAt_fst
  have hqf : fderiv ℝ (fun z : X × ℝ => initDisp u0 x0 z.1) y ((0:X),(1:ℝ)) = 0 := by
    have hc := fderiv_comp y haq differentiableAt_fst
    change fderiv ℝ ((initDisp u0 x0) ∘ (fun z : X×ℝ => z.1)) y _ = _
    rw [hc, fderiv_fst]
    simp
  have hs : DifferentiableAt ℝ (fun z : X × ℝ => z.2) y := differentiableAt_snd
  have hprod := hq.fderiv_prodMk hs
  change fderiv ℝ (fun z : X × ℝ =>
    ((fun z : X × ℝ => initDisp u0 x0 z.1) z, z.2)) y _ = _
  rw [hprod]
  change (_, _) = _
  simp [hqf, fderiv_snd]

lemma fderiv_initPar_space_base {u0 : X → ℝ} {x0:X}
    (hu : AnalyticAt ℝ u0 x0) (v:X) :
    (fderiv ℝ (initPar u0 x0) (x0,(0:ℝ)) (v,(0:ℝ))).1.1 = v ∧
    (fderiv ℝ (initPar u0 x0) (x0,(0:ℝ)) (v,(0:ℝ))).2 = 0 := by
  have ha : AnalyticAt ℝ (initDisp u0 x0) x0 := analyticAt_initDisp u0 hu x0
  have haq := ha.differentiableAt
  have hq : DifferentiableAt ℝ (fun z : X × ℝ => initDisp u0 x0 z.1)
      (x0,(0:ℝ)) := by
        change DifferentiableAt ℝ ((initDisp u0 x0) ∘ (fun z : X×ℝ => z.1)) _
        exact haq.comp (x0,(0:ℝ)) differentiableAt_fst
  have hs : DifferentiableAt ℝ (fun z : X × ℝ => z.2) (x0,(0:ℝ)) :=
    differentiableAt_snd
  have hprod := hq.fderiv_prodMk hs
  -- derivative of `initDisp` has first projection identity
  have hfirst : ∀ v:X, (fderiv ℝ (initDisp u0 x0) x0 v).1 = v := by
    intro w
    -- first projection composed with the graph is the identity
    have heq : (fun x:X => (initDisp u0 x0 x).1) =
        (fun x:X => x - x0) := by
      funext x; simp [initDisp, initialPoint]
    have hc := fderiv_comp x0 differentiableAt_fst haq
    -- extract the evaluation
    have H : ( (ContinuousLinearMap.fst ℝ X (ℝ×ℝ)) ∘L
          fderiv ℝ (initDisp u0 x0) x0) =
          (ContinuousLinearMap.id ℝ X) := by
      calc
        _ = fderiv ℝ ((fun z : X × ℝ × ℝ => z.1) ∘ initDisp u0 x0) x0 := by
              rw [hc, fderiv_fst]
        _ = fderiv ℝ (fun x : X => x - x0) x0 := by
              congr 1
        _ = (ContinuousLinearMap.id ℝ X) := by
              simpa using (fderiv_sub_const (𝕜:=ℝ) (f:= fun x:X => x) x0 (x:=x0))
    have h := congrArg (fun L : X →L[ℝ] X => L w) H
    simpa using h
  change _ ∧ _
  change (fderiv ℝ (fun z : X × ℝ =>
    ((fun z : X × ℝ => initDisp u0 x0 z.1) z, z.2)) _ _).1.1 = _ ∧
    (fderiv ℝ (fun z : X × ℝ =>
    ((fun z : X × ℝ => initDisp u0 x0 z.1) z, z.2)) _ _).2 = _
  rw [hprod]
  change ((fderiv ℝ (fun z : X × ℝ => initDisp u0 x0 z.1)
        (x0,0) (v,0)).1 = v) ∧
     (fderiv ℝ (fun z : X × ℝ => z.2) (x0,0) (v,0) = 0)
  constructor
  · have hc := fderiv_comp (𝕜:=ℝ) (f:=fun z : X × ℝ => z.1)
        (g:= initDisp u0 x0) (x0,(0:ℝ)) haq differentiableAt_fst
    change fderiv ℝ ((initDisp u0 x0) ∘ (fun z : X×ℝ => z.1)) _ = _ at hc
    -- rewrite our term by chain rule
    change ((fderiv ℝ ((initDisp u0 x0) ∘ (fun z : X×ℝ => z.1))
      (x0,(0:ℝ)) (v,0)).1 = v)
    rw [hc, fderiv_fst]
    change (fderiv ℝ (initDisp u0 x0) x0 v).1 = v
    exact hfirst v
  · simp [fderiv_snd]
end CKSupport
namespace CKSupport
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {B : ((X × ℝ × ℝ) × ℝ) → (X × ℝ × ℝ)}
lemma fderiv_B_space0 (hB0 : ∀ q : X × ℝ × ℝ, B (q,0)=q)
    (hd : DifferentiableAt ℝ B (0 : (X × ℝ × ℝ) × ℝ))
    (w : X × ℝ × ℝ) :
    fderiv ℝ B (0 : (X × ℝ × ℝ) × ℝ) (w,0) = w := by
  let inj : (X × ℝ × ℝ) → ((X × ℝ × ℝ) × ℝ) := fun q => (q,0)
  have hi : DifferentiableAt ℝ inj 0 :=
    (differentiableAt_id.prodMk (differentiableAt_const (c:=(0:ℝ))))
  have hc := fderiv_comp (0 : X × ℝ × ℝ) hd hi
  have heq : B ∘ inj = id := by funext q; exact hB0 q
  have hf : fderiv ℝ (B ∘ inj) (0 : X × ℝ × ℝ) =
       ContinuousLinearMap.id ℝ (X × ℝ × ℝ) := by rw [heq, fderiv_id]
  rw [hf] at hc
  have hv := congrArg (fun L : (X × ℝ × ℝ) →L[ℝ] (X × ℝ × ℝ) => L w) hc
  change w = fderiv ℝ B (0 : (X × ℝ × ℝ) × ℝ)
    (fderiv ℝ inj 0 w) at hv
  have hinj : fderiv ℝ inj 0 w = (w,0) := by
    have hprod := (differentiableAt_id (𝕜:=ℝ) (x:= (0:X×ℝ×ℝ))).fderiv_prodMk
      (differentiableAt_const (c:=(0:ℝ)) (x:=(0:X×ℝ×ℝ)))
    change fderiv ℝ inj 0 = _ at hprod
    rw [hprod, fderiv_id]
    simp
  rw [hinj] at hv
  exact hv.symm
end CKSupport
namespace CKSupport
open Classical
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- The bit of the analytic inverse theorem most useful for a flow germ.  Only
analyticity at the centre is needed. Shrinking afterwards gives both maps
analytic on genuine open sets; no false global `ContDiff` upgrade is used. -/
lemma analytic_local_inverse_germ
    (P : T → T) (a : T) (i : T ≃L[ℝ] T)
    (ha : AnalyticAt ℝ P a) (hlin : fderiv ℝ P a = (i : T →L[ℝ] T)) :
    ∃ H : OpenPartialHomeomorph T T,
      (H : T → T) = P ∧ a ∈ H.source ∧ H a = P a ∧
      (∃ s ∈ 𝓝 a, IsOpen s ∧ s ⊆ H.source ∧ AnalyticOnNhd ℝ P s) ∧
      (∃ t ∈ 𝓝 (P a), IsOpen t ∧ t ⊆ H.target ∧
            AnalyticOnNhd ℝ (H.symm : T → T) t) := by
  let hs : HasStrictFDerivAt P (i : T →L[ℝ] T) a := by
    rw [← hlin]
    exact ha.hasStrictFDerivAt
  let H : OpenPartialHomeomorph T T := hs.toOpenPartialHomeomorph P
  have hco : (H : T → T) = P :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe hs
  have hmem : a ∈ H.source := hs.mem_toOpenPartialHomeomorph_source
  have htmem : P a ∈ H.target := by simpa [hco] using H.map_source hmem
  have hac := ha
  obtain ⟨p, hp⟩ := hac
  have hp' : HasFPowerSeriesAt (H : T → T) p a := by simpa [hco] using hp
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℝ T T).symm
       (i : T →L[ℝ] T) := by
    apply (continuousMultilinearCurryFin1 ℝ T T).injective
    have hh := hp.fderiv_eq
    rw [hlin] at hh
    simpa using hh.symm
  have hinv : HasFPowerSeriesAt (H.symm : T → T) (p.leftInv i a) (H a) :=
    H.hasFPowerSeriesAt_symm hmem hp' hp1
  have hainv : AnalyticAt ℝ (H.symm : T → T) (P a) := by
    simpa [hco] using hinv.analyticAt
  -- open subsets consisting solely of analytic points, intersected with the
  -- inverse-homeomorphism source/target
  let s : Set T := H.source ∩ {x | AnalyticAt ℝ P x}
  have hsopen : IsOpen s := H.open_source.inter (isOpen_analyticAt ℝ P)
  have hsa : a ∈ s := ⟨hmem, ha⟩
  have hsnh : s ∈ 𝓝 a := hsopen.mem_nhds hsa
  let t : Set T := H.target ∩ {x | AnalyticAt ℝ (H.symm : T → T) x}
  have htopen : IsOpen t := H.open_target.inter
      (isOpen_analyticAt ℝ (H.symm : T → T))
  have hta : P a ∈ t := ⟨htmem, hainv⟩
  refine ⟨H, hco, hmem, ?_, ⟨s, hsnh, hsopen,
      (inter_subset_left), ?_⟩,
      ⟨t, htopen.mem_nhds hta, htopen, inter_subset_left, ?_⟩⟩
  · simp [hco]
  · intro z hz; exact hz.2
  · intro z hz; exact hz.2
end CKSupport
namespace CKSupport
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {B : ((X × ℝ × ℝ) × ℝ) → (X × ℝ × ℝ)} {u0 : X → ℝ} {x0 : X}
lemma analyticAt_graphFlow_base
    (hu : AnalyticAt ℝ u0 x0)
    (hB : AnalyticAt ℝ B (0 : ((X × ℝ × ℝ) × ℝ))) :
    AnalyticAt ℝ (graphFlow B u0 x0) (x0,(0:ℝ)) := by
  have hq : AnalyticAt ℝ (initPar u0 x0) (x0,(0:ℝ)) :=
    analyticAt_initPar (u0:=u0) hu x0
  have hb' : AnalyticAt ℝ (B ∘ initPar u0 x0) (x0,(0:ℝ)) := by
    exact (by simpa using hB : AnalyticAt ℝ B (initPar u0 x0 (x0,0))).comp hq
  have hc : AnalyticAt ℝ
      (fun _ : X×ℝ => initialPoint u0 x0) (x0,(0:ℝ)) := analyticAt_const
  convert hc.add hb' using 1
  funext y <;> rfl
lemma analyticAt_graphPhi_base
    (hu : AnalyticAt ℝ u0 x0)
    (hB : AnalyticAt ℝ B (0 : ((X × ℝ × ℝ) × ℝ))) :
    AnalyticAt ℝ (graphPhi B u0 x0) (x0,(0:ℝ)) := by
  have h := analyticAt_graphFlow_base (B:=B) hu hB
  exact (analyticAt_fst.comp h).prod (analyticAt_fst.comp (analyticAt_snd.comp h))
lemma analyticAt_graphZ_base
    (hu : AnalyticAt ℝ u0 x0)
    (hB : AnalyticAt ℝ B (0 : ((X × ℝ × ℝ) × ℝ))) :
    AnalyticAt ℝ (graphZ B u0 x0) (x0,(0:ℝ)) :=
  analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_graphFlow_base (B:=B) hu hB))
end CKSupport

namespace CKSupport
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {B : ((X × ℝ × ℝ) × ℝ) → (X × ℝ × ℝ)} {u0 : X → ℝ} {x0 : X}

/-- Analyticity of the graph flow at any point where the displacement series is analytic. -/
lemma analyticAt_graphFlow
    {y : X × ℝ}
    (hu : AnalyticAt ℝ u0 y.1)
    (hB : AnalyticAt ℝ B (initPar u0 x0 y)) :
    AnalyticAt ℝ (graphFlow B u0 x0) y := by
  have hq : AnalyticAt ℝ (initPar u0 x0) y :=
    analyticAt_initPar (u0:=u0) hu x0
  have hb' : AnalyticAt ℝ (B ∘ initPar u0 x0) y := hB.comp hq
  have hc : AnalyticAt ℝ
      (fun _ : X×ℝ => initialPoint u0 x0) y := analyticAt_const
  convert hc.add hb' using 1
  funext z <;> rfl

lemma analyticAt_graphPhi
    {y : X × ℝ}
    (hu : AnalyticAt ℝ u0 y.1)
    (hB : AnalyticAt ℝ B (initPar u0 x0 y)) :
    AnalyticAt ℝ (graphPhi B u0 x0) y := by
  have h := analyticAt_graphFlow (B:=B) hu hB
  exact (analyticAt_fst.comp h).prod (analyticAt_fst.comp (analyticAt_snd.comp h))

lemma analyticAt_graphZ
    {y : X × ℝ}
    (hu : AnalyticAt ℝ u0 y.1)
    (hB : AnalyticAt ℝ B (initPar u0 x0 y)) :
    AnalyticAt ℝ (graphZ B u0 x0) y :=
  analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_graphFlow (B:=B) hu hB))

/-- derivative of the graph flow on the time vector.  The graph-displacement
has no time input, so only the second slot of `B` survives. -/
lemma fderiv_graphFlow_time
    {y : X × ℝ}
    (hu : AnalyticAt ℝ u0 y.1)
    (hB : DifferentiableAt ℝ B (initPar u0 x0 y)) :
    fderiv ℝ (graphFlow B u0 x0) y ((0:X),(1:ℝ)) =
      fderiv ℝ B (initPar u0 x0 y) ((0 : X × ℝ × ℝ),(1:ℝ)) := by
  have hqA : AnalyticAt ℝ (initPar u0 x0) y := analyticAt_initPar (u0:=u0) hu x0
  have hq := hqA.differentiableAt
  have hcomp := fderiv_comp y hB hq
  have hc : fderiv ℝ (fun z : X×ℝ =>
      initialPoint u0 x0 + B (initPar u0 x0 z)) y =
      fderiv ℝ (B ∘ initPar u0 x0) y := by
    -- derivative of a constant plus a map
    simpa using (fderiv_const_add (𝕜:=ℝ)
      (f:= B ∘ initPar u0 x0) (x:=y) (initialPoint u0 x0))
  change fderiv ℝ (fun z : X×ℝ =>
      initialPoint u0 x0 + B (initPar u0 x0 z)) y _ = _
  rw [hc, hcomp]
  change fderiv ℝ B (initPar u0 x0 y)
      (fderiv ℝ (initPar u0 x0) y ((0:X),(1:ℝ))) = _
  rw [fderiv_initPar_time hu]

lemma fderiv_graphPhi_time
    {y : X × ℝ}
    (hu : AnalyticAt ℝ u0 y.1)
    (hB : AnalyticAt ℝ B (initPar u0 x0 y)) :
    fderiv ℝ (graphPhi B u0 x0) y ((0:X),(1:ℝ)) =
      ((fderiv ℝ B (initPar u0 x0 y) ((0 : X × ℝ × ℝ),(1:ℝ))).1,
       (fderiv ℝ B (initPar u0 x0 y) ((0 : X × ℝ × ℝ),(1:ℝ))).2.1) := by
  have hflow : DifferentiableAt ℝ (graphFlow B u0 x0) y :=
    (analyticAt_graphFlow (B:=B) hu hB).differentiableAt
  -- projection map from `X×ℝ×ℝ`
  let pr : (X × ℝ × ℝ) → (X × ℝ) := fun w => (w.1, w.2.1)
  have hpr : Differentiable ℝ pr := by
    fun_prop
  have hchain := fderiv_comp y (hpr (graphFlow B u0 x0 y)) hflow
  change fderiv ℝ (graphPhi B u0 x0) y _ = _
  have hfun : graphPhi B u0 x0 = pr ∘ graphFlow B u0 x0 := by rfl
  rw [hfun, hchain]
  change fderiv ℝ pr (graphFlow B u0 x0 y)
    (fderiv ℝ (graphFlow B u0 x0) y ((0:X),(1:ℝ))) = _
  rw [fderiv_graphFlow_time hu hB.differentiableAt]
  -- derivative of the two projections
  have h1 : DifferentiableAt ℝ (fun w : X × ℝ × ℝ => w.1)
      (graphFlow B u0 x0 y) := differentiableAt_fst
  have h2 : DifferentiableAt ℝ (fun w : X × ℝ × ℝ => w.2.1)
      (graphFlow B u0 x0 y) := differentiableAt_fst.comp _ differentiableAt_snd
  rw [DifferentiableAt.fderiv_prodMk h1 h2]
  have h21 : fderiv ℝ (fun w : X × ℝ × ℝ => w.2.1)
       (graphFlow B u0 x0 y) =
       (ContinuousLinearMap.fst ℝ ℝ ℝ) ∘L
         (ContinuousLinearMap.snd ℝ X (ℝ×ℝ)) := by
    change fderiv ℝ ((fun z : ℝ×ℝ => z.1) ∘
       (fun w : X × ℝ × ℝ => w.2)) (graphFlow B u0 x0 y) = _
    rw [fderiv_comp (graphFlow B u0 x0 y)
      (differentiableAt_fst) (differentiableAt_snd)]
    rw [fderiv_fst, fderiv_snd]
  rw [fderiv_fst, h21]
  simp

lemma fderiv_graphZ_time
    {y : X × ℝ}
    (hu : AnalyticAt ℝ u0 y.1)
    (hB : AnalyticAt ℝ B (initPar u0 x0 y)) :
    fderiv ℝ (graphZ B u0 x0) y ((0:X),(1:ℝ)) =
       (fderiv ℝ B (initPar u0 x0 y) ((0 : X × ℝ × ℝ),(1:ℝ))).2.2 := by
  have hflow : DifferentiableAt ℝ (graphFlow B u0 x0) y :=
    (analyticAt_graphFlow (B:=B) hu hB).differentiableAt
  let pr : (X × ℝ × ℝ) → ℝ := fun w => w.2.2
  have hpr : Differentiable ℝ pr := by fun_prop
  have hchain := fderiv_comp y (hpr (graphFlow B u0 x0 y)) hflow
  change fderiv ℝ (graphZ B u0 x0) y _ = _
  have hfun : graphZ B u0 x0 = pr ∘ graphFlow B u0 x0 := by rfl
  rw [hfun, hchain]
  change fderiv ℝ pr (graphFlow B u0 x0 y)
    (fderiv ℝ (graphFlow B u0 x0) y ((0:X),(1:ℝ))) = _
  rw [fderiv_graphFlow_time hu hB.differentiableAt]
  have h21 : fderiv ℝ (fun w : X × ℝ × ℝ => w.2.2)
       (graphFlow B u0 x0 y) =
       (ContinuousLinearMap.snd ℝ ℝ ℝ) ∘L
         (ContinuousLinearMap.snd ℝ X (ℝ×ℝ)) := by
    change fderiv ℝ ((fun z : ℝ×ℝ => z.2) ∘
       (fun w : X × ℝ × ℝ => w.2)) (graphFlow B u0 x0 y) = _
    rw [fderiv_comp (graphFlow B u0 x0 y)
      differentiableAt_snd differentiableAt_snd]
    rw [fderiv_snd, fderiv_snd]
  change fderiv ℝ (fun w : X × ℝ × ℝ => w.2.2)
     (graphFlow B u0 x0 y) _ = _
  rw [h21]
  simp
end CKSupport

namespace CKSupport
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma fderiv_initPar_space_middle_base {u0 : X → ℝ} {x0:X}
    (hu : AnalyticAt ℝ u0 x0) (v:X) :
    (fderiv ℝ (initPar u0 x0) (x0,(0:ℝ)) (v,(0:ℝ))).1.2.1 = 0 := by
  have haq : DifferentiableAt ℝ (initDisp u0 x0) x0 :=
    (analyticAt_initDisp u0 hu x0).differentiableAt
  have hp : DifferentiableAt ℝ (fun z : X × ℝ × ℝ => z.2.1)
       (initDisp u0 x0 x0) :=
    differentiableAt_fst.comp _ differentiableAt_snd
  have hpr : fderiv ℝ (fun z : X × ℝ × ℝ => z.2.1)
       (initDisp u0 x0 x0) =
       (ContinuousLinearMap.fst ℝ ℝ ℝ) ∘L
          (ContinuousLinearMap.snd ℝ X (ℝ×ℝ)) := by
    change fderiv ℝ ((fun w : ℝ×ℝ => w.1) ∘
       (fun z : X×ℝ×ℝ => z.2)) (initDisp u0 x0 x0) = _
    rw [fderiv_comp (initDisp u0 x0 x0)
       differentiableAt_fst differentiableAt_snd,
       fderiv_fst, fderiv_snd]
  have hc := fderiv_comp x0 hp haq
  change fderiv ℝ ((fun z : X × ℝ × ℝ => z.2.1) ∘ initDisp u0 x0) x0 = _ at hc
  have hconst : ((fun z : X × ℝ × ℝ => z.2.1) ∘ initDisp u0 x0) =
       (fun _ : X => (0:ℝ)) := by
    funext x; simp [initDisp, initialPoint]
  rw [hconst] at hc
  have hmid : (fderiv ℝ (initDisp u0 x0) x0 v).2.1 = 0 := by
    have hv := congrArg (fun L : X →L[ℝ] ℝ => L v) hc
    -- left side is derivative of a constant, right side the projected vector
    have hzero : fderiv ℝ (fun _ : X => (0:ℝ)) x0 = 0 := by
      simpa using congrArg (fun H => H x0)
        (fderiv_const (𝕜:=ℝ) (E:=X) (c:=(0:ℝ)))
    rw [hzero, hpr] at hv
    simpa using hv.symm
  have hq : DifferentiableAt ℝ ((initDisp u0 x0) ∘
       (fun z : X × ℝ => z.1)) (x0,(0:ℝ)) :=
     haq.comp (x0,(0:ℝ)) differentiableAt_fst
  have hprod := hq.fderiv_prodMk
       (differentiableAt_snd : DifferentiableAt ℝ
         (fun z : X×ℝ => z.2) (x0,(0:ℝ)))
  change fderiv ℝ (initPar u0 x0) (x0,(0:ℝ)) _ |>.1.2.1 = _
  change fderiv ℝ (fun z : X × ℝ =>
     (initDisp u0 x0 z.1, z.2)) (x0,(0:ℝ)) _ |>.1.2.1 = _
  change (fderiv ℝ (fun z : X × ℝ =>
     (((initDisp u0 x0) ∘ (fun z : X×ℝ => z.1)) z, z.2))
      (x0,(0:ℝ)) _ |>.1.2.1) = _
  rw [hprod]
  change (fderiv ℝ (fun z : X × ℝ => initDisp u0 x0 z.1)
       (x0,(0:ℝ)) (v,0)).2.1 = 0
  have hcomp := fderiv_comp (𝕜:=ℝ)
       (f:= fun z : X×ℝ => z.1) (g:= initDisp u0 x0)
       (x0,(0:ℝ)) haq differentiableAt_fst
  change fderiv ℝ ((initDisp u0 x0) ∘ (fun z : X×ℝ => z.1)) _ = _ at hcomp
  change (fderiv ℝ ((initDisp u0 x0) ∘ (fun z : X×ℝ => z.1))
     (x0,(0:ℝ)) (v,0)).2.1 = 0
  rw [hcomp, fderiv_fst]
  change (fderiv ℝ (initDisp u0 x0) x0 v).2.1 = 0
  exact hmid
end CKSupport

namespace CKSupport
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {B : ((X × ℝ × ℝ) × ℝ) → (X × ℝ × ℝ)} {u0 : X → ℝ} {x0 : X}

lemma fderiv_graphFlow_apply
    {y : X × ℝ}
    (hu : AnalyticAt ℝ u0 y.1)
    (hB : DifferentiableAt ℝ B (initPar u0 x0 y)) (v : X×ℝ) :
    fderiv ℝ (graphFlow B u0 x0) y v =
      fderiv ℝ B (initPar u0 x0 y)
        (fderiv ℝ (initPar u0 x0) y v) := by
  have hq := (analyticAt_initPar (u0:=u0) hu x0).differentiableAt
  change fderiv ℝ (fun z : X×ℝ =>
      initialPoint u0 x0 + B (initPar u0 x0 z)) y v = _
  change (fderiv ℝ (fun z : X×ℝ =>
      initialPoint u0 x0 + ((B ∘ initPar u0 x0) z)) y) v = _
  rw [fderiv_const_add (𝕜:=ℝ) (f:= B ∘ initPar u0 x0)
      (x:=y) (initialPoint u0 x0)]
  rw [fderiv_comp y hB hq]
  rfl

lemma fderiv_graphPhi_apply
    {y : X × ℝ}
    (hu : AnalyticAt ℝ u0 y.1)
    (hB : AnalyticAt ℝ B (initPar u0 x0 y)) (v : X×ℝ) :
    fderiv ℝ (graphPhi B u0 x0) y v =
      ((fderiv ℝ B (initPar u0 x0 y) (fderiv ℝ (initPar u0 x0) y v)).1,
       (fderiv ℝ B (initPar u0 x0 y) (fderiv ℝ (initPar u0 x0) y v)).2.1) := by
  have hflow : DifferentiableAt ℝ (graphFlow B u0 x0) y :=
    (analyticAt_graphFlow (B:=B) hu hB).differentiableAt
  let pr : (X × ℝ × ℝ) → (X × ℝ) := fun w => (w.1, w.2.1)
  have hpr : Differentiable ℝ pr := by fun_prop
  have hchain := fderiv_comp y (hpr (graphFlow B u0 x0 y)) hflow
  change fderiv ℝ (graphPhi B u0 x0) y v = _
  have hfun : graphPhi B u0 x0 = pr ∘ graphFlow B u0 x0 := by rfl
  rw [hfun, hchain]
  change fderiv ℝ pr (graphFlow B u0 x0 y)
    (fderiv ℝ (graphFlow B u0 x0) y v) = _
  rw [fderiv_graphFlow_apply hu hB.differentiableAt v]
  have h1 : DifferentiableAt ℝ (fun w : X × ℝ × ℝ => w.1)
      (graphFlow B u0 x0 y) := differentiableAt_fst
  have h2 : DifferentiableAt ℝ (fun w : X × ℝ × ℝ => w.2.1)
      (graphFlow B u0 x0 y) := differentiableAt_fst.comp _ differentiableAt_snd
  rw [DifferentiableAt.fderiv_prodMk h1 h2]
  have h21 : fderiv ℝ (fun w : X × ℝ × ℝ => w.2.1)
       (graphFlow B u0 x0 y) =
       (ContinuousLinearMap.fst ℝ ℝ ℝ) ∘L
         (ContinuousLinearMap.snd ℝ X (ℝ×ℝ)) := by
    change fderiv ℝ ((fun z : ℝ×ℝ => z.1) ∘
       (fun w : X × ℝ × ℝ => w.2)) (graphFlow B u0 x0 y) = _
    rw [fderiv_comp (graphFlow B u0 x0 y)
      (differentiableAt_fst) (differentiableAt_snd)]
    rw [fderiv_fst, fderiv_snd]
  rw [fderiv_fst, h21]
  simp

/-- The derivative of the graph projection at the initial point is the
characteristic triangular shear.  Only the time value of the displacement
vector field is used. -/
lemma fderiv_graphPhi_base_eq_shear
    [FiniteDimensional ℝ X]
    {a : X} {gval : ℝ}
    (hu : AnalyticAt ℝ u0 x0)
    (hB : AnalyticAt ℝ B (0 : ((X × ℝ × ℝ) × ℝ)))
    (hB0 : ∀ q : X × ℝ × ℝ, B (q,0) = q)
    (ht : fderiv ℝ B (0 : ((X × ℝ × ℝ) × ℝ))
          ((0 : X × ℝ × ℝ),(1:ℝ)) =
          ((-a,(1:ℝ),gval) : X × ℝ × ℝ)) :
    fderiv ℝ (graphPhi B u0 x0) (x0,(0:ℝ)) =
      (shear a : (X×ℝ) →L[ℝ] (X×ℝ)) := by
  apply ContinuousLinearMap.ext (fun v : X×ℝ => ?_)
  have hinit : initPar u0 x0 (x0,(0:ℝ)) = 0 := initPar_self _ _
  have hAtB : AnalyticAt ℝ B (initPar u0 x0 (x0,(0:ℝ))) := by
    simpa [hinit] using hB
  have hspace : ∀ w : X,
       fderiv ℝ (graphPhi B u0 x0) (x0,(0:ℝ)) (w,(0:ℝ)) =
         (w,(0:ℝ)) := by
    intro w
    rw [fderiv_graphPhi_apply (B:=B) hu hAtB]
    rw [hinit]
    let z := fderiv ℝ (initPar u0 x0) (x0,(0:ℝ)) (w,(0:ℝ))
    have hz1 : z.1.1 = w := (fderiv_initPar_space_base hu w).1
    have hzmid : z.1.2.1 = 0 := fderiv_initPar_space_middle_base hu w
    have hz2 : z.2 = 0 := (fderiv_initPar_space_base hu w).2
    have hzeq : z = (z.1,(0:ℝ)) := by ext <;> simp [hz2]
    change ((fderiv ℝ B 0 z).1, (fderiv ℝ B 0 z).2.1) = _
    rw [hzeq, fderiv_B_space0 hB0 hB.differentiableAt]
    change (z.1.1, z.1.2.1) = _
    rw [hz1, hzmid]
  have htime : fderiv ℝ (graphPhi B u0 x0) (x0,(0:ℝ))
        ((0:X),(1:ℝ)) = ((-a),(1:ℝ)) := by
    rw [fderiv_graphPhi_apply (B:=B) hu hAtB]
    rw [hinit]
    rw [fderiv_initPar_time hu]
    rw [ht]
  have hv : v = ((v.1,(0:ℝ)) : X×ℝ) + v.2 • ((0:X),(1:ℝ)) := by
    ext <;> simp
  rw [hv, map_add, map_smul, hspace, htime]
  simp [shear_apply, sub_eq_add_neg]

end CKSupport

-- END INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/LocalFlow.lean

-- BEGIN INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/OdeMajorantBasic.lean
open Set Filter
open scoped BigOperators ENNReal NNReal Topology
namespace CKSupport
noncomputable section
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- An elementary coefficientwise estimate for formal composition.  Unlike
`le_comp_radius_of_summable` this does not presuppose a radius for the
inside series; it is a finite estimate at each degree. -/
lemma comp_coeff_norm_le_sum (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) (n : ℕ) :
    ‖(q.comp p) n‖ ≤
      ∑ c : Composition n, ‖q c.length‖ * ∏ i, ‖p (c.blocksFun i)‖ := by
  classical
  -- `comp` is a finite sum indexed by compositions of `n`.
  change ‖∑ c : Composition n, q.compAlongComposition p c‖ ≤ _
  calc
    ‖∑ c : Composition n, q.compAlongComposition p c‖
        ≤ ∑ c : Composition n, ‖q.compAlongComposition p c‖ := by
          simpa using norm_sum_le (Finset.univ)
            (fun c : Composition n => q.compAlongComposition p c)
    _ ≤ ∑ c : Composition n, ‖q c.length‖ * ∏ i, ‖p (c.blocksFun i)‖ := by
          exact Finset.sum_le_sum (fun c _ =>
            FormalMultilinearSeries.compAlongComposition_norm q p c)


/-- The same finite estimate with nonnegative coefficients. This form is
usually the convenient one for induction on coefficients. -/
lemma comp_coeff_nnnorm_le_sum (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) (n : ℕ) :
    ‖(q.comp p) n‖₊ ≤
      ∑ c : Composition n, ‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊ := by
  classical
  change ‖∑ c : Composition n, q.compAlongComposition p c‖₊ ≤ _
  calc
    ‖∑ c : Composition n, q.compAlongComposition p c‖₊
        ≤ ∑ c : Composition n, ‖q.compAlongComposition p c‖₊ := by
          simpa using nnnorm_sum_le (Finset.univ)
            (fun c : Composition n => q.compAlongComposition p c)
    _ ≤ ∑ c : Composition n, ‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊ := by
          exact Finset.sum_le_sum (fun c _ =>
            FormalMultilinearSeries.compAlongComposition_nnnorm q p c)


/-- A geometric-coefficient version of the composition estimate.  This is
finite, so the inside series need not converge.  The only loss counted here
is the number `2^(n-1)` of ordered compositions of `n` and a harmless
`Cp^n`.  This form is useful with `fmsLt` in a triangular induction. -/
lemma comp_coeff_nnnorm_mul_pow_le (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F)
    (rq rp Cq Cp : ℝ≥0)
    (hrq1 : rq ≤ 1) (hCp1 : 1 ≤ Cp)
    (hq : ∀ n : ℕ, ‖q n‖₊ * rq ^ n ≤ Cq)
    (hp : ∀ n : ℕ, ‖p n‖₊ * rp ^ n ≤ Cp)
    (n : ℕ) :
    ‖(q.comp p) n‖₊ * (rp * rq) ^ n ≤
      (2 : ℝ≥0) ^ (n-1) * (Cq * Cp ^ n) := by
  classical
  calc
    ‖(q.comp p) n‖₊ * (rp * rq) ^ n
        ≤ (∑ c : Composition n,
              ‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊) *
              (rp * rq) ^ n :=
          mul_le_mul' (comp_coeff_nnnorm_le_sum q p n) le_rfl
    _ = ∑ c : Composition n,
          (‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊) *
            (rp * rq) ^ n := by
          rw [Finset.sum_mul]
    _ ≤ ∑ _c : Composition n, (Cq * Cp ^ n) := by
      apply Finset.sum_le_sum
      intro c hc
      have A : ‖q c.length‖₊ * rq ^ n ≤ Cq := by
        calc
          ‖q c.length‖₊ * rq ^ n
              ≤ ‖q c.length‖₊ * rq ^ c.length :=
                mul_le_mul' le_rfl
                  (pow_le_pow_of_le_one (by exact bot_le) hrq1 c.length_le)
          _ ≤ Cq := hq _
      have B : (∏ i, ‖p (c.blocksFun i)‖₊) * rp ^ n ≤ Cp ^ n := by
        calc
          (∏ i, ‖p (c.blocksFun i)‖₊) * rp ^ n =
              ∏ i, ‖p (c.blocksFun i)‖₊ * rp ^ c.blocksFun i := by
                simp only [Finset.prod_mul_distrib,
                  Finset.prod_pow_eq_pow_sum, c.sum_blocksFun]
          _ ≤ ∏ _i : Fin c.length, Cp :=
                Finset.prod_le_prod' (fun i _ => hp _)
          _ = Cp ^ c.length := by simp
          _ ≤ Cp ^ n := pow_right_mono₀ hCp1 c.length_le
      calc
        (‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊) *
              (rp * rq) ^ n
            = (‖q c.length‖₊ * rq ^ n) *
                ((∏ i, ‖p (c.blocksFun i)‖₊) * rp ^ n) := by
                  rw [mul_pow]
                  -- exchange the two scalar radial factors
                  ac_rfl
        _ ≤ Cq * Cp ^ n := mul_le_mul' A B
    _ = (2 : ℝ≥0) ^ (n-1) * (Cq * Cp ^ n) := by
      -- There are `2^(n-1)` ordered compositions of `n`.
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [Finset.card_univ, composition_card]


/-- Truncating an inductively bounded family preserves the same nonnegative
geometric bound without any convergence assumption.  The zero tail is
occasionally easy to overlook in composition estimates. -/
lemma fmsLt_nnnorm_mul_pow_le {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (b : FormalMultilinearSeries ℝ ((Y)×ℝ) Y)
    (r B : ℝ≥0) (N : ℕ)
    (hb : ∀ m < N, ‖b m‖₊ * r ^ m ≤ B) :
    ∀ m : ℕ, ‖(fmsLt b N) m‖₊ * r ^ m ≤ B := by
  intro m
  classical
  by_cases h : m < N
  · simpa [fmsLt, h] using hb m h
  · simp [fmsLt, h]


section splitAnt
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A tail of a set of slots, with the initial integration slot removed. -/
def tailSlots {n : ℕ} (S : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i.succ ∈ S)

@[simp] lemma mem_tailSlots {n : ℕ} (S : Finset (Fin (n+1))) (i : Fin n) :
    i ∈ tailSlots S ↔ i.succ ∈ S := by
  simp [tailSlots]

@[simp] lemma antTerm_apply {n : ℕ} (r : (Y × ℝ)[×n]→L[ℝ] Y)
    (s : Finset (Fin n)) (v : Fin (n+1) → Y×ℝ) :
    antTerm r s v = (v 0).2 • splitCoeff r s (Fin.tail v) := by
  classical
  -- this is the computation underlying the diagonal version; it is handy
  -- before specializing the inputs to their two projections.
  simp [antTerm, ContinuousLinearMap.uncurryLeft_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousMultilinearMap.smul_apply]

/-- Polarization removes the exponential loss in `timeAnt_norm_le`.
For a *fixed* pattern of parameter/time slots only one summand of the
antiderivative survives.  This elementary identity is useful when the
crude `2^n` bound cannot be iterated. -/
lemma splitCoeff_timeAnt {n : ℕ} (r : (Y × ℝ)[×n]→L[ℝ] Y)
    (S : Finset (Fin (n+1))) :
    splitCoeff (timeAnt r) S =
      if h : (0 : Fin (n+1)) ∈ S then
        (1 / (((tailSlots S).card:ℝ) + 1)) •
          antTerm r (tailSlots S)
      else 0 := by
  classical
  -- expand a split input once.  Subsequent splits of an already pure
  -- parameter or pure time vector have only one nonzero choice.
  ext v
  let w : Fin (n+1) → (Y×ℝ) :=
    fun i => if i ∈ S then (0, (v i).2) else ((v i).1, 0)
  have hw (i : Fin (n+1)) : w i =
      (if i ∈ S then (0, (v i).2) else ((v i).1, 0)) := rfl
  rw [splitCoeff_apply]
  change timeAnt r w = _
  by_cases h0 : (0 : Fin (n+1)) ∈ S
  · simp only [dif_pos h0]
    rw [ContinuousMultilinearMap.smul_apply]
    rw [timeAnt, ContinuousMultilinearMap.sum_apply]
    -- exactly the tail pattern remains
    rw [Finset.sum_eq_single (tailSlots S)]
    · rw [ContinuousMultilinearMap.smul_apply]
      -- both sides are scalar multiples of the same split tail
      rw [antTerm_apply, antTerm_apply]
      have hw0 : (w 0).2 = (v 0).2 := by
        simp [w, h0]
      have htail : splitCoeff r (tailSlots S) (Fin.tail w) =
          splitCoeff r (tailSlots S) (Fin.tail v) := by
        rw [splitCoeff_apply, splitCoeff_apply]
        congr 1
        funext i
        by_cases hi : i ∈ tailSlots S
        · have hi' : i.succ ∈ S := (mem_tailSlots S i).1 hi
          simp [Fin.tail, w, hi, hi']
        · have hi' : i.succ ∉ S := by
            intro H
            exact hi ((mem_tailSlots S i).2 H)
          simp [Fin.tail, w, hi, hi']
      rw [hw0, htail]
      -- reassociate the two scalar actions
    · intro b hb hne
      -- choose a tail slot where `b` and `tailSlots S` differ
      have hex : ∃ i : Fin n, (i ∈ b) ≠ (i ∈ tailSlots S) := by
        by_contra H
        push_neg at H
        -- `push_neg` changes this into equality of the two propositions.
        have eqb : b = tailSlots S := by
          ext i
          exact Iff.of_eq (H i)
        exact hne eqb
      obtain ⟨i, hi⟩ := hex
      rw [ContinuousMultilinearMap.smul_apply]
      have hz : splitCoeff r b (Fin.tail w) = 0 := by
        rw [splitCoeff_apply]
        -- one of the mismatched projections is zero
        apply ContinuousMultilinearMap.map_coord_zero r i
        by_cases hib : i ∈ b
        · have hit : i ∉ tailSlots S := by
            intro ht
            apply hi
            exact propext ⟨(fun _ => ht), (fun _ => hib)⟩
          have hiS : i.succ ∉ S := by
            intro ht
            exact hit ((mem_tailSlots S i).2 ht)
          simp [Fin.tail, hib, w, hiS]
        · have hit : i ∈ tailSlots S := by
            by_contra ht
            apply hi
            exact propext ⟨(fun h => False.elim (hib h)),
              (fun h => False.elim (ht h))⟩
          have hiS : i.succ ∈ S := (mem_tailSlots S i).1 hit
          simp [Fin.tail, hib, w, hiS]
      rw [antTerm_apply, hz, smul_zero, smul_zero]
    · intro hx
      exfalso
      exact (hx (Finset.mem_univ _))
  · simp only [dif_neg h0]
    rw [timeAnt, ContinuousMultilinearMap.sum_apply]
    -- the first slot is forced to be a time slot in every term
    simp only [ContinuousMultilinearMap.smul_apply, antTerm_apply]
    have hw0 : (w 0).2 = 0 := by simp [w, h0]
    simp [hw0]

lemma antTerm_split_norm_le {n : ℕ} (r : (Y × ℝ)[×n]→L[ℝ] Y)
    (s : Finset (Fin n)) : ‖antTerm r s‖ ≤ ‖splitCoeff r s‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  rw [antTerm_apply]
  calc
    ‖(v 0).2 • splitCoeff r s (Fin.tail v)‖
        = ‖(v 0).2‖ * ‖splitCoeff r s (Fin.tail v)‖ := norm_smul _ _
    _ ≤ ‖v 0‖ *
          (‖splitCoeff r s‖ * ∏ i : Fin n, ‖v i.succ‖) := by
        gcongr
        · simp [Prod.norm_def]
        · exact ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖splitCoeff r s‖ * ∏ i : Fin (n+1), ‖v i‖ := by
        rw [Fin.prod_univ_succ]
        ring

/-- In a fixed polarization there is no `2^n` loss in one integration
step.  The loss in `timeAnt_norm_le` is from summing the polarizations,
not from repeatedly integrating one of them. -/
lemma splitCoeff_timeAnt_norm_le {n : ℕ} (r : (Y × ℝ)[×n]→L[ℝ] Y)
    (S : Finset (Fin (n+1))) :
    ‖splitCoeff (timeAnt r) S‖ ≤ ‖splitCoeff r (tailSlots S)‖ := by
  classical
  rw [splitCoeff_timeAnt]
  split_ifs with h
  · rw [norm_smul]
    have hc0 : 0 ≤ (1 / (((tailSlots S).card:ℝ) + 1) : ℝ) := by positivity
    have hc : ‖(1 / (((tailSlots S).card:ℝ) + 1) : ℝ)‖ ≤ (1:ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hc0]
      have h1 : (1:ℝ) ≤ ((tailSlots S).card:ℝ) + 1 := by
        exact_mod_cast (Nat.le_add_left 1 (tailSlots S).card)
      exact (div_le_one (by positivity)).2 h1
    calc
      ‖(1 / (((tailSlots S).card:ℝ) + 1) : ℝ)‖ *
          ‖antTerm r (tailSlots S)‖
            ≤ 1 * ‖splitCoeff r (tailSlots S)‖ :=
                mul_le_mul hc (antTerm_split_norm_le r _)
                  (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  · simp


/-- Recovering a map from all its parameter/time polarizations.  This is the
non-diagonal version of `sum_splitCoeff_apply`; keeping it as a map identity
allows operator-norm estimates. -/
lemma sum_splitCoeff {n : ℕ} (r : (Y × ℝ)[×n]→L[ℝ] Y) :
    (∑ s : Finset (Fin n), splitCoeff r s) = r := by
  classical
  ext v
  rw [ContinuousMultilinearMap.sum_apply]
  have H := r.map_add_univ
       (fun i : Fin n => tPart (Y:=Y) (v i))
       (fun i : Fin n => qPart (Y:=Y) (v i))
  have huv : ((fun i : Fin n => tPart (Y:=Y) (v i)) +
          (fun i : Fin n => qPart (Y:=Y) (v i))) = v := by
    funext i
    have hv := qPart_add_tPart (Y:=Y) (v i)
    simpa [Pi.add_apply, add_comm] using hv
  rw [huv] at H
  -- each summand is obtained by selecting exactly these projections
  have hp : (∑ s : Finset (Fin n),
        r (fun i => if i ∈ s then (0,(v i).2) else ((v i).1,0))) =
      (∑ s : Finset (Fin n),
        r (s.piecewise
          (fun i : Fin n => tPart (Y:=Y) (v i))
          (fun i : Fin n => qPart (Y:=Y) (v i)))) := by
    apply Finset.sum_congr rfl
    intro s hs
    apply congrArg r
    funext i
    by_cases hi : i ∈ s
    · simp [Finset.piecewise, hi]
    · simp [Finset.piecewise, hi]
  -- turn the left hand side into `splitCoeff_apply`
  calc
    (∑ s : Finset (Fin n), splitCoeff r s v) =
        ∑ s : Finset (Fin n),
          r (fun i => if i ∈ s then (0,(v i).2) else ((v i).1,0)) := by
            apply Finset.sum_congr rfl
            intro s hs
            exact splitCoeff_apply r s v
    _ = _ := hp.trans H.symm

lemma norm_le_sum_splitCoeff {n : ℕ} (r : (Y × ℝ)[×n]→L[ℝ] Y) :
    ‖r‖ ≤ ∑ s : Finset (Fin n), ‖splitCoeff r s‖ := by
  classical
  calc
    ‖r‖ = ‖(∑ s : Finset (Fin n), splitCoeff r s)‖ :=
      congrArg norm (sum_splitCoeff r).symm
    _ ≤ ∑ s : Finset (Fin n), ‖splitCoeff r s‖ := by
      simpa using norm_sum_le (Finset.univ)
        (fun s : Finset (Fin n) => splitCoeff r s)

/-- The pattern induced on one block of a composition. -/
def blockSlots {k : ℕ} (c : Composition k) (T : Finset (Fin k))
    (i : Fin c.length) : Finset (Fin (c.blocksFun i)) :=
  Finset.univ.filter (fun j : Fin (c.blocksFun i) => c.embedding i j ∈ T)
@[simp] lemma mem_blockSlots {k : ℕ} (c : Composition k)
    (T : Finset (Fin k)) (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    j ∈ blockSlots c T i ↔ c.embedding i j ∈ T := by
  simp [blockSlots]

lemma splitCoeff_compAlong_bound
    (p : FormalMultilinearSeries ℝ Y Y)
    (b : FormalMultilinearSeries ℝ (Y×ℝ) Y)
    {k : ℕ} (c : Composition k) (T : Finset (Fin k))
    (v : Fin k → Y×ℝ) :
    ‖splitCoeff (p.compAlongComposition b c) T v‖ ≤
      (‖p c.length‖ *
        ∏ i, ‖splitCoeff (b (c.blocksFun i)) (blockSlots c T i)‖) *
        ∏ i : Fin k, ‖v i‖ := by
  classical
  rw [splitCoeff_apply]
  let w : Fin k → (Y×ℝ) :=
    fun j => if j ∈ T then (0, (v j).2) else ((v j).1,0)
  change ‖p c.length (b.applyComposition c w)‖ ≤ _
  have hw (i : Fin c.length) :
      b (c.blocksFun i) (w ∘ c.embedding i) =
        splitCoeff (b (c.blocksFun i)) (blockSlots c T i)
          (v ∘ c.embedding i) := by
    rw [splitCoeff_apply]
    congr 1
    funext j
    by_cases h : c.embedding i j ∈ T
    · have hj : j ∈ blockSlots c T i := (mem_blockSlots c T i j).2 h
      simp [Function.comp_def, w, h, hj]
    · have hj : j ∉ blockSlots c T i := by
          intro hh; exact h ((mem_blockSlots c T i j).1 hh)
      simp [Function.comp_def, w, h, hj]
  calc
    ‖p c.length (b.applyComposition c w)‖
        ≤ ‖p c.length‖ * ∏ i, ‖b (c.blocksFun i)
            (w ∘ c.embedding i)‖ := by
          exact ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖p c.length‖ * ∏ i,
          ‖splitCoeff (b (c.blocksFun i)) (blockSlots c T i)
            (v ∘ c.embedding i)‖ := by
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          rw [hw]
    _ ≤ ‖p c.length‖ *
          ∏ i, (‖splitCoeff (b (c.blocksFun i)) (blockSlots c T i)‖ *
            ∏ j : Fin (c.blocksFun i), ‖(v ∘ c.embedding i) j‖) := by
          gcongr with i
          exact ContinuousMultilinearMap.le_opNorm _ _
    _ = (‖p c.length‖ *
          ∏ i, ‖splitCoeff (b (c.blocksFun i)) (blockSlots c T i)‖) *
          ∏ i, ∏ j : Fin (c.blocksFun i), ‖(v ∘ c.embedding i) j‖ := by
          rw [Finset.prod_mul_distrib, mul_assoc]
    _ = (‖p c.length‖ *
          ∏ i, ‖splitCoeff (b (c.blocksFun i)) (blockSlots c T i)‖) *
          ∏ i : Fin k, ‖v i‖ := by
          rw [← c.blocksFinEquiv.prod_comp, ← Finset.univ_sigma_univ,
            Finset.prod_sigma]
          congr

lemma splitCoeff_compAlongComposition_norm_fixed
    (p : FormalMultilinearSeries ℝ Y Y)
    (b : FormalMultilinearSeries ℝ (Y×ℝ) Y)
    {k : ℕ} (c : Composition k) (T : Finset (Fin k)) :
    ‖splitCoeff (p.compAlongComposition b c) T‖ ≤
      ‖p c.length‖ *
        ∏ i, ‖splitCoeff (b (c.blocksFun i)) (blockSlots c T i)‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  exact splitCoeff_compAlong_bound p b c T v


lemma splitCoeff_comp_sum
    (p : FormalMultilinearSeries ℝ Y Y)
    (b : FormalMultilinearSeries ℝ (Y×ℝ) Y)
    (k : ℕ) (T : Finset (Fin k)) :
    splitCoeff ((p.comp b) k) T =
      ∑ c : Composition k, splitCoeff (p.compAlongComposition b c) T := by
  classical
  ext v
  rw [splitCoeff_apply, ContinuousMultilinearMap.sum_apply]
  -- split after summing is the same finite linear operation
  simp [FormalMultilinearSeries.comp,
    ContinuousMultilinearMap.sum_apply]

lemma splitCoeff_comp_norm_le_sum
    (p : FormalMultilinearSeries ℝ Y Y)
    (b : FormalMultilinearSeries ℝ (Y×ℝ) Y)
    (k : ℕ) (T : Finset (Fin k)) :
    ‖splitCoeff ((p.comp b) k) T‖ ≤
      ∑ c : Composition k,
        ‖p c.length‖ *
          ∏ i, ‖splitCoeff (b (c.blocksFun i)) (blockSlots c T i)‖ := by
  classical
  rw [splitCoeff_comp_sum]
  calc
    ‖∑ c : Composition k, splitCoeff (p.compAlongComposition b c) T‖
         ≤ ∑ c : Composition k,
             ‖splitCoeff (p.compAlongComposition b c) T‖ := by
             simpa using norm_sum_le (Finset.univ)
               (fun c : Composition k =>
                  splitCoeff (p.compAlongComposition b c) T)
    _ ≤ ∑ c : Composition k,
        ‖p c.length‖ *
          ∏ i, ‖splitCoeff (b (c.blocksFun i)) (blockSlots c T i)‖ :=
      Finset.sum_le_sum (fun c _ =>
        splitCoeff_compAlongComposition_norm_fixed p b c T)
end splitAnt


section odePolar
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma splitCoeff_add {n : ℕ} (a b : (Y×ℝ)[×n]→L[ℝ] Y)
    (S : Finset (Fin n)) :
    splitCoeff (a+b) S = splitCoeff a S + splitCoeff b S := by
  classical
  ext v
  simp [splitCoeff, ContinuousMultilinearMap.compContinuousLinearMap_apply]
lemma splitCoeff_zero {n : ℕ} (S : Finset (Fin n)) :
    splitCoeff (0 : (Y×ℝ)[×n]→L[ℝ] Y) S = 0 := by
  classical
  ext v
  simp [splitCoeff, ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- In the triangular ODE recurrence one only loses `2^k` after summing over
patterns. On each fixed pattern a time integration has norm at most one;
the harmless degree-one term is the boundary `q`. -/
lemma odeSeries_succ_split_norm
    (p : FormalMultilinearSeries ℝ Y Y) (k : ℕ)
    (S : Finset (Fin (k+1))) :
    ‖splitCoeff (odeSeries p (k+1)) S‖ ≤
      ‖splitCoeff ((p.comp (fmsLt (odeSeries p) (k+1))) k)
          (tailSlots S)‖ + (if k=0 then 1 else 0) := by
  classical
  rcases k with _ | k
  · -- the one boundary coefficient
    rw [odeSeries_succ]
    dsimp
    rw [splitCoeff_add]
    calc
      ‖splitCoeff (timeAnt ((p.comp (fmsLt (odeSeries p) (0+1))) 0)) S +
          splitCoeff odeBoundary S‖
          ≤ ‖splitCoeff (timeAnt ((p.comp (fmsLt (odeSeries p) (0+1))) 0)) S‖ +
            ‖splitCoeff (odeBoundary) S‖ := norm_add_le _ _
      _ ≤ ‖splitCoeff ((p.comp (fmsLt (odeSeries p) (0+1))) 0)
              (tailSlots S)‖ + 1 := by
            exact add_le_add
              (splitCoeff_timeAnt_norm_le _ _)
              ((splitCoeff_norm_le _ _).trans odeBoundary_norm_le)
  · rw [odeSeries_succ]
    simp
    exact splitCoeff_timeAnt_norm_le _ _
end odePolar

section odePolarStep
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma odeSeries_succ_split_norm_le_sum
    (p : FormalMultilinearSeries ℝ Y Y) (k : ℕ)
    (S : Finset (Fin (k+1))) :
    ‖splitCoeff (odeSeries p (k+1)) S‖ ≤
      (∑ c : Composition k,
          ‖p c.length‖ *
            ∏ i, ‖splitCoeff ((odeSeries p) (c.blocksFun i))
              (blockSlots c (tailSlots S) i)‖) +
        (if k=0 then 1 else 0) := by
  classical
  refine (odeSeries_succ_split_norm p k S).trans ?_
  apply add_le_add ?_ le_rfl
  have h := splitCoeff_comp_norm_le_sum p
      (fmsLt (odeSeries p) (k+1)) k (tailSlots S)
  -- On a block of a composition of `k` the truncation to `k+1`
  -- leaves the coefficient untouched.
  calc
    ‖splitCoeff ((p.comp (fmsLt (odeSeries p) (k+1))) k)
          (tailSlots S)‖
      ≤ ∑ c : Composition k, ‖p c.length‖ *
          ∏ i, ‖splitCoeff ((fmsLt (odeSeries p) (k+1)) (c.blocksFun i))
            (blockSlots c (tailSlots S) i)‖ := h
    _ = ∑ c : Composition k, ‖p c.length‖ *
          ∏ i, ‖splitCoeff ((odeSeries p) (c.blocksFun i))
            (blockSlots c (tailSlots S) i)‖ := by
        apply Finset.sum_congr rfl
        intro c hc
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        have hi' : c.blocksFun i < k + 1 :=
          Nat.lt_succ_of_le (c.blocksFun_le i)
        simp [fmsLt, hi']
end odePolarStep

section splitRadius
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Uniform exponential control of each polarization is enough; summing
patterns costs exactly another `2^n`. This keeps the weighted-slot problem
separate from the analytic-radius problem. -/
lemma norm_ode_coeff_of_polar_bound
    (b : FormalMultilinearSeries ℝ (Y×ℝ) Y)
    (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ (n : ℕ) (S : Finset (Fin n)),
        ‖splitCoeff (b n) S‖ ≤ D ^ n) :
    ∀ n : ℕ, ‖b n‖ ≤ (2*D) ^ n := by
  intro n
  classical
  calc
    ‖b n‖ ≤ ∑ S : Finset (Fin n), ‖splitCoeff (b n) S‖ :=
      norm_le_sum_splitCoeff _
    _ ≤ ∑ _S : Finset (Fin n), D ^ n :=
      Finset.sum_le_sum (fun S _ => hb n S)
    _ = (2*D)^n := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_univ]
      -- there are `2^n` choices of a pattern
      simp
      rw [mul_pow]
end splitRadius
end
end CKSupport

-- END INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/OdeMajorantBasic.lean

-- BEGIN INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/OdeMajorantRefined.lean
open Set Filter
open scoped BigOperators ENNReal NNReal Topology
namespace CKSupport
noncomputable section
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- On a block of a composition of `k`, truncating the triangular ODE at
`k+1` leaves the block unchanged.  This isolates the norm estimate used
both by the crude polarization bound and by its weighted (time-slot)
version. -/
lemma splitCoeff_comp_fmsLt_odeSeries_norm_le_sum
    (p : FormalMultilinearSeries ℝ Y Y) (k : ℕ)
    (T : Finset (Fin k)) :
    ‖splitCoeff
        ((p.comp (fmsLt (odeSeries p) (k+1))) k) T‖ ≤
      ∑ c : Composition k,
        ‖p c.length‖ *
          ∏ i, ‖splitCoeff ((odeSeries p) (c.blocksFun i))
            (blockSlots c T i)‖ := by
  classical
  have h := splitCoeff_comp_norm_le_sum p
      (fmsLt (odeSeries p) (k+1)) k T
  calc
    ‖splitCoeff
        ((p.comp (fmsLt (odeSeries p) (k+1))) k) T‖
      ≤ ∑ c : Composition k, ‖p c.length‖ *
          ∏ i, ‖splitCoeff ((fmsLt (odeSeries p) (k+1)) (c.blocksFun i))
            (blockSlots c T i)‖ := h
    _ = ∑ c : Composition k, ‖p c.length‖ *
          ∏ i, ‖splitCoeff ((odeSeries p) (c.blocksFun i))
            (blockSlots c T i)‖ := by
        apply Finset.sum_congr rfl
        intro c hc
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        have hi' : c.blocksFun i < k + 1 :=
          Nat.lt_succ_of_le (c.blocksFun_le i)
        simp [fmsLt, hi']

/-- The polarization recurrence with the *time weight* left in it.
The coarse lemma `odeSeries_succ_split_norm_le_sum` deliberately discards
this scalar.  For convergence one must not do so: a term with `m` time
slots is the integral of a term with `m-1` of them, hence is divided by
`m`.  Moreover the integral vanishes unless the distinguished first slot
is a time slot.  This finite statement has no analyticity hypotheses. -/
lemma odeSeries_succ_split_norm_le_sum_weighted
    (p : FormalMultilinearSeries ℝ Y Y) (k : ℕ)
    (S : Finset (Fin (k+1))) :
    ‖splitCoeff (odeSeries p (k+1)) S‖ ≤
      (if (0 : Fin (k+1)) ∈ S then
        (1 / (((tailSlots S).card:ℝ) + 1)) *
          (∑ c : Composition k,
            ‖p c.length‖ *
              ∏ i, ‖splitCoeff ((odeSeries p) (c.blocksFun i))
                (blockSlots c (tailSlots S) i)‖)
       else 0) +
        (if k=0 then 1 else 0) := by
  classical
  by_cases hfirst : (0 : Fin (k+1)) ∈ S
  · simp only [if_pos hfirst]
    -- treat the boundary coefficient separately; it is present only in
    -- degree one and has norm at most one in every polarization.
    by_cases hk : k = 0
    · subst k
      -- Make the degree-one recurrence explicit.
      rw [odeSeries_succ]
      dsimp
      rw [splitCoeff_add]
      calc
        ‖splitCoeff
              (timeAnt ((p.comp (fmsLt (odeSeries p) (0+1))) 0)) S
            + splitCoeff (odeBoundary (Y:=Y)) S‖
            ≤ ‖splitCoeff
                (timeAnt ((p.comp (fmsLt (odeSeries p) (0+1))) 0)) S‖ +
              ‖splitCoeff (odeBoundary (Y:=Y)) S‖ := norm_add_le _ _
        _ ≤
            (1 / (((tailSlots S).card:ℝ) + 1)) *
                (∑ c : Composition 0,
                  ‖p c.length‖ *
                    ∏ i, ‖splitCoeff ((odeSeries p) (c.blocksFun i))
                      (blockSlots c (tailSlots S) i)‖) + 1 := by
              apply add_le_add ?_ ?_
              · -- the integral component
                rw [splitCoeff_timeAnt]
                simp only [dif_pos hfirst, norm_smul]
                have hc0 :
                    0 ≤ (1 / (((tailSlots S).card:ℝ) + 1) : ℝ) := by
                      positivity
                rw [Real.norm_eq_abs, abs_of_nonneg hc0]
                have hcomp :=
                  splitCoeff_comp_fmsLt_odeSeries_norm_le_sum
                    (Y:=Y) p 0 (tailSlots S)
                -- antiderivative at a fixed pattern uses just the one
                -- matching pattern of its integrand.
                exact mul_le_mul_of_nonneg_left
                  ((antTerm_split_norm_le
                      ((p.comp (fmsLt (odeSeries p) (0+1))) 0)
                      (tailSlots S)).trans hcomp)
                    hc0
              · exact (splitCoeff_norm_le _ _).trans odeBoundary_norm_le
        _ =
            (1 / (((tailSlots S).card:ℝ) + 1)) *
                (∑ c : Composition 0,
                  ‖p c.length‖ *
                    ∏ i, ‖splitCoeff ((odeSeries p) (c.blocksFun i))
                      (blockSlots c (tailSlots S) i)‖) +
                (if (0:ℕ)=0 then 1 else 0) := by simp
    · -- In all higher degrees there is no boundary coefficient.
      rw [odeSeries_succ]
      simp [hk]
      -- keep the exact time coefficient and estimate the remaining
      -- integrand by its composition polarization.
      rw [splitCoeff_timeAnt]
      simp only [dif_pos hfirst, norm_smul]
      have hc0 :
          0 ≤ (1 / (((tailSlots S).card:ℝ) + 1) : ℝ) := by
            positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hc0]
      simpa [one_div] using
        (mul_le_mul_of_nonneg_left
          ((antTerm_split_norm_le
              ((p.comp (fmsLt (odeSeries p) (k+1))) k)
              (tailSlots S)).trans
            (splitCoeff_comp_fmsLt_odeSeries_norm_le_sum
              (Y:=Y) p k (tailSlots S))) hc0)
  · simp only [if_neg hfirst]
    -- Without a time in the first slot, every antiderivative term is zero.
    -- Only the (degree-one) boundary term can survive.
    by_cases hk : k = 0
    · subst k
      rw [odeSeries_succ]
      dsimp
      rw [splitCoeff_add]
      -- Use the exact polarization formula to dispose of the integral.
      have hz : splitCoeff
          (timeAnt ((p.comp (fmsLt (odeSeries p) (0+1))) 0)) S = 0 := by
        rw [splitCoeff_timeAnt]
        simp [hfirst]
      -- the remaining boundary component is bounded by one.  Keeping the
      -- index of the zero map explicit avoids a dependent rewrite through
      -- `Fin (0+1)`.
      rw [hz]
      -- the zero is on the left
      have hadd' :
          (0 : (Y×ℝ)[×1]→L[ℝ] Y) +
              splitCoeff (odeBoundary (Y:=Y)) S =
            splitCoeff (odeBoundary (Y:=Y)) S := zero_add _
      rw [hadd']
      -- the remaining boundary component is bounded by one
      simpa using
        ((splitCoeff_norm_le (odeBoundary (Y:=Y)) S).trans
          (odeBoundary_norm_le (Y:=Y)))
    · rw [odeSeries_succ]
      simp [hk]
      rw [splitCoeff_timeAnt]
      simp [hfirst]
end
end CKSupport

namespace CKSupport
noncomputable section
open scoped BigOperators
/-- A scalar, nonnegative *plane tree* majorant for the polar coefficients.
`planeMajor A R (k+1)` is obtained by cutting an ordered list of `k` tail
slots into its nonempty blocks; the root contributes `A R^l` for `l`
blocks.  It deliberately ignores the divisors from integrating a time
slot.  Keeping the ordered blocks (rather than replacing the answer by
`2^k`) is the important point: it is the ordinary plane-tree series.
All involved sums are finite. -/
def planeMajor (A R : ℝ) : ℕ → ℝ :=
  Nat.strongRec (fun n ih =>
    match n with
    | 0 => 0
    | k+1 =>
        (if k=0 then 1 else 0) +
          A * (∑ c : Composition k, R ^ c.length *
            ∏ i : Fin c.length,
              ih (c.blocksFun i)
                (Nat.lt_succ_of_le (c.blocksFun_le i))))

@[simp] lemma planeMajor_zero (A R : ℝ) : planeMajor A R 0 = 0 := by
  rw [planeMajor, Nat.strongRec_eq]

lemma planeMajor_succ (A R : ℝ) (k : ℕ) :
    planeMajor A R (k+1) =
      (if k=0 then 1 else 0) +
        A * (∑ c : Composition k, R ^ c.length *
          ∏ i : Fin c.length, planeMajor A R (c.blocksFun i)) := by
  rw [planeMajor, Nat.strongRec_eq]
  -- the strong recursive calls are definitionally the same function on
  -- smaller indices; spelling this out avoids any convergence assumptions.
  congr

lemma planeMajor_nonneg {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    ∀ n : ℕ, 0 ≤ planeMajor A R n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [planeMajor_zero]
    | succ k =>
      rw [planeMajor_succ]
      have hdelta : 0 ≤ (if k=0 then (1:ℝ) else 0) := by split_ifs <;> norm_num
      have hsum :
          0 ≤ ∑ c : Composition k, R ^ c.length *
            ∏ i : Fin c.length, planeMajor A R (c.blocksFun i) := by
        apply Finset.sum_nonneg
        intro c hc
        exact mul_nonneg (pow_nonneg hR _)
          (Finset.prod_nonneg (fun i hi =>
            ih (c.blocksFun i) (Nat.lt_succ_of_le (c.blocksFun_le i))))
      exact add_nonneg hdelta (mul_nonneg hA hsum)

variable {Y' : Type*} [NormedAddCommGroup Y'] [NormedSpace ℝ Y']

/-- Every fixed sequence of parameter/time slots in the triangular ODE is
bounded by the scalar plane-tree coefficient.  This is a useful reduction:
it is purely triangular induction and still makes sense without a radius
for `odeSeries`.  Analyticity is a subsequent, entirely scalar, majorant
problem for `planeMajor`; replacing it here by the crude count `2^k` loses
that reduction. -/
lemma splitCoeff_odeSeries_le_planeMajor
    (p : FormalMultilinearSeries ℝ Y' Y')
    (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hp : ∀ l : ℕ, ‖p l‖ ≤ A * R ^ l) :
    ∀ (n : ℕ) (S : Finset (Fin n)),
      ‖splitCoeff (odeSeries p n) S‖ ≤ planeMajor A R n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S
    cases n with
    | zero =>
      simp [odeSeries_zero, splitCoeff_zero, planeMajor_zero]
    | succ k =>
      have hstep := odeSeries_succ_split_norm_le_sum p k S
      have hmini (c : Composition k) :
          ‖p c.length‖ *
              ∏ i, ‖splitCoeff ((odeSeries p) (c.blocksFun i))
                (blockSlots c (tailSlots S) i)‖
            ≤
          (A * R ^ c.length) *
              ∏ i : Fin c.length, planeMajor A R (c.blocksFun i) := by
        have hprod :
            (∏ i, ‖splitCoeff ((odeSeries p) (c.blocksFun i))
              (blockSlots c (tailSlots S) i)‖)
              ≤ ∏ i : Fin c.length, planeMajor A R (c.blocksFun i) := by
          apply Finset.prod_le_prod
          · intro i hi
            exact norm_nonneg _
          · intro i hi
            exact ih (c.blocksFun i)
              (Nat.lt_succ_of_le (c.blocksFun_le i)) _
        apply mul_le_mul (hp c.length) hprod
        · exact Finset.prod_nonneg (fun i hi => norm_nonneg _)
        · exact mul_nonneg hA (pow_nonneg hR _)
      rw [planeMajor_succ]
      calc
        ‖splitCoeff (odeSeries p (k+1)) S‖
            ≤ (∑ c : Composition k,
                ‖p c.length‖ *
                  ∏ i, ‖splitCoeff ((odeSeries p) (c.blocksFun i))
                    (blockSlots c (tailSlots S) i)‖) +
                  (if k=0 then 1 else 0) := hstep
        _ ≤ (∑ c : Composition k,
                (A * R ^ c.length) *
                  ∏ i : Fin c.length, planeMajor A R (c.blocksFun i)) +
                  (if k=0 then 1 else 0) := by
                    refine add_le_add_left ?_ (if k=0 then (1:ℝ) else 0)
                    exact Finset.sum_le_sum (fun c _ => hmini c)
        _ = (if k=0 then 1 else 0) +
              A * (∑ c : Composition k, R ^ c.length *
                ∏ i : Fin c.length, planeMajor A R (c.blocksFun i)) := by
              rw [Finset.mul_sum]
              -- reorder the scalar factors at each summand
              simp_rw [mul_assoc]
              ac_rfl
end
end CKSupport

namespace CKSupport
noncomputable section
open scoped BigOperators

/-- If the distinguished slot is marked for time, the scalar in
`splitCoeff_timeAnt` is exactly the reciprocal of the number of time slots
in the output pattern. -/
lemma card_tailSlots_add_one {n : ℕ} (S : Finset (Fin (n+1)))
    (h : (0 : Fin (n+1)) ∈ S) :
    (tailSlots S).card + 1 = S.card := by
  classical
  have ht : (tailSlots S).card =
      ∑ i : Fin n, if i.succ ∈ S then 1 else 0 := by
        simp [tailSlots]
  have hs : S.card =
      ∑ i : Fin (n+1), if i ∈ S then 1 else 0 := by
        simp
  rw [ht, hs, Fin.sum_univ_succ]
  simp [h, add_comm]

/-- A block decomposition does not create or lose marked slots.  This little
counting identity is useful when a later scalar majorant keeps track of the
number of time slots rather than just the total degree. -/
lemma sum_card_blockSlots {k : ℕ} (c : Composition k)
    (T : Finset (Fin k)) :
    (∑ i, (blockSlots c T i).card) = T.card := by
  classical
  have hb (i : Fin c.length) :
      (blockSlots c T i).card =
        ∑ j : Fin (c.blocksFun i), if c.embedding i j ∈ T then 1 else 0 := by
          simp [blockSlots]
  calc
    (∑ i, (blockSlots c T i).card) =
        ∑ i, ∑ j : Fin (c.blocksFun i),
          if c.embedding i j ∈ T then 1 else 0 := by simp_rw [hb]
    _ = ∑ j : Fin k, if j ∈ T then 1 else 0 :=
      (Composition.sum_sum_apply_embedding (A:=ℕ)
        (fun j : Fin k => if j ∈ T then 1 else 0) c)
    _ = T.card := by simp

variable {Y'' : Type*} [NormedAddCommGroup Y''] [NormedSpace ℝ Y'']
/-- Above degree one an ODE coefficient has no component with a parameter in
its first slot.  This is the exact support statement behind the much smaller
plane-tree count. -/
lemma splitCoeff_odeSeries_succ_eq_zero_of_not_mem
    (p : FormalMultilinearSeries ℝ Y'' Y'') (k : ℕ) (hk : k ≠ 0)
    (S : Finset (Fin (k+1))) (h : (0 : Fin (k+1)) ∉ S) :
    splitCoeff (odeSeries p (k+1)) S = 0 := by
  classical
  rw [odeSeries_succ]
  simp [hk]
  rw [splitCoeff_timeAnt]
  simp [h]
end
end CKSupport

-- END INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/OdeMajorantRefined.lean

-- BEGIN INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/PlaneMajorBound.lean
open scoped BigOperators
open Set
namespace CKSupport
noncomputable section

def compScalar (R : ℝ) (M : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ c : Composition k, R ^ c.length * ∏ i : Fin c.length, M (c.blocksFun i)

lemma compScalar_zero (R : ℝ) (M : ℕ → ℝ) : compScalar R M 0 = 1 := by
  classical
  unfold compScalar
  have hlen (c : Composition 0) : c.length = 0 := by
    exact Nat.le_zero.mp c.length_le
  simp_rw [hlen]
  simp
  
  have hx (x : Composition 0) : (∏ i : Fin x.length, M (x.blocksFun i)) = 1 := by
    classical
    apply Finset.prod_eq_one
    intro i hi
    have hz : (i : ℕ) < 0 := by simpa [hlen x] using i.isLt
    exact (Nat.not_lt_zero _ hz).elim
  simp_rw [hx]
  simpa using (composition_card 0)

end
end CKSupport

namespace CKSupport
noncomputable section
open scoped BigOperators
/-- prepend a positive head block to a composition. -/
def compPrepend {k : ℕ} (i : Fin (k+1))
    (c : Composition ((k+1) - (i.1+1))) : Composition (k+1) where
  blocks := (i.1+1) :: c.blocks
  blocks_pos := by
    intro b hb
    rcases (List.mem_cons.mp hb) with h | h
    · omega
    · exact c.blocks_pos h
  blocks_sum := by
    simp
    omega

-- check
@[simp] lemma compPrepend_blocks {k : ℕ} (i : Fin (k+1))
    (c : Composition ((k+1)-(i.1+1))) :
    (compPrepend i c).blocks = (i.1+1)::c.blocks := rfl

noncomputable def compUnprepend (k : ℕ) (c : Composition (k+1)) :
    (Σ i : Fin (k+1), Composition ((k+1) - (i.1+1))) := by
  classical
  cases h : c.blocks with
  | nil =>
      have hh := c.blocks_sum
      simp [h] at hh
  | cons a l =>
      have ha : 0 < a := c.blocks_pos (by simp [h])
      have hsum : a + l.sum = k+1 := by simpa [h] using c.blocks_sum
      have hi : a-1 < k+1 := by omega
      let i : Fin (k+1) := ⟨a-1, hi⟩
      have htail : l.sum = (k+1)-((a-1)+1) := by omega
      let t : Composition ((k+1)-(i.1+1)) :=
        { blocks := l
          blocks_pos := by
            intro b hb
            exact c.blocks_pos (by simp [h, hb])
          blocks_sum := by
            change l.sum = (k+1)-((a-1)+1)
            exact htail }
      exact ⟨i,t⟩

-- needed simp roundtrips
lemma compUnprepend_prepend {k : ℕ} (i : Fin (k+1))
    (c : Composition ((k+1)-(i.1+1))) :
    compUnprepend k (compPrepend i c) = ⟨i,c⟩ := by
  classical
  -- unfold the list pattern and all arithmetic proof components by extensionality
  -- equality of sigma in a dependent type follows from val equality then blocks
  -- `rcases` simp unfolds pattern on the nonempty list.
  unfold compUnprepend
  dsimp [compPrepend]


lemma compPrepend_unprepend {k : ℕ} (c : Composition (k+1)) :
    compPrepend (compUnprepend k c).1 (compUnprepend k c).2 = c := by
  classical
  rcases c with ⟨blocks, pos, sum⟩
  cases blocks with
  | nil =>
      simp at sum
  | cons a l =>
      apply Composition.ext
      dsimp [compUnprepend, compPrepend]
      -- now only the arithmetic `a-1+1=a`
      have ha : 0 < a := pos (by simp)
      simp [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by omega : a ≠ 0))]

noncomputable def compEquivSucc (k : ℕ) :
    Composition (k+1) ≃ (Σ i : Fin (k+1), Composition ((k+1)-(i.1+1))) where
  toFun := compUnprepend k
  invFun := fun t => compPrepend t.1 t.2
  left_inv := compPrepend_unprepend
  right_inv := by
    intro t
    rcases t with ⟨i,c⟩
    exact compUnprepend_prepend i c

end
end CKSupport

namespace CKSupport
noncomputable section
open scoped BigOperators
lemma prod_blocks_as_list (M : ℕ → ℝ) {n : ℕ} (c : Composition n) :
    (∏ i : Fin c.length, M (c.blocksFun i)) = (c.blocks.map M).prod := by
  classical
  rw [← List.prod_ofFn]
  change (List.ofFn (M ∘ c.blocksFun)).prod = _
  rw [← List.map_ofFn]
  rw [Composition.ofFn_blocksFun]

@[simp] lemma compPrepend_length {k : ℕ} (i : Fin (k+1))
    (c : Composition ((k+1)-(i.1+1))) :
    (compPrepend i c).length = c.length + 1 := by
  simp [Composition.length, compPrepend]

lemma compPrepend_term (R : ℝ) (M : ℕ → ℝ) {k : ℕ}
    (i : Fin (k+1)) (c : Composition ((k+1)-(i.1+1))) :
    R ^ (compPrepend i c).length *
        (∏ j : Fin (compPrepend i c).length, M ((compPrepend i c).blocksFun j)) =
      (R * M (i.1+1)) *
        (R ^ c.length * (∏ j : Fin c.length, M (c.blocksFun j))) := by
  classical
  rw [prod_blocks_as_list, prod_blocks_as_list]
  rw [compPrepend_length]
  simp [compPrepend, pow_succ]
  ring

lemma compScalar_succ (R : ℝ) (M : ℕ → ℝ) (k : ℕ) :
    compScalar R M (k+1) =
      ∑ i : Fin (k+1), (R * M (i.1+1)) *
        compScalar R M ((k+1)-(i.1+1)) := by
  classical
  let e := compEquivSucc k
  let term : Composition (k+1) → ℝ := fun c =>
    R ^ c.length * ∏ j : Fin c.length, M (c.blocksFun j)
  let g : (Σ i : Fin (k+1), Composition ((k+1)-(i.1+1))) → ℝ :=
    fun t => term (compPrepend t.1 t.2)
  change (∑ c : Composition (k+1), term c) = _
  calc
    (∑ c : Composition (k+1), term c) = ∑ c : Composition (k+1), g (e c) := by
      apply Finset.sum_congr rfl
      intro c hc
      dsimp [g]
      change term c = term (compPrepend (compUnprepend k c).1 (compUnprepend k c).2)
      rw [compPrepend_unprepend]
    _ = ∑ t : (Σ i : Fin (k+1), Composition ((k+1)-(i.1+1))), g t :=
      Equiv.sum_comp e g
    _ = ∑ i : Fin (k+1), ∑ c : Composition ((k+1)-(i.1+1)),
            g ⟨i,c⟩ := by
      simpa using
        (Fintype.sum_sigma'
          (fun (i : Fin (k+1)) (c : Composition ((k+1)-(i.1+1))) => g ⟨i,c⟩))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold compScalar
      dsimp [g, term]
      -- factor out the fixed first block
      simp_rw [compPrepend_term]
      rw [Finset.mul_sum]

lemma planeMajor_as_compScalar (A R : ℝ) (k : ℕ) :
    planeMajor A R (k+1) = (if k=0 then 1 else 0) +
      A * compScalar R (planeMajor A R) k := by
  simpa [compScalar] using (planeMajor_succ A R k)

lemma planeMajor_succ_le_conv {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (k : ℕ) :
    planeMajor A R (k+2) ≤
      ∑ i : Fin (k+1),
        R * planeMajor A R (i.1+1) *
          planeMajor A R (((k+1)-(i.1+1))+1) := by
  classical
  let M : ℕ → ℝ := planeMajor A R
  have hm (n : ℕ) : 0 ≤ M n := planeMajor_nonneg hA hR n
  have hAQ (m : ℕ) : A * compScalar R M m ≤ M (m+1) := by
    change A * compScalar R (planeMajor A R) m ≤ planeMajor A R (m+1)
    rw [planeMajor_as_compScalar]
    have hd : 0 ≤ (if m=0 then (1:ℝ) else 0) := by
      split_ifs <;> norm_num
    linarith
  -- write the left coefficient through a nonempty composition
  have hk0 : k+1 ≠ 0 := Nat.succ_ne_zero _
  -- normalise the length
  change M ( (k+1)+1) ≤ _
  change M ((k+1)+1) ≤ ∑ i : Fin (k+1), R * M (i.1+1) * M (((k+1)-(i.1+1))+1)
  change planeMajor A R ((k+1)+1) ≤ _
  rw [planeMajor_as_compScalar]
  simp only [if_neg hk0, zero_add]
  rw [compScalar_succ]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hcoef : 0 ≤ R * M (i.1+1) := mul_nonneg hR (hm _)
  calc
    A * (R * M (↑i + 1) * compScalar R M (k + 1 - (↑i + 1))) =
        (R * M (i.1+1)) * (A * compScalar R M (k+1-(i.1+1))) := by ring
    _ ≤ (R * M (i.1+1)) * M ((k+1-(i.1+1))+1) :=
      mul_le_mul_of_nonneg_left (hAQ _) hcoef
    _ = _ := by rfl

end
end CKSupport

namespace CKSupport
noncomputable section
open scoped BigOperators
open Nat
lemma planeMajor_le_catalan {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    ∀ n : ℕ, planeMajor A R (n+1) ≤
      (1+A)^(n+1) * R^n * (catalan n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [planeMajor_as_compScalar]
      simp [compScalar_zero]
    | succ k =>
      -- binary convolution
      refine le_trans (planeMajor_succ_le_conv hA hR k) ?_
      -- compare each child by the induction hypothesis
      calc
        (∑ i : Fin (k+1),
            R * planeMajor A R (i.1+1) *
              planeMajor A R (((k+1)-(i.1+1))+1)) ≤
          ∑ i : Fin (k+1),
            R * ((1+A)^(i.1+1) * R^(i.1) * (catalan i.1 : ℝ)) *
              ((1+A)^(((k+1)-(i.1+1))+1) *
                R^((k+1)-(i.1+1)) *
                (catalan ((k+1)-(i.1+1)) : ℝ)) := by
                  apply Finset.sum_le_sum
                  intro i hi
                  have hK : 0 ≤ 1 + A := by linarith
                  have h1 := ih i.1 (by omega)
                  have hrem : (k+1)-(i.1+1) < (k+1) := by omega
                  have h2 := ih ((k+1)-(i.1+1)) hrem
                  have hp1 : 0 ≤ planeMajor A R (i.1+1) := planeMajor_nonneg hA hR _
                  have hb1 : 0 ≤ (1+A)^(i.1+1) * R^(i.1) * (catalan i.1 : ℝ) := by positivity
                  have hp2 : 0 ≤ planeMajor A R (((k+1)-(i.1+1))+1) :=
                    planeMajor_nonneg hA hR _
                  have hb2 : 0 ≤ (1+A)^(((k+1)-(i.1+1))+1) *
                      R^((k+1)-(i.1+1)) *
                      (catalan ((k+1)-(i.1+1)) : ℝ) := by positivity
                  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hR) h2 hp2
                    (mul_nonneg hR hb1)
        _ = (1+A)^((k+1)+1) * R^(k+1) * (catalan (k+1) : ℝ) := by
          -- the common powers telescope on every cut
          rw [catalan_succ]
          simp only [Nat.cast_sum, Nat.cast_mul]
          -- distribute the two constants over the finite convolution
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hle : i.1 ≤ k := Nat.lt_succ_iff.mp i.2
          have har : (k+1)-(i.1+1) = k-i.1 := by omega
          -- only commutative products and `i+(k-i)=k`
          rw [har]
          norm_cast
          have he : i.1 + (k - i.1) = k := Nat.add_sub_of_le hle
          -- powers split according to that equality
          have hpbase : R^k = R^i.1 * R^(k-i.1) := by
            calc
              R^k = R^(i.1 + (k-i.1)) := congrArg (fun t : ℕ => R^t) he.symm
              _ = _ := by rw [pow_add]
          have hpR : R^(k+1) = R^i.1 * R^(k-i.1) * R := by
            calc
              R^(k+1) = R^k * R := by rw [pow_succ]
              _ = (R^i.1 * R^(k-i.1)) * R := by rw [hpbase]
          rw [show k+1+1 = (i.1+1) + ((k-i.1)+1) by omega,
              pow_add, hpR]
          simp only [Nat.cast_mul]
          ring
end
end CKSupport

namespace CKSupport
noncomputable section
open scoped BigOperators
open Nat
lemma catalan_le_four (n : ℕ) : catalan n ≤ 4^n := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow n)

lemma planeMajor_geometric {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    ∀ n : ℕ, planeMajor A R n ≤
      ((1+A) * max (1:ℝ) (4*R)) ^ n := by
  intro n
  cases n with
  | zero => simp [planeMajor_zero]
  | succ m =>
    have hK : 0 ≤ 1+A := by linarith
    let L : ℝ := max (1:ℝ) (4*R)
    have hL : 0 ≤ L := by dsimp [L]; exact le_trans (by norm_num) (le_max_left _ _)
    have hL1 : 1 ≤ L := le_max_left _ _
    have h4R : 4*R ≤ L := le_max_right _ _
    calc
      planeMajor A R (m+1) ≤ (1+A)^(m+1) * R^m * (catalan m : ℝ) :=
        planeMajor_le_catalan hA hR m
      _ ≤ (1+A)^(m+1) * (R^m * (4:ℝ)^m) := by
        have hc : (catalan m : ℝ) ≤ (4:ℝ)^m := by exact_mod_cast (catalan_le_four m)
        calc
          (1+A)^(m+1) * R^m * (catalan m : ℝ)
              ≤ (1+A)^(m+1) * R^m * (4:ℝ)^m := by
                gcongr <;> positivity
          _ = _ := by ring
      _ ≤ (1+A)^(m+1) * L^(m+1) := by
        have hp : (4*R)^m ≤ L^m := pow_le_pow_left₀ (by positivity) h4R _
        calc
          (1+A)^(m+1) * (R^m * (4:ℝ)^m)
              = (1+A)^(m+1) * (4*R)^m := by ring
          _ ≤ (1+A)^(m+1) * L^m := by
                exact mul_le_mul_of_nonneg_left hp (by positivity)
          _ ≤ (1+A)^(m+1) * L^(m+1) := by
                have hs : L^m ≤ L^(m+1) :=
                  calc L^m = L^m * 1 := by ring
                       _ ≤ L^m * L := by
                        exact mul_le_mul_of_nonneg_left hL1 (by positivity)
                       _ = L^(m+1) := by rw [pow_succ]
                exact mul_le_mul_of_nonneg_left hs (by positivity)
      _ = ((1+A)* max (1:ℝ) (4*R))^(m+1) := by
        dsimp [L]
        rw [mul_pow]
end
end CKSupport

namespace CKSupport
noncomputable section
-- composition in a given degree only sees positive coefficients up to that degree
lemma comp_fmsLt_coeff {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (p : FormalMultilinearSeries ℝ Y Y)
    (b : FormalMultilinearSeries ℝ (Y×ℝ) Y)
    (k : ℕ) :
    (p.comp (fmsLt b (k+1))) k = (p.comp b) k := by
  classical
  unfold FormalMultilinearSeries.comp
  apply Finset.sum_congr rfl
  intro c hc
  -- it suffices to compare the inner block applications
  apply ContinuousMultilinearMap.ext
  intro v
  rw [FormalMultilinearSeries.compAlongComposition_apply,
      FormalMultilinearSeries.compAlongComposition_apply]
  congr 1
  funext i
  unfold FormalMultilinearSeries.applyComposition
  have hi : c.blocksFun i < k+1 := Nat.lt_succ_of_le (c.blocksFun_le i)
  simp [fmsLt, hi]

lemma odeSeries_full_succ {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (p : FormalMultilinearSeries ℝ Y Y) (k : ℕ) :
    odeSeries p (k+1) = timeAnt ((p.comp (odeSeries p)) k) +
      (if h : k=0 then h ▸ odeBoundary (Y:=Y) else 0) := by
  rw [odeSeries_succ]
  rw [comp_fmsLt_coeff]
end
end CKSupport

namespace CKSupport
noncomputable section
open scoped BigOperators Topology
lemma timeAnt_apply_zero_time {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {n : ℕ} (r : (Y×ℝ)[×n]→L[ℝ] Y) (q : Y) :
    timeAnt r (fun _ : Fin (n+1) => (q,0)) = 0 := by
  classical
  simp [timeAnt, ContinuousMultilinearMap.sum_apply,
    antTerm_apply_diag]

-- the displacement series realizes its prescribed initial parameter wherever
-- it converges: all integrated terms have a visible time factor.
lemma odeSeries_sum_initial {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y]
    (p : FormalMultilinearSeries ℝ Y Y) (q : Y) :
    (odeSeries p).sum (q, (0:ℝ)) = q := by
  classical
  unfold FormalMultilinearSeries.sum
  -- only the degree-one boundary term remains
  have hcoeff0 : odeSeries p 0 (fun _ : Fin 0 => (q,(0:ℝ))) = 0 := by
    rw [odeSeries_zero]
    simp
  have hcoeff1 : odeSeries p 1 (fun _ : Fin 1 => (q,(0:ℝ))) = q := by
    have hh := odeSeries_full_succ p 0
    simp at hh
    rw [hh]
    simp [timeAnt_apply_zero_time, odeBoundary_apply]
  have hcoeffN : ∀ n : ℕ, 2 ≤ n →
      odeSeries p n (fun _ : Fin n => (q,(0:ℝ))) = 0 := by
    intro n hn
    obtain ⟨k,hk⟩ : ∃ k, n = k+1 := by
      use n-1
      omega
    subst n
    have hk0 : k ≠ 0 := by omega
    rw [odeSeries_full_succ]
    simp [hk0, timeAnt_apply_zero_time]
  -- compute the tsum with finite support
  calc
    (∑' n : ℕ, odeSeries p n (fun _ : Fin n => (q,(0:ℝ)))) =
        odeSeries p 1 (fun _ : Fin 1 => (q,(0:ℝ))) := by
          apply tsum_eq_single 1
          intro n hn'
          by_cases h0 : n = 0
          · subst n; exact hcoeff0
          · have h2 : 2 ≤ n := by omega
            exact hcoeffN n h2
    _ = q := hcoeff1
end
end CKSupport

-- END INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/PlaneMajorBound.lean

-- BEGIN INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/FlowDerivative.lean
open Set Filter
open scoped BigOperators ENNReal NNReal Topology
namespace CKSupport
noncomputable section
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- On the domain of convergence the displacement series is the boundary
value plus the sum of its formal antiderivative terms.  This is a little
reindexing lemma; recording it separately avoids all termwise-differentiation
questions. -/
lemma odeSeries_sum_eq_add_tsum_timeAnt
    (p : FormalMultilinearSeries ℝ Y Y)
    (q : Y) (t : ℝ)
    (hbs : Summable (fun n : ℕ =>
      (odeSeries p n) (fun _ : Fin n => (q,t))))
    (hcomp : Summable (fun n : ℕ =>
      ((p.comp (odeSeries p)) n) (fun _ : Fin n => (q,t)))) :
    (odeSeries p).sum (q,t) =
      q + ∑' k : ℕ, timeAnt ((p.comp (odeSeries p)) k)
              (fun _ : Fin (k+1) => (q,t)) := by
  classical
  -- abbreviate the three coefficient families
  let a : ℕ → Y := fun n => (odeSeries p n) (fun _ : Fin n => (q,t))
  let v : ℕ → Y := fun k =>
    timeAnt ((p.comp (odeSeries p)) k) (fun _ : Fin (k+1) => (q,t))
  let e : ℕ → Y := fun k => if k = 0 then q else 0
  have h0 : a 0 = 0 := by
    dsimp [a]
    rw [odeSeries_zero]
    simp
  have hsucc : ∀ k : ℕ, a (k+1) = v k + e k := by
    intro k
    dsimp [a, v, e]
    have hk := odeSeries_full_succ p k
    -- evaluate the identity of multilinear coefficients on the diagonal
    have := congrArg
      (fun T : (Y×ℝ)[×(k+1)]→L[ℝ] Y => T (fun _ : Fin (k+1) => (q,t))) hk
    by_cases h : k = 0
    · subst k
      simpa [ContinuousMultilinearMap.add_apply, odeBoundary_apply] using this
    · simpa [ContinuousMultilinearMap.add_apply, odeBoundary_apply, h] using this
  have ha : Summable a := by simpa [a] using hbs
  have hat : Summable (fun k : ℕ => a (k+1)) := by
    have h := (summable_nat_add_iff (f:=a) 1).2 ha
    -- its conventional tail is `a (k+1)` instead of `a (k+1_right)`
    simpa [Nat.add_comm] using h
  have he : Summable e := by
    exact (hasSum_ite_eq 0 q).summable
  have hv : Summable v := by
    -- subtract the finitely supported boundary from the tail
    have hh : (fun k : ℕ => a (k+1) - e k) = v := by
      funext k
      rw [hsucc]
      abel
    rw [← hh]
    exact hat.sub he
  -- sums of the tail and the finitely supported zeroth term
  have htail : (∑' k : ℕ, a (k+1)) = (odeSeries p).sum (q,t) := by
    have hs := ha.sum_add_tsum_nat_add 1
    -- remove the initial zero coefficient
    have hsumdef : (∑' n : ℕ, a n) = (odeSeries p).sum (q,t) := by
      rfl
    simpa [Nat.add_comm, h0, hsumdef] using hs
  have heval : (∑' k : ℕ, e k) = q := by
    -- `e` is a singleton-support series
    rw [tsum_eq_single 0]
    · simp [e]
    · intro b hb
      simp [e, hb]
  calc
    (odeSeries p).sum (q,t) = ∑' k : ℕ, a (k+1) := htail.symm
    _ = ∑' k : ℕ, (v k + e k) := by
      congr 1
      funext k
      exact hsucc k
    _ = (∑' k : ℕ, v k) + (∑' k : ℕ, e k) :=
      (hv.tsum_add he)
    _ = q + ∑' k : ℕ, v k := by rw [heval]; abel
    _ = _ := by rfl

/-- Differentiating the convergent displacement series in the time
coordinate.  The radius `R` is deliberately a real nonnegative radius
strictly below both series radii; this form is convenient for applying the
uniform derivative theorem on the real interval `(-R,R)`. -/
lemma odeSeries_hasDeriv_time
    (p : FormalMultilinearSeries ℝ Y Y)
    (R : ℝ≥0)
    (hRbs : (R:ℝ≥0∞) < (odeSeries p).radius)
    (hRc : (R:ℝ≥0∞) < (p.comp (odeSeries p)).radius)
    (q : Y) (hq : ‖q‖ < (R:ℝ))
    (t : ℝ) (ht : t ∈ Set.Ioo (-(R:ℝ)) (R:ℝ)) :
    HasDerivAt (fun u : ℝ => (odeSeries p).sum (q,u))
      ((p.comp (odeSeries p)).sum (q,t)) t := by
  classical
  let r : FormalMultilinearSeries ℝ (Y×ℝ) Y := p.comp (odeSeries p)
  let g : ℕ → ℝ → Y := fun n u =>
    timeAnt (r n) (fun _ : Fin (n+1) => (q,u))
  let g' : ℕ → ℝ → Y := fun n u => r n (fun _ : Fin n => (q,u))
  let B : ℕ → ℝ := fun n => ‖r n‖ * (R:ℝ)^n
  have hR0 : 0 < (R:ℝ) := lt_of_le_of_lt (norm_nonneg q) hq
  have hsumB : Summable B := by
    dsimp [B, r]
    exact (p.comp (odeSeries p)).summable_norm_mul_pow hRc
  have hderiv : ∀ n (u : ℝ), u ∈ Set.Ioo (-(R:ℝ)) (R:ℝ) →
      HasDerivAt (g n) (g' n u) u := by
    intro n u hu
    simpa [g, g', r] using
      (timeAnt_hasDerivAt (Y:=Y) ((p.comp (odeSeries p)) n) q u)
  have hbound : ∀ n (u : ℝ), u ∈ Set.Ioo (-(R:ℝ)) (R:ℝ) →
      ‖g' n u‖ ≤ B n := by
    intro n u hu
    have huabs : |u| < (R:ℝ) := (abs_lt).2 (by simpa using hu)
    have hz : ‖(q,u)‖ ≤ (R:ℝ) := by
      rw [Prod.norm_def]
      exact max_le (le_of_lt hq)
        (le_of_lt (by simpa [Real.norm_eq_abs] using huabs))
    calc
      ‖g' n u‖ ≤ ‖r n‖ * ∏ _i : Fin n, ‖(q,u)‖ := by
        exact ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖r n‖ * ‖(q,u)‖^n := by simp
      _ ≤ ‖r n‖ * (R:ℝ)^n := by
        gcongr
      _ = B n := rfl
  have hzero : (0:ℝ) ∈ Set.Ioo (-(R:ℝ)) (R:ℝ) := by
    constructor <;> linarith
  have hg0 : Summable (fun n : ℕ => g n 0) := by
    have hz : (fun n : ℕ => g n 0) = (fun _ : ℕ => (0:Y)) := by
      funext n
      simp [g, timeAnt_apply_zero_time]
    rw [hz]
    exact summable_zero
  have H := hasDerivAt_tsum_of_isPreconnected hsumB isOpen_Ioo
      isPreconnected_Ioo hderiv hbound hzero hg0 ht
  -- points of this interval are within both balls of convergence
  have hnorm : ∀ u : ℝ, u ∈ Set.Ioo (-(R:ℝ)) (R:ℝ) →
      ‖(q,u)‖ < (R:ℝ) := by
    intro u hu
    have huabs : |u| < (R:ℝ) := (abs_lt).2 (by simpa using hu)
    rw [Prod.norm_def]
    exact max_lt hq (by simpa [Real.norm_eq_abs] using huabs)
  have hmem : ∀ u : ℝ, u ∈ Set.Ioo (-(R:ℝ)) (R:ℝ) →
      (q,u) ∈ Metric.eball (0 : Y×ℝ) (odeSeries p).radius := by
    intro u hu
    rw [Metric.mem_eball, edist_zero_right]
    calc
      ‖(q,u)‖ₑ = ENNReal.ofReal ‖(q,u)‖ := (ofReal_norm _).symm
      _ < (R:ℝ≥0∞) := (ENNReal.ofReal_lt_coe_iff (norm_nonneg _)).2 (hnorm u hu)
      _ < _ := hRbs
  have hmemc : ∀ u : ℝ, u ∈ Set.Ioo (-(R:ℝ)) (R:ℝ) →
      (q,u) ∈ Metric.eball (0 : Y×ℝ) r.radius := by
    intro u hu
    rw [Metric.mem_eball, edist_zero_right]
    calc
      ‖(q,u)‖ₑ = ENNReal.ofReal ‖(q,u)‖ := (ofReal_norm _).symm
      _ < (R:ℝ≥0∞) := (ENNReal.ofReal_lt_coe_iff (norm_nonneg _)).2 (hnorm u hu)
      _ < _ := hRc
  have heq : ∀ u : ℝ, u ∈ Set.Ioo (-(R:ℝ)) (R:ℝ) →
      (odeSeries p).sum (q,u) = q + ∑' n : ℕ, g n u := by
    intro u hu
    have hb := (odeSeries p).summable (hmem u hu)
    have hc := r.summable (hmemc u hu)
    simpa [g, r] using (odeSeries_sum_eq_add_tsum_timeAnt p q u hb (by simpa [r] using hc))
  have Hev : (fun u : ℝ => (odeSeries p).sum (q,u))
        =ᶠ[𝓝 t] (fun u : ℝ => q + ∑' n : ℕ, g n u) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact heq u hu
  have H' : HasDerivAt (fun u : ℝ => q + ∑' n : ℕ, g n u)
      (∑' n : ℕ, g' n t) t := H.const_add q
  have H'' := H'.congr_of_eventuallyEq Hev
  simpa [g', r, FormalMultilinearSeries.sum] using H''

/-- The preceding derivative, written as a Fréchet derivative of the joint
analytic sum in the distinguished time direction. -/
lemma odeSeries_fderiv_time
    (p : FormalMultilinearSeries ℝ Y Y)
    (R : ℝ≥0)
    (hRbs : (R:ℝ≥0∞) < (odeSeries p).radius)
    (hRc : (R:ℝ≥0∞) < (p.comp (odeSeries p)).radius)
    (q : Y) (hq : ‖q‖ < (R:ℝ))
    (t : ℝ) (ht : t ∈ Set.Ioo (-(R:ℝ)) (R:ℝ)) :
    fderiv ℝ (odeSeries p).sum (q,t) ((0:Y),(1:ℝ)) =
      (p.comp (odeSeries p)).sum (q,t) := by
  classical
  have HD := odeSeries_hasDeriv_time p R hRbs hRc q hq t ht
  have hnorm : ‖(q,t)‖ < (R:ℝ) := by
    have ht' : |t| < (R:ℝ) := (abs_lt).2 (by simpa using ht)
    rw [Prod.norm_def]
    exact max_lt hq (by simpa [Real.norm_eq_abs] using ht')
  have hmem : (q,t) ∈ Metric.eball (0 : Y×ℝ) (odeSeries p).radius := by
    rw [Metric.mem_eball, edist_zero_right]
    calc
      ‖(q,t)‖ₑ = ENNReal.ofReal ‖(q,t)‖ := (ofReal_norm _).symm
      _ < (R:ℝ≥0∞) := (ENNReal.ofReal_lt_coe_iff (norm_nonneg _)).2 hnorm
      _ < _ := hRbs
  have hpos : (0:ℝ≥0∞) < (odeSeries p).radius :=
    lt_of_le_of_lt (by exact bot_le) hRbs
  have hb : DifferentiableAt ℝ (odeSeries p).sum (q,t) :=
    (((odeSeries p).hasFPowerSeriesOnBall hpos).analyticAt_of_mem hmem).differentiableAt
  have hline : HasDerivAt (fun u : ℝ => (q,u)) ((0:Y),(1:ℝ)) t := by
    convert (hasDerivAt_const (x:=t) q).prodMk (hasDerivAt_id t) using 1
    funext x
    rfl
  have HC := hb.hasFDerivAt.comp_hasDerivAt t hline
  have HC' : HasDerivAt (fun u : ℝ => (odeSeries p).sum (q,u))
      (fderiv ℝ (odeSeries p).sum (q,t) ((0:Y),(1:ℝ))) t := by
    simpa [Function.comp_def] using HC
  exact HC'.unique HD
end
end CKSupport

-- END INLINED FILE: Mathlib/Support/cauchy_kovalevskaya_9676f66359/FlowDerivative.lean

-- BEGIN INLINED FILE: Main.lean

set_option maxHeartbeats 800000

open LeanEval.Analysis
open Set Filter
open scoped ENNReal NNReal Topology

namespace Submission

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem cauchy_kovalevskaya {d : ℕ}
    (F : E d × ℝ × ℝ → E d) (f : E d × ℝ × ℝ → ℝ) (u₀ : E d → ℝ)
    (_hF : AnalyticOnNhd ℝ F univ) (_hf : AnalyticOnNhd ℝ f univ)
    (_hu₀ : AnalyticOnNhd ℝ u₀ univ) (x₀ : E d) :
    ∃ (U : Set (E d × ℝ)) (u : E d × ℝ → ℝ),
      (x₀, (0 : ℝ)) ∈ U ∧ IsOpen U ∧ AnalyticOnNhd ℝ u U ∧
      (∀ x : E d, (x, (0 : ℝ)) ∈ U → u (x, 0) = u₀ x) ∧
      (∀ p ∈ U,
        fderiv ℝ u p ((0 : E d), (1 : ℝ)) =
          fderiv ℝ u p (F (p.1, p.2, u p), (0 : ℝ)) + f (p.1, p.2, u p)) ∧
      (∀ v : E d × ℝ → ℝ, AnalyticOnNhd ℝ v U →
        (∀ x : E d, (x, (0 : ℝ)) ∈ U → v (x, 0) = u₀ x) →
        (∀ p ∈ U,
          fderiv ℝ v p ((0 : E d), (1 : ℝ)) =
            fderiv ℝ v p (F (p.1, p.2, v p), (0 : ℝ)) + f (p.1, p.2, v p)) →
        ∀ p ∈ U, u p = v p) :=
/-ResultProofBegin-/ by
  classical
  -- The characteristic vector field is `(x,t,z)'=(-F,1,f)`.
  -- The remaining existence/convergence step amounts to constructing its
  -- analytic characteristic chart.  The inverse-chart calculus itself is
  -- separate: it only differentiates an identity on an open set.
  have hfield : AnalyticOnNhd ℝ (CKSupport.charField (X:=E d) F f) univ :=
    CKSupport.analyticOnNhd_charField (X:=E d) F f _hF _hf
  obtain ⟨U,V, Φ, Ψ, Z, hU,hV,hbase,hΨ,hΦ,hleft,hright,aΨ,aΦ,aZ,
      dΦ,dZ, iΨ,iZ, chart_unique⟩ :
      ∃ (U V : Set (E d × ℝ))
        (Φ Ψ : (E d × ℝ) → (E d × ℝ)) (Z : (E d × ℝ) → ℝ),
        IsOpen U ∧ IsOpen V ∧ (x₀,(0:ℝ)) ∈ U ∧
        (∀ p ∈ U, Ψ p ∈ V) ∧
        (∀ y ∈ V, Φ y ∈ U) ∧
        (∀ p ∈ U, Φ (Ψ p) = p) ∧
        (∀ y ∈ V, Ψ (Φ y) = y) ∧
        AnalyticOnNhd ℝ Ψ U ∧
        AnalyticOnNhd ℝ Φ V ∧
        AnalyticOnNhd ℝ Z V ∧
        (∀ y ∈ V, fderiv ℝ Φ y ((0:E d),(1:ℝ)) =
          (-F ((Φ y).1, (Φ y).2, Z y),(1:ℝ))) ∧
        (∀ y ∈ V, fderiv ℝ Z y ((0:E d),(1:ℝ)) =
          f ((Φ y).1, (Φ y).2, Z y)) ∧
        (∀ x : E d, (x,(0:ℝ)) ∈ U → Ψ (x,0) = (x,0)) ∧
        (∀ x : E d, (x,(0:ℝ)) ∈ U → Z (x,0) = u₀ x) ∧
        (∀ v : E d × ℝ → ℝ, AnalyticOnNhd ℝ v U →
          (∀ x : E d, (x,(0:ℝ)) ∈ U → v (x,0) = u₀ x) →
          (∀ p ∈ U, fderiv ℝ v p ((0:E d),(1:ℝ)) =
            fderiv ℝ v p (F (p.1,p.2,v p),(0:ℝ)) +
              f (p.1,p.2,v p)) →
          ∀ p ∈ U, (Z ∘ Ψ) p = v p) := by
      -- Around the initial point one can first choose coefficients for the
      -- vector field.  This is a genuine consequence of `AnalyticAt`, and
      -- does not assume an analytic flow.  It is an especially useful
      -- normalization of the open analytic-ODE step.
      have hcentre : AnalyticAt ℝ
          (CKSupport.charField (X:=E d) F f)
          (CKSupport.initialPoint u₀ x₀) :=
        hfield _ (Set.mem_univ _)
      obtain ⟨pc, ρ, C, hρ, hC, hball, hcoeff⟩ :=
        CKSupport.geometric_bound_of_analyticAt
          (E := (E d × ℝ × ℝ)) (F := (E d × ℝ × ℝ)) hcentre
      -- We record the corresponding operator-norm (rather than only
      -- pointwise) radius statement.  It is often the first missing step
      -- in an attempted Picard argument for analyticity.
      have hposrad : (0 : ℝ≥0∞) < pc.radius :=
        lt_of_lt_of_le hball.r_pos hball.r_le
      have hdiv : ∀ n : ℕ,
          ‖pc n‖ ≤ C / (ρ : ℝ)^n := by
        intro n
        exact CKSupport.coeff_le_div_of_geometric pc ρ C hρ hcoeff n
      let Acoef : ℝ≥0 := Real.toNNReal C
      have hAreal : (Acoef:ℝ) = C := by
        simp [Acoef, Real.coe_toNNReal C (le_of_lt hC)]
      have hcoeff_nn : ∀ n : ℕ, ‖pc n‖₊ ≤ Acoef * ρ⁻¹ ^ n := by
        have h' : ∀ n : ℕ, ‖pc n‖ * (ρ:ℝ)^n ≤ (Acoef:ℝ) := by
          intro n
          rw [hAreal]
          exact hcoeff n
        exact CKSupport.nnnorm_le_mul_inv_pow_of_mul_pow pc ρ Acoef hρ h'

      -- On that same ball the old formal series majorizes actual values.
      -- This scalar estimate is harmless (a single geometric series); it
      -- should not be confused with the much harder *flow* majorant.
      have hval : ∀ w : (E d × ℝ × ℝ), ‖w‖ < (ρ : ℝ) →
          ‖CKSupport.charField (X:=E d) F f
               (CKSupport.initialPoint u₀ x₀ + w)‖ ≤
             C / (1 - ‖w‖ / (ρ : ℝ)) := by
        intro w hw
        have hwball : w ∈ Metric.eball
              (0 : (E d × ℝ × ℝ)) (ρ : ℝ≥0∞) := by
          apply (Metric.mem_eball).2
          rw [edist_dist, dist_zero_right]
          have hr : 0 < (ρ : ℝ) := by exact_mod_cast hρ
          calc
            ENNReal.ofReal ‖w‖ < ENNReal.ofReal (ρ : ℝ) :=
              (ENNReal.ofReal_lt_ofReal_iff hr).2 hw
            _ = (ρ : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
        exact CKSupport.norm_fpowerSeries_le_geometric pc ρ C hρ
          (le_of_lt hC) hcoeff hw (hball.hasSum hwball)
      have hhalf : ∀ w : (E d × ℝ × ℝ), ‖w‖ ≤ (ρ : ℝ)/2 →
          ‖CKSupport.charField (X:=E d) F f
             (CKSupport.initialPoint u₀ x₀ + w)‖ ≤ 2*C := by
        intro w hw
        have hwball : w ∈ Metric.eball
              (0 : (E d × ℝ × ℝ)) (ρ : ℝ≥0∞) := by
          apply (Metric.mem_eball).2
          rw [edist_dist, dist_zero_right]
          have hr : 0 < (ρ : ℝ) := by exact_mod_cast hρ
          have hlt : ‖w‖ < (ρ : ℝ) := lt_of_le_of_lt hw (by linarith)
          calc
            ENNReal.ofReal ‖w‖ < ENNReal.ofReal (ρ : ℝ) :=
              (ENNReal.ofReal_lt_ofReal_iff hr).2 hlt
            _ = (ρ : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
        exact CKSupport.norm_fpowerSeries_le_two_mul pc ρ C hρ
          (le_of_lt hC) hcoeff hw (hball.hasSum hwball)

      -- At the formal-series level the convergence implication itself is
      -- available.  It is worth isolating it: if a later coefficient
      -- recurrence for displacements in `(q,t)` yields an *operator-norm*
      -- geometric family, its sum is analytic on a positive ball.  This
      -- follows from `le_radius_of_bound`, not from smoothness of a Picard
      -- germ.
      have hsum_upgrade : ∀
          (s : FormalMultilinearSeries ℝ
             ((E d × ℝ × ℝ) × ℝ) (E d × ℝ × ℝ))
          (r : ℝ≥0) (B : ℝ), 0 < r →
          (∀ n : ℕ, ‖s n‖ * (r:ℝ)^n ≤ B) →
          (0 : ℝ≥0∞) < s.radius ∧
            ((r:ℝ≥0∞) ≤ s.radius) ∧
            AnalyticOnNhd ℝ s.sum
              (Metric.eball (0 : ((E d × ℝ × ℝ) × ℝ))
                (r:ℝ≥0∞)) := by
        intro s r B hr hs
        exact CKSupport.analyticOnNhd_sum_of_geometric s r B hr hs

      -- Likewise, once both series have positive radius there is no
      -- set-theoretic obstruction to composing them.  The obstruction is
      -- genuinely the ODE recurrence for the parameter series, not the
      -- summability of formal block compositions.
      have hcomp_positive : ∀
          (q : FormalMultilinearSeries ℝ
             ((E d × ℝ × ℝ) × ℝ) (E d × ℝ × ℝ)),
          0 < q.radius →
          (0:ℝ≥0∞) < (pc.comp q).radius := by
        intro q hq
        exact CKSupport.comp_radius_pos pc q hposrad hq

      -- There is no topological *existence* obstruction for individual
      -- characteristics.  Mathlib's Picard--Lindelöf theorem already
      -- supplies them on a uniform small interval for a C¹ vector field.
      -- This is deliberately recorded with its exact conclusion: it gives
      -- differentiable curves, not a jointly analytic dependence on their
      -- initial points.
      have hpicard : ∃ r > (0:ℝ), ∃ ε > (0:ℝ),
          ∀ y ∈ Metric.closedBall
              (CKSupport.initialPoint u₀ x₀) r,
            ∃ α : ℝ → (E d × ℝ × ℝ), α 0 = y ∧
              ∀ t ∈ Set.Ioo (0-ε) (0+ε),
                HasDerivAt α
                  (CKSupport.charField (X:=E d) F f (α t)) t := by
        have hc1 : ContDiffAt ℝ 1
            (CKSupport.charField (X:=E d) F f)
            (CKSupport.initialPoint u₀ x₀) := hcentre.contDiffAt
        simpa using
          (ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
            hc1 (0:ℝ))

      -- We can also fix the second, sometimes hidden, topological issue
      -- with a characteristic proof: one wants *one* flow, not a family
      -- of unrelated choices of Picard curves.  On a finite-dimensional
      -- space C1 uniqueness is local (put the two curves in a compact
      -- closed ball). Consequently the Picard choices are well-defined and
      -- any curve constructed from a convergent power series will
      -- automatically be that flow.  This still says nothing about analytic
      -- dependence on the two variables.
      have hflowC1 : ∃ r > (0:ℝ), ∃ ε > (0:ℝ),
          ∃ A : (E d × ℝ × ℝ) → ℝ → (E d × ℝ × ℝ),
          ∀ y ∈ Metric.closedBall
              (CKSupport.initialPoint u₀ x₀) r,
            A y 0 = y ∧
            (∀ t ∈ Set.Ioo (-(ε:ℝ)) ε,
              HasDerivAt (A y)
                (CKSupport.charField (X:=E d) F f (A y t)) t) ∧
            ∀ β : ℝ → (E d × ℝ × ℝ), β 0 = y →
              (∀ t ∈ Set.Ioo (-(ε:ℝ)) ε,
                HasDerivAt β
                  (CKSupport.charField (X:=E d) F f (β t)) t) →
              Set.EqOn (A y) β (Set.Ioo (-(ε:ℝ)) ε) := by
        have hgC : ContDiff ℝ 1
            (CKSupport.charField (X:=E d) F f) :=
          (contDiff_iff_contDiffAt.mpr
             (fun z => (hfield z (Set.mem_univ _)).contDiffAt))
        exact CKSupport.exists_local_flow_unique_of_contDiff
          (Y := (E d × ℝ × ℝ))
          (CKSupport.charField (X:=E d) F f) hgC
          (CKSupport.initialPoint u₀ x₀)

      -- A triangular formal germ can in fact be written without any
      -- convergence choices. Splitting the multilinear inputs into time and
      -- parameter slots gives a true antiderivative (division by the number
      -- of time slots, not by the total degree). This avoids the tempting
      -- but false `1/(n+1)` total-degree integration. The remaining estimate
      -- is now precisely a geometric bound for these recursively composed
      -- coefficients.
      let bs : FormalMultilinearSeries ℝ
          ((E d × ℝ × ℝ) × ℝ) (E d × ℝ × ℝ) :=
        CKSupport.odeSeries pc
      have bs0 : bs 0 = 0 := CKSupport.odeSeries_zero pc
      have bsstep : ∀ k : ℕ,
          bs (k+1) =
            CKSupport.timeAnt
              ((pc.comp (CKSupport.fmsLt bs (k+1))) k) +
              (if h : k=0 then
                h ▸ CKSupport.odeBoundary (Y:=(E d × ℝ × ℝ)) else 0) := by
        intro k
        exact CKSupport.odeSeries_succ pc k
      have bs_bound_step : ∀ k : ℕ,
          ‖bs (k+1)‖ ≤
            (2:ℝ)^k * ‖(pc.comp (CKSupport.fmsLt bs (k+1))) k‖ +
              (if k=0 then 1 else 0) := by
        intro k
        exact CKSupport.odeSeries_succ_norm pc k
      -- There is a finite coefficient estimate for the previously opaque
      -- composition in the recursion.  Notice that no radius of `bs` is
      -- used here: the inside series is `fmsLt`, so an inductive bound on
      -- the first `k+1` coefficients is sufficient.  We first put the
      -- outside radius into `NNReal` and (only for it) shrink it below one.
      have hpc_rho : ∀ n : ℕ, ‖pc n‖₊ * ρ ^ n ≤ Acoef := by
        intro n
        apply (NNReal.coe_le_coe).1
        simpa [hAreal] using hcoeff n
      let rq : ℝ≥0 := min ρ 1
      have hrq1 : rq ≤ (1 : ℝ≥0) := by
        exact min_le_right _ _
      have hrqρ : rq ≤ ρ := by
        exact min_le_left _ _
      have hrq : 0 < rq := by
        -- both entries of this minimum are positive
        exact lt_min hρ (by norm_num)
      have hpc_rq : ∀ n : ℕ, ‖pc n‖₊ * rq ^ n ≤ Acoef := by
        intro n
        exact le_trans
          (mul_le_mul' le_rfl (pow_le_pow_left' hrqρ n))
          (hpc_rho n)
      have bs_comp_bound :
          ∀ (rb Db : ℝ≥0) (k : ℕ), 1 ≤ Db →
            (∀ m < k+1, ‖bs m‖₊ * rb ^ m ≤ Db) →
            ‖(pc.comp (CKSupport.fmsLt bs (k+1))) k‖₊ *
                (rb * rq) ^ k ≤
              (2 : ℝ≥0) ^ (k-1) * (Acoef * Db ^ k) := by
        intro rb Db k hDb hb
        have hb' : ∀ m : ℕ,
            ‖(CKSupport.fmsLt bs (k+1)) m‖₊ * rb ^ m ≤ Db :=
          CKSupport.fmsLt_nnnorm_mul_pow_le bs rb Db (k+1) hb
        exact CKSupport.comp_coeff_nnnorm_mul_pow_le
          (E := ((E d × ℝ × ℝ) × ℝ))
          (F := (E d × ℝ × ℝ)) (G := (E d × ℝ × ℝ))
          pc (CKSupport.fmsLt bs (k+1)) rq rb Acoef Db
            hrq1 hDb hpc_rq hb' k

      -- The large `2^k` in the preceding operator-norm estimate is not
      -- intrinsic to a fixed polarization.  Splitting a coefficient into
      -- its time and parameter slots, a time antiderivative has just *one*
      -- surviving summand.  The recursive estimate is therefore the
      -- following honest finite convolution; all factors on its right
      -- have strictly smaller degree.  This is often the useful starting
      -- point for a scalar (weighted-slot) majorant.
      have bs_polar_step :
          ∀ (k : ℕ) (S : Finset (Fin (k+1))),
          ‖CKSupport.splitCoeff (bs (k+1)) S‖ ≤
            (∑ c : Composition k,
                ‖pc c.length‖ *
                  ∏ i, ‖CKSupport.splitCoeff (bs (c.blocksFun i))
                    (CKSupport.blockSlots c (CKSupport.tailSlots S) i)‖) +
              (if k=0 then 1 else 0) := by
        intro k S
        simpa [bs] using
          (CKSupport.odeSeries_succ_split_norm_le_sum pc k S)


      -- Retaining the time weight is essential at the still-open majorant
      -- step.  In one fixed pattern `m` marked time slots are divided by
      -- `m`; if the distinguished first slot is not time the integral part
      -- vanishes altogether.  This strengthens `bs_polar_step`, which on
      -- purpose discards both facts.
      have bs_polar_weighted :
          ∀ (k : ℕ) (S : Finset (Fin (k+1))),
          ‖CKSupport.splitCoeff (bs (k+1)) S‖ ≤
            (if (0 : Fin (k+1)) ∈ S then
              (1 / (((CKSupport.tailSlots S).card:ℝ) + 1)) *
                (∑ c : Composition k,
                  ‖pc c.length‖ *
                    ∏ i, ‖CKSupport.splitCoeff (bs (c.blocksFun i))
                      (CKSupport.blockSlots c (CKSupport.tailSlots S) i)‖)
              else 0) + (if k=0 then 1 else 0) := by
        intro k S
        simpa [bs] using
          (CKSupport.odeSeries_succ_split_norm_le_sum_weighted pc k S)

      -- Even before solving the scalar majorant, the vector recurrence
      -- reduces to an ordinary *plane tree* one.  In contrast to
      -- `bs_comp_bound` this does not replace ordered blocks by their number
      -- `2^k`, which is too destructive to iterate.
      have hpc_real_major : ∀ l : ℕ,
          ‖pc l‖ ≤ C * ((ρ : ℝ)⁻¹)^l := by
        intro l
        simpa [div_eq_mul_inv, inv_pow] using (hdiv l)
      have hplane : ∀ (n : ℕ) (S : Finset (Fin n)),
          ‖CKSupport.splitCoeff (bs n) S‖ ≤
            CKSupport.planeMajor C ((ρ : ℝ)⁻¹) n := by
        simpa [bs] using
          (CKSupport.splitCoeff_odeSeries_le_planeMajor pc C
            ((ρ : ℝ)⁻¹) (le_of_lt hC) (by positivity)
            hpc_real_major)

      have bs_norm_of_polar :
          ∀ (D : ℝ), 0 ≤ D →
            (∀ (n : ℕ) (S : Finset (Fin n)),
              ‖CKSupport.splitCoeff (bs n) S‖ ≤ D ^ n) →
            ∀ n : ℕ, ‖bs n‖ ≤ (2*D)^n := by
        intro D hD hpat
        exact CKSupport.norm_ode_coeff_of_polar_bound bs D hD hpat

      -- Thus the remaining estimate can even be formulated as a scalar
      -- coefficient problem: any positive exponential bound for
      -- `planeMajor` gives a genuine analytic ball for the characteristic
      -- germ.  This implication is just `le_radius_of_bound`; it involves no
      -- exchange of a flow with a formal composition.
      have bs_analytic_of_plane_bound :
          ∀ (D : ℝ), 0 < D →
            (∀ n : ℕ,
              CKSupport.planeMajor C ((ρ : ℝ)⁻¹) n ≤ D ^ n) →
            ∃ r' : ℝ≥0, 0 < r' ∧
              (0 : ℝ≥0∞) < bs.radius ∧
              AnalyticOnNhd ℝ bs.sum
                (Metric.eball
                  (0 : ((E d × ℝ × ℝ) × ℝ))
                  (r':ℝ≥0∞)) := by
        intro D hD hm
        have hpat : ∀ (n : ℕ) (S : Finset (Fin n)),
            ‖CKSupport.splitCoeff (bs n) S‖ ≤ D ^ n := by
          intro n S
          exact le_trans (hplane n S) (hm n)
        have hbn : ∀ n : ℕ, ‖bs n‖ ≤ (2*D)^n :=
          CKSupport.norm_ode_coeff_of_polar_bound bs D (le_of_lt hD) hpat
        let r' : ℝ≥0 :=
          ⟨(2*D)⁻¹, le_of_lt (by positivity : (0:ℝ) < (2*D)⁻¹)⟩
        have hr' : 0 < r' := by
          exact_mod_cast (show (0:ℝ) < (2*D)⁻¹ by positivity)
        have hmul : ∀ n : ℕ, ‖bs n‖ * (r':ℝ)^n ≤ (1:ℝ) := by
          intro n
          calc
            ‖bs n‖ * (r':ℝ)^n ≤ (2*D)^n * (r':ℝ)^n := by
              exact mul_le_mul_of_nonneg_right (hbn n) (by positivity)
            _ = 1 := by
              change (2*D)^n * ((2*D)⁻¹)^n = _
              rw [← mul_pow]
              have hD0 : D ≠ 0 := ne_of_gt hD
              have heq : (2:ℝ) * D * (D⁻¹ * (2:ℝ)⁻¹) = 1 := by
                field_simp
              have hh : (2:ℝ) * D ≠ 0 := mul_ne_zero (by norm_num) hD0
              calc
                (2 * D * ((2:ℝ)*D)⁻¹) ^ n = (1:ℝ)^n := by rw [mul_inv_cancel₀ hh]
                _ = 1 := by simp
        obtain ⟨hp,hle,ha⟩ :=
          (CKSupport.analyticOnNhd_sum_of_geometric bs r' (1:ℝ)
            hr' hmul)
        exact ⟨r', hr', hp, ha⟩

      -- The scalar plane-tree recurrence has an actual positive
      -- exponential majorant.  This closes the purely convergence-theoretic
      -- part of the triangular characteristic construction.
      let D : ℝ := (1 + C) * max (1:ℝ) (4 * ((ρ:ℝ)⁻¹))
      have hD : 0 < D := by
        dsimp [D]
        have h1 : 0 < (1 + C) := by linarith
        have h2 : 0 < max (1:ℝ) (4 * ((ρ:ℝ)⁻¹)) :=
          lt_of_lt_of_le (by norm_num) (le_max_left _ _)
        positivity
      have hmplane : ∀ n : ℕ,
          CKSupport.planeMajor C ((ρ : ℝ)⁻¹) n ≤ D ^ n := by
        intro n
        simpa [D] using
          (CKSupport.planeMajor_geometric (A:=C) (R:=((ρ:ℝ)⁻¹))
            (le_of_lt hC) (by positivity) n)
      obtain ⟨rbs, hrbs, hbspos, hbsan⟩ :=
        bs_analytic_of_plane_bound D hD hmplane
      have bs_full_step : ∀ k : ℕ,
          bs (k+1) =
            CKSupport.timeAnt ((pc.comp bs) k) +
              (if h : k=0 then
                h ▸ CKSupport.odeBoundary (Y:=(E d × ℝ × ℝ)) else 0) := by
        intro k
        exact CKSupport.odeSeries_full_succ pc k
      have hbcomp_pos : (0:ℝ≥0∞) < (pc.comp bs).radius :=
        hcomp_positive bs hbspos
      have hbcomp_an : AnalyticOnNhd ℝ (pc.comp bs).sum
          (Metric.eball (0 : ((E d × ℝ × ℝ) × ℝ))
            (pc.comp bs).radius) :=
        ((pc.comp bs).hasFPowerSeriesOnBall hbcomp_pos).analyticOnNhd
      have bs_initial : ∀ q : (E d × ℝ × ℝ),
          bs.sum (q,(0:ℝ)) = q := by
        intro q
        exact CKSupport.odeSeries_sum_initial pc q

      have hbsAt : HasFPowerSeriesAt bs.sum bs
          (0 : ((E d × ℝ × ℝ) × ℝ)) :=
        (bs.hasFPowerSeriesOnBall hbspos).hasFPowerSeriesAt
      have hpcAt : HasFPowerSeriesAt pc.sum pc
          (0 : (E d × ℝ × ℝ)) :=
        (pc.hasFPowerSeriesOnBall hposrad).hasFPowerSeriesAt
      have hbsz : bs.sum (0 : ((E d × ℝ × ℝ) × ℝ)) = 0 := by
        convert (bs_initial (0 : (E d × ℝ × ℝ))) using 1 <;>
          ext <;> rfl
      have hcomAt : HasFPowerSeriesAt (pc.sum ∘ bs.sum) (pc.comp bs)
          (0 : ((E d × ℝ × ℝ) × ℝ)) := by
        have hh : HasFPowerSeriesAt pc.sum pc
            (bs.sum (0 : ((E d × ℝ × ℝ) × ℝ))) := by simpa [hbsz] using hpcAt
        exact hh.comp hbsAt
      have hbcAt : HasFPowerSeriesAt (pc.comp bs).sum (pc.comp bs)
          (0 : ((E d × ℝ × ℝ) × ℝ)) :=
        ((pc.comp bs).hasFPowerSeriesOnBall hbcomp_pos).hasFPowerSeriesAt
      have comp_germ : (pc.comp bs).sum =ᶠ[nhds (0 : ((E d × ℝ × ℝ) × ℝ))]
          (pc.sum ∘ bs.sum) := by
        have h1 := hbcAt.eventually_hasSum
        have h2 := hcomAt.eventually_hasSum
        -- both assertions are expressed on increments away from the origin
        filter_upwards [h1, h2] with z hz hz'
        simpa using hz.unique hz'
      -- There is a uniform real radius on which the convergent
      -- displacement series actually differentiates in the time variable.
      -- This is the formerly missing passage from the finite `timeAnt`
      -- identity to the summed analytic one.
      have hminrad : (0:ℝ≥0∞) <
          min bs.radius (pc.comp bs).radius :=
        lt_min hbspos hbcomp_pos
      obtain ⟨Rflow, hRflow0, hRflowlt⟩ :=
        (ENNReal.lt_iff_exists_nnreal_btwn).1 hminrad
      have hRbs : (Rflow:ℝ≥0∞) < bs.radius :=
        lt_of_lt_of_le hRflowlt (min_le_left _ _)
      have hRc : (Rflow:ℝ≥0∞) < (pc.comp bs).radius :=
        lt_of_lt_of_le hRflowlt (min_le_right _ _)
      have hRreal : 0 < Rflow := (ENNReal.coe_pos).1 hRflow0
      have flow_time : ∀ q : (E d × ℝ × ℝ), ‖q‖ < (Rflow:ℝ) →
          ∀ t : ℝ, t ∈ Set.Ioo (-(Rflow:ℝ)) (Rflow:ℝ) →
          fderiv ℝ bs.sum (q,t) ((0 : (E d × ℝ × ℝ)),(1:ℝ)) =
            (pc.comp bs).sum (q,t) := by
        intro q hq t ht
        exact CKSupport.odeSeries_fderiv_time
          pc Rflow hRbs hRc q hq t ht

      have bs_cont0 : ContinuousAt bs.sum
          (0 : ((E d × ℝ × ℝ) × ℝ)) := hbsAt.continuousAt
      have hsmall : ∀ᶠ z : ((E d × ℝ × ℝ) × ℝ)
          in 𝓝 (0 : ((E d × ℝ × ℝ) × ℝ)),
            bs.sum z ∈ Metric.eball (0 : (E d × ℝ × ℝ))
               (ρ:ℝ≥0∞) := by
        have hm0 : Metric.eball (0 : (E d × ℝ × ℝ)) (ρ:ℝ≥0∞)
            ∈ 𝓝 (0 : (E d × ℝ × ℝ)) :=
          Metric.eball_mem_nhds _ (by exact_mod_cast hρ)
        have hm1 : Metric.eball (0 : (E d × ℝ × ℝ)) (ρ:ℝ≥0∞)
            ∈ 𝓝 (bs.sum (0 : ((E d × ℝ × ℝ) × ℝ))) := by
          rw [hbsz]
          exact hm0
        exact bs_cont0.preimage_mem_nhds hm1
      have flow_rhs_germ :
          (pc.comp bs).sum =ᶠ[nhds
              (0 : ((E d × ℝ × ℝ) × ℝ))]
            (fun z => CKSupport.charField (X:=E d) F f
                 (CKSupport.initialPoint u₀ x₀ + bs.sum z)) := by
        filter_upwards [comp_germ, hsmall] with z heq hzin
        rw [heq]
        change pc.sum (bs.sum z) = _
        -- the coefficients `pc` were chosen for the original vector field
        exact (hball.hasSum hzin).tsum_eq.symm.symm

      have fqevent : ∀ᶠ z : ((E d × ℝ × ℝ) × ℝ)
          in 𝓝 (0 : ((E d × ℝ × ℝ) × ℝ)),
            ‖z.1‖ < (Rflow:ℝ) := by
        have hop : IsOpen {q : (E d × ℝ × ℝ) | ‖q‖ < (Rflow:ℝ)} :=
          isOpen_lt continuous_norm continuous_const
        have hnh : {q : (E d × ℝ × ℝ) | ‖q‖ < (Rflow:ℝ)}
            ∈ 𝓝 (0 : (E d × ℝ × ℝ)) :=
          hop.mem_nhds (by simpa using hRreal)
        have hf : ContinuousAt
            (fun z : ((E d × ℝ × ℝ) × ℝ) => z.1)
            (0 : ((E d × ℝ × ℝ) × ℝ)) := continuous_fst.continuousAt
        exact hf.preimage_mem_nhds hnh
      have ftevent : ∀ᶠ z : ((E d × ℝ × ℝ) × ℝ)
          in 𝓝 (0 : ((E d × ℝ × ℝ) × ℝ)),
            z.2 ∈ Set.Ioo (-(Rflow:ℝ)) (Rflow:ℝ) := by
        have hRr : (0:ℝ) < (Rflow:ℝ) := by exact_mod_cast hRreal
        have hz0 : (0:ℝ) ∈ Set.Ioo (-(Rflow:ℝ)) (Rflow:ℝ) := by
          constructor <;> linarith
        have hnh : Set.Ioo (-(Rflow:ℝ)) (Rflow:ℝ) ∈ 𝓝 (0:ℝ) :=
          isOpen_Ioo.mem_nhds hz0
        -- spelling the membership directly avoids a change of product charts
        have hf : ContinuousAt
            (fun z : ((E d × ℝ × ℝ) × ℝ) => z.2)
            (0 : ((E d × ℝ × ℝ) × ℝ)) := continuous_snd.continuousAt
        exact hf.preimage_mem_nhds hnh
      have flow_field_germ :
          (fun z : ((E d × ℝ × ℝ) × ℝ) =>
            fderiv ℝ bs.sum z
              ((0 : (E d × ℝ × ℝ)),(1:ℝ))) =ᶠ[nhds
              (0 : ((E d × ℝ × ℝ) × ℝ))]
          (fun z => CKSupport.charField (X:=E d) F f
                 (CKSupport.initialPoint u₀ x₀ + bs.sum z)) := by
        filter_upwards [flow_rhs_germ, fqevent, ftevent] with z hz hqz htz
        rw [flow_time z.1 hqz z.2 htz]
        exact hz

      -- `flow_time` is the delicate passage from the formal time
      -- antiderivative to the analytic equation.  Its proof (in
      -- `FlowDerivative`) fixes a parameter `q`, works on the open interval
      -- `(-Rflow,Rflow)`, and applies `hasDerivAt_tsum_of_isPreconnected`
      -- to the family `timeAnt ((pc.comp bs) k)`. The derivative series is
      -- bounded on that interval by
      -- `‖(pc.comp bs) k‖ * Rflow^k`, hence summable strictly below the
      -- composition radius.  Reindexing `bs_full_step` removes the unique
      -- degree-one boundary term.  The resulting uniform derivative is then
      -- the Frechet derivative of the joint analytic series.  Thus the germ
      -- `flow_field_germ` is an actual analytic ODE flow germ, not merely a
      -- coefficient identity.
      --
      -- To produce the advertised local characteristic chart from this germ
      -- one must now restrict it to the analytic initial submanifold
      -- `(x,0,u₀ x)`, apply the analytic inverse function theorem to its
      -- `(x,t)` projection, and use ODE uniqueness for this single flow.
      -- The flow is in displacement coordinates.  Inserting the analytic
      -- initial graph gives the map to which the inverse theorem is applied.
      let P : (E d × ℝ) → (E d × ℝ) :=
        CKSupport.graphPhi bs.sum u₀ x₀
      let Zh : (E d × ℝ) → ℝ :=
        CKSupport.graphZ bs.sum u₀ x₀
      have hU0a : AnalyticAt ℝ u₀ x₀ := _hu₀ x₀ (Set.mem_univ _)
      have hPa : AnalyticAt ℝ P (x₀,(0:ℝ)) := by
        dsimp [P]
        exact CKSupport.analyticAt_graphPhi_base hU0a hbsAt.analyticAt
      have hZa : AnalyticAt ℝ Zh (x₀,(0:ℝ)) := by
        dsimp [Zh]
        exact CKSupport.analyticAt_graphZ_base hU0a hbsAt.analyticAt
      have hP0 : ∀ x:E d, P (x,0) = (x,0) := by
        intro x
        exact CKSupport.graphPhi_zero bs.sum bs_initial x
      have hZ0 : ∀ x:E d, Zh (x,0) = u₀ x := by
        intro x
        exact CKSupport.graphZ_zero bs.sum bs_initial x
      -- Isolate the one remaining algebraic calculation for the inverse
      -- step: the derivative is the triangular shear `(v,s) ↦
      -- (v-s F(c),s)`. All inverse analyticity after that fact uses only a
      -- germ, so there is no unjustified global inverse-`ContDiff` step.
      let sh : (E d × ℝ) ≃L[ℝ] (E d × ℝ) :=
        CKSupport.shear (F (CKSupport.initialPoint u₀ x₀))
      have hfc0 : fderiv ℝ bs.sum
            (0 : ((E d × ℝ × ℝ) × ℝ))
            ((0 : (E d × ℝ × ℝ)),(1:ℝ)) =
          CKSupport.charField (X:=E d) F f
            (CKSupport.initialPoint u₀ x₀) := by
        have hh := flow_field_germ.self_of_nhds
        simpa [hbsz] using hh
      have hbsSpace : ∀ w : (E d × ℝ × ℝ),
          fderiv ℝ bs.sum (0 : ((E d × ℝ × ℝ) × ℝ)) (w,0) = w := by
        intro w
        exact CKSupport.fderiv_B_space0 bs_initial hbsAt.differentiableAt w
      have hparTime : fderiv ℝ (CKSupport.initPar u₀ x₀)
            (x₀,(0:ℝ)) ((0:E d),(1:ℝ)) =
          ((0 : E d × ℝ × ℝ),(1:ℝ)) := by
        exact CKSupport.fderiv_initPar_time hU0a
      have hparSpace : ∀ w:E d,
          (fderiv ℝ (CKSupport.initPar u₀ x₀)
            (x₀,(0:ℝ)) (w,(0:ℝ))).1.1 = w ∧
          (fderiv ℝ (CKSupport.initPar u₀ x₀)
            (x₀,(0:ℝ)) (w,(0:ℝ))).2 = 0 := by
        intro w
        exact CKSupport.fderiv_initPar_space_base hU0a w
      have hinv_if : fderiv ℝ P (x₀,(0:ℝ)) =
          (sh : (E d × ℝ) →L[ℝ] (E d × ℝ)) →
          ∃ H : OpenPartialHomeomorph (E d × ℝ) (E d × ℝ),
            (H : (E d × ℝ) → (E d × ℝ)) = P ∧
            (x₀,(0:ℝ)) ∈ H.source ∧ H (x₀,(0:ℝ)) = P (x₀,0) ∧
            (∃ S ∈ 𝓝 (x₀,(0:ℝ)), IsOpen S ∧ S ⊆ H.source ∧
              AnalyticOnNhd ℝ P S) ∧
            (∃ T ∈ 𝓝 (P (x₀,(0:ℝ))), IsOpen T ∧ T ⊆ H.target ∧
              AnalyticOnNhd ℝ (H.symm : (E d × ℝ) → (E d × ℝ)) T) := by
        intro hlin
        exact CKSupport.analytic_local_inverse_germ P (x₀,(0:ℝ)) sh hPa hlin
      have hPlin : fderiv ℝ P (x₀,(0:ℝ)) =
          (sh : (E d × ℝ) →L[ℝ] (E d × ℝ)) := by
        dsimp [P, sh]
        -- the last coordinate of the centre vector field does not enter the projection
        apply CKSupport.fderiv_graphPhi_base_eq_shear
          (B:=bs.sum) (u0:=u₀) (x0:=x₀)
          (a:= F (CKSupport.initialPoint u₀ x₀))
          (gval:= f (CKSupport.initialPoint u₀ x₀)) hU0a hbsAt.analyticAt bs_initial
        simpa [CKSupport.charField] using hfc0
      obtain ⟨H,hHP,hHa,hHval, ⟨S,hSnh,hSo,hSsub,hSa⟩,
          ⟨T,hTnh,hTo,hTsub,hTa⟩⟩ := hinv_if hPlin
      -- Pull all germ conditions back to the parameter plane and then choose a
      -- rectangle; taking full time fibres is what is needed for uniqueness.
      let GoodZ : Set (((E d × ℝ × ℝ) × ℝ)) :=
        {z | fderiv ℝ bs.sum z ((0:E d × ℝ × ℝ),(1:ℝ)) =
          CKSupport.charField (X:=E d) F f
            (CKSupport.initialPoint u₀ x₀ + bs.sum z)}
      have hGood : GoodZ ∈ 𝓝 (0 : ((E d × ℝ × ℝ) × ℝ)) := by
        exact flow_field_germ
      have hparcont : Continuous (CKSupport.initPar u₀ x₀) := by
        rw [continuous_iff_continuousAt]; intro y
        exact (CKSupport.analyticAt_initPar (u0:=u₀)
          (_hu₀ y.1 (Set.mem_univ _)) x₀).continuousAt
      have hBball : Metric.eball (0 : ((E d × ℝ × ℝ) × ℝ))
            (rbs:ℝ≥0∞) ∈ 𝓝 (0 : ((E d × ℝ × ℝ) × ℝ)) :=
        Metric.eball_mem_nhds _ (by exact_mod_cast hrbs)
      let W : Set (E d × ℝ) :=
        S ∩ P ⁻¹' T ∩
          (CKSupport.initPar u₀ x₀) ⁻¹'
            (GoodZ ∩ Metric.eball
                (0 : ((E d × ℝ × ℝ) × ℝ)) (rbs:ℝ≥0∞))
      have hWnh : W ∈ 𝓝 (x₀,(0:ℝ)) := by
        dsimp [W]
        have hpT : P ⁻¹' T ∈ 𝓝 (x₀,(0:ℝ)) := by
          have : T ∈ 𝓝 (P (x₀,(0:ℝ))) := hTnh
          exact hPa.continuousAt.preimage_mem_nhds this
        have hp0 : ContinuousAt (CKSupport.initPar u₀ x₀) (x₀,(0:ℝ)) :=
          hparcont.continuousAt
        have hpG : (CKSupport.initPar u₀ x₀) ⁻¹'
            (GoodZ ∩ Metric.eball (0 : ((E d × ℝ × ℝ) × ℝ))
              (rbs:ℝ≥0∞)) ∈ 𝓝 (x₀,(0:ℝ)) := by
          apply hp0.preimage_mem_nhds
          simpa using (inter_mem hGood hBball)
        exact inter_mem (inter_mem hSnh hpT) hpG
      obtain ⟨O,hOW,hOo,hOa⟩ := (mem_nhds_iff.mp hWnh)
      obtain ⟨δ,hδ,hδsub⟩ := (Metric.mem_nhds_iff.mp (hOo.mem_nhds hOa))
      let r : ℝ := δ/2
      have hr : 0 < r := by dsimp [r]; linarith
      let N : Set (E d) := Metric.ball x₀ r
      let I : Set ℝ := Set.Ioo (-r) r
      let V' : Set (E d × ℝ) := N ×ˢ I
      have hV'o : IsOpen V' := Metric.isOpen_ball.prod isOpen_Ioo
      have hbsub : V' ⊆ O := by
        intro y hy
        apply hδsub
        have h1 : dist y.1 x₀ < r := hy.1
        have h2 : dist y.2 0 < r := by
          rw [Real.dist_eq]
          simpa using ( (abs_lt).2 (show -r < y.2 ∧ y.2 < r from hy.2))
        rw [Metric.mem_ball, Prod.dist_eq]
        exact lt_of_le_of_lt (max_le (le_of_lt h1) (le_of_lt h2)) (by dsimp [r]; linarith)
      have hVW : V' ⊆ W := fun z hz => hOW (hbsub hz)
      have hVs : V' ⊆ H.source := fun z hz => hSsub (hVW hz).1.1
      let U' : Set (E d × ℝ) := H '' V'
      have hU'o : IsOpen U' := H.isOpen_image_of_subset_source hV'o hVs
      have hUt : U' ⊆ H.target := by
        intro p hp; obtain ⟨y,hy,rfl⟩ := hp
        exact H.map_source (hVs hy)
      have hUT : U' ⊆ T := by
        intro p hp
        obtain ⟨y,hy,rfl⟩ := hp
        have hh := hVW hy
        have hpt : P y ∈ T := hh.1.2
        simpa [hHP] using hpt
      have hxV : (x₀,(0:ℝ)) ∈ V' := by
        constructor
        · exact Metric.mem_ball_self hr
        · constructor <;> linarith
      have hxU : (x₀,(0:ℝ)) ∈ U' := by
        refine ⟨(x₀,(0:ℝ)), hxV, ?_⟩
        simpa [hHP, hP0]
      -- Inside the rectangle both the projection and its height satisfy the
      -- characteristic equations.
      have aP' : AnalyticOnNhd ℝ P V' := by
        intro y hy; exact hSa y (hVW hy).1.1
      have aZ' : AnalyticOnNhd ℝ Zh V' := by
        intro y hy
        have hz := (hVW hy).2
        have han : AnalyticAt ℝ bs.sum (CKSupport.initPar u₀ x₀ y) :=
          hbsan _ hz.2
        exact CKSupport.analyticAt_graphZ (B:=bs.sum)
          (_hu₀ y.1 (Set.mem_univ _)) han
      have aPhi' : AnalyticOnNhd ℝ P V' := aP'
      have dP' : ∀ y ∈ V', fderiv ℝ P y ((0:E d),(1:ℝ)) =
           (-F ((P y).1, (P y).2, Zh y), (1:ℝ)) := by
        intro y hy
        have hz := (hVW hy).2
        have hbAt : AnalyticAt ℝ bs.sum (CKSupport.initPar u₀ x₀ y) := hbsan _ hz.2
        dsimp [P, Zh]
        rw [CKSupport.fderiv_graphPhi_time
          (_hu₀ y.1 (Set.mem_univ _)) hbAt]
        rw [show fderiv ℝ bs.sum (CKSupport.initPar u₀ x₀ y)
           ((0:E d × ℝ × ℝ),(1:ℝ)) =
           CKSupport.charField (X:=E d) F f
             (CKSupport.initialPoint u₀ x₀ +
                bs.sum (CKSupport.initPar u₀ x₀ y)) from hz.1]
        rfl
      have dZ' : ∀ y ∈ V', fderiv ℝ Zh y ((0:E d),(1:ℝ)) =
           f ((P y).1, (P y).2, Zh y) := by
        intro y hy
        have hz := (hVW hy).2
        have hbAt : AnalyticAt ℝ bs.sum (CKSupport.initPar u₀ x₀ y) := hbsan _ hz.2
        dsimp [Zh, P]
        rw [CKSupport.fderiv_graphZ_time
          (_hu₀ y.1 (Set.mem_univ _)) hbAt]
        rw [show fderiv ℝ bs.sum (CKSupport.initPar u₀ x₀ y)
           ((0:E d × ℝ × ℝ),(1:ℝ)) =
           CKSupport.charField (X:=E d) F f
             (CKSupport.initialPoint u₀ x₀ +
                bs.sum (CKSupport.initPar u₀ x₀ y)) from hz.1]
        rfl
      have lineDer (ξ : E d) (t : ℝ) :
          HasDerivAt (fun s : ℝ => (ξ,s)) ((0:E d),(1:ℝ)) t := by
        convert ( (hasDerivAt_const (x:=t) ξ).prodMk (hasDerivAt_id t)) using 1 <;>
          ext <;> rfl
      have Pcurve : ∀ ξ ∈ N, ∀ t ∈ I,
          HasDerivAt (fun s : ℝ => P (ξ,s))
            (-F ((P (ξ,t)).1,(P (ξ,t)).2, Zh (ξ,t)),(1:ℝ)) t := by
        intro ξ hξ t ht
        have hh := ((aP' (ξ,t) ⟨hξ,ht⟩).differentiableAt.hasFDerivAt).comp_hasDerivAt t
             (lineDer ξ t)
        change HasDerivAt (P ∘ fun s : ℝ => (ξ,s)) _ t at hh
        convert hh using 1
        · rfl
        · exact (dP' (ξ,t) ⟨hξ,ht⟩).symm
      have Zcurve : ∀ ξ ∈ N, ∀ t ∈ I,
          HasDerivAt (fun s : ℝ => Zh (ξ,s))
            (f ((P (ξ,t)).1,(P (ξ,t)).2, Zh (ξ,t))) t := by
        intro ξ hξ t ht
        have hh := ((aZ' (ξ,t) ⟨hξ,ht⟩).differentiableAt.hasFDerivAt).comp_hasDerivAt t
             (lineDer ξ t)
        change HasDerivAt (Zh ∘ fun s : ℝ => (ξ,s)) _ t at hh
        convert hh using 1
        · rfl
        · exact (dZ' (ξ,t) ⟨hξ,ht⟩).symm
      have timeCurve : ∀ ξ ∈ N, ∀ t ∈ I,
          HasDerivAt (fun s : ℝ => (P (ξ,s)).2) 1 t := by
        intro ξ hξ t ht
        have hc := (hasFDerivAt_snd (𝕜:=ℝ)
          (p:= P (ξ,t))).comp_hasDerivAt t (Pcurve ξ hξ t ht)
        change HasDerivAt (Prod.snd ∘ fun s : ℝ => P (ξ,s)) 1 t at hc
        exact hc
      have tmem : (0:ℝ) ∈ I := by change -r < 0 ∧ (0:ℝ)<r; constructor <;> linarith
      have htimeEq : ∀ ξ ∈ N, ∀ t ∈ I, (P (ξ,t)).2 = t := by
        intro ξ hξ
        have hd : Set.EqOn (deriv (fun t : ℝ => (P (ξ,t)).2))
             (deriv (fun t : ℝ => t)) I := by
          intro t ht
          rw [(timeCurve ξ hξ t ht).deriv]
          simpa using (hasDerivAt_id t).deriv
        have he := (isOpen_Ioo : IsOpen I).eqOn_of_deriv_eq
              isPreconnected_Ioo
              (fun t ht => (timeCurve ξ hξ t ht).differentiableAt.differentiableWithinAt)
              (fun t ht => differentiableAt_id.differentiableWithinAt)
              hd tmem (by simpa [hP0])
        intro t ht; exact he ht
      let Ps : (E d × ℝ) → (E d × ℝ) := (H.symm : (E d × ℝ) → (E d × ℝ))
      have hPsiMem : ∀ p ∈ U', Ps p ∈ V' := by
        intro p hp
        obtain ⟨y,hy,hyp⟩ := hp
        change H.symm p ∈ V'
        have := H.left_inv (hVs hy)
        rw [← hyp]
        simpa using (show H.symm (H y) ∈ V' from (by simpa [this] using hy))
      have hPhiMem : ∀ y ∈ V', P y ∈ U' := by
        intro y hy
        exact ⟨y, hy, by simp [hHP]⟩
      have hleft' : ∀ p ∈ U', P (Ps p) = p := by
        intro p hp
        have hpt := hUt hp
        simpa [Ps, ← hHP] using H.right_inv hpt
      have hright' : ∀ y ∈ V', Ps (P y) = y := by
        intro y hy
        simpa [Ps, ← hHP] using H.left_inv (hVs hy)
      have ai' : AnalyticOnNhd ℝ Ps U' := by
        intro p hp
        exact hTa p (hUT hp)
      have izeroPsi : ∀ x : E d, (x,(0:ℝ)) ∈ U' → Ps (x,0) = (x,0) := by
        intro x hx
        obtain ⟨y,hy,hyp⟩ := hx
        have hty : y.2 = 0 := by
          have he := htimeEq y.1 hy.1 y.2 hy.2
          have hp2 : (P y).2 = 0 := by
            rw [← hHP]
            simpa using congrArg Prod.snd hyp
          simpa [hp2] using he.symm
        have hy0 : y = (y.1,(0:ℝ)) := by ext <;> simp [hty]
        have hp0 : P y = (y.1,0) := by rw [hy0]; exact hP0 y.1
        have hyp' : P y = (x,0) := by simpa [hHP] using hyp
        have hxid : x = y.1 := by
          have hp' : (y.1,(0:ℝ)) = (x,0) := hp0.symm.trans hyp'
          exact (congrArg Prod.fst hp').symm
        have hhh : Ps (P y) = y := hright' y hy
        rw [hyp', hy0, ← hxid] at hhh
        exact hhh
      have izeroZ : ∀ x : E d, (x,(0:ℝ)) ∈ U' → Zh (x,0) = u₀ x := by
        intro x hx; exact hZ0 x
      refine ⟨U', V', P, Ps, Zh, hU'o, hV'o, hxU,
        hPsiMem, hPhiMem, hleft', hright', ai', aPhi', aZ',
        dP', dZ', izeroPsi, izeroZ, ?_⟩
      intro v av iv pv p hp
      -- On each full fibre the analytic graph is quite literally a
      -- characteristic (including the height).  This is the useful exact
      -- one-dimensional formulation for the remaining uniqueness step.
      have xCurve : ∀ ξ ∈ N, ∀ t ∈ I,
          HasDerivAt (fun s : ℝ => (P (ξ,s)).1)
             (- F ((P (ξ,t)).1,(P (ξ,t)).2,Zh (ξ,t))) t := by
        intro ξ hξ t ht
        have hc := (hasFDerivAt_fst (𝕜:=ℝ)
          (p:=P (ξ,t))).comp_hasDerivAt t (Pcurve ξ hξ t ht)
        change HasDerivAt (Prod.fst ∘ fun s : ℝ => P (ξ,s)) _ t at hc
        exact hc
      have fullCurve : ∀ ξ ∈ N, ∀ t ∈ I,
          HasDerivAt
            (fun s : ℝ =>
              ((P (ξ,s)).1, (P (ξ,s)).2, Zh (ξ,s)))
            (CKSupport.charField (X:=E d) F f
              ((P (ξ,t)).1, (P (ξ,t)).2, Zh (ξ,t))) t := by
        intro ξ hξ t ht
        have h1 := xCurve ξ hξ t ht
        have h2 := timeCurve ξ hξ t ht
        have h3 := Zcurve ξ hξ t ht
        have hh := h1.prodMk (h2.prodMk h3)
        simpa [CKSupport.charField] using hh
      have lift_init : ∀ ξ ∈ N,
          ((P (ξ,(0:ℝ))).1, (P (ξ,(0:ℝ))).2, Zh (ξ,(0:ℝ))) =
             CKSupport.initialPoint u₀ ξ := by
        intro ξ
        simp [hP0, hZ0, CKSupport.initialPoint]
      -- For an arbitrary analytic solution the lifted characteristic has a
      -- different spatial foot (its derivative involves `F(...,v)`).  To
      -- finish one now integrates *that* characteristic backward to the
      -- zero slice and compares it with `fullCurve`, using local ODE
      -- uniqueness.  All convergence, inverse-chart, and genuine-time
      -- identities used by this comparison are above.
      have hy : Ps p ∈ V' := hPsiMem p hp
      let ξ : E d := (Ps p).1
      let τ : ℝ := (Ps p).2
      have hξ : ξ ∈ N := hy.1
      have hτ : τ ∈ I := hy.2
      have hpback : P (ξ,τ) = p := by
        simpa [ξ, τ] using (hleft' p hp)
      let PL : ℝ → (E d × ℝ) := fun t => P (ξ,t)
      let ZL : ℝ → ℝ := fun t => Zh (ξ,t)
      have hPLmem : ∀ t ∈ I, PL t ∈ U' := by
        intro t ht
        exact hPhiMem (ξ,t) ⟨hξ, ht⟩
      have hPL : ∀ t ∈ I,
          HasDerivAt PL
            (- F ((PL t).1,(PL t).2,ZL t),(1:ℝ)) t := by
        intro t ht
        simpa [PL, ZL] using (Pcurve ξ hξ t ht)
      have hZL : ∀ t ∈ I,
          HasDerivAt ZL (f ((PL t).1,(PL t).2,ZL t)) t := by
        intro t ht
        simpa [PL, ZL] using (Zcurve ξ hξ t ht)
      have hVL : ∀ t ∈ I,
          HasDerivAt (fun s : ℝ => v (PL s))
            (f ((PL t).1,(PL t).2, v (PL t)) +
              fderiv ℝ v (PL t)
                (F ((PL t).1,(PL t).2, v (PL t)) -
                  F ((PL t).1,(PL t).2,ZL t), (0:ℝ))) t := by
        intro t ht
        exact CKSupport.hasDerivAt_along_chart (X:=E d)
          F f ZL PL v t (hPL t ht)
          ((av _ (hPLmem t ht)).differentiableAt)
          (pv _ (hPLmem t ht))
      let G : (ℝ × ℝ) → (ℝ × ℝ) :=
        CKSupport.comparisonField F f v PL ZL
      let aa : ℝ → (ℝ × ℝ) := fun t => (t, ZL t)
      let bb : ℝ → (ℝ × ℝ) := fun t => (t, v (PL t))
      have haa : ∀ t ∈ Set.Ioo (-r) r,
          HasDerivAt aa (G (aa t)) t := by
        intro t ht
        have hz : t ∈ I := ht
        simpa [aa, G] using
          (CKSupport.hasDerivAt_comparison_Z (X:=E d)
            F f v PL ZL t (hZL t hz))
      have hbb : ∀ t ∈ Set.Ioo (-r) r,
          HasDerivAt bb (G (bb t)) t := by
        intro t ht
        have hz : t ∈ I := ht
        simpa [bb, G] using
          (CKSupport.hasDerivAt_comparison_v (X:=E d)
            F f v PL ZL t (hVL t hz))
      have hloc : ∀ t ∈ Set.Ioo (-r) r,
          ContDiffAt ℝ 1 G (aa t) := by
        intro t ht
        have hz : t ∈ I := ht
        have hline : ContDiffAt ℝ 1 (fun s : ℝ => (ξ,s)) t := by
          exact (contDiffAt_const (𝕜:=ℝ)).prodMk
            (by change ContDiffAt ℝ 1 id t; exact contDiffAt_id)
        have hpca : ContDiffAt ℝ 1 PL t := by
          have hpa : ContDiffAt ℝ 1 P (ξ,t) :=
            (aP' (ξ,t) ⟨hξ,hz⟩).contDiffAt
          convert hpa.comp (x:=t) hline using 1 <;> rfl
        have hzca : ContDiffAt ℝ 1 ZL t := by
          have hza : ContDiffAt ℝ 1 Zh (ξ,t) :=
            (aZ' (ξ,t) ⟨hξ,hz⟩).contDiffAt
          convert hza.comp (x:=t) hline using 1 <;> rfl
        have hdva : ContDiffAt ℝ 1 (fderiv ℝ v) (PL t) :=
          ((av.fderiv) (PL t) (hPLmem t hz)).contDiffAt
        have hfda : ∀ q : E d × ℝ × ℝ, ContDiffAt ℝ 1 F q := by
          intro q; exact (_hF q (Set.mem_univ _)).contDiffAt
        have hfdb : ∀ q : E d × ℝ × ℝ, ContDiffAt ℝ 1 f q := by
          intro q; exact (_hf q (Set.mem_univ _)).contDiffAt
        simpa [G, aa] using
          (CKSupport.contDiffAt_comparisonField (X:=E d)
            F f v PL ZL t (ZL t) hpca hzca hdva hfda hfdb)
      have h0i : (0:ℝ) ∈ Set.Ioo (-r) r := by
        constructor <;> linarith
      have heq0 : aa 0 = bb 0 := by
        have hV0 : (ξ,(0:ℝ)) ∈ V' := ⟨hξ, tmem⟩
        have hU0 : (ξ,(0:ℝ)) ∈ U' := by
          have hu := hPhiMem (ξ,(0:ℝ)) hV0
          simpa [hP0] using hu
        have hvzero : v (ξ,(0:ℝ)) = u₀ ξ := iv ξ hU0
        have hpzero : PL 0 = (ξ,(0:ℝ)) := by simp [PL, hP0]
        have hzzero : ZL 0 = u₀ ξ := by simp [ZL, hZ0]
        ext
        · rfl
        · simpa [aa, bb, hpzero, hzzero, ZL, PL, hP0, hZ0]
            using hvzero.symm
      have hEq : Set.EqOn aa bb (Set.Ioo (-r) r) :=
        CKSupport.ode_unique_of_local_contDiff
          G aa bb (-r) r 0 h0i haa hbb hloc heq0
      have hval := hEq hτ
      have hvτ : ZL τ = v (PL τ) := congrArg Prod.snd hval
      change Zh (Ps p) = v p
      calc
        Zh (Ps p) = ZL τ := by simp [ZL, ξ, τ]
        _ = v (PL τ) := hvτ
        _ = v p := by rw [show PL τ = p by simpa [PL] using hpback]
  obtain ⟨u, hu, au, hinit, hpde⟩ :=
    CKSupport.solution_of_local_chart (X:=E d)
      F f u₀ x₀ U V Φ Ψ Z hU hV hbase hΨ hΦ hleft hright
        aΨ aΦ aZ dΦ dZ iΨ iZ
  refine ⟨U, u, hbase, hU, au, hinit, hpde, ?_⟩
  intro v av iv pv p hp
  rw [hu]
  exact chart_unique v av iv pv p hp
/-ResultProofEnd-/
/-ResultEnd-/

end Submission

-- END INLINED FILE: Main.lean
