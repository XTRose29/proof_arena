import Mathlib
import Mathlib.Analysis.Calculus.ImplicitContDiff

-- BEGIN INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Core.lean

open MeasureTheory
open scoped ContDiff

/-! Proof-only facts used in the `regular_value_ae` problem.  There is a small
but useful distinction here: the bad values are an image set; the image needn't
be measurable for the a.e. statement, and `ae_iff` is the right (outer-measure)
version. -/
namespace RegularValueAeSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Purely set-theoretic description of the bad values. `fderiv` is intentional
(rather than a chosen derivative); no differentiability hypotheses are needed
for this equivalence. -/
lemma badValues_eq_image (f : E → ℝ) :
    {c : ℝ | ¬ (∀ x, f x = c → fderiv ℝ f x ≠ 0)}
      = f '' {x : E | fderiv ℝ f x = 0} := by
  classical
  ext c
  constructor
  · intro hc
    change ¬ (∀ x, f x = c → fderiv ℝ f x ≠ 0) at hc
    push Not at hc
    rcases hc with ⟨x, hx, hzero⟩
    exact ⟨x, hzero, hx⟩
  · rintro ⟨x, hx, rfl⟩
    intro hall
    exact (hall x rfl) hx

lemma ae_regular_of_critical_image_null (f : E → ℝ)
    (hnull : (volume : Measure ℝ) (f '' {x : E | fderiv ℝ f x = 0}) = 0) :
    ∀ᵐ c ∂(volume : Measure ℝ), (∀ x, f x = c → fderiv ℝ f x ≠ 0) := by
  rw [ae_iff, badValues_eq_image]
  exact hnull

/-- In dimension zero the image, critical or not, is contained in a singleton.
This is useful as the bottom of the induction on source dimension. -/
lemma critical_image_null_fin_zero
    (f : EuclideanSpace ℝ (Fin 0) → ℝ) :
    (volume : Measure ℝ) (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  have hs : f '' {x | fderiv ℝ f x = 0} ⊆ ({f 0} : Set ℝ) := by
    rintro _ ⟨x, hx, rfl⟩
    have he : x = (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
    simp [he]
  exact measure_mono_null hs (by simp)

noncomputable def finOneCLE : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans
    ((LinearEquiv.funUnique (Fin 1) ℝ ℝ).toContinuousLinearEquiv)

/-- The complete equal-dimension step.  In dimension one it is convenient not
to transport Haar measures on the source: precompose with an equivalence
`ℝ ≃L EuclideanSpace ℝ (Fin 1)`, so that the *image subset of the same target
`ℝ`* is unchanged. Then mathlib's equal-dimension Jacobian/Sard lemma applies.
Only the higher-source-dimensional difficulty (source dimension ≥ 2 for a scalar
map) remains after this lemma. -/
lemma critical_image_null_fin_one
    (f : EuclideanSpace ℝ (Fin 1) → ℝ) (hf : ContDiff ℝ ∞ f) :
    (volume : Measure ℝ) (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  let ψ : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) := finOneCLE.symm
  let g : ℝ → ℝ := fun t => f (ψ t)
  have hd_f : Differentiable ℝ f := hf.differentiable (by simp)
  have hdψ : Differentiable ℝ (fun t : ℝ => ψ t) := ψ.differentiable
  have hd_g : Differentiable ℝ g := by
    intro t
    simpa [g, Function.comp_def] using (hd_f (ψ t)).comp t (hdψ t)
  have hderiv_eq (t : ℝ) :
      fderiv ℝ g t =
        (fderiv ℝ f (ψ t)).comp
          (ψ : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) := by
    have hψ :
        fderiv ℝ (ψ : ℝ → EuclideanSpace ℝ (Fin 1)) t =
          (ψ : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) :=
      ψ.hasFDerivAt.fderiv
    simpa [g, hψ, Function.comp_def] using
      (fderiv_comp (𝕜:=ℝ) t (hd_f (ψ t)) (hdψ t))
  let s : Set ℝ := {t | fderiv ℝ g t = 0}
  have hz : volume (g '' s) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (f := g) (f' := fun x => fderiv ℝ g x)
      (μ := (volume : Measure ℝ))
    · intro x hx
      exact (hd_g x).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      change fderiv ℝ g x = 0 at hx
      rw [hx]
      simp
  have critical_imp (t : ℝ) :
      fderiv ℝ g t = 0 ↔ fderiv ℝ f (ψ t) = 0 := by
    rw [hderiv_eq t]
    constructor
    · intro h
      apply ContinuousLinearMap.ext
      intro v
      have happ :
          ((fderiv ℝ f (ψ t)).comp
            (ψ : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))) ((ψ.symm) v)
            = (0 : ℝ →L[ℝ] ℝ) ((ψ.symm) v) :=
        congrArg (fun L : ℝ →L[ℝ] ℝ => L (ψ.symm v)) h
      simpa using happ
    · intro h
      rw [h]
      simp
  have himage : f '' {x | fderiv ℝ f x = 0} = g '' s := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨ψ.symm x, ?_, ?_⟩
      · change fderiv ℝ g (ψ.symm x) = 0
        rw [critical_imp]
        simpa using hx
      · simp [g]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨ψ t, ?_, ?_⟩
      · change fderiv ℝ g t = 0 at ht
        exact (critical_imp t).1 ht
      · rfl
  rw [himage]
  exact hz

end RegularValueAeSupport

-- END INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Core.lean

-- BEGIN INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Flat.lean

set_option maxHeartbeats 4000000
open MeasureTheory Set Filter Function
open scoped ContDiff ENNReal NNReal Topology
namespace RegularValueAeSupport

/-- A Hölder map from a finite dimensional real normed space into the line,
with exponent larger than the dimension, sends the set on which it is
Hölder to a Lebesgue null set.  We use this small wrapper around the
Hausdorff-dimension API; crucially it makes no measurability assumption on
the set. -/
lemma holderOn_image_volume_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f : E → ℝ} {s : Set E} {C p : ℝ≥0}
    (h : HolderOnWith C p f s) (hp : (Module.finrank ℝ E : ℝ≥0) < p) :
    (volume : Measure ℝ) (f '' s) = 0 := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hs : dimH s ≤ (Module.finrank ℝ E : ℝ≥0∞) := by
    simpa using (dimH_mono (subset_univ s)).trans_eq (Real.dimH_univ_eq_finrank E)
  have hi : dimH (f '' s) ≤ dimH s / (p : ℝ≥0∞) := h.dimH_image_le hp0
  have hp_top : (p : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := ENNReal.coe_ne_top
  have hcastlt : (Module.finrank ℝ E : ℝ≥0∞) < (p : ℝ≥0∞) := by
    exact_mod_cast hp
  have hlt : dimH (f '' s) < (1 : ℝ≥0) := by
    have hdiv_lt : (Module.finrank ℝ E : ℝ≥0∞) / (p : ℝ≥0∞) < (1 : ℝ≥0∞) := by
      apply (ENNReal.div_lt_iff (Or.inl ?_) (Or.inl hp_top)).2
      · simpa using hcastlt
      · exact ENNReal.coe_ne_zero.mpr hp0.ne' 
    have hx : dimH s / (p : ℝ≥0∞) ≤ (Module.finrank ℝ E : ℝ≥0∞) / (p : ℝ≥0∞) :=
      ENNReal.div_le_div_right hs _
    have ht : dimH (f '' s) < (1 : ℝ≥0∞) := lt_of_le_of_lt (hi.trans hx) hdiv_lt
    exact ht
  have hz : (μH[(1 : ℝ≥0)] : Measure ℝ) (f '' s) = 0 :=
    hausdorffMeasure_of_dimH_lt hlt
  exact MeasureTheory.hausdorffMeasure_real ▸ hz

end RegularValueAeSupport

namespace RegularValueAeSupport
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology
lemma image_volume_zero_of_dist_le_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f : E → ℝ} {s : Set E} {p : ℝ≥0}
    (hp : (Module.finrank ℝ E : ℝ≥0) < p)
    (hest : ∃ C : ℝ≥0, ∀ x ∈ s, ∀ y ∈ s,
      dist (f x) (f y) ≤ C * dist x y ^ (p : ℝ)) :
    (volume : Measure ℝ) (f '' s) = 0 := by
  rcases hest with ⟨C,hC⟩
  refine holderOn_image_volume_zero (C:=C) (p:=p) ?_ hp
  -- `HolderOnWith` uses exactly this inequality.
  intro x hx y hy
  rw [edist_dist, edist_dist,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg (NNReal.coe_nonneg _)]
  -- change the product to a single `ofReal` and use the given real inequality
  rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
  exact ENNReal.ofReal_le_ofReal (hC x hx y hy)
end RegularValueAeSupport
namespace RegularValueAeSupport
open Set MeasureTheory Filter
lemma image_null_of_subset_iUnion
    {X Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) {f : X → Y} {s : Set X} (t : ℕ → Set X)
    (hst : s ⊆ ⋃ n, t n) (ht : ∀ n, μ (f '' t n) = 0) :
    μ (f '' s) = 0 := by
  apply le_zero_iff.mp
  calc
    μ (f '' s) ≤ μ (f '' ⋃ n, t n) :=
      measure_mono (Set.image_mono hst)
    _ ≤ ∑' n, μ (f '' t n) := by rw [Set.image_iUnion]; exact measure_iUnion_le _
    _ ≤ 0 := by simp [ht]
end RegularValueAeSupport
namespace RegularValueAeSupport
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
/-- Local variant.  This is convenient for Taylor estimates on the all-jets-zero
stratum; the coefficient is allowed to depend on the point. -/
lemma image_volume_zero_of_locally_holder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f : E → ℝ} {s : Set E} {p : ℝ≥0}
    (hp : (Module.finrank ℝ E : ℝ≥0) < p)
    (hlocal : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, HolderOnWith C p f t) :
    (volume : Measure ℝ) (f '' s) = 0 := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hs : dimH s ≤ (Module.finrank ℝ E : ℝ≥0∞) := by
    simpa using (dimH_mono (subset_univ s)).trans_eq (Real.dimH_univ_eq_finrank E)
  have hi : dimH (f '' s) ≤ dimH s / (p : ℝ≥0∞) :=
    dimH_image_le_of_locally_holder_on hp0 hlocal
  have hp_top : (p : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := ENNReal.coe_ne_top
  have hcastlt : (Module.finrank ℝ E : ℝ≥0∞) < (p : ℝ≥0∞) := by exact_mod_cast hp
  have hdiv_lt : (Module.finrank ℝ E : ℝ≥0∞) / (p : ℝ≥0∞) < (1 : ℝ≥0∞) := by
    apply (ENNReal.div_lt_iff (Or.inl ?_) (Or.inl hp_top)).2
    · simpa using hcastlt
    · exact ENNReal.coe_ne_zero.mpr hp0.ne'
  have hx : dimH s / (p : ℝ≥0∞) ≤ (Module.finrank ℝ E : ℝ≥0∞) / (p : ℝ≥0∞) :=
    ENNReal.div_le_div_right hs _
  have hlt : dimH (f '' s) < (1 : ℝ≥0) :=
    lt_of_le_of_lt (hi.trans hx) hdiv_lt
  have hz : (μH[(1 : ℝ≥0)] : Measure ℝ) (f '' s) = 0 :=
    hausdorffMeasure_of_dimH_lt hlt
  exact MeasureTheory.hausdorffMeasure_real ▸ hz
end RegularValueAeSupport
namespace RegularValueAeSupport
open Set MeasureTheory Filter
open scoped ContDiff Topology
/-- The genuinely local-constant (open) part of the critical set causes no
problem in Sard.  This useful outer-measure formulation avoids a measurability
assumption on the remaining critical set. On each open set on which `df=0`
the fibres are disjoint nonempty opens. A separable space has only countably
many such opens. -/
lemma image_null_of_isOpen_fderiv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) {u : Set E} (hu : IsOpen u)
    (hd : DifferentiableOn ℝ f u) (hzero : u.EqOn (fderiv ℝ f) 0) :
    (volume : Measure ℝ) (f '' u) = 0 := by
  classical
  let A : Set ℝ := f '' u
  let V : ℝ → Set E := fun c => u ∩ f ⁻¹' ({c} : Set ℝ)
  have hopen : ∀ c ∈ A, IsOpen (V c) := by
    intro c hc
    exact hu.isOpen_inter_preimage_of_fderiv_eq_zero hd hzero {c}
  have hne : ∀ c ∈ A, (V c).Nonempty := by
    rintro c ⟨x,hx,rfl⟩
    exact ⟨x, hx, by simp [V]⟩
  have hpair : A.PairwiseDisjoint V := by
    -- fibres over different values are disjoint
    rw [Set.pairwiseDisjoint_iff]
    intro i hi j hj h
    rcases h with ⟨x, hxi, hxj⟩
    have hi' : f x = i := by simpa [V] using hxi.2
    have hj' : f x = j := by simpa [V] using hxj.2
    exact hi'.symm.trans hj'
  have hcount : A.Countable :=
    Set.PairwiseDisjoint.countable_of_isOpen hpair hopen hne
  exact hcount.measure_zero _
end RegularValueAeSupport
namespace RegularValueAeSupport
open Set MeasureTheory Filter
open scoped ContDiff Topology
/-- In applying scalar Sard one can discard, at once, the open part of the
zero derivative set. The difficult set has empty interior. Notice this is an
outer-measure assertion throughout. -/
lemma critical_image_null_of_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hd : Differentiable ℝ f) (s : Set E)
    (hs : s ⊆ {x | fderiv ℝ f x = 0})
    (hrem : (volume : Measure ℝ) (f '' (s \ interior s)) = 0) :
    (volume : Measure ℝ) (f '' s) = 0 := by
  have hu0 : (interior s).EqOn (fderiv ℝ f) 0 := by
    intro x hx
    change fderiv ℝ f x = 0
    exact hs (interior_subset hx)
  have hu : (volume : Measure ℝ) (f '' interior s) = 0 :=
    image_null_of_isOpen_fderiv_zero f isOpen_interior
      hd.differentiableOn hu0
  -- two pieces suffice, no measurability of their images is used
  apply le_zero_iff.mp
  calc
    (volume : Measure ℝ) (f '' s) ≤
        (volume : Measure ℝ) (f '' interior s ∪ f '' (s \ interior s)) := by
          apply measure_mono
          rintro y ⟨x,hx,rfl⟩
          by_cases h : x ∈ interior s
          · exact Or.inl ⟨x,h,rfl⟩
          · exact Or.inr ⟨x,⟨hx,h⟩,rfl⟩
    _ ≤ (volume : Measure ℝ) (f '' interior s) +
        (volume : Measure ℝ) (f '' (s \ interior s)) :=
          measure_union_le _ _
    _ ≤ 0 := by simp [hu, hrem]
end RegularValueAeSupport

-- END INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Flat.lean

-- BEGIN INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Strata.lean

open MeasureTheory Set Filter Function
open scoped ContDiff Topology NNReal ENNReal
namespace RegularValueAeSupport

section Jets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The order-`q` flat locus.  It is much handier to use the full iterated
Fréchet derivative than coordinates: zero of that multilinear map exactly
says that all partials of the given order vanish. -/
def flatJet (f : E → ℝ) (q : ℕ) : Set E :=
  {x | ∀ i : ℕ, 1 ≤ i → i ≤ q → iteratedFDeriv ℝ i f x = 0}

@[simp] lemma mem_flatJet {f : E → ℝ} {q : ℕ} {x : E} :
    x ∈ flatJet f q ↔ ∀ i : ℕ, 1 ≤ i → i ≤ q → iteratedFDeriv ℝ i f x = 0 := Iff.rfl

@[simp] lemma flatJet_zero (f : E → ℝ) : flatJet f 0 = Set.univ := by
  ext x
  constructor
  · intro hx; trivial
  · intro hx i hi1 hi0; omega

lemma flatJet_anti {f : E → ℝ} {a b : ℕ} (hab : a ≤ b) :
    flatJet f b ⊆ flatJet f a := by
  intro x hx i hi1 hi
  exact hx i hi1 (hi.trans hab)

lemma flatJet_succ_subset {f : E → ℝ} (q : ℕ) :
    flatJet f (q+1) ⊆ flatJet f q :=
  flatJet_anti (Nat.le_succ _)

/-- The first full multilinear derivative has the same norm as `fderiv`. -/
lemma iterated_one_zero_iff (f : E → ℝ) (x : E) :
    iteratedFDeriv ℝ 1 f x = 0 ↔ fderiv ℝ f x = 0 := by
  have hn := norm_iteratedFDeriv_one (𝕜:=ℝ) (x:=x) f
  constructor
  · intro h
    have : ‖fderiv ℝ f x‖ = 0 := by simpa [h] using hn.symm
    exact norm_eq_zero.mp this
  · intro h
    have : ‖iteratedFDeriv ℝ 1 f x‖ = 0 := by simpa [h] using hn
    exact norm_eq_zero.mp this

lemma flatJet_one (f : E → ℝ) :
    flatJet f 1 = {x | fderiv ℝ f x = 0} := by
  ext x
  constructor
  · intro hx
    exact (iterated_one_zero_iff f x).1 (hx 1 (by decide) (by decide))
  · intro hx i hi1 hi
    have hi : i = 1 := Nat.le_antisymm hi (by omega)
    subst i
    exact (iterated_one_zero_iff f x).2 hx

/-- A point which is flat to order one is either flat to order `q`, or has a
*first* nonzero jet.  Keeping this as a countable cover (rather than a
measurable partition) is convenient: the subsequent Sard argument uses outer
measure throughout. -/
lemma flatJet_one_cover (f : E → ℝ) (q : ℕ) (hq : 1 ≤ q) :
    flatJet f 1 ⊆ flatJet f q ∪
      ⋃ j : ℕ, (if 1 ≤ j ∧ j < q then flatJet f j \ flatJet f (j+1) else (∅ : Set E)) := by
  intro x hx
  by_cases htop : x ∈ flatJet f q
  · exact Or.inl htop
  · right
    -- walk upwards until the first failure.  This elementary induction avoids
    -- any choice of coordinates for the jets.
    -- use the least positive failing stage and its predecessor
    have hex : ∃ k : ℕ, 1 < k ∧ k ≤ q ∧ x ∉ flatJet f k := by
      -- if `q=1` the discarded case is impossible
      by_cases hq1 : q = 1
      · subst q; exact False.elim (htop hx)
      · refine ⟨q, ?_, le_rfl, htop⟩
        -- turn `1 ≤ q` and `q ≠ 1` into `1 < q`
        exact (Nat.lt_of_le_of_ne hq (Ne.symm hq1))
    classical
    let k := Nat.find hex
    have hk := Nat.find_spec hex
    have hprev : x ∈ flatJet f (k-1) := by
      by_contra hn
      have hle : k-1 < k := Nat.sub_lt (Nat.zero_lt_of_lt hk.1) (by decide)
      have hcand : 1 < k-1 ∧ k-1 ≤ q ∧ x ∉ flatJet f (k-1) ∨
                    k-1 = 1 := by
        by_cases heq : k-1 = 1
        · exact Or.inr heq
        · left
          refine ⟨?_, ?_, hn⟩
          · have : 1 ≤ k-1 := by omega
            exact Nat.lt_of_le_of_ne this (Ne.symm heq)
          · omega
      cases hcand with
      | inl hbad =>
          have := Nat.find_min' hex hbad
          omega
      | inr heq =>
          exact hn (by simpa [heq] using hx)
    have kpos : 0 < k := Nat.zero_lt_of_lt hk.1
    have kdec : k-1+1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr kpos.ne')
    refine Set.mem_iUnion.mpr ⟨k-1, ?_⟩
    have hcond : 1 ≤ k-1 ∧ k-1 < q := by omega
    rw [if_pos hcond]
    refine ⟨hprev, ?_⟩
    have hnxt : x ∉ flatJet f (k-1+1) := by
      rw [kdec]
      exact hk.2.2
    exact hnxt

end Jets
end RegularValueAeSupport

namespace RegularValueAeSupport
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reduction to the finitely many non-flat strata and the top flat locus.
There is deliberately no measurability side-condition here. -/
lemma image_flatJet_one_null_of_strata
    (f : E → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (htop : (volume : Measure ℝ) (f '' flatJet f q) = 0)
    (hlayer : ∀ j : ℕ, 1 ≤ j → j < q →
      (volume : Measure ℝ) (f '' (flatJet f j \ flatJet f (j+1))) = 0) :
    (volume : Measure ℝ) (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  classical
  rw [← flatJet_one (f:=f)]
  let T : ℕ → Set E := fun j =>
    if j = 0 then flatJet f q
    else if 1 ≤ j ∧ j < q then flatJet f j \ flatJet f (j+1)
    else ∅
  apply image_null_of_subset_iUnion (volume : Measure ℝ) T
  · intro x hx
    have hc := flatJet_one_cover f q hq hx
    cases hc with
    | inl h =>
        exact Set.mem_iUnion.mpr ⟨0, by simp [T, h]⟩
    | inr h =>
        rcases Set.mem_iUnion.mp h with ⟨j, hj⟩
        have hjpos : j ≠ 0 := by
          intro hz
          subst j
          simp at hj
        have hcond : 1 ≤ j ∧ j < q := by
          by_contra hn
          simp [hn] at hj
        exact Set.mem_iUnion.mpr ⟨j, by simpa [T, hjpos, hcond] using hj⟩
  · intro j
    by_cases hj0 : j = 0
    · simpa [T, hj0] using htop
    · by_cases hc : 1 ≤ j ∧ j < q
      · simpa [T, hj0, hc] using hlayer j hc.1 hc.2
      · simp [T, hj0, hc]

/-- Frequently one needs only a subset of the first critical locus (a ball,
or a frontier). The same global strata estimates suffice. -/
lemma image_subset_flatJet_one_null_of_strata
    (f : E → ℝ) (u : Set E) (hu : u ⊆ {x | fderiv ℝ f x = 0})
    (q : ℕ) (hq : 1 ≤ q)
    (htop : (volume : Measure ℝ) (f '' flatJet f q) = 0)
    (hlayer : ∀ j : ℕ, 1 ≤ j → j < q →
      (volume : Measure ℝ) (f '' (flatJet f j \ flatJet f (j+1))) = 0) :
    (volume : Measure ℝ) (f '' u) = 0 := by
  refine measure_mono_null (Set.image_mono hu) ?_
  exact image_flatJet_one_null_of_strata f q hq htop hlayer
end RegularValueAeSupport
namespace RegularValueAeSupport
open Set Filter
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Each finite flat locus is closed. Its successive differences are the natural
locally-closed strata for the implicit-function portion of Sard. -/
lemma isClosed_flatJet {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (q : ℕ) :
    IsClosed (flatJet f q) := by
  classical
  -- arbitrary intersection is simplest; the vacuous orders cost nothing
  have hc (i : ℕ) : IsClosed {x : E | iteratedFDeriv ℝ i f x = 0} := by
    exact isClosed_eq
      (hf.continuous_iteratedFDeriv (by exact_mod_cast
        (show (i : ℕ∞) ≤ ⊤ from le_top))) continuous_const
  change IsClosed {x : E | ∀ i : ℕ, 1 ≤ i → i ≤ q →
    iteratedFDeriv ℝ i f x = 0}
  -- unfold the bounded interval by closed intersections
  induction q with
  | zero =>
      convert (isClosed_univ : IsClosed (Set.univ : Set E)) using 1
      ext x
      constructor
      · intro; trivial
      · intro hx i hi1 hi0; omega
  | succ q IH =>
      have heq : {x : E | ∀ i : ℕ, 1 ≤ i → i ≤ q+1 →
              iteratedFDeriv ℝ i f x = 0}
            = {x : E | ∀ i : ℕ, 1 ≤ i → i ≤ q →
              iteratedFDeriv ℝ i f x = 0} ∩
                {x : E | iteratedFDeriv ℝ (q+1) f x = 0} := by
        ext x
        change ( (∀ i : ℕ, 1 ≤ i → i ≤ q+1 → iteratedFDeriv ℝ i f x = 0) ↔
          ((∀ i : ℕ, 1 ≤ i → i ≤ q → iteratedFDeriv ℝ i f x = 0) ∧
            iteratedFDeriv ℝ (q+1) f x = 0))
        constructor
        · intro h
          refine ⟨?_, ?_⟩
          · intro i hi hle
            exact h i hi (by omega)
          · exact h (q+1) (by omega) (by omega)
        · rintro ⟨hpre, hlast⟩ i hi hle
          by_cases hq : i = q+1
          · subst i
            exact hlast
          · exact hpre i hi (by omega)
      rw [heq]
      exact IsClosed.inter IH (hc _)

end RegularValueAeSupport

-- END INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Strata.lean

-- BEGIN INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/FlatTaylor.lean
open Set Filter Function MeasureTheory
open scoped ContDiff Topology ENNReal NNReal
namespace RegularValueAeSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma iterated_bound_down
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (N : ℕ) {u : Set E} (hu : Convex ℝ u)
    {a : E} (ha : a ∈ u)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ u, ‖iteratedFDeriv ℝ N f z‖ ≤ M)
    (hz : a ∈ flatJet f N) :
    ∀ d : ℕ, d < N → ∀ z ∈ u,
      ‖iteratedFDeriv ℝ (N-d) f z‖ ≤ M * ‖z-a‖^d := by
  intro d hd
  induction d with
  | zero =>
      intro z hzu
      simpa using hM z hzu
  | succ d IH =>
      intro z hzu
      have hd' : d < N := Nat.lt_trans (Nat.lt_succ_self _) hd
      have hi_pos : 1 ≤ N-(d+1) := by omega
      let i : ℕ := N-(d+1)
      have hi : i + 1 = N-d := by dsimp [i]; omega
      let C : ℝ := M * ‖z-a‖^d
      have hC : ∀ w ∈ segment ℝ a z,
          ‖fderiv ℝ (iteratedFDeriv ℝ i f) w‖ ≤ C := by
        intro w hw
        rw [norm_fderiv_iteratedFDeriv, hi]
        have subu : segment ℝ a z ⊆ u := hu.segment_subset ha hzu
        have h1 := IH hd' w (subu hw)
        have hdist : ‖w-a‖ ≤ ‖z-a‖ := norm_sub_le_of_mem_segment hw
        exact h1.trans (by
          dsimp [C]
          gcongr)
      have hdiff :=
        Convex.norm_image_sub_le_of_norm_fderiv_le
          (𝕜:=ℝ) (f:= fun y : E => iteratedFDeriv ℝ i f y)
          (s:=segment ℝ a z) (C:=C) (x:=a) (y:=z)
          (fun w hw => (hf.differentiable_iteratedFDeriv (by exact_mod_cast (ENat.coe_lt_top i)) w))
          hC (convex_segment _ _) (left_mem_segment _ _ _) (right_mem_segment _ _ _)
      have hzeroi : iteratedFDeriv ℝ i f a = 0 :=
        hz i (by dsimp [i]; omega) (by dsimp [i]; omega)
      -- turn the difference estimate into the next power
      rw [hzeroi, sub_zero] at hdiff
      -- powers: `C*r = M*r^(d+1)`
      simpa [i, C, pow_succ, mul_assoc] using hdiff

/-- Uniform flat estimate on a convex set. There is no factorial here; repeated
mean value bounds are more convenient for the Hölder application. -/
lemma norm_sub_le_of_flatJet
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (N : ℕ) (hN : 0 < N) {u : Set E} (hu : Convex ℝ u)
    {a z : E} (ha : a ∈ u) (hzmem : z ∈ u)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ w ∈ u, ‖iteratedFDeriv ℝ N f w‖ ≤ M)
    (hflat : a ∈ flatJet f N) :
    ‖f z - f a‖ ≤ M * ‖z-a‖^N := by
  let i := N-1
  have hi : i + 1 = N := Nat.sub_add_cancel hN
  have hiN : i < N := by dsimp [i]; omega
  have hprev : ∀ w ∈ segment ℝ a z,
      ‖fderiv ℝ f w‖ ≤ M * ‖z-a‖^i := by
    intro w hw
    have subu : segment ℝ a z ⊆ u := hu.segment_subset ha hzmem
    have hb := iterated_bound_down f hf N hu ha hM0 hM hflat i
      (by dsimp [i]; omega) w (subu hw)
    have hidx : N-i = 1 := by dsimp [i]; omega
    rw [hidx, norm_iteratedFDeriv_one] at hb
    exact hb.trans (by
      have hdw : ‖w-a‖ ≤ ‖z-a‖ := norm_sub_le_of_mem_segment hw
      gcongr)
  have hdiff :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜:=ℝ) (f:=f) (s:=segment ℝ a z)
      (C:= M * ‖z-a‖^i) (x:=a) (y:=z)
      (fun w hw => hf.differentiable (by simp) w)
      hprev (convex_segment _ _) (left_mem_segment _ _ _) (right_mem_segment _ _ _)
  simpa [← hi, pow_succ, mul_assoc] using hdiff
end RegularValueAeSupport
namespace RegularValueAeSupport
open Set Filter Function MeasureTheory Metric
open scoped NNReal ENNReal ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- The top (flat) piece of the scalar critical set. This is the Taylor/Hausdorff
part of Sard; the still harder finite-order pieces require hypersurface charts.
-/
lemma image_flatJet_volume_zero
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (N : ℕ) (hN : (Module.finrank ℝ E) < N) :
    (volume : Measure ℝ) (f '' flatJet f N) = 0 := by
  let p : ℝ≥0 := (N : ℝ≥0)
  have hp : (Module.finrank ℝ E : ℝ≥0) < p := by dsimp [p]; exact_mod_cast hN
  refine image_volume_zero_of_locally_holder (f:=f) (s:=flatJet f N) (p:=p) hp ?_
  intro x hx
  let u : Set E := Metric.closedBall x (1/2 : ℝ)
  have hucomp : IsCompact u := isCompact_closedBall x _
  have hcN : Continuous (fun y : E => iteratedFDeriv ℝ N f y) :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast (show (N : ℕ∞) ≤ ⊤ from le_top))
  have hbdd : BddAbove ((fun y : E => ‖iteratedFDeriv ℝ N f y‖) '' u) :=
    hucomp.bddAbove_image hcN.norm.continuousOn
  rcases bddAbove_def.mp hbdd with ⟨B, hB⟩
  let M : ℝ := max B 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ z ∈ u, ‖iteratedFDeriv ℝ N f z‖ ≤ M := by
    intro z hz
    exact (hB _ ⟨z,hz,rfl⟩).trans (le_max_left _ _)
  let C : ℝ≥0 := ⟨M, hM0⟩
  refine ⟨C, flatJet f N ∩ u, ?_, ?_⟩
  · exact inter_mem_nhdsWithin _ (Metric.closedBall_mem_nhds x (by norm_num))
  · intro a ha z hz
    have hN0 : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hN
    have est := norm_sub_le_of_flatJet f hf N hN0 (convex_closedBall x (1/2 : ℝ))
      ha.2 hz.2 hM0 hM ha.1
    -- `HolderOnWith` is phrased with `edist`.
    rw [edist_dist, edist_dist,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg (NNReal.coe_nonneg p)]
    rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
    apply ENNReal.ofReal_le_ofReal
    -- the real estimate above is exactly this inequality
    change dist (f a) (f z) ≤ M * dist a z ^ (N : ℝ)
    simpa [Real.norm_eq_abs, Real.dist_eq, dist_eq_norm, abs_sub_comm, norm_sub_rev, p, C, NNReal.smul_def, NNReal.coe_mk] using est
end RegularValueAeSupport

-- END INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/FlatTaylor.lean

-- BEGIN INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Local.lean

open Set Filter MeasureTheory
open scoped Topology
namespace RegularValueAeSupport

/-- A version of the elementary countable-localization step which does not
mention measurability of an image.  In a second countable source a null-image
estimate can be checked on (possibly very point dependent) neighbourhoods.
This little lemma is useful for Sard strata, where a different implicit chart
is chosen at each point.  Notice the repeated intersection with `s`: this
form avoids any measurable-space assumptions on the source. -/
lemma image_null_of_locally
    {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace Y]
    (μ : Measure Y) {f : X → Y} {s : Set X}
    (h : ∀ x ∈ s, ∃ u ∈ (𝓝 x), μ (f '' (s ∩ u)) = 0) :
    μ (f '' s) = 0 := by
  classical
  choose u hu hu0 using (fun x : s => h (x : X) x.property)
  have hxmem (x : s) : (x : X) ∈ interior (u x) :=
    mem_interior_iff_mem_nhds.mpr (hu x)
  have hcov : s ⊆ ⋃ x : s, interior (u x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩, hxmem ⟨x,hx⟩⟩
  obtain ⟨r, hr, hrs⟩ :=
    (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
      (fun x : s => interior (u x)) (fun x => isOpen_interior) hcov
  have hsub : f '' s ⊆ ⋃ i ∈ r, f '' (s ∩ interior (u i)) := by
    rintro y ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.mp (hrs hx) with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨hir, hxi⟩
    -- in the double union the second index is a proof of `i ∈ r`
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hir,
      ⟨x, ⟨hx, hxi⟩, rfl⟩⟩⟩
  refine measure_mono_null hsub ?_
  -- Countability comes just from topology, no measurability is used.
  exact (measure_biUnion_null_iff hr).2 (by
    intro i hi
    apply measure_mono_null (Set.image_mono ?_) (hu0 i)
    intro x hx
    exact ⟨hx.1, interior_subset hx.2⟩)

end RegularValueAeSupport

-- END INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Local.lean

-- BEGIN INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Chart.lean
open Set Filter MeasureTheory Function
open scoped ContDiff Topology
namespace RegularValueAeSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma flatJet_local_equation (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (j : ℕ) (hj : 1 ≤ j) {x : E} (hx : x ∈ flatJet f j \ flatJet f (j+1)) :
    ∃ h : E → ℝ, ContDiff ℝ ∞ h ∧ (fderiv ℝ h x ≠ 0) ∧
      flatJet f j ⊆ {y | h y = 0} := by
  have hn : iteratedFDeriv ℝ (j+1) f x ≠ 0 := by
    intro he
    apply hx.2
    intro i hi hil
    by_cases hi' : i ≤ j
    · exact hx.1 i hi hi'
    · have : i = j+1 := by omega
      subst i
      exact he
  have hm : ∃ v : Fin (j+1) → E, iteratedFDeriv ℝ (j+1) f x v ≠ 0 := by
    by_contra H
    push_neg at H
    apply hn
    exact ContinuousMultilinearMap.ext H
  rcases hm with ⟨v, hv⟩
  let L : (E [×j]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => E) ℝ (Fin.tail v)
  let h : E → ℝ := fun y => L (iteratedFDeriv ℝ j f y)
  refine ⟨h, ?_, ?_, ?_⟩
  · exact L.contDiff.comp (hf.iteratedFDeriv_right (n:=∞) (m:=∞) (by exact_mod_cast (show (⊤ : ℕ∞) + (j : ℕ∞) ≤ ⊤ from le_top)))
  · -- derivative nonzero, evaluate on v0
    intro hz
    have hdj : Differentiable ℝ (iteratedFDeriv ℝ j f) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast (show (j : ℕ∞) < ⊤ from ENat.coe_lt_top _) )
    have hder : fderiv ℝ h x = L.comp (fderiv ℝ (iteratedFDeriv ℝ j f) x) := by
      simpa [h, Function.comp_def] using
        (fderiv_comp (𝕜:=ℝ) x L.differentiableAt (hdj x)) -- order?
    have happ := congrArg (fun T : E →L[ℝ] ℝ => T (v 0)) hz
    rw [hder] at happ
    change iteratedFDeriv ℝ (j+1) f x v = 0 at happ
    exact hv happ
  · intro y hy
    change L (iteratedFDeriv ℝ j f y) = 0
    have hj0 := hy j hj (le_rfl)
    rw [hj0]
    rfl
end RegularValueAeSupport
namespace RegularValueAeSupport
section Germ
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

lemma critical_local_of_germ
    (IH : ∀ g : A → ℝ, ContDiff ℝ ∞ g →
      (volume : Measure ℝ) (g '' {z | fderiv ℝ g z = 0}) = 0)
    {q : A → ℝ} {a : A} {V : Set A} (hV : V ∈ 𝓝 a)
    (hq : ∀ z ∈ V, ContDiffAt ℝ ∞ q z) :
    ∃ w ∈ 𝓝 a,
      (volume : Measure ℝ) (q '' ({z | fderiv ℝ q z = 0} ∩ w)) = 0 := by
  classical
  rcases Metric.mem_nhds_iff.mp hV with ⟨ε, hε, hball⟩
  let bspec : ContDiffBump a :=
    { rIn := ε / 2, rOut := ε * (3/4),
      rIn_pos := by positivity,
      rIn_lt_rOut := by linarith }
  let b : A → ℝ := (bspec : A → ℝ)
  let Q : A → ℝ := fun z => b z * q z
  have hts : tsupport b ⊆ V := by
    intro z hz
    apply hball
    have hz' : z ∈ Metric.closedBall a (ε * (3/4)) := by
      simpa [b, ContDiffBump.tsupport_eq, bspec] using hz
        -- `tsupport_eq` is the closed outer ball
        -- simp knows the radii of this bump
    exact Metric.mem_ball'.mpr ((Metric.mem_closedBall'.mp hz').trans_lt (by linarith))
  have hQ : ContDiff ℝ ∞ Q := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ V
    · exact (bspec.contDiff.contDiffAt).mul (hq z hz)
    · have hz0 : b =ᶠ[𝓝 z] 0 := by
        have hnot : z ∉ tsupport b := fun H => hz (hts H)
        exact (notMem_tsupport_iff_eventuallyEq).mp hnot
      have hzero : Q =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [hz0] with y hy
        simp [Q, hy]
      exact (contDiffAt_const (c:= (0:ℝ))).congr_of_eventuallyEq hzero
  let w : Set A := Metric.ball a (ε/2)
  refine ⟨w, Metric.ball_mem_nhds _ (by positivity), ?_⟩
  have hsub : q '' ({z | fderiv ℝ q z = 0} ∩ w) ⊆
      Q '' {z | fderiv ℝ Q z = 0} := by
    rintro _ ⟨z, ⟨hzcrit, hzw⟩, rfl⟩
    have hbnear : b =ᶠ[𝓝 z] 1 := by
      simpa [b, bspec, w] using
        (bspec.eventuallyEq_one_of_mem_ball (by simpa [w, bspec] using hzw))
    have hEq : Q =ᶠ[𝓝 z] q := by
      filter_upwards [hbnear] with y hy
      simp [Q, hy]
    refine ⟨z, ?_, ?_⟩
    · change fderiv ℝ Q z = 0
      rw [hEq.fderiv_eq]
      exact hzcrit
    · exact (hEq.self_of_nhds)
  exact measure_mono_null hsub (IH Q hQ)
end Germ
lemma scalar_range_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0) : (L : E →ₗ[ℝ] ℝ).range = ⊤ := by
  rw [eq_top_iff]
  intro t ht
  have hv : ∃ v : E, L v ≠ 0 := by
    by_contra H
    push_neg at H
    exact hL (ContinuousLinearMap.ext H)
  rcases hv with ⟨v, hv⟩
  refine ⟨(t / L v) • v, ?_⟩
  simp [hv]

lemma finrank_ker_scalar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E →L[ℝ] ℝ) (hL : L ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (L : E →ₗ[ℝ] ℝ)) + 1 =
       Module.finrank ℝ E := by
  have htop := scalar_range_top L hL
  have hr := LinearMap.finrank_range_add_finrank_ker (L : E →ₗ[ℝ] ℝ)
  have hrange : Module.finrank ℝ ((L : E →ₗ[ℝ] ℝ).range) = 1 := by
    rw [htop]
    simp
  omega
end RegularValueAeSupport

-- END INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Chart.lean

-- BEGIN INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Hypersurface.lean
open Set Filter MeasureTheory Function
open scoped Topology ContDiff
noncomputable section
namespace RegularValueAeSupport
/-! A local, outer-measure form of the implicit-chart step.  This lemma deliberately
separates the geometric parametrisation from the induction used in Sard. -/
lemma image_level_null_of_implicit_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f h : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {x : E} {L : E →L[ℝ] ℝ}
    (sh : HasStrictFDerivAt h L x) (hsur : (L : E →ₗ[ℝ] ℝ).range = ⊤)
    {s : Set E}
    (hx0 : h x = 0)
    (hs0 : s ⊆ {y | h y = 0})
    (hsc : s ⊆ {y | fderiv ℝ f y = 0})
    (IH : ∀ g : (LinearMap.ker (L : E →ₗ[ℝ] ℝ)) → ℝ, ContDiff ℝ ∞ g →
      (volume : Measure ℝ) (g '' {z | fderiv ℝ g z = 0}) = 0)
    (hphi : ∃ V ∈ 𝓝 (0 : LinearMap.ker (L : E →ₗ[ℝ] ℝ)),
      ∀ z ∈ V, ContDiffAt ℝ ∞ (sh.implicitFunction h L hsur (h x)) z) :
    ∃ u ∈ 𝓝 x, (volume : Measure ℝ) (f '' (s ∩ u)) = 0 := by
  classical
  let A := LinearMap.ker (L : E →ₗ[ℝ] ℝ)
  let phi : A → E := sh.implicitFunction h L hsur (h x)
  let q : A → ℝ := fun z => f (phi z)
  let T := sh.implicitToOpenPartialHomeomorph h L hsur
  rcases hphi with ⟨V, hV, hphiV⟩
  -- smooth germ of the restricted function
  have hqV : ∀ z ∈ V, ContDiffAt ℝ ∞ q z := by
    intro z hz
    exact hf.contDiffAt.comp z (hphiV z hz)
  obtain ⟨w, hw, hNull⟩ :=
    critical_local_of_germ (A:=A) IH (q:=q) (a:=(0:A)) hV hqV
  have hxsrc : x ∈ T.source := sh.mem_implicitToOpenPartialHomeomorph_source hsur
  have hT0 : T x = (h x, (0 : A)) := sh.implicitToOpenPartialHomeomorph_self hsur
  have htend : Tendsto (fun y : E => (T y).2) (𝓝 x) (𝓝 (0 : A)) := by
    have ht : Tendsto T (𝓝 x) (𝓝 (T x)) := T.continuousAt hxsrc
    have hsnd : Tendsto (fun p : ℝ × (LinearMap.ker (L : E →ₗ[ℝ] ℝ)) => p.2) (𝓝 (T x)) (𝓝 (T x).2) :=
      continuousAt_snd
    have hcomp := hsnd.comp ht
    simpa [hT0, Function.comp_def] using hcomp
  have hmw : {y : E | (T y).2 ∈ w} ∈ 𝓝 x := htend hw
  have hmV : {y : E | (T y).2 ∈ V} ∈ 𝓝 x := htend hV
  have heq0 : ∀ᶠ y : E in 𝓝 x,
      sh.implicitFunction h L hsur (h y) (T y).2 = y := by
    simpa [T] using (sh.eq_implicitFunction hsur)
  have hseteq : {y : E |
      sh.implicitFunction h L hsur (h y) (T y).2 = y} ∈ 𝓝 x := heq0
  let u : Set E := {y : E |
      sh.implicitFunction h L hsur (h y) (T y).2 = y} ∩
        ({y : E | (T y).2 ∈ w} ∩ {y : E | (T y).2 ∈ V})
  have hu : u ∈ 𝓝 x := Filter.inter_mem hseteq (Filter.inter_mem hmw hmV)
  refine ⟨u, hu, ?_⟩
  apply measure_mono_null (t:= q '' ({z | fderiv ℝ q z = 0} ∩ w)) ?_ hNull
  rintro _ ⟨y, hy, rfl⟩
  have hys : y ∈ s := hy.1
  have hyu : y ∈ u := hy.2
  have heq := hyu.1
  have hzW : (T y).2 ∈ w := hyu.2.1
  have hzV : (T y).2 ∈ V := hyu.2.2
  let z : A := (T y).2
  have hyh : h y = 0 := hs0 hys
  have hphi_y : phi z = y := by
    -- replace the first parameter of the implicit function by its value at `x`
    simpa [phi, z, hx0, hyh] using heq
  refine ⟨z, ?_, ?_⟩
  · refine ⟨?_, hzW⟩
    have hcy : fderiv ℝ f y = 0 := hsc hys
    have hdf : DifferentiableAt ℝ f (phi z) := hf.differentiable (by simp) _
    have hdphi : DifferentiableAt ℝ phi z :=
      (hphiV z hzV).differentiableAt (by simp)
    change fderiv ℝ q z = 0
    rw [show q = f ∘ phi from by rfl]
    rw [fderiv_comp z hdf hdphi]
    rw [hphi_y] at hdf ⊢
    rw [hcy]
    simp
  · change q z = f y
    simp [q, hphi_y]
end RegularValueAeSupport
namespace RegularValueAeSupport
-- Smoothness of the vertical parametrisation on a neighbourhood.  The IFT in
-- `Implicit.lean` states differentiability of this particular inverse only at
-- the base point.  Using openness of the set of isomorphisms and the
-- open-partial-homeomorphism it actually has the whole smooth germ.
lemma eventually_contDiffAt_implicitFunction_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h : E → ℝ} (hh : ContDiff ℝ ∞ h)
    {x : E} {L : E →L[ℝ] ℝ}
    (sh : HasStrictFDerivAt h L x) (hsur : (L : E →ₗ[ℝ] ℝ).range = ⊤) :
    ∃ V ∈ 𝓝 (0 : LinearMap.ker (L : E →ₗ[ℝ] ℝ)),
      ∀ z ∈ V, ContDiffAt ℝ ∞ (sh.implicitFunction h L hsur (h x)) z := by
  classical
  let A := LinearMap.ker (L : E →ₗ[ℝ] ℝ)
  let T := sh.implicitToOpenPartialHomeomorph h L hsur
  let hk := L.ker_closedComplemented_of_finiteDimensional_range
  let D := HasStrictFDerivAt.implicitFunctionDataOfComplemented h L sh hsur hk
  let g : E → (ℝ × A) := D.prodFun
  have hTg : (T : E → (ℝ × A)) = g := by
    -- both definitions are the `prodFun` of the same implicit data
    rfl
  have hg : ContDiff ℝ ∞ g := by
    -- the second coordinate is a fixed continuous linear projection
    change ContDiff ℝ ∞ (fun y : E => (h y, (Classical.choose hk) (y-x)))
    fun_prop
  have hxsrc : x ∈ T.source := sh.mem_implicitToOpenPartialHomeomorph_source hsur
  have hTx : T x = (h x, (0 : A)) := sh.implicitToOpenPartialHomeomorph_self hsur
  have hxinv : (fderiv ℝ g x).IsInvertible := by
    -- `ImplicitFunctionData` has an invertible derivative of `prodFun` at pt
    have hdx := D.isInvertible_fderiv_prodFun
    change (fderiv ℝ g x).IsInvertible at hdx
    exact hdx
  -- the invertibility holds on a neighbourhood, since the range of equivalences is open
  have hdercont : Continuous (fun y : E => fderiv ℝ g y) :=
    hg.continuous_fderiv (by simp)
  have hinvnh : {y : E | (fderiv ℝ g y).IsInvertible} ∈ 𝓝 x := by
    let e : E ≃L[ℝ] (ℝ × A) := Classical.choose hxinv
    have heq : (e : E →L[ℝ] (ℝ × A)) = fderiv ℝ g x := (Classical.choose_spec hxinv)
    have hopen : IsOpen (Set.range ((↑) : (E ≃L[ℝ] (ℝ × A)) → E →L[ℝ] (ℝ × A))) :=
      ContinuousLinearEquiv.isOpen
    have hxmem : fderiv ℝ g x ∈ Set.range ((↑) : (E ≃L[ℝ] (ℝ × A)) → E →L[ℝ] (ℝ × A)) :=
      ⟨e, heq⟩
    have hm := (hopen.mem_nhds hxmem)
    have hp := (hdercont.continuousAt (x:=x)) hm
    -- range is exactly the predicate `IsInvertible`
    filter_upwards [hp] with y hy
    rcases hy with ⟨e', he'⟩
    exact ⟨e', he'⟩
  have hsrcnh : T.source ∈ 𝓝 x := T.open_source.mem_nhds hxsrc
  let U : Set E := {y : E | (fderiv ℝ g y).IsInvertible} ∩ T.source
  have hU : U ∈ 𝓝 x := Filter.inter_mem hinvnh hsrcnh
  have htar : (T.target) ∈ 𝓝 (T x) :=
    T.open_target.mem_nhds (T.map_source hxsrc)
  have htendsym : Tendsto T.symm (𝓝 (T x)) (𝓝 x) := T.tendsto_symm hxsrc
  have hpre : T.symm ⁻¹' U ∈ 𝓝 (T x) := htendsym hU
  have hboth : T.target ∩ (T.symm ⁻¹' U) ∈ 𝓝 (T x) :=
    Filter.inter_mem htar hpre
  -- pull this neighbourhood back along `z ↦ (h x, z)`
  have hemb : Tendsto (fun z : A => (h x, z)) (𝓝 (0 : A)) (𝓝 (T x)) := by
    rw [hTx]
    exact (continuousAt_const.prodMk continuousAt_id)
  let V : Set A := (fun z : A => (h x, z)) ⁻¹' (T.target ∩ T.symm ⁻¹' U)
  have hV : V ∈ 𝓝 (0 : A) := hemb hboth
  refine ⟨V, hV, ?_⟩
  intro z hz
  change (h x, z) ∈ T.target ∩ T.symm ⁻¹' U at hz
  let p : ℝ × A := (h x, z)
  have hpt : p ∈ T.target := hz.1
  have hyU : T.symm p ∈ U := hz.2
  have hyinv : (fderiv ℝ g (T.symm p)).IsInvertible := hyU.1
  rcases hyinv with ⟨e, he⟩
  have hd : HasFDerivAt T (e : E →L[ℝ] (ℝ × A)) (T.symm p) := by
    rw [hTg]
    have hdg : HasFDerivAt g (fderiv ℝ g (T.symm p)) (T.symm p) :=
      (hg.differentiable (by simp) _).hasFDerivAt
    simpa [he] using hdg
  have hct : ContDiffAt ℝ ∞ T (T.symm p) := by
    rw [hTg]
    exact hg.contDiffAt
  have hsym : ContDiffAt ℝ ∞ T.symm p :=
    T.contDiffAt_symm hpt hd hct
  -- the slice of the inverse is the implicit function
  have hpemb : ContDiffAt ℝ ∞ (fun z : A => (h x, z)) z := by fun_prop
  have hcomp := hsym.comp z hpemb
  -- unfold definitions of the implicit function
  change ContDiffAt ℝ ∞ (fun z : A => T.symm (h x, z)) z at hcomp
  change ContDiffAt ℝ ∞ (fun z : A => T.symm (h x, z)) z
  exact hcomp
end RegularValueAeSupport
namespace RegularValueAeSupport
lemma local_flatJet_stratum_of_kernel_IH
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (j : ℕ) (hj : 1 ≤ j) {a : E}
    (ha : a ∈ flatJet f j \ flatJet f (j+1))
    (IHker : ∀ (h : E → ℝ) (x : E) (L : E →L[ℝ] ℝ)
        (sh : HasStrictFDerivAt h L x) (hL : L ≠ 0),
        ∀ g : (LinearMap.ker (L : E →ₗ[ℝ] ℝ)) → ℝ, ContDiff ℝ ∞ g →
          (volume : Measure ℝ) (g '' {z | fderiv ℝ g z = 0}) = 0) :
    ∃ u ∈ 𝓝 a,
      (volume : Measure ℝ) (f '' ((flatJet f j \ flatJet f (j+1)) ∩ u)) = 0 := by
  classical
  rcases flatJet_local_equation f hf j hj (x:=a) ha with ⟨h, hh, hL, hflat⟩
  let L : E →L[ℝ] ℝ := fderiv ℝ h a
  have hL' : L ≠ 0 := hL
  have hsur : (L : E →ₗ[ℝ] ℝ).range = ⊤ := scalar_range_top L hL'
  let sh : HasStrictFDerivAt h L a := hh.contDiffAt.hasStrictFDerivAt (by simp)
  have ha0 : h a = 0 := hflat ha.1
  apply image_level_null_of_implicit_chart hf sh hsur ha0
  · intro y hy
    exact hflat hy.1
  · intro y hy
    have h1 : y ∈ flatJet f 1 := by
      intro i hi hil
      have hi' : i ≤ j := by omega
      exact hy.1 i hi hi'
    have : y ∈ {t : E | fderiv ℝ f t = 0} :=
      (flatJet_one f ▸ h1)
    exact this
  · exact IHker h a L sh hL'
  · exact eventually_contDiffAt_implicitFunction_slice hh sh hsur
end RegularValueAeSupport

end

-- END INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Hypersurface.lean

-- BEGIN INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Induction.lean
open Set Filter MeasureTheory Function
open scoped Topology ContDiff
noncomputable section
universe u
namespace RegularValueAeSupport
-- The scalar induction. Isolating it makes the implicit-chart bookkeeping reusable.
theorem critical_image_null_fd
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) :
    (volume : Measure ℝ) (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  classical
  have H : ∀ n : ℕ, ∀ (F : Type u) [NormedAddCommGroup F]
      [NormedSpace ℝ F] [FiniteDimensional ℝ F],
      Module.finrank ℝ F = n →
      ∀ g : F → ℝ, ContDiff ℝ ∞ g →
        (volume : Measure ℝ) (g '' {x | fderiv ℝ g x = 0}) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F _ _ _ hn g hg
      -- top flat locus of order n+1, and finite-order strata
      refine image_flatJet_one_null_of_strata g (n+1) (by omega) ?_ ?_
      · apply image_flatJet_volume_zero g hg
        omega
      · intro j hj hjn
        -- prove each stratum countably locally
        apply image_null_of_locally (volume : Measure ℝ)
        intro a ha
        refine local_flatJet_stratum_of_kernel_IH g hg j hj ha ?_
        intro h x L sh hL q hq
        let A := LinearMap.ker (L : F →ₗ[ℝ] ℝ)
        have hdim : Module.finrank ℝ A + 1 = Module.finrank ℝ F :=
          finrank_ker_scalar L hL
        have hlt : Module.finrank ℝ A < n := by omega
        exact ih (Module.finrank ℝ A) hlt A rfl q hq
  exact H (Module.finrank ℝ E) E rfl f hf
end RegularValueAeSupport

end

-- END INLINED FILE: Mathlib/Support/regular_value_ae_e5a93b29ad/Induction.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval.Geometry.RegularValue

/-!
# Sard's regular-value corollary

`regular_value_ae`: for a smooth `f : ℝᵐ → ℝ`, almost every `c ∈ ℝ` is a regular
value (every point of the level set `f⁻¹(c)` has nonzero derivative). This is the
measure-theoretic heart of the regular-value form of Sard's theorem; the main
critical-set-null Sard theorem is already in lean-eval (§125 main / `sard`).
The trusted helper `IsRegularValue` is a non-hole. Mathlib has the equal-
dimension Jacobian-null lemma and Hausdorff-dimension corollaries but not the
general critical-values-are-null statement.

Category-(b) candidate from §125 of the Knill survey (additional statement 1).
-/

open MeasureTheory
open Filter
open scoped Topology
open scoped ContDiff

/-- `c` is a **regular value** of `f : ℝᵐ → ℝ`: every point of the level set
`f⁻¹(c)` has nonzero derivative. -/
def IsRegularValue {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) (c : ℝ) : Prop :=
  ∀ x, f x = c → fderiv ℝ f x ≠ 0



end LeanEval.Geometry.RegularValue

open LeanEval.Geometry.RegularValue
open MeasureTheory
open Filter
open scoped Topology
open scoped ContDiff
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem regular_value_ae {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ∀ᵐ c ∂(volume : Measure ℝ), IsRegularValue f c :=
/-ResultProofBegin-/by
  classical
  -- the bad values form the image of the zero-fderivative/critical set
  change ∀ᵐ c ∂(volume : Measure ℝ),
    (∀ x, f x = c → fderiv ℝ f x ≠ 0)
  refine RegularValueAeSupport.ae_regular_of_critical_image_null f ?_
  cases m with
  | zero =>
      simpa using RegularValueAeSupport.critical_image_null_fin_zero f
  | succ m =>
      cases m with
      | zero =>
          simpa using RegularValueAeSupport.critical_image_null_fin_one f hf
      | succ k =>
          -- Sard is local on the source.  Removing this countable exhaustion
          -- up front avoids any measurability assertion about the image: the
          -- outer measure is countably subadditive.  The remaining obligation
          -- is the bounded scalar Sard estimate.
          let s : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
            {x | fderiv ℝ f x = 0}
          change (volume : Measure ℝ) (f '' s) = 0
          suffices H : ∀ R : ℕ,
              (volume : Measure ℝ)
                (f '' (s ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) R)) = 0 by
            rw [← nonpos_iff_eq_zero,
              ← Metric.iUnion_inter_closedBall_nat s (0 : EuclideanSpace ℝ (Fin (k + 2)))]
            calc
              (volume : Measure ℝ)
                  (f '' ⋃ n : ℕ,
                    s ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) n) ≤
                    ∑' n : ℕ, (volume : Measure ℝ)
                      (f '' (s ∩ Metric.closedBall
                        (0 : EuclideanSpace ℝ (Fin (k + 2))) n)) := by
                          rw [Set.image_iUnion]
                          exact measure_iUnion_le _
              _ ≤ 0 := by simp [H]
          intro R
          cases R with
          | zero =>
              apply measure_mono_null (t := ({f 0} : Set ℝ))
              · rintro _ ⟨x, hx, rfl⟩
                have hx0 : x = (0 : EuclideanSpace ℝ (Fin (k + 2))) := by
                  simpa using hx.2
                simp [hx0]
              · simp
          | succ R =>
              -- First discard the locally constant open part of the critical
              -- set.  The image of that part is countable (separable source),
              -- and the argument is entirely in outer measure.  What remains
              -- is the nowhere-open boundary stratum; this is the genuine
              -- higher scalar Sard estimate.
              refine RegularValueAeSupport.critical_image_null_of_remainder
                f (hf.differentiable (by simp))
                (s ∩ Metric.closedBall
                  (0 : EuclideanSpace ℝ (Fin (k + 2))) ( (R + 1 : ℕ) : ℝ)) ?_ ?_
              · intro x hx
                exact hx.1
              · -- the remaining set is literally the frontier of a closed
                -- critical compact set; future Sard/Taylor induction only
                -- has to handle this boundary.
                have hc : IsClosed s := by
                  dsimp [s]
                  exact isClosed_eq (hf.continuous_fderiv (by simp)) continuous_const
                have hb : IsClosed
                    (s ∩ Metric.closedBall
                      (0 : EuclideanSpace ℝ (Fin (k + 2))) ((R + 1 : ℕ) : ℝ)) :=
                  hc.inter Metric.isClosed_closedBall
                -- Stratify by the first nonzero higher Fréchet jet.  The
                -- order `k+3` flat part is already small by Taylor plus
                -- Hausdorff dimension; only the finite-order hypersurface
                -- strata remain.
                refine RegularValueAeSupport.image_subset_flatJet_one_null_of_strata
                  f _ ?_ (k+3) (by omega) ?_ ?_
                · intro x hx
                  exact hx.1.1
                · apply RegularValueAeSupport.image_flatJet_volume_zero f hf
                  simp
                · -- On this locus the `(j+1)`-st jet is nonzero, so the zero of
                  -- a scalar `j`-th partial derivative is a smooth
                  -- hypersurface; scalar Sard in one lower source dimension
                  -- finishes the induction.
                  intro j hj jq
                  -- Nullity of a stratum is a countably local assertion.  This is
                  -- a useful place to switch to pointwise charts: no
                  -- measurability of the stratum/image is ever used.
                  refine RegularValueAeSupport.image_null_of_locally
                    (volume : Measure ℝ) (f:=f)
                    (s:=RegularValueAeSupport.flatJet f j \
                         RegularValueAeSupport.flatJet f (j+1)) ?_
                  intro x hx
                  -- extract a scalar equation cutting out this particular finite
                  -- jet stratum
                  rcases RegularValueAeSupport.flatJet_local_equation f hf j hj (x:=x) hx with
                    ⟨h, hh, hL, hflat⟩
                  let L : (EuclideanSpace ℝ (Fin (k+2))) →L[ℝ] ℝ := fderiv ℝ h x
                  have hL' : L ≠ 0 := hL
                  have hsur : (L : (EuclideanSpace ℝ (Fin (k+2))) →ₗ[ℝ] ℝ).range = ⊤ :=
                    RegularValueAeSupport.scalar_range_top L hL'
                  let sh : HasStrictFDerivAt h L x :=
                    hh.contDiffAt.hasStrictFDerivAt (by simp)
                  let T := sh.implicitToOpenPartialHomeomorph h L hsur
                  let φ : (LinearMap.ker (L : (EuclideanSpace ℝ (Fin (k+2))) →ₗ[ℝ] ℝ)) →
                      EuclideanSpace ℝ (Fin (k+2)) :=
                    fun z => sh.implicitFunction h L hsur (h x) z
                  let q : (LinearMap.ker (L : (EuclideanSpace ℝ (Fin (k+2))) →ₗ[ℝ] ℝ)) → ℝ :=
                    fun z => f (φ z)
                  -- What remains after the submersion chart is the
                  -- lower-dimensional scalar estimate on its kernel.
                  -- the kernel has one less dimension; this is precisely the
                  -- remaining inductive hypersurface chart estimate.
                  have hdim : Module.finrank ℝ
                      (LinearMap.ker (L : (EuclideanSpace ℝ (Fin (k+2))) →ₗ[ℝ] ℝ)) + 1 =
                        Module.finrank ℝ (EuclideanSpace ℝ (Fin (k+2))) :=
                    RegularValueAeSupport.finrank_ker_scalar L hL'

                  exact
                    RegularValueAeSupport.local_flatJet_stratum_of_kernel_IH
                      f hf j hj hx (by
                        intro h0 y L0 sh0 hL0 g hg
                        exact
                          RegularValueAeSupport.critical_image_null_fd g hg)
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
