import Mathlib

namespace Submission

namespace LeanEval.Analysis.HausdorffAbsoluteContinuity

/-!
# Hausdorff moment problem: absolute-continuity criterion

`hausdorff_absolute_continuity`: a positive probability measure `μ` on the unit
cube is uniformly absolutely continuous with respect to Lebesgue measure iff its
moment differences are dominated by those of Lebesgue measure. This is the third
statement of §115 of the Knill survey (the moment realizability and positivity
criteria are the companion lean-eval problems). The trusted helpers (`cube`,
`monomial`, `momentOf`, `multiChoose`, `diff`, `UniformlyAbsolutelyContinuous`)
are non-holes. Mathlib has `SignedMeasure`, finite measures, and set integrals
but no moment-problem machinery.

Category-(b) candidate from §115 of the Knill survey (additional statement 2).
-/

open MeasureTheory
open scoped BigOperators NNReal

/-- The closed unit cube `Iᵈ = [0,1]ᵈ ⊆ ℝᵈ`. -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The monomial `xⁿ = ∏ᵢ xᵢ^{nᵢ}`. -/
def monomial {d : ℕ} (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, (x i) ^ (n i)

/-- The `n`-th moment `∫_{Iᵈ} xⁿ dμ`. -/
noncomputable def momentOf {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (n : Fin d → ℕ) : ℝ :=
  ∫ x in cube d, monomial n x ∂μ

/-- The multi-index binomial coefficient `C(n,k) = ∏ᵢ C(nᵢ, kᵢ)`. -/
def multiChoose {d : ℕ} (n k : Fin d → ℕ) : ℕ := ∏ i, (n i).choose (k i)

/-- The iterated backward partial difference `(Δᵏa)ₙ` in closed form. -/
noncomputable def diff {d : ℕ} (a : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) : ℝ :=
  ∑ j ∈ Finset.Iic k,
    (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * a (n - j)

/-- `μ` is **uniformly absolutely continuous** w.r.t. `ν`: `μ ≤ C • ν` for some
constant `C` (an essentially-bounded Radon–Nikodym density). -/
def UniformlyAbsolutelyContinuous {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ C : ℝ≥0, μ ≤ C • ν



end LeanEval.Analysis.HausdorffAbsoluteContinuity

open LeanEval.Analysis.HausdorffAbsoluteContinuity
open MeasureTheory
open scoped BigOperators NNReal
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

-- Algebraic identities for the kernels
private lemma scalar_diff_kernel (x : ℝ) (n k : ℕ) (h : k ≤ n) :
    (∑ j ∈ Finset.range (k+1),
      (-1 : ℝ) ^ (k-j) * (k.choose j : ℝ) * x ^ (n-j)) =
      x ^ (n-k) * (1-x)^k := by
  classical
  calc
    (∑ j ∈ Finset.range (k+1),
      (-1 : ℝ) ^ (k-j) * (k.choose j : ℝ) * x ^ (n-j)) =
        ∑ j ∈ Finset.range (k+1),
          x^(n-k) * ((-1 : ℝ)^(k-j) * (k.choose j : ℝ) * x^(k-j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            rw [← Nat.sub_add_sub_cancel h hj', pow_add]
            ring
    _ = x^(n-k) * (∑ j ∈ Finset.range (k+1),
          ((-1 : ℝ)^(k-j) * (k.choose j : ℝ) * x^(k-j))) := by
            rw [Finset.mul_sum]
    _ = x^(n-k) * (1 + (-x))^k := by
          congr 1
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro j hj
          rw [neg_pow]
          simp
          ring
    _ = x^(n-k) * (1-x)^k := by rw [sub_eq_add_neg]



private lemma multi_diff_kernel {d : ℕ} (x : EuclideanSpace ℝ (Fin d))
    (n k : Fin d → ℕ) (h : k ≤ n) :
    (∑ j ∈ Finset.Iic k,
       (-1 : ℝ) ^ (∑ i, (k i - j i)) *
         (multiChoose k j : ℝ) * monomial (n-j) x) =
      ∏ i, (x i)^(n i-k i) * (1-x i)^(k i) := by
  classical
  have hI : Finset.Iic k =
      Fintype.piFinset (fun i : Fin d => Finset.range (k i + 1)) := by
    ext j
    simp only [Finset.mem_Iic, Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · intro hj i
      exact Nat.lt_succ_of_le (hj i)
    · intro hj i
      exact Nat.lt_succ_iff.mp (hj i)
  calc
    (∑ j ∈ Finset.Iic k,
       (-1 : ℝ) ^ (∑ i, (k i - j i)) *
         (multiChoose k j : ℝ) * monomial (n-j) x) =
      ∑ j ∈ Fintype.piFinset (fun i : Fin d => Finset.range (k i + 1)),
        ∏ i, ((-1 : ℝ)^(k i - j i) * ((k i).choose (j i) : ℝ) *
             (x i)^(n i - j i)) := by
          rw [hI]
          apply Finset.sum_congr rfl
          intro j hj
          have hpow : (-1 : ℝ) ^ (∑ i, (k i - j i)) =
              ∏ i, (-1 : ℝ)^(k i - j i) := by
                rw [Finset.prod_pow_eq_pow_sum]
          rw [hpow]
          change (∏ i, (-1 : ℝ)^(k i - j i)) *
              (multiChoose k j : ℝ) *
              (∏ i, (x i) ^ ((n - j) i)) = _
          simp only [Pi.sub_apply]
          -- distribute products
          rw [multiChoose]
          rw [Nat.cast_prod]
          -- collect the three products
          rw [← Finset.prod_mul_distrib]
          rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ ji ∈ Finset.range (k i + 1),
           ((-1 : ℝ)^(k i - ji) * ((k i).choose ji : ℝ) *
             (x i)^(n i - ji)) := by
          rw [Finset.prod_univ_sum]
    _ = ∏ i, (x i)^(n i-k i) * (1-x i)^(k i) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact scalar_diff_kernel (x i) (n i) (k i) (h i)


private def ker {d : ℕ} (k n : Fin d → ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, (x i)^(n i - k i) * (1 - x i)^(k i)

private lemma cube_compact (d : ℕ) : IsCompact (cube d) := by
  classical
  apply Metric.isCompact_iff_isClosed_bounded.2
  constructor
  · have hc : cube d = ⋂ i : Fin d,
        (fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹' Set.Icc (0:ℝ) 1 := by
          ext x
          simp [cube]
    rw [hc]
    apply isClosed_iInter
    intro i
    apply IsClosed.preimage (PiLp.continuous_apply (2:ENNReal) (fun _ : Fin d => ℝ) i)
    exact isClosed_Icc
  · -- use the euclidean norm bound `sqrt d`
    refine (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin d))).2 ?_
    refine ⟨Real.sqrt d, ?_⟩
    intro x hx
    change dist x 0 ≤ Real.sqrt d
    rw [dist_zero_right, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc
      (∑ i : Fin d, ‖x i‖ ^ 2) ≤ ∑ _i : Fin d, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hxi0 : 0 ≤ x i := (hx i).1
        have hxi1 : x i ≤ 1 := (hx i).2
        have hn : ‖x i‖ ≤ (1:ℝ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hxi0]
          exact hxi1
        have hn0 : 0 ≤ ‖x i‖ := norm_nonneg _
        nlinarith
      _ = (d:ℝ) := by simp

private lemma cube_meas (d : ℕ) : MeasurableSet (cube d) :=
  (cube_compact d).isClosed.measurableSet

private lemma ker_cont {d : ℕ} (k n : Fin d → ℕ) :
    Continuous (ker k n) := by
  classical
  unfold ker
  fun_prop

private lemma monomial_cont {d : ℕ} (n : Fin d → ℕ) :
    Continuous (monomial n) := by
  classical
  unfold monomial
  fun_prop

private lemma ker_nonneg {d : ℕ} {k n : Fin d → ℕ} (h : k ≤ n)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cube d) :
    0 ≤ ker k n x := by
  classical
  unfold ker
  apply Finset.prod_nonneg
  intro i hi
  have h0 : 0 ≤ x i := (hx i).1
  have h1 : x i ≤ 1 := (hx i).2
  exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_nonneg.mpr h1) _)


private lemma diff_moment_kernel {d : ℕ}
    (m : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasureOnCompacts m]
    (k n : Fin d → ℕ) (h : k ≤ n) :
    diff (momentOf m) k n = ∫ x in cube d, ker k n x ∂m := by
  classical
  unfold diff momentOf
  -- put the finite linear combination under the integral
  calc
    (∑ j ∈ Finset.Iic k,
      (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) *
        (∫ x in cube d, monomial (n - j) x ∂m)) =
        ∑ j ∈ Finset.Iic k,
          (∫ x in cube d,
            ((-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ)) *
              monomial (n-j) x ∂m) := by
              apply Finset.sum_congr rfl
              intro j hj
              change _ = ∫ x, (_ : ℝ) • monomial (n-j) x ∂(m.restrict (cube d))
              rw [MeasureTheory.integral_smul]
              rfl
    _ = ∫ x in cube d,
          (∑ j ∈ Finset.Iic k,
            (((-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ)) *
               monomial (n-j) x)) ∂m := by
            symm
            apply MeasureTheory.integral_finset_sum
            intro j hj
            have hmj : IntegrableOn (monomial (n-j)) (cube d) m :=
              ContinuousOn.integrableOn_compact (μ := m)
                (cube_compact d) (monomial_cont (n-j)).continuousOn
            exact hmj.const_mul _
    _ = ∫ x in cube d, ker k n x ∂m := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          exact multi_diff_kernel x n k h


/-- On a Euclidean space it suffices to compare the integrals of nonnegative
compactly supported continuous functions to compare two finite measures.  The
usual compact-neighbourhood proof of the Riesz comparison lemma only uses
nonnegative bump functions. -/
private lemma le_of_nonneg_cont {d : ℕ}
    (m v : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m] [IsFiniteMeasure v]
    (ht : ∀ f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin d)) ℝ,
      (∀ x, 0 ≤ f x) → (∫ x, f x ∂m) ≤ ∫ x, f x ∂v) : m ≤ v := by
  classical
  have hcomp : ∀ ⦃K : Set (EuclideanSpace ℝ (Fin d))⦄, IsCompact K → m K ≤ v K := by
    intro K hK
    -- the standard compact-neighbourhood proof
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hv => ?_
    have hvK : v K ≠ ⊤ := hv.ne
    have hmK : m K ≠ ⊤ := hK.measure_lt_top.ne
    obtain ⟨V, pV1, pV2, pV3⟩ : ∃ V ⊇ K, IsOpen V ∧ v V ≤ v K + ε :=
      Set.exists_isOpen_le_add K v (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
    suffices hh : m.real K ≤ v.real K + ε by
      rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
      all_goals finiteness
    have VltTop : v V < ⊤ := pV3.trans_lt <| by finiteness
    obtain ⟨f, pf1, pf2, pf3⟩ :
        ∃ f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin d)) ℝ,
          Set.EqOn (⇑f) 1 K ∧ tsupport ⇑f ⊆ V ∧ ∀ x, f x ∈ Set.Icc (0:ℝ) 1 := by
      obtain ⟨g, hg1, hg2, hg3⟩ :=
        exists_continuousMap_one_of_isCompact_subset_isOpen hK pV2 pV1
      exact ⟨⟨g, hasCompactSupport_def.mpr hg2⟩, hg1, hg3⟩
    have hfV (x : EuclideanSpace ℝ (Fin d)) :
        f x ≤ V.indicator 1 x := by
      by_cases hx : x ∈ tsupport f
      · simp [(pf2 hx), (pf3 x).2]
      · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
    have hfK (x : EuclideanSpace ℝ (Fin d)) :
        K.indicator 1 x ≤ f x := by
      by_cases hx : x ∈ K
      · simp [hx, pf1 hx]
      · simp [hx, (pf3 x).1]
    calc
      m.real K = ∫ x, K.indicator 1 x ∂m := (integral_indicator_one hK.measurableSet).symm
      _ ≤ ∫ x, f x ∂m := by
        refine integral_mono ?_ f.integrable hfK
        exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
      _ ≤ ∫ x, f x ∂v := ht f (fun x => (pf3 x).1)
      _ ≤ ∫ x, V.indicator 1 x ∂v := by
        refine integral_mono f.integrable ?_ hfV
        exact IntegrableOn.integrable_indicator integrableOn_const pV2.measurableSet
      _ ≤ (v K).toReal + (ε:ℝ) := by
        rwa [integral_indicator_one pV2.measurableSet, measureReal_def,
          ← ENNReal.coe_toReal, ← ENNReal.toReal_add, ENNReal.toReal_le_toReal]
        all_goals finiteness
  refine Measure.le_iff.2 ?_
  intro s hs
  -- inner regularity of a finite Borel measure on the Euclidean space
  rw [Measure.InnerRegularWRT.measure_eq_iSup
        (Measure.InnerRegular.innerRegular (μ:=m)) hs]
  refine iSup_le ?_
  intro K
  refine iSup_le ?_
  intro hKs
  refine iSup_le ?_
  intro hK
  exact (hcomp hK).trans (measure_mono hKs)


open Filter Topology
open scoped unitInterval

private lemma tensor_cont_upd {d : ℕ} (i : Fin d) : Continuous (fun p : I × (Fin d → I) => Function.update p.2 i p.1) := by
 classical
 apply continuous_pi
 intro j
 by_cases h : j = i
 · subst j
   simpa [Function.update_self] using (continuous_fst : Continuous fun p : I × (Fin d → I) => p.1)
 · convert ((continuous_apply j).comp (continuous_snd : Continuous fun p : I × (Fin d → I) => p.2)) using 1
   ext p; simp [h]

private noncomputable def tensorT {d:ℕ} (n:ℕ) (i:Fin d) (f : C(Fin d → I, ℝ)) : C(Fin d → I, ℝ) :=
{ toFun := fun x => ∑ k : Fin (n+1), bernstein n k (x i) * f (Function.update x i (bernstein.z k))
  continuous_toFun := by
    apply continuous_finset_sum _
    intro k hk
    apply Continuous.mul
    · fun_prop
    · apply f.continuous.comp
      -- x ↦ update x constant; via tensor_cont_upd
      exact (tensor_cont_upd i).comp (by fun_prop : Continuous fun x : Fin d → I => (bernstein.z k, x)) }

-- construct g
private noncomputable def tensorG {d:ℕ} (i:Fin d) (f:C(Fin d → I,ℝ)) : C(I, C(Fin d → I,ℝ)) :=
  (⟨(fun p : I × (Fin d → I) => f (Function.update p.2 i p.1)),
     f.continuous.comp (tensor_cont_upd i)⟩ : C(I × (Fin d → I),ℝ)).curry

private lemma tensorT_apply_eq {d} (n:ℕ) (i:Fin d) (f:C(Fin d → I,ℝ)) (x:Fin d → I) :
 tensorT n i f x = (bernsteinApproximation n (tensorG i f) (x i)) x := by
 classical
 rw [bernsteinApproximation.apply]
 simp only [tensorG, ContinuousMap.curry_apply]
 change (∑ k : Fin (n+1), _) = _ --? tensorT
 simp [tensorT]

private lemma tensorT_err {d} (n:ℕ) (i:Fin d) (f:C(Fin d → I,ℝ)) :
  ‖tensorT n i f - f‖ ≤ ‖bernsteinApproximation n (tensorG i f) - tensorG i f‖ := by
  classical
  let H : C(I, C(Fin d → I,ℝ)) := bernsteinApproximation n (tensorG i f) - tensorG i f
  have hH0 : 0 ≤ ‖H‖ := norm_nonneg H
  apply (ContinuousMap.norm_le _ hH0).2
  intro x
  calc
   ‖(tensorT n i f - f) x‖ = ‖(bernsteinApproximation n (tensorG i f) (x i) - (tensorG i f) (x i)) x‖ := by
     rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply]
     rw [tensorT_apply_eq]
     change ‖_ - f x‖ = ‖_ - f (Function.update x i (x i))‖
     rw [Function.update_eq_self]
   _ ≤ ‖(bernsteinApproximation n (tensorG i f) (x i) - (tensorG i f) (x i))‖ := ContinuousMap.norm_coe_le_norm _ _
   _ ≤ ‖H‖ := by
     exact ContinuousMap.norm_coe_le_norm H (x i)

private lemma tensorT_tend {d} (i:Fin d) (f:C(Fin d → I,ℝ)) :
 Tendsto (fun n : ℕ => tensorT n i f) atTop (𝓝 f) := by
 have h := bernsteinApproximation_uniform (tensorG i f)
 have h' : Tendsto (fun n : ℕ =>
      ContinuousMap.equivBoundedOfCompact I (C(Fin d → I,ℝ)) (bernsteinApproximation n (tensorG i f)))
    atTop (𝓝 (ContinuousMap.equivBoundedOfCompact I (C(Fin d → I,ℝ)) (tensorG i f))) :=
      ( (ContinuousMap.isUniformEmbedding_equivBoundedOfCompact I (C(Fin d → I,ℝ))).isInducing.tendsto_nhds_iff).1 h
 -- output via inducing
 apply ( (ContinuousMap.isUniformEmbedding_equivBoundedOfCompact (Fin d → I) ℝ).isInducing.tendsto_nhds_iff).2
 rw [Metric.tendsto_atTop] at h' ⊢
 intro eps heps
 rcases h' eps heps with ⟨N,hN⟩
 refine ⟨N, ?_⟩
 intro n hn
 have hn' := hN n hn
 change dist (tensorT n i f) f < eps -- since mapped distance defeq
 -- convert
 rw [dist_eq_norm]
 have hb := tensorT_err n i f
 have hn'' : ‖bernsteinApproximation n (tensorG i f) - tensorG i f‖ < eps := by
   -- dist equality C/BCF
   change dist (bernsteinApproximation n (tensorG i f)) (tensorG i f) < eps at hn'
   exact (dist_eq_norm (bernsteinApproximation n (tensorG i f)) (tensorG i f)) ▸ hn'
 exact lt_of_le_of_lt hb hn''
private lemma tensorT_contract {d} (n:ℕ) (i:Fin d) (f g:C(Fin d → I,ℝ)) :
 ‖tensorT n i f - tensorT n i g‖ ≤ ‖f-g‖ := by
 classical
 have h0 : 0 ≤ ‖f-g‖ := norm_nonneg _
 apply (ContinuousMap.norm_le _ h0).2
 intro x
 change |(∑ k : Fin (n+1), bernstein n k (x i) * f (Function.update x i (bernstein.z k))) -
   (∑ k : Fin (n+1), bernstein n k (x i) * g (Function.update x i (bernstein.z k)))| ≤ _
 rw [← Finset.sum_sub_distrib]
 calc
  |∑ k : Fin (n+1), (bernstein n k (x i) * f _ - bernstein n k (x i) * g _)|
    ≤ ∑ k : Fin (n+1), |bernstein n k (x i) * f (Function.update x i (bernstein.z k)) - bernstein n k (x i) * g (Function.update x i (bernstein.z k))| := Finset.abs_sum_le_sum_abs _ _
  _ ≤ ∑ k : Fin (n+1), bernstein n k (x i) * ‖f-g‖ := by
    apply Finset.sum_le_sum; intro k hk
    rw [← mul_sub, abs_mul]
    rw [abs_of_nonneg (bernstein_nonneg)]
    exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm (f-g) _) bernstein_nonneg
  _ = ‖f-g‖ := by rw [← Finset.sum_mul, bernstein.probability, one_mul]
private noncomputable def tensorIter {d} (n:ℕ) : List (Fin d) → C(Fin d → I,ℝ) → C(Fin d → I,ℝ)
 | [], f => f
 | i::l, f => tensorT n i (tensorIter n l f)

private lemma tensorIter_err {d} (n:ℕ) (l:List (Fin d)) (f:C(Fin d → I,ℝ)) :
 ‖tensorIter n l f - f‖ ≤ (l.map (fun i => ‖tensorT n i f - f‖)).sum := by
 classical
 induction l with
 | nil => simp [tensorIter]
 | cons i l ih =>
   rw [tensorIter]
   have tri : ‖tensorT n i (tensorIter n l f) - f‖ ≤
       ‖tensorT n i (tensorIter n l f) - tensorT n i f‖ + ‖tensorT n i f - f‖ := by
       calc
        _ = ‖(tensorT n i (tensorIter n l f) - tensorT n i f) + (tensorT n i f - f)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
   have hb : ‖tensorT n i (tensorIter n l f) - tensorT n i f‖ ≤ ‖tensorIter n l f - f‖ := tensorT_contract _ _ _ _
   calc
    _ ≤ ‖tensorIter n l f - f‖ + ‖tensorT n i f - f‖ := tri.trans (add_le_add hb (le_rfl))
    _ ≤ (l.map (fun z => ‖tensorT n z f - f‖)).sum + ‖tensorT n i f - f‖ := add_le_add ih (le_rfl)
    _ = _ := by simp [add_comm]
private lemma tensorT_err_event {d} (i:Fin d) (f:C(Fin d → I,ℝ)) :
 Tendsto (fun n : ℕ => ‖tensorT n i f - f‖) atTop (𝓝 0) := by
 have h := tensorT_tend i f
 exact tendsto_iff_norm_sub_tendsto_zero.1
   (by -- topology C compactOpen, but target h and private lemma expects norm topology? 
    exact h)
private lemma tensorList_err_event {d} (l:List (Fin d)) (f:C(Fin d → I,ℝ)) :
 Tendsto (fun n : ℕ => (l.map (fun i => ‖tensorT n i f - f‖)).sum) atTop (𝓝 0) := by
 induction l with
 | nil => simp
 | cons i l ih =>
   simpa using ( (tensorT_err_event i f).add ih)

private lemma tensorIter_tend {d} (l:List (Fin d)) (f:C(Fin d → I,ℝ)) :
 Tendsto (fun n : ℕ => tensorIter n l f) atTop (𝓝 f) := by
 apply tendsto_iff_norm_sub_tendsto_zero.2
 -- squeeze norm nonnegative and tensorIter_err
 have h := tensorList_err_event l f
 exact squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) (Filter.Eventually.of_forall (fun n => tensorIter_err n l f)) h


private noncomputable def tensorToE {d : ℕ} (x : Fin d → I) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp _ (fun i => (x i : ℝ))

private lemma tensorToE_apply {d : ℕ} (x : Fin d → I) (i : Fin d) :
    tensorToE x i = (x i : ℝ) := rfl

private lemma tensorToE_cont {d : ℕ} :
    Continuous (fun x : Fin d → I => tensorToE x) := by
  unfold tensorToE
  apply (PiLp.continuous_toLp (2:ENNReal) (fun _ : Fin d => ℝ)).comp
  fun_prop

private noncomputable def tensorGrid {d : ℕ} (n : ℕ) (j : Fin d → ℕ) : Fin d → I :=
 fun i => bernstein.z (n:=n) ⟨min (j i) n, Nat.lt_succ_of_le (min_le_right _ _)⟩

private lemma tensor_kernel_weight {d : ℕ} (n : ℕ) (j : Fin d → ℕ)
    (hj : j ≤ (fun _ : Fin d => n)) (x : Fin d → I) :
 (multiChoose (fun _ : Fin d => n) j : ℝ) *
    ker ((fun _ : Fin d => n) - j) (fun _ : Fin d => n) (tensorToE x) =
      ∏ i, bernstein n (j i) (x i) := by
 classical
 unfold ker
 rw [multiChoose, Nat.cast_prod]
 rw [← Finset.prod_mul_distrib]
 apply Finset.prod_congr rfl
 intro i hi
 rw [bernstein_apply]
 simp only [tensorToE_apply, Pi.sub_apply]
 have hji := hj i
 have he1 : n - (n - j i) = j i := Nat.sub_sub_self hji
 rw [he1]
 -- arrange
 ring

private lemma tensorGrid_apply_of_le {d : ℕ} (n : ℕ) (j : Fin d → ℕ)
   (hj : j ≤ (fun _ : Fin d => n)) (i : Fin d) :
 tensorGrid n j i = bernstein.z (n:=n) ⟨j i, Nat.lt_succ_of_le (hj i)⟩ := by
 unfold tensorGrid
 have e : min (j i) n = j i := min_eq_left (hj i)
 simp [e]


private lemma tensor_reindex {d : ℕ} (n : ℕ) (φ : (Fin d → ℕ) → ℝ) :
  (∑ j ∈ Finset.Iic (fun _ : Fin d => n), φ j) =
    ∑ q : Fin d → Fin (n+1), φ (fun i => (q i : ℕ)) := by
 classical
 -- bijection between bounded `Nat` functions and `Fin` functions
 let lift : (Fin d → ℕ) → (Fin d → Fin (n+1)) :=
   fun j i => ⟨min (j i) n, Nat.lt_succ_of_le (min_le_right _ _)⟩

 have linv {j : Fin d → ℕ} (hj : j ∈ Finset.Iic (fun _ : Fin d => n)) :
     (fun i => ((lift j i : Fin (n+1)) : ℕ)) = j := by
   funext i
   exact min_eq_left ((Finset.mem_Iic.mp hj) i)
 have rinv (q : Fin d → Fin (n+1)) :
     lift (fun i => (q i : ℕ)) = q := by
   funext i
   apply Fin.ext
   exact min_eq_left (Nat.lt_succ_iff.mp (q i).isLt)
 classical
 refine Finset.sum_bij (s:=Finset.Iic (fun _ : Fin d => n))
   (t:= (Finset.univ : Finset (Fin d → Fin (n+1))))
   (f:=φ) (g:= fun q => φ (fun i => (q i : ℕ)))
   (fun j _ => lift j) ?_ ?_ ?_ ?_
 · intro a ha; simp
 · intro a₁ h₁ a₂ h₂ eq
   have e1 := linv h₁
   have e2 := linv h₂
   calc a₁ = (fun i => ((lift a₁ i : Fin (n+1)) : ℕ)) := e1.symm
        _ = (fun i => ((lift a₂ i : Fin (n+1)) : ℕ)) := congrArg (fun z : Fin d → Fin (n+1) => fun i => (z i : ℕ)) eq
        _ = a₂ := e2
 · intro q hq
   have hmem : (fun i => ((q i : Fin (n+1)) : ℕ)) ∈
        Finset.Iic (fun _ : Fin d => n) :=
      Finset.mem_Iic.mpr (fun i => Nat.lt_succ_iff.mp (q i).isLt)
   exact ⟨_, hmem, rinv q⟩
 · intro a ha
   rw [linv ha]


private noncomputable def tensorWeight {d : ℕ} (n : ℕ) (x : Fin d → I)
  (q : Fin d → Fin (n+1)) : ℝ := ∏ i, bernstein n (q i) (x i)

private lemma tensorWeight_sum {d : ℕ} (n : ℕ) (x : Fin d → I) :
    (∑ q : Fin d → Fin (n+1), tensorWeight n x q) = 1 := by
 classical
 change (∑ q ∈ Finset.univ, _) = _
 rw [show (Finset.univ : Finset (Fin d → Fin (n+1))) =
   Fintype.piFinset (fun _ : Fin d => (Finset.univ : Finset (Fin (n+1)))) by ext q; simp]
 unfold tensorWeight
 have e := Finset.prod_univ_sum
    (R:=ℝ) (ι:=Fin d) (κ:=fun _ : Fin d => Fin (n+1))
    (fun _ : Fin d => (Finset.univ : Finset (Fin (n+1))))
    (fun i q => bernstein n q (x i))
 rw [← e]
 simp [bernstein.probability]


private lemma tensor_flat {d : ℕ} (n : ℕ) (F : C(Fin d → I, ℝ)) (x : Fin d → I) :
 (∑ j ∈ Finset.Iic (fun _ : Fin d => n),
    ((multiChoose (fun _ : Fin d => n) j : ℝ) * F (tensorGrid n j)) *
      ker ((fun _ : Fin d => n) - j) (fun _ : Fin d => n) (tensorToE x)) =
    ∑ q : Fin d → Fin (n+1), tensorWeight n x q *
       F (fun i => bernstein.z (n:=n) (q i)) := by
 classical
 rw [tensor_reindex]
 apply Finset.sum_congr rfl
 intro q hq
 change ((multiChoose (fun _ : Fin d => n) (fun i => (q i : ℕ)) : ℝ) *
    F (tensorGrid n (fun i => (q i : ℕ)))) * _ = _
 have hj : (fun i => (q i : ℕ)) ≤ (fun _ : Fin d => n) :=
    fun i => Nat.lt_succ_iff.mp (q i).isLt
 have hw := tensor_kernel_weight n (fun i => (q i : ℕ)) hj x
 have hg : tensorGrid n (fun i => (q i : ℕ)) =
        (fun i => bernstein.z (n:=n) (q i)) := by
    funext i
    simpa using tensorGrid_apply_of_le n (fun i => (q i : ℕ)) hj i
 unfold tensorWeight
 rw [hg]
 rw [mul_assoc]
 rw [mul_comm (F _) (ker _ _ _)]
 rw [← mul_assoc]
 rw [hw]



-- Partial tensor Bernstein operators, indexed by a set of coordinates.
-- Using the subtype of the finite set for the coefficients avoids dummy
-- summation variables in the induction adding one coordinate.
private noncomputable def partialPoint {d : ℕ} {n : ℕ}
    (S : Finset (Fin d)) (q : (↥S → Fin (n+1)))
    (x : Fin d → I) : Fin d → I :=
  fun j => if h : j ∈ S then bernstein.z (n:=n) (q ⟨j,h⟩) else x j

private noncomputable def tensorPart {d : ℕ} (n : ℕ)
    (S : Finset (Fin d)) (f : C(Fin d → I, ℝ)) (x : Fin d → I) : ℝ :=
  ∑ q : (↥S → Fin (n+1)),
      (∏ u : ↥S, bernstein n (q u) (x u.1)) *
        f (partialPoint (n:=n) S q x)

private noncomputable def tensorExtend {d : ℕ} {n : ℕ}
    {S : Finset (Fin d)} (i : Fin d) (hi : i ∉ S)
    (k : Fin (n+1)) (q : ↥S → Fin (n+1)) :
      ↥(insert i S) → Fin (n+1) :=
  fun u => if h : (u.1 : Fin d) = i then k
    else q ⟨u.1, (Finset.mem_insert.mp u.2).resolve_left h⟩

private lemma tensorExtend_i {d : ℕ} {n : ℕ}
    {S : Finset (Fin d)} (i : Fin d) (hi : i ∉ S)
    (k : Fin (n+1)) (q : ↥S → Fin (n+1)) :
    tensorExtend (S:=S) i hi k q ⟨i, Finset.mem_insert_self i S⟩ = k := by
  simp [tensorExtend]

private lemma tensorExtend_of_mem {d : ℕ} {n : ℕ}
    {S : Finset (Fin d)} (i : Fin d) (hi : i ∉ S)
    (k : Fin (n+1)) (q : ↥S → Fin (n+1)) (u : ↥S) :
    tensorExtend (S:=S) i hi k q
      ⟨u.1, Finset.mem_insert_of_mem u.2⟩ = q u := by
  -- at a genuine element of `S` the new value is the old one
  have hne : (u.1 : Fin d) ≠ i := by
    intro h
    apply hi
    simpa [h] using u.2
  simp [tensorExtend, hne]

private noncomputable def tensorExtendEquiv {d : ℕ} {n : ℕ}
    {S : Finset (Fin d)} (i : Fin d) (hi : i ∉ S) :
    (Fin (n+1) × (↥S → Fin (n+1))) ≃
      (↥(insert i S) → Fin (n+1)) where
  toFun p := tensorExtend (S:=S) i hi p.1 p.2
  invFun r := (r ⟨i, Finset.mem_insert_self i S⟩,
    fun u => r ⟨u.1, Finset.mem_insert_of_mem u.2⟩)
  left_inv p := by
    cases p with
    | mk k q =>
      -- extensional equality of the pair
      apply Prod.ext
      · exact tensorExtend_i (S:=S) i hi k q
      · funext u
        exact tensorExtend_of_mem (S:=S) i hi k q u
  right_inv r := by
    funext u
    by_cases h : (u.1 : Fin d) = i
    · -- this is the distinguished new coordinate
      have hu : (u : ↥(insert i S)) = ⟨i, Finset.mem_insert_self i S⟩ := by
        apply Subtype.ext
        exact h
      subst u
      simpa [tensorExtend]
    · -- it was already in `S`
      simp [tensorExtend, h]

private lemma tensorPart_cons_point {d : ℕ} (n : ℕ)
    (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S)
    (k : Fin (n+1)) (q : ↥S → Fin (n+1)) (x : Fin d → I) :
    partialPoint (n:=n) S q (Function.update x i (bernstein.z (n:=n) k)) =
      partialPoint (n:=n) (insert i S) (tensorExtend (S:=S) i hi k q) x := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    -- the new coordinate
    simp [partialPoint, hi, tensorExtend, Function.update_apply]
  · by_cases hs : j ∈ S
    · have his : j ∈ insert i S := Finset.mem_insert_of_mem hs
      have hh : tensorExtend (S:=S) i hi k q
          ⟨j, his⟩ = q ⟨j, hs⟩ := by
        -- same as the old-coordinate lemma
        simpa using
          (tensorExtend_of_mem (S:=S) i hi k q (⟨j,hs⟩ : ↥S))
      simp [partialPoint, hs, his, hj, Function.update_apply, hh]
    · have his : j ∉ insert i S := by
          simp [hj, hs]
      simp [partialPoint, hs, his, hj, Function.update_apply]

private lemma tensorPart_cons_weight {d : ℕ} (n : ℕ)
    (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S)
    (k : Fin (n+1)) (q : ↥S → Fin (n+1)) (x : Fin d → I) :
    bernstein n k (x i) *
        (∏ u : ↥S,
            bernstein n (q u)
              ((Function.update x i (bernstein.z (n:=n) k)) u.1)) =
      ∏ v : ↥(insert i S),
          bernstein n ((tensorExtend (S:=S) i hi k q) v) (x v.1) := by
  classical
  -- reindex the product over the inserted subtype explicitly as a product over
  -- the ambient finset; this makes `prod_insert` available.
  -- `Finset.prod_subtype` converts a subtype product.
  -- first the old factors do not see the update at `i`.
  have hold : (∏ u : ↥S,
            bernstein n (q u)
              ((Function.update x i (bernstein.z (n:=n) k)) u.1)) =
        ∏ u : ↥S, bernstein n (q u) (x u.1) := by
    apply Finset.prod_congr rfl
    intro u hu
    -- `u` is an element of the subtype fintype
    have hne : (u.1 : Fin d) ≠ i := by
      intro h
      apply hi
      simpa [h] using u.2
    rw [Function.update_of_ne hne]
  rw [hold]
  -- now split the new product into the new coordinate and the old subtype
  -- use the equivalence between subtype product and finset product
  -- the simp lemma `Finset.prod_subtype` has the right orientation.
  classical
  -- switch both subtype products to products over the finsets
  -- `Fin.prod` notation here is `Finset.univ.prod` on the subtype.
  -- We carry out this conversion with `Finset.prod_subtype`.
  -- formulate equalities locally to keep rewriting predictable.
  let W : Fin d → ℝ := fun a =>
        if h : a = i then bernstein n k (x a)
        else if ha : a ∈ S then bernstein n (q ⟨a,ha⟩) (x a)
        else 1
  have hnew (v : ↥(insert i S)) :
      bernstein n ((tensorExtend (S:=S) i hi k q) v) (x v.1)
          = W v.1 := by
    classical
    by_cases hvi : (v.1 : Fin d) = i
    · simp [tensorExtend, W, hvi]
    · have hvS : (v.1 : Fin d) ∈ S :=
        (Finset.mem_insert.mp v.2).resolve_left hvi
      -- no proof arguments survive because `Fin` is independent
      have he : (tensorExtend (S:=S) i hi k q) v =
          q ⟨v.1, hvS⟩ := by simp [tensorExtend, hvi]
      simp [W, hvi, hvS, he]
  have hnewprod :
      (∏ v : ↥(insert i S),
          bernstein n ((tensorExtend (S:=S) i hi k q) v) (x v.1)) =
        ∏ a ∈ insert i S, W a := by
    classical
    calc
      (∏ v : ↥(insert i S),
          bernstein n ((tensorExtend (S:=S) i hi k q) v) (x v.1)) =
          ∏ v : ↥(insert i S), W v.1 := by
            apply Finset.prod_congr rfl
            intro v hv
            exact hnew v
      _ = ∏ v ∈ (insert i S).attach, W v.1 := by
            -- the univ finset on a subtype is its attach
            rw [Finset.univ_eq_attach]
      _ = ∏ a ∈ insert i S, W a := Finset.prod_attach _ _
  rw [hnewprod]
  rw [Finset.prod_insert hi]
  have hWi : W i = bernstein n k (x i) := by simp [W]
  rw [hWi]
  -- identify the remaining product over `S`
  congr 1
  -- subtype product as attach again
  calc
    (∏ u : ↥S, bernstein n (q u) (x u.1)) =
        ∏ u ∈ S.attach, W u.1 := by
          rw [Finset.univ_eq_attach]
          apply Finset.prod_congr rfl
          intro u hu
          have hne : (u.1 : Fin d) ≠ i := by
            intro h
            apply hi
            simpa [h] using u.2
          simp [W, hne, u.2]
    _ = ∏ a ∈ S, W a := Finset.prod_attach _ _


set_option maxHeartbeats 800000 in
private lemma tensorPart_empty {d : ℕ} (n : ℕ)
    (f : C(Fin d → I, ℝ)) (x : Fin d → I) :
    tensorPart n (∅ : Finset (Fin d)) f x = f x := by
  classical
  have impossible (u : ↥(∅ : Finset (Fin d))) : False :=
    (Finset.exists_mem_empty_iff (fun _ : Fin d => True)).1
      ⟨u.1, u.2, trivial⟩
  let q0 : ↥(∅ : Finset (Fin d)) → Fin (n+1) :=
    fun u => (impossible u).elim
  have hall (q : ↥(∅ : Finset (Fin d)) → Fin (n+1)) : q = q0 := by
    funext u
    exact (impossible u).elim
  have hU : (Finset.univ : Finset (↥(∅ : Finset (Fin d)) → Fin (n+1))) = {q0} := by
    ext q
    constructor
    · intro h
      exact Finset.mem_singleton.mpr (hall q)
    · intro h
      exact Finset.mem_univ q
  unfold tensorPart
  -- expose the singleton summation rather than relying on its `default`
  change (∑ q : (↥(∅ : Finset (Fin d)) → Fin (n+1)),
      (∏ u : ↥(∅ : Finset (Fin d)), bernstein n (q u) (x u.1)) *
        f (partialPoint (n:=n) (∅ : Finset (Fin d)) q x)) = _
  rw [show (∑ q : (↥(∅ : Finset (Fin d)) → Fin (n+1)),
      (∏ u : ↥(∅ : Finset (Fin d)), bernstein n (q u) (x u.1)) *
        f (partialPoint (n:=n) (∅ : Finset (Fin d)) q x)) =
      (Finset.univ : Finset (↥(∅ : Finset (Fin d)) → Fin (n+1))).sum
        (fun q => (∏ u : ↥(∅ : Finset (Fin d)), bernstein n (q u) (x u.1)) *
        f (partialPoint (n:=n) (∅ : Finset (Fin d)) q x)) by rfl]
  rw [hU]
  simp only [Finset.sum_singleton]
  have hprod : (∏ u : ↥(∅ : Finset (Fin d)), bernstein n (q0 u) (x u.1)) = (1:ℝ) := by
    apply Fintype.prod_eq_one
    intro u
    exact (impossible u).elim
  have hpt : partialPoint (n:=n) (∅ : Finset (Fin d)) q0 x = x := by
    funext j
    -- no coordinate lies in the empty finset
    by_cases h : j ∈ (∅ : Finset (Fin d))
    · have hh : False :=
        (Finset.exists_mem_empty_iff (fun _ : Fin d => True)).1 ⟨j,h,trivial⟩
      exact hh.elim
    · simp [partialPoint, h]
  calc
    (∏ u : ↥(∅ : Finset (Fin d)), bernstein n (q0 u) (x u.1)) *
      f (partialPoint (n:=n) (∅ : Finset (Fin d)) q0 x)
        = (1:ℝ) * f x := congrArg₂ (fun a b : ℝ => a*b) hprod
            (congrArg (fun y : (Fin d → I) => f y) hpt)
    _ = f x := one_mul _


private lemma tensorPart_step {d : ℕ} (n : ℕ)
    (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S)
    (f : C(Fin d → I, ℝ)) (x : Fin d → I) :
    (∑ k : Fin (n+1), bernstein n k (x i) *
       tensorPart n S f (Function.update x i (bernstein.z (n:=n) k))) =
       tensorPart n (insert i S) f x := by
  classical
  -- first expose the two sums and distribute the outer scalar
  unfold tensorPart
  -- convenient notation for the summand on the inserted side
  let V : (↥(insert i S) → Fin (n+1)) → ℝ :=
    fun r => (∏ v : ↥(insert i S), bernstein n (r v) (x v.1)) *
      f (partialPoint (n:=n) (insert i S) r x)
  -- after distribution, a pair `(k,q)` has exactly this inserted summand
  have hp (k : Fin (n+1)) (q : ↥S → Fin (n+1)) :
      bernstein n k (x i) *
        ((∏ u : ↥S, bernstein n (q u)
             ((Function.update x i (bernstein.z (n:=n) k)) u.1)) *
          f (partialPoint (n:=n) S q
             (Function.update x i (bernstein.z (n:=n) k)))) =
        V ((tensorExtendEquiv (S:=S) (n:=n) i hi) (k,q)) := by
    change _ = (∏ v : ↥(insert i S),
        bernstein n ((tensorExtend (S:=S) i hi k q) v) (x v.1)) *
          f (partialPoint (n:=n) (insert i S)
            (tensorExtend (S:=S) i hi k q) x)
    rw [← tensorPart_cons_weight n S i hi k q x]
    -- associate the scalar with the old product
    rw [tensorPart_cons_point n S i hi k q x]
    ring
  -- reindex the sum on the right by the extension equivalence
  have hre :
      (∑ r : (↥(insert i S) → Fin (n+1)), V r) =
        ∑ kq : (Fin (n+1) × (↥S → Fin (n+1))),
             V ((tensorExtendEquiv (S:=S) (n:=n) i hi) kq) := by
    symm
    exact Equiv.sum_comp (tensorExtendEquiv (S:=S) (n:=n) i hi) V
  -- distribute the outer finite sums (sum over a product type)
  rw [show (∑ r : (↥(insert i S) → Fin (n+1)),
       (∏ v : ↥(insert i S), bernstein n (r v) (x v.1)) *
         f (partialPoint (n:=n) (insert i S) r x)) =
       ∑ r : (↥(insert i S) → Fin (n+1)), V r by rfl]
  rw [hre]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k hk
  -- multiplication distributes through the inner sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact hp k q


private lemma tensorIter_part {d : ℕ} (n : ℕ)
    (l : List (Fin d)) (hl : l.Nodup)
    (f : C(Fin d → I, ℝ)) (x : Fin d → I) :
    tensorIter n l f x = tensorPart n l.toFinset f x := by
  classical
  induction l generalizing x with
  | nil =>
      -- no coordinates have been sampled
      simp only [tensorIter, List.toFinset_nil]
      exact (tensorPart_empty n f x).symm
  | cons i l ih =>
      have htail : l.Nodup := (List.nodup_cons.mp hl).2
      have hiList : i ∉ l := (List.nodup_cons.mp hl).1
      have hi : i ∉ l.toFinset := by simpa using hiList
      -- expand the first coordinate and use the induction hypothesis for the tail
      simp only [tensorIter, tensorT, List.toFinset_cons]
      change (∑ k : Fin (n+1), bernstein n k (x i) *
          (tensorIter n l f) (Function.update x i (bernstein.z (n:=n) k))) =
        tensorPart n (insert i l.toFinset) f x
      have e : (∑ k : Fin (n+1), bernstein n k (x i) *
          (tensorIter n l f) (Function.update x i (bernstein.z (n:=n) k))) =
          ∑ k : Fin (n+1), bernstein n k (x i) *
            tensorPart n l.toFinset f
             (Function.update x i (bernstein.z (n:=n) k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih htail (Function.update x i (bernstein.z (n:=n) k))]
      rw [e]
      exact tensorPart_step n l.toFinset i hi f x


private noncomputable def tensorUnivEquiv {d : ℕ} {n : ℕ} :
    (Fin d → Fin (n+1)) ≃
      (↥(Finset.univ : Finset (Fin d)) → Fin (n+1)) where
  toFun q := fun u => q u.1
  invFun r := fun i => r ⟨i, Finset.mem_univ i⟩
  left_inv q := by funext i; rfl
  right_inv r := by funext u; congr 1

private lemma tensorPart_univ {d : ℕ} (n : ℕ)
    (f : C(Fin d → I, ℝ)) (x : Fin d → I) :
    tensorPart n (Finset.univ : Finset (Fin d)) f x =
      ∑ q : Fin d → Fin (n+1), tensorWeight n x q *
        f (fun i => bernstein.z (n:=n) (q i)) := by
  classical
  let V : (↥(Finset.univ : Finset (Fin d)) → Fin (n+1)) → ℝ :=
     fun r => (∏ u : ↥(Finset.univ : Finset (Fin d)),
          bernstein n (r u) (x u.1)) *
        f (partialPoint (n:=n) (Finset.univ : Finset (Fin d)) r x)
  have hr (q : Fin d → Fin (n+1)) :
      V ((tensorUnivEquiv (d:=d) (n:=n)) q) =
        tensorWeight n x q *
          f (fun i => bernstein.z (n:=n) (q i)) := by
    change (∏ u : ↥(Finset.univ : Finset (Fin d)),
        bernstein n (q u.1) (x u.1)) *
          f (partialPoint (n:=n) (Finset.univ : Finset (Fin d))
              (fun u => q u.1) x)
        = tensorWeight n x q * f (fun i => bernstein.z (n:=n) (q i))
    have hp : (∏ u : ↥(Finset.univ : Finset (Fin d)),
        bernstein n (q u.1) (x u.1)) = tensorWeight n x q := by
      unfold tensorWeight
      -- univ on the subtype is the attach of univ
      calc
        (∏ u : ↥(Finset.univ : Finset (Fin d)),
            bernstein n (q u.1) (x u.1)) =
            ∏ u ∈ (Finset.univ : Finset (Fin d)).attach,
               bernstein n (q u.1) (x u.1) := by rw [Finset.univ_eq_attach]
        _ = ∏ i ∈ (Finset.univ : Finset (Fin d)),
               bernstein n (q i) (x i) := by
             simpa using (Finset.prod_attach
               (Finset.univ : Finset (Fin d))
               (fun i : Fin d => bernstein n (q i) (x i)))
        _ = ∏ i : Fin d, bernstein n (q i) (x i) := by rfl
    have hpt : partialPoint (n:=n) (Finset.univ : Finset (Fin d))
              (fun u => q u.1) x =
             (fun i => bernstein.z (n:=n) (q i)) := by
      funext i
      simp [partialPoint]
    rw [hp, hpt]
  unfold tensorPart
  change (∑ r : (↥(Finset.univ : Finset (Fin d)) → Fin (n+1)),
       V r) = _
  calc
    (∑ r : (↥(Finset.univ : Finset (Fin d)) → Fin (n+1)), V r) =
        ∑ q : Fin d → Fin (n+1),
            V ((tensorUnivEquiv (d:=d) (n:=n)) q) := by
          symm
          exact Equiv.sum_comp (tensorUnivEquiv (d:=d) (n:=n)) V
    _ = _ := by
          apply Finset.sum_congr rfl
          intro q hq
          exact hr q

private lemma ofFn_full (d : ℕ) :
    (List.ofFn (fun i : Fin d => i)).toFinset = (Finset.univ : Finset (Fin d)) := by
  classical
  ext i
  simp

private lemma tensorIter_flat {d : ℕ} (n : ℕ)
    (f : C(Fin d → I, ℝ)) (x : Fin d → I) :
    tensorIter n (List.ofFn (fun i : Fin d => i)) f x =
      ∑ q : Fin d → Fin (n+1), tensorWeight n x q *
        f (fun i => bernstein.z (n:=n) (q i)) := by
  classical
  have hn : (List.ofFn (fun i : Fin d => i)).Nodup :=
     (List.nodup_ofFn.mpr fun _ _ h => h)
  rw [tensorIter_part n (List.ofFn (fun i : Fin d => i)) hn f x]
  rw [ofFn_full d]
  exact tensorPart_univ n f x


private noncomputable def cubeParam {d : ℕ}
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ cube d) : Fin d → I :=
  fun i => ⟨y i, hy i⟩

private lemma cubeParam_inv {d : ℕ}
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ cube d) :
    tensorToE (cubeParam y hy) = y := by
  -- the `WithLp` Euclidean representation has the same coordinates
  apply PiLp.ext
  intro i
  rfl

private lemma tensor_flat_iter {d : ℕ} (n : ℕ)
    (f : C(Fin d → I, ℝ)) (x : Fin d → I) :
 (∑ j ∈ Finset.Iic (fun _ : Fin d => n),
    ((multiChoose (fun _ : Fin d => n) j : ℝ) * f (tensorGrid n j)) *
      ker ((fun _ : Fin d => n) - j) (fun _ : Fin d => n) (tensorToE x)) =
    tensorIter n (List.ofFn (fun i : Fin d => i)) f x := by
  rw [tensor_flat n f x]
  exact (tensorIter_flat n f x).symm


private noncomputable def polyE {d : ℕ} (n : ℕ)
    (f : C(Fin d → I, ℝ)) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ j ∈ Finset.Iic (fun _ : Fin d => n),
    ((multiChoose (fun _ : Fin d => n) j : ℝ) * f (tensorGrid n j)) *
       ker ((fun _ : Fin d => n) - j) (fun _ : Fin d => n) y

private lemma polyE_cont {d : ℕ} (n : ℕ) (f : C(Fin d → I, ℝ)) :
    Continuous (polyE n f) := by
  classical
  unfold polyE
  apply continuous_finset_sum
  intro j hj
  exact (ker_cont ((fun _ : Fin d => n) - j) (fun _ : Fin d => n)).const_mul _

private lemma polyE_cube {d : ℕ} (n : ℕ) (f : C(Fin d → I, ℝ))
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ cube d) :
    polyE n f y =
      tensorIter n (List.ofFn (fun i : Fin d => i)) f (cubeParam y hy) := by
  classical
  unfold polyE
  have hh := tensor_flat_iter n f (cubeParam y hy)
  simpa [cubeParam_inv y hy] using hh

private lemma polyE_integral_tend {d : ℕ}
    (m : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m]
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : Continuous g)
    (f : C(Fin d → I, ℝ))
    (hgf : ∀ x : Fin d → I, f x = g (tensorToE x)) :
    Tendsto (fun t : ℕ => tensorIter t (List.ofFn (fun i : Fin d => i)) f)
       Filter.atTop (𝓝 f) →
    Tendsto (fun t : ℕ => ∫ y in cube d, polyE t f y ∂m)
       Filter.atTop (𝓝 (∫ y in cube d, g y ∂m)) := by
  classical
  intro hc
  let m' : Measure (EuclideanSpace ℝ (Fin d)) := m.restrict (cube d)
  letI : IsFiniteMeasure m' := by dsimp [m']; infer_instance
  have hi_g : Integrable g m' := by
    -- compact support isn't needed on a compact set
    exact ContinuousOn.integrableOn_compact (μ:=m) (cube_compact d) hg.continuousOn
  have hi_p (t : ℕ) : Integrable (polyE t f) m' := by
    exact ContinuousOn.integrableOn_compact (μ:=m) (cube_compact d)
        (polyE_cont t f).continuousOn
  have hn : Tendsto
      (fun t : ℕ => ‖tensorIter t (List.ofFn (fun i : Fin d => i)) f - f‖)
      Filter.atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hc
  -- reduce to the norms of the differences of the integrals
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hbound : ∀ t : ℕ,
      ‖(∫ y in cube d, polyE t f y ∂m) - (∫ y in cube d, g y ∂m)‖ ≤
        ‖tensorIter t (List.ofFn (fun i : Fin d => i)) f - f‖ *
          m'.real Set.univ := by
    intro t
    change ‖(∫ y, polyE t f y ∂m') - (∫ y, g y ∂m')‖ ≤ _
    rw [← MeasureTheory.integral_sub (hi_p t) hi_g]
    apply MeasureTheory.norm_integral_le_of_norm_le_const
    filter_upwards [ae_restrict_mem (μ:=m) (cube_meas d)] with y hy
    have hpoly := polyE_cube t f y hy
    rw [hpoly]
    have he : g y = f (cubeParam y hy) := by
      simpa [cubeParam_inv y hy] using (hgf (cubeParam y hy)).symm
    rw [he]
    change ‖(tensorIter t (List.ofFn (fun i : Fin d => i)) f - f)
          (cubeParam y hy)‖ ≤ _
    -- pointwise evaluation is bounded by the sup norm on the compact product
    exact ContinuousMap.norm_coe_le_norm
      (tensorIter t (List.ofFn (fun i : Fin d => i)) f - f) (cubeParam y hy)
  have hn' : Tendsto (fun t : ℕ =>
      ‖tensorIter t (List.ofFn (fun i : Fin d => i)) f - f‖ *
        m'.real Set.univ) Filter.atTop (𝓝 0) := by
    convert hn.mul_const (m'.real Set.univ) using 1
    simp
  exact squeeze_zero'
     (Filter.Eventually.of_forall (fun t => norm_nonneg _))
     (Filter.Eventually.of_forall hbound) hn'
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem hausdorff_absolute_continuity {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (hμ : μ ((cube d)ᶜ) = 0) :
    UniformlyAbsolutelyContinuous μ (volume.restrict (cube d)) ↔
      ∃ C : ℝ, ∀ k n : Fin d → ℕ, k ≤ n →
        diff (momentOf μ) k n ≤ C * diff (momentOf (volume.restrict (cube d))) k n :=
/-ResultProofBegin-/by
  classical
  constructor
  · rintro ⟨B, hle⟩
    refine ⟨(B : ℝ), ?_⟩
    intro k n hkn
    let lam : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (cube d)
    let eta : Measure (EuclideanSpace ℝ (Fin d)) := B • lam
    have hle' : μ.restrict (cube d) ≤ eta.restrict (cube d) := by
      exact Measure.restrict_mono (s := cube d) (s' := cube d) (by intro x hx; exact hx) hle
    have hres : eta.restrict (cube d) = eta := by
      dsimp [eta, lam]
      simp [Measure.restrict_smul, Measure.restrict_restrict (cube_meas d)]
    have hint_lam : Integrable (ker k n) lam := by
      exact ContinuousOn.integrableOn_compact (μ := volume) (cube_compact d)
        (ker_cont k n).continuousOn
    have hint_eta : Integrable (ker k n) (eta.restrict (cube d)) := by
      rw [hres]
      -- a finite scalar preserves integrability
      dsimp [eta]
      rw [ENNReal.smul_def]
      exact hint_lam.smul_measure ENNReal.coe_ne_top
    have hpos : 0 ≤ᵐ[eta.restrict (cube d)] ker k n := by
      filter_upwards [ae_restrict_mem (μ := eta) (cube_meas d)] with x hx
      exact ker_nonneg hkn hx
    have hineq :
        (∫ x, ker k n x ∂(μ.restrict (cube d))) ≤
          ∫ x, ker k n x ∂(eta.restrict (cube d)) :=
      integral_mono_measure hle' hpos hint_eta
    rw [hres] at hineq
    change diff (momentOf μ) k n ≤
      (B:ℝ) * diff (momentOf (volume.restrict (cube d))) k n
    rw [diff_moment_kernel (m:= μ) k n hkn,
        diff_moment_kernel (m:= volume.restrict (cube d)) k n hkn]
    -- turn the set integrals into integrals against the restricted measures
    change (∫ x, ker k n x ∂(μ.restrict (cube d))) ≤
      (B:ℝ) * (∫ x, ker k n x ∂(volume.restrict (cube d)).restrict (cube d))
    have hlamres : (lam.restrict (cube d)) = lam := by
      dsimp [lam]
      simp [Measure.restrict_restrict (cube_meas d)]
    have hlamres' : (volume.restrict (cube d)).restrict (cube d) = lam := by
      simpa [lam] using hlamres
    rw [hlamres']
    -- compute the integral in the scaled measure
    have hi' : (∫ x, ker k n x ∂eta) =
        (B:ℝ) * (∫ x, ker k n x ∂lam) := by
      dsimp [eta]
      rw [ENNReal.smul_def]
      rw [integral_smul_measure]
      simp
    rw [← hi']
    exact hineq
  · rintro ⟨A, hA⟩
    let R : ℝ := max A 0
    have hR : 0 ≤ R := le_max_right _ _
    let B : ℝ≥0 := ⟨R, hR⟩
    let lam : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (cube d)
    let eta : Measure (EuclideanSpace ℝ (Fin d)) := B • lam
    letI : IsFiniteMeasure lam :=
      ⟨by
        dsimp [lam]
        rw [Measure.restrict_apply MeasurableSet.univ]
        simpa using (cube_compact d).measure_lt_top (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))⟩
    letI : IsFiniteMeasure eta := by
      dsimp [eta]
      infer_instance
    refine ⟨B, ?_⟩
    change μ ≤ eta
    -- it remains to compare integrals of nonnegative continuous functions
    apply le_of_nonneg_cont μ eta
    intro f hf
    -- Both measures in these integrals are supported on the cube.  The
    -- substantive step is to approximate `f|cube` by its (multivariate)
    -- Bernstein polynomials; the estimates on the individual kernels below
    -- are the finite-dimensional input to that argument.
    have hker : ∀ (k n : Fin d → ℕ) (hk : k ≤ n),
        (∫ x in cube d, ker k n x ∂μ) ≤
          R * (∫ x in cube d, ker k n x ∂(volume.restrict (cube d))) := by
      intro k n hk
      have hd := hA k n hk
      rw [diff_moment_kernel (m:=μ) k n hk,
          diff_moment_kernel (m:= volume.restrict (cube d)) k n hk] at hd
      have hlpos : 0 ≤ ∫ x in cube d, ker k n x ∂(volume.restrict (cube d)) := by
        apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem (μ := volume.restrict (cube d))
          (cube_meas d)] with x hx
        exact ker_nonneg hk hx
      exact hd.trans (by
        have hh : A ≤ R := le_max_left _ _
        exact mul_le_mul_of_nonneg_right hh hlpos)
    have hlin : ∀ (u : Fin d → ℕ) (c : (Fin d → ℕ) → ℝ),
        (∀ j ∈ Finset.Iic u, 0 ≤ c j) →
        (∫ x in cube d, (∑ j ∈ Finset.Iic u,
              c j * ker (u-j) u x) ∂μ) ≤
          R * (∫ x in cube d, (∑ j ∈ Finset.Iic u,
              c j * ker (u-j) u x) ∂(volume.restrict (cube d))) := by
      intro u c hc
      have hv (j : Fin d → ℕ) : j ∈ Finset.Iic u → j ≤ u :=
        fun hj => (Finset.mem_Iic.mp hj)
      have hsub (j : Fin d → ℕ) (hj : j ∈ Finset.Iic u) : u-j ≤ u :=
        fun i => Nat.sub_le _ _
      have hm : (∫ x in cube d, (∑ j ∈ Finset.Iic u,
              c j * ker (u-j) u x) ∂μ) =
            ∑ j ∈ Finset.Iic u, c j * (∫ x in cube d, ker (u-j) u x ∂μ) := by
        calc
          _ = ∑ j ∈ Finset.Iic u, (∫ x in cube d, c j * ker (u-j) u x ∂μ) := by
            apply MeasureTheory.integral_finset_sum
            intro j hj
            have hjj : IntegrableOn (ker (u-j) u) (cube d) μ :=
              ContinuousOn.integrableOn_compact (μ:=μ) (cube_compact d)
                (ker_cont (u-j) u).continuousOn
            exact hjj.const_mul _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j hj
            change (∫ x, (c j) • ker (u-j) u x ∂(μ.restrict (cube d))) = _
            rw [integral_smul]
            rfl
      have hl : (∫ x in cube d, (∑ j ∈ Finset.Iic u,
              c j * ker (u-j) u x) ∂(volume.restrict (cube d))) =
            ∑ j ∈ Finset.Iic u, c j * (∫ x in cube d, ker (u-j) u x ∂(volume.restrict (cube d))) := by
        calc
          _ = ∑ j ∈ Finset.Iic u,
              (∫ x in cube d, c j * ker (u-j) u x ∂(volume.restrict (cube d))) := by
            apply MeasureTheory.integral_finset_sum
            intro j hj
            have hjj : IntegrableOn (ker (u-j) u) (cube d)
                (volume.restrict (cube d)) :=
              ContinuousOn.integrableOn_compact (μ:=volume.restrict (cube d))
                (cube_compact d) (ker_cont (u-j) u).continuousOn
            exact hjj.const_mul _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j hj
            change (∫ x, (c j) • ker (u-j) u x ∂((volume.restrict (cube d)).restrict (cube d))) = _
            rw [integral_smul]
            rfl
      rw [hm, hl, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hh := hker (u-j) u (hsub j hj)
      calc
        c j * (∫ x in cube d, ker (u-j) u x ∂μ) ≤
            c j * (R * (∫ x in cube d, ker (u-j) u x ∂(volume.restrict (cube d)))) :=
              mul_le_mul_of_nonneg_left hh (hc j hj)
        _ = R * (c j * (∫ x in cube d, ker (u-j) u x ∂(volume.restrict (cube d)))) := by ring
    have hset : (∫ x in cube d, f x ∂μ) ≤
        R * (∫ x in cube d, f x ∂(volume.restrict (cube d))) := by
      let F : C(Fin d → I, ℝ) :=
        ⟨fun x => f (tensorToE x), f.continuous.comp tensorToE_cont⟩
      -- The positive tensor Bernstein polynomials are exactly the combinations in `hlin`.
      have hbern (t : ℕ) :
        (∫ x in cube d, (∑ j ∈ Finset.Iic (fun _ : Fin d => t),
          ((multiChoose (fun _ : Fin d => t) j : ℝ) * F (tensorGrid t j)) *
             ker ((fun _ : Fin d => t) - j) (fun _ : Fin d => t) x) ∂μ) ≤
          R * (∫ x in cube d, (∑ j ∈ Finset.Iic (fun _ : Fin d => t),
          ((multiChoose (fun _ : Fin d => t) j : ℝ) * F (tensorGrid t j)) *
             ker ((fun _ : Fin d => t) - j) (fun _ : Fin d => t) x)
                 ∂(volume.restrict (cube d))) := by
        have hp := hlin (fun _ : Fin d => t)
          (fun j => (multiChoose (fun _ : Fin d => t) j : ℝ) * F (tensorGrid t j))
          (by
            intro j hj
            apply mul_nonneg
            · exact_mod_cast (Nat.zero_le (multiChoose (fun _ : Fin d => t) j))
            · exact hf (tensorToE (tensorGrid t j)))
        exact hp
      have hcoord : Tendsto
          (fun n : ℕ => tensorIter n (List.ofFn (fun i : Fin d => i)) F)
             Filter.atTop (𝓝 F) :=
        tensorIter_tend (List.ofFn (fun i : Fin d => i)) F
      -- Pass to the limit in the positive polynomial inequalities.
      have hF : ∀ x : Fin d → I, F x = f (tensorToE x) := by
        intro x; rfl
      have hmLim : Tendsto (fun t : ℕ => ∫ y in cube d, polyE t F y ∂μ)
          Filter.atTop (𝓝 (∫ y in cube d, f y ∂μ)) :=
        polyE_integral_tend μ (fun y => f y) f.continuous F hF hcoord
      have hlLim : Tendsto (fun t : ℕ =>
          ∫ y in cube d, polyE t F y ∂(volume.restrict (cube d)))
          Filter.atTop (𝓝 (∫ y in cube d, f y ∂(volume.restrict (cube d)))) := by
        -- the restricted volume is finite (and is our `lam` instance)
        change Tendsto (fun t : ℕ => ∫ y in cube d, polyE t F y ∂lam)
          Filter.atTop (𝓝 (∫ y in cube d, f y ∂lam))
        exact polyE_integral_tend lam (fun y => f y) f.continuous F hF hcoord
      apply le_of_tendsto_of_tendsto hmLim (Filter.Tendsto.const_mul R hlLim)
      filter_upwards [] with t
      -- this is the finite polynomial inequality above, merely written as `polyE`
      simpa [polyE] using hbern t
    have hmres : μ.restrict (cube d) = μ := by
      apply Measure.restrict_eq_self_of_ae_mem
      exact (mem_ae_iff.mpr hμ)
    have hlres : (volume.restrict (cube d)).restrict (cube d) = lam := by
      dsimp [lam]
      simp [Measure.restrict_restrict (cube_meas d)]
    change (∫ x, f x ∂μ) ≤ ∫ x, f x ∂eta
    have hetaInt : (∫ x, f x ∂eta) = R * (∫ x, f x ∂lam) := by
      dsimp [eta]
      rw [ENNReal.smul_def, integral_smul_measure]
      change (B:ℝ) * _ = _
      rfl
    rw [hetaInt]
    change (∫ x, f x ∂μ) ≤ R * (∫ x, f x ∂lam)
    rw [← hmres]
    change (∫ x in cube d, f x ∂μ) ≤ R * (∫ x, f x ∂lam)
    rw [← hlres]
    exact hset
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
