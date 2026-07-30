import ChallengeDeps

open LeanEval.Analysis.HausdorffAbsoluteContinuity
open MeasureTheory
open Filter
open scoped BigOperators NNReal Topology unitInterval

namespace Submission.Helpers

lemma sum_diff_monomial_one (x : ℝ) (k n : ℕ) (hkn : k ≤ n) :
    ∑ j ∈ Finset.Iic k,
        (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * x ^ (n - j) =
      x ^ (n - k) * (1 - x) ^ k := by
  rw [← Nat.range_succ_eq_Iic]
  calc
    ∑ j ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * x ^ (n - j) =
        x ^ (n - k) * ∑ j ∈ Finset.range (k + 1),
          (1 : ℝ) ^ j * (-x) ^ (k - j) * (k.choose j : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            have hjk : j ≤ k := by simpa using hj
            rw [show n - j = (n - k) + (k - j) by omega, pow_add]
            rw [neg_pow]
            ring
    _ = x ^ (n - k) * (1 + -x) ^ k := by rw [add_pow]
    _ = x ^ (n - k) * (1 - x) ^ k := by ring

/-- The product kernel represented by an iterated moment difference. -/
def diffKernel {d : ℕ} (k n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, (x i) ^ (n i - k i) * (1 - x i) ^ (k i)

lemma sum_diff_monomial {d : ℕ} (x : EuclideanSpace ℝ (Fin d))
    (k n : Fin d → ℕ) (hkn : k ≤ n) :
    ∑ j ∈ Finset.Iic k,
        (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * monomial (n - j) x =
      diffKernel k n x := by
  classical
  have hIic : Finset.Iic k = Fintype.piFinset (fun i => Finset.Iic (k i)) := by
    ext j
    simp [Pi.le_def]
  rw [hIic]
  calc
    ∑ j ∈ Fintype.piFinset (fun i => Finset.Iic (k i)),
        (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * monomial (n - j) x =
        ∑ j ∈ Fintype.piFinset (fun i => Finset.Iic (k i)),
          ∏ i, ((-1 : ℝ) ^ (k i - j i) * (k i).choose (j i) * x i ^ (n i - j i)) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [multiChoose, monomial, Pi.sub_apply, Nat.cast_prod]
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
              Finset.prod_pow_eq_pow_sum]
    _ = ∏ i, ∑ j ∈ Finset.Iic (k i),
          ((-1 : ℝ) ^ (k i - j) * (k i).choose j * x i ^ (n i - j)) := by
            rw [Finset.prod_univ_sum]
    _ = diffKernel k n x := by
      unfold diffKernel
      apply Finset.prod_congr rfl
      intro i hi
      exact sum_diff_monomial_one (x i) (k i) (n i) (hkn i)

lemma isCompact_cube (d : ℕ) : IsCompact (cube d) := by
  have hc : cube d = (EuclideanSpace.equiv (Fin d) ℝ) ⁻¹'
      Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp [cube, Pi.le_def, forall_and]
  rw [hc]
  exact (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph.isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

lemma measurableSet_cube (d : ℕ) : MeasurableSet (cube d) :=
  (isCompact_cube d).measurableSet

lemma continuous_monomial {d : ℕ} (n : Fin d → ℕ) : Continuous (monomial n) := by
  unfold monomial
  fun_prop

lemma continuous_diffKernel {d : ℕ} (k n : Fin d → ℕ) : Continuous (diffKernel k n) := by
  unfold diffKernel
  fun_prop

lemma diffKernel_nonneg_on_cube {d : ℕ} (k n : Fin d → ℕ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cube d) : 0 ≤ diffKernel k n x := by
  unfold diffKernel
  exact Finset.prod_nonneg fun i _ =>
    mul_nonneg (pow_nonneg (hx i).1 _) (pow_nonneg (sub_nonneg.mpr (hx i).2) _)

lemma integrableOn_monomial {d : ℕ} (m : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure m] (n : Fin d → ℕ) : IntegrableOn (monomial n) (cube d) m :=
  (continuous_monomial n).continuousOn.integrableOn_compact (isCompact_cube d)

lemma diff_momentOf_eq_integral_diffKernel {d : ℕ}
    (m : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m]
    (k n : Fin d → ℕ) (hkn : k ≤ n) :
    diff (momentOf m) k n = ∫ x in cube d, diffKernel k n x ∂m := by
  classical
  unfold diff
  calc
    ∑ j ∈ Finset.Iic k,
        (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * momentOf m (n - j) =
        ∑ j ∈ Finset.Iic k, ∫ x in cube d,
          ((-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ)) *
            monomial (n - j) x ∂m := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [momentOf, integral_const_mul]
    _ = ∫ x in cube d, ∑ j ∈ Finset.Iic k,
          ((-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ)) *
            monomial (n - j) x ∂m := by
      rw [integral_finsetSum]
      intro j hj
      exact (integrableOn_monomial m (n - j)).const_mul _
    _ = ∫ x in cube d, diffKernel k n x ∂m := by
      apply integral_congr_ae
      filter_upwards with x
      simpa [mul_assoc] using sum_diff_monomial x k n hkn

/-! ## Positive Bernstein approximation on a finite cube -/

/-- A coordinate cube, expressed as a product of copies of `[0,1]`. -/
abbrev UnitCube (ι : Type*) := ι → Set.Icc (0 : ℝ) 1

/-- A product of the unnormalised Bernstein basis functions. -/
def bernsteinBasis {ι : Type*} [Fintype ι] (a b : ι → ℕ) : C(UnitCube ι, ℝ) :=
  ⟨fun x => ∏ i, (x i : ℝ) ^ (a i) * (1 - (x i : ℝ)) ^ (b i), by fun_prop⟩

/-- The cone of finite nonnegative combinations of product Bernstein basis functions. -/
noncomputable def bernsteinCone (ι : Type*) [Fintype ι] : PointedCone ℝ C(UnitCube ι, ℝ) :=
  PointedCone.hull ℝ (Set.range fun p : (ι → ℕ) × (ι → ℕ) =>
    bernsteinBasis p.1 p.2)

/-- Splitting off the first coordinate of a finite cube. -/
def unitCubeSuccHomeomorph (d : ℕ) :
    UnitCube (Fin (d + 1)) ≃ₜ Set.Icc (0 : ℝ) 1 × UnitCube (Fin d) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x i := Fin.cases x.1 x.2 i
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd

/-- Multiply a function on the tail cube by a one-variable Bernstein polynomial in the head. -/
noncomputable def bernsteinLift (d n : ℕ) (j : Fin (n + 1))
    (g : C(UnitCube (Fin d), ℝ)) :
    C(UnitCube (Fin (d + 1)), ℝ) :=
  ⟨fun x => bernstein n j (x 0) * g (fun i => x i.succ), by fun_prop⟩

lemma continuous_bernsteinLift (d n : ℕ) (j : Fin (n + 1)) :
    Continuous (bernsteinLift d n j) := by
  let head : C(UnitCube (Fin (d + 1)), Set.Icc (0 : ℝ) 1) :=
    ⟨fun x => x 0, by fun_prop⟩
  let tail : C(UnitCube (Fin (d + 1)), UnitCube (Fin d)) :=
    ⟨fun x i => x i.succ, by fun_prop⟩
  change Continuous (fun g : C(UnitCube (Fin d), ℝ) =>
    (bernstein n j).comp head * g.comp tail)
  exact continuous_const.mul (ContinuousMap.continuous_precomp tail)

/-- `bernsteinLift` is linear for nonnegative scalars. -/
noncomputable def bernsteinLiftLinear (d n : ℕ) (j : Fin (n + 1)) :
    C(UnitCube (Fin d), ℝ) →ₗ[ℝ≥0] C(UnitCube (Fin (d + 1)), ℝ) where
  toFun := bernsteinLift d n j
  map_add' f g := by
    ext x
    simp [bernsteinLift, mul_add]
  map_smul' c f := by
    ext x
    change bernstein n (j : ℕ) (x 0) * ((c : ℝ) * f (fun i => x i.succ)) =
      (c : ℝ) * (bernstein n (j : ℕ) (x 0) * f (fun i => x i.succ))
    ring

lemma bernsteinLift_mapsTo_cone (d n : ℕ) (j : Fin (n + 1)) :
    Set.MapsTo (bernsteinLift d n j) (bernsteinCone (Fin d))
      (bernsteinCone (Fin (d + 1))) := by
  intro g hg
  change g ∈ Submodule.span ℝ≥0
      (Set.range fun p : (Fin d → ℕ) × (Fin d → ℕ) => bernsteinBasis p.1 p.2) at hg
  have hle : Submodule.span ℝ≥0
      (Set.range fun p : (Fin d → ℕ) × (Fin d → ℕ) => bernsteinBasis p.1 p.2) ≤
      Submodule.comap (bernsteinLiftLinear d n j) (bernsteinCone (Fin (d + 1))) := by
    apply Submodule.span_le.2
    rintro _ ⟨⟨a, b⟩, rfl⟩
    let a' : Fin (d + 1) → ℕ := Fin.cases (j : ℕ) a
    let b' : Fin (d + 1) → ℕ := Fin.cases (n - (j : ℕ)) b
    have heq : bernsteinLift d n j (bernsteinBasis a b) =
        (n.choose (j : ℕ) : ℝ≥0) • bernsteinBasis a' b' := by
      ext x
      simp [bernsteinLift, bernsteinBasis, bernstein_apply, a', b', Fin.prod_univ_succ,
        NNReal.smul_def, smul_eq_mul]
      ring
    change bernsteinLift d n j (bernsteinBasis a b) ∈ bernsteinCone (Fin (d + 1))
    rw [heq]
    exact Submodule.smul_mem (bernsteinCone (Fin (d + 1))) _
      (PointedCone.subset_hull ⟨(a', b'), rfl⟩)
  exact hle hg

lemma bernsteinLift_mem_closure (d n : ℕ) (j : Fin (n + 1))
    {g : C(UnitCube (Fin d), ℝ)} (hg : g ∈ (bernsteinCone (Fin d)).closure) :
    bernsteinLift d n j g ∈ (bernsteinCone (Fin (d + 1))).closure :=
  map_mem_closure (continuous_bernsteinLift d n j) hg (bernsteinLift_mapsTo_cone d n j)

/-- The multivariate Bernstein approximation obtained by adding one coordinate. -/
noncomputable def bernsteinSuccApprox (d n : ℕ)
    (f : C(UnitCube (Fin (d + 1)), ℝ)) : C(UnitCube (Fin (d + 1)), ℝ) :=
  let fp : C(Set.Icc (0 : ℝ) 1 × UnitCube (Fin d), ℝ) :=
    f.comp (unitCubeSuccHomeomorph d).symm
  let fc : C(Set.Icc (0 : ℝ) 1, C(UnitCube (Fin d), ℝ)) := fp.curry
  ∑ j : Fin (n + 1), bernsteinLift d n j (fc (bernstein.z j))

set_option maxHeartbeats 800000 in
lemma bernsteinSuccApprox_tendsto (d : ℕ) (f : C(UnitCube (Fin (d + 1)), ℝ)) :
    Filter.Tendsto (fun n => bernsteinSuccApprox d n f) Filter.atTop (𝓝 f) := by
  let H : C(UnitCube (Fin (d + 1)), Set.Icc (0 : ℝ) 1 × UnitCube (Fin d)) :=
    ⟨unitCubeSuccHomeomorph d, (unitCubeSuccHomeomorph d).continuous⟩
  let Hinv : C(Set.Icc (0 : ℝ) 1 × UnitCube (Fin d), UnitCube (Fin (d + 1))) :=
    ⟨(unitCubeSuccHomeomorph d).symm, (unitCubeSuccHomeomorph d).symm.continuous⟩
  let fp : C(Set.Icc (0 : ℝ) 1 × UnitCube (Fin d), ℝ) :=
    f.comp Hinv
  let fc : C(Set.Icc (0 : ℝ) 1, C(UnitCube (Fin d), ℝ)) := fp.curry
  have hbern := bernsteinApproximation_uniform fc
  have huncurry : Filter.Tendsto
      (fun n => (bernsteinApproximation n fc).uncurry) Filter.atTop (𝓝 fc.uncurry) :=
    Continuous.tendsto (ContinuousMap.continuous_uncurry) _ |>.comp hbern
  have hcomp : Filter.Tendsto
      (fun n => (bernsteinApproximation n fc).uncurry.comp H)
      Filter.atTop (𝓝 (fc.uncurry.comp H)) :=
    Continuous.tendsto (ContinuousMap.continuous_precomp H) _ |>.comp huncurry
  have happ (n : ℕ) : bernsteinSuccApprox d n f =
      (bernsteinApproximation n fc).uncurry.comp H := by
    ext x
    simp [bernsteinSuccApprox, fp, fc, H, Hinv, bernsteinApproximation.apply,
      bernsteinLift, unitCubeSuccHomeomorph]
  have hlimit : fc.uncurry.comp H = f := by
    ext x
    change f ((unitCubeSuccHomeomorph d).symm ((unitCubeSuccHomeomorph d) x)) = f x
    rw [(unitCubeSuccHomeomorph d).symm_apply_apply]
  have hseq : Filter.Tendsto (fun n => bernsteinSuccApprox d n f) Filter.atTop
      (𝓝 (fc.uncurry.comp H)) :=
    hcomp.congr' (Filter.Eventually.of_forall fun n => (happ n).symm)
  simpa only [hlimit] using hseq

theorem nonneg_mem_bernsteinCone_closure (d : ℕ)
    (f : C(UnitCube (Fin d), ℝ)) (hf : 0 ≤ f) :
    f ∈ (bernsteinCone (Fin d)).closure := by
  induction d with
  | zero =>
      let x0 : UnitCube (Fin 0) := fun i => Fin.elim0 i
      have hc : 0 ≤ f x0 := hf x0
      have hb : bernsteinBasis (ι := Fin 0) 0 0 ∈ bernsteinCone (Fin 0) :=
        PointedCone.subset_hull ⟨(0, 0), rfl⟩
      have hsmul : (⟨f x0, hc⟩ : ℝ≥0) • bernsteinBasis (ι := Fin 0) 0 0 ∈
          bernsteinCone (Fin 0) :=
        Submodule.smul_mem (bernsteinCone (Fin 0)) ⟨f x0, hc⟩ hb
      apply subset_closure
      have heq : f = (⟨f x0, hc⟩ : ℝ≥0) • bernsteinBasis (ι := Fin 0) 0 0 := by
        ext x
        have hx : x = x0 := Subsingleton.elim _ _
        subst x
        simp [bernsteinBasis]
      rw [heq]
      exact hsmul
  | succ d ih =>
      have hcoeff (n : ℕ) (j : Fin (n + 1)) :
          let fp : C(Set.Icc (0 : ℝ) 1 × UnitCube (Fin d), ℝ) :=
            f.comp (unitCubeSuccHomeomorph d).symm
          let fc : C(Set.Icc (0 : ℝ) 1, C(UnitCube (Fin d), ℝ)) := fp.curry
          fc (bernstein.z j) ∈ (bernsteinCone (Fin d)).closure := by
        dsimp
        apply ih
        intro x
        exact hf ((unitCubeSuccHomeomorph d).symm (bernstein.z j, x))
      have happ (n : ℕ) : bernsteinSuccApprox d n f ∈
          (bernsteinCone (Fin (d + 1))).closure := by
        unfold bernsteinSuccApprox
        exact Submodule.sum_mem _ fun j _ => bernsteinLift_mem_closure d n j (hcoeff n j)
      exact isClosed_closure.mem_of_tendsto (bernsteinSuccApprox_tendsto d f)
        (Filter.Eventually.of_forall happ)

/-! ## Transporting measures to the coordinate cube -/

/-- Coordinatewise projection of Euclidean space onto `[0,1]`. -/
noncomputable def toUnitCube (d : ℕ) : C(EuclideanSpace ℝ (Fin d), UnitCube (Fin d)) :=
  ⟨fun x i => Set.projIcc 0 1 (by norm_num) (x i), by fun_prop⟩

/-- The natural inclusion of the coordinate cube into Euclidean space. -/
def fromUnitCube (d : ℕ) : C(UnitCube (Fin d), EuclideanSpace ℝ (Fin d)) :=
  ⟨fun x => WithLp.toLp 2 fun i => (x i : ℝ), by fun_prop⟩

/-- Push a measure onto the coordinate cube. -/
noncomputable def cubeMeasure {d : ℕ} (m : Measure (EuclideanSpace ℝ (Fin d))) :
    Measure (UnitCube (Fin d)) :=
  m.map (toUnitCube d)

noncomputable instance isFiniteMeasure_cubeMeasure {d : ℕ}
    (m : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m] :
    IsFiniteMeasure (cubeMeasure m) :=
  Measure.isFiniteMeasure_map m (toUnitCube d)

lemma integrable_cubeMeasure {d : ℕ} (m : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure m] (f : C(UnitCube (Fin d), ℝ)) : Integrable f (cubeMeasure m) := by
  simpa using f.continuous.continuousOn.integrableOn_compact
    (μ := cubeMeasure m) isCompact_univ

/-- Integration on the pushed-forward cube measure, as a continuous linear functional. -/
noncomputable def integralUnitCubeCLM {d : ℕ}
    (m : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m] :
    C(UnitCube (Fin d), ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂cubeMeasure m
      map_add' := fun f g => integral_add (integrable_cubeMeasure m f)
        (integrable_cubeMeasure m g)
      map_smul' := fun c f => integral_smul c f }
    ((cubeMeasure m).real Set.univ) fun f => by
      simpa [mul_comm] using norm_integral_le_of_norm_le_const
        (μ := cubeMeasure m) (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)

@[simp]
lemma integralUnitCubeCLM_apply {d : ℕ}
    (m : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m]
    (f : C(UnitCube (Fin d), ℝ)) :
    integralUnitCubeCLM m f = ∫ x, f x ∂cubeMeasure m := rfl

lemma integralUnitCubeCLM_bernsteinBasis {d : ℕ}
    (m : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m]
    (hm : ∀ᵐ x ∂m, x ∈ cube d) (a b : Fin d → ℕ) :
    integralUnitCubeCLM m (bernsteinBasis a b) = diff (momentOf m) b (a + b) := by
  have hba : b ≤ a + b := fun i => by
    simp only [Pi.add_apply]
    omega
  calc
    integralUnitCubeCLM m (bernsteinBasis a b) =
        ∫ x, bernsteinBasis a b (toUnitCube d x) ∂m := by
      rw [integralUnitCubeCLM_apply, cubeMeasure,
        integral_map_of_stronglyMeasurable (toUnitCube d).continuous.measurable
          (bernsteinBasis a b).continuous.stronglyMeasurable]
    _ = ∫ x in cube d, bernsteinBasis a b (toUnitCube d x) ∂m := by
      rw [Measure.restrict_eq_self_of_ae_mem hm]
    _ = ∫ x in cube d, diffKernel b (a + b) x ∂m := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_cube d)] with x hx
      unfold bernsteinBasis diffKernel
      simp only [ContinuousMap.coe_mk, Pi.add_apply]
      apply Finset.prod_congr rfl
      intro i hi
      have hproj : ((toUnitCube d x i : Set.Icc (0 : ℝ) 1) : ℝ) = x i := by
        simp [toUnitCube, Set.projIcc_of_mem (by norm_num) (hx i)]
      rw [hproj]
      congr 2
      omega
    _ = diff (momentOf m) b (a + b) :=
      (diff_momentOf_eq_integral_diffKernel m b (a + b) hba).symm

/-! ## Moment domination gives domination of positive continuous functions -/

noncomputable def dominationCone {d : ℕ}
    (m v : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m] [IsFiniteMeasure v]
    (D : ℝ) : PointedCone ℝ C(UnitCube (Fin d), ℝ) where
  carrier := {f | integralUnitCubeCLM m f ≤ D * integralUnitCubeCLM v f}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change integralUnitCubeCLM m f ≤ D * integralUnitCubeCLM v f at hf
    change integralUnitCubeCLM m g ≤ D * integralUnitCubeCLM v g at hg
    change integralUnitCubeCLM m (f + g) ≤ D * integralUnitCubeCLM v (f + g)
    rw [map_add, map_add]
    linarith
  smul_mem' := by
    rintro ⟨c, hc⟩ f hf
    change integralUnitCubeCLM m f ≤ D * integralUnitCubeCLM v f at hf
    change integralUnitCubeCLM m (c • f) ≤ D * integralUnitCubeCLM v (c • f)
    simp only [map_smul, smul_eq_mul]
    nlinarith

lemma isClosed_dominationCone {d : ℕ}
    (m v : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m] [IsFiniteMeasure v]
    (D : ℝ) : IsClosed (dominationCone m v D : Set C(UnitCube (Fin d), ℝ)) := by
  exact isClosed_le (integralUnitCubeCLM m).continuous
    (continuous_const.mul (integralUnitCubeCLM v).continuous)

lemma integralUnitCubeCLM_le_of_diff_le {d : ℕ}
    (m v : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m] [IsFiniteMeasure v]
    (hm : ∀ᵐ x ∂m, x ∈ cube d) (hv : ∀ᵐ x ∂v, x ∈ cube d)
    (D : ℝ)
    (h : ∀ k n : Fin d → ℕ, k ≤ n →
      diff (momentOf m) k n ≤ D * diff (momentOf v) k n)
    (f : C(UnitCube (Fin d), ℝ)) (hf : 0 ≤ f) :
    integralUnitCubeCLM m f ≤ D * integralUnitCubeCLM v f := by
  have hcone : bernsteinCone (Fin d) ≤ dominationCone m v D := by
    apply Submodule.span_le.2
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change integralUnitCubeCLM m (bernsteinBasis a b) ≤
      D * integralUnitCubeCLM v (bernsteinBasis a b)
    rw [integralUnitCubeCLM_bernsteinBasis m hm,
      integralUnitCubeCLM_bernsteinBasis v hv]
    have hba : b ≤ a + b := fun i => by
      simp only [Pi.add_apply]
      omega
    exact h b (a + b) hba
  have hfcl := nonneg_mem_bernsteinCone_closure d f hf
  change f ∈ closure (bernsteinCone (Fin d) : Set C(UnitCube (Fin d), ℝ)) at hfcl
  exact closure_minimal hcone (isClosed_dominationCone m v D) hfcl

/-! ## Recovering measure domination from positive continuous test functions -/

lemma measure_le_of_integral_le_nonneg_continuous
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (m v : Measure X) [IsFiniteMeasure m] [IsFiniteMeasure v]
    (h : ∀ f : C(X, ℝ), 0 ≤ f → ∫ x, f x ∂m ≤ ∫ x, f x ∂v) :
    m ≤ v := by
  have hcompact ⦃K : Set X⦄ (hK : IsCompact K) : m K ≤ v K := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hvKε => ?_
    have hvK : v K ≠ ⊤ := (hK.measure_lt_top (μ := v)).ne
    have hmK : m K ≠ ⊤ := (hK.measure_lt_top (μ := m)).ne
    obtain ⟨V, hKV, hVopen, hVle⟩ : ∃ V ⊇ K, IsOpen V ∧ v V ≤ v K + ε :=
      Set.exists_isOpen_le_add K v (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
    suffices m.real K ≤ v.real K + ε by
      rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
      all_goals finiteness
    have hVtop : v V < ⊤ := hVle.trans_lt (by finiteness)
    obtain ⟨f, hfK, _, hfV, hf01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hVopen hKV
    have hfm : Integrable f m := by
      simpa using f.continuous.continuousOn.integrableOn_compact
        (μ := m) isCompact_univ
    have hfv : Integrable f v := by
      simpa using f.continuous.continuousOn.integrableOn_compact
        (μ := v) isCompact_univ
    have hf_le_V (x : X) : f x ≤ V.indicator 1 x := by
      by_cases hx : x ∈ tsupport f
      · simp [(hfV hx), (hf01 x).2]
      · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
    have hK_le_f (x : X) : K.indicator 1 x ≤ f x := by
      by_cases hx : x ∈ K
      · simp [hx, hfK hx]
      · simp [hx, (hf01 x).1]
    calc
      m.real K = ∫ x, K.indicator 1 x ∂m :=
        (integral_indicator_one hK.measurableSet).symm
      _ ≤ ∫ x, f x ∂m := by
        refine integral_mono ?_ hfm hK_le_f
        exact (continuousOn_const.integrableOn_compact hK).integrable_indicator
          hK.measurableSet
      _ ≤ ∫ x, f x ∂v :=
        h f fun x => (hf01 x).1
      _ ≤ ∫ x, V.indicator 1 x ∂v := by
        refine integral_mono hfv ?_ hf_le_V
        exact IntegrableOn.integrable_indicator integrableOn_const hVopen.measurableSet
      _ ≤ (v K).toReal + (ε : ℝ) := by
        rwa [integral_indicator_one hVopen.measurableSet, measureReal_def,
          ← ENNReal.coe_toReal, ← ENNReal.toReal_add, ENNReal.toReal_le_toReal]
        all_goals finiteness
  rw [Measure.le_iff]
  intro A hA
  rw [hA.measure_eq_iSup_isCompact m]
  exact iSup_le fun K => iSup_le fun hKA => iSup_le fun hK =>
    (hcompact hK).trans (measure_mono hKA)

lemma ae_mem_cube_of_compl_measure_zero {d : ℕ}
    {m : Measure (EuclideanSpace ℝ (Fin d))} (hm : m ((cube d)ᶜ) = 0) :
    ∀ᵐ x ∂m, x ∈ cube d := by
  rw [ae_iff]
  change m ((cube d)ᶜ) = 0
  exact hm

lemma fromUnitCube_toUnitCube {d : ℕ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ cube d) : fromUnitCube d (toUnitCube d x) = x := by
  ext i
  simp [fromUnitCube, toUnitCube, Set.projIcc_of_mem (by norm_num) (hx i)]

lemma map_cubeMeasure_fromUnitCube {d : ℕ}
    (m : Measure (EuclideanSpace ℝ (Fin d)))
    (hm : ∀ᵐ x ∂m, x ∈ cube d) :
    (cubeMeasure m).map (fromUnitCube d) = m := by
  rw [cubeMeasure, Measure.map_map (fromUnitCube d).continuous.measurable
    (toUnitCube d).continuous.measurable]
  calc
    m.map (fromUnitCube d ∘ toUnitCube d) = m.map id := by
      apply Measure.map_congr
      filter_upwards [hm] with x hx
      exact fromUnitCube_toUnitCube hx
    _ = m := Measure.map_id

noncomputable instance isFiniteMeasure_volume_restrict_cube (d : ℕ) :
    IsFiniteMeasure (volume.restrict (cube d)) where
  measure_univ_lt_top := by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_cube d).measure_lt_top

lemma measure_le_nnreal_smul_of_diff_le {d : ℕ}
    (m v : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure m] [IsFiniteMeasure v]
    (hm : ∀ᵐ x ∂m, x ∈ cube d) (hv : ∀ᵐ x ∂v, x ∈ cube d)
    (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ k n : Fin d → ℕ, k ≤ n →
      diff (momentOf m) k n ≤ D * diff (momentOf v) k n) :
    ∃ c : ℝ≥0, m ≤ c • v := by
  let c : ℝ≥0 := ⟨D, hD⟩
  have hpush : cubeMeasure m ≤ c • cubeMeasure v := by
    apply measure_le_of_integral_le_nonneg_continuous
    intro f hf
    have htest := integralUnitCubeCLM_le_of_diff_le m v hm hv D h f hf
    rw [integral_smul_nnreal_measure]
    change (∫ x, f x ∂cubeMeasure m) ≤ (c : ℝ) * ∫ x, f x ∂cubeMeasure v
    change (∫ x, f x ∂cubeMeasure m) ≤ D * ∫ x, f x ∂cubeMeasure v
    simpa only [integralUnitCubeCLM_apply] using htest
  refine ⟨c, ?_⟩
  calc
    m = (cubeMeasure m).map (fromUnitCube d) :=
      (map_cubeMeasure_fromUnitCube m hm).symm
    _ ≤ (c • cubeMeasure v).map (fromUnitCube d) :=
      Measure.map_mono hpush (fromUnitCube d).continuous.measurable
    _ = c • (cubeMeasure v).map (fromUnitCube d) :=
      Measure.map_smul c (cubeMeasure v) (fromUnitCube d)
    _ = c • v := by rw [map_cubeMeasure_fromUnitCube v hv]

lemma diff_volume_restrict_cube_nonneg {d : ℕ}
    (k n : Fin d → ℕ) (hkn : k ≤ n) :
    0 ≤ diff (momentOf (volume.restrict (cube d))) k n := by
  let v : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (cube d)
  have hv : ∀ᵐ x ∂v, x ∈ cube d :=
    ae_restrict_mem (measurableSet_cube d)
  rw [diff_momentOf_eq_integral_diffKernel v k n hkn,
    Measure.restrict_eq_self_of_ae_mem hv]
  exact integral_nonneg_of_ae (hv.mono fun x hx => diffKernel_nonneg_on_cube k n hx)

theorem hausdorff_absolute_continuity_aux {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (hμ : μ ((cube d)ᶜ) = 0) :
    UniformlyAbsolutelyContinuous μ (volume.restrict (cube d)) ↔
      ∃ C : ℝ, ∀ k n : Fin d → ℕ, k ≤ n →
        diff (momentOf μ) k n ≤
          C * diff (momentOf (volume.restrict (cube d))) k n := by
  let v : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (cube d)
  have hm : ∀ᵐ x ∂μ, x ∈ cube d := ae_mem_cube_of_compl_measure_zero hμ
  have hv : ∀ᵐ x ∂v, x ∈ cube d :=
    ae_restrict_mem (measurableSet_cube d)
  constructor
  · rintro ⟨c, hcv⟩
    refine ⟨(c : ℝ), fun k n hkn => ?_⟩
    rw [diff_momentOf_eq_integral_diffKernel μ k n hkn,
      diff_momentOf_eq_integral_diffKernel v k n hkn]
    have hfv : Integrable (diffKernel k n) v :=
      (continuous_diffKernel k n).continuousOn.integrableOn_compact
        (μ := volume) (isCompact_cube d)
    have hfcv : Integrable (diffKernel k n) (c • v) :=
      hfv.smul_measure_nnreal
    have hnonnegv : 0 ≤ᵐ[v] diffKernel k n :=
      hv.mono fun x hx => diffKernel_nonneg_on_cube k n hx
    calc
      ∫ x in cube d, diffKernel k n x ∂μ ≤ ∫ x, diffKernel k n x ∂(c • v) :=
        integral_mono_measure
          ((Measure.restrict_le_self : μ.restrict (cube d) ≤ μ).trans hcv)
          (Measure.ae_smul_measure hnonnegv c) hfcv
      _ = (c : ℝ) * ∫ x, diffKernel k n x ∂v := by
        rw [integral_smul_nnreal_measure]
        rfl
      _ = (c : ℝ) * ∫ x in cube d, diffKernel k n x ∂v := by
        rw [Measure.restrict_eq_self_of_ae_mem hv]
  · rintro ⟨C, hC⟩
    let D : ℝ := max C 0
    have hD : 0 ≤ D := le_max_right C 0
    have hdom : ∀ k n : Fin d → ℕ, k ≤ n →
        diff (momentOf μ) k n ≤ D * diff (momentOf v) k n := by
      intro k n hkn
      exact (hC k n hkn).trans (mul_le_mul_of_nonneg_right
        (le_max_left C 0) (by
          change 0 ≤ diff (momentOf (volume.restrict (cube d))) k n
          exact diff_volume_restrict_cube_nonneg k n hkn))
    change ∃ c : ℝ≥0, μ ≤ c • v
    exact measure_le_nnreal_smul_of_diff_le μ v hm hv D hD hdom

end Submission.Helpers
