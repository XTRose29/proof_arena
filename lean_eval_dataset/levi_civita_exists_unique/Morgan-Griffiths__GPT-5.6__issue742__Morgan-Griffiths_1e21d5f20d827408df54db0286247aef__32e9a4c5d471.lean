import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/Koszul.lean
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative
noncomputable section
namespace LeviSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [CompleteSpace E]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
 [RiemannianBundle (fun x : M => TangentSpace I x)]
 [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]

def K (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv I (fun y : M => inner ℝ (Y y) (Z y)) x (X x)
  + mvfderiv I (fun y : M => inner ℝ (X y) (Z y)) x (Y x)
  - mvfderiv I (fun y : M => inner ℝ (X y) (Y y)) x (Z x)
  - inner ℝ (mlieBracket I Y Z x) (X x)
  - inner ℝ (mlieBracket I X Z x) (Y x)
  + inner ℝ (mlieBracket I X Y x) (Z x)

lemma K_tensor_X (x : M) (Y Z : Π x : M, TangentSpace I x)
 (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
 TensorialAt I E (fun X => K X Y Z x) x := by
  constructor
  · intro f X hf hX
    have hXZ : MDiffAt (fun y : M => inner ℝ (X y) (Z y)) x :=
      MDifferentiableAt.inner_bundle (IB:=I) hX hZ
    have hXY : MDiffAt (fun y : M => inner ℝ (X y) (Y y)) x :=
      MDifferentiableAt.inner_bundle (IB:=I) hX hY
    have d1 := mvfderiv_fun_mul hf hXZ
    have d2 := mvfderiv_fun_mul hf hXY
    dsimp [K]
    simp [inner_smul_left]
    rw [d1, d2]
    simp [hf, hX, hY, hZ, VectorField.mlieBracket_smul_left,
      VectorField.mlieBracket_smul_right, inner_add_left, inner_smul_left, inner_smul_right, real_inner_comm]
    ring
  · intro X X' hX hX'
    have hXZ : MDiffAt (fun y : M => inner ℝ (X y) (Z y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hX hZ)
    have hXZ' : MDiffAt (fun y : M => inner ℝ (X' y) (Z y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hX' hZ)
    have hXY : MDiffAt (fun y : M => inner ℝ (X y) (Y y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hX hY)
    have hXY' : MDiffAt (fun y : M => inner ℝ (X' y) (Y y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hX' hY)
    have d1 := mvfderiv_fun_add hXZ hXZ'
    have d2 := mvfderiv_fun_add hXY hXY'
    dsimp [K]
    simp only [inner_add_left]
    rw [d1, d2]
    simp [hX, hX', hY, hZ, VectorField.mlieBracket_add_left,
      VectorField.mlieBracket_add_right, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
    ring

lemma K_tensor_Z (x : M) (X Y : Π x : M, TangentSpace I x)
 (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
 TensorialAt I E (fun Z => K X Y Z x) x := by
  constructor
  · intro f Z hf hZ
    have hYZ : MDiffAt (fun y : M => inner ℝ (Y y) (Z y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hY hZ)
    have hXZ : MDiffAt (fun y : M => inner ℝ (X y) (Z y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hX hZ)
    have d1 := mvfderiv_fun_mul hf hYZ
    have d2 := mvfderiv_fun_mul hf hXZ
    dsimp [K]
    simp only [inner_smul_right]
    rw [d1, d2]
    simp [hf, hX, hY, hZ, VectorField.mlieBracket_smul_left,
      VectorField.mlieBracket_smul_right, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
    ring
  · intro Z Z' hZ hZ'
    have hYZ : MDiffAt (fun y : M => inner ℝ (Y y) (Z y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hY hZ)
    have hYZ' : MDiffAt (fun y : M => inner ℝ (Y y) (Z' y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hY hZ')
    have hXZ : MDiffAt (fun y : M => inner ℝ (X y) (Z y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hX hZ)
    have hXZ' : MDiffAt (fun y : M => inner ℝ (X y) (Z' y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hX hZ')
    have d1 := mvfderiv_fun_add hYZ hYZ'
    have d2 := mvfderiv_fun_add hXZ hXZ'
    dsimp [K]
    simp only [inner_add_right]
    rw [d1, d2]
    simp [hY, hX, hZ, hZ', VectorField.mlieBracket_add_left,
      VectorField.mlieBracket_add_right, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
    ring

lemma K_add_Y (x : M) (X Y Y' Z : Π x : M, TangentSpace I x)
 (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
 (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
 K X (Y+Y') Z x = K X Y Z x + K X Y' Z x := by
  have hYZ : MDiffAt (fun y:M => inner ℝ (Y y) (Z y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hY hZ)
  have hY'Z : MDiffAt (fun y:M => inner ℝ (Y' y) (Z y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hY' hZ)
  have hXY : MDiffAt (fun y:M => inner ℝ (X y) (Y y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hX hY)
  have hXY' : MDiffAt (fun y:M => inner ℝ (X y) (Y' y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hX hY')
  have d1 := mvfderiv_fun_add hYZ hY'Z
  have d2 := mvfderiv_fun_add hXY hXY'
  dsimp [K]
  simp only [inner_add_left, inner_add_right]
  rw [d1, d2]
  simp [hY,hY',hX,hZ, VectorField.mlieBracket_add_left,
    VectorField.mlieBracket_add_right, inner_add_left, inner_add_right]
  ring

lemma K_smul_Y (x : M) (X Y Z : Π x : M, TangentSpace I x) (f:M→ℝ)
 (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
 (hZ : MDiffAt (T% Z) x) (hf : MDiffAt f x) :
 K X (f • Y) Z x = f x * K X Y Z x
                   + 2 * (mvfderiv I f x (X x)) * inner ℝ (Y x) (Z x) := by
  have hYZ : MDiffAt (fun y:M => inner ℝ (Y y) (Z y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hY hZ)
  have hXY : MDiffAt (fun y:M => inner ℝ (X y) (Y y)) x := (MDifferentiableAt.inner_bundle (IB:=I) hX hY)
  have d1 := mvfderiv_fun_mul hf hYZ
  have d2 := mvfderiv_fun_mul hf hXY
  dsimp [K]
  simp [inner_smul_left, inner_smul_right]
  rw [d1, d2]
  simp [hf, hY,hX,hZ,
    VectorField.mlieBracket_smul_left, VectorField.mlieBracket_smul_right,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_comm]
  ring

noncomputable def B (Y : Π x : M, TangentSpace I x) (x : M)
    (hY : MDiffAt (T% Y) x) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Z => K X Y Z x) x
    (fun Z hZ => K_tensor_X x Y Z hY hZ)
    (fun X hX => K_tensor_Z x X Y hX hY)

lemma B_apply (Y X Z : Π x : M, TangentSpace I x) (x:M)
 (hY : MDiffAt (T% Y) x) (hX : MDiffAt (T% X) x) (hZ : MDiffAt (T% Z) x) :
 B Y x hY (X x) (Z x) = K X Y Z x := by
 unfold B
 exact TensorialAt.mkHom₂_apply _ _ hX hZ

-- the Riesz representer of half of the Koszul functional
noncomputable def kcAt (Y : Π x : M, TangentSpace I x) (x : M)
    (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  -- Although the tangent fibre is (non-reducibly) just the model vector
  -- space, the manifold keeps this definition opaque for typeclass search.
  -- Pull finite dimensionality from the vector bundle identification with E.
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  letI : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  LinearMap.toContinuousLinearMap
  { toFun := fun v => (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm
                       (((2:ℝ)⁻¹) • (B Y x hY v))
    map_add' := by
      intro v w
      -- semilinear equivalence is additive
      simp
    map_smul' := by
      intro c v
      -- over the reals the conjugation is trivial
      simp [star_trivial, smul_smul, mul_comm] }

lemma kcAt_inner (Y X Z : Π x : M, TangentSpace I x) (x:M)
 (hY : MDiffAt (T% Y) x) (hX : MDiffAt (T% X) x) (hZ : MDiffAt (T% Z) x) :
 inner ℝ (kcAt Y x hY (X x)) (Z x) = (2:ℝ)⁻¹ * K X Y Z x := by
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  letI : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  have h := @InnerProductSpace.toDual_symm_apply ℝ (TangentSpace I x) _ _ _
  -- simp form
  unfold kcAt
  dsimp
  change inner ℝ ((InnerProductSpace.toDual ℝ (TangentSpace I x)).symm
                       (((2:ℝ)⁻¹) • (B Y x hY (X x)))) (Z x) = _
  rw [InnerProductSpace.toDual_symm_apply]
  change (((2:ℝ)⁻¹) • (B Y x hY (X x))) (Z x) = _
  simp [B_apply Y X Z x hY hX hZ]

end LeviSupport

end

-- END INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/Koszul.lean

-- BEGIN INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/SmoothRep.lean
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Function Module
noncomputable section
namespace LeviSupport
/-- Testing smoothness of a family of operators on vectors. The source of the
family may be a manifold. This variant of `contDiffOn_clm_apply` is handy for
bundle charts. -/
lemma contMDiffAt_clm_apply_iff_fd
 {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
 {H₀ : Type*} [TopologicalSpace H₀] {J : ModelWithCorners ℝ E₀ H₀}
 {N : Type*} [TopologicalSpace N] [ChartedSpace H₀ N]
 {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
 {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
 {k : WithTop ℕ∞} {p : N} {A : N → U →L[ℝ] W} :
 ContMDiffAt J 𝓘(ℝ, U →L[ℝ] W) k A p ↔
   ∀ u : U, ContMDiffAt J 𝓘(ℝ, W) k (fun z => A z u) p := by
  classical
  constructor
  · intro h u
    exact h.clm_apply (contMDiffAt_const (c:=u))
  · intro h
    let d := finrank ℝ U
    have hd : d = finrank ℝ (Fin d → ℝ) := (finrank_fin_fun ℝ).symm
    let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
    let e₂ := (e₁.arrowCongr (1 : W ≃L[ℝ] W)).trans (ContinuousLinearEquiv.piRing (Fin d))
    -- change coordinates in the finite-dimensional argument
    have hp : ContMDiffAt J 𝓘(ℝ, (Fin d → W)) k (fun z => e₂ (A z)) p := by
      apply (contMDiffAt_pi_space).2
      intro i
      have hi := h (e₁.symm (Pi.single i 1))
      -- the coordinate of `e₂ T` is evaluation on this vector
      change ContMDiffAt J 𝓘(ℝ, W) k
        (fun z => (1 : W ≃L[ℝ] W) ((A z) (e₁.symm (Pi.single i 1)))) p
      change ContMDiffAt J 𝓘(ℝ, W) k
        (fun z => (A z) (e₁.symm (Pi.single i 1))) p
      exact hi
    have hc : ContMDiffAt 𝓘(ℝ, (Fin d → W)) 𝓘(ℝ, U →L[ℝ] W) k
          (e₂.symm : (Fin d → W) → (U →L[ℝ] W)) (e₂ (A p)) :=
      e₂.symm.contDiff.contMDiff.contMDiffAt
    have hh := ContMDiffAt.comp p hc hp
    have heq : ((e₂.symm : (Fin d → W) → (U →L[ℝ] W)) ∘
                  (fun z => e₂ (A z))) = A := by
      funext z
      exact e₂.symm_apply_apply (A z)
    rw [heq] at hh
    exact hh
end LeviSupport
namespace LeviSupport
open scoped Manifold ContDiff
lemma ContMDiffAt.clm_inverse
 {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
 {H₀ : Type*} [TopologicalSpace H₀] {J : ModelWithCorners ℝ E₀ H₀}
 {N : Type*} [TopologicalSpace N] [ChartedSpace H₀ N]
 {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
 {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
 {k : WithTop ℕ∞} {p:N} {g : N → U →L[ℝ] W}
 (hg : ContMDiffAt J 𝓘(ℝ, U →L[ℝ] W) k g p)
 (hi : (g p).IsInvertible) :
 ContMDiffAt J 𝓘(ℝ, W →L[ℝ] U) k (fun z => (g z).inverse) p := by
 have hdiff : ContDiffAt ℝ k (ContinuousLinearMap.inverse : (U →L[ℝ] W) → (W →L[ℝ] U)) (g p) :=
   ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse hi
 exact hdiff.contMDiffAt.comp p hg
end LeviSupport

end

-- END INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/SmoothRep.lean

-- BEGIN INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/Uniqueness.lean
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative

lemma exists_smooth_tangent_extension
 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [FiniteDimensional ℝ E] [CompleteSpace E]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
 [IsManifold I ∞ M]
 {x : M} (v : TangentSpace I x) :
 ∃ X : (Π y : M, TangentSpace I y), CMDiff ∞ (T% X) ∧ X x = v := by
  -- local smooth extension in trivialization
  obtain ⟨s, hs, hsmooth⟩ :=
    (FiberBundle.exists_contMDiffOn_extend (I := I) (k := (∞ : ℕ∞ω)) E v)
  rcases mem_nhds_iff.mp hs with ⟨u, hu_sub, hu_open, hx_u⟩
  -- smooth on u
  have hsmooth' :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (FiberBundle.extend E v)) u :=
    hsmooth.mono hu_sub
  -- choose bump with support contained in u
  have hu_nhds : u ∈ 𝓝 x := hu_open.mem_nhds hx_u
  rcases (SmoothBumpFunction.nhds_basis_tsupport (I:=I) x).mem_iff.mp hu_nhds with
    ⟨f, hf_true, hf_sub⟩
  let X : Π y : M, TangentSpace I y := (f : M → ℝ) • (FiberBundle.extend E v)
  refine ⟨X, ?_, ?_⟩
  · -- smooth extension
    have hf_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f : M → ℝ) u :=
      f.contMDiff.contMDiffOn
    -- apply smul_section_tsupport
    exact ContMDiffOn.smul_section_of_tsupport hf_smooth hu_open hf_sub hsmooth'
  · -- value at x
    change f x • FiberBundle.extend E v x = v
    simp

lemma cov_unique_smooth_of_axioms
 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [FiniteDimensional ℝ E] [CompleteSpace E]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
 [IsManifold I ∞ M]
 [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
 [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
 (cov cov' : CovariantDerivative I E (TangentSpace I (M:=M)))
 (ht : cov.torsion = 0) (ht' : cov'.torsion = 0)
 (hm : ∀ (Y Z : Π x : M, TangentSpace I x),
    CMDiff ∞ (T% Y) → CMDiff ∞ (T% Z) →
    ∀ (x : M) (v : TangentSpace I x),
      mvfderiv I (fun y : M => inner ℝ (Y y) (Z y)) x v =
        inner ℝ (cov Y x v) (Z x) + inner ℝ (Y x) (cov Z x v))
 (hm' : ∀ (Y Z : Π x : M, TangentSpace I x),
    CMDiff ∞ (T% Y) → CMDiff ∞ (T% Z) →
    ∀ (x : M) (v : TangentSpace I x),
      mvfderiv I (fun y : M => inner ℝ (Y y) (Z y)) x v =
        inner ℝ (cov' Y x v) (Z x) + inner ℝ (Y x) (cov' Z x v)) :
 ∀ (Y : Π x : M, TangentSpace I x), CMDiff ∞ (T% Y) →
 ∀ (x : M) (v : TangentSpace I x), cov Y x v = cov' Y x v := by
  intro Y hYglob x v
  obtain ⟨X, hXglob, hvX⟩ := exists_smooth_tangent_extension (I:=I) v
  have hXat : MDiffAt (T% X) x := (hXglob x).mdifferentiableAt (by simp)
  have hYat : MDiffAt (T% Y) x := (hYglob x).mdifferentiableAt (by simp)
  let A (P Q R : Π x : M, TangentSpace I x) : ℝ :=
    inner ℝ (cov Q x (P x) - cov' Q x (P x)) (R x)
  have symmA (P Q : Π x : M, TangentSpace I x)
      (hP : MDiffAt (T% P) x) (hQ : MDiffAt (T% Q) x) :
      cov Q x (P x) - cov' Q x (P x) =
        cov P x (Q x) - cov' P x (Q x) := by
    have h1 : cov Q x (P x) - cov P x (Q x) - mlieBracket I P Q x = 0 := by
      calc
        _ = cov.torsion x (P x) (Q x) :=
          (cov.torsion_apply hP hQ).symm
        _ = 0 := by rw [ht]; rfl
    have h2 : cov' Q x (P x) - cov' P x (Q x) - mlieBracket I P Q x = 0 := by
      calc
        _ = cov'.torsion x (P x) (Q x) :=
          (cov'.torsion_apply hP hQ).symm
        _ = 0 := by rw [ht']; rfl
    -- rearrange additive group equality
    -- abel after substituting
    have hh1 : cov Q x (P x) - cov P x (Q x) = mlieBracket I P Q x :=
      sub_eq_zero.mp h1
    have hh2 : cov' Q x (P x) - cov' P x (Q x) = mlieBracket I P Q x :=
      sub_eq_zero.mp h2
    have hh := hh1.trans hh2.symm
    apply sub_eq_sub_iff_add_eq_add.mpr
    have hhh := sub_eq_sub_iff_add_eq_add.mp hh
    simpa [add_comm] using hhh
  have symmA' (P Q R : Π x : M, TangentSpace I x)
      (hP : CMDiff ∞ (T% P)) (hQ : CMDiff ∞ (T% Q)) :
      A P Q R = A Q P R := by
    unfold A
    rw [symmA P Q ((hP x).mdifferentiableAt (by simp))
      ((hQ x).mdifferentiableAt (by simp))]
  have skewA (P Q R : Π x : M, TangentSpace I x)
      (hQ : CMDiff ∞ (T% Q)) (hR : CMDiff ∞ (T% R)) :
      A P Q R = - A P R Q := by
    have e1 := hm Q R hQ hR x (P x)
    have e2 := hm' Q R hQ hR x (P x)
    rw [← real_inner_comm (cov Q x (P x)) (R x)] at e1
    rw [← real_inner_comm (cov' Q x (P x)) (R x)] at e2
    unfold A
    simp [inner_sub_left, real_inner_comm]
    linear_combination e2 - e1
  -- pair with arbitrary smooth Z extension to show vector zero
  apply sub_eq_zero.mp ?_
  let d : TangentSpace I x := cov Y x v - cov' Y x v
  obtain ⟨Z, hZglob, hdZ⟩ := exists_smooth_tangent_extension (I:=I) d
  have a1 := symmA' X Y Z hXglob hYglob
  have a2 := skewA Y X Z hXglob hZglob
  have a3 := symmA' Y Z X hYglob hZglob
  have a4 := skewA Z Y X hYglob hXglob
  have a5 := symmA' Z X Y hZglob hXglob
  have a6 := skewA X Z Y hZglob hYglob
  have a0 : A X Y Z = 0 := by
    linarith
  have id0 : inner ℝ d d = 0 := by
    simpa [A, d, hvX, hdZ] using a0
  have dzero : d = 0 := (inner_self_eq_zero).mp id0
  exact dzero

-- END INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/Uniqueness.lean

-- BEGIN INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/Construction.lean
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative
noncomputable section
namespace LeviSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [CompleteSpace E]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
 [RiemannianBundle (fun x : M => TangentSpace I x)]
 [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]

/-- First Koszul identity, purely alternating in the directing fields. -/
lemma K_swap_XY (X Y Z : Π x : M, TangentSpace I x) (x:M) :
 K X Y Z x - K Y X Z x =
    2 * inner ℝ (mlieBracket I X Y x) (Z x) := by
  dsimp [K]
  rw [VectorField.mlieBracket_swap_apply (I:=I) (V:=Y) (W:=X) (x:=x)]
  simp [real_inner_comm, inner_neg_left, inner_neg_right]
  ring

lemma K_pair_YZ (X Y Z : Π x : M, TangentSpace I x) (x:M) :
 K X Y Z x + K X Z Y x =
    2 * mvfderiv I (fun y:M => inner ℝ (Y y) (Z y)) x (X x) := by
  dsimp [K]
  rw [VectorField.mlieBracket_swap_apply (I:=I) (V:=Z) (W:=Y) (x:=x)]
  simp [real_inner_comm, inner_neg_left, inner_neg_right]
  ring

/-- Pointwise representative has the expected value on any differentiable direction field. -/
lemma kcAt_pair (Y X Z : Π x : M, TangentSpace I x) (x:M)
 (hY : MDiffAt (T% Y) x) (hX : MDiffAt (T% X) x) (hZ : MDiffAt (T% Z) x) :
 inner ℝ (kcAt Y x hY (X x)) (Z x) = (2:ℝ)⁻¹ * K X Y Z x :=
 kcAt_inner Y X Z x hY hX hZ

/-- Additivity of the pointwise representative in the differentiated section. Proof by
pairing with arbitrary differentiable extensions, avoiding any choice of frames. -/
lemma kcAt_add (Y Y' : Π x : M, TangentSpace I x) (x:M)
 (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) :
 kcAt (Y+Y') x (mdifferentiableAt_add_section hY hY') = kcAt Y x hY + kcAt Y' x hY' := by
  apply ContinuousLinearMap.ext
  intro v
  -- test against an arbitrary vector by the canonical differentiable extension
  let X : Π y:M, TangentSpace I y := FiberBundle.extend E v
  have hX : MDiffAt (T% X) x := FiberBundle.mdifferentiableAt_extend I E v
  -- equality of vectors in the real inner product fiber
  apply ext_inner_right ℝ
  intro w
  let Z : Π y:M, TangentSpace I y := FiberBundle.extend E w
  have hZ : MDiffAt (T% Z) x := FiberBundle.mdifferentiableAt_extend I E w
  have hxv : X x = v := by simp [X]
  have hxw : Z x = w := by simp [Z]
  have A := kcAt_inner (Y+Y') X Z x (mdifferentiableAt_add_section hY hY') hX hZ
  have B1 := kcAt_inner Y X Z x hY hX hZ
  have B2 := kcAt_inner Y' X Z x hY' hX hZ
  rw [K_add_Y x X Y Y' Z hX hY hY' hZ] at A
  -- the continuous maps are being evaluated at the chosen `v,w`
  simpa [hxv, hxw, inner_add_left] using (A.trans (by rw [mul_add, ← B1, ← B2]; rw [hxv, hxw]))

lemma kcAt_smul (f:M→ℝ) (Y : Π x:M, TangentSpace I x) (x:M)
 (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) :
 kcAt (f • Y) x (hf.smul_section hY) =
      f x • kcAt Y x hY + (mvfderiv I f x).smulRight (Y x) := by
  apply ContinuousLinearMap.ext
  intro v
  let X : Π y:M, TangentSpace I y := FiberBundle.extend E v
  have hX : MDiffAt (T% X) x := FiberBundle.mdifferentiableAt_extend I E v
  apply ext_inner_right ℝ
  intro w
  let Z : Π y:M, TangentSpace I y := FiberBundle.extend E w
  have hZ : MDiffAt (T% Z) x := FiberBundle.mdifferentiableAt_extend I E w
  have hxv : X x = v := by simp [X]
  have hxw : Z x = w := by simp [Z]
  have A := kcAt_inner (f • Y) X Z x (hf.smul_section hY) hX hZ
  have B1 := kcAt_inner Y X Z x hY hX hZ
  rw [K_smul_Y x X Y Z f hX hY hZ hf] at A
  have A' :
      inner ℝ (kcAt (f • Y) x (hf.smul_section hY) (X x)) (Z x) =
       f x * inner ℝ (kcAt Y x hY (X x)) (Z x) +
          (mvfderiv I f x (X x)) * inner ℝ (Y x) (Z x) := by
    rw [A, B1]
    ring
  -- identify the second term with the evaluation of `smulRight`
  simpa [hxv, hxw, inner_add_left, inner_smul_left, mul_comm, mul_left_comm,
    mul_assoc] using A'

/-- Unbundled Koszul prescription. At a nonsmooth germ the connection axioms impose no
condition; zero is a convenient total value. -/
noncomputable def koszulFun (Y : Π x:M, TangentSpace I x) (x:M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
by
  classical
  exact if h : MDiffAt (T% Y) x then kcAt Y x h else 0

lemma koszulFun_apply (Y : Π x:M, TangentSpace I x) (x:M)
 (hY : MDiffAt (T% Y) x) : koszulFun Y x = kcAt Y x hY := by
  classical
  unfold koszulFun
  simp [hY]

noncomputable def koszulCov :
 CovariantDerivative I E (TangentSpace I (M:=M)) where
 toFun := koszulFun
 isCovariantDerivativeOnUniv := by
   constructor
   · intro Y Y' x hY hY' hx
     have hsum : MDiffAt (T% (Y+Y')) x := mdifferentiableAt_add_section hY hY'
     simpa [koszulFun_apply (I:=I) _ _ hsum,
       koszulFun_apply (I:=I) _ _ hY, koszulFun_apply (I:=I) _ _ hY'] using
       (kcAt_add (I:=I) Y Y' x hY hY')
   · intro Y f x hY hf hx
     have hp : MDiffAt (T% (f • Y)) x := hf.smul_section hY
     simpa [koszulFun_apply (I:=I) _ _ hp,
       koszulFun_apply (I:=I) _ _ hY] using
       (kcAt_smul (I:=I) f Y x hf hY)

@[simp] lemma koszulCov_apply (Y : Π x:M, TangentSpace I x) (x:M)
 (hY : MDiffAt (T% Y) x) : koszulCov (I:=I) Y x = kcAt Y x hY :=
 koszulFun_apply (I:=I) _ _ hY

end LeviSupport

end

-- END INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/Construction.lean

-- BEGIN INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/Geometric.lean
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative
noncomputable section
open LeviSupport
namespace LeviSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [CompleteSpace E]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
 [RiemannianBundle (fun x : M => TangentSpace I x)]
 [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]

lemma koszul_torsion_zero : (koszulCov (I:=I) (M:=M)).torsion = 0 := by
  apply (CovariantDerivative.torsion_eq_zero_iff (koszulCov (I:=I) (M:=M))).2
  intro X Y x hX hY
  -- test against every w using differentiable extend
  apply ext_inner_right ℝ
  intro w
  let Z : Π y:M, TangentSpace I y := FiberBundle.extend E w
  have hZ : MDiffAt (T% Z) x := FiberBundle.mdifferentiableAt_extend I E w
  have hxw : Z x = w := by simp [Z]
  have A := kcAt_inner Y X Z x hY hX hZ
  have B' := kcAt_inner X Y Z x hX hY hZ
  rw [← koszulCov_apply (I:=I) Y x hY] at A
  rw [← koszulCov_apply (I:=I) X x hX] at B'
  rw [inner_sub_left]
  rw [← hxw]
  rw [A, B']
  have S := K_swap_XY (I:=I) X Y Z x
  nlinarith

lemma koszul_metric_formula :
    ∀ (Y Z : Π x:M, TangentSpace I x), CMDiff ∞ (T% Y) → CMDiff ∞ (T% Z) →
      ∀ (x:M) (v : TangentSpace I x),
       mvfderiv I (fun y : M => inner ℝ (Y y) (Z y)) x v =
        inner ℝ ((koszulCov (I:=I) (M:=M)) Y x v) (Z x) +
        inner ℝ (Y x) ((koszulCov (I:=I) (M:=M)) Z x v) := by
  intro Y Z hYglob hZglob x v
  -- extend v to smooth/diff X
  obtain ⟨X, hXglob, hv⟩ := exists_smooth_tangent_extension (I:=I) v
  have hX : MDiffAt (T% X) x := (hXglob x).mdifferentiableAt (by simp)
  have hY : MDiffAt (T% Y) x := (hYglob x).mdifferentiableAt (by simp)
  have hZ : MDiffAt (T% Z) x := (hZglob x).mdifferentiableAt (by simp)
  have A := kcAt_inner Y X Z x hY hX hZ
  have B' := kcAt_inner Z X Y x hZ hX hY
  rw [← koszulCov_apply (I:=I) Y x hY] at A
  rw [← koszulCov_apply (I:=I) Z x hZ] at B'
  rw [← hv]
  rw [← real_inner_comm (Y x) ((koszulCov (I:=I) (M:=M)) Z x (X x))]
  rw [A, B']
  have P := K_pair_YZ (I:=I) X Y Z x
  nlinarith
end LeviSupport

end

-- END INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/Geometric.lean

-- BEGIN INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/SmoothKoszul.lean
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative
noncomputable section
namespace LeviSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [CompleteSpace E]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
 [RiemannianBundle (fun x : M => TangentSpace I x)]
 [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]

/-- Directional derivative of a smooth real function in a smooth vector field is smooth.
This small consequence of `ContMDiffAt.mfderiv_const` is convenient because `mvfderiv`
lives in nontrivial tangent fibres. -/
lemma dir_smooth (f:M→ℝ) (X: Π x:M, TangentSpace I x)
 (hf : CMDiff ∞ f) (hX: CMDiff ∞ (T% X)) :
 CMDiff ∞ (fun x:M => mvfderiv I f x (X x)) := by
 intro x
 have hd : CMDiffAt ∞ (inTangentCoordinates I 𝓘(ℝ) id f (fun x => mfderiv I 𝓘(ℝ) f x) x) x :=
   ContMDiffAt.mfderiv_const (I:=I) (I':=𝓘(ℝ)) (hf x) (by simp)
 have hv : ContMDiffAt I ((𝓘(ℝ)).prod 𝓘(ℝ, ℝ)) ∞
      (fun y : M => ((⟨f y, (mfderiv I 𝓘(ℝ) f y) (X y)⟩ :
          TotalSpace ℝ (TangentSpace 𝓘(ℝ) : ℝ → Type _)))) x := by
   exact ContMDiffAt.clm_apply_of_inCoordinates hd (hX x) (hf x)
 have hv' := hv
 simp [contMDiffAt_totalSpace] at hv'
 exact hv'.2

end LeviSupport

namespace LeviSupport
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [CompleteSpace E]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
 [RiemannianBundle (fun x : M => TangentSpace I x)]
 [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]

/-- Local form; all the operations in the Koszul formula are local. -/
lemma dir_smoothAt (f : M → ℝ) (X : Π x : M, TangentSpace I x) {x : M}
    (hf : CMDiffAt ∞ f x) (hX : CMDiffAt ∞ (T% X) x) :
    CMDiffAt ∞ (fun y : M => mvfderiv I f y (X y)) x := by
  have hd : CMDiffAt ∞
      (inTangentCoordinates I 𝓘(ℝ) id f (fun y => mfderiv I 𝓘(ℝ) f y) x) x :=
    ContMDiffAt.mfderiv_const (I:=I) (I':=𝓘(ℝ)) hf (by simp)
  have hv : ContMDiffAt I ((𝓘(ℝ)).prod 𝓘(ℝ, ℝ)) ∞
      (fun y : M => ((⟨f y, (mfderiv I 𝓘(ℝ) f y) (X y)⟩ :
        TotalSpace ℝ (TangentSpace 𝓘(ℝ) : ℝ → Type _)))) x := by
    exact ContMDiffAt.clm_apply_of_inCoordinates hd hX hf
  have hv' := hv
  simp [contMDiffAt_totalSpace] at hv'
  exact hv'.2

/-- A pointwise (in fact germwise) smoothness lemma for the six terms of Koszul. -/
lemma K_smoothAt (X Y Z : Π x : M, TangentSpace I x) {x : M}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x)
    (hZ : CMDiffAt ∞ (T% Z) x) :
    CMDiffAt ∞ (fun y : M => K X Y Z y) x := by
  letI : IsManifold I (↑(⊤ : ℕ∞) + 1) M := IsManifold.of_le (m := (↑(⊤ : ℕ∞) + 1)) (n:=∞) (by simp)
  letI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) (by simpa using (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
  have hYZ : CMDiffAt ∞ (fun y : M => inner ℝ (Y y) (Z y)) x :=
    ContMDiffAt.inner_bundle hY hZ
  have hXZ : CMDiffAt ∞ (fun y : M => inner ℝ (X y) (Z y)) x :=
    ContMDiffAt.inner_bundle hX hZ
  have hXY : CMDiffAt ∞ (fun y : M => inner ℝ (X y) (Y y)) x :=
    ContMDiffAt.inner_bundle hX hY
  have a := dir_smoothAt (I:=I) _ _ hYZ hX
  have b := dir_smoothAt (I:=I) _ _ hXZ hY
  have c := dir_smoothAt (I:=I) _ _ hXY hZ
  have hbr₁ : CMDiffAt ∞ (T% (mlieBracket I Y Z)) x :=
    ContMDiffAt.mlieBracket_vectorField hY hZ (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)
  have hbr₂ : CMDiffAt ∞ (T% (mlieBracket I X Z)) x :=
    ContMDiffAt.mlieBracket_vectorField hX hZ (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)
  have hbr₃ : CMDiffAt ∞ (T% (mlieBracket I X Y)) x :=
    ContMDiffAt.mlieBracket_vectorField hX hY (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)
  have d : CMDiffAt ∞ (fun y : M => inner ℝ (mlieBracket I Y Z y) (X y)) x :=
    ContMDiffAt.inner_bundle hbr₁ hX
  have e : CMDiffAt ∞ (fun y : M => inner ℝ (mlieBracket I X Z y) (Y y)) x :=
    ContMDiffAt.inner_bundle hbr₂ hY
  have f : CMDiffAt ∞ (fun y : M => inner ℝ (mlieBracket I X Y y) (Z y)) x :=
    ContMDiffAt.inner_bundle hbr₃ hZ
  exact a.add b |>.sub c |>.sub d |>.sub e |>.add f

end LeviSupport

end

-- END INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/SmoothKoszul.lean

-- BEGIN INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/SmoothConstruction.lean
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Function
noncomputable section
namespace LeviSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [CompleteSpace E]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
 [RiemannianBundle (fun x : M => TangentSpace I x)]
 [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]

abbrev TP (x:M) := TangentSpace I x
local notation "t[" p "]" => (trivializationAt E (TangentSpace I (M:=M)) p)

lemma extend_symmL (p y:M) (u:E) :
 FiberBundle.extend E ((t[p].symmL ℝ p) u) y = (t[p].symmL ℝ y) u := by
  rw [Bundle.Trivialization.symmL_apply]
  rw [Bundle.Trivialization.symmL_apply]
  change FiberBundle.extend E (t[p].symm p u) y = t[p].symm y u
  simp [FiberBundle.extend, Bundle.Trivialization.apply_mk_symm,
    FiberBundle.mem_baseSet_trivializationAt]

/-- pair against arbitrary vectors, not just extended fields -/
lemma kcAt_inner' (Y : Π x:M, TangentSpace I x) (x:M) (hY : MDiffAt (T% Y) x)
 (v w : TangentSpace I x) :
 inner ℝ (kcAt Y x hY v) w = (2:ℝ)⁻¹ * (B Y x hY v w) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  letI : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  unfold kcAt
  dsimp
  change inner ℝ ((InnerProductSpace.toDual ℝ (TangentSpace I x)).symm
                       (((2:ℝ)⁻¹) • (B Y x hY v))) w = _
  rw [InnerProductSpace.toDual_symm_apply]
  change (((2:ℝ)⁻¹) • (B Y x hY v)) w = _
  simp

-- transform a bilinear form by a coordinate map going into its domain
def pull₂ {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 [NormedAddCommGroup W] [NormedSpace ℝ W]
 (L : E →L[ℝ] V) (q : V →L[ℝ] V →L[ℝ] W) : E →L[ℝ] E →L[ℝ] W :=
  ((ContinuousLinearMap.compL ℝ E V W).flip L).comp
    (q.comp L)

@[simp] lemma pull₂_apply {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 [NormedAddCommGroup W] [NormedSpace ℝ W]
 (L : E →L[ℝ] V) (q : V →L[ℝ] V →L[ℝ] W) (u z:E) :
 pull₂ (E:=E) L q u z = q (L u) (L z) := rfl

-- the coordinate objects on a fixed trivialization
variable (p:M)
def Lcoord (y:M) : E →L[ℝ] TangentSpace I y := t[p].symmL ℝ y

def Gcoord (y:M) : E →L[ℝ] E →L[ℝ] ℝ :=
  pull₂ (Lcoord (I:=I) p y) (innerSL ℝ : TangentSpace I y →L[ℝ] _)

def Bcoord (Y : Π x:M, TangentSpace I x)
 (h : ∀ x:M, MDiffAt (T% Y) x) (y:M) : E →L[ℝ] E →L[ℝ] ℝ :=
  pull₂ (Lcoord (I:=I) p y) (B Y y (h y))

def Acoord (Y : Π x:M, TangentSpace I x)
 (h : ∀ x:M, MDiffAt (T% Y) x) (y:M) : E →L[ℝ] E :=
  ContinuousLinearMap.inCoordinates E (TangentSpace I (M:=M)) E
   (TangentSpace I) p y p y (kcAt Y y (h y))

@[simp] lemma Gcoord_apply (p y:M) (u w:E) :
 Gcoord (I:=I) p y u w = inner ℝ ((Lcoord (I:=I) p y) u) ((Lcoord (I:=I) p y) w) := rfl
@[simp] lemma Bcoord_apply (p:M) (Y : Π x:M, TangentSpace I x)
 (h : ∀ x:M, MDiffAt (T% Y) x) (y:M) (u w:E) :
 Bcoord (I:=I) p Y h y u w = B Y y (h y) ((Lcoord (I:=I) p y) u) ((Lcoord (I:=I) p y) w) := rfl

lemma Lcoord_field_smoothAt (p:M) (u:E) :
 CMDiffAt ∞ (T% (fun y:M => (Lcoord (I:=I) p y) u)) p := by
  obtain ⟨s, hs, ht⟩ := (FiberBundle.exists_contMDiffOn_extend (I:=I)
    (k:=(∞ : ℕ∞ω)) E ((t[p].symmL ℝ p) u))
  have hx : p ∈ s := mem_of_mem_nhds hs
  have hz := (ht p hx).contMDiffAt hs
  have eqf : (fun y:M => (⟨y, (Lcoord (I:=I) p y) u⟩ :
      TotalSpace E (TangentSpace I))) =
      (fun y:M => (⟨y, FiberBundle.extend E ((t[p].symmL ℝ p) u) y⟩ :
       TotalSpace E (TangentSpace I))) := by
    funext y
    congr 1
    exact (extend_symmL (I:=I) p y u).symm
  rw [eqf]
  exact hz
lemma Gcoord_smoothAt (p:M) :
 ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (Gcoord (I:=I) p) p := by
  apply (contMDiffAt_clm_apply_iff_fd (J:=I)).2
  intro u
  apply (contMDiffAt_clm_apply_iff_fd (J:=I)).2
  intro w
  change CMDiffAt ∞ (fun y:M => inner ℝ ((Lcoord (I:=I) p y) u)
     ((Lcoord (I:=I) p y) w)) p
  exact ContMDiffAt.inner_bundle (Lcoord_field_smoothAt (I:=I) p u)
    (Lcoord_field_smoothAt (I:=I) p w)

lemma Bcoord_smoothAt (p:M) (Y : Π x:M, TangentSpace I x)
 (hsm : CMDiff ∞ (T% Y))
 (h : ∀ x:M, MDiffAt (T% Y) x) :
 ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (Bcoord (I:=I) p Y h) p := by
  apply (contMDiffAt_clm_apply_iff_fd (J:=I)).2
  intro u
  apply (contMDiffAt_clm_apply_iff_fd (J:=I)).2
  intro w
  let X : Π y:M, TangentSpace I y := fun y => (Lcoord (I:=I) p y) u
  let Z : Π y:M, TangentSpace I y := fun y => (Lcoord (I:=I) p y) w
  have hX : CMDiffAt ∞ (T% X) p := Lcoord_field_smoothAt (I:=I) p u
  have hZ : CMDiffAt ∞ (T% Z) p := Lcoord_field_smoothAt (I:=I) p w
  have hk := K_smoothAt (I:=I) X Y Z hX (hsm p) hZ
  change CMDiffAt ∞ (fun y:M =>
    B Y y (h y) ((Lcoord (I:=I) p y) u) ((Lcoord (I:=I) p y) w)) p
  -- equality with K holds near p, where the extensions are differentiable
  apply hk.congr_of_eventuallyEq
  have evX : ∀ᶠ y in 𝓝 p, MDiffAt (T% X) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (I:=I)
       (I':= I.prod 𝓘(ℝ, E)) (n:= (1:ℕ∞ω)) (by simp)).1
       (hX.of_le (by simp))).mono (fun y hy =>
         hy.mdifferentiableAt (by simp))
  have evZ : ∀ᶠ y in 𝓝 p, MDiffAt (T% Z) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (I:=I)
       (I':= I.prod 𝓘(ℝ, E)) (n:= (1:ℕ∞ω)) (by simp)).1
       (hZ.of_le (by simp))).mono (fun y hy =>
         hy.mdifferentiableAt (by simp))
  filter_upwards [evX, evZ] with y hy hz
  change B Y y (h y) (X y) (Z y) = K X Y Z y
  exact B_apply Y X Z y (h y) hy hz
lemma Gcoord_invertible (p:M) : (Gcoord (I:=I) p p).IsInvertible := by
 letI : FiniteDimensional ℝ (TangentSpace I p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) p
 letI : CompleteSpace (TangentSpace I p) := FiniteDimensional.complete ℝ _
 let ep := t[p].continuousLinearEquivAt ℝ p (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) p)
 let td : TangentSpace I p ≃L[ℝ] (TangentSpace I p →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ (TangentSpace I p)).toContinuousLinearEquiv
 let pre := (ep.arrowCongr (1 : ℝ ≃L[ℝ] ℝ))
 let eqv : E ≃L[ℝ] (E →L[ℝ] ℝ) := ep.symm.trans (td.trans pre)
 refine ⟨eqv, ?_⟩
 ext u w
 change inner ℝ ((t[p].symmL ℝ p) u) ((t[p].symmL ℝ p) w) = _
 -- evaluation of the composed equivalence
 change _ = ((pre) (td (ep.symm u))) w
 change _ = (td (ep.symm u)) (ep.symm w)
 change _ = inner ℝ (ep.symm u) (ep.symm w)
 rw [Bundle.Trivialization.continuousLinearEquivAt_symm_apply]
 rfl
lemma Gcoord_invertible_mem (p y:M) (hy : y ∈ t[p].baseSet) : (Gcoord (I:=I) p y).IsInvertible := by
 letI : FiniteDimensional ℝ (TangentSpace I y) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) y
 letI : CompleteSpace (TangentSpace I y) := FiniteDimensional.complete ℝ _
 let ep := t[p].continuousLinearEquivAt ℝ y hy
 let td : TangentSpace I y ≃L[ℝ] (TangentSpace I y →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ (TangentSpace I y)).toContinuousLinearEquiv
 let pre := (ep.arrowCongr (1 : ℝ ≃L[ℝ] ℝ))
 let eqv : E ≃L[ℝ] (E →L[ℝ] ℝ) := ep.symm.trans (td.trans pre)
 refine ⟨eqv, ?_⟩
 ext u w
 change inner ℝ ((t[p].symmL ℝ y) u) ((t[p].symmL ℝ y) w) = _
 -- evaluation of the composed equivalence
 change _ = ((pre) (td (ep.symm u))) w
 change _ = (td (ep.symm u)) (ep.symm w)
 change _ = inner ℝ (ep.symm u) (ep.symm w)
 rw [Bundle.Trivialization.continuousLinearEquivAt_symm_apply]
 rfl
def Ccoord (p:M) (Y : Π x:M, TangentSpace I x)
 (h : ∀ x:M, MDiffAt (T% Y) x) (y:M) : E →L[ℝ] E :=
   (Gcoord (I:=I) p y).inverse ∘L ((2:ℝ)⁻¹ • (Bcoord (I:=I) p Y h y))

lemma Ccoord_smoothAt (p:M) (Y : Π x:M, TangentSpace I x)
 (hsm : CMDiff ∞ (T% Y)) (h : ∀ x:M, MDiffAt (T% Y) x) :
  ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (Ccoord (I:=I) p Y h) p := by
  have ginv := ContMDiffAt.clm_inverse (Gcoord_smoothAt (I:=I) p)
    (Gcoord_invertible (I:=I) p)
  have bs := Bcoord_smoothAt (I:=I) p Y hsm h
  have bs' : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
     (fun y => (2:ℝ)⁻¹ • Bcoord (I:=I) p Y h y) p := by
       have hc : ContMDiffAt I 𝓘(ℝ) ∞ (fun _ : M => (2:ℝ)⁻¹) p := contMDiffAt_const
       exact hc.smul bs
  exact ginv.clm_comp bs'

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [CompleteSpace E]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
 [RiemannianBundle (fun x : M => TangentSpace I x)]
 [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
local notation "t[" p "]" => (trivializationAt E (TangentSpace I (M:=M)) p)

lemma Lcoord_Acoord_apply (p y : M) (Y : Π x:M, TangentSpace I x)
 (h : ∀ x:M, MDiffAt (T% Y) x) (hy : y ∈ t[p].baseSet) (u:E) :
  (Lcoord (I:=I) p y) (Acoord (I:=I) p Y h y u) =
      kcAt Y y (h y) ((Lcoord (I:=I) p y) u) := by
  let ep := t[p].continuousLinearEquivAt ℝ y hy
  have hh := ContinuousLinearMap.inCoordinates_eq (𝕜₁:=ℝ) (𝕜₂:=ℝ)
    (F:=E) (E:=TangentSpace I (M:=M))
    (F':=E) (E':=TangentSpace I (M:=M))
    (ϕ:=kcAt Y y (h y)) (x₀:=p) (x:=y) (y₀:=p) (y:=y) hy hy
  change Acoord (I:=I) p Y h y = _ at hh
  -- convert to coordinates with the equivalence
  change (ep.symm) (Acoord (I:=I) p Y h y u) =
    kcAt Y y (h y) ((Lcoord (I:=I) p y) u)
  apply ep.injective
  -- the chart of the vector on the right is exactly the coordinate expression
  calc
    ep (ep.symm (Acoord (I:=I) p Y h y u)) =
        Acoord (I:=I) p Y h y u := ep.apply_symm_apply _
    _ = ep (kcAt Y y (h y) ((Lcoord (I:=I) p y) u)) := by
      rw [hh]
      rfl

lemma Acoord_eq_Ccoord_mem (p y : M) (Y : Π x:M, TangentSpace I x)
 (h : ∀ x:M, MDiffAt (T% Y) x) (hy : y ∈ t[p].baseSet) :
   Acoord (I:=I) p Y h y = Ccoord (I:=I) p Y h y := by
  apply ContinuousLinearMap.ext
  intro u
  have inv := Gcoord_invertible_mem (I:=I) p y hy
  change Acoord (I:=I) p Y h y u =
    (Gcoord (I:=I) p y).inverse (((2:ℝ)⁻¹ • Bcoord (I:=I) p Y h y) u)
  symm
  apply (inv.inverse_apply_eq).2
  apply ContinuousLinearMap.ext
  intro z
  have ke := kcAt_inner' (I:=I) Y y (h y)
     ((Lcoord (I:=I) p y) u) ((Lcoord (I:=I) p y) z)
  change (2:ℝ)⁻¹ * B Y y (h y) ((Lcoord (I:=I) p y) u)
       ((Lcoord (I:=I) p y) z) =
    inner ℝ ((Lcoord (I:=I) p y) (Acoord (I:=I) p Y h y u))
       ((Lcoord (I:=I) p y) z)
  rw [Lcoord_Acoord_apply (I:=I) p y Y h hy u]
  exact ke.symm

lemma Acoord_smoothAt (p : M) (Y : Π x:M, TangentSpace I x)
 (hsm : CMDiff ∞ (T% Y)) (h : ∀ x:M, MDiffAt (T% Y) x) :
  ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (Acoord (I:=I) p Y h) p := by
  have hc := Ccoord_smoothAt (I:=I) p Y hsm h
  apply hc.congr_of_eventuallyEq
  filter_upwards [(t[p]).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) p)] with y hy
  exact (Acoord_eq_Ccoord_mem (I:=I) p y Y h hy)

lemma koszul_section_smooth (Y : Π x:M, TangentSpace I x)
 (hsm : CMDiff ∞ (T% Y)) :
 ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
   (fun x:M => (⟨x, LeviSupport.koszulCov (I:=I) Y x⟩ :
     TotalSpace (E →L[ℝ] E) (fun x:M => TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  -- all germs are differentiable
  have h : ∀ x:M, MDiffAt (T% Y) x := fun x => (hsm x).mdifferentiableAt (by simp)
  intro p
  -- use the hom-bundle chart
  apply (contMDiffAt_hom_bundle
    (n:=(∞:ℕ∞ω))
    (IB:=I) (IM:=I) (F₁:=E) (E₁:=TangentSpace I (M:=M))
      (F₂:=E) (E₂:=TangentSpace I (M:=M))
    (fun x:M => (⟨x, LeviSupport.koszulCov (I:=I) Y x⟩ :
      TotalSpace (E →L[ℝ] E)
       (fun x:M => TangentSpace I x →L[ℝ] TangentSpace I x)))).2
    ?_
  constructor
  · exact contMDiffAt_id
  · change CMDiffAt ∞ (fun y:M =>
      ContinuousLinearMap.inCoordinates E (TangentSpace I (M:=M)) E
       (TangentSpace I (M:=M)) p y p y (LeviSupport.koszulCov (I:=I) Y y)) p
    have ha := Acoord_smoothAt (I:=I) p Y hsm h
    change CMDiffAt ∞ (Acoord (I:=I) p Y h) p at ha
    apply ha.congr_of_eventuallyEq
    -- equality of the chosen representatives, at every point
    refine Filter.Eventually.of_forall ?_
    intro y
    change ContinuousLinearMap.inCoordinates E (TangentSpace I (M:=M)) E
       (TangentSpace I (M:=M)) p y p y (LeviSupport.koszulCov (I:=I) Y y) =
      Acoord (I:=I) p Y h y
    simp [Acoord, LeviSupport.koszulCov_apply (I:=I) Y y (h y)]

lemma koszulCov_contMDiff :
 ContMDiffCovariantDerivative (LeviSupport.koszulCov (I:=I) (M:=M)) ∞ := by
  constructor
  constructor
  intro Y hY
  -- convert `On univ` smoothness of the input to global smoothness
  have hY' : CMDiff ∞ (T% Y) := by
    intro x
    exact (hY x (Set.mem_univ x)).contMDiffAt (by simp)
  have hres := koszul_section_smooth (I:=I) Y hY'
  exact hres.contMDiffOn

end LeviSupport

end

-- END INLINED FILE: Mathlib/Support/levi_civita_exists_unique_2fb22f85ee/SmoothConstruction.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval
namespace Geometry
namespace LeviCivita

/-!
# Fundamental theorem of Riemannian geometry (Levi-Civita)

§38 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. On a `C^∞`
finite-dimensional Riemannian manifold `(M, g)`, there exists a unique
smooth torsion-free covariant derivative on `TM` that is compatible with
the metric — the **Levi-Civita connection**.

mathlib has `CovariantDerivative` on a tangent bundle,
`CovariantDerivative.torsion`, `ContMDiffCovariantDerivative`,
`RiemannianBundle`, `IsContMDiffRiemannianBundle`, and `mvfderiv` — but
no metric-compatibility predicate, no Levi-Civita existence/uniqueness, and
no Koszul formula (`grep -ri LeviCivita\|metric.compatible`: no relevant
hits). One helper definition (`IsMetricCompatible`, ~½ page) and an
"agreement on smooth sections" predicate (`SameOnSmooth`, mathlib's
`CovariantDerivative` is bundled over all sections including non-smooth
ones, so uniqueness is stated on the smooth-section subspace) are added
here.

A `[T2Space M]` hypothesis was added on 2026-06-14. We are not certain the
statement is wrong without it, but it looks suspicious: uniqueness on
smooth sections reduces to global smooth vector fields spanning every
tangent space, which (given how mathlib's bump-function machinery works)
needs `M` Hausdorff, and mathlib does not bundle Hausdorffness into
`IsManifold`. Since the classical Levi-Civita theorem is always stated for
(Hausdorff) manifolds, the original intent is better reflected with
`[T2Space M]`, so we add it now. Lorenzo Luccioli, using Harmonic's
Aristotle, flagged the missing hypothesis. Thanks to both.
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative

/-- A covariant derivative `cov` on `TM` is **compatible with the
Riemannian metric** if `v · ⟨Y, Z⟩ = ⟨∇_v Y, Z⟩ + ⟨Y, ∇_v Z⟩` for all
smooth vector fields `Y, Z` and every point/direction `(x, v)`. -/
def IsMetricCompatible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ (Y Z : Π x : M, TangentSpace I x),
    CMDiff ∞ (T% Y) → CMDiff ∞ (T% Z) →
    ∀ (x : M) (v : TangentSpace I x),
      mvfderiv I (fun y : M => inner ℝ (Y y) (Z y)) x v =
        inner ℝ (cov Y x v) (Z x) + inner ℝ (Y x) (cov Z x v)

/-- Two covariant derivatives **agree on smooth sections** if they produce
the same image on every smooth vector field. mathlib's
`CovariantDerivative` is bundled over all sections; the textbook Levi-Civita
uniqueness statement is uniqueness on the smooth-section subspace, captured
by `SameOnSmooth`. -/
def SameOnSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (cov cov' : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ (Y : Π x : M, TangentSpace I x), CMDiff ∞ (T% Y) →
    ∀ (x : M) (v : TangentSpace I x), cov Y x v = cov' Y x v



end LeviCivita
end Geometry
end LeanEval

open LeanEval.Geometry.LeviCivita
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem levi_civita_exists_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)] :
    ∃ cov : CovariantDerivative I E (TangentSpace I (M := M)),
      (ContMDiffCovariantDerivative cov ∞ ∧
        cov.torsion = 0 ∧ IsMetricCompatible cov) ∧
      ∀ cov' : CovariantDerivative I E (TangentSpace I (M := M)),
        (ContMDiffCovariantDerivative cov' ∞ ∧
          cov'.torsion = 0 ∧ IsMetricCompatible cov') →
        SameOnSmooth cov cov' :=
/-ResultProofBegin-/by
  classical
  -- The remaining (and genuinely geometric) part is the construction.  Keeping the
  -- witness separated is useful: uniqueness uses just torsion/metric identities, not
  -- smoothness of the chosen connection.
  -- Pointwise Riesz representative of the Koszul functional constructed in
  -- `Koszul`. For nonsmooth germs the axioms impose no value, so set it to zero.
  obtain ⟨cov, hcovs, hcovt, hcovm⟩ : ∃ cov : CovariantDerivative I E (TangentSpace I (M := M)), ContMDiffCovariantDerivative cov ∞ ∧ cov.torsion = 0 ∧ IsMetricCompatible cov := by
    refine ⟨LeviSupport.koszulCov (I:=I) (M:=M), ?_,
      LeviSupport.koszul_torsion_zero (I:=I) (M:=M), ?_⟩
    · exact LeviSupport.koszulCov_contMDiff (I:=I) (M:=M)
    · exact LeviSupport.koszul_metric_formula (I:=I) (M:=M)
  refine ⟨cov, ⟨hcovs, hcovt, hcovm⟩, ?_⟩
  intro cov' h'
  rcases h' with ⟨h'smooth, h'tors, h'metric⟩
  -- Agreement follows pointwise from the symmetric/skew-symmetric argument;
  -- global smooth extensions of vectors are supplied by smooth bump functions.
  exact cov_unique_smooth_of_axioms (I := I) cov cov' hcovt h'tors hcovm h'metric
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
