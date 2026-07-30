import Mathlib
namespace Submission

set_option maxHeartbeats 2000000
open Matrix
open scoped Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (A : Matrix n n ℂ)
lemma hHerm : (A + star A).IsHermitian := by
  rw [Matrix.star_eq_conjTranspose]
  exact Matrix.isHermitian_add_transpose_self _
lemma kHerm : ((Complex.I) • (A - star A)).IsHermitian := by
  -- compute
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub]
  -- goal star I • ((A)ᴴ - (star A)ᴴ) = ...
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  simp [smul_sub, sub_eq_add_neg]; ac_rfl

lemma hkcomm (hN : IsStarNormal A) :
    Commute (A + star A) ((Complex.I) • (A - star A)) := by
  rw [Commute]
  change (A + star A) * ((Complex.I) • (A - star A)) =
    ((Complex.I) • (A - star A)) * (A + star A)
  rw [Matrix.mul_smul, Matrix.smul_mul]
  -- goals factors scalar; commute scalars
  -- pull and inject
  congr 1
  -- now 
  have hc : star A * A = A * star A := (isStarNormal_iff A).mp hN |>.eq
  -- expand
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul]
  -- replace commuting middle
  rw [hc]
  abel
open WithLp
lemma lincomm (hN : IsStarNormal A) :
    Commute (Matrix.toEuclideanLin (A + star A))
      (Matrix.toEuclideanLin ((Complex.I) • (A - star A))) := by
  -- via ext
  rw [Commute]
  apply LinearMap.ext
  intro v
  -- simp mul_apply, toEuclideanLin_apply
  -- forget lp wrapper
  change WithLp.toLp 2 ((A + star A) *ᵥ (((Complex.I) • (A - star A)) *ᵥ v.ofLp)) =
    WithLp.toLp 2 (((Complex.I) • (A - star A)) *ᵥ ((A + star A) *ᵥ v.ofLp))
  congr 1
  simp_rw [Matrix.mulVec_mulVec]
  exact congr_arg (fun M : Matrix n n ℂ => M *ᵥ v.ofLp) (hkcomm A hN).eq
open Module End -- maybe
lemma exists_onb (hN : IsStarNormal A) :
    ∃ q : OrthonormalBasis n ℂ (EuclideanSpace ℂ n), ∃ d : n → ℂ,
      ∀ j : n, A *ᵥ (q j).ofLp = d j • (q j).ofLp := by
  classical
  let H : Module.End ℂ (EuclideanSpace ℂ n) := Matrix.toEuclideanLin (A + star A)
  let K : Module.End ℂ (EuclideanSpace ℂ n) := Matrix.toEuclideanLin ((Complex.I) • (A - star A))
  have hsH : LinearMap.IsSymmetric H := Matrix.isSymmetric_toEuclideanLin_iff.mpr (hHerm A)
  have hsK : LinearMap.IsSymmetric K := Matrix.isSymmetric_toEuclideanLin_iff.mpr (kHerm A)
  have hc : Commute H K := lincomm A hN
  let V : ℂ × ℂ → Submodule ℂ (EuclideanSpace ℂ n) := fun i =>
    Module.End.eigenspace H i.2 ⊓ Module.End.eigenspace K i.1
  have hV : DirectSum.IsInternal V :=
    LinearMap.IsSymmetric.directSum_isInternal_of_commute hsH hsK hc
  have hVo : OrthogonalFamily ℂ (fun i => V i) (fun i => (V i).subtypeₗᵢ) :=
    LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hsH hsK
  let I := (Module.End.Eigenvalues K) × (Module.End.Eigenvalues H)
  let W : I → Submodule ℂ (EuclideanSpace ℂ n) := fun i =>
    Module.End.eigenspace H (i.2 : ℂ) ⊓ Module.End.eigenspace K (i.1 : ℂ)
  have hWo : OrthogonalFamily ℂ (fun i => W i) (fun i => (W i).subtypeₗᵢ) := by
    let f : I → ℂ × ℂ := fun i => ((i.1 : ℂ), (i.2 : ℂ))
    have inj : Function.Injective f := by
      intro a b hab
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hab)
      · exact Subtype.ext (congrArg Prod.snd hab)
    have hh := hVo.comp inj
    change OrthogonalFamily ℂ (fun i : I => V (f i)) (fun i => (V (f i)).subtypeₗᵢ) at hh
    change OrthogonalFamily ℂ (fun i : I => V (f i)) (fun i => (V (f i)).subtypeₗᵢ)
    exact hh
  have hiSup : iSup W = (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) := by
    -- it contains each old space
    have all : ∀ i : ℂ × ℂ, V i ≤ iSup W := by
      intro i
      by_cases h1 : Module.End.eigenspace K i.1 = ⊥
      · have zz : V i = ⊥ := by dsimp [V]; rw [h1]; simp
        simp [zz]
      by_cases h2 : Module.End.eigenspace H i.2 = ⊥
      · have zz : V i = ⊥ := by dsimp [V]; rw [h2]; simp
        simp [zz]
      let a : Module.End.Eigenvalues K := ⟨i.1, h1⟩
      let b : Module.End.Eigenvalues H := ⟨i.2, h2⟩
      have le : W (a,b) ≤ iSup W := le_iSup W (a,b)
      exact le
    calc
      iSup W = (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) := by
        apply top_unique
        have hvtop : iSup V = (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) := by
          -- from hV? use symmetric-specific theorem easier
          change (⨆ i : ℂ × ℂ, H.eigenspace i.2 ⊓ K.eigenspace i.1) = ⊤
          rw [iSup_prod]
          rw [iSup_comm]
          exact LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hsH hsK hc
        rw [← hvtop]
        exact iSup_le all
      _ = _ := rfl
  have hW : DirectSum.IsInternal W := hWo.isInternal_iff.mpr
    (Submodule.orthogonal_eq_bot_iff.mpr hiSup)
  let q0 : OrthonormalBasis (Fin (Fintype.card n)) ℂ (EuclideanSpace ℂ n) :=
    hW.subordinateOrthonormalBasis (finrank_euclideanSpace (𝕜:=ℂ) (ι:=n)) hWo
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let q : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := q0.reindex e
  -- eigenvalues index values of both maps
  let idx0 : Fin (Fintype.card n) → I := fun j =>
    hW.subordinateOrthonormalBasisIndex (finrank_euclideanSpace (𝕜:=ℂ) (ι:=n)) j hWo
  let idx : n → I := fun j => idx0 (e.symm j)
  let d : n → ℂ := fun j => (((idx j).2 : ℂ) + -Complex.I * ((idx j).1 : ℂ)) / 2
  refine ⟨q, d, ?_⟩
  intro j
  have mem : q j ∈ W (idx j) := by
    change (q0.reindex e) j ∈ W (idx0 (e.symm j))
    rw [OrthonormalBasis.reindex_apply]
    exact hW.subordinateOrthonormalBasis_subordinate
      (finrank_euclideanSpace (𝕜:=ℂ) (ι:=n)) _ hWo
  have hH' : H (q j) = ((idx j).2 : ℂ) • (q j) := by
    exact Module.End.mem_eigenspace_iff.mp mem.1
  have hK' : K (q j) = ((idx j).1 : ℂ) • (q j) := by
    exact Module.End.mem_eigenspace_iff.mp mem.2
  -- solve, via function-valued equations
  have hHv : (A + star A) *ᵥ (q j).ofLp = ((idx j).2 : ℂ) • (q j).ofLp := by
    exact congrArg WithLp.ofLp hH'
  have hKv : ((Complex.I) • (A - star A)) *ᵥ (q j).ofLp = ((idx j).1 : ℂ) • (q j).ofLp := by
    exact congrArg WithLp.ofLp hK'
  -- convert K to equation for A-starA
  dsimp [d]
  -- use linear algebra combination; ext coordinate
  funext t
  have eH := congrFun hHv t
  have eK := congrFun hKv t
  -- simplify mulvec distribution and function smul at t
  simp [Matrix.add_mulVec] at eH
  simp [Matrix.smul_mulVec, Matrix.sub_mulVec] at eK
  -- let x=A..., y=star A
  dsimp at eH eK ⊢
  -- remove the factor i
  have eK' := congrArg (fun z : ℂ => (-Complex.I) * z) eK
  have ii : (Complex.I:ℂ) * Complex.I = -1 := Complex.I_mul_I
  -- simplify it
  have eK'' : ( (A *ᵥ (q j).ofLp) t - (star A *ᵥ (q j).ofLp) t) =
      (-Complex.I) * (((idx j).1 : ℂ) * (q j).ofLp t) := by
    calc
      _ = (-Complex.I) * (Complex.I * ((A *ᵥ (q j).ofLp) t - (star A *ᵥ (q j).ofLp) t)) := by
        rw [← mul_assoc, neg_mul, ii]; ring
      _ = _ := eK'
  linear_combination (1/2) * eH + (1/2) * eK''
lemma forward (hN : IsStarNormal A) :
      ∃ U ∈ unitary (Matrix n n ℂ), ∃ d : n → ℂ,
        A = U * diagonal d * star U := by
  classical
  obtain ⟨q,d,hd⟩ := exists_onb A hN
  let b := EuclideanSpace.basisFun n ℂ
  let U : Matrix n n ℂ := b.toBasis.toMatrix q.toBasis
  have hU1 : star U * U = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    exact b.toMatrix_orthonormalBasis_conjTranspose_mul_self q
  have hU2 : U * star U = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    exact b.toMatrix_orthonormalBasis_self_mul_conjTranspose q
  refine ⟨U, ⟨hU1,hU2⟩, d, ?_⟩
  -- It suffices A U = U diag
  have colU (j : n) : U.col j = (q j).ofLp := by rfl
  have AU : A * U = U * diagonal d := by
    -- columns
    ext i j
    have ev := hd j
    -- take coordinate
    have evt := congrFun ev i
    change (A *ᵥ U.col j) i = _
    -- first the diagonal product
    simp [Matrix.mul_apply, Matrix.diagonal, mul_ite]
    rw [colU j]
    -- express the entry of U by its column
    have entry : U i j = (q j).ofLp i := congrFun (colU j) i
    rw [entry]
    simpa [mul_comm] using evt
  -- multiply by star
  calc
    A = A * 1 := by rw [mul_one]
    _ = A * (U * star U) := by rw [hU2]
    _ = (A * U) * star U := by rw [mul_assoc]
    _ = U * diagonal d * star U := by rw [AU]
lemma reverse {A : Matrix n n ℂ} (h : ∃ U ∈ unitary (Matrix n n ℂ), ∃ d : n → ℂ,
        A = U * diagonal d * star U) : IsStarNormal A := by
  classical
  rcases h with ⟨U, hU, d, rfl⟩
  have hU1 : star U * U = (1 : Matrix n n ℂ) := hU.1
  have hU2 : U * star U = (1 : Matrix n n ℂ) := hU.2
  apply (isStarNormal_iff (U * diagonal d * star U)).2
  rw [Commute]
  change star (U * diagonal d * star U) * (U * diagonal d * star U) =
      (U * diagonal d * star U) * star (U * diagonal d * star U)
  have hstar : star (U * diagonal d * star U) =
      U * star (diagonal d) * star U := by
    simp [star_mul, mul_assoc]
  have hD : (star (diagonal d) : Matrix n n ℂ) * diagonal d =
      diagonal d * star (diagonal d) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hstar]
  calc
    (U * star (diagonal d) * star U) * (U * diagonal d * star U)
        = (U * star (diagonal d)) * (star U * U) * diagonal d * star U := by
            simp only [mul_assoc]
    _ = (U * star (diagonal d)) * diagonal d * star U := by
          rw [hU1]
          simp
    _ = U * (star (diagonal d) * diagonal d) * star U := by
          simp only [mul_assoc]
    _ = U * (diagonal d * star (diagonal d)) * star U := by
          rw [hD]
    _ = (U * diagonal d) * star (diagonal d) * star U := by
          simp only [mul_assoc]
    _ = (U * diagonal d) * (star U * U) * star (diagonal d) * star U := by
          rw [hU1]
          simp
    _ = (U * diagonal d * star U) * (U * star (diagonal d) * star U) := by
          simp only [mul_assoc]
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/
/-ResultBegin-/

theorem normal_spectral_theorem (A : Matrix n n ℂ) :
    IsStarNormal A ↔
      ∃ U ∈ unitary (Matrix n n ℂ), ∃ d : n → ℂ,
        A = U * diagonal d * star U :=
/-ResultProofBegin-/ by
 constructor
 · exact forward A
 · exact reverse
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
