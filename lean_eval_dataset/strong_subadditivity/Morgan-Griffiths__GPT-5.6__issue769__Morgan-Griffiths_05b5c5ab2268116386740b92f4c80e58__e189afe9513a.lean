import ChallengeDeps
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/AnalyticBase.lean
section
open ComplexOrder
open scoped MatrixOrder Matrix.Norms.L2Operator
open Filter

-- Continuity of the harmless, total version of x log x on self-adjoint matrix paths.
noncomputable section
namespace SSAux
-- product with the raw logarithm equals CFC of the continuous scalar x log x.
lemma mul_cfc_log_eq_cfc_mulLog {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (T : Matrix n n ℂ) (hT : T.IsHermitian) :
    T * cfc Real.log T = cfc (fun t : ℝ => t * Real.log t) T := by
  classical
  have fin : (spectrum ℝ T).Finite := by
    rw [hT.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  change T * cfc Real.log T = _
  conv_lhs => lhs; rw [← cfc_id ℝ T (ha:=hT.isSelfAdjoint)]
  -- multiply in the functional calculus (every function is continuous on this finite spectrum)
  rw [← cfc_mul id Real.log T (hf:=continuous_id.continuousOn)
        (hg:=fin.continuousOn _)]
  rfl


end SSAux

end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/AnalyticBase.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Block.lean
section
open scoped Kronecker
open ComplexOrder
noncomputable section
-- block embedding I_X \otimes Y
namespace SSAux
variable (ι κ : Type*) [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
/-- Unital star algebra embedding which repeats a square matrix along an identity
    block. This is `I ⊗ S`. -/
noncomputable def leftIdHom : Matrix κ κ ℂ →⋆ₐ[ℂ] Matrix (ι × κ) (ι × κ) ℂ where
  toFun S := (1 : Matrix ι ι ℂ) ⊗ₖ S
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by
    simpa using
      (Matrix.mul_kronecker_mul (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) X Y)
  map_zero' := Matrix.kronecker_zero _
  map_add' X Y := Matrix.kronecker_add _ _ _
  commutes' r := by
    classical
    ext x y
    by_cases hx : x = y
    · subst y
      simp [Matrix.kronecker_apply, Matrix.algebraMap_eq_diagonal,
        Matrix.diagonal, Pi.algebraMap_def]
    · have hor : x.1 ≠ y.1 ∨ x.2 ≠ y.2 := by
        contrapose hx
        push_neg at hx
        exact Prod.ext hx.1 hx.2
      rcases hor with h1 | h2
      · simp [Matrix.kronecker_apply, Matrix.algebraMap_eq_diagonal,
          Matrix.diagonal, h1, (show x ≠ y by intro q; exact h1 (congrArg Prod.fst q))]
      · simp [Matrix.kronecker_apply, Matrix.algebraMap_eq_diagonal,
          Matrix.diagonal, h2, (show x ≠ y by intro q; exact h2 (congrArg Prod.snd q))]
  map_star' X := by
    change (1 : Matrix ι ι ℂ) ⊗ₖ star X = star ((1 : Matrix ι ι ℂ) ⊗ₖ X)
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

@[simp] lemma leftIdHom_apply (S : Matrix κ κ ℂ) :
    leftIdHom ι κ S = (1 : Matrix ι ι ℂ) ⊗ₖ S := rfl

lemma continuous_leftIdHom : Continuous (leftIdHom ι κ) := by
  -- entries are finite-coordinate linear functions
  change Continuous (fun S : Matrix κ κ ℂ =>
    (1 : Matrix ι ι ℂ) ⊗ₖ S)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun S : Matrix κ κ ℂ =>
    (1 : Matrix ι ι ℂ) i.1 j.1 * S i.2 j.2)
  fun_prop

/-- Continuous functional calculus on a repeated block repeats the calculus. -/
lemma leftIdHom_cfc (S : Matrix κ κ ℂ) (hS : S.IsHermitian) (f : ℝ → ℝ) :
    leftIdHom ι κ (cfc f S) = cfc f (leftIdHom ι κ S) := by
  have hf : ContinuousOn f (spectrum ℝ S) := by
    rw [hS.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn _
  have hs : IsSelfAdjoint S := hS.isSelfAdjoint
  have hms : IsSelfAdjoint (leftIdHom ι κ S) := by
    -- a star hom sends self adjoints to self adjoints
    rw [isSelfAdjoint_iff] at hs ⊢
    calc
      star (leftIdHom ι κ S) = leftIdHom ι κ (star S) :=
        (map_star (leftIdHom ι κ) S).symm
      _ = leftIdHom ι κ S := congrArg _ hs
  have hh := StarAlgHomClass.map_cfc (leftIdHom ι κ) f S
    (hf := hf) (hφ := continuous_leftIdHom ι κ) (ha := hs) (hφa := hms)
  exact hh

lemma leftIdHom_entry (S : Matrix κ κ ℂ) (i j : ι × κ) :
    leftIdHom ι κ S i j = if i.1 = j.1 then S i.2 j.2 else 0 := by
  classical
  by_cases h : i.1 = j.1
  · simp [leftIdHom_apply, Matrix.kronecker_apply, Matrix.one_apply, h]
  · simp [leftIdHom_apply, Matrix.kronecker_apply, Matrix.one_apply, h]

-- product of trace against repeated block, without using any named partial trace
lemma trace_mul_leftIdHom (T : Matrix (ι × κ) (ι × κ) ℂ)
    (S : Matrix κ κ ℂ) :
    Matrix.trace (T * leftIdHom ι κ S) =
      Matrix.trace ((Matrix.of (fun b c : κ => ∑ a : ι, T (a,b) (a,c))) * S) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  -- expand all product indices and use delta on the first coordinate of the second factor
  -- first split the product sum
  simp [leftIdHom_entry, Finset.mul_sum, Finset.sum_mul,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]

end SSAux
end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Block.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Intertwine.lean
section
open scoped ComplexOrder Kronecker
open Matrix
noncomputable section
namespace SSAuxInter

-- rectangular intertwining transports the finite-dimensional real functional calculus.
-- No continuity hypotheses on f are needed for matrices.
lemma cfc_mul_rect_eq
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (P : Matrix n n ℂ) (Q : Matrix m m ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (K : Matrix n m ℂ) (h : P * K = K * Q) (f : ℝ → ℝ) :
    (cfc f P) * K = K * (cfc f Q) := by
  classical
  let U := hP.eigenvectorUnitary
  let V := hQ.eigenvectorUnitary
  let d : n → ℝ := hP.eigenvalues
  let e : m → ℝ := hQ.eigenvalues
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (d i : ℂ))
  let E : Matrix m m ℂ := Matrix.diagonal (fun j => (e j : ℂ))
  let dF : Matrix n n ℂ := Matrix.diagonal (fun i => (f (d i) : ℂ))
  let eF : Matrix m m ℂ := Matrix.diagonal (fun j => (f (e j) : ℂ))
  let W : Matrix n m ℂ := star (↑U : Matrix n n ℂ) * K * (↑V : Matrix m m ℂ)
  have pdiag : P = (↑U : Matrix n n ℂ) * D * star (↑U : Matrix n n ℂ) := by
    simpa [D, d, Function.comp_def, mul_assoc, Unitary.conjStarAlgAut_apply] using hP.spectral_theorem
  have qdiag : Q = (↑V : Matrix m m ℂ) * E * star (↑V : Matrix m m ℂ) := by
    simpa [E, e, Function.comp_def, mul_assoc, Unitary.conjStarAlgAut_apply] using hQ.spectral_theorem
  have pfdiag : cfc f P = (↑U : Matrix n n ℂ) * dF * star (↑U : Matrix n n ℂ) := by
    rw [hP.cfc_eq f, Matrix.IsHermitian.cfc]
    simp [dF, d, U, Function.comp_def, mul_assoc, Unitary.conjStarAlgAut_apply]
  have qfdiag : cfc f Q = (↑V : Matrix m m ℂ) * eF * star (↑V : Matrix m m ℂ) := by
    rw [hQ.cfc_eq f, Matrix.IsHermitian.cfc]
    simp [eF, e, V, Function.comp_def, mul_assoc, Unitary.conjStarAlgAut_apply]
  have Uc (Z : Matrix n m ℂ) : star (↑U : Matrix n n ℂ) * ((↑U : Matrix n n ℂ) * Z) = Z := by
    rw [← Matrix.mul_assoc, U.property.1, Matrix.one_mul]
  have UU (Z : Matrix n m ℂ) : (↑U : Matrix n n ℂ) * (star (↑U : Matrix n n ℂ) * Z) = Z := by
    rw [← Matrix.mul_assoc, U.property.2, Matrix.one_mul]
  have mid : D * W = W * E := by
    -- multiply h by the eigenvector unitaries
    -- U†(P K)V = U†(K Q)V
    have hh := congrArg (fun Z : Matrix n m ℂ =>
       star (↑U : Matrix n n ℂ) * Z * (↑V : Matrix m m ℂ)) h
    -- cancel the unitary pairs
    simpa [pdiag, qdiag, W, Matrix.mul_assoc, U.property.1, U.property.2,
      V.property.1, V.property.2, Uc] using hh
  have midf : dF * W = W * eF := by
    ext i j
    have ij := congrArg (fun Z : Matrix n m ℂ => Z i j) mid
    -- entries of a product by a diagonal matrix
    have base : (d i : ℂ) * W i j = W i j * (e j : ℂ) := by
      simpa [D, E, Matrix.diagonal, Matrix.mul_apply] using ij
    by_cases hz : d i = e j
    · simp [dF, eF, Matrix.diagonal, Matrix.mul_apply, hz, mul_comm]
    · have hn : ( (d i : ℂ) - (e j : ℂ) ) ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast hz)
      have wij : W i j = 0 := by
        have z : ((d i : ℂ) - (e j : ℂ)) * W i j = 0 := by
          calc
            ((d i : ℂ) - (e j : ℂ)) * W i j =
                (d i : ℂ) * W i j - W i j * (e j : ℂ) := by ring
            _ = 0 := sub_eq_zero.mpr base
        exact (mul_eq_zero.mp z |>.resolve_left hn)
      simp [dF, eF, Matrix.diagonal, Matrix.mul_apply, wij]
  rw [pfdiag, qfdiag]
  -- insert U† and V into K
  have res := congrArg (fun Z : Matrix n m ℂ =>
      (↑U : Matrix n n ℂ) * Z * star (↑V : Matrix m m ℂ)) midf
  simpa [W, Matrix.mul_assoc, U.property.1, U.property.2,
        V.property.1, V.property.2, UU] using res

end SSAuxInter
namespace SSAuxInter
open Matrix
/-- A useful compression corollary. If an isometric column intertwines two
Hermitian finite matrices, then compressing *any* real functional calculus is
exact. Unlike analytic Jensen, this is an equality about the invariant corner. -/
lemma compress_cfc_of_intertwine
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (K : Matrix n m ℂ) (hK : K.conjTranspose * K = (1 : Matrix m m ℂ))
    (P : Matrix n n ℂ) (Q : Matrix m m ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (h : P * K = K * Q) (f : ℝ → ℝ) :
    K.conjTranspose * cfc f P * K = cfc f Q := by
  have z := cfc_mul_rect_eq P Q hP hQ K h f
  -- multiply the intertwining identity by K† on the left
  have z' := congrArg (fun X : Matrix n m ℂ => K.conjTranspose * X) z
  simpa [Matrix.mul_assoc, ← Matrix.mul_assoc K.conjTranspose K,
      hK, Matrix.one_mul] using z'
end SSAuxInter

end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Intertwine.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/JointBridge.lean
section
open scoped ComplexOrder
open Matrix
open CStarMatrix
namespace SSAuxJoint

variable {n : Type*} [Fintype n] [DecidableEq n]
noncomputable local instance : ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint := IsSelfAdjoint.instContinuousFunctionalCalculus
noncomputable local instance : NonnegSpectrumClass ℝ (CStarMatrix n n ℂ) := CStarAlgebra.instNonnegSpectrumClass

lemma ofMatrix_pos (A : Matrix n n ℂ) (h : A.PosDef) :
 IsStrictlyPositive (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) := by
  have ha : IsSelfAdjoint (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) := by
    change star A = A
    exact h.isHermitian
  apply (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R:=ℝ) _ ha).2
  change ∀ x ∈ spectrum ℝ A, 0 < x
  rw [h.isHermitian.spectrum_real_eq_range_eigenvalues]
  intro x hx
  obtain ⟨i,rfl⟩ := hx
  exact (h.isHermitian.posDef_iff_eigenvalues_pos.mp h) i
lemma posDef_iff_ofMatrix (A : Matrix n n ℂ) :
 A.PosDef ↔ IsStrictlyPositive (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) := by
 constructor
 · exact fun h => by exact (by
     have ha : IsSelfAdjoint (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) := by
       change star A = A
       exact h.isHermitian
     apply (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R:=ℝ) _ ha).2
     change ∀ x ∈ spectrum ℝ A, 0 < x
     rw [h.isHermitian.spectrum_real_eq_range_eigenvalues]
     intro x hx
     obtain ⟨i,rfl⟩ := hx
     exact (h.isHermitian.posDef_iff_eigenvalues_pos.mp h) i)
 · intro hh
   have ha' : IsSelfAdjoint (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) :=
     IsSelfAdjoint.of_nonneg hh.1
   have ha : A.IsHermitian := by
     change star A = A at ha'
     exact ha'
   apply ha.posDef_iff_eigenvalues_pos.mpr
   have hp := (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R:=ℝ)
       (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) ha').1 hh
   change ∀ x ∈ spectrum ℝ A, 0 < x at hp
   rw [ha.spectrum_real_eq_range_eigenvalues] at hp
   intro i
   exact hp _ ⟨i,rfl⟩
lemma posSemidef_iff_ofMatrix (A : Matrix n n ℂ) :
 A.PosSemidef ↔ (0 ≤ (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ)) := by
 constructor
 · intro h
   have ha : IsSelfAdjoint (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) := by
     change star A = A
     exact h.isHermitian
   apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R:=ℝ) _ ha).2
   change ∀ x ∈ spectrum ℝ A, 0 ≤ x
   rw [h.isHermitian.spectrum_real_eq_range_eigenvalues]
   intro x hx; obtain ⟨i,rfl⟩ := hx
   exact Matrix.PosSemidef.eigenvalues_nonneg h i
 · intro h
   have ha' : IsSelfAdjoint (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) :=
     IsSelfAdjoint.of_nonneg h
   have ha : A.IsHermitian := by change star A = A at ha'; exact ha'
   apply ha.posSemidef_iff_eigenvalues_nonneg.mpr
   have q := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R:=ℝ)
     (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) ha').1 h
   change ∀ x ∈ spectrum ℝ A, 0 ≤ x at q
   rw [ha.spectrum_real_eq_range_eigenvalues] at q
   exact fun i => q _ ⟨i,rfl⟩
lemma ofMatrix_cfc_log (A : Matrix n n ℂ) (hA : A.IsHermitian) :
 CStarMatrix.ofMatrix (cfc Real.log A) =
  CFC.log (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) := by
  have hf : ContinuousOn Real.log (spectrum ℝ A) := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn _
  have hs : IsSelfAdjoint A := hA
  have ht : IsSelfAdjoint (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) := by
    change star A = A
    exact hA
  exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log A
     (hf:=hf) (hφ:= CStarMatrix.ofMatrixL.continuous) (ha:=hs) (hφa:=ht)

/-- The operator logarithm Jensen inequality transported back from CStarMatrix.
 It is a Loewner (quadratic form) inequality; the later trace perspective
 uses precisely this compression form rather than scalar concavity. -/
lemma cfc_log_concave_matrix (A B : Matrix n n ℂ) (hA : A.PosDef) (hB : B.PosDef)
 (a b : ℝ) (ha:0≤a) (hb:0≤b) (hab:a+b=1) :
 (cfc Real.log (a • A + b • B) - (a • cfc Real.log A + b • cfc Real.log B)).PosSemidef := by
  -- mixture strict (using a=0 cases)
  have hmix : (a • A + b • B).PosDef := by
    rcases lt_or_eq_of_le ha with ha'|ha0
    · rcases lt_or_eq_of_le hb with hb'|hb0
      · exact (Matrix.PosDef.smul hA ha').add (Matrix.PosDef.smul hB hb')
      · subst b
        have aa : a = 1 := by linarith
        simpa [aa] using hA
    · subst a
      have bb : b = 1 := by linarith
      simpa [bb] using hB
  apply (posSemidef_iff_ofMatrix
    (cfc Real.log (a • A + b • B) - (a • cfc Real.log A + b • cfc Real.log B))).2
  -- concave operator inequality
  have hx : (CStarMatrix.ofMatrix A : CStarMatrix n n ℂ) ∈
       {z : CStarMatrix n n ℂ | IsStrictlyPositive z} := ofMatrix_pos A hA
  have hy : (CStarMatrix.ofMatrix B : CStarMatrix n n ℂ) ∈
       {z : CStarMatrix n n ℂ | IsStrictlyPositive z} := ofMatrix_pos B hB
  have H := (CFC.concaveOn_log (A:= CStarMatrix n n ℂ)).2 hx hy ha hb hab
  rw [← sub_nonneg] at H
  change 0 ≤ (CStarMatrix.ofMatrix (cfc Real.log (a • A + b • B)) -
                (a • CStarMatrix.ofMatrix (cfc Real.log A) + b • CStarMatrix.ofMatrix (cfc Real.log B)) : CStarMatrix n n ℂ)
  rw [ofMatrix_cfc_log A hA.isHermitian, ofMatrix_cfc_log B hB.isHermitian,
      ofMatrix_cfc_log _ hmix.isHermitian]
  exact H
end SSAuxJoint

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/JointBridge.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Modular.lean
section
open scoped ComplexOrder
open Matrix
noncomputable section
namespace SSAuxMod
variable {n : Type*} [Fintype n] [DecidableEq n]
noncomputable local instance : ContinuousFunctionalCalculus ℝ (n → ℂ) IsSelfAdjoint := IsSelfAdjoint.instContinuousFunctionalCalculus

def diagStar : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ :=
 StarAlgHom.mk (Matrix.diagonalAlgHom ℂ) (by
  intro x
  ext i j
  by_cases h : i = j
  · subst j; simp [Matrix.diagonal, Matrix.star_apply]
  · simp [Matrix.diagonal, Matrix.star_apply, h, Ne.symm h])
lemma diag_cont : Continuous (diagStar (n:=n)) := by
 change Continuous (fun x : n → ℂ => Matrix.diagonal x)
 fun_prop

lemma cfc_diag (d : n → ℝ) (f : ℝ → ℝ) :
  cfc f (Matrix.diagonal (fun i => (d i : ℂ))) =
    Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
 let x : n → ℂ := fun i => (d i : ℂ)
 have hx : IsSelfAdjoint x := by
   change (fun i => star (x i)) = x
   funext i
   dsimp [x]
   simp
 have hmx : IsSelfAdjoint (diagStar (n:=n) x) := by
   rw [isSelfAdjoint_iff] at hx ⊢
   exact (map_star (diagStar (n:=n)) x) ▸ congrArg _ hx
 have hf : ContinuousOn f (spectrum ℝ x) := by
   rw [Pi.spectrum_eq]
   apply Set.Finite.continuousOn
   apply Set.finite_iUnion
   intro i
   have sub : spectrum ℝ (x i) ⊆ {d i} := by
     dsimp [x]
     exact CFC.spectrum_algebraMap_subset (A:=ℂ) (d i)
   exact (Set.finite_singleton _).subset sub
 have q := StarAlgHomClass.map_cfc (diagStar (n:=n)) f x
   (hf:=hf) (hφ:=diag_cont (n:=n)) (ha:=hx) (hφa:=hmx)
 change cfc f (diagStar (n:=n) x) = _
 rw [← q]
 change Matrix.diagonal (cfc f x) = _
 congr 1
 funext i
 -- use projection cfc? Pi map lemma or eval hom. cfc_apply for pi
 have qi : (cfc f x) i = cfc f (x i) := by
   have hu : ContinuousOn f (⋃ j, spectrum ℝ (x j)) := by
     rwa [Pi.spectrum_eq] at hf
   have z := cfc_map_pi (S:=ℂ) f x (hf:=hu) (ha:=hx)
     (ha' := (fun j => (by dsimp [x]; change star ((d j : ℂ)) = _; simp)))
   exact congrFun z i
 rw [qi]
 change cfc f ((algebraMap ℝ ℂ) (d i)) = _
 exact cfc_algebraMap (d i) f
end SSAuxMod
namespace SSAuxMod
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma cfc_conj (Z : Matrix n n ℂ) (hZ : Z.IsHermitian)
 (U : Matrix.unitaryGroup n ℂ) (f:ℝ→ℝ) :
 cfc f (((↑U : Matrix n n ℂ) * Z * star (↑U : Matrix n n ℂ))) =
   (↑U : Matrix n n ℂ) * cfc f Z * star (↑U : Matrix n n ℂ) := by
  let φ := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) U
  have hf : ContinuousOn f (spectrum ℝ Z) := by
    rw [hZ.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn _
  have hz : IsSelfAdjoint Z := hZ.isSelfAdjoint
  have ht : IsSelfAdjoint (φ Z) := by
    rw [isSelfAdjoint_iff] at hz ⊢
    exact (map_star φ Z) ▸ congrArg φ hz
  have q := StarAlgHomClass.map_cfc φ f Z (hf:=hf)
     (hφ:= by -- continuous innerAut
       change Continuous (fun X : Matrix n n ℂ => (↑U : Matrix n n ℂ) * X * star (↑U : Matrix n n ℂ)); fun_prop)
       (ha:= hz) (hφa:=ht)
  simpa [φ, Unitary.conjStarAlgAut_apply] using q.symm
end SSAuxMod
open scoped Kronecker
namespace SSAuxMod
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
lemma log_kron (P : Matrix n n ℂ) (Q : Matrix m m ℂ)
 (hp : P.PosDef) (hq : Q.PosDef) :
 cfc Real.log (P ⊗ₖ Q) =
   (cfc Real.log P) ⊗ₖ (1:Matrix m m ℂ) +
      (1:Matrix n n ℂ) ⊗ₖ (cfc Real.log Q) := by
 let U := hp.isHermitian.eigenvectorUnitary
 let V := hq.isHermitian.eigenvectorUnitary
 let d : n → ℝ := hp.isHermitian.eigenvalues
 let e : m → ℝ := hq.isHermitian.eigenvalues
 let D : Matrix n n ℂ := Matrix.diagonal (fun i => (d i : ℂ))
 let E : Matrix m m ℂ := Matrix.diagonal (fun i => (e i : ℂ))
 have pp : P = (↑U : Matrix n n ℂ) * D * star (↑U : Matrix n n ℂ) := by
   simpa [D, d, Function.comp_def, mul_assoc, Unitary.conjStarAlgAut_apply] using hp.isHermitian.spectral_theorem
 have qq : Q = (↑V : Matrix m m ℂ) * E * star (↑V : Matrix m m ℂ) := by
   simpa [E, e, Function.comp_def, mul_assoc, Unitary.conjStarAlgAut_apply] using hq.isHermitian.spectral_theorem
 let W : Matrix (n×m) (n×m) ℂ := (↑U : Matrix n n ℂ) ⊗ₖ (↑V : Matrix m m ℂ)
 have hwstar : star W = (star (↑U : Matrix n n ℂ)) ⊗ₖ (star (↑V : Matrix m m ℂ)) := by
   simp [W, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
 let W' : Matrix.unitaryGroup (n×m) ℂ := ⟨W, by
   constructor
   · rw [hwstar]
     dsimp [W]
     rw [← Matrix.mul_kronecker_mul]
     change (star (↑U : Matrix n n ℂ) * (↑U : Matrix n n ℂ)) ⊗ₖ
       (star (↑V : Matrix m m ℂ) * (↑V : Matrix m m ℂ)) = _
     rw [U.property.1, V.property.1, Matrix.one_kronecker_one]
   · rw [hwstar]
     dsimp [W]
     rw [← Matrix.mul_kronecker_mul]
     rw [U.property.2, V.property.2, Matrix.one_kronecker_one] ⟩
 have kron : P ⊗ₖ Q = W * (D ⊗ₖ E) * star W := by
   rw [pp, qq, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
   simp [W, hwstar]
 have diagk : D ⊗ₖ E = Matrix.diagonal (fun ij : n×m => ((d ij.1 * e ij.2 : ℝ) : ℂ)) := by
   dsimp [D, E]
   rw [Matrix.diagonal_kronecker_diagonal]
   ext i j
   by_cases h:i=j
   · subst j; simp [Matrix.diagonal, Complex.ofReal_mul]
   · simp [Matrix.diagonal, h]
 have hlogd : cfc Real.log D = Matrix.diagonal (fun i => (Real.log (d i) : ℂ)) :=
   cfc_diag d Real.log
 have hloge : cfc Real.log E = Matrix.diagonal (fun i => (Real.log (e i) : ℂ)) :=
   cfc_diag e Real.log
 have hlogk : cfc Real.log (D ⊗ₖ E) =
     (cfc Real.log D) ⊗ₖ (1:Matrix m m ℂ) +
        (1:Matrix n n ℂ) ⊗ₖ (cfc Real.log E) := by
   rw [diagk, cfc_diag (fun ij : n×m => d ij.1 * e ij.2) Real.log]
   rw [hlogd, hloge]
   ext ij kl
   by_cases h : ij=kl
   · subst kl
     simp [Matrix.add_apply, Matrix.diagonal, Matrix.kronecker_apply, Matrix.one_apply]
     change (Real.log (d ij.1 * e ij.2) : ℂ) = _
     norm_cast
     exact Real.log_mul
       (ne_of_gt ((hp.isHermitian.posDef_iff_eigenvalues_pos.mp hp) ij.1))
       (ne_of_gt ((hq.isHermitian.posDef_iff_eigenvalues_pos.mp hq) ij.2))
   · have hor : ij.1 ≠ kl.1 ∨ ij.2 ≠ kl.2 := by
       contrapose h; push_neg at h; exact Prod.ext h.1 h.2
     rcases hor with h1|h2
     · simp [Matrix.diagonal, Matrix.one_apply, Matrix.kronecker_apply, h, h1]
     · simp [Matrix.diagonal, Matrix.one_apply, Matrix.kronecker_apply, h, h2]
 have deherm : (D ⊗ₖ E).IsHermitian := by
   rw [diagk]
   rw [Matrix.IsHermitian.ext_iff]
   intro i j
   by_cases h:i=j
   · subst j; simp [Matrix.diagonal]
   · simp [Matrix.diagonal, h, Ne.symm h]
 have dherm : D.IsHermitian := by
   dsimp [D]; rw [Matrix.IsHermitian.ext_iff]
   intro i j; by_cases h:i=j
   · subst j; simp [Matrix.diagonal]
   · simp [Matrix.diagonal, h, Ne.symm h]
 have eherm : E.IsHermitian := by
   dsimp [E]; rw [Matrix.IsHermitian.ext_iff]
   intro i j; by_cases h:i=j
   · subst j; simp [Matrix.diagonal]
   · simp [Matrix.diagonal, h, Ne.symm h]
 have uc := cfc_conj (D ⊗ₖ E) deherm W' Real.log
 rw [kron]
 rw [cfc_conj (D ⊗ₖ E) deherm W' Real.log]
 rw [hlogk]
 rw [pp, qq, cfc_conj D dherm U Real.log, cfc_conj E eherm V Real.log]
 dsimp [W']
 rw [hwstar]
 -- expand distributivity and tensor products
 rw [mul_add, add_mul]
 dsimp [W]
 simp only [← Matrix.mul_kronecker_mul]
 simp [U.property.2, V.property.2]
end SSAuxMod

end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Modular.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/TraceNonneg.lean
section
open scoped ComplexOrder
open Matrix
namespace SSAuxJoint
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma trace_mul_nonneg (P Q : Matrix n n ℂ) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
  0 ≤ Complex.re (Matrix.trace (P * Q)) := by
  classical
  let U := hQ.isHermitian.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)
  have hd : Q = (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) U D := by
    simpa [D] using hQ.isHermitian.spectral_theorem
  rw [hd]
  rw [Unitary.conjStarAlgAut_apply]
  -- cycle U star to front
  -- P * (U * D * star U)
  have cyc : Matrix.trace (P * ((↑U : Matrix n n ℂ) * D * star (↑U : Matrix n n ℂ))) =
     Matrix.trace ((star (↑U : Matrix n n ℂ) * P * (↑U : Matrix n n ℂ)) * D) := by
    -- use trace cyclic rotations
    rw [← mul_assoc]
    -- P*U*D * starU
    rw [Matrix.trace_mul_cycle]
    -- starU * (P*U*D)
    simp [mul_assoc]
  rw [cyc]
  let R : Matrix n n ℂ := star (↑U : Matrix n n ℂ) * P * (↑U : Matrix n n ℂ)
  have hu : IsUnit (↑U : Matrix n n ℂ) :=
    isUnit_iff_exists_inv.mpr ⟨star (↑U : Matrix n n ℂ), Unitary.coe_mul_star_self U⟩
  have hv : IsUnit (star (↑U : Matrix n n ℂ)) := isUnit_star.mpr hu
  have hR : R.PosSemidef := by
    dsimp [R]
    have q := (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hv).mpr hP
    simpa using q
  change 0 ≤ Complex.re (Matrix.trace (R * D))
  simp [Matrix.trace, Matrix.mul_apply, D, Matrix.diagonal]
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg
  · exact (Complex.nonneg_iff.mp (Matrix.PosSemidef.diag_nonneg hR)).1
  · exact Matrix.PosSemidef.eigenvalues_nonneg hQ i
end SSAuxJoint

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/TraceNonneg.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Compress.lean
section
open scoped ComplexOrder
open Matrix
noncomputable section
namespace SSAuxComp
lemma log_compress
 {n m : Type*} [Fintype n] [Fintype m]
 [DecidableEq n] [DecidableEq m]
 (P : Matrix n n ℂ) (hP : P.PosDef)
 (K : Matrix n m ℂ) (hK : K.conjTranspose * K = (1 : Matrix m m ℂ)) :
 (cfc Real.log (K.conjTranspose * P * K) -
    K.conjTranspose * cfc Real.log P * K).PosSemidef := by
  classical
  -- the reflection in the range of K
  let E : Matrix n n ℂ := K * K.conjTranspose
  let S : Matrix n n ℂ := E + E - 1
  have e2 : E * E = E := by
    dsimp [E]
    calc
      (K * K.conjTranspose) * (K * K.conjTranspose) =
        K * (K.conjTranspose * K) * K.conjTranspose := by simp [Matrix.mul_assoc]
      _ = _ := by rw [hK]; simp [E]
  have eh : E.IsHermitian := by
    dsimp [E]
    exact Matrix.isHermitian_mul_conjTranspose_self K
  have sh : S.IsHermitian := by
    dsimp [S]
    exact (eh.add eh).sub (Matrix.isHermitian_one)
  have sk : S * K = K := by
    dsimp [S, E]
    simp [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hK]
  have ss : S * S = (1 : Matrix n n ℂ) := by
    dsimp [S]
    calc
      (E + E - 1) * (E + E - 1) =
        (E*E + E*E + (E*E + E*E)) - (E+E) - (E+E) + 1 := by noncomm_ring
      _ = 1 := by rw [e2]; noncomm_ring

  have sstar : star S = S := sh
  have sunit : IsUnit S := by
    -- self inverse
    exact isUnit_iff_exists_inv.mpr ⟨S, ss⟩
  let P' : Matrix n n ℂ := S * P * S
  have ppd : P'.PosDef := by
    dsimp [P']
    have := (Matrix.IsUnit.posDef_star_left_conjugate_iff (U:=S) (x:=P) sunit).2 hP
    -- theorem star S * P * S; star=S
    simpa [sstar] using this
  let Q : Matrix n n ℂ := ( (2:ℝ)⁻¹ ) • P + ((2:ℝ)⁻¹) • P'
  have coeff : (0:ℝ) ≤ (2:ℝ)⁻¹ := by norm_num
  have sumc : (2:ℝ)⁻¹ + (2:ℝ)⁻¹ = (1:ℝ) := by norm_num
  have qdef : Q.PosDef := by
    dsimp [Q]
    exact (Matrix.PosDef.smul hP (by norm_num)).add
      (Matrix.PosDef.smul ppd (by norm_num))
  have conc : (cfc Real.log Q -
       (((2:ℝ)⁻¹) • cfc Real.log P + ((2:ℝ)⁻¹) • cfc Real.log P')).PosSemidef :=
    SSAuxJoint.cfc_log_concave_matrix P P' hP ppd _ _ coeff coeff sumc
  have concK := Matrix.PosSemidef.conjTranspose_mul_mul_same conc K
  -- Formula log P' by conjugation, via intertwining
  have sp : P' * S = S * P := by
    dsimp [P']
    -- S*S=1
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ss, Matrix.mul_one]
  have logsp : cfc Real.log P' * S = S * cfc Real.log P :=
    SSAuxInter.cfc_mul_rect_eq P' P ppd.isHermitian hP.isHermitian S sp _
  have logp' : cfc Real.log P' = S * cfc Real.log P * S := by
    -- multiply right S (S^2=1)
    calc
      cfc Real.log P' = cfc Real.log P' * (1:Matrix n n ℂ) := by simp
      _ = cfc Real.log P' * (S*S) := by rw [ss]
      _ = (cfc Real.log P' * S) * S := by rw [Matrix.mul_assoc]
      _ = _ := by rw [logsp]
  have ks : K.conjTranspose * S = K.conjTranspose := by
    -- transpose sk
    have z := congrArg Matrix.conjTranspose sk
    -- star_mul etc
    simpa [Matrix.conjTranspose_mul, sh.eq] using z
  -- compressed operator A
  let A : Matrix m m ℂ := K.conjTranspose * P * K
  have aherm : A.IsHermitian := by
    dsimp [A]
    exact Matrix.isHermitian_conjTranspose_mul_mul K hP.isHermitian
  -- Q leaves K invariant and its compression is A
  have qk : Q * K = K * A := by
    dsimp [Q, P', A]
    -- pinching block fixes the range
    -- use sk twice
    change (((2:ℝ)⁻¹) • P + ((2:ℝ)⁻¹) • (S * P * S)) * K =
      K * (K.conjTranspose * P * K)
    -- the left is (P K + S P K)/2
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul]
    simp [Matrix.mul_assoc, sk]
    dsimp [S, E]
    simp [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
          Matrix.mul_assoc, hK, Matrix.smul_mul, Matrix.mul_smul]
    -- coefficients 1/2, central
    -- remaining scalar arithmetic
    module
  have logq : K.conjTranspose * cfc Real.log Q * K =
       cfc Real.log A :=
    SSAuxInter.compress_cfc_of_intertwine K hK Q A
      qdef.isHermitian aherm qk _
  have kp' : K.conjTranspose * cfc Real.log P' * K =
       K.conjTranspose * cfc Real.log P * K := by
    rw [logp']
    simp [Matrix.mul_assoc, sk]
    rw [← Matrix.mul_assoc, ks]
  -- expand the compressed concavity inequality
  -- use the two equal compressed pieces
  -- the signs commute with compression by associativity
  have eqfinal : K.conjTranspose * (cfc Real.log Q -
       (((2:ℝ)⁻¹) • cfc Real.log P + ((2:ℝ)⁻¹) • cfc Real.log P')) * K =
     cfc Real.log A - K.conjTranspose * cfc Real.log P * K := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [logq, kp']
    -- average of two same terms
    module
  rw [← eqfinal]
  exact concK

end SSAuxComp

end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Compress.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Transpose.lean
section
open scoped ComplexOrder
open Matrix
noncomputable section
namespace SSAuxT
lemma posDef_transpose {n:Type*} [Fintype n] [DecidableEq n]
 (A:Matrix n n ℂ) (hA:A.PosDef) : A.transpose.PosDef := by
  classical
  let U := hA.isHermitian.eigenvectorUnitary
  let d : n → ℝ := hA.isHermitian.eigenvalues
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (d i : ℂ))
  let W : Matrix n n ℂ := (star (↑U : Matrix n n ℂ)).transpose
  have hstar : star W = (↑U : Matrix n n ℂ).transpose := by
    -- star of map conj
    -- ext
    ext i j
    simp [W, Matrix.star_eq_conjTranspose, Matrix.conjTranspose, Matrix.transpose_apply,
      Matrix.map_apply]
  have hw1 : star W * W = 1 := by
    rw [hstar]
    dsimp [W]
    -- transpose of U? use property
    rw [← Matrix.transpose_mul]
    rw [U.property.1]
    simp
  have hw2 : W * star W = 1 := by
    rw [hstar]
    dsimp [W]
    rw [← Matrix.transpose_mul]
    rw [U.property.2]
    simp
  have wunit : IsUnit W :=
    isUnit_iff_exists_inv.mpr ⟨star W, hw2⟩
  have dpd : D.PosDef := by
    dsimp [D]
    apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast ((hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA) i)
  have ate : A.transpose = W * D * star W := by
    have sp := hA.isHermitian.spectral_theorem
    -- transpose equality
    -- sp: A = U * diag comp * star U
    have sp' := congrArg Matrix.transpose sp
    -- simplify transpose products
    --
    simpa [D, W, hstar, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.mul_assoc, d, U] using sp'
  rw [ate]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff (x:=D) wunit).2 dpd

lemma cfc_transpose {n:Type*} [Fintype n] [DecidableEq n]
 (A:Matrix n n ℂ) (hA:A.IsHermitian) (f:ℝ→ℝ) :
 (cfc f A).transpose = cfc f A.transpose := by
  classical
  -- diagonalize simultaneously as before
  let U := hA.eigenvectorUnitary
  let d : n → ℝ := hA.eigenvalues
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (d i : ℂ))
  let F : Matrix n n ℂ := Matrix.diagonal (fun i => (f (d i) : ℂ))
  let W : Matrix n n ℂ := (star (↑U : Matrix n n ℂ)).transpose
  have hstar : star W = (↑U : Matrix n n ℂ).transpose := by
    ext i j
    simp [W, Matrix.star_eq_conjTranspose, Matrix.conjTranspose, Matrix.transpose_apply,
      Matrix.map_apply]
  have hw1 : star W * W = 1 := by
    rw [hstar]; dsimp [W]
    rw [← Matrix.transpose_mul, U.property.1]; simp
  have hw2 : W * star W = 1 := by
    rw [hstar]; dsimp [W]
    rw [← Matrix.transpose_mul, U.property.2]; simp
  let W' : Matrix.unitaryGroup n ℂ := ⟨W, hw1, hw2⟩
  have sp : A = (↑U:Matrix n n ℂ) * D * star (↑U:Matrix n n ℂ) := by
    simpa [D, d, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.mul_assoc] using hA.spectral_theorem
  have asp : A.transpose = W * D * star W := by
    have z := congrArg Matrix.transpose sp
    simpa [D, W, hstar, Matrix.mul_assoc] using z
  have fc : cfc f A = (↑U:Matrix n n ℂ) * F * star (↑U:Matrix n n ℂ) := by
    rw [hA.cfc_eq f, Matrix.IsHermitian.cfc]
    simp [U, F, d, Function.comp_def, Unitary.conjStarAlgAut_apply]
  have dh : D.IsHermitian := by
    dsimp [D]
    rw [Matrix.IsHermitian.ext_iff]; intro i j
    by_cases h:i=j
    · subst j; simp [Matrix.diagonal]
    · simp [Matrix.diagonal, h, Ne.symm h]
  have df : cfc f D = F := by
    simpa [F] using (SSAuxMod.cfc_diag (n:=n) d f)
  rw [asp, SSAuxMod.cfc_conj D dh W' f]
  rw [df, fc]
  -- transpose fc
  simp [W', W, hstar, Matrix.transpose_add, Matrix.transpose_mul,
     F, Matrix.diagonal_transpose, Matrix.mul_assoc]
lemma cfc_log_inv {n:Type*} [Fintype n] [DecidableEq n]
 (A:Matrix n n ℂ) (hA:A.PosDef) :
 cfc Real.log A⁻¹ = - cfc Real.log A := by
  classical
  -- transport through the eigenbasis
  let U := hA.isHermitian.eigenvectorUnitary
  let d : n → ℝ := hA.isHermitian.eigenvalues
  let e : n → ℝ := fun i => (d i)⁻¹
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (d i : ℂ))
  let E : Matrix n n ℂ := Matrix.diagonal (fun i => (e i : ℂ))
  have de : D * E = (1:Matrix n n ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h:i=j
    · subst j; simp [D, E, e, d, Matrix.diagonal,
          (ne_of_gt ((hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA) i))]
    · simp [Matrix.diagonal, h]
  have ed : E * D = (1:Matrix n n ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h:i=j
    · subst j; simp [D, E, e, d, Matrix.diagonal,
          (ne_of_gt ((hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA) i))]
    · simp [Matrix.diagonal, h]
  have dinv : D⁻¹ = E := by
    exact (Matrix.inv_eq_right_inv de)
  have sp : A = (↑U:Matrix n n ℂ) * D * star (↑U:Matrix n n ℂ) := by
    simpa [D, d, Function.comp_def, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
      using hA.isHermitian.spectral_theorem
  have ainv : A⁻¹ = (↑U:Matrix n n ℂ) * E * star (↑U:Matrix n n ℂ) := by
    -- use inverse uniqueness from explicit products
    have r : A * ((↑U:Matrix n n ℂ) * E * star (↑U:Matrix n n ℂ)) = 1 := by
      rw [sp]
      calc
       ( (↑U:Matrix n n ℂ) * D * star (↑U:Matrix n n ℂ)) *
           ((↑U:Matrix n n ℂ) * E * star (↑U:Matrix n n ℂ)) =
          (↑U:Matrix n n ℂ) * (D * (star (↑U:Matrix n n ℂ) * (↑U:Matrix n n ℂ)) * E) * star (↑U:Matrix n n ℂ) := by noncomm_ring
       _ = 1 := by rw [U.property.1]; simp [de, Matrix.mul_assoc]
    have l : ((↑U:Matrix n n ℂ) * E * star (↑U:Matrix n n ℂ)) * A = 1 := by
      rw [sp]
      calc
       ((↑U:Matrix n n ℂ) * E * star (↑U:Matrix n n ℂ)) *
        ((↑U:Matrix n n ℂ) * D * star (↑U:Matrix n n ℂ)) =
          (↑U:Matrix n n ℂ) * (E * (star (↑U:Matrix n n ℂ) * (↑U:Matrix n n ℂ)) * D) * star (↑U:Matrix n n ℂ) := by noncomm_ring
       _ = 1 := by rw [U.property.1]; simp [ed, Matrix.mul_assoc]
    -- nonsing inverse
    exact (Matrix.inv_eq_right_inv r)
  have dh : D.IsHermitian := by
    dsimp [D]; rw [Matrix.IsHermitian.ext_iff]; intro i j
    by_cases h:i=j
    · subst j; simp [Matrix.diagonal]
    · simp [Matrix.diagonal, h, Ne.symm h]
  have eh : E.IsHermitian := by
    dsimp [E]; rw [Matrix.IsHermitian.ext_iff]; intro i j
    by_cases h:i=j
    · subst j; simp [Matrix.diagonal]
    · simp [Matrix.diagonal, h, Ne.symm h]
  have diaglog : cfc Real.log E = - cfc Real.log D := by
    rw [SSAuxMod.cfc_diag (n:=n) e Real.log, SSAuxMod.cfc_diag (n:=n) d Real.log]
    ext i j
    by_cases h:i=j
    · subst j
      simp [Matrix.diagonal, e, d,
        Real.log_inv]
    · simp [Matrix.diagonal, h]
  rw [ainv, SSAuxMod.cfc_conj E eh U Real.log]
  rw [sp, SSAuxMod.cfc_conj D dh U Real.log]
  rw [diaglog]
  simp [Matrix.mul_neg, Matrix.neg_mul]

end SSAuxT
end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Transpose.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Twirl.lean
section
noncomputable section
namespace SSAux
/-- The Boolean phases form a convenient finite unitary pinching family. -/
def eps (b : Bool) : ℂ := if b then -1 else 1
@[simp] lemma eps_false : eps false = 1 := rfl
@[simp] lemma eps_true : eps true = -1 := rfl
@[simp] lemma eps_not (b : Bool) : eps (!b) = - eps b := by cases b <;> simp [eps]
@[simp] lemma eps_sq (b : Bool) : eps b * eps b = 1 := by cases b <;> simp [eps]

variable {ι : Type*} [DecidableEq ι]
def flipAt (a : ι) (u : ι → Bool) : ι → Bool := fun i => if i = a then !(u i) else u i
@[simp] lemma flipAt_same (a : ι) (u : ι → Bool) : flipAt a u a = !(u a) := by simp [flipAt]
lemma flipAt_diff (a i : ι) (h : i ≠ a) (u : ι → Bool) : flipAt a u i = u i := by simp [flipAt, h]
lemma flipAt_invol (a : ι) (u : ι → Bool) : flipAt a (flipAt a u) = u := by
  funext i
  by_cases h : i = a
  · subst i; simp [flipAt]
  · simp [flipAt, h]
def flipPerm (a : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun := flipAt a
  invFun := flipAt a
  left_inv := flipAt_invol a
  right_inv := flipAt_invol a

variable [Fintype ι]
/-- Orthogonality of the Boolean diagonal characters, in the coefficient
field actually used by the matrices. -/
lemma sum_eps_mul_eps (a b : ι) :
    (∑ u : ι → Bool, eps (u a) * eps (u b)) =
      if a = b then (Fintype.card (ι → Bool) : ℂ) else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp [eps_sq]
  · simp only [h, ↓reduceIte]
    let g : (ι → Bool) → ℂ := fun u => eps (u a) * eps (u b)
    have flipneg (u : ι → Bool) : g (flipAt a u) = - g u := by
      dsimp [g]
      rw [flipAt_same, flipAt_diff a b (Ne.symm h)]
      rw [eps_not]
      ring
    have H := Equiv.sum_comp (flipPerm a) g
    change (∑ u : ι → Bool, g (flipAt a u)) = _ at H
    -- reindexing the finite family changes every term's sign
    calc
      (∑ u : ι → Bool, eps (u a) * eps (u b)) =
          ∑ u : ι → Bool, g u := rfl
      _ = 0 := by
        have hz : (∑ u : ι → Bool, g u) =
              - (∑ u : ι → Bool, g u) := by
          conv_lhs => rw [← H]
          simp_rw [flipneg]
          simp
        have ha' : (∑ u : ι → Bool, g u) +
              (∑ u : ι → Bool, g u) = 0 :=
          (add_eq_zero_iff_eq_neg.mpr hz)
        exact (add_self_eq_zero.mp ha')

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
/-- Conjugating a matrix by a diagonal sign unitary on its first subsystem;
we give the entry formula, which does not require any choices of bases. -/
def phaseTwist (u : ι → Bool) (T : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ := fun i j =>
      eps (u i.1) * T i j * eps (u j.1)

/-- Sum over all signs kills exactly the off-diagonal blocks. This is the
first (pinching) half of the finite-dimensional twirling proof of the
partial-trace channel. -/
lemma sum_phaseTwist (T : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι × κ) :
    (∑ u : ι → Bool, phaseTwist u T) i j =
      if i.1 = j.1
        then (Fintype.card (ι → Bool) : ℂ) * T i j
        else 0 := by
  classical
  simp only [Matrix.sum_apply, phaseTwist]
  -- the prefactor is the previous character sum
  calc
    (∑ u : ι → Bool, eps (u i.1) * T i j * eps (u j.1)) =
        (∑ u : ι → Bool, eps (u i.1) * eps (u j.1)) * T i j := by
          -- commute the scalar entry past the signs
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro u hu
          ring
    _ = _ := by
      rw [sum_eps_mul_eps]
      by_cases z : i.1 = j.1 <;> simp [z]

/-- The permutation part of the twirl makes all the diagonal blocks the
same.  This coefficient-free form is convenient: it works without choosing
an enumeration or the factorial of an empty type. -/
lemma card_mul_sum_perm_diag (T : Matrix (ι × κ) (ι × κ) ℂ)
    (a : ι) (d e : κ) :
    (Fintype.card ι : ℂ) *
        (∑ σ : Equiv.Perm ι, T (σ a, d) (σ a, e)) =
      (Fintype.card (Equiv.Perm ι) : ℂ) *
        (∑ x : ι, T (x,d) (x,e)) := by
  classical
  let r : ι → ℂ := fun b => ∑ σ : Equiv.Perm ι, T (σ b,d) (σ b,e)
  have const (b : ι) : r b = r a := by
    let τ : Equiv.Perm ι := Equiv.swap a b
    have HH := Equiv.sum_comp (Equiv.mulRight τ)
      (fun σ : Equiv.Perm ι => T (σ a,d) (σ a,e))
    -- its left terms are the b-row
    simpa [r, Equiv.Perm.mul_apply, τ, Equiv.swap_apply_left] using HH
  calc
    (Fintype.card ι : ℂ) * (∑ σ : Equiv.Perm ι, T (σ a,d) (σ a,e)) =
        ∑ b : ι, r b := by
          have csum : (∑ b : ι, r b) = Fintype.card ι • r a := by
            calc
              _ = ∑ _b : ι, r a := by
                apply Finset.sum_congr rfl
                intro b hb
                exact const b
              _ = Fintype.card ι • r a := by simp
          rw [csum]
          simp [r, nsmul_eq_mul]
    _ = ∑ σ : Equiv.Perm ι, ∑ b : ι, T (σ b,d) (σ b,e) := by
          change (∑ b : ι, ∑ σ : Equiv.Perm ι, T (σ b,d) (σ b,e)) = _
          rw [Finset.sum_comm]
    _ = ∑ σ : Equiv.Perm ι, ∑ x : ι, T (x,d) (x,e) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          simpa using
            (Equiv.sum_comp σ (fun x : ι => T (x,d) (x,e)))
    _ = _ := by simp

end SSAux
end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Twirl.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/DirectSum.lean
section
open scoped ComplexOrder Kronecker MatrixOrder
open Matrix
open scoped BigOperators
noncomputable section
namespace SSAuxDS
variable {n : Type*} [Fintype n] [DecidableEq n]
-- diagonal two block, on Sum
def diag2 (P Q : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks P 0 0 Q
-- stack two square maps
def col2 (U V : Matrix n n ℂ) : Matrix (n ⊕ n) n ℂ
 | Sum.inl i, j => U i j
 | Sum.inr i, j => V i j
@[simp] lemma col2_l (U V : Matrix n n ℂ) (i j:n) : col2 U V (Sum.inl i) j = U i j := rfl
@[simp] lemma col2_r (U V : Matrix n n ℂ) (i j:n) : col2 U V (Sum.inr i) j = V i j := rfl
lemma col2_ct (U V : Matrix n n ℂ) : (col2 U V).conjTranspose = fun i x => Sum.elim (fun j=> U.conjTranspose i j) (fun j=> V.conjTranspose i j) x := by
 ext i x
 rcases x with j|j <;> simp [Matrix.conjTranspose_apply, col2]
lemma ct_col2 (U V : Matrix n n ℂ) :
 (col2 U V).conjTranspose * col2 U V = U.conjTranspose * U + V.conjTranspose * V := by
 classical
 ext i j
 simp [Matrix.mul_apply, col2_ct, Fintype.sum_sum_type, Matrix.add_apply, col2]
lemma diag_col (P Q U V : Matrix n n ℂ) :
 diag2 P Q * col2 U V = col2 (P*U) (Q*V) := by
 ext (i|i) j <;> simp [diag2, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks, col2]
lemma col_ct_mul (U V : Matrix n n ℂ) (T W : Matrix n n ℂ) :
 (col2 U V).conjTranspose * col2 T W = U.conjTranspose*T + V.conjTranspose*W := by
 ext i j
 simp [Matrix.mul_apply, col2_ct, Fintype.sum_sum_type, col2, Matrix.add_apply]
lemma compress_diag (P Q U V : Matrix n n ℂ) :
 (col2 U V).conjTranspose * diag2 P Q * col2 U V =
   U.conjTranspose*P*U + V.conjTranspose*Q*V := by
 rw [Matrix.mul_assoc, diag_col, col_ct_mul]
 rw [Matrix.mul_assoc, Matrix.mul_assoc]

lemma diag2_herm {P Q : Matrix n n ℂ} (hP:P.IsHermitian) (hQ:Q.IsHermitian) :
 (diag2 P Q).IsHermitian := by
 exact Matrix.IsHermitian.fromBlocks hP (by simp) hQ

lemma diag2_posDef {P Q : Matrix n n ℂ} (hP:P.PosDef) (hQ:Q.PosDef) :
 (diag2 P Q).PosDef := by
 classical
 apply Matrix.PosDef.of_dotProduct_mulVec_pos (diag2_herm hP.isHermitian hQ.isHermitian)
 intro x hx
 let xl : n → ℂ := x ∘ Sum.inl
 let xr : n → ℂ := x ∘ Sum.inr
 have nz : xl ≠ 0 ∨ xr ≠ 0 := by
   by_contra hh
   push_neg at hh
   apply hx
   funext i
   rcases i with i|i
   · have q := congrFun hh.1 i; exact q
   · have q := congrFun hh.2 i; exact q
 have lp : 0 ≤ star xl ⬝ᵥ (P *ᵥ xl) :=
   (Matrix.PosSemidef.dotProduct_mulVec_nonneg hP.posSemidef) xl
 have rp : 0 ≤ star xr ⬝ᵥ (Q *ᵥ xr) :=
   (Matrix.PosSemidef.dotProduct_mulVec_nonneg hQ.posSemidef) xr
 have eqn : star x ⬝ᵥ (diag2 P Q *ᵥ x) =
       star xl ⬝ᵥ (P *ᵥ xl) + star xr ⬝ᵥ (Q *ᵥ xr) := by
   classical
   simp [diag2, Matrix.fromBlocks_mulVec, dotProduct,
     Fintype.sum_sum_type, xl, xr]
 rw [eqn]
 rcases nz with nz|nz
 · exact add_pos_of_pos_of_nonneg
      ((Matrix.PosDef.dotProduct_mulVec_pos hP) nz) rp
 · exact add_pos_of_nonneg_of_pos lp
      ((Matrix.PosDef.dotProduct_mulVec_pos hQ) nz)

-- injection columns
 def inlC : Matrix (n ⊕ n) n ℂ := col2 (1:Matrix n n ℂ) 0
 def inrC : Matrix (n ⊕ n) n ℂ := col2 0 (1:Matrix n n ℂ)
lemma diag_inl (P Q:Matrix n n ℂ) : diag2 P Q * inlC = inlC * P := by

 change diag2 P Q * col2 (1:Matrix n n ℂ) (0:Matrix n n ℂ) = _
 calc
  _ = col2 (P*1) (Q*0) := diag_col P Q _ _
  _ = col2 1 0 * P := by
    ext (i|i) j
    · change ((P*(1:Matrix n n ℂ)) : Matrix n n ℂ) i j = ∑ k:n, (1:Matrix n n ℂ) i k * P k j
      simp [Matrix.one_apply]
    · change ((Q*(0:Matrix n n ℂ)) : Matrix n n ℂ) i j = ∑ k:n, (0:Matrix n n ℂ) i k * P k j
      simp [Matrix.one_apply]
  _ = _ := rfl
lemma diag_inr (P Q:Matrix n n ℂ) : diag2 P Q * inrC = inrC * Q := by

 change diag2 P Q * col2 (0:Matrix n n ℂ) (1:Matrix n n ℂ) = _
 calc
  _ = col2 (P*0) (Q*1) := diag_col P Q _ _
  _ = col2 0 1 * Q := by
    ext (i|i) j
    · change ((P*(0:Matrix n n ℂ)) : Matrix n n ℂ) i j = ∑ k:n, (0:Matrix n n ℂ) i k * Q k j
      simp [Matrix.one_apply]
    · change ((Q*(1:Matrix n n ℂ)) : Matrix n n ℂ) i j = ∑ k:n, (1:Matrix n n ℂ) i k * Q k j
      simp [Matrix.one_apply]
  _ = _ := rfl
lemma inl_inr_expand (A : Matrix (n ⊕ n) (n ⊕ n) ℂ)
 (P Q : Matrix n n ℂ)
 (h1 : A * inlC = inlC * P) (h2 : A * inrC = inrC * Q) :
 A = diag2 P Q := by
 ext (i|i) (j|j)
 · have e := congrArg (fun M : Matrix (n ⊕ n) n ℂ => M (Sum.inl i) j) h1
   change (∑ k : n ⊕ n, A (Sum.inl i) k * inlC k j) =
      ∑ k:n, inlC (Sum.inl i) k * P k j at e
   simpa [inlC, col2, diag2, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply] using e
 · have e := congrArg (fun M : Matrix (n ⊕ n) n ℂ => M (Sum.inl i) j) h2
   change (∑ k : n ⊕ n, A (Sum.inl i) k * inrC k j) =
      ∑ k:n, inrC (Sum.inl i) k * Q k j at e
   simpa [inrC, col2, diag2, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply] using e
 · have e := congrArg (fun M : Matrix (n ⊕ n) n ℂ => M (Sum.inr i) j) h1
   change (∑ k : n ⊕ n, A (Sum.inr i) k * inlC k j) =
      ∑ k:n, inlC (Sum.inr i) k * P k j at e
   simpa [inlC, col2, diag2, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply] using e
 · have e := congrArg (fun M : Matrix (n ⊕ n) n ℂ => M (Sum.inr i) j) h2
   change (∑ k : n ⊕ n, A (Sum.inr i) k * inrC k j) =
      ∑ k:n, inrC (Sum.inr i) k * Q k j at e
   simpa [inrC, col2, diag2, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply] using e

lemma cfc_diag2 (P Q:Matrix n n ℂ) (hP:P.IsHermitian) (hQ:Q.IsHermitian) (f:ℝ→ℝ) :
 cfc f (diag2 P Q) = diag2 (cfc f P) (cfc f Q) := by
 have one := SSAuxInter.cfc_mul_rect_eq (diag2 P Q) P
    (diag2_herm hP hQ) hP inlC (diag_inl P Q) f
 have two := SSAuxInter.cfc_mul_rect_eq (diag2 P Q) Q
    (diag2_herm hP hQ) hQ inrC (diag_inr P Q) f
 exact inl_inr_expand (cfc f (diag2 P Q)) (cfc f P) (cfc f Q) one two
end SSAuxDS
namespace SSAuxDS
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma log_compress_two (P Q U V : Matrix n n ℂ)
 (hp:P.PosDef) (hq:Q.PosDef)
 (hk : U.conjTranspose*U + V.conjTranspose*V = (1:Matrix n n ℂ)) :
 (cfc Real.log (U.conjTranspose*P*U + V.conjTranspose*Q*V) -
   (U.conjTranspose*cfc Real.log P*U + V.conjTranspose*cfc Real.log Q*V)).PosSemidef := by
 let D : Matrix (n ⊕ n) (n ⊕ n) ℂ := diag2 P Q
 let K : Matrix (n ⊕ n) n ℂ := col2 U V
 have kd : K.conjTranspose * K = (1:Matrix n n ℂ) := by
   simpa [K, ct_col2] using hk
 have main := SSAuxComp.log_compress D (diag2_posDef hp hq) K kd
 have cd : cfc Real.log D = diag2 (cfc Real.log P) (cfc Real.log Q) :=
   cfc_diag2 P Q hp.isHermitian hq.isHermitian Real.log
 -- expose both compressed corners
 simpa [D, K, compress_diag, cd]
   using main
end SSAuxDS

end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/DirectSum.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/TwirlFull.lean
section
open scoped BigOperators Kronecker
open ComplexOrder
noncomputable section
namespace SSAux

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
-- κ only needed as an index; no sums over it in these definitions
variable [Fintype κ] [DecidableEq κ]

/-- Twirl permutation entry map. -/
def permTwist (s : Equiv.Perm ι) (T : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ := fun i j =>
  T (s i.1, i.2) (s j.1, j.2)

def fullTwist (s : Equiv.Perm ι) (u : ι → Bool)
    (T : Matrix (ι × κ) (ι × κ) ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  phaseTwist u (permTwist s T)

@[simp] lemma permTwist_apply (s : Equiv.Perm ι)
    (T : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι × κ) :
    permTwist s T i j = T (s i.1, i.2) (s j.1, j.2) := rfl

@[simp] lemma fullTwist_apply (s : Equiv.Perm ι) (u : ι → Bool)
    (T : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι × κ) :
    fullTwist s u T i j =
      eps (u i.1) * T (s i.1, i.2) (s j.1, j.2) * eps (u j.1) := rfl

/-- Sum of first diagonal blocks.  In users this is `traceLeft`; it is kept
as an entry formula here so this support file does not depend on the chosen
name for the partial trace. -/
def blockSum (T : Matrix (ι × κ) (ι × κ) ℂ) : Matrix κ κ ℂ :=
  fun d e => ∑ x : ι, T (x,d) (x,e)

@[simp] lemma blockSum_apply (T : Matrix (ι × κ) (ι × κ) ℂ) (d e : κ) :
    blockSum T d e = ∑ x : ι, T (x,d) (x,e) := rfl

/-- Coefficient-free full twirl identity.  We deliberately clear the
`card ι` denominator.  This version also remains true for the empty type;
for the channel argument `ι` is nonempty and the factor will be divided out
only in the scalar field. -/
lemma card_mul_sum_fullTwist (T : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι × κ) :
    (Fintype.card ι : ℂ) *
        ( (∑ s : Equiv.Perm ι, ∑ u : ι → Bool, fullTwist s u T) i j ) =
      (Fintype.card (Equiv.Perm ι) : ℂ) * (Fintype.card (ι → Bool) : ℂ) *
        (leftIdHom ι κ (blockSum T)) i j := by
  classical
  -- expose the two entry sums.  The inner sign sum is exactly the
  -- pinching identity of `sum_phaseTwist` applied to the permuted matrix.
  simp only [Matrix.sum_apply]
  have inner (s : Equiv.Perm ι) :
      (∑ u : ι → Bool, fullTwist s u T i j) =
        if i.1 = j.1
          then (Fintype.card (ι → Bool) : ℂ) * (permTwist s T) i j
          else 0 := by
    have HH := (sum_phaseTwist (ι:=ι) (κ:=κ)
      (permTwist s T) i j)
    rw [Matrix.sum_apply] at HH
    simpa [fullTwist] using HH
  by_cases hij : i.1 = j.1
  · -- diagonal output block
    -- use equality to rewrite only in the entries, not the pairs
    have P := card_mul_sum_perm_diag (ι:=ι) (κ:=κ) T i.1 i.2 j.2
    -- P : card ι * sum_s T (s i.1) = card_perm * sum_x ...
    -- first collect the inner sign sums
    calc
      (Fintype.card ι : ℂ) *
            (∑ s : Equiv.Perm ι, ∑ u : ι → Bool, fullTwist s u T i j) =
          (Fintype.card (ι → Bool) : ℂ) *
            ((Fintype.card ι : ℂ) *
              (∑ s : Equiv.Perm ι, T (s i.1, i.2) (s i.1, j.2))) := by
                -- substitute in every inner sum.  Now use `hij` to put both
                -- first coordinates equal.
                simp_rw [inner]
                simp [hij, permTwist]
                rw [← Finset.mul_sum]
                ring
      _ = (Fintype.card (ι → Bool) : ℂ) *
            ((Fintype.card (Equiv.Perm ι) : ℂ) *
              (∑ x : ι, T (x,i.2) (x,j.2))) := by rw [P]
      _ = (Fintype.card (Equiv.Perm ι) : ℂ) *
            (Fintype.card (ι → Bool) : ℂ) *
            (leftIdHom ι κ (blockSum T)) i j := by
              rw [leftIdHom_entry]
              simp [hij, blockSum]
              ring
  · -- off diagonal blocks are killed by the sign average
    have zero : (∑ s : Equiv.Perm ι, ∑ u : ι → Bool, fullTwist s u T i j) = 0 := by
      simp_rw [inner]
      simp [hij]
    rw [zero]
    simp [leftIdHom_entry, hij]

/-- Average version.  The only extra hypothesis is `Nonempty ι`, needed to
divide by the dimension. The other indexing types of the finite group have
canonical inhabitants. -/
lemma average_fullTwist [Nonempty ι] (T : Matrix (ι × κ) (ι × κ) ℂ) :
    (((Fintype.card (Equiv.Perm ι) : ℂ) *
        (Fintype.card (ι → Bool) : ℂ))⁻¹) •
       (∑ s : Equiv.Perm ι, ∑ u : ι → Bool, fullTwist s u T) =
      ((Fintype.card ι : ℂ)⁻¹) • leftIdHom ι κ (blockSum T) := by
  classical
  ext i j
  have H := card_mul_sum_fullTwist (ι:=ι) (κ:=κ) T i j
  -- none of the three finite dimensions disappear
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hp0 : Fintype.card (Equiv.Perm ι) ≠ 0 := Fintype.card_ne_zero
  have hp : (Fintype.card (Equiv.Perm ι) : ℂ) ≠ 0 := by exact_mod_cast hp0
  have hq0 : Fintype.card (ι → Bool) ≠ 0 := Fintype.card_ne_zero
  have hq : (Fintype.card (ι → Bool) : ℂ) ≠ 0 := by exact_mod_cast hq0
  -- evaluation of a scalar multiple is pointwise
  simp only [smul_eq_mul, Matrix.smul_apply]
  simp only [Matrix.sum_apply] at H ⊢
  -- a field computation applied to the coefficient-free identity
  calc
    (((Fintype.card (Equiv.Perm ι) : ℂ) *
        (Fintype.card (ι → Bool) : ℂ))⁻¹) *
        (∑ x, ∑ x_1, fullTwist x x_1 T i j) =
      ((Fintype.card ι : ℂ)⁻¹) *
        (leftIdHom ι κ (blockSum T)) i j := by
          -- `field_simp` reduces it to `H`
          field_simp
          -- the remaining equality is exactly H, with commuting factors
          simpa [mul_comm, mul_left_comm, mul_assoc] using H
    _ = _ := rfl

end SSAux
end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/TwirlFull.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Perspective.lean
section
set_option maxHeartbeats 1000000
open scoped ComplexOrder Kronecker MatrixOrder BigOperators
open Matrix
noncomputable section
namespace SSAuxPers
variable {n : Type*} [Fintype n] [DecidableEq n]
noncomputable def root (A : Matrix n n ℂ) : Matrix n n ℂ := cfc Real.sqrt A

lemma root_spec (A : Matrix n n ℂ) (hA : A.IsHermitian) :
 root A = (↑hA.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (fun i => (Real.sqrt (hA.eigenvalues i) : ℂ)) *
    star (↑hA.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [root, hA.cfc_eq Real.sqrt, Matrix.IsHermitian.cfc]
  simp [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.mul_assoc]

lemma root_posDef (A : Matrix n n ℂ) (hA : A.PosDef) : (root A).PosDef := by
  rw [root_spec A hA.isHermitian]
  have dpos : (Matrix.diagonal (fun i : n =>
       (Real.sqrt (hA.isHermitian.eigenvalues i) : ℂ))).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast (Real.sqrt_pos.2
      ((hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA) i))
  have hu : IsUnit (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) :=
    isUnit_iff_exists_inv.mpr ⟨star (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ),
      Unitary.coe_mul_star_self _⟩
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hu).mpr dpos

lemma root_sq (A : Matrix n n ℂ) (hA : A.PosDef) : root A * root A = A := by
  let U := hA.isHermitian.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (fun i =>
      (hA.isHermitian.eigenvalues i : ℂ))
  let S : Matrix n n ℂ := Matrix.diagonal (fun i =>
      (Real.sqrt (hA.isHermitian.eigenvalues i) : ℂ))
  have Ur : star (↑U : Matrix n n ℂ) * (↑U : Matrix n n ℂ) = 1 := U.property.1
  have SS : S*S = D := by
    dsimp [S, D]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases q:i=j
    · subst j
      simp [Matrix.diagonal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (le_of_lt
          ((hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA) i))]
    · simp [Matrix.diagonal, q]
  have Asp : A = (↑U : Matrix n n ℂ) * D * star (↑U : Matrix n n ℂ) := by
    simpa [D, U, Function.comp_def, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
      using hA.isHermitian.spectral_theorem
  have Rsp : root A = (↑U : Matrix n n ℂ) * S * star (↑U : Matrix n n ℂ) := by
    simpa [U, S] using root_spec A hA.isHermitian
  rw [Rsp, Asp]
  calc
    ((↑U : Matrix n n ℂ) * S * star (↑U : Matrix n n ℂ)) *
        ((↑U : Matrix n n ℂ) * S * star (↑U : Matrix n n ℂ)) =
        (↑U : Matrix n n ℂ) * (S * (star (↑U : Matrix n n ℂ) *
             (↑U : Matrix n n ℂ)) * S) * star (↑U : Matrix n n ℂ) := by noncomm_ring
    _ = _ := by rw [Ur]; simp [SS, Matrix.mul_assoc]

lemma root_star (A : Matrix n n ℂ) (hA : A.PosDef) : star (root A) = root A := by
  exact (root_posDef A hA).isHermitian
lemma root_conj (A : Matrix n n ℂ) (hA : A.PosDef) : (root A)ᴴ = root A :=
  (root_posDef A hA).isHermitian.eq

lemma root_mul_inv (A : Matrix n n ℂ) (hA:A.PosDef) :
 root A * (root A)⁻¹ = 1 :=
 Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (root_posDef A hA).isUnit)
lemma inv_mul_root (A : Matrix n n ℂ) (hA:A.PosDef) :
 (root A)⁻¹ * root A = 1 :=
 Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (root_posDef A hA).isUnit)
lemma ainv_roots (A : Matrix n n ℂ) (hA:A.PosDef) :
 A⁻¹ = (root A)⁻¹ * (root A)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  calc
    A * ((root A)⁻¹ * (root A)⁻¹) =
       (root A * root A) * ((root A)⁻¹ * (root A)⁻¹) := by rw [root_sq A hA]
    _ = (root A) * (root A * (root A)⁻¹) * (root A)⁻¹ := by noncomm_ring
    _ = 1 := by rw [root_mul_inv A hA, Matrix.mul_one]; exact root_mul_inv A hA
lemma invroot_A_invroot (A:Matrix n n ℂ) (hA:A.PosDef) :
 (root A)⁻¹ * A * (root A)⁻¹ = 1 := by
 calc
  (root A)⁻¹ * A * (root A)⁻¹ =
    (root A)⁻¹ * (root A * root A) * (root A)⁻¹ := by rw [root_sq A hA]
  _ = 1 := by simp [Matrix.mul_assoc, inv_mul_root A hA, root_mul_inv A hA]
lemma root_Ainv_root (A:Matrix n n ℂ) (hA:A.PosDef) :
 root A * A⁻¹ * root A = 1 := by
 rw [ainv_roots A hA]
 simp [Matrix.mul_assoc, inv_mul_root A hA, root_mul_inv A hA]
lemma invroot_sq (A:Matrix n n ℂ) (hA:A.PosDef) :
 (root A)⁻¹ * (root A)⁻¹ = A⁻¹ := (ainv_roots A hA).symm
lemma invroot_conj (A:Matrix n n ℂ) (hA:A.PosDef) :
 ((root A)⁻¹)ᴴ = (root A)⁻¹ := by
 rw [Matrix.conjTranspose_nonsing_inv, root_conj A hA]

noncomputable def rop (T : Matrix n n ℂ) : Matrix (n×n) (n×n) ℂ :=
  (1 : Matrix n n ℂ) ⊗ₖ T.transpose
lemma rop_ct (T:Matrix n n ℂ) : (rop T)ᴴ = rop Tᴴ := by
  rw [rop, Matrix.conjTranspose_kronecker]
  -- conjugate transpose of transpose commutes
  unfold rop
  ext i j
  simp [Matrix.conjTranspose, Matrix.transpose_apply, Matrix.one_apply,
    Matrix.map_apply]
lemma rop_mul (S T:Matrix n n ℂ) : rop S * rop T = rop (T*S) := by
  -- transposes reverse
  rw [rop, rop, rop]
  rw [← Matrix.mul_kronecker_mul]
  simp [Matrix.transpose_mul]

lemma one_kron (T:Matrix n n ℂ) :
 (1:Matrix (n×n) (n×n) ℂ) =
   (1:Matrix n n ℂ) ⊗ₖ (1:Matrix n n ℂ) := by
  symm; exact Matrix.one_kronecker_one

lemma kron_rop_conj (L T : Matrix n n ℂ) :
 (rop T)ᴴ * (L ⊗ₖ (1:Matrix n n ℂ)) * rop T =
   L ⊗ₖ (T*Tᴴ).transpose := by
 rw [rop_ct, rop, rop]
 rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
 simp [Matrix.transpose_mul, Matrix.mul_assoc]

lemma kron_inv_conj (B A T : Matrix n n ℂ) :
 (rop T)ᴴ * (B ⊗ₖ A.transpose) * rop T =
    B ⊗ₖ (T * A * Tᴴ).transpose := by
 rw [rop_ct, rop, rop]
 rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
 simp [Matrix.transpose_mul, Matrix.mul_assoc]

lemma rop_sum_ct (T Z:Matrix n n ℂ) :
 (rop T)ᴴ * rop T + (rop Z)ᴴ * rop Z =
   (1:Matrix n n ℂ) ⊗ₖ (T*Tᴴ + Z*Zᴴ).transpose := by
 rw [rop_ct, rop_mul, rop_ct, rop_mul]
 -- rop (T * Tᴴ)? order
 unfold rop
 rw [Matrix.transpose_add]
 rw [Matrix.kronecker_add]

lemma log_rel (B A:Matrix n n ℂ) (hB:B.PosDef) (hA:A.PosDef) :
 cfc Real.log (B ⊗ₖ (A⁻¹).transpose) =
   (cfc Real.log B) ⊗ₖ (1:Matrix n n ℂ) -
       (1:Matrix n n ℂ) ⊗ₖ (cfc Real.log A).transpose := by
 have tpos : (A⁻¹).transpose.PosDef :=
   SSAuxT.posDef_transpose _ (Matrix.PosDef.inv hA)
 rw [SSAuxMod.log_kron B (A⁻¹).transpose hB tpos]
 rw [← SSAuxT.cfc_transpose A⁻¹ (Matrix.PosDef.inv hA).isHermitian Real.log]
 rw [SSAuxT.cfc_log_inv A hA]
 ext i j; simp [Matrix.sub_apply, Matrix.add_apply]; ring

noncomputable def vec (Z:Matrix n n ℂ) : n×n → ℂ := fun i => Z i.1 i.2
lemma quad_kron (Z L T:Matrix n n ℂ) :
 star (vec Z) ⬝ᵥ ((L ⊗ₖ T.transpose) *ᵥ vec Z) =
    Matrix.trace (Zᴴ * L * Z * T) := by
 classical
 -- expand all four sums
 simp [vec, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.trace,
       Matrix.kronecker_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
       Finset.mul_sum, Finset.sum_mul]
 -- reorder the four independent indices
 have swap4 (f : n → n → n → n → ℂ) :
     (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) =
       ∑ j, ∑ l, ∑ k, ∑ i, f i j k l := by
   calc
    _ = ∑ j, ∑ i, ∑ k, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ j, (∑ k, ∑ i, ∑ l, f i j k l) := by
       apply Finset.sum_congr rfl
       intro j hj
       exact Finset.sum_comm
    _ = ∑ j, (∑ k, ∑ l, ∑ i, f i j k l) := by
       apply Finset.sum_congr rfl
       intro j hj
       apply Finset.sum_congr rfl
       intro k hk
       exact Finset.sum_comm
    _ = ∑ j, (∑ l, ∑ k, ∑ i, f i j k l) := by
       apply Finset.sum_congr rfl
       intro j hj
       exact Finset.sum_comm
 -- pointwise commute the two last complex factors, then permute the sums
 calc
  (∑ i, ∑ j, ∑ k, ∑ l,
       (starRingEnd ℂ) (Z i j) * (L i k * T l j * Z k l)) =
    ∑ i, ∑ j, ∑ k, ∑ l,
       (starRingEnd ℂ) (Z i j) * (L i k * (Z k l * T l j)) := by
       apply Finset.sum_congr rfl; intro i hi
       apply Finset.sum_congr rfl; intro j hj
       apply Finset.sum_congr rfl; intro k hk
       apply Finset.sum_congr rfl; intro l hl
       ring
  _ = ∑ j, ∑ l, ∑ k, ∑ i,
       (starRingEnd ℂ) (Z i j) * (L i k * (Z k l * T l j)) :=
       swap4 (fun i j k l =>
         (starRingEnd ℂ) (Z i j) * (L i k * (Z k l * T l j)))
  _ = _ := by
       apply Finset.sum_congr rfl; intro j hj
       apply Finset.sum_congr rfl; intro l hl
       apply Finset.sum_congr rfl; intro k hk
       apply Finset.sum_congr rfl; intro i hi
       ring

lemma cyc_root (A L:Matrix n n ℂ) (hA:A.PosDef) :
 Matrix.trace ((root A)ᴴ * L * root A) = Matrix.trace (A * L) := by
 rw [root_conj A hA]
 rw [Matrix.trace_mul_cycle]
 rw [root_sq A hA]
lemma expect_rel (B A:Matrix n n ℂ) (hB:B.PosDef) (hA:A.PosDef) :
 star (vec (root A)) ⬝ᵥ
    (cfc Real.log (B ⊗ₖ (A⁻¹).transpose) *ᵥ vec (root A)) =
  - Matrix.trace (A * cfc Real.log A - A * cfc Real.log B) := by
 let z := vec (root A)
 let LA := cfc Real.log A
 let LB := cfc Real.log B
 rw [log_rel B A hB hA]
 rw [Matrix.sub_mulVec, dotProduct_sub]
 have e1 := quad_kron (root A) LB (1:Matrix n n ℂ)
 simp at e1
 have e2 := quad_kron (root A) (1:Matrix n n ℂ) LA
 change star (vec (root A)) ⬝ᵥ ((LB ⊗ₖ (1:Matrix n n ℂ)) *ᵥ vec (root A)) -
      star (vec (root A)) ⬝ᵥ (((1:Matrix n n ℂ) ⊗ₖ LA.transpose) *ᵥ vec (root A)) = _
 rw [e1, e2]
 -- identify the two traces
 have q1 : Matrix.trace ((root A)ᴴ * LB * root A * (1:Matrix n n ℂ)) =
       Matrix.trace (A * LB) := by simp [cyc_root A LB hA]
 have q2 : Matrix.trace ((root A)ᴴ * (1:Matrix n n ℂ) * root A * LA) =
       Matrix.trace (A * LA) := by
   simp [root_conj A hA, root_sq A hA]
 rw [cyc_root A LB hA, q2]
 simp [Matrix.trace_sub]
 ring

end SSAuxPers

end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Perspective.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/TwirlUnitary.lean
section
open scoped BigOperators Kronecker
open ComplexOrder
noncomputable section
namespace SSAux
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

def pairPerm (s : Equiv.Perm ι) : (ι × κ) ≃ (ι × κ) :=
  Equiv.prodCongr s (Equiv.refl κ)
@[simp] lemma pairPerm_apply (s : Equiv.Perm ι) (i : ι × κ) :
    pairPerm (κ:=κ) s i = (s i.1, i.2) := rfl
@[simp] lemma pairPerm_symm (s : Equiv.Perm ι) :
    (pairPerm (κ:=κ) s).symm = pairPerm (κ:=κ) s.symm := rfl

def permU (s : Equiv.Perm ι) : Matrix (ι × κ) (ι × κ) ℂ :=
  (pairPerm (κ:=κ) s).toPEquiv.toMatrix

lemma permU_mul (s : Equiv.Perm ι) (T : Matrix (ι × κ) (ι × κ) ℂ) :
    permU (κ:=κ) s * T = T.submatrix (pairPerm (κ:=κ) s) (Equiv.refl _) := by
  simpa [permU] using (PEquiv.toMatrix_toPEquiv_mul (α:=ℂ)
    (M:=T) (pairPerm (κ:=κ) s))
lemma mul_permU (s : Equiv.Perm ι) (T : Matrix (ι × κ) (ι × κ) ℂ) :
    T * permU (κ:=κ) s = T.submatrix (Equiv.refl _) (pairPerm (κ:=κ) s).symm := by
  simpa [permU] using (PEquiv.mul_toMatrix_toPEquiv (α:=ℂ)
    (M:=T) (pairPerm (κ:=κ) s))

lemma permTwist_eq (s : Equiv.Perm ι) (T : Matrix (ι × κ) (ι × κ) ℂ) :
    permTwist s T = permU (κ:=κ) s * T * permU (κ:=κ) s.symm := by
  ext i j
  rw [permU_mul, mul_permU]
  rfl

@[simp] lemma permU_star (s : Equiv.Perm ι) :
    star (permU (κ:=κ) s) = permU (κ:=κ) s.symm := by
  classical
  ext i j
  change star ((permU (κ:=κ) s) j i) = (permU (κ:=κ) s.symm) i j
  simp only [permU, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, pairPerm_apply]
  change star (if (s j.1, j.2) = i then (1:ℂ) else 0) =
    (if (s.symm i.1, i.2) = j then 1 else 0)
  have iff : (s j.1, j.2) = i ↔ (s.symm i.1, i.2) = j := by
    constructor
    · intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact Prod.ext (by simpa using (congrArg s.symm h1).symm) h2.symm
    · intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact Prod.ext (by simpa using (congrArg s h1).symm) h2.symm
  by_cases h : (s j.1, j.2) = i
  · have k := iff.mp h
    simp [h, k]
  · have k : ¬ (s.symm i.1, i.2) = j := by tauto
    simp [h, k]

@[simp] lemma permU_mul_inv (s : Equiv.Perm ι) :
    permU (κ:=κ) s * permU (κ:=κ) s.symm = 1 := by
  classical
  rw [permU_mul]
  ext i j
  simp [Matrix.submatrix, permU, PEquiv.toMatrix_apply, Matrix.one_apply]
@[simp] lemma permU_inv_mul (s : Equiv.Perm ι) :
    permU (κ:=κ) s.symm * permU (κ:=κ) s = 1 := by
  simpa using (permU_mul_inv (κ:=κ) s.symm)

def phaseD (u : ι → Bool) : Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.diagonal (fun i => eps (u i.1))

@[simp] lemma phaseD_star (u : ι → Bool) : star (phaseD (κ:=κ) u) = phaseD (κ:=κ) u := by
  classical
  ext i j
  change star ((phaseD (κ:=κ) u) j i) = phaseD (κ:=κ) u i j
  by_cases h : j = i
  · subst j
    cases hbool : u i.1 <;> simp [phaseD, eps, hbool]
  · have h' : i ≠ j := Ne.symm h
    simp [phaseD, Matrix.diagonal, h, h']
@[simp] lemma phaseD_sq (u : ι → Bool) :
    phaseD (κ:=κ) u * phaseD (κ:=κ) u = 1 := by
  classical
  rw [phaseD, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j; simp [eps_sq]
  · simp [Matrix.diagonal, h]

lemma phaseTwist_eq (u : ι → Bool) (T : Matrix (ι × κ) (ι × κ) ℂ) :
    phaseTwist u T = phaseD (κ:=κ) u * T * phaseD (κ:=κ) u := by
  classical
  ext i j
  change eps (u i.1) * T i j * eps (u j.1) = _
  change _ = (Matrix.diagonal (fun i : ι×κ => eps (u i.1)) * T *
    Matrix.diagonal (fun i : ι×κ => eps (u i.1))) i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

def twistU (s : Equiv.Perm ι) (u : ι → Bool) : Matrix (ι × κ) (ι × κ) ℂ :=
  phaseD (κ:=κ) u * permU (κ:=κ) s

@[simp] lemma twistU_star (s : Equiv.Perm ι) (u : ι → Bool) :
    star (twistU (κ:=κ) s u) =
      permU (κ:=κ) s.symm * phaseD (κ:=κ) u := by
  rw [twistU, star_mul, phaseD_star, permU_star]
@[simp] lemma twistU_star_mul (s : Equiv.Perm ι) (u : ι → Bool) :
    star (twistU (κ:=κ) s u) * twistU (κ:=κ) s u = 1 := by
  rw [twistU_star, twistU]
  calc
    permU (κ:=κ) s.symm * phaseD (κ:=κ) u *
      (phaseD (κ:=κ) u * permU (κ:=κ) s) =
      permU (κ:=κ) s.symm * (phaseD (κ:=κ) u * phaseD (κ:=κ) u) *
        permU (κ:=κ) s := by noncomm_ring
    _ = 1 := by simp
@[simp] lemma twistU_mul_star (s : Equiv.Perm ι) (u : ι → Bool) :
    twistU (κ:=κ) s u * star (twistU (κ:=κ) s u) = 1 := by
  rw [twistU_star, twistU]
  -- reassociate the permutation first
  calc
    (phaseD (κ:=κ) u * permU (κ:=κ) s) *
      (permU (κ:=κ) s.symm * phaseD (κ:=κ) u) =
       phaseD (κ:=κ) u * (permU (κ:=κ) s * permU (κ:=κ) s.symm) * phaseD (κ:=κ) u := by noncomm_ring
    _ = 1 := by simp

def twistUnitary (s : Equiv.Perm ι) (u : ι → Bool) :
    unitary (Matrix (ι × κ) (ι × κ) ℂ) :=
  ⟨twistU (κ:=κ) s u, twistU_star_mul s u, twistU_mul_star s u⟩

lemma fullTwist_eq_conj (s : Equiv.Perm ι) (u : ι → Bool)
    (T : Matrix (ι × κ) (ι × κ) ℂ) :
  fullTwist s u T =
    ((Unitary.conjStarAlgAut ℂ (Matrix (ι × κ) (ι × κ) ℂ))
      (twistUnitary (κ:=κ) s u)) T := by
  change fullTwist s u T = twistU (κ:=κ) s u * T * star (twistU (κ:=κ) s u)
  rw [twistU_star, twistU, fullTwist, phaseTwist_eq, permTwist_eq]
  noncomm_ring

lemma continuous_twistAut (s : Equiv.Perm ι) (u : ι → Bool) :
    Continuous ((Unitary.conjStarAlgAut ℂ (Matrix (ι × κ) (ι × κ) ℂ))
      (twistUnitary (κ:=κ) s u)) := by
  change Continuous (fun T : Matrix (ι × κ) (ι × κ) ℂ =>
    twistU (κ:=κ) s u * T * star (twistU (κ:=κ) s u))
  fun_prop

lemma fullTwist_cfc (s : Equiv.Perm ι) (u : ι → Bool)
    (S : Matrix (ι × κ) (ι × κ) ℂ) (hS : S.IsHermitian) (f : ℝ → ℝ) :
    fullTwist s u (cfc f S) = cfc f (fullTwist s u S) := by
  rw [fullTwist_eq_conj, fullTwist_eq_conj]
  let Φ := ((Unitary.conjStarAlgAut ℂ (Matrix (ι × κ) (ι × κ) ℂ))
      (twistUnitary (κ:=κ) s u))
  have hf : ContinuousOn f (spectrum ℝ S) := by
    rw [hS.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn _
  have hself : IsSelfAdjoint S := hS.isSelfAdjoint
  have hm : IsSelfAdjoint (Φ S) := by
    rw [isSelfAdjoint_iff] at hself ⊢
    exact (map_star Φ S) ▸ congrArg Φ hself
  exact StarAlgHomClass.map_cfc Φ f S (hf:=hf)
    (hφ:=continuous_twistAut (κ:=κ) s u) (ha:=hself) (hφa:=hm)

lemma trace_fullTwist (s : Equiv.Perm ι) (u : ι → Bool)
    (T : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix.trace (fullTwist s u T) = Matrix.trace T := by
  rw [fullTwist_eq_conj]
  change Matrix.trace (twistU (κ:=κ) s u * T * star (twistU (κ:=κ) s u)) = _
  rw [Matrix.trace_mul_cycle]
  rw [twistU_star_mul]
  rw [Matrix.one_mul]

lemma trace_mul_fullTwist_cfc (s : Equiv.Perm ι) (u : ι → Bool)
    (X Y : Matrix (ι × κ) (ι × κ) ℂ) (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (fullTwist s u X * cfc f (fullTwist s u Y)) =
      Matrix.trace (X * cfc f Y) := by
  rw [← fullTwist_cfc s u Y hY]
  have mult : fullTwist s u X * fullTwist s u (cfc f Y) =
      fullTwist s u (X * cfc f Y) := by
    simp_rw [fullTwist_eq_conj]
    exact (map_mul _ _ _).symm
  rw [mult]
  exact trace_fullTwist s u _

end SSAux
end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/TwirlUnitary.lean

-- BEGIN INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Convex.lean
section
set_option maxHeartbeats 2000000
open scoped ComplexOrder Kronecker MatrixOrder BigOperators
open Matrix
noncomputable section
namespace SSAuxPers
variable {n : Type*} [Fintype n] [DecidableEq n]

-- right multiplication on the vectorized Hilbert--Schmidt space is an ordinary matrix
lemma rop_mulVec (Z T : Matrix n n ℂ) :
    rop T *ᵥ vec Z = vec (Z*T) := by
  classical
  ext i
  rcases i with ⟨i,j⟩
  simp [rop, vec, Matrix.mulVec, Matrix.mul_apply,
        Matrix.kronecker_apply, Matrix.transpose_apply, dotProduct,
        Fintype.sum_prod_type, Matrix.one_apply]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Moving a rectangular adjoint across the Hilbert space scalar product. -/
lemma dot_ct (m : Type*) [Fintype m] [DecidableEq m]
    (U : Matrix m n ℂ) (z : m → ℂ) (w : n → ℂ) :
    star w ⬝ᵥ (Uᴴ *ᵥ z) = star (U *ᵥ w) ⬝ᵥ z := by
  classical
  simp [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply,
        Finset.mul_sum, star_sum]
  -- distribute the final scalar and commute the two independent indices
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma dot_mul (S : Matrix n n ℂ) (U : Matrix n n ℂ) (z : n → ℂ) :
    star z ⬝ᵥ ((Uᴴ * S * U) *ᵥ z) =
      star (U *ᵥ z) ⬝ᵥ (S *ᵥ (U *ᵥ z)) := by
  rw [← Matrix.mulVec_mulVec z (Uᴴ * S) U]
  rw [← Matrix.mulVec_mulVec (U *ᵥ z) Uᴴ S]
  exact dot_ct n U _ _

-- simple scalar handling for a real coefficient regarded as a complex one
lemma real_smul_as_complex (r : ℝ) (A : Matrix n n ℂ) :
    r • A = (r : ℂ) • A := by
  ext i j
  simp [RCLike.real_smul_eq_coe_mul]

lemma scale_root_vec (r : ℝ) (Z : Matrix n n ℂ) :
    vec ((r:ℂ) • Z) = (r:ℂ) • vec Z := by rfl

-- algebra of the normalising columns
lemma norm_col (A C : Matrix n n ℂ)
    (hA : A.PosDef) (hC : C.PosDef)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
 let AB : Matrix n n ℂ := a • A + b • C
 let TA : Matrix n n ℂ :=
      (Real.sqrt a : ℂ) • ((root AB)⁻¹ * root A)
 let TC : Matrix n n ℂ :=
      (Real.sqrt b : ℂ) • ((root AB)⁻¹ * root C)
 TA * TAᴴ + TC * TCᴴ = (1 : Matrix n n ℂ) := by
  classical
  dsimp
  -- keep names short in the calculation
  let P : Matrix n n ℂ := a • A + b • C
  have hp : P.PosDef :=
    (Matrix.PosDef.smul hA ha).add (Matrix.PosDef.smul hC hb)
  let R : Matrix n n ℂ := root P
  let S : Matrix n n ℂ := root A
  let T : Matrix n n ℂ := root C
  have Rc : Rᴴ = R := root_conj P hp
  have Si : Sᴴ = S := root_conj A hA
  have Ti : Tᴴ = T := root_conj C hC
  have As : S*S = A := root_sq A hA
  have Cs : T*T = C := root_sq C hC
  have Ri : (R⁻¹)ᴴ = R⁻¹ := invroot_conj P hp
  have invP : R⁻¹ * P * R⁻¹ = (1:Matrix n n ℂ) := invroot_A_invroot P hp
  have aa : (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = (a:ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (le_of_lt ha)
  have bb : (Real.sqrt b : ℂ) * (Real.sqrt b : ℂ) = (b:ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (le_of_lt hb)
  change ((Real.sqrt a : ℂ) • (R⁻¹ * S)) *
          (((Real.sqrt a : ℂ) • (R⁻¹ * S))ᴴ) +
        ((Real.sqrt b : ℂ) • (R⁻¹ * T)) *
          (((Real.sqrt b : ℂ) • (R⁻¹ * T))ᴴ) = _
  -- conjugate transpose the scalar products then collect the middle terms
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul]
  -- simp turns conjugates of real scalars into themselves
  -- try assemble by rewriting self-adjointness
  simp [Rc, Ri, Si, Ti]
  simp only [smul_smul]
  have aar : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt (le_of_lt ha)
  have bbr : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt (le_of_lt hb)
  rw [aar, bbr]
  -- collect the two middle squares
  have mid :
      a • (R⁻¹ * S * (S * R⁻¹)) +
        b • (R⁻¹ * T * (T * R⁻¹)) =
        R⁻¹ * ((a • (S*S)) + (b • (T*T))) * R⁻¹ := by
      simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_assoc]
  rw [mid, As, Cs]
  -- the real linear combination in the middle is exactly P
  exact invP

/-- Each normalized column carries the inverse first density to the inverse
of the barycentre, with its scalar weight. -/
lemma col_inv (A C : Matrix n n ℂ)
    (hA : A.PosDef) (hC : C.PosDef)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
 let P : Matrix n n ℂ := a • A + b • C
 let T : Matrix n n ℂ :=
    (Real.sqrt a : ℂ) • ((root P)⁻¹ * root A)
 T * A⁻¹ * Tᴴ = a • P⁻¹ := by
  classical
  dsimp
  let P : Matrix n n ℂ := a • A + b • C
  have hp : P.PosDef :=
    (Matrix.PosDef.smul hA ha).add (Matrix.PosDef.smul hC hb)
  let R : Matrix n n ℂ := root P
  let S : Matrix n n ℂ := root A
  have Ri : (R⁻¹)ᴴ = R⁻¹ := invroot_conj P hp
  have Si : Sᴴ = S := root_conj A hA
  have mid : S * A⁻¹ * S = (1:Matrix n n ℂ) := root_Ainv_root A hA
  have ri2 : R⁻¹ * R⁻¹ = P⁻¹ := invroot_sq P hp
  change (((Real.sqrt a : ℂ) • (R⁻¹ * S)) * A⁻¹ *
         (((Real.sqrt a : ℂ) • (R⁻¹ * S))ᴴ)) = _
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]
  simp [Ri, Si]
  simp only [smul_smul]
  have aar : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt (le_of_lt ha)
  -- collect products and remove the middle inverse
  rw [aar]
  rw [← Matrix.smul_mul]
  rw [Matrix.smul_mul]
  congr 1
  calc
    (R⁻¹ * S * A⁻¹) * (S * R⁻¹) = R⁻¹ * (S * A⁻¹ * S) * R⁻¹ := by noncomm_ring
    _ = R⁻¹ * R⁻¹ := by rw [mid]; simp
    _ = P⁻¹ := ri2

lemma col_vec (A C : Matrix n n ℂ)
    (hA : A.PosDef) (hC : C.PosDef)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
 let P : Matrix n n ℂ := a • A + b • C
 let T : Matrix n n ℂ :=
    (Real.sqrt a : ℂ) • ((root P)⁻¹ * root A)
 rop T *ᵥ vec (root P) =
     (Real.sqrt a : ℂ) • vec (root A) := by
  classical
  dsimp
  let P : Matrix n n ℂ := a • A + b • C
  have hp : P.PosDef :=
    (Matrix.PosDef.smul hA ha).add (Matrix.PosDef.smul hC hb)
  let R : Matrix n n ℂ := root P
  let S : Matrix n n ℂ := root A
  change rop ((Real.sqrt a : ℂ) • (R⁻¹ * S)) *ᵥ vec R = _
  rw [rop_mulVec]
  have e : R * ((Real.sqrt a : ℂ) • (R⁻¹ * S)) =
       (Real.sqrt a : ℂ) • S := by
     rw [Matrix.mul_smul]
     have ri : R * R⁻¹ = (1:Matrix n n ℂ) := root_mul_inv P hp
     rw [← Matrix.mul_assoc, ri, Matrix.one_mul]
  rw [e]
  rfl

lemma rop_cols_one (A C : Matrix n n ℂ)
    (hA : A.PosDef) (hC : C.PosDef)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
 let P : Matrix n n ℂ := a • A + b • C
 let T : Matrix n n ℂ :=
    (Real.sqrt a : ℂ) • ((root P)⁻¹ * root A)
 let Z : Matrix n n ℂ :=
    (Real.sqrt b : ℂ) • ((root P)⁻¹ * root C)
 (rop T)ᴴ * rop T + (rop Z)ᴴ * rop Z =
      (1:Matrix (n×n) (n×n) ℂ) := by
  classical
  dsimp
  let P : Matrix n n ℂ := a • A + b • C
  let T : Matrix n n ℂ :=
    (Real.sqrt a : ℂ) • ((root P)⁻¹ * root A)
  let Z : Matrix n n ℂ :=
    (Real.sqrt b : ℂ) • ((root P)⁻¹ * root C)
  change (rop T)ᴴ * rop T + (rop Z)ᴴ * rop Z = _
  rw [rop_sum_ct]
  have k : T * Tᴴ + Z * Zᴴ = (1:Matrix n n ℂ) :=
     norm_col A C hA hC a b ha hb
  rw [k]
  simpa using (Matrix.one_kronecker_one (m:=n) (n:=n) (α:=ℂ))

lemma col_delta (A B C D : Matrix n n ℂ)
    (hA : A.PosDef) (hB : B.PosDef)
    (hC : C.PosDef) (hD : D.PosDef)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
 let P : Matrix n n ℂ := a • A + b • C
 let Q : Matrix n n ℂ := a • B + b • D
 let T : Matrix n n ℂ :=
    (Real.sqrt a : ℂ) • ((root P)⁻¹ * root A)
 let Z : Matrix n n ℂ :=
    (Real.sqrt b : ℂ) • ((root P)⁻¹ * root C)
 (rop T)ᴴ * (B ⊗ₖ (A⁻¹).transpose) * rop T +
 (rop Z)ᴴ * (D ⊗ₖ (C⁻¹).transpose) * rop Z =
       Q ⊗ₖ (P⁻¹).transpose := by
  classical
  dsimp
  let P : Matrix n n ℂ := a • A + b • C
  let Q : Matrix n n ℂ := a • B + b • D
  let T : Matrix n n ℂ :=
    (Real.sqrt a : ℂ) • ((root P)⁻¹ * root A)
  let Z : Matrix n n ℂ :=
    (Real.sqrt b : ℂ) • ((root P)⁻¹ * root C)
  change (rop T)ᴴ * (B ⊗ₖ (A⁻¹).transpose) * rop T +
    (rop Z)ᴴ * (D ⊗ₖ (C⁻¹).transpose) * rop Z =
       Q ⊗ₖ (P⁻¹).transpose
  rw [kron_inv_conj B (A⁻¹) T, kron_inv_conj D (C⁻¹) Z]
  have t : T * A⁻¹ * Tᴴ = a • P⁻¹ :=
      col_inv A C hA hC a b ha hb
  have z : Z * C⁻¹ * Zᴴ = b • P⁻¹ := by
      -- interchange the two inputs
      have q := col_inv C A hC hA b a hb ha
      -- barycentre is the same after commuting the two summands
      simpa [Z, T, P, Q, add_comm] using q
  rw [t, z]
  -- distribute the two weights from the right factor to the left one
  -- all scalar multiplications are real here
  ext i j
  simp [Q, Matrix.kronecker_apply, Matrix.transpose_apply,
        Matrix.add_apply, RCLike.real_smul_eq_coe_mul]
  ring

lemma dot_scale (M : Matrix n n ℂ) (v : n → ℂ) (r a : ℝ)
   (hr : r*r = a) :
    star ((r:ℂ) • v) ⬝ᵥ (M *ᵥ ((r:ℂ) • v)) =
       (a:ℂ) * (star v ⬝ᵥ (M *ᵥ v)) := by
 classical
 simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_add]
 -- after distribution it is just a scalar identity termwise
 have hrc : (r:ℂ)*(r:ℂ) = (a:ℂ) := by exact_mod_cast hr
 apply Finset.sum_congr rfl
 intro i hi
 apply Finset.sum_congr rfl
 intro j hj
 rw [← hrc]
 ring

/-- Joint convexity of the finite trace relative entropy on the open face.
The proof is a Hilbert--Schmidt relative modular argument. -/
lemma trace_joint (A B C D : Matrix n n ℂ)
    (hA : A.PosDef) (hB : B.PosDef)
    (hC : C.PosDef) (hD : D.PosDef)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
 Complex.re (Matrix.trace
   ((a • A + b • C) * cfc Real.log (a • A + b • C) -
    (a • A + b • C) * cfc Real.log (a • B + b • D))) ≤
   a * Complex.re (Matrix.trace
       (A * cfc Real.log A - A * cfc Real.log B)) +
   b * Complex.re (Matrix.trace
       (C * cfc Real.log C - C * cfc Real.log D)) := by
 classical
 let P : Matrix n n ℂ := a • A + b • C
 let Q : Matrix n n ℂ := a • B + b • D
 have hp : P.PosDef :=
    (Matrix.PosDef.smul hA ha).add (Matrix.PosDef.smul hC hb)
 have hq : Q.PosDef :=
    (Matrix.PosDef.smul hB ha).add (Matrix.PosDef.smul hD hb)
 let T : Matrix n n ℂ :=
    (Real.sqrt a : ℂ) • ((root P)⁻¹ * root A)
 let Z : Matrix n n ℂ :=
    (Real.sqrt b : ℂ) • ((root P)⁻¹ * root C)
 let E : Matrix (n×n) (n×n) ℂ := B ⊗ₖ (A⁻¹).transpose
 let F : Matrix (n×n) (n×n) ℂ := D ⊗ₖ (C⁻¹).transpose
 have ep : E.PosDef := by
   dsimp [E]
   exact Matrix.PosDef.kronecker hB
      (SSAuxT.posDef_transpose _ (Matrix.PosDef.inv hA))
 have fp : F.PosDef := by
   dsimp [F]
   exact Matrix.PosDef.kronecker hD
      (SSAuxT.posDef_transpose _ (Matrix.PosDef.inv hC))
 have iso : (rop T)ᴴ * rop T + (rop Z)ᴴ * rop Z =
       (1 : Matrix (n×n) (n×n) ℂ) := by
   exact rop_cols_one A C hA hC a b ha hb
 have delta : (rop T)ᴴ * E * rop T + (rop Z)ᴴ * F * rop Z =
       Q ⊗ₖ (P⁻¹).transpose := by
   exact col_delta A B C D hA hB hC hD a b ha hb
 have J := SSAuxDS.log_compress_two E F (rop T) (rop Z) ep fp iso
 rw [delta] at J
 -- test expression type
 have nz := J.dotProduct_mulVec_nonneg (vec (root P))
 have nr : 0 ≤ Complex.re
      (star (vec (root P)) ⬝ᵥ
        ((cfc Real.log (Q ⊗ₖ (P⁻¹).transpose) -
          ((rop T)ᴴ * cfc Real.log E * rop T +
           (rop Z)ᴴ * cfc Real.log F * rop Z)) *ᵥ
            vec (root P))) :=
      (RCLike.nonneg_iff.mp nz).1
 -- abbreviate the three expectations
 have eP : star (vec (root P)) ⬝ᵥ
       (cfc Real.log (Q ⊗ₖ (P⁻¹).transpose) *ᵥ vec (root P)) =
       - Matrix.trace (P * cfc Real.log P - P * cfc Real.log Q) :=
       expect_rel Q P hq hp
 have eA : star (vec (root A)) ⬝ᵥ
       (cfc Real.log E *ᵥ vec (root A)) =
       - Matrix.trace (A * cfc Real.log A - A * cfc Real.log B) := by
       exact expect_rel B A hB hA
 have eC : star (vec (root C)) ⬝ᵥ
       (cfc Real.log F *ᵥ vec (root C)) =
       - Matrix.trace (C * cfc Real.log C - C * cfc Real.log D) := by
       exact expect_rel D C hD hC
 have cvT : rop T *ᵥ vec (root P) =
       (Real.sqrt a : ℂ) • vec (root A) :=
       col_vec A C hA hC a b ha hb
 have cvZ : rop Z *ᵥ vec (root P) =
       (Real.sqrt b : ℂ) • vec (root C) := by
       have q := col_vec C A hC hA b a hb ha
       simpa [Z, T, P, add_comm] using q
 have qT : star (vec (root P)) ⬝ᵥ
        (((rop T)ᴴ * cfc Real.log E * rop T) *ᵥ vec (root P)) =
      (a:ℂ) * (star (vec (root A)) ⬝ᵥ
           (cfc Real.log E *ᵥ vec (root A))) := by
      rw [dot_mul]
      rw [cvT]
      exact dot_scale (cfc Real.log E) (vec (root A)) (Real.sqrt a) a
        (Real.mul_self_sqrt (le_of_lt ha))
 have qZ : star (vec (root P)) ⬝ᵥ
        (((rop Z)ᴴ * cfc Real.log F * rop Z) *ᵥ vec (root P)) =
      (b:ℂ) * (star (vec (root C)) ⬝ᵥ
           (cfc Real.log F *ᵥ vec (root C))) := by
      rw [dot_mul]
      rw [cvZ]
      exact dot_scale (cfc Real.log F) (vec (root C)) (Real.sqrt b) b
        (Real.mul_self_sqrt (le_of_lt hb))
 -- expand the vector form of J
 rw [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
      eP, qT, qZ, eA, eC] at nr
 dsimp [P, Q] at nr ⊢
 -- the remaining statement is just the real part of the preceding inequality
 push_cast at nr
 simp [Complex.mul_re] at nr
 simp [Matrix.trace_sub, Complex.sub_re]
 linarith

end SSAuxPers

end

end
-- END INLINED FILE: Mathlib/Support/strong_subadditivity_fb0a335e77/Convex.lean

-- BEGIN INLINED MAIN PRELUDE

open LeanEval.Physics
open ComplexOrder

variable {A B C : Type*}
variable [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [Nonempty A] [Nonempty B] [Nonempty C]
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

-- Finite dimensional partial traces are just sums of principal submatrices.  It is
-- useful to record this explicitly: the positivity statement below needs no
-- spectral theory -- it is a sum of compressions of the original positive
-- matrix.
lemma Matrix.traceLeft_eq_sum_submatrix
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix (ι × κ) (ι × κ) ℂ) :
    T.traceLeft = ∑ a : ι, T.submatrix (fun b : κ => (a,b)) (fun b : κ => (a,b)) := by
  classical
  ext b c
  simp [Matrix.traceLeft, Matrix.submatrix, Matrix.of_apply, Matrix.sum_apply]

lemma Matrix.traceRight_eq_sum_submatrix
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix (ι × κ) (ι × κ) ℂ) :
    T.traceRight = ∑ b : κ, T.submatrix (fun a : ι => (a,b)) (fun a : ι => (a,b)) := by
  classical
  ext a c
  simp [Matrix.traceRight, Matrix.submatrix, Matrix.of_apply, Matrix.sum_apply]

lemma Matrix.PosSemidef.traceLeft
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {T : Matrix (ι × κ) (ι × κ) ℂ} (hT : T.PosSemidef) :
    (T.traceLeft : Matrix κ κ ℂ).PosSemidef := by
  classical
  rw [Matrix.traceLeft_eq_sum_submatrix T]
  exact Matrix.posSemidef_sum Finset.univ (by
    intro i hi
    exact hT.submatrix (fun j => (i,j)))

lemma Matrix.PosSemidef.traceRight
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {T : Matrix (ι × κ) (ι × κ) ℂ} (hT : T.PosSemidef) :
    (T.traceRight : Matrix ι ι ℂ).PosSemidef := by
  classical
  rw [Matrix.traceRight_eq_sum_submatrix T]
  exact Matrix.posSemidef_sum Finset.univ (by
    intro i hi
    exact hT.submatrix (fun j => (j,i)))


lemma Matrix.PosDef.traceLeft
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
    {T : Matrix (ι × κ) (ι × κ) ℂ} (hT : T.PosDef) :
    (T.traceLeft : Matrix κ κ ℂ).PosDef := by
  classical
  rw [Matrix.traceLeft_eq_sum_submatrix T]
  exact Matrix.posDef_sum Finset.univ_nonempty (by
    intro i hi
    exact hT.submatrix (by intro a b h; exact congrArg Prod.snd h))

lemma Matrix.PosDef.traceRight
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty κ]
    {T : Matrix (ι × κ) (ι × κ) ℂ} (hT : T.PosDef) :
    (T.traceRight : Matrix ι ι ℂ).PosDef := by
  classical
  rw [Matrix.traceRight_eq_sum_submatrix T]
  exact Matrix.posDef_sum Finset.univ_nonempty (by
    intro i hi
    exact hT.submatrix (by intro a b h; exact congrArg Prod.fst h))

lemma Matrix.trace_traceLeft
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix.trace (T.traceLeft) = Matrix.trace T := by
  classical
  simp [Matrix.trace, Matrix.traceLeft, Matrix.of_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

lemma Matrix.trace_traceRight
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix.trace (T.traceRight) = Matrix.trace T := by
  classical
  simp [Matrix.trace, Matrix.traceRight, Matrix.of_apply,
    Fintype.sum_prod_type]


-- tracing an infinitesimal identity: the missing multiplicity is exactly the size of
-- the discarded factor.  This formula is useful for honest regularizations (there
-- is no continuity of `log` at the origin by itself).
lemma Matrix.traceLeft_add_r_one
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix (ι × κ) (ι × κ) ℂ) (r : ℝ) :
    ((T + algebraMap ℝ (Matrix (ι × κ) (ι × κ) ℂ) r).traceLeft :
       Matrix κ κ ℂ) =
      (T.traceLeft : Matrix κ κ ℂ) +
        algebraMap ℝ (Matrix κ κ ℂ) ((Fintype.card ι : ℝ) * r) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.traceLeft, Matrix.of_apply, Matrix.add_apply,
      Matrix.algebraMap_eq_diagonal, Matrix.diagonal, Finset.sum_add_distrib, mul_comm]
  · simp [Matrix.traceLeft, Matrix.of_apply, Matrix.add_apply,
      Matrix.algebraMap_eq_diagonal, Matrix.diagonal, hij]

lemma Matrix.traceRight_add_r_one
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix (ι × κ) (ι × κ) ℂ) (r : ℝ) :
    ((T + algebraMap ℝ (Matrix (ι × κ) (ι × κ) ℂ) r).traceRight :
       Matrix ι ι ℂ) =
      (T.traceRight : Matrix ι ι ℂ) +
        algebraMap ℝ (Matrix ι ι ℂ) ((Fintype.card κ : ℝ) * r) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.traceRight, Matrix.of_apply, Matrix.add_apply,
      Matrix.algebraMap_eq_diagonal, Matrix.diagonal, Finset.sum_add_distrib, mul_comm]
  · simp [Matrix.traceRight, Matrix.of_apply, Matrix.add_apply,
      Matrix.algebraMap_eq_diagonal, Matrix.diagonal, hij]

lemma Matrix.reindex_add_r_one
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix ι ι ℂ) (q : ι ≃ κ) (r : ℝ) :
    ((T + algebraMap ℝ (Matrix ι ι ℂ) r).reindex q q : Matrix κ κ ℂ) =
      T.reindex q q + algebraMap ℝ (Matrix κ κ ℂ) r := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.reindex_apply, Matrix.add_apply,
      Matrix.algebraMap_eq_diagonal, Matrix.diagonal]
  · have hn : q.symm i ≠ q.symm j := by
      intro w
      exact h (q.symm.injective w)
    simp [Matrix.reindex_apply, Matrix.add_apply,
      Matrix.algebraMap_eq_diagonal, Matrix.diagonal, h, hn]


-- Reindexing by a bijection is another compression.  Keeping it in this
-- form avoids changing to a positivity notion on linear maps.
lemma Matrix.PosSemidef.reindex_self
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {T : Matrix ι ι ℂ} (hT : T.PosSemidef) (e : ι ≃ κ) :
    (T.reindex e e : Matrix κ κ ℂ).PosSemidef := by
  -- `reindex` uses the inverse map on entries.
  simpa [Matrix.reindex_apply] using
    (hT.submatrix (fun j : κ => e.symm j))



lemma Matrix.trace_reindex_self
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix ι ι ℂ) (e : ι ≃ κ) :
    Matrix.trace (T.reindex e e) = Matrix.trace T := by
  classical
  -- this is the same finite sum, only the name of its diagonal index changes.
  change (∑ j : κ, T (e.symm j) (e.symm j)) = ∑ i : ι, T i i
  exact (Fintype.sum_equiv e (fun i : ι => T i i)
    (fun j : κ => T (e.symm j) (e.symm j)) (by intro i; simp)).symm

-- The logarithm in `entropy` is the real functional calculus.  On a finite
-- Hermitian matrix the underlying spectrum is finite, so it evaluates the
-- scalar function on every eigenvalue -- in particular at `0` it is the
-- total `Real.log` with `Real.log 0 = 0`.  Exposing the resulting elementary
-- expression is useful for all subsequent limiting arguments.
lemma Matrix.IsHermitian.trace_mul_cfc_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Matrix ι ι ℂ} (hT : T.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (T * cfc f T) =
      ∑ i : ι, (hT.eigenvalues i : ℂ) * (f (hT.eigenvalues i) : ℂ) := by
  classical
  -- write both factors in the eigenbasis.  The same unitary occurs for the
  -- two occurrences of the functional calculus.
  rw [hT.cfc_eq f, Matrix.IsHermitian.cfc]
  -- keep notation for the unitary and the two diagonals small; the cyclicity
  -- of trace removes the unitary without any coordinates.
  let U := hT.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues)
  let E : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ f ∘ hT.eigenvalues)
  have hdiag : T = (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) U D := by
    simpa [D] using hT.spectral_theorem

  change Matrix.trace (T * ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) U) E) = _
  calc
    _ = Matrix.trace
        (((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) U) D *
         ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) U) E) := by
          exact congrArg (fun X : Matrix ι ι ℂ =>
            Matrix.trace (X * ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) U) E)) hdiag
    _ = _ := by
      rw [← map_mul]
      rw [Unitary.conjStarAlgAut_apply]
      rw [Matrix.trace_mul_cycle]
      rw [Unitary.coe_star_mul_self]
      rw [Matrix.one_mul]
      dsimp [D, E]
      rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      rfl


lemma entropy_eq_sum_negMulLog
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Matrix ι ι ℂ} (hT : T.PosSemidef) :
    entropy T = ∑ i : ι, Real.negMulLog (hT.isHermitian.eigenvalues i) := by
  classical
  unfold entropy
  rw [Matrix.IsHermitian.trace_mul_cfc_sum hT.isHermitian Real.log]
  -- all eigenvalues and logarithms here are real scalars in `ℂ`; taking the
  -- real part commutes with the finite sum.
  simp [Real.negMulLog, ← Finset.sum_neg_distrib]




-- The product appearing in entropy is a continuous scalar functional calculus,
-- even at a zero eigenvalue.  Keeping this version avoids any fake continuity
-- of `log` at zero.
lemma entropy_eq_trace_mulLog {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (T : Matrix m m ℂ) (hT : T.IsHermitian) :
    entropy T = - Complex.re (Matrix.trace (cfc (fun x : ℝ => x * Real.log x) T)) := by
  unfold entropy
  rw [SSAux.mul_cfc_log_eq_cfc_mulLog T hT]

lemma Matrix.IsHermitian.trace_cfc_sum
    {m : Type*} [Fintype m] [DecidableEq m]
    {T : Matrix m m ℂ} (hT : T.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (cfc f T) = ∑ i : m, (f (hT.eigenvalues i) : ℂ) := by
  classical
  rw [hT.cfc_eq f, Matrix.IsHermitian.cfc]
  let U := hT.eigenvectorUnitary
  let D : Matrix m m ℂ := Matrix.diagonal (RCLike.ofReal ∘ f ∘ hT.eigenvalues)
  change Matrix.trace (((Unitary.conjStarAlgAut ℂ (Matrix m m ℂ)) U) D) = _
  rw [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  rw [Unitary.coe_star_mul_self]
  rw [Matrix.one_mul]
  dsimp [D]
  rw [Matrix.trace_diagonal]
  rfl

/-- A scalar translate of a self-adjoint finite matrix is obtained by translating
inside its functional calculus.  Notice that neither occurrence of `f` below
is required to be globally continuous: both spectra are finite. -/
lemma Matrix.IsHermitian.cfc_add_r_one
    {m : Type*} [Fintype m] [DecidableEq m]
    (T : Matrix m m ℂ) (hT : T.IsHermitian) (f : ℝ → ℝ) (r : ℝ) :
    cfc f (T + (algebraMap ℝ (Matrix m m ℂ) r)) =
      cfc (fun x : ℝ => f (x + r)) T := by
  classical
  have fin : (spectrum ℝ T).Finite := by
    rw [hT.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have shift : cfc (fun x : ℝ => x + r) T =
      T + algebraMap ℝ (Matrix m m ℂ) r := by
    change cfc (fun x : ℝ => id x + (fun _ : ℝ => r) x) T = _
    rw [cfc_add T id (fun _ : ℝ => r)
      (hf:=continuous_id.continuousOn) (hg:=continuous_const.continuousOn)]
    rw [cfc_id ℝ T (ha:=hT.isSelfAdjoint)]
    rw [cfc_const r T (ha:=hT.isSelfAdjoint)]
  rw [← shift]
  rw [← cfc_comp f (fun x : ℝ => x + r) T (ha:=hT.isSelfAdjoint)
      (hf:= continuous_add_right r |>.continuousOn)
      (hg:= (fin.image (fun x : ℝ => x + r)).continuousOn _)]
  rfl

lemma entropy_add_r_one_formula
    {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (T : Matrix m m ℂ) (hT : T.IsHermitian) (r : ℝ) :
    entropy (T + algebraMap ℝ (Matrix m m ℂ) r) =
      ∑ i : m, -( (hT.eigenvalues i + r) * Real.log (hT.eigenvalues i + r)) := by
  classical
  have hone : (algebraMap ℝ (Matrix m m ℂ) r).IsHermitian :=
    (IsSelfAdjoint.algebraMap (Matrix m m ℂ) (by
      change star r = r
      exact star_trivial r))
  rw [entropy_eq_trace_mulLog _ (hT.add hone)]
  rw [Matrix.IsHermitian.cfc_add_r_one T hT (fun x : ℝ => x * Real.log x) r]
  rw [Matrix.IsHermitian.trace_cfc_sum hT]
  simp [map_sum, ← Finset.sum_neg_distrib]

lemma continuous_entropy_add_r_one
    {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (T : Matrix m m ℂ) (hT : T.IsHermitian) :
    Continuous (fun r : ℝ => entropy (T + algebraMap ℝ (Matrix m m ℂ) r)) := by
  classical
  simp_rw [entropy_add_r_one_formula T hT]
  fun_prop (disch := exact Real.continuous_mul_log)

lemma tendsto_entropy_add_invNat_one
    {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (T : Matrix m m ℂ) (hT : T.IsHermitian) :
    Filter.Tendsto
      (fun k : ℕ => entropy (T + algebraMap ℝ (Matrix m m ℂ) ((k:ℝ) + 1)⁻¹))
      Filter.atTop (nhds (entropy T)) := by
  have z : entropy T = entropy (T + algebraMap ℝ (Matrix m m ℂ) (0:ℝ)) := by simp
  rw [z]
  apply (continuous_entropy_add_r_one T hT).continuousAt.tendsto.comp
  convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)) using 1 <;>
    simp [one_div]

-- Multiplicities from a traced identity are harmless in the positivity
-- regularization as well.  We state the limit for an arbitrary fixed real
-- coefficient; this keeps all four systems on one sequence later.
lemma tendsto_entropy_add_c_invNat_one
    {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (T : Matrix m m ℂ) (hT : T.IsHermitian) (c : ℝ) :
    Filter.Tendsto
      (fun k : ℕ => entropy
        (T + algebraMap ℝ (Matrix m m ℂ) (c * ((k:ℝ) + 1)⁻¹)))
      Filter.atTop (nhds (entropy T)) := by
  have z : entropy T = entropy
        (T + algebraMap ℝ (Matrix m m ℂ) (c * (0:ℝ))) := by simp
  rw [z]
  apply (continuous_entropy_add_r_one T hT).continuousAt.tendsto.comp
  have ht : Filter.Tendsto
      (fun k : ℕ => ((k:ℝ) + 1)⁻¹) Filter.atTop (nhds (0:ℝ)) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)) using 1 <;>
      simp [one_div]
  convert (tendsto_const_nhds.mul ht) using 1 <;> simp

open scoped Kronecker
/-- The (finite, support-friendly) trace expression for relative entropy.  In
this problem it is used only with the second argument an identity block
containing the marginal of the first. -/
noncomputable def matrixQRel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) : ℝ :=
  Complex.re (Matrix.trace (X * cfc Real.log X - X * cfc Real.log Y))

lemma Matrix.trace_mul_leftId_cfc
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix (ι × κ) (ι × κ) ℂ) (S : Matrix κ κ ℂ)
    (hS : S.IsHermitian) :
    Matrix.trace (T * cfc Real.log (SSAux.leftIdHom ι κ S)) =
      Matrix.trace
        ((T.traceLeft : Matrix κ κ ℂ) * cfc Real.log S) := by
  rw [← SSAux.leftIdHom_cfc ι κ S hS]
  simpa [Matrix.traceLeft] using (SSAux.trace_mul_leftIdHom ι κ T (cfc Real.log S))

/- Homogeneity at a positive scalar.  The matrix instance of the real CFC in
mathlib is entrywise finite-dimensional (it is not the normed-C* one), so we give
the two-line `cfc_comp` argument here rather than using `CFC.log_smul'`.  Finiteness
of the real spectrum is exactly what supplies the continuity hypotheses. -/
lemma matrixQRel_rsmul_posDef
    {m : Type*} [Fintype m] [DecidableEq m]
    (X Y : Matrix m m ℂ) (hX : X.PosDef) (hY : Y.PosDef)
    {r : ℝ} (hr : 0 < r) :
    matrixQRel (r • X) (r • Y) = r * matrixQRel X Y := by
  have logSmul (Z : Matrix m m ℂ) (hz : Z.PosDef) :
      cfc Real.log (r • Z) =
        algebraMap ℝ (Matrix m m ℂ) (Real.log r) + cfc Real.log Z := by
    have nz : ∀ x ∈ spectrum ℝ Z, x ≠ 0 := by
      rw [hz.isHermitian.spectrum_real_eq_range_eigenvalues]
      intro x hxv
      obtain ⟨i, rfl⟩ := hxv
      exact ne_of_gt ((hz.isHermitian.posDef_iff_eigenvalues_pos.mp hz) i)
    have fin : (spectrum ℝ Z).Finite := by
      rw [hz.isHermitian.spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    rw [← cfc_smul_id (R:=ℝ) r Z (ha:=hz.isHermitian.isSelfAdjoint)]
    rw [← cfc_comp Real.log (r • ·) Z
       (ha:=hz.isHermitian.isSelfAdjoint)
       (hf:=fin.continuousOn _)
       (hg:=(fin.image _).continuousOn _)]
    calc
      _ = cfc (fun z : ℝ => Real.log r + Real.log z) Z := by
        apply cfc_congr
        intro x hxmem
        dsimp
        exact Real.log_mul (ne_of_gt hr) (nz x hxmem)
      _ = _ := by
        rw [cfc_const_add _ _ Z
          (hf:=fin.continuousOn _) (ha:=hz.isHermitian.isSelfAdjoint)]
  unfold matrixQRel
  rw [logSmul X hX, logSmul Y hY]
  have eqn :
    (r • X) * ((algebraMap ℝ (Matrix m m ℂ) (Real.log r)) + cfc Real.log X) -
    (r • X) * ((algebraMap ℝ (Matrix m m ℂ) (Real.log r)) + cfc Real.log Y) =
      r • (X * cfc Real.log X - X * cfc Real.log Y) := by
    simp [mul_add, smul_sub]
  rw [eqn, Matrix.trace_smul]
  simp [Complex.mul_re]

-- Repeating an identical square block multiplies its trace by the number of
-- blocks.  This formulation deliberately does not assume positivity: for a
-- Hermitian block the CFC really is repeated by the star hom in `Block`. 
lemma Matrix.PosSemidef.leftIdHom
    {d m : Type*} [Fintype d] [Fintype m]
    [DecidableEq d] [DecidableEq m]
    {X : Matrix m m ℂ} (hX : X.PosSemidef) :
    (SSAux.leftIdHom d m X).PosSemidef := by
  rw [SSAux.leftIdHom_apply]
  exact Matrix.PosSemidef.kronecker (.one) hX

lemma Matrix.PosDef.leftIdHom
    {d m : Type*} [Fintype d] [Fintype m]
    [DecidableEq d] [DecidableEq m]
    {X : Matrix m m ℂ} (hX : X.PosDef) :
    (SSAux.leftIdHom d m X).PosDef := by
  rw [SSAux.leftIdHom_apply]
  exact Matrix.PosDef.kronecker (.one) hX

lemma Matrix.trace_mul_two_leftId
    {d m : Type*} [Fintype d] [Fintype m]
    [DecidableEq d] [DecidableEq m]
    (X Z : Matrix m m ℂ) :
    Matrix.trace ((SSAux.leftIdHom d m X) * SSAux.leftIdHom d m Z) =
      (Fintype.card d : ℂ) * Matrix.trace (X * Z) := by
  classical
  rw [SSAux.trace_mul_leftIdHom]
  simp [SSAux.leftIdHom_entry, Matrix.trace, Matrix.mul_apply,
        Finset.mul_sum]

lemma matrixQRel_leftId
    {d m : Type*} [Fintype d] [Fintype m]
    [DecidableEq d] [DecidableEq m]
    (X Y : Matrix m m ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    matrixQRel (SSAux.leftIdHom d m X) (SSAux.leftIdHom d m Y) =
      (Fintype.card d : ℝ) * matrixQRel X Y := by
  classical
  unfold matrixQRel
  rw [← SSAux.leftIdHom_cfc d m X hX,
      ← SSAux.leftIdHom_cfc d m Y hY]
  rw [Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_mul_two_leftId, Matrix.trace_mul_two_leftId]
  simp [Complex.mul_re]
  ring

lemma matrixQRel_uniformBlock_posDef
    {d m : Type*} [Fintype d] [Fintype m]
    [DecidableEq d] [DecidableEq m] [Nonempty d]
    (X Y : Matrix m m ℂ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixQRel
       (((Fintype.card d : ℝ)⁻¹) • SSAux.leftIdHom d m X)
       (((Fintype.card d : ℝ)⁻¹) • SSAux.leftIdHom d m Y) =
    matrixQRel X Y := by
  have cd : (0:ℝ) < (Fintype.card d : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  rw [matrixQRel_rsmul_posDef
        (SSAux.leftIdHom d m X) (SSAux.leftIdHom d m Y)
        (Matrix.PosDef.leftIdHom hX) (Matrix.PosDef.leftIdHom hY)
        (inv_pos.mpr cd)]
  rw [matrixQRel_leftId X Y hX.isHermitian hY.isHermitian]
  apply (inv_mul_cancel_left₀ (ne_of_gt cd) (matrixQRel X Y))

lemma Matrix.PosDef.fullTwist
    {d m : Type*} [Fintype d] [Fintype m]
    [DecidableEq d] [DecidableEq m]
    {X : Matrix (d × m) (d × m) ℂ} (hX : X.PosDef)
    (s : Equiv.Perm d) (u : d → Bool) :
    (SSAux.fullTwist s u X).PosDef := by
  rw [SSAux.fullTwist_eq_conj]
  rw [Unitary.conjStarAlgAut_apply]
  change (SSAux.twistU (κ:=m) s u * X *
      star (SSAux.twistU (κ:=m) s u)).PosDef
  have hu : IsUnit (SSAux.twistU (κ:=m) s u) :=
    isUnit_iff_exists_inv.mpr
      ⟨star (SSAux.twistU (κ:=m) s u), SSAux.twistU_mul_star s u⟩
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hu).mpr hX

lemma Matrix.PosSemidef.fullTwist
    {d m : Type*} [Fintype d] [Fintype m]
    [DecidableEq d] [DecidableEq m]
    {X : Matrix (d × m) (d × m) ℂ} (hX : X.PosSemidef)
    (s : Equiv.Perm d) (u : d → Bool) :
    (SSAux.fullTwist s u X).PosSemidef := by
  rw [SSAux.fullTwist_eq_conj]
  rw [Unitary.conjStarAlgAut_apply]
  change (SSAux.twistU (κ:=m) s u * X *
      star (SSAux.twistU (κ:=m) s u)).PosSemidef
  have hu : IsUnit (SSAux.twistU (κ:=m) s u) :=
    isUnit_iff_exists_inv.mpr
      ⟨star (SSAux.twistU (κ:=m) s u), SSAux.twistU_mul_star s u⟩
  exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hu).mpr hX

lemma matrixQRel_fullTwist
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Equiv.Perm ι) (u : ι → Bool)
    (X Y : Matrix (ι × κ) (ι × κ) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    matrixQRel (SSAux.fullTwist s u X) (SSAux.fullTwist s u Y) =
      matrixQRel X Y := by
  unfold matrixQRel
  rw [Matrix.trace_sub, Matrix.trace_sub]
  rw [Complex.sub_re, Complex.sub_re]
  rw [SSAux.trace_mul_fullTwist_cfc s u X X hX]
  rw [SSAux.trace_mul_fullTwist_cfc s u X Y hY]

/-- Pairing a state with the identity block over its marginal cancels the
cross term in relative entropy.  This is the elementary cancellation needed
before monotonicity under a partial trace; it remains true for singular
marginals because `log 0` in the CFC is the total real logarithm. -/
lemma matrixQRel_leftId_of_traceLeft
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix (ι × κ) (ι × κ) ℂ) (hT : T.IsHermitian) :
    matrixQRel T (SSAux.leftIdHom ι κ (T.traceLeft : Matrix κ κ ℂ)) =
      - entropy T + entropy (T.traceLeft : Matrix κ κ ℂ) := by
  have hS : (T.traceLeft : Matrix κ κ ℂ).IsHermitian := by
    -- taking identical diagonal blocks preserves the adjoint symmetry
    classical
    rw [Matrix.IsHermitian.ext_iff] at hT ⊢
    intro i j
    simp [Matrix.traceLeft, hT]
  unfold matrixQRel entropy
  rw [Matrix.trace_sub]
  rw [Complex.sub_re]
  rw [Matrix.trace_mul_leftId_cfc T (T.traceLeft : Matrix κ κ ℂ) hS]
  ring

/-- The two iterated contractions used for `AB` and `B` agree entrywise.
The associativity reindexing only changes the parentheses of a product. -/
lemma Matrix.traceLeft_traceRight_assoc
    {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq δ]
    (T : Matrix (ι × κ × δ) (ι × κ × δ) ℂ) :
    (((T.reindex (Equiv.prodAssoc ι κ δ).symm
          (Equiv.prodAssoc ι κ δ).symm : Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ).traceRight :
          Matrix (ι × κ) (ι × κ) ℂ).traceLeft : Matrix κ κ ℂ) =
      ((T.traceLeft : Matrix (κ × δ) (κ × δ) ℂ).traceRight : Matrix κ κ ℂ) := by
  classical
  ext i j
  simp [Matrix.traceLeft, Matrix.traceRight, Matrix.reindex_apply,
    Matrix.submatrix, Matrix.of_apply]
  rw [Finset.sum_comm]


lemma Matrix.traceRight_assoc_leftId
    {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq δ]
    (S : Matrix (κ × δ) (κ × δ) ℂ) :
    (((SSAux.leftIdHom ι (κ × δ) S).reindex
          (Equiv.prodAssoc ι κ δ).symm (Equiv.prodAssoc ι κ δ).symm :
        Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ).traceRight :
        Matrix (ι × κ) (ι × κ) ℂ) =
      SSAux.leftIdHom ι κ (S.traceRight : Matrix κ κ ℂ) := by
  classical
  ext x y
  by_cases q : x.1 = y.1
  · simp [Matrix.traceRight, Matrix.reindex_apply, SSAux.leftIdHom_entry,
          Matrix.of_apply, Matrix.one_apply, q]
  · simp [Matrix.traceRight, Matrix.reindex_apply, SSAux.leftIdHom_entry,
          Matrix.of_apply, q]

lemma Matrix.traceLeft_swap_assoc_leftId
    {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq δ]
    (S : Matrix (κ × δ) (κ × δ) ℂ) :
    (((SSAux.leftIdHom ι (κ × δ) S).reindex
          (Equiv.prodAssoc ι κ δ).symm (Equiv.prodAssoc ι κ δ).symm).reindex
          (Equiv.prodComm (ι × κ) δ) (Equiv.prodComm (ι × κ) δ)).traceLeft =
        SSAux.leftIdHom ι κ (S.traceRight : Matrix κ κ ℂ) := by
  classical
  change (((SSAux.leftIdHom ι (κ × δ) S).reindex
          (Equiv.prodAssoc ι κ δ).symm (Equiv.prodAssoc ι κ δ).symm :
        Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ).traceRight :
        Matrix (ι × κ) (ι × κ) ℂ) = _
  exact Matrix.traceRight_assoc_leftId S

/-- The twirling sum really is the conditional expectation onto the identity
block.  This entry-free normalization is used for a trace-out on the first
factor; no choice of ordering of the basis vectors is involved. -/
lemma Matrix.average_fullTwist_traceLeft
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
    (T : Matrix (ι × κ) (ι × κ) ℂ) :
    (((Fintype.card (Equiv.Perm ι) : ℂ) *
        (Fintype.card (ι → Bool) : ℂ))⁻¹) •
       (∑ s : Equiv.Perm ι, ∑ u : ι → Bool, SSAux.fullTwist s u T) =
      ((Fintype.card ι : ℂ)⁻¹) •
        SSAux.leftIdHom ι κ (T.traceLeft : Matrix κ κ ℂ) := by
  have h := SSAux.average_fullTwist (ι:=ι) (κ:=κ) T
  have eqn : SSAux.blockSum T = (T.traceLeft : Matrix κ κ ℂ) := by
    rfl
  simpa [eqn] using h

/-- The right trace is a left trace after merely interchanging the tensor
indices. This precise reindexing is what lets the same twirl handle a trace
on `C`. -/
def SSAux.swapTensor (ι κ : Type*) : (ι × κ) ≃ (κ × ι) := Equiv.prodComm _ _

lemma Matrix.swap_traceLeft
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix (ι × κ) (ι × κ) ℂ) :
    ((T.reindex (SSAux.swapTensor ι κ) (SSAux.swapTensor ι κ) :
       Matrix (κ × ι) (κ × ι) ℂ).traceLeft : Matrix ι ι ℂ) =
       (T.traceRight : Matrix ι ι ℂ) := by
  classical
  rfl

lemma Matrix.trace_reindex_swap
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (T : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix.trace (T.reindex (SSAux.swapTensor ι κ) (SSAux.swapTensor ι κ)) =
      Matrix.trace T := by
  classical
  exact Matrix.trace_reindex_self T (SSAux.swapTensor ι κ)


/-- Reindexing a basis preserves the star, so it transports the real
functional calculus as well. -/
def SSAux.reindexStar {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    intro X
    rw [Matrix.reindexAlgEquiv_apply]
    ext i j
    rfl)

@[simp] lemma SSAux.reindexStar_apply {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (X : Matrix m m ℂ) :
    SSAux.reindexStar e X = X.reindex e e := rfl

lemma SSAux.continuous_reindexStar {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) : Continuous (SSAux.reindexStar e) := by
  change Continuous (fun X : Matrix m m ℂ => X.reindex e e)
  fun_prop

lemma Matrix.cfc_reindex
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (S : Matrix m m ℂ) (hS : S.IsHermitian) (f : ℝ → ℝ) :
    (cfc f S).reindex e e = cfc f (S.reindex e e) := by
  let Φ := SSAux.reindexStar e
  have hf : ContinuousOn f (spectrum ℝ S) := by
    rw [hS.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn _
  have hs : IsSelfAdjoint S := hS.isSelfAdjoint
  have ht : IsSelfAdjoint (Φ S) := by
    rw [isSelfAdjoint_iff] at hs ⊢
    exact (map_star Φ S) ▸ congrArg Φ hs
  exact StarAlgHomClass.map_cfc Φ f S (hf:=hf)
    (hφ:= SSAux.continuous_reindexStar e) (ha:=hs) (hφa:=ht)

lemma matrixQRel_reindex
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (X Y : Matrix m m ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    matrixQRel (X.reindex e e) (Y.reindex e e) = matrixQRel X Y := by
  classical
  unfold matrixQRel
  rw [← Matrix.cfc_reindex e X hX, ← Matrix.cfc_reindex e Y hY]
  -- reindex on a square matrix is an algebra equivalence
  have mulr (P Q : Matrix m m ℂ) :
      P.reindex e e * Q.reindex e e = (P * Q).reindex e e := by
    have q := map_mul (Matrix.reindexAlgEquiv ℂ ℂ e) P Q
    simpa using q.symm
  rw [mulr, mulr]
  have subr (P Q : Matrix m m ℂ) :
      P.reindex e e - Q.reindex e e = (P - Q).reindex e e := by
    have q := map_sub (Matrix.reindexAlgEquiv ℂ ℂ e) P Q
    simpa using q.symm
  rw [subr]
  rw [Matrix.trace_reindex_self]



lemma convex_pair_posDef
    {m : Type*} [Fintype m] [DecidableEq m] :
    Convex ℝ {p : Matrix m m ℂ × Matrix m m ℂ |
          p.1.PosDef ∧ p.2.PosDef} := by
  classical
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  change ((a • x + b • y).1.PosDef ∧ (a • x + b • y).2.PosDef)
  constructor
  · simpa using
      ((Matrix.PosDef.smul hx.1 ha).add (Matrix.PosDef.smul hy.1 hb))
  · simpa using
      ((Matrix.PosDef.smul hx.2 ha).add (Matrix.PosDef.smul hy.2 hb))

-- All the algebra in a twirl argument is Jensen's finite--sum lemma.  This
-- version leaves only the genuine analytic assertion--joint convexity on
-- the open positive face--as a parameter.  No boundary continuity is used
-- in this step.
lemma matrixQRel_twirl_le_of_convexOn
    {d m : Type*} [Fintype d] [Fintype m]
    [DecidableEq d] [DecidableEq m] [Nonempty d] [Nonempty m]
    (joint : ConvexOn ℝ
      {p : Matrix (d × m) (d × m) ℂ × Matrix (d × m) (d × m) ℂ |
          p.1.PosDef ∧ p.2.PosDef}
      (fun p => matrixQRel p.1 p.2))
    (X Y : Matrix (d × m) (d × m) ℂ) (hX : X.PosDef) (hY : Y.PosDef) :
      matrixQRel (X.traceLeft : Matrix m m ℂ)
          (Y.traceLeft : Matrix m m ℂ) ≤ matrixQRel X Y := by
  classical
  let I := Equiv.Perm d × (d → Bool)
  let N : ℝ := (Fintype.card (Equiv.Perm d) : ℝ) *
                 (Fintype.card (d → Bool) : ℝ)
  have hn : 0 < N := by
    dsimp [N]
    have h1 : 0 < (Fintype.card (Equiv.Perm d) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
        0 < Fintype.card (Equiv.Perm d))
    have h2 : 0 < (Fintype.card (d → Bool) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
        0 < Fintype.card (d → Bool))
    exact mul_pos h1 h2
  let w : I → ℝ := fun _ => N⁻¹
  let p : I →
      (Matrix (d × m) (d × m) ℂ × Matrix (d × m) (d × m) ℂ) :=
       fun i => (SSAux.fullTwist i.1 i.2 X, SSAux.fullTwist i.1 i.2 Y)
  have weights : ∑ i : I, w i = (1:ℝ) := by
    classical
    dsimp [w, I]
    rw [Fintype.sum_prod_type]
    simp [N]
  have memp (i : I) : p i ∈
      {p : Matrix (d × m) (d × m) ℂ × Matrix (d × m) (d × m) ℂ |
          p.1.PosDef ∧ p.2.PosDef} := by
    exact ⟨Matrix.PosDef.fullTwist hX i.1 i.2,
           Matrix.PosDef.fullTwist hY i.1 i.2⟩
  have J := joint.map_sum_le
       (t := (Finset.univ : Finset I)) (w := w) (p := p)
       (by intro i hi; exact le_of_lt (inv_pos.mpr hn))
       weights (by intro i hi; exact memp i)
  change matrixQRel
      (∑ i : I, w i • (p i)).1
      (∑ i : I, w i • (p i)).2 ≤
        ∑ i : I, w i • (matrixQRel (p i).1 (p i).2) at J
  have rhs : (∑ i : I, w i • (matrixQRel (p i).1 (p i).2)) =
       matrixQRel X Y := by
    classical
    -- every term is the same real number
    have val (i : I) : matrixQRel (p i).1 (p i).2 = matrixQRel X Y := by
      exact matrixQRel_fullTwist i.1 i.2 X Y hX.isHermitian hY.isHermitian
    simp_rw [val]
    rw [← Finset.sum_smul]
    rw [weights]
    simp
  rw [rhs] at J
  have bx : (∑ i : I, w i • (p i)).1 =
       ((Fintype.card d : ℝ)⁻¹) •
          SSAux.leftIdHom d m (X.traceLeft : Matrix m m ℂ) := by
    -- convert the real barycentre to the complex coefficient in the twirl
    -- identity; on matrices real scalar multiplication is entrywise.
    have av := Matrix.average_fullTwist_traceLeft (T := X)
    change (LinearMap.fst ℝ _ _) (∑ i : I, w i • p i) = _
    rw [map_sum]
    simp only [LinearMap.fst_apply, Prod.smul_fst]
    change (∑ i : I, w i • SSAux.fullTwist i.1 i.2 X) = _
    rw [← Finset.smul_sum]
    dsimp [w]
    rw [Fintype.sum_prod_type]
    -- it remains just to change the real scalar to its complex cast in `av`
    -- on both sides
    have castsmul {a : ℝ}
        (P : Matrix (d × m) (d × m) ℂ) :
        a • P = (a : ℂ) • P := by
      ext i j
      simp [RCLike.real_smul_eq_coe_mul]
    have leftCast : N⁻¹ •
        (∑ x : Equiv.Perm d, ∑ y : d → Bool,
             SSAux.fullTwist (κ:=m) x y X) =
        ((N⁻¹ : ℝ) : ℂ) •
        (∑ x : Equiv.Perm d, ∑ y : d → Bool,
             SSAux.fullTwist (κ:=m) x y X) :=
      castsmul _
    rw [leftCast]
    calc
      _ = ((Fintype.card d : ℂ)⁻¹) •
            SSAux.leftIdHom d m (X.traceLeft : Matrix m m ℂ) := by
            simpa [N, Complex.ofReal_mul, Complex.ofReal_inv] using av
      _ = ((Fintype.card d : ℝ)⁻¹) •
            SSAux.leftIdHom d m (X.traceLeft : Matrix m m ℂ) := by
            symm
            simpa [Complex.ofReal_inv] using
              (castsmul (a:=((Fintype.card d : ℝ)⁻¹))
                (SSAux.leftIdHom d m (X.traceLeft : Matrix m m ℂ)))
  have byy : (∑ i : I, w i • (p i)).2 =
       ((Fintype.card d : ℝ)⁻¹) •
          SSAux.leftIdHom d m (Y.traceLeft : Matrix m m ℂ) := by
    have av := Matrix.average_fullTwist_traceLeft (T := Y)
    change (LinearMap.snd ℝ _ _) (∑ i : I, w i • p i) = _
    rw [map_sum]
    simp only [LinearMap.snd_apply, Prod.smul_snd]
    change (∑ i : I, w i • SSAux.fullTwist i.1 i.2 Y) = _
    rw [← Finset.smul_sum]
    dsimp [w]
    rw [Fintype.sum_prod_type]
    have castsmul {a : ℝ}
        (P : Matrix (d × m) (d × m) ℂ) :
        a • P = (a : ℂ) • P := by
      ext i j
      simp [RCLike.real_smul_eq_coe_mul]
    have leftCast : N⁻¹ •
        (∑ x : Equiv.Perm d, ∑ y : d → Bool,
             SSAux.fullTwist (κ:=m) x y Y) =
        ((N⁻¹ : ℝ) : ℂ) •
        (∑ x : Equiv.Perm d, ∑ y : d → Bool,
             SSAux.fullTwist (κ:=m) x y Y) := castsmul _
    rw [leftCast]
    calc
      _ = ((Fintype.card d : ℂ)⁻¹) •
            SSAux.leftIdHom d m (Y.traceLeft : Matrix m m ℂ) := by
            simpa [N, Complex.ofReal_mul, Complex.ofReal_inv] using av
      _ = ((Fintype.card d : ℝ)⁻¹) •
            SSAux.leftIdHom d m (Y.traceLeft : Matrix m m ℂ) := by
            symm
            simpa [Complex.ofReal_inv] using
              (castsmul (a:=((Fintype.card d : ℝ)⁻¹))
                (SSAux.leftIdHom d m (Y.traceLeft : Matrix m m ℂ)))
  rw [bx, byy] at J
  have hxleft : (X.traceLeft : Matrix m m ℂ).PosDef :=
    Matrix.PosDef.traceLeft hX
  have hyleft : (Y.traceLeft : Matrix m m ℂ).PosDef :=
    Matrix.PosDef.traceLeft hY
  rw [matrixQRel_uniformBlock_posDef
          (d:=d) (X := (X.traceLeft : Matrix m m ℂ))
          (Y := (Y.traceLeft : Matrix m m ℂ)) hxleft hyleft] at J
  exact J

/-- A closed-face reduction.  It is important to regularize the state, not
`log` in a single cross term: a singular cross term need not be continuous on
independent arguments.  All four terms here are entropies, hence are
continuous along the simultaneous scalar translates.  Tracing an identity
just changes its coefficient by the size of the forgotten factor. -/
lemma ssa_of_forall_posDef
    {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq δ]
    [Nonempty ι] [Nonempty κ] [Nonempty δ]
    (pd : ∀ (T : Matrix (ι × κ × δ) (ι × κ × δ) ℂ), T.PosDef →
       entropy T + entropy
         ((T.traceLeft : Matrix (κ × δ) (κ × δ) ℂ).traceRight : Matrix κ κ ℂ) ≤
       entropy
         ((T.reindex (Equiv.prodAssoc ι κ δ).symm (Equiv.prodAssoc ι κ δ).symm :
            Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ).traceRight :
            Matrix (ι × κ) (ι × κ) ℂ) +
       entropy (T.traceLeft : Matrix (κ × δ) (κ × δ) ℂ))
    (T : Matrix (ι × κ × δ) (ι × κ × δ) ℂ) (hT : T.PosSemidef) :
       entropy T + entropy
         ((T.traceLeft : Matrix (κ × δ) (κ × δ) ℂ).traceRight : Matrix κ κ ℂ) ≤
       entropy
         ((T.reindex (Equiv.prodAssoc ι κ δ).symm (Equiv.prodAssoc ι κ δ).symm :
            Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ).traceRight :
            Matrix (ι × κ) (ι × κ) ℂ) +
       entropy (T.traceLeft : Matrix (κ × δ) (κ × δ) ℂ) := by
  classical
  let q : (ι × κ × δ) ≃ ((ι × κ) × δ) := (Equiv.prodAssoc ι κ δ).symm
  let U : Matrix (κ × δ) (κ × δ) ℂ := T.traceLeft
  let V : Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ := T.reindex q q
  let K : Matrix κ κ ℂ := U.traceRight
  let W : Matrix (ι × κ) (ι × κ) ℂ := V.traceRight
  have hU : U.PosSemidef := Matrix.PosSemidef.traceLeft hT
  have hV : V.PosSemidef := Matrix.PosSemidef.reindex_self hT q
  have hK : K.PosSemidef := Matrix.PosSemidef.traceRight hU
  have hW : W.PosSemidef := Matrix.PosSemidef.traceRight hV
  let rn (n : ℕ) : ℝ := ((n:ℝ) + 1)⁻¹
  let Tn (n : ℕ) : Matrix (ι × κ × δ) (ι × κ × δ) ℂ :=
     T + algebraMap ℝ (Matrix (ι × κ × δ) (ι × κ × δ) ℂ) (rn n)
  have hr (n : ℕ) : 0 < rn n := by
    dsimp [rn]
    positivity
  have htndef (n : ℕ) : (Tn n).PosDef := by
    have hi : (algebraMap ℝ
        (Matrix (ι × κ × δ) (ι × κ × δ) ℂ) (rn n)).PosDef := by
      have z : ((rn n) • (1 : Matrix (ι × κ × δ) (ι × κ × δ) ℂ)).PosDef :=
        Matrix.PosDef.smul Matrix.PosDef.one (hr n)
      simpa [Algebra.smul_def] using z
    have z := hi.add_posSemidef hT
    simpa [Tn, add_comm] using z
  -- Exact formulas for the three regularized marginals.  They are used
  -- twice: once to identify the pointwise inequality, once for the four
  -- independent limits.
  have Un (n : ℕ) :
      ((Tn n).traceLeft : Matrix (κ × δ) (κ × δ) ℂ) =
        U + algebraMap ℝ (Matrix (κ × δ) (κ × δ) ℂ)
              ((Fintype.card ι : ℝ) * rn n) := by
    simpa [Tn, U] using
      (Matrix.traceLeft_add_r_one
        (T := T) (r := rn n))
  have Vn (n : ℕ) :
      ((Tn n).reindex q q : Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ) =
        V + algebraMap ℝ (Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ) (rn n) := by
    simpa [Tn, V] using
      (Matrix.reindex_add_r_one (T := T) (q := q) (r := rn n))
  have Kn (n : ℕ) :
      (((Tn n).traceLeft : Matrix (κ × δ) (κ × δ) ℂ).traceRight :
          Matrix κ κ ℂ) =
        K + algebraMap ℝ (Matrix κ κ ℂ)
              ((Fintype.card δ : ℝ) * ((Fintype.card ι : ℝ) * rn n)) := by
    rw [Un]
    simpa [K] using
      (Matrix.traceRight_add_r_one
        (T := U) (r := ((Fintype.card ι : ℝ) * rn n)))
  have Wn (n : ℕ) :
      (((Tn n).reindex q q : Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ).traceRight :
          Matrix (ι × κ) (ι × κ) ℂ) =
        W + algebraMap ℝ (Matrix (ι × κ) (ι × κ) ℂ)
              ((Fintype.card δ : ℝ) * rn n) := by
    rw [Vn]
    simpa [W] using
      (Matrix.traceRight_add_r_one (T := V) (r := rn n))
  have hn (n : ℕ) :
       entropy (Tn n) + entropy
         (((Tn n).traceLeft : Matrix (κ × δ) (κ × δ) ℂ).traceRight : Matrix κ κ ℂ) ≤
       entropy
         (((Tn n).reindex q q : Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ).traceRight :
            Matrix (ι × κ) (ι × κ) ℂ) +
       entropy ((Tn n).traceLeft : Matrix (κ × δ) (κ × δ) ℂ) := by
    simpa [q] using (pd (Tn n) (htndef n))
  -- Each of the four real expressions has an honest limit.  Notice in the
  -- `K` term the coefficient `|δ| |ι|`; a regularization of a single cross
  -- logarithm would miss exactly this multiplicity.
  have t1 : Filter.Tendsto (fun n : ℕ => entropy (Tn n)) Filter.atTop
      (nhds (entropy T)) := by
    simpa [Tn, rn] using
      (tendsto_entropy_add_c_invNat_one T hT.isHermitian (1:ℝ))
  have tU : Filter.Tendsto (fun n : ℕ =>
        entropy ((Tn n).traceLeft : Matrix (κ × δ) (κ × δ) ℂ))
        Filter.atTop (nhds (entropy U)) := by
    have z := tendsto_entropy_add_c_invNat_one U hU.isHermitian
          (Fintype.card ι : ℝ)
    simpa [Un, rn] using z
  have tW : Filter.Tendsto (fun n : ℕ =>
        entropy (((Tn n).reindex q q :
          Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ).traceRight :
            Matrix (ι × κ) (ι × κ) ℂ))
        Filter.atTop (nhds (entropy W)) := by
    have z := tendsto_entropy_add_c_invNat_one W hW.isHermitian
          (Fintype.card δ : ℝ)
    convert z using 1
    ext n
    rw [Wn]
  have tK : Filter.Tendsto (fun n : ℕ =>
        entropy (((Tn n).traceLeft : Matrix (κ × δ) (κ × δ) ℂ).traceRight :
          Matrix κ κ ℂ))
        Filter.atTop (nhds (entropy K)) := by
    have z := tendsto_entropy_add_c_invNat_one K hK.isHermitian
          ((Fintype.card δ : ℝ) * (Fintype.card ι : ℝ))
    convert (show Filter.Tendsto
      (fun n : ℕ => entropy
        (K + algebraMap ℝ (Matrix κ κ ℂ)
          (((Fintype.card δ : ℝ) * (Fintype.card ι : ℝ)) *
              ((n:ℝ)+1)⁻¹))) _ _ from z) using 1
    ext n
    rw [Kn]
    have eqs :
      (Fintype.card δ : ℝ) * ((Fintype.card ι : ℝ) * rn n) =
        ((Fintype.card δ : ℝ) * (Fintype.card ι : ℝ)) * ((n:ℝ)+1)⁻¹ := by
          dsimp [rn]
          ring
    rw [eqs]
  have lhs_lim : Filter.Tendsto
      (fun n : ℕ => entropy (Tn n) +
        entropy (((Tn n).traceLeft : Matrix (κ × δ) (κ × δ) ℂ).traceRight :
          Matrix κ κ ℂ)) Filter.atTop (nhds (entropy T + entropy K)) :=
    t1.add tK
  have rhs_lim : Filter.Tendsto
      (fun n : ℕ =>
        entropy (((Tn n).reindex q q : Matrix ((ι × κ) × δ) ((ι × κ) × δ) ℂ).traceRight :
          Matrix (ι × κ) (ι × κ) ℂ) +
        entropy ((Tn n).traceLeft : Matrix (κ × δ) (κ × δ) ℂ))
       Filter.atTop (nhds (entropy W + entropy U)) :=
    tW.add tU
  have lim_le : entropy T + entropy K ≤ entropy W + entropy U :=
    le_of_tendsto_of_tendsto lhs_lim rhs_lim (Filter.Eventually.of_forall hn)
  simpa [U, V, K, W, q] using lim_le

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem strong_subadditivity (M_ABC : Matrix (A × B × C) (A × B × C) ℂ) (h : M_ABC.PosSemidef) :
    let M_AB : Matrix (A × B) (A × B) ℂ :=
      .traceRight <| M_ABC.reindex (.symm <| .prodAssoc ..) (.symm <| .prodAssoc ..)
    let M_BC : Matrix (B × C) (B × C) ℂ := M_ABC.traceLeft
    let M_B : Matrix B B ℂ := M_BC.traceRight
    entropy M_ABC + entropy M_B ≤ entropy M_AB + entropy M_BC :=
/-ResultProofBegin-/by
  classical
  dsimp
  refine ssa_of_forall_posDef (ι:=A) (κ:=B) (δ:=C) ?_ M_ABC h
  clear h M_ABC
  intro M_ABC hpd
  have h : M_ABC.PosSemidef := hpd.posSemidef
  -- First all three of the matrices which occur as marginals really are
  -- positive semidefinite.  The associativity reindexing is a bijective
  -- submatrix; the two partial traces are sums of principal submatrices.
  let e : (A × B × C) ≃ ((A × B) × C) := (Equiv.prodAssoc A B C).symm
  have hepd :
      (M_ABC.reindex e e : Matrix ((A × B) × C) ((A × B) × C) ℂ).PosDef := by
    simpa [Matrix.reindex_apply] using
      (hpd.submatrix (by intro i j z; exact e.symm.injective z))
  have hABpd :
      ((M_ABC.reindex e e).traceRight : Matrix (A × B) (A × B) ℂ).PosDef :=
    Matrix.PosDef.traceRight hepd
  have hBCpd : (M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ).PosDef :=
    Matrix.PosDef.traceLeft hpd
  have hBpd : ((M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ).traceRight :
       Matrix B B ℂ).PosDef := Matrix.PosDef.traceRight hBCpd
  have he :
      (M_ABC.reindex e e : Matrix ((A × B) × C) ((A × B) × C) ℂ).PosSemidef :=
    Matrix.PosSemidef.reindex_self h e
  have hAB :
      ((M_ABC.reindex e e).traceRight : Matrix (A × B) (A × B) ℂ).PosSemidef :=
    Matrix.PosSemidef.traceRight he
  have hBC : (M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ).PosSemidef :=
    Matrix.PosSemidef.traceLeft h
  have hB : ((M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ).traceRight :
      Matrix B B ℂ).PosSemidef :=
    Matrix.PosSemidef.traceRight hBC
  -- The four spectra below consist of non-negative reals of the same total
  -- mass.  These facts are often convenient when applying convexity to the
  -- elementary `negMulLog` expression.
  have trAB : Matrix.trace
        ((M_ABC.reindex e e : Matrix ((A × B) × C) ((A × B) × C) ℂ).traceRight) =
        Matrix.trace M_ABC := by
    calc
      _ = Matrix.trace (M_ABC.reindex e e :
            Matrix ((A × B) × C) ((A × B) × C) ℂ) :=
          Matrix.trace_traceRight _
      _ = Matrix.trace M_ABC := Matrix.trace_reindex_self _ _
  have trBC : Matrix.trace (M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ) =
        Matrix.trace M_ABC := Matrix.trace_traceLeft _
  have trB : Matrix.trace
        ((M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ).traceRight) =
        Matrix.trace M_ABC := (Matrix.trace_traceRight _).trans trBC
  have sumAB : (∑ i, hAB.isHermitian.eigenvalues i) =
        ∑ i, h.isHermitian.eigenvalues i := by
    have q := congrArg Complex.re trAB
    -- Hermitian trace is the sum of its (real) eigenvalues.
    rw [hAB.isHermitian.trace_eq_sum_eigenvalues,
      h.isHermitian.trace_eq_sum_eigenvalues] at q
    simpa using q
  have sumBC : (∑ i, hBC.isHermitian.eigenvalues i) =
        ∑ i, h.isHermitian.eigenvalues i := by
    have q := congrArg Complex.re trBC
    rw [hBC.isHermitian.trace_eq_sum_eigenvalues,
      h.isHermitian.trace_eq_sum_eigenvalues] at q
    simpa using q
  have sumB : (∑ i, hB.isHermitian.eigenvalues i) =
        ∑ i, h.isHermitian.eigenvalues i := by
    have q := congrArg Complex.re trB
    rw [hB.isHermitian.trace_eq_sum_eigenvalues,
      h.isHermitian.trace_eq_sum_eigenvalues] at q
    simpa using q

  have evABC (i : A × B × C) : 0 ≤ h.isHermitian.eigenvalues i :=
    Matrix.PosSemidef.eigenvalues_nonneg h i
  have evAB (i : A × B) : 0 ≤ hAB.isHermitian.eigenvalues i :=
    Matrix.PosSemidef.eigenvalues_nonneg hAB i
  have evBC (i : B × C) : 0 ≤ hBC.isHermitian.eigenvalues i :=
    Matrix.PosSemidef.eigenvalues_nonneg hBC i
  have evB (i : B) : 0 ≤ hB.isHermitian.eigenvalues i :=
    Matrix.PosSemidef.eigenvalues_nonneg hB i

  change entropy M_ABC +
        entropy ((M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ).traceRight) ≤
      entropy ((M_ABC.reindex e e : Matrix ((A × B) × C) ((A × B) × C) ℂ).traceRight) +
        entropy (M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ)
  -- At this point no statement about the four unordered spectra can imply the
  -- result.  It is precisely monotonicity of relative entropy for the partial
  -- trace over C.  The following reduction keeps the missing analytic
  -- inequality isolated, and proves the cancellation (including zero
  -- eigenvalues) rather than silently assuming an inverse marginal.
  have compat :
      (((M_ABC.reindex e e : Matrix ((A × B) × C) ((A × B) × C) ℂ).traceRight :
          Matrix (A × B) (A × B) ℂ).traceLeft : Matrix B B ℂ) =
        ((M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ).traceRight : Matrix B B ℂ) := by
    simpa [e] using (Matrix.traceLeft_traceRight_assoc (T := M_ABC))
  have cancel₁ :=
    matrixQRel_leftId_of_traceLeft (T := M_ABC) h.isHermitian
  have cancel₂ :=
    matrixQRel_leftId_of_traceLeft
      (T := ((M_ABC.reindex e e : Matrix ((A × B) × C) ((A × B) × C) ℂ).traceRight :
        Matrix (A × B) (A × B) ℂ)) hAB.isHermitian
  rw [compat] at cancel₂
  suffices mono :
      matrixQRel M_ABC
        (SSAux.leftIdHom A (B × C)
          (M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ)) ≥
      matrixQRel
        ((M_ABC.reindex e e : Matrix ((A × B) × C) ((A × B) × C) ℂ).traceRight :
          Matrix (A × B) (A × B) ℂ)
        (SSAux.leftIdHom A B
          ((M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ).traceRight : Matrix B B ℂ)) by
    rw [cancel₁, cancel₂] at mono
    linarith
  -- This is the genuine data-processing inequality for the indicated
  -- marginal pair `(X, I_A ⊗ X_BC)`.  All equalities needed to state it in the
  -- presence of singular marginals have been discharged above.  The channel
  -- itself is now available as an actual finite unitary average.  Moving `C`
  -- into the first coordinate is important here; averaging signs on `A`
  -- would be the wrong trace.
  let R : Matrix (C × (A × B)) (C × (A × B)) ℂ :=
      (M_ABC.reindex e e : Matrix ((A × B) × C) ((A × B) × C) ℂ).reindex
        (SSAux.swapTensor (A × B) C) (SSAux.swapTensor (A × B) C)
  have Rpos : R.PosSemidef :=
    Matrix.PosSemidef.reindex_self he (SSAux.swapTensor (A × B) C)
  have Rpd : R.PosDef := by
    dsimp [R]
    simpa [Matrix.reindex_apply] using
      (hepd.submatrix
        (by intro i j z;
            exact (SSAux.swapTensor (A × B) C).symm.injective z))
  have Rleft : (R.traceLeft : Matrix (A × B) (A × B) ℂ) =
      ((M_ABC.reindex e e : Matrix ((A × B) × C) ((A × B) × C) ℂ).traceRight :
        Matrix (A × B) (A × B) ℂ) := by
    exact Matrix.swap_traceLeft _
  have channel := Matrix.average_fullTwist_traceLeft (T:=R)
  -- put the other member of the pair through *the same* change of coordinates;
  -- using the trace of `R` here instead gives the wrong marginal.
  let Yo : Matrix (A × (B × C)) (A × (B × C)) ℂ :=
       SSAux.leftIdHom A (B × C)
          (M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ)
  have Yop : Yo.PosSemidef := Matrix.PosSemidef.leftIdHom hBC
  have Yopd : Yo.PosDef := Matrix.PosDef.leftIdHom hBCpd
  let Y1 : Matrix ((A × B) × C) ((A × B) × C) ℂ := Yo.reindex e e
  have Y1p : Y1.PosSemidef := Matrix.PosSemidef.reindex_self Yop e
  have Y1pd : Y1.PosDef := by
    dsimp [Y1]
    simpa [Matrix.reindex_apply] using
      (Yopd.submatrix (by intro i j z; exact e.symm.injective z))
  let Y : Matrix (C × (A × B)) (C × (A × B)) ℂ :=
       Y1.reindex (SSAux.swapTensor (A × B) C) (SSAux.swapTensor (A × B) C)
  have Yp : Y.PosSemidef :=
       Matrix.PosSemidef.reindex_self Y1p (SSAux.swapTensor (A × B) C)
  have Ypd : Y.PosDef := by
       dsimp [Y]
       simpa [Matrix.reindex_apply] using
         (Y1pd.submatrix (by
         intro i j z
         exact (SSAux.swapTensor (A × B) C).symm.injective z))
  have Yleft : (Y.traceLeft : Matrix (A × B) (A × B) ℂ) =
        SSAux.leftIdHom A B
          ((M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ).traceRight :
            Matrix B B ℂ) := by
    -- this calculation is independent of `M_ABC`; on a block matrix it is
    -- simply `∑_c δ_{aa'} S_(b,c),(b',c)`.
    simpa [Yo, Y1, Y, e, SSAux.swapTensor] using
      (Matrix.traceLeft_swap_assoc_leftId
        (ι:=A) (κ:=B) (δ:=C)
        (S := (M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ)))
  have channelY := Matrix.average_fullTwist_traceLeft (T:=Y)

  have leftTransport : matrixQRel M_ABC
          (SSAux.leftIdHom A (B × C)
             (M_ABC.traceLeft : Matrix (B × C) (B × C) ℂ)) =
        matrixQRel R Y := by
    have r₁ := matrixQRel_reindex e M_ABC Yo h.isHermitian Yop.isHermitian
    have r₂ := matrixQRel_reindex (SSAux.swapTensor (A × B) C)
        (M_ABC.reindex e e : Matrix ((A × B) × C) ((A × B) × C) ℂ)
        Y1 he.isHermitian Y1p.isHermitian
    -- isolate the definitions so no associativity reindex is guessed by simp
    change matrixQRel M_ABC Yo = matrixQRel R Y
    exact (r₂.trans r₁).symm

  -- Everything outside this inequality is now deterministic bookkeeping.  In
  -- these coordinates it is precisely joint convexity for the finite family
  -- `(fullTwist s u R, fullTwist s u Y)`.  The right two identifications are
  -- `channel` and `channelY`; they use the *same* coefficient.  Stating it for
  -- the resulting blocks avoids silently twirling on `A`.
  -- `channel` and `channelY` identify its two barycentres with the same
  -- uniform coefficient.  The analytic joint-convexity inequality (with its
  -- support-face extension at zero) is the remaining step.
  -- No entropy terms remain on the analytic side: it is the information
  -- loss in erasing the *first* coordinate of a pair of blocks.
  rw [leftTransport]
  rw [← Rleft, ← Yleft]
  -- Everything singular has been removed before this point by
  -- `ssa_of_forall_posDef`: `R` and `Y` are now actually positive
  -- *definite*.  Algebraically a conditional expectation is a finite
  -- unitary average, so finite Jensen is the only use we make of joint
  -- convexity.
  have joint : ConvexOn ℝ
      {p : Matrix (C × (A × B)) (C × (A × B)) ℂ ×
           Matrix (C × (A × B)) (C × (A × B)) ℂ |
           p.1.PosDef ∧ p.2.PosDef}
      (fun p => matrixQRel p.1 p.2) := by
    refine ⟨convex_pair_posDef, ?_⟩
    intro X hX Y hY a b ha hb hab
    rcases lt_or_eq_of_le ha with ha' | rfl
    · rcases lt_or_eq_of_le hb with hb' | rfl
      · have hL : (a • X.1 + b • Y.1).PosDef :=
            (Matrix.PosDef.smul hX.1 ha').add (Matrix.PosDef.smul hY.1 hb')
        have hR : (a • X.2 + b • Y.2).PosDef :=
            (Matrix.PosDef.smul hX.2 ha').add (Matrix.PosDef.smul hY.2 hb')
        -- the only genuine analytic interior.  We display its exact matrix
        -- content (the two pairs have no zero eigenvalues).  This is the
        -- standard joint-convexity theorem for quantum relative entropy.
        change matrixQRel (a • X.1 + b • Y.1) (a • X.2 + b • Y.2) ≤
          a * matrixQRel X.1 X.2 + b * matrixQRel Y.1 Y.2
        -- The immediately weaker scalar ``log concavity'' used in a naive
        -- proof is in fact an *operator* inequality.  Work with its precise
        -- Loewner version; this is often an implicit prerequisite of the
        -- perspective argument.  It lives on ordinary matrices, not on an
        -- unmentioned ambient order: `JointBridge` transports
        -- `CFC.concaveOn_log` from the type copy `CStarMatrix`.
        have log₂ : (cfc Real.log (a • X.2 + b • Y.2) -
            (a • cfc Real.log X.2 + b • cfc Real.log Y.2)).PosSemidef :=
          SSAuxJoint.cfc_log_concave_matrix X.2 Y.2 hX.2 hY.2 a b
            (le_of_lt ha') (le_of_lt hb') hab
        have log₁ : (cfc Real.log (a • X.1 + b • Y.1) -
            (a • cfc Real.log X.1 + b • cfc Real.log Y.1)).PosSemidef :=
          SSAuxJoint.cfc_log_concave_matrix X.1 Y.1 hX.1 hY.1 a b
            (le_of_lt ha') (le_of_lt hb') hab
        have zpos : (a • X.1 + b • Y.1).PosSemidef := hL.posSemidef
        have tlog₂ : 0 ≤ Complex.re (Matrix.trace
             ((a • X.1 + b • Y.1) *
               (cfc Real.log (a • X.2 + b • Y.2) -
                 (a • cfc Real.log X.2 + b • cfc Real.log Y.2)))) :=
          SSAuxJoint.trace_mul_nonneg _ _ zpos log₂
        -- What `log₂` says is only concavity in the *second* operator.  The
        -- mixed trace below pairs it with the first operator, so this alone
        -- is not scalar convexity.  The remaining step is Jensen for the
        -- perspective of `-log` (equivalently the relative modular operator).
        -- Keeping both weighted inputs positive and spelling out the defect
        -- is a convenient fully checked starting point for that compression
        -- lemma; applying scalar Jensen to eigenvalues here would be invalid,
        -- since the four eigenbases need not commute.
        -- On the Hilbert--Schmidt lift the logarithm really splits over the
        -- two commuting tensor factors.  This finite-dimensional identity is
        -- the base calculation in the relative modular proof (and needs
        -- positive *definite*, not merely Hermitian, factors).
        have modular_log_X :
            cfc Real.log (X.1 ⊗ₖ X.2) =
              (cfc Real.log X.1) ⊗ₖ
                  (1 : Matrix (C × (A × B)) (C × (A × B)) ℂ) +
                (1 : Matrix (C × (A × B)) (C × (A × B)) ℂ) ⊗ₖ
                  (cfc Real.log X.2) :=
          SSAuxMod.log_kron X.1 X.2 hX.1 hX.2
        have modular_log_Y :
            cfc Real.log (Y.1 ⊗ₖ Y.2) =
              (cfc Real.log Y.1) ⊗ₖ
                  (1 : Matrix (C × (A × B)) (C × (A × B)) ℂ) +
                (1 : Matrix (C × (A × B)) (C × (A × B)) ℂ) ⊗ₖ
                  (cfc Real.log Y.2) :=
          SSAuxMod.log_kron Y.1 Y.2 hY.1 hY.2
        -- The subtle Jensen ingredient is a statement for a *rectangular*
        -- isometry, not scalar concavity.  This is often the first missing
        -- step in this reduction.  It is useful in this form since no
        -- extension of the isometry to a unitary basis is involved.  In
        -- `SSAuxComp.log_compress` it has now been proved: reflect in the
        -- range projection `K Kᴴ`, average `P` with the reflected matrix,
        -- use operator concavity of log for this pair, and apply the
        -- rectangular intertwining lemma.  Here is the specialized
        -- application to either of the positive lift blocks; it is the
        -- Jensen compression which will be needed for the direct-sum
        -- Stinespring column.
        let idx := (C × (A × B))
        have compX :
            (cfc Real.log ((1 : Matrix (idx × idx) (idx × idx) ℂ).conjTranspose *
                    (X.1 ⊗ₖ X.2) * (1 : Matrix (idx × idx) (idx × idx) ℂ)) -
              (1 : Matrix (idx × idx) (idx × idx) ℂ).conjTranspose *
                  cfc Real.log (X.1 ⊗ₖ X.2) *
                     (1 : Matrix (idx × idx) (idx × idx) ℂ)).PosSemidef := by
          have kp : (X.1 ⊗ₖ X.2).PosDef :=
            Matrix.PosDef.kronecker hX.1 hX.2
          exact SSAuxComp.log_compress (X.1 ⊗ₖ X.2) kp
             (1 : Matrix (idx × idx) (idx × idx) ℂ) (by simp)
        have compY :
            (cfc Real.log ((1 : Matrix (idx × idx) (idx × idx) ℂ).conjTranspose *
                    (Y.1 ⊗ₖ Y.2) * (1 : Matrix (idx × idx) (idx × idx) ℂ)) -
              (1 : Matrix (idx × idx) (idx × idx) ℂ).conjTranspose *
                  cfc Real.log (Y.1 ⊗ₖ Y.2) *
                     (1 : Matrix (idx × idx) (idx × idx) ℂ)).PosSemidef := by
          have kp : (Y.1 ⊗ₖ Y.2).PosDef :=
            Matrix.PosDef.kronecker hY.1 hY.2
          exact SSAuxComp.log_compress (Y.1 ⊗ₖ Y.2) kp
             (1 : Matrix (idx × idx) (idx × idx) ℂ) (by simp)
        -- The remaining construction is the nontrivial direct-sum column
        -- (its right factors are the square roots of the two first
        -- densities).  `compX`/`compY` show exactly which Jensen theorem is
        -- available, without the illicit simultaneous diagonalisation of
        -- the four matrices.
        -- First do the rectangular Jensen step for the actual *two block*
        -- column.  `log_compress` alone only treats one square block (in
        -- earlier versions of the reduction it was inadvertently applied to
        -- the identity column, which says 0=0).  The sum index of the
        -- Stinespring space is important.  `log_compress_two` constructs
        -- `fromBlocks P 0 0 Q : Matrix (h ⊕ h)` and the column `col2 U V`;
        -- it proves the off--diagonal CFC entries vanish by the rectangular
        -- intertwining lemma rather than a fictitious diagonalisation.
        let ca : ℝ := Real.sqrt a
        let cb : ℝ := Real.sqrt b
        have ca2 : ca ^ 2 = a := by
          dsimp [ca]
          exact Real.sq_sqrt (le_of_lt ha')
        have cb2 : cb ^ 2 = b := by
          dsimp [cb]
          exact Real.sq_sqrt (le_of_lt hb')
        let Uc : Matrix (idx × idx) (idx × idx) ℂ :=
          ca • (1 : Matrix (idx × idx) (idx × idx) ℂ)
        let Vc : Matrix (idx × idx) (idx × idx) ℂ :=
          cb • (1 : Matrix (idx × idx) (idx × idx) ℂ)
        have UVone : Uc.conjTranspose * Uc + Vc.conjTranspose * Vc =
              (1 : Matrix (idx × idx) (idx × idx) ℂ) := by
          have scalar : (ca:ℂ)*(ca:ℂ) + (cb:ℂ)*(cb:ℂ) = 1 := by
            norm_cast
            nlinarith
          -- doing this entrywise keeps real/complex smul coercions explicit
          classical
          ext i j
          by_cases z:i=j
          · subst j
            simp [Uc, Vc, Matrix.mul_apply, Matrix.one_apply,
              RCLike.real_smul_eq_coe_mul, scalar]
          · simp [Uc, Vc, Matrix.mul_apply, Matrix.one_apply,
                  RCLike.real_smul_eq_coe_mul, z]
        have blockJ :
            (cfc Real.log
                (Uc.conjTranspose * (X.1 ⊗ₖ X.2) * Uc +
                 Vc.conjTranspose * (Y.1 ⊗ₖ Y.2) * Vc) -
              (Uc.conjTranspose * cfc Real.log (X.1 ⊗ₖ X.2) * Uc +
                 Vc.conjTranspose * cfc Real.log (Y.1 ⊗ₖ Y.2) * Vc)).PosSemidef := by
          exact SSAuxDS.log_compress_two
             (X.1 ⊗ₖ X.2) (Y.1 ⊗ₖ Y.2) Uc Vc
             (Matrix.PosDef.kronecker hX.1 hX.2)
             (Matrix.PosDef.kronecker hY.1 hY.2) UVone
        -- We will not use a positive tensor of the two densities in the
        -- perspective calculation.  The correct modular blocks have the
        -- *inverse transpose* of the first density as their right factor.
        -- They too are honest positive definite matrices; transposition is
        -- delicate over `ℂ` and is the reason for the separate spectral
        -- lemma `posDef_transpose`.
        let PX : Matrix (idx × idx) (idx × idx) ℂ :=
              X.2 ⊗ₖ (X.1⁻¹).transpose
        let PY : Matrix (idx × idx) (idx × idx) ℂ :=
              Y.2 ⊗ₖ (Y.1⁻¹).transpose
        have px : PX.PosDef := by
          dsimp [PX]
          exact Matrix.PosDef.kronecker hX.2
            (SSAuxT.posDef_transpose _ (Matrix.PosDef.inv hX.1))
        have py : PY.PosDef := by
          dsimp [PY]
          exact Matrix.PosDef.kronecker hY.2
            (SSAuxT.posDef_transpose _ (Matrix.PosDef.inv hY.1))
        -- Thus there is already a *real* sum-space Jensen inequality for
        -- the relative modular blocks (not merely for the harmless tensor
        -- used above). This isolates the last unsolved algebraic step: change
        -- `Uc,Vc` to the normalized right multiplications.  All CFC on the
        -- direct sum and all off-diagonal assertions have disappeared.
        have modularBlockJ :
            (cfc Real.log
                (Uc.conjTranspose * PX * Uc +
                 Vc.conjTranspose * PY * Vc) -
              (Uc.conjTranspose * cfc Real.log PX * Uc +
                 Vc.conjTranspose * cfc Real.log PY * Vc)).PosSemidef := by
          exact SSAuxDS.log_compress_two PX PY Uc Vc px py UVone
        -- `blockJ` is Jensen on the direct sum (not the tautological identity
        -- compression `compX`).  What is left is to replace the scalar
        -- columns by right multiplications by `sqrt X.1` and `sqrt Y.1`;
        -- the second tensor factor then becomes `X.1⁻ᵀ`/`Y.1⁻ᵀ` and
        -- `Transpose.cfc_log_inv` plus cyclic trace give the claimed
        -- perspective.  No simultaneous choice of eigenbasis is possible.
        exact SSAuxPers.trace_joint X.1 X.2 Y.1 Y.2
          hX.1 hX.2 hY.1 hY.2 a b ha' hb'
      · have haa : a = 1 := by simpa using hab
        subst a
        simp
    · have hbb : b = 1 := by simpa using hab
      subst b
      simp
  exact matrixQRel_twirl_le_of_convexOn
      (d:=C) (m:= A × B) joint R Y Rpd Ypd/-ResultProofEnd-/
/-ResultEnd-/

end Submission
