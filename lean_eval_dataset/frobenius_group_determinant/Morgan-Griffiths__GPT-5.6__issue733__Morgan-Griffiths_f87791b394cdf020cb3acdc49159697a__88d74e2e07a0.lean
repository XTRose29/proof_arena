import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Foundation.lean

/-!
Elementary polynomial facts used for the group determinant.  These are kept separate from
its definition: it is the matrix `(fun g h => X (g*h))` in the statement file.
-
In particular the determinant is a *nonzero homogeneous* polynomial.  A useful point in
the non-vanishing argument is that no result about representations is needed: putting one
in the coordinate of the identity and zero in all the other coordinates gives a
permutation matrix (inversion of the group).
-/

open Matrix MvPolynomial BigOperators
open scoped BigOperators
noncomputable section
namespace FrobeniusDeterminantSupport

/-- The involution `g ↦ g⁻¹`, regarded just as a permutation of the underlying
finite set.  It is a permutation also when the group is non-abelian. -/
def invEquiv (H : Type*) [Group H] : Equiv.Perm H where
  toFun := fun g => g⁻¹
  invFun := fun g => g⁻¹
  left_inv g := inv_inv g
  right_inv g := inv_inv g

variable (H : Type*) [Group H] [Fintype H] [DecidableEq H]

/-- Evaluation of the variables at the characteristic function of `1` takes the
matrix with entries `X_(g*h)` to the permutation matrix for inversion.  Writing
this explicitly is occasionally a little easier than multiplying delta-functions. -/
lemma eval_group_matrix :
  ((MvPolynomial.eval (fun t : H => if t = 1 then (1:ℂ) else 0)).mapMatrix
    (fun g : H => fun h : H => (MvPolynomial.X (R:=ℂ) (g*h))))
   = Equiv.Perm.permMatrix ℂ (invEquiv H) := by
  ext g h
  change (MvPolynomial.eval (fun t : H => if t = 1 then (1:ℂ) else 0))
      (MvPolynomial.X (g*h)) = _
  rw [MvPolynomial.eval_X]
  change (ite (g*h=1) 1 0 : ℂ) =
    (if h ∈ (Equiv.toPEquiv (invEquiv H)) g then 1 else 0)
  simp [Equiv.toPEquiv, invEquiv, mul_eq_one_iff_eq_inv, inv_eq_iff_eq_inv]

/-- Consequently the determinant of that polynomial matrix is nonzero.  The
proof works in every characteristic zero codomain of the evaluation; here using
`ℂ` means the sign of a permutation certainly remains nonzero. -/
lemma group_matrix_det_ne_zero :
 Matrix.det ((fun g : H => fun h : H => (MvPolynomial.X (R:=ℂ) (g*h))) :
     Matrix H H (MvPolynomial H ℂ)) ≠ 0 := by
  classical
  let f := (MvPolynomial.eval (fun t : H => if t = 1 then (1:ℂ) else 0))
  let A : Matrix H H (MvPolynomial H ℂ) := (fun g h => MvPolynomial.X (g*h))
  have hmap : f.mapMatrix A = Equiv.Perm.permMatrix ℂ (invEquiv H) :=
    eval_group_matrix H
  have hdetmap : f A.det = (Equiv.Perm.permMatrix ℂ (invEquiv H)).det := by
    rw [RingHom.map_det]
    rw [hmap]
  have hsign : ((Equiv.Perm.permMatrix ℂ (invEquiv H)).det) ≠ 0 := by
    rw [Matrix.det_permutation]
    norm_num
  change A.det ≠ 0
  intro h
  have he : f A.det = 0 := by rw [h]; exact map_zero f
  exact hsign (hdetmap ▸ he)

variable {ι σ R:Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- A determinant whose entries are homogeneous of degree one is homogeneous
of degree the size of the indexing type.  Keeping this lemma for arbitrary
coefficient rings is helpful: the only use of subtraction is the sign in the
Leibniz formula. -/
lemma det_isHomogeneous (A : Matrix ι ι (MvPolynomial σ R))
    (hA : ∀ i j, (A i j).IsHomogeneous 1) :
    A.det.IsHomogeneous (Fintype.card ι) := by
  classical
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro p hp
  have hprod : (∏ i : ι, A (p i) i).IsHomogeneous
      (∑ _i : ι, (1 : ℕ)) := by
    simpa using (MvPolynomial.IsHomogeneous.prod (Finset.univ) (fun i : ι => A (p i) i)
      (fun _i => (1:ℕ)) (by
        intro i hi; exact hA _ _))
  have hprod' : (∏ i : ι, A (p i) i).IsHomogeneous (Fintype.card ι) := by
    simpa using hprod
  have hc : ( ( (↑(↑(p.sign) : ℤ) : MvPolynomial σ R))).IsHomogeneous 0 := by
    simpa using (MvPolynomial.isHomogeneous_C (σ) ((↑(↑(p.sign) : ℤ) : R)))
  simpa using hc.mul hprod'

variable {K : Type*} [Group K] [Fintype K] [DecidableEq K]

lemma group_matrix_det_isHomogeneous :
   (Matrix.det ((fun g : K => fun h : K => (MvPolynomial.X (R:=ℂ) (g*h))) :
    Matrix K K (MvPolynomial K ℂ))).IsHomogeneous (Fintype.card K) := by
    apply det_isHomogeneous
    intro g h
    exact MvPolynomial.isHomogeneous_X (R:=ℂ) _

lemma group_matrix_totalDegree :
   (Matrix.det ((fun g : K => fun h : K => (MvPolynomial.X (R:=ℂ) (g*h))) :
    Matrix K K (MvPolynomial K ℂ))).totalDegree = Fintype.card K := by
  apply group_matrix_det_isHomogeneous.totalDegree
  exact group_matrix_det_ne_zero K


/-- The convention `X_(g*h)` in the statement differs from the left-regular
convention by the column permutation `h ↦ h⁻¹`.  Keeping track of this sign is
important in later linear representation arguments. -/
lemma column_inversion (T : Type*) [Group T] [Fintype T] [DecidableEq T] :
 let A : Matrix T T (MvPolynomial T ℂ) := fun g h => X (g*h)
 let B : Matrix T T (MvPolynomial T ℂ) := fun g h => X (g*h⁻¹)
 A = B * (Equiv.Perm.permMatrix (MvPolynomial T ℂ) (invEquiv T)) := by
  dsimp
  let B : Matrix T T (MvPolynomial T ℂ) := fun g h => X (g*h⁻¹)
  change _ = B * (invEquiv T).toPEquiv.toMatrix
  rw [PEquiv.mul_toMatrix_toPEquiv]
  ext g h
  simp [B, invEquiv]

lemma det_column_inversion (T : Type*) [Group T] [Fintype T] [DecidableEq T] :
 (Matrix.det ((fun g : T => fun h : T => (X (R:=ℂ) (g*h))) : Matrix T T (MvPolynomial T ℂ))) =
 (Matrix.det ((fun g : T => fun h : T => (X (R:=ℂ) (g*h⁻¹))) : Matrix T T (MvPolynomial T ℂ))) *
   ( (↑(↑((invEquiv T).sign) : ℤ) : MvPolynomial T ℂ)) := by
  let A : Matrix T T (MvPolynomial T ℂ) := fun g h => X (g*h)
  let B : Matrix T T (MvPolynomial T ℂ) := fun g h => X (g*h⁻¹)
  let P : Matrix T T (MvPolynomial T ℂ) := Equiv.Perm.permMatrix _ (invEquiv T)
  change A.det = B.det * ( (↑(↑((invEquiv T).sign) : ℤ) : MvPolynomial T ℂ))
  have hab : A = B * P := column_inversion T
  rw [hab]
  rw [Matrix.det_mul]
  have hp : P.det = ( (↑(↑((invEquiv T).sign) : ℤ) : MvPolynomial T ℂ)) := by
    exact Matrix.det_permutation _
  rw [hp]

end FrobeniusDeterminantSupport

end

-- END INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Foundation.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Blocks.lean
open Matrix MvPolynomial BigOperators LinearMap Module
open scoped MonoidAlgebra BigOperators
noncomputable section
namespace FrobeniusDeterminantSupport
lemma leftMulMatrix_matrix {k n : Type*} [CommRing k] [Fintype n] [DecidableEq n]
    (A : Matrix n n k) :
  Algebra.leftMulMatrix (Matrix.stdBasis k n n) A =
    Matrix.blockDiagonal (fun _ : n => A) := by
  classical
  ext ij kl
  rcases ij with ⟨i,j⟩
  rcases kl with ⟨l,m⟩
  simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
        Matrix.blockDiagonal_apply, Matrix.mul_apply, Matrix.stdBasis]
  by_cases h : j = m
  · subst m
    simp [Pi.single_apply, *, mul_ite, ite_apply]
  · simp [Pi.single_apply, h, ite_apply]
lemma norm_matrix {k n : Type*} [CommRing k] [Fintype n] [DecidableEq n]
    (A : Matrix n n k) :
    Algebra.norm k A = (Matrix.det A) ^ Fintype.card n := by
  classical
  rw [Algebra.norm_eq_matrix_det (Matrix.stdBasis k n n)]
  rw [leftMulMatrix_matrix A, Matrix.det_blockDiagonal]
  simp
lemma complex_group_blocks (G : Type*) [Group G] [Fintype G] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (MonoidAlgebra ℂ G ≃ₐ[ℂ]
          Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast (Nat.card_pos.ne')⟩
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ _
lemma norm_in_blocks
    {G : Type*} [Group G] [Fintype G]
    {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ]
          Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (x : MonoidAlgebra ℂ G) :
    Algebra.norm ℂ (e x) = Algebra.norm ℂ x := by
  exact Algebra.norm_eq_of_algEquiv e x
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
def blockPoly {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ]
          Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i : Fin n) : MvPolynomial G ℂ :=
  Matrix.det (fun a b : Fin (d i) =>
    ∑ g : G, C (((e (MonoidAlgebra.single g 1)) i) a b) * X g)
lemma blockPoly_isHomogeneous {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ]
          Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i : Fin n) :
    (blockPoly e i).IsHomogeneous (d i) := by
  classical
  unfold blockPoly
  simpa using (det_isHomogeneous
    (A := (fun a b : Fin (d i) =>
      ∑ g : G, C (((e (MonoidAlgebra.single g 1)) i) a b) * X g))
    (fun a b => by
      apply MvPolynomial.IsHomogeneous.sum
      intro g hg
      exact (MvPolynomial.isHomogeneous_C (G) _).mul
        (MvPolynomial.isHomogeneous_X (R:=ℂ) _)))
end FrobeniusDeterminantSupport

end

-- END INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Blocks.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Coordinates.lean
open scoped BigOperators
open MvPolynomial Matrix LinearMap Module
noncomputable section
namespace FrobeniusLinearChange
variable {k σ τ υ V W U : Type*}
variable [Field k]
variable [Fintype σ] [Fintype τ] [Fintype υ]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]
variable [AddCommGroup U] [Module k U]

def lp (b : Basis σ k V) (c : Basis τ k W) (f : V →ₗ[k] W)
    (t : τ) : MvPolynomial σ k :=
  ∑ s : σ, MvPolynomial.C ((c.repr (f (b s))) t) * MvPolynomial.X s

def ls (b : Basis σ k V) (c : Basis τ k W) (f : V →ₗ[k] W) :
    MvPolynomial τ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (lp b c f)

@[simp] lemma ls_X (b : Basis σ k V) (c : Basis τ k W) (f : V →ₗ[k] W)
    (t : τ) : ls b c f (MvPolynomial.X t) = lp b c f t := by
  simp [ls]
@[simp] lemma ls_C (b : Basis σ k V) (c : Basis τ k W) (f : V →ₗ[k] W)
    (x : k) : ls b c f (MvPolynomial.C x) = MvPolynomial.C x := by
  simp [ls]

lemma comp_lp (b : Basis σ k V) (c : Basis τ k W) (d : Basis υ k U)
    (f : V →ₗ[k] W) (g : W →ₗ[k] U) (u : υ) :
    ls b c f (lp c d g u) = lp b d (g.comp f) u := by
  classical
  unfold lp
  -- map outer sum
  simp only [map_sum, map_mul, ls_C, ls_X]
  -- goal sums
  -- distribute and exchange
  simp [lp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [← mul_assoc, ← map_mul]
  rw [← Finset.sum_mul]
  rw [← map_sum]
  congr 2
  have H := congrArg (fun z : W => (d.repr (g z)) u) (c.sum_repr (f (b i)))
  simpa only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, mul_comm] using H

lemma comp_ls (b : Basis σ k V) (c : Basis τ k W) (d : Basis υ k U)
    (f : V →ₗ[k] W) (g : W →ₗ[k] U) :
   (ls b c f).comp (ls c d g) = ls b d (g.comp f) := by
  apply MvPolynomial.algHom_ext
  intro u
  change ls b c f (ls c d g (MvPolynomial.X u)) = ls b d (g.comp f) (MvPolynomial.X u)
  simp only [ls_X]
  exact comp_lp b c d f g u

lemma ls_id (b : Basis σ k V) : ls b b LinearMap.id = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro s
  classical
  simp [ls, lp, Basis.repr_self, Finsupp.single_apply]

-- forward equivalence
def lsEquiv (b : Basis σ k V) (c : Basis τ k W) (f : V ≃ₗ[k] W) :
    MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom (ls b c f) (ls c b f.symm)
    (by
      rw [comp_ls]
      have h : (f.toLinearMap.comp f.symm.toLinearMap) = LinearMap.id := by ext x; simp
      simpa [h] using (ls_id b))
    (by
      rw [comp_ls]
      have h : (f.symm.toLinearMap.comp f.toLinearMap) = LinearMap.id := by ext x; simp
      simpa [h] using (ls_id c))

@[simp] lemma lsEquiv_apply (b : Basis σ k V) (c : Basis τ k W) (f : V ≃ₗ[k] W)
    (p : MvPolynomial τ k) : lsEquiv b c f p = ls b c f p := rfl
@[simp] lemma lsEquiv_X (b : Basis σ k V) (c : Basis τ k W) (f : V ≃ₗ[k] W)
    (t : τ) : lsEquiv b c f (MvPolynomial.X t) = lp b c f t := by simp [lsEquiv]

end FrobeniusLinearChange

namespace FrobeniusDeterminantSupport
open Matrix
private lemma stdrepr {k α β : Type*} [Field k] [Fintype α] [Fintype β]
 (A : Matrix α β k) (a:α) (b:β) :
 ((Matrix.stdBasis k α β).repr A) (a,b) = A a b := by
  classical
  -- expand
  simp [Matrix.stdBasis, Basis.repr_reindex_apply]
open scoped BigOperators MonoidAlgebra
open MvPolynomial Matrix LinearMap Module
noncomputable section

-- reuse Test defs for now
variable {G:Type*} [Group G] [Fintype G] [DecidableEq G]
variable {n:ℕ} {d: Fin n → ℕ}

def blockBasis := Pi.basis (fun i : Fin n => Matrix.stdBasis ℂ (Fin (d i)) (Fin (d i)))

def gpBasis : Basis G ℂ (MonoidAlgebra ℂ G) := MonoidAlgebra.basis G ℂ

def fullBlockDet (i : Fin n) : MvPolynomial (Σ j : Fin n, (Fin (d j) × Fin (d j))) ℂ :=
  Matrix.det (fun a b : Fin (d i) => MvPolynomial.X (⟨i,(a,b)⟩ : Σ j : Fin n, (Fin (d j) × Fin (d j))))

lemma blockBasis_coord (z : Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i : Fin n) (a b : Fin (d i)) :
    ((blockBasis (n:=n) (d:=d)).repr z) (⟨i,(a,b)⟩ : Σ j, (Fin (d j) × Fin (d j))) = z i a b := by
  classical
  change (((Pi.basis (fun j : Fin n => Matrix.stdBasis ℂ (Fin (d j)) (Fin (d j)))).repr z) ⟨i,(a,b)⟩) = _
  rw [Pi.basis_repr]
  exact stdrepr (z i) a b

lemma fullBlockDet_map
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ]
          Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i : Fin n) :
    FrobeniusLinearChange.lsEquiv (gpBasis (G:=G)) (blockBasis (n:=n) (d:=d)) e.toLinearEquiv
      (fullBlockDet (d:=d) i) = blockPoly e i := by
  classical
  unfold fullBlockDet blockPoly
  let E := FrobeniusLinearChange.lsEquiv (gpBasis (G:=G)) (blockBasis (n:=n) (d:=d)) e.toLinearEquiv
  let A : Matrix (Fin (d i)) (Fin (d i))
       (MvPolynomial (Σ j : Fin n, (Fin (d j) × Fin (d j))) ℂ) :=
       (fun a b => MvPolynomial.X (⟨i,(a,b)⟩ : Σ j : Fin n, (Fin (d j) × Fin (d j))))
  change E A.det = _
  change E.toRingEquiv.toRingHom A.det = _
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext a b : 1
  change E (A a b) = _
  change E (MvPolynomial.X (⟨i,(a,b)⟩ : Σ j : Fin n, (Fin (d j) × Fin (d j)))) = _
  change FrobeniusLinearChange.ls (gpBasis (G:=G)) (blockBasis (n:=n) (d:=d)) e.toLinearEquiv
      (MvPolynomial.X (⟨i,(a,b)⟩ : Σ j : Fin n, (Fin (d j) × Fin (d j)))) = _
  simp [FrobeniusLinearChange.lp]
  apply Finset.sum_congr rfl
  intro g hg
  congr 1

lemma blockPoly_irred_of_full
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ]
          Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i : Fin n)
    (h : Irreducible (fullBlockDet (d:=d) i)) :
    Irreducible (blockPoly e i) := by
  rw [← fullBlockDet_map (G:=G) e i]
  exact h.map (FrobeniusLinearChange.lsEquiv (gpBasis (G:=G)) (blockBasis (n:=n) (d:=d)) e.toLinearEquiv)
/-- The remaining polynomial after the linear change is literally the generic determinant;
all variables outside a block are absent. -/
def smallGenericDet (m : ℕ) : MvPolynomial (Fin m × Fin m) ℂ :=
  Matrix.det (fun a b : Fin m => MvPolynomial.X (a,b))

def blockIncl {n : ℕ} {d : Fin n → ℕ} (i : Fin n) :
    (Fin (d i) × Fin (d i)) → (Σ j : Fin n, (Fin (d j) × Fin (d j))) :=
  fun u => ⟨i,u⟩

lemma fullBlockDet_rename {n : ℕ} {d : Fin n → ℕ} (i : Fin n) :
    fullBlockDet (d:=d) i = MvPolynomial.rename (blockIncl (d:=d) i) (smallGenericDet (d i)) := by
  classical
  unfold fullBlockDet smallGenericDet
  let A : Matrix (Fin (d i)) (Fin (d i)) (MvPolynomial (Fin (d i) × Fin (d i)) ℂ) :=
    fun a b => MvPolynomial.X (a,b)
  let B : Matrix (Fin (d i)) (Fin (d i)) (MvPolynomial (Σ j : Fin n, (Fin (d j) × Fin (d j))) ℂ) :=
    fun a b => MvPolynomial.X (blockIncl (d:=d) i (a,b))
  change B.det = MvPolynomial.rename (blockIncl (d:=d) i) A.det
  symm
  change (MvPolynomial.rename (blockIncl (d:=d) i)).toRingHom A.det = B.det
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext a b : 1
  simp [A, B, blockIncl]

lemma fullBlockDet_irred_one {n:ℕ} {d : Fin n → ℕ} (i : Fin n) (h : d i = 1) :
    Irreducible (fullBlockDet (d:=d) i) := by
  classical
  have hu : Unique (Fin (d i)) := h ▸ inferInstance
  letI : Unique (Fin (d i)) := hu
  unfold fullBlockDet
  rw [Matrix.det_unique]
  -- the one coordinate is a variable
  apply MvPolynomial.irreducible_of_totalDegree_eq_one (by simp)
  intro x hx
  apply (isUnit_iff_ne_zero).2
  intro he
  subst x
  have hh := hx (Finsupp.single (⟨i,(default,default)⟩ : Σ j : Fin n, (Fin (d j) × Fin (d j))) 1)
  simpa using hh

lemma blockPoly_irred_one
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ]
          Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i : Fin n) (h : d i = 1) :
    Irreducible (blockPoly e i) :=
  blockPoly_irred_of_full e i (fullBlockDet_irred_one i h)

end
end FrobeniusDeterminantSupport

end

-- END INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Coordinates.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Transfer.lean
open Matrix MvPolynomial BigOperators LinearMap Module
open scoped MonoidAlgebra BigOperators
noncomputable section
namespace FrobeniusDeterminantSupport
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The element of the complex group algebra with coordinate `x g` in the group basis. -/
private def genericEval (x : G → ℂ) : MonoidAlgebra ℂ G :=
  ∑ g : G, MonoidAlgebra.single g (x g)

private lemma genericEval_apply (x : G → ℂ) (g : G) : genericEval x g = x g := by
  classical
  unfold genericEval
  change MonoidAlgebra.coeff (∑ h : G, MonoidAlgebra.single h (x h)) g = _
  rw [MonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply']
  change (∑ h : G, ((Finsupp.single h (x h) : G →₀ ℂ) g)) = _
  simp [Finsupp.single_apply]

lemma leftMulMatrix_generic (x : G → ℂ) :
    Algebra.leftMulMatrix (MonoidAlgebra.basis G ℂ) (genericEval x) =
      ((fun g : G => fun h : G => x (g * h⁻¹)) : Matrix G G ℂ) := by
  classical
  ext g h
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change MonoidAlgebra.coeff ((genericEval x) * MonoidAlgebra.single h 1) g = _
  have H := MonoidAlgebra.mul_single_apply (genericEval x) (1:ℂ) h g
  change MonoidAlgebra.coeff ((genericEval x) * MonoidAlgebra.single h 1) g = _ at H
  rw [H]
  rw [genericEval_apply]
  simp

lemma norm_generic (x : G → ℂ) :
    Algebra.norm ℂ (genericEval x) =
      Matrix.det ((fun g : G => fun h : G => x (g * h⁻¹)) : Matrix G G ℂ) := by
  classical
  rw [Algebra.norm_eq_matrix_det (MonoidAlgebra.basis G ℂ)]
  rw [leftMulMatrix_generic]

-- eval form of blockPoly
lemma eval_blockPoly
    {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ]
          Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i : Fin n) (x : G → ℂ) :
    MvPolynomial.eval x (blockPoly e i) = Matrix.det ((e (genericEval x)) i) := by
  classical
  unfold blockPoly
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [genericEval, map_sum]
  have hsingle (c : G) :
      MonoidAlgebra.single c (x c) =
        (x c) • (MonoidAlgebra.single c (1 : ℂ)) := by
      symm
      simpa using (MonoidAlgebra.smul_single' (x c) c (1 : ℂ))
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro c hc
  rw [hsingle c]
  change _ = e.toLinearMap ((x c) • (MonoidAlgebra.single c (1:ℂ))) i a b
  rw [e.toLinearMap.map_smul]
  simp [Pi.smul_apply, Matrix.smul_apply, mul_comm]


open Matrix in
lemma det_blockDiagonal'
    {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {m : o → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {R : Type*} [CommRing R]
    (A : ∀ i : o, Matrix (m i) (m i) R) :
    Matrix.det (Matrix.blockDiagonal' A) = ∏ i, Matrix.det (A i) := by
  classical
  have h := (Matrix.blockTriangular_blockDiagonal' A).det_fintype
  -- compute square blocks by reindexing their evident fibers
  have hblock (k : o) :
      Matrix.det ((Matrix.blockDiagonal' A).toSquareBlock Sigma.fst k) =
        Matrix.det (A k) := by
    let ek : {z : (Σ i, m i) // z.1 = k} ≃ m k :=
    { toFun := fun z => z.val.2 |> (fun t => _root_.cast (congrArg m z.property) t)
      invFun := fun u => ⟨⟨k,u⟩, rfl⟩
      left_inv := by
        intro z
        rcases z with ⟨⟨i,v⟩, hi⟩
        change i = k at hi
        subst i
        rfl
      right_inv := by intro u; rfl }
    have hm : Matrix.reindex ek ek
          ((Matrix.blockDiagonal' A).toSquareBlock Sigma.fst k) = A k := by
      ext u v
      rw [Matrix.reindex_apply]
      rw [Matrix.toSquareBlock_def]
      simp [ek, Matrix.blockDiagonal'_apply]
    calc
      Matrix.det ((Matrix.blockDiagonal' A).toSquareBlock Sigma.fst k) =
          Matrix.det (Matrix.reindex ek ek
            ((Matrix.blockDiagonal' A).toSquareBlock Sigma.fst k)) :=
            (Matrix.det_reindex_self ek _).symm
      _ = Matrix.det (A k) := by rw [hm]
  classical
  simpa [hblock] using h

end FrobeniusDeterminantSupport
namespace FrobeniusDeterminantSupport
open Matrix LinearMap Module
lemma norm_pi_matrix
    {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {d : o → ℕ} {k : Type*} [CommRing k]
    (A : ∀ i : o, Matrix (Fin (d i)) (Fin (d i)) k) :
    Algebra.norm k A = ∏ i, Algebra.norm k (A i) := by
  classical
  let b : ∀ i : o, Basis (Fin (d i) × Fin (d i)) k
        (Matrix (Fin (d i)) (Fin (d i)) k) :=
      fun i => Matrix.stdBasis k (Fin (d i)) (Fin (d i))
  rw [Algebra.norm_eq_matrix_det (Pi.basis b)]
  have hm : Algebra.leftMulMatrix (Pi.basis b) A =
      Matrix.blockDiagonal'
        (fun i => Algebra.leftMulMatrix (b i) (A i)) := by
    ext iu jv
    rcases iu with ⟨i,u⟩
    rcases jv with ⟨j,v⟩
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    rw [Pi.basis_repr]
    rw [Pi.basis_apply]
    by_cases hij : i = j
    · subst j
      simpa [Matrix.blockDiagonal'_apply, Pi.single_apply]
        using (Algebra.leftMulMatrix_eq_repr_mul (b i) (A i) u v).symm
    · have hji : j ≠ i := Ne.symm hij
      simp [Matrix.blockDiagonal'_apply, hij, Pi.single_apply, hji]
  rw [hm]
  rw [det_blockDiagonal']
  simp_rw [← Algebra.norm_eq_matrix_det]

lemma det_leftRegular_blocks
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ]
          Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    (Matrix.det ((fun g : G => fun h : G =>
        MvPolynomial.X (R:=ℂ) (g*h⁻¹)) : Matrix G G (MvPolynomial G ℂ))) =
        ∏ i : Fin n, (blockPoly e i) ^ (d i) := by
  classical
  apply MvPolynomial.funext
  intro x
  rw [RingHom.map_det]
  -- evaluate each summand on the right
  simp only [map_prod, map_pow]
  -- identify the evaluated left matrix
  have hl :
      (MvPolynomial.eval x).mapMatrix
        ((fun g : G => fun h : G =>
          MvPolynomial.X (R:=ℂ) (g*h⁻¹)) : Matrix G G (MvPolynomial G ℂ)) =
        ((fun g : G => fun h : G => x (g*h⁻¹)) : Matrix G G ℂ) := by
      ext g h
      simp
  rw [hl]
  simp_rw [eval_blockPoly e]
  calc
    Matrix.det ((fun g : G => fun h : G => x (g*h⁻¹)) : Matrix G G ℂ) =
        Algebra.norm ℂ (genericEval x) := (norm_generic x).symm
    _ = Algebra.norm ℂ (e (genericEval x)) :=
        (norm_in_blocks e (genericEval x)).symm
    _ = ∏ i : Fin n, Algebra.norm ℂ ((e (genericEval x)) i) :=
        norm_pi_matrix (e (genericEval x))
    _ = ∏ i : Fin n, Matrix.det ((e (genericEval x)) i) ^ (d i) := by
        apply Finset.prod_congr rfl
        intro i hi
        simpa using (norm_matrix ((e (genericEval x)) i))
end FrobeniusDeterminantSupport

end

-- END INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Transfer.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Generic.lean
open scoped BigOperators
open MvPolynomial Matrix
noncomputable section
namespace FrobeniusDeterminantSupport

namespace Generic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
-- work over any field? fixed C
abbrev S (ι : Type*) := MvPolynomial (ι × ι) ℂ

def gen : MvPolynomial (ι × ι) ℂ := Matrix.det (fun a b : ι => X (a,b))

def pexp (u : Equiv.Perm ι) : (ι × ι) →₀ ℕ :=
  ∑ j : ι, Finsupp.single (u j, j) 1

lemma pexp_apply (u : Equiv.Perm ι) (a b : ι) :
    pexp u (a,b) = if u b = a then 1 else 0 := by
  classical
  unfold pexp
  simp only [Finset.sum_apply', Finsupp.single_apply]
  classical
  by_cases h : u b = a
  · have hz : ∀ j ∈ (Finset.univ : Finset ι), j ≠ b →
         (if (u j, j) = (a,b) then 1 else 0) = 0 := by
       intro j _ hj
       have : (u j, j) ≠ (a,b) := fun he => hj (congrArg Prod.snd he)
       simp [this]
    rw [Finset.sum_eq_single b hz (by simp)]
    simp [h]
  · have hh : ∀ j : ι, (u j, j) ≠ (a,b) := by
      intro j h'
      have hbj : j = b := congrArg Prod.snd h'
      subst j
      exact h (congrArg Prod.fst h')
    simp [h, hh]

lemma pexp_inj : Function.Injective (pexp (ι:=ι)) := by
  classical
  intro u v h
  ext j
  have hv := congrArg (fun f : (ι × ι) →₀ ℕ => f (u j, j)) h
  rw [pexp_apply, pexp_apply] at hv
  simp at hv
  exact hv.symm

lemma prod_X_eq (u : Equiv.Perm ι) :
    (∏ j : ι, (X (R:=ℂ) (u j, j))) =
      MvPolynomial.monomial (pexp u) (1 : ℂ) := by
  classical
  classical
  unfold pexp
  -- finite induction over univ general
  have aux : ∀ s : Finset ι,
      (∏ j ∈ s, (X (R:=ℂ) (u j, j))) =
        MvPolynomial.monomial (∑ j ∈ s, Finsupp.single (u j, j) 1) (1 : ℂ) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.prod_insert, Finset.sum_insert, ha, not_false_eq_true]
      rw [ih]
      rw [show (X (R:=ℂ) (u a, a)) =
          MvPolynomial.monomial (Finsupp.single (u a, a) 1) (1:ℂ) by rfl]
      rw [MvPolynomial.monomial_mul]
      simp
  simpa using aux Finset.univ

lemma cast_sign (v : Equiv.Perm ι) :
    ( (↑(↑(Equiv.Perm.sign v) : ℤ) :
      MvPolynomial (ι × ι) ℂ)) =
    MvPolynomial.C ((↑(↑(Equiv.Perm.sign v) : ℤ) : ℂ)) := by
  -- constants commute with the inclusion
  norm_cast

lemma coeff_gen (u : Equiv.Perm ι) :
    MvPolynomial.coeff (pexp u) (gen (ι:=ι)) =
      ( (↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ)) := by
  classical
  unfold gen
  rw [Matrix.det_apply']
  -- rewrite every summand as a distinct monomial
  have term (v : Equiv.Perm ι) :
      ( (↑(↑(Equiv.Perm.sign v) : ℤ) :
          MvPolynomial (ι × ι) ℂ)) *
          (∏ j : ι, X (R:=ℂ) (v j, j)) =
        MvPolynomial.monomial (pexp v)
          ((↑(↑(Equiv.Perm.sign v) : ℤ) : ℂ)) := by
      rw [prod_X_eq, cast_sign]
      -- C times a monomial
      change MvPolynomial.monomial (0) _ * _ = _
      rw [MvPolynomial.monomial_mul]
      simp
  simp_rw [term]
  classical
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  -- one term survives
  simp [pexp_inj.eq_iff]

lemma sign_ne (u : Equiv.Perm ι) :
    ((↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ)) ≠ 0 := by
  -- units have nonzero coercion
  exact_mod_cast (Units.ne_zero (Equiv.Perm.sign u))

lemma gen_ne_zero : gen (ι:=ι) ≠ 0 := by
  classical
  let u : Equiv.Perm ι := 1
  intro h
  have hc := coeff_gen (ι:=ι) u
  rw [h] at hc
  have hz : ((0:ℂ)) ≠ ((↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ)) :=
    ne_comm.mp (sign_ne u)
  exact hz hc

lemma mem_gen_exp {w : (ι × ι) →₀ ℕ}
    (hw : w ∈ (gen (ι:=ι)).support) : ∃ u : Equiv.Perm ι, pexp u = w := by
  classical
  rw [MvPolynomial.mem_support_iff] at hw
  by_contra hn
  push_neg at hn
  unfold gen at hw
  rw [Matrix.det_apply'] at hw
  have term (v : Equiv.Perm ι) :
      ( (↑(↑(Equiv.Perm.sign v) : ℤ) :
          MvPolynomial (ι × ι) ℂ)) *
          (∏ j : ι, X (R:=ℂ) (v j, j)) =
        MvPolynomial.monomial (pexp v)
          ((↑(↑(Equiv.Perm.sign v) : ℤ) : ℂ)) := by
      rw [prod_X_eq, cast_sign]
      change MvPolynomial.monomial (0) _ * _ = _
      rw [MvPolynomial.monomial_mul]
      simp
  simp_rw [term] at hw
  rw [MvPolynomial.coeff_sum] at hw
  simp [MvPolynomial.coeff_monomial, hn] at hw

lemma degree_cell (a b : ι) :
    MvPolynomial.degreeOf (a,b) (gen (ι:=ι)) = 1 := by
  classical
  apply le_antisymm
  · rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro w hw
    obtain ⟨u, rfl⟩ := mem_gen_exp (ι:=ι) hw
    simp only [pexp_apply]
    split <;> omega
  · -- the permutation swapping a and b contains this entry
    let u : Equiv.Perm ι := Equiv.swap b a
    have hu : u b = a := by simp [u]
    have hw : pexp u ∈ (gen (ι:=ι)).support := by
      rw [MvPolynomial.mem_support_iff, coeff_gen]
      exact sign_ne u
    have hle := MvPolynomial.le_degreeOf_of_mem_support
      (p := gen (ι:=ι)) (a,b) hw
    simpa [pexp_apply, hu] using hle

abbrev Row (r : ι) := {p : ι × ι // p.1 = r}
abbrev NRow (r : ι) := {p : ι × ι // p.1 ≠ r}

def rowEquiv (r : ι) : (ι × ι) ≃ (Row r ⊕ NRow r) where
  toFun p := if h : p.1 = r then Sum.inl ⟨p,h⟩ else Sum.inr ⟨p,h⟩
  invFun x := match x with | Sum.inl a => a.1 | Sum.inr b => b.1
  left_inv p := by
    dsimp
    by_cases h : p.1 = r <;> simp [h]
  right_inv x := by
    rcases x with a|b
    · dsimp
      have h : a.val.1 = r := a.property
      simp [h]
    · dsimp
      have h : b.val.1 ≠ r := b.property
      simp [h]

def rowSplit (r : ι) :
    MvPolynomial (ι × ι) ℂ ≃+*
      MvPolynomial (Row r) (MvPolynomial (NRow r) ℂ) :=
  (MvPolynomial.renameEquiv ℂ (rowEquiv r)).toRingEquiv |>.trans
    (MvPolynomial.sumRingEquiv ℂ (Row r) (NRow r))

lemma rowSplit_X_in (r a b : ι) (h : a = r) :
    rowSplit r (X (R:=ℂ) (a,b)) = X (⟨(a,b), h⟩ : Row r) := by
  classical
  change MvPolynomial.sumToIter ℂ (Row r) (NRow r)
     (MvPolynomial.rename (rowEquiv r) (X (R:=ℂ) (a,b))) = _
  rw [MvPolynomial.rename_X]
  have he : rowEquiv r (a,b) = Sum.inl (⟨(a,b), h⟩ : Row r) := by
    simp [rowEquiv, h]
  rw [he]
  exact MvPolynomial.sumToIter_Xl _ _ _ _

lemma rowSplit_X_out (r a b : ι) (h : a ≠ r) :
    rowSplit r (X (R:=ℂ) (a,b)) =
      C (X (R:=ℂ) (⟨(a,b), h⟩ : NRow r)) := by
  classical
  change MvPolynomial.sumToIter ℂ (Row r) (NRow r)
     (MvPolynomial.rename (rowEquiv r) (X (R:=ℂ) (a,b))) = _
  rw [MvPolynomial.rename_X]
  have he : rowEquiv r (a,b) = Sum.inr (⟨(a,b), h⟩ : NRow r) := by
    simp [rowEquiv, h]
  rw [he]
  exact MvPolynomial.sumToIter_Xr _ _ _ _

def rdeg (r : ι) (f : MvPolynomial (ι × ι) ℂ) : ℕ :=
  (rowSplit r f).totalDegree

lemma rdeg_mul (r : ι) {f g : MvPolynomial (ι × ι) ℂ}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    rdeg r (f*g) = rdeg r f + rdeg r g := by
  unfold rdeg
  rw [map_mul, MvPolynomial.totalDegree_mul_of_isDomain]
  · exact (rowSplit r).injective.ne (by simpa using hf)
  · exact (rowSplit r).injective.ne (by simpa using hg)

lemma rowsum_one (r : ι) (u : Equiv.Perm ι) :
    (∑ j : ι, if u j = r then 1 else 0) = 1 := by
  classical
  have hz : ∀ j ∈ (Finset.univ : Finset ι), j ≠ u.symm r →
       (if u j = r then (1:ℕ) else 0) = 0 := by
    intro j hj hn
    have hh : u j ≠ r := by
      intro h
      apply hn
      simpa using congrArg (fun z => u.symm z) h
    simp [hh]
  rw [Finset.sum_eq_single (u.symm r) hz (by simp)]
  simp

lemma row_gen_hom (r : ι) :
    (rowSplit r (gen (ι:=ι))).IsHomogeneous 1 := by
  classical
  change (rowSplit r).toRingHom (gen (ι:=ι)) |>.IsHomogeneous 1
  unfold gen
  rw [RingHom.map_det]
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro u hu
  have hent (j : ι) :
      ( (rowSplit r).toRingHom ((fun a b : ι => X (R:=ℂ) (a,b)) (u j) j)).IsHomogeneous
        (if u j = r then 1 else 0) := by
    change (rowSplit r (X (R:=ℂ) (u j, j))).IsHomogeneous _
    split_ifs with h
    · rw [rowSplit_X_in r (u j) j h]
      exact MvPolynomial.isHomogeneous_X _ _
    · rw [rowSplit_X_out r (u j) j h]
      exact MvPolynomial.isHomogeneous_C _ _
  have hprod :
      (∏ j : ι, (rowSplit r).toRingHom
          ((fun a b : ι => X (R:=ℂ) (a,b)) (u j) j)).IsHomogeneous 1 := by
    have hp := MvPolynomial.IsHomogeneous.prod (Finset.univ) (fun j : ι =>
        (rowSplit r).toRingHom (X (R:=ℂ) (u j, j)))
        (fun j : ι => if u j = r then 1 else 0)
        (by intro j hj; exact hent j)
    simpa [rowsum_one r u] using hp
  have hconst :
      ( (↑(↑(Equiv.Perm.sign u) : ℤ) :
        MvPolynomial (Row r) (MvPolynomial (NRow r) ℂ))).IsHomogeneous 0 := by
    have he : ( (↑(↑(Equiv.Perm.sign u) : ℤ) :
        MvPolynomial (Row r) (MvPolynomial (NRow r) ℂ))) =
        C ((↑(↑(Equiv.Perm.sign u) : ℤ) :
            (MvPolynomial (NRow r) ℂ))) := by
      norm_cast
    rw [he]
    exact MvPolynomial.isHomogeneous_C _ _
  simpa using hconst.mul hprod

lemma rdeg_gen (r : ι) : rdeg r (gen (ι:=ι)) = 1 := by
  unfold rdeg
  exact (row_gen_hom r).totalDegree ((rowSplit r).injective.ne gen_ne_zero)

lemma rowSplit_rename_out (r : ι) (f : MvPolynomial (NRow r) ℂ) :
    rowSplit r (MvPolynomial.rename (fun z : NRow r => (z.val : ι × ι)) f) =
       (C f : MvPolynomial (Row r) (MvPolynomial (NRow r) ℂ)) := by
  classical
  let inc : NRow r → (ι × ι) := fun z => z.val
  have hom :
     (rowSplit r).toRingHom.comp
        (MvPolynomial.rename inc).toRingHom =
       (MvPolynomial.C : MvPolynomial (NRow r) ℂ →+*
          MvPolynomial (Row r) (MvPolynomial (NRow r) ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      -- constants
      change rowSplit r (MvPolynomial.rename inc (MvPolynomial.C a)) = _
      rw [MvPolynomial.rename_C]
      change rowSplit r (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a)
      -- equivalence on constants
      change MvPolynomial.sumToIter ℂ (Row r) (NRow r)
         (MvPolynomial.rename (rowEquiv r) (MvPolynomial.C a)) = _
      simp
    · intro t
      change rowSplit r (MvPolynomial.rename inc (X (R:=ℂ) t)) = C (X t)
      rw [MvPolynomial.rename_X]
      change rowSplit r (X (R:=ℂ) (t.val.1,t.val.2)) = C (X t)
      -- non-row entry
      have ho : t.val.1 ≠ r := t.property
      simpa using (rowSplit_X_out r t.val.1 t.val.2 ho)
  have hh := DFunLike.congr_fun hom f
  exact hh

lemma degreeOf_zero_of_rdeg_zero (r a b : ι) (h : a = r)
    {f : MvPolynomial (ι × ι) ℂ} (hf : rdeg r f = 0) :
    MvPolynomial.degreeOf (a,b) f = 0 := by
  classical
  unfold rdeg at hf
  obtain heq : rowSplit r f =
       C ((rowSplit r f).coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hf)
  let q : MvPolynomial (NRow r) ℂ := (rowSplit r f).coeff 0
  have hx : f = MvPolynomial.rename (fun z : NRow r => (z.val : ι × ι)) q := by
    apply (rowSplit r).injective
    simpa [q, rowSplit_rename_out] using heq
  -- the variables in this renamed polynomial avoid the row
  apply Classical.byContradiction
  intro hn
  have hm : (a,b) ∈ f.vars :=
    MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hn
  rw [hx] at hm
  have hs := MvPolynomial.vars_rename
      (R:=ℂ) (fun z : NRow r => (z.val : ι × ι)) q hm
  rcases (Finset.mem_image.mp hs) with ⟨z, hz, hh⟩
  have hout : z.val.1 ≠ r := z.property
  have hin : z.val.1 = r := by
    have := congrArg Prod.fst hh
    simpa [h] using this
  exact hout hin

def sw : (ι × ι) ≃ (ι × ι) := Equiv.prodComm ι ι

def tr (f : MvPolynomial (ι × ι) ℂ) : MvPolynomial (ι × ι) ℂ :=
  MvPolynomial.rename (sw (ι:=ι)) f

lemma tr_ne {f : MvPolynomial (ι × ι) ℂ} (h : f ≠ 0) : tr f ≠ 0 := by
  exact (MvPolynomial.renameEquiv ℂ (sw (ι:=ι))).injective.ne h
lemma tr_mul (f g : MvPolynomial (ι × ι) ℂ) : tr (f*g) = tr f * tr g := by
  exact map_mul (MvPolynomial.rename (sw (ι:=ι))) f g
lemma tr_gen : tr (gen (ι:=ι)) = gen (ι:=ι) := by
  classical
  unfold tr gen
  change (MvPolynomial.rename (sw (ι:=ι))).toRingHom
       (Matrix.det (fun a b : ι => X (R:=ℂ) (a,b))) = _
  rw [RingHom.map_det]
  change Matrix.det (fun i j : ι =>
     (MvPolynomial.rename (sw (ι:=ι))) (X (R:=ℂ) (i,j))) = _
  have hm :
    (fun i j : ι => (MvPolynomial.rename (sw (ι:=ι))) (X (R:=ℂ) (i,j))) =
      Matrix.transpose (fun i j : ι => X (R:=ℂ) (i,j)) := by
    ext i j
    simp [sw, Matrix.transpose_apply]
  rw [hm, Matrix.det_transpose]

lemma degree_tr (f : MvPolynomial (ι × ι) ℂ) (a b : ι) :
    MvPolynomial.degreeOf (b,a) (tr f) =
      MvPolynomial.degreeOf (a,b) f := by
  simpa [tr, sw] using
    (MvPolynomial.degreeOf_rename_of_injective
      (R:=ℂ) (p:=f) (f:=sw (ι:=ι)) (Equiv.injective _) (a,b))

lemma total_zero_of_all_degree_zero (f : MvPolynomial (ι × ι) ℂ)
    (h : ∀ a b : ι, MvPolynomial.degreeOf (a,b) f = 0) :
    f.totalDegree = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro w hw
  -- all powers are zero
  have hz : ∀ p : ι × ι, w p = 0 := by
    intro p
    have hh := MvPolynomial.monomial_le_degreeOf p hw
    rcases p with ⟨a,b⟩
    simpa [h a b] using hh
  have ww : w = 0 := Finsupp.ext (by intro p; simp [hz p])
  simp [ww]

lemma unit_of_total_zero {f : MvPolynomial (ι × ι) ℂ}
    (hf : f ≠ 0) (h0 : f.totalDegree = 0) : IsUnit f := by
  have hx : f = C (f.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
  apply (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mpr ?_)
  refine ⟨?_, h0⟩
  -- constant coefficient is nonzero
  have hz : f.coeff 0 ≠ 0 := by
    intro h
    apply hf
    simpa [h] using hx
  have hi : IsUnit (f.coeff 0) := (isUnit_iff_ne_zero).2 hz
  -- in fact this is exactly the required coefficient
  simpa using hi

lemma exists_rdeg_ne_zero (f : MvPolynomial (ι × ι) ℂ)
    (hfdeg : f.totalDegree ≠ 0) : ∃ r : ι, rdeg r f ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  have hd : ∀ a b : ι, MvPolynomial.degreeOf (a,b) f = 0 := by
    intro a b
    exact degreeOf_zero_of_rdeg_zero a a b rfl (hn a)
  exact hfdeg (total_zero_of_all_degree_zero f hd)

lemma irreducible_gen [Nonempty ι] : Irreducible (gen (ι:=ι)) := by
  classical
  constructor
  · intro hu
    have h0 := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    let a : ι := Classical.choice (inferInstance : Nonempty ι)
    have hle := MvPolynomial.degreeOf_le_totalDegree (gen (ι:=ι)) (a,a)
    rw [degree_cell] at hle
    omega
  · intro f g hab
    have hne : gen (ι:=ι) ≠ 0 := gen_ne_zero
    have hf : f ≠ 0 := by intro h; simp [h] at hab; exact hne hab
    have hg : g ≠ 0 := by intro h; simp [h] at hab; exact hne hab
    by_cases fu : IsUnit f
    · exact Or.inl fu
    by_cases gu : IsUnit g
    · exact Or.inr gu
    exfalso
    have fd : f.totalDegree ≠ 0 := fun h => fu (unit_of_total_zero hf h)
    have gd : g.totalDegree ≠ 0 := fun h => gu (unit_of_total_zero hg h)
    obtain ⟨r, hr⟩ := exists_rdeg_ne_zero f fd
    obtain ⟨c, hc⟩ := exists_rdeg_ne_zero (tr g) (by
      intro hzero
      have tu := unit_of_total_zero (tr_ne hg) hzero
      -- equivalence reflects units
      have hh : IsUnit ((MvPolynomial.renameEquiv ℂ (sw (ι:=ι))) g) := tu
      exact gu ( (MulEquiv.isUnit_map
        (MvPolynomial.renameEquiv ℂ (sw (ι:=ι))).toMulEquiv).mp hh))
    have roweq (x : ι) : rdeg x f + rdeg x g = 1 := by
      rw [← rdeg_mul x hf hg, ← hab, rdeg_gen]
    have treq (x : ι) : rdeg x (tr f) + rdeg x (tr g) = 1 := by
      rw [← rdeg_mul x (tr_ne hf) (tr_ne hg)]
      rw [← tr_mul, ← hab, tr_gen, rdeg_gen]
    have rg0 : rdeg r g = 0 := by have hh := roweq r; omega
    have fc0 : rdeg c (tr f) = 0 := by have := treq c; omega
    have hgf : MvPolynomial.degreeOf (r,c) g = 0 :=
      degreeOf_zero_of_rdeg_zero r r c rfl rg0
    have hff' : MvPolynomial.degreeOf (r,c) f = 0 := by
      rw [← degree_tr f r c]
      exact degreeOf_zero_of_rdeg_zero c c r rfl fc0
    have hm := MvPolynomial.degreeOf_mul_eq
       (n:=(r,c)) hf hg
    rw [← hab, degree_cell, hff', hgf] at hm
    omega

lemma smallGenericDet_irreducible (m : ℕ) (hm : 0 < m) :
    Irreducible (smallGenericDet m) := by
  classical
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  exact irreducible_gen (ι:=Fin m)

end Generic
end FrobeniusDeterminantSupport

end

-- END INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Generic.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Extension.lean

/-!
A small commutative-algebra bridge.  The variables belonging to one matrix
block form a subtype of the variables of all the Wedderburn blocks.  A prime
polynomial remains prime on adjoining the other indeterminates.  In
`MvPolynomial` there is already a rather useful version of this assertion for
the inclusion of a `Set`, `MvPolynomial.prime_rename_iff`.  The following
lemma is just that result in the convenient form of an arbitrary injective
map of variables.
-/
open MvPolynomial
noncomputable section
namespace FrobeniusDeterminantSupport

lemma prime_rename_iff_of_injective {σ τ R : Type*} [CommRing R]
    (f : σ → τ) (hf : Function.Injective f) (p : MvPolynomial σ R) :
    Prime (MvPolynomial.rename f p) ↔ Prime p := by
  classical
  let s : Set τ := Set.range f
  let ee : σ ≃ s := Equiv.ofInjective f hf
  -- factoring the given map through its range is what changes the existing
  -- `Set` lemma into the present one.
  have hrename :
      MvPolynomial.rename (fun y : s => (y : τ)) (MvPolynomial.rename ee p) =
        MvPolynomial.rename f p := by
    rw [MvPolynomial.rename_rename]
    apply congrArg (fun g : σ → τ => MvPolynomial.rename g p)
    funext x
    rfl
  rw [← hrename]
  rw [MvPolynomial.prime_rename_iff s]
  change Prime ((MvPolynomial.renameEquiv R ee) p) ↔ Prime p
  exact MulEquiv.prime_iff (MvPolynomial.renameEquiv R ee)

/-- Over a field the polynomial rings are factorial.  Thus the prime
statement above is the corresponding assertion for irreducibles. -/
lemma irreducible_rename_of_injective {σ τ : Type*}
    (f : σ → τ) (hf : Function.Injective f) (p : MvPolynomial σ ℂ)
    (hp : Irreducible p) : Irreducible (MvPolynomial.rename f p) := by
  rw [irreducible_iff_prime] at hp ⊢
  exact (prime_rename_iff_of_injective f hf p).2 hp

/-- The coordinates of one summand amongst the coordinates of all the
matrix blocks. -/
lemma blockIncl_injective {n : ℕ} {d : Fin n → ℕ} (i : Fin n) :
    Function.Injective (blockIncl (d:=d) i) := by
  intro x y h
  have hh : (Sigma.mk i x : Σ j : Fin n, (Fin (d j) × Fin (d j))) =
            Sigma.mk i y := h
  -- taking the second projection of this equality keeps us in the same
  -- fibre; no transport is present since both first projections are `i`.
  cases hh
  rfl

/-- The full-coordinate determinant of a positive block is irreducible.
It is just the small generic determinant with variables renamed along the
block inclusion; adjoining the variables of the other blocks cannot split a
prime. -/
lemma fullBlockDet_irreducible {n : ℕ} {d : Fin n → ℕ} (i : Fin n)
    (hi : 0 < d i) : Irreducible (fullBlockDet (d:=d) i) := by
  classical
  rw [fullBlockDet_rename (d:=d) i]
  exact irreducible_rename_of_injective
    (blockIncl (d:=d) i) (blockIncl_injective (d:=d) i)
    (smallGenericDet (d i))
    (Generic.smallGenericDet_irreducible (d i) hi)

end FrobeniusDeterminantSupport
namespace FrobeniusDeterminantSupport
open MvPolynomial
open scoped BigOperators

lemma fullBlockDet_ne {n : ℕ} {d : Fin n → ℕ} (i : Fin n) (hi : 0 < d i) :
    fullBlockDet (d:=d) i ≠ 0 :=
  (fullBlockDet_irreducible (d:=d) i hi).ne_zero

/-- A variable not in the chosen block has degree zero. -/
lemma degree_fullBlockDet_other
    {n : ℕ} {d : Fin n → ℕ} (j i : Fin n) (hij : i ≠ j)
    (a b : Fin (d i)) :
    MvPolynomial.degreeOf (Sigma.mk i (a,b))
      (fullBlockDet (d:=d) j) = 0 := by
  classical
  rw [fullBlockDet_rename (d:=d) j]
  by_contra hne
  have hm : (Sigma.mk i (a,b)) ∈
      (MvPolynomial.rename (blockIncl (d:=d) j) (smallGenericDet (d j))).vars :=
    MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hne
  have hs := MvPolynomial.vars_rename
      (R:=ℂ) (blockIncl (d:=d) j) (smallGenericDet (d j)) hm
  rcases Finset.mem_image.mp hs with ⟨z,hz,he⟩
  have he' := congrArg Sigma.fst he
  exact hij (by simpa [blockIncl] using he'.symm)

lemma degree_fullBlockDet_self
    {n : ℕ} {d : Fin n → ℕ} (i : Fin n) (a b : Fin (d i)) :
    MvPolynomial.degreeOf (Sigma.mk i (a,b))
      (fullBlockDet (d:=d) i) = 1 := by
  classical
  rw [fullBlockDet_rename (d:=d) i]
  change MvPolynomial.degreeOf (blockIncl (d:=d) i (a,b))
      (MvPolynomial.rename (blockIncl (d:=d) i) (smallGenericDet (d i))) = 1
  rw [MvPolynomial.degreeOf_rename_of_injective
       (blockIncl_injective (d:=d) i) (a,b)]
  exact Generic.degree_cell (ι:=Fin (d i)) a b

/-- Distinct, nonempty blocks give non-associated polynomials even before the
change of (group) coordinates.  The variable on their diagonal has degree
one in the first and degree zero in the second. -/
lemma fullBlockDet_not_associated
    {n : ℕ} {d : Fin n → ℕ} (i j : Fin n) (hi : 0 < d i) (hj : 0 < d j)
    (hij : i ≠ j) :
    ¬ Associated (fullBlockDet (d:=d) i) (fullBlockDet (d:=d) j) := by
  classical
  intro h
  rcases h with ⟨u, hu⟩
  -- the degree of a unit polynomial is zero
  have hunit : IsUnit ( (↑u) :
       MvPolynomial (Σ k : Fin n, Fin (d k) × Fin (d k)) ℂ) := u.isUnit
  have htu : ( (↑u) :
       MvPolynomial (Σ k : Fin n, Fin (d k) × Fin (d k)) ℂ).totalDegree = 0 :=
    (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  have hcu : ( (↑u) :
       MvPolynomial (Σ k : Fin n, Fin (d k) × Fin (d k)) ℂ) =
       MvPolynomial.C (( (↑u) :
       MvPolynomial (Σ k : Fin n, Fin (d k) × Fin (d k)) ℂ).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htu
  let a : Fin (d i) := ⟨0, hi⟩
  have hdeg := MvPolynomial.degreeOf_mul_eq
        (n := (Sigma.mk i (a,a)))
        (fullBlockDet_ne (d:=d) i hi) hunit.ne_zero
  rw [hu, degree_fullBlockDet_self (d:=d) i a a,
        degree_fullBlockDet_other (d:=d) j i hij a a,
        hcu, MvPolynomial.degreeOf_C] at hdeg
  omega

/-- The linear coordinate change from all blocks to the group basis is an
equivalence, so it also reflects non-association. -/
lemma blockPoly_not_associated
    {G:Type*} [Group G] [Fintype G] [DecidableEq G]
    {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ]
          Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i j : Fin n) (hi : 0 < d i) (hj : 0 < d j) (hij : i ≠ j) :
      ¬ Associated (blockPoly e i) (blockPoly e j) := by
  intro h
  have hm := Associated.map
     (FrobeniusLinearChange.lsEquiv
        (gpBasis (G:=G)) (blockBasis (n:=n) (d:=d)) e.toLinearEquiv).symm
      h
  -- inverse images of the two blocks are their full coordinate determinants
  have hi' := fullBlockDet_map (G:=G) e i
  have hj' := fullBlockDet_map (G:=G) e j
  have hmi :
    (FrobeniusLinearChange.lsEquiv
      (gpBasis (G:=G)) (blockBasis (n:=n) (d:=d)) e.toLinearEquiv).symm
        (blockPoly e i) = fullBlockDet (d:=d) i := by
      rw [← hi']
      exact (FrobeniusLinearChange.lsEquiv
        (gpBasis (G:=G)) (blockBasis (n:=n) (d:=d)) e.toLinearEquiv).symm_apply_apply _
  have hmj :
    (FrobeniusLinearChange.lsEquiv
      (gpBasis (G:=G)) (blockBasis (n:=n) (d:=d)) e.toLinearEquiv).symm
        (blockPoly e j) = fullBlockDet (d:=d) j := by
      rw [← hj']
      exact (FrobeniusLinearChange.lsEquiv
        (gpBasis (G:=G)) (blockBasis (n:=n) (d:=d)) e.toLinearEquiv).symm_apply_apply _
  rw [hmi, hmj] at hm
  exact fullBlockDet_not_associated i j hi hj hij hm

end FrobeniusDeterminantSupport

end

-- END INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Extension.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Assembly.lean
open scoped BigOperators MonoidAlgebra
open Matrix MvPolynomial
noncomputable section
namespace FrobeniusDeterminantSupport

/-- Centers are preserved by an algebra equivalence, as a linear equivalence. -/
def centerAlgEquiv {A B : Type*} [Ring A] [Ring B]
    [Algebra ℂ A] [Algebra ℂ B]
    (e : A ≃ₐ[ℂ] B) :
    (Subalgebra.center ℂ A) ≃ₗ[ℂ] (Subalgebra.center ℂ B) := by
  let f : Subalgebra.center ℂ A → Subalgebra.center ℂ B := fun x =>
    ⟨e x.1, (Subalgebra.mem_center_iff).2 (fun b => by
      have h := (Subalgebra.mem_center_iff.mp x.2 (e.symm b))
      have h' := congrArg e h
      simpa using h')⟩
  let g : Subalgebra.center ℂ B → Subalgebra.center ℂ A := fun x =>
    ⟨e.symm x.1, (Subalgebra.mem_center_iff).2 (fun a => by
      have h := (Subalgebra.mem_center_iff.mp x.2 (e a))
      have h' := congrArg e.symm h
      simpa using h')⟩
  exact
  { toFun := f
    invFun := g
    left_inv := by intro x; apply Subtype.ext; simp [f,g]
    right_inv := by intro x; apply Subtype.ext; simp [f,g]
    map_add' := by intro x y; apply Subtype.ext; simp [f]
    map_smul' := by intro c x; apply Subtype.ext; simp [f] }

variable {n : ℕ} {d : Fin n → ℕ}

private def diagIndex (hn : ∀ i : Fin n, NeZero (d i)) (i : Fin n) : Fin (d i) :=
  ⟨0, Nat.pos_of_ne_zero (hn i).out⟩

private lemma scalar_diag (hn : ∀ i : Fin n, NeZero (d i))
    (i : Fin n) (c : ℂ) :
    (algebraMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) c)
       (diagIndex hn i) (diagIndex hn i) = c := by
  classical
  simp [Algebra.algebraMap_eq_smul_one, diagIndex]

private lemma component_central
    (hn : ∀ i : Fin n, NeZero (d i))
    (z : Subalgebra.center ℂ (∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ))
    (i : Fin n) : z.1 i ∈ Subalgebra.center ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  classical
  apply Subalgebra.mem_center_iff.mpr
  intro A
  have h := Subalgebra.mem_center_iff.mp z.2
    (Pi.single i A : ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)
  have hh := congrFun h i
  simpa [Pi.single_apply] using hh

/-- The centre of a product of nonempty full complex matrix blocks has one
coordinate for each block. -/
def centerBlocksEquiv (hn : ∀ i : Fin n, NeZero (d i)) :
    (Subalgebra.center ℂ (∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)) ≃ₗ[ℂ]
       (Fin n → ℂ) := by
  classical
  let F : Subalgebra.center ℂ (∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) →
        (Fin n → ℂ) := fun z i => z.1 i (diagIndex hn i) (diagIndex hn i)
  let I : (Fin n → ℂ) →
        Subalgebra.center ℂ (∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) := fun c =>
    ⟨(fun i => algebraMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) (c i)),
      (Subalgebra.mem_center_iff).2 (by
        intro y
        funext i
        -- scalars commute in each block
        exact (Algebra.commutes (c i) (y i)).symm)⟩
  refine
   { toFun := F
     invFun := I
     left_inv := ?_
     right_inv := ?_
     map_add' := ?_
     map_smul' := ?_ }
  · -- map_add is the first structure obligation
    intro x y
    funext i
    simp [F]
  · intro c x
    funext i
    simp [F, smul_eq_mul]
  · intro z
    apply Subtype.ext
    funext i
    have hzi := component_central hn z i
    rcases (Algebra.IsCentral.mem_center_iff ℂ).1 hzi with ⟨c, hc⟩
    change (algebraMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) (F z i)) = z.1 i
    have heq : F z i = c := by
      dsimp [F]
      rw [hc]
      exact scalar_diag hn i c
    rw [heq, hc]
  · intro c
    funext i
    change (algebraMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) (c i))
       (diagIndex hn i) (diagIndex hn i) = c i
    exact scalar_diag hn i (c i)

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

lemma coeff_conjugate (x : MonoidAlgebra ℂ G)
    (hx : x ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (t g : G) :
    x (t*g*t⁻¹) = x g := by
  have H := (Subalgebra.mem_center_iff.mp hx (MonoidAlgebra.single t (1:ℂ)))
  have HH := congrArg (fun z : MonoidAlgebra ℂ G => z (t*g)) H
  rw [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply] at HH
  simpa [mul_assoc] using HH.symm

lemma coeff_class (x : MonoidAlgebra ℂ G)
    (hx : x ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) {a b : G}
    (h : ConjClasses.mk a = ConjClasses.mk b) : x a = x b := by
  have hi : IsConj a b := ConjClasses.mk_eq_mk_iff_isConj.mp h
  rcases (isConj_iff.mp hi) with ⟨t, ht⟩
  have hh := coeff_conjugate x hx t a
  rw [ht] at hh
  exact hh.symm

private def classRep (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.exists_rep c)

private lemma mk_classRep (c : ConjClasses G) :
    ConjClasses.mk (classRep c : G) = c :=
  Classical.choose_spec (ConjClasses.exists_rep c)

private def classElem (f : ConjClasses G → ℂ) : MonoidAlgebra ℂ G :=
  (Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm (fun g => f (ConjClasses.mk g))

@[simp] private lemma classElem_apply (f : ConjClasses G → ℂ) (g : G) :
    classElem f g = f (ConjClasses.mk g) := by
  change ((Finsupp.linearEquivFunOnFinite ℂ ℂ G)
       ((Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm
          (fun t : G => f (ConjClasses.mk t)))) g = _
  simp

private lemma classElem_central (f : ConjClasses G → ℂ) :
    classElem f ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
  classical
  apply Subalgebra.mem_center_iff.mpr
  intro y
  -- commute first with group basis elements, then use that they span.
  refine @MonoidAlgebra.induction_on ℂ G _ _
    (fun y : MonoidAlgebra ℂ G => y * classElem f = classElem f * y) y ?_ ?_ ?_
  · intro t
    -- the coefficients at `t⁻¹ k` and `k t⁻¹` have the same class.
    ext k
    change ((MonoidAlgebra.single t (1:ℂ)) * classElem f) k =
      (classElem f * (MonoidAlgebra.single t (1:ℂ))) k
    rw [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply]
    simp only [classElem_apply, one_mul, mul_one]
    apply congrArg f
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    apply isConj_iff.mpr
    refine ⟨t, ?_⟩
    simp [mul_assoc]
  · intro a b ha hb
    simp [add_mul, mul_add, ha, hb]
  · intro c a ha
    simpa [Algebra.smul_mul_assoc, Algebra.mul_smul_comm] using
      congrArg (fun z : MonoidAlgebra ℂ G => c • z) ha

/-- Coefficients of a central element of a group algebra are the functions on
conjugacy classes. -/
def centerGroupEquiv :
    (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) ≃ₗ[ℂ] (ConjClasses G → ℂ) := by
  classical
  let F : Subalgebra.center ℂ (MonoidAlgebra ℂ G) → (ConjClasses G → ℂ) :=
    fun z c => z.1 (classRep c : G)
  let I : (ConjClasses G → ℂ) → Subalgebra.center ℂ (MonoidAlgebra ℂ G) :=
    fun f => ⟨classElem f, classElem_central f⟩
  refine { toFun := F, invFun := I, left_inv := ?_, right_inv := ?_,
            map_add' := ?_, map_smul' := ?_ }
  · -- addition
    intro x y
    funext c
    simp [F]
  · intro c x
    funext z
    simp [F, smul_eq_mul]
  · intro z
    apply Subtype.ext
    apply Finsupp.ext
    intro g
    change classElem (F z) g = z.1 g
    rw [classElem_apply]
    dsimp [F]
    exact coeff_class z.1 z.2 (mk_classRep (ConjClasses.mk g))
  · intro f
    funext c
    change classElem f (classRep c : G) = f c
    rw [classElem_apply]
    rw [mk_classRep]

lemma card_blocks_eq_conj
    {n : ℕ} {d : Fin n → ℕ} (hn : ∀ i : Fin n, NeZero (d i))
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ]
          Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    n = Nat.card (ConjClasses G) := by
  classical
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  calc
    n = Module.finrank ℂ (Fin n → ℂ) := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
    _ = Module.finrank ℂ (Subalgebra.center ℂ
          (∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)) :=
      (centerBlocksEquiv (d:=d) hn).finrank_eq.symm
    _ = Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :=
      (centerAlgEquiv e).finrank_eq.symm
    _ = Module.finrank ℂ (ConjClasses G → ℂ) :=
      (centerGroupEquiv (G:=G)).finrank_eq
    _ = Nat.card (ConjClasses G) := by
      rw [Module.finrank_fintype_fun_eq_card]
      exact (Nat.card_eq_fintype_card).symm

end FrobeniusDeterminantSupport

end

-- END INLINED FILE: Mathlib/Support/frobenius_group_determinant_b0fc066f9d/Assembly.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval.RepresentationTheory.FrobeniusDeterminant

/-!
# Frobenius determinant theorem (Dedekind's group determinant)

`frobenius_group_determinant`: the group determinant `Θ(G) = det(A)` of the
group matrix `A_{gh} = x_{gh}` factors into irreducible polynomials, each to the
power of its own total degree, with the factors pairwise non-associated and
their number equal to the number of conjugacy classes of `G`. Trusted helpers
`groupMatrix`, `groupDeterminant` (non-holes). Category-(b) candidate from §171
of the Knill survey.
-/

open MvPolynomial Matrix


/-- The **group matrix** of Dedekind/Frobenius: a `G × G` matrix over the
polynomial ring `ℂ[x_g : g ∈ G]`, with entry `(g, h)` the variable indexed by
the product `g * h`. -/
noncomputable def groupMatrix (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Matrix G G (MvPolynomial G ℂ) :=
  fun g h => MvPolynomial.X (g * h)

/-- The **group determinant** `Θ(G) = det(A)`, a polynomial in the variables
`x_g`. -/
noncomputable def groupDeterminant (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    MvPolynomial G ℂ :=
  (groupMatrix G).det



end LeanEval.RepresentationTheory.FrobeniusDeterminant

open LeanEval.RepresentationTheory.FrobeniusDeterminant
open MvPolynomial Matrix
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

namespace LeanEval.RepresentationTheory.FrobeniusDeterminant

open scoped BigOperators
open Matrix MvPolynomial
open FrobeniusDeterminantSupport
noncomputable section

/-- The polynomial in the statement is nonzero; specializing all coordinates but the
identity to zero gives a permutation matrix for inversion. -/
lemma groupDeterminant_ne_zero (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    groupDeterminant G ≠ 0 := by
  unfold groupDeterminant
  unfold groupMatrix
  exact FrobeniusDeterminantSupport.group_matrix_det_ne_zero G


/-- The determinant has the expected homogeneous degree before any factorization
arguments are used. -/
lemma groupDeterminant_isHomogeneous (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    (groupDeterminant G).IsHomogeneous (Fintype.card G) := by
  unfold groupDeterminant
  unfold groupMatrix
  exact FrobeniusDeterminantSupport.group_matrix_det_isHomogeneous (K:=G)

lemma groupDeterminant_totalDegree (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    (groupDeterminant G).totalDegree = Fintype.card G := by
  unfold groupDeterminant
  unfold groupMatrix
  exact FrobeniusDeterminantSupport.group_matrix_totalDegree (K:=G)


/-- Since a group has an identity element, that homogeneous degree is positive; in
particular the determinant is not a unit.  This makes the usual UFD factorisation
lemmas applicable without a degenerate empty case. -/
lemma groupDeterminant_not_isUnit (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    ¬ IsUnit (groupDeterminant G) := by
  intro hu
  have hd0 : (groupDeterminant G).totalDegree = 0 :=
    (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
  have hd := groupDeterminant_totalDegree G
  have : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  exact this (hd ▸ hd0)


/-- In the left-regular convention the column at `h` has coordinates `X_(g*h⁻¹)`;
our determinant is this one times the scalar sign of the inversion permutation. -/
lemma groupDeterminant_leftRegular_sign (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
 groupDeterminant G =
 (Matrix.det ((fun g : G => fun h : G => (X (R:=ℂ) (g*h⁻¹))) : Matrix G G (MvPolynomial G ℂ))) *
   ( (↑(↑((FrobeniusDeterminantSupport.invEquiv G).sign) : ℤ) : MvPolynomial G ℂ)) := by
 unfold groupDeterminant
 unfold groupMatrix
 exact FrobeniusDeterminantSupport.det_column_inversion G

end
end LeanEval.RepresentationTheory.FrobeniusDeterminant

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem frobenius_group_determinant (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    ∃ (r : ℕ) (p : Fin r → MvPolynomial G ℂ),
      r = Nat.card (ConjClasses G) ∧
      (∀ j, Irreducible (p j)) ∧
      (∀ i j, i ≠ j → ¬ Associated (p i) (p j)) ∧
      groupDeterminant G = ∏ j, (p j) ^ (p j).totalDegree :=
/-ResultProofBegin-/by
  classical
  by_cases htriv : Nontrivial G
  · letI : Nontrivial G := htriv
    -- Maschke and the algebraically closed Wedderburn theorem in mathlib give actual
    -- matrix blocks, rather than postulating a list of representations.  In each
    -- block the polynomial we have to study is quite concrete.
    obtain ⟨n, d, hd, ⟨e⟩⟩ :=
      FrobeniusDeterminantSupport.complex_group_blocks G
    let q : Fin n → MvPolynomial G ℂ := fun i =>
      FrobeniusDeterminantSupport.blockPoly e i
    have hq (i : Fin n) : (q i).IsHomogeneous (d i) := by
      exact FrobeniusDeterminantSupport.blockPoly_isHomogeneous e i
    -- The determinant on a matrix simple summand is the determinant of the
    -- ordinary matrix, repeated once for every column.  This is the small
    -- norm calculation needed to identify the exponents of these factors in
    -- the regular module.
    have hnorm (i : Fin n) (A : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
        Algebra.norm ℂ A = A.det ^ d i := by
      simpa using (FrobeniusDeterminantSupport.norm_matrix A)
    -- The norm comparison is now an identity of polynomials (not merely
    -- equality after numerical substitutions).  It uses the group basis for
    -- the regular algebra and the sigma basis for the product of blocks.
    have hreg :
        Matrix.det ((fun g : G => fun h : G =>
          X (R:=ℂ) (g*h⁻¹)) : Matrix G G (MvPolynomial G ℂ)) =
            ∏ i : Fin n, (q i) ^ (d i) := by
      simpa [q] using (FrobeniusDeterminantSupport.det_leftRegular_blocks e)
    have hfac : groupDeterminant G =
        (∏ i : Fin n, (q i) ^ (d i)) *
          ( (↑(↑((FrobeniusDeterminantSupport.invEquiv G).sign) : ℤ) :
              MvPolynomial G ℂ)) := by
      rw [groupDeterminant_leftRegular_sign]
      rw [hreg]
    -- The coefficient forms for a block really are independent: the
    -- Wedderburn equivalence induces an automorphism of the polynomial ring.
    -- Thus the remaining irreducibility question has no hidden linear algebra
    -- hypothesis.  In block coordinates it is just the generic determinant
    -- on the indicated square block (with the other block variables unused).
    have hblock_irred_of_generic (i : Fin n)
        (H : Irreducible
          (FrobeniusDeterminantSupport.fullBlockDet (d:=d) i)) :
        Irreducible (q i) := by
      change Irreducible (FrobeniusDeterminantSupport.blockPoly e i)
      exact FrobeniusDeterminantSupport.blockPoly_irred_of_full e i H
    have hblock_irred_one (i : Fin n) (hi : d i = 1) :
        Irreducible (q i) := by
      change Irreducible (FrobeniusDeterminantSupport.blockPoly e i)
      exact FrobeniusDeterminantSupport.blockPoly_irred_one e i hi
    -- The ordinary generic determinant itself is irreducible in every
    -- positive size.  The proof in `Generic` is by the row/column grading:
    -- in a factorisation each row, and each column, must belong to a single
    -- factor, and a crossed entry gives a contradiction.
    have hsmall (m : ℕ) (hm : 0 < m) :
        Irreducible (FrobeniusDeterminantSupport.smallGenericDet m) := by
      exact FrobeniusDeterminantSupport.Generic.smallGenericDet_irreducible m hm
    -- A block is not a separate coefficient ring here: its variables are a
    -- subset of all of the block variables.  `prime_rename_iff` identifies
    -- that inclusion with adjoining a family of indeterminates.  In
    -- particular a prime over the small block stays prime, and over these
    -- factorial rings this is exactly the assertion for irreducibles.
    have Hfull (i : Fin n) :
        Irreducible (FrobeniusDeterminantSupport.fullBlockDet (d:=d) i) := by
      have hi : 0 < d i := Nat.pos_of_ne_zero (hd i).out
      exact FrobeniusDeterminantSupport.fullBlockDet_irreducible i hi
    have hirr (i : Fin n) : Irreducible (q i) :=
      hblock_irred_of_generic i (Hfull i)
    -- In block coordinates the blocks cannot be associates.  On the
    -- variable at `(i,(0,0))` the `i`th determinant has degree one while
    -- every other determinant has degree zero.  Units have degree zero as
    -- well.  Applying the inverse linear coordinate equivalence carries this
    -- observation back to the polynomials `q`.
    have hsep (i j : Fin n) (hij : i ≠ j) :
        ¬ Associated (q i) (q j) := by
      change ¬ Associated (FrobeniusDeterminantSupport.blockPoly e i)
          (FrobeniusDeterminantSupport.blockPoly e j)
      exact FrobeniusDeterminantSupport.blockPoly_not_associated e i j
        (Nat.pos_of_ne_zero (hd i).out) (Nat.pos_of_ne_zero (hd j).out) hij
    have hnpos : 0 < n := by
      by_contra hh
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hh
      subst n
      -- If there were no block at all, our norm formula would make the
      -- determinant a nonzero constant (indeed a unit).
      have hu : IsUnit
          ((↑(↑((FrobeniusDeterminantSupport.invEquiv G).sign) : ℤ) :
              MvPolynomial G ℂ)) := by
        have hc : IsUnit ((↑(↑((FrobeniusDeterminantSupport.invEquiv G).sign) : ℤ) : ℂ)) :=
          (isUnit_iff_ne_zero).2 (by
            exact_mod_cast
              (Units.ne_zero ((FrobeniusDeterminantSupport.invEquiv G).sign)))
        simpa using hc.map (MvPolynomial.C : ℂ →+* MvPolynomial G ℂ)
      have hhdet : groupDeterminant G =
          ((↑(↑((FrobeniusDeterminantSupport.invEquiv G).sign) : ℤ) :
              MvPolynomial G ℂ)) := by simpa using hfac
      exact (groupDeterminant_not_isUnit G) (hhdet.symm ▸ hu)
    -- adjust one factor by a constant root of the column sign.
    let i0 : Fin n := ⟨0, hnpos⟩
    let sgn : ℂ := (↑(↑((FrobeniusDeterminantSupport.invEquiv G).sign) : ℤ) : ℂ)
    have hsg : sgn ≠ 0 := by
      dsimp [sgn]
      exact_mod_cast (Units.ne_zero ((FrobeniusDeterminantSupport.invEquiv G).sign))
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq sgn
      (Nat.pos_of_ne_zero (hd i0).out)
    have ha0 : a ≠ (0:ℂ) := by
      intro h0
      subst a
      simp [zero_pow (Nat.pos_of_ne_zero (hd i0).out).ne'] at ha
      exact hsg ha.symm
    have hCa : IsUnit ((C a : MvPolynomial G ℂ) : MvPolynomial G ℂ) := by
      exact ((isUnit_iff_ne_zero).2 ha0).map (MvPolynomial.C : ℂ →+* MvPolynomial G ℂ)
    let U : (MvPolynomial G ℂ)ˣ := hCa.unit
    have hU : (U : MvPolynomial G ℂ) = (C a : MvPolynomial G ℂ) := by
      exact IsUnit.unit_spec hCa
    let p : Fin n → MvPolynomial G ℂ :=
      fun i => if i = i0 then q i * (C a) else q i
    have hdegree (i : Fin n) : (q i).totalDegree = d i :=
      (hq i).totalDegree (hirr i).ne_zero
    have hp_assoc (i : Fin n) : Associated (p i) (q i) := by
      classical
      by_cases hi : i = i0
      · subst i
        change Associated (q i0 * C a) (q i0)
        rw [← hU]
        exact (associated_mul_unit_left_iff).2 (Associated.refl _)
      · simp [p, hi]
    have hpdeg (i : Fin n) : (p i).totalDegree = d i := by
      classical
      by_cases hi : i = i0
      · subst i
        change (q i0 * C a).totalDegree = d i0
        rw [MvPolynomial.totalDegree_mul_of_isDomain (hirr i0).ne_zero hCa.ne_zero,
            MvPolynomial.totalDegree_C, Nat.add_zero]
        exact hdegree i0
      · simpa [p, hi] using hdegree i
    have hpirr (i : Fin n) : Irreducible (p i) :=
      (hp_assoc i).irreducible_iff.mpr (hirr i)
    have hpsep (i j : Fin n) (hij : i ≠ j) : ¬ Associated (p i) (p j) := by
      intro h
      have hh : Associated (q i) (q j) :=
        (hp_assoc i).symm.trans (h.trans (hp_assoc j))
      exact hsep i j hij hh
    have hp_prod : (∏ i : Fin n, (p i) ^ (p i).totalDegree) =
        (∏ i : Fin n, (q i) ^ (d i)) *
          ((↑(↑((FrobeniusDeterminantSupport.invEquiv G).sign) : ℤ) :
              MvPolynomial G ℂ)) := by
      -- only the chosen component is changed.
      classical
      have hpow : ((C a : MvPolynomial G ℂ) : MvPolynomial G ℂ) ^ (d i0) =
          ((↑(↑((FrobeniusDeterminantSupport.invEquiv G).sign) : ℤ) :
              MvPolynomial G ℂ)) := by
        rw [← map_pow, ha]
        change C sgn = _
        simp [sgn]
      calc
        (∏ i : Fin n, (p i) ^ (p i).totalDegree) =
            ∏ i : Fin n, (p i) ^ (d i) := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [hpdeg i]
        _ = ∏ i : Fin n,
              ((q i) ^ (d i) *
                (if i = i0 then (C a : MvPolynomial G ℂ) ^ (d i) else 1)) := by
              apply Finset.prod_congr rfl
              intro i hi
              by_cases h : i = i0
              · subst i; simp [p, mul_pow]
              · simp [p, h]
        _ = (∏ i : Fin n, (q i) ^ (d i)) *
              (∏ i : Fin n, if i = i0 then
                   (C a : MvPolynomial G ℂ) ^ (d i) else 1) := by
              rw [Finset.prod_mul_distrib]
        _ = (∏ i : Fin n, (q i) ^ (d i)) *
              ((↑(↑((FrobeniusDeterminantSupport.invEquiv G).sign) : ℤ) :
                 MvPolynomial G ℂ)) := by
              rw [Finset.prod_ite_eq' Finset.univ i0]
              simp only [Finset.mem_univ, ↓reduceIte]
              rw [hpow]
    refine ⟨n, p, ?_, hpirr, hpsep, ?_⟩
    · exact (FrobeniusDeterminantSupport.card_blocks_eq_conj (G:=G) hd e)
    · exact hfac.trans hp_prod.symm
  · have hs : Subsingleton G := not_nontrivial_iff_subsingleton.mp htriv
    letI : Unique G := { default := 1, uniq := fun x => hs.elim _ _ }
    have hscc : Subsingleton (ConjClasses G) :=
      ⟨fun a b => by
        obtain ⟨x, rfl⟩ := ConjClasses.exists_rep a
        obtain ⟨y, rfl⟩ := ConjClasses.exists_rep b
        exact congrArg ConjClasses.mk (hs.elim x y)⟩
    letI : Subsingleton (ConjClasses G) := hscc
    have hc : Nat.card (ConjClasses G) = 1 := Nat.card_unique
    refine ⟨1, (fun _ : Fin 1 => X (1 : G)), hc.symm, ?_, ?_, ?_⟩
    · intro j
      apply MvPolynomial.irreducible_of_totalDegree_eq_one (by simp)
      intro x hx
      apply (isUnit_iff_ne_zero).2
      intro he
      subst x
      have h := hx (Finsupp.single (1 : G) 1)
      simpa using h
    · intro i j hn
      exact False.elim (hn (Subsingleton.elim _ _))
    · unfold groupDeterminant
      rw [Matrix.det_unique]
      unfold groupMatrix
      -- The finite product has just its single index.
      simp
      exact Subsingleton.elim _ _
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
