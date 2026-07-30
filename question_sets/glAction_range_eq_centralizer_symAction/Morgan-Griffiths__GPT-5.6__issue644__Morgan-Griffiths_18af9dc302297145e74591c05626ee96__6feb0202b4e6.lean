import Mathlib

namespace Submission

namespace LeanEval
namespace RepresentationTheory

open scoped TensorProduct

/-!
Schur–Weyl duality on `V^⊗k`.

Two commuting actions on `V^⊗k`:

* `symAction`: the symmetric group `S_k` acts by permuting tensor factors.
* `glAction`: the general linear group `GL(V)` acts diagonally as `g · (v₁ ⊗ ⋯ ⊗ v_k) =
  (g v₁) ⊗ ⋯ ⊗ (g v_k)`.

Schur–Weyl duality says their images in `End(V^⊗k)` generate mutual centralizers. We state
the two directions as separate `eval_problem`s.
-/

/-- The symmetric group `S_k` acts on `V^⊗k` by permuting the tensor factors. -/
def symAction (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] (k : ℕ) :
    Equiv.Perm (Fin k) →* Module.End R (⨂[R]^k M) where
  toFun σ := (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap
  map_one' := by
    ext x
    simp only [LinearEquiv.coe_coe, LinearMap.coe_compMultilinearMap, Function.comp_apply,
      PiTensorProduct.reindex_tprod, Module.End.one_apply]
    rfl
  map_mul' σ τ := by
    ext x
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe, LinearMap.coe_compMultilinearMap,
      Function.comp_apply, PiTensorProduct.reindex_tprod]
    rfl

/-- The general linear group `GL(V)` acts diagonally on `V^⊗k`:
`g · (v₁ ⊗ ⋯ ⊗ v_k) = (g v₁) ⊗ ⋯ ⊗ (g v_k)`. -/
def glAction (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] (k : ℕ) :
    (M →ₗ[R] M)ˣ →* Module.End R (⨂[R]^k M) where
  toFun g := PiTensorProduct.map (fun _ : Fin k => (g : M →ₗ[R] M))
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp



end RepresentationTheory
end LeanEval

open LeanEval.RepresentationTheory
open scoped TensorProduct
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-- A diagonal map on a `PiTensorProduct` commutes with a reindexing of
    its (equal) factors.  This elementary half of the commutant theorem
    does not use finite dimensionality. -/
lemma piTensorProduct_reindex_mul_map_eq_map_mul_reindex
    {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {k : ℕ} (f : M →ₗ[R] M) (σ : Equiv.Perm (Fin k)) :
    (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap *
          PiTensorProduct.map (fun _ : Fin k => f)
      = PiTensorProduct.map (fun _ : Fin k => f) *
          (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap := by
  ext x
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe,
    LinearMap.coe_compMultilinearMap, Function.comp_apply,
    PiTensorProduct.map_tprod, PiTensorProduct.reindex_tprod]


namespace SchurAux
open scoped TensorProduct
open PiTensorProduct
open Module
@[simp] lemma symb {R M : Type*} [CommSemiring R] [AddCommMonoid M]
 [Module R M] {κ : Type*} (b : Basis κ R M)
 {k:ℕ} (σ: Equiv.Perm (Fin k)) (i : Fin k → κ) :
  (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap
      ((Basis.piTensorProduct (fun _ : Fin k => b)) i)
   = (Basis.piTensorProduct (fun _ : Fin k => b))
      (fun t => i (σ.symm t)) := by
  simp

open Module
open scoped TensorProduct
open PiTensorProduct
lemma repr_reindex {R M : Type*} [CommSemiring R] [AddCommMonoid M]
 [Module R M] {κ : Type*} (b : Basis κ R M)
 {k:ℕ} (σ: Equiv.Perm (Fin k))
 (x : ⨂[R]^k M) (i : Fin k → κ) :
  (Basis.piTensorProduct (fun _ : Fin k => b)).repr
     ((PiTensorProduct.reindex R (fun _ : Fin k => M) σ) x)
     (fun t => i (σ.symm t))
   = (Basis.piTensorProduct (fun _ : Fin k => b)).repr x i := by
  let tb : Basis (Fin k → κ) R (⨂[R]^k M) := Basis.piTensorProduct (fun _ : Fin k => b)
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      -- try simp
      simp only [map_smul, PiTensorProduct.reindex_tprod,
        map_smul, LinearEquiv.map_smul,
        Finsupp.smul_apply, smul_eq_mul,
        Basis.piTensorProduct_repr_tprod_apply]
      -- goal?
      apply congrArg (fun z : R => r * z)
        ((Equiv.prod_comp σ.symm
          (fun t : Fin k => b.repr (f t) (i t))))
  | add x y hx hy =>
      simpa using congrArg₂ (fun a b : R => a + b) hx hy

open Module
open scoped TensorProduct
open PiTensorProduct
open scoped BigOperators
set_option autoImplicit true
lemma coeff_invariant_of_commute
 {R : Type*} [CommSemiring R]
 {M : Type*} [AddCommMonoid M] [Module R M]
 {n k : ℕ} (b : Basis (Fin n) R M)
 (a : Module.End R (⨂[R]^k M))
 (h : ∀ σ : Equiv.Perm (Fin k),
   (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap * a =
     a * (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap)
 (σ : Equiv.Perm (Fin k)) (i j : Fin k → Fin n) :
 let tb : Basis (Fin k → Fin n) R (⨂[R]^k M) :=
    Basis.piTensorProduct (fun _ : Fin k => b)
 (LinearMap.toMatrix tb tb)
       a (fun t => i (σ.symm t)) (fun t => j (σ.symm t)) =
  (LinearMap.toMatrix tb tb) a i j := by
  let tb : Basis (Fin k → Fin n) R (⨂[R]^k M) :=
    Basis.piTensorProduct (fun _ : Fin k => b)
  dsimp
  simp only [LinearMap.toMatrix_apply]
  change (tb.repr (a (tb (fun t => j (σ.symm t))))
      (fun t => i (σ.symm t))) = (tb.repr (a (tb j)) i)
  have eqv := LinearMap.congr_fun (h σ) (tb j)
  -- trace_state
  -- use congrArg repr
  have e2 := congrArg
       (fun z : (⨂[R]^k M) => tb.repr z (fun t => i (σ.symm t))) eqv
  -- left side
  -- simplify mul_apply etc and action on basis
  -- multiply in `Module.End` is composition
  simp only [Module.End.mul_apply] at e2
  have left : tb.repr
        ((PiTensorProduct.reindex R (fun _ : Fin k => M) σ)
          (a (tb j))) (fun t => i (σ.symm t)) = tb.repr (a (tb j)) i := by
    -- the coordinate is merely transported by the permutation
    exact SchurAux.repr_reindex (b:=b) σ (a (tb j)) i
  have bas :
        (PiTensorProduct.reindex R (fun _ : Fin k => M) σ)
          (tb j) = tb (fun t => j (σ.symm t)) := by
    simpa [tb] using (SchurAux.symb (R:=R) (b:=b) σ j)
  change tb.repr
      ((PiTensorProduct.reindex R (fun _ : Fin k => M) σ) (a (tb j)))
         (fun t => i (σ.symm t)) =
    tb.repr (a ((PiTensorProduct.reindex R (fun _ : Fin k => M) σ) (tb j)))
         (fun t => i (σ.symm t)) at e2
  rw [bas] at e2
  rw [left] at e2
  exact e2.symm

open Module
open scoped TensorProduct
open PiTensorProduct
@[simp] lemma diagonal_coeff
 {R : Type*} [CommSemiring R]
 {M : Type*} [AddCommMonoid M] [Module R M]
 {n k : ℕ} (b : Basis (Fin n) R M)
 (f : Module.End R M) (i j : Fin k → Fin n) :
 let tb : Basis (Fin k → Fin n) R (⨂[R]^k M) :=
    Basis.piTensorProduct (fun _ : Fin k => b)
 (LinearMap.toMatrix tb tb)
    (PiTensorProduct.map (fun _ : Fin k => f)) i j =
   ∏ t : Fin k, (LinearMap.toMatrix b b f) (i t) (j t) := by
 dsimp
 rw [LinearMap.toMatrix_apply]
 simp [Basis.piTensorProduct_apply,
    Basis.piTensorProduct_repr_tprod_apply,
    PiTensorProduct.map_tprod, LinearMap.toMatrix_apply]

open Module
open scoped TensorProduct
open PiTensorProduct
-- gl def

def diag {R:Type*} [CommSemiring R] {n k : ℕ}
 (X : Matrix (Fin n) (Fin n) R) :
 Matrix (Fin k → Fin n) (Fin k → Fin n) R :=
 fun i j => ∏ t, X (i t) (j t)

lemma image_range_diag
 {R : Type*} [CommSemiring R]
 {M : Type*} [AddCommMonoid M] [Module R M]
 {n k:ℕ} (b : Basis (Fin n) R M) :
 let tb : Basis (Fin k → Fin n) R (⨂[R]^k M) :=
   Basis.piTensorProduct (fun _ : Fin k => b)
 (fun x => (LinearMap.toMatrix tb tb) x) ''
     Set.range (glAction R M k) =
   {Y | ∃ X : Matrix (Fin n) (Fin n) R, IsUnit X ∧ diag X = Y} := by
  let tb : Basis (Fin k → Fin n) R (⨂[R]^k M) :=
   Basis.piTensorProduct (fun _ : Fin k => b)
  dsimp
  ext Y
  constructor
  · intro h
    rcases h with ⟨T, ⟨g, rfl⟩, rfl⟩
    let e : (Module.End R M) ≃ₐ[R] Matrix (Fin n) (Fin n) R :=
       LinearMap.toMatrixAlgEquiv b
    refine ⟨e (g : Module.End R M), ?_, ?_⟩
    · exact Units.isUnit (Units.map e.toMonoidHom g)
    · -- use diagonal_coeff
      ext i j
      change (∏ t, (LinearMap.toMatrix b b (g : Module.End R M))
                    (i t) (j t)) =
             (LinearMap.toMatrix
                (Basis.piTensorProduct (fun _ : Fin k => b))
                (Basis.piTensorProduct (fun _ : Fin k => b))
                (PiTensorProduct.map (fun _ : Fin k => (g : Module.End R M)))) i j
      exact (SchurAux.diagonal_coeff (b:=b) (f:= (g : Module.End R M)) i j).symm
  · intro h
    rcases h with ⟨X, hX, rfl⟩
    let e : (Module.End R M) ≃ₐ[R] Matrix (Fin n) (Fin n) R :=
       LinearMap.toMatrixAlgEquiv b
    have hf : IsUnit (e.symm X : Module.End R M) := by
       exact IsUnit.map e.symm.toMulEquiv.toMonoidHom hX
    -- choose a unit in the endomorphism ring
    rcases hf with ⟨g, hg⟩
    refine ⟨(glAction R M k) g, ⟨g, rfl⟩, ?_⟩
    ext i j
    -- diagonal coeff, plus e apply symm
    have he : (LinearMap.toMatrix b b) (g : Module.End R M) = X := by
      have he' : e (e.symm X) = X := e.apply_symm_apply X
      have hg' : (g : Module.End R M) = e.symm X := hg
      rw [hg']
      -- entries of the two versions of `toMatrix` agree definitionally
      ext u v
      change e (e.symm X) u v = X u v
      exact congrFun (congrFun he' u) v
    -- the coefficients are the entries of the chosen matrix
    simpa [diag, he, glAction] using
       (SchurAux.diagonal_coeff (b:=b) (f:=(g : Module.End R M)) i j)
end SchurAux

/-- The range of a monoid homomorphism is already multiplicatively closed, so
`adjoin` of that range has, as a submodule, just its linear span.  This avoids
products in later membership arguments for the diagonal action. -/
lemma adjoin_range_monoidHom_toSubmodule
    {R : Type*} {A : Type*} {G : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] [Monoid G]
    (f : G →* A) :
    (Algebra.adjoin R (Set.range f)).toSubmodule =
      Submodule.span R (Set.range f) := by
  rw [Algebra.adjoin_eq_span]
  have h : (Set.range f : Set A) =
      (MonoidHom.mrange f : Set A) := by
    ext x
    change (∃ g, f g = x) ↔ _
    exact (MonoidHom.mem_mrange).symm
  rw [h]
  rw [Submonoid.closure_eq]

lemma adjoin_glAction_le_centralizer_symAction
    {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {k : ℕ} :
    Algebra.adjoin R (Set.range (glAction R M k)) ≤
      Subalgebra.centralizer R (Set.range (symAction R M k)) := by
  apply Algebra.adjoin_le
  intro z hz
  rcases hz with ⟨g, rfl⟩
  -- The centralizer is stated with the element from the set on the
  -- left; on simple tensors both composites are the same tensor.
  refine (Subalgebra.mem_centralizer_iff R).2 ?_
  intro w hw
  rcases hw with ⟨σ, rfl⟩
  exact piTensorProduct_reindex_mul_map_eq_map_mul_reindex (R:=R)
    (M:=M) (k:=k) (g : M →ₗ[R] M) σ

-- test section
namespace SchurAux
open scoped BigOperators
section Fiber
variable {β : Type*} [Fintype β] [DecidableEq β]
variable {k:ℕ}
noncomputable def fibEquiv (s : Fin k → β) :
    (Sigma fun p : β => {t : Fin k // s t = p}) ≃ Fin k where
  toFun := fun z => z.2.1
  invFun := fun t => ⟨s t, ⟨t, rfl⟩⟩
  left_inv := by
    intro z
    rcases z with ⟨p,t,ht⟩
    dsimp
    -- show equal sigma, p is s t
    subst p
    rfl
  right_inv := by intro t; rfl

example (s : Fin k → β) (p : β) :
    Fintype.card {t : Fin k // s t = p} =
      (Finset.univ.filter (fun t : Fin k => s t = p)).card := by
  classical
  simpa using (Fintype.card_subtype (fun t : Fin k => s t = p))

lemma card_fiber_eq (s : Fin k → β) (p : β) :
    Fintype.card {t : Fin k // s t = p} =
      (Finset.univ.filter (fun t : Fin k => s t = p)).card := by
  classical
  simpa using (Fintype.card_subtype (fun t : Fin k => s t = p))

noncomputable def permOfFiberCard (s u : Fin k → β)
  (h : ∀ p : β, Fintype.card {t : Fin k // u t = p} =
                      Fintype.card {t : Fin k // s t = p}) :
  Equiv.Perm (Fin k) :=
  let E : ∀ p : β, {t : Fin k // u t = p} ≃ {t : Fin k // s t = p} :=
    fun p => Fintype.equivOfCardEq (h p)
  (fibEquiv u).symm |>.trans ((Equiv.sigmaCongrRight E).trans (fibEquiv s))

lemma permOfFiberCard_spec (s u : Fin k → β)
  (h : ∀ p : β, Fintype.card {t : Fin k // u t = p} =
                      Fintype.card {t : Fin k // s t = p})
  (t : Fin k) :
    s (permOfFiberCard s u h t) = u t := by
  classical
  -- unfold
  change s (((fun p : β => Fintype.equivOfCardEq (h p)) (u t)) ⟨t, rfl⟩).val = u t
  exact (((fun p : β => Fintype.equivOfCardEq (h p)) (u t)) ⟨t, rfl⟩).property

lemma exists_perm_of_mult_eq (s u : Fin k → β)
 (h : ∀ p : β,
   (Finset.univ.filter (fun t : Fin k => s t = p)).card =
   (Finset.univ.filter (fun t : Fin k => u t = p)).card) :
 ∃ σ : Equiv.Perm (Fin k), (fun t => s (σ t)) = u := by
  classical
  have hc : ∀ p : β, Fintype.card {t : Fin k // u t = p} =
                    Fintype.card {t : Fin k // s t = p} := by
    intro p
    rw [card_fiber_eq, card_fiber_eq]
    exact (h p).symm
  refine ⟨permOfFiberCard s u hc, ?_⟩
  funext t
  exact permOfFiberCard_spec s u hc t
end Fiber
end SchurAux




namespace SchurAux
open scoped BigOperators
section FunAverage
variable {R : Type*} [Field R]
variable {β : Type*} [Fintype β]
variable {k : ℕ}

noncomputable def funDelta (s : Fin k → β) : (Fin k → β) → R := by
  classical
  exact fun u => if u = s then 1 else 0

noncomputable def funSymm (s : Fin k → β) : (Fin k → β) → R :=
  ∑ σ : Equiv.Perm (Fin k), funDelta (R:=R) (fun t => s (σ t))

lemma sum_funDelta (F : (Fin k → β) → R) :
    (∑ s : (Fin k → β), (F s) • funDelta (R:=R) s) = F := by
  classical
  funext u
  -- the only non-zero summand has the word `u`
  simp [funDelta]

lemma sum_coeff_funSymm_apply (F : (Fin k → β) → R) (u : Fin k → β) :
 ((∑ s : (Fin k → β), (F s) • funSymm (R:=R) s) u) =
    ∑ σ : Equiv.Perm (Fin k), F (fun t => u (σ.symm t)) := by
  classical
  -- swap the two finite sums and pick the unique word for each permutation
  -- unfold all operations to sums of scalars
  simp_rw [funSymm, Finset.smul_sum]
  simp_rw [Fintype.sum_apply]
  simp_rw [Pi.smul_apply]
  -- rearrange the two sums
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  -- for fixed σ, unique s with s ∘ σ = u
  -- need algebraic simp via Equiv
  have huniq (s : Fin k → β) :
      (fun t => s (σ t)) = u ↔ s = (fun t => u (σ.symm t)) := by
    constructor
    · intro h
      funext t
      have hh := congrFun h (σ.symm t)
      simpa using hh
    · intro h
      subst s
      funext t
      simp
  have hc (x : Fin k → β) :
      (u = fun t => x (σ t)) ↔ x = (fun t => u (σ.symm t)) := by
    constructor
    · intro h
      exact (huniq x).1 h.symm
    · intro h
      exact ((huniq x).2 h).symm
  simp only [funDelta, Pi.smul_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  -- goal now an indicator with equality
  simp_rw [hc]
  simp

lemma invariant_fun_mem_of_symm
 {F : (Fin k → β) → R}
 (hchar : (k.factorial : R) ≠ 0)
 (hF : ∀ (σ : Equiv.Perm (Fin k)) (u : Fin k → β),
       F (fun t => u (σ.symm t)) = F u)
 (S : Submodule R ((Fin k → β) → R))
 (hs : ∀ s : Fin k → β, funSymm (R:=R) s ∈ S) :
 F ∈ S := by
  classical
  let Z : (Fin k → β) → R :=
    ∑ s : (Fin k → β), (F s) • funSymm (R:=R) s
  have hZ : Z ∈ S := by
    dsimp [Z]
    exact Submodule.sum_mem S (fun s _ => S.smul_mem _ (hs s))
  have heq : Z = (k.factorial : R) • F := by
    funext u
    change (∑ s : (Fin k → β), (F s) • funSymm (R:=R) s) u = _
    rw [sum_coeff_funSymm_apply (F:=F) u]
    simp_rw [hF]
    change (∑ _x : Equiv.Perm (Fin k), F u) = (k.factorial : R) * F u
    rw [Finset.sum_const]
    classical
    rw [nsmul_eq_mul]
    congr 1
    have hn : (Finset.univ : Finset (Equiv.Perm (Fin k))).card = k.factorial := by
      simpa using (Fintype.card_perm (α:=Fin k))
    exact congrArg (fun q : ℕ => (q : R)) hn
  have hh : ((k.factorial : R)⁻¹) • Z ∈ S := S.smul_mem _ hZ
  rw [heq] at hh
  simpa [smul_smul, hchar] using hh
end FunAverage
end SchurAux


namespace SchurAux
section Pair
variable {R : Type*} [Semiring R]
-- scalar semiring enough? need add comm? matrices Pi module; linear inverse
variable {n k : ℕ}
/-- Repack the two multi-indices of a matrix into a single word in pairs. -/
@[simps!]
def matrixWordEquiv (R : Type*) [Semiring R] (n k : ℕ) :
    Matrix (Fin k → Fin n) (Fin k → Fin n) R ≃ₗ[R]
      ((Fin k → (Fin n × Fin n)) → R) := by
  classical
  -- use linear equivalence piCongr? build
  refine
   { toFun := fun Y s => Y (fun t => (s t).1) (fun t => (s t).2)
     map_add' := ?_
     map_smul' := ?_
     invFun := fun F i j => F (fun t => (i t, j t))
     left_inv := ?_
     right_inv := ?_ }
  · intro A B; rfl
  · intro c A; rfl
  · intro A; ext i j; rfl
  · intro F; funext s
    congr 1

end Pair
end SchurAux


namespace SchurAux
open scoped BigOperators
/-- Polynomial (rank-one symmetric tensor) attached to a matrix after pairing
row and column letters. -/
def wordPower {R : Type*} [CommSemiring R] {n k : ℕ}
    (X : Matrix (Fin n) (Fin n) R) : (Fin k → (Fin n × Fin n)) → R :=
  fun s => ∏ t, X (s t).1 (s t).2

@[simp] lemma matrixWordEquiv_diag_wordPower
   {R : Type*} [CommSemiring R] {n k : ℕ}
   (X : Matrix (Fin n) (Fin n) R) :
   (matrixWordEquiv R n k) (diag (k:=k) X) = wordPower (k:=k) X := by
  funext s
  rfl
end SchurAux



namespace SchurAux
open scoped BigOperators
-- matrices obtained by adding the elementary letters in a set of positions
noncomputable def posSumMat {R : Type*} [Field R] {n k : ℕ}
    (s : Fin k → (Fin n × Fin n)) (I : Finset (Fin k)) :
    Matrix (Fin n) (Fin n) R := fun a b =>
      ∑ i : Fin k, if i ∈ I ∧ s i = (a,b) then 1 else 0

@[simp] lemma wordPower_posSumMat {R : Type*} [Field R] {n k : ℕ}
    (s u : Fin k → (Fin n × Fin n)) (I : Finset (Fin k)) :
    wordPower (k:=k) (posSumMat (R:=R) s I) u =
      ∑ f : Fin k → Fin k,
        ∏ t : Fin k, (if f t ∈ I ∧ s (f t) = u t then (1:R) else 0) := by
  classical
  unfold wordPower posSumMat
  -- expand a product of sums
  simpa using
    (Fintype.prod_sum (f := fun t (i : Fin k) =>
      if i ∈ I ∧ s i = u t then (1:R) else 0))

-- signed inclusion/exclusion coefficient.  This self-contained finite-set
-- lemma is useful for polarization.
lemma sum_superset_sign
    {R : Type*} [Field R] {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset α) :
    (∑ I : Finset α, if F ⊆ I then
          ((-1:R) ^ ((Fintype.card α) - I.card)) else 0)
       = if F = Finset.univ then (1:R) else 0 := by
  classical
  -- complements turn supersets of F into subsets of Fᶜ
  let C : Finset α := Finset.univ \ F
  have hcard (I : Finset α) :
      Fintype.card α - I.card = (Finset.univ \ I).card := by
    simpa using (Finset.card_sdiff_of_subset (Finset.subset_univ I)).symm
  -- reindex the full sum by taking complements in univ
  let e : (Finset α) ≃ (Finset α) :=
    { toFun := fun I => Finset.univ \ I
      invFun := fun I => Finset.univ \ I
      left_inv := by intro I; ext x; simp
      right_inv := by intro I; ext x; simp }
  have hsub (J : Finset α) :
      F ⊆ (Finset.univ \ J) ↔ J ⊆ C := by
    dsimp [C]
    constructor
    · intro h x hx
      have hxnot : x ∉ F := by
        intro hxF
        have hx' := h hxF
        exact (Finset.mem_sdiff.mp hx').2 hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxnot⟩
    · intro h x hxF
      have : x ∉ J := by
        intro hxJ
        have hh := h hxJ
        exact (Finset.mem_sdiff.mp hh).2 hxF
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, this⟩
  calc
    (∑ I : Finset α, if F ⊆ I then
          ((-1:R) ^ ((Fintype.card α) - I.card)) else 0)
        = ∑ J : Finset α, if J ⊆ C then ((-1:R)^J.card) else 0 := by
          -- an equivalence of all finite sets
          refine Fintype.sum_equiv e _ _ ?_
          intro I
          dsimp [e]
          rw [hcard I]
          have hh : (Finset.univ \ I).card = (Finset.univ \ I).card := rfl
          by_cases hFI : F ⊆ I
          · have hs : (Finset.univ \ I) ⊆ C := (hsub (Finset.univ \ I)).1 (by
                  intro x hx
                  -- twice complement
                  have hxI := hFI hx
                  simpa [hxI] using hxI)
            simp [hFI, hs]
          · have hs : ¬ (Finset.univ \ I) ⊆ C := by
                  intro h
                  have h' := (hsub (Finset.univ \ I)).2 h
                  apply hFI
                  intro x hx
                  have hxII := h' hx
                  -- remove a double complement
                  have : x ∈ I := by
                    simpa using hxII
                  exact this
            simp [hFI, hs]
    _ = ∑ J ∈ C.powerset, ((-1:R)^J.card) := by
          classical
          -- write both sides as a filtered sum on univ
          change (∑ J : Finset α, if J ⊆ C then ((-1:R)^J.card) else 0) = _
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext J; simp
          · intro J hJ; rfl
    _ = ∏ x ∈ C, (1 + (-1:R)) := by
          -- expand the product
          simpa using (Finset.prod_one_add (s:=C) (f:=fun _ : α => (-1:R))).symm
    _ = if F = Finset.univ then (1:R) else 0 := by
          by_cases h : F = Finset.univ
          · subst F
            simp [C]
          · have hC : C.Nonempty := by
              -- complement of a proper finite subset
              by_contra hn
              have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
              have : F = (Finset.univ : Finset α) := by
                ext x
                have hx : x ∈ (Finset.univ : Finset α) := Finset.mem_univ _
                have hxnot : ¬ x ∈ C := by simp [he]
                have hxF : x ∈ F := by
                  by_contra q
                  have : x ∈ C := Finset.mem_sdiff.mpr ⟨hx, q⟩
                  exact hxnot this
                simp [hxF]
              exact h this
            rcases hC with ⟨x,hx⟩
            have hz : ∏ y ∈ C, (1 + (-1:R)) = 0 :=
              Finset.prod_eq_zero hx (by simp)
            rw [hz]
            simp [h]


lemma prod_indicator_all {R : Type*} [Field R] {ι : Type*} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] :
    (∏ i : ι, if P i then (1:R) else 0) =
       if (∀ i, P i) then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · classical
    have hh : ∃ i, ¬ P i := by
      simpa using h
    rcases hh with ⟨i,hi⟩
    have hz : (∏ j : ι, if P j then (1:R) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hz]
    simp [h]

lemma sum_weight_for_function {R : Type*} [Field R]
    {k : ℕ} (f : Fin k → Fin k) :
    (∑ I : Finset (Fin k),
       ((-1:R) ^ (k-I.card)) *
          (∏ t : Fin k, if f t ∈ I then (1:R) else 0))
       = if Function.Surjective f then 1 else 0 := by
  classical
  let F : Finset (Fin k) := Finset.univ.image f
  have hcontains (I : Finset (Fin k)) :
      (∀ t, f t ∈ I) ↔ F ⊆ I := by
    dsimp [F]
    constructor
    · intro h x hx
      rcases Finset.mem_image.mp hx with ⟨t,_,rfl⟩
      exact h t
    · intro h t
      exact h (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)
  have hprod (I : Finset (Fin k)) :
     (∏ t : Fin k, if f t ∈ I then (1:R) else 0) =
        if F ⊆ I then 1 else 0 := by
      classical
      simpa [hcontains I] using
        (prod_indicator_all (R:=R) (fun t : Fin k => f t ∈ I))
  have hsurj : Function.Surjective f ↔ F = Finset.univ := by
    dsimp [F]
    constructor
    · intro h
      apply Finset.eq_univ_of_forall
      intro x
      obtain ⟨t, rfl⟩ := h x
      exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
    · intro h x
      have hx : x ∈ Finset.univ.image f := by rw [h]; exact Finset.mem_univ _
      rcases Finset.mem_image.mp hx with ⟨t,_,ht⟩
      exact ⟨t, ht⟩
  simp_rw [hprod]
  -- the remaining sum is precisely inclusion/exclusion on the image of f
  have hv := sum_superset_sign (R:=R) F
  have he :
      (∑ I : Finset (Fin k),
        (-1:R) ^ (k-I.card) * (if F ⊆ I then 1 else 0)) =
      (∑ I : Finset (Fin k),
         if F ⊆ I then ((-1:R) ^ (k-I.card)) else 0) := by
        apply Finset.sum_congr rfl
        intro I hI
        by_cases h : F ⊆ I <;> simp [h]
  rw [he]
  have hv' :
      (∑ I : Finset (Fin k), if F ⊆ I then ((-1:R)^(k-I.card)) else 0) =
        if F = Finset.univ then (1:R) else 0 := by
          simpa using hv
  rw [hv']
  by_cases h : Function.Surjective f
  · simp [h, (hsurj.mp h)]
  · have hh : F ≠ Finset.univ := by
      intro q
      exact h (hsurj.mpr q)
    simp [h, hh]

-- the actual (labelled) polarization identity. Positions are labelled, so
-- repeated letters cause no division by multiplicity.
lemma funSymm_eq_sum_powers {R : Type*} [Field R] {n k : ℕ}
    (s : Fin k → (Fin n × Fin n)) :
    funSymm (R:=R) s =
       ∑ I : Finset (Fin k),
          ((-1:R)^(k-I.card)) •
             wordPower (k:=k) (posSumMat (R:=R) s I) := by
  classical
  funext u
  -- expand each power as a sum indexed by choices of a position
  simp_rw [Finset.sum_apply]
  simp_rw [Pi.smul_apply]
  simp_rw [smul_eq_mul]
  simp_rw [wordPower_posSumMat (R:=R) s u]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- first write the answer too as a sum over permutations/indicators
  have hfun : funSymm (R:=R) s u =
       ∑ σ : Equiv.Perm (Fin k),
            if (fun t => s (σ t)) = u then (1:R) else 0 := by
    unfold funSymm funDelta
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro σ hσ
    simp [eq_comm]
  rw [hfun]
  -- for a fixed choice f : Fin k -> Fin k its contribution is zero unless
  -- it is a permutation with the prescribed letters
  classical
  -- characterize the product appearing in the expansion
  have hp (f : Fin k → Fin k) (I : Finset (Fin k)) :
      (∏ t : Fin k, if f t ∈ I ∧ s (f t) = u t then (1:R) else 0) =
      ( (∏ t : Fin k, if f t ∈ I then (1:R) else 0) *
        (∏ t : Fin k, if s (f t) = u t then (1:R) else 0)) := by
    -- split each zero-one factor
    simp_rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro t ht
    by_cases h₁ : f t ∈ I <;> by_cases h₂ : s (f t) = u t <;> simp [h₁,h₂]
  simp_rw [hp]
  -- move the second (letter) factor out of the I-sum
  have hmove (f : Fin k → Fin k) :
      (∑ I : Finset (Fin k),
         (-1:R)^(k-I.card) *
           ((∏ t : Fin k, if f t ∈ I then (1:R) else 0) *
            (∏ t : Fin k, if s (f t) = u t then (1:R) else 0))) =
       (if Function.Surjective f then (1:R) else 0) *
            (∏ t : Fin k, if s (f t) = u t then (1:R) else 0) := by
    let c : R := (∏ t : Fin k, if s (f t) = u t then (1:R) else 0)
    have hw := sum_weight_for_function (R:=R) f
    calc
      _ = (∑ I : Finset (Fin k),
            (-1:R)^(k-I.card) *
              (∏ t : Fin k, if f t ∈ I then (1:R) else 0)) * c := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro I hI
                dsimp [c]
                ring
      _ = (if Function.Surjective f then (1:R) else 0) * c := by rw [hw]
      _ = _ := by rfl
  simp_rw [hmove]
  -- discard non-bijections and identify the bijections with permutations
  -- first both indicator products equal the equality of words
  have heq (f : Fin k → Fin k) :
      (∏ t : Fin k, if s (f t) = u t then (1:R) else 0) =
        if (fun t => s (f t)) = u then (1:R) else 0 := by
    rw [prod_indicator_all]
    by_cases h : (fun t => s (f t)) = u
    · have ht : ∀ t, s (f t) = u t := fun t => congrFun h t
      simp [h, ht]
    · have ht : ¬ (∀ t, s (f t) = u t) := by
        intro q; apply h; funext t; exact q t
      simp [h, ht]
  simp_rw [heq]
  -- change the full function sum into a sum over bijections, then equivalences
  classical
  -- convert surjective to bijective on this finite type
  have hb (f : Fin k → Fin k) :
      Function.Surjective f ↔ Function.Bijective f :=
    ⟨fun q => q.bijective_of_finite, fun q => q.2⟩
  simp_rw [hb]
  let B := {f : (Fin k → Fin k) // Function.Bijective f}
  -- the all-functions sum with indicator is the subtype sum
  symm
  calc
    (∑ f : Fin k → Fin k,
        (if Function.Bijective f then (1:R) else 0) *
          (if (fun t => s (f t)) = u then (1:R) else 0))
        = ∑ f : B,
          (if (fun t => s (f.1 t)) = u then (1:R) else 0) := by
            classical
            simp_rw [ite_mul, one_mul, zero_mul]
            rw [← Finset.sum_filter]
            exact Finset.sum_subtype
              (s:= Finset.univ.filter (fun f : Fin k → Fin k => Function.Bijective f))
              (p:= fun f : Fin k → Fin k => Function.Bijective f)
              (by intro x; simp) _
    _ = ∑ σ : Equiv.Perm (Fin k),
            if (fun t => s (σ t)) = u then (1:R) else 0 := by
          classical
          let e : (Equiv.Perm (Fin k)) ≃ B :=
            { toFun := fun σ => ⟨σ, σ.bijective⟩
              invFun := fun f => Equiv.ofBijective f.1 f.2
              left_inv := by intro σ; ext t; rfl
              right_inv := by intro f; cases f; rfl }
          exact (Fintype.sum_equiv e _ _ (by intro σ; rfl)).symm

end SchurAux

namespace SchurAux
open scoped BigOperators Polynomial Matrix
open Polynomial

variable {R : Type*} [Field R] {n:ℕ}
lemma nil_shift (N : Matrix (Fin n) (Fin n) R) (hN:IsNilpotent N)
 (c:R) (hc:c≠0) : IsUnit (N + c • (1 : Matrix (Fin n) (Fin n) R)) := by
 have hnil : IsNilpotent (c⁻¹ • N) := hN.smul _
 have hu : IsUnit ((c⁻¹ • N) + 1) := hnil.isUnit_add_one
 have hc' : IsUnit c := (isUnit_iff_ne_zero).2 hc
 have hmap : IsUnit (algebraMap R (Matrix (Fin n) (Fin n) R) c) :=
    (algebraMap R (Matrix (Fin n) (Fin n) R)).isUnit_map hc'
 have hm := hmap.mul hu
 have heq :
      (algebraMap R (Matrix (Fin n) (Fin n) R) c) *
        ((c⁻¹ • N) + 1) = N + c • (1: Matrix (Fin n) (Fin n) R) := by
   rw [mul_add]
   simp [← Algebra.smul_def, smul_smul, hc, Algebra.algebraMap_eq_smul_one]
 rw [heq] at hm
 exact hm
lemma line_factor (X : Matrix (Fin n) (Fin n) R)
 (A N : Matrix (Fin n) (Fin n) R) (hA : IsUnit A)
 (hN : IsNilpotent N) (hx : X = A * N) :
 ∀ c:R, c≠0 → IsUnit (X + c • A) := by
 intro c hc
 have hu := hA.mul (nil_shift N hN c hc)
 have heq : X + c • A = A * (N + c • (1 : Matrix (Fin n) (Fin n) R)) := by
   rw [hx, mul_add]
   simp
 rw [heq]
 exact hu


variable {R : Type*} [Field R]
variable {n k : ℕ}
open Matrix
-- indices
noncomputable def wpP (X A : Matrix (Fin n) (Fin n) R)
 (u : Fin k → (Fin n × Fin n)) : R[X] :=
 ∏ t : Fin k, (C (X (u t).1 (u t).2) + C (A (u t).1 (u t).2) * Polynomial.X)
lemma wpP_eval (X A : Matrix (Fin n) (Fin n) R) (u : Fin k → (Fin n × Fin n)) (c:R) :
 (wpP X A u).eval c =
   ∏ t : Fin k, ((X + c • A) (u t).1 (u t).2) := by
 classical
 simp only [wpP, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
 -- entries
 apply Finset.prod_congr rfl
 intro t ht
 simp [mul_comm]

lemma wpP_degree (X A : Matrix (Fin n) (Fin n) R) (u : Fin k → (Fin n × Fin n)) :
  (wpP X A u).natDegree ≤ k := by
 classical
 unfold wpP
 refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
 have hterm (t : Fin k) :
      (C (X (u t).1 (u t).2) + C (A (u t).1 (u t).2) * Polynomial.X).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    -- constant and linear
    exact max_le ((by simpa using Polynomial.natDegree_C (X (u t).1 (u t).2))) (by
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      simp)
 exact (Finset.sum_le_sum (fun i hi => hterm i)).trans (by simp)
lemma coeff_top (X A : Matrix (Fin n) (Fin n) R) (u : Fin k → (Fin n × Fin n)) :
 (wpP X A u).coeff k = ∏ t : Fin k, A (u t).1 (u t).2 := by
 classical
 have hfac (t : Fin k) :
      (C (X (u t).1 (u t).2) + C (A (u t).1 (u t).2) * Polynomial.X).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    exact max_le ((by simpa using Polynomial.natDegree_C (X (u t).1 (u t).2))) (by
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      simp)
 have hcoef (t : Fin k) :
      (C (X (u t).1 (u t).2) + C (A (u t).1 (u t).2) * Polynomial.X).coeff 1 =
        A (u t).1 (u t).2 := by
    simp [Polynomial.coeff_add, Polynomial.coeff_C_mul_X]
 unfold wpP
 have hv :=
   (Polynomial.coeff_prod_of_natDegree_le
      (s := (Finset.univ : Finset (Fin k)))
      (f := fun t : Fin k =>
        (C (X (u t).1 (u t).2) + C (A (u t).1 (u t).2) * Polynomial.X))
      1 (by intro i hi; exact hfac i))
 -- simplify card*1
 simp only [Finset.card_univ, Fintype.card_fin, mul_one] at hv
 -- replace the top coefficients
 simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul_X] using hv


noncomputable def totP (l : ((Fin k → (Fin n × Fin n)) → R) →ₗ[R] R)
 (X A : Matrix (Fin n) (Fin n) R) : R[X] :=
  ∑ u : (Fin k → (Fin n × Fin n)),
       C (l (Pi.single u (1:R))) * wpP X A u

lemma lin_expand (l : ((Fin k → (Fin n × Fin n)) → R) →ₗ[R] R)
 (F : (Fin k → (Fin n × Fin n)) → R) :
 l F = ∑ u : (Fin k → (Fin n × Fin n)),
          F u * l (Pi.single u (1:R)) := by
 classical
 have hv : F = ∑ u : (Fin k → (Fin n × Fin n)),
                    (F u) • Pi.single u (1:R) := by
   funext v
   simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
   rw [Finset.sum_eq_single v]
   · simp
   · intro b hb hn; simp [Ne.symm hn]
   · simp
 calc
   l F = l (∑ u : (Fin k → (Fin n × Fin n)), (F u) • Pi.single u (1:R)) := by conv_lhs => rw [hv]
   _ = _ := by simp [mul_comm]

lemma totP_eval (l : ((Fin k → (Fin n × Fin n)) → R) →ₗ[R] R)
 (X A : Matrix (Fin n) (Fin n) R) (c:R) :
 (totP l X A).eval c = l (SchurAux.wordPower (k:=k) (X + c • A)) := by
 classical
 rw [lin_expand]
 unfold totP
 simp_rw [Polynomial.eval_finset_sum]
 -- eval product
 simp_rw [Polynomial.eval_mul, Polynomial.eval_C, wpP_eval]
 -- reorder
 unfold SchurAux.wordPower
 apply Finset.sum_congr rfl
 intro u hu
 ring

lemma totP_degree (l : ((Fin k → (Fin n × Fin n)) → R) →ₗ[R] R)
 (X A : Matrix (Fin n) (Fin n) R) :
 (totP l X A).natDegree ≤ k := by
 classical
 unfold totP
 refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
 apply Finset.sup_le
 intro u hu
 dsimp [Function.comp_apply]
 -- C * wp
 by_cases h0 : l (Pi.single u (1:R)) = 0
 · simp [h0]
 · rw [Polynomial.natDegree_C_mul h0]
   exact wpP_degree X A u

lemma totP_coeff_top (l : ((Fin k → (Fin n × Fin n)) → R) →ₗ[R] R)
 (X A : Matrix (Fin n) (Fin n) R) :
 (totP l X A).coeff k = l (SchurAux.wordPower (k:=k) A) := by
 classical
 -- expand both
 rw [lin_expand]
 unfold totP
 change (Polynomial.lcoeff R k) (∑ u, C (l (Pi.single u (1:R))) * wpP X A u) = _
 rw [map_sum]
 change (∑ u, (C (l (Pi.single u (1:R))) * wpP X A u).coeff k) = _
 simp_rw [Polynomial.coeff_C_mul]
 simp_rw [coeff_top (X:=X) (A:=A)]
 unfold SchurAux.wordPower
 apply Finset.sum_congr rfl
 intro u hu
 ring

lemma small_ne (hfac : (k.factorial : R) ≠ 0)
 {m : ℕ} (hm0 : 0 < m) (hmk : m ≤ k) : (m : R) ≠ 0 := by
 intro hzero
 obtain ⟨z,hz⟩ := Nat.dvd_factorial hm0 hmk
 have : (k.factorial : R) = 0 := by
   rw [hz, Nat.cast_mul, hzero, zero_mul]
 exact hfac this
lemma small_inj (hfac : (k.factorial : R) ≠ 0)
 {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k)
 (h : (i : R) = (j : R)) : i = j := by
 by_contra hn
 rcases lt_or_gt_of_ne hn with hlt|hgt
 · have hz : ((j-i:ℕ) : R) = 0 := by
     rw [Nat.cast_sub (show i ≤ j from Nat.le_of_lt hlt), h, sub_self]
   exact (small_ne hfac (Nat.sub_pos_of_lt hlt)
        (Nat.le_trans (Nat.sub_le _ _) hj)) hz
 · have hz : ((i-j:ℕ) : R) = 0 := by
     rw [Nat.cast_sub (show j ≤ i from Nat.le_of_lt hgt), h, sub_self]
   exact (small_ne hfac (Nat.sub_pos_of_lt hgt)
        (Nat.le_trans (Nat.sub_le _ _) hi)) hz
lemma ces (hfac : (k.factorial : R) ≠ 0) :
  Function.Injective (fun i : Fin k => ((i.1+1 : ℕ) : R)) := by
 intro i j h
 have hij : i.val+1 = j.val+1 := small_inj hfac
   (by omega) (by omega) h
 apply Fin.ext
 omega
lemma ces_ne0 (hfac : (k.factorial : R) ≠ 0) (i:Fin k) : (((i.1+1:ℕ):R)) ≠ 0 := by
 apply small_ne hfac <;> omega

lemma roots_zero (p : R[X]) (c : Fin k → R) (hc : Function.Injective c)
 (hle : p.natDegree ≤ k) (hcoef : p.coeff k = 0)
 (heval : ∀ i, p.eval (c i) = 0) : p = 0 := by
 classical
 by_contra hp0
 have hdeg' : p.degree < (k:WithBot ℕ) :=
   (Polynomial.degree_lt_iff_coeff_zero p k).2 (by
     intro m hm
     rcases Nat.eq_or_lt_of_le hm with rfl | hlt
     · exact hcoef
     · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle hlt))
 have hdeg : p.natDegree < k :=
   (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hdeg'
 have hsub : Finset.univ.image c ⊆ p.roots.toFinset := by
   intro x hx
   rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
   exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp0).2 (heval i))
 have hcard : k ≤ p.roots.toFinset.card := by
   have hci : (Finset.univ.image c).card = k := by
      rw [Finset.card_image_of_injective _ hc]
      simp
   rw [← hci]
   exact Finset.card_le_card hsub
 have hr := Polynomial.card_roots' p
 have ht : p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le _
 omega


lemma wordPower_mem_of_good_line
 {X A : Matrix (Fin n) (Fin n) R}
 (S : Submodule R ((Fin k → (Fin n × Fin n)) → R))
 (hkfac : (k.factorial : R) ≠ 0)
 (hA : SchurAux.wordPower (k:=k) A ∈ S)
 (hline : ∀ c : R, c ≠ 0 →
       SchurAux.wordPower (k:=k) (X + c • A) ∈ S) :
 SchurAux.wordPower (k:=k) X ∈ S := by
 classical
 by_contra hnmem
 obtain ⟨l, hlne, hlker⟩ :=
   Submodule.exists_le_ker_of_notMem (p:=S) hnmem
 -- test polynomial
 let p : R[X] := totP l X A
 have htop : p.coeff k = 0 := by
   change (totP l X A).coeff k = 0
   rw [totP_coeff_top]
   exact (hlker hA)
 let c : Fin k → R := fun i => ((i.val + 1 : ℕ) : R)
 have hc : Function.Injective c := ces hkfac
 have hnon : ∀ i, c i ≠ 0 := ces_ne0 hkfac
 have heval : ∀ i, p.eval (c i) = 0 := by
   intro i
   change (totP l X A).eval (c i) = 0
   rw [totP_eval]
   exact hlker (hline (c i) (hnon i))
 have hzero : p = 0 := roots_zero p c hc (totP_degree l X A) htop heval
 have hz0 : p.eval (0:R) = 0 := by rw [hzero]; simp
 have hh : l (SchurAux.wordPower (k:=k) X) = 0 := by
   have hv : l (SchurAux.wordPower (k:=k) (X + (0:R) • A)) = 0 := by
     rw [← totP_eval]
     exact hz0
   simpa using hv
 exact hlne hh


-- elementary row-equivalence factorization used for the pencil argument
open Module
open FiniteDimensional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

-- abstract lemma
lemma fac_endo (f : Module.End K V) (hbot : LinearMap.ker f ≠ ⊥) :
    ∃ (a g : Module.End K V), IsUnit a ∧ IsNilpotent g ∧ f = a * g := by
  classical
  let p : Submodule K V := LinearMap.ker f
  obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
  let d : ℕ := Module.finrank K p
  have hdpos : 0 < d := by
    dsimp [d]
    rw [Module.finrank_pos_iff]
    exact (Submodule.nontrivial_iff_ne_bot.mpr hbot)
  let r : ℕ := Module.finrank K q
  let bp : Basis (Fin d) K p := Module.finBasis K p
  let bq : Basis (Fin r) K q := Module.finBasis K q
  let ee : (p × q) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl p q hpq
  let b : Basis (Fin d ⊕ Fin r) K V := (bp.prod bq).map ee
  let i0 : Fin d := ⟨0, hdpos⟩
  have blev_l (i : Fin d) : b (Sum.inl i) = (bp i : V) := by
    -- simp
    change ee ((bp.prod bq) (Sum.inl i)) = _
    -- compute pair
    change ((bp.prod bq) (Sum.inl i)).1.val + ((bp.prod bq) (Sum.inl i)).2.val = _
    rw [Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd]
    simp
  have blev_r (j : Fin r) : b (Sum.inr j) = (bq j : V) := by
    change ee ((bp.prod bq) (Sum.inr j)) = _
    change ((bp.prod bq) (Sum.inr j)).1.val + ((bp.prod bq) (Sum.inr j)).2.val = _
    rw [Basis.prod_apply_inr_fst, Basis.prod_apply_inr_snd]
    simp
  -- shift into the indices of b
  let sh : Fin r → (Fin d ⊕ Fin r) := fun j =>
    if hj : j.val = 0 then Sum.inl i0
    else Sum.inr (⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ : Fin r)
  have shinj : Function.Injective sh := by
    intro j j' h
    dsimp [sh] at h
    split at h <;> rename_i hj
    · split at h <;> rename_i hj'
      · exact Fin.ext (hj.trans hj'.symm)
      · cases h
    · split at h <;> rename_i hj'
      · cases h
      · have he : j.val - 1 = j'.val - 1 := by
          have hh : (⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ : Fin r) =
                    ⟨j'.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j'.isLt⟩ :=
            Sum.inr.inj h
          exact congrArg Fin.val hh
        apply Fin.ext
        omega
  -- endomorphism killing p and shifting q
  let vals : (Fin d ⊕ Fin r) → V := Sum.elim (fun _ => 0) (fun j => b (sh j))
  let g : Module.End K V := b.constr K vals
  have gb_l (i : Fin d) : g (b (Sum.inl i)) = 0 := by
    simpa [g, vals] using (b.constr_basis K vals (Sum.inl i))
  have gb_r (j : Fin r) : g (b (Sum.inr j)) = b (sh j) := by
    simpa [g, vals] using (b.constr_basis K vals (Sum.inr j))
  -- nilpotent: powers follow the chain
  have gnil : IsNilpotent g := by
    refine ⟨r+1, ?_⟩
    apply b.ext
    intro ij
    rcases ij with i|j
    · -- killed left
      change (g^(r+1)) (b (Sum.inl i)) = 0
      rw [pow_succ, Module.End.mul_apply, gb_l]
      simp
    · change (g^(r+1)) (b (Sum.inr j)) = 0
      have hv : ∀ j : Fin r, (g^(j.val+2)) (b (Sum.inr j)) = 0 := by
        intro w
        induction hval : w.val using Nat.strong_induction_on generalizing w with
        | h m ih =>
          cases m with
          | zero =>
            have hs : sh w = Sum.inl i0 := by simp [sh, hval]
            -- pow2
            change (g^2) (b (Sum.inr w)) = 0
            rw [show (2:ℕ)=1+1 by decide, pow_succ, Module.End.mul_apply,
                gb_r, hs]
            simp [gb_l i0]
          | succ m =>
            let w' : Fin r := ⟨m, by omega⟩
            have hs : sh w = Sum.inr w' := by
              dsimp [sh]
              have hnot : w.val ≠ 0 := by omega
              simp [hnot, w', hval]
            have ih' : (g^(w'.val+2)) (b (Sum.inr w')) = 0 :=
              ih m (Nat.lt_succ_self _) w' rfl
            have ex : m+1+2 = (w'.val+2)+1 := by dsimp [w']
            rw [ex, pow_succ, Module.End.mul_apply, gb_r, hs, ih']
      have hj := hv j
      obtain ⟨m, hm⟩ : ∃ m, (r+1) = m + (j.val+2) := by
        have le : j.val+2 ≤ r+1 := by omega
        exact ⟨(r+1)-(j.val+2), (Nat.sub_add_cancel le).symm⟩
      rw [hm, pow_add, Module.End.mul_apply, hj]
      simp
  have gp (x : p) : g (x : V) = 0 := by
    have he : g.comp p.subtype = (0 : p →ₗ[K] V) := by
      apply bp.ext
      intro i
      change g ( (bp i : p) : V) = 0
      rw [← blev_l, gb_l]
    exact LinearMap.congr_fun he x
  have gqinj : Function.Injective (g.comp q.subtype) := by
    let tq : q →ₗ[K] V := bq.constr K (fun j => b (sh j))
    have ht : g.comp q.subtype = tq := by
      apply bq.ext
      intro j
      change g ((bq j : q) : V) = _
      rw [← blev_r, gb_r]
      exact (bq.constr_basis K (fun w => b (sh w)) j).symm
    rw [ht]
    exact bq.injective_constr_of_linearIndependent
      (b.linearIndependent.comp sh shinj)
  have fp (x : p) : f (x : V) = 0 := by
    exact (LinearMap.mem_ker).1 x.property
  have fqinj : Function.Injective (f.comp q.subtype) := by
    intro x y hxy
    have hzero : f ((x:V) - (y:V)) = 0 := by
      simpa using sub_eq_zero.mpr hxy
    have inp : (x:V) - (y:V) ∈ p := (LinearMap.mem_ker).2 hzero
    have inq : (x:V) - (y:V) ∈ q := by
      exact q.sub_mem x.property y.property
    have hz : (x:V) - (y:V) = 0 :=
      (Submodule.disjoint_def.mp hpq.disjoint) _ inp inq
    have heq : (x:V) = (y:V) := sub_eq_zero.mp hz
    exact Subtype.ext heq
  -- package the restrictions as equivalences onto the ranges
  let tg : q →ₗ[K] LinearMap.range g :=
    (g.comp q.subtype).codRestrict (LinearMap.range g)
      (by intro x; exact ⟨x, rfl⟩)
  let tf : q →ₗ[K] LinearMap.range f :=
    (f.comp q.subtype).codRestrict (LinearMap.range f)
      (by intro x; exact ⟨x, rfl⟩)
  have tginj : Function.Injective tg := by
    intro x y hxy
    apply gqinj
    exact congrArg Subtype.val hxy
  have tfinj : Function.Injective tf := by
    intro x y hxy
    apply fqinj
    exact congrArg Subtype.val hxy
  have tgsurj : Function.Surjective tg := by
    rintro ⟨y, ⟨v,hv⟩⟩
    rcases z : ee.symm v with ⟨xp,xq⟩
    refine ⟨xq, ?_⟩
    apply Subtype.ext
    change g (xq:V) = y
    rw [← hv]
    have ev : (xp:V) + (xq:V) = v := by
      have := ee.apply_symm_apply v
      rw [z] at this
      exact this
    rw [← ev]
    simp [map_add, gp xp]
  have tfsurj : Function.Surjective tf := by
    rintro ⟨y, ⟨v,hv⟩⟩
    rcases z : ee.symm v with ⟨xp,xq⟩
    refine ⟨xq, ?_⟩
    apply Subtype.ext
    change f (xq:V) = y
    rw [← hv]
    have ev : (xp:V) + (xq:V) = v := by
      have hh := ee.apply_symm_apply v
      rw [z] at hh
      exact hh
    rw [← ev]
    simp [map_add, fp xp]
  let eg : q ≃ₗ[K] LinearMap.range g :=
    LinearEquiv.ofBijective tg ⟨tginj, tgsurj⟩
  let ef : q ≃ₗ[K] LinearMap.range f :=
    LinearEquiv.ofBijective tf ⟨tfinj, tfsurj⟩
  let ph : LinearMap.range g ≃ₗ[K] LinearMap.range f := eg.symm.trans ef
  have ph_apply (x : q) : ph (⟨g (x:V), ⟨(x:V), rfl⟩⟩ : LinearMap.range g)
          = (⟨f (x:V), ⟨(x:V), rfl⟩⟩ : LinearMap.range f) := by
      -- eg x, ef x
      change ph (tg x) = tf x
      change ef (eg.symm (eg x)) = ef x
      rw [eg.symm_apply_apply]
  -- choose complements to the ranges
  obtain ⟨ug, hug⟩ := Submodule.exists_isCompl (LinearMap.range g)
  obtain ⟨uf, huf⟩ := Submodule.exists_isCompl (LinearMap.range f)
  let EG : (LinearMap.range g × ug) ≃ₗ[K] V :=
    Submodule.prodEquivOfIsCompl _ _ hug
  let EF : (LinearMap.range f × uf) ≃ₗ[K] V :=
    Submodule.prodEquivOfIsCompl _ _ huf
  have hdim : Module.finrank K ug = Module.finrank K uf := by
    have H1 : Module.finrank K (LinearMap.range g) + Module.finrank K ug =
          Module.finrank K V := by
      simpa [Module.finrank_prod] using EG.finrank_eq
    have H2 : Module.finrank K (LinearMap.range f) + Module.finrank K uf =
          Module.finrank K V := by
      simpa [Module.finrank_prod] using EF.finrank_eq
    have Hr : Module.finrank K (LinearMap.range g) =
              Module.finrank K (LinearMap.range f) := ph.finrank_eq
    omega
  let ps : ug ≃ₗ[K] uf := LinearEquiv.ofFinrankEq _ _ hdim
  let mid : (LinearMap.range g × ug) ≃ₗ[K] (LinearMap.range f × uf) :=
    ph.prodCongr ps
  let big : V ≃ₗ[K] V := EG.symm.trans (mid.trans EF)
  let a : Module.End K V := big.toLinearMap
  have ha : IsUnit a := by
    exact (LinearMap.isUnit_iff_ker_eq_bot a).2
      ((LinearMap.ker_eq_bot).2 big.injective)
  refine ⟨a, g, ha, gnil, ?_⟩
  -- equality on vectors by decomposition
  apply LinearMap.ext
  intro x
  change f x = a (g x)
  -- represent x as p+q
  rcases z : ee.symm x with ⟨xp,xq⟩
  have ev : (xp:V) + (xq:V) = x := by
    have hh := ee.apply_symm_apply x
    rw [z] at hh
    exact hh
  have gx : g x = g (xq:V) := by rw [← ev]; simp [map_add, gp xp]
  have fx : f x = f (xq:V) := by rw [← ev]; simp [map_add, fp xp]
  rw [gx, fx]
  -- expand big on a range element
  change f (xq:V) = big (g (xq:V))
  change f (xq:V) = EF (mid (EG.symm (g (xq:V))))
  have hleft : EG.symm (g (xq:V)) =
       (⟨g (xq:V), ⟨(xq:V), rfl⟩⟩, 0) := by
    dsimp [EG]
    exact Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hug
      (⟨g (xq:V), ⟨(xq:V), rfl⟩⟩ : LinearMap.range g)
  rw [hleft]
  change f (xq:V) = EF (ph ⟨g (xq:V), ⟨(xq:V), rfl⟩⟩, ps 0)
  rw [ph_apply xq]
  -- EF maps pair to sum
  change f (xq:V) = ( (⟨f (xq:V), ⟨(xq:V), rfl⟩⟩ : LinearMap.range f) : V) + (ps 0 : uf)
  simp

lemma fac_matrix {K : Type*} [Field K] {n : ℕ}
  (X : Matrix (Fin n) (Fin n) K) (hX : ¬ IsUnit X) :
  ∃ (A N : Matrix (Fin n) (Fin n) K),
       IsUnit A ∧ IsNilpotent N ∧ X = A * N := by
  classical
  let bb : Basis (Fin n) K (Fin n → K) := Pi.basisFun K (Fin n)
  let E : Module.End K (Fin n → K) ≃ₐ[K]
        Matrix (Fin n) (Fin n) K := LinearMap.toMatrixAlgEquiv bb
  let f : Module.End K (Fin n → K) := E.symm X
  have hfu : ¬ IsUnit f := by
    intro h
    have hm : IsUnit (E f) :=
      IsUnit.map E.toRingEquiv.toRingHom h
    have he : E f = X := E.apply_symm_apply X
    exact hX (he ▸ hm)
  have hb : LinearMap.ker f ≠ ⊥ := by
    intro h
    exact hfu ((LinearMap.isUnit_iff_ker_eq_bot f).2 h)
  obtain ⟨a,g,ha,hg,hfg⟩ := fac_endo f hb
  refine ⟨E a, E g, ?_, ?_, ?_⟩
  · exact IsUnit.map E.toRingEquiv.toRingHom ha
  · exact hg.map E.toRingEquiv.toRingHom
  · have he : E f = X := E.apply_symm_apply X
    rw [← he, hfg]
    exact E.map_mul a g



end SchurAux

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem glAction_range_eq_centralizer_symAction {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {k : ℕ} [Invertible (k.factorial : R)] :
    Algebra.adjoin R (Set.range (glAction R M k)) =
      Subalgebra.centralizer R (Set.range (symAction R M k)) :=
/-ResultProofBegin-/by
  apply le_antisymm
  · exact adjoin_glAction_le_centralizer_symAction (R:=R) (M:=M) (k:=k)
  · intro a ha
    -- Since the diagonal maps form a monoid already, no iterated algebra
    -- words are necessary on this side: it is enough to prove linear-span
    -- membership.
    have hspan : a ∈ Submodule.span R (Set.range (glAction R M k)) := by
      classical
      -- In a basis, the remaining assertion is the finite polynomial/matrix
      -- part of Schur--Weyl.  Keeping track of the two bases is useful: a
      -- permutation simply permutes row and column multi-indices.
      let n := Module.finrank R M
      let b : Module.Basis (Fin n) R M := Module.finBasis R M
      let tb : Module.Basis (Fin k → Fin n) R (⨂[R]^k M) :=
        Basis.piTensorProduct (fun _ : Fin k => b)
      let L : (Module.End R (⨂[R]^k M)) ≃ₗ[R]
          Matrix (Fin k → Fin n) (Fin k → Fin n) R :=
        LinearMap.toMatrix tb tb
      have hc : ∀ σ : Equiv.Perm (Fin k),
          (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap * a =
            a * (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap := by
        intro σ
        exact (Subalgebra.mem_centralizer_iff R).1 ha _ ⟨σ, rfl⟩
      have hcoeff : ∀ (σ : Equiv.Perm (Fin k)) (i j : Fin k → Fin n),
          L a (fun t => i (σ.symm t)) (fun t => j (σ.symm t)) = L a i j := by
        intro σ i j
        simpa [L, tb] using
          (SchurAux.coeff_invariant_of_commute (b:=b) (a:=a) hc σ i j)
      have hm : L a ∈ Submodule.span R
          {Y | ∃ X : Matrix (Fin n) (Fin n) R,
                    IsUnit X ∧ SchurAux.diag (k:=k) X = Y} := by
        classical
        let E := SchurAux.matrixWordEquiv R n k
        let S₀ : Submodule R (Matrix (Fin k → Fin n) (Fin k → Fin n) R) :=
          Submodule.span R
            {Y | ∃ X : Matrix (Fin n) (Fin n) R,
                      IsUnit X ∧ SchurAux.diag (k:=k) X = Y}
        -- Transport the subspace along the harmless re-packing of the two
        -- multi-indices into words in pairs.
        let T : Submodule R ((Fin k → (Fin n × Fin n)) → R) :=
          Submodule.map E.toLinearMap S₀
        have hpowerImage :
            E '' {Y | ∃ X : Matrix (Fin n) (Fin n) R,
                        IsUnit X ∧ SchurAux.diag (k:=k) X = Y} =
              {F | ∃ X : Matrix (Fin n) (Fin n) R,
                        IsUnit X ∧ SchurAux.wordPower (k:=k) X = F} := by
          ext F
          constructor
          · intro hF'
            rcases hF' with ⟨Y, ⟨X, hxu, hx⟩, rfl⟩
            refine ⟨X, hxu, ?_⟩
            rw [← hx]
            exact SchurAux.matrixWordEquiv_diag_wordPower (k:=k) X
          · intro hF'
            rcases hF' with ⟨X, hxu, rfl⟩
            refine ⟨SchurAux.diag (k:=k) X, ⟨X, hxu, rfl⟩, ?_⟩
            exact SchurAux.matrixWordEquiv_diag_wordPower (k:=k) X
        have hT : T = Submodule.span R
              {F | ∃ X : Matrix (Fin n) (Fin n) R,
                        IsUnit X ∧ SchurAux.wordPower (k:=k) X = F} := by
          dsimp [T, S₀]
          rw [Submodule.map_span]
          -- images of the generating sets
          exact congrArg (Submodule.span R) hpowerImage
        have hs : ∀ s : Fin k → (Fin n × Fin n),
              SchurAux.funSymm (R:=R) s ∈ T := by
          intro s
          -- This is now a completely explicit polarization statement about one
          -- orbit of a word.  The earlier `hm` asserted the conclusion for an
          -- arbitrary invariant matrix; no invariance (and no `a` or `M`)
          -- remains in this finite lemma.
          rw [hT]
          -- active finite polynomial lemma: the symmetric sum of a single word
          -- is in the span of the pure powers of *invertible* matrices.
          by_cases hk : k = 0
          · subst k
            apply Submodule.subset_span
            refine ⟨(1 : Matrix (Fin n) (Fin n) R), isUnit_one, ?_⟩
            -- there is just the empty word/permutation
            funext u
            have hu : u = (fun z : Fin 0 => (s z)) := by funext z; exact Fin.elim0 z
            classical
            simpa [SchurAux.wordPower, SchurAux.funSymm, SchurAux.funDelta]
              using hu
          · by_cases hn : n = 0
            · have hpos : 0 < k := Nat.pos_of_ne_zero hk
              have ii : Fin k := ⟨0, hpos⟩
              exact Fin.elim0 (Fin.cast hn ((s ii).1))
            · -- after labelled polarization it remains only to replace an
              -- arbitrary matrix by invertible matrices.  All combinatorics
              -- of an orbit (including repeated letters) has disappeared.
              let Uspan : Submodule R ((Fin k → (Fin n × Fin n)) → R) :=
                Submodule.span R {F | ∃ X : Matrix (Fin n) (Fin n) R,
                        IsUnit X ∧ SchurAux.wordPower (k:=k) X = F}
              have hpowers : ∀ X : Matrix (Fin n) (Fin n) R,
                       SchurAux.wordPower (k:=k) X ∈ Uspan := by
                intro X
                by_cases hx0 : X = 0
                · subst X
                  have hz : SchurAux.wordPower (k:=k)
                        (0 : Matrix (Fin n) (Fin n) R) = 0 := by
                    funext u
                    unfold SchurAux.wordPower
                    have t0 : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
                    exact Finset.prod_eq_zero (Finset.mem_univ t0) (by simp)
                  rw [hz]
                  exact Uspan.zero_mem
                · by_cases hx : IsUnit X
                  · exact Submodule.subset_span ⟨X, hx, rfl⟩
                  · have hxdet : X.det = 0 := by
                      by_contra hdet
                      have hu : IsUnit X :=
                        (Matrix.isUnit_iff_isUnit_det X).2
                          ((isUnit_iff_ne_zero).2 hdet)
                      exact hx hu
                    have hfac : (k.factorial : R) ≠ 0 :=
                      (isUnit_of_invertible (k.factorial : R)).ne_zero
                    -- It remains a pure linear-algebra line construction.  Once a
                    -- direction with a nilpotent pencil is chosen, interpolation of
                    -- the preceding scalar polynomial proves the required span.
                    have hnil_factor : ∃ (A N : Matrix (Fin n) (Fin n) R),
                        IsUnit A ∧ IsNilpotent N ∧ X = A * N := by
                      exact SchurAux.fac_matrix X hx
                    rcases hnil_factor with ⟨A, N, hAu, hNu, hfacN⟩
                    have hAc : ∀ c : R, c ≠ 0 → IsUnit (X + c • A) :=
                      SchurAux.line_factor X A N hAu hNu hfacN
                    exact SchurAux.wordPower_mem_of_good_line (k:=k)
                      (X:=X) (A:=A) Uspan hfac
                      (Submodule.subset_span ⟨A, hAu, rfl⟩)
                      (fun c hc => Submodule.subset_span
                         ⟨X + c • A, hAc c hc, rfl⟩)

              change SchurAux.funSymm (R:=R) s ∈ Uspan
              rw [SchurAux.funSymm_eq_sum_powers (R:=R) s]
              exact Submodule.sum_mem _ (fun I _ =>
                Submodule.smul_mem _ _ (hpowers (SchurAux.posSumMat (R:=R) s I)))

        have hchar : (k.factorial : R) ≠ 0 :=
          (isUnit_of_invertible (k.factorial : R)).ne_zero
        have hF : ∀ (σ : Equiv.Perm (Fin k))
              (u : Fin k → (Fin n × Fin n)),
              E (L a) (fun t => u (σ.symm t)) = E (L a) u := by
          intro σ u
          change L a (fun t => (u (σ.symm t)).1)
                    (fun t => (u (σ.symm t)).2) =
                 L a (fun t => (u t).1) (fun t => (u t).2)
          exact hcoeff σ (fun t => (u t).1) (fun t => (u t).2)
        have hmem : E (L a) ∈ T :=
          SchurAux.invariant_fun_mem_of_symm
            (F:= E (L a)) hchar hF T hs
        rcases (Submodule.mem_map).1 hmem with ⟨z, hz, he⟩
        have hzl : z = L a := E.injective he
        -- The transport equivalence is injective, so membership transports
        -- back without a loss.
        change L a ∈ S₀
        simpa [hzl] using hz
      have himage :
          L '' (Set.range (glAction R M k)) =
            {Y | ∃ X : Matrix (Fin n) (Fin n) R,
                   IsUnit X ∧ SchurAux.diag (k:=k) X = Y} := by
        simpa [L, tb] using
          (SchurAux.image_range_diag (R:=R) (b:=b) (k:=k))
      rw [← himage] at hm
      have hm' : L a ∈ Submodule.map L.toLinearMap
          (Submodule.span R (Set.range (glAction R M k))) := by
        rw [Submodule.map_span]
        exact hm
      rcases (Submodule.mem_map).1 hm' with ⟨z, hz, hza⟩
      have za : z = a := L.injective hza
      simpa [za] using hz
    have hsub : a ∈ (Algebra.adjoin R
        (Set.range (glAction R M k))).toSubmodule := by
      simpa [adjoin_range_monoidHom_toSubmodule]
        using hspan
    exact hsub
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
