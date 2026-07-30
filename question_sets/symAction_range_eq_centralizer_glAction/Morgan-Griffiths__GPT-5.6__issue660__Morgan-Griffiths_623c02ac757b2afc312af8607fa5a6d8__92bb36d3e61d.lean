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

lemma glAction_symAction_commute {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] (k : ℕ)
    (σ : Equiv.Perm (Fin k)) (g : (M →ₗ[R] M)ˣ) :
    (glAction R M k g) * (symAction R M k σ) =
      (symAction R M k σ) * (glAction R M k g) := by
  ext x
  simp only [Module.End.mul_apply,
    glAction, symAction,
    LinearMap.coe_compMultilinearMap, Function.comp_apply]
  rfl


lemma symAction_adjoin_le_centralizer_glAction
    {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] (k : ℕ) :
    Algebra.adjoin R (Set.range (symAction R M k)) ≤
      Subalgebra.centralizer R (Set.range (glAction R M k)) := by
  refine Algebra.adjoin_le ?_
  rintro z ⟨σ, rfl⟩
  refine (Subalgebra.mem_centralizer_iff R).2 ?_
  rintro a ⟨g, rfl⟩
  exact glAction_symAction_commute k σ g


lemma end_empty_is_scalar {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (T : Module.End R (⨂[R]^ (0 : ℕ) M)) :
    ∃ r : R, T = algebraMap R (Module.End R (⨂[R]^ (0 : ℕ) M)) r := by
  let b : (⨂[R]^ (0 : ℕ) M) :=
    PiTensorProduct.tprod R (fun i : Fin 0 => isEmptyElim i)
  let e : (⨂[R]^ (0 : ℕ) M) ≃ₗ[R] R :=
    PiTensorProduct.isEmptyEquiv (Fin 0)
  let r : R := e (T b)
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro x
  have hrep (y : (⨂[R]^ (0 : ℕ) M)) : y = (e y) • b := by
    have h := e.symm_apply_apply y
    change (PiTensorProduct.isEmptyEquiv (Fin 0)).symm
      ((PiTensorProduct.isEmptyEquiv (Fin 0)) y) = y at h
    rw [PiTensorProduct.isEmptyEquiv_symm_apply] at h
    exact h.symm
  have hb : T b = r • b := by
    simpa [r] using hrep (T b)
  -- now use linearity
  rw [hrep x, map_smul, hb]
  -- compute the scalar endomorphism
  change (e x) • (r • b) = r • ((e x) • b)
  -- commutative scalars
  rw [smul_smul, smul_smul, mul_comm]

lemma piTensorProduct_subsingleton_of_subsingleton
    {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Subsingleton M]
    {ι : Type*} [Nonempty ι] :
    Subsingleton (⨂[R] (_ : ι), M) := by
  constructor
  intro x y
  have hzero (z : (⨂[R] (_ : ι), M)) : z = 0 := by
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r f =>
        let i : ι := Classical.choice (inferInstance : Nonempty ι)
        have hi : f i = 0 := Subsingleton.elim _ _
        have ht : (PiTensorProduct.tprod R) f = 0 :=
          MultilinearMap.map_coord_zero (PiTensorProduct.tprod R) i hi
        rw [ht, smul_zero]
    | add a b ha hb =>
        rw [ha, hb, add_zero]
  rw [hzero x, hzero y]

lemma end_eq_scalar_of_commutes_units {R V : Type*} [Field R]
 [AddCommGroup V] [Module R V] [FiniteDimensional R V]
 (f : Module.End R V)
 (h : ∀ g : (Module.End R V)ˣ, (g : Module.End R V) * f = f * (g : Module.End R V)) :
 ∃ r : R, f = algebraMap R (Module.End R V) r := by
  classical
  by_cases hdim0 : Module.finrank R V = 0
  · letI : Subsingleton V := (Module.finrank_zero_iff).1 hdim0
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  by_cases hdim1 : Module.finrank R V = 1
  · let b := Module.finBasis R V
    let i : Fin (Module.finrank R V) := ⟨0, Nat.pos_of_ne_zero hdim0⟩
    let r : R := (b.repr (f (b i))) i
    refine ⟨r, ?_⟩
    apply LinearMap.ext
    intro x
    -- show via repr all coords
    rw [b.ext_elem_iff]
    intro j
    have hji : j = i := by
      -- both indices fin1
      apply Fin.ext
      have hfin : ∀ a : Fin (Module.finrank R V), a.val = 0 := by
        intro a
        have : a.val < 1 := by simpa [hdim1] using a.isLt
        exact (Nat.lt_one_iff).1 this
      rw [hfin j, hfin i]
    subst j
    -- repr f x =...? use x expression in basis
    have hx : x = (b.repr x i) • b i := by
      rw [b.ext_elem_iff]
      intro j
      have hj : j = i := by
        apply Fin.ext
        have hfin : ∀ a : Fin (Module.finrank R V), a.val = 0 := by
          intro a
          have ha : a.val < 1 := by simpa [hdim1] using a.isLt
          exact (Nat.lt_one_iff).1 ha
        rw [hfin j, hfin i]
      subst j
      simp
    -- compute
    rw [hx]
    -- map_smul etc; need repr
    simp [r]
    -- maybe simp yields mul order
    -- rely field comm
  · have h2 : 2 ≤ Module.finrank R V :=
      (Nat.two_le_iff (Module.finrank R V)).2 ⟨hdim0, hdim1⟩
    let b := Module.finBasis R V
    letI : Nontrivial (Fin (Module.finrank R V)) :=
      (Fin.nontrivial_iff_two_le).2 h2
    obtain ⟨a, ha⟩ := LinearMap.commute_transvections_iff_of_basis b (f:=f) (by
      intro i j r hij
      have hz : (b.coord i) (r • b j) = 0 := by
        simp [hij]
      let u : (Module.End R V)ˣ :=
        LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection hz)
      -- using h u
      rw [commute_iff_eq]
      have hu : (u : Module.End R V) =
          LinearMap.transvection (b.coord i) (r • b j) := by
        exact LinearEquiv.transvection.coe_toLinearMap hz
      have hh := (h u).symm
      rw [hu] at hh
      exact hh)
    refine ⟨(a : R), ?_⟩
    -- convert ha
    simpa [Algebra.algebraMap_eq_smul_one, Subring.smul_def] using ha

lemma conj_glAction_one {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
 (g : (M →ₗ[R] M)ˣ) :
   (LinearEquiv.algConj R (PiTensorProduct.subsingletonEquiv (s:=fun _ : Fin 1 => M) (0:Fin 1)))
     (glAction R M 1 g) = (g : M →ₗ[R] M) := by
  apply LinearMap.ext
  intro x
  change (PiTensorProduct.subsingletonEquiv (s:=fun _ : Fin 1 => M) (0:Fin 1))
      ((glAction R M 1 g)
        ((PiTensorProduct.subsingletonEquiv (s:=fun _ : Fin 1 => M) (0:Fin 1)).symm x))
       = (g : M →ₗ[R] M) x
  rw [PiTensorProduct.subsingletonEquiv_symm_apply]
  change (PiTensorProduct.subsingletonEquiv (s:=fun _ : Fin 1 => M) (0:Fin 1))
    ((PiTensorProduct.map (fun _ : Fin 1 => (g : M →ₗ[R] M)))
      ((PiTensorProduct.tprod R) (fun i : Fin 1 => Function.update (0 : Fin 1 → M) (0:Fin 1) x i))) = _
  rw [PiTensorProduct.map_tprod]
  rw [PiTensorProduct.subsingletonEquiv_apply_tprod]
  simp

lemma centralizer_glAction_one_le {R M : Type*} [Field R]
    [AddCommGroup M] [Module R M] [FiniteDimensional R M] :
    Subalgebra.centralizer R (Set.range (glAction R M 1)) ≤
      Algebra.adjoin R (Set.range (symAction R M 1)) := by
  classical
  intro z hz
  let e : (⨂[R]^ (1:ℕ) M) ≃ₗ[R] M :=
    PiTensorProduct.subsingletonEquiv (s:=fun _ : Fin 1 => M) (0 : Fin 1)
  let A : Module.End R (⨂[R]^ (1:ℕ) M) ≃ₐ[R] Module.End R M :=
    LinearEquiv.algConj R e
  have hcomm (g : (M →ₗ[R] M)ˣ) :
      (g : Module.End R M) * (A z) = (A z) * (g : Module.End R M) := by
    have h0 : (glAction R M 1 g) * z = z * (glAction R M 1 g) :=
      (Subalgebra.mem_centralizer_iff R).1 hz _ ⟨g, rfl⟩
    have h1 := congrArg (fun t => A t) h0
    -- use multiplicativity under conjugation
    change A ((glAction R M 1 g) * z) = A (z * (glAction R M 1 g)) at h1
    rw [map_mul, map_mul] at h1
    have hg : A (glAction R M 1 g) = (g : Module.End R M) := by
      exact conj_glAction_one g
    rwa [hg] at h1
  obtain ⟨r, hr⟩ := end_eq_scalar_of_commutes_units (A z) hcomm
  have hzscalar : z = algebraMap R (Module.End R (⨂[R]^ (1:ℕ) M)) r := by
    apply A.injective
    -- map sends scalar to scalar
    simpa using hr
  rw [hzscalar]
  exact (Algebra.adjoin R (Set.range (symAction R M 1))).algebraMap_mem r


lemma end_is_scalar_of_unique_basis {R X ι : Type*} [CommSemiring R]
 [AddCommMonoid X] [Module R X] [Unique ι]
 (b : Module.Basis ι R X) (f : Module.End R X) :
 ∃ r : R, f = algebraMap R (Module.End R X) r := by
  let i : ι := default
  let r : R := (b.repr (f (b i))) i
  refine ⟨r, ?_⟩
  -- two linear maps agree on the (single) basis vector
  apply b.ext
  intro j
  have hj : j = i := Subsingleton.elim _ _
  subst j
  -- compare coordinates in the basis
  apply b.ext_elem
  intro j
  have hj : j = i := Subsingleton.elim _ _
  subst j
  -- a scalar endomorphism acts by scalar multiplication
  simp [r, Algebra.algebraMap_eq_smul_one]

lemma end_piTensor_is_scalar_finrank_one {R M : Type*} [Field R]
 [AddCommGroup M] [Module R M] [FiniteDimensional R M]
 (hM : Module.finrank R M = 1) (n : ℕ) :
 ∀ f : Module.End R (⨂[R]^ n M),
   ∃ r : R, f = algebraMap R (Module.End R (⨂[R]^ n M)) r := by
  classical
  -- use the tensor product basis.  Its type of indices is a product of
  -- singleton types and hence again a singleton.
  let bM := Module.finBasis R M
  letI : Unique (Fin (Module.finrank R M)) :=
    hM ▸ (inferInstance : Unique (Fin 1))
  letI : Unique ((i : Fin n) → Fin (Module.finrank R M)) :=
    { default := fun _ => default
      uniq := by
        intro a
        funext i
        exact Subsingleton.elim _ _ }
  let bT : Module.Basis ((i : Fin n) → Fin (Module.finrank R M)) R
      (⨂[R]^ n M) := Basis.piTensorProduct (fun _ : Fin n => bM)
  intro f
  exact end_is_scalar_of_unique_basis bT f
-- Diagonal maps commute with reindexing even when the common map is not a
-- unit.  This elementary observation is convenient in the ``large
-- dimension'' part of the tensor calculation below.
lemma tensor_diag_sym_commute {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (n : ℕ) (u : Module.End R M)
    (σ : Equiv.Perm (Fin n)) :
    (PiTensorProduct.map (fun _ : Fin n => u)) * (symAction R M n σ) =
      (symAction R M n σ) * (PiTensorProduct.map (fun _ : Fin n => u)) := by
  ext x
  simp only [Module.End.mul_apply, symAction,
    LinearMap.coe_compMultilinearMap, Function.comp_apply]
  rfl

-- Some notation-free lemmas about the diagonal projections in a tensor
-- product of a based module.
noncomputable def swProjection {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] {d : ℕ}
    (b : Module.Basis (Fin d) R M) (S : Finset (Fin d)) : Module.End R M :=
  (b.constr R) (fun j => if j ∈ S then b j else 0)

lemma swProjection_basis {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] {d : ℕ}
    (b : Module.Basis (Fin d) R M) (S : Finset (Fin d)) (j : Fin d) :
    swProjection b S (b j) = if j ∈ S then b j else 0 := by
  classical
  simp [swProjection, Module.Basis.constr_basis]

lemma swProjection_tprod {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] {d n : ℕ}
    (b : Module.Basis (Fin d) R M) (S : Finset (Fin d))
    (q : Fin n → Fin d) :
    (PiTensorProduct.map (fun _ : Fin n => swProjection b S))
       ((Basis.piTensorProduct (fun _ : Fin n => b)) q)
       = if (∀ i : Fin n, q i ∈ S)
           then (Basis.piTensorProduct (fun _ : Fin n => b)) q
           else 0 := by
  classical
  -- write a basis tensor as a pure tensor
  rw [Basis.piTensorProduct_apply]
  rw [PiTensorProduct.map_tprod]
  classical
  by_cases hq : ∀ i : Fin n, q i ∈ S
  · -- all the coordinates survive
    rw [if_pos hq]
    congr 1
    funext i
    rw [swProjection_basis, if_pos (hq i)]
  · classical
    rw [if_neg hq]
    push_neg at hq
    obtain ⟨i, hi⟩ := hq
    have hz : swProjection b S (b (q i)) = 0 := by
      rw [swProjection_basis, if_neg hi]
    exact MultilinearMap.map_coord_zero (PiTensorProduct.tprod R) i hz

-- coordinate formula for the same projection on an arbitrary tensor.  The
-- short proof just expands in the tensor basis.
lemma swProjection_repr {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] {d n : ℕ}
    (b : Module.Basis (Fin d) R M) (S : Finset (Fin d))
    (x : (⨂[R]^ n M)) (q : Fin n → Fin d) :
    let B := (Basis.piTensorProduct (fun _ : Fin n => b))
    B.repr ((PiTensorProduct.map (fun _ : Fin n => swProjection b S)) x) q
       = if (∀ i : Fin n, q i ∈ S) then B.repr x q else 0 := by
  classical
  dsimp
  let B := (Basis.piTensorProduct (fun _ : Fin n => b))
  -- expand x in the basis B
  have hx : (∑ p, (B.repr x p) • B p) = x := B.sum_repr x
  have hB (p : Fin n → Fin d) : B.repr (B p) q = if p = q then 1 else 0 := by
    rw [Module.Basis.repr_self_apply]
  have hP (p : Fin n → Fin d) :
      B.repr ((PiTensorProduct.map (fun _ : Fin n => swProjection b S)) (B p)) q =
        if (∀ i : Fin n, p i ∈ S) then (if p = q then 1 else 0) else 0 := by
    rw [swProjection_tprod b S p]
    by_cases hp : ∀ i : Fin n, p i ∈ S
    · rw [if_pos hp, if_pos hp]
      exact hB p
    · rw [if_neg hp, if_neg hp]
      simp
  rw [← hx]
  simp only [map_sum, LinearMap.map_smul]
  have sum_eval (F : (Fin n → Fin d) → ((Fin n → Fin d) →₀ R)) :
      (∑ p, F p) q = ∑ p, (F p) q := by
    let ev : ((Fin n → Fin d) →₀ R) →+ R :=
      { toFun := fun t => t q, map_zero' := rfl,
        map_add' := by intros; rfl }
    exact map_sum ev (fun p => F p) Finset.univ

  rw [sum_eval]
  split_ifs with hq
  · rw [sum_eval]
    apply Finset.sum_congr rfl
    intro p hp
    change (B.repr ((B.repr x p) • (PiTensorProduct.map (fun _ : Fin n => swProjection b S)) (B p)) q) =
       (B.repr ((B.repr x p) • (B p)) q)
    simp only [map_smul]
    change (B.repr x p) * ((B.repr ((PiTensorProduct.map (fun _ : Fin n => swProjection b S)) (B p))) q) =
      (B.repr x p) * ((B.repr (B p)) q)
    rw [hP p, hB p]
    by_cases hpq : p = q
    · subst p
      simp [hq]
    · simp [hpq]
  · apply Finset.sum_eq_zero
    intro p hp
    change (B.repr ((B.repr x p) • (PiTensorProduct.map (fun _ : Fin n => swProjection b S)) (B p)) q) = 0
    rw [map_smul]
    change (B.repr x p) * ((B.repr ((PiTensorProduct.map (fun _ : Fin n => swProjection b S)) (B p))) q) = 0
    rw [hP p]
    by_cases hpq : p = q
    · subst p; simp [hq]
    · simp [hpq]


lemma sw_indices_are_permutation {n d : ℕ} (h : n ≤ d) (q : Fin n → Fin d)
    (hAll : ∀ i, q i ∈ Finset.image (Fin.castLE h) (Finset.univ : Finset (Fin n)))
    (hHit : ∀ a : Fin n, ∃ i : Fin n, q i = Fin.castLE h a) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, q i = Fin.castLE h (e i) := by
  classical
  -- every value of q has a unique preimage under the standard inclusion
  have hpre (i : Fin n) : ∃ a : Fin n, Fin.castLE h a = q i := by
    rcases (Finset.mem_image.mp (hAll i)) with ⟨a, ha, hval⟩
    exact ⟨a, hval⟩
  let φ : Fin n → Fin n := fun i => Classical.choose (hpre i)
  have hφ (i : Fin n) : Fin.castLE h (φ i) = q i :=
    Classical.choose_spec (hpre i)
  have hsur : Function.Surjective φ := by
    intro a
    obtain ⟨i, hi⟩ := hHit a
    refine ⟨i, ?_⟩
    apply (Fin.castLE_injective h)
    simpa [hφ i] using hi
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_surjective_and_card φ).2 ⟨hsur, rfl⟩
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective φ hbij
  refine ⟨e, ?_⟩
  intro i
  exact (hφ i).symm.trans (by rfl)

/-- The elementary coefficient step in the usual based proof.  Here the
hypothesis is deliberately phrased with *all* common linear maps.  The
extension from units to these maps is the polynomial step of the argument.
If a tensor starts with `n` distinct basis vectors, every nonzero coefficient
of its image is a reordering of exactly those vectors.  Projections onto the
chosen coordinate hyperplanes give a particularly cheap proof; no diagonal
eigenvalue argument (and hence no assumption that the field is infinite) is
needed for this step. -/
lemma tensor_distinct_coefficient_of_all_maps {R M : Type*} [Field R]
    [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (n : ℕ) (hn : n ≤ Module.finrank R M)
    (T : Module.End R (⨂[R]^ n M))
    (hT : ∀ u : Module.End R M,
      (PiTensorProduct.map (fun _ : Fin n => u)) * T =
        T * (PiTensorProduct.map (fun _ : Fin n => u))) :
    let b := Module.finBasis R M
    let B := (Basis.piTensorProduct (fun _ : Fin n => b))
    let p : Fin n → Fin (Module.finrank R M) := Fin.castLE hn
    ∀ q : Fin n → Fin (Module.finrank R M),
       B.repr (T (B p)) q ≠ 0 →
        ∃ e : Equiv.Perm (Fin n), ∀ i, q i = Fin.castLE hn (e i) := by
  classical
  dsimp
  let b := Module.finBasis R M
  let B := (Basis.piTensorProduct (fun _ : Fin n => b))
  let p : Fin n → Fin (Module.finrank R M) := Fin.castLE hn
  let S : Finset (Fin (Module.finrank R M)) :=
    Finset.image (Fin.castLE hn) Finset.univ
  intro q hq
  have hmap (U : Finset (Fin (Module.finrank R M))) :
      (PiTensorProduct.map (fun _ : Fin n => swProjection b U)) (T (B p)) =
        T ((PiTensorProduct.map (fun _ : Fin n => swProjection b U)) (B p)) := by
    have ht := hT (swProjection b U)
    have hv := DFunLike.congr_fun ht (B p)
    simpa [Module.End.mul_apply] using hv
  have hpS : ∀ i : Fin n, p i ∈ S := by
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hkeep :
      (PiTensorProduct.map (fun _ : Fin n => swProjection b S)) (T (B p)) = T (B p) := by
    rw [hmap S, swProjection_tprod b S p, if_pos hpS]
  have hAll : ∀ i : Fin n, q i ∈ S := by
    by_contra hnot
    have hcoord := congrArg (fun y : (⨂[R]^ n M) => B.repr y q) hkeep
    -- the left hand coefficient is zero for a basis vector outside S
    rw [swProjection_repr b S (T (B p)) q, if_neg hnot] at hcoord
    exact hq hcoord.symm
  have hHit : ∀ a : Fin n, ∃ i : Fin n, q i = Fin.castLE hn a := by
    intro a
    by_contra hmiss
    push_neg at hmiss
    let U : Finset (Fin (Module.finrank R M)) := S.erase (Fin.castLE hn a)
    have hvzero :
        (PiTensorProduct.map (fun _ : Fin n => swProjection b U)) (B p) = 0 := by
      -- the a-th coordinate has just been erased
      have hpa : ¬ (∀ i : Fin n, p i ∈ U) := by
        intro HH
        have H := HH a
        have Hbad : Fin.castLE hn a ∉ U := by
          simp [U]
        exact Hbad H
      rw [swProjection_tprod b U p, if_neg hpa]
    have hz :
        (PiTensorProduct.map (fun _ : Fin n => swProjection b U)) (T (B p)) = 0 := by
      rw [hmap U, hvzero, map_zero]
    have hqU : ∀ i : Fin n, q i ∈ U := by
      intro i
      have hsi : q i ∈ S := hAll i
      have hne : q i ≠ Fin.castLE hn a := hmiss i
      exact Finset.mem_erase.mpr ⟨hne, hsi⟩
    have hcoord := congrArg (fun y : (⨂[R]^ n M) => B.repr y q) hz
    rw [swProjection_repr b U (T (B p)) q, if_pos hqU] at hcoord
    simp at hcoord
    exact hq hcoord
  exact sw_indices_are_permutation hn q hAll hHit
lemma cast_ne_zero_le_factorial {R : Type*} [Field R] (n t : ℕ)
    [Invertible (n.factorial : R)] (ht : 0 < t) (h : t ≤ n) : (t : R) ≠ 0 := by
  intro hz
  obtain ⟨c, hc⟩ := Nat.dvd_factorial ht h
  have hzfac : (n.factorial : R) = 0 := by
    rw [hc, Nat.cast_mul, hz, zero_mul]
  exact (isUnit_of_invertible (n.factorial : R)).ne_zero hzfac

lemma factorial_cast_injective_fin {R : Type*} [Field R] (n : ℕ)
    [Invertible (n.factorial : R)] :
    Function.Injective (fun i : Fin (n+1) => (i.val : R)) := by
  intro a b hab
  by_contra hn
  have hcases : a.val < b.val ∨ b.val < a.val := Nat.lt_or_gt_of_ne (by
    intro e; exact hn (Fin.ext e))
  cases hcases with
  | inl hlt =>
      have hpos : 0 < b.val - a.val := Nat.sub_pos_of_lt hlt
      have hle : b.val - a.val ≤ n := le_trans (Nat.sub_le _ _) (Nat.lt_succ_iff.mp b.isLt)
      have hne := cast_ne_zero_le_factorial (R:=R) n (b.val-a.val) hpos hle
      have heq : ((b.val-a.val : ℕ) : R) = 0 := by
        rw [Nat.cast_sub (Nat.le_of_lt hlt)]
        exact sub_eq_zero.mpr hab.symm
      exact hne heq
  | inr hlt =>
      have hpos : 0 < a.val - b.val := Nat.sub_pos_of_lt hlt
      have hle : a.val - b.val ≤ n := le_trans (Nat.sub_le _ _) (Nat.lt_succ_iff.mp a.isLt)
      have hne := cast_ne_zero_le_factorial (R:=R) n (a.val-b.val) hpos hle
      have heq : ((a.val-b.val : ℕ) : R) = 0 := by
        rw [Nat.cast_sub (Nat.le_of_lt hlt)]
        exact sub_eq_zero.mpr hab
      exact hne heq

lemma poly_eq_zero_of_eval_all_factorial {R : Type*} [Field R] (n : ℕ)
    [Invertible (n.factorial : R)] (p : Polynomial R)
    (hpdeg : p.natDegree ≤ n) (hp : ∀ r : R, p.eval r = 0) : p = 0 := by
  classical
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (factorial_cast_injective_fin (R:=R) n)
  · intro i; exact hp _
  · simpa using Nat.lt_succ_of_le hpdeg


-- Coefficients of a tensor pencil are polynomials of degree at most the
-- tensor degree.  Notice that we do not put a cardinality hypothesis in
-- this elementary lemma; the cardinality argument is a separate step.
lemma tensor_pencil_coord_polynomial {R M : Type*} [Field R]
    [AddCommGroup M] [Module R M]
    {d n : ℕ} (b : Module.Basis (Fin d) R M)
    (v u : Module.End R M) (x : (⨂[R]^ n M))
    (q : Fin n → Fin d) :
    ∃ p : Polynomial R, p.natDegree ≤ n ∧
      (∀ a : R,
        p.eval a =
          ((Basis.piTensorProduct (fun _ : Fin n => b)).repr
            ((PiTensorProduct.map (fun _ : Fin n => v + a • u)) x)) q) ∧
      p.coeff n =
          ((Basis.piTensorProduct (fun _ : Fin n => b)).repr
            ((PiTensorProduct.map (fun _ : Fin n => u)) x)) q := by
  classical
  let B := (Basis.piTensorProduct (fun _ : Fin n => b))
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      -- On a pure tensor the coordinate is a product of n linear
      -- polynomials.
      let w : Fin n → Polynomial R := fun i =>
        Polynomial.C ((b.repr (v (f i))) (q i)) +
          Polynomial.C ((b.repr (u (f i))) (q i)) * Polynomial.X
      refine ⟨Polynomial.C r * (∏ i : Fin n, w i), ?_, ?_, ?_⟩
      · calc
          (Polynomial.C r * (∏ i : Fin n, w i)).natDegree
              ≤ (Polynomial.C r).natDegree
                    + (∏ i : Fin n, w i).natDegree := Polynomial.natDegree_mul_le
          _ ≤ 0 + (∑ i : Fin n, (w i).natDegree) := by
                rw [Polynomial.natDegree_C]
                exact Nat.add_le_add_left
                  (Polynomial.natDegree_prod_le (Finset.univ) w) _
          _ ≤ 0 + (∑ _i : Fin n, 1) := by
                refine Nat.add_le_add_left ?_ _
                exact Finset.sum_le_sum (fun i hi => by
                  -- each of the factors is affine linear
                  calc
                    (w i).natDegree =
                        (Polynomial.C ((b.repr (v (f i))) (q i)) +
                          Polynomial.C ((b.repr (u (f i))) (q i)) * Polynomial.X).natDegree := rfl
                    _ ≤ max
                          (Polynomial.C ((b.repr (v (f i))) (q i))).natDegree
                          (Polynomial.C ((b.repr (u (f i))) (q i)) * Polynomial.X).natDegree :=
                            Polynomial.natDegree_add_le _ _
                    _ ≤ 1 := by
                          have hlin :
                              (Polynomial.C ((b.repr (u (f i))) (q i)) * Polynomial.X).natDegree
                                ≤ (Polynomial.C ((b.repr (u (f i))) (q i))).natDegree +
                                    Polynomial.X.natDegree := Polynomial.natDegree_mul_le
                          rw [Polynomial.natDegree_C, Polynomial.natDegree_X] at hlin
                          have h0 :
                              (Polynomial.C ((b.repr (v (f i))) (q i))).natDegree = 0 :=
                            Polynomial.natDegree_C _
                          rw [h0]
                          -- We phrase the estimate solely in `Nat`, avoiding
                          -- a case distinction on a possible zero coefficient.
                          exact max_le (by decide) (by simpa using hlin))
          _ = n := by simp
      · intro a
        -- Evaluation and the tensor coordinate formula are both
        -- multiplicative on a pure tensor.
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
        -- rewrite the image as a pure tensor
        rw [LinearMap.map_smul, PiTensorProduct.map_tprod]
        rw [map_smul]
        change _ = r * (((Basis.piTensorProduct (fun _ : Fin n => b)).repr
            ((PiTensorProduct.tprod R) (fun i => (v + a • u) (f i)))) q)
        rw [Basis.piTensorProduct_repr_tprod_apply]
        -- coordinates of a sum of two maps are the two affine
        -- coordinates occurring in `w`
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        simp [w]
        rw [mul_comm]

      · -- The top coefficient is obtained by taking the linear term in
        -- every factor.  This version of the coefficient lemma works even
        -- when one of those linear terms vanishes.
        rw [Polynomial.coeff_C_mul]
        have hlin (i : Fin n) : (w i).natDegree ≤ 1 := by
          calc
            (w i).natDegree =
                (Polynomial.C ((b.repr (v (f i))) (q i)) +
                  Polynomial.C ((b.repr (u (f i))) (q i)) * Polynomial.X).natDegree := rfl
            _ ≤ max
                  (Polynomial.C ((b.repr (v (f i))) (q i))).natDegree
                  (Polynomial.C ((b.repr (u (f i))) (q i)) * Polynomial.X).natDegree :=
                    Polynomial.natDegree_add_le _ _
            _ ≤ 1 := by
              have hbound :
                  (Polynomial.C ((b.repr (u (f i))) (q i)) * Polynomial.X).natDegree
                    ≤ (Polynomial.C ((b.repr (u (f i))) (q i))).natDegree +
                        Polynomial.X.natDegree := Polynomial.natDegree_mul_le
              rw [Polynomial.natDegree_C, Polynomial.natDegree_X] at hbound
              have hz :
                  (Polynomial.C ((b.repr (v (f i))) (q i))).natDegree = 0 :=
                Polynomial.natDegree_C _
              rw [hz]
              exact max_le (by decide) (by simpa using hbound)
        -- the uniform bound form has coefficient at `card * 1`
        have hp := Polynomial.coeff_prod_of_natDegree_le
            (R:=R) (s:= (Finset.univ : Finset (Fin n))) w 1
            (by intro i hi; exact hlin i)
        simp at hp
        rw [hp]
        -- identify the right hand coefficient as another pure tensor
        rw [LinearMap.map_smul, PiTensorProduct.map_tprod]
        rw [map_smul]
        change r * (∏ i : Fin n, (w i).coeff 1) =
          r * (((Basis.piTensorProduct (fun _ : Fin n => b)).repr
            ((PiTensorProduct.tprod R) (fun i => u (f i)))) q)
        rw [Basis.piTensorProduct_repr_tprod_apply]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        simp [w, Polynomial.coeff_C_mul]
  | add x y hx hy =>
      rcases hx with ⟨p, hp, hpval, hpcoeff⟩
      rcases hy with ⟨t, ht, htval, htcoeff⟩
      refine ⟨p + t, ?_, ?_, ?_⟩
      · calc
          (p + t).natDegree ≤ max p.natDegree t.natDegree :=
            Polynomial.natDegree_add_le _ _
          _ ≤ n := max_le hp ht
      · intro a
        rw [Polynomial.eval_add, hpval a, htval a, map_add, map_add]
        rfl
      · rw [Polynomial.coeff_add, hpcoeff, htcoeff, map_add, map_add]
        rfl



-- The same polynomial construction can be followed by an arbitrary linear
-- functional.  This is useful for the right side of a commutator where a
-- fixed endomorphism is applied after the varying tensor map.
lemma tensor_pencil_linear_polynomial {R M : Type*} [Field R]
    [AddCommGroup M] [Module R M]
    {d n : ℕ} (b : Module.Basis (Fin d) R M)
    (v u : Module.End R M) (x : (⨂[R]^ n M))
    (L : (⨂[R]^ n M) →ₗ[R] R) :
    ∃ p : Polynomial R, p.natDegree ≤ n ∧
      (∀ a : R, p.eval a =
          L ((PiTensorProduct.map (fun _ : Fin n => v + a • u)) x)) ∧
      p.coeff n = L ((PiTensorProduct.map (fun _ : Fin n => u)) x) := by
  classical
  let B := (Basis.piTensorProduct (fun _ : Fin n => b))
  -- Fix all the coordinate polynomials at once.
  choose p hpdeg hpval hpcoeff using
    (fun i : (Fin n → Fin d) => tensor_pencil_coord_polynomial
      b v u x i)
  let term : (Fin n → Fin d) → Polynomial R := fun i =>
      Polynomial.C (L (B i)) * p i
  have hterm (i : (Fin n → Fin d)) : (term i).natDegree ≤ n := by
    calc
      (term i).natDegree ≤ (Polynomial.C (L (B i))).natDegree + (p i).natDegree :=
        Polynomial.natDegree_mul_le
      _ = (p i).natDegree := by rw [Polynomial.natDegree_C, Nat.zero_add]
      _ ≤ n := hpdeg i
  have hsum (s : Finset (Fin n → Fin d)) :
      (∑ i ∈ s, term i).natDegree ≤ n := by
    classical
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact le_trans (Polynomial.natDegree_add_le _ _)
        (max_le (hterm i) ih)
  have expand (y : (⨂[R]^ n M)) :
      L y = ∑ i : (Fin n → Fin d),
          ((B.repr y) i) * L (B i) := by
    calc
      L y = L (∑ i : (Fin n → Fin d), (B.repr y i) • B i) :=
        congrArg (fun z => L z) (B.sum_repr y).symm
      _ = ∑ i : (Fin n → Fin d), ((B.repr y) i) * L (B i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [map_smul]
        rfl
  refine ⟨∑ i : (Fin n → Fin d), term i, hsum Finset.univ, ?_, ?_⟩
  · intro a
    rw [Polynomial.eval_finset_sum]
    rw [expand]
    apply Finset.sum_congr rfl
    intro i hi
    change Polynomial.eval a (Polynomial.C (L (B i)) * p i) =
      ((B.repr ((PiTensorProduct.map (fun _ : Fin n => v + a • u)) x)) i) * L (B i)
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    have he := hpval i a
    change Polynomial.eval a (p i) =
      (B.repr ((PiTensorProduct.map (fun _ : Fin n => v + a • u)) x)) i at he
    rw [he, mul_comm]
  · -- Coefficients, just like evaluation, commute with finite sums.
    -- `map_sum` can be used since `coeff _ n` is an additive map.
    let c : Polynomial R →+ R :=
      { toFun := fun t => t.coeff n
        map_zero' := by simp
        map_add' := by intro a b; simp }
    change c (∑ i : (Fin n → Fin d), term i) = _
    rw [map_sum]
    rw [expand]
    apply Finset.sum_congr rfl
    intro i hi
    change (Polynomial.C (L (B i)) * p i).coeff n =
      ((B.repr ((PiTensorProduct.map (fun _ : Fin n => u)) x)) i) * L (B i)
    rw [Polynomial.coeff_C_mul]
    have he := hpcoeff i
    change (p i).coeff n =
      (B.repr ((PiTensorProduct.map (fun _ : Fin n => u)) x)) i at he
    rw [he, mul_comm]


/-- Interpolation step for a *pencil all of whose members are units*.
The leading coefficient of `(v+a u)^{⊗ n}` is `u^{⊗ n}`.  Since there
are more than `n` scalars under the factorial hypothesis, vanishing of all
commutators on the pencil implies commutation with that leading term.  The
important point here is that no assertion is made about a pencil having
exceptional (singular) members. -/
lemma tensor_commute_of_every_pencil_unit {R M : Type*} [Field R]
    [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (n : ℕ) [Invertible (n.factorial : R)]
    (T : Module.End R (⨂[R]^ n M))
    (H : ∀ g : (Module.End R M)ˣ,
      (PiTensorProduct.map (fun _ : Fin n => (g : Module.End R M))) * T =
        T * (PiTensorProduct.map (fun _ : Fin n => (g : Module.End R M))))
    (v u : Module.End R M)
    (hpencil : ∀ a : R, IsUnit (v + a • u)) :
    (PiTensorProduct.map (fun _ : Fin n => u)) * T =
       T * (PiTensorProduct.map (fun _ : Fin n => u)) := by
  classical
  let b := Module.finBasis R M
  let B := (Basis.piTensorProduct (fun _ : Fin n => b))
  apply LinearMap.ext
  intro x
  apply B.ext_elem
  intro q
  obtain ⟨pl, hpldeg, hplval, hplc⟩ :=
    tensor_pencil_coord_polynomial b v u (T x) q
  -- the right hand side is the coordinate functional after `T`
  let L : (⨂[R]^ n M) →ₗ[R] R :=
    (Finsupp.lapply q).comp ((B.repr).toLinearMap.comp T)
  obtain ⟨pr, hprdeg, hprval, hprc⟩ :=
    tensor_pencil_linear_polynomial b v u x L
  have hdeg : (pl - pr).natDegree ≤ n :=
    le_trans (Polynomial.natDegree_sub_le _ _) (max_le hpldeg hprdeg)
  have heval (a : R) : (pl - pr).eval a = 0 := by
    rw [Polynomial.eval_sub]
    rw [hplval a, hprval a]
    -- instantiate the hypothesis with the unit belonging to this pencil
    rcases hpencil a with ⟨ga, hga⟩
    have hcomm := H ga
    have hpoint := DFunLike.congr_fun hcomm x
    have hval : (ga : Module.End R M) = v + a • u := hga
    rw [hval] at hpoint
    have hcoord := congrArg (fun y : (⨂[R]^ n M) => B.repr y q) hpoint
    -- `L` was just this coordinate composed with `T`
    change ((B.repr
      ((PiTensorProduct.map (fun _ : Fin n => v + a • u)) (T x))) q) -
        L ((PiTensorProduct.map (fun _ : Fin n => v + a • u)) x) = 0
    apply sub_eq_zero.mpr
    change ((B.repr
      ((PiTensorProduct.map (fun _ : Fin n => v + a • u)) (T x))) q) =
        L ((PiTensorProduct.map (fun _ : Fin n => v + a • u)) x)
    -- the two readings of a product of endomorphisms
    change (B.repr
      ((PiTensorProduct.map (fun _ : Fin n => v + a • u)) (T x)) q) =
        (B.repr (T ((PiTensorProduct.map
          (fun _ : Fin n => v + a • u)) x)) q)
    simpa [Module.End.mul_apply] using hcoord
  have hzero : pl - pr = 0 :=
    poly_eq_zero_of_eval_all_factorial (R:=R) n (pl - pr) hdeg heval
  have hc := congrArg (fun t : Polynomial R => t.coeff n) hzero
  rw [Polynomial.coeff_sub, hplc, hprc] at hc
  -- read the top coefficient.  `L` is a coordinate functional.
  change (B.repr ((PiTensorProduct.map (fun _ : Fin n => u)) (T x))) q =
    (B.repr (T ((PiTensorProduct.map (fun _ : Fin n => u)) x))) q
  change ((B.repr ((PiTensorProduct.map (fun _ : Fin n => u)) (T x))) q) -
    (B.repr (T ((PiTensorProduct.map (fun _ : Fin n => u)) x)) q) = 0 at hc
  exact sub_eq_zero.mp hc


-- A large useful family of pencils have no singular members: multiply a
-- unit by `1 + a w` with `w` nilpotent.
lemma tensor_commute_unit_mul_nilpotent {R M : Type*} [Field R]
    [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (n : ℕ) [Invertible (n.factorial : R)]
    (T : Module.End R (⨂[R]^ n M))
    (H : ∀ g : (Module.End R M)ˣ,
      (PiTensorProduct.map (fun _ : Fin n => (g : Module.End R M))) * T =
        T * (PiTensorProduct.map (fun _ : Fin n => (g : Module.End R M))))
    (g : (Module.End R M)ˣ) (w : Module.End R M)
    (hw : IsNilpotent w) :
    (PiTensorProduct.map (fun _ : Fin n => (g : Module.End R M) * w)) * T =
       T * (PiTensorProduct.map (fun _ : Fin n => (g : Module.End R M) * w)) := by
  classical
  apply tensor_commute_of_every_pencil_unit n T H
    (g : Module.End R M) ((g : Module.End R M) * w)
  intro a
  have hu : IsUnit (1 + a • w) := (hw.smul a).isUnit_one_add
  have hv : IsUnit (g : Module.End R M) := Units.isUnit g
  have huv : IsUnit ((g : Module.End R M) * (1 + a • w)) := hv.mul hu
  -- scalar multiplication is central in the endomorphism algebra
  convert huv using 1 <;>
    simp [mul_add, Algebra.mul_smul_comm]


lemma tensor_commute_of_unit_or_unit_mul_nilpotent {R M : Type*} [Field R]
    [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (n : ℕ) [Invertible (n.factorial : R)]
    (T : Module.End R (⨂[R]^ n M))
    (H : ∀ g : (Module.End R M)ˣ,
      (PiTensorProduct.map (fun _ : Fin n => (g : Module.End R M))) * T =
        T * (PiTensorProduct.map (fun _ : Fin n => (g : Module.End R M))))
    (hdecomp : ∀ u : Module.End R M, IsUnit u ∨
      ∃ (g : (Module.End R M)ˣ) (w : Module.End R M),
        IsNilpotent w ∧ u = (g : Module.End R M) * w) :
    ∀ u : Module.End R M,
      (PiTensorProduct.map (fun _ : Fin n => u)) * T =
        T * (PiTensorProduct.map (fun _ : Fin n => u)) := by
  classical
  intro u
  rcases hdecomp u with hu | hu
  · convert H hu.unit using 2
    · ext x
      -- `unit` was chosen with this value in the ring
      have hv : (hu.unit : Module.End R M) = u := hu.unit_spec
      simp [hv]
    · ext x
      have hv : (hu.unit : Module.End R M) = u := hu.unit_spec
      simp [hv]
  · rcases hu with ⟨g, w, hw, rfl⟩
    exact tensor_commute_unit_mul_nilpotent n T H g w hw


-- Algebraic reduction: every singular endomorphism has the same kernel as a nilpotent shift.
lemma sw_unit_factor_of_ker_eq {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
 [FiniteDimensional R M] (u w : Module.End R M)
 (hk : LinearMap.ker w = LinearMap.ker u) :
 ∃ g : (Module.End R M)ˣ, u = (g : Module.End R M) * w := by
  classical
  let eu : (M ⧸ LinearMap.ker w) ≃ₗ[R] LinearMap.range u :=
    (Submodule.quotEquivOfEq (LinearMap.ker w) (LinearMap.ker u) hk).trans
      u.quotKerEquivRange
  let er : LinearMap.range w ≃ₗ[R] LinearMap.range u :=
    w.quotKerEquivRange.symm.trans eu
  choose Cw hCw using (LinearMap.range w).exists_isCompl
  choose Cu hCu using (LinearMap.range u).exists_isCompl
  have hdim : Module.finrank R Cw = Module.finrank R Cu := by
    have hw := Submodule.finrank_add_eq_of_isCompl hCw
    have hu := Submodule.finrank_add_eq_of_isCompl hCu
    have he := LinearEquiv.finrank_eq er
    omega
  let ec : Cw ≃ₗ[R] Cu :=
    Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hdim)
  let G : M ≃ₗ[R] M :=
    ((LinearMap.range w).prodEquivOfIsCompl Cw hCw).symm.trans
      ((er.prodCongr ec).trans
        ((LinearMap.range u).prodEquivOfIsCompl Cu hCu))
  let g : (Module.End R M)ˣ := LinearMap.GeneralLinearGroup.ofLinearEquiv G
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro x
  change u x = G (w x)
  let wx : LinearMap.range w := ⟨w x, ⟨x, rfl⟩⟩
  let ux : LinearMap.range u := ⟨u x, ⟨x, rfl⟩⟩
  have her : er wx = ux := by
    -- the quotient calculation
    change eu (w.quotKerEquivRange.symm wx) = ux
    have hmemw : w x ∈ LinearMap.range w := ⟨x, rfl⟩
    have hwx : wx = (⟨w x, hmemw⟩ : LinearMap.range w) := rfl
    rw [hwx, LinearMap.quotKerEquivRange_symm_apply_image w x hmemw]
    -- identify eu on the common quotient
    change eu ((LinearMap.ker w).mkQ x) = ux
    -- prove by reducing to equality in M
    apply Subtype.ext
    -- kernel cast inside eu
    dsimp [eu]
    -- quotient application lemma
    -- simplification used quotient formula
  have hsplit :
      ((LinearMap.range w).prodEquivOfIsCompl Cw hCw).symm (w x) = (wx, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left _ _ _ wx
  change u x =
    ((LinearMap.range u).prodEquivOfIsCompl Cu hCu)
      ((er.prodCongr ec)
        (((LinearMap.range w).prodEquivOfIsCompl Cw hCw).symm (w x)))
  rw [hsplit]
  -- evaluate on the product
  change u x =
    ((LinearMap.range u).prodEquivOfIsCompl Cu hCu)
      (er wx, ec 0)
  rw [her]
  -- complement is zero
  rw [map_zero]
  have hh := Submodule.coe_prodEquivOfIsCompl'
      (LinearMap.range u) Cu hCu (ux, (0 : Cu))
  have hh' : ((LinearMap.range u).prodEquivOfIsCompl Cu hCu) (ux, (0:Cu))
      = (ux : M) := by
    simpa using hh
  exact hh'.symm
lemma sw_nilpotent_for_submodule {R M : Type*} [Field R]
 [AddCommGroup M] [Module R M] [FiniteDimensional R M]
 (K : Submodule R M) (hpos : 0 < Module.finrank R K) :
 ∃ w : Module.End R M, IsNilpotent w ∧ LinearMap.ker w = K := by
  classical
  choose C hC using K.exists_isCompl
  let bk := Module.finBasis R K
  let bc := Module.finBasis R C
  let m := Module.finrank R K
  let r := Module.finrank R C
  have hm : 0 < m := hpos
  let i0 : Fin m := ⟨0, hm⟩
  by_cases hr0 : r = 0
  · -- complement zero
    have hCbot : C = ⊥ := (Submodule.finrank_eq_zero).1 hr0
    have hKtop : K = ⊤ := by
      subst C
      simpa using hC.sup_eq_top
    refine ⟨0, ?_, ?_⟩
    · refine ⟨1, ?_⟩
      simp
    · simp [hKtop]
  · have hr : 0 < r := Nat.pos_of_ne_zero hr0
    let c0 : Fin r := ⟨0, hr⟩
    let predIndex (j : Fin r) (_h : j.val ≠ 0) : Fin r :=
      ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
    let succIndex (j : Fin r) (h : j.val + 1 < r) : Fin r :=
      ⟨j.val + 1, h⟩
    let t : C →ₗ[R] M :=
      (bc.constr R) (fun j => if h:j.val = 0
         then ((bk i0 : K) : M)
         else ((bc (predIndex j h) : C) : M))
    let φ : K →ₗ[R] C :=
      (bk.constr R) (fun i => if h:i = i0 then bc c0 else 0)
    let ψ : C →ₗ[R] C :=
      (bc.constr R) (fun j => if h : j.val + 1 < r
         then bc (succIndex j h) else 0)
    let s : M →ₗ[R] C := LinearMap.ofIsCompl hC φ ψ
    have ht_basis_zero (j : Fin r) (hj : j.val = 0) :
        t (bc j) = ((bk i0 : K) : M) := by
      change ((bc.constr R) _) (bc j) = _
      rw [Module.Basis.constr_basis]
      simp [hj]
    have ht_basis_succ (j : Fin r) (hj : j.val ≠ 0) :
        t (bc j) = ((bc (predIndex j hj) : C) : M) := by
      change ((bc.constr R) _) (bc j) = _
      rw [Module.Basis.constr_basis]
      simp [hj]
    have hs_t_basis (j : Fin r) : s (t (bc j)) = bc j := by
      by_cases hj : j.val = 0
      · have hjfin : j = c0 := Fin.ext hj
        subst j
        rw [ht_basis_zero c0 rfl]
        -- s on element of K
        change s ((bk i0 : K) : M) = bc c0
        rw [LinearMap.ofIsCompl_apply_left hC]
        simp [φ]
      · rw [ht_basis_succ j hj]
        change s ((bc (predIndex j hj) : C) : M) = bc j
        rw [LinearMap.ofIsCompl_apply_right hC]
        -- ψ shift
        have hineq : (predIndex j hj).val + 1 < r := by
          dsimp [predIndex]
          omega
        -- prove indices
        have hind : succIndex (predIndex j hj) hineq = j := by
          apply Fin.ext
          dsimp [succIndex, predIndex]
          omega
        -- simp
        change ψ (bc (predIndex j hj)) = bc j
        change ((bc.constr R) _) (bc (predIndex j hj)) = _
        rw [Module.Basis.constr_basis]
        simp [hineq, hind]
    have hinj : Function.Injective t := by
      intro a b hab
      have ha := congrArg (fun x => s x) hab
      have ha' : (s.comp t) a = (s.comp t) b := ha
      -- show comp=id via basis
      have hleft : s.comp t = LinearMap.id := by
        apply bc.ext
        intro j
        simpa using hs_t_basis j
      simpa [hleft] using ha'
    let w : Module.End R M :=
      LinearMap.ofIsCompl hC (0 : K →ₗ[R] M) t
    have wk (i : Fin m) : w ((bk i : K) : M) = 0 := by
      simp [w, LinearMap.ofIsCompl_apply_left hC]
    have wc0 : ∀ j : Fin r, j.val = 0 ->
        w ((bc j : C) : M) = ((bk i0 : K) : M) := by
      intro j hj
      -- apply right
      rw [show w ((bc j : C):M) = t (bc j) from
        LinearMap.ofIsCompl_apply_right hC _]
      exact ht_basis_zero j hj
    have wcs : ∀ (j : Fin r) (hj : j.val ≠ 0),
        w ((bc j : C) : M) = ((bc (predIndex j hj) : C) : M) := by
      intro j hj
      rw [show w ((bc j : C):M) = t (bc j) from
        LinearMap.ofIsCompl_apply_right hC _]
      exact ht_basis_succ j hj
    have hker : LinearMap.ker w = K := by
      apply le_antisymm
      · intro x hx
        have hx0 : w x = 0 := hx
        have hy : ((K.prodEquivOfIsCompl C hC).symm x).2 = 0 := by
          -- use injectivity of t
          apply hinj
          have hwrepr : w x = t (((K.prodEquivOfIsCompl C hC).symm x).2) := by
            -- decompose
            let y := (K.prodEquivOfIsCompl C hC).symm x
            have he : x = ( (y.1 : M) + (y.2 : M)) := by
              have hyapp := (K.prodEquivOfIsCompl C hC).apply_symm_apply x
              -- expansion formula
              calc
                x = (K.prodEquivOfIsCompl C hC) y := hyapp.symm
                _ = (y.1 : M) + (y.2 : M) :=
                  Submodule.coe_prodEquivOfIsCompl' K C hC y
            calc
              w x = w ((y.1 : M) + (y.2 : M)) := congrArg w he
              _ = w (y.1 : M) + w (y.2 : M) := by rw [map_add]
              _ = 0 + t y.2 := by
                rw [show w (y.1 : M) = 0 from by
                  simpa [w] using (LinearMap.ofIsCompl_apply_left hC (φ:= (0:K→ₗ[R] M)) (ψ:=t) y.1)]
                rw [show w (y.2 : M) = t y.2 from
                  LinearMap.ofIsCompl_apply_right hC y.2]
              _ = t y.2 := zero_add _
              _ = t (((K.prodEquivOfIsCompl C hC).symm x).2) := by rfl
          -- t v = t 0
          have hz : t (((K.prodEquivOfIsCompl C hC).symm x).2) = 0 := by
            rw [← hwrepr, hx0]
          simpa using hz
        exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero K C hC).1 hy
      · intro x hx
        have hh := LinearMap.ofIsCompl_apply_left hC
          (φ:=(0:K→ₗ[R] M)) (ψ:=t) (⟨x, hx⟩ : K)
        change w x = 0
        simpa [w] using hh
    have hkillC : ∀ j : Fin r,
        (w ^ (j.val + 2)) ((bc j : C) : M) = 0 := by
      have aux : ∀ a : ℕ, ∀ j : Fin r, j.val = a →
          (w ^ (j.val+2)) ((bc j : C) : M) = 0 := by
        intro a
        induction a using Nat.strong_induction_on with
        | h a ih =>
          intro j hjv
          by_cases ha : a = 0
          · have hj0 : j.val = 0 := hjv.trans ha
            -- chain begins in K
            -- direct calculation of the square
            change (w^ (j.val+2)) ((bc j : C) : M) = 0
            rw [show j.val + 2 = 1 + 1 by omega, pow_succ,
                Module.End.mul_apply]
            simp [wc0 j hj0, wk i0, Module.End.mul_apply]
          · have hjne : j.val ≠ 0 := by omega
            let jp : Fin r := predIndex j hjne
            have hp : jp.val = a - 1 := by
              dsimp [jp, predIndex]
              omega
            have hlt : a - 1 < a := by omega
            have ihp := ih (a-1) hlt jp hp
            calc
              (w ^ (j.val + 2)) ((bc j : C) : M) =
                  (w ^ (j.val + 1)) (w ((bc j : C) : M)) := by
                    rw [show j.val + 2 = (j.val + 1) + 1 by omega,
                      pow_succ, Module.End.mul_apply]
              _ = (w ^ (j.val + 1)) ((bc jp : C) : M) := by
                    rw [wcs j hjne]
              _ = 0 := by
                    have heq : jp.val + 2 = j.val + 1 := by omega
                    rw [← heq]
                    exact ihp
      intro j
      exact aux j.val j rfl
    have hzeroC (j : Fin r) :
        (w ^ (r+1)) ((bc j : C) : M) = 0 := by
      have hle : j.val + 2 ≤ r + 1 := by have := j.isLt; omega
      let d : ℕ := r + 1 - (j.val + 2)
      have hd : d + (j.val + 2) = r + 1 := by
        dsimp [d]
        omega
      calc
        (w ^ (r+1)) ((bc j : C) : M) =
            (w ^ (d + (j.val+2))) ((bc j : C) : M) := by rw [hd]
        _ = (w^d) ((w^(j.val+2)) ((bc j : C) : M)) := by
              rw [pow_add, Module.End.mul_apply]
        _ = 0 := by rw [hkillC j]; simp
    have hnil : IsNilpotent w := by
      refine ⟨r+1, ?_⟩
      have hmapK : (w^(r+1)).comp K.subtype = (0 : K →ₗ[R] M) := by
        apply bk.ext
        intro i
        change (w^(r+1)) ((bk i : K) : M) = (0 : K →ₗ[R] M) (bk i)
        rw [pow_succ, Module.End.mul_apply, wk i]
        simp
      have hmapC : (w^(r+1)).comp C.subtype = (0 : C →ₗ[R] M) := by
        apply bc.ext
        intro j
        change (w^(r+1)) ((bc j : C) : M) = (0 : C →ₗ[R] M) (bc j)
        simp [hzeroC]
      apply LinearMap.ext
      intro x
      let y := (K.prodEquivOfIsCompl C hC).symm x
      have he : x = ((y.1 : M) + (y.2 : M)) := by
        calc
          x = (K.prodEquivOfIsCompl C hC) y :=
            (K.prodEquivOfIsCompl C hC).apply_symm_apply x |>.symm
          _ = (y.1 : M) + (y.2 : M) :=
            Submodule.coe_prodEquivOfIsCompl' K C hC y
      change (w^(r+1)) x = (0 : Module.End R M) x
      rw [he, map_add]
      have h1 : (w^(r+1)) (y.1 : M) = 0 := by
        have hh := LinearMap.congr_fun hmapK y.1
        exact hh
      have h2 : (w^(r+1)) (y.2 : M) = 0 := by
        have hh := LinearMap.congr_fun hmapC y.2
        exact hh
      rw [h1, h2]
      simp
    exact ⟨w, hnil, hker⟩
lemma sw_end_unit_or_nilpotent {R M : Type*} [Field R]
 [AddCommGroup M] [Module R M] [FiniteDimensional R M] :
 ∀ u : Module.End R M, IsUnit u ∨
      ∃ (g : (Module.End R M)ˣ) (w : Module.End R M),
        IsNilpotent w ∧ u = (g : Module.End R M) * w := by
  classical
  intro u
  by_cases hu : IsUnit u
  · exact Or.inl hu
  right
  have hknot : LinearMap.ker u ≠ (⊥ : Submodule R M) := by
    intro hk
    have hi : Function.Injective u := (LinearMap.ker_eq_bot).1 hk
    have hs : Function.Surjective u := LinearMap.surjective_of_injective hi
    let e : M ≃ₗ[R] M := LinearEquiv.ofBijective u ⟨hi, hs⟩
    let gu : (Module.End R M)ˣ :=
      LinearMap.GeneralLinearGroup.ofLinearEquiv e
    have hval : (gu : Module.End R M) = u := by rfl
    exact hu (hval ▸ (Units.isUnit gu))
  have hp : 0 < Module.finrank R (LinearMap.ker u) := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hknot ((Submodule.finrank_eq_zero).1 hz)
  obtain ⟨w, hwn, hwk⟩ := sw_nilpotent_for_submodule (LinearMap.ker u) hp
  obtain ⟨g, hg⟩ := sw_unit_factor_of_ker_eq u w hwk
  exact ⟨g, w, hwn, hg⟩


/-- In every dimension the first elementary restriction on a coefficient of
an equivariant endomorphism is a weight restriction.  The polynomial proof
below works also over the small finite fields allowed by the hypothesis. -/
lemma tensor_coefficient_same_count {R M : Type*} [Field R]
    [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (n : ℕ) [Invertible (n.factorial : R)]
    (T : Module.End R (⨂[R]^ n M))
    (hT : ∀ u : Module.End R M,
      (PiTensorProduct.map (fun _ : Fin n => u)) * T =
        T * (PiTensorProduct.map (fun _ : Fin n => u))) :
    let b := Module.finBasis R M
    let B := Basis.piTensorProduct (fun _ : Fin n => b)
    ∀ p q : Fin n → Fin (Module.finrank R M),
      (B.repr (T (B p)) q) ≠ 0 →
      ∀ j : Fin (Module.finrank R M),
        (Finset.univ.filter (fun i : Fin n => p i = j)).card =
          (Finset.univ.filter (fun i : Fin n => q i = j)).card := by
  classical
  dsimp
  let b := Module.finBasis R M
  let B := Basis.piTensorProduct (fun _ : Fin n => b)
  intro p q hp j
  let D (a : R) : Module.End R M :=
    (b.constr R) (fun l => if l = j then a • b l else b l)
  have D_basis (a : R) (l : Fin (Module.finrank R M)) :
      D a (b l) = (if l = j then a else 1) • b l := by
    change ((b.constr R) _) (b l) = _
    rw [Module.Basis.constr_basis]
    by_cases h : l = j
    · simp [h]
    · simp [h]
  have prod_count (a : R) (s : Fin n → Fin (Module.finrank R M)) :
      (∏ i : Fin n, (if s i = j then a else 1)) =
        a ^ (Finset.univ.filter (fun i : Fin n => s i = j)).card := by
    classical
    simp [Finset.prod_ite]
  have map_word (a : R) (s : Fin n → Fin (Module.finrank R M)) :
      (PiTensorProduct.map (fun _ : Fin n => D a)) (B s) =
        (a ^ (Finset.univ.filter (fun i : Fin n => s i = j)).card) • B s := by
    rw [show B s = (PiTensorProduct.tprod R) (fun i : Fin n => b (s i)) from
      Basis.piTensorProduct_apply _ _]
    rw [PiTensorProduct.map_tprod]
    simp_rw [D_basis]
    rw [MultilinearMap.map_smul_univ]
    rw [prod_count]
  have point (a : R) :
      a ^ (Finset.univ.filter (fun i : Fin n => q i = j)).card =
        a ^ (Finset.univ.filter (fun i : Fin n => p i = j)).card := by
    have h := DFunLike.congr_fun (hT (D a)) (B p)
    change (PiTensorProduct.map (fun _ : Fin n => D a)) (T (B p)) =
      T ((PiTensorProduct.map (fun _ : Fin n => D a)) (B p)) at h
    have hcoord := congrArg (fun y : (⨂[R]^ n M) => B.repr y q) h
    have diag_coord (x : (⨂[R]^ n M)) :
        (B.repr ((PiTensorProduct.map (fun _ : Fin n => D a)) x) q) =
          (a ^ (Finset.univ.filter (fun i : Fin n => q i = j)).card) *
            (B.repr x q) := by
      have hx : (∑ s, (B.repr x s) • B s) = x := B.sum_repr x
      rw [← hx]
      simp only [map_sum, LinearMap.map_smul]
      let ev : ((Fin n → Fin (Module.finrank R M)) →₀ R) →+ R :=
        { toFun := fun z => z q, map_zero' := rfl,
          map_add' := by intros; rfl }
      change ev (∑ s, B.repr ((B.repr x s) •
        (PiTensorProduct.map (fun _ : Fin n => D a)) (B s))) = _
      rw [map_sum]
      classical
      rw [Finset.sum_eq_single q]
      · simp [map_word, mul_comm]
        change (((fun₀ | q => a ^ (Finset.univ.filter (fun i : Fin n => q i = j)).card) *
          (fun₀ | q => (B.repr x) q)) q) = _
        simp [Finsupp.single_apply]
      · intro s hs hne
        rw [map_word]
        change (B.repr ((B.repr x s) •
          ((a ^ (Finset.univ.filter (fun i : Fin n => s i = j)).card) • B s)) q) = 0
        simp [map_smul, Module.Basis.repr_self_apply, hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    rw [diag_coord (T (B p)), map_word] at hcoord
    change
      (a ^ (Finset.univ.filter (fun i : Fin n => q i = j)).card) *
          (B.repr (T (B p)) q) =
        (B.repr (T
          ((a ^ (Finset.univ.filter (fun i : Fin n => p i = j)).card) •
            B p)) q) at hcoord
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hcoord
    change
      (a ^ (Finset.univ.filter (fun i : Fin n => q i = j)).card) *
          (B.repr (T (B p)) q) =
        (a ^ (Finset.univ.filter (fun i : Fin n => p i = j)).card) *
          (B.repr (T (B p)) q) at hcoord
    exact (mul_right_cancel₀ hp hcoord)
  let A : ℕ := (Finset.univ.filter (fun i : Fin n => p i = j)).card
  let C : ℕ := (Finset.univ.filter (fun i : Fin n => q i = j)).card
  have hA : A ≤ n := by
    dsimp [A]
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  have hC : C ≤ n := by
    dsimp [C]
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  let poly : Polynomial R := Polynomial.X ^ C - Polynomial.X ^ A
  have hdeg : poly.natDegree ≤ n := by
    dsimp [poly]
    exact le_trans (Polynomial.natDegree_sub_le _ _)
      (max_le (by simpa using hC) (by simpa using hA))
  have heval (a : R) : poly.eval a = 0 := by
    dsimp [poly]
    simp [Polynomial.eval_sub, Polynomial.eval_pow, point a, A, C]
  have hz := poly_eq_zero_of_eval_all_factorial (R:=R) n poly hdeg heval
  have hpow : (Polynomial.X : Polynomial R) ^ C = Polynomial.X ^ A :=
    sub_eq_zero.mp hz
  have hdegpow := congrArg Polynomial.natDegree hpow
  simpa [Polynomial.natDegree_X_pow] using hdegpow.symm

/-- Maschke's averaging, in the small form used for a double-commutant
argument.  The representation is a monoid hom into endomorphisms; since the
source is a group the inverse used in the average is just `ρ (g⁻¹)` and no
choice of inverse matrix is involved. -/
lemma invariant_projection_of_finite_group
    {R W G : Type*} [Field R] [AddCommGroup W] [Module R W]
    [Group G] [Fintype G]
    (hcard : (Fintype.card G : R) ≠ 0)
    (ρ : G →* Module.End R W)
    (N : Submodule R W)
    (hstable : ∀ (g : G) (x : W), x ∈ N → ρ g x ∈ N) :
    ∃ P : Module.End R W,
        (∀ x : W, x ∈ N → P x = x) ∧
        (∀ x : W, P x ∈ N) ∧
        (∀ g : G, ρ g * P = P * ρ g) := by
  classical
  choose Q hQ using N.exists_isCompl
  let P0 : Module.End R W := N.projection Q hQ
  have P0_fix (x : W) (hx : x ∈ N) : P0 x = x := by
    exact Submodule.projection_apply_of_mem_left hQ hx
  have P0_mem (x : W) : P0 x ∈ N := by
    exact Submodule.projection_apply_mem hQ x
  let C (g : G) : Module.End R W := ρ g * P0 * ρ (g⁻¹)
  let P : Module.End R W := ( (Fintype.card G : R)⁻¹) • (∑ g : G, C g)
  have rho_mul (g h : G) : ρ (g*h) = ρ g * ρ h := ρ.map_mul _ _
  have C_fix (g : G) (x : W) (hx : x ∈ N) : C g x = x := by
    have h1 : ρ (g⁻¹) x ∈ N := hstable _ _ hx
    dsimp [C]
    rw [P0_fix _ h1]
    -- inverse in the source group
    rw [← Module.End.mul_apply, ← rho_mul]
    simp
  have C_mem (g : G) (x : W) : C g x ∈ N := by
    dsimp [C]
    exact hstable _ _ (P0_mem _)
  have P_fix (x : W) (hx : x ∈ N) : P x = x := by
    change ((Fintype.card G : R)⁻¹) •
      ((∑ g : G, C g) x) = x
    rw [LinearMap.sum_apply]
    simp_rw [C_fix _ _ hx]
    -- `sum_const` is an `nsmul`; over a vector space it is the cast.
    have hc : (∑ _g : G, x) = (Fintype.card G) • x := by
      simp
    rw [hc, ← Nat.cast_smul_eq_nsmul R, smul_smul]
    simp [hcard]
  have P_mem (x : W) : P x ∈ N := by
    change ((Fintype.card G : R)⁻¹) •
      ((∑ g : G, C g) x) ∈ N
    rw [LinearMap.sum_apply]
    refine N.smul_mem _ ?_
    exact N.sum_mem (fun g hg => C_mem g x)
  have C_shift (g e : G) :
      ρ g * C e = C (g * e) * ρ g := by
    dsimp [C]
    calc
      ρ g * (ρ e * P0 * ρ (e⁻¹)) =
          ρ (g*e) * P0 * ρ (e⁻¹) := by
            simp [rho_mul, mul_assoc]
      _ = ρ (g*e) * P0 * (ρ ((g*e)⁻¹) * ρ g) := by
            have hid : (g*e)⁻¹ * g = e⁻¹ := by group
            rw [← rho_mul, hid]
      _ = (ρ (g*e) * P0 * ρ ((g*e)⁻¹)) * ρ g := by
            simp [mul_assoc]
  have sum_comm (g : G) :
      ρ g * (∑ e : G, C e) = (∑ e : G, C e) * ρ g := by
    classical
    rw [Finset.mul_sum, Finset.sum_mul]
    -- reindex the sum on the right by left multiplication by g
    -- the elementary identity is `C_shift`
    refine Finset.sum_bij (fun e he => g * e) ?_ ?_ ?_ ?_
    · intro e he; exact Finset.mem_univ _
    · intro a ha b hb hab
      exact mul_left_cancel hab
    · intro b hb
      refine ⟨g⁻¹ * b, Finset.mem_univ _, ?_⟩
      simp
    · intro e he
      exact C_shift g e
  refine ⟨P, P_fix, P_mem, ?_⟩
  intro g
  dsimp [P]
  -- a scalar commutes with multiplication in the endomorphism algebra
  simp only [mul_smul_comm, Algebra.smul_mul_assoc]
  congr 1
  exact sum_comm g


lemma tensor_mem_adjoin_of_all_maps_large {R M : Type*} [Field R]
 [AddCommGroup M] [Module R M] [FiniteDimensional R M]
 (n : ℕ) (hn : n ≤ Module.finrank R M)
 (T : Module.End R (⨂[R]^ n M))
 (hT : ∀ u : Module.End R M,
      (PiTensorProduct.map (fun _ : Fin n => u)) * T =
        T * (PiTensorProduct.map (fun _ : Fin n => u))) :
 T ∈ Algebra.adjoin R (Set.range (symAction R M n)) := by
  classical
  let b := Module.finBasis R M
  let B := Basis.piTensorProduct (fun _ : Fin n => b)
  let p0 : Fin n → Fin (Module.finrank R M) := Fin.castLE hn
  let a : Equiv.Perm (Fin n) → R := fun e =>
    B.repr (T (B p0)) (fun i => Fin.castLE hn (e i))
  let U : Equiv.Perm (Fin n) → Module.End R (⨂[R]^ n M) :=
    fun e => symAction R M n e.symm
  let W : Module.End R (⨂[R]^ n M) := ∑ e : Equiv.Perm (Fin n), a e • U e
  have hU (e : Equiv.Perm (Fin n)) (p : Fin n → Fin (Module.finrank R M)) :
      U e (B p) = B (fun i => p (e i)) := by
    -- reindex formula
    change (PiTensorProduct.reindex R (fun _ : Fin n => M) e.symm).toLinearMap
      (B p) = B (fun i => p (e i))
    simp [B, Basis.piTensorProduct_apply, PiTensorProduct.reindex_tprod]
  have hinjfun : Function.Injective
      (fun e : Equiv.Perm (Fin n) => (fun i : Fin n => Fin.castLE hn (e i))) := by
    intro e f h
    apply Equiv.ext
    intro i
    exact Fin.castLE_injective hn (congrFun h i)
  have hbase : W (B p0) = T (B p0) := by
    apply B.ext_elem
    intro q
    rw [show W = ∑ e : Equiv.Perm (Fin n), a e • U e from rfl]
    rw [LinearMap.sum_apply]
    rw [map_sum]
    let ev : ((Fin n → Fin (Module.finrank R M)) →₀ R) →+ R :=
      { toFun := fun t => t q, map_zero' := rfl,
        map_add' := by intros; rfl }
    change ev (∑ x, B.repr ((a x • U x) (B p0))) = _
    rw [map_sum]
    simp only [LinearMap.smul_apply, map_smul, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    change (∑ x, a x * ((B.repr (U x (B p0))) q)) = _
    have hcoef (e : Equiv.Perm (Fin n)) :
        (B.repr (U e (B p0))) q =
          if (fun i : Fin n => Fin.castLE hn (e i)) = q then 1 else 0 := by
      rw [hU]
      exact Module.Basis.repr_self_apply _ _ _
    simp_rw [hcoef]
    -- coefficients of T not on the orbit vanish
    by_cases hq0 : B.repr (T (B p0)) q = 0
    · rw [hq0]
      apply Finset.sum_eq_zero
      intro e he
      split_ifs with heq
      · -- if an orbit coefficient nonzero then target is that coefficient, contradiction
        have ae0 : a e = 0 := by
          dsimp [a]
          rw [heq]
          exact hq0
        simp [ae0]
      · simp
    · obtain ⟨e, he⟩ :=
          tensor_distinct_coefficient_of_all_maps (R:=R) (M:=M)
            n hn T hT q hq0
      have heq : (fun i : Fin n => Fin.castLE hn (e i)) = q := by
        funext i; symm; exact he i
      classical
      -- only this permutation contributes
      classical
      have hmem : e ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))) := Finset.mem_univ _
      rw [Finset.sum_eq_single e]
      · simp [heq, a]
      · intro b' hb' hne
        have hneq : (fun i : Fin n => Fin.castLE hn (b' i)) ≠ q := by
          intro hh
          have : b' = e := hinjfun (hh.trans heq.symm)
          exact hne this
        simp [hneq]
      · intro hnot
        exact False.elim (hnot hmem)
  -- send the distinguished tuple to an arbitrary tuple
  have hu_for (p : Fin n → Fin (Module.finrank R M)) :
      ∃ u : Module.End R M,
        (PiTensorProduct.map (fun _ : Fin n => u)) (B p0) = B p := by
    let u : Module.End R M := (b.constr R) (fun j =>
      if h : ∃ i : Fin n, Fin.castLE hn i = j
      then b (p (Classical.choose h)) else 0)
    refine ⟨u, ?_⟩
    rw [show B p0 = (PiTensorProduct.tprod R) (fun i => b (p0 i)) from
      Basis.piTensorProduct_apply _ _, PiTensorProduct.map_tprod,
      Basis.piTensorProduct_apply]
    congr 1
    funext i
    change u (b (p0 i)) = b (p i)
    change ((b.constr R) _) (b (p0 i)) = _
    rw [Module.Basis.constr_basis]
    have hi : ∃ t : Fin n, Fin.castLE hn t = p0 i := ⟨i, rfl⟩
    simp only [dif_pos hi]
    have he : Classical.choose hi = i :=
      Fin.castLE_injective hn (Classical.choose_spec hi)
    rw [he]
  have hcommW (u : Module.End R M) :
      (PiTensorProduct.map (fun _ : Fin n => u)) * W =
        W * (PiTensorProduct.map (fun _ : Fin n => u)) := by
    dsimp [W]
    -- multiplication distributes over the finite sum and scalars
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Algebra.smul_mul_assoc]
    apply Finset.sum_congr rfl
    intro e he
    congr 1
    have hc := tensor_diag_sym_commute (R:=R) (M:=M) n u e.symm
    exact hc
  have hTW : T = W := by
    apply B.ext
    intro p
    obtain ⟨u, hu⟩ := hu_for p
    have ht := DFunLike.congr_fun (hT u) (B p0)
    have hw := DFunLike.congr_fun (hcommW u) (B p0)
    change (PiTensorProduct.map (fun _ : Fin n => u)) (T (B p0)) =
      T ((PiTensorProduct.map (fun _ : Fin n => u)) (B p0)) at ht
    change (PiTensorProduct.map (fun _ : Fin n => u)) (W (B p0)) =
      W ((PiTensorProduct.map (fun _ : Fin n => u)) (B p0)) at hw
    rw [hu] at ht hw
    rw [← hbase] at ht
    rw [hw] at ht
    exact ht.symm
  rw [hTW]
  dsimp [W]
  -- closure under sums and scalar multiples
  apply (Algebra.adjoin R (Set.range (symAction R M n))).sum_mem
  intro e he
  exact (Algebra.adjoin R (Set.range (symAction R M n))).smul_mem
    ((Algebra.subset_adjoin) ⟨e.symm, rfl⟩) (a e)



-- Polarization in slots: commuting with all diagonal tensor maps implies
-- commuting with every *symmetrized* tensor of a tuple of endomorphisms.
lemma tensor_symmetrized_mem_commutant {R M : Type*} [Field R]
    [AddCommGroup M] [Module R M] (n : ℕ)
    (T : Module.End R (⨂[R]^ n M))
    (hT : ∀ u : Module.End R M,
      (PiTensorProduct.map (fun _ : Fin n => u)) * T =
        T * (PiTensorProduct.map (fun _ : Fin n => u)))
    (f : Fin n → Module.End R M) :
    (∑ e : Equiv.Perm (Fin n),
        PiTensorProduct.map (fun i : Fin n => f (e i))) * T =
      T * (∑ e : Equiv.Perm (Fin n),
        PiTensorProduct.map (fun i : Fin n => f (e i))) := by
  classical
  let C : Submodule R (Module.End R (⨂[R]^ n M)) :=
    { carrier := {A | A * T = T * A}
      zero_mem' := by simp
      add_mem' := by
        intro A B hA hB
        change (A + B) * T = T * (A + B)
        simpa [add_mul, mul_add] using congrArg₂ (· + ·) hA hB
      smul_mem' := by
        intro a A hA
        change (a • A) * T = T * (a • A)
        simpa [mul_smul_comm, Algebra.smul_mul_assoc] using congrArg (fun u => a • u) hA }
  let imageOf (r : Fin n → Fin n) : Finset (Fin n) :=
    Finset.image r Finset.univ
  let Ψ (r : Fin n → Fin n) : Module.End R (⨂[R]^ n M) :=
    PiTensorProduct.map (fun i : Fin n => f (r i))
  let exactPart (s : Finset (Fin n)) : Module.End R (⨂[R]^ n M) :=
    ∑ r ∈ (Finset.univ.filter (fun r : Fin n → Fin n => imageOf r = s)), Ψ r
  let upTo (s : Finset (Fin n)) : Module.End R (⨂[R]^ n M) :=
    ∑ r ∈ (Finset.univ.filter (fun r : Fin n → Fin n => imageOf r ⊆ s)), Ψ r
  have upTo_diag (s : Finset (Fin n)) :
      upTo s = PiTensorProduct.map (fun _ : Fin n =>
        ∑ i ∈ s, f i) := by
    -- just multilinearity of a pure tensor
    dsimp [upTo, Ψ, imageOf]
    ext x
    simp only [LinearMap.coe_compMultilinearMap, Function.comp_apply]
    simp only [LinearMap.sum_apply, PiTensorProduct.map_tprod]
    have hfin :
        (Finset.univ.filter (fun r : Fin n → Fin n =>
          Finset.image r Finset.univ ⊆ s)) =
          Fintype.piFinset (fun _ : Fin n => s) := by
      ext r
      simp [Finset.image_subset_iff, Fintype.mem_piFinset]
    rw [hfin]
    symm
    simpa using
      (MultilinearMap.map_sum_finset (PiTensorProduct.tprod R)
        (fun (j : Fin n) (i : Fin n) => f i (x j))
        (fun _ : Fin n => s))
  have upTo_mem (s : Finset (Fin n)) : upTo s ∈ C := by
    rw [upTo_diag]
    change (PiTensorProduct.map (fun _ : Fin n => ∑ i ∈ s, f i)) * T = _
    exact hT _
  have decomp (s : Finset (Fin n)) :
      upTo s =
        ∑ t ∈ (Finset.univ.filter (fun t : Finset (Fin n) => t ⊆ s)),
          exactPart t := by
    classical
    let SF : Finset (Fin n → Fin n) :=
      Finset.univ.filter (fun r : Fin n → Fin n => imageOf r ⊆ s)
    have fib := Finset.sum_fiberwise SF imageOf Ψ
    have inner (t : Finset (Fin n)) :
        (∑ r ∈ SF with imageOf r = t, Ψ r) =
          if t ⊆ s then exactPart t else 0 := by
      by_cases ht : t ⊆ s
      · rw [if_pos ht]
        dsimp [exactPart]
        have heq : SF.filter (fun r : Fin n → Fin n => imageOf r = t) =
              Finset.univ.filter (fun r : Fin n → Fin n => imageOf r = t) := by
          ext r
          simp [SF]
          intro hEq
          simpa [hEq] using ht
        rw [heq]
      · rw [if_neg ht]
        apply Finset.sum_eq_zero
        intro r hr
        have hr' : r ∈ SF := (Finset.mem_filter.mp hr).1
        have hre : imageOf r = t := (Finset.mem_filter.mp hr).2
        have hs' : imageOf r ⊆ s := (Finset.mem_filter.mp hr').2
        exact False.elim (ht (hre ▸ hs'))
    have fib' :
        (∑ t : Finset (Fin n), if t ⊆ s then exactPart t else 0) = upTo s := by
      have fib0 :
          (∑ t : Finset (Fin n),
            ∑ r ∈ SF with imageOf r = t, Ψ r) = upTo s := by
        simpa [upTo, SF] using fib
      rw [← fib0]
      apply Finset.sum_congr rfl
      intro t ht
      exact inner t |>.symm
    -- express the sum with a filter
    rw [← fib']
    classical
    simp [Finset.sum_filter]
  have exact_mem : ∀ s : Finset (Fin n), exactPart s ∈ C := by
    intro s0
    have aux : ∀ m : ℕ, ∀ s : Finset (Fin n), s.card = m → exactPart s ∈ C := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro s hs
        let SS : Finset (Finset (Fin n)) :=
          Finset.univ.filter (fun t : Finset (Fin n) => t ⊆ s)
        have hsS : s ∈ SS := by
          simp [SS]
        let rest : Module.End R (⨂[R]^ n M) :=
          ∑ t ∈ SS.erase s, exactPart t
        have hrest : rest ∈ C := by
          dsimp [rest]
          apply C.sum_mem
          intro t ht
          have htS : t ∈ SS := (Finset.mem_erase.mp ht).2
          have hne : t ≠ s := (Finset.mem_erase.mp ht).1
          have hsub : t ⊆ s := (Finset.mem_filter.mp htS).2
          have hlt : t.card < m := by
            have hss : t ⊂ s := (Finset.ssubset_iff_subset_ne).2 ⟨hsub, hne⟩
            have hc := Finset.card_lt_card hss
            simpa [hs] using hc
          exact ih t.card hlt t rfl
        have hsumEq : exactPart s + rest = upTo s := by
          -- use decomposition by all subsets
          rw [decomp s]
          change exactPart s + (∑ t ∈ SS.erase s, exactPart t) =
            ∑ t ∈ SS, exactPart t
          exact Finset.add_sum_erase SS exactPart hsS
        have hex : exactPart s = upTo s - rest :=
          eq_sub_of_add_eq hsumEq
        rw [hex]
        exact C.sub_mem (upTo_mem s) hrest
    exact aux s0.card s0 rfl
  have hsurjmem : exactPart (Finset.univ : Finset (Fin n)) ∈ C :=
    exact_mem _
  -- functions hitting every index are permutations
  have heqper :
      exactPart (Finset.univ : Finset (Fin n)) =
        ∑ e : Equiv.Perm (Fin n),
          PiTensorProduct.map (fun i : Fin n => f (e i)) := by
    dsimp [exactPart, Ψ, imageOf]
    let Good : Finset (Fin n → Fin n) :=
      Finset.univ.filter (fun r : Fin n → Fin n =>
        Finset.image r Finset.univ = Finset.univ)
    let mkE (r : Fin n → Fin n)
        (hr : r ∈ Good) : Equiv.Perm (Fin n) :=
      Equiv.ofBijective r
        ((Finite.surjective_iff_bijective).1 (by
          intro y
          have hy : y ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
          have hm : y ∈ Finset.image r (Finset.univ : Finset (Fin n)) := by
            rw [(Finset.mem_filter.mp hr).2]
            exact hy
          rcases Finset.mem_image.mp hm with ⟨x, hx, he⟩
          exact ⟨x, he⟩))
    change (∑ r ∈ Good,
        PiTensorProduct.map (fun i : Fin n => f (r i))) = _
    refine Finset.sum_bij (fun r hr => mkE r hr) ?_ ?_ ?_ ?_
    · intro r hr
      exact Finset.mem_univ _
    · intro a ha b hb hab
      have hc := congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) hab
      exact hc
    · intro e he
      let r : Fin n → Fin n := fun i => e i
      have hr : r ∈ Good := by
        dsimp [Good]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact Finset.image_univ_of_surjective e.surjective
      refine ⟨r, hr, ?_⟩
      apply Equiv.ext
      intro i
      change (mkE r hr) i = e i
      simp [mkE, r, Good]
    · intro r hr
      -- values of ofBijective are the original map
      congr 1
  change (∑ e : Equiv.Perm (Fin n),
          PiTensorProduct.map (fun i : Fin n => f (e i))) ∈ C
  rw [← heqper]
  exact hsurjmem



lemma tensor_commute_of_symmetry_commutant {R M : Type*} [Field R]
    [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (n : ℕ) [Invertible (n.factorial : R)]
    (T : Module.End R (⨂[R]^ n M))
    (hT : ∀ u : Module.End R M,
      (PiTensorProduct.map (fun _ : Fin n => u)) * T =
        T * (PiTensorProduct.map (fun _ : Fin n => u)))
    (F : Module.End R (⨂[R]^ n M))
    (hF : ∀ σ : Equiv.Perm (Fin n),
      (symAction R M n σ) * F = F * (symAction R M n σ)) :
    F * T = T * F := by
  classical
  let d := Module.finrank R M
  let b := Module.finBasis R M
  let B := Basis.piTensorProduct (fun _ : Fin n => b)
  -- elementary matrix units in one slot
  let eu (a c : Fin d) : Module.End R M :=
    (b.constr R) (fun j => if j = c then b a else 0)
  have eu_basis (a c j : Fin d) :
      eu a c (b j) = if j = c then b a else 0 := by
    dsimp [eu]
    rw [Module.Basis.constr_basis]
  let E (p q : Fin n → Fin d) : Module.End R (⨂[R]^ n M) :=
    PiTensorProduct.map (fun i : Fin n => eu (q i) (p i))
  have E_on (p q t : Fin n → Fin d) :
      E p q (B t) = if t = p then B q else 0 := by
    dsimp [E, B]
    rw [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod]
    by_cases ht : t = p
    · subst t
      rw [if_pos rfl]
      rw [Basis.piTensorProduct_apply]
      congr 1
      funext i
      rw [eu_basis]
      simp
    · rw [if_neg ht]
      have hi : ∃ i : Fin n, t i ≠ p i := by
        by_contra hh
        push_neg at hh
        exact ht (funext hh)
      rcases hi with ⟨i, hi⟩
      have hz : eu (q i) (p i) (b (t i)) = 0 := by
        simp [eu_basis, hi]
      exact MultilinearMap.map_coord_zero (PiTensorProduct.tprod R) i hz
  -- expand an arbitrary endomorphism in these elementary matrices
  have F_expand : F =
      ∑ p : (Fin n → Fin d),
        ∑ q : (Fin n → Fin d),
          ((B.repr (F (B p)) q) • E p q) := by
    apply B.ext
    intro t
    apply B.ext_elem
    intro r
    rw [LinearMap.sum_apply]
    rw [map_sum]
    let ev : ((Fin n → Fin d) →₀ R) →+ R :=
      { toFun := fun z => z r, map_zero' := rfl,
        map_add' := by intro x y; rfl }
    change (B.repr (F (B t))) r =
      ev (∑ p, B.repr ((∑ q, (B.repr (F (B p))) q • E p q) (B t)))
    rw [map_sum]
    classical
    -- all input words except t are killed by their matrix units
    rw [Finset.sum_eq_single t]
    · rw [LinearMap.sum_apply, map_sum, map_sum]
      change _ = ∑ q, (B.repr (((B.repr (F (B t))) q • E t q) (B t))) r
      -- now only the output q=r contributes
      rw [Finset.sum_eq_single r]
      · simp [E_on]
      · intro q hq hne
        simp [E_on, Module.Basis.repr_self_apply, hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · intro p hp hne
      -- every summand has wrong input
      rw [LinearMap.sum_apply, map_sum, map_sum]
      change (∑ q, (B.repr (((B.repr (F (B p))) q • E p q) (B t))) r) = 0
      apply Finset.sum_eq_zero
      intro q hq
      simp [E_on, Ne.symm hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  let C : Submodule R (Module.End R (⨂[R]^ n M)) :=
    { carrier := {A | A * T = T * A}
      zero_mem' := by simp
      add_mem' := by
        intro A D hA hD
        change (A + D) * T = T * (A + D)
        simpa [add_mul, mul_add] using congrArg₂ (· + ·) hA hD
      smul_mem' := by
        intro a A hA
        change (a • A) * T = T * (a • A)
        simpa [mul_smul_comm, Algebra.smul_mul_assoc]
          using congrArg (fun u => a • u) hA }
  let U (e : Equiv.Perm (Fin n)) : Module.End R (⨂[R]^ n M) :=
    symAction R M n e.symm
  have Uinv (e : Equiv.Perm (Fin n)) : U e * U e.symm = 1 := by
    dsimp [U]
    rw [← (symAction R M n).map_mul]
    have he : (e.symm * e : Equiv.Perm (Fin n)) = 1 := by
      apply Equiv.ext
      intro i
      exact e.symm_apply_apply i
    rw [he, MonoidHom.map_one]
  have conjF (e : Equiv.Perm (Fin n)) : U e * F * U e.symm = F := by
    calc
      U e * F * U e.symm = F * (U e * U e.symm) := by
        have hh := hF e.symm
        dsimp [U]
        -- just commute F with this factor
        rw [hh]
        simp [mul_assoc]
      _ = F := by rw [Uinv]; simp
  have conjE (e : Equiv.Perm (Fin n)) (p q : Fin n → Fin d) :
      U e * E p q * U e.symm =
        PiTensorProduct.map (fun i : Fin n => eu (q (e i)) (p (e i))) := by
    ext x
    change (PiTensorProduct.reindex R (fun _ : Fin n => M) e.symm)
        ((PiTensorProduct.map (fun i : Fin n => eu (q i) (p i)))
          ((PiTensorProduct.reindex R (fun _ : Fin n => M) e)
            ((PiTensorProduct.tprod R) x))) =
          (PiTensorProduct.map
            (fun i : Fin n => eu (q (e i)) (p (e i))))
            ((PiTensorProduct.tprod R) x)
    rw [PiTensorProduct.reindex_tprod, PiTensorProduct.map_tprod,
        PiTensorProduct.reindex_tprod, PiTensorProduct.map_tprod]
    congr 1
    funext i
    simp only [Equiv.symm_symm]
    rw [e.symm_apply_apply]
  have avE (p q : Fin n → Fin d) :
      (∑ e : Equiv.Perm (Fin n), U e * E p q * U e.symm) ∈ C := by
    have hs := tensor_symmetrized_mem_commutant (R:=R) (M:=M) n T hT
      (fun i : Fin n => eu (q i) (p i))
    change (∑ e : Equiv.Perm (Fin n), U e * E p q * U e.symm) * T = _
    simpa [conjE] using hs
  have avFmem :
      (∑ e : Equiv.Perm (Fin n), U e * F * U e.symm) ∈ C := by
    rw [F_expand]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    -- move the scalar coefficients out
    simp_rw [mul_smul_comm, Algebra.smul_mul_assoc]
    rw [Finset.sum_comm]
    -- now p is outermost; interchange the remaining two sums
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))]
    apply C.sum_mem
    intro p hp
    apply C.sum_mem
    intro q hq
    rw [← Finset.smul_sum]
    exact C.smul_mem _ (avE p q)
  -- the averaged conjugate is a nonzero scalar multiple of F
  have havEq :
      (∑ e : Equiv.Perm (Fin n), U e * F * U e.symm) =
        (Fintype.card (Equiv.Perm (Fin n)) : R) • F := by
    simp_rw [conjF]
    simp [Algebra.smul_def]
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : R) ≠ 0 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact (isUnit_of_invertible (n.factorial : R)).ne_zero
  have hscalar : ((Fintype.card (Equiv.Perm (Fin n)) : R)⁻¹) •
      (∑ e : Equiv.Perm (Fin n), U e * F * U e.symm) ∈ C :=
    C.smul_mem _ avFmem
  -- cancel the scalar
  have he : ((Fintype.card (Equiv.Perm (Fin n)) : R)⁻¹) •
      (∑ e : Equiv.Perm (Fin n), U e * F * U e.symm) = F := by
    rw [havEq, smul_smul]
    simp [hcard]
  change F ∈ C
  rw [← he]
  exact hscalar



lemma tensor_mem_adjoin_of_all_maps {R M : Type*} [Field R]
 [AddCommGroup M] [Module R M] [FiniteDimensional R M]
 (n : ℕ) [Invertible (n.factorial : R)]
 (T : Module.End R (⨂[R]^ n M))
 (hT : ∀ u : Module.End R M,
      (PiTensorProduct.map (fun _ : Fin n => u)) * T =
        T * (PiTensorProduct.map (fun _ : Fin n => u))) :
 T ∈ Algebra.adjoin R (Set.range (symAction R M n)) := by
  classical
  let d := Module.finrank R M
  let I := (Fin n → Fin d)
  let X := (⨂[R]^ n M)
  let b := Module.finBasis R M
  let B : Module.Basis I R X := Basis.piTensorProduct (fun _ : Fin n => b)
  let ρ : Equiv.Perm (Fin n) →* Module.End R (I → X) :=
    { toFun := fun g =>
        { toFun := fun z i => (symAction R M n g) (z i)
          map_add' := by intro x y; funext i; simp
          map_smul' := by intro a x; funext i; simp }
      map_one' := by ext z i; simp
      map_mul' := by intro g h; ext z i; simp [Module.End.mul_apply] }
  let v : I → X := fun i => B i
  let N : Submodule R (I → X) :=
    Submodule.span R (Set.range (fun g : Equiv.Perm (Fin n) => ρ g v))
  have stable (g : Equiv.Perm (Fin n)) (x : I → X) (hx : x ∈ N) :
      ρ g x ∈ N := by
    change x ∈ Submodule.span R (Set.range (fun h : Equiv.Perm (Fin n) => ρ h v)) at hx
    change ρ g x ∈ Submodule.span R (Set.range (fun h : Equiv.Perm (Fin n) => ρ h v))
    refine Submodule.span_induction (p:=fun y _ => ρ g y ∈
      Submodule.span R (Set.range (fun h : Equiv.Perm (Fin n) => ρ h v))) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with ⟨h, rfl⟩
      have hv : ρ g (ρ h v) = ρ (g*h) v := by
        have hm := ρ.map_mul g h
        exact DFunLike.congr_fun hm v |>.symm
      rw [hv]
      exact Submodule.subset_span ⟨g*h, rfl⟩
    · simp
    · intro x y hx hy hx' hy'
      simpa using (Submodule.add_mem _ hx' hy')
    · intro a x hx hx'
      simpa using (Submodule.smul_mem _ a hx')
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : R) ≠ 0 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact (isUnit_of_invertible (n.factorial : R)).ne_zero
  obtain ⟨P, Pfix, Pmem, Pcomm⟩ :=
    invariant_projection_of_finite_group (R:=R) (W:= I → X)
      hcard ρ N (by intro g x hx; exact stable g x hx)
  let TT : Module.End R (I → X) :=
    { toFun := fun z i => T (z i)
      map_add' := by intro x y; funext i; simp
      map_smul' := by intro a x; funext i; simp }
  let Q (i j : I) : Module.End R X :=
    (LinearMap.proj i).comp (P.comp (LinearMap.single R (fun _ : I => X) j))
  have single_action (g : Equiv.Perm (Fin n)) (j : I) (x : X) :
      ρ g ((LinearMap.single R (fun _ : I => X) j) x) =
        (LinearMap.single R (fun _ : I => X) j) ((symAction R M n g) x) := by
    funext i
    by_cases hi : i = j
    · subst i
      simp [ρ, LinearMap.single_apply, Pi.single_apply]
    · simp [ρ, LinearMap.single_apply, Pi.single_apply, hi]
  have Qcomm (i j : I) (g : Equiv.Perm (Fin n)) :
      (symAction R M n g) * Q i j = Q i j * (symAction R M n g) := by
    apply LinearMap.ext
    intro x
    have hc := DFunLike.congr_fun (Pcomm g)
      ((LinearMap.single R (fun _ : I => X) j) x)
    change ρ g (P ((LinearMap.single R (fun _ : I => X) j) x)) =
      P (ρ g ((LinearMap.single R (fun _ : I => X) j) x)) at hc
    have hci := congrFun hc i
    change (symAction R M n g)
        (P ((LinearMap.single R (fun _ : I => X) j) x) i) = _ at hci
    rw [single_action] at hci
    exact hci
  have QT (i j : I) : Q i j * T = T * Q i j := by
    exact tensor_commute_of_symmetry_commutant
      (R:=R) (M:=M) n T hT (Q i j) (Qcomm i j)
  have TT_P : TT * P = P * TT := by
    apply LinearMap.ext
    intro z
    funext i
    -- decompose a tuple into its coordinates
    have expand (y : I → X) :
        (∑ j : I, (LinearMap.single R (fun _ : I => X) j) (y j)) = y :=
      LinearMap.sum_single_apply (fun _ : I => X) y
    have Pcoord (y : I → X) :
        P y i = ∑ j : I, Q i j (y j) := by
      calc
        P y i = P (∑ j : I,
            (LinearMap.single R (fun _ : I => X) j) (y j)) i :=
          congrArg (fun t : I → X => P t i) (expand y).symm
        _ = ∑ j : I, Q i j (y j) := by
          rw [map_sum]
          rw [Finset.sum_apply]
          rfl
    change T (P z i) = P (fun j => T (z j)) i
    rw [Pcoord z, map_sum, Pcoord]
    apply Finset.sum_congr rfl
    intro j hj
    have hc := DFunLike.congr_fun (QT i j) (z j)
    change Q i j (T (z j)) = T (Q i j (z j)) at hc
    exact hc.symm
  have vmem : v ∈ N := by
    change v ∈ Submodule.span R
      (Set.range (fun g : Equiv.Perm (Fin n) => ρ g v))
    have hv : ρ (1 : Equiv.Perm (Fin n)) v = v := by simp
    exact Submodule.subset_span ⟨1, hv⟩
  have Tv_mem : TT v ∈ N := by
    have hc := DFunLike.congr_fun TT_P v
    change TT (P v) = P (TT v) at hc
    rw [Pfix v vmem] at hc
    rw [hc]
    exact Pmem _
  have combo (y : I → X) (hy : y ∈ N) :
      ∃ c : Equiv.Perm (Fin n) → R,
        y = ∑ g : Equiv.Perm (Fin n), c g • ρ g v := by
    change y ∈ Submodule.span R
      (Set.range (fun g : Equiv.Perm (Fin n) => ρ g v)) at hy
    refine Submodule.span_induction
      (p:=fun z _ => ∃ c : Equiv.Perm (Fin n) → R,
        z = ∑ g : Equiv.Perm (Fin n), c g • ρ g v) ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases hz with ⟨h, rfl⟩
      refine ⟨(fun g => if g = h then 1 else 0), ?_⟩
      symm
      rw [Finset.sum_eq_single h]
      · simp
      · intro b hb hne
        simp [hne]
      · intro hn
        exact False.elim (hn (Finset.mem_univ _))
    · refine ⟨(fun _ => 0), ?_⟩
      simp
    · intro x y hx hy hx' hy'
      rcases hx' with ⟨a, ha⟩
      rcases hy' with ⟨c, hc⟩
      refine ⟨(fun g => a g + c g), ?_⟩
      rw [ha, hc, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g hg
      rw [add_smul]
    · intro a x hx hx'
      rcases hx' with ⟨c, hc⟩
      refine ⟨(fun g => a * c g), ?_⟩
      rw [hc, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      rw [smul_smul]
  obtain ⟨c, hc⟩ := combo (TT v) Tv_mem
  have Tend : T = ∑ g : Equiv.Perm (Fin n),
        c g • (symAction R M n g) := by
    apply B.ext
    intro i
    have hi := congrFun hc i
    change T (B i) = _
    simpa [TT, v, ρ, LinearMap.sum_apply, Finset.sum_apply] using hi
  rw [Tend]
  apply (Algebra.adjoin R (Set.range (symAction R M n))).sum_mem
  intro g hg
  exact (Algebra.adjoin R (Set.range (symAction R M n))).smul_mem
    ((Algebra.subset_adjoin) ⟨g, rfl⟩) (c g)

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


/-ResultBegin-/

theorem symAction_range_eq_centralizer_glAction {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {k : ℕ} [Invertible (k.factorial : R)] :
    Algebra.adjoin R (Set.range (symAction R M k)) =
      Subalgebra.centralizer R (Set.range (glAction R M k)) :=
/-ResultProofBegin-/by
  apply le_antisymm
  · exact symAction_adjoin_le_centralizer_glAction k
  · classical
    intro z hz
    -- split off the empty tensor power; only scalars act there
    cases k with
    | zero =>
        obtain ⟨r, hr⟩ := end_empty_is_scalar (R:=R) (M:=M) z
        rw [hr]
        exact (Algebra.adjoin R (Set.range (symAction R M 0))).algebraMap_mem r
    | succ k =>
        by_cases hdim : Module.finrank R M = 0
        · letI : Subsingleton M := (Module.finrank_zero_iff).1 hdim
          haveI : Nonempty (Fin (Nat.succ k)) := ⟨⟨0, Nat.zero_lt_succ k⟩⟩
          letI : Subsingleton (⨂[R]^ (Nat.succ k) M) :=
            piTensorProduct_subsingleton_of_subsingleton (R:=R) (M:=M)
          have hz0 : z = 0 := Subsingleton.elim _ _
          rw [hz0]
          exact (Algebra.adjoin R (Set.range (symAction R M (Nat.succ k)))).zero_mem
        · cases k with
          | zero =>
              exact centralizer_glAction_one_le (R:=R) (M:=M) hz
          | succ k =>
              by_cases hdim1 : Module.finrank R M = 1
              · obtain ⟨r, hr⟩ := end_piTensor_is_scalar_finrank_one (R:=R) (M:=M) hdim1 (Nat.succ (Nat.succ k)) z
                rw [hr]
                exact (Algebra.adjoin R (Set.range (symAction R M (Nat.succ (Nat.succ k))))).algebraMap_mem r
              · have h2 : 2 ≤ Module.finrank R M :=
                  (Nat.two_le_iff (Module.finrank R M)).2 ⟨hdim, hdim1⟩
                have hunit (g : (M →ₗ[R] M)ˣ) :
                    (PiTensorProduct.map (fun _ : Fin (Nat.succ (Nat.succ k)) =>
                      (g : Module.End R M))) * z =
                      z * (PiTensorProduct.map (fun _ : Fin (Nat.succ (Nat.succ k)) =>
                        (g : Module.End R M))) := by
                  exact (Subalgebra.mem_centralizer_iff R).1 hz _ ⟨g, rfl⟩
                -- In particular the commutation already extends to every
                -- leading coefficient coming from a nonsingular pencil.
                -- A useful uniform form is a unit followed by a nilpotent;
                -- the missing step in the large case is a decomposition into
                -- these pencils.
                have hnil (g : (M →ₗ[R] M)ˣ) (w : Module.End R M)
                    (hw : IsNilpotent w) :
                    (PiTensorProduct.map
                      (fun _ : Fin (Nat.succ (Nat.succ k)) =>
                        (g : Module.End R M) * w)) * z =
                      z * (PiTensorProduct.map
                        (fun _ : Fin (Nat.succ (Nat.succ k)) =>
                          (g : Module.End R M) * w)) := by
                  exact tensor_commute_unit_mul_nilpotent
                    (R:=R) (M:=M) (Nat.succ (Nat.succ k)) z hunit g w hw
                have hall : ∀ u : Module.End R M,
                    (PiTensorProduct.map
                      (fun _ : Fin (Nat.succ (Nat.succ k)) => u)) * z =
                        z * (PiTensorProduct.map
                          (fun _ : Fin (Nat.succ (Nat.succ k)) => u)) :=
                  tensor_commute_of_unit_or_unit_mul_nilpotent
                    (R:=R) (M:=M) (Nat.succ (Nat.succ k)) z hunit
                      (sw_end_unit_or_nilpotent (R:=R) (M:=M))
                by_cases hn : Nat.succ (Nat.succ k) ≤ Module.finrank R M
                · exact tensor_mem_adjoin_of_all_maps_large
                    (R:=R) (M:=M) (Nat.succ (Nat.succ k)) hn z hall
                · exact tensor_mem_adjoin_of_all_maps (R:=R) (M:=M) (Nat.succ (Nat.succ k)) z hall

/-ResultProofEnd-/
/-ResultEnd-/

end Submission
