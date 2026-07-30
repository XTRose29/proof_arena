import Mathlib
import Submission.Helpers

open Matrix

namespace Submission

/-ResultProofDefinitionsBegin-/

/-- On a row of a unitary matrix the squares of the absolute values add up to one.
We use rows (rather than columns) below. -/
lemma lidskii_unitary_row_sq {m : Type*} [Fintype m] [DecidableEq m]
    (U : Matrix.unitaryGroup m ℂ) (i : m) :
    ∑ k : m, ‖(U : Matrix m m ℂ) i k‖ ^ 2 = (1 : ℝ) := by
  have hu := Unitary.coe_mul_star_self U
  have hi := congrArg (fun M : Matrix m m ℂ => M i i) hu
  -- The `(i,i)` entry of `U * U⋆`.
  simp [Matrix.mul_apply, Matrix.star_apply, Complex.mul_conj,
    Complex.normSq_eq_norm_sq] at hi
  have hi' :
      ((∑ k : m, ‖(U : Matrix m m ℂ) i k‖ ^ 2 : ℝ) : ℂ) = (1 : ℂ) := by
    simpa [Complex.ofReal_sum] using hi
  exact Complex.ofReal_inj.mp hi'

/-- Consequently the pointwise product of the absolute values of two rows
has sum at most one.  The elementary inequality `2*x*y ≤ x^2+y^2`
is convenient here and avoids any choice of a Cauchy--Schwarz lemma. -/
lemma lidskii_unitary_two_rows {m : Type*} [Fintype m] [DecidableEq m]
    (U : Matrix.unitaryGroup m ℂ) (i j : m) :
    ∑ k : m, ‖(U : Matrix m m ℂ) i k‖ * ‖(U : Matrix m m ℂ) j k‖
      ≤ (1 : ℝ) := by
  have hs : ∑ k : m, (2 : ℝ) * ‖(U : Matrix m m ℂ) i k‖ * ‖(U : Matrix m m ℂ) j k‖
        ≤ ∑ k : m, (‖(U : Matrix m m ℂ) i k‖ ^ 2 +
                       ‖(U : Matrix m m ℂ) j k‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro k hk
    simpa using
      (two_mul_le_add_sq (‖(U : Matrix m m ℂ) i k‖)
        (‖(U : Matrix m m ℂ) j k‖))
  rw [Finset.sum_add_distrib, lidskii_unitary_row_sq U i,
      lidskii_unitary_row_sq U j] at hs
  have hleft :
      (∑ k : m, (2 : ℝ) * ‖(U : Matrix m m ℂ) i k‖ *
          ‖(U : Matrix m m ℂ) j k‖) =
        2 * (∑ k : m, ‖(U : Matrix m m ℂ) i k‖ *
          ‖(U : Matrix m m ℂ) j k‖) := by
    rw [Finset.mul_sum]
    simp [mul_assoc]
  rw [hleft] at hs
  linarith

/-- For one eigenvector, expand its Rayleigh quotient in matrix coordinates
and take the triangle inequality.  This is the part of the estimate for a
single Hermitian matrix which does not use any perturbation theorem. -/
lemma lidskii_one_eigenvalue {m : Type*} [Fintype m] [DecidableEq m]
    {M : Matrix m m ℂ} (h : M.IsHermitian) (k : m) :
    |h.eigenvalues k| ≤
      ∑ i : m, ∑ j : m,
        ‖(h.eigenvectorUnitary : Matrix m m ℂ) i k‖ * ‖M i j‖ *
          ‖(h.eigenvectorUnitary : Matrix m m ℂ) j k‖ := by
  calc
    |h.eigenvalues k| =
        |(((dotProduct (star ⇑(h.eigenvectorBasis k))
          (M *ᵥ ⇑(h.eigenvectorBasis k))) : ℂ).re)| := by
            rw [h.eigenvalues_eq k]
            rfl
    _ ≤ ‖dotProduct (star ⇑(h.eigenvectorBasis k))
        (M *ᵥ ⇑(h.eigenvectorBasis k))‖ := Complex.abs_re_le_norm _
    _ = ‖∑ i : m, ∑ j : m,
        star ((h.eigenvectorUnitary : Matrix m m ℂ) i k) *
          (M i j * (h.eigenvectorUnitary : Matrix m m ℂ) j k)‖ := by
          simp [dotProduct, mulVec, Finset.mul_sum,
            Matrix.IsHermitian.eigenvectorUnitary_apply]
    _ ≤ ∑ i : m, ‖∑ j : m,
        star ((h.eigenvectorUnitary : Matrix m m ℂ) i k) *
          (M i j * (h.eigenvectorUnitary : Matrix m m ℂ) j k)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ i : m, ∑ j : m, ‖
        star ((h.eigenvectorUnitary : Matrix m m ℂ) i k) *
          (M i j * (h.eigenvectorUnitary : Matrix m m ℂ) j k)‖ := by
          apply Finset.sum_le_sum
          intro i hi
          exact norm_sum_le _ _
    _ = _ := by
      simp [mul_assoc]

/-- The elementary (non-perturbative) half of the desired estimate: for a
Hermitian matrix the ell-one norm of its eigenvalues is bounded by the
entrywise ell-one norm.  This proof uses the inverse eigenvector coefficients;
the two row estimate for a unitary is exactly the missing factor in the
triangle inequality. -/
lemma lidskii_one_matrix {m : Type*} [Fintype m] [DecidableEq m]
    {M : Matrix m m ℂ} (h : M.IsHermitian) :
    ∑ k : m, |h.eigenvalues k| ≤ ∑ i : m, ∑ j : m, ‖M i j‖ := by
  calc
    ∑ k : m, |h.eigenvalues k| ≤
        ∑ k : m, ∑ i : m, ∑ j : m,
          ‖(h.eigenvectorUnitary : Matrix m m ℂ) i k‖ * ‖M i j‖ *
            ‖(h.eigenvectorUnitary : Matrix m m ℂ) j k‖ := by
              apply Finset.sum_le_sum
              intro k hk
              exact lidskii_one_eigenvalue h k
    _ = ∑ i : m, ∑ j : m, ‖M i j‖ * (∑ k : m,
          ‖(h.eigenvectorUnitary : Matrix m m ℂ) i k‖ *
            ‖(h.eigenvectorUnitary : Matrix m m ℂ) j k‖) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ ≤ ∑ i : m, ∑ j : m, ‖M i j‖ * 1 := by
          apply Finset.sum_le_sum; intro i hi
          apply Finset.sum_le_sum; intro j hj
          exact mul_le_mul_of_nonneg_left
            (lidskii_unitary_two_rows h.eigenvectorUnitary i j)
            (norm_nonneg _)
    _ = _ := by simp

/-- The preceding bound with the canonical `Fin (card m)` indexing of the
ordered eigenvalues. -/
lemma lidskii_one_matrix₀ {m : Type*} [Fintype m] [DecidableEq m]
    {M : Matrix m m ℂ} (h : M.IsHermitian) :
    ∑ k : Fin (Fintype.card m), |h.eigenvalues₀ k| ≤ ∑ i : m, ∑ j : m, ‖M i j‖ := by
  have hind :
      ∑ k : Fin (Fintype.card m), |h.eigenvalues₀ k| =
        ∑ k : m, |h.eigenvalues k| := by
    let e : Fin (Fintype.card m) ≃ m :=
      Fintype.equivOfCardEq (Fintype.card_fin _)
    change ∑ k : Fin (Fintype.card m), |h.eigenvalues₀ k| =
      ∑ k : m, |h.eigenvalues₀ (e.symm k)|
    exact (Equiv.sum_comp e.symm
      (fun k : Fin (Fintype.card m) => |h.eigenvalues₀ k|)).symm
  rw [hind]
  exact lidskii_one_matrix h



open scoped ComplexOrder
open scoped ComplexConjugate
open scoped BigOperators

/-- The eigen equation, indexed by the ordered finite index, as an equation in
Euclidean space. -/
lemma lidskii_eigen_fin {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : M.IsHermitian) (p : Fin (Fintype.card n)) :
    WithLp.toLp (2:ENNReal) (M *ᵥ (h.eigenvectorBasis
      (Fintype.equivOfCardEq (Fintype.card_fin _ ) p)).ofLp) =
       ( (h.eigenvalues₀ p : ℝ) : ℂ) •
        h.eigenvectorBasis (Fintype.equivOfCardEq (Fintype.card_fin _) p) := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have heig := h.mulVec_eigenvectorBasis (e p)
  -- the definition of the reindexed eigenvalue
  have hv : h.eigenvalues (e p) = h.eigenvalues₀ p := by
    simp [Matrix.IsHermitian.eigenvalues, e]
  rw [heig, hv]
  change WithLp.toLp (2:ENNReal) ((h.eigenvalues₀ p : ℝ) •
      (h.eigenvectorBasis (e p)).ofLp) =
       ((h.eigenvalues₀ p : ℝ) : ℂ) •
        h.eigenvectorBasis (Fintype.equivOfCardEq (Fintype.card_fin _) p)
  rw [WithLp.toLp_smul]
  change ((h.eigenvalues₀ p : ℝ) : ℂ) • h.eigenvectorBasis (e p) = _
  rfl



/-- Rayleigh form on a linear combination of *distinct* members of the
ordered eigenbasis. This elementary diagonal calculation is useful for the
min-max argument; doing it in the inner product space avoids coordinates. -/
lemma lidskii_rayleigh_sum {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : M.IsHermitian)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Fin (Fintype.card n)) (hf : Function.Injective f)
    (c : ι → ℂ) :
    let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
    let v : ι → EuclideanSpace ℂ n := fun i => h.eigenvectorBasis (e (f i))
    let x : EuclideanSpace ℂ n := ∑ i, c i • v i
    inner ℂ x (WithLp.toLp (2:ENNReal) (M *ᵥ x.ofLp)) =
      ∑ i, ( (h.eigenvalues₀ (f i) : ℝ) : ℂ) * (star (c i) * c i) := by
  classical
  dsimp
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let v : ι → EuclideanSpace ℂ n := fun i => h.eigenvectorBasis (e (f i))
  change inner ℂ (∑ i, c i • v i)
      (WithLp.toLp (2:ENNReal) (M *ᵥ ( (∑ i, c i • v i : EuclideanSpace ℂ n)).ofLp)) = _
  -- equation for the operator on each vector
  have he (i : ι) : WithLp.toLp (2:ENNReal) (M *ᵥ (v i).ofLp) =
       ((h.eigenvalues₀ (f i) : ℝ) : ℂ) • v i :=
    lidskii_eigen_fin h (f i)
  have ht0 : WithLp.toLp (2:ENNReal)
        (M *ᵥ ( (∑ i, c i • v i : EuclideanSpace ℂ n)).ofLp) =
        ∑ i, c i •
          (WithLp.toLp (2:ENNReal) (M *ᵥ (v i).ofLp)) := by
    ext j
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.toLp_sum,
      WithLp.toLp_smul]
    -- linearity of matrix multiplication by a vector
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
  have ht : WithLp.toLp (2:ENNReal)
        (M *ᵥ ( (∑ i, c i • v i : EuclideanSpace ℂ n)).ofLp) =
        ∑ i, c i •
          (((h.eigenvalues₀ (f i) : ℝ) : ℂ) • v i) := by
    rw [ht0]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he]

  rw [ht]
  -- orthonormality of these distinct basis vectors.
  have ho (i j : ι) : inner ℂ (v i) (v j) = if i = j then 1 else 0 := by
    have H := (orthonormal_iff_ite.mp h.eigenvectorBasis.orthonormal)
        (e (f i)) (e (f j))
    change inner ℂ (h.eigenvectorBasis (e (f i)))
       (h.eigenvectorBasis (e (f j))) = _ at H
    change inner ℂ (h.eigenvectorBasis (e (f i)))
       (h.eigenvectorBasis (e (f j))) = _
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      rw [if_pos rfl] at H
      exact H
    · have hne : e (f i) ≠ e (f j) := by
          intro hh
          have hx : f i = f j := e.injective hh
          exact hij (hf hx)
      rw [if_neg hij]
      rw [if_neg hne] at H
      exact H

  -- expand the two finite sums
  classical
  calc
    inner ℂ (∑ i, c i • v i)
        (∑ j, c j • (((h.eigenvalues₀ (f j) : ℝ) : ℂ) • v j))
      = ∑ i, ∑ j,
          star (c i) * (c j * ((h.eigenvalues₀ (f j) : ℝ) : ℂ)) *
             inner ℂ (v i) (v j) := by
          simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
          apply Finset.sum_congr rfl; intro i hi
          apply Finset.sum_congr rfl; intro j hj
          rw [RCLike.star_def]
          ring
    _ = _ := by
      -- collapse the inner sum using orthogonality
      classical
      simp_rw [ho]
      -- the Kronecker delta kills all but `j=i`
      simp [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring



lemma lidskii_norm_combo {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : M.IsHermitian)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Fin (Fintype.card n)) (hf : Function.Injective f) (c : ι → ℂ) :
    let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
    ‖(∑ i, c i • h.eigenvectorBasis (e (f i)) : EuclideanSpace ℂ n)‖ ^ 2
       = ∑ i, ‖c i‖ ^ 2 := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  dsimp
  rw [← Complex.ofReal_inj]
  have hs := inner_self_eq_norm_sq_to_K
    (𝕜:=ℂ) (∑ i, c i • h.eigenvectorBasis (e (f i)) : EuclideanSpace ℂ n)
  push_cast
  -- it is enough to compute this inner product
  change ( (‖(∑ i, c i • h.eigenvectorBasis (e (f i)) : EuclideanSpace ℂ n)‖ : ℂ) ^ 2) = _
  have hs' : ((‖(∑ i, c i • h.eigenvectorBasis (e (f i)) : EuclideanSpace ℂ n)‖ : ℂ)^2) =
      inner ℂ (∑ i, c i • h.eigenvectorBasis (e (f i))) (∑ i, c i • h.eigenvectorBasis (e (f i))) := by
        simpa using hs.symm
  rw [hs']
  -- orthogonality
  have ho (i j : ι) : inner ℂ (h.eigenvectorBasis (e (f i)))
        (h.eigenvectorBasis (e (f j))) = if i = j then 1 else 0 := by
    have H := (orthonormal_iff_ite.mp h.eigenvectorBasis.orthonormal)
        (e (f i)) (e (f j))
    by_cases hij : i = j
    · subst j; simpa using H
    · have hn : e (f i) ≠ e (f j) := fun hh => hij (hf (e.injective hh))
      simp [hij, hn] at H ⊢
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, ho]
  -- only equal indices remain
  apply Finset.sum_congr rfl; intro i hi
  simp
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast


/-- The two spectral subspaces used in the min--max argument intersect.
There are `k+1` vectors above `k` and `N-k` below it. -/
lemma lidskii_spectral_intersection {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (k : Fin (Fintype.card n)) :
    let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
    let s : Submodule ℂ (EuclideanSpace ℂ n) :=
      Submodule.span ℂ (Set.range (fun i : Set.Iic k => hP.eigenvectorBasis (e i.1)))
    let t : Submodule ℂ (EuclideanSpace ℂ n) :=
      Submodule.span ℂ (Set.range (fun i : Set.Ici k => hQ.eigenvectorBasis (e i.1)))
    ∃ x : EuclideanSpace ℂ n, x ∈ s ∧ x ∈ t ∧ x ≠ 0 := by
  classical
  dsimp
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let s : Submodule ℂ (EuclideanSpace ℂ n) :=
      Submodule.span ℂ (Set.range (fun i : Set.Iic k => hP.eigenvectorBasis (e i.1)))
  let t : Submodule ℂ (EuclideanSpace ℂ n) :=
      Submodule.span ℂ (Set.range (fun i : Set.Ici k => hQ.eigenvectorBasis (e i.1)))
  change ∃ x, x ∈ s ∧ x ∈ t ∧ x ≠ 0
  have liP : LinearIndependent ℂ
       (fun i : Set.Iic k => hP.eigenvectorBasis (e i.1)) :=
    hP.eigenvectorBasis.toBasis.linearIndependent.comp
      (fun i : Set.Iic k => e i.1) (fun _ _ hh => Subtype.ext (e.injective hh))
  have liQ : LinearIndependent ℂ
       (fun i : Set.Ici k => hQ.eigenvectorBasis (e i.1)) :=
    hQ.eigenvectorBasis.toBasis.linearIndependent.comp
      (fun i : Set.Ici k => e i.1) (fun _ _ hh => Subtype.ext (e.injective hh))
  have ds : Module.finrank ℂ s = k.val + 1 := by
    change Module.finrank ℂ (Submodule.span ℂ (Set.range _)) = _
    rw [finrank_span_eq_card liP]
    simp
  have dt : Module.finrank ℂ t = Fintype.card n - k.val := by
    change Module.finrank ℂ (Submodule.span ℂ (Set.range _)) = _
    rw [finrank_span_eq_card liQ]
    simp
  have hn : s ⊓ t ≠ ⊥ := by
    intro hb
    have dis : Disjoint s t := (disjoint_iff_inf_le).2 (le_of_eq hb)
    have le := Submodule.finrank_add_finrank_le_of_disjoint dis
    rw [ds, dt, finrank_euclideanSpace] at le
    have kv : k.val < Fintype.card n := k.isLt
    omega
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  exact ⟨x, hx.1, hx.2, hne⟩





/-- A real version of the diagonal Rayleigh computation, valid for any finite
subfamily of the ordered eigenbasis.  Keeping this separate makes using the
min--max subspaces below rather painless: the coefficients occurring in the
`span` lemmas are functions, not `Finsupp`s. -/
lemma lidskii_rayleigh_sum_re {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : M.IsHermitian)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Fin (Fintype.card n)) (hf : Function.Injective f) (c : ι → ℂ) :
    let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
    let x : EuclideanSpace ℂ n := ∑ i, c i • h.eigenvectorBasis (e (f i))
    (inner ℂ x (WithLp.toLp (2:ENNReal) (M *ᵥ x.ofLp))).re =
       ∑ i, h.eigenvalues₀ (f i) * ‖c i‖ ^ 2 := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  dsimp
  have H := lidskii_rayleigh_sum (n:=n) h f hf c
  -- take real parts of the already diagonal, complex identity
  dsimp at H
  rw [H]
  simp [Complex.mul_re, mul_comm, mul_left_comm, mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  apply Finset.sum_congr rfl
  intro i hi
  simp [← Complex.ofReal_pow]

/-- Rayleigh's inequality on the *upper* (first `k+1`) eigenvectors.
Here `upper` refers to their position in the non-increasing spectral list. -/
lemma lidskii_rayleigh_Iic {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : M.IsHermitian)
    (k : Fin (Fintype.card n)) (x : EuclideanSpace ℂ n)
    (hx : x ∈ Submodule.span ℂ
      (Set.range (fun i : Set.Iic k =>
        h.eigenvectorBasis
          (Fintype.equivOfCardEq (Fintype.card_fin _) i.1)))) :
    h.eigenvalues₀ k * ‖x‖ ^ 2 ≤
      (inner ℂ x (WithLp.toLp (2:ENNReal) (M *ᵥ x.ofLp))).re := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  change x ∈ Submodule.span ℂ (Set.range
      (fun i : Set.Iic k => h.eigenvectorBasis (e i.1))) at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
  have f_inj : Function.Injective (fun i : Set.Iic k => (i.1 : Fin (Fintype.card n))) :=
    fun _ _ hh => Subtype.ext hh
  have Hre := lidskii_rayleigh_sum_re (n:=n) h
      (fun i : Set.Iic k => (i.1 : Fin (Fintype.card n))) f_inj c
  dsimp at Hre
  change (inner ℂ (∑ i, c i • h.eigenvectorBasis (e i.1))
        (WithLp.toLp (2:ENNReal)
          (M *ᵥ ( (∑ i, c i • h.eigenvectorBasis (e i.1) :
              EuclideanSpace ℂ n)).ofLp))).re =
       _ at Hre
  -- compute the norm of this expansion as well
  have Hnorm := lidskii_norm_combo (n:=n) h
      (fun i : Set.Iic k => (i.1 : Fin (Fintype.card n))) f_inj c
  dsimp at Hnorm
  change ‖(∑ i, c i • h.eigenvectorBasis (e i.1) :
            EuclideanSpace ℂ n)‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 at Hnorm
  -- every eigenvalue with index in `Iic k` is at least the kth one
  have hsum :
      h.eigenvalues₀ k * (∑ i : Set.Iic k, ‖c i‖ ^ 2) ≤
        ∑ i : Set.Iic k, h.eigenvalues₀ i.1 * ‖c i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (h.eigenvalues₀_antitone i.2) (sq_nonneg _)
  rw [← Hnorm] at hsum
  rw [hc] at Hre
  -- and rewrite the other expansion in the inequality
  simpa [hc, Hre] using hsum

/-- The dual Rayleigh inequality on the *lower* tail of the eigenbasis. -/
lemma lidskii_rayleigh_Ici {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : M.IsHermitian)
    (k : Fin (Fintype.card n)) (x : EuclideanSpace ℂ n)
    (hx : x ∈ Submodule.span ℂ
      (Set.range (fun i : Set.Ici k =>
        h.eigenvectorBasis
          (Fintype.equivOfCardEq (Fintype.card_fin _) i.1)))) :
    (inner ℂ x (WithLp.toLp (2:ENNReal) (M *ᵥ x.ofLp))).re ≤
       h.eigenvalues₀ k * ‖x‖ ^ 2 := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  change x ∈ Submodule.span ℂ (Set.range
      (fun i : Set.Ici k => h.eigenvectorBasis (e i.1))) at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
  have f_inj : Function.Injective (fun i : Set.Ici k => (i.1 : Fin (Fintype.card n))) :=
    fun _ _ hh => Subtype.ext hh
  have Hre := lidskii_rayleigh_sum_re (n:=n) h
      (fun i : Set.Ici k => (i.1 : Fin (Fintype.card n))) f_inj c
  dsimp at Hre
  change (inner ℂ (∑ i, c i • h.eigenvectorBasis (e i.1))
        (WithLp.toLp (2:ENNReal)
          (M *ᵥ ( (∑ i, c i • h.eigenvectorBasis (e i.1) :
              EuclideanSpace ℂ n)).ofLp))).re =
       _ at Hre
  have Hnorm := lidskii_norm_combo (n:=n) h
      (fun i : Set.Ici k => (i.1 : Fin (Fintype.card n))) f_inj c
  dsimp at Hnorm
  change ‖(∑ i, c i • h.eigenvectorBasis (e i.1) :
            EuclideanSpace ℂ n)‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 at Hnorm
  have hsum :
      (∑ i : Set.Ici k, h.eigenvalues₀ i.1 * ‖c i‖ ^ 2) ≤
       h.eigenvalues₀ k * (∑ i : Set.Ici k, ‖c i‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (h.eigenvalues₀_antitone i.2) (sq_nonneg _)
  rw [← Hnorm] at hsum
  rw [hc] at Hre
  simpa [hc, Hre] using hsum



/-- A crude but very useful uniform Rayleigh bound.  It is worth recording
with the full `Fin (card n)` basis: no choice of an extremal vector is involved,
and it also covers the zero-dimensional case. -/
lemma lidskii_rayleigh_abs {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : M.IsHermitian) (x : EuclideanSpace ℂ n) :
    |(inner ℂ x (WithLp.toLp (2:ENNReal) (M *ᵥ x.ofLp))).re| ≤
      (∑ i : Fin (Fintype.card n), |h.eigenvalues₀ i|) * ‖x‖ ^ 2 := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hx' : x ∈ Submodule.span ℂ
      (Set.range (fun i : n => h.eigenvectorBasis i)) := by
    change x ∈ Submodule.span ℂ
      (Set.range (⇑h.eigenvectorBasis.toBasis))
    rw [Module.Basis.span_eq]
    trivial
  obtain ⟨d, hd⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx'
  let c : Fin (Fintype.card n) → ℂ := fun i => d (e i)
  have hc : (∑ i : Fin (Fintype.card n),
        c i • h.eigenvectorBasis (e i) : EuclideanSpace ℂ n) = x := by
    -- re-index the finite sum in `hd`
    change (∑ i : Fin (Fintype.card n),
        d (e i) • h.eigenvectorBasis (e i)) = x
    simpa using ((Equiv.sum_comp e
      (fun j : n => d j • h.eigenvectorBasis j)).trans hd)
  have Hre := lidskii_rayleigh_sum_re (n:=n) h
      (fun i : Fin (Fintype.card n) => i) (fun _ _ z => z) c
  dsimp at Hre
  change (inner ℂ (∑ i, c i • h.eigenvectorBasis (e i))
        (WithLp.toLp (2:ENNReal)
          (M *ᵥ ( (∑ i, c i • h.eigenvectorBasis (e i) :
              EuclideanSpace ℂ n)).ofLp))).re =
       _ at Hre
  have Hnorm := lidskii_norm_combo (n:=n) h
      (fun i : Fin (Fintype.card n) => i) (fun _ _ z => z) c
  dsimp at Hnorm
  change ‖(∑ i, c i • h.eigenvectorBasis (e i) :
            EuclideanSpace ℂ n)‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 at Hnorm
  rw [hc] at Hre Hnorm
  rw [Hre, Hnorm]
  calc
    |∑ i : Fin (Fintype.card n), h.eigenvalues₀ i * ‖c i‖ ^ 2|
        ≤ ∑ i : Fin (Fintype.card n),
              |h.eigenvalues₀ i * ‖c i‖ ^ 2| := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (Fintype.card n),
          |h.eigenvalues₀ i| * ‖c i‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            |h.eigenvalues₀ i * ‖c i‖ ^ 2| =
                |h.eigenvalues₀ i| * |‖c i‖ ^ 2| :=
                   abs_mul _ _
            _ = |h.eigenvalues₀ i| * ‖c i‖ ^ 2 := by
                  have ht : 0 ≤ (‖c i‖ ^ 2 : ℝ) := sq_nonneg _
                  have habs : |(‖c i‖ ^ 2 : ℝ)| = ‖c i‖ ^ 2 :=
                    abs_of_nonneg ht
                  rw [habs]
    _ ≤ ∑ i : Fin (Fintype.card n),
          |h.eigenvalues₀ i| * (∑ j : Fin (Fintype.card n), ‖c j‖ ^ 2) := by
          apply Finset.sum_le_sum
          intro i hi
          have hci : ‖c i‖ ^ 2 ≤
                ∑ j : Fin (Fintype.card n), ‖c j‖ ^ 2 := by
            have hs := Finset.single_le_sum
              (s := (Finset.univ : Finset (Fin (Fintype.card n))))
              (f := fun j : Fin (Fintype.card n) => ‖c j‖ ^ 2)
              (fun j hj => sq_nonneg (‖c j‖)) (show i ∈ (Finset.univ :
                 Finset (Fin (Fintype.card n))) by simp)
            simpa using hs
          exact mul_le_mul_of_nonneg_left hci (abs_nonneg _)
    _ = (∑ i : Fin (Fintype.card n), |h.eigenvalues₀ i|) *
          (∑ j : Fin (Fintype.card n), ‖c j‖ ^ 2) := by
          rw [Finset.sum_mul]

/-- For later Ky Fan refinements it is convenient to have the sharper
Rayleigh bound with the *largest* eigenvalue.  We assume the ambient index
type nonempty only to name `0 : Fin (card n)`; the earlier absolute bound did
not need this assumption. -/
lemma lidskii_rayleigh_max {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n]
    {M : Matrix n n ℂ} (h : M.IsHermitian) (x : EuclideanSpace ℂ n) :
    let z : Fin (Fintype.card n) :=
      ⟨0, (Fintype.card_pos_iff.mpr (inferInstance : Nonempty n))⟩
    (inner ℂ x (WithLp.toLp (2:ENNReal) (M *ᵥ x.ofLp))).re ≤
       h.eigenvalues₀ z * ‖x‖ ^ 2 := by
  classical
  dsimp
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let z : Fin (Fintype.card n) :=
      ⟨0, (Fintype.card_pos_iff.mpr (inferInstance : Nonempty n))⟩
  have hz (i : Fin (Fintype.card n)) : z ≤ i := by
    exact Fin.mk_le_mk.mpr (Nat.zero_le _)
  have hx' : x ∈ Submodule.span ℂ
      (Set.range (fun i : n => h.eigenvectorBasis i)) := by
    change x ∈ Submodule.span ℂ (Set.range (⇑h.eigenvectorBasis.toBasis))
    rw [Module.Basis.span_eq]
    trivial
  obtain ⟨d, hd⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx'
  let c : Fin (Fintype.card n) → ℂ := fun i => d (e i)
  have hc : (∑ i : Fin (Fintype.card n),
        c i • h.eigenvectorBasis (e i) : EuclideanSpace ℂ n) = x := by
    change (∑ i : Fin (Fintype.card n),
        d (e i) • h.eigenvectorBasis (e i)) = x
    simpa using ((Equiv.sum_comp e
      (fun j : n => d j • h.eigenvectorBasis j)).trans hd)
  have Hre := lidskii_rayleigh_sum_re (n:=n) h
      (fun i : Fin (Fintype.card n) => i) (fun _ _ z => z) c
  dsimp at Hre
  change (inner ℂ (∑ i, c i • h.eigenvectorBasis (e i))
        (WithLp.toLp (2:ENNReal)
          (M *ᵥ ( (∑ i, c i • h.eigenvectorBasis (e i) :
              EuclideanSpace ℂ n)).ofLp))).re =
       _ at Hre
  have Hnorm := lidskii_norm_combo (n:=n) h
      (fun i : Fin (Fintype.card n) => i) (fun _ _ z => z) c
  dsimp at Hnorm
  change ‖(∑ i, c i • h.eigenvectorBasis (e i) :
            EuclideanSpace ℂ n)‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 at Hnorm
  rw [hc] at Hre Hnorm
  rw [Hre]
  calc
    ∑ i : Fin (Fintype.card n), h.eigenvalues₀ i * ‖c i‖ ^ 2 ≤
        ∑ i : Fin (Fintype.card n), h.eigenvalues₀ z * ‖c i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right
             (h.eigenvalues₀_antitone (hz i)) (sq_nonneg _)
    _ = h.eigenvalues₀ z * (∑ i : Fin (Fintype.card n), ‖c i‖ ^ 2) := by
          rw [Finset.mul_sum]
    _ = h.eigenvalues₀ z * ‖x‖ ^ 2 := by rw [Hnorm]

/-- Weyl's one-index upper comparison (named using the largest eigenvalue
rather than a supremum of Rayleigh quotients). -/
lemma lidskii_weyl_max {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (k : Fin (Fintype.card n)) :
    let z : Fin (Fintype.card n) := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
    hP.eigenvalues₀ k - hQ.eigenvalues₀ k ≤
       (hP.sub hQ).eigenvalues₀ z := by
  classical
  dsimp
  letI : Nonempty n := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt k.isLt)
  let z : Fin (Fintype.card n) := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
  obtain ⟨x, hxS, hxT, hx0⟩ := lidskii_spectral_intersection hP hQ k
  have hp : hP.eigenvalues₀ k * ‖x‖ ^ 2 ≤
      (inner ℂ x (WithLp.toLp (2:ENNReal) (P *ᵥ x.ofLp))).re :=
    lidskii_rayleigh_Iic hP k x hxS
  have hq : (inner ℂ x (WithLp.toLp (2:ENNReal) (Q *ᵥ x.ofLp))).re ≤
      hQ.eigenvalues₀ k * ‖x‖ ^ 2 :=
    lidskii_rayleigh_Ici hQ k x hxT
  have hsub :
      (hP.eigenvalues₀ k - hQ.eigenvalues₀ k) * ‖x‖^2 ≤
       (inner ℂ x (WithLp.toLp (2:ENNReal) ((P-Q) *ᵥ x.ofLp))).re := by
    rw [Matrix.sub_mulVec, WithLp.toLp_sub, inner_sub_right, Complex.sub_re]
    linarith
  -- instantiate the maximum-Rayleigh inequality above
  have hm := lidskii_rayleigh_max (hP.sub hQ) x
  change (inner ℂ x
      (WithLp.toLp (2:ENNReal) ((P-Q) *ᵥ x.ofLp))).re ≤
        (hP.sub hQ).eigenvalues₀ z * ‖x‖^2 at hm
  have hpos : 0 < ‖x‖ ^ 2 := by
    have : 0 < ‖x‖ := (norm_pos_iff.mpr hx0)
    positivity
  exact le_of_mul_le_mul_right (le_trans hsub hm) hpos

/-- The Rayleigh functional respects subtraction of matrices.  We state this
for its real part, which is all that the ordered eigenvalues see. -/
lemma lidskii_rayleigh_sub {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    (inner ℂ x (WithLp.toLp (2:ENNReal) ((P-Q) *ᵥ x.ofLp))).re =
      (inner ℂ x (WithLp.toLp (2:ENNReal) (P *ᵥ x.ofLp))).re -
      (inner ℂ x (WithLp.toLp (2:ENNReal) (Q *ᵥ x.ofLp))).re := by
  rw [Matrix.sub_mulVec, WithLp.toLp_sub, inner_sub_right]
  exact Complex.sub_re _ _

/-- The one-index min--max comparison.  This is the part of the perturbation
argument that only uses an intersection of two subspaces (rather than the
later simultaneous Ky Fan sums).  The right hand side is the spectral
`ℓ¹` bound for the difference; leaving it as a Rayleigh bound first avoids
any division by the norm of the chosen nonzero vector. -/
lemma lidskii_weyl_l1_upper {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hP.eigenvalues₀ k - hQ.eigenvalues₀ k ≤
      ∑ i : Fin (Fintype.card n),
        |(hP.sub hQ).eigenvalues₀ i| := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let s : Submodule ℂ (EuclideanSpace ℂ n) :=
      Submodule.span ℂ (Set.range (fun i : Set.Iic k =>
        hP.eigenvectorBasis (e i.1)))
  let t : Submodule ℂ (EuclideanSpace ℂ n) :=
      Submodule.span ℂ (Set.range (fun i : Set.Ici k =>
        hQ.eigenvectorBasis (e i.1)))
  obtain ⟨x, hxS, hxT, hx0⟩ := lidskii_spectral_intersection hP hQ k
  have hp : hP.eigenvalues₀ k * ‖x‖ ^ 2 ≤
      (inner ℂ x (WithLp.toLp (2:ENNReal) (P *ᵥ x.ofLp))).re :=
    lidskii_rayleigh_Iic hP k x hxS
  have hq : (inner ℂ x (WithLp.toLp (2:ENNReal) (Q *ᵥ x.ofLp))).re ≤
      hQ.eigenvalues₀ k * ‖x‖ ^ 2 :=
    lidskii_rayleigh_Ici hQ k x hxT
  have hsub :
      (hP.eigenvalues₀ k - hQ.eigenvalues₀ k) * ‖x‖^2 ≤
       (inner ℂ x (WithLp.toLp (2:ENNReal) ((P-Q) *ᵥ x.ofLp))).re := by
    rw [lidskii_rayleigh_sub]
    linarith
  have hbound := lidskii_rayleigh_abs (hP.sub hQ) x
  have hpos : 0 < ‖x‖ ^ 2 := by
    have : 0 < ‖x‖ := (norm_pos_iff.mpr hx0)
    positivity
  -- the real part is bounded by its absolute value, and divide by the
  -- (strictly) positive squared norm
  have hxineq :
      (hP.eigenvalues₀ k - hQ.eigenvalues₀ k) * ‖x‖^2 ≤
        (∑ i : Fin (Fintype.card n), |(hP.sub hQ).eigenvalues₀ i|) *
          ‖x‖^2 := le_trans hsub (le_trans (le_abs_self _ ) hbound)
  exact le_of_mul_le_mul_right hxineq hpos

/-- The symmetric pointwise bound. -/
lemma lidskii_weyl_l1 {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (k : Fin (Fintype.card n)) :
    |hP.eigenvalues₀ k - hQ.eigenvalues₀ k| ≤
      ∑ i : Fin (Fintype.card n),
        |(hP.sub hQ).eigenvalues₀ i| := by
  classical
  -- the upper half was just the usual dimension-intersection argument.
  have hup := lidskii_weyl_l1_upper hP hQ k
  -- For the lower half use the opposite two subspaces.  We still evaluate
  -- the Rayleigh functional of `P-Q`, so no assertion about how a spectrum
  -- is permuted by negation is needed.
  obtain ⟨x, hxQ, hxP, hx0⟩ := lidskii_spectral_intersection hQ hP k
  have hq : hQ.eigenvalues₀ k * ‖x‖ ^ 2 ≤
      (inner ℂ x (WithLp.toLp (2:ENNReal) (Q *ᵥ x.ofLp))).re :=
    lidskii_rayleigh_Iic hQ k x hxQ
  have hp : (inner ℂ x (WithLp.toLp (2:ENNReal) (P *ᵥ x.ofLp))).re ≤
      hP.eigenvalues₀ k * ‖x‖ ^ 2 :=
    lidskii_rayleigh_Ici hP k x hxP
  have hsub :
      (hQ.eigenvalues₀ k - hP.eigenvalues₀ k) * ‖x‖^2 ≤
       - (inner ℂ x (WithLp.toLp (2:ENNReal) ((P-Q) *ᵥ x.ofLp))).re := by
    rw [lidskii_rayleigh_sub]
    linarith
  have hb := lidskii_rayleigh_abs (hP.sub hQ) x
  have hpos : 0 < ‖x‖ ^ 2 := by
    have : 0 < ‖x‖ := (norm_pos_iff.mpr hx0)
    positivity
  have hxineq :
      (hQ.eigenvalues₀ k - hP.eigenvalues₀ k) * ‖x‖^2 ≤
        (∑ i : Fin (Fintype.card n), |(hP.sub hQ).eigenvalues₀ i|) *
           ‖x‖^2 :=
    le_trans hsub (le_trans (neg_le_abs _) hb)
  have hlo' : hQ.eigenvalues₀ k - hP.eigenvalues₀ k ≤
        ∑ i : Fin (Fintype.card n), |(hP.sub hQ).eigenvalues₀ i| :=
    le_of_mul_le_mul_right hxineq hpos
  -- `abs_le` is the convenient way of recombining the two halves.
  apply (abs_le).2
  constructor
  · linarith
  · exact hup


/-- A Loewner-order version of the one-dimensional min--max argument.  We
only need positivity of the Rayleigh functional of the difference; this
formulation is often easier to use than a packaged PSD theory. -/
lemma lidskii_loewner_eigen {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hpos : ∀ x : EuclideanSpace ℂ n,
       0 ≤ (inner ℂ x (WithLp.toLp (2:ENNReal)
            ((P-Q) *ᵥ x.ofLp))).re)
    (k : Fin (Fintype.card n)) :
    hQ.eigenvalues₀ k ≤ hP.eigenvalues₀ k := by
  classical
  -- The upper subspace for `Q` and lower for `P` meet.
  obtain ⟨x, hxQ, hxP, hx0⟩ := lidskii_spectral_intersection hQ hP k
  have hq : hQ.eigenvalues₀ k * ‖x‖ ^ 2 ≤
      (inner ℂ x (WithLp.toLp (2:ENNReal) (Q *ᵥ x.ofLp))).re :=
    lidskii_rayleigh_Iic hQ k x hxQ
  have hp : (inner ℂ x (WithLp.toLp (2:ENNReal) (P *ᵥ x.ofLp))).re ≤
      hP.eigenvalues₀ k * ‖x‖ ^ 2 :=
    lidskii_rayleigh_Ici hP k x hxP
  have hn :
      (hQ.eigenvalues₀ k - hP.eigenvalues₀ k) * ‖x‖ ^ 2 ≤ 0 := by
    have H := hpos x
    rw [lidskii_rayleigh_sub] at H
    nlinarith
  have ht : 0 < ‖x‖ ^ 2 := by
    have : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    positivity
  have hd : hQ.eigenvalues₀ k - hP.eigenvalues₀ k ≤ 0 := by
    nlinarith
  linarith

/-- The real trace is the sum of the canonically indexed eigenvalues. -/
lemma lidskii_trace_re {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : M.IsHermitian) :
    M.trace.re = ∑ i : Fin (Fintype.card n), h.eigenvalues₀ i := by
  classical
  have H := Matrix.IsHermitian.trace_eq_sum_eigenvalues h
  -- take real parts of the usual `n`-indexed formula
  have Hr := congrArg Complex.re H
  -- then re-index the finite sum
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hs : (∑ i : n, h.eigenvalues i) =
       ∑ i : Fin (Fintype.card n), h.eigenvalues₀ i := by
    change (∑ i : n, h.eigenvalues₀ (e.symm i)) = _
    exact Equiv.sum_comp e.symm _
  rw [Complex.re_sum] at Hr
  have Hr' : M.trace.re = ∑ i : n, h.eigenvalues i := by
    simpa using Hr
  exact Hr'.trans hs

/-- Consequently a positive perturbation has no cancellation in the
`ℓ¹` displacement of the ordered eigenvalues: it is just its trace. -/
lemma lidskii_loewner_l1 {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hpos : ∀ x : EuclideanSpace ℂ n,
       0 ≤ (inner ℂ x (WithLp.toLp (2:ENNReal)
            ((P-Q) *ᵥ x.ofLp))).re) :
    (∑ k : Fin (Fintype.card n),
        |hP.eigenvalues₀ k - hQ.eigenvalues₀ k|) =
       (P-Q).trace.re := by
  classical
  calc
    (∑ k : Fin (Fintype.card n),
        |hP.eigenvalues₀ k - hQ.eigenvalues₀ k|) =
        ∑ k : Fin (Fintype.card n),
          (hP.eigenvalues₀ k - hQ.eigenvalues₀ k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [abs_of_nonneg]
            exact sub_nonneg.mpr (lidskii_loewner_eigen hP hQ hpos k)
    _ = (∑ k : Fin (Fintype.card n), hP.eigenvalues₀ k) -
        (∑ k : Fin (Fintype.card n), hQ.eigenvalues₀ k) := by
          rw [← Finset.sum_sub_distrib]
    _ = (P-Q).trace.re := by
          rw [← lidskii_trace_re hP, ← lidskii_trace_re hQ,
            Matrix.trace_sub, Complex.sub_re]



noncomputable def lidskii_cdiag {n : Type*} [Fintype n] [DecidableEq n]
 (U : Matrix.unitaryGroup n ℂ) (d:n→ℝ) : Matrix n n ℂ :=
 (U:Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) * star (U:Matrix n n ℂ)
lemma lidskii_cdiag_herm {n : Type*} [Fintype n] [DecidableEq n]
 (U : Matrix.unitaryGroup n ℂ) (d:n→ℝ) : (lidskii_cdiag U d).IsHermitian := by
  have hD : (diagonal (fun i => (d i : ℂ)) : Matrix n n ℂ).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    exact Complex.conj_ofReal _
  change star ((U:Matrix n n ℂ) * diagonal (fun i => (d i:ℂ)) * star (U:Matrix n n ℂ)) =
     ((U:Matrix n n ℂ) * diagonal (fun i => (d i:ℂ)) * star (U:Matrix n n ℂ))
  rw [Matrix.star_mul, Matrix.star_mul, star_star]
  change star (diagonal (fun i => (d i:ℂ)) : Matrix n n ℂ) = _ at hD
  rw [hD]
  rw [Matrix.mul_assoc]

lemma lidskii_cdiag_trace {n : Type*} [Fintype n] [DecidableEq n]
 (U : Matrix.unitaryGroup n ℂ) (d:n→ℝ) :
   (lidskii_cdiag U d).trace.re = ∑ i : n, d i := by
  classical
  unfold lidskii_cdiag
  rw [Matrix.trace_mul_cycle]
  -- ((star U)*U*D)
  have hu0 := Unitary.star_mul_self U
  have hu : star (U:Matrix n n ℂ) * (U:Matrix n n ℂ) = 1 := by
    simpa using congrArg (fun V : Matrix.unitaryGroup n ℂ => (V : Matrix n n ℂ)) hu0
  rw [hu, one_mul]
  rw [Matrix.trace_diagonal]
  -- re
  simp
lemma lidskii_cdiag_ray {n : Type*} [Fintype n] [DecidableEq n]
 (U : Matrix.unitaryGroup n ℂ) (d:n→ℝ)
 (x : EuclideanSpace ℂ n) :
 (inner ℂ x (WithLp.toLp (2:ENNReal) (lidskii_cdiag U d *ᵥ x.ofLp))).re =
    ∑ i : n, d i * ‖((star (U:Matrix n n ℂ)) *ᵥ x.ofLp) i‖ ^ 2 := by
  classical
  let u : Matrix n n ℂ := (U : Matrix n n ℂ)
  let v : n → ℂ := x.ofLp
  let y : n → ℂ := star u *ᵥ v
  have hx : x = WithLp.toLp (2:ENNReal) v := by
    rfl
  have hy : y = star u *ᵥ v := rfl
  -- compute transforms
  have hw : (lidskii_cdiag U d) *ᵥ v =
       u *ᵥ ((diagonal (fun i => (d i : ℂ))) *ᵥ y) := by
    simp [lidskii_cdiag, u, y, v, ← Matrix.mulVec_mulVec]
  -- helper: vecMul relation
  have hy' : (star v ᵥ* u) = star y := by
    -- mulVec_conjTranspose u v : uᴴ *ᵥ v = star (star v ᵥ* u)
    have H := Matrix.mulVec_conjTranspose u v
    -- star u = conjTranspose u
    -- need
    -- H lhs uses uᴴ = star u
    change star u *ᵥ v = star (star v ᵥ* u) at H
    -- y = ...
    have H' : y = star (star v ᵥ* u) := by simpa [y] using H
    -- take star both sides
    -- star on functions
    have K := congrArg star H'
    -- star y = star (star (...))
    have K' : star y = (star v ᵥ* u) := by simpa using K
    exact K'.symm
  -- goal inner
  rw [hx]
  -- change via inner_toLp
  change (dotProduct ((lidskii_cdiag U d) *ᵥ v) (star v)).re = _
  rw [hw]
  -- commute dot product then dotProduct_mulVec
  rw [dotProduct_comm]
  rw [Matrix.dotProduct_mulVec]
  -- currently `(star v ᵥ* u) ⬝ᵥ _`
  rw [hy']
  -- expand dot product and diagonal
  unfold dotProduct
  -- real part sum
  rw [Complex.re_sum]
  -- goal each term via sum_congr?
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.mulVec_diagonal]
  -- expression re of ...
  dsimp [y]
  -- reorder to use norm square
  let yi : ℂ := (star u *ᵥ v) i
  change (star yi * ((d i : ℂ) * yi)).re = d i * ‖(star (U:Matrix n n ℂ) *ᵥ v) i‖ ^ 2
  have hrearr : star yi * ((d i : ℂ) * yi) = (d i : ℂ) * (star yi * yi) := by ring
  rw [hrearr]
  change ((d i : ℂ) * ((starRingEnd ℂ) yi * yi)).re = _
  rw [Complex.conj_mul']
  rw [← Complex.ofReal_pow]
  -- try now
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  change d i * ‖((star (U:Matrix n n ℂ)) *ᵥ v) i‖ ^ 2 = _
  rfl
lemma lidskii_cdiag_pos {n : Type*} [Fintype n] [DecidableEq n]
 (U : Matrix.unitaryGroup n ℂ) (d:n→ℝ) (hd:∀ i, 0 ≤ d i)
 (x : EuclideanSpace ℂ n) :
 0 ≤ (inner ℂ x (WithLp.toLp (2:ENNReal) (lidskii_cdiag U d *ᵥ x.ofLp))).re := by
  rw [lidskii_cdiag_ray]
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hd i) (sq_nonneg _))
lemma lidskii_cdiag_sub {n : Type*} [Fintype n] [DecidableEq n]
 (U : Matrix.unitaryGroup n ℂ) (d₁ d₂:n→ℝ) :
 lidskii_cdiag U d₁ - lidskii_cdiag U d₂ = lidskii_cdiag U (fun i => d₁ i - d₂ i) := by
  classical
  unfold lidskii_cdiag
  -- algebra pull
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h]
lemma lidskii_cdiag_eig {n : Type*} [Fintype n] [DecidableEq n]
 {M: Matrix n n ℂ} (h:M.IsHermitian) :
 lidskii_cdiag h.eigenvectorUnitary h.eigenvalues = M := by
  have hs := h.spectral_theorem
  -- M = U * diag (RCLike.ofReal ∘ eigenvalues)
  symm
  -- hs :
  simpa [lidskii_cdiag, Function.comp_def, Unitary.conjStarAlgAut_apply] using hs
lemma lidskii_real_max_sub (r:ℝ) : max r 0 - max (-r) 0 = r := by
  by_cases h : 0 ≤ r
  · have hn : -r ≤ 0 := neg_nonpos.mpr h
    simp [max_eq_left h, max_eq_right hn]
  · have h' : r ≤ 0 := le_of_not_ge h
    have hn : 0 ≤ -r := neg_nonneg.mpr h'
    simp [max_eq_right h', max_eq_left hn]
lemma lidskii_real_max_add (r:ℝ) : max r 0 + max (-r) 0 = |r| := by
  by_cases h : 0 ≤ r
  · have hn : -r ≤ 0 := neg_nonpos.mpr h
    simp [max_eq_left h, max_eq_right hn, abs_of_nonneg h]
  · have h' : r ≤ 0 := le_of_not_ge h
    have hn : 0 ≤ -r := neg_nonneg.mpr h'
    rw [max_eq_right h', max_eq_left hn, abs_of_nonpos h']
    -- 0 + -r
    simp

noncomputable def lidskii_posM {n:Type*} [Fintype n] [DecidableEq n]
 {M:Matrix n n ℂ} (h:M.IsHermitian) : Matrix n n ℂ :=
 lidskii_cdiag h.eigenvectorUnitary (fun i => max (h.eigenvalues i) 0)
noncomputable def lidskii_negM {n:Type*} [Fintype n] [DecidableEq n]
 {M:Matrix n n ℂ} (h:M.IsHermitian) : Matrix n n ℂ :=
 lidskii_cdiag h.eigenvectorUnitary (fun i => max (- h.eigenvalues i) 0)
lemma lidskii_pos_sub_neg {n:Type*} [Fintype n] [DecidableEq n]
 {M:Matrix n n ℂ} (h:M.IsHermitian) : lidskii_posM h - lidskii_negM h = M := by
  rw [lidskii_posM, lidskii_negM, lidskii_cdiag_sub]
  have H : (fun i : n => max (h.eigenvalues i) 0 - max (-h.eigenvalues i) 0) = h.eigenvalues := by
     funext i
     exact lidskii_real_max_sub _
  rw [H, lidskii_cdiag_eig]
lemma lidskii_pos_herm {n:Type*} [Fintype n] [DecidableEq n]
 {M:Matrix n n ℂ} (h:M.IsHermitian) : (lidskii_posM h).IsHermitian := lidskii_cdiag_herm _ _
lemma lidskii_neg_herm {n:Type*} [Fintype n] [DecidableEq n]
 {M:Matrix n n ℂ} (h:M.IsHermitian) : (lidskii_negM h).IsHermitian := lidskii_cdiag_herm _ _
lemma lidskii_pos_pos {n:Type*} [Fintype n] [DecidableEq n]
 {M:Matrix n n ℂ} (h:M.IsHermitian) (x:EuclideanSpace ℂ n) :
 0 ≤ (inner ℂ x (WithLp.toLp (2:ENNReal) (lidskii_posM h *ᵥ x.ofLp))).re := by
   unfold lidskii_posM
   apply lidskii_cdiag_pos
   intro i
   exact le_max_right _ _
lemma lidskii_my_neg_pos {n:Type*} [Fintype n] [DecidableEq n]
 {M:Matrix n n ℂ} (h:M.IsHermitian) (x:EuclideanSpace ℂ n) :
 0 ≤ (inner ℂ x (WithLp.toLp (2:ENNReal) (lidskii_negM h *ᵥ x.ofLp))).re := by
   unfold lidskii_negM
   apply lidskii_cdiag_pos
   intro i
   exact le_max_right _ _
lemma lidskii_pos_trace {n:Type*} [Fintype n] [DecidableEq n]
 {M:Matrix n n ℂ} (h:M.IsHermitian) :
 (lidskii_posM h).trace.re = ∑ i:n, max (h.eigenvalues i) 0 := by
 unfold lidskii_posM
 exact lidskii_cdiag_trace _ _
lemma lidskii_neg_trace {n:Type*} [Fintype n] [DecidableEq n]
 {M:Matrix n n ℂ} (h:M.IsHermitian) :
 (lidskii_negM h).trace.re = ∑ i:n, max (-h.eigenvalues i) 0 := by
 unfold lidskii_negM
 exact lidskii_cdiag_trace _ _
lemma lidskii_trace_sum_abs {n:Type*} [Fintype n] [DecidableEq n]
 {M:Matrix n n ℂ} (h:M.IsHermitian) :
 (lidskii_posM h).trace.re + (lidskii_negM h).trace.re =
    ∑ i : Fin (Fintype.card n), |h.eigenvalues₀ i| := by
 rw [lidskii_pos_trace, lidskii_neg_trace]
 rw [← Finset.sum_add_distrib]
 -- replace scalar
 have H : (∑ i:n, (max (h.eigenvalues i) 0 + max (-h.eigenvalues i) 0)) = ∑ i:n, |h.eigenvalues i| := by
  apply Finset.sum_congr rfl
  intro i hi
  exact lidskii_real_max_add _
 rw [H]
 -- reorder
 let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
 change (∑ i:n, |h.eigenvalues₀ (e.symm i)|) = _
 exact Equiv.sum_comp e.symm (fun k : Fin (Fintype.card n) => |h.eigenvalues₀ k|)



/-- Simultaneous spectral l1 perturbation via the positive and negative
spectral parts of the Hermitian difference.  Splitting the difference into
two positive matrices reduces the general case to monotonicity and trace. -/
lemma lidskii_spectral_l1 {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤
       ∑ j : Fin (Fintype.card n), |(hA.sub hB).eigenvalues₀ j| := by
  classical
  have hC : (A-B).IsHermitian := hA.sub hB
  -- add the positive part to B.  It is above both endpoints.
  let T : Matrix n n ℂ := B + lidskii_posM hC
  have hT : T.IsHermitian := hB.add (lidskii_pos_herm hC)
  have hTA : T - A = lidskii_negM hC := by
    change B + lidskii_posM hC - A = _
    have hc := lidskii_pos_sub_neg hC
    -- turn `B + p - A` into `p - (A-B)` and use the decomposition
    calc
      B + lidskii_posM hC - A = lidskii_posM hC - (A-B) := by abel
      _ = lidskii_posM hC -
            (lidskii_posM hC - lidskii_negM hC) := by rw [hc]
      _ = lidskii_negM hC := by abel
  have hTB : T - B = lidskii_posM hC := by
    change B + lidskii_posM hC - B = _
    abel
  have hTApos : ∀ x : EuclideanSpace ℂ n,
       0 ≤ (inner ℂ x (WithLp.toLp (2:ENNReal)
            ((T-A) *ᵥ x.ofLp))).re := by
    intro x
    rw [hTA]
    exact lidskii_my_neg_pos hC x
  have hTBpos : ∀ x : EuclideanSpace ℂ n,
       0 ≤ (inner ℂ x (WithLp.toLp (2:ENNReal)
            ((T-B) *ᵥ x.ofLp))).re := by
    intro x
    rw [hTB]
    exact lidskii_pos_pos hC x
  have h1 := lidskii_loewner_l1 hT hA hTApos
  have h2 := lidskii_loewner_l1 hT hB hTBpos
  -- ordinary scalar triangle inequality, with the same intermediate
  -- eigenvalue at each ordered index
  have htri :
      (∑ j : Fin (Fintype.card n),
        |hA.eigenvalues₀ j - hB.eigenvalues₀ j|) ≤
        (∑ j : Fin (Fintype.card n),
          |hT.eigenvalues₀ j - hA.eigenvalues₀ j|) +
        (∑ j : Fin (Fintype.card n),
          |hT.eigenvalues₀ j - hB.eigenvalues₀ j|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    calc
      |hA.eigenvalues₀ j - hB.eigenvalues₀ j| =
          |(hA.eigenvalues₀ j - hT.eigenvalues₀ j) +
             (hT.eigenvalues₀ j - hB.eigenvalues₀ j)| := by
                congr 1 <;> ring
      _ ≤ |hA.eigenvalues₀ j - hT.eigenvalues₀ j| +
            |hT.eigenvalues₀ j - hB.eigenvalues₀ j| :=
              abs_add_le _ _
      _ = |hT.eigenvalues₀ j - hA.eigenvalues₀ j| +
            |hT.eigenvalues₀ j - hB.eigenvalues₀ j| := by
              rw [abs_sub_comm (hA.eigenvalues₀ j) (hT.eigenvalues₀ j)]
  calc
    (∑ j : Fin (Fintype.card n),
      |hA.eigenvalues₀ j - hB.eigenvalues₀ j|) ≤
        (∑ j : Fin (Fintype.card n),
          |hT.eigenvalues₀ j - hA.eigenvalues₀ j|) +
        (∑ j : Fin (Fintype.card n),
          |hT.eigenvalues₀ j - hB.eigenvalues₀ j|) := htri
    _ = (T-A).trace.re + (T-B).trace.re := by rw [h1, h2]
    _ = (lidskii_negM hC).trace.re + (lidskii_posM hC).trace.re := by
          rw [hTA, hTB]
    _ = (lidskii_posM hC).trace.re + (lidskii_negM hC).trace.re := by
          rw [add_comm]
    _ = (∑ j : Fin (Fintype.card n), |hC.eigenvalues₀ j|) :=
          lidskii_trace_sum_abs hC

/-ResultProofDefinitionsEnd-/


theorem lidskii_last {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤
      ∑ i, ∑ j, ‖A i j - B i j‖ := by
  -- After the perturbation estimate, the passage from the Hermitian
  -- difference to entries is independent of any comparison of spectra.
  have hC : (A - B).IsHermitian := hA.sub hB
  calc
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤
        ∑ j : Fin (Fintype.card n), |hC.eigenvalues₀ j| := by
          classical
          by_cases hn : Fintype.card n = 0
          · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
            haveI : IsEmpty (Fin (Fintype.card n)) := by
              simpa [hn] using (inferInstance : IsEmpty (Fin 0))
            simp
          · -- Already the individual terms are controlled, by the
            -- min--max lemmas above; simultaneous Ky Fan control is the
            -- remaining perturbative step.
            have hone (j : Fin (Fintype.card n)) :
                |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤
                  ∑ i : Fin (Fintype.card n), |hC.eigenvalues₀ i| := by
              exact lidskii_weyl_l1 hA hB j
            by_cases hsmall : Fintype.card n = 1
            · let j0 : Fin (Fintype.card n) :=
                ⟨0, Nat.zero_lt_of_ne_zero hn⟩
              have hu : (Finset.univ : Finset (Fin (Fintype.card n))) =
                  {j0} := by
                ext j
                have hjv : j.val = 0 := by
                  have hj := j.isLt
                  omega
                have hj' : j = j0 := Fin.ext hjv
                simp [hj']
              -- there is only one term, so the pointwise estimate is
              -- exactly the simultaneous one.
              simpa [hu] using (hone j0)
            · -- Pointwise comparison alone introduces a factor equal to
              -- the dimension as soon as two indices are present.  The
              -- remaining step is the simultaneous Ky Fan/Lidskii partial
              -- sum comparison.
              exact lidskii_spectral_l1 hA hB
    _ ≤ ∑ i : n, ∑ j : n, ‖(A - B) i j‖ :=
      lidskii_one_matrix₀ hC
    _ = ∑ i : n, ∑ j : n, ‖A i j - B i j‖ := by
      simp [Matrix.sub_apply]


end Submission
