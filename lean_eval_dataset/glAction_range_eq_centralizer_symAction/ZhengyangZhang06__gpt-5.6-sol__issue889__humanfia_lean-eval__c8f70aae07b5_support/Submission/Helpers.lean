import ChallengeDeps

open LeanEval.RepresentationTheory
open Module
open scoped Polynomial TensorProduct

namespace Submission.Helpers

private def piProdEquiv (ι α β : Type*) : (ι → α × β) ≃ (ι → α) × (ι → β) where
  toFun f := (fun i ↦ (f i).1, fun i ↦ (f i).2)
  invFun f i := (f.1 i, f.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] private theorem piProdEquiv_apply_fst {ι α β : Type*} (f : ι → α × β) :
    ((piProdEquiv ι α β) f).1 = fun i ↦ (f i).1 :=
  rfl

@[simp] private theorem piProdEquiv_apply_snd {ι α β : Type*} (f : ι → α × β) :
    ((piProdEquiv ι α β) f).2 = fun i ↦ (f i).2 :=
  rfl

noncomputable def tensorEndEquiv {R M ι : Type*} [Field R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (k : ℕ) :
    (⨂[R]^k (Module.End R M)) ≃ₗ[R] Module.End R (⨂[R]^k M) := by
  classical
  exact (Basis.piTensorProduct (fun _ : Fin k ↦ b.end)).equiv
    (Basis.end (Basis.piTensorProduct (fun _ : Fin k ↦ b))) (piProdEquiv (Fin k) ι ι)

theorem tensorEndEquiv_eq_piTensorHomMap {R M ι : Type*} [Field R]
    [AddCommGroup M] [Module R M] [Fintype ι] (b : Module.Basis ι R M) (k : ℕ) :
    (tensorEndEquiv b k).toLinearMap = PiTensorProduct.piTensorHomMap := by
  classical
  apply (Basis.piTensorProduct (fun _ : Fin k ↦ b.end)).ext
  intro p
  change (tensorEndEquiv b k) ((Basis.piTensorProduct (fun _ : Fin k ↦ b.end)) p) = _
  rw [tensorEndEquiv, Basis.equiv_apply, Basis.piTensorProduct_apply]
  apply (Basis.piTensorProduct (fun _ : Fin k ↦ b)).ext
  intro q
  rw [Module.Basis.end_apply_apply]
  simp only [piProdEquiv_apply_fst, piProdEquiv_apply_snd, Basis.piTensorProduct_apply,
    PiTensorProduct.piTensorHomMap_tprod_tprod, Module.Basis.end_apply_apply]
  by_cases h : (fun i ↦ (p i).2) = q
  · subst q
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, (p i).2 ≠ q i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    symm
    apply (PiTensorProduct.tprod R).map_coord_zero i
    simp [hi]

noncomputable def tensorPolynomial {R E ι : Type*} [CommRing R] [AddCommGroup E]
    [Module R E] [Fintype ι] (b : Module.Basis ι R E) (k : ℕ)
    (φ : Module.Dual R (⨂[R]^k E)) : MvPolynomial ι R :=
  ∑ f : Fin k → ι,
    MvPolynomial.C (φ ((Basis.piTensorProduct (fun _ : Fin k ↦ b)) f)) *
      ∏ i : Fin k, MvPolynomial.X (f i)

theorem eval_tensorPolynomial {R E ι : Type*} [CommRing R] [AddCommGroup E]
    [Module R E] [Fintype ι] (b : Module.Basis ι R E) (k : ℕ)
    (φ : Module.Dual R (⨂[R]^k E)) (c : ι → R) :
    MvPolynomial.eval c (tensorPolynomial b k φ) =
      φ ((PiTensorProduct.tprod R) (fun _ : Fin k ↦ ∑ j : ι, c j • b j)) := by
  classical
  rw [tensorPolynomial, map_sum, (PiTensorProduct.tprod R).map_sum, map_sum φ]
  apply Finset.sum_congr rfl
  intro f _
  rw [map_mul, MvPolynomial.eval_C, map_prod, Basis.piTensorProduct_apply,
    (PiTensorProduct.tprod R).map_smul_univ, LinearMap.map_smul]
  simp only [MvPolynomial.eval_X]
  rw [mul_comm, smul_eq_mul]

theorem isHomogeneous_tensorPolynomial {R E ι : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [Fintype ι] (b : Module.Basis ι R E) (k : ℕ)
    (φ : Module.Dual R (⨂[R]^k E)) :
    (tensorPolynomial b k φ).IsHomogeneous k := by
  classical
  rw [tensorPolynomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro f _
  have hp : (∏ i : Fin k, MvPolynomial.X (f i) : MvPolynomial ι R).IsHomogeneous k := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i : Fin k ↦ MvPolynomial.X (f i)) (fun _ ↦ 1)
      (fun i _ ↦ MvPolynomial.isHomogeneous_X (R := R) (f i))
  exact hp.C_mul _

theorem eval₂_smul_of_isHomogeneous {R S σ : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (p : MvPolynomial σ R) (n : ℕ)
    (hp : p.IsHomogeneous n) (c : S) (g : σ → S) :
    MvPolynomial.eval₂ f (fun i ↦ c * g i) p =
      c ^ n * MvPolynomial.eval₂ f g p := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdegree : ∑ i ∈ d.support, d i = n := by
    simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum]
      using hp (MvPolynomial.mem_support_iff.mp hd)
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdegree]
  ring

noncomputable def tensorLinePolynomial {R K E ι : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [AddCommGroup E] [Module R E] [Fintype ι]
    (b : Module.Basis ι R E) (k : ℕ) (φ : Module.Dual R (⨂[R]^k E))
    (a d : ι → K) : K[X] :=
  ∑ f : Fin k → ι,
    Polynomial.C (algebraMap R K (φ ((Basis.piTensorProduct (fun _ : Fin k ↦ b)) f))) *
      ∏ i : Fin k, (Polynomial.C (a (f i)) + Polynomial.X * Polynomial.C (d (f i)))

theorem eval_tensorLinePolynomial {R K E ι : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [AddCommGroup E] [Module R E] [Fintype ι]
    (b : Module.Basis ι R E) (k : ℕ) (φ : Module.Dual R (⨂[R]^k E))
    (a d : ι → K) (t : K) :
    Polynomial.eval t (tensorLinePolynomial b k φ a d) =
      MvPolynomial.eval (fun j ↦ a j + t * d j)
        ((tensorPolynomial b k φ).map (algebraMap R K)) := by
  classical
  simp [tensorLinePolynomial, tensorPolynomial]
  change (Polynomial.evalRingHom t) _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [map_mul]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C]
  change _ * (Polynomial.evalRingHom t) _ = _
  rw [map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]
  rw [mul_comm (d (f i)) t]

theorem natDegree_tensorLinePolynomial_le {R K E ι : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [AddCommGroup E] [Module R E] [Fintype ι]
    (b : Module.Basis ι R E) (k : ℕ) (φ : Module.Dual R (⨂[R]^k E))
    (a d : ι → K) : (tensorLinePolynomial b k φ a d).natDegree ≤ k := by
  classical
  rw [tensorLinePolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le Finset.univ
  intro f _
  refine Polynomial.natDegree_mul_le.trans ?_
  simp only [Polynomial.natDegree_C, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin k, 1 := by
      apply Finset.sum_le_sum
      intro i _
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      apply max_le
      · simp
      · calc
          (Polynomial.X * Polynomial.C (d (f i))).natDegree ≤
              Polynomial.X.natDegree + (Polynomial.C (d (f i))).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 1 + 0 := Nat.add_le_add Polynomial.natDegree_X_le (by simp)
          _ = 1 := by simp
    _ = k := by simp

theorem natCast_fin_succ_injective {R : Type*} [Field R] (k : ℕ)
    [Invertible (k.factorial : R)] :
    Function.Injective (fun i : Fin (k + 1) ↦ (i : R)) := by
  have aux {a b : ℕ} (hab : a < b) (hb : b ≤ k) : (a : R) ≠ (b : R) := by
    intro heq
    have hdpos : 0 < b - a := Nat.sub_pos_of_lt hab
    have hdle : b - a ≤ k := (Nat.sub_le b a).trans hb
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hdpos hdle
    have hdzero : ((b - a : ℕ) : R) = 0 := by
      rw [Nat.cast_sub hab.le]
      exact sub_eq_zero.mpr heq.symm
    apply Invertible.ne_zero (k.factorial : R)
    rw [hc, Nat.cast_mul, hdzero, zero_mul]
  intro i j hij
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact aux hlt (Nat.lt_succ_iff.mp j.isLt) hij
  · exact aux hgt (Nat.lt_succ_iff.mp i.isLt) hij.symm

theorem polynomial_eq_zero_of_eval_natCast {R K : Type*} [Field R] [Field K]
    [Algebra R K] (k : ℕ) [Invertible (k.factorial : R)] (p : K[X])
    (hdeg : p.natDegree ≤ k)
    (heval : ∀ i : Fin (k + 1), p.eval (algebraMap R K (i : R)) = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    ((FaithfulSMul.algebraMap_injective R K).comp (natCast_fin_succ_injective k)) heval
  simpa using Nat.lt_succ_of_le hdeg

structure TransvectionIndex (ι : Type*) where
  (i j : ι)
  hij : i ≠ j

def transvectionProd {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι] :
    (n : ℕ) → (Fin n → TransvectionIndex ι) → (Fin n → K) → Matrix ι ι K
  | 0, _, _ => 1
  | n + 1, s, c =>
      Matrix.transvection (s 0).i (s 0).j (c 0) *
        transvectionProd n (fun i ↦ s i.succ) (fun i ↦ c i.succ)

theorem mul_transvection_mul_eq_add_smul {K ι : Type*} [CommRing K] [Fintype ι]
    [DecidableEq ι] (A B : Matrix ι ι K) (i j : ι) (t : K) :
    A * Matrix.transvection i j t * B =
      A * B + t • (A * Matrix.single i j 1 * B) := by
  have hs : Matrix.single i j t = t • Matrix.single i j (1 : K) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  rw [hs]
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

theorem eval_tensorPolynomial_transvectionProd {R K E ι : Type*} [Field R] [Field K]
    [Algebra R K] [AddCommGroup E] [Module R E] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis (ι × ι) R E) (k : ℕ) [Invertible (k.factorial : R)]
    (φ : Module.Dual R (⨂[R]^k E)) (n : ℕ) (s : Fin n → TransvectionIndex ι)
    (A : Matrix ι ι K)
    (hbase : ∀ c : Fin n → R,
      MvPolynomial.eval
          (fun ij ↦ (A * transvectionProd n s (fun i ↦ algebraMap R K (c i))) ij.1 ij.2)
          ((tensorPolynomial b k φ).map (algebraMap R K)) = 0) :
    ∀ c : Fin n → K,
      MvPolynomial.eval (fun ij ↦ (A * transvectionProd n s c) ij.1 ij.2)
        ((tensorPolynomial b k φ).map (algebraMap R K)) = 0 := by
  induction n generalizing A with
  | zero =>
      intro c
      simpa [transvectionProd] using hbase (fun i ↦ Fin.elim0 i)
  | succ n ih =>
      intro c
      let s₀ := s 0
      let s' : Fin n → TransvectionIndex ι := fun i ↦ s i.succ
      let c' : Fin n → K := fun i ↦ c i.succ
      let B := transvectionProd n s' c'
      have hroots (r : R) :
          MvPolynomial.eval
              (fun ij ↦ (A * Matrix.transvection s₀.i s₀.j (algebraMap R K r) * B)
                ij.1 ij.2)
              ((tensorPolynomial b k φ).map (algebraMap R K)) = 0 := by
        apply ih s' (A * Matrix.transvection s₀.i s₀.j (algebraMap R K r))
        · intro d
          simpa [s₀, s', transvectionProd, Matrix.mul_assoc] using hbase (Fin.cases r d)
      let a : ι × ι → K := fun ij ↦ (A * B) ij.1 ij.2
      let d : ι × ι → K := fun ij ↦
        ((A * Matrix.single s₀.i s₀.j 1 * B : Matrix ι ι K) ij.1 ij.2)
      let q := tensorLinePolynomial b k φ a d
      have hq : q = 0 := by
        apply polynomial_eq_zero_of_eval_natCast (R := R) (K := K) k q
          (natDegree_tensorLinePolynomial_le b k φ a d)
        intro u
        rw [eval_tensorLinePolynomial]
        have hr := hroots (u : R)
        rw [mul_transvection_mul_eq_add_smul] at hr
        simpa only [a, d, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using hr
      have hqc : Polynomial.eval (c 0) q = 0 := by rw [hq, Polynomial.eval_zero]
      change Polynomial.eval (c 0) (tensorLinePolynomial b k φ a d) = 0 at hqc
      rw [eval_tensorLinePolynomial] at hqc
      rw [transvectionProd, ← Matrix.mul_assoc]
      rw [mul_transvection_mul_eq_add_smul]
      simpa only [a, d, B, c', s₀, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using hqc

def transvectionIndexOf {K ι : Type*} (t : Matrix.TransvectionStruct ι K) :
    TransvectionIndex ι :=
  ⟨t.i, t.j, t.hij⟩

theorem transvectionProd_list {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.TransvectionStruct ι K)) :
    transvectionProd L.length (fun i ↦ transvectionIndexOf (L.get i))
        (fun i ↦ (L.get i).c) =
      (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp [transvectionProd]
  | cons t L ih =>
      change Matrix.transvection t.i t.j t.c *
          transvectionProd L.length (fun i ↦ transvectionIndexOf (L.get i))
            (fun i ↦ (L.get i).c) =
        t.toMatrix * (L.map Matrix.TransvectionStruct.toMatrix).prod
      rw [ih]
      rfl

theorem transvectionProd_map {R K ι : Type*} [CommRing R] [CommRing K]
    [Fintype ι] [DecidableEq ι] (f : R →+* K) (n : ℕ)
    (s : Fin n → TransvectionIndex ι) (c : Fin n → R) :
    (transvectionProd n s c).map f =
      transvectionProd n s (fun i ↦ f (c i)) := by
  induction n with
  | zero => simp [transvectionProd]
  | succ n ih =>
      have ht : (Matrix.transvection (s 0).i (s 0).j (c 0)).map f =
          Matrix.transvection (s 0).i (s 0).j (f (c 0)) := by
        ext i j
        by_cases h : (s 0).i = i ∧ (s 0).j = j <;>
          simp [Matrix.transvection, Matrix.one_apply, h]
      rw [transvectionProd, Matrix.map_mul, transvectionProd, ih]
      rw [ht]

theorem det_transvectionProd {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (n : ℕ) (s : Fin n → TransvectionIndex ι) (c : Fin n → K) :
    Matrix.det (transvectionProd n s c) = 1 := by
  induction n with
  | zero => simp [transvectionProd]
  | succ n ih =>
      rw [transvectionProd, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ (s 0).hij]
      simpa using ih (fun i ↦ s i.succ) (fun i ↦ c i.succ)

theorem eval_map_tensorPolynomial_smul {R K E ι : Type*} [CommRing R] [CommRing K]
    [AddCommGroup E] [Module R E] [Fintype ι] (f : R →+* K)
    (b : Module.Basis ι R E) (k : ℕ) (φ : Module.Dual R (⨂[R]^k E))
    (c : K) (a : ι → R) :
    MvPolynomial.eval (fun i ↦ c * f (a i)) ((tensorPolynomial b k φ).map f) =
      c ^ k * f (MvPolynomial.eval a (tensorPolynomial b k φ)) := by
  rw [MvPolynomial.eval_map]
  calc
    MvPolynomial.eval₂ f (fun i ↦ c * f (a i)) (tensorPolynomial b k φ) =
        c ^ k * MvPolynomial.eval₂ f (fun i ↦ f (a i)) (tensorPolynomial b k φ) :=
      eval₂_smul_of_isHomogeneous f _ k (isHomogeneous_tensorPolynomial b k φ) c _
    _ = c ^ k * f (MvPolynomial.eval a (tensorPolynomial b k φ)) := by
      rw [MvPolynomial.eval₂_comp]
      rfl

theorem triple_transvection_apply {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (i j : ι) (hij : i ≠ j) (a : K) (ha : a ≠ 0) (x y : ι) :
    (Matrix.transvection i j a * Matrix.transvection j i (-a⁻¹) *
        Matrix.transvection i j a) x y =
      if x = i then (if y = j then a else 0)
      else if x = j then (if y = i then -a⁻¹ else 0)
      else if x = y then 1 else 0 := by
  by_cases hyj : y = j
  · subst y
    rw [Matrix.mul_transvection_apply_same (i := i) (j := j) x a]
    rw [Matrix.mul_transvection_apply_of_ne (i := j) (j := i) x j hij.symm (-a⁻¹)]
    rw [Matrix.mul_transvection_apply_same (i := j) (j := i) x (-a⁻¹)]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      simp_all [Matrix.transvection, eq_comm]
  · rw [Matrix.mul_transvection_apply_of_ne (i := i) (j := j) x y hyj a]
    by_cases hyi : y = i
    · subst y
      rw [Matrix.mul_transvection_apply_same (i := j) (j := i) x (-a⁻¹)]
      by_cases hxi : x = i <;> by_cases hxj : x = j <;>
        simp_all [Matrix.transvection, eq_comm]
    · rw [Matrix.mul_transvection_apply_of_ne (i := j) (j := i) x y hyi (-a⁻¹)]
      by_cases hxi : x = i <;> by_cases hxj : x = j <;>
        simp_all [Matrix.transvection, Matrix.one_apply, eq_comm]

theorem diagonal_two_eq_transvections {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (i j : ι) (hij : i ≠ j) (a : K) (ha : a ≠ 0) :
    Matrix.diagonal (fun x ↦ if x = i then a else if x = j then a⁻¹ else 1) =
      Matrix.transvection i j a * Matrix.transvection j i (-a⁻¹) *
        Matrix.transvection i j a * Matrix.transvection i j (-1) *
          Matrix.transvection j i 1 * Matrix.transvection i j (-1) := by
  ext x y
  change (if x = y then (if x = i then a else if x = j then a⁻¹ else 1) else 0) = _
  rw [show
    Matrix.transvection i j a * Matrix.transvection j i (-a⁻¹) *
          Matrix.transvection i j a * Matrix.transvection i j (-1) *
            Matrix.transvection j i 1 * Matrix.transvection i j (-1) =
      (Matrix.transvection i j a * Matrix.transvection j i (-a⁻¹) *
          Matrix.transvection i j a) *
        (Matrix.transvection i j (-1) * Matrix.transvection j i 1 *
          Matrix.transvection i j (-1)) by simp only [Matrix.mul_assoc]]
  have hfirst (z w : ι) := triple_transvection_apply i j hij a ha z w
  have hsecond (z w : ι) :
      (Matrix.transvection i j (-1) * Matrix.transvection j i 1 *
          Matrix.transvection i j (-1) : Matrix ι ι K) z w =
        if z = i then (if w = j then -1 else 0)
        else if z = j then (if w = i then 1 else 0)
        else if z = w then 1 else 0 := by
    simpa using triple_transvection_apply i j hij (-1 : K) (by simp) z w
  rw [Matrix.mul_apply]
  simp only [hfirst, hsecond]
  by_cases hxi : x = i
  · subst x
    by_cases hyi : y = i <;> by_cases hyj : y = j <;>
      simp_all [eq_comm, Finset.sum_ite]
  · by_cases hxj : x = j
    · subst x
      by_cases hyi : y = i <;> by_cases hyj : y = j <;>
        simp_all [eq_comm]
    · by_cases hyi : y = i <;> by_cases hyj : y = j <;>
        by_cases hxy : x = y <;> simp_all [eq_comm, Finset.sum_ite]

def IsTransvectionProduct {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ L : List (Matrix.TransvectionStruct ι K),
    (L.map Matrix.TransvectionStruct.toMatrix).prod = A

theorem isTransvectionProduct_one {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] : IsTransvectionProduct (1 : Matrix ι ι K) := by
  exact ⟨[], by simp⟩

theorem isTransvectionProduct_transvection {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (i j : ι) (hij : i ≠ j) (c : K) :
    IsTransvectionProduct (Matrix.transvection i j c) := by
  exact ⟨[⟨i, j, hij, c⟩], by simp⟩

theorem IsTransvectionProduct.mul {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] {A B : Matrix ι ι K}
    (hA : IsTransvectionProduct A) (hB : IsTransvectionProduct B) :
    IsTransvectionProduct (A * B) := by
  obtain ⟨L, rfl⟩ := hA
  obtain ⟨L', rfl⟩ := hB
  exact ⟨L ++ L', by simp⟩

theorem isTransvectionProduct_diagonal_two {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (i j : ι) (hij : i ≠ j) (a : K) (ha : a ≠ 0) :
    IsTransvectionProduct
      (Matrix.diagonal (fun x ↦ if x = i then a else if x = j then a⁻¹ else 1)) := by
  rw [diagonal_two_eq_transvections i j hij a ha]
  exact (((((isTransvectionProduct_transvection i j hij a).mul
    (isTransvectionProduct_transvection j i hij.symm (-a⁻¹))).mul
      (isTransvectionProduct_transvection i j hij a)).mul
        (isTransvectionProduct_transvection i j hij (-1))).mul
          (isTransvectionProduct_transvection j i hij.symm 1)).mul
            (isTransvectionProduct_transvection i j hij (-1))

theorem isTransvectionProduct_list_prod {K ι α : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (L : List α) (f : α → Matrix ι ι K)
    (h : ∀ i ∈ L, IsTransvectionProduct (f i)) :
    IsTransvectionProduct (L.map f).prod := by
  induction L with
  | nil => simpa using (isTransvectionProduct_one (K := K) (ι := ι))
  | cons i L ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (h i (by simp)).mul (ih fun j hj ↦ h j (by simp [hj]))

theorem list_prod_diagonal {K ι α : Type*} [CommRing K] [Fintype ι]
    [DecidableEq ι] (L : List α) (d : α → ι → K) :
    (L.map fun i ↦ Matrix.diagonal (d i)).prod =
      Matrix.diagonal (fun x ↦ (L.map fun i ↦ d i x).prod) := by
  induction L with
  | nil => simp
  | cons i L ih => simp [ih, Matrix.diagonal_mul_diagonal]

theorem isTransvectionProduct_diagonal_of_det_eq_one {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (D : ι → K)
    (hdet : Matrix.det (Matrix.diagonal D) = 1) :
    IsTransvectionProduct (Matrix.diagonal D) := by
  classical
  by_cases hι : Nontrivial ι
  · letI : Nontrivial ι := hι
    let j : ι := Classical.choice (inferInstance : Nonempty ι)
    let s : Finset ι := Finset.univ.erase j
    let d : ι → ι → K := fun i x ↦
      if x = i then D i else if x = j then (D i)⁻¹ else 1
    have hprodD : ∏ i, D i = 1 := by simpa using hdet
    have hD_ne (i : ι) : D i ≠ 0 := by
      intro hi
      have hz : ∏ x, D x = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hprodD] at hz
      exact one_ne_zero hz
    have hfac (i : ι) (hi : i ∈ s.toList) :
        IsTransvectionProduct (Matrix.diagonal (d i)) := by
      have hij : i ≠ j := by simpa [s] using hi
      exact isTransvectionProduct_diagonal_two i j hij (D i) (hD_ne i)
    have hp : IsTransvectionProduct
        ((s.toList.map fun i ↦ Matrix.diagonal (d i)).prod) :=
      isTransvectionProduct_list_prod s.toList _ hfac
    have heq : (s.toList.map fun i ↦ Matrix.diagonal (d i)).prod =
        Matrix.diagonal D := by
      rw [list_prod_diagonal]
      congr 1
      funext x
      by_cases hx : x = j
      · subst x
        have hP : (∏ i ∈ s, D i) * D j = 1 := by
          calc
            (∏ i ∈ s, D i) * D j = ∏ i, D i := by
              simpa [s] using
                (Finset.prod_erase_mul Finset.univ D (Finset.mem_univ j))
            _ = 1 := hprodD
        calc
          (s.toList.map fun i ↦ d i j).prod = ∏ i ∈ s, (D i)⁻¹ := by
            rw [Finset.prod_map_toList]
            apply Finset.prod_congr rfl
            intro i hi
            have hij : i ≠ j := Finset.ne_of_mem_erase hi
            simp [d, Ne.symm hij]
          _ = (∏ i ∈ s, D i)⁻¹ := by rw [Finset.prod_inv_distrib]
          _ = D j := inv_eq_of_mul_eq_one_right hP
      · calc
          (s.toList.map fun i ↦ d i x).prod =
              ∏ i ∈ s, if x = i then D i else 1 := by
                simp [s, d, hx]
          _ = D x := by simp [s, hx]
    rwa [heq] at hp
  · haveI : Subsingleton ι := not_nontrivial_iff_subsingleton.mp hι
    cases isEmpty_or_nonempty ι with
    | inl h =>
        letI : IsEmpty ι := h
        have heq : Matrix.diagonal D = (1 : Matrix ι ι K) := Subsingleton.elim _ _
        rw [heq]
        exact isTransvectionProduct_one
    | inr h =>
        letI : Nonempty ι := h
        let j : ι := Classical.choice h
        have hDj : D j = 1 := by
          simpa [Matrix.det_eq_elem_of_subsingleton (Matrix.diagonal D) j] using hdet
        have heq : Matrix.diagonal D = (1 : Matrix ι ι K) := by
          ext x y
          have hxy : x = y := Subsingleton.elim _ _
          subst y
          have hxj : x = j := Subsingleton.elim _ _
          subst x
          simp [hDj]
        rw [heq]
        exact isTransvectionProduct_one

theorem isTransvectionProduct_of_det_eq_one {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : Matrix.det A = 1) :
    IsTransvectionProduct A := by
  apply Matrix.diagonal_transvection_induction IsTransvectionProduct A
  · intro D hD
    apply isTransvectionProduct_diagonal_of_det_eq_one D
    rw [hD, hA]
  · intro t
    exact isTransvectionProduct_transvection t.i t.j t.hij t.c
  · intro B C hB hC
    exact hB.mul hC

theorem tensorPolynomial_eq_zero_of_eval_det_one {R E ι : Type*} [Field R]
    [AddCommGroup E] [Module R E] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis (ι × ι) R E) (k : ℕ) [Invertible (k.factorial : R)]
    (φ : Module.Dual R (⨂[R]^k E))
    (h : ∀ A : Matrix ι ι R, Matrix.det A = 1 →
      MvPolynomial.eval (fun ij ↦ A ij.1 ij.2) (tensorPolynomial b k φ) = 0) :
    tensorPolynomial b k φ = 0 := by
  classical
  let K := AlgebraicClosure R
  let f : R →+* K := algebraMap R K
  let p := tensorPolynomial b k φ
  have hpK : p.map f = 0 := by
    apply MvPolynomial.eq_of_eval_eq_on_gl
    intro g
    change MvPolynomial.eval (fun ij : ι × ι ↦ (g : Matrix ι ι K) ij.1 ij.2)
      (p.map f) = 0
    cases isEmpty_or_nonempty ι with
    | inl hι =>
        letI : IsEmpty ι := hι
        let A : Matrix ι ι R := 1
        have hA : MvPolynomial.eval (fun ij ↦ A ij.1 ij.2) p = 0 :=
          h A (by simp [A])
        have hv : (fun ij : ι × ι ↦ (g : Matrix ι ι K) ij.1 ij.2) =
            fun ij ↦ f (A ij.1 ij.2) := by
          funext ij
          exact isEmptyElim ij.1
        rw [hv, MvPolynomial.eval_map]
        change MvPolynomial.eval₂ f
            (f ∘ fun ij : ι × ι ↦ A ij.1 ij.2) p = 0
        rw [← MvPolynomial.eval₂_comp, hA, map_zero]
    | inr hι =>
        letI : Nonempty ι := hι
        have hn : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hι
        have hgdet : Matrix.det (g : Matrix ι ι K) ≠ 0 := g.det_ne_zero
        obtain ⟨c : K, hcroot⟩ :=
          IsAlgClosed.exists_pow_nat_eq (Matrix.det (g : Matrix ι ι K)) hn
        have hc : c ≠ 0 := by
          intro hc
          apply hgdet
          rw [← hcroot, hc, zero_pow hn.ne']
        let B : Matrix ι ι K := c⁻¹ • (g : Matrix ι ι K)
        have hBdet : Matrix.det B = 1 := by
          change Matrix.det (c⁻¹ • (g : Matrix ι ι K)) = 1
          rw [Matrix.det_smul, inv_pow, hcroot]
          exact inv_mul_cancel₀ hgdet
        obtain ⟨L, hL⟩ := isTransvectionProduct_of_det_eq_one B hBdet
        let s : Fin L.length → TransvectionIndex ι := fun i ↦
          transvectionIndexOf (L.get i)
        have hbase (r : Fin L.length → R) :
            MvPolynomial.eval
                (fun ij ↦ ((c • (1 : Matrix ι ι K)) *
                  transvectionProd L.length s (fun i ↦ f (r i))) ij.1 ij.2)
                (p.map f) = 0 := by
          let A : Matrix ι ι R := transvectionProd L.length s r
          have hA : MvPolynomial.eval (fun ij ↦ A ij.1 ij.2) p = 0 :=
            h A (det_transvectionProd L.length s r)
          have hs := eval_map_tensorPolynomial_smul f b k φ c
            (fun ij : ι × ι ↦ A ij.1 ij.2)
          change MvPolynomial.eval (fun ij ↦ c * f (A ij.1 ij.2)) (p.map f) =
              c ^ k * f (MvPolynomial.eval (fun ij ↦ A ij.1 ij.2) p) at hs
          rw [hA, map_zero, mul_zero] at hs
          have hmap : transvectionProd L.length s (fun i ↦ f (r i)) = A.map f := by
            simpa [A] using (transvectionProd_map f L.length s r).symm
          rw [hmap]
          simpa only [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
            smul_eq_mul, Matrix.map_apply] using hs
        have hinterp := eval_tensorPolynomial_transvectionProd b k φ L.length s
          (c • (1 : Matrix ι ι K)) hbase (fun i ↦ (L.get i).c)
        have hmat : (c • (1 : Matrix ι ι K)) *
            transvectionProd L.length s (fun i ↦ (L.get i).c) =
              (g : Matrix ι ι K) := by
          rw [transvectionProd_list, hL]
          simp [B, smul_smul, hc]
        rw [hmat] at hinterp
        exact hinterp
  apply (MvPolynomial.map_injective f (FaithfulSMul.algebraMap_injective R K))
  simpa [p] using hpK

noncomputable def polarizationPolynomial {R E : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] (k : ℕ) (φ : Module.Dual R (⨂[R]^k E))
    (v : Fin k → E) : MvPolynomial (Fin k) R :=
  ∑ g : Fin k → Fin k,
    MvPolynomial.C (φ ((PiTensorProduct.tprod R) (fun i ↦ v (g i)))) *
      ∏ i : Fin k, MvPolynomial.X (g i)

theorem eval_polarizationPolynomial {R E : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] (k : ℕ) (φ : Module.Dual R (⨂[R]^k E))
    (v : Fin k → E) (c : Fin k → R) :
    MvPolynomial.eval c (polarizationPolynomial k φ v) =
      φ ((PiTensorProduct.tprod R) (fun _ : Fin k ↦ ∑ j : Fin k, c j • v j)) := by
  classical
  rw [polarizationPolynomial, map_sum, (PiTensorProduct.tprod R).map_sum, map_sum φ]
  apply Finset.sum_congr rfl
  intro g _
  rw [map_mul, MvPolynomial.eval_C, map_prod,
    (PiTensorProduct.tprod R).map_smul_univ, LinearMap.map_smul]
  simp only [MvPolynomial.eval_X]
  rw [mul_comm, smul_eq_mul]

theorem isHomogeneous_polarizationPolynomial {R E : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] (k : ℕ) (φ : Module.Dual R (⨂[R]^k E))
    (v : Fin k → E) : (polarizationPolynomial k φ v).IsHomogeneous k := by
  classical
  rw [polarizationPolynomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro g _
  have hp : (∏ i : Fin k, MvPolynomial.X (g i) : MvPolynomial (Fin k) R).IsHomogeneous k := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i : Fin k ↦ MvPolynomial.X (g i)) (fun _ ↦ 1)
      (fun i _ ↦ MvPolynomial.isHomogeneous_X (R := R) (g i))
  exact hp.C_mul _

noncomputable def tupleDegree (k : ℕ) (g : Fin k → Fin k) : Fin k →₀ ℕ :=
  ∑ i : Fin k, Finsupp.single (g i) 1

noncomputable def squarefreeDegree (k : ℕ) : Fin k →₀ ℕ :=
  ∑ i : Fin k, Finsupp.single i 1

theorem tupleDegree_eq_squarefreeDegree_iff (k : ℕ) (g : Fin k → Fin k) :
    tupleDegree k g = squarefreeDegree k ↔ Function.Bijective g := by
  classical
  constructor
  · intro h
    apply Finite.surjective_iff_bijective.mp
    intro j
    by_contra hj
    push Not at hj
    have heval := congrArg (fun d : Fin k →₀ ℕ ↦ d j) h
    simp [tupleDegree, squarefreeDegree, hj] at heval
  · intro hg
    simpa [tupleDegree, squarefreeDegree] using
      hg.sum_comp (fun j : Fin k ↦ Finsupp.single j 1)

noncomputable def permEquivBijective (α : Type*) :
    Equiv.Perm α ≃ {f : α → α // Function.Bijective f} where
  toFun σ := ⟨σ, σ.bijective⟩
  invFun f := Equiv.ofBijective f f.property
  left_inv σ := Equiv.ext fun _ ↦ rfl
  right_inv f := by
    apply Subtype.ext
    rfl

theorem coeff_polarizationPolynomial {R E : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] (k : ℕ) (φ : Module.Dual R (⨂[R]^k E))
    (v : Fin k → E) :
    MvPolynomial.coeff (squarefreeDegree k) (polarizationPolynomial k φ v) =
      ∑ σ : Equiv.Perm (Fin k),
        φ ((PiTensorProduct.tprod R) (fun i ↦ v (σ i))) := by
  classical
  rw [polarizationPolynomial, MvPolynomial.coeff_sum]
  have hterm (g : Fin k → Fin k) :
      MvPolynomial.C (φ ((PiTensorProduct.tprod R) (fun i ↦ v (g i)))) *
          ∏ i : Fin k, MvPolynomial.X (g i) =
        MvPolynomial.monomial (tupleDegree k g)
          (φ ((PiTensorProduct.tprod R) (fun i ↦ v (g i)))) := by
    symm
    rw [tupleDegree, MvPolynomial.monomial_sum_index]
    congr 1
  simp_rw [hterm, MvPolynomial.coeff_monomial]
  have hcond (g : Fin k → Fin k) :
      tupleDegree k g = squarefreeDegree k ↔ Function.Bijective g :=
    tupleDegree_eq_squarefreeDegree_iff k g
  calc
    (∑ g : Fin k → Fin k,
        if tupleDegree k g = squarefreeDegree k then
          φ ((PiTensorProduct.tprod R) (fun i ↦ v (g i))) else 0) =
        (∑ g : Fin k → Fin k,
          if Function.Bijective g then
            φ ((PiTensorProduct.tprod R) (fun i ↦ v (g i))) else 0) := by
      apply Finset.sum_congr rfl
      intro g _
      exact if_congr (hcond g) rfl rfl
    _ = ∑ g : {g : Fin k → Fin k // Function.Bijective g},
          φ ((PiTensorProduct.tprod R) (fun i ↦ v (g.val i))) := by
      apply Finset.sum_congr_set (s := {g | Function.Bijective g})
      · intro g hg
        change Function.Bijective g at hg
        rw [if_pos hg]
      · intro g hg
        change ¬Function.Bijective g at hg
        rw [if_neg hg]
    _ = ∑ σ : Equiv.Perm (Fin k),
          φ ((PiTensorProduct.tprod R) (fun i ↦ v (σ i))) := by
      symm
      exact Fintype.sum_equiv (permEquivBijective (Fin k)) _ _ (fun _ ↦ rfl)

theorem sum_perm_tprod_eq_zero_of_diagonal {R E : Type*} [Field R]
    [AddCommGroup E] [Module R E] (k : ℕ) [Invertible (k.factorial : R)]
    (φ : Module.Dual R (⨂[R]^k E))
    (hdiag : ∀ e : E, φ ((PiTensorProduct.tprod R) (fun _ : Fin k ↦ e)) = 0)
    (v : Fin k → E) :
    ∑ σ : Equiv.Perm (Fin k),
      φ ((PiTensorProduct.tprod R) (fun i ↦ v (σ i))) = 0 := by
  classical
  let q := polarizationPolynomial k φ v
  have hqeval (c : Fin k → R) : MvPolynomial.eval c q = 0 := by
    change MvPolynomial.eval c (polarizationPolynomial k φ v) = 0
    rw [eval_polarizationPolynomial]
    exact hdiag _
  have hcard_succ : (k + 1 : Cardinal) ≤ Cardinal.mk R := by
    let emb : ULift (Fin (k + 1)) → R := fun i ↦ (i.down : R)
    have hemb : Function.Injective emb := by
      intro i j hij
      apply ULift.ext
      exact natCast_fin_succ_injective (R := R) k hij
    simpa [emb, Cardinal.mk_fin] using Cardinal.mk_le_of_injective hemb
  have hk : (k : Cardinal) ≤ (k + 1 : Cardinal) := by
    exact_mod_cast Nat.le_succ k
  have hcard : (k : Cardinal) ≤ Cardinal.mk R := hk.trans hcard_succ
  have hq : q = 0 :=
    MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card (by
      simpa [q] using isHomogeneous_polarizationPolynomial k φ v) hqeval hcard
  have hc := congrArg (MvPolynomial.coeff (squarefreeDegree k)) hq
  rw [coeff_polarizationPolynomial, MvPolynomial.coeff_zero] at hc
  exact hc

noncomputable def permInvEquiv (α : Type*) : Equiv.Perm α ≃ Equiv.Perm α where
  toFun σ := σ.symm
  invFun σ := σ.symm
  left_inv σ := by simp
  right_inv σ := by simp

theorem sum_perm_reindex_eq_zero_of_diagonal {R E : Type*} [Field R]
    [AddCommGroup E] [Module R E] (k : ℕ) [Invertible (k.factorial : R)]
    (φ : Module.Dual R (⨂[R]^k E))
    (hdiag : ∀ e : E, φ ((PiTensorProduct.tprod R) (fun _ : Fin k ↦ e)) = 0)
    (x : ⨂[R]^k E) :
    ∑ σ : Equiv.Perm (Fin k),
      φ (PiTensorProduct.reindex R (fun _ : Fin k ↦ E) σ x) = 0 := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
      simp only [map_smul, smul_eq_mul]
      rw [← Finset.mul_sum]
      have hsum := sum_perm_tprod_eq_zero_of_diagonal k φ hdiag v
      have hinv :
          (∑ σ : Equiv.Perm (Fin k),
              φ ((PiTensorProduct.tprod R) (fun i ↦ v (σ.symm i)))) =
            ∑ σ : Equiv.Perm (Fin k),
              φ ((PiTensorProduct.tprod R) (fun i ↦ v (σ i))) := by
        exact Fintype.sum_equiv (permInvEquiv (Fin k)) _ _ (fun _ ↦ rfl)
      have hreindex (σ : Equiv.Perm (Fin k)) :
          φ (PiTensorProduct.reindex R (fun _ : Fin k ↦ E) σ
            ((PiTensorProduct.tprod R) v)) =
            φ ((PiTensorProduct.tprod R) (fun i ↦ v (σ.symm i))) := by
        rw [PiTensorProduct.reindex_tprod]
      simp_rw [hreindex]
      rw [hinv, hsum, mul_zero]
  | add x y hx hy =>
      simp_rw [map_add]
      rw [Finset.sum_add_distrib, hx, hy, add_zero]

theorem apply_eq_zero_of_diagonal_and_invariant {R E : Type*} [Field R]
    [AddCommGroup E] [Module R E] (k : ℕ) [Invertible (k.factorial : R)]
    (φ : Module.Dual R (⨂[R]^k E))
    (hdiag : ∀ e : E, φ ((PiTensorProduct.tprod R) (fun _ : Fin k ↦ e)) = 0)
    (x : ⨂[R]^k E)
    (hinv : ∀ σ : Equiv.Perm (Fin k),
      PiTensorProduct.reindex R (fun _ : Fin k ↦ E) σ x = x) :
    φ x = 0 := by
  have hsum := sum_perm_reindex_eq_zero_of_diagonal k φ hdiag x
  have hsum' : Fintype.card (Equiv.Perm (Fin k)) • φ x = 0 := by
    simpa only [hinv, Finset.sum_const, Finset.card_univ] using hsum
  rw [Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at hsum'
  exact (mul_eq_zero.mp hsum').resolve_left (Invertible.ne_zero (k.factorial : R))

theorem piTensorHomMap_reindex {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    (k : ℕ) (σ : Equiv.Perm (Fin k)) (x : ⨂[R]^k (Module.End R M)) :
    PiTensorProduct.piTensorHomMap
        (PiTensorProduct.reindex R (fun _ : Fin k ↦ Module.End R M) σ x) =
      (symAction R M k) σ * PiTensorProduct.piTensorHomMap x * (symAction R M k) σ⁻¹ := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      ext m
      have hinv (i : Fin k) : (σ⁻¹).symm (σ.symm i) = i := by
        change σ (σ.symm i) = i
        exact σ.apply_symm_apply i
      simp [symAction, Module.End.mul_apply]
      apply congrArg (fun z ↦ r • z)
      apply congrArg (PiTensorProduct.tprod R)
      funext i
      rw [hinv]
  | add x y hx hy =>
      simp [map_add, hx, hy, add_mul, mul_add]

theorem glAction_adjoin_le_centralizer {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] (k : ℕ) :
    Algebra.adjoin R (Set.range (glAction R M k)) ≤
      Subalgebra.centralizer R (Set.range (symAction R M k)) := by
  apply Algebra.adjoin_le
  rintro _ ⟨g, rfl⟩
  change (glAction R M k) g ∈ Subalgebra.centralizer R (Set.range (symAction R M k))
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨σ, rfl⟩
  ext x
  simp [glAction, symAction]

end Submission.Helpers
