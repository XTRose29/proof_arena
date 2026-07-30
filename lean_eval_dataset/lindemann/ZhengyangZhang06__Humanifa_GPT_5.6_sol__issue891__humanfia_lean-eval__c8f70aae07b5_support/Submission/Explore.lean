import Submission.Helpers

open scoped BigOperators
open Polynomial Finset

noncomputable section

private def negAddEquiv (A : Type*) [AddCommGroup A] : A ≃+ A where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x
  map_add' x y := neg_add x y

private def Lreflect {A : Type*} [AddCommGroup A]
    (u : AddMonoidAlgebra ℤ A) : AddMonoidAlgebra ℤ A :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (negAddEquiv A).toAddMonoidHom u

private def formalF (σ : Type*) [Fintype σ] :
    AddMonoidAlgebra ℤ (MvPolynomial σ ℤ) :=
  ∏ i : σ, (AddMonoidAlgebra.single 0 1 - AddMonoidAlgebra.single (MvPolynomial.X i) 1)

private def formalB (σ : Type*) [Fintype σ] :
    AddMonoidAlgebra ℤ (MvPolynomial σ ℤ) :=
  formalF σ * Lreflect (formalF σ)

private def actualF {σ : Type*} [Fintype σ] (x : σ → ℂ) :
    AddMonoidAlgebra ℤ ℂ :=
  ∏ i : σ, (AddMonoidAlgebra.single 0 1 - AddMonoidAlgebra.single (x i) 1)

private def actualB {σ : Type*} [Fintype σ] (x : σ → ℂ) :
    AddMonoidAlgebra ℤ ℂ :=
  actualF x * Lreflect (actualF x)

private def evalFormal {σ : Type*} [Fintype σ] (x : σ → ℂ) :
    AddMonoidAlgebra ℤ (MvPolynomial σ ℤ) →+* AddMonoidAlgebra ℤ ℂ :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (MvPolynomial.aeval x).toRingHom.toAddMonoidHom

private lemma evalFormal_formalF {σ : Type*} [Fintype σ] (x : σ → ℂ) :
    evalFormal x (formalF σ) = actualF x := by
  simp only [formalF, actualF, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_sub]
  congr 1
  · change Finsupp.mapDomain (MvPolynomial.aeval x)
        (Finsupp.single (0 : MvPolynomial σ ℤ) (1 : ℤ)) =
      Finsupp.single (0 : ℂ) (1 : ℤ)
    rw [Finsupp.mapDomain_single]
    simp
  · change Finsupp.mapDomain (MvPolynomial.aeval x)
        (Finsupp.single (MvPolynomial.X i) (1 : ℤ)) =
      Finsupp.single (x i) (1 : ℤ)
    rw [Finsupp.mapDomain_single]
    simp

private lemma evalFormal_reflect {σ : Type*} [Fintype σ] (x : σ → ℂ)
    (u : AddMonoidAlgebra ℤ (MvPolynomial σ ℤ)) :
    evalFormal x (Lreflect u) = Lreflect (evalFormal x u) := by
  change Finsupp.mapDomain (MvPolynomial.aeval x)
      (Finsupp.mapDomain (fun q ↦ -q) u) =
    Finsupp.mapDomain (fun y ↦ -y) (Finsupp.mapDomain (MvPolynomial.aeval x) u)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro q hq
  simp

private lemma evalFormal_formalB {σ : Type*} [Fintype σ] (x : σ → ℂ) :
    evalFormal x (formalB σ) = actualB x := by
  simp [formalB, actualB, evalFormal_formalF, evalFormal_reflect]

private lemma rename_formalF {σ : Type*} [Fintype σ] (e : Equiv.Perm σ) :
    AddMonoidAlgebra.mapDomainRingEquiv ℤ (MvPolynomial.renameEquiv ℤ e).toAddEquiv
      (formalF σ) = formalF σ := by
  simp only [formalF, map_prod]
  have hfactor (i : σ) :
      AddMonoidAlgebra.mapDomainRingEquiv ℤ (MvPolynomial.renameEquiv ℤ e).toAddEquiv
          (AddMonoidAlgebra.single 0 1 - AddMonoidAlgebra.single (MvPolynomial.X i) 1) =
        AddMonoidAlgebra.single 0 1 - AddMonoidAlgebra.single (MvPolynomial.X (e i)) 1 := by
    rw [map_sub]
    simp
  simp_rw [hfactor]
  exact Fintype.prod_equiv e _ _ (fun _ ↦ rfl)

private lemma rename_reflect {σ : Type*} [Fintype σ] (e : Equiv.Perm σ)
    (u : AddMonoidAlgebra ℤ (MvPolynomial σ ℤ)) :
    AddMonoidAlgebra.mapDomainRingEquiv ℤ (MvPolynomial.renameEquiv ℤ e).toAddEquiv
        (Lreflect u) =
      Lreflect (AddMonoidAlgebra.mapDomainRingEquiv ℤ
        (MvPolynomial.renameEquiv ℤ e).toAddEquiv u) := by
  change Finsupp.mapDomain (MvPolynomial.rename e)
      (Finsupp.mapDomain (fun q ↦ -q) u) =
    Finsupp.mapDomain (fun q ↦ -q) (Finsupp.mapDomain (MvPolynomial.rename e) u)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro q hq
  simp

private lemma rename_formalB {σ : Type*} [Fintype σ] (e : Equiv.Perm σ) :
    AddMonoidAlgebra.mapDomainRingEquiv ℤ (MvPolynomial.renameEquiv ℤ e).toAddEquiv
      (formalB σ) = formalB σ := by
  simp [formalB, rename_reflect, rename_formalF]

private def formalMoment {σ : Type*} (g : ℤ[X])
    (u : AddMonoidAlgebra ℤ (MvPolynomial σ ℤ)) : MvPolynomial σ ℤ :=
  u.sum fun y a ↦ MvPolynomial.C a * g.eval₂ MvPolynomial.C y

private lemma rename_formalMoment {σ : Type*} [Fintype σ] (e : Equiv.Perm σ)
    (g : ℤ[X]) (u : AddMonoidAlgebra ℤ (MvPolynomial σ ℤ)) :
    MvPolynomial.rename e (formalMoment g u) =
      formalMoment g (AddMonoidAlgebra.mapDomainRingEquiv ℤ
        (MvPolynomial.renameEquiv ℤ e).toAddEquiv u) := by
  let h : MvPolynomial σ ℤ → ℤ →+ MvPolynomial σ ℤ := fun y ↦
    { toFun := fun a ↦ MvPolynomial.C a * g.eval₂ MvPolynomial.C y
      map_zero' := by simp
      map_add' := by intro a b; simp [add_mul] }
  change MvPolynomial.rename e (u.sum fun y a ↦ h y a) =
    (Finsupp.mapDomain (MvPolynomial.rename e) u).sum fun y a ↦ h y a
  rw [map_finsuppSum, Finsupp.sum_mapDomain_index_addMonoidHom h]
  apply Finsupp.sum_congr
  intro y hy
  dsimp [h]
  rw [map_mul, MvPolynomial.rename_C]
  congr 1
  calc
    MvPolynomial.rename e (g.eval₂ MvPolynomial.C y) =
        g.eval₂ ((MvPolynomial.rename e).toRingHom.comp MvPolynomial.C)
          (MvPolynomial.rename e y) :=
      Polynomial.hom_eval₂ (p := g) (f := MvPolynomial.C)
        (g := (MvPolynomial.rename e).toRingHom) y
    _ = g.eval₂ MvPolynomial.C (MvPolynomial.rename e y) := by
      congr 1
      ext a
      simp

private lemma formalMoment_isSymmetric {σ : Type*} [Fintype σ] (g : ℤ[X]) :
    (formalMoment g (formalB σ)).IsSymmetric := by
  intro e
  rw [rename_formalMoment, rename_formalB]

private lemma aeval_formalMoment {σ : Type*} [Fintype σ] (x : σ → ℂ)
    (g : ℤ[X]) (u : AddMonoidAlgebra ℤ (MvPolynomial σ ℤ)) :
    MvPolynomial.aeval x (formalMoment g u) =
      (evalFormal x u).sum fun y a ↦ (a : ℂ) * Polynomial.aeval y g := by
  let h : ℂ → ℤ →+ ℂ := fun y ↦
    { toFun := fun a ↦ (a : ℂ) * Polynomial.aeval y g
      map_zero' := by simp
      map_add' := by intro a b; push_cast; ring }
  change MvPolynomial.aeval x
      (u.sum fun y a ↦ MvPolynomial.C a * g.eval₂ MvPolynomial.C y) =
    (Finsupp.mapDomain (MvPolynomial.aeval x) u).sum fun y a ↦ h y a
  rw [map_finsuppSum, Finsupp.sum_mapDomain_index_addMonoidHom h]
  apply Finsupp.sum_congr
  intro y hy
  dsimp [h]
  rw [map_mul, MvPolynomial.aeval_C]
  congr 1
  calc
    MvPolynomial.aeval x (g.eval₂ MvPolynomial.C y) =
        g.eval₂ ((MvPolynomial.aeval x).toRingHom.comp MvPolynomial.C)
          (MvPolynomial.aeval x y) :=
      Polynomial.hom_eval₂ (p := g) (f := MvPolynomial.C)
        (g := (MvPolynomial.aeval x).toRingHom) y
    _ = Polynomial.aeval (MvPolynomial.aeval x y) g := by
      rw [Polynomial.aeval_def]
      congr 1
      ext a
      simp

private theorem symmetric_aeval_roots_isInt {σ : Type*} [Fintype σ]
    (P : ℤ[X]) (hP : P.Monic) (x : σ → ℂ)
    (hσ : Fintype.card σ = P.natDegree)
    (hx : Multiset.map x Finset.univ.val = (P.map (algebraMap ℤ ℂ)).roots)
    (φ : MvPolynomial σ ℤ) (hφ : φ.IsSymmetric) :
    ∃ z : ℤ, (z : ℂ) = MvPolynomial.aeval x φ := by
  let n := P.natDegree
  have hncard : Fintype.card σ ≤ n := by simp [n, hσ]
  obtain ⟨q, hq⟩ := MvPolynomial.esymmAlgHom_surjective ℤ hncard ⟨φ, hφ⟩
  have hφq : MvPolynomial.aeval
        (fun i : Fin n ↦ MvPolynomial.esymm σ ℤ (i + 1)) q = φ := by
    simpa [MvPolynomial.esymmAlgHom_apply] using congrArg Subtype.val hq
  let v : Fin n → ℤ := fun i ↦
    (-1 : ℤ) ^ (i + 1 : ℕ) * P.coeff (n - (i + 1 : ℕ))
  have hcard : (P.map (algebraMap ℤ ℂ)).roots.card = n := by
    rw [← hx]
    simpa [n] using hσ
  have hdeg : (P.map (algebraMap ℤ ℂ)).natDegree = n := by
    exact Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff
      (p := P) (algebraMap ℤ ℂ) (by rw [hP.leadingCoeff]; exact isUnit_one)
  have hcard' : (P.map (algebraMap ℤ ℂ)).roots.card =
      (P.map (algebraMap ℤ ℂ)).natDegree := hcard.trans hdeg.symm
  have hv (i : Fin n) :
      (v i : ℂ) = (P.map (algebraMap ℤ ℂ)).roots.esymm (i + 1 : ℕ) := by
    have hi : (i + 1 : ℕ) ≤ n := i.isLt
    have hk : n - (i + 1 : ℕ) ≤ (P.map (algebraMap ℤ ℂ)).natDegree := by
      rw [hdeg]
      exact Nat.sub_le _ _
    have hvi := Polynomial.coeff_eq_esymm_roots_of_card
      (p := P.map (algebraMap ℤ ℂ)) hcard'
      (k := n - (i + 1 : ℕ)) hk
    rw [Polynomial.coeff_map, (hP.map (algebraMap ℤ ℂ)).leadingCoeff,
      one_mul, hdeg, Nat.sub_sub_self hi] at hvi
    change ((P.coeff (n - (i + 1 : ℕ)) : ℤ) : ℂ) =
      (-1 : ℂ) ^ (i + 1 : ℕ) *
        (P.map (algebraMap ℤ ℂ)).roots.esymm (i + 1 : ℕ) at hvi
    dsimp [v]
    push_cast
    rw [hvi, ← mul_assoc, ← pow_add]
    simp
  refine ⟨MvPolynomial.aeval v q, ?_⟩
  calc
    ((MvPolynomial.aeval v q : ℤ) : ℂ) =
        MvPolynomial.aeval (fun i ↦ (v i : ℂ)) q := by
          simpa using (MvPolynomial.comp_aeval_apply (f := v) (Algebra.ofId ℤ ℂ) q)
    _ = MvPolynomial.aeval
        (fun i : Fin n ↦ (P.map (algebraMap ℤ ℂ)).roots.esymm (i + 1 : ℕ)) q := by
          simp only [MvPolynomial.aeval_def]
          apply MvPolynomial.eval₂_congr
          intro i c hi hc
          exact hv i
    _ = MvPolynomial.aeval
        (fun i : Fin n ↦ MvPolynomial.aeval x
          (MvPolynomial.esymm σ ℤ (i + 1 : ℕ))) q := by
          simp only [MvPolynomial.aeval_def]
          apply MvPolynomial.eval₂_congr
          intro i c hi hc
          rw [← MvPolynomial.aeval_def,
            MvPolynomial.aeval_esymm_eq_multiset_esymm, hx]
    _ = MvPolynomial.aeval x
        (MvPolynomial.aeval
          (fun i : Fin n ↦ MvPolynomial.esymm σ ℤ (i + 1 : ℕ)) q) := by
          simp only [MvPolynomial.aeval_def]
          rw [MvPolynomial.eval₂_assoc]
          congr 2
    _ = MvPolynomial.aeval x φ := by rw [hφq]

private theorem actual_moment_isInt {σ : Type*} [Fintype σ]
    (P : ℤ[X]) (hP : P.Monic) (x : σ → ℂ)
    (hσ : Fintype.card σ = P.natDegree)
    (hx : Multiset.map x Finset.univ.val = (P.map (algebraMap ℤ ℂ)).roots)
    (hb0 : actualB x 0 ≠ 0) (g : ℤ[X]) :
    ∃ z : ℤ, (z : ℂ) = ∑ y ∈ (actualB x).support.erase 0,
      (actualB x y : ℂ) * Polynomial.aeval y g := by
  obtain ⟨z, hz⟩ := symmetric_aeval_roots_isInt P hP x hσ hx
    (formalMoment g (formalB σ)) (formalMoment_isSymmetric g)
  rw [aeval_formalMoment, evalFormal_formalB] at hz
  let H : ℂ → ℤ → ℂ := fun y a ↦ (a : ℂ) * Polynomial.aeval y g
  change (z : ℂ) = (actualB x).sum H at hz
  have hmem : 0 ∈ (actualB x).support := Finsupp.mem_support_iff.mpr hb0
  have hsum : (actualB x).sum H = H 0 (actualB x 0) +
      ∑ y ∈ (actualB x).support.erase 0, H y (actualB x y) := by
    change (∑ y ∈ (actualB x).support, H y (actualB x y)) = _
    rw [← Finset.sum_erase_add _ _ hmem]
    ac_rfl
  have hzero : (((actualB x 0) * g.eval 0 : ℤ) : ℂ) = H 0 (actualB x 0) := by
    dsimp [H]
    push_cast
    rw [show Polynomial.aeval (0 : ℂ) g = ((g.eval 0 : ℤ) : ℂ) by
      simpa using Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval
        (A := ℂ) (0 : ℤ) g]
  refine ⟨z - actualB x 0 * g.eval 0, ?_⟩
  rw [Int.cast_sub, hz, hzero, hsum]
  ring

private lemma aeval_isIntegral {σ : Type*} [Fintype σ] (x : σ → ℂ)
    (hx : ∀ i, IsIntegral ℤ (x i)) (q : MvPolynomial σ ℤ) :
    IsIntegral ℤ (MvPolynomial.aeval x q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ a))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hx i)

private lemma actualB_support_integral {σ : Type*} [Fintype σ] (x : σ → ℂ)
    (hx : ∀ i, IsIntegral ℤ (x i)) (y : ℂ) (hy : y ∈ (actualB x).support) :
    IsIntegral ℤ y := by
  rw [← evalFormal_formalB x] at hy
  change y ∈ (Finsupp.mapDomain (MvPolynomial.aeval x) (formalB σ)).support at hy
  have hymap := Finsupp.mapDomain_support hy
  rcases Finset.mem_image.mp hymap with ⟨q, hq, rfl⟩
  exact aeval_isIntegral x hx q

private lemma Lreflect_apply {A : Type*} [AddCommGroup A]
    (u : AddMonoidAlgebra ℤ A) (y : A) : Lreflect u y = u (-y) := by
  change Finsupp.mapDomain (fun z : A ↦ -z) u y = u (-y)
  simpa [negAddEquiv] using
    (Finsupp.mapDomain_equiv_apply (f := negAddEquiv A) u y)

private lemma actualF_ne_zero {σ : Type*} [Fintype σ] (x : σ → ℂ)
    (hx : ∀ i, x i ≠ 0) : actualF x ≠ 0 := by
  dsimp [actualF]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi hfactor
  have hzero := congrArg (fun f : AddMonoidAlgebra ℤ ℂ ↦ f 0) hfactor
  change (Finsupp.single (0 : ℂ) (1 : ℤ) - Finsupp.single (x i) (1 : ℤ)) 0 =
    (0 : ℂ →₀ ℤ) 0 at hzero
  simp [hx i] at hzero

private lemma actualB_zero_ne {σ : Type*} [Fintype σ] (x : σ → ℂ)
    (hx : ∀ i, x i ≠ 0) : actualB x 0 ≠ 0 := by
  let F := actualF x
  have hF : F ≠ 0 := actualF_ne_zero x hx
  have hsupport : F.support.Nonempty := Finsupp.support_nonempty_iff.mpr hF
  have hcoeff : actualB x 0 = F.sum fun y a ↦ a * a := by
    rw [actualB, AddMonoidAlgebra.mul_apply_left]
    apply Finsupp.sum_congr
    intro y hy
    rw [Lreflect_apply]
    simp
  rw [hcoeff]
  apply ne_of_gt
  change 0 < ∑ y ∈ F.support, F y * F y
  exact Finset.sum_pos
    (fun y hy ↦ mul_self_pos.mpr (Finsupp.mem_support_iff.mp hy)) hsupport

private def expMonoidHom : Multiplicative ℂ →* ℂ where
  toFun z := Complex.exp z.toAdd
  map_one' := Complex.exp_zero
  map_mul' a b := by
    change Complex.exp (a.toAdd + b.toAdd) = Complex.exp a.toAdd * Complex.exp b.toAdd
    exact Complex.exp_add _ _

private def expEval : AddMonoidAlgebra ℤ ℂ →+* ℂ :=
  (AddMonoidAlgebra.lift ℤ ℂ ℂ expMonoidHom).toRingHom

private lemma expEval_apply (u : AddMonoidAlgebra ℤ ℂ) :
    expEval u = u.sum fun y a ↦ (a : ℂ) * Complex.exp y := by
  rfl

private lemma expEval_actualF {σ : Type*} [Fintype σ] (x : σ → ℂ) :
    expEval (actualF x) = ∏ i : σ, (1 - Complex.exp (x i)) := by
  simp [expEval, actualF, expMonoidHom]

private lemma expEval_actualB_zero {σ : Type*} [Fintype σ] (x : σ → ℂ)
    (i : σ) (hi : Complex.exp (x i) = 1) : expEval (actualB x) = 0 := by
  rw [actualB, map_mul, expEval_actualF]
  have hzero : (∏ j : σ, (1 - Complex.exp (x j))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hi, sub_self]
  rw [hzero, zero_mul]

private lemma actualB_exp_relation {σ : Type*} [Fintype σ] (x : σ → ℂ)
    (hb0 : actualB x 0 ≠ 0) (hexp : expEval (actualB x) = 0) :
    (actualB x 0 : ℂ) + ∑ y ∈ (actualB x).support.erase 0,
      (actualB x y : ℂ) * Complex.exp y = 0 := by
  let H : ℂ → ℤ → ℂ := fun y a ↦ (a : ℂ) * Complex.exp y
  rw [expEval_apply] at hexp
  change (actualB x).sum H = 0 at hexp
  have hmem : 0 ∈ (actualB x).support := Finsupp.mem_support_iff.mpr hb0
  calc
    (actualB x 0 : ℂ) + ∑ y ∈ (actualB x).support.erase 0,
        (actualB x y : ℂ) * Complex.exp y =
        H 0 (actualB x 0) + ∑ y ∈ (actualB x).support.erase 0,
          H y (actualB x y) := by simp [H]
    _ = (actualB x).sum H := by
      change H 0 (actualB x 0) +
        ∑ y ∈ (actualB x).support.erase 0, H y (actualB x y) =
        ∑ y ∈ (actualB x).support, H y (actualB x y)
      rw [add_comm, Finset.sum_erase_add _ _ hmem]
    _ = 0 := hexp

private lemma root_isIntegral (P : ℤ[X]) (hP : P.Monic) {y : ℂ}
    (hy : y ∈ (P.map (algebraMap ℤ ℂ)).roots) : IsIntegral ℤ y := by
  refine ⟨P, hP, ?_⟩
  exact (Polynomial.eval₂_eq_eval_map (algebraMap ℤ ℂ)).trans
    (Polynomial.isRoot_of_mem_roots hy)

private lemma root_ne_zero (P : ℤ[X]) (hP0 : P.eval 0 ≠ 0) {y : ℂ}
    (hy : y ∈ (P.map (algebraMap ℤ ℂ)).roots) : y ≠ 0 := by
  intro hy0
  subst y
  have hroot := Polynomial.isRoot_of_mem_roots hy
  apply hP0
  simpa [Polynomial.eval_zero_map] using hroot

private theorem pi_algebraic_false (hpi : IsAlgebraic ℤ Real.pi) : False := by
  have hpiC : IsAlgebraic ℤ (Real.pi : ℂ) := hpi.algebraMap
  have hbase : IsAlgebraic ℤ ((Real.pi : ℂ) * Complex.I) :=
    hpiC.mul Complex.isIntegral_int_I.isAlgebraic
  obtain ⟨d, hd, hdint⟩ := hbase.exists_integral_multiple
  let α : ℂ := (2 : ℕ) • (d • ((Real.pi : ℂ) * Complex.I))
  have hαint : IsIntegral ℤ α := hdint.nsmul 2
  have hαeq : α = (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp only [α, nsmul_eq_mul, zsmul_eq_mul, Nat.cast_ofNat]
    ring
  have hα0 : α ≠ 0 := by
    rw [hαeq]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hd)
      (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero)
  have hαexp : Complex.exp α = 1 := by
    rw [hαeq]
    exact Complex.exp_int_mul_two_pi_mul_I d
  let P : ℤ[X] := minpoly ℤ α
  have hP : P.Monic := minpoly.monic hαint
  have hP0 : P.eval 0 ≠ 0 := Submission.Helpers.minpoly_eval_zero_ne hαint hα0
  let roots : List ℂ := (P.map (algebraMap ℤ ℂ)).roots.toList
  let x : Fin roots.length → ℂ := roots.get
  have hxroots : Multiset.map x Finset.univ.val =
      (P.map (algebraMap ℤ ℂ)).roots := by
    change Multiset.map roots.get Finset.univ.val = _
    rw [Fin.univ_val_map, List.ofFn_get]
    simp [roots]
  have hσ : Fintype.card (Fin roots.length) = P.natDegree := by
    rw [Fintype.card_fin]
    have hdeg : (P.map (algebraMap ℤ ℂ)).natDegree = P.natDegree :=
      Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff
        (p := P) (algebraMap ℤ ℂ) (by rw [hP.leadingCoeff]; exact isUnit_one)
    calc
      roots.length = (P.map (algebraMap ℤ ℂ)).roots.card := by simp [roots]
      _ = (P.map (algebraMap ℤ ℂ)).natDegree :=
        Polynomial.splits_iff_card_roots.mp
          (IsAlgClosed.splits (P.map (algebraMap ℤ ℂ)))
      _ = P.natDegree := hdeg
  have hxmem (i : Fin roots.length) : x i ∈ (P.map (algebraMap ℤ ℂ)).roots := by
    rw [← hxroots]
    simp
  have hxint : ∀ i, IsIntegral ℤ (x i) := fun i ↦ root_isIntegral P hP (hxmem i)
  have hx0 : ∀ i, x i ≠ 0 := fun i ↦ root_ne_zero P hP0 (hxmem i)
  have hαmem : α ∈ (P.map (algebraMap ℤ ℂ)).roots := by
    change α ∈ P.aroots ℂ
    rw [mem_aroots]
    exact ⟨hP.ne_zero, minpoly.aeval ℤ α⟩
  have hαlist : α ∈ roots := by simpa [roots] using hαmem
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hαlist
  have hxi : x i = α := by simpa [x] using hi
  let b : ℂ →₀ ℤ := actualB x
  have hb0 : b 0 ≠ 0 := actualB_zero_ne x hx0
  have hbexp : expEval b = 0 := by
    dsimp [b]
    exact expEval_actualB_zero x i (hxi ▸ hαexp)
  have hbrel : (b 0 : ℂ) + ∑ y ∈ b.support.erase 0,
      (b y : ℂ) * Complex.exp y = 0 := actualB_exp_relation x hb0 hbexp
  exact Submission.Helpers.no_integral_relation_exp b hb0
    (fun y hy ↦ actualB_support_integral x hxint y (Finset.mem_of_mem_erase hy))
    hbrel
    (fun g ↦ actual_moment_isInt P hP x hσ hxroots hb0 g)

theorem pi_transcendental : Transcendental ℤ Real.pi := by
  change ¬IsAlgebraic ℤ Real.pi
  exact pi_algebraic_false

end
