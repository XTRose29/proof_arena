import Submission.Helpers

open scoped BigOperators
open Polynomial Finset

namespace Submission.Galois

noncomputable section

set_option maxHeartbeats 0

private def exponentHom {ι L : Type*} [AddCommMonoid L] (a : ι → L) :
    (ι →₀ ℕ) →+ L :=
  (Finsupp.linearCombination ℕ a).toAddMonoidHom

private lemma exponentHom_apply {ι L : Type*} [AddCommMonoid L] (a : ι → L)
    (d : ι →₀ ℕ) : exponentHom a d = d.sum fun i m ↦ m • a i := by
  rfl

private lemma exponentHom_injective {ι L : Type*} [Field L] [Algebra ℚ L]
    (a : ι → L) (ha : LinearIndependent ℚ a) : Function.Injective (exponentHom a) := by
  exact (ha.restrict_scalars' ℕ).finsuppLinearCombination_injective

private def groupPolynomial {ι L : Type*} [CommRing L] (a : ι → L) :
    MvPolynomial ι ℤ →+* AddMonoidAlgebra ℤ L :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (exponentHom a)

private lemma groupPolynomial_ne_zero {ι L : Type*} [Field L] [Algebra ℚ L]
    (a : ι → L) (ha : LinearIndependent ℚ a) {q : MvPolynomial ι ℤ} (hq : q ≠ 0) :
    groupPolynomial a q ≠ 0 := by
  exact fun h ↦ hq (Finsupp.mapDomain_injective (exponentHom_injective a ha) h)

private def mapAut {L : Type*} [Field L] [Algebra ℚ L] (τ : L ≃ₐ[ℚ] L) :
    AddMonoidAlgebra ℤ L ≃+* AddMonoidAlgebra ℤ L :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ τ.toAddEquiv

private lemma mapAut_groupPolynomial {ι L : Type*} [Field L] [Algebra ℚ L]
    (τ : L ≃ₐ[ℚ] L) (a : ι → L) (q : MvPolynomial ι ℤ) :
    mapAut τ (groupPolynomial a q) = groupPolynomial (τ ∘ a) q := by
  change Finsupp.mapDomain τ (Finsupp.mapDomain (exponentHom a) q) =
    Finsupp.mapDomain (exponentHom (τ ∘ a)) q
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro d hd
  simp only [Function.comp_apply, exponentHom_apply]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i hi
  simp

private def orbitProduct {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (q : MvPolynomial ι ℤ) (a : ι → L) :
    AddMonoidAlgebra ℤ L :=
  ∏ τ : L ≃ₐ[ℚ] L, groupPolynomial (τ ∘ a) q

private lemma mapAut_orbitProduct {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (ρ : L ≃ₐ[ℚ] L) (q : MvPolynomial ι ℤ) (a : ι → L) :
    mapAut ρ (orbitProduct q a) = orbitProduct q a := by
  simp only [orbitProduct, map_prod, mapAut_groupPolynomial]
  exact Fintype.prod_equiv (Equiv.mulLeft ρ) _ _ fun τ ↦ by rfl

private lemma orbitProduct_ne_zero {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (q : MvPolynomial ι ℤ) (a : ι → L)
    (hq : q ≠ 0) (ha : LinearIndependent ℚ a) : orbitProduct q a ≠ 0 := by
  dsimp [orbitProduct]
  apply Finset.prod_ne_zero_iff.mpr
  intro τ hτ
  apply groupPolynomial_ne_zero (τ ∘ a) _ hq
  exact ha.map' τ.toLinearMap (LinearMap.ker_eq_bot.mpr τ.injective)

private def reflect {L : Type*} [AddCommGroup L]
    (u : AddMonoidAlgebra ℤ L) : AddMonoidAlgebra ℤ L :=
  AddMonoidAlgebra.mapDomainRingHom ℤ
    ({ toFun := fun x : L ↦ -x
       map_zero' := neg_zero
       map_add' := neg_add } : L →+ L) u

private lemma reflect_apply {L : Type*} [AddCommGroup L]
    (u : AddMonoidAlgebra ℤ L) (y : L) : reflect u y = u (-y) := by
  change Finsupp.mapDomain (fun z : L ↦ -z) u y = u (-y)
  simpa using
    (Finsupp.mapDomain_equiv_apply
      (f := { toFun := fun x : L ↦ -x
              invFun := fun x : L ↦ -x
              left_inv := neg_neg
              right_inv := neg_neg } ) u y)

private def balancedOrbit {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (q : MvPolynomial ι ℤ) (a : ι → L) :
    AddMonoidAlgebra ℤ L :=
  orbitProduct q a * reflect (orbitProduct q a)

private lemma balancedOrbit_zero_ne {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (q : MvPolynomial ι ℤ) (a : ι → L)
    (hq : q ≠ 0) (ha : LinearIndependent ℚ a) : balancedOrbit q a 0 ≠ 0 := by
  let F := orbitProduct q a
  have hF : F ≠ 0 := orbitProduct_ne_zero q a hq ha
  have hsupport : F.support.Nonempty := Finsupp.support_nonempty_iff.mpr hF
  have hcoeff : balancedOrbit q a 0 = F.sum fun y c ↦ c * c := by
    rw [balancedOrbit, AddMonoidAlgebra.mul_apply_left]
    apply Finsupp.sum_congr
    intro y hy
    rw [reflect_apply]
    simp
  rw [hcoeff]
  apply ne_of_gt
  change 0 < ∑ y ∈ F.support, F y * F y
  exact Finset.sum_pos
    (fun y hy ↦ mul_self_pos.mpr (Finsupp.mem_support_iff.mp hy)) hsupport

private lemma mapAut_reflect {L : Type*} [Field L] [Algebra ℚ L]
    (τ : L ≃ₐ[ℚ] L) (u : AddMonoidAlgebra ℤ L) :
    mapAut τ (reflect u) = reflect (mapAut τ u) := by
  change Finsupp.mapDomain τ (Finsupp.mapDomain (fun z : L ↦ -z) u) =
    Finsupp.mapDomain (fun z : L ↦ -z) (Finsupp.mapDomain τ u)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro y hy
  simp

private lemma mapAut_balancedOrbit {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (τ : L ≃ₐ[ℚ] L) (q : MvPolynomial ι ℤ) (a : ι → L) :
    mapAut τ (balancedOrbit q a) = balancedOrbit q a := by
  simp [balancedOrbit, mapAut_reflect, mapAut_orbitProduct]

private def expMonoidHom {L : Type*} [Field L] [Algebra ℚ L] (ιL : L →ₐ[ℚ] ℂ) :
    Multiplicative L →* ℂ where
  toFun z := Complex.exp (ιL z.toAdd)
  map_one' := by simp
  map_mul' a b := by
    change Complex.exp (ιL (a.toAdd + b.toAdd)) =
      Complex.exp (ιL a.toAdd) * Complex.exp (ιL b.toAdd)
    rw [map_add, Complex.exp_add]

private def expEval {L : Type*} [Field L] [Algebra ℚ L] (ιL : L →ₐ[ℚ] ℂ) :
    AddMonoidAlgebra ℤ L →+* ℂ :=
  (AddMonoidAlgebra.lift ℤ ℂ L (expMonoidHom ιL)).toRingHom

private lemma expEval_apply {L : Type*} [Field L] [Algebra ℚ L]
    (ιL : L →ₐ[ℚ] ℂ) (u : AddMonoidAlgebra ℤ L) :
    expEval ιL u = u.sum fun y c ↦ (c : ℂ) * Complex.exp (ιL y) := by
  exact AddMonoidAlgebra.lift_apply' (expMonoidHom ιL) u

private lemma expEval_groupPolynomial {ι L : Type*} [Field L] [Algebra ℚ L]
    (ιL : L →ₐ[ℚ] ℂ) (a : ι → L) (q : MvPolynomial ι ℤ) :
    expEval ιL (groupPolynomial a q) =
      MvPolynomial.aeval (fun i ↦ Complex.exp (ιL (a i))) q := by
  change ((expEval ιL).comp (groupPolynomial a)) q =
    (MvPolynomial.aeval fun i ↦ Complex.exp (ιL (a i))) q
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [groupPolynomial, expEval]
  · intro i
    rw [RingHom.comp_apply]
    have hX : groupPolynomial a (MvPolynomial.X i) =
        Finsupp.single (a i) 1 := by
      change Finsupp.mapDomain (exponentHom a)
          (Finsupp.single (Finsupp.single i 1) 1) = Finsupp.single (a i) 1
      rw [Finsupp.mapDomain_single]
      simp [exponentHom]
    rw [hX]
    simp [expEval, expMonoidHom, MvPolynomial.aeval_def,
      AddMonoidAlgebra.lift_apply']

private lemma expEval_orbitProduct_zero {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (ιL : L →ₐ[ℚ] ℂ) (q : MvPolynomial ι ℤ) (a : ι → L)
    (hrel : MvPolynomial.aeval (fun i ↦ Complex.exp (ιL (a i))) q = 0) :
    expEval ιL (orbitProduct q a) = 0 := by
  rw [orbitProduct, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : L ≃ₐ[ℚ] L))
  simpa [expEval_groupPolynomial] using hrel

private lemma expEval_balancedOrbit_zero {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (ιL : L →ₐ[ℚ] ℂ) (q : MvPolynomial ι ℤ) (a : ι → L)
    (hrel : MvPolynomial.aeval (fun i ↦ Complex.exp (ιL (a i))) q = 0) :
    expEval ιL (balancedOrbit q a) = 0 := by
  rw [balancedOrbit, map_mul, expEval_orbitProduct_zero ιL q a hrel, zero_mul]

private def IntegralSupport {L : Type*} [Field L] [Algebra ℤ L]
    (u : AddMonoidAlgebra ℤ L) : Prop :=
  ∀ y ∈ u.support, IsIntegral ℤ y

private lemma integralSupport_one {L : Type*} [Field L] [Algebra ℤ L] :
    IntegralSupport (1 : AddMonoidAlgebra ℤ L) := by
  classical
  intro y hy
  change y ∈ (Finsupp.single 0 (1 : ℤ)).support at hy
  rw [Finsupp.mem_support_iff] at hy
  have : y = 0 := by
    by_contra h
    simp [h] at hy
  subst y
  exact isIntegral_zero

private lemma integralSupport_mul {L : Type*} [Field L] [Algebra ℤ L]
    {u v : AddMonoidAlgebra ℤ L} (hu : IntegralSupport u) (hv : IntegralSupport v) :
    IntegralSupport (u * v) := by
  classical
  intro y hy
  have hy' := AddMonoidAlgebra.support_mul u v hy
  obtain ⟨yu, hyu, yv, hyv, rfl⟩ := Finset.mem_add.mp hy'
  exact (hu yu hyu).add (hv yv hyv)

private lemma exponentHom_isIntegral {ι L : Type*} [Field L] [Algebra ℤ L]
    (a : ι → L) (ha : ∀ i, IsIntegral ℤ (a i)) (d : ι →₀ ℕ) :
    IsIntegral ℤ (exponentHom a d) := by
  classical
  rw [exponentHom_apply]
  change IsIntegral ℤ (∑ i ∈ d.support, d i • a i)
  exact IsIntegral.sum _ fun i hi ↦ (ha i).nsmul _

private lemma groupPolynomial_integralSupport {ι L : Type*} [Field L] [Algebra ℤ L]
    (a : ι → L) (ha : ∀ i, IsIntegral ℤ (a i)) (q : MvPolynomial ι ℤ) :
    IntegralSupport (groupPolynomial a q) := by
  classical
  intro y hy
  change y ∈ (Finsupp.mapDomain (exponentHom a) q).support at hy
  have hymap := Finsupp.mapDomain_support hy
  rcases Finset.mem_image.mp hymap with ⟨d, hd, rfl⟩
  exact exponentHom_isIntegral a ha d

private lemma orbitProduct_integralSupport {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (q : MvPolynomial ι ℤ) (a : ι → L)
    (ha : ∀ i, IsIntegral ℤ (a i)) : IntegralSupport (orbitProduct q a) := by
  classical
  let s : Finset (L ≃ₐ[ℚ] L) := Finset.univ
  change IntegralSupport (∏ τ ∈ s, groupPolynomial (τ ∘ a) q)
  induction s using Finset.induction with
  | empty => simpa using (integralSupport_one (L := L))
  | @insert τ s hτ ih =>
      rw [Finset.prod_insert hτ]
      apply integralSupport_mul
      · apply groupPolynomial_integralSupport
        intro i
        exact IsIntegral.map (τ.restrictScalars ℤ) (ha i)
      · exact ih

private lemma reflect_integralSupport {L : Type*} [Field L] [Algebra ℤ L]
    {u : AddMonoidAlgebra ℤ L} (hu : IntegralSupport u) : IntegralSupport (reflect u) := by
  classical
  intro y hy
  have hneg : -y ∈ u.support := by
    rw [Finsupp.mem_support_iff] at hy ⊢
    simpa [reflect_apply] using hy
  simpa using (hu (-y) hneg).neg

private lemma balancedOrbit_integralSupport {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (q : MvPolynomial ι ℤ) (a : ι → L)
    (ha : ∀ i, IsIntegral ℤ (a i)) : IntegralSupport (balancedOrbit q a) := by
  apply integralSupport_mul
  · exact orbitProduct_integralSupport q a ha
  · exact reflect_integralSupport (orbitProduct_integralSupport q a ha)

private def moment {L : Type*} [Field L] [Algebra ℤ L] (g : ℤ[X])
    (u : AddMonoidAlgebra ℤ L) : L :=
  u.sum fun y c ↦ (c : L) * Polynomial.aeval y g

private lemma mapAut_moment {L : Type*} [Field L] [Algebra ℚ L]
    (τ : L ≃ₐ[ℚ] L) (g : ℤ[X]) (u : AddMonoidAlgebra ℤ L) :
    τ (moment g u) = moment g (mapAut τ u) := by
  let h : L → ℤ →+ L := fun y ↦
    { toFun := fun c ↦ (c : L) * Polynomial.aeval y g
      map_zero' := by simp
      map_add' := by intro c d; push_cast; ring }
  change τ (u.sum fun y c ↦ h y c) =
    (Finsupp.mapDomain τ u).sum fun y c ↦ h y c
  rw [map_finsuppSum, Finsupp.sum_mapDomain_index_addMonoidHom h]
  apply Finsupp.sum_congr
  intro y hy
  dsimp [h]
  rw [map_mul]
  congr 1
  · simp
  · rw [Polynomial.aeval_def, Polynomial.aeval_def]
    calc
      τ (g.eval₂ (algebraMap ℤ L) y) =
          g.eval₂ (τ.toRingHom.comp (algebraMap ℤ L)) (τ y) :=
        Polynomial.hom_eval₂ (p := g) (f := algebraMap ℤ L) (g := τ.toRingHom) y
      _ = g.eval₂ (algebraMap ℤ L) (τ y) := by
        congr 1
        ext z
        simp

private lemma polynomial_aeval_isIntegral {L : Type*} [Field L] [Algebra ℤ L]
    {y : L} (hy : IsIntegral ℤ y) (g : ℤ[X]) : IsIntegral ℤ (Polynomial.aeval y g) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n c =>
      simpa [Polynomial.aeval_monomial, Algebra.smul_def] using
        (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ L c)).mul (hy.pow n)

private lemma moment_isIntegral {L : Type*} [Field L] [Algebra ℤ L]
    (g : ℤ[X]) {u : AddMonoidAlgebra ℤ L} (hu : IntegralSupport u) :
    IsIntegral ℤ (moment g u) := by
  change IsIntegral ℤ (∑ y ∈ u.support, (u y : L) * Polynomial.aeval y g)
  exact IsIntegral.sum _ fun y hy ↦ by
    simpa using
      (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ L (u y))).mul
        (polynomial_aeval_isIntegral (hu y hy) g)

private lemma balancedOrbit_moment_isInt {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (ιL : L →ₐ[ℚ] ℂ)
    (q : MvPolynomial ι ℤ) (a : ι → L) (ha : ∀ i, IsIntegral ℤ (a i)) (g : ℤ[X]) :
    ∃ z : ℤ, (z : ℂ) = ιL (moment g (balancedOrbit q a)) := by
  let b := balancedOrbit q a
  have hfixed : ∀ τ : L ≃ₐ[ℚ] L, τ (moment g b) = moment g b := by
    intro τ
    rw [mapAut_moment, mapAut_balancedOrbit]
  obtain ⟨r, hr⟩ :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) (moment g b)).mpr hfixed
  have hintL : IsIntegral ℤ (moment g b) :=
    moment_isIntegral g (balancedOrbit_integralSupport q a ha)
  have hintC : IsIntegral ℤ (ιL (moment g b)) :=
    IsIntegral.map (ιL.restrictScalars ℤ) hintL
  have hrat : ∃ r : ℚ, ιL (moment g b) = r := by
    refine ⟨r, ?_⟩
    rw [← hr]
    simp
  obtain ⟨z, hz⟩ := (IsIntegral.exists_int_iff_exists_rat hintC).mp hrat
  exact ⟨z, hz.symm⟩

private def toComplex {L : Type*} [Field L] [Algebra ℚ L] (ιL : L →ₐ[ℚ] ℂ)
    (u : AddMonoidAlgebra ℤ L) : AddMonoidAlgebra ℤ ℂ :=
  AddMonoidAlgebra.mapDomainRingHom ℤ ιL.toRingHom.toAddMonoidHom u

private lemma toComplex_apply {L : Type*} [Field L] [Algebra ℚ L]
    (ιL : L →ₐ[ℚ] ℂ) (u : AddMonoidAlgebra ℤ L) (y : L) :
    toComplex ιL u (ιL y) = u y := by
  exact Finsupp.mapDomain_apply ιL.injective u y

private lemma map_moment {L : Type*} [Field L] [Algebra ℚ L]
    (ιL : L →ₐ[ℚ] ℂ) (g : ℤ[X]) (u : AddMonoidAlgebra ℤ L) :
    ιL (moment g u) =
      (toComplex ιL u).sum fun y c ↦ (c : ℂ) * Polynomial.aeval y g := by
  let h : ℂ → ℤ →+ ℂ := fun y ↦
    { toFun := fun c ↦ (c : ℂ) * Polynomial.aeval y g
      map_zero' := by simp
      map_add' := by intro c d; push_cast; ring }
  change ιL (u.sum fun y c ↦ (c : L) * Polynomial.aeval y g) =
    (Finsupp.mapDomain ιL u).sum fun y c ↦ h y c
  rw [Finsupp.sum_mapDomain_index_addMonoidHom h]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro y hy
  dsimp [h]
  rw [map_mul]
  congr 1
  · simp
  · rw [Polynomial.aeval_def, Polynomial.aeval_def]
    calc
      ιL (g.eval₂ (algebraMap ℤ L) y) =
          g.eval₂ (ιL.toRingHom.comp (algebraMap ℤ L)) (ιL y) :=
        Polynomial.hom_eval₂ (p := g) (f := algebraMap ℤ L) (g := ιL.toRingHom) y
      _ = g.eval₂ (algebraMap ℤ ℂ) (ιL y) := by
        congr 1
        ext z
        simp

theorem no_relation_of_integral_galois {ι L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (ιL : L →ₐ[ℚ] ℂ) (a : ι → L)
    (ha : ∀ i, IsIntegral ℤ (a i)) (hli : LinearIndependent ℚ a)
    (q : MvPolynomial ι ℤ) (hq : q ≠ 0)
    (hrel : MvPolynomial.aeval (fun i ↦ Complex.exp (ιL (a i))) q = 0) : False := by
  let bL : AddMonoidAlgebra ℤ L := balancedOrbit q a
  let b : AddMonoidAlgebra ℤ ℂ := toComplex ιL bL
  have hbL0 : bL 0 ≠ 0 := balancedOrbit_zero_ne q a hq hli
  have hb0eq : b 0 = bL 0 := by
    simpa [b] using toComplex_apply ιL bL 0
  have hb0 : b 0 ≠ 0 := hb0eq ▸ hbL0
  have hbLint : IntegralSupport bL := balancedOrbit_integralSupport q a ha
  have hbint : ∀ y ∈ b.support.erase 0, IsIntegral ℤ y := by
    intro y hy
    have hsupp : b.support = Finset.image ιL bL.support := by
      dsimp [b, toComplex]
      exact Finsupp.mapDomain_support_of_injective ιL.injective bL
    have himage : y ∈ Finset.image ιL bL.support := by
      rw [← hsupp]
      exact Finset.mem_of_mem_erase hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp himage
    exact IsIntegral.map (ιL.restrictScalars ℤ) (hbLint x hx)
  have hbexp : expEval ιL bL = 0 := expEval_balancedOrbit_zero ιL q a hrel
  have hexp : b.sum (fun y c ↦ (c : ℂ) * Complex.exp y) = 0 := by
    let H : ℂ → ℤ →+ ℂ := fun y ↦
      { toFun := fun c ↦ (c : ℂ) * Complex.exp y
        map_zero' := by simp
        map_add' := by intro c d; push_cast; ring }
    change (Finsupp.mapDomain ιL bL).sum (fun y c ↦ H y c) = 0
    rw [Finsupp.sum_mapDomain_index_addMonoidHom H]
    simpa [H, expEval_apply] using hbexp
  have hbrel : (b 0 : ℂ) +
      ∑ y ∈ b.support.erase 0, (b y : ℂ) * Complex.exp y = 0 := by
    let H : ℂ → ℤ → ℂ := fun y c ↦ (c : ℂ) * Complex.exp y
    change b.sum H = 0 at hexp
    have hmem : 0 ∈ b.support := Finsupp.mem_support_iff.mpr hb0
    calc
      (b 0 : ℂ) + ∑ y ∈ b.support.erase 0, (b y : ℂ) * Complex.exp y =
          H 0 (b 0) + ∑ y ∈ b.support.erase 0, H y (b y) := by simp [H]
      _ = b.sum H := by
        change H 0 (b 0) + ∑ y ∈ b.support.erase 0, H y (b y) =
          ∑ y ∈ b.support, H y (b y)
        rw [add_comm, Finset.sum_erase_add _ _ hmem]
      _ = 0 := hexp
  have hmoment : ∀ g : ℤ[X], ∃ z : ℤ,
      (z : ℂ) = ∑ y ∈ b.support.erase 0, (b y : ℂ) * Polynomial.aeval y g := by
    intro g
    obtain ⟨z, hz⟩ := balancedOrbit_moment_isInt ιL q a ha g
    rw [map_moment] at hz
    let H : ℂ → ℤ → ℂ := fun y c ↦ (c : ℂ) * Polynomial.aeval y g
    change (z : ℂ) = b.sum H at hz
    have hmem : 0 ∈ b.support := Finsupp.mem_support_iff.mpr hb0
    have hsum : b.sum H = H 0 (b 0) +
        ∑ y ∈ b.support.erase 0, H y (b y) := by
      change (∑ y ∈ b.support, H y (b y)) = _
      rw [← Finset.sum_erase_add _ _ hmem]
      ac_rfl
    have hzero : (((b 0) * g.eval 0 : ℤ) : ℂ) = H 0 (b 0) := by
      dsimp [H]
      push_cast
      rw [show Polynomial.aeval (0 : ℂ) g = ((g.eval 0 : ℤ) : ℂ) by
        simpa using Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval
          (A := ℂ) (0 : ℤ) g]
    refine ⟨z - b 0 * g.eval 0, ?_⟩
    rw [Int.cast_sub, hz, hzero, hsum]
    ring
  exact Submission.Helpers.no_integral_relation_exp b hb0 hbint hbrel hmoment

theorem no_relation_of_integral {ι : Type*} [Finite ι] (x : ι → ℂ)
    (hx : ∀ i, IsIntegral ℤ (x i)) (hli : LinearIndependent ℚ x)
    (q : MvPolynomial ι ℤ) (hq : q ≠ 0)
    (hrel : MvPolynomial.aeval (fun i ↦ Complex.exp (x i)) q = 0) : False := by
  let K := IntermediateField.adjoin ℚ (Set.range x)
  letI : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun y hy ↦ by
      obtain ⟨i, rfl⟩ := hy
      exact (hx i).tower_top
  let L := IntermediateField.normalClosure ℚ K ℂ
  letI : FiniteDimensional ℚ L :=
    normalClosure.is_finiteDimensional ℚ K ℂ
  letI : Normal ℚ L :=
    (Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (F := ℚ) (K := K) (L := ℂ) fun _ ↦ IsAlgClosed.splits _).normal
  let hG : IsGalois ℚ L := ⟨⟩
  let a : ι → L := fun i ↦
    ⟨x i, IntermediateField.le_normalClosure K
      (IntermediateField.subset_adjoin ℚ (Set.range x) (Set.mem_range_self i))⟩
  have ha : ∀ i, IsIntegral ℤ (a i) := by
    intro i
    apply (isIntegral_algHom_iff (L.val.restrictScalars ℤ) L.val.injective).mp
    simpa [a] using hx i
  have hlia : LinearIndependent ℚ a := by
    apply LinearIndependent.of_comp L.val.toLinearMap
    simpa [Function.comp_def, a] using hli
  exact @no_relation_of_integral_galois ι L _ _ _ hG L.val a ha hlia q hq (by
    have heq : (fun i ↦ Complex.exp (L.val (a i))) = fun i ↦ Complex.exp (x i) := by
      funext i
      rfl
    exact (congrArg (fun f : ι → ℂ ↦ MvPolynomial.aeval f q) heq).trans hrel)

theorem algebraicIndependent_of_generators_of_finite {ι : Type*} [Finite ι]
    (y z : ι → ℂ) (hz : AlgebraicIndependent ℚ z)
    (hzmem : ∀ i, z i ∈ Algebra.adjoin ℚ (Set.range y)) :
    AlgebraicIndependent ℚ y := by
  let B := Algebra.adjoin ℚ (Set.range y)
  let yB : ι → B := fun i ↦
    ⟨y i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  let zB : ι → B := fun i ↦ ⟨z i, hzmem i⟩
  have hzB : AlgebraicIndependent ℚ zB := by
    apply AlgebraicIndependent.of_comp B.val
    rw [show B.val ∘ zB = z by
      funext i
      rfl]
    exact hz
  have hgen : Algebra.adjoin ℚ (Set.range yB) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    intro b
    have hb := b.property
    change (b : ℂ) ∈ Algebra.adjoin ℚ (Set.range y) at hb
    rw [Algebra.adjoin_range_eq_range_aeval] at hb
    obtain ⟨p, hp⟩ := hb
    refine ⟨p, ?_⟩
    apply Subtype.val_injective
    have hcomp : B.val.comp (MvPolynomial.aeval yB) = MvPolynomial.aeval y := by
      ext i
      simp [yB]
    exact (AlgHom.congr_fun hcomp p).trans hp
  letI : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range yB)) B := by
    constructor
    intro b
    have hb : b ∈ Algebra.adjoin ℚ (Set.range yB) := by
      rw [hgen]
      trivial
    let b' : Algebra.adjoin ℚ (Set.range yB) := ⟨b, hb⟩
    have heq : algebraMap (Algebra.adjoin ℚ (Set.range yB)) B b' = b := rfl
    rw [← heq]
    exact isAlgebraic_algebraMap b'
  have hyB : AlgebraicIndependent ℚ yB :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite
      (A := B) ℚ yB hzB.lift_cardinalMk_le_trdeg).1
  have hmap := hyB.map' (f := B.val) Subtype.val_injective
  rw [show B.val ∘ yB = y by
    funext i
    rfl] at hmap
  exact hmap

end

end Submission.Galois
