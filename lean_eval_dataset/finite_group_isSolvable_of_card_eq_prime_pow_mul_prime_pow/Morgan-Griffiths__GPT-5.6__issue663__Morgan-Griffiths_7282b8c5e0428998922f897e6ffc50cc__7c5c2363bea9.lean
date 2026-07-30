import Mathlib
namespace Submission

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
universe u v w

open scoped IsMulCommutative

private lemma commutator_lt_of_normalizer_le_centralizer
    {T : Type u} [Group T] [Finite T]
    {r : ℕ} (hr : Nat.Prime r) (P : Sylow r T) (hrd : r ∣ Nat.card T)
    (hP : Subgroup.normalizer (P : Subgroup T) ≤
      Subgroup.centralizer (P : Set T)) :
    commutator T < (⊤ : Subgroup T) := by
  classical
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  -- The transfer homomorphism has a complementary kernel.  Since `P` is
  -- nontrivial its kernel is proper, and every homomorphism to its abelian
  -- image kills the commutator.
  haveI iC : IsMulCommutative P :=
    ⟨⟨fun a b => Subtype.ext (hP (Subgroup.le_normalizer b.2) a a.2)⟩⟩
  let f := MonoidHom.transferSylow P hP
  refine lt_of_le_of_lt (Abelianization.commutator_subset_ker f) ?_
  have hne : (P : Subgroup T) ≠ ⊥ := P.ne_bot_of_dvd_card hrd
  by_contra! h
  have htop : f.ker = (⊤ : Subgroup T) := (not_lt_top_iff.mp h)
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hP
  have : (P : Subgroup T) = ⊥ := by
    change Subgroup.IsComplement' f.ker (P : Subgroup T) at hcomp
    rw [htop] at hcomp
    exact (Subgroup.isComplement'_top_left).1 hcomp
  exact hne this

private lemma commutator_lt_of_cyclic_minSylow
    {T : Type u} [Group T] [Finite T] [Nontrivial T]
    (hm : (Nat.card T).minFac.Prime)
    (P : Sylow (Nat.card T).minFac T) (hP : IsCyclic P) :
    commutator T < (⊤ : Subgroup T) := by
  classical
  letI : Fact (Nat.card T).minFac.Prime := ⟨hm⟩
  let f := MonoidHom.transferSylow P (hP.normalizer_le_centralizer rfl)
  refine lt_of_le_of_lt (Abelianization.commutator_subset_ker f) ?_
  have hne : (P : Subgroup T) ≠ ⊥ :=
    P.ne_bot_of_dvd_card (Nat.card T).minFac_dvd
  by_contra! h
  have htop : f.ker = (⊤ : Subgroup T) := (not_lt_top_iff.mp h)
  have hcomp := hP.isComplement' rfl
  -- a complement whose left term is the whole group forces `P` to be trivial
  have : (P : Subgroup T) = ⊥ := by
    have hh : Subgroup.IsComplement' (⊤ : Subgroup T) (P : Subgroup T) := by
      change Subgroup.IsComplement' f.ker (P : Subgroup T) at hcomp
      rw [htop] at hcomp
      exact hcomp
    exact (Subgroup.isComplement'_top_left).1 hh
  exact hne this

private lemma two_le_factorization_of_not_isCyclic_sylow
    {T : Type u} [Group T] [Finite T]
    {r : ℕ} (hr : Nat.Prime r) (P : Sylow r T)
    (hP : ¬ IsCyclic P.1) :
    2 ≤ (Nat.card T).factorization r := by
  classical
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  by_contra! hlt
  have hle : (Nat.card T).factorization r ≤ 1 := (Nat.lt_succ_iff.mp hlt)
  have hd : Nat.card P ∣ r := by
    rw [P.card_eq_multiplicity]
    rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hle) with h0 | h1
    · simp [h0]
    · simp [h1]
  exact hP (isCyclic_of_card_dvd_prime hd)

private lemma minFac_prime_pow_mul_eq_left
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : a ≠ 0) (hle : p ≤ q) :
    (p ^ a * q ^ b).minFac = p := by
  have hd : p ∣ p ^ a * q ^ b := dvd_mul_of_dvd_left (dvd_pow_self p ha) _
  have h₁ : (p ^ a * q ^ b).minFac ≤ p :=
    Nat.minFac_le_of_dvd hp.two_le hd
  have hne : p ^ a * q ^ b ≠ 1 := by
    intro h
    have hx : p ∣ 1 := h ▸ hd
    exact hp.not_dvd_one hx
  have h₂ : p ≤ (p ^ a * q ^ b).minFac := by
    have hall : ∀ r : ℕ, r.Prime → r ∣ p ^ a * q ^ b → p ≤ r := by
      intro r hr hrdiv
      rcases (hr.dvd_mul).1 hrdiv with hl | hr'
      · have hh : r ∣ p := hr.dvd_of_dvd_pow hl
        have he : r = p := (Nat.dvd_prime_two_le hp hr.two_le).1 hh
        simpa [he]
      · have hh : r ∣ q := hr.dvd_of_dvd_pow hr'
        have he : r = q := (Nat.dvd_prime_two_le hq hr.two_le).1 hh
        simpa [he] using hle
    exact (Nat.le_minFac.2 hall).resolve_left hne
  exact Nat.le_antisymm h₁ h₂

private lemma sylow_isCyclic_of_left_one
    {T : Type u} [Group T] [Finite T]
    {p q b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hcard : Nat.card T = p ^ (1:ℕ) * q ^ b) (P : Sylow p T) :
    IsCyclic P := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hnot : ¬ p ∣ q ^ b := by
    intro h
    have h' : p ∣ q := hp.dvd_of_dvd_pow h
    exact hpq ((Nat.dvd_prime_two_le hq hp.two_le).1 h')
  have hf : (Nat.card T).factorization p = 1 := by
    rw [hcard, pow_one,
      Nat.factorization_mul hp.ne_zero (pow_ne_zero b hq.ne_zero),
      Finsupp.add_apply, hp.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hnot]
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [P.card_eq_multiplicity, hf, pow_one]

/-- The elementary divisor fact used in reducing Burnside's statement to simple
finite groups.  It is useful to keep the induction on the order rather than on
the two exponents: a subgroup and a quotient again have orders with no other
prime factors. -/
private lemma dvd_prime_pow_mul_prime_pow
    {p q a b n : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hn : n ≠ 0) (hdiv : n ∣ p ^ a * q ^ b) :
    ∃ c d : ℕ, n = p ^ c * q ^ d := by
  -- Remove the p-primary part.  `ordCompl[p]` is particularly handy here,
  -- since its functoriality for divisibility is in the library.
  have hnot : ¬ p ∣ q ^ b := by
    intro h
    have hpq' : p ∣ q := hp.dvd_of_dvd_pow h
    exact hpq ((Nat.dvd_prime_two_le hq hp.two_le).mp hpq')
  have hcompl : ordCompl[p] n ∣ q ^ b := by
    have h' := Nat.ordCompl_dvd_ordCompl_of_dvd hdiv p
    -- on the right the p-part of `p^a*q^b` disappears
    simpa [Nat.ordCompl_pow_mul_of_not_dvd a hp hnot] using h'
  rcases (Nat.dvd_prime_pow hq).1 hcompl with ⟨d, hd, hd'⟩
  refine ⟨n.factorization p, d, ?_⟩
  -- multiply the part we removed back in
  calc
    n = ordProj[p] n * ordCompl[p] n := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
    _ = p ^ n.factorization p * q ^ d := by rw [hd']




/-- A faithful linear representation cannot send a noncentral element to a
scalar.  This elementary part of the character-theoretic step is independent
of finite dimensionality: the kernel and the fact that scalars commute with
all linear maps already suffice. -/
private lemma mem_center_of_scalar_of_ker_eq_bot
    {H : Type u} [Group H]
    {k : Type v} [CommSemiring k]
    {V : Type w} [AddCommMonoid V] [Module k V]
    (ρ : Representation k H V)
    (hker : MonoidHom.ker ρ = (⊥ : Subgroup H))
    {x : H} (c : k) (hx : ρ x = c • LinearMap.id) :
    x ∈ Subgroup.center H := by
  -- `ker = ⊥` is just faithfulness for a homomorphism out of a group.
  have hi : Function.Injective ρ :=
    (MonoidHom.ker_eq_bot_iff ρ).1 hker
  apply (Subgroup.mem_center_iff).2
  intro y
  apply hi
  -- We do not need matrices here.  A linear endomorphism commutes with a
  -- scalar multiple of the identity.
  ext z
  simp [map_mul, hx, Module.End.mul_apply]


/-- The other elementary character calculation in Burnside's argument is the
value of the regular character off `1`.  We spell it out for the
`Representation.leftRegular` representation.  On the standard `Finsupp`
basis the matrix permutes the basis vectors by left multiplication, and every
diagonal coefficient is zero when the multiplier is not `1`. -/
private lemma character_leftRegular_of_ne_one
    {H : Type u} [Group H] [Fintype H]
    {k : Type v} [Field k]
    (g : H) (hg : g ≠ 1) :
    (Representation.leftRegular k H).character g = 0 := by
  classical
  rw [Representation.character, LinearMap.trace_eq_matrix_trace k
      (Finsupp.basisSingleOne (R := k))]
  unfold Matrix.trace
  apply Finset.sum_eq_zero
  intro i hi
  dsimp [Matrix.diag]
  rw [LinearMap.toMatrix_apply]
  -- make the basis vector explicit before applying `ofMulAction_single`;
  -- `leftRegular` is an abbreviation for this representation.
  change (Finsupp.basisSingleOne.repr
    ((Representation.leftRegular k H) g (Finsupp.single i 1))) i = 0
  rw [Representation.ofMulAction_single]
  have hgi : g * i ≠ i := by
    intro h
    apply hg
    apply mul_right_cancel (b := i)
    simpa using h
  -- The coefficient of a single basis vector at a different index is zero.
  simpa [Finsupp.basisSingleOne, Finsupp.single_apply, hgi]


/-- A tiny arithmetic end of the usual regular-character contradiction.  A
prime inverse is not an algebraic integer (also after embedding the rationals
in `ℂ`).  Isolating it is useful because in Burnside's proof the final regular
character equation says precisely that such an inverse is integral. -/
private lemma not_isIntegral_inv_natCast_complex_prime
    {r : ℕ} (hr : Nat.Prime r) :
    ¬ IsIntegral ℤ ((r : ℂ)⁻¹) := by
  intro h
  have h' : IsIntegral ℤ ((r : ℚ)⁻¹) := by
    apply (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ)
      (algebraMap ℚ ℂ).injective).mp
    simpa using h
  -- A rational integral over the integers is an integer.  Here we use the
  -- integral-root theorem for the fraction field of the UFD `ℤ`.
  have hi : IsLocalization.IsInteger ℤ ((r : ℚ)⁻¹) :=
    UniqueFactorizationMonoid.integer_of_integral h'
  rcases hi with ⟨z, hz⟩
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hm : (z : ℚ) * (r : ℚ) = 1 := by
    change (algebraMap ℤ ℚ z) * (r : ℚ) = 1
    rw [hz]
    exact inv_mul_cancel₀ hr0
  have hm' : z * (r : ℤ) = 1 := by
    exact_mod_cast hm
  have hd : (r : ℤ) ∣ 1 := by
    refine ⟨z, ?_⟩
    simpa [mul_comm] using hm'.symm
  have hd' : r ∣ 1 := by exact_mod_cast hd
  exact hr.not_dvd_one hd'


/-- Roots of unity in the coefficient field are algebraic integers.  Using
`X^n-1` rather than a cyclotomic polynomial is convenient here: all that is
needed for the character argument is integrality. -/
private lemma isIntegral_of_pow_eq_one_complex
    (z : ℂ) {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : IsIntegral ℤ z := by
  refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
  · simpa using (Polynomial.monic_X_pow_sub_C (R := ℤ) 1 hn.ne')
  · simp [hz]

/-- If a complex endomorphism is of finite order, its trace is an algebraic
integer.  One does not need to choose a splitting into eigenspaces.  The
characteristic polynomial splits over `ℂ`; every root is an eigenvalue and
hence is killed by `X^n-1`.  The trace is the sum of these roots, with
multiplicities. -/
private lemma isIntegral_trace_of_pow_eq_one
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : Module.End ℂ W) {n : ℕ} (hn : 0 < n) (hA : A ^ n = 1) :
    IsIntegral ℤ (LinearMap.trace ℂ W A) := by
  classical
  have hs : A.charpoly.Splits := IsAlgClosed.splits _
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits hs]
  apply IsIntegral.multiset_sum
  intro z hz
  apply isIntegral_of_pow_eq_one_complex z hn
  have hroot : A.charpoly.IsRoot z :=
    (Polynomial.mem_roots (LinearMap.charpoly_monic A).ne_zero).1 hz
  have heig : A.HasEigenvalue z :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly A z).2 hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hvpow := hv.pow_apply n
  rw [hA] at hvpow
  change v = z ^ n • v at hvpow
  have hvzero : ((1 : ℂ) - z ^ n) • v = 0 := by
    rw [sub_smul, one_smul, sub_eq_zero]
    exact hvpow
  have hz0 : (1 : ℂ) - z ^ n = 0 :=
    (smul_eq_zero.mp hvzero).resolve_right hv.2
  exact (sub_eq_zero.mp hz0).symm

/-- Values of ordinary complex characters of a finite group are algebraic
integers.  This is the only integrality assertion in the last elementary
arithmetic step that only uses a *single* element of the group. -/
private lemma isIntegral_character_complex
    {H : Type*} [Group H] [Fintype H]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ H W) (g : H) :
    IsIntegral ℤ (σ.character g) := by
  unfold Representation.character
  apply isIntegral_trace_of_pow_eq_one (A := σ g)
      (Nat.card_pos (α := H))
  rw [← map_pow]
  have he : g ^ Nat.card H = (1 : H) := by
    simpa [Nat.card_eq_fintype_card] using (pow_card_eq_one (x := g))
  rw [he, map_one]

private noncomputable def burnsideClassFinset {H : Type*} [Group H] [Fintype H] (x:H) : Finset H :=
  (Set.toFinite (ConjClasses.mk x).carrier).toFinset

@[simp] private lemma mem_burnsideClassFinset {H : Type*} [Group H] [Fintype H] (x y:H) :
    y ∈ burnsideClassFinset x ↔ y ∈ (ConjClasses.mk x).carrier := by
  classical
  simp [burnsideClassFinset]

private lemma burnside_class_scalar
    {H : Type u} [Group H] [Fintype H]
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) [Representation.IsIrreducible ρ]
    (x : H) :
    ∃ c : ℂ, (∑ y ∈ burnsideClassFinset x, ρ y) = c • LinearMap.id := by
  classical
  -- conjugation permutes the class
  let C := (ConjClasses.mk x).carrier
  letI : Fintype C := Fintype.ofFinite C
  have hmem (g y : H) (hy : y ∈ C) : g * y * g⁻¹ ∈ C := by
    -- use class equality
    have hy' : ConjClasses.mk y = ConjClasses.mk x :=
      (ConjClasses.mem_carrier_iff_mk_eq).1 hy
    apply (ConjClasses.mem_carrier_iff_mk_eq).2
    apply (ConjClasses.mk_eq_mk_iff_isConj).2
    have h1 : IsConj (g*y*g⁻¹) y := by
      apply (isConj_iff).2
      refine ⟨g⁻¹, ?_⟩
      simp [mul_assoc]
    exact h1.trans ((ConjClasses.mk_eq_mk_iff_isConj).1 hy')

  let phi (g : H) : C ≃ C :=
    { toFun := fun y => ⟨g * (y:H) * g⁻¹, hmem g y.1 y.2⟩
      invFun := fun y => ⟨g⁻¹ * (y:H) * (g⁻¹)⁻¹, hmem g⁻¹ y.1 y.2⟩
      left_inv := by
        intro y
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := by
        intro y
        apply Subtype.ext
        simp [mul_assoc] }
  let T : Module.End ℂ V := ∑ y : C, ρ (y : H)
  have hcomm (g : H) (v : V) : T (ρ g v) = ρ g (T v) := by
    change (∑ y : C, ρ (y : H)) (ρ g v) = ρ g ((∑ y : C, ρ (y : H)) v)
    simp only [LinearMap.sum_apply]
    -- rewrite products
    simp only [← Module.End.mul_apply, ← map_mul]
    -- RHS distribute
    rw [map_sum]
    -- rw on rhs terms
    -- actually map_sum uses linear map ρ g
    simp only [← Module.End.mul_apply, ← map_mul]
    -- need reindex LHS with phi g
    refine (Equiv.sum_comp (phi g) (fun y : C => (ρ ((y:H) * g)) v)).symm.trans ?_
    apply Finset.sum_congr rfl
    intro y hy
    congr 2
    dsimp [phi]
    -- (g*y*g^-1) * g = g*y
    simp [mul_assoc]
  let F : Representation.IntertwiningMap ρ ρ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ T hcomm
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ:=ρ) (k:=ℂ)).2 F
  refine ⟨c, ?_⟩
  have hc' := congrArg Representation.IntertwiningMap.toLinearMap hc
  -- evaluate algebraMap
  change _ = _ at hc'
  -- inspect
  -- exact?
  change c • LinearMap.id = T at hc'
  calc
    (∑ y ∈ burnsideClassFinset x, ρ y) = ∑ y : C, ρ (y:H) := by
      exact Finset.sum_subtype (burnsideClassFinset x)
        (fun y => (mem_burnsideClassFinset x y)) (fun y => ρ y)
    _ = T := rfl
    _ = c • LinearMap.id := hc'.symm

private lemma burnside_class_scalar_integral
    {H : Type u} [Group H] [Fintype H]
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) [Representation.IsIrreducible ρ]
    (x : H) :
    ∃ c : ℂ, (∑ y ∈ burnsideClassFinset x, ρ y) = c • LinearMap.id ∧ IsIntegral ℤ c := by
  classical
  obtain ⟨c, hc⟩ := burnside_class_scalar ρ x
  refine ⟨c, hc, ?_⟩
  let a : MonoidAlgebra ℤ H := ∑ y ∈ burnsideClassFinset x, MonoidAlgebra.single y 1
  -- finite module
  letI : Module.Finite ℤ (MonoidAlgebra ℤ H) := by
    change Module.Finite ℤ (H →₀ ℤ)
    infer_instance
  have ha : IsIntegral ℤ a := IsIntegral.of_finite ℤ a
  let Φ : MonoidAlgebra ℤ H →ₐ[ℤ] Module.End ℂ V :=
    (MonoidAlgebra.lift ℤ (Module.End ℂ V) H) ρ
  have him : Φ a = (∑ y ∈ burnsideClassFinset x, ρ y) := by
    simp [a, Φ, MonoidAlgebra.lift_single]
  have hT : IsIntegral ℤ (c • (LinearMap.id : Module.End ℂ V)) := by
    rw [← hc, ← him]
    exact ha.map Φ
  -- algebra map C into end
  let f : ℂ →ₐ[ℤ] Module.End ℂ V := IsScalarTower.toAlgHom ℤ ℂ (Module.End ℂ V)
  have hf : Function.Injective f := by
    intro r s h
    -- evaluate at a nonzero vector
    have hnM : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) ρ.asModule
    letI : Nontrivial V := hnM
    have hi : Function.Injective (algebraMap ℂ (Module.End ℂ V)) :=
      FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ V)
    exact hi h
  have he : f c = c • (LinearMap.id : Module.End ℂ V) := by
    rfl
  rw [← (isIntegral_algHom_iff f hf), he]
  exact hT
private lemma burnside_trace_class_scalar
    {H : Type u} [Group H] [Fintype H]
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (x:H) (c:ℂ)
    (hc : (∑ y ∈ burnsideClassFinset x, ρ y) = c • LinearMap.id) :
    ((burnsideClassFinset x).card : ℂ) * ρ.character x = c * Module.finrank ℂ V := by
  classical
  have ht := congrArg (LinearMap.trace ℂ V) hc
  have ht' : (∑ y ∈ burnsideClassFinset x, ρ.character y) = c * (Module.finrank ℂ V : ℂ) := by
    simpa [Representation.character, map_sum] using ht
  calc
    ((burnsideClassFinset x).card : ℂ) * ρ.character x =
        ∑ y ∈ burnsideClassFinset x, ρ.character x := by simp
    _ = ∑ y ∈ burnsideClassFinset x, ρ.character y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hmk : ConjClasses.mk y = ConjClasses.mk x :=
        (ConjClasses.mem_carrier_iff_mk_eq).1 ((mem_burnsideClassFinset x y).1 hy)
      obtain ⟨g, hg⟩ := (isConj_iff).1 ((ConjClasses.mk_eq_mk_iff_isConj).1 hmk)
      -- hg : g*y*g^-1=x
      simpa [hg] using (Representation.char_conj ρ y g)
    _ = _ := ht'
private lemma burnside_integral_div_of_coprime_relation
 (m f : ℕ) (χ c : ℂ)
 (hf0 : f ≠ 0)
 (hcop : Nat.Coprime m f)
 (heq : (m : ℂ) * χ = c * f)
 (hc : IsIntegral ℤ c) (hχ : IsIntegral ℤ χ) :
 IsIntegral ℤ (χ / f) := by
  classical
  have hci : IsCoprime (m : ℤ) (f : ℤ) := hcop.isCoprime
  obtain ⟨a,b, hab⟩ := hci
  have habc : (a : ℂ) * m + (b : ℂ) * f = 1 := by
    exact_mod_cast hab
  have hid : χ / (f:ℂ) = (a:ℂ) * c + (b:ℂ) * χ := by
    have hf' : (f:ℂ) ≠ 0 := by exact_mod_cast hf0
    field_simp
    -- goal inspect
    linear_combination -χ * habc + (a:ℂ) * heq
  rw [hid]
  exact ((isIntegral_intCast _).mul hc).add ((isIntegral_intCast _).mul hχ)
-- assume isIntegral character as arg
private lemma burnside_classFinset_card_of_natCard {H:Type*} [Group H] [Fintype H]
 (x:H) (q d:ℕ) (h: Nat.card (ConjClasses.mk x).carrier = q^d) :
 (burnsideClassFinset x).card = q^d := by
  classical
  letI : Fintype (ConjClasses.mk x).carrier := Fintype.ofFinite _
  have h' : Fintype.card (ConjClasses.mk x).carrier = q^d := by
    simpa [Nat.card_eq_fintype_card] using h
  simpa [burnsideClassFinset] using h'

private lemma burnside_integral_character_average {q:ℕ} (hq:Nat.Prime q) {d:ℕ}
    {H : Type u} [Group H] [Fintype H]
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) [Representation.IsIrreducible ρ]
    (x:H) (hsize : (burnsideClassFinset x).card = q^d)
    (hn : ¬ q ∣ Module.finrank ℂ V)
    (hz : IsIntegral ℤ (ρ.character x)) :
    IsIntegral ℤ (ρ.character x / (Module.finrank ℂ V : ℂ)) := by
  classical
  obtain ⟨c, hc, hci⟩ := burnside_class_scalar_integral ρ x
  have he := burnside_trace_class_scalar ρ x c hc
  have f0 : Module.finrank ℂ V ≠ 0 := by
    -- simple nonzero use nontrivial
    have hnM : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) ρ.asModule
    letI : Nontrivial V := hnM
    exact (Module.finrank_pos).ne'
  have hcopq : Nat.Coprime q (Module.finrank ℂ V) := (Nat.Prime.coprime_iff_not_dvd hq).2 hn
  have hcop : Nat.Coprime (q^d) (Module.finrank ℂ V) := (hcopq.pow_left _)
  apply burnside_integral_div_of_coprime_relation (q^d) (Module.finrank ℂ V) (ρ.character x) c f0 hcop
  · simpa [hsize] using he
  · exact hci
  · exact hz


/-- The integer arithmetic at the end of the regular character argument.
We isolate it from the construction of constituents.  If the non-trivial
constituents have degrees `f i`, their contributions at `x` are `z i`.
Constituents of degree prime to `r` vanish; the other terms are visibly
multiples of `r` *as algebraic integers*.  Thus the regular-character
identity `0 = 1 + ...` would make `1/r` an algebraic integer.

This form, in terms of a finite family, is useful without making any choices
of a set of representatives of irreducibles. -/
private lemma isIntegral_inv_of_character_family
    {r n : ℕ} (hr : Nat.Prime r)
    (f : Fin n → ℕ) (z : Fin n → ℂ)
    (hint : ∀ i, IsIntegral ℤ (z i))
    (heq : (0 : ℂ) = 1 + ∑ i : Fin n, (f i : ℂ) * z i)
    (hz : ∀ i : Fin n, ¬ r ∣ f i → z i = 0) :
    IsIntegral ℤ ((r : ℂ)⁻¹) := by
  classical
  let t : ℂ := ∑ i : Fin n, ((f i / r : ℕ) : ℂ) * z i
  have ht : IsIntegral ℤ t := by
    dsimp [t]
    apply IsIntegral.sum
    intro i hi
    exact (isIntegral_natCast (f i / r)).mul (hint i)
  have hterm (i : Fin n) :
      (f i : ℂ) * z i =
        (r : ℂ) * (((f i / r : ℕ) : ℂ) * z i) := by
    by_cases hd : r ∣ f i
    · have hm : r * (f i / r) = f i := Nat.mul_div_cancel' hd
      have hm' : (r : ℂ) * ((f i / r : ℕ) : ℂ) = (f i : ℂ) := by
        exact_mod_cast hm
      calc
        (f i : ℂ) * z i =
            ((r : ℂ) * ((f i / r : ℕ) : ℂ)) * z i := by rw [hm']
        _ = (r : ℂ) * (((f i / r : ℕ) : ℂ) * z i) := by ring
    · have hi := hz i hd
      simp [hi]
  have hsum : (∑ i : Fin n, (f i : ℂ) * z i) = (r : ℂ) * t := by
    calc
      (∑ i : Fin n, (f i : ℂ) * z i) =
          ∑ i : Fin n, (r : ℂ) * (((f i / r : ℕ) : ℂ) * z i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i
      _ = (r : ℂ) * t := by
            simp [t, Finset.mul_sum]
  have hrt : (r : ℂ) * t = -1 := by
    rw [hsum] at heq
    exact eq_neg_of_add_eq_zero_right heq.symm
  have hr0 : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne_zero
  have hinv : (r : ℂ)⁻¹ = -t := by
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      (r : ℂ)⁻¹ + t = (r : ℂ)⁻¹ * (1 + (r : ℂ) * t) := by
        field_simp
      _ = 0 := by rw [hrt]; simp
  rw [hinv]
  exact ht.neg



-- The numerical Burnside averaging lemma.  We work in the cyclotomic
-- subfield generated by the roots so that the field norm has only finitely
-- many factors.  This avoids using an embedding of all of `ℂ` into a number
-- field.
private lemma burnside_isIntegralQpow (z:ℂ) {N:ℕ} (hN : N ≠ 0) (h:z^N=1) : IsIntegral ℚ z := by
  refine ⟨Polynomial.X ^ N - 1, ?_, ?_⟩
  · simpa using (Polynomial.monic_X_pow_sub_C (R := ℚ) 1 hN)
  · simp [h]

private lemma burnside_integral_average_roots_norm {m N : ℕ} (hm : m ≠ 0) (hN : N ≠ 0)
    (α : Fin m → ℂ) (hα : ∀ i, α i ^ N = 1)
    (hu : IsIntegral ℤ ((∑ i, α i) / (m : ℂ))) :
    (∑ i, α i) / (m : ℂ) = 0 ∨ ‖(∑ i, α i) / (m : ℂ)‖ = 1 := by
  classical
  -- build the cyclotomic subfield generated by the entries
  let L := IntermediateField.adjoin ℚ (Set.range α)
  let al (i : Fin m) : L :=
    ⟨α i, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self _)⟩
  let t : L := (∑ i, al i) / (algebraMap ℚ L (m : ℚ))
  have htval : (t : ℂ) = (∑ i, α i) / (m : ℂ) := by
    change ((↑((∑ i, al i) / (algebraMap ℚ L (m : ℚ))) : L) : ℂ) = _ --?
    simp [al]
  -- integrality inside this field
  have htint : IsIntegral ℤ t := by
    apply (isIntegral_algHom_iff (L.val.restrictScalars ℤ)
      (fun _ _ h => Subtype.ext h)).mp
    change IsIntegral ℤ (t : ℂ)
    rw [htval]
    exact hu
  -- roots unity integral => finite dimensional
  letI : FiniteDimensional ℚ L := by
    apply IntermediateField.finiteDimensional_adjoin
      (S := Set.range α)
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    -- integral over Q follows from power root monic over Z or Q
    exact (show IsIntegral ℚ (α i) from
      (burnside_isIntegralQpow (α i) hN (hα i)))
  letI : Algebra.IsSeparable ℚ L :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hroot (σ : L →ₐ[ℚ] ℂ) (i : Fin m) : (σ (al i)) ^ N = 1 := by
    have haL : (al i) ^ N = (1 : L) := by
      apply Subtype.ext
      exact hα i
    simpa [map_pow] using congrArg σ haL
  have hbound (σ : L →ₐ[ℚ] ℂ) : ‖σ t‖ ≤ 1 := by
    -- all conjugates are averages of roots of unity
    have hn : ∀ i : Fin m, ‖σ (al i)‖ = (1:ℝ) :=
      fun i => Complex.norm_eq_one_of_pow_eq_one (hroot σ i) hN
    have hs : ‖∑ i, σ (al i)‖ ≤ (m:ℝ) := by
      simpa [hn] using (norm_sum_le (s := Finset.univ) (f := fun i : Fin m => σ (al i)))
    change ‖σ ((∑ i, al i) / (algebraMap ℚ L (m : ℚ)))‖ ≤ _
    rw [map_div₀, map_sum, norm_div]
    rw [σ.commutes]
    -- the denominator is the positive integer m
    have hden : ‖(algebraMap ℚ ℂ) (m : ℚ)‖ = (m : ℝ) := by
      simpa using (Complex.norm_natCast m)
    rw [hden]
    apply (div_le_iff₀ (by exact_mod_cast (Nat.pos_of_ne_zero hm) : (0:ℝ)<(m:ℝ))).2
    simpa using hs
  -- rule out a strict inequality by taking the field norm to Q
  have hbase : ‖( (L.val : L →ₐ[ℚ] ℂ) t)‖ =
        ‖(∑ i, α i) / (m : ℂ)‖ := by
    change ‖(t : ℂ)‖ = _
    rw [htval]
  have hle : ‖(∑ i, α i) / (m : ℂ)‖ ≤ 1 := by
    rw [← hbase]
    exact hbound (L.val)
  by_cases hzval : (∑ i, α i) / (m : ℂ) = 0
  · exact Or.inl hzval
  right
  have hpos : 0 < ‖(∑ i, α i) / (m : ℂ)‖ :=
    (norm_pos_iff).2 hzval
  have hnlt : ¬ ‖(∑ i, α i) / (m : ℂ)‖ < 1 := by
    intro hstrict
    have hprodlt : (∏ σ : L →ₐ[ℚ] ℂ, ‖σ t‖) < 1 := by
      let incl : L →ₐ[ℚ] ℂ := L.val
      let rest : ℝ := ∏ σ ∈ (Finset.univ : Finset (L →ₐ[ℚ] ℂ)).erase incl, ‖σ t‖
      have hrest : rest ≤ 1 := by
        dsimp [rest]
        apply Finset.prod_le_one
        · intro i hi; exact norm_nonneg _
        · intro i hi; exact hbound i
      have hone : ‖incl t‖ < (1 : ℝ) := by
        change ‖(L.val : L →ₐ[ℚ] ℂ) t‖ < 1
        rw [hbase]
        exact hstrict
      have hfactor : ‖incl t‖ * rest = ∏ σ : L →ₐ[ℚ] ℂ, ‖σ t‖ := by
        simpa [rest] using
          (Finset.mul_prod_erase (Finset.univ : Finset (L →ₐ[ℚ] ℂ))
            (fun σ : L →ₐ[ℚ] ℂ => ‖σ t‖) (Finset.mem_univ incl))
      rw [← hfactor]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hone hrest
    have hnormeq := Algebra.norm_eq_prod_embeddings ℚ ℂ t
    have habseq := congrArg norm hnormeq
    rw [norm_prod] at habseq
    have hsmall : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ t)‖ < 1 := by
      rw [habseq]
      exact hprodlt
    have hrint : IsIntegral ℤ (Algebra.norm ℚ t) :=
      Algebra.isIntegral_norm ℚ htint
    have hzint : IsLocalization.IsInteger ℤ (Algebra.norm ℚ t) :=
      UniqueFactorizationMonoid.integer_of_integral hrint
    rcases hzint with ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      intro e
      subst z
      simp at hz
      have ht0 : t ≠ 0 := by
        intro h0
        have := congrArg (fun v : L => (v : ℂ)) h0
        exact hzval (by simpa [htval] using this)
      exact ht0 ((Algebra.norm_eq_zero_iff).mp hz.symm)
    have hbig : (1:ℝ) ≤ ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ t)‖ := by
      rw [← hz]
      -- a nonzero integer has absolute value at least one
      change (1:ℝ) ≤ ‖(z : ℂ)‖
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast (Int.one_le_abs hz0)
    exact (not_lt_of_ge hbig) hsmall
  exact le_antisymm hle (not_lt.mp hnlt)


private lemma burnside_eq_one_of_norm_re (z : ℂ) (hn : ‖z‖ = 1) (hr : z.re = 1) : z = 1 := by
  apply Complex.ext
  · simpa using hr
  · have hs := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hn, hr] at hs
    have hz : z.im = 0 := by nlinarith [sq_nonneg z.im]
    simpa using hz

private lemma burnside_integral_average_roots_eq {m N : ℕ} (hm : m ≠ 0) (hN : N ≠ 0)
    (α : Fin m → ℂ) (hα : ∀ i, α i ^ N = 1)
    (hu : IsIntegral ℤ ((∑ i, α i) / (m : ℂ))) :
    (∑ i, α i) / (m : ℂ) = 0 ∨
      (∀ i, α i = (∑ i, α i) / (m:ℂ)) := by
  classical
  let u : ℂ := (∑ i, α i) / (m:ℂ)
  rcases burnside_integral_average_roots_norm hm hN α hα hu with hz | hn
  · exact Or.inl hz
  right
  have hnu : ‖u‖ = 1 := hn
  have hu_sum : (∑ i, α i) = (m : ℂ) * u := by
    dsimp [u]
    have hm' : (m:ℂ) ≠ 0 := by exact_mod_cast hm
    field_simp
  have hαnorm (i : Fin m) : ‖α i‖ = (1:ℝ) :=
    Complex.norm_eq_one_of_pow_eq_one (hα i) hN
  let s : Fin m → ℝ := fun i => (α i * starRingEnd ℂ u).re
  have hsle (i : Fin m) : s i ≤ 1 := by
    dsimp [s]
    calc
      (α i * starRingEnd ℂ u).re ≤ ‖α i * starRingEnd ℂ u‖ :=
        Complex.re_le_norm _
      _ = 1 := by simp [norm_mul, hαnorm, hnu]
  have hssum : (∑ i, s i) = (m:ℝ) := by
    change (∑ i : Fin m, (α i * starRingEnd ℂ u).re) = _
    calc
      (∑ i : Fin m, (α i * starRingEnd ℂ u).re) =
          ((∑ i : Fin m, α i * starRingEnd ℂ u) : ℂ).re := by simp
      _ = (((∑ i : Fin m, α i) * starRingEnd ℂ u) : ℂ).re := by
          rw [Finset.sum_mul]
      _ = (((m : ℂ) * u) * starRingEnd ℂ u).re := by rw [hu_sum]
      _ = ((m : ℂ) * (u * starRingEnd ℂ u)).re := by rw [mul_assoc]
      _ = (m : ℝ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnu]
          norm_num
  have hseach (i : Fin m) : s i = 1 := by
    by_contra hne
    have hlt : s i < 1 := lt_of_le_of_ne (hsle i) hne
    have hsumlt : (∑ j : Fin m, s j) < ∑ j : Fin m, (1:ℝ) := by
      apply Finset.sum_lt_sum
      · intro j hj; exact hsle j
      · exact ⟨i, Finset.mem_univ _, hlt⟩
    have : ¬ (m:ℝ) < (m:ℝ) := lt_irrefl _
    exact this (by simpa [hssum] using hsumlt)
  intro i
  have hmulnorm : ‖α i * starRingEnd ℂ u‖ = (1:ℝ) := by
    simp [norm_mul, hαnorm, hnu]
  have hmulre : (α i * starRingEnd ℂ u).re = 1 := hseach i
  have hmulone : α i * starRingEnd ℂ u = 1 :=
    burnside_eq_one_of_norm_re _ hmulnorm hmulre
  -- multiply by u to cancel the conjugate
  calc
    α i = α i * (starRingEnd ℂ u * u) := by
      rw [mul_comm (starRingEnd ℂ u) u, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, hnu]
      norm_num
    _ = (α i * starRingEnd ℂ u) * u := by rw [mul_assoc]
    _ = u := by rw [hmulone, one_mul]


private lemma burnside_pow_eq_one_of_mem_roots_charpoly
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : Module.End ℂ W) {n : ℕ} (hA : A ^ n = 1)
    {z : ℂ} (hz : z ∈ A.charpoly.roots) : z^n=1 := by
  have hroot : A.charpoly.IsRoot z :=
    (Polynomial.mem_roots (LinearMap.charpoly_monic A).ne_zero).1 hz
  have heig : A.HasEigenvalue z :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly A z).2 hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hvpow := hv.pow_apply n
  rw [hA] at hvpow
  change v = z ^ n • v at hvpow
  have hvzero : ((1 : ℂ) - z ^ n) • v = 0 := by
    rw [sub_smul, one_smul, sub_eq_zero]
    exact hvpow
  have hz0 : (1 : ℂ) - z ^ n = 0 :=
    (smul_eq_zero.mp hvzero).resolve_right hv.2
  exact (sub_eq_zero.mp hz0).symm
private lemma burnside_scalar_of_roots_eq
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : Module.End ℂ W) {n : ℕ} (hn : n ≠ 0) (hA : A ^ n = 1)
    {z : ℂ} (hzall : ∀ y ∈ A.charpoly.roots, y = z) :
    A = z • LinearMap.id := by
  -- semisimple because X^n-1 separable in characteristic zero
  have hsep : (Polynomial.X ^ n - Polynomial.C (1:ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hn) (by norm_num)
  have heval : Polynomial.aeval A (Polynomial.X ^ n - Polynomial.C (1:ℂ)) = 0 := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C]
    -- algebra map of one scalar is identity
    apply sub_eq_zero.mpr
    simpa using hA
  have hsemi : A.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree heval
  have hzspace (y : ℂ) (hy : y ≠ z) : A.eigenspace y = ⊥ := by
    by_contra h
    have heig : A.HasEigenvalue y := (Module.End.hasEigenvalue_iff).2 h
    have hroot : A.charpoly.IsRoot y :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly A y).1 heig
    have hm : y ∈ A.charpoly.roots :=
      (Polynomial.mem_roots (LinearMap.charpoly_monic A).ne_zero).2 hroot
    exact hy (hzall y hm)
  have htop : A.eigenspace z = ⊤ := by
    apply top_unique
    -- use the semisimple spanning theorem
    rw [← hsemi.iSup_eigenspace_eq_top]
    apply iSup_le
    intro y
    by_cases hy : y = z
    · subst y; exact le_rfl
    · rw [hzspace y hy]
      exact bot_le
  ext v
  have hv : v ∈ A.eigenspace z := by rw [htop]; trivial
  simpa [Module.End.mem_eigenspace_iff] using
    (Module.End.mem_eigenspace_iff.mp hv)



/-- A character-theoretic averaging step in a form that avoids choosing an
 eigenbasis.  The eigenvalues are the roots (with multiplicity) of the
 characteristic polynomial.  Enumerating that multiset gives the list of
 roots of unity to which the preceding averaging lemma applies. -/
private lemma burnside_character_eq_zero_of_integral_average
    {H : Type*} [Group H] [Fintype H]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : Representation ℂ H V) (x : H)
    (hm : Module.finrank ℂ V ≠ 0)
    (hu : IsIntegral ℤ (σ.character x / (Module.finrank ℂ V : ℂ)))
    (hnu : ¬ (∃ z : ℂ, ∀ y ∈ (σ x).charpoly.roots, y = z)) :
    σ.character x = 0 := by
  classical
  let n : ℕ := Nat.card H
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.card_pos (α := H))
  have hpow : (σ x : Module.End ℂ V) ^ n = 1 := by
    rw [← map_pow]
    have hxpow : x ^ Nat.card H = (1 : H) := by
      simpa [Nat.card_eq_fintype_card] using (pow_card_eq_one (x := x))
    change σ (x ^ Nat.card H) = 1
    rw [hxpow, map_one]
  let l : List ℂ := (σ x).charpoly.roots.toList
  have hlen : l.length = Module.finrank ℂ V := by
    dsimp [l]
    rw [Multiset.length_toList]
    rw [← (IsAlgClosed.splits ((σ x).charpoly)).natDegree_eq_card_roots]
    exact LinearMap.charpoly_natDegree (σ x)
  let α : Fin (Module.finrank ℂ V) → ℂ :=
    fun i => l.get (Fin.cast hlen.symm i)
  have hmem (i : Fin (Module.finrank ℂ V)) :
      α i ∈ (σ x).charpoly.roots := by
    -- `mem_toList` is the bridge between the chosen order and the multiset.
    change l.get (Fin.cast hlen.symm i) ∈ (σ x).charpoly.roots
    apply (Multiset.mem_toList).1
    change l.get (Fin.cast hlen.symm i) ∈ l
    exact List.get_mem l (Fin.cast hlen.symm i)
  have hα (i : Fin (Module.finrank ℂ V)) : α i ^ n = 1 :=
    burnside_pow_eq_one_of_mem_roots_charpoly (σ x) hpow (hmem i)
  have hsumroots :
      (∑ i : Fin (Module.finrank ℂ V), α i) = (σ x).charpoly.roots.sum := by
    -- First sum over the positions of the chosen list; casting the finite
    -- index by `hlen` does not change such a sum.
    have hs1 :
        (∑ i : Fin (Module.finrank ℂ V), l.get (Fin.cast hlen.symm i)) =
          ∑ j : Fin l.length, l.get j := by
      simpa using (Equiv.sum_comp (finCongr hlen.symm)
        (fun j : Fin l.length => l.get j))
    have hs2 : (∑ j : Fin l.length, l.get j) = l.sum := by
      rw [← List.sum_ofFn, List.ofFn_get]
    calc
      (∑ i : Fin (Module.finrank ℂ V), α i) =
          ∑ j : Fin l.length, l.get j := by simpa [α] using hs1
      _ = l.sum := hs2
      _ = (σ x).charpoly.roots.sum := by
        -- sums commute with passing from a list to its multiset
        rw [← Multiset.sum_coe]
        rw [Multiset.coe_toList]
  have hsumchar :
      (∑ i : Fin (Module.finrank ℂ V), α i) = σ.character x := by
    -- The trace is the sum of the roots over an algebraically closed field.
    unfold Representation.character
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits
      (IsAlgClosed.splits ((σ x).charpoly))]
    exact hsumroots
  have hu' : IsIntegral ℤ
        ((∑ i : Fin (Module.finrank ℂ V), α i) /
          (Module.finrank ℂ V : ℂ)) := by
    rw [hsumchar]
    exact hu
  rcases burnside_integral_average_roots_eq hm hn α hα hu' with hzero | hall
  · have hmC : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hm
    have hsum0 : (∑ i : Fin (Module.finrank ℂ V), α i) = 0 :=
      (div_eq_zero_iff.mp hzero).resolve_right hmC
    -- and the trace is that sum
    rw [← hsumchar]
    exact hsum0
  · exfalso
    apply hnu
    refine ⟨(∑ i : Fin (Module.finrank ℂ V), α i) /
      (Module.finrank ℂ V : ℂ), ?_⟩
    intro y hy
    have hy' : y ∈ l := by
      simpa [l] using hy
    obtain ⟨j, hj⟩ := (List.mem_iff_get).1 hy'
    let i : Fin (Module.finrank ℂ V) := Fin.cast hlen j
    have hai : α i = y := by
      dsimp [α, i]
      have hc : Fin.cast hlen.symm (Fin.cast hlen j) = j := by
        simp
      exact (congrArg (fun t : Fin l.length => l.get t) hc).trans hj
    calc
      y = α i := hai.symm
      _ = (∑ k : Fin (Module.finrank ℂ V), α k) /
            (Module.finrank ℂ V : ℂ) := hall i


set_option backward.isDefEq.respectTransparency false
-- A `k[G]` submodule of the module of a representation and the corresponding
-- subrepresentation have exactly the same action.  Keeping track of the
-- type synonym `asModule` is a little awkward; the following linear
-- equivalence is a useful way of transporting simplicity.
private noncomputable def burnside_submodule_subrep_equiv
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (N : Submodule (MonoidAlgebra k G) ρ.asModule) :
    N ≃ₗ[MonoidAlgebra k G]
      (Subrepresentation.ofSubmodule' N).toRepresentation.asModule := by
  classical
  let W : Subrepresentation ρ := Subrepresentation.ofSubmodule' N
  let f : N → W.toRepresentation.asModule := fun n => ⟨n.1, n.2⟩
  let g : W.toRepresentation.asModule → N := fun n => ⟨n.1, n.2⟩
  have hadd : ∀ a b : N, f (a+b) = f a + f b := by intros; rfl
  have hzero : f 0 = 0 := by rfl
  have hsmul : ∀ (a : MonoidAlgebra k G) (b:N), f (a • b) = a • f b := by
    intro a b
    induction a using MonoidAlgebra.induction_linear with
    | zero => exact hzero
    | add x y hx hy =>
        rw [add_smul, add_smul]
        rw [hadd, hx, hy]
    | single g' r =>
        apply Subtype.ext
        change ((MonoidAlgebra.single g' r) • (b : N) : ρ.asModule) = _
        rw [Representation.single_smul]
        simp [Representation.single_smul, W, Subrepresentation.toRepresentation,
          Subrepresentation.ofSubmodule']
        change r • ρ g' (b.1) = r • ρ g' (b.1)
        rfl
  let F : N →ₗ[MonoidAlgebra k G] W.toRepresentation.asModule :=
    { toFun := f
      map_add' := hadd
      map_smul' := hsmul }
  have hgiadd : ∀ a b : W.toRepresentation.asModule, g (a+b) = g a + g b := by
    intros
    rfl
  have hgizero : g 0 = 0 := by rfl
  have hgismul : ∀ (a : MonoidAlgebra k G) (b:W.toRepresentation.asModule),
        g (a • b) = a • g b := by
    intro a b
    induction a using MonoidAlgebra.induction_linear with
    | zero => exact hgizero
    | add x y hx hy =>
        rw [add_smul, add_smul]
        rw [hgiadd, hx, hy]
    | single g' r =>
        apply Subtype.ext
        change _
        simp [Representation.single_smul, W, Subrepresentation.toRepresentation,
          Subrepresentation.ofSubmodule']
        change r • ρ g' (b.1) = r • ρ g' (b.1)
        rfl
  let Gi : W.toRepresentation.asModule →ₗ[MonoidAlgebra k G] N :=
    { toFun := g
      map_add' := hgiadd
      map_smul' := hgismul }
  have h1 : F ∘ₗ Gi = LinearMap.id := by
    ext v
    rfl
  have h2 : Gi ∘ₗ F = LinearMap.id := by
    ext v
    rfl
  exact LinearEquiv.ofLinear F Gi h1 h2

private lemma burnside_irreducible_subrep_of_simple
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (N : Submodule (MonoidAlgebra k G) ρ.asModule)
    [IsSimpleModule (MonoidAlgebra k G) N] :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' N).toRepresentation := by
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).2
  -- `IsSimpleModule.congr` is stated with its typeclass on the target.
  -- The target of the symmetric equivalence is `N`, for which we already
  -- have the instance.
  exact IsSimpleModule.congr (burnside_submodule_subrep_equiv ρ N).symm

/-- Trace of a diagonal action on a finite dependent direct sum.  We use
`linearEquivFunOnFintype` rather than coordinates on the group algebra; with
`Pi.basis` the matrix is the ordinary block diagonal matrix. -/
private lemma burnside_trace_dfinsupp
    {k : Type*} [Field k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
      [∀ i, FiniteDimensional k (M i)]
    (A : ∀ i, Module.End k (M i)) :
    (LinearMap.trace k (Π₀ i, M i)) (DFinsupp.mapRange.linearMap A) =
      ∑ i, (LinearMap.trace k (M i)) (A i) := by
  classical
  let b (i:ι) := Module.finBasis k (M i)
  let B := Pi.basis b
  let e := DFinsupp.linearEquivFunOnFintype (R:=k) (M:=M)
  let F : Module.End k (∀ i, M i) := e.conj (DFinsupp.mapRange.linearMap A)
  have hf (v : (∀ i, M i)) (i:ι) : F v i = A i (v i) := by
    dsimp [F, e]
    simp [DFinsupp.linearEquivFunOnFintype]
    rfl
  have hmat : LinearMap.toMatrix B B F =
      Matrix.blockDiagonal' (fun i => LinearMap.toMatrix (b i) (b i) (A i)) := by
    ext ⟨i,a⟩ ⟨j,c⟩
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix_apply, B, Pi.basis_apply, Pi.basis_repr, hf, b,
        Matrix.blockDiagonal'_apply, Pi.single_apply]
    · simp [LinearMap.toMatrix_apply, B, Pi.basis_apply, Pi.basis_repr, hf, b,
        Matrix.blockDiagonal'_apply, Pi.single_apply, hij]
  rw [← LinearMap.trace_conj' _ e]
  rw [LinearMap.trace_eq_matrix_trace k B]
  rw [hmat, Matrix.trace_blockDiagonal']
  apply Finset.sum_congr rfl
  intro i hi
  rw [← LinearMap.trace_eq_matrix_trace k (b i)]


private lemma burnside_leftRegular_character_decomp
 {S:Type*} [Group S] [Fintype S]
 {t:ℕ}
 (U : Fin t → Submodule (MonoidAlgebra ℂ S) (Representation.leftRegular ℂ S).asModule)
 (e : (Representation.leftRegular ℂ S).asModule ≃ₗ[MonoidAlgebra ℂ S] Π₀ i : Fin t, U i) :
 ∀ g:S, (Representation.leftRegular ℂ S).character g =
   ∑ i : Fin t, (Subrepresentation.ofSubmodule' (U i)).toRepresentation.character g := by
 classical
 intro g
 letI ig (i : Fin t) : AddCommGroup (U i) := by infer_instance
 letI fd (i:Fin t) : FiniteDimensional ℂ (U i) := by
   let f : (U i) →ₗ[ℂ] (S →₀ ℂ) :=
    { toFun := fun u => u.1
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
   exact FiniteDimensional.of_injective f (by intro a b h; exact Subtype.ext h)
 let ee : (S →₀ ℂ) ≃ₗ[ℂ] (Π₀ i : Fin t, U i) := e.restrictScalars ℂ
 have hcomp : ee.conj ((Representation.leftRegular ℂ S) g) =
       DFinsupp.mapRange.linearMap (fun i => (Subrepresentation.ofSubmodule' (U i)).toRepresentation g) := by
   apply LinearMap.ext
   intro v
   apply DFinsupp.ext
   intro i
   have hh : e ((MonoidAlgebra.single g (1:ℂ)) • (e.symm v)) =
          (MonoidAlgebra.single g (1:ℂ)) • v := by
     simpa using (e.map_smul (MonoidAlgebra.single g (1:ℂ)) (e.symm v))
   have hh' := congrArg (fun z : (Π₀ i : Fin t, U i) => z i) hh
   change (e ((Representation.leftRegular ℂ S g) (e.symm v))) i = _
   change _ = ((Subrepresentation.ofSubmodule' (U i)).toRepresentation g) (v i)
   have hh'' : (e ((Representation.leftRegular ℂ S g) (e.symm v))) i =
          MonoidAlgebra.single g (1:ℂ) • (v i) := by
     
     rw [Representation.single_smul (Representation.leftRegular ℂ S)] at hh'
     -- simplify coefficients of smul in the direct sum
     simp only [DFinsupp.smul_apply] at hh'
     change (e ((Representation.leftRegular ℂ S g) (e.symm v))) i =
          MonoidAlgebra.single g (1:ℂ) • (v i)
     have hid (w : (Representation.leftRegular ℂ S).asModule) :
       (Representation.leftRegular ℂ S).asModuleEquiv w = w := rfl
     simpa only [one_smul, hid] using hh' 
   rw [hh'']
   -- simplify action on subrep
   -- try
   apply Subtype.ext
   change ((MonoidAlgebra.single g (1:ℂ)) • (v i : U i) :
       (Representation.leftRegular ℂ S).asModule) = _
   -- look simp
   simp [Representation.single_smul, Subrepresentation.toRepresentation,
     Subrepresentation.ofSubmodule', Representation.asModuleEquiv]
   rfl

 unfold Representation.character
 have htrace := LinearMap.trace_conj' (R:=ℂ)
        (M:= (S →₀ ℂ)) (N:= (Π₀ i : Fin t, U i))
        ((Representation.leftRegular ℂ S) g) ee
 -- try use
 rw [← htrace]
 rw [hcomp, burnside_trace_dfinsupp]
 rfl


open scoped Classical in
private lemma burnside_regular_multiplicity
 {S:Type*} [Group S] [Fintype S]
 {t:ℕ} (W : Fin t → Subrepresentation (Representation.leftRegular ℂ S))
 (hs : ∀ i, Representation.IsIrreducible (W i).toRepresentation)
 (hsum : ∀ g:S, (Representation.leftRegular ℂ S).character g =
   ∑ i:Fin t, (W i).toRepresentation.character g)
 (hzero : ∀ g:S, g ≠ 1 → (Representation.leftRegular ℂ S).character g = 0)
 (i : Fin t) :
 ((Finset.univ.filter (fun j : Fin t => Nonempty (Representation.Equiv
      (W i).toRepresentation (W j).toRepresentation))).card : ℂ) =
      (Module.finrank ℂ (W i).toSubmodule : ℂ) := by
 classical
 letI invCard : Invertible (Nat.card S : ℂ) :=
   invertibleOfNonzero (by exact_mod_cast (Nat.ne_of_gt (Nat.card_pos (α:=S))))
 letI irI : Representation.IsIrreducible (W i).toRepresentation := hs i
 have hleft : (Nat.card S : ℂ)⁻¹ *
        ∑ g:S, (Representation.leftRegular ℂ S).character g *
          (W i).toRepresentation.character g⁻¹ =
        (Module.finrank ℂ (W i).toSubmodule : ℂ) := by
     have hs1 : (∑ g:S, (Representation.leftRegular ℂ S).character g *
          (W i).toRepresentation.character g⁻¹) =
          (Nat.card S : ℂ) * (Module.finrank ℂ (W i).toSubmodule : ℂ) := by
       rw [Finset.sum_eq_single (1:S)]
       · simp [Representation.char_one, Module.finrank_finsupp,
               Nat.card_eq_fintype_card]
       · intro b hb hbne
         rw [hzero b hbne]
         simp
       · intro h; simp at h
     rw [hs1]
     have hn : (Nat.card S : ℂ) ≠ 0 := by
       exact_mod_cast (Nat.ne_of_gt (Nat.card_pos (α:=S)))
     field_simp
 have hright : (Nat.card S : ℂ)⁻¹ *
        ∑ g:S, (Representation.leftRegular ℂ S).character g *
          (W i).toRepresentation.character g⁻¹ =
        ∑ j:Fin t, (if Nonempty (Representation.Equiv
              (W i).toRepresentation (W j).toRepresentation)
             then (1:ℂ) else 0) := by
     simp_rw [hsum]
     simp_rw [Finset.sum_mul]
     rw [Finset.sum_comm]
     rw [Finset.mul_sum]
     apply Finset.sum_congr rfl
     intro j hj
     letI irJ : Representation.IsIrreducible (W j).toRepresentation := hs j
     simpa using (Representation.char_orthonormal
       (W j).toRepresentation (W i).toRepresentation)
 rw [hright] at hleft
 have hcnt : (∑ j:Fin t, (if Nonempty (Representation.Equiv
              (W i).toRepresentation (W j).toRepresentation)
             then (1:ℂ) else 0)) =
             ((Finset.univ.filter (fun j : Fin t => Nonempty (Representation.Equiv
               (W i).toRepresentation (W j).toRepresentation))).card : ℂ) := by
     rw [Finset.sum_boole]
 simpa [hcnt] using hleft





private lemma burnside_finrank_eq_one_of_irreducible_trivial {S V:Type*} [Group S]
 [AddCommGroup V] [Module ℂ V]
 (σ: Representation ℂ S V) [Representation.IsIrreducible σ]
 (hall : ∀ g:S, σ g = LinearMap.id) : Module.finrank ℂ V = 1 := by
 have hnM : Nontrivial σ.asModule :=
   IsSimpleModule.nontrivial (MonoidAlgebra ℂ S) σ.asModule
 letI : Nontrivial V := hnM
 obtain ⟨v, hv⟩ := exists_ne (0:V)
 let L : Subrepresentation σ :=
   { toSubmodule := ℂ ∙ v
     apply_mem_toSubmodule := by
       intro g w hw
       rw [hall g]
       exact hw }
 have hnb : L ≠ (⊥ : Subrepresentation σ) := by
   intro h
   have hv' : v ∈ L.toSubmodule := by
     exact Submodule.mem_span_singleton_self v
   have : v = 0 := by
     have hv'' : v ∈ (⊥ : Subrepresentation σ).toSubmodule := by
       rw [← h]; exact hv'
     exact hv''
   exact hv this
 have htop : L = (⊤ : Subrepresentation σ) :=
     (IsSimpleOrder.eq_bot_or_eq_top L).resolve_left hnb
 have hspan : (ℂ ∙ v : Submodule ℂ V) = ⊤ := by
   change L.toSubmodule = _
   rw [htop]
   rfl
 apply finrank_eq_one v hv
 intro w
 exact Submodule.mem_span_singleton.mp
       (by rw [hspan]; trivial)
private lemma burnside_trivial_of_fixvector_irreducible {S V:Type*} [Group S]
 [AddCommGroup V] [Module ℂ V]
 (σ: Representation ℂ S V) [Representation.IsIrreducible σ]
 {v:V} (hn:v ≠ 0) (hv : ∀ g:S, σ g v = v) :
 ∀ g:S, σ g = LinearMap.id := by
 let L : Subrepresentation σ :=
   { toSubmodule := ℂ ∙ v
     apply_mem_toSubmodule := by
       intro g w hw
       rcases (Submodule.mem_span_singleton.mp hw) with ⟨c, rfl⟩
       have : σ g (c • v) = c • v := by simp [hv]
       rw [this]
       exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v) }
 have hnb : L ≠ (⊥ : Subrepresentation σ) := by
   intro h
   have h' : v ∈ (⊥ : Subrepresentation σ).toSubmodule := by
     rw [← h]
     exact Submodule.mem_span_singleton_self v
   exact hn h'
 have htop : L = (⊤ : Subrepresentation σ) :=
   (IsSimpleOrder.eq_bot_or_eq_top L).resolve_left hnb
 have hspan : (ℂ ∙ v : Submodule ℂ V) = ⊤ := by
   change L.toSubmodule = _
   rw [htop]
   rfl
 intro g
 ext w
 have hw : w ∈ (ℂ ∙ v : Submodule ℂ V) := by rw [hspan]; trivial
 obtain ⟨c,rfl⟩ := (Submodule.mem_span_singleton.mp hw)
 simp [hv]



/-- In a simple group the alternative in the preceding observation has a
useful form for any representation.  Either a scalar element is central, or
the whole representation is trivial.  Indeed the kernel of a representation
is a normal subgroup. -/
private lemma mem_center_or_trivial_of_scalar_of_simple
    {H : Type u} [Group H] [IsSimpleGroup H]
    {k : Type v} [CommSemiring k]
    {V : Type w} [AddCommMonoid V] [Module k V]
    (ρ : Representation k H V) {x : H} (c : k)
    (hx : ρ x = c • LinearMap.id) :
    x ∈ Subgroup.center H ∨ (∀ g : H, ρ g = LinearMap.id) := by
  rcases (MonoidHom.normal_ker ρ).eq_bot_or_eq_top with hk | hk
  · exact Or.inl (mem_center_of_scalar_of_ker_eq_bot ρ hk c hx)
  · right
    intro g
    have hg : g ∈ MonoidHom.ker ρ := by
      rw [hk]
      exact Subgroup.mem_top g
    exact MonoidHom.mem_ker.mp hg


/-- The group-theoretic (and difficult) simple-group case of Burnside.  The
rest of the argument below only uses this case for smaller sections. -/
private lemma simple_burnside_comm
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    {S : Type u} [Group S] [Finite S] [IsSimpleGroup S]
    {a b : ℕ} (hS : Nat.card S = p ^ a * q ^ b) :
    ∀ x y : S, x * y = y * x := by
  classical
  by_cases ha : a = 0
  · subst a
    simp only [pow_zero, one_mul] at hS
    letI : Fact (Nat.Prime q) := ⟨hq⟩
    have hpg : IsPGroup q S := IsPGroup.of_card hS
    letI ni : Group.IsNilpotent S := hpg.isNilpotent
    have sol : IsSolvable S := inferInstance
    exact IsSimpleGroup.comm_iff_isSolvable.mpr sol
  by_cases hb : b = 0
  · subst b
    simp only [pow_zero, mul_one] at hS
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    have hpg : IsPGroup p S := IsPGroup.of_card hS
    letI ni : Group.IsNilpotent S := hpg.isNilpotent
    have sol : IsSolvable S := inferInstance
    exact IsSimpleGroup.comm_iff_isSolvable.mpr sol
  by_cases hab : a = 1 ∧ b = 1
  · rcases hab with ⟨rfl,rfl⟩
    simp only [pow_one] at hS
    have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
    have hsf' : Squarefree (p*q) :=
      (Nat.squarefree_mul hcop).2 ⟨hp.prime.squarefree, hq.prime.squarefree⟩
    have hsf : Squarefree (Nat.card S) := hS.symm ▸ hsf'
    letI iz : IsZGroup S := IsZGroup.of_squarefree hsf
    have sol : IsSolvable S := inferInstance
    exact IsSimpleGroup.comm_iff_isSolvable.mpr sol
  -- If the smaller prime occurs just once, its Sylow subgroup is cyclic.
  -- Burnside transfer for the *least* prime is enough in this case.  Isolating
  -- it is useful: the genuinely hard case has both Sylow groups noncyclic.
  by_cases hsmall : (a = 1 ∧ p < q) ∨ (b = 1 ∧ q < p)
  · rcases hsmall with hsmall | hsmall
    · rcases hsmall with ⟨rfl, hp_lt⟩
      letI : Fact (Nat.Prime p) := ⟨hp⟩
      let P : Sylow p S := default
      have hP : IsCyclic P :=
        sylow_isCyclic_of_left_one (T:=S) hp hq hpq hS P
      have hmin : (Nat.card S).minFac = p := by
        rw [hS]
        exact minFac_prime_pow_mul_eq_left hp hq (by decide) (Nat.le_of_lt hp_lt)
      have hlt : commutator S < (⊤ : Subgroup S) := by
        have hm : (Nat.card S).minFac.Prime :=
          Nat.minFac_prime (Finite.one_lt_card.ne')
        -- rewrite the parameter of the Sylow subgroup to the least prime
        let PP : Sylow (Nat.card S).minFac S := hmin.symm ▸ P
        have hPP : IsCyclic PP.1 := by
          dsimp [PP]
          -- casting the prime index does not change the subgroup
          cases hmin
          exact hP
        exact commutator_lt_of_cyclic_minSylow hm PP hPP
      have hnottop : commutator S ≠ (⊤ : Subgroup S) := ne_of_lt hlt
      have hh := (Subgroup.commutator_normal (⊤ : Subgroup S)
        (⊤ : Subgroup S)).eq_bot_or_eq_top
      have hb0 : commutator S = (⊥ : Subgroup S) := hh.resolve_right hnottop
      have im : IsMulCommutative S := (commutator_eq_bot_iff S).1 hb0
      exact fun x y => im.is_comm.comm x y
    · rcases hsmall with ⟨rfl, hq_lt⟩
      -- the same argument with the primes interchanged
      letI : Fact (Nat.Prime q) := ⟨hq⟩
      let Q : Sylow q S := default
      have hQ : IsCyclic Q := by
        -- write the order with the smaller prime first
        have hc' : Nat.card S = q ^ (1:ℕ) * p ^ a := by
          simpa [mul_comm] using hS
        exact sylow_isCyclic_of_left_one (T:=S) hq hp (Ne.symm hpq) hc' Q
      have hmin : (Nat.card S).minFac = q := by
        have hc' : Nat.card S = q ^ (1:ℕ) * p ^ a := by
          simpa [mul_comm] using hS
        rw [hc']
        exact minFac_prime_pow_mul_eq_left hq hp (by decide) (Nat.le_of_lt hq_lt)
      have hlt : commutator S < (⊤ : Subgroup S) := by
        have hm : (Nat.card S).minFac.Prime :=
          Nat.minFac_prime (Finite.one_lt_card.ne')
        let QQ : Sylow (Nat.card S).minFac S := hmin.symm ▸ Q
        have hQQ : IsCyclic QQ.1 := by
          dsimp [QQ]
          cases hmin
          exact hQ
        exact commutator_lt_of_cyclic_minSylow hm QQ hQQ
      have hnottop : commutator S ≠ (⊤ : Subgroup S) := ne_of_lt hlt
      have hh := (Subgroup.commutator_normal (⊤ : Subgroup S)
        (⊤ : Subgroup S)).eq_bot_or_eq_top
      have hb0 : commutator S = (⊥ : Subgroup S) := hh.resolve_right hnottop
      have im : IsMulCommutative S := (commutator_eq_bot_iff S).1 hb0
      exact fun x y => im.is_comm.comm x y
  -- Any remaining simple counterexample is necessarily centreless.  This is a
  -- useful sharp form of the missing character-theoretic step: the central
  -- alternative itself is immediate.
  have hcz : Subgroup.center S = (⊥ : Subgroup S) ∨
      Subgroup.center S = (⊤ : Subgroup S) :=
    (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top
  rcases hcz with hc | hc
  · -- the centreless mixed, non-squarefree simple case is also perfect; the
    -- abelian commutator alternative in a simple group would finish at once.
    by_cases hcomm : commutator S = ⊥
    · have im : IsMulCommutative S := (commutator_eq_bot_iff S).1 hcomm
      exact fun x y => im.is_comm.comm x y
    have htop : commutator S = (⊤ : Subgroup S) := by
      have hh := (Subgroup.commutator_normal (⊤ : Subgroup S)
        (⊤ : Subgroup S)).eq_bot_or_eq_top
      exact hh.resolve_left hcomm
    -- In fact a counterexample here cannot even have a cyclic Sylow
    -- subgroup for its least prime.  Burnside transfer gives a proper
    -- (abelian) quotient in exactly that situation.
    have hm : (Nat.card S).minFac.Prime :=
      Nat.minFac_prime (Finite.one_lt_card.ne')
    letI : Fact (Nat.card S).minFac.Prime := ⟨hm⟩
    let R : Sylow (Nat.card S).minFac S := default
    by_cases hR : IsCyclic R.1
    · have hlt : commutator S < (⊤ : Subgroup S) :=
        commutator_lt_of_cyclic_minSylow hm R hR
      exact False.elim ((ne_of_lt hlt) htop)
    · have hmult : 2 ≤ (Nat.card S).factorization (Nat.card S).minFac :=
        two_le_factorization_of_not_isCyclic_sylow hm R hR
      have hfacp : (Nat.card S).factorization p = a := by
        have hpnot : ¬ p ∣ q ^ b := by
          intro hx
          exact hpq ((Nat.dvd_prime_two_le hq hp.two_le).1
            (hp.dvd_of_dvd_pow hx))
        rw [hS, Nat.factorization_mul (pow_ne_zero a hp.ne_zero)
              (pow_ne_zero b hq.ne_zero),
            Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
            Nat.factorization_eq_zero_of_not_dvd hpnot, add_zero]
      have hfacq : (Nat.card S).factorization q = b := by
        have hqnot : ¬ q ∣ p ^ a := by
          intro hx
          exact hpq (((Nat.dvd_prime_two_le hp hq.two_le).1
            (hq.dvd_of_dvd_pow hx))).symm
        -- commute the formula, so that the `q`-part is the first factor
        have hc' : Nat.card S = q ^ b * p ^ a := by
          simpa [mul_comm] using hS
        rw [hc', Nat.factorization_mul (pow_ne_zero b hq.ne_zero)
              (pow_ne_zero a hp.ne_zero),
            Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same,
            Nat.factorization_eq_zero_of_not_dvd hqnot, add_zero]
      have hexp : (p < q ∧ 2 ≤ a) ∨ (q < p ∧ 2 ≤ b) := by
        rcases Nat.lt_or_gt_of_ne hpq with hp' | hq'
        · left
          refine ⟨hp', ?_⟩
          have hm' : (Nat.card S).minFac = p := by
            rw [hS]
            exact minFac_prime_pow_mul_eq_left hp hq ha (Nat.le_of_lt hp')
          rw [hm', hfacp] at hmult
          exact hmult
        · right
          refine ⟨hq', ?_⟩
          have hc' : Nat.card S = q ^ b * p ^ a := by
            simpa [mul_comm] using hS
          have hm' : (Nat.card S).minFac = q := by
            rw [hc']
            exact minFac_prime_pow_mul_eq_left hq hp hb (Nat.le_of_lt hq')
          rw [hm', hfacq] at hmult
          exact hmult
      -- More generally transfer rules out a self-centralizing normalizer for
      -- *any* Sylow present in this putative perfect simple group.  The final
      -- case of Burnside is precisely to handle fusion when none of these
      -- normalizers is central.
      have hfusion : ∀ (r : ℕ), ∀ (hr : Nat.Prime r), ∀ (P : Sylow r S),
          r ∣ Nat.card S →
          ¬ (Subgroup.normalizer (P : Subgroup S) ≤
              Subgroup.centralizer (P : Set S)) := by
        intro r hr P hd hn
        have hlt : commutator S < (⊤ : Subgroup S) :=
          commutator_lt_of_normalizer_le_centralizer hr P hd hn
        exact (ne_of_lt hlt) htop
      -- There is nevertheless a very small conjugacy class.  This is the
      -- other standard reduction before the character-theoretic part of
      -- Burnside's argument.  If `x` lies in the (non-trivial) centre of a
      -- Sylow `p`-subgroup, that whole Sylow subgroup centralizes `x`.  Hence
      -- the index of `C(x)` is a power of the *other* prime.  Notice that in
      -- a centreless group it is a positive power: `C(x)` cannot be the
      -- whole group.  Spelling out the cancellation of the Sylow order is a
      -- useful way of making this reduction independent of a chosen
      -- `Fintype`.
      have hclass : ∃ x : S, x ≠ 1 ∧
          ∃ d : ℕ, d ≤ b ∧ d ≠ 0 ∧
            (Subgroup.centralizer ({x} : Set S)).index = q ^ d := by
        letI hpI : Fact (Nat.Prime p) := ⟨hp⟩
        let Pp : Sylow p S := default
        have hpd : p ∣ Nat.card S := by
          rw [hS]
          exact dvd_mul_of_dvd_left (dvd_pow_self p ha) _
        have hnePp : (Pp : Subgroup S) ≠ ⊥ :=
          Pp.ne_bot_of_dvd_card hpd
        letI nPp : Nontrivial Pp :=
          (Subgroup.nontrivial_iff_ne_bot _).2 hnePp
        haveI nZ : Nontrivial (Subgroup.center Pp) :=
          IsPGroup.center_nontrivial Pp.isPGroup'
        obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center Pp)
        let x : S := (z.1.1 : S)
        have hx : x ≠ 1 := by
          intro e
          apply hz
          apply Subtype.ext
          apply Subtype.ext
          exact e
        have hPC : (Pp : Subgroup S) ≤
            Subgroup.centralizer ({x} : Set S) := by
          intro y hy
          change ∀ t ∈ ({x} : Set S), t * y = y * t
          intro t ht
          have ht' : t = x := (Set.mem_singleton_iff.mp ht)
          subst t
          -- `z.2` says precisely that `z` commutes with every element of
          -- the Sylow group; the coercions pass twice, from the centre and
          -- from the Sylow subgroup.
          have hcomm := (Subgroup.mem_center_iff.mp z.2) (⟨y, hy⟩ : Pp)
          -- The equation above is written as `y*x=x*y`; the centralizer
          -- convention asks for `x*y=y*x`.
          exact congrArg (fun k : Pp => (k : S)) hcomm.symm
        have hcp : (Nat.card S).factorization p = a := hfacp
        have hcardPp : Nat.card Pp = p ^ a := by
          -- the order of a Sylow subgroup is the full p-part
          simpa [hcp] using (Pp.card_eq_multiplicity)
        have hindPp : (Pp : Subgroup S).index = q ^ b := by
          have heq := (Pp : Subgroup S).index_mul_card
          rw [hcardPp, hS] at heq
          -- cancel the positive factor `p^a`
          have heq' : p ^ a * (Pp : Subgroup S).index =
                p ^ a * q ^ b := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using heq
          exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) heq'
        have hidx : (Subgroup.centralizer ({x} : Set S)).index ∣ q ^ b := by
          -- indices reverse along an inclusion
          simpa [hindPp] using (Subgroup.index_dvd_of_le hPC)
        obtain ⟨d, hdle, hdeq⟩ := (Nat.dvd_prime_pow hq).1 hidx
        refine ⟨x, hx, d, hdle, ?_, hdeq⟩
        intro hd0
        subst d
        have hone : (Subgroup.centralizer ({x} : Set S)).index = 1 := by
          simpa using hdeq
        have hctop : Subgroup.centralizer ({x} : Set S) = (⊤ : Subgroup S) :=
          Subgroup.index_eq_one.mp hone
        have hxz : x ∈ Subgroup.center S := by
          have hsub : ({x} : Set S) ⊆ (Subgroup.center S : Set S) :=
            (Subgroup.centralizer_eq_top_iff_subset.mp hctop)
          exact hsub (Set.mem_singleton x)
        have hxone : x = 1 := by
          have : x ∈ (⊥ : Subgroup S) := by simpa [hc] using hxz
          exact (Subgroup.mem_bot.mp this)
        exact hx hxone
      have hcarrier (x : S) :
          Nat.card (ConjClasses.mk x).carrier =
            (Subgroup.centralizer ({x} : Set S)).index := by
        -- The formulation of orbit--stabilizer for conjugacy classes in the
        -- library is in terms of `ConjAct`.  Its stabilizer has the same
        -- cardinality as the (ordinary) centralizer.
        classical
        cases nonempty_fintype S
        have hh := ConjClasses.card_carrier x
        have hs := Subgroup.nat_card_centralizer_nat_card_stabilizer x
        have hs' :
            Fintype.card (MulAction.stabilizer (ConjAct S) x) =
              Nat.card (Subgroup.centralizer ({x} : Set S)) := by
          simpa [Nat.card_eq_fintype_card] using hs.symm
        rw [Nat.card_eq_fintype_card, hh, hs']
        have heq := (Subgroup.centralizer ({x} : Set S)).card_mul_index
        apply Nat.div_eq_of_eq_mul_left
        · exact Nat.card_pos
        · simpa [mul_comm] using heq.symm
      have hclass' : ∃ x : S, x ≠ 1 ∧
          ∃ d : ℕ, d ≤ b ∧ d ≠ 0 ∧
            Nat.card (ConjClasses.mk x).carrier = q ^ d := by
        obtain ⟨x, hx, d, hd, hd0, hdval⟩ := hclass
        exact ⟨x, hx, d, hd, hd0, (hcarrier x).trans hdval⟩
      have hclass_noncentral : ∃ x : S, x ∉ Subgroup.center S ∧
          ∃ d : ℕ, d ≤ b ∧ d ≠ 0 ∧
            Nat.card (ConjClasses.mk x).carrier = q ^ d := by
        obtain ⟨x, hx, d, hd, hd0, hcidx⟩ := hclass'
        refine ⟨x, ?_, d, hd, hd0, hcidx⟩
        intro hz
        have hbot : x ∈ (⊥ : Subgroup S) := by
          -- here we use the centreless alternative; otherwise the central
          -- conjugacy class would of course be a singleton.
          simpa [hc] using hz
        exact hx (Subgroup.mem_bot.mp hbot)
      -- In a nonabelian simple group the impossibility of a noncentral
      -- conjugacy class of prime-power size is Burnside's character-theory
      -- lemma.  `hclass_noncentral` is its exact input.  This is the
      -- remaining fusion/character step.
      exfalso
      obtain ⟨x, hxnc, d, hdle, hd0, hxcard⟩ := hclass_noncentral
      -- The missing character lemma is applied to this *particular* class.
      -- Record the elementary part of it explicitly.  In a simple group every
      -- nontrivial representation is faithful; consequently our element can
      -- never act by a scalar in such a representation.  This is often the
      -- last group-theoretic input in Burnside's character argument.
      have hx1 : x ≠ (1 : S) := by
        intro h
        apply hxnc
        rw [h]
        exact (Subgroup.center S).one_mem
      have hqclass : q ∣ Nat.card (ConjClasses.mk x).carrier := by
        rw [hxcard]
        exact dvd_pow_self _ hd0
      have hqord : q ∣ Nat.card S := by
        rw [hS]
        exact dvd_mul_of_dvd_right (dvd_pow_self q hb) _
      have hx_not_scalar :
          ∀ (V : Type u) [AddCommMonoid V] [Module ℂ V]
            (ρ : Representation ℂ S V),
            (∃ g : S, ρ g ≠ LinearMap.id) →
              ∀ c : ℂ, ρ x ≠ c • LinearMap.id := by
        intro V _ _ ρ hnon c heq
        rcases mem_center_or_trivial_of_scalar_of_simple ρ c heq with hz | hz
        · exact hxnc hz
        · obtain ⟨g, hg⟩ := hnon
          exact hg (hz g)
      letI : Fintype S := Fintype.ofFinite S
      have hreg : (Representation.leftRegular ℂ S).character x = 0 :=
        character_leftRegular_of_ne_one (k := ℂ) x hx1
      have hnotint : ¬ IsIntegral ℤ ((q : ℂ)⁻¹) :=
        not_isIntegral_inv_natCast_complex_prime hq
      -- What remains is the character-theoretic part: among the irreducible
      -- complex representations one finds a nontrivial constituent of degree
      -- prime to `q`.  The central-character integrality for the above class
      -- (its size is the positive `q`-power `hxcard`) forces that constituent
      -- to have either value zero at `x`, or to act by a scalar there.  The
      -- scalar alternative is ruled out by `hx_not_scalar`; the regular
      -- character at `x ≠ 1` and `hqord` then give the usual contradiction
      -- modulo `q`.
      -- Put the non-trivial constituents of the regular representation in
      -- a finite family.  We keep the family (rather than a quotient by
      -- isomorphism of irreducibles) so that multiplicities need not be
      -- discussed in the final arithmetic step.  Maschke decomposes the
      -- regular module; the central class-sum argument says precisely that a
      -- constituent whose degree is prime to `q` has value zero here.
      have hconstituents :
          ∃ (N : ℕ)
            (W : Fin N →
              Subrepresentation (Representation.leftRegular ℂ S)),
            (∀ i : Fin N,
              Representation.IsIrreducible (W i).toRepresentation) ∧
            (∀ i : Fin N, ∃ g : S,
              (W i).toRepresentation g ≠ LinearMap.id) ∧
            ((Representation.leftRegular ℂ S).character x =
              1 + ∑ i : Fin N,
                (Module.finrank ℂ (W i).toSubmodule : ℂ) *
                  (W i).toRepresentation.character x) ∧
            (∀ i : Fin N, ¬ q ∣ Module.finrank ℂ (W i).toSubmodule →
              (W i).toRepresentation.character x = 0) := by
        -- For each irreducible summand the central class sum already gives the
        -- number theoretic half of the Burnside lemma.  This formulation is
        -- useful independently of a choice of decomposition.
        have havg : ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
            [FiniteDimensional ℂ V] (σ : Representation ℂ S V)
            [Representation.IsIrreducible σ],
            ¬ q ∣ Module.finrank ℂ V →
            IsIntegral ℤ (σ.character x / (Module.finrank ℂ V : ℂ)) := by
          intro V _ _ _ σ _ hn
          have hsiz : (burnsideClassFinset x).card = q^d :=
            burnside_classFinset_card_of_natCard x q d hxcard
          exact burnside_integral_character_average hq σ x hsiz hn
            (isIntegral_character_complex σ x)
        -- The archimedean part of Burnside's averaging lemma is rather easy
        -- to lose sight of here.  For this particular element no constituent
        -- can have all its eigenvalues equal.  We record it before choosing a
        -- decomposition; it only uses the roots-of-unity argument.
        have hno_uniform : ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
            [FiniteDimensional ℂ V] (σ : Representation ℂ S V),
            (∃ g : S, σ g ≠ LinearMap.id) →
            ¬ (∃ z : ℂ, ∀ y ∈ (σ x).charpoly.roots, y = z) := by
          intro V _ _ _ σ hnon hu
          rcases hu with ⟨z, hz⟩
          have hpow : (σ x : Module.End ℂ V) ^ Nat.card S = 1 := by
            rw [← map_pow]
            have hxpow : x ^ Nat.card S = (1:S) := by
              simpa [Nat.card_eq_fintype_card] using (pow_card_eq_one (x:=x))
            rw [hxpow, map_one]
          have hscalar : (σ x : Module.End ℂ V) = z • LinearMap.id :=
            burnside_scalar_of_roots_eq (σ x) (Nat.ne_of_gt (Nat.card_pos)) hpow hz
          exact hx_not_scalar V σ hnon z hscalar
        -- The actual local Burnside vanishing statement, independent of how
        -- the regular module is subsequently cut into constituents.
        have hvan_irred : ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
            [FiniteDimensional ℂ V] (σ : Representation ℂ S V)
            [Representation.IsIrreducible σ],
            (∃ g : S, σ g ≠ LinearMap.id) →
            ¬ q ∣ Module.finrank ℂ V → σ.character x = 0 := by
          intro V _ _ _ σ _ hnon hqdim
          -- Irrreducibility gives a nonzero space, hence a nonempty list of
          -- roots for the characteristic polynomial.
          have hnM : Nontrivial σ.asModule :=
            IsSimpleModule.nontrivial (MonoidAlgebra ℂ S) σ.asModule
          letI : Nontrivial V := hnM
          have hmV : Module.finrank ℂ V ≠ 0 :=
            (Module.finrank_pos (R := ℂ) (M := V)).ne'
          exact burnside_character_eq_zero_of_integral_average σ x hmV
            (havg V σ hqdim) (hno_uniform V σ hnon)
        -- Maschke gives, quite concretely, a *finite* direct decomposition
        -- of the regular module into simple submodules.  Working over the
        -- group algebra first avoids choices of representatives.
        --
        letI nzreg : NeZero (Nat.card S : ℂ) :=
          ⟨by exact_mod_cast (Nat.ne_of_gt (Nat.card_pos (α := S)))⟩
        have hmodule :
            ∃ (t : ℕ)
              (U : Fin t → Submodule (MonoidAlgebra ℂ S) (Representation.leftRegular ℂ S).asModule)
              (e : (Representation.leftRegular ℂ S).asModule ≃ₗ[MonoidAlgebra ℂ S] Π₀ i : Fin t, U i),
              ∀ i, IsSimpleModule (MonoidAlgebra ℂ S) (U i) := by
          -- finite over the ground field implies finite over the larger ring
          letI : Module.Finite (MonoidAlgebra ℂ S) (Representation.leftRegular ℂ S).asModule := by
            apply Module.Finite.of_restrictScalars_finite ℂ (MonoidAlgebra ℂ S)
              (Representation.leftRegular ℂ S).asModule
          exact IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp
            (MonoidAlgebra ℂ S) (Representation.leftRegular ℂ S).asModule
        obtain ⟨t, U, e, hU⟩ := hmodule
        -- The summands produced here really are subrepresentations of the
        -- *original* regular representation (not of a copy of its
        -- underlying vector space).  This harmless point is easy to miss:
        -- `ofSubmodule` builds a representation on `RestrictScalars`,
        -- whereas `ofSubmodule'` uses precisely the `asModule` synonym of
        -- `leftRegular`.
        let W₀ : Fin t → Subrepresentation (Representation.leftRegular ℂ S) :=
          fun i => Subrepresentation.ofSubmodule' (U i)
        have hs₀ (i : Fin t) :
            Representation.IsIrreducible (W₀ i).toRepresentation := by
          letI : IsSimpleModule (MonoidAlgebra ℂ S) (U i) := hU i
          exact burnside_irreducible_subrep_of_simple
            (Representation.leftRegular ℂ S) (U i)
        -- Thus every nontrivial entry of this list already satisfies the
        -- hard vanishing assertion proved above.  The part of the regular
        -- character bookkeeping still to be done is purely about
        -- multiplicities and the single trivial copy; it cannot require a
        -- new form of the local character lemma.
        have hvan₀ (i : Fin t)
            (hi : ∃ g : S,
              (W₀ i).toRepresentation g ≠ LinearMap.id) :
            ¬ q ∣ Module.finrank ℂ (W₀ i).toSubmodule →
              (W₀ i).toRepresentation.character x = 0 := by
          letI : Representation.IsIrreducible (W₀ i).toRepresentation := hs₀ i
          -- subspaces of a finite dimensional space are again finite
          -- dimensional, so the local lemma applies directly
          exact hvan_irred (W₀ i).toSubmodule (W₀ i).toRepresentation hi
        -- Delete the (possibly several isomorphic) *trivial* summands from
        -- the finite indexing family now.  Reindexing a finite subtype with
        -- `equivFin` is much nicer than carrying evidence from a filtered
        -- list through the final arithmetic lemma.
        -- Index one representative from each isomorphism class.  The
        -- semisimple decomposition lists copies; the regular module contains
        -- `dim` many copies of a given simple.  Its proof is the
        -- orthogonality computation `burnside_regular_multiplicity`.
        let rr : Setoid (Fin t) :=
          { r := fun i j => Nonempty (Representation.Equiv
                (W₀ i).toRepresentation (W₀ j).toRepresentation)
            iseqv := by
              constructor
              · intro i; exact ⟨Representation.Equiv.refl _⟩
              · intro i j h; exact ⟨h.some.symm⟩
              · intro i j k h h'; exact ⟨h.some.trans h'.some⟩ }
        let Q := Quotient rr
        letI : Fintype Q := Quotient.fintype rr
        let rep : Q → Fin t := fun c => Quotient.out c
        let good : Q → Prop := fun c => ∃ g : S,
            (W₀ (rep c)).toRepresentation g ≠ LinearMap.id
        let I := {c : Q // good c}
        let N : ℕ := Fintype.card I
        let r : Fin N ≃ I := (Fintype.equivFin I).symm
        let W : Fin N → Subrepresentation (Representation.leftRegular ℂ S) :=
          fun j => W₀ (rep (r j).1)
        refine ⟨N, W, ?_, ?_, ?_, ?_⟩
        · intro j
          change Representation.IsIrreducible (W₀ (rep (r j).1)).toRepresentation
          exact hs₀ (rep (r j).1)
        · intro j
          change ∃ g : S, (W₀ (rep (r j).1)).toRepresentation g ≠ LinearMap.id
          exact (r j).2
        · -- regular character grouped by isomorphism classes
          let cls : Fin t → Q := fun i => Quotient.mk _ i
          let occ : Q → Finset (Fin t) := fun c =>
            Finset.univ.filter (fun i => cls i = c)
          have hrep (c:Q) : cls (rep c) = c := Quotient.out_eq c
          have hrel (i j : Fin t) : cls i = cls j ↔
              Nonempty (Representation.Equiv (W₀ i).toRepresentation
                 (W₀ j).toRepresentation) := by
            exact Quotient.eq
          have hchar (i j : Fin t) (hh : cls i = cls j) (s:S) :
              (W₀ i).toRepresentation.character s =
              (W₀ j).toRepresentation.character s := by
            obtain ⟨E⟩ := (hrel i j).1 hh
            exact congrFun (Representation.char_iso E) s
          have hsums (g:S) :
              (Representation.leftRegular ℂ S).character g =
                ∑ i:Fin t, (W₀ i).toRepresentation.character g := by
            simpa [W₀] using
              (burnside_leftRegular_character_decomp (S:=S) U e g)
          have hzero' (g:S) (hg:g ≠ 1) :
              (Representation.leftRegular ℂ S).character g = 0 :=
            character_leftRegular_of_ne_one (k:=ℂ) g hg
          have hm (c:Q) : ((occ c).card : ℂ) =
                (Module.finrank ℂ (W₀ (rep c)).toSubmodule : ℂ) := by
            have hbase := burnside_regular_multiplicity W₀ hs₀ hsums hzero' (rep c)
            -- its filter is this fiber
            have hfilters : occ c = Finset.univ.filter
                (fun j : Fin t => Nonempty (Representation.Equiv
                   (W₀ (rep c)).toRepresentation (W₀ j).toRepresentation)) := by
              ext j
              simp only [occ, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro hj
                apply (hrel (rep c) j).1
                exact (hrep c).trans hj.symm
              · intro hj
                have := (hrel (rep c) j).2 hj
                exact this.symm.trans (hrep c)
            rwa [hfilters]
          have hallclasses : (∑ i:Fin t, (W₀ i).toRepresentation.character x) =
              ∑ c:Q, ((occ c).card : ℂ) *
                    (W₀ (rep c)).toRepresentation.character x := by
            symm
            calc
              (∑ c:Q, ((occ c).card : ℂ) *
                    (W₀ (rep c)).toRepresentation.character x) =
                  ∑ c:Q, ∑ i ∈ occ c, (W₀ i).toRepresentation.character x := by
                    apply Finset.sum_congr rfl
                    intro c hc'
                    have heq : (∑ i ∈ occ c,
                        (W₀ i).toRepresentation.character x) =
                        ∑ _i ∈ occ c,
                          (W₀ (rep c)).toRepresentation.character x := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      apply hchar _ _ (s:=x)
                      have hi' : cls i = c := (Finset.mem_filter.mp hi).2
                      exact hi'.trans (hrep c).symm
                    rw [heq]
                    simp
              _ = ∑ i:Fin t, (W₀ i).toRepresentation.character x := by
                    simpa [occ] using (Finset.sum_fiberwise
                       (Finset.univ : Finset (Fin t)) cls
                       (fun i => (W₀ i).toRepresentation.character x))
          rw [hsums x, hallclasses]
          have hbadfin (c:Q) (hc' : ¬ good c) :
                Module.finrank ℂ (W₀ (rep c)).toSubmodule = 1 := by
            letI irr : Representation.IsIrreducible
                (W₀ (rep c)).toRepresentation := hs₀ _
            apply burnside_finrank_eq_one_of_irreducible_trivial
                 (σ := (W₀ (rep c)).toRepresentation)
            intro g
            exact Classical.not_not.mp (not_exists.mp hc' g)
          have hbadchar (c:Q) (hc' : ¬ good c) :
                (W₀ (rep c)).toRepresentation.character x = (1:ℂ) := by
            unfold Representation.character
            have hhg : (W₀ (rep c)).toRepresentation x = LinearMap.id :=
                Classical.not_not.mp (not_exists.mp hc' x)
            rw [hhg]
            simp [hbadfin c hc']
          have hbadeq (c k:Q) (hc' : ¬ good c) (hk' : ¬ good k) : c = k := by
            letI irc : Representation.IsIrreducible (W₀ (rep c)).toRepresentation := hs₀ _
            letI irk : Representation.IsIrreducible (W₀ (rep k)).toRepresentation := hs₀ _
            let L : (W₀ (rep c)).toSubmodule ≃ₗ[ℂ] (W₀ (rep k)).toSubmodule :=
              LinearEquiv.ofFinrankEq _ _ ((hbadfin c hc').trans (hbadfin k hk').symm)
            let E : Representation.Equiv (W₀ (rep c)).toRepresentation
                       (W₀ (rep k)).toRepresentation :=
              Representation.Equiv.mk L (by
                intro g
                ext v
                have h1 : (W₀ (rep c)).toRepresentation g = LinearMap.id :=
                  Classical.not_not.mp (not_exists.mp hc' g)
                have h2 : (W₀ (rep k)).toRepresentation g = LinearMap.id :=
                  Classical.not_not.mp (not_exists.mp hk' g)
                simp [h1, h2])
            have hrs : cls (rep c) = cls (rep k) :=
                (hrel _ _).2 ⟨E⟩
            exact (hrep c).symm.trans (hrs.trans (hrep k))
          -- A fixed nonzero vector in the regular representation shows that
          -- one of these classes really is the trivial one.
          have hexbad : ∃ c:Q, ¬ good c := by
            let v : S →₀ ℂ := ∑ s:S, Finsupp.single s 1
            have hvapp (i:S) : v i = 1 := by
              simp [v, Finsupp.single_apply]
            have hv : v ≠ 0 := by
              intro h0
              have h' := hvapp 1
              rw [h0] at h'
              simp at h'
            have hvfix (a:S) : (Representation.leftRegular ℂ S a) v = v := by
              ext i
              rw [Representation.ofMulAction_apply]
              change v (a⁻¹ * i) = v i
              rw [hvapp, hvapp]
            have hev : e v ≠ 0 := by
              intro he0
              exact hv (e.injective (by simpa using he0))
            have hncomp : ∃ i:Fin t, (e v) i ≠ 0 := by
              by_contra hh
              push_neg at hh
              apply hev
              apply DFinsupp.ext
              intro i
              exact hh i
            obtain ⟨i, hi⟩ := hncomp
            have hifix (a:S) : (W₀ i).toRepresentation a ((e v) i) = (e v) i := by
              have hh := e.map_smul (MonoidAlgebra.single a (1:ℂ)) v
              have hh' := congrArg (fun z : (Π₀ i : Fin t, U i) => z i) hh
              rw [Representation.single_smul (Representation.leftRegular ℂ S)] at hh'
              simp only [DFinsupp.smul_apply] at hh'
              have hid (w : (Representation.leftRegular ℂ S).asModule) :
                  (Representation.leftRegular ℂ S).asModuleEquiv w = w := rfl
              have hh'' : (e ((Representation.leftRegular ℂ S a) v)) i =
                    MonoidAlgebra.single a (1:ℂ) • (e v) i := by
                simpa only [one_smul, hid] using hh'
              rw [hvfix a] at hh''
              -- compare in the original submodule
              have ht : MonoidAlgebra.single a (1:ℂ) • (e v) i = (e v) i := hh''.symm
              apply Subtype.ext
              change ((Representation.leftRegular ℂ S a) ((e v) i).1) = ((e v) i).1
              have ht' := congrArg (fun w : U i => (w.1 : S →₀ ℂ)) ht
              simpa [Representation.single_smul, hid] using ht'
            have hall : ∀ a:S, (W₀ i).toRepresentation a = LinearMap.id := by
              letI iri : Representation.IsIrreducible (W₀ i).toRepresentation := hs₀ i
              exact burnside_trivial_of_fixvector_irreducible
                    (σ := (W₀ i).toRepresentation) hi hifix
            refine ⟨cls i, ?_⟩
            intro hg'
            obtain ⟨a, ha⟩ := hg'
            have hequ : cls i = cls (rep (cls i)) := (hrep _).symm
            obtain ⟨E⟩ := (hrel _ _).1 hequ
            have hiso := E.isIntertwining' a
            -- conjugating identity along an equivalence remains identity
            have : (W₀ (rep (cls i))).toRepresentation a = LinearMap.id := by
              -- ext and use the intertwining map's bijectivity
              apply LinearMap.ext
              intro w
              obtain ⟨y,rfl⟩ := E.toLinearEquiv.surjective w
              simpa [hall a] using (LinearMap.congr_fun hiso y).symm
            exact ha this
          obtain ⟨c0,hc0⟩ := hexbad
          have htermbad (c:Q) (hc' : ¬ good c) :
              ((occ c).card : ℂ) *
                 (W₀ (rep c)).toRepresentation.character x = 1 := by
            rw [hm c, hbadchar c hc', hbadfin c hc']
            norm_num
          -- The remaining sums over `Q` and over its subtype of good
          -- classes are now just a finite fiber calculation.  Notice that
          -- `hbadeq` and `hexbad` say the complement is the singleton `c0`;
          -- in particular this slot is not a representation-theoretic
          -- multiplicity assertion any more.
          let F : Q → ℂ := fun c =>
            ((occ c).card : ℂ) *
                 (W₀ (rep c)).toRepresentation.character x
          have hFbad (c : Q) (hc' : ¬ good c) : F c = 1 := by
            dsimp [F]
            exact htermbad c hc'
          have hbadset :
              Finset.univ.filter (fun c : Q => ¬ good c) = {c0} := by
            ext c
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_singleton]
            constructor
            · intro hc'
              exact hbadeq c c0 hc' hc0
            · intro hcc
              subst c
              exact hc0
          have hbadSum :
              (∑ c ∈ Finset.univ.filter (fun c : Q => ¬ good c), F c) = (1:ℂ) := by
            rw [hbadset]
            simp [hFbad c0 hc0]
          have hgoodSum :
              (∑ c ∈ Finset.univ.filter good, F c) =
                ∑ j : Fin N, (Module.finrank ℂ (W j).toSubmodule : ℂ) *
                  (W j).toRepresentation.character x := by
            -- first write the filtered finite sum as a sum over its subtype
            calc
              (∑ c ∈ Finset.univ.filter good, F c) =
                    ∑ c : I, F c.1 := by
                      simpa [I] using
                        (Finset.sum_subtype (Finset.univ.filter good)
                          (fun c : Q => (by simp :
                            c ∈ (Finset.univ.filter good : Finset Q) ↔ good c)) F)
              _ = ∑ c : I,
                    (Module.finrank ℂ (W₀ (rep c.1)).toSubmodule : ℂ) *
                        (W₀ (rep c.1)).toRepresentation.character x := by
                      apply Finset.sum_congr rfl
                      intro c hc'
                      dsimp [F]
                      rw [hm c.1]
              _ = ∑ j : Fin N,
                    (Module.finrank ℂ (W j).toSubmodule : ℂ) *
                        (W j).toRepresentation.character x := by
                      let g : I → ℂ := fun c =>
                        (Module.finrank ℂ (W₀ (rep c.1)).toSubmodule : ℂ) *
                          (W₀ (rep c.1)).toRepresentation.character x
                      simpa [W, g] using (Equiv.sum_comp r g).symm
          have hsplit :
              (∑ c : Q, F c) =
                (∑ c ∈ Finset.univ.filter (fun c : Q => ¬ good c), F c) +
                (∑ c ∈ Finset.univ.filter good, F c) := by
            have h := Finset.sum_filter_add_sum_filter_not
              (Finset.univ : Finset Q) good F
            exact h.symm.trans (add_comm _ _)
          change (∑ c : Q, F c) = _
          rw [hsplit, hbadSum, hgoodSum]
        · intro j hj
          change (W₀ (rep (r j).1)).toRepresentation.character x = 0
          have hn' : ¬ q ∣ Module.finrank ℂ (W₀ (rep (r j).1)).toSubmodule := by
            exact hj
          exact hvan₀ (rep (r j).1) ((r j).2) hn'
      obtain ⟨N, W, hsimple, hnontriv, hdecomp, hvanish⟩ := hconstituents
      apply hnotint
      -- Every character value in this family is an algebraic integer already:
      -- no irreducibility or class-sum input is needed for this.
      let f : Fin N → ℕ := fun i => Module.finrank ℂ (W i).toSubmodule
      let z : Fin N → ℂ := fun i => (W i).toRepresentation.character x
      have hzint : ∀ i, IsIntegral ℤ (z i) := by
        intro i
        change IsIntegral ℤ (Representation.character (W i).toRepresentation x)
        exact isIntegral_character_complex (W i).toRepresentation x
      have heq : (0 : ℂ) = 1 + ∑ i : Fin N, (f i : ℂ) * z i := by
        simpa [f, z, hreg] using hdecomp
      have hz0 : ∀ i : Fin N, ¬ q ∣ f i → z i = 0 := by
        intro i hi
        exact hvanish i hi
      exact isIntegral_inv_of_character_family hq f z hzint heq hz0
  · intro x y
    have hy : y ∈ Subgroup.center S := by
      rw [hc]
      exact Subgroup.mem_top y
    exact (Subgroup.mem_center_iff.mp hy) x

/-- Closure under extensions plus induction on the order.  Separating this
from the simple case means that quotient and subgroup orders are accounted
for explicitly; it also avoids choosing Fintypes during the induction. -/
private lemma burnside_from_simple
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    ∀ (K : Type u) [Group K] [Finite K],
      ∀ {a b : ℕ}, Nat.card K = p ^ a * q ^ b → IsSolvable K := by
  classical
  -- strong induction on the order; all the groups that occur (a subgroup
  -- or a quotient) live in the same universe.
  suffices H : ∀ n : ℕ, ∀ (K : Type u) [Group K] [Finite K],
      Nat.card K = n → ∀ {a b : ℕ}, Nat.card K = p ^ a * q ^ b → IsSolvable K by
    intro K iG iF a b h
    exact H (Nat.card K) K rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K iG iF hn a b hcard
    -- The trivial group does not need the simple case.
    by_cases hk : Nontrivial K
    swap
    · haveI : Subsingleton K := not_nontrivial_iff_subsingleton.mp hk
      infer_instance
    letI : Nontrivial K := hk
    by_cases hN : ∃ N : Subgroup K, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤
    · rcases hN with ⟨N, hNnormal, hNbot, hNtop⟩
      letI : N.Normal := hNnormal
      have hltN : Nat.card N < n := by
        rw [← hn, ← N.index_mul_card]
        exact lt_mul_of_one_lt_left Nat.card_pos
          (Subgroup.one_lt_index_of_ne_top hNtop)
      have hltQ : Nat.card (K ⧸ N) < n := by
        rw [← hn, ← N.index_eq_card, ← N.index_mul_card]
        exact lt_mul_of_one_lt_right
          (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N)))
          ( (Subgroup.one_lt_card_iff_ne_bot N).mpr hNbot )
      have hdivN : Nat.card N ∣ p ^ a * q ^ b := by
        simpa [hcard] using N.card_subgroup_dvd_card
      have hdivQ : Nat.card (K ⧸ N) ∣ p ^ a * q ^ b := by
        simpa [hcard] using N.card_quotient_dvd_card
      obtain ⟨c,d,hcd⟩ := dvd_prime_pow_mul_prime_pow hp hq hpq
        (show Nat.card N ≠ 0 from Nat.ne_of_gt Nat.card_pos) hdivN
      obtain ⟨e,f,hef⟩ := dvd_prime_pow_mul_prime_pow hp hq hpq
        (show Nat.card (K ⧸ N) ≠ 0 from Nat.ne_of_gt Nat.card_pos) hdivQ
      have iSN : IsSolvable N := ih (Nat.card N) hltN N rfl hcd
      have iSQ : IsSolvable (K ⧸ N) := ih (Nat.card (K ⧸ N)) hltQ (K ⧸ N) rfl hef
      letI : IsSolvable N := iSN
      letI : IsSolvable (K ⧸ N) := iSQ
      refine solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) ?_
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
    · -- with no proper nontrivial normal subgroup the group is simple
      let _ : IsSimpleGroup K :=
        { toNontrivial := hk
          eq_bot_or_eq_top_of_normal := by
            intro M hM
            by_contra h
            have h' : M ≠ (⊥ : Subgroup K) ∧ M ≠ ⊤ :=
              not_or.mp h
            exact hN ⟨M, hM, h'.1, h'.2⟩ }
      exact IsSimpleGroup.comm_iff_isSolvable.mp
        (simple_burnside_comm (S := K) hp hq hpq hcard)

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q)
    (hcard : Fintype.card G = p ^ a * q ^ b) :
    IsSolvable G :=
/-ResultProofBegin-/by
  have hc : Nat.card G = p ^ a * q ^ b := by
    simpa [Nat.card_eq_fintype_card] using hcard
  exact burnside_from_simple hp hq hpq G hc
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
