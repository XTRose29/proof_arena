import Submission.PolyhedronEuler

open scoped BigOperators

noncomputable section

namespace CarrierProto

open Submission.Helpers.DehnSommerville

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma contractLeft_ιMulti_succ (d : Module.Dual R M) :
    ∀ {n : ℕ} (v : Fin (n + 1) → M),
      CliffordAlgebra.contractLeft d (ExteriorAlgebra.ιMulti R (n + 1) v) =
        ∑ i : Fin (n + 1), (((-1 : R) ^ (i : ℕ) * d (v i)) •
          ExteriorAlgebra.ιMulti R n (fun j => v (i.succAbove j))) := by
  intro n
  induction n with
  | zero =>
      intro v
      rw [ExteriorAlgebra.ιMulti_succ_apply,
        CliffordAlgebra.contractLeft_ι_mul]
      simp [ExteriorAlgebra.ιMulti_zero_apply,
        CliffordAlgebra.contractLeft_one]
  | succ n ih =>
      intro v
      rw [ExteriorAlgebra.ιMulti_succ_apply,
        CliffordAlgebra.contractLeft_ι_mul]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul]
      rw [ih (Matrix.vecTail v)]
      simp only [Fin.val_succ, pow_succ]
      rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      simp_rw [mul_smul, neg_smul]
      apply congrArg₂ (· + ·)
      · simp [Matrix.vecTail, Function.comp_def]
      · apply Finset.sum_congr rfl
        intro i _
        rw [ExteriorAlgebra.ιMulti_succ_apply]
        simp [Matrix.vecTail, Function.comp_def]

variable {V : Type*} [Fintype V] [LinearOrder V]

abbrev VertexModule := V →₀ ℚ
abbrev Exterior := ExteriorAlgebra ℚ (VertexModule (V := V))

noncomputable def augmentation : Module.Dual ℚ (VertexModule (V := V)) :=
  Finsupp.lsum ℚ (fun _ => LinearMap.id)

omit [Fintype V] [LinearOrder V] in
@[simp]
lemma augmentation_single (v : V) :
    augmentation (V := V) (Finsupp.single v 1) = 1 := by
  simp [augmentation]

omit [Fintype V] [LinearOrder V] in
lemma contract_mem_exteriorPower (n : ℕ)
    (x : ⋀[ℚ]^(n + 1) (VertexModule (V := V))) :
    CliffordAlgebra.contractLeft (augmentation (V := V)) (x : Exterior (V := V)) ∈
      ⋀[ℚ]^n (VertexModule (V := V)) := by
  have hx : (x : Exterior (V := V)) ∈
      Submodule.span ℚ (Set.range (ExteriorAlgebra.ιMulti ℚ (n + 1))) := by
    rw [ExteriorAlgebra.ιMulti_span_fixedDegree]
    exact x.property
  refine Submodule.span_induction (p := fun (y : Exterior (V := V)) _ =>
      CliffordAlgebra.contractLeft (augmentation (V := V)) y ∈
        ⋀[ℚ]^n (VertexModule (V := V))) ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨v, rfl⟩ := hy
    rw [contractLeft_ιMulti_succ]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact ExteriorAlgebra.ιMulti_range ℚ n ⟨_, rfl⟩
  · simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro a y _ hy
    rw [map_smul]
    exact Submodule.smul_mem _ a hy

noncomputable def boundaryPower (n : ℕ) :
    (⋀[ℚ]^(n + 1) (VertexModule (V := V))) →ₗ[ℚ]
      (⋀[ℚ]^n (VertexModule (V := V))) :=
  LinearMap.codRestrict _
    ((CliffordAlgebra.contractLeft (augmentation (V := V))).comp
      (⋀[ℚ]^(n + 1) (VertexModule (V := V))).subtype)
    (contract_mem_exteriorPower (V := V) n)

omit [Fintype V] [LinearOrder V] in
lemma boundaryPower_sq (n : ℕ)
    (x : ⋀[ℚ]^(n + 2) (VertexModule (V := V))) :
    boundaryPower (V := V) n (boundaryPower (V := V) (n + 1) x) = 0 := by
  apply Subtype.ext
  exact CliffordAlgebra.contractLeft_contractLeft
    (augmentation (V := V)) (x : Exterior (V := V))

/-! Abstract finite complexes and their augmented chains. -/

def AugFace (K : PreAbstractSimplicialComplex V) (n : ℕ) :=
  {s : Set.powersetCard V n // n = 0 ∨ s.1 ∈ K.faces}

noncomputable instance (n : ℕ) : Fintype (Set.powersetCard V n) :=
  Fintype.ofEquiv (Fin n ↪o V) Set.powersetCard.ofFinEmbEquiv

noncomputable instance (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Fintype (AugFace K n) := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun s : Set.powersetCard V n =>
    n = 0 ∨ s.1 ∈ K.faces) (by simp)

abbrev Chain (K : PreAbstractSimplicialComplex V) (n : ℕ) := AugFace K n →₀ ℚ

def faceVal {K : PreAbstractSimplicialComplex V} {n : ℕ} :
    AugFace K n → Set.powersetCard V n := Subtype.val

omit [Fintype V] [LinearOrder V] in
lemma faceVal_injective {K : PreAbstractSimplicialComplex V} {n : ℕ} :
    Function.Injective (faceVal (K := K) (n := n)) := Subtype.val_injective

def faceDrop {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (s : AugFace K (n + 1)) (i : Fin (n + 1)) : AugFace K n := by
  let e : Fin n ↪o V := (Fin.succAboveOrderEmb i).trans
    (Set.powersetCard.ofFinEmbEquiv.symm s.1)
  let t : Set.powersetCard V n := Set.powersetCard.ofFinEmbEquiv e
  refine ⟨t, ?_⟩
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    have hs : s.1.1 ∈ K.faces := s.2.resolve_left (by omega)
    apply (K.isRelLowerSet_faces hs).2
    · intro v hv
      have hv' : v ∈ Set.range e := by
        apply (Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range e v).mp
        exact hv
      obtain ⟨j, rfl⟩ := hv'
      apply (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s.1 _).mp
      exact ⟨i.succAbove j, rfl⟩
    · apply Finset.card_pos.mp
      rw [t.2]
      exact Nat.pos_of_ne_zero hn

noncomputable def boundaryBasis {K : PreAbstractSimplicialComplex V} (n : ℕ)
    (s : AugFace K (n + 1)) : Chain K n :=
  ∑ i : Fin (n + 1), ((-1 : ℚ) ^ (i : ℕ)) •
    Finsupp.single (faceDrop s i) 1

noncomputable def boundary (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Chain K (n + 1) →ₗ[ℚ] Chain K n :=
  Finsupp.linearCombination ℚ (boundaryBasis n)

noncomputable def fullChainPowerEquiv (n : ℕ) :
    (Set.powersetCard V n →₀ ℚ) ≃ₗ[ℚ]
      (⋀[ℚ]^n (VertexModule (V := V))) :=
  ((Finsupp.basisSingleOne.exteriorPower n).repr).symm

noncomputable def chainToPower (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Chain K n →ₗ[ℚ] (⋀[ℚ]^n (VertexModule (V := V))) :=
  (fullChainPowerEquiv (V := V) n).toLinearMap.comp
    (Finsupp.lmapDomain ℚ ℚ (faceVal (K := K) (n := n)))

omit [Fintype V] in
lemma chainToPower_injective (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Function.Injective (chainToPower K n) := by
  intro x y hxy
  apply Finsupp.mapDomain_injective (faceVal_injective (K := K) (n := n))
  apply (fullChainPowerEquiv (V := V) n).injective
  exact hxy

omit [Fintype V] in
lemma chainToPower_single (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (s : AugFace K n) :
    chainToPower K n (Finsupp.single s 1) =
      ⟨ExteriorAlgebra.ιMulti ℚ n (fun i =>
          Finsupp.single ((Set.powersetCard.ofFinEmbEquiv.symm s.1) i) 1),
        ExteriorAlgebra.ιMulti_range ℚ n ⟨_, rfl⟩⟩ := by
  apply Subtype.ext
  simp [chainToPower, fullChainPowerEquiv, faceVal,
    ExteriorAlgebra.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, Function.comp_def]

omit [Fintype V] in
lemma chainToPower_boundary (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (x : Chain K (n + 1)) :
    chainToPower K n (boundary K n x) =
      boundaryPower (V := V) n (chainToPower K (n + 1) x) := by
  refine Finsupp.induction_linear (motive := fun x =>
      chainToPower K n (boundary K n x) =
        boundaryPower (V := V) n (chainToPower K (n + 1) x)) x ?_ ?_ ?_
  · simp [boundary, chainToPower]
  · intro y z hy hz
    simp only [map_add, hy, hz]
  · intro s a
    rw [show Finsupp.single s a = a • Finsupp.single s 1 by simp]
    simp only [map_smul]
    congr 1
    simp only [boundary, Finsupp.linearCombination_single, one_smul]
    rw [boundaryBasis, map_sum]
    simp_rw [map_smul, chainToPower_single]
    apply Subtype.ext
    rw [show (((boundaryPower (V := V) n)
        ⟨ExteriorAlgebra.ιMulti ℚ (n + 1) (fun i =>
          Finsupp.single ((Set.powersetCard.ofFinEmbEquiv.symm s.1) i) 1),
          ExteriorAlgebra.ιMulti_range ℚ (n + 1) ⟨_, rfl⟩⟩ :
            ⋀[ℚ]^n (VertexModule (V := V))) : Exterior (V := V)) =
        CliffordAlgebra.contractLeft (augmentation (V := V))
          (ExteriorAlgebra.ιMulti ℚ (n + 1) (fun i =>
            Finsupp.single ((Set.powersetCard.ofFinEmbEquiv.symm s.1) i) 1)) by rfl]
    rw [contractLeft_ιMulti_succ]
    change (⋀[ℚ]^n (VertexModule (V := V))).subtype
        (∑ i : Fin (n + 1), ((-1 : ℚ) ^ (i : ℕ)) •
          ⟨ExteriorAlgebra.ιMulti ℚ n (fun j =>
            Finsupp.single ((Set.powersetCard.ofFinEmbEquiv.symm
              (faceDrop s i).1) j) 1),
            ExteriorAlgebra.ιMulti_range ℚ n ⟨_, rfl⟩⟩) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    simp only [augmentation_single, mul_one]
    congr 1
    change ExteriorAlgebra.ιMulti ℚ n (fun j =>
        Finsupp.single ((Set.powersetCard.ofFinEmbEquiv.symm
          (faceDrop s i).1) j) (1 : ℚ)) =
      ExteriorAlgebra.ιMulti ℚ n (fun j =>
        Finsupp.single ((Set.powersetCard.ofFinEmbEquiv.symm s.1)
          (i.succAbove j)) (1 : ℚ))
    congr 1
    funext j
    simp [faceDrop]

omit [Fintype V] in
lemma boundary_sq (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (x : Chain K (n + 2)) :
    boundary K n (boundary K (n + 1) x) = 0 := by
  apply chainToPower_injective K n
  rw [chainToPower_boundary, chainToPower_boundary, boundaryPower_sq]
  rfl

omit [Fintype V] [LinearOrder V] in
lemma mul_ι_mem_exteriorPower (v : V) (n : ℕ)
    (x : ⋀[ℚ]^n (VertexModule (V := V))) :
    ExteriorAlgebra.ι ℚ (Finsupp.single v 1) * (x : Exterior (V := V)) ∈
      ⋀[ℚ]^(n + 1) (VertexModule (V := V)) := by
  change ExteriorAlgebra.ι ℚ (Finsupp.single v 1) * (x : Exterior (V := V)) ∈
    (LinearMap.range (ExteriorAlgebra.ι ℚ : VertexModule (V := V) →ₗ[ℚ] _)) ^ (n + 1)
  rw [pow_succ']
  apply Submodule.mul_mem_mul
  · exact ⟨Finsupp.single v 1, rfl⟩
  · exact x.property

noncomputable def conePower (v : V) (n : ℕ) :
    (⋀[ℚ]^n (VertexModule (V := V))) →ₗ[ℚ]
      (⋀[ℚ]^(n + 1) (VertexModule (V := V))) :=
  LinearMap.codRestrict _
    ((LinearMap.mulLeft ℚ (ExteriorAlgebra.ι ℚ (Finsupp.single v 1))).comp
      (⋀[ℚ]^n (VertexModule (V := V))).subtype)
    (mul_ι_mem_exteriorPower v n)

omit [Fintype V] [LinearOrder V] in
lemma contract_exteriorPower_zero
    (x : ⋀[ℚ]^0 (VertexModule (V := V))) :
    CliffordAlgebra.contractLeft (augmentation (V := V)) (x : Exterior (V := V)) = 0 := by
  have hx : (x : Exterior (V := V)) ∈
      Submodule.span ℚ (Set.range (ExteriorAlgebra.ιMulti ℚ 0)) := by
    rw [ExteriorAlgebra.ιMulti_span_fixedDegree]
    exact x.property
  refine Submodule.span_induction (p := fun (y : Exterior (V := V)) _ =>
      CliffordAlgebra.contractLeft (augmentation (V := V)) y = 0) ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨v, rfl⟩ := hy
    simp [ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one]
  · simp
  · intro a b _ _ ha hb
    simp [map_add, ha, hb]
  · intro a y _ hy
    simp [map_smul, hy]

omit [Fintype V] [LinearOrder V] in
lemma boundaryPower_conePower_zero (v : V)
    (x : ⋀[ℚ]^0 (VertexModule (V := V))) :
    boundaryPower (V := V) 0 (conePower (V := V) v 0 x) = x := by
  apply Subtype.ext
  change CliffordAlgebra.contractLeft (augmentation (V := V))
      (ExteriorAlgebra.ι ℚ (Finsupp.single v 1) * (x : Exterior (V := V))) = x
  rw [CliffordAlgebra.contractLeft_ι_mul, augmentation_single]
  rw [contract_exteriorPower_zero]
  simp

omit [Fintype V] [LinearOrder V] in
lemma boundaryPower_conePower_succ (v : V) (n : ℕ)
    (x : ⋀[ℚ]^(n + 1) (VertexModule (V := V))) :
    boundaryPower (V := V) (n + 1) (conePower (V := V) v (n + 1) x) +
      conePower (V := V) v n (boundaryPower (V := V) n x) = x := by
  apply Subtype.ext
  change (⋀[ℚ]^(n + 1) (VertexModule (V := V))).subtype
      (boundaryPower (V := V) (n + 1) (conePower (V := V) v (n + 1) x) +
        conePower (V := V) v n (boundaryPower (V := V) n x)) = x
  rw [map_add]
  change CliffordAlgebra.contractLeft (augmentation (V := V))
        (ExteriorAlgebra.ι ℚ (Finsupp.single v 1) * (x : Exterior (V := V))) +
      ExteriorAlgebra.ι ℚ (Finsupp.single v 1) *
        CliffordAlgebra.contractLeft (augmentation (V := V)) (x : Exterior (V := V)) =
      (x : Exterior (V := V))
  rw [CliffordAlgebra.contractLeft_ι_mul, augmentation_single]
  module

def singletonPower (v : V) : Set.powersetCard V 1 :=
  ⟨{v}, Finset.card_singleton v⟩

def insertPower {n : ℕ} (v : V) (s : Set.powersetCard V n) (hv : v ∉ s.1) :
    Set.powersetCard V (n + 1) := by
  refine ⟨insert v s.1, Set.powersetCard.mem_iff.mpr ?_⟩
  rw [Finset.card_insert_of_notMem hv, s.2]

omit [Fintype V] in
lemma insertPower_coe {n : ℕ} (v : V) (s : Set.powersetCard V n) (hv : v ∉ s.1) :
    (insertPower v s hv).1 = insert v s.1 := by
  rfl

def coneSign {n : ℕ} (v : V) (s : Set.powersetCard V n) (hv : v ∉ s.1) : ℚ := by
  let hdisj : Disjoint (singletonPower v).1 s.1 := by
    simp [singletonPower, hv]
  exact (((Set.powersetCard.permOfDisjoint hdisj).sign : ℤ) : ℚ)

def insertAugFace {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : Finset V) (hF : F ∈ K.faces) (v : V) (hvF : v ∈ F)
    (s : AugFace K n) (hsF : s.1.1 ⊆ F) (hvs : v ∉ s.1.1) :
    AugFace K (n + 1) := by
  refine ⟨insertPower v s.1 hvs, Or.inr ?_⟩
  apply (K.isRelLowerSet_faces hF).2
  · rw [insertPower_coe]
    exact Finset.insert_subset hvF hsF
  · rw [insertPower_coe]
    exact Finset.insert_nonempty v s.1.1

def SupportedIn {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : Finset V) (x : Chain K n) : Prop :=
  ∀ s ∈ x.support, s.1.1 ⊆ F

omit [Fintype V] [LinearOrder V] in
lemma supportedIn_zero {K : PreAbstractSimplicialComplex V} {n : ℕ} (F : Finset V) :
    SupportedIn (K := K) (n := n) F 0 := by
  simp [SupportedIn]

omit [Fintype V] in
lemma supportedIn_add {K : PreAbstractSimplicialComplex V} {n : ℕ}
    {F : Finset V} {x y : Chain K n}
    (hx : SupportedIn F x) (hy : SupportedIn F y) : SupportedIn F (x + y) := by
  intro s hs
  rw [Finsupp.mem_support_iff] at hs
  by_contra hsub
  have hxs : x s = 0 := by
    by_contra hx0
    exact hsub (hx s (Finsupp.mem_support_iff.mpr hx0))
  have hys : y s = 0 := by
    by_contra hy0
    exact hsub (hy s (Finsupp.mem_support_iff.mpr hy0))
  simp [hxs, hys] at hs

omit [Fintype V] in
lemma supportedIn_smul {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : Finset V) (a : ℚ) {x : Chain K n} (hx : SupportedIn F x) :
    SupportedIn F (a • x) := by
  intro s hs
  rw [Finsupp.mem_support_iff] at hs
  by_contra hsub
  have hxs : x s = 0 := by
    by_contra hx0
    exact hsub (hx s (Finsupp.mem_support_iff.mpr hx0))
  simp [hxs] at hs

omit [Fintype V] in
lemma supportedIn_neg {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : Finset V) {x : Chain K n} (hx : SupportedIn F x) :
    SupportedIn F (-x) := by
  simpa only [neg_one_smul] using supportedIn_smul F (-1) hx

omit [Fintype V] in
lemma supportedIn_sub {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : Finset V) {x y : Chain K n}
    (hx : SupportedIn F x) (hy : SupportedIn F y) : SupportedIn F (x - y) := by
  rw [sub_eq_add_neg]
  exact supportedIn_add hx (supportedIn_neg F hy)

omit [Fintype V] [LinearOrder V] in
lemma supportedIn_mono {K : PreAbstractSimplicialComplex V} {n : ℕ}
    {F G : Finset V} (hFG : F ⊆ G) {x : Chain K n}
    (hx : SupportedIn F x) : SupportedIn G x := by
  intro s hs
  exact (hx s hs).trans hFG

noncomputable def coneBasis {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : Finset V) (hF : F ∈ K.faces) (v : V) (hvF : v ∈ F)
    (s : AugFace K n) : Chain K (n + 1) := by
  classical
  by_cases hsF : s.1.1 ⊆ F
  · by_cases hvs : v ∈ s.1.1
    · exact 0
    · exact coneSign v s.1 hvs •
        Finsupp.single (insertAugFace F hF v hvF s hsF hvs) 1
  · exact 0

noncomputable def coneChain {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : Finset V) (hF : F ∈ K.faces) (v : V) (hvF : v ∈ F) :
    Chain K n →ₗ[ℚ] Chain K (n + 1) :=
  Finsupp.linearCombination ℚ (coneBasis F hF v hvF)

omit [Fintype V] in
lemma chainToPower_single_exteriorBasis (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (s : AugFace K n) :
    ((chainToPower K n (Finsupp.single s 1) :
      ⋀[ℚ]^n (VertexModule (V := V))) : Exterior (V := V)) =
      Finsupp.basisSingleOne.ExteriorAlgebra s.1.1 := by
  rw [chainToPower_single]
  let b : Module.Basis V ℚ (VertexModule (V := V)) := Finsupp.basisSingleOne
  exact (ExteriorAlgebra.basis_apply_ofCard b s.1.2).symm

omit [Fintype V] in
lemma exteriorBasis_singleton (v : V) :
    Finsupp.basisSingleOne.ExteriorAlgebra ({v} : Finset V) =
      ExteriorAlgebra.ι ℚ (Finsupp.single v 1) := by
  rw [ExteriorAlgebra.basis_apply]
  change ExteriorAlgebra.ιMulti ℚ 1
      (Finsupp.basisSingleOne ∘
        Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.ofCard (Finset.card_singleton v))) = _
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  simp only [ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  congr 1
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply]

omit [Fintype V] in
set_option maxHeartbeats 1000000 in
lemma chainToPower_coneBasis {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : Finset V) (hF : F ∈ K.faces) (v : V) (hvF : v ∈ F)
    (s : AugFace K n) (hsF : s.1.1 ⊆ F) :
    chainToPower K (n + 1) (coneBasis F hF v hvF s) =
      conePower (V := V) v n (chainToPower K n (Finsupp.single s 1)) := by
  classical
  by_cases hvs : v ∈ s.1.1
  · rw [coneBasis]
    simp only [dif_pos hsF, dif_pos hvs]
    apply Subtype.ext
    simp only [map_zero]
    change 0 = ExteriorAlgebra.ι ℚ (Finsupp.single v 1) *
      ((chainToPower K n (Finsupp.single s 1) :
        ⋀[ℚ]^n (VertexModule (V := V))) : Exterior (V := V))
    rw [chainToPower_single_exteriorBasis]
    rw [← exteriorBasis_singleton]
    let b : Module.Basis V ℚ (VertexModule (V := V)) := Finsupp.basisSingleOne
    have hnd : ¬ Disjoint (singletonPower v).1 s.1.1 := by
      rw [Finset.not_disjoint_iff]
      exact ⟨v, by simp [singletonPower], hvs⟩
    exact (ExteriorAlgebra.basis_mul_of_not_disjoint
      b (singletonPower v) s.1 hnd).symm
  · let t : AugFace K (n + 1) := insertAugFace F hF v hvF s hsF hvs
    have hcone : coneBasis F hF v hvF s =
        coneSign v s.1 hvs •
          Finsupp.single t 1 := by
      rw [coneBasis]
      simp only [dif_pos hsF, dif_neg hvs, t]
    rw [hcone, map_smul]
    apply Subtype.ext
    change coneSign v s.1 hvs •
        ((chainToPower K (n + 1) (Finsupp.single t 1) :
          ⋀[ℚ]^(n + 1) (VertexModule (V := V))) : Exterior (V := V)) =
      ExteriorAlgebra.ι ℚ (Finsupp.single v 1) *
        ((chainToPower K n (Finsupp.single s 1) :
          ⋀[ℚ]^n (VertexModule (V := V))) : Exterior (V := V))
    rw [chainToPower_single_exteriorBasis K (n + 1) t]
    rw [chainToPower_single_exteriorBasis K n s]
    rw [← exteriorBasis_singleton]
    let b : Module.Basis V ℚ (VertexModule (V := V)) := Finsupp.basisSingleOne
    let hdisj : Disjoint (singletonPower v).1 s.1.1 := by
      simp [singletonPower, hvs]
    have hmul := ExteriorAlgebra.basis_mul_of_disjoint
      b (singletonPower v) s.1 hdisj
    rw [show t.1.1 =
        (Set.powersetCard.disjUnion hdisj).1 by
      simp [t, insertAugFace, insertPower, singletonPower]]
    simpa [coneSign, hdisj, b, singletonPower, Units.smul_def,
      Algebra.smul_def] using hmul.symm

omit [Fintype V] in
lemma chainToPower_coneChain {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : Finset V) (hF : F ∈ K.faces) (v : V) (hvF : v ∈ F)
    (x : Chain K n) (hx : SupportedIn F x) :
    chainToPower K (n + 1) (coneChain F hF v hvF x) =
      conePower (V := V) v n (chainToPower K n x) := by
  induction x using Finsupp.induction with
  | zero => simp [coneChain]
  | single_add s a x hs ha ih =>
      have hxs : x s = 0 := by
        by_contra h
        exact hs (Finsupp.mem_support_iff.mpr h)
      have hsa : s ∈ (Finsupp.single s a + x).support := by
        rw [Finsupp.mem_support_iff]
        simp [hxs, ha]
      have hsF : s.1.1 ⊆ F := hx s hsa
      have hxF : SupportedIn F x := by
        intro t ht
        apply hx t
        rw [Finsupp.mem_support_iff] at ht ⊢
        have hts : t ≠ s := by
          intro h
          subst t
          exact hs (Finsupp.mem_support_iff.mpr ht)
        simp [hts, ht]
      simp only [map_add, ih hxF]
      congr 1
      rw [show Finsupp.single s a = a • Finsupp.single s 1 by simp]
      simp only [map_smul]
      congr 1
      simp only [coneChain, Finsupp.linearCombination_single, one_smul]
      exact chainToPower_coneBasis F hF v hvF s hsF

omit [Fintype V] in
lemma supportedIn_coneBasis {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : Finset V) (hF : F ∈ K.faces) (v : V) (hvF : v ∈ F)
    (s : AugFace K n) (hsF : s.1.1 ⊆ F) :
    SupportedIn F (coneBasis F hF v hvF s) := by
  classical
  rw [coneBasis]
  simp only [dif_pos hsF]
  by_cases hvs : v ∈ s.1.1
  · simp [hvs, SupportedIn]
  · simp only [dif_neg hvs]
    intro t ht
    rw [Finsupp.mem_support_iff] at ht
    have hts : t = insertAugFace F hF v hvF s hsF hvs := by
      by_contra hne
      simp [hne] at ht
    subst t
    rw [insertAugFace, insertPower_coe]
    exact Finset.insert_subset hvF hsF

omit [Fintype V] in
lemma supportedIn_coneChain {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : Finset V) (hF : F ∈ K.faces) (v : V) (hvF : v ∈ F)
    (x : Chain K n) (hx : SupportedIn F x) :
    SupportedIn F (coneChain F hF v hvF x) := by
  induction x using Finsupp.induction with
  | zero => simp [coneChain, SupportedIn]
  | single_add s a x hs ha ih =>
      have hxs : x s = 0 := by
        by_contra h
        exact hs (Finsupp.mem_support_iff.mpr h)
      have hsa : s ∈ (Finsupp.single s a + x).support := by
        rw [Finsupp.mem_support_iff]
        simp [hxs, ha]
      have hsF : s.1.1 ⊆ F := hx s hsa
      have hxF : SupportedIn F x := by
        intro t ht
        apply hx t
        rw [Finsupp.mem_support_iff] at ht ⊢
        have hts : t ≠ s := by
          intro h
          subst t
          exact hs (Finsupp.mem_support_iff.mpr ht)
        simp [hts, ht]
      rw [map_add]
      apply supportedIn_add
      · rw [coneChain, Finsupp.linearCombination_single]
        exact supportedIn_smul F a (supportedIn_coneBasis F hF v hvF s hsF)
      · exact ih hxF

omit [Fintype V] in
lemma boundary_coneChain_zero {K : PreAbstractSimplicialComplex V}
    (F : Finset V) (hF : F ∈ K.faces) (v : V) (hvF : v ∈ F)
    (x : Chain K 0) (hx : SupportedIn F x) :
    boundary K 0 (coneChain F hF v hvF x) = x := by
  apply chainToPower_injective K 0
  rw [chainToPower_boundary, chainToPower_coneChain F hF v hvF x hx]
  exact boundaryPower_conePower_zero v (chainToPower K 0 x)

omit [Fintype V] in
lemma boundary_coneChain_succ_of_cycle {K : PreAbstractSimplicialComplex V}
    (F : Finset V) (hF : F ∈ K.faces) (v : V) (hvF : v ∈ F)
    (n : ℕ) (x : Chain K (n + 1)) (hx : SupportedIn F x)
    (hcycle : boundary K n x = 0) :
    boundary K (n + 1) (coneChain F hF v hvF x) = x := by
  apply chainToPower_injective K (n + 1)
  rw [chainToPower_boundary, chainToPower_coneChain F hF v hvF x hx]
  have hboundary : boundaryPower (V := V) n (chainToPower K (n + 1) x) = 0 := by
    rw [← chainToPower_boundary, hcycle, map_zero]
  have hcone := boundaryPower_conePower_succ (V := V) v n
    (chainToPower K (n + 1) x)
  rw [hboundary, map_zero, add_zero] at hcone
  exact hcone

/-! Monotone simplex carriers and their recursively constructed chain maps. -/

section Carriers

variable {W : Type*} [Fintype W] [LinearOrder W]

abbrev ComplexFace (K : PreAbstractSimplicialComplex V) := K.faces

structure FaceCarrier (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) where
  face : ComplexFace K → ComplexFace L
  mono : ∀ {s t : ComplexFace K}, s.1 ⊆ t.1 → (face s).1 ⊆ (face t).1

def nonemptyFaceOfAug {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (s : AugFace K (n + 1)) : ComplexFace K :=
  ⟨s.1.1, s.2.resolve_left (by omega)⟩

def emptyAugFace (K : PreAbstractSimplicialComplex V) : AugFace K 0 :=
  ⟨Set.powersetCard.ofCard (s := (∅ : Finset V)) (by simp), Or.inl rfl⟩

omit [Fintype V] [LinearOrder V] in
lemma augFace_zero_eq (K : PreAbstractSimplicialComplex V) (s : AugFace K 0) :
    s = emptyAugFace K := by
  apply Subtype.ext
  apply Subtype.ext
  exact Finset.card_eq_zero.mp s.1.2

omit [Fintype W] [LinearOrder W] in
lemma supportedIn_degree_zero {L : PreAbstractSimplicialComplex W}
    (F : Finset W) (x : Chain L 0) : SupportedIn F x := by
  intro s _
  have hs : s.1.1 = ∅ := Finset.card_eq_zero.mp s.1.2
  simp [hs]

omit [Fintype V] in
lemma faceDrop_subset {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (s : AugFace K (n + 1)) (i : Fin (n + 1)) :
    (faceDrop s i).1.1 ⊆ s.1.1 := by
  intro v hv
  let e : Fin n ↪o V := (Fin.succAboveOrderEmb i).trans
    (Set.powersetCard.ofFinEmbEquiv.symm s.1)
  have hv' : v ∈ Set.range e := by
    apply (Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range e v).mp
    exact hv
  obtain ⟨j, rfl⟩ := hv'
  apply (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s.1 _).mp
  exact ⟨i.succAbove j, rfl⟩

noncomputable def carriedMap
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (A : FaceCarrier K L) :
    (n : ℕ) → Chain K n →ₗ[ℚ] Chain L n
  | 0 => Finsupp.linearCombination ℚ fun _ =>
      Finsupp.single (emptyAugFace L) 1
  | n + 1 => Finsupp.linearCombination ℚ fun s => by
      let F : ComplexFace L := A.face (nonemptyFaceOfAug s)
      let hFne : F.1.Nonempty := L.isRelLowerSet_faces F.2 |>.1
      let v : W := F.1.min' hFne
      exact coneChain F.1 F.2 v (F.1.min'_mem hFne)
        (carriedMap A n (boundaryBasis n s))

omit [Fintype V] [Fintype W] in
lemma carriedMap_zero_single
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (A : FaceCarrier K L)
    (s : AugFace K 0) :
    carriedMap A 0 (Finsupp.single s 1) =
      Finsupp.single (emptyAugFace L) 1 := by
  simp [carriedMap]

omit [Fintype V] [Fintype W] in
lemma carriedMap_succ_single
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (A : FaceCarrier K L)
    (n : ℕ) (s : AugFace K (n + 1)) :
    carriedMap A (n + 1) (Finsupp.single s 1) = by
      let F : ComplexFace L := A.face (nonemptyFaceOfAug s)
      let hFne : F.1.Nonempty := L.isRelLowerSet_faces F.2 |>.1
      let v : W := F.1.min' hFne
      exact coneChain F.1 F.2 v (F.1.min'_mem hFne)
        (carriedMap A n (boundaryBasis n s)) := by
  simp [carriedMap]

omit [Fintype V] [Fintype W] in
lemma carriedMap_boundaryBasis_supported
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (A : FaceCarrier K L)
    (n : ℕ) (s : AugFace K (n + 1))
    (hprev : ∀ i : Fin (n + 1),
      SupportedIn (A.face (nonemptyFaceOfAug s)).1
        (carriedMap A n (Finsupp.single (faceDrop s i) 1))) :
    SupportedIn (A.face (nonemptyFaceOfAug s)).1
      (carriedMap A n (boundaryBasis n s)) := by
  rw [boundaryBasis, map_sum]
  apply Finset.sum_induction _ (SupportedIn (A.face (nonemptyFaceOfAug s)).1)
    (fun _ _ => supportedIn_add) (supportedIn_zero _)
  intro i _
  rw [map_smul]
  exact supportedIn_smul _ _ (hprev i)

omit [Fintype V] [Fintype W] in
lemma carriedMap_basis_supported
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (A : FaceCarrier K L) :
    ∀ (n : ℕ) (s : AugFace K (n + 1)),
      SupportedIn (A.face (nonemptyFaceOfAug s)).1
        (carriedMap A (n + 1) (Finsupp.single s 1)) := by
  intro n
  induction n with
  | zero =>
      intro s
      rw [carriedMap_succ_single]
      apply supportedIn_coneChain
      exact supportedIn_degree_zero _ _
  | succ n ih =>
      intro s
      rw [carriedMap_succ_single]
      apply supportedIn_coneChain
      apply carriedMap_boundaryBasis_supported
      intro i
      apply supportedIn_mono (A.mono (s := nonemptyFaceOfAug (faceDrop s i))
        (t := nonemptyFaceOfAug s) (faceDrop_subset s i))
      exact ih (faceDrop s i)

omit [Fintype V] [Fintype W] in
lemma carriedMap_boundary
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (A : FaceCarrier K L) :
    ∀ (n : ℕ) (x : Chain K (n + 1)),
      boundary L n (carriedMap A (n + 1) x) =
        carriedMap A n (boundary K n x) := by
  intro n
  induction n with
  | zero =>
      intro x
      refine Finsupp.induction_linear (motive := fun x =>
          boundary L 0 (carriedMap A 1 x) = carriedMap A 0 (boundary K 0 x))
        x ?_ ?_ ?_
      · simp [carriedMap, boundary]
      · intro x y hx hy
        simp only [map_add, hx, hy]
      · intro s a
        rw [show Finsupp.single s a = a • Finsupp.single s 1 by simp]
        simp only [map_smul]
        congr 1
        rw [carriedMap_succ_single]
        rw [show boundary K 0 (Finsupp.single s 1) = boundaryBasis 0 s by
          simp [boundary]]
        dsimp only
        apply boundary_coneChain_zero
        exact supportedIn_degree_zero _ _
  | succ n ih =>
      intro x
      refine Finsupp.induction_linear (motive := fun x =>
          boundary L (n + 1) (carriedMap A (n + 2) x) =
            carriedMap A (n + 1) (boundary K (n + 1) x))
        x ?_ ?_ ?_
      · simp [carriedMap, boundary]
      · intro x y hx hy
        simp only [map_add, hx, hy]
      · intro s a
        rw [show Finsupp.single s a = a • Finsupp.single s 1 by simp]
        simp only [map_smul]
        congr 1
        rw [carriedMap_succ_single]
        rw [show boundary K (n + 1) (Finsupp.single s 1) =
            boundaryBasis (n + 1) s by simp [boundary]]
        dsimp only
        apply boundary_coneChain_succ_of_cycle
        · apply carriedMap_boundaryBasis_supported
          intro i
          apply supportedIn_mono (A.mono (s := nonemptyFaceOfAug (faceDrop s i))
            (t := nonemptyFaceOfAug s) (faceDrop_subset s i))
          exact carriedMap_basis_supported A n (faceDrop s i)
        · rw [ih]
          have hsq : boundary K n (boundaryBasis (n + 1) s) = 0 := by
            simpa [boundary] using boundary_sq K n (Finsupp.single s 1)
          rw [hsq, map_zero]

structure AugChainMap (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) where
  map : ∀ n : ℕ, Chain K n →ₗ[ℚ] Chain L n
  map_boundary : ∀ (n : ℕ) (x : Chain K (n + 1)),
    boundary L n (map (n + 1) x) = map n (boundary K n x)
  map_empty : map 0 (Finsupp.single (emptyAugFace K) 1) =
    Finsupp.single (emptyAugFace L) 1

noncomputable def carriedAugChainMap
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (A : FaceCarrier K L) :
    AugChainMap K L where
  map := carriedMap A
  map_boundary := carriedMap_boundary A
  map_empty := carriedMap_zero_single A (emptyAugFace K)

def CarriedBy
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (A : FaceCarrier K L)
    (f : AugChainMap K L) : Prop :=
  ∀ (n : ℕ) (s : AugFace K (n + 1)),
    SupportedIn (A.face (nonemptyFaceOfAug s)).1
      (f.map (n + 1) (Finsupp.single s 1))

omit [Fintype V] [Fintype W] in
lemma carriedAugChainMap_carriedBy
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (A : FaceCarrier K L) :
    CarriedBy A (carriedAugChainMap A) :=
  carriedMap_basis_supported A

omit [Fintype V] [Fintype W] in
lemma AugChainMap.map_zero_eq
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (f g : AugChainMap K L)
    (x : Chain K 0) :
    f.map 0 x = g.map 0 x := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add s a x hs ha ih =>
      rw [map_add, map_add, ih]
      have hse : s = emptyAugFace K := augFace_zero_eq K s
      subst s
      rw [show Finsupp.single (emptyAugFace K) a =
          a • Finsupp.single (emptyAugFace K) 1 by simp]
      simp only [map_smul, f.map_empty, g.map_empty]

noncomputable def AugChainMap.id (K : PreAbstractSimplicialComplex V) :
    AugChainMap K K where
  map := fun _ => LinearMap.id
  map_boundary := by simp
  map_empty := rfl

noncomputable def AugChainMap.comp
    {U : Type*} [Fintype U] [LinearOrder U]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {N : PreAbstractSimplicialComplex U}
    (g : AugChainMap L N) (f : AugChainMap K L) : AugChainMap K N where
  map := fun n => (g.map n).comp (f.map n)
  map_boundary := by
    intro n x
    rw [LinearMap.comp_apply, g.map_boundary, LinearMap.comp_apply, f.map_boundary]
  map_empty := by
    rw [LinearMap.comp_apply, f.map_empty, g.map_empty]

omit [Fintype V] [Fintype W] in
lemma carriedBy_map_supported
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} {A : FaceCarrier K L}
    {f : AugChainMap K L} (hf : CarriedBy A f)
    {n : ℕ} {F : ComplexFace K} {x : Chain K (n + 1)}
    (hx : SupportedIn F.1 x) :
    SupportedIn (A.face F).1 (f.map (n + 1) x) := by
  induction x using Finsupp.induction with
  | zero => simp [SupportedIn]
  | single_add s a x hs ha ih =>
      have hxs : x s = 0 := by
        by_contra h
        exact hs (Finsupp.mem_support_iff.mpr h)
      have hsa : s ∈ (Finsupp.single s a + x).support := by
        rw [Finsupp.mem_support_iff]
        simp [hxs, ha]
      have hsF : s.1.1 ⊆ F.1 := hx s hsa
      have hxF : SupportedIn F.1 x := by
        intro t ht
        apply hx t
        rw [Finsupp.mem_support_iff] at ht ⊢
        have hts : t ≠ s := by
          intro h
          subst t
          exact hs (Finsupp.mem_support_iff.mpr ht)
        simp [hts, ht]
      rw [map_add]
      apply supportedIn_add
      · rw [show Finsupp.single s a = a • Finsupp.single s 1 by simp, map_smul]
        apply supportedIn_smul
        apply supportedIn_mono (A.mono (s := nonemptyFaceOfAug s) (t := F) hsF)
        exact hf n s
      · exact ih hxF

structure AugChainHomotopy
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (f g : AugChainMap K L) where
  hom : ∀ n : ℕ, Chain K n →ₗ[ℚ] Chain L (n + 1)
  hom_zero : ∀ x : Chain K 0,
    boundary L 0 (hom 0 x) = f.map 0 x - g.map 0 x
  hom_succ : ∀ (n : ℕ) (x : Chain K (n + 1)),
    boundary L (n + 1) (hom (n + 1) x) + hom n (boundary K n x) =
      f.map (n + 1) x - g.map (n + 1) x

noncomputable def carrierHomotopyMap
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (C : FaceCarrier K L)
    (f g : AugChainMap K L) :
    (n : ℕ) → Chain K n →ₗ[ℚ] Chain L (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℚ fun s => by
      let F : ComplexFace L := C.face (nonemptyFaceOfAug s)
      let hFne : F.1.Nonempty := L.isRelLowerSet_faces F.2 |>.1
      let v : W := F.1.min' hFne
      let z : Chain L (n + 1) :=
        f.map (n + 1) (Finsupp.single s 1) -
          g.map (n + 1) (Finsupp.single s 1) -
            carrierHomotopyMap C f g n (boundaryBasis n s)
      exact coneChain F.1 F.2 v (F.1.min'_mem hFne) z

omit [Fintype V] [Fintype W] in
lemma carrierHomotopyMap_zero
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (C : FaceCarrier K L)
    (f g : AugChainMap K L) (x : Chain K 0) :
    carrierHomotopyMap C f g 0 x = 0 := by
  rfl

omit [Fintype V] [Fintype W] in
lemma carrierHomotopyMap_succ_single
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (C : FaceCarrier K L)
    (f g : AugChainMap K L) (n : ℕ) (s : AugFace K (n + 1)) :
    carrierHomotopyMap C f g (n + 1) (Finsupp.single s 1) = by
      let F : ComplexFace L := C.face (nonemptyFaceOfAug s)
      let hFne : F.1.Nonempty := L.isRelLowerSet_faces F.2 |>.1
      let v : W := F.1.min' hFne
      let z : Chain L (n + 1) :=
        f.map (n + 1) (Finsupp.single s 1) -
          g.map (n + 1) (Finsupp.single s 1) -
            carrierHomotopyMap C f g n (boundaryBasis n s)
      exact coneChain F.1 F.2 v (F.1.min'_mem hFne) z := by
  simp [carrierHomotopyMap]

omit [Fintype V] [Fintype W] in
lemma carrierHomotopyMap_boundaryBasis_supported
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (C : FaceCarrier K L)
    (f g : AugChainMap K L) (n : ℕ) (s : AugFace K (n + 1))
    (hprev : ∀ i : Fin (n + 1),
      SupportedIn (C.face (nonemptyFaceOfAug s)).1
        (carrierHomotopyMap C f g n (Finsupp.single (faceDrop s i) 1))) :
    SupportedIn (C.face (nonemptyFaceOfAug s)).1
      (carrierHomotopyMap C f g n (boundaryBasis n s)) := by
  rw [boundaryBasis, map_sum]
  apply Finset.sum_induction _ (SupportedIn (C.face (nonemptyFaceOfAug s)).1)
    (fun _ _ => supportedIn_add) (supportedIn_zero _)
  intro i _
  rw [map_smul]
  exact supportedIn_smul _ _ (hprev i)

omit [Fintype V] [Fintype W] in
lemma carrierHomotopyMap_basis_supported
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (C : FaceCarrier K L)
    (f g : AugChainMap K L) (hf : CarriedBy C f) (hg : CarriedBy C g) :
    ∀ (n : ℕ) (s : AugFace K (n + 1)),
      SupportedIn (C.face (nonemptyFaceOfAug s)).1
        (carrierHomotopyMap C f g (n + 1) (Finsupp.single s 1)) := by
  intro n
  induction n with
  | zero =>
      intro s
      rw [carrierHomotopyMap_succ_single]
      apply supportedIn_coneChain
      apply supportedIn_sub
      · exact supportedIn_sub _ (hf 0 s) (hg 0 s)
      · simp [carrierHomotopyMap, SupportedIn]
  | succ n ih =>
      intro s
      rw [carrierHomotopyMap_succ_single]
      apply supportedIn_coneChain
      apply supportedIn_sub
      · exact supportedIn_sub _ (hf (n + 1) s) (hg (n + 1) s)
      · apply carrierHomotopyMap_boundaryBasis_supported
        intro i
        apply supportedIn_mono (C.mono (s := nonemptyFaceOfAug (faceDrop s i))
          (t := nonemptyFaceOfAug s) (faceDrop_subset s i))
        exact ih (faceDrop s i)

def HomotopyEquationAt
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (C : FaceCarrier K L)
    (f g : AugChainMap K L) (n : ℕ) (x : Chain K (n + 1)) : Prop :=
  boundary L (n + 1) (carrierHomotopyMap C f g (n + 1) x) +
      carrierHomotopyMap C f g n (boundary K n x) =
    f.map (n + 1) x - g.map (n + 1) x

omit [Fintype V] [Fintype W] in
lemma homotopyEquationAt_zero
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (C : FaceCarrier K L)
    (f g : AugChainMap K L) (n : ℕ) : HomotopyEquationAt C f g n 0 := by
  simp [HomotopyEquationAt]

omit [Fintype V] [Fintype W] in
lemma homotopyEquationAt_add
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (C : FaceCarrier K L)
    (f g : AugChainMap K L) (n : ℕ) {x y : Chain K (n + 1)}
    (hx : HomotopyEquationAt C f g n x)
    (hy : HomotopyEquationAt C f g n y) :
    HomotopyEquationAt C f g n (x + y) := by
  unfold HomotopyEquationAt at hx hy ⊢
  calc
    boundary L (n + 1) (carrierHomotopyMap C f g (n + 1) (x + y)) +
          carrierHomotopyMap C f g n (boundary K n (x + y)) =
        (boundary L (n + 1) (carrierHomotopyMap C f g (n + 1) x) +
          carrierHomotopyMap C f g n (boundary K n x)) +
        (boundary L (n + 1) (carrierHomotopyMap C f g (n + 1) y) +
          carrierHomotopyMap C f g n (boundary K n y)) := by
      simp only [map_add]
      module
    _ = (f.map (n + 1) x - g.map (n + 1) x) +
        (f.map (n + 1) y - g.map (n + 1) y) := by rw [hx, hy]
    _ = f.map (n + 1) (x + y) - g.map (n + 1) (x + y) := by
      simp only [map_add]
      module

omit [Fintype V] [Fintype W] in
lemma homotopyEquationAt_smul
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (C : FaceCarrier K L)
    (f g : AugChainMap K L) (n : ℕ) (a : ℚ) {x : Chain K (n + 1)}
    (hx : HomotopyEquationAt C f g n x) :
    HomotopyEquationAt C f g n (a • x) := by
  unfold HomotopyEquationAt at hx ⊢
  calc
    boundary L (n + 1) (carrierHomotopyMap C f g (n + 1) (a • x)) +
          carrierHomotopyMap C f g n (boundary K n (a • x)) =
        a • (boundary L (n + 1) (carrierHomotopyMap C f g (n + 1) x) +
          carrierHomotopyMap C f g n (boundary K n x)) := by
      simp only [map_smul]
      module
    _ = a • (f.map (n + 1) x - g.map (n + 1) x) := by rw [hx]
    _ = f.map (n + 1) (a • x) - g.map (n + 1) (a • x) := by
      simp only [map_smul]
      module

omit [Fintype V] [Fintype W] in
set_option maxHeartbeats 2000000 in
lemma carrierHomotopyMap_equation
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (C : FaceCarrier K L)
    (f g : AugChainMap K L) (hf : CarriedBy C f) (hg : CarriedBy C g) :
    (∀ x : Chain K 0,
      boundary L 0 (carrierHomotopyMap C f g 0 x) =
        f.map 0 x - g.map 0 x) ∧
    (∀ (n : ℕ) (x : Chain K (n + 1)), HomotopyEquationAt C f g n x) := by
  constructor
  · intro x
    rw [carrierHomotopyMap_zero, map_zero]
    rw [f.map_zero_eq g x, sub_self]
  · intro n
    induction n with
    | zero =>
        have hmaps :
            (boundary L 1).comp (carrierHomotopyMap C f g 1) +
                (carrierHomotopyMap C f g 0).comp (boundary K 0) =
              f.map 1 - g.map 1 := by
          apply Finsupp.lhom_ext
          intro s a
          rw [show Finsupp.single s a = a • Finsupp.single s 1 by simp]
          simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
            map_smul]
          have hbasis :
              boundary L 1
                  (carrierHomotopyMap C f g 1 (Finsupp.single s 1)) +
                carrierHomotopyMap C f g 0
                  (boundary K 0 (Finsupp.single s 1)) =
                f.map 1 (Finsupp.single s 1) -
                  g.map 1 (Finsupp.single s 1) := by
            rw [carrierHomotopyMap_zero, add_zero]
            rw [carrierHomotopyMap_succ_single]
            simp only [carrierHomotopyMap_zero, sub_zero]
            apply boundary_coneChain_succ_of_cycle
            · exact supportedIn_sub _ (hf 0 s) (hg 0 s)
            · rw [map_sub, f.map_boundary, g.map_boundary]
              rw [f.map_zero_eq g (boundary K 0 (Finsupp.single s 1)), sub_self]
          rw [hbasis]
        intro x
        unfold HomotopyEquationAt
        exact congrArg (fun h => h x) hmaps
    | succ n ih =>
        have hmaps :
            (boundary L (n + 2)).comp (carrierHomotopyMap C f g (n + 2)) +
                (carrierHomotopyMap C f g (n + 1)).comp (boundary K (n + 1)) =
              f.map (n + 2) - g.map (n + 2) := by
          apply Finsupp.lhom_ext
          intro s a
          rw [show Finsupp.single s a = a • Finsupp.single s 1 by simp]
          simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
            map_smul]
          have hfill : boundary L (n + 2)
              (carrierHomotopyMap C f g (n + 2) (Finsupp.single s 1)) =
            f.map (n + 2) (Finsupp.single s 1) -
              g.map (n + 2) (Finsupp.single s 1) -
                carrierHomotopyMap C f g (n + 1) (boundaryBasis (n + 1) s) := by
            rw [carrierHomotopyMap_succ_single]
            apply boundary_coneChain_succ_of_cycle
            · apply supportedIn_sub
              · exact supportedIn_sub _ (hf (n + 1) s) (hg (n + 1) s)
              · apply carrierHomotopyMap_boundaryBasis_supported
                intro i
                apply supportedIn_mono (C.mono
                  (s := nonemptyFaceOfAug (faceDrop s i))
                  (t := nonemptyFaceOfAug s) (faceDrop_subset s i))
                exact carrierHomotopyMap_basis_supported C f g hf hg n (faceDrop s i)
            · rw [map_sub, map_sub, f.map_boundary, g.map_boundary]
              have heq := ih (boundaryBasis (n + 1) s)
              unfold HomotopyEquationAt at heq
              have hsq : boundary K n (boundaryBasis (n + 1) s) = 0 := by
                simpa [boundary] using boundary_sq K n (Finsupp.single s 1)
              rw [hsq, map_zero, add_zero] at heq
              rw [show boundary K (n + 1) (Finsupp.single s 1) =
                  boundaryBasis (n + 1) s by simp [boundary]]
              rw [← heq]
              module
          rw [show boundary K (n + 1) (Finsupp.single s 1) =
              boundaryBasis (n + 1) s by simp [boundary]]
          rw [hfill]
          module
        intro x
        unfold HomotopyEquationAt
        exact congrArg (fun h => h x) hmaps

noncomputable def carrierHomotopy
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (C : FaceCarrier K L)
    (f g : AugChainMap K L) (hf : CarriedBy C f) (hg : CarriedBy C g) :
    AugChainHomotopy f g where
  hom := carrierHomotopyMap C f g
  hom_zero := (carrierHomotopyMap_equation C f g hf hg).1
  hom_succ := (carrierHomotopyMap_equation C f g hf hg).2

/-! A cone whose apex can be adjoined to every supported face. -/

def insertAugFaceWith
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (v : V) (s : AugFace K n) (hvs : v ∉ s.1.1)
    (hface : insert v s.1.1 ∈ K.faces) : AugFace K (n + 1) :=
  ⟨insertPower v s.1 hvs, Or.inr (by simpa [insertPower_coe] using hface)⟩

noncomputable def adjoinConeBasis
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (v : V) (Good : AugFace K n → Prop)
    (hinsert : ∀ s : AugFace K n, Good s → ∀ _hvs : v ∉ s.1.1,
      insert v s.1.1 ∈ K.faces) (s : AugFace K n) : Chain K (n + 1) := by
  classical
  by_cases hs : Good s
  · by_cases hvs : v ∈ s.1.1
    · exact 0
    · exact coneSign v s.1 hvs •
        Finsupp.single (insertAugFaceWith v s hvs (hinsert s hs hvs)) 1
  · exact 0

noncomputable def adjoinConeChain
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (v : V) (Good : AugFace K n → Prop)
    (hinsert : ∀ s : AugFace K n, Good s → ∀ _hvs : v ∉ s.1.1,
      insert v s.1.1 ∈ K.faces) : Chain K n →ₗ[ℚ] Chain K (n + 1) :=
  Finsupp.linearCombination ℚ (adjoinConeBasis v Good hinsert)

omit [Fintype V] in
set_option maxHeartbeats 1000000 in
lemma chainToPower_adjoinConeBasis
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (v : V) (Good : AugFace K n → Prop)
    (hinsert : ∀ s : AugFace K n, Good s → ∀ _hvs : v ∉ s.1.1,
      insert v s.1.1 ∈ K.faces)
    (s : AugFace K n) (hs : Good s) :
    chainToPower K (n + 1) (adjoinConeBasis v Good hinsert s) =
      conePower (V := V) v n (chainToPower K n (Finsupp.single s 1)) := by
  classical
  by_cases hvs : v ∈ s.1.1
  · rw [adjoinConeBasis]
    simp only [dif_pos hs, dif_pos hvs]
    apply Subtype.ext
    simp only [map_zero]
    change 0 = ExteriorAlgebra.ι ℚ (Finsupp.single v 1) *
      ((chainToPower K n (Finsupp.single s 1) :
        ⋀[ℚ]^n (VertexModule (V := V))) : Exterior (V := V))
    rw [chainToPower_single_exteriorBasis]
    rw [← exteriorBasis_singleton]
    let b : Module.Basis V ℚ (VertexModule (V := V)) := Finsupp.basisSingleOne
    have hnd : ¬ Disjoint (singletonPower v).1 s.1.1 := by
      rw [Finset.not_disjoint_iff]
      exact ⟨v, by simp [singletonPower], hvs⟩
    exact (ExteriorAlgebra.basis_mul_of_not_disjoint
      b (singletonPower v) s.1 hnd).symm
  · let t : AugFace K (n + 1) :=
      insertAugFaceWith v s hvs (hinsert s hs hvs)
    have hcone : adjoinConeBasis v Good hinsert s =
        coneSign v s.1 hvs • Finsupp.single t 1 := by
      rw [adjoinConeBasis]
      simp only [dif_pos hs, dif_neg hvs, t]
    rw [hcone, map_smul]
    apply Subtype.ext
    change coneSign v s.1 hvs •
        ((chainToPower K (n + 1) (Finsupp.single t 1) :
          ⋀[ℚ]^(n + 1) (VertexModule (V := V))) : Exterior (V := V)) =
      ExteriorAlgebra.ι ℚ (Finsupp.single v 1) *
        ((chainToPower K n (Finsupp.single s 1) :
          ⋀[ℚ]^n (VertexModule (V := V))) : Exterior (V := V))
    rw [chainToPower_single_exteriorBasis K (n + 1) t]
    rw [chainToPower_single_exteriorBasis K n s]
    rw [← exteriorBasis_singleton]
    let b : Module.Basis V ℚ (VertexModule (V := V)) := Finsupp.basisSingleOne
    let hdisj : Disjoint (singletonPower v).1 s.1.1 := by
      simp [singletonPower, hvs]
    have hmul := ExteriorAlgebra.basis_mul_of_disjoint
      b (singletonPower v) s.1 hdisj
    rw [show t.1.1 = (Set.powersetCard.disjUnion hdisj).1 by
      simp [t, insertAugFaceWith, insertPower, singletonPower]]
    simpa [coneSign, hdisj, b, singletonPower, Units.smul_def,
      Algebra.smul_def] using hmul.symm

def GoodSupported
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (Good : AugFace K n → Prop) (x : Chain K n) : Prop :=
  ∀ s ∈ x.support, Good s

omit [Fintype V] [LinearOrder V] in
lemma goodSupported_zero
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (Good : AugFace K n → Prop) : GoodSupported Good (0 : Chain K n) := by
  simp [GoodSupported]

omit [Fintype V] [LinearOrder V] in
lemma goodSupported_add
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    {Good : AugFace K n → Prop} {x y : Chain K n}
    (hx : GoodSupported Good x) (hy : GoodSupported Good y) :
    GoodSupported Good (x + y) := by
  intro s hs
  rw [Finsupp.mem_support_iff] at hs
  by_contra hgood
  have hxs : x s = 0 := by
    by_contra hne
    exact hgood (hx s (Finsupp.mem_support_iff.mpr hne))
  have hys : y s = 0 := by
    by_contra hne
    exact hgood (hy s (Finsupp.mem_support_iff.mpr hne))
  simp [hxs, hys] at hs

omit [Fintype V] [LinearOrder V] in
lemma goodSupported_smul
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    {Good : AugFace K n → Prop} (a : ℚ) {x : Chain K n}
    (hx : GoodSupported Good x) : GoodSupported Good (a • x) := by
  intro s hs
  rw [Finsupp.mem_support_iff] at hs
  apply hx s
  rw [Finsupp.mem_support_iff]
  intro hxs
  simp [hxs] at hs

omit [Fintype V] [LinearOrder V] in
lemma goodSupported_sum
    {K : PreAbstractSimplicialComplex V} {n : ℕ} {ι : Type*}
    {Good : AugFace K n → Prop} (t : Finset ι) (f : ι → Chain K n)
    (hf : ∀ i ∈ t, GoodSupported Good (f i)) :
    GoodSupported Good (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [goodSupported_zero]
  | @insert i t hit ih =>
      rw [Finset.sum_insert hit]
      exact goodSupported_add (hf i (Finset.mem_insert_self i t))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

omit [Fintype V] in
lemma chainToPower_adjoinConeChain
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (v : V) (Good : AugFace K n → Prop)
    (hinsert : ∀ s : AugFace K n, Good s → ∀ _hvs : v ∉ s.1.1,
      insert v s.1.1 ∈ K.faces)
    (x : Chain K n) (hx : GoodSupported Good x) :
    chainToPower K (n + 1) (adjoinConeChain v Good hinsert x) =
      conePower (V := V) v n (chainToPower K n x) := by
  induction x using Finsupp.induction with
  | zero => simp [adjoinConeChain]
  | single_add s a x hs ha ih =>
      have hxs : x s = 0 := by
        by_contra h
        exact hs (Finsupp.mem_support_iff.mpr h)
      have hsa : s ∈ (Finsupp.single s a + x).support := by
        rw [Finsupp.mem_support_iff]
        simp [hxs, ha]
      have hGood : Good s := hx s hsa
      have hxGood : GoodSupported Good x := by
        intro t ht
        apply hx t
        rw [Finsupp.mem_support_iff] at ht ⊢
        have hts : t ≠ s := by
          intro h
          subst t
          exact hs (Finsupp.mem_support_iff.mpr ht)
        simp [hts, ht]
      simp only [map_add, ih hxGood]
      congr 1
      rw [show Finsupp.single s a = a • Finsupp.single s 1 by simp]
      simp only [map_smul]
      congr 1
      simp only [adjoinConeChain, Finsupp.linearCombination_single, one_smul]
      exact chainToPower_adjoinConeBasis v Good hinsert s hGood

omit [Fintype V] in
lemma boundary_adjoinConeChain_zero
    {K : PreAbstractSimplicialComplex V}
    (v : V) (Good : AugFace K 0 → Prop)
    (hinsert : ∀ s : AugFace K 0, Good s → ∀ _hvs : v ∉ s.1.1,
      insert v s.1.1 ∈ K.faces)
    (x : Chain K 0) (hx : GoodSupported Good x) :
    boundary K 0 (adjoinConeChain v Good hinsert x) = x := by
  apply chainToPower_injective K 0
  rw [chainToPower_boundary, chainToPower_adjoinConeChain v Good hinsert x hx]
  exact boundaryPower_conePower_zero v (chainToPower K 0 x)

omit [Fintype V] in
lemma boundary_adjoinConeChain_succ_of_cycle
    {K : PreAbstractSimplicialComplex V}
    (v : V) (n : ℕ) (Good : AugFace K (n + 1) → Prop)
    (hinsert : ∀ s : AugFace K (n + 1), Good s → ∀ _hvs : v ∉ s.1.1,
      insert v s.1.1 ∈ K.faces)
    (x : Chain K (n + 1)) (hx : GoodSupported Good x)
    (hcycle : boundary K n x = 0) :
    boundary K (n + 1) (adjoinConeChain v Good hinsert x) = x := by
  apply chainToPower_injective K (n + 1)
  rw [chainToPower_boundary, chainToPower_adjoinConeChain v Good hinsert x hx]
  have hboundary : boundaryPower (V := V) n (chainToPower K (n + 1) x) = 0 := by
    rw [← chainToPower_boundary, hcycle, map_zero]
  have hcone := boundaryPower_conePower_succ (V := V) v n
    (chainToPower K (n + 1) x)
  rw [hboundary, map_zero, add_zero] at hcone
  exact hcone

/-! Abstract barycentric subdivision. -/

noncomputable instance complexFaceFintype
    (K : PreAbstractSimplicialComplex V) : Fintype (ComplexFace K) :=
  Fintype.ofFinite (ComplexFace K)

noncomputable instance complexFaceLinearOrder
    (K : PreAbstractSimplicialComplex V) : LinearOrder (ComplexFace K) :=
  LinearOrder.lift' (Fintype.equivFin (ComplexFace K))
    (Fintype.equivFin (ComplexFace K)).injective

def IsAbstractFaceChain (K : PreAbstractSimplicialComplex V)
    (c : Finset (ComplexFace K)) : Prop :=
  c.Nonempty ∧ ∀ F ∈ c, ∀ G ∈ c, F.1 ⊆ G.1 ∨ G.1 ⊆ F.1

omit [Fintype V] [LinearOrder V] in
lemma IsAbstractFaceChain.subset
    {K : PreAbstractSimplicialComplex V}
    {c d : Finset (ComplexFace K)} (hc : IsAbstractFaceChain K c)
    (hd : d.Nonempty) (hdc : d ⊆ c) : IsAbstractFaceChain K d := by
  refine ⟨hd, ?_⟩
  intro F hF G hG
  exact hc.2 F (hdc hF) G (hdc hG)

def barycentricAbstract (K : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (ComplexFace K) where
  faces := {c | IsAbstractFaceChain K c}
  isRelLowerSet_faces := by
    intro c hc
    refine ⟨hc.1, ?_⟩
    intro d hdc hd
    exact hc.subset hd hdc

omit [Fintype V] [LinearOrder V] in
lemma mem_barycentricAbstract_faces
    {K : PreAbstractSimplicialComplex V} {c : Finset (ComplexFace K)} :
    c ∈ (barycentricAbstract K).faces ↔ IsAbstractFaceChain K c :=
  Iff.rfl

omit [Fintype V] in
lemma exists_abstractChainTop
    {K : PreAbstractSimplicialComplex V}
    (c : Finset (ComplexFace K)) (hc : IsAbstractFaceChain K c) :
    ∃ F ∈ c, ∀ G ∈ c, G.1 ⊆ F.1 := by
  classical
  induction c using Finset.induction_on with
  | empty =>
      have hfalse : False := by simpa using hc.1
      exact hfalse.elim
  | @insert a c ha ih =>
      by_cases hcne : c.Nonempty
      · have hchainc : IsAbstractFaceChain K c :=
          hc.subset hcne (Finset.subset_insert a c)
        obtain ⟨F, hFc, hFtop⟩ := ih hchainc
        rcases hc.2 a (Finset.mem_insert_self a c) F
            (Finset.mem_insert_of_mem hFc) with haF | hFa
        · exact ⟨F, Finset.mem_insert_of_mem hFc, by
            intro G hG
            rcases Finset.mem_insert.mp hG with rfl | hGc
            · exact haF
            · exact hFtop G hGc⟩
        · exact ⟨a, Finset.mem_insert_self a c, by
            intro G hG
            rcases Finset.mem_insert.mp hG with rfl | hGc
            · exact Finset.Subset.rfl
            · exact (hFtop G hGc).trans hFa⟩
      · have hcempty : c = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcne
        subst c
        exact ⟨a, by simp, by simp⟩

noncomputable def abstractChainTop
    {K : PreAbstractSimplicialComplex V}
    (c : Finset (ComplexFace K)) (hc : IsAbstractFaceChain K c) :
    ComplexFace K :=
  Classical.choose (exists_abstractChainTop c hc)

omit [Fintype V] in
lemma abstractChainTop_mem
    {K : PreAbstractSimplicialComplex V}
    (c : Finset (ComplexFace K)) (hc : IsAbstractFaceChain K c) :
    abstractChainTop c hc ∈ c :=
  (Classical.choose_spec (exists_abstractChainTop c hc)).1

omit [Fintype V] in
lemma le_abstractChainTop
    {K : PreAbstractSimplicialComplex V}
    (c : Finset (ComplexFace K)) (hc : IsAbstractFaceChain K c)
    (F : ComplexFace K) (hF : F ∈ c) :
    F.1 ⊆ (abstractChainTop c hc).1 :=
  (Classical.choose_spec (exists_abstractChainTop c hc)).2 F hF

noncomputable def barycentricProjectionCarrier
    (K : PreAbstractSimplicialComplex V) :
    FaceCarrier (barycentricAbstract K) K where
  face := fun c => abstractChainTop c.1 c.2
  mono := by
    intro c d hcd
    exact le_abstractChainTop d.1 d.2 (abstractChainTop c.1 c.2)
      (hcd (abstractChainTop_mem c.1 c.2))

def BaryUnder
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : ComplexFace K) (c : AugFace (barycentricAbstract K) n) : Prop :=
  ∀ G ∈ c.1.1, G.1 ⊆ F.1

omit [Fintype V] [LinearOrder V] in
lemma baryUnder_mono
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    {F G : ComplexFace K} (hFG : F.1 ⊆ G.1)
    {c : AugFace (barycentricAbstract K) n} (hc : BaryUnder F c) :
    BaryUnder G c := by
  intro H hH
  exact (hc H hH).trans hFG

omit [Fintype V] in
lemma insert_bary_face
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : ComplexFace K) (c : AugFace (barycentricAbstract K) n)
    (hcF : BaryUnder F c) :
    insert F c.1.1 ∈ (barycentricAbstract K).faces := by
  refine ⟨Finset.insert_nonempty F c.1.1, ?_⟩
  intro A hA B hB
  rcases Finset.mem_insert.mp hA with rfl | hAc
  · rcases Finset.mem_insert.mp hB with rfl | hBc
    · exact Or.inl Finset.Subset.rfl
    · exact Or.inr (hcF B hBc)
  rcases Finset.mem_insert.mp hB with rfl | hBc
  · exact Or.inl (hcF A hAc)
  · have hcchain : IsAbstractFaceChain K c.1.1 := by
      by_cases hn : n = 0
      · have hempty : c.1.1 = ∅ := Finset.card_eq_zero.mp (hn ▸ c.1.2)
        simp [hempty] at hAc
      · exact c.2.resolve_left hn
    exact hcchain.2 A hAc B hBc

omit [LinearOrder V] in
lemma baryInsertable
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : ComplexFace K) (c : AugFace (barycentricAbstract K) n)
    (hc : BaryUnder F c) (_hFc : F ∉ c.1.1) :
    @insert (ComplexFace K) (Finset (ComplexFace K))
      (@Finset.instInsert (ComplexFace K) (complexFaceLinearOrder K).toDecidableEq)
      F c.1.1 ∈ (barycentricAbstract K).faces := by
  letI : DecidableEq (ComplexFace K) := (complexFaceLinearOrder K).toDecidableEq
  refine ⟨Finset.insert_nonempty F c.1.1, ?_⟩
  intro A hA B hB
  rcases Finset.mem_insert.mp hA with rfl | hAc
  · rcases Finset.mem_insert.mp hB with rfl | hBc
    · exact Or.inl Finset.Subset.rfl
    · exact Or.inr (hc B hBc)
  rcases Finset.mem_insert.mp hB with rfl | hBc
  · exact Or.inl (hc A hAc)
  · have hcchain : IsAbstractFaceChain K c.1.1 := by
      by_cases hn : n = 0
      · have hempty : c.1.1 = ∅ := Finset.card_eq_zero.mp (hn ▸ c.1.2)
        simp [hempty] at hAc
      · exact c.2.resolve_left hn
    exact hcchain.2 A hAc B hBc

set_option maxHeartbeats 1000000 in
noncomputable def baryConeBasis
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : ComplexFace K) (c : AugFace (barycentricAbstract K) n) :
    Chain (barycentricAbstract K) (n + 1) := by
  letI : DecidableEq (ComplexFace K) := Subtype.instDecidableEq
  exact adjoinConeBasis (K := barycentricAbstract K) F (BaryUnder F)
    (baryInsertable F) c

set_option maxHeartbeats 1000000 in
noncomputable def baryConeChain
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : ComplexFace K) :
    Chain (barycentricAbstract K) n →ₗ[ℚ]
      Chain (barycentricAbstract K) (n + 1) := by
  letI : DecidableEq (ComplexFace K) := Subtype.instDecidableEq
  exact adjoinConeChain (K := barycentricAbstract K) F (BaryUnder F)
    (baryInsertable F)

omit [Fintype V] [LinearOrder V] in
lemma baryUnder_degree_zero
    {K : PreAbstractSimplicialComplex V} (F : ComplexFace K)
    (x : Chain (barycentricAbstract K) 0) :
    GoodSupported (BaryUnder F) x := by
  intro c _ G hG
  have hcempty : c.1.1 = ∅ := Finset.card_eq_zero.mp c.1.2
  simp [hcempty] at hG

omit [LinearOrder V] in
lemma adjoinConeBasis_baryUnder
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : ComplexFace K) (c : AugFace (barycentricAbstract K) n)
    (hc : BaryUnder F c) :
    GoodSupported (BaryUnder F)
      (baryConeBasis F c) := by
  classical
  letI : DecidableEq (ComplexFace K) := (complexFaceLinearOrder K).toDecidableEq
  unfold baryConeBasis
  rw [adjoinConeBasis]
  simp only [dif_pos hc]
  by_cases hFc : F ∈ c.1.1
  · simp [hFc, GoodSupported]
  · simp only [dif_neg hFc]
    intro t ht
    rw [Finsupp.mem_support_iff] at ht
    have htc : t = insertAugFaceWith F c hFc (baryInsertable F c hc hFc) := by
      by_contra hne
      simp [hne] at ht
    subst t
    intro G hG
    rw [insertAugFaceWith, insertPower_coe] at hG
    rcases Finset.mem_insert.mp hG with rfl | hGc
    · exact Finset.Subset.rfl
    · exact hc G hGc

omit [LinearOrder V] in
lemma adjoinConeChain_baryUnder
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (F : ComplexFace K) (x : Chain (barycentricAbstract K) n)
    (hx : GoodSupported (BaryUnder F) x) :
    GoodSupported (BaryUnder F)
      (baryConeChain F x) := by
  unfold baryConeChain
  induction x using Finsupp.induction with
  | zero => simp [adjoinConeChain, GoodSupported]
  | single_add c a x hs ha ih =>
      have hxs : x c = 0 := by
        by_contra h
        exact hs (Finsupp.mem_support_iff.mpr h)
      have hca : c ∈ (Finsupp.single c a + x).support := by
        rw [Finsupp.mem_support_iff]
        simp [hxs, ha]
      have hc : BaryUnder F c := hx c hca
      have hx' : GoodSupported (BaryUnder F) x := by
        intro t ht
        apply hx t
        rw [Finsupp.mem_support_iff] at ht ⊢
        have htc : t ≠ c := by
          intro h
          subst t
          exact hs (Finsupp.mem_support_iff.mpr ht)
        simp [htc, ht]
      rw [map_add]
      apply goodSupported_add
      · rw [show Finsupp.single c a = a • Finsupp.single c 1 by simp, map_smul]
        apply goodSupported_smul
        have hb := adjoinConeBasis_baryUnder F c hc
        simpa [baryConeChain, baryConeBasis, adjoinConeChain] using hb
      · exact ih hx'

noncomputable def subdivisionMap (K : PreAbstractSimplicialComplex V) :
    (n : ℕ) → Chain K n →ₗ[ℚ] Chain (barycentricAbstract K) n
  | 0 => Finsupp.linearCombination ℚ fun _ =>
      Finsupp.single (emptyAugFace (barycentricAbstract K)) 1
  | n + 1 => Finsupp.linearCombination ℚ fun s => by
      let F : ComplexFace K := nonemptyFaceOfAug s
      exact baryConeChain F (subdivisionMap K n (boundaryBasis n s))

lemma subdivisionMap_zero_single (K : PreAbstractSimplicialComplex V)
    (s : AugFace K 0) :
    subdivisionMap K 0 (Finsupp.single s 1) =
      Finsupp.single (emptyAugFace (barycentricAbstract K)) 1 := by
  simp [subdivisionMap]

lemma subdivisionMap_succ_single (K : PreAbstractSimplicialComplex V)
    (n : ℕ) (s : AugFace K (n + 1)) :
    subdivisionMap K (n + 1) (Finsupp.single s 1) = by
      let F : ComplexFace K := nonemptyFaceOfAug s
      exact baryConeChain F (subdivisionMap K n (boundaryBasis n s)) := by
  simp [subdivisionMap]

lemma subdivisionMap_boundaryBasis_baryUnder
    (K : PreAbstractSimplicialComplex V)
    (n : ℕ) (s : AugFace K (n + 1))
    (hprev : ∀ i : Fin (n + 1),
      GoodSupported (BaryUnder (nonemptyFaceOfAug s))
        (subdivisionMap K n (Finsupp.single (faceDrop s i) 1))) :
    GoodSupported (BaryUnder (nonemptyFaceOfAug s))
      (subdivisionMap K n (boundaryBasis n s)) := by
  rw [boundaryBasis, map_sum]
  apply goodSupported_sum
  intro i _
  rw [map_smul]
  exact goodSupported_smul _ (hprev i)

lemma subdivisionMap_basis_baryUnder (K : PreAbstractSimplicialComplex V) :
    ∀ (n : ℕ) (s : AugFace K (n + 1)),
      GoodSupported (BaryUnder (nonemptyFaceOfAug s))
        (subdivisionMap K (n + 1) (Finsupp.single s 1)) := by
  intro n
  induction n with
  | zero =>
      intro s
      rw [subdivisionMap_succ_single]
      apply adjoinConeChain_baryUnder
      exact baryUnder_degree_zero _ _
  | succ n ih =>
      intro s
      rw [subdivisionMap_succ_single]
      apply adjoinConeChain_baryUnder
      apply subdivisionMap_boundaryBasis_baryUnder
      intro i c hc G hG
      exact (ih (faceDrop s i) c hc G hG).trans (faceDrop_subset s i)

lemma subdivisionMap_boundary (K : PreAbstractSimplicialComplex V) :
    ∀ (n : ℕ) (x : Chain K (n + 1)),
      boundary (barycentricAbstract K) n (subdivisionMap K (n + 1) x) =
        subdivisionMap K n (boundary K n x) := by
  intro n
  induction n with
  | zero =>
      intro x
      refine Finsupp.induction_linear (motive := fun x =>
          boundary (barycentricAbstract K) 0 (subdivisionMap K 1 x) =
            subdivisionMap K 0 (boundary K 0 x)) x ?_ ?_ ?_
      · simp [subdivisionMap, boundary]
      · intro x y hx hy
        simp only [map_add, hx, hy]
      · intro s a
        rw [show Finsupp.single s a = a • Finsupp.single s 1 by simp]
        simp only [map_smul]
        congr 1
        rw [subdivisionMap_succ_single]
        rw [show boundary K 0 (Finsupp.single s 1) = boundaryBasis 0 s by
          simp [boundary]]
        dsimp only
        apply boundary_adjoinConeChain_zero
        exact baryUnder_degree_zero _ _
  | succ n ih =>
      intro x
      refine Finsupp.induction_linear (motive := fun x =>
          boundary (barycentricAbstract K) (n + 1) (subdivisionMap K (n + 2) x) =
            subdivisionMap K (n + 1) (boundary K (n + 1) x)) x ?_ ?_ ?_
      · simp [subdivisionMap, boundary]
      · intro x y hx hy
        simp only [map_add, hx, hy]
      · intro s a
        rw [show Finsupp.single s a = a • Finsupp.single s 1 by simp]
        simp only [map_smul]
        congr 1
        rw [subdivisionMap_succ_single]
        rw [show boundary K (n + 1) (Finsupp.single s 1) =
            boundaryBasis (n + 1) s by simp [boundary]]
        dsimp only
        apply boundary_adjoinConeChain_succ_of_cycle
        · apply subdivisionMap_boundaryBasis_baryUnder
          intro i c hc G hG
          exact (subdivisionMap_basis_baryUnder K n (faceDrop s i) c hc G hG).trans
            (faceDrop_subset s i)
        · rw [ih]
          have hsq : boundary K n (boundaryBasis (n + 1) s) = 0 := by
            simpa [boundary] using boundary_sq K n (Finsupp.single s 1)
          rw [hsq, map_zero]

noncomputable def subdivisionAugChainMap (K : PreAbstractSimplicialComplex V) :
    AugChainMap K (barycentricAbstract K) where
  map := subdivisionMap K
  map_boundary := subdivisionMap_boundary K
  map_empty := subdivisionMap_zero_single K (emptyAugFace K)

def identityFaceCarrier (K : PreAbstractSimplicialComplex V) : FaceCarrier K K where
  face := id
  mono := fun h => h

omit [Fintype V] in
lemma identityAugChainMap_carriedBy (K : PreAbstractSimplicialComplex V) :
    CarriedBy (identityFaceCarrier K) (AugChainMap.id K) := by
  intro n s t ht
  rw [Finsupp.mem_support_iff] at ht
  have hts : t = s := by
    by_contra hne
    simp [AugChainMap.id, hne] at ht
  subst t
  exact Finset.Subset.rfl

noncomputable def barycentricProjectionAugChainMap
    (K : PreAbstractSimplicialComplex V) :
    AugChainMap (barycentricAbstract K) K :=
  carriedAugChainMap (barycentricProjectionCarrier K)

lemma projectionMap_baryUnder
    (K : PreAbstractSimplicialComplex V) {n : ℕ}
    (F : ComplexFace K) (x : Chain (barycentricAbstract K) (n + 1))
    (hx : GoodSupported (BaryUnder F) x) :
    SupportedIn F.1 ((barycentricProjectionAugChainMap K).map (n + 1) x) := by
  induction x using Finsupp.induction with
  | zero => simp [SupportedIn]
  | single_add c a x hs ha ih =>
      have hxc : x c = 0 := by
        by_contra hne
        exact hs (Finsupp.mem_support_iff.mpr hne)
      have hca : c ∈ (Finsupp.single c a + x).support := by
        rw [Finsupp.mem_support_iff]
        simp [hxc, ha]
      have hc : BaryUnder F c := hx c hca
      have hx' : GoodSupported (BaryUnder F) x := by
        intro t ht
        apply hx t
        rw [Finsupp.mem_support_iff] at ht ⊢
        have htc : t ≠ c := by
          intro h
          subst t
          exact hs (Finsupp.mem_support_iff.mpr ht)
        simp [htc, ht]
      rw [map_add]
      apply supportedIn_add
      · rw [show Finsupp.single c a = a • Finsupp.single c 1 by simp, map_smul]
        apply supportedIn_smul
        have hcface : c.1.1 ∈ (barycentricAbstract K).faces :=
          c.2.resolve_left (by omega)
        apply supportedIn_mono
          (hc (abstractChainTop (K := K) c.1 hcface)
            (abstractChainTop_mem (K := K) c.1 hcface))
        exact carriedAugChainMap_carriedBy (barycentricProjectionCarrier K) n c
      · exact ih hx'

lemma projectionSubdivision_carriedBy (K : PreAbstractSimplicialComplex V) :
    CarriedBy (identityFaceCarrier K)
      ((barycentricProjectionAugChainMap K).comp (subdivisionAugChainMap K)) := by
  intro n s
  change SupportedIn s.1.1
    ((barycentricProjectionAugChainMap K).map (n + 1)
      (subdivisionMap K (n + 1) (Finsupp.single s 1)))
  exact projectionMap_baryUnder K (nonemptyFaceOfAug s) _
    (subdivisionMap_basis_baryUnder K n s)

noncomputable def projectionSubdivisionHomotopy
    (K : PreAbstractSimplicialComplex V) :
    AugChainHomotopy
      ((barycentricProjectionAugChainMap K).comp (subdivisionAugChainMap K))
      (AugChainMap.id K) :=
  carrierHomotopy (identityFaceCarrier K) _ _
    (projectionSubdivision_carriedBy K) (identityAugChainMap_carriedBy K)

omit [Fintype V] [LinearOrder V] in
lemma goodSupported_baryUnder_mono
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    {F G : ComplexFace K} (hFG : F.1 ⊆ G.1)
    {x : Chain (barycentricAbstract K) n}
    (hx : GoodSupported (BaryUnder F) x) :
    GoodSupported (BaryUnder G) x := by
  intro c hc
  exact baryUnder_mono hFG (hx c hc)

omit [Fintype V] [LinearOrder V] in
lemma goodSupported_sub
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    {Good : AugFace K n → Prop} (x : Chain K n) {y : Chain K n}
    (hx : GoodSupported Good x) (hy : GoodSupported Good y) :
    GoodSupported Good (x - y) := by
  rw [sub_eq_add_neg]
  apply goodSupported_add hx
  intro s hs
  apply hy s
  simpa using hs

noncomputable def augBaryTop
    {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (c : AugFace (barycentricAbstract K) (n + 1)) : ComplexFace K :=
  abstractChainTop c.1
    (mem_barycentricAbstract_faces.mp (c.2.resolve_left (by omega)))

lemma subdivisionMap_supported_baryUnder
    (K : PreAbstractSimplicialComplex V) (F : ComplexFace K) :
    ∀ {n : ℕ} {x : Chain K n}, SupportedIn F.1 x →
      GoodSupported (BaryUnder F) (subdivisionMap K n x) := by
  intro n
  cases n with
  | zero =>
      intro x _
      exact baryUnder_degree_zero F _
  | succ n =>
      intro x hx
      induction x using Finsupp.induction with
      | zero => simp [goodSupported_zero]
      | single_add s a x hs ha ih =>
          have hxs : x s = 0 := by
            by_contra h
            exact hs (Finsupp.mem_support_iff.mpr h)
          have hsa : s ∈ (Finsupp.single s a + x).support := by
            rw [Finsupp.mem_support_iff]
            simp [hxs, ha]
          have hsF : s.1.1 ⊆ F.1 := hx s hsa
          have hxF : SupportedIn F.1 x := by
            intro t ht
            apply hx t
            rw [Finsupp.mem_support_iff] at ht ⊢
            have hts : t ≠ s := by
              intro h
              subst t
              exact hs (Finsupp.mem_support_iff.mpr ht)
            simp [hts, ht]
          rw [map_add]
          apply goodSupported_add
          · rw [show Finsupp.single s a = a • Finsupp.single s 1 by simp, map_smul]
            apply goodSupported_smul
            exact goodSupported_baryUnder_mono hsF
              (subdivisionMap_basis_baryUnder K n s)
          · exact ih hxF

lemma identityMap_basis_baryUnder_top
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (c : AugFace (barycentricAbstract K) (n + 1)) :
    GoodSupported
      (BaryUnder (augBaryTop c))
      ((AugChainMap.id (barycentricAbstract K)).map (n + 1)
        (Finsupp.single c 1)) := by
  intro t ht
  rw [Finsupp.mem_support_iff] at ht
  have htc : t = c := by
    by_contra hne
    simp [AugChainMap.id, hne] at ht
  subst t
  intro G hG
  exact le_abstractChainTop c.1
    (mem_barycentricAbstract_faces.mp (c.2.resolve_left (by omega))) G hG

lemma subdivisionProjection_basis_baryUnder_top
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (c : AugFace (barycentricAbstract K) (n + 1)) :
    GoodSupported
      (BaryUnder (augBaryTop c))
      (((subdivisionAugChainMap K).comp
        (barycentricProjectionAugChainMap K)).map (n + 1)
          (Finsupp.single c 1)) := by
  change GoodSupported _
    (subdivisionMap K (n + 1)
      ((barycentricProjectionAugChainMap K).map (n + 1)
        (Finsupp.single c 1)))
  apply subdivisionMap_supported_baryUnder K
  exact carriedAugChainMap_carriedBy (barycentricProjectionCarrier K) n c

lemma top_faceDrop_subset
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (c : AugFace (barycentricAbstract K) (n + 2)) (i : Fin (n + 2)) :
    (augBaryTop (faceDrop c i)).1 ⊆ (augBaryTop c).1 := by
  simp only [augBaryTop]
  refine le_abstractChainTop c.1
    ((mem_barycentricAbstract_faces (K := K)).mp (c.2.resolve_left (by omega)))
    (abstractChainTop (K := K) (faceDrop c i).1
      ((mem_barycentricAbstract_faces (K := K)).mp
        ((faceDrop c i).2.resolve_left (by omega)))) ?_
  apply faceDrop_subset c i
  exact abstractChainTop_mem (K := K) (faceDrop c i).1
    ((mem_barycentricAbstract_faces (K := K)).mp
      ((faceDrop c i).2.resolve_left (by omega)))

noncomputable def subdivisionProjectionHomotopyMap
    (K : PreAbstractSimplicialComplex V) :
    (n : ℕ) → Chain (barycentricAbstract K) n →ₗ[ℚ]
      Chain (barycentricAbstract K) (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℚ fun c => by
      let F : ComplexFace K := augBaryTop c
      let z : Chain (barycentricAbstract K) (n + 1) :=
        ((subdivisionAugChainMap K).comp
            (barycentricProjectionAugChainMap K)).map (n + 1)
              (Finsupp.single c 1) -
          (AugChainMap.id (barycentricAbstract K)).map (n + 1)
              (Finsupp.single c 1) -
            subdivisionProjectionHomotopyMap K n (boundaryBasis n c)
      exact baryConeChain F z

lemma subdivisionProjectionHomotopyMap_zero
    (K : PreAbstractSimplicialComplex V)
    (x : Chain (barycentricAbstract K) 0) :
    subdivisionProjectionHomotopyMap K 0 x = 0 := by
  rfl

lemma subdivisionProjectionHomotopyMap_succ_single
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (c : AugFace (barycentricAbstract K) (n + 1)) :
    subdivisionProjectionHomotopyMap K (n + 1) (Finsupp.single c 1) = by
      let F : ComplexFace K := augBaryTop c
      let z : Chain (barycentricAbstract K) (n + 1) :=
        ((subdivisionAugChainMap K).comp
            (barycentricProjectionAugChainMap K)).map (n + 1)
              (Finsupp.single c 1) -
          (AugChainMap.id (barycentricAbstract K)).map (n + 1)
              (Finsupp.single c 1) -
            subdivisionProjectionHomotopyMap K n (boundaryBasis n c)
      exact baryConeChain F z := by
  simp [subdivisionProjectionHomotopyMap]

lemma subdivisionProjectionHomotopyMap_boundaryBasis_baryUnder
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (c : AugFace (barycentricAbstract K) (n + 1))
    (hprev : ∀ i : Fin (n + 1),
      GoodSupported
        (BaryUnder (augBaryTop c))
        (subdivisionProjectionHomotopyMap K n
          (Finsupp.single (faceDrop c i) 1))) :
    GoodSupported
      (BaryUnder (augBaryTop c))
      (subdivisionProjectionHomotopyMap K n (boundaryBasis n c)) := by
  rw [boundaryBasis, map_sum]
  apply goodSupported_sum
  intro i _
  rw [map_smul]
  exact goodSupported_smul _ (hprev i)

lemma subdivisionProjectionHomotopyMap_basis_baryUnder_top
    (K : PreAbstractSimplicialComplex V) :
    ∀ (n : ℕ) (c : AugFace (barycentricAbstract K) (n + 1)),
      GoodSupported
        (BaryUnder (augBaryTop c))
        (subdivisionProjectionHomotopyMap K (n + 1)
          (Finsupp.single c 1)) := by
  intro n
  induction n with
  | zero =>
      intro c
      rw [subdivisionProjectionHomotopyMap_succ_single]
      apply adjoinConeChain_baryUnder
      apply goodSupported_sub
      · exact goodSupported_sub _
          (subdivisionProjection_basis_baryUnder_top K 0 c)
          (identityMap_basis_baryUnder_top K 0 c)
      · simp [subdivisionProjectionHomotopyMap, GoodSupported]
  | succ n ih =>
      intro c
      rw [subdivisionProjectionHomotopyMap_succ_single]
      apply adjoinConeChain_baryUnder
      apply goodSupported_sub
      · exact goodSupported_sub _
          (subdivisionProjection_basis_baryUnder_top K (n + 1) c)
          (identityMap_basis_baryUnder_top K (n + 1) c)
      · apply subdivisionProjectionHomotopyMap_boundaryBasis_baryUnder
        intro i
        exact goodSupported_baryUnder_mono (top_faceDrop_subset K n c i)
          (ih (faceDrop c i))

def SubdivisionProjectionHomotopyEquationAt
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (x : Chain (barycentricAbstract K) (n + 1)) : Prop :=
  boundary (barycentricAbstract K) (n + 1)
      (subdivisionProjectionHomotopyMap K (n + 1) x) +
    subdivisionProjectionHomotopyMap K n
      (boundary (barycentricAbstract K) n x) =
    ((subdivisionAugChainMap K).comp
      (barycentricProjectionAugChainMap K)).map (n + 1) x -
      (AugChainMap.id (barycentricAbstract K)).map (n + 1) x

set_option maxHeartbeats 2000000 in
lemma subdivisionProjectionHomotopyMap_equation
    (K : PreAbstractSimplicialComplex V) :
    (∀ x : Chain (barycentricAbstract K) 0,
      boundary (barycentricAbstract K) 0
          (subdivisionProjectionHomotopyMap K 0 x) =
        ((subdivisionAugChainMap K).comp
          (barycentricProjectionAugChainMap K)).map 0 x -
          (AugChainMap.id (barycentricAbstract K)).map 0 x) ∧
    (∀ (n : ℕ) (x : Chain (barycentricAbstract K) (n + 1)),
      SubdivisionProjectionHomotopyEquationAt K n x) := by
  constructor
  · intro x
    rw [subdivisionProjectionHomotopyMap_zero, map_zero]
    rw [AugChainMap.map_zero_eq _ _ x, sub_self]
  · intro n
    induction n with
    | zero =>
        have hmaps :
            (boundary (barycentricAbstract K) 1).comp
                (subdivisionProjectionHomotopyMap K 1) +
              (subdivisionProjectionHomotopyMap K 0).comp
                (boundary (barycentricAbstract K) 0) =
            ((subdivisionAugChainMap K).comp
              (barycentricProjectionAugChainMap K)).map 1 -
              (AugChainMap.id (barycentricAbstract K)).map 1 := by
          apply Finsupp.lhom_ext
          intro c a
          rw [show Finsupp.single c a = a • Finsupp.single c 1 by simp]
          simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
            map_smul]
          have hbasis :
              boundary (barycentricAbstract K) 1
                  (subdivisionProjectionHomotopyMap K 1
                    (Finsupp.single c 1)) +
                subdivisionProjectionHomotopyMap K 0
                  (boundary (barycentricAbstract K) 0
                    (Finsupp.single c 1)) =
              ((subdivisionAugChainMap K).comp
                (barycentricProjectionAugChainMap K)).map 1
                  (Finsupp.single c 1) -
                (AugChainMap.id (barycentricAbstract K)).map 1
                  (Finsupp.single c 1) := by
            rw [subdivisionProjectionHomotopyMap_zero, add_zero]
            rw [subdivisionProjectionHomotopyMap_succ_single]
            simp only [subdivisionProjectionHomotopyMap_zero, sub_zero]
            apply boundary_adjoinConeChain_succ_of_cycle
            · exact goodSupported_sub _
                (subdivisionProjection_basis_baryUnder_top K 0 c)
                (identityMap_basis_baryUnder_top K 0 c)
            · rw [map_sub]
              rw [((subdivisionAugChainMap K).comp
                (barycentricProjectionAugChainMap K)).map_boundary]
              rw [(AugChainMap.id (barycentricAbstract K)).map_boundary]
              rw [AugChainMap.map_zero_eq _ _
                (boundary (barycentricAbstract K) 0 (Finsupp.single c 1)), sub_self]
          rw [hbasis]
        intro x
        unfold SubdivisionProjectionHomotopyEquationAt
        exact congrArg (fun h => h x) hmaps
    | succ n ih =>
        have hmaps :
            (boundary (barycentricAbstract K) (n + 2)).comp
                (subdivisionProjectionHomotopyMap K (n + 2)) +
              (subdivisionProjectionHomotopyMap K (n + 1)).comp
                (boundary (barycentricAbstract K) (n + 1)) =
            ((subdivisionAugChainMap K).comp
              (barycentricProjectionAugChainMap K)).map (n + 2) -
              (AugChainMap.id (barycentricAbstract K)).map (n + 2) := by
          apply Finsupp.lhom_ext
          intro c a
          rw [show Finsupp.single c a = a • Finsupp.single c 1 by simp]
          simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
            map_smul]
          have hfill :
              boundary (barycentricAbstract K) (n + 2)
                  (subdivisionProjectionHomotopyMap K (n + 2)
                    (Finsupp.single c 1)) =
              ((subdivisionAugChainMap K).comp
                (barycentricProjectionAugChainMap K)).map (n + 2)
                  (Finsupp.single c 1) -
                (AugChainMap.id (barycentricAbstract K)).map (n + 2)
                  (Finsupp.single c 1) -
                subdivisionProjectionHomotopyMap K (n + 1)
                  (boundaryBasis (n + 1) c) := by
            rw [subdivisionProjectionHomotopyMap_succ_single]
            apply boundary_adjoinConeChain_succ_of_cycle
            · apply goodSupported_sub
              · exact goodSupported_sub _
                  (subdivisionProjection_basis_baryUnder_top K (n + 1) c)
                  (identityMap_basis_baryUnder_top K (n + 1) c)
              · apply subdivisionProjectionHomotopyMap_boundaryBasis_baryUnder
                intro i
                exact goodSupported_baryUnder_mono (top_faceDrop_subset K n c i)
                  (subdivisionProjectionHomotopyMap_basis_baryUnder_top K n
                    (faceDrop c i))
            · rw [map_sub, map_sub]
              rw [((subdivisionAugChainMap K).comp
                (barycentricProjectionAugChainMap K)).map_boundary]
              rw [(AugChainMap.id (barycentricAbstract K)).map_boundary]
              have heq := ih (boundaryBasis (n + 1) c)
              unfold SubdivisionProjectionHomotopyEquationAt at heq
              have hsq : boundary (barycentricAbstract K) n
                  (boundaryBasis (n + 1) c) = 0 := by
                simpa [boundary] using boundary_sq (barycentricAbstract K) n
                  (Finsupp.single c 1)
              rw [hsq, map_zero, add_zero] at heq
              rw [show boundary (barycentricAbstract K) (n + 1)
                  (Finsupp.single c 1) = boundaryBasis (n + 1) c by
                simp [boundary]]
              rw [← heq]
              module
          rw [show boundary (barycentricAbstract K) (n + 1)
              (Finsupp.single c 1) = boundaryBasis (n + 1) c by simp [boundary]]
          rw [hfill]
          module
        intro x
        unfold SubdivisionProjectionHomotopyEquationAt
        exact congrArg (fun h => h x) hmaps

noncomputable def subdivisionProjectionHomotopy
    (K : PreAbstractSimplicialComplex V) :
    AugChainHomotopy
      ((subdivisionAugChainMap K).comp (barycentricProjectionAugChainMap K))
      (AugChainMap.id (barycentricAbstract K)) where
  hom := subdivisionProjectionHomotopyMap K
  hom_zero := (subdivisionProjectionHomotopyMap_equation K).1
  hom_succ := (subdivisionProjectionHomotopyMap_equation K).2

/-! Alternating traces of finite augmented chain complexes. -/

def chainMapTrace (K : PreAbstractSimplicialComplex V)
    (f : AugChainMap K K) (n : ℕ) : ℚ :=
  LinearMap.trace ℚ (Chain K n) (f.map n)

def alternatingTraceUpTo (K : PreAbstractSimplicialComplex V)
    (f : AugChainMap K K) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N + 1), (-1 : ℚ) ^ n * chainMapTrace K f n

def alternatingTraceDiffUpTo (K : PreAbstractSimplicialComplex V)
    (f g : AugChainMap K K) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N + 1),
    (-1 : ℚ) ^ n * LinearMap.trace ℚ (Chain K n) (f.map n - g.map n)

omit [Fintype V] in
lemma alternatingTraceDiffUpTo_eq_sub
    (K : PreAbstractSimplicialComplex V) (f g : AugChainMap K K) (N : ℕ) :
    alternatingTraceDiffUpTo K f g N =
      alternatingTraceUpTo K f N - alternatingTraceUpTo K g N := by
  rw [alternatingTraceDiffUpTo, alternatingTraceUpTo, alternatingTraceUpTo]
  calc
    (∑ n ∈ Finset.range (N + 1),
        (-1 : ℚ) ^ n * LinearMap.trace ℚ (Chain K n) (f.map n - g.map n)) =
        ∑ n ∈ Finset.range (N + 1),
          ((-1 : ℚ) ^ n * chainMapTrace K f n -
            (-1 : ℚ) ^ n * chainMapTrace K g n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [map_sub]
      unfold chainMapTrace
      ring
    _ = (∑ n ∈ Finset.range (N + 1), (-1 : ℚ) ^ n * chainMapTrace K f n) -
        ∑ n ∈ Finset.range (N + 1), (-1 : ℚ) ^ n * chainMapTrace K g n := by
      rw [Finset.sum_sub_distrib]

omit [Fintype V] in
lemma homotopy_trace_zero
    {K : PreAbstractSimplicialComplex V} {f g : AugChainMap K K}
    (H : AugChainHomotopy f g) :
    LinearMap.trace ℚ (Chain K 0) (f.map 0 - g.map 0) =
      LinearMap.trace ℚ (Chain K 0) ((boundary K 0).comp (H.hom 0)) := by
  congr 1
  apply LinearMap.ext
  intro x
  exact (H.hom_zero x).symm

lemma homotopy_trace_succ
    {K : PreAbstractSimplicialComplex V} {f g : AugChainMap K K}
    (H : AugChainHomotopy f g) (n : ℕ) :
    LinearMap.trace ℚ (Chain K (n + 1)) (f.map (n + 1) - g.map (n + 1)) =
      LinearMap.trace ℚ (Chain K (n + 1))
        ((boundary K (n + 1)).comp (H.hom (n + 1))) +
      LinearMap.trace ℚ (Chain K n) ((boundary K n).comp (H.hom n)) := by
  have hmaps : f.map (n + 1) - g.map (n + 1) =
      (boundary K (n + 1)).comp (H.hom (n + 1)) +
        (H.hom n).comp (boundary K n) := by
    apply LinearMap.ext
    intro x
    exact (H.hom_succ n x).symm
  rw [hmaps, map_add]
  congr 1
  exact LinearMap.trace_comp_comm' (boundary K n) (H.hom n)

lemma alternatingTraceDiffUpTo_homotopy
    {K : PreAbstractSimplicialComplex V} {f g : AugChainMap K K}
    (H : AugChainHomotopy f g) (N : ℕ) :
    alternatingTraceDiffUpTo K f g N =
      (-1 : ℚ) ^ N * LinearMap.trace ℚ (Chain K N)
        ((boundary K N).comp (H.hom N)) := by
  induction N with
  | zero =>
      rw [alternatingTraceDiffUpTo]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
        one_mul]
      exact homotopy_trace_zero H
  | succ N ih =>
      rw [alternatingTraceDiffUpTo, Finset.sum_range_succ]
      change alternatingTraceDiffUpTo K f g N +
          (-1 : ℚ) ^ (N + 1) *
            LinearMap.trace ℚ (Chain K (N + 1))
              (f.map (N + 1) - g.map (N + 1)) = _
      rw [ih, homotopy_trace_succ H N, pow_succ]
      ring

omit [LinearOrder V] in
lemma no_augFace_above_card (K : PreAbstractSimplicialComplex V)
    (s : AugFace K (Fintype.card V + 1)) : False := by
  have hcard : s.1.1.card = Fintype.card V + 1 := s.1.2
  have hle : s.1.1.card ≤ Fintype.card V := Finset.card_le_univ s.1.1
  omega

omit [LinearOrder V] in
lemma no_augFace_of_card_lt (K : PreAbstractSimplicialComplex V)
    {n : ℕ} (hn : Fintype.card V < n) (s : AugFace K n) : False := by
  have hcard : s.1.1.card = n := s.1.2
  have hle : s.1.1.card ≤ Fintype.card V := Finset.card_le_univ s.1.1
  omega

omit [LinearOrder V] in
lemma chain_above_card_eq_zero (K : PreAbstractSimplicialComplex V)
    (x : Chain K (Fintype.card V + 1)) : x = 0 := by
  ext s
  exact (no_augFace_above_card K s).elim

lemma homotopy_top_boundary_trace_zero
    {K : PreAbstractSimplicialComplex V} {f g : AugChainMap K K}
    (H : AugChainHomotopy f g) :
    LinearMap.trace ℚ (Chain K (Fintype.card V))
      ((boundary K (Fintype.card V)).comp (H.hom (Fintype.card V))) = 0 := by
  have hhom : H.hom (Fintype.card V) = 0 := by
    apply LinearMap.ext
    intro x
    exact chain_above_card_eq_zero K _
  rw [hhom, LinearMap.comp_zero, map_zero]

lemma homotopy_boundary_trace_zero_of_card_le
    {K : PreAbstractSimplicialComplex V} {f g : AugChainMap K K}
    (H : AugChainHomotopy f g) {N : ℕ} (hN : Fintype.card V ≤ N) :
    LinearMap.trace ℚ (Chain K N) ((boundary K N).comp (H.hom N)) = 0 := by
  have hhom : H.hom N = 0 := by
    apply LinearMap.ext
    intro x
    ext s
    exact (no_augFace_of_card_lt K (by omega) s).elim
  rw [hhom, LinearMap.comp_zero, map_zero]

lemma alternatingTraceUpTo_eq_of_homotopy
    {K : PreAbstractSimplicialComplex V} {f g : AugChainMap K K}
    (H : AugChainHomotopy f g) :
    alternatingTraceUpTo K f (Fintype.card V) =
      alternatingTraceUpTo K g (Fintype.card V) := by
  have hdiff := alternatingTraceDiffUpTo_homotopy H (Fintype.card V)
  rw [homotopy_top_boundary_trace_zero H, mul_zero,
    alternatingTraceDiffUpTo_eq_sub] at hdiff
  exact sub_eq_zero.mp hdiff

lemma alternatingTraceUpTo_eq_of_homotopy_of_card_le
    {K : PreAbstractSimplicialComplex V} {f g : AugChainMap K K}
    (H : AugChainHomotopy f g) {N : ℕ} (hN : Fintype.card V ≤ N) :
    alternatingTraceUpTo K f N = alternatingTraceUpTo K g N := by
  have hdiff := alternatingTraceDiffUpTo_homotopy H N
  rw [homotopy_boundary_trace_zero_of_card_le H hN, mul_zero,
    alternatingTraceDiffUpTo_eq_sub] at hdiff
  exact sub_eq_zero.mp hdiff

def chainEulerQ (K : PreAbstractSimplicialComplex V) : ℚ :=
  ∑ n ∈ Finset.range (Fintype.card V + 1),
    (-1 : ℚ) ^ n * (Fintype.card (AugFace K n) : ℚ)

lemma alternatingTrace_id_eq_chainEulerQ (K : PreAbstractSimplicialComplex V) :
    alternatingTraceUpTo K (AugChainMap.id K) (Fintype.card V) = chainEulerQ K := by
  rw [alternatingTraceUpTo, chainEulerQ]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  change LinearMap.trace ℚ (Chain K n) LinearMap.id = _
  rw [LinearMap.trace_id, Module.finrank_finsupp_self]

lemma chainMapTrace_id_eq_zero_of_card_lt
    (K : PreAbstractSimplicialComplex V) {n : ℕ} (hn : Fintype.card V < n) :
    chainMapTrace K (AugChainMap.id K) n = 0 := by
  have hcard : Fintype.card (AugFace K n) = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨no_augFace_of_card_lt K hn⟩
  rw [chainMapTrace]
  change LinearMap.trace ℚ (Chain K n) LinearMap.id = 0
  rw [LinearMap.trace_id, Module.finrank_finsupp_self, hcard]
  norm_num

lemma alternatingTrace_id_eq_chainEulerQ_of_card_le
    (K : PreAbstractSimplicialComplex V) {N : ℕ} (hN : Fintype.card V ≤ N) :
    alternatingTraceUpTo K (AugChainMap.id K) N = chainEulerQ K := by
  rw [← alternatingTrace_id_eq_chainEulerQ K]
  rw [alternatingTraceUpTo, alternatingTraceUpTo]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hN))
  intro n hnN hnV
  have hlt : Fintype.card V < n := by
    rw [Finset.mem_range] at hnN
    simp only [Finset.mem_range, not_lt] at hnV
    omega
  rw [chainMapTrace_id_eq_zero_of_card_lt K hlt, mul_zero]

structure AugChainHomotopyEquiv
    {W : Type*} [Fintype W] [LinearOrder W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W) where
  hom : AugChainMap K L
  inv : AugChainMap L K
  inv_hom : AugChainHomotopy (inv.comp hom) (AugChainMap.id K)
  hom_inv : AugChainHomotopy (hom.comp inv) (AugChainMap.id L)

noncomputable def subdivisionChainHomotopyEquiv
    (K : PreAbstractSimplicialComplex V) :
    AugChainHomotopyEquiv K (barycentricAbstract K) where
  hom := subdivisionAugChainMap K
  inv := barycentricProjectionAugChainMap K
  inv_hom := projectionSubdivisionHomotopy K
  hom_inv := subdivisionProjectionHomotopy K

lemma alternatingTrace_comp_comm
    {W : Type*} [Fintype W] [LinearOrder W]
    {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}
    (f : AugChainMap K L) (g : AugChainMap L K) (N : ℕ) :
    alternatingTraceUpTo K (g.comp f) N = alternatingTraceUpTo L (f.comp g) N := by
  rw [alternatingTraceUpTo, alternatingTraceUpTo]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  exact LinearMap.trace_comp_comm' (f.map n) (g.map n)

lemma chainEulerQ_eq_of_homotopyEquiv
    {W : Type*} [Fintype W] [LinearOrder W]
    {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}
    (e : AugChainHomotopyEquiv K L) : chainEulerQ K = chainEulerQ L := by
  let N := max (Fintype.card V) (Fintype.card W)
  have hVK : Fintype.card V ≤ N := Nat.le_max_left _ _
  have hWL : Fintype.card W ≤ N := Nat.le_max_right _ _
  calc
    chainEulerQ K = alternatingTraceUpTo K (AugChainMap.id K) N :=
      (alternatingTrace_id_eq_chainEulerQ_of_card_le K hVK).symm
    _ = alternatingTraceUpTo K (e.inv.comp e.hom) N :=
      (alternatingTraceUpTo_eq_of_homotopy_of_card_le e.inv_hom hVK).symm
    _ = alternatingTraceUpTo L (e.hom.comp e.inv) N :=
      alternatingTrace_comp_comm e.hom e.inv N
    _ = alternatingTraceUpTo L (AugChainMap.id L) N :=
      alternatingTraceUpTo_eq_of_homotopy_of_card_le e.hom_inv hWL
    _ = chainEulerQ L := alternatingTrace_id_eq_chainEulerQ_of_card_le L hWL

end Carriers

end CarrierProto
