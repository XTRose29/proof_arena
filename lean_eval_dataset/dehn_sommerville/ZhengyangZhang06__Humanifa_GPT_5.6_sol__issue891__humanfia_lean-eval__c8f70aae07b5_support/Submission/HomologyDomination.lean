import Submission.SimplicialApproximation

namespace Submission.Helpers.DehnSommerville

open CarrierProto

noncomputable section

namespace FinitePolyhedron

variable {V W : Type*} [Fintype V] [LinearOrder V]
  [Fintype W] [LinearOrder W]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def augCycles (K : PreAbstractSimplicialComplex V) :
    (n : ℕ) → Submodule ℚ (Chain K n)
  | 0 => ⊤
  | n + 1 => LinearMap.ker (boundary K n)

def augBoundaries (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Submodule ℚ (Chain K n) := LinearMap.range (boundary K n)

omit [Fintype V] in
lemma augBoundaries_le_cycles (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    augBoundaries K n ≤ augCycles K n := by
  cases n with
  | zero => exact le_top
  | succ n =>
      rintro x ⟨y, rfl⟩
      change boundary K n (boundary K (n + 1) y) = 0
      exact boundary_sq K n y

def augBoundariesInCycles (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Submodule ℚ (augCycles K n) :=
  (augBoundaries K n).comap (augCycles K n).subtype

abbrev AugHomology (K : PreAbstractSimplicialComplex V) (n : ℕ) :=
  (augCycles K n) ⧸ augBoundariesInCycles K n

noncomputable def augCycleMap
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (f : AugChainMap K L) :
    (n : ℕ) → augCycles K n →ₗ[ℚ] augCycles L n
  | 0 => LinearMap.codRestrict _ ((f.map 0).comp (augCycles K 0).subtype)
      (fun _ => Submodule.mem_top)
  | n + 1 => LinearMap.codRestrict _
      ((f.map (n + 1)).comp (augCycles K (n + 1)).subtype) (by
        intro x
        change boundary L n (f.map (n + 1) x.1) = 0
        rw [f.map_boundary]
        rw [x.2, map_zero])

omit [Fintype V] [Fintype W] in
@[simp]
lemma augCycleMap_coe
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (f : AugChainMap K L)
    (n : ℕ) (x : augCycles K n) :
    (augCycleMap f n x).1 = f.map n x.1 := by
  cases n <;> rfl

omit [Fintype V] [Fintype W] in
lemma augCycleMap_boundaries
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (f : AugChainMap K L) (n : ℕ) :
    augBoundariesInCycles K n ≤
      (augBoundariesInCycles L n).comap (augCycleMap f n) := by
  intro x hx
  change (augCycleMap f n x).1 ∈ augBoundaries L n
  rw [augCycleMap_coe]
  change x.1 ∈ augBoundaries K n at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨f.map (n + 1) y, ?_⟩
  rw [f.map_boundary, hy]

noncomputable def augHomologyMap
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (f : AugChainMap K L) (n : ℕ) :
    AugHomology K n →ₗ[ℚ] AugHomology L n :=
  (augBoundariesInCycles K n).mapQ (augBoundariesInCycles L n)
    (augCycleMap f n) (augCycleMap_boundaries f n)

omit [Fintype V] [Fintype W] in
@[simp]
lemma augHomologyMap_mk
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (f : AugChainMap K L)
    (n : ℕ) (x : augCycles K n) :
    augHomologyMap f n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (augCycleMap f n x) :=
  rfl

omit [Fintype V] in
lemma augHomologyMap_id (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    augHomologyMap (AugChainMap.id K) n = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
      rw [augHomologyMap_mk]
      apply (Submodule.Quotient.eq (augBoundariesInCycles K n)).mpr
      change ((augCycleMap (AugChainMap.id K) n x - x : augCycles K n)).1 ∈
        augBoundaries K n
      change (augCycleMap (AugChainMap.id K) n x).1 - x.1 ∈ augBoundaries K n
      rw [augCycleMap_coe]
      simp [AugChainMap.id]

omit [Fintype V] [Fintype W] in
lemma augHomologyMap_comp
    {U : Type*} [Fintype U] [LinearOrder U]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {M : PreAbstractSimplicialComplex U}
    (g : AugChainMap L M) (f : AugChainMap K L) (n : ℕ) :
    augHomologyMap (g.comp f) n =
      (augHomologyMap g n).comp (augHomologyMap f n) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
      rw [augHomologyMap_mk, LinearMap.comp_apply, augHomologyMap_mk,
        augHomologyMap_mk]
      apply (Submodule.Quotient.eq (augBoundariesInCycles M n)).mpr
      change ((augCycleMap (g.comp f) n x -
        augCycleMap g n (augCycleMap f n x) : augCycles M n)).1 ∈ augBoundaries M n
      change (augCycleMap (g.comp f) n x).1 -
        (augCycleMap g n (augCycleMap f n x)).1 ∈ augBoundaries M n
      rw [augCycleMap_coe, augCycleMap_coe, augCycleMap_coe]
      simp [AugChainMap.comp]

omit [Fintype V] [Fintype W] in
lemma augHomologyMap_eq_of_homotopy
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {f g : AugChainMap K L} (H : AugChainHomotopy f g) (n : ℕ) :
    augHomologyMap f n = augHomologyMap g n := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
      apply (Submodule.Quotient.eq (augBoundariesInCycles L n)).mpr
      change (augCycleMap f n x).1 - (augCycleMap g n x).1 ∈ augBoundaries L n
      rw [augCycleMap_coe, augCycleMap_coe]
      cases n with
      | zero =>
          exact ⟨H.hom 0 x.1, H.hom_zero x.1⟩
      | succ n =>
          have h := H.hom_succ n x.1
          rw [x.2, map_zero, add_zero] at h
          exact ⟨H.hom (n + 1) x.1, h⟩

omit [Fintype W] in
lemma augHomologyMap_injective_of_left_homotopyInverse
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    (f : AugChainMap K L) (g : AugChainMap L K)
    (H : AugChainHomotopy (g.comp f) (AugChainMap.id K)) (n : ℕ) :
    Function.Injective (augHomologyMap f n) := by
  apply Function.LeftInverse.injective (g := augHomologyMap g n)
  intro x
  have hcomp := augHomologyMap_comp g f n
  have hhom := augHomologyMap_eq_of_homotopy H n
  have hid := augHomologyMap_id K n
  calc
    augHomologyMap g n (augHomologyMap f n x) =
        augHomologyMap (g.comp f) n x := by
      rw [hcomp]
      rfl
    _ = augHomologyMap (AugChainMap.id K) n x := by rw [hhom]
    _ = x := by rw [hid]; rfl

lemma augHomology_finrank_le_of_domination
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    (f : AugChainMap K L) (g : AugChainMap L K)
    (H : AugChainHomotopy (g.comp f) (AugChainMap.id K)) (n : ℕ) :
    Module.finrank ℚ (AugHomology K n) ≤
      Module.finrank ℚ (AugHomology L n) :=
  (augHomologyMap f n).finrank_le_finrank_of_injective
    (augHomologyMap_injective_of_left_homotopyInverse f g H n)

lemma augHomology_finrank_eq_of_homotopyEquiv
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (C : FiniteGeometricComplex E) (D : FiniteGeometricComplex F)
    (e : ContinuousMap.HomotopyEquiv C.K.space D.K.space) (n : ℕ) :
    Module.finrank ℚ (AugHomology (abstractComplex C) n) =
      Module.finrank ℚ (AugHomology (abstractComplex D) n) := by
  obtain ⟨Hleft⟩ := e.left_inv
  obtain ⟨Fmap, Gmap, ⟨Hchain⟩⟩ :=
    exists_augChainDomination_of_homotopy C D e.toFun e.invFun Hleft
  have hCD := augHomology_finrank_le_of_domination Fmap Gmap Hchain n
  obtain ⟨Hright⟩ := e.right_inv
  obtain ⟨Fmap', Gmap', ⟨Hchain'⟩⟩ :=
    exists_augChainDomination_of_homotopy D C e.invFun e.toFun Hright
  have hDC := augHomology_finrank_le_of_domination Fmap' Gmap' Hchain' n
  omega

noncomputable def augBoundaryEquivBoundariesInCycles
    (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    augBoundaries K n ≃ₗ[ℚ] augBoundariesInCycles K n where
  toFun := fun x => ⟨⟨x.1, augBoundaries_le_cycles K n x.2⟩, x.2⟩
  invFun := fun x => ⟨x.1.1, x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def augBoundaryRank (K : PreAbstractSimplicialComplex V) (n : ℕ) : ℕ :=
  Module.finrank ℚ (augBoundaries K n)

omit [Fintype V] in
lemma finrank_augBoundariesInCycles
    (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Module.finrank ℚ (augBoundariesInCycles K n) = augBoundaryRank K n := by
  rw [augBoundaryRank]
  exact (augBoundaryEquivBoundariesInCycles K n).finrank_eq.symm

omit [Fintype V] in
lemma finrank_augCycles_zero (K : PreAbstractSimplicialComplex V) :
    Module.finrank ℚ (augCycles K 0) = Module.finrank ℚ (Chain K 0) := by
  exact finrank_top ℚ (Chain K 0)

lemma finrank_augCycles_succ (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Module.finrank ℚ (Chain K (n + 1)) =
      Module.finrank ℚ (augCycles K (n + 1)) + augBoundaryRank K n := by
  have h := (boundary K n).finrank_range_add_finrank_ker
  change Module.finrank ℚ (Chain K (n + 1)) =
    Module.finrank ℚ (LinearMap.ker (boundary K n)) +
      Module.finrank ℚ (LinearMap.range (boundary K n))
  omega

lemma finrank_augCycles_eq_homology_add_boundary
    (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Module.finrank ℚ (augCycles K n) =
      Module.finrank ℚ (AugHomology K n) + augBoundaryRank K n := by
  have h := (augBoundariesInCycles K n).finrank_quotient_add_finrank
  rw [finrank_augBoundariesInCycles] at h
  exact h.symm

lemma finrank_augChain_zero (K : PreAbstractSimplicialComplex V) :
    Module.finrank ℚ (Chain K 0) =
      Module.finrank ℚ (AugHomology K 0) + augBoundaryRank K 0 := by
  rw [← finrank_augCycles_zero K,
    finrank_augCycles_eq_homology_add_boundary]

lemma finrank_augChain_succ (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Module.finrank ℚ (Chain K (n + 1)) =
      Module.finrank ℚ (AugHomology K (n + 1)) +
        augBoundaryRank K (n + 1) + augBoundaryRank K n := by
  rw [finrank_augCycles_succ, finrank_augCycles_eq_homology_add_boundary]

lemma augBoundaryRank_top (K : PreAbstractSimplicialComplex V) :
    augBoundaryRank K (Fintype.card V) = 0 := by
  have hboundary : boundary K (Fintype.card V) = 0 := by
    apply LinearMap.ext
    intro x
    rw [chain_above_card_eq_zero K x]
    simp
  rw [augBoundaryRank, augBoundaries, hboundary, LinearMap.range_zero,
    finrank_bot]

lemma sum_augBoundaryRanks_eq_zero (K : PreAbstractSimplicialComplex V) :
    (∑ n ∈ Finset.range (Fintype.card V), (-1 : ℚ) ^ (n + 1) *
      (augBoundaryRank K (n + 1) + augBoundaryRank K n)) +
        augBoundaryRank K 0 = 0 := by
  have htop :
      (∑ n ∈ Finset.range (Fintype.card V + 1),
        (-1 : ℚ) ^ n * augBoundaryRank K n) =
      ∑ n ∈ Finset.range (Fintype.card V),
        (-1 : ℚ) ^ n * augBoundaryRank K n := by
    rw [Finset.sum_range_succ, augBoundaryRank_top K]
    simp
  calc
    (∑ n ∈ Finset.range (Fintype.card V), (-1 : ℚ) ^ (n + 1) *
        (augBoundaryRank K (n + 1) + augBoundaryRank K n)) +
        augBoundaryRank K 0 =
      ((∑ n ∈ Finset.range (Fintype.card V), (-1 : ℚ) ^ (n + 1) *
        augBoundaryRank K (n + 1)) + augBoundaryRank K 0) +
      ∑ n ∈ Finset.range (Fintype.card V), (-1 : ℚ) ^ (n + 1) *
        augBoundaryRank K n := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      ring
    _ = (∑ n ∈ Finset.range (Fintype.card V + 1),
        (-1 : ℚ) ^ n * augBoundaryRank K n) +
      ∑ n ∈ Finset.range (Fintype.card V), (-1 : ℚ) ^ (n + 1) *
        augBoundaryRank K n := by
      rw [Finset.sum_range_succ']
      norm_num
    _ = (∑ n ∈ Finset.range (Fintype.card V + 1),
        (-1 : ℚ) ^ n * augBoundaryRank K n) +
      ∑ n ∈ Finset.range (Fintype.card V),
        -((-1 : ℚ) ^ n * augBoundaryRank K n) := by
      apply congrArg (fun z : ℚ =>
        (∑ n ∈ Finset.range (Fintype.card V + 1),
          (-1 : ℚ) ^ n * augBoundaryRank K n) + z)
      apply Finset.sum_congr rfl
      intro n _
      rw [pow_succ]
      ring
    _ = 0 := by
      rw [Finset.sum_neg_distrib, htop]
      ring

def homologyEulerQ (K : PreAbstractSimplicialComplex V) : ℚ :=
  ∑ n ∈ Finset.range (Fintype.card V + 1),
    (-1 : ℚ) ^ n * Module.finrank ℚ (AugHomology K n)

lemma chainEulerQ_eq_homologyEulerQ (K : PreAbstractSimplicialComplex V) :
    chainEulerQ K = homologyEulerQ K := by
  rw [chainEulerQ, homologyEulerQ]
  have hchain : ∀ n,
      (Fintype.card (AugFace K n) : ℚ) =
        Module.finrank ℚ (Chain K n) := by
    intro n
    rw [Module.finrank_finsupp_self]
  have hsum :
      (∑ n ∈ Finset.range (Fintype.card V + 1),
        (-1 : ℚ) ^ n * (Fintype.card (AugFace K n) : ℚ)) =
      ∑ n ∈ Finset.range (Fintype.card V + 1),
        (-1 : ℚ) ^ n * Module.finrank ℚ (Chain K n) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [hchain n]
  rw [hsum]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  rw [finrank_augChain_zero K]
  push_cast
  norm_num
  rw [← sub_eq_zero]
  calc
    _ =
      (∑ n ∈ Finset.range (Fintype.card V), (-1 : ℚ) ^ (n + 1) *
        (augBoundaryRank K (n + 1) + augBoundaryRank K n)) +
          augBoundaryRank K 0 := by
      have hsumSucc :
          (∑ n ∈ Finset.range (Fintype.card V), (-1 : ℚ) ^ (n + 1) *
            (Fintype.card (AugFace K (n + 1)) : ℚ)) =
          ∑ n ∈ Finset.range (Fintype.card V), (-1 : ℚ) ^ (n + 1) *
            Module.finrank ℚ (Chain K (n + 1)) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Module.finrank_finsupp_self]
      rw [hsumSucc]
      simp_rw [finrank_augChain_succ K]
      push_cast
      simp_rw [mul_add, Finset.sum_add_distrib]
      ring
    _ = 0 := sum_augBoundaryRanks_eq_zero K

omit [LinearOrder V] in
lemma chain_eq_zero_of_card_lt (K : PreAbstractSimplicialComplex V)
    {n : ℕ} (hn : Fintype.card V < n) (x : Chain K n) : x = 0 := by
  ext s
  exact (no_augFace_of_card_lt K hn s).elim

lemma augHomology_finrank_zero_of_card_lt
    (K : PreAbstractSimplicialComplex V) {n : ℕ} (hn : Fintype.card V < n) :
    Module.finrank ℚ (AugHomology K n) = 0 := by
  letI : Subsingleton (Chain K n) :=
    ⟨fun x y => (chain_eq_zero_of_card_lt K hn x).trans
      (chain_eq_zero_of_card_lt K hn y).symm⟩
  letI : Subsingleton (augCycles K n) := inferInstance
  letI : Subsingleton (AugHomology K n) := inferInstance
  exact Module.finrank_zero_of_subsingleton

lemma homologyEulerQ_eq_sum_of_card_le
    (K : PreAbstractSimplicialComplex V) {N : ℕ} (hN : Fintype.card V ≤ N) :
    homologyEulerQ K =
      ∑ n ∈ Finset.range (N + 1),
        (-1 : ℚ) ^ n * Module.finrank ℚ (AugHomology K n) := by
  rw [homologyEulerQ]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hN))
  intro n hnN hnV
  have hlt : Fintype.card V < n := by
    rw [Finset.mem_range] at hnN
    simp only [Finset.mem_range, not_lt] at hnV
    omega
  rw [augHomology_finrank_zero_of_card_lt K hlt, Nat.cast_zero, mul_zero]

lemma chainEulerQ_eq_of_topologicalHomotopyEquiv
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (C : FiniteGeometricComplex E) (D : FiniteGeometricComplex F)
    (e : ContinuousMap.HomotopyEquiv C.K.space D.K.space) :
    chainEulerQ (abstractComplex C) = chainEulerQ (abstractComplex D) := by
  rw [chainEulerQ_eq_homologyEulerQ, chainEulerQ_eq_homologyEulerQ]
  let N := max (Fintype.card (GeometricVertex C))
    (Fintype.card (GeometricVertex D))
  rw [homologyEulerQ_eq_sum_of_card_le (abstractComplex C)
      (Nat.le_max_left _ _),
    homologyEulerQ_eq_sum_of_card_le (abstractComplex D)
      (Nat.le_max_right _ _)]
  apply Finset.sum_congr rfl
  intro n _
  rw [augHomology_finrank_eq_of_homotopyEquiv C D e n]

def AugmentedAbstractFace (K : PreAbstractSimplicialComplex V) :=
  {s : Finset V // s = ∅ ∨ s ∈ K.faces}

noncomputable instance (K : PreAbstractSimplicialComplex V) :
    Fintype (AugmentedAbstractFace K) := by
  exact Fintype.subtype
    (Finset.univ.filter fun s : Finset V => s = ∅ ∨ s ∈ K.faces)
    (by simp)

abbrev AllAugFace (K : PreAbstractSimplicialComplex V) :=
  Σ n : Fin (Fintype.card V + 1), AugFace K n

def allAugFaceToAugmentedAbstractFace
    (K : PreAbstractSimplicialComplex V) :
    AllAugFace K → AugmentedAbstractFace K :=
  fun a => ⟨a.2.1.1, by
    rcases a.2.2 with hn | hface
    · left
      apply Finset.card_eq_zero.mp
      rw [a.2.1.2]
      exact hn
    · exact Or.inr hface⟩

def augmentedAbstractFaceToAllAugFace
    (K : PreAbstractSimplicialComplex V) :
    AugmentedAbstractFace K → AllAugFace K :=
  fun s =>
    ⟨⟨s.1.card, Nat.lt_succ_of_le (Finset.card_le_univ s.1)⟩,
      ⟨⟨s.1, rfl⟩, by
        rcases s.2 with hempty | hface
        · exact Or.inl (by simp [hempty])
        · exact Or.inr hface⟩⟩

omit [LinearOrder V] in
lemma allAugFaceToAugmentedAbstractFace_injective
    (K : PreAbstractSimplicialComplex V) :
    Function.Injective (allAugFaceToAugmentedAbstractFace K) := by
  rintro ⟨n, s⟩ ⟨m, t⟩ h
  have hst : s.1.1 = t.1.1 := congrArg Subtype.val h
  have hnm : n = m := by
    apply Fin.ext
    rw [← s.1.2, ← t.1.2, hst]
  subst m
  have hst' : s = t := by
    apply Subtype.ext
    apply Subtype.ext
    exact hst
  rw [hst']

omit [LinearOrder V] in
lemma augmentedAbstractFaceToAllAugFace_rightInverse
    (K : PreAbstractSimplicialComplex V) :
    Function.RightInverse (augmentedAbstractFaceToAllAugFace K)
      (allAugFaceToAugmentedAbstractFace K) := by
    intro s
    apply Subtype.ext
    rfl

noncomputable def allAugFaceEquivAugmentedAbstractFace
    (K : PreAbstractSimplicialComplex V) :
    AllAugFace K ≃ AugmentedAbstractFace K :=
  Equiv.ofBijective (allAugFaceToAugmentedAbstractFace K)
    ⟨allAugFaceToAugmentedAbstractFace_injective K,
      (augmentedAbstractFaceToAllAugFace_rightInverse K).surjective⟩

lemma chainEulerQ_eq_augmentedAbstractFaceSum
    (K : PreAbstractSimplicialComplex V) :
    chainEulerQ K =
      ∑ s : AugmentedAbstractFace K, (-1 : ℚ) ^ s.1.card := by
  rw [chainEulerQ, ← Fin.sum_univ_eq_sum_range]
  calc
    (∑ n : Fin (Fintype.card V + 1),
      (-1 : ℚ) ^ (n : ℕ) * Fintype.card (AugFace K n)) =
        ∑ n : Fin (Fintype.card V + 1),
          ∑ _s : AugFace K n, (-1 : ℚ) ^ (n : ℕ) := by
      apply Fintype.sum_congr
      intro n
      simp [nsmul_eq_mul, mul_comm]
    _ = ∑ a : AllAugFace K, (-1 : ℚ) ^ (a.1 : ℕ) := by
      rw [Fintype.sum_sigma]
    _ = ∑ s : AugmentedAbstractFace K, (-1 : ℚ) ^ s.1.card := by
      exact Fintype.sum_equiv (allAugFaceEquivAugmentedAbstractFace K)
        (fun a : AllAugFace K => (-1 : ℚ) ^ (a.1 : ℕ))
        (fun s : AugmentedAbstractFace K => (-1 : ℚ) ^ s.1.card)
        (fun a => by
          rw [show (allAugFaceEquivAugmentedAbstractFace K a).1.card =
            (a.1 : ℕ) from a.2.1.2])

end FinitePolyhedron

end

end Submission.Helpers.DehnSommerville
