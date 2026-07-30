import Submission.RelationCocycle

namespace Submission.FilteredPresentation

open Submission.GroupAlgebra Submission.Hilbert Submission.GeneratorRank
  Submission.Presentation

variable (k : Type*) (G : Type) [Field k] [Group G] [Finite G]

/-- Vectors all of whose coordinates lie in `Jⁿ`. -/
noncomputable def freePower (d n : ℕ) :
    Submodule k (FreeRelations k G d) where
  carrier := {v | ∀ i, v i ∈ augmentationIdeal k G ^ n}
  zero_mem' := fun _ ↦ Submodule.zero_mem _
  add_mem' := fun hv hw i ↦ Submodule.add_mem _ (hv i) (hw i)
  smul_mem' := fun c v hv i ↦ by
    rw [Pi.smul_apply]
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hv i)

omit [Finite G] in
theorem freePower_antitone (d : ℕ) : Antitone (freePower k G d) := by
  intro m n hmn v hv i
  exact Ideal.pow_le_pow_right hmn (hv i)

/-- The induced augmentation filtration on the relation kernel. -/
noncomputable def kernelPower {d : ℕ} (g : Fin d → G) (n : ℕ) :
    Submodule k (RelationKernel k G g) where
  carrier := {x | ∀ i, x.1 i ∈ augmentationIdeal k G ^ n}
  zero_mem' := fun _ ↦ Submodule.zero_mem _
  add_mem' := fun hx hy i ↦ Submodule.add_mem _ (hx i) (hy i)
  smul_mem' := fun c x hx i ↦ by
    change c • x.1 i ∈ augmentationIdeal k G ^ n
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hx i)

omit [Finite G] in
theorem kernelPower_antitone {d : ℕ} (g : Fin d → G) :
    Antitone (kernelPower k G g) := by
  intro m n hmn x hx i
  exact Ideal.pow_le_pow_right hmn (hx i)

/-- The filtered range of the presentation map, retained as a left ideal. -/
noncomputable def filteredPresentationRange {d : ℕ} (g : Fin d → G) (n : ℕ) :
    Ideal (GroupAlgebra k G) where
  carrier := {a | ∃ v : FreeRelations k G d,
    (∀ i, v i ∈ augmentationIdeal k G ^ n) ∧
      (presentationMap k G g v).1 = a}
  zero_mem' := ⟨0, fun _ ↦ Submodule.zero_mem _,
    congrArg Subtype.val (map_zero (presentationMap k G g))⟩
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    refine ⟨v + w, fun i ↦ Submodule.add_mem _ (hv i) (hw i), ?_⟩
    exact congrArg Subtype.val (map_add (presentationMap k G g) v w)
  smul_mem' := by
    rintro a _ ⟨v, hv, rfl⟩
    refine ⟨a • v, fun i ↦ Ideal.mul_mem_left _ _ (hv i), ?_⟩
    exact congrArg Subtype.val (map_smul (presentationMap k G g) a v)

omit [Finite G] in
theorem filteredPresentationRange_le_power {d : ℕ} (g : Fin d → G) (n : ℕ) :
    filteredPresentationRange k G g n ≤ augmentationIdeal k G ^ (n + 1) := by
  rintro a ⟨v, hv, rfl⟩
  change (∑ i, v i * (MonoidAlgebra.single (g i) 1 - 1)) ∈
    augmentationIdeal k G ^ (n + 1)
  rw [show n + 1 = n + 1 by rfl, Submodule.pow_succ]
  apply Submodule.sum_mem
  intro i _
  apply Ideal.mul_mem_mul
  · exact hv i
  · change augmentation k G (MonoidAlgebra.single (g i) 1 - 1) = 0
    simp [augmentation]

omit [Finite G] in
theorem power_le_filteredPresentationRange_of_surjective {d : ℕ}
    (g : Fin d → G) (hsurj : Function.Surjective (presentationMap k G g)) (n : ℕ) :
    augmentationIdeal k G ^ (n + 1) ≤ filteredPresentationRange k G g n := by
  rw [Submodule.pow_succ]
  apply Ideal.mul_le.2
  intro a ha b hb
  obtain ⟨v, hv⟩ := hsurj ⟨b, by simpa only [Submodule.pow_one] using hb⟩
  refine ⟨a • v, ?_, ?_⟩
  · intro i
    change a * v i ∈ augmentationIdeal k G ^ n
    exact Ideal.IsTwoSided.mul_mem_of_left _ ha
  · change (presentationMap k G g (a • v)).1 = a * b
    rw [map_smul]
    change a * (presentationMap k G g v).1 = a * b
    rw [congrArg Subtype.val hv]

omit [Finite G] in
theorem filteredPresentationRange_eq_power_of_surjective {d : ℕ}
    (g : Fin d → G) (hsurj : Function.Surjective (presentationMap k G g)) (n : ℕ) :
    filteredPresentationRange k G g n = augmentationIdeal k G ^ (n + 1) :=
  le_antisymm (filteredPresentationRange_le_power k G g n)
    (power_le_filteredPresentationRange_of_surjective k G g hsurj n)

noncomputable def freePowerEquivPi (d n : ℕ) :
    freePower k G d n ≃ₗ[k] (Fin d → augmentationPower k G n) where
  toFun v i := ⟨v.1 i, v.2 i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨fun i ↦ (v i).1, fun i ↦ (v i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_freePower (d n : ℕ) :
    Module.finrank k (freePower k G d n) =
      d * Module.finrank k (augmentationPower k G n) := by
  rw [LinearEquiv.finrank_eq (freePowerEquivPi k G d n)]
  simp [Module.finrank_pi_fintype]

noncomputable def filteredPresentationMap {d : ℕ} (g : Fin d → G) (n : ℕ) :
    freePower k G d n →ₗ[k] augmentationPower k G (n + 1) where
  toFun v := ⟨(presentationMap k G g v.1).1,
    filteredPresentationRange_le_power k G g n
      ⟨v.1, v.2, rfl⟩⟩
  map_add' v w := by
    apply Subtype.ext
    change (presentationMap k G g (v.1 + w.1)).1 =
      (presentationMap k G g v.1).1 + (presentationMap k G g w.1).1
    exact congrArg Subtype.val (map_add (presentationMap k G g) v.1 w.1)
  map_smul' c v := by
    apply Subtype.ext
    change (presentationMap k G g (c • v.1)).1 =
      c • (presentationMap k G g v.1).1
    rw [Algebra.smul_def, Algebra.smul_def]
    exact congrArg Subtype.val (map_smul (presentationMap k G g)
      (algebraMap k (GroupAlgebra k G) c) v.1)

omit [Finite G] in
theorem filteredPresentationMap_surjective {d : ℕ} (g : Fin d → G)
    (hsurj : Function.Surjective (presentationMap k G g)) (n : ℕ) :
    Function.Surjective (filteredPresentationMap k G g n) := by
  intro y
  have hy : y.1 ∈ filteredPresentationRange k G g n := by
    rw [filteredPresentationRange_eq_power_of_surjective k G g hsurj n]
    exact y.2
  obtain ⟨v, hv, heq⟩ := hy
  refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
  exact heq

noncomputable def kernelPowerEquivFilteredKer {d : ℕ} (g : Fin d → G) (n : ℕ) :
    kernelPower k G g n ≃ₗ[k] LinearMap.ker (filteredPresentationMap k G g n) where
  toFun x := ⟨⟨x.1.1, x.2⟩, by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change (presentationMap k G g x.1.1).1 = 0
    have hxmap : presentationMap k G g x.1.1 = 0 := x.1.2
    exact congrArg Subtype.val hxmap⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨⟨x.1.1, by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change (presentationMap k G g x.1.1).1 = 0
    have hxmap : filteredPresentationMap k G g n x.1 = 0 := x.2
    exact congrArg Subtype.val hxmap⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_freePower_eq_kernel_add_power {d : ℕ} (g : Fin d → G)
    (hsurj : Function.Surjective (presentationMap k G g)) (n : ℕ) :
    Module.finrank k (freePower k G d n) =
      Module.finrank k (kernelPower k G g n) +
        Module.finrank k (augmentationPower k G (n + 1)) := by
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (filteredPresentationMap k G g n)
  rw [LinearMap.range_eq_top.mpr
    (filteredPresentationMap_surjective k G g hsurj n), finrank_top,
    ← LinearEquiv.finrank_eq (kernelPowerEquivFilteredKer k G g n)] at hrank
  omega

/-- The `k`-subspace generated by the action of an ideal on the relation
module. -/
noncomputable def idealAction {d : ℕ} (g : Fin d → G)
    (I : Ideal (GroupAlgebra k G)) : Submodule k (RelationKernel k G g) :=
  Submodule.span k {z | ∃ (a : GroupAlgebra k G), a ∈ I ∧
    ∃ x : RelationKernel k G g, z = a • x}

omit [Finite G] in
theorem idealAction_mono {d : ℕ} (g : Fin d → G)
    {I J : Ideal (GroupAlgebra k G)} (hIJ : I ≤ J) :
    idealAction k G g I ≤ idealAction k G g J := by
  rw [idealAction, idealAction, Submodule.span_le]
  rintro z ⟨a, ha, x, rfl⟩
  exact Submodule.subset_span ⟨a, hIJ ha, x, rfl⟩

omit [Finite G] in
theorem smul_idealAction_power_mem {d : ℕ} (g : Fin d → G)
    (n : ℕ) {a : GroupAlgebra k G} (ha : a ∈ augmentationIdeal k G ^ n)
    {x : RelationKernel k G g}
    (hx : x ∈ idealAction k G g (augmentationIdeal k G)) :
    a • x ∈ idealAction k G g (augmentationIdeal k G ^ (n + 1)) := by
  refine Submodule.span_induction (p := fun x _ ↦
    a • x ∈ idealAction k G g (augmentationIdeal k G ^ (n + 1)))
    ?_ ?_ ?_ ?_ hx
  · rintro z ⟨b, hb, y, rfl⟩
    rw [smul_smul]
    apply Submodule.subset_span
    refine ⟨a * b, ?_, y, rfl⟩
    rw [Submodule.pow_succ]
    exact Ideal.mul_mem_mul ha hb
  · simp
  · intro x y hx hy hax hay
    rw [smul_add]
    exact Submodule.add_mem _ hax hay
  · intro c x _ hx
    rw [smul_comm a c x]
    exact Submodule.smul_mem _ c hx

omit [Finite G] in
theorem idealAction_power_le_sup {d : ℕ} (g : Fin d → G)
    (N : Submodule (GroupAlgebra k G) (RelationKernel k G g))
    (hbase : (⊤ : Submodule k (RelationKernel k G g)) ≤
      N.restrictScalars k ⊔ idealAction k G g (augmentationIdeal k G))
    (n : ℕ) :
    idealAction k G g (augmentationIdeal k G ^ n) ≤
      N.restrictScalars k ⊔
        idealAction k G g (augmentationIdeal k G ^ (n + 1)) := by
  rw [idealAction, Submodule.span_le]
  rintro z ⟨a, ha, x, rfl⟩
  obtain ⟨y, hy, w, hw, hxy⟩ :=
    Submodule.mem_sup.mp (hbase (x := x) Submodule.mem_top)
  rw [← hxy, smul_add]
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left (N.smul_mem a hy)
  · exact Submodule.mem_sup_right (smul_idealAction_power_mem k G g n ha hw)

omit [Finite G] in
theorem top_le_of_top_le_sup_idealAction_of_nilpotent {d : ℕ}
    (g : Fin d → G)
    (N : Submodule (GroupAlgebra k G) (RelationKernel k G g))
    (hnil : IsNilpotent (augmentationIdeal k G))
    (hbase : (⊤ : Submodule k (RelationKernel k G g)) ≤
      N.restrictScalars k ⊔ idealAction k G g (augmentationIdeal k G)) :
    (⊤ : Submodule k (RelationKernel k G g)) ≤ N.restrictScalars k := by
  have hpow (n : ℕ) : (⊤ : Submodule k (RelationKernel k G g)) ≤
      N.restrictScalars k ⊔ idealAction k G g (augmentationIdeal k G ^ n) := by
    induction n with
    | zero =>
        intro x _
        apply Submodule.mem_sup_right
        apply Submodule.subset_span
        refine ⟨1, ?_, x, (one_smul _ _).symm⟩
        rw [Submodule.pow_zero]
        rw [Ideal.one_eq_top]
        exact Submodule.mem_top
    | succ n ih =>
        exact ih.trans (sup_le le_sup_left (idealAction_power_le_sup k G g N hbase n))
  obtain ⟨m, hm⟩ := hnil
  have haction : idealAction k G g (augmentationIdeal k G ^ m) = ⊥ := by
    rw [hm, idealAction]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨a, ha, x, rfl⟩
      change a = 0 at ha
      subst a
      simp
    · exact bot_le
  simpa only [haction, sup_bot_eq] using hpow m

theorem exists_relationGenerators {d : ℕ} (g : Fin d → G)
    (hnil : IsNilpotent (augmentationIdeal k G)) :
    ∃ y : Fin (Module.finrank k (RelationSpace k G g)) → RelationKernel k G g,
      Submodule.span k (Set.range fun i ↦
        (relationRadical k G g).mkQ (y i)) = ⊤ ∧
      Submodule.span (GroupAlgebra k G) (Set.range y) = ⊤ := by
  classical
  let inclusion : RelationKernel k G g →ₗ[k] FreeRelations k G d :=
    { toFun := fun x ↦ x.1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  letI : FiniteDimensional k (RelationKernel k G g) :=
    FiniteDimensional.of_injective inclusion (by
      intro x y hxy
      exact Subtype.ext hxy)
  letI : FiniteDimensional k (RelationSpace k G g) :=
    FiniteDimensional.of_surjective (relationRadical k G g).mkQ
      (relationRadical k G g).mkQ_surjective
  let q := (relationRadical k G g).mkQ
  let f : Fin (Module.finrank k (RelationSpace k G g)) →
      RelationSpace k G g := Module.finBasis k (RelationSpace k G g)
  have hfspan : Submodule.span k (Set.range f) = ⊤ := by
    simpa only [f] using
      (Module.finBasis k (RelationSpace k G g)).span_eq
  choose y hy using fun i ↦ (relationRadical k G g).mkQ_surjective (f i)
  have hfy : (fun i ↦ q (y i)) = f := by
    funext i
    exact hy i
  have hqspan : Submodule.span k (Set.range fun i ↦ q (y i)) = ⊤ := by
    rw [hfy, hfspan]
  let N : Submodule (GroupAlgebra k G) (RelationKernel k G g) :=
    Submodule.span (GroupAlgebra k G) (Set.range y)
  let Nk : Submodule k (RelationKernel k G g) := Submodule.span k (Set.range y)
  have hNkN : Nk ≤ N.restrictScalars k := by
    dsimp only [Nk]
    rw [Submodule.span_le]
    intro x hx
    exact Submodule.subset_span hx
  have hmap : Nk.map q = ⊤ := by
    dsimp only [Nk]
    rw [Submodule.map_span]
    rw [show q '' Set.range y = Set.range (fun i ↦ q (y i)) by
      ext z
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨y i, ⟨i, rfl⟩, rfl⟩]
    exact hqspan
  have hbase : (⊤ : Submodule k (RelationKernel k G g)) ≤
      N.restrictScalars k ⊔ idealAction k G g (augmentationIdeal k G) := by
    intro x _
    have hqx : q x ∈ Nk.map q := by
      rw [hmap]
      exact Submodule.mem_top
    obtain ⟨z, hz, hzx⟩ := hqx
    have hdiff : x - z ∈ relationRadical k G g := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change q x - q z = 0
      rw [hzx, sub_self]
    refine Submodule.mem_sup.mpr ⟨z, hNkN hz, x - z, ?_, by abel⟩
    exact hdiff
  have hNtop : (⊤ : Submodule k (RelationKernel k G g)) ≤ N.restrictScalars k :=
    top_le_of_top_le_sup_idealAction_of_nilpotent k G g N hnil hbase
  refine ⟨y, hqspan, ?_⟩
  apply top_unique
  intro x _
  exact hNtop Submodule.mem_top

noncomputable def relationMap {d r : ℕ} (g : Fin d → G)
    (y : Fin r → RelationKernel k G g) :
    FreeRelations k G r →ₗ[GroupAlgebra k G] RelationKernel k G g where
  toFun v := ∑ i, v i • y i
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    change (∑ i, (a * v i) • y i) = a • ∑ i, v i • y i
    simp only [mul_smul, Finset.smul_sum]

omit [Finite G] in
theorem relationMap_basis {d r : ℕ} (g : Fin d → G)
    (y : Fin r → RelationKernel k G g) (i : Fin r) :
    relationMap k G g y (Pi.single i 1) = y i := by
  classical
  simp [relationMap]

omit [Finite G] in
theorem relationMap_surjective_of_span_eq_top {d r : ℕ} (g : Fin d → G)
    (y : Fin r → RelationKernel k G g)
    (hy : Submodule.span (GroupAlgebra k G) (Set.range y) = ⊤) :
    Function.Surjective (relationMap k G g y) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← hy, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨Pi.single i 1, relationMap_basis k G g y i⟩

omit [Finite G] in
theorem relationGenerator_mem_kernelPower_one {d r : ℕ} (g : Fin d → G)
    (hlin : LinearIndependent k (fun i ↦ groupToCotangent k G (g i)))
    (y : Fin r → RelationKernel k G g) (j : Fin r) :
    y j ∈ kernelPower k G g 1 := by
  change ∀ i, (y j).1 i ∈ augmentationIdeal k G ^ 1
  intro i
  simpa only [Submodule.pow_one] using
    relationKernel_coordinate_mem_augmentationIdeal k G g hlin (y j) i

noncomputable def relationMapLinear {d r : ℕ} (g : Fin d → G)
    (y : Fin r → RelationKernel k G g) :
    FreeRelations k G r →ₗ[k] RelationKernel k G g :=
  (relationMap k G g y).restrictScalars k

noncomputable def relationImagePower {d r : ℕ} (g : Fin d → G)
    (y : Fin r → RelationKernel k G g) (n : ℕ) :
    Submodule k (RelationKernel k G g) :=
  (freePower k G r n).map (relationMapLinear k G g y)

omit [Finite G] in
theorem relationImagePower_antitone {d r : ℕ} (g : Fin d → G)
    (y : Fin r → RelationKernel k G g) :
    Antitone (relationImagePower k G g y) := by
  intro m n hmn
  exact Submodule.map_mono ((freePower_antitone k G r) hmn)

omit [Finite G] in
theorem relationImagePower_zero_eq_top {d r : ℕ} (g : Fin d → G)
    (y : Fin r → RelationKernel k G g)
    (hy : Function.Surjective (relationMap k G g y)) :
    relationImagePower k G g y 0 = ⊤ := by
  have hfree : freePower k G r 0 = ⊤ := by
    apply top_unique
    intro v _ i
    simp only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  have hy' : Function.Surjective (relationMapLinear k G g y) := hy
  rw [relationImagePower, hfree, Submodule.map_top,
    LinearMap.range_eq_top.mpr hy']

omit [Finite G] in
theorem relationImagePower_le_kernelPower_succ {d r : ℕ} (g : Fin d → G)
    (hlin : LinearIndependent k (fun i ↦ groupToCotangent k G (g i)))
    (y : Fin r → RelationKernel k G g) (n : ℕ) :
    relationImagePower k G g y n ≤ kernelPower k G g (n + 1) := by
  rintro z ⟨v, hv, rfl⟩
  change ∀ i, ((relationMapLinear k G g y) v).1 i ∈
    augmentationIdeal k G ^ (n + 1)
  intro i
  change ((∑ j, v j • y j : RelationKernel k G g)).1 i ∈
    augmentationIdeal k G ^ (n + 1)
  rw [Submodule.coe_sum, Finset.sum_apply]
  change (∑ j, v j * (y j).1 i) ∈ augmentationIdeal k G ^ (n + 1)
  rw [Submodule.pow_succ]
  apply Submodule.sum_mem
  intro j _
  exact Ideal.mul_mem_mul (hv j)
    (relationKernel_coordinate_mem_augmentationIdeal k G g hlin (y j) i)

end Submission.FilteredPresentation
