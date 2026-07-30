import Submission.BarExact
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

namespace Submission.RelationCocycle

open CategoryTheory
open Submission.GroupAlgebra Submission.GeneratorRank Submission.Presentation
  Submission.BarExact

noncomputable section

variable (k : Type) (G : Type) [Field k] [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G
local instance : DecidableEq G := Classical.decEq G
local instance : SMul G k := ⟨fun _ x ↦ x⟩

noncomputable abbrev trivialRep : Rep k G := Rep.trivial k G k

noncomputable abbrev PresentationLift {d : ℕ} (g : Fin d → G)
    (t : G → FreeRelations k G d) : Prop :=
  ∀ h, presentationMap k G g (t h) =
    ⟨MonoidAlgebra.single h 1 - 1, by
      change augmentation k G (MonoidAlgebra.single h 1 - 1) = 0
      simp [augmentation]⟩

/-- The `A`-linear map from the first bar module to a chosen presentation,
determined by lifts of all group differences. -/
noncomputable def barToPresentation {d : ℕ} (t : G → FreeRelations k G d) :
    BarOne k G →ₗ[GroupAlgebra k G] FreeRelations k G d where
  toFun b := ∑ h, b h • t h
  map_add' b c := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a b := by
    change (∑ h, (a * b h) • t h) = a • ∑ h, b h • t h
    simp only [mul_smul, Finset.smul_sum]

theorem barToPresentation_barBasis {d : ℕ}
    (t : G → FreeRelations k G d) (h : G) :
    barToPresentation k G t (barBasis k G h) = t h := by
  classical
  simp [barToPresentation, barBasis, Pi.single_apply]

theorem presentationMap_barToPresentation {d : ℕ} (g : Fin d → G)
    (t : G → FreeRelations k G d)
    (ht : PresentationLift k G g t)
    (b : BarOne k G) :
    (presentationMap k G g) (barToPresentation k G t b) =
      ⟨barBoundary k G b, by
        change augmentation k G
          (∑ h, b h * (MonoidAlgebra.single h 1 - 1)) = 0
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro h _
        rw [map_mul]
        simp [augmentation]⟩ := by
  apply Subtype.ext
  change (presentationMap k G g (∑ h, b h • t h)).1 =
    ∑ h, b h * (MonoidAlgebra.single h 1 - 1)
  rw [map_sum]
  rw [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [map_smul]
  change b h * (presentationMap k G g (t h)).1 =
    b h * (MonoidAlgebra.single h 1 - 1)
  rw [congrArg Subtype.val (ht h)]

/-- A bar relation, transported to the kernel of the chosen presentation. -/
noncomputable def relationVector {d : ℕ} (g : Fin d → G)
    (t : G → FreeRelations k G d)
    (ht : PresentationLift k G g t)
    (a b : G) : RelationKernel k G g :=
  ⟨barToPresentation k G t (barRelation k G a b), by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change (presentationMap k G g
      (barToPresentation k G t (barRelation k G a b))).1 = 0
    have hmap := congrArg Subtype.val
      (presentationMap_barToPresentation k G g t ht (barRelation k G a b))
    exact hmap.trans (barBoundary_barRelation k G a b)⟩

omit [Finite G] in
theorem barRelation_identity (a b c : G) :
    MonoidAlgebra.single a (1 : k) • barRelation k G b c +
        barRelation k G a (b * c) =
      barRelation k G (a * b) c + barRelation k G a b := by
  classical
  funext x
  simp [barRelation, barBasis]
  rw [mul_sub, ← mul_assoc, MonoidAlgebra.single_mul_single]
  simp only [one_mul, mul_assoc]
  abel

theorem relationVector_identity {d : ℕ} (g : Fin d → G)
    (t : G → FreeRelations k G d) (ht : PresentationLift k G g t)
    (a b c : G) :
    MonoidAlgebra.single a (1 : k) • relationVector k G g t ht b c +
        relationVector k G g t ht a (b * c) =
      relationVector k G g t ht (a * b) c + relationVector k G g t ht a b := by
  apply Subtype.ext
  change MonoidAlgebra.single a (1 : k) •
        barToPresentation k G t (barRelation k G b c) +
      barToPresentation k G t (barRelation k G a (b * c)) =
    barToPresentation k G t (barRelation k G (a * b) c) +
      barToPresentation k G t (barRelation k G a b)
  simpa only [relationVector, map_add, map_smul] using
    congrArg (barToPresentation k G t) (barRelation_identity k G a b c)

/-- The ordinary inhomogeneous cocycle associated to a functional on the
minimal relation space. -/
noncomputable def relationCocycle {d : ℕ} (g : Fin d → G)
    (t : G → FreeRelations k G d) (ht : PresentationLift k G g t)
    (ell : Module.Dual k (RelationSpace k G g)) : G × G → k :=
  fun ab ↦ relationFunctional k G g ell (relationVector k G g t ht ab.1 ab.2)

theorem relationCocycle_isCocycle {d : ℕ} (g : Fin d → G)
    (t : G → FreeRelations k G d) (ht : PresentationLift k G g t)
    (ell : Module.Dual k (RelationSpace k G g)) :
    groupCohomology.IsCocycle₂ (relationCocycle k G g t ht ell) := by
  intro a b c
  have hid := relationVector_identity k G g t ht a b c
  have hfun := congrArg (relationFunctional k G g ell) hid
  rw [map_add, map_add, relationFunctional_smul, augmentation,
    MonoidAlgebra.lift_single, MonoidHom.one_apply, one_smul, one_mul] at hfun
  change relationCocycle k G g t ht ell (a * b, c) +
      relationCocycle k G g t ht ell (a, b) =
    relationCocycle k G g t ht ell (b, c) +
      relationCocycle k G g t ht ell (a, b * c)
  simpa only [relationCocycle] using hfun.symm

noncomputable def relationCocyclesMap {d : ℕ} (g : Fin d → G)
    (t : G → FreeRelations k G d) (ht : PresentationLift k G g t) :
    Module.Dual k (RelationSpace k G g) →ₗ[k]
      groupCohomology.cocycles₂ (trivialRep k G) where
  toFun ell := ⟨relationCocycle k G g t ht ell, by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro a b c
    have hc := relationCocycle_isCocycle k G g t ht ell a b c
    change relationCocycle k G g t ht ell (a * b, c) +
        relationCocycle k G g t ht ell (a, b) =
      relationCocycle k G g t ht ell (b, c) +
        relationCocycle k G g t ht ell (a, b * c) at hc
    simpa only [Representation.trivial_apply] using hc⟩
  map_add' ell m := by
    apply groupCohomology.cocycles₂_ext
    intro a b
    rfl
  map_smul' c ell := by
    apply groupCohomology.cocycles₂_ext
    intro a b
    rfl

noncomputable def relationH2Map {d : ℕ} (g : Fin d → G)
    (t : G → FreeRelations k G d) (ht : PresentationLift k G g t) :
    Module.Dual k (RelationSpace k G g) →ₗ[k]
      groupCohomology.H2 (trivialRep k G) :=
  (groupCohomology.H2π (trivialRep k G)).hom.comp
    (relationCocyclesMap k G g t ht)

noncomputable def idealGroupDifference (h : G) : AugmentationIdeal k G :=
  ⟨MonoidAlgebra.single h 1 - 1, by
    change augmentation k G (MonoidAlgebra.single h 1 - 1) = 0
    simp [augmentation]⟩

omit [Finite G] in
theorem presentationMap_single_basis {d : ℕ} (g : Fin d → G) (i : Fin d) :
    presentationMap k G g (Pi.single i 1) = idealGroupDifference k G (g i) := by
  classical
  apply Subtype.ext
  simp [presentationMap, idealGroupDifference, Pi.single_apply]

noncomputable def arbitraryPresentationLift {d : ℕ} (g : Fin d → G)
    (hsurj : Function.Surjective (presentationMap k G g)) (h : G) :
    FreeRelations k G d :=
  Classical.choose (hsurj (idealGroupDifference k G h))

omit [Finite G] in
theorem arbitraryPresentationLift_spec {d : ℕ} (g : Fin d → G)
    (hsurj : Function.Surjective (presentationMap k G g)) (h : G) :
    presentationMap k G g (arbitraryPresentationLift k G g hsurj h) =
      idealGroupDifference k G h :=
  Classical.choose_spec (hsurj (idealGroupDifference k G h))

noncomputable def chosenPresentationLift {d : ℕ} (g : Fin d → G)
    (hsurj : Function.Surjective (presentationMap k G g)) :
    G → FreeRelations k G d :=
  Function.extend g (fun i ↦ Pi.single i 1)
    (arbitraryPresentationLift k G g hsurj)

omit [Finite G] in
theorem chosenPresentationLift_hits {d : ℕ} (g : Fin d → G)
    (hg : Function.Injective g)
    (hsurj : Function.Surjective (presentationMap k G g)) (i : Fin d) :
    chosenPresentationLift k G g hsurj (g i) = Pi.single i 1 := by
  exact hg.extend_apply _ _ i

omit [Finite G] in
theorem chosenPresentationLift_spec {d : ℕ} (g : Fin d → G)
    (hg : Function.Injective g)
    (hsurj : Function.Surjective (presentationMap k G g)) (h : G) :
    presentationMap k G g (chosenPresentationLift k G g hsurj h) =
      idealGroupDifference k G h := by
  classical
  by_cases hh : ∃ i, g i = h
  · obtain ⟨i, rfl⟩ := hh
    rw [chosenPresentationLift_hits k G g hg hsurj]
    exact presentationMap_single_basis k G g i
  · rw [chosenPresentationLift, Function.extend_apply' _ _ _ hh]
    exact arbitraryPresentationLift_spec k G g hsurj h

noncomputable def barFunctional (f : G → k) : BarOne k G →ₗ[k] k where
  toFun b := ∑ h, augmentation k G (b h) * f h
  map_add' b c := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a b := by
    simp only [Pi.smul_apply, map_smul, smul_eq_mul, mul_assoc, Finset.mul_sum,
      RingHom.id_apply]

theorem barFunctional_smul (f : G → k) (a : GroupAlgebra k G)
    (b : BarOne k G) :
    barFunctional k G f (a • b) = augmentation k G a * barFunctional k G f b := by
  simp [barFunctional, mul_assoc, Finset.mul_sum]

theorem barFunctional_barBasis (f : G → k) (g : G) :
    barFunctional k G f (barBasis k G g) = f g := by
  classical
  simp [barFunctional, barBasis, Pi.single_apply, augmentation]

theorem barFunctional_barRelation (f : G → k) (a b : G) :
    barFunctional k G f (barRelation k G a b) =
      f b - f (a * b) + f a := by
  rw [barRelation, map_add, map_sub, barFunctional_smul,
    barFunctional_barBasis, barFunctional_barBasis, barFunctional_barBasis,
    augmentation, MonoidAlgebra.lift_single, MonoidHom.one_apply, one_smul, one_mul]

noncomputable def cycleRelation {d : ℕ} (g : Fin d → G)
    (t : G → FreeRelations k G d) (ht : PresentationLift k G g t)
    (b : BarOne k G) (hb : barBoundary k G b = 0) :
    RelationKernel k G g :=
  ⟨barToPresentation k G t b, by
    rw [LinearMap.mem_ker, presentationMap_barToPresentation k G g t ht]
    apply Subtype.ext
    exact hb⟩

noncomputable def agreementSubmodule {d : ℕ} (g : Fin d → G)
    (t : G → FreeRelations k G d)
    (ht : PresentationLift k G g t)
    (ell : Module.Dual k (RelationSpace k G g)) (f : G → k) :
    Submodule (GroupAlgebra k G) (BarOne k G) where
  carrier := {b | ∃ hb : barBoundary k G b = 0,
    barFunctional k G f b =
      relationFunctional k G g ell (cycleRelation k G g t ht b hb)}
  zero_mem' := by
    let hb : barBoundary k G (0 : BarOne k G) = 0 := map_zero (barBoundary k G)
    refine ⟨hb, ?_⟩
    have hcycle : cycleRelation k G g t ht 0 hb = 0 := by
      apply Subtype.ext
      exact map_zero (barToPresentation k G t)
    rw [map_zero, hcycle, map_zero]
  add_mem' := by
    rintro b c ⟨hb, hbeq⟩ ⟨hc, hceq⟩
    have hbc : barBoundary k G (b + c) = 0 := by
      rw [map_add, hb, hc, add_zero]
    refine ⟨hbc, ?_⟩
    have hcycle : cycleRelation k G g t ht (b + c) hbc =
        cycleRelation k G g t ht b hb + cycleRelation k G g t ht c hc := by
      apply Subtype.ext
      exact map_add (barToPresentation k G t) b c
    rw [map_add, hcycle, map_add, hbeq, hceq]
  smul_mem' := by
    rintro a b ⟨hb, hbeq⟩
    have hab : barBoundary k G (a • b) = 0 := by
      rw [map_smul, hb, smul_zero]
    refine ⟨hab, ?_⟩
    have hcycle : cycleRelation k G g t ht (a • b) hab =
        a • cycleRelation k G g t ht b hb := by
      apply Subtype.ext
      exact map_smul (barToPresentation k G t) a b
    rw [barFunctional_smul, hcycle, relationFunctional_smul, hbeq]

theorem barRelationSpan_le_agreement {d : ℕ} (g : Fin d → G)
    (t : G → FreeRelations k G d) (ht : PresentationLift k G g t)
    (ell : Module.Dual k (RelationSpace k G g)) (f : G → k)
    (hf : ∀ a b : G, f b - f (a * b) + f a =
      relationCocycle k G g t ht ell (a, b)) :
    barRelationSpan k G ≤ agreementSubmodule k G g t ht ell f := by
  rw [barRelationSpan, Submodule.span_le]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  refine ⟨barBoundary_barRelation k G a b, ?_⟩
  rw [barFunctional_barRelation, hf]
  rfl

omit [Finite G] in
theorem sum_smul_presentationBasis {d : ℕ} (x : FreeRelations k G d) :
    (∑ i, x i • Pi.single i (1 : GroupAlgebra k G)) = x := by
  classical
  funext i
  simp [Pi.single_apply]

theorem relationH2Map_injective {d : ℕ} (g : Fin d → G)
    (hlin : LinearIndependent k (fun i ↦ groupToCotangent k G (g i)))
    (t : G → FreeRelations k G d)
    (ht : PresentationLift k G g t)
    (hhit : ∀ i, t (g i) = Pi.single i 1) :
    Function.Injective (relationH2Map k G g t ht) := by
  rw [← LinearMap.ker_eq_bot]
  ext ell
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hell
    have hz : groupCohomology.H2π (trivialRep k G)
        (relationCocyclesMap k G g t ht ell) = 0 := hell
    have hcob := (groupCohomology.H2π_eq_zero_iff
      (relationCocyclesMap k G g t ht ell)).mp hz
    obtain ⟨f, hf⟩ := hcob
    have hf' : ∀ a b : G, f b - f (a * b) + f a =
        relationCocycle k G g t ht ell (a, b) := by
      intro a b
      have hab := congrFun hf (a, b)
      calc
        f b - f (a * b) + f a =
            (relationCocyclesMap k G g t ht ell) (a, b) := by
          simpa only [groupCohomology.d₁₂_hom_apply,
            Representation.trivial_apply] using hab
        _ = relationCocycle k G g t ht ell (a, b) := rfl
    have hagree := barRelationSpan_le_agreement k G g t ht ell f hf'
    have hell_zero : ell = 0 := by
      apply LinearMap.ext (R := k)
      rintro q
      change ell q = 0
      refine Quotient.inductionOn q ?_
      intro x
      let b : BarOne k G := ∑ i, x.1 i • barBasis k G (g i)
      have hTb : barToPresentation k G t b = x.1 := by
        dsimp only [b]
        calc
          barToPresentation k G t
              (∑ i, x.1 i • barBasis k G (g i)) =
              ∑ i, barToPresentation k G t
                (x.1 i • barBasis k G (g i)) :=
            map_sum (barToPresentation k G t) _ _
          _ = ∑ i, x.1 i • t (g i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [map_smul, barToPresentation_barBasis]
          _ = ∑ i, x.1 i • Pi.single i 1 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hhit]
          _ = x.1 := sum_smul_presentationBasis k G x.1
      have hbzero : barBoundary k G b = 0 := by
        have hp := presentationMap_barToPresentation k G g t ht b
        rw [hTb, LinearMap.mem_ker.mp x.2] at hp
        exact (congrArg Subtype.val hp).symm
      have hbspan : b ∈ barRelationSpan k G :=
        mem_barRelationSpan_of_barBoundary_eq_zero k G b hbzero
      obtain ⟨hbzero', ha⟩ := hagree hbspan
      have hcycle : cycleRelation k G g t ht b hbzero' = x := by
        apply Subtype.ext
        exact hTb
      rw [hcycle] at ha
      have hphi : barFunctional k G f b = 0 := by
        dsimp only [b]
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro i _
        have hi :=
          relationKernel_coordinate_mem_augmentationIdeal k G g hlin x i
        change augmentation k G (x.1 i) = 0 at hi
        rw [barFunctional_smul, hi, zero_mul]
      have hrel : relationFunctional k G g ell x = 0 := ha ▸ hphi
      change relationFunctional k G g ell x = 0
      exact hrel
    exact hell_zero
  · rintro rfl
    exact map_zero (relationH2Map k G g t ht)

theorem relationSpace_finrank_le_groupH2 {d : ℕ} (g : Fin d → G)
    (hlin : LinearIndependent k (fun i ↦ groupToCotangent k G (g i)))
    (hspan : Submodule.span k
      (Set.range fun i ↦ groupToCotangent k G (g i)) = ⊤)
    (hnil : IsNilpotent (augmentationIdeal k G)) :
    Module.finrank k (RelationSpace k G g) ≤
      Module.finrank k (groupCohomology.H2 (trivialRep k G)) := by
  classical
  letI := Fintype.ofFinite G
  have hg : Function.Injective g := by
    intro i j hij
    exact hlin.injective (by rw [hij])
  have hspan' : Submodule.span k
      (groupToCotangent k G '' Set.range g) = ⊤ := by
    rw [show groupToCotangent k G '' Set.range g =
        Set.range (fun i ↦ groupToCotangent k G (g i)) by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨g i, ⟨i, rfl⟩, rfl⟩]
    exact hspan
  have hsurj : Function.Surjective (presentationMap k G g) :=
    presentationMap_surjective_of_cotangent_span k G g hspan' hnil
  let t := chosenPresentationLift k G g hsurj
  have ht : ∀ h, presentationMap k G g (t h) =
      ⟨MonoidAlgebra.single h 1 - 1, by
        change augmentation k G (MonoidAlgebra.single h 1 - 1) = 0
        simp [augmentation]⟩ := by
    intro h
    exact chosenPresentationLift_spec k G g hg hsurj h
  have hhit : ∀ i, t (g i) = Pi.single i 1 := by
    intro i
    exact chosenPresentationLift_hits k G g hg hsurj i
  have hinj := relationH2Map_injective k G g hlin t ht hhit
  letI : FiniteDimensional k (groupCohomology.H2 (trivialRep k G)) :=
    FiniteDimensional.of_surjective
      (groupCohomology.H2π (trivialRep k G)).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  rw [← Subspace.dual_finrank_eq (K := k) (V := RelationSpace k G g)]
  exact LinearMap.finrank_le_finrank_of_injective hinj

end

end Submission.RelationCocycle
