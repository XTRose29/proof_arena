import Submission.ClassTwoClosure

namespace Submission.Helpers

open scoped BigOperators Filter Topology commutatorElement

noncomputable section

def bfcCore (G : Type) [Group G] : Subgroup G :=
  Subgroup.centralizer (commutator G : Set G)

instance bfcCore_normal (G : Type) [Group G] : (bfcCore G).Normal := by
  dsimp [bfcCore]
  infer_instance

def FiniteCommProbWitness.centralCoreWitness (W : FiniteCommProbWitness) :
    FiniteCommProbWitness := by
  letI := W.group
  letI := W.finite
  exact ⟨bfcCore W.carrier, inferInstance, inferInstance⟩

lemma bfcCore_commutator_le_center (G : Type) [Group G] :
    let C := bfcCore G
    letI := C.toGroup
    commutator C ≤ Subgroup.center C := by
  let C := bfcCore G
  letI := C.toGroup
  change commutator C ≤ Subgroup.center C
  intro x hx
  have hxmap : (x.1 : G) ∈ Subgroup.map C.subtype (commutator C) :=
    ⟨x, hx, rfl⟩
  rw [Subgroup.map_subtype_commutator] at hxmap
  have hxcenter : (x.1 : G) ∈ Subgroup.center G :=
    commutator_centralizer_commutator_le_center G hxmap
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hxcenter y.1

lemma bfcCore_commutatorCard_le (W : FiniteCommProbWitness) :
    W.centralCoreWitness.commutatorCard ≤ W.commutatorCard := by
  letI := W.group
  letI := W.finite
  let C := bfcCore W.carrier
  let f : commutator C → commutator W.carrier := fun x =>
    ⟨x.1.1, by
      have hxmap : (x.1.1 : W.carrier) ∈
          Subgroup.map C.subtype (commutator C) := ⟨x.1, x.2, rfl⟩
      rw [Subgroup.map_subtype_commutator] at hxmap
      have hle : ⁅C, C⁆ ≤ commutator W.carrier := by
        simpa [commutator_def] using
          (Subgroup.commutator_mono (show C ≤ ⊤ from le_top)
            (show C ≤ ⊤ from le_top))
      exact hle hxmap⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : commutator W.carrier => (z : W.carrier)) hxy
  exact Nat.card_le_card_of_injective f hf

def bfcCoreDerivedEmbedding (G : Type) [Group G] :
    let C := bfcCore G
    letI := C.toGroup
    commutator C →* G := by
  let C := bfcCore G
  letI := C.toGroup
  exact C.subtype.comp (commutator C).subtype

lemma bfcCoreDerivedEmbedding_injective (G : Type) [Group G] :
    let C := bfcCore G
    letI := C.toGroup
    Function.Injective (bfcCoreDerivedEmbedding G) := by
  let C := bfcCore G
  letI := C.toGroup
  change Function.Injective (bfcCoreDerivedEmbedding G)
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

def bfcCoreDerivedEquivRange (G : Type) [Group G] :
    let C := bfcCore G
    letI := C.toGroup
    commutator C ≃* (bfcCoreDerivedEmbedding G).range := by
  let C := bfcCore G
  letI := C.toGroup
  exact MonoidHom.ofInjective (bfcCoreDerivedEmbedding_injective G)

lemma bfcCoreDerivedEmbedding_range_le_center (G : Type) [Group G] :
    let C := bfcCore G
    letI := C.toGroup
    (bfcCoreDerivedEmbedding G).range ≤ Subgroup.center G := by
  let C := bfcCore G
  letI := C.toGroup
  change (bfcCoreDerivedEmbedding G).range ≤ Subgroup.center G
  rintro g ⟨x, rfl⟩
  have hxmap : (x.1.1 : G) ∈ Subgroup.map C.subtype (commutator C) :=
    ⟨x.1, x.2, rfl⟩
  rw [Subgroup.map_subtype_commutator] at hxmap
  exact commutator_centralizer_commutator_le_center G hxmap

def bfcCoreProfileKernelInGroup
    (G : Type) [Group G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (X : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      Subgroup (commutator C →* ℂˣ)) : Subgroup G := by
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  exact (unitCharacterAnnihilator (commutator C) X).map
    (bfcCoreDerivedEmbedding G)

lemma bfcCoreProfileKernelInGroup_le_center
    (G : Type) [Group G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (X : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      Subgroup (commutator C →* ℂˣ)) :
    bfcCoreProfileKernelInGroup G hcentral X ≤ Subgroup.center G := by
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  have hmap := Subgroup.map_mono
    (f := bfcCoreDerivedEmbedding G)
    (show unitCharacterAnnihilator (commutator C) X ≤ ⊤ from le_top)
  have htop : Subgroup.map (bfcCoreDerivedEmbedding G) ⊤ =
      (bfcCoreDerivedEmbedding G).range := by
    ext g
    simp
  exact hmap.trans (by
    rw [htop]
    exact bfcCoreDerivedEmbedding_range_le_center G)

theorem bfcCoreProfileKernelInGroupNormal
    (G : Type) [Group G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (X : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      Subgroup (commutator C →* ℂˣ)) :
    (bfcCoreProfileKernelInGroup G hcentral X).Normal := by
  let K := bfcCoreProfileKernelInGroup G hcentral X
  constructor
  intro x hx g
  have hxcenter := bfcCoreProfileKernelInGroup_le_center G hcentral X hx
  have hxg : x * g = g * x := (Subgroup.mem_center_iff.mp hxcenter g).symm
  have hconj : g * x * g⁻¹ = x := by
    calc
      g * x * g⁻¹ = x * g * g⁻¹ := by rw [hxg]
      _ = x := by simp
  rw [hconj]
  exact hx

noncomputable def bfcCoreCharacterValue
    (G : Type) [Group G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (chi : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      commutator C →* ℂˣ)
    (x y : G) : ℂ := by
  classical
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  exact if h : ⁅x, y⁆ ∈ (bfcCoreDerivedEmbedding G).range then
    (chi ((bfcCoreDerivedEquivRange G).symm ⟨⁅x, y⁆, h⟩) : ℂ)
  else 0

lemma expect_bfcCoreCharacterValue_eq_indicator
    (G : Type) [Group G] [Finite G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (X : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      Subgroup (commutator C →* ℂˣ))
    (x y : G) :
    let C := bfcCore G
    letI := C.toGroup
    letI := commutatorCommGroupOfLeCenter C hcentral
    letI := Fintype.ofFinite X
    (𝔼 chi : X, bfcCoreCharacterValue G hcentral chi.1 x y) =
      complexPropIndicator (⁅x, y⁆ ∈ bfcCoreProfileKernelInGroup G hcentral X) := by
  classical
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  letI := Fintype.ofFinite X
  change (𝔼 chi : X, bfcCoreCharacterValue G hcentral chi.1 x y) =
    complexPropIndicator (⁅x, y⁆ ∈ bfcCoreProfileKernelInGroup G hcentral X)
  by_cases hrange : ⁅x, y⁆ ∈ (bfcCoreDerivedEmbedding G).range
  · let d : commutator C :=
      (bfcCoreDerivedEquivRange G).symm ⟨⁅x, y⁆, hrange⟩
    have hdval : bfcCoreDerivedEmbedding G d = ⁅x, y⁆ := by
      change ((bfcCoreDerivedEquivRange G) d).1 = ⁅x, y⁆
      rw [MulEquiv.apply_symm_apply]
    have hmem : ⁅x, y⁆ ∈ bfcCoreProfileKernelInGroup G hcentral X ↔
        d ∈ unitCharacterAnnihilator (commutator C) X := by
      constructor
      · rintro ⟨e, he, heq⟩
        have hed : e = d := bfcCoreDerivedEmbedding_injective G
          (heq.trans hdval.symm)
        simpa [hed] using he
      · intro hd
        exact ⟨d, hd, hdval⟩
    simp only [bfcCoreCharacterValue, dif_pos hrange]
    change (𝔼 chi : X, ((chi.1 d : ℂˣ) : ℂ)) = _
    rw [expect_unitCharacterEvaluation_eq_indicator]
    congr 1
    exact propext hmem.symm
  · have hnot : ⁅x, y⁆ ∉ bfcCoreProfileKernelInGroup G hcentral X := by
      intro hmem
      rcases hmem with ⟨d, _hd, hdval⟩
      apply hrange
      exact ⟨d, hdval⟩
    simp [bfcCoreCharacterValue, hrange, hnot, complexPropIndicator]

lemma quotient_commute_iff_mem_bfcCoreProfileKernel
    (G : Type) [Group G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (X : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      Subgroup (commutator C →* ℂˣ))
    (x y : G) :
    let K := bfcCoreProfileKernelInGroup G hcentral X
    letI := bfcCoreProfileKernelInGroupNormal G hcentral X
    Commute ((x : G) : G ⧸ K) ((y : G) : G ⧸ K) ↔ ⁅x, y⁆ ∈ K := by
  let K := bfcCoreProfileKernelInGroup G hcentral X
  letI := bfcCoreProfileKernelInGroupNormal G hcentral X
  change (((x : G) : G ⧸ K) * (y : G)) =
      ((y : G) : G ⧸ K) * (x : G) ↔ _
  rw [← commutatorElement_eq_one_iff_mul_comm]
  change ((⁅x, y⁆ : G) : G ⧸ K) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]

lemma commProb_bfcCoreProfileQuotient_eq_expect
    (G : Type) [Group G] [Finite G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (X : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      Subgroup (commutator C →* ℂˣ)) :
    let C := bfcCore G
    letI := C.toGroup
    letI := commutatorCommGroupOfLeCenter C hcentral
    letI := Fintype.ofFinite G
    letI := Fintype.ofFinite X
    let K := bfcCoreProfileKernelInGroup G hcentral X
    letI := bfcCoreProfileKernelInGroupNormal G hcentral X
    ((commProb (G ⧸ K) : ℚ) : ℂ) =
      𝔼 chi : X, 𝔼 x : G, 𝔼 y : G,
        bfcCoreCharacterValue G hcentral chi.1 x y := by
  classical
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  letI := Fintype.ofFinite X
  let K := bfcCoreProfileKernelInGroup G hcentral X
  letI := bfcCoreProfileKernelInGroupNormal G hcentral X
  letI := Fintype.ofFinite G
  calc
    ((commProb (G ⧸ K) : ℚ) : ℂ) =
        𝔼 x : G, 𝔼 y : G,
          complexPropIndicator (Commute ((x : G) : G ⧸ K) ((y : G) : G ⧸ K)) := by
      rw [expect_quotient_commute_indicator_eq_liftPairRatio]
      exact_mod_cast commProb_quotient_eq_liftPairRatio G K
    _ = 𝔼 x : G, 𝔼 y : G, 𝔼 chi : X,
        bfcCoreCharacterValue G hcentral chi.1 x y := by
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      rw [expect_bfcCoreCharacterValue_eq_indicator]
      congr 1
      exact propext (quotient_commute_iff_mem_bfcCoreProfileKernel
        G hcentral X x y)
    _ = 𝔼 chi : X, 𝔼 x : G, 𝔼 y : G,
        bfcCoreCharacterValue G hcentral chi.1 x y :=
      @expect_rotate_three G G X _ _ _
        (fun x y chi => bfcCoreCharacterValue G hcentral chi.1 x y)

lemma norm_expect_ite_addMonoidHom_fiber_le_inv_index
    {A B : Type} [AddGroup A] [Fintype A] [AddGroup B] [DecidableEq B]
    (f : A →+ B) (b : B) (u : A → ℂ) (hu : ∀ a, ‖u a‖ ≤ 1) :
    ‖𝔼 a : A, if f a = b then u a else 0‖ ≤ 1 / (f.ker.index : ℝ) := by
  classical
  rw [Fintype.expect_eq_sum_div_card, norm_div]
  simp only [Complex.norm_natCast]
  have hsum : ‖∑ a : A, if f a = b then u a else 0‖ ≤
      ((Finset.univ.filter fun a : A => f a = b).card : ℝ) := by
    calc
      ‖∑ a : A, if f a = b then u a else 0‖ ≤
          ∑ a : A, ‖if f a = b then u a else 0‖ := norm_sum_le _ _
      _ ≤ ∑ a : A, if f a = b then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : f a = b
        · simpa [ha] using hu a
        · simp [ha]
      _ = ((Finset.univ.filter fun a : A => f a = b).card : ℝ) := by
        rw [Finset.sum_boole]
  have hfiber : (Finset.univ.filter fun a : A => f a = b).card ≤
      Nat.card f.ker := by
    by_cases hb : b ∈ Set.range f
    · have hzero : (0 : B) ∈ Set.range f := ⟨0, f.map_zero⟩
      have heq := AddMonoidHom.card_fiber_eq_of_mem_range f hb hzero
      rw [heq]
      exact le_of_eq (calc
          (Finset.univ.filter fun a : A => f a = 0).card =
              Fintype.card {a : A // f a = 0} :=
            (Fintype.subtype_card _ (by simp)).symm
          _ = Fintype.card f.ker := by
            apply Fintype.card_congr
            exact {
              toFun := fun a => ⟨a.1, a.2⟩
              invFun := fun a => ⟨a.1, a.2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          _ = Nat.card f.ker := Nat.card_eq_fintype_card.symm)
    · have hnone : ∀ a : A, f a ≠ b := by
        intro a ha
        exact hb ⟨a, ha⟩
      simp [hnone]
  have hfiberR : ((Finset.univ.filter fun a : A => f a = b).card : ℝ) ≤
      Nat.card f.ker := by
    exact_mod_cast hfiber
  have hcard : Nat.card f.ker * f.ker.index = Nat.card A :=
    f.ker.card_mul_index
  have hcardR : (Nat.card f.ker : ℝ) * f.ker.index = Fintype.card A := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast hcard
  have hA : (0 : ℝ) < Fintype.card A := by positivity
  have hindex : (0 : ℝ) < f.ker.index := by
    exact_mod_cast (show 0 < f.ker.index from Finite.card_pos)
  have hker : (Nat.card f.ker : ℝ) ≠ 0 := by
    exact_mod_cast (show Nat.card f.ker ≠ 0 from Nat.ne_of_gt Nat.card_pos)
  calc
    ‖∑ a : A, if f a = b then u a else 0‖ / Fintype.card A ≤
        (Nat.card f.ker : ℝ) / Fintype.card A :=
      (div_le_div_iff_of_pos_right hA).2 (hsum.trans hfiberR)
    _ = 1 / (f.ker.index : ℝ) := by
      rw [← hcardR]
      field_simp [hker, hindex.ne']

def commutatorUnitChar
    (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (chi : commutator G →* ℂˣ) (x : G) : G →* ℂˣ where
  toFun y := chi (derivedCommutator G x y)
  map_one' := by
    rw [show derivedCommutator G x 1 = 1 by ext; simp [derivedCommutator]]
    exact map_one chi
  map_mul' := by
    intro y z
    rw [derivedCommutator_mul_right G hcentral, map_mul]

def commutatorUnitCharMap
    (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (chi : commutator G →* ℂˣ) :
    Additive G →+ Additive (G →* ℂˣ) where
  toFun x := Additive.ofMul (commutatorUnitChar G hcentral chi x.toMul)
  map_zero' := by
    change commutatorUnitChar G hcentral chi 1 = 1
    apply MonoidHom.ext
    intro y
    change chi (derivedCommutator G 1 y) = 1
    rw [show derivedCommutator G 1 y = 1 by ext; simp [derivedCommutator]]
    exact map_one chi
  map_add' := by
    intro x y
    change commutatorUnitChar G hcentral chi (x.toMul * y.toMul) =
      commutatorUnitChar G hcentral chi x.toMul *
        commutatorUnitChar G hcentral chi y.toMul
    apply MonoidHom.ext
    intro z
    change chi (derivedCommutator G (x.toMul * y.toMul) z) =
      chi (derivedCommutator G x.toMul z) * chi (derivedCommutator G y.toMul z)
    rw [derivedCommutator_mul_left G hcentral, map_mul]

lemma unitCharToComplex_injective {G : Type} [Group G] :
    Function.Injective (unitCharToComplex : (G →* ℂˣ) → AddChar (Additive G) ℂ) := by
  intro psi chi h
  ext x
  have hx := DFunLike.congr_fun h (Additive.ofMul x)
  exact hx

lemma unitCharToComplex_eq_zero_iff {G : Type} [Group G]
    (chi : G →* ℂˣ) : unitCharToComplex chi = 0 ↔ chi = 1 := by
  constructor
  · intro h
    apply unitCharToComplex_injective
    have hone : unitCharToComplex (1 : G →* ℂˣ) = 0 := by
      ext x
      rfl
    exact h.trans hone.symm
  · rintro rfl
    ext x
    rfl

lemma commutatorUnitCharMap_ker_eq
    (G : Type) [Group G] [Finite G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (chi : commutator G →* ℂˣ) :
    (commutatorUnitCharMap G hcentral chi).ker =
      (commutatorCharMap G hcentral (unitCharToComplex chi)).ker := by
  ext x
  change commutatorUnitChar G hcentral chi x.toMul = 1 ↔
    commutatorAddChar G hcentral (unitCharToComplex chi) x.toMul = 0
  have hchar : unitCharToComplex (commutatorUnitChar G hcentral chi x.toMul) =
      commutatorAddChar G hcentral (unitCharToComplex chi) x.toMul := by
    ext y
    rfl
  rw [← hchar]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact (unitCharToComplex_eq_zero_iff _).mp h

lemma norm_expect_unitCharMap_fiber_le_inv_index
    (G : Type) [Group G] [Fintype G]
    (f : Additive G →+ Additive (G →* ℂˣ))
    (b : Additive (G →* ℂˣ)) (u : Additive G → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) :
    ‖𝔼 x : Additive G, if f x = b then u x else 0‖ ≤
      1 / (f.ker.index : ℝ) := by
  classical
  rw [Fintype.expect_eq_sum_div_card, norm_div]
  simp only [Complex.norm_natCast]
  have hsum : ‖∑ x : Additive G, if f x = b then u x else 0‖ ≤
      ((Finset.univ.filter fun x : Additive G => f x = b).card : ℝ) := by
    calc
      ‖∑ x : Additive G, if f x = b then u x else 0‖ ≤
          ∑ x : Additive G, ‖if f x = b then u x else 0‖ := norm_sum_le _ _
      _ ≤ ∑ x : Additive G, if f x = b then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : f x = b
        · simpa [hx] using hu x
        · simp [hx]
      _ = ((Finset.univ.filter fun x : Additive G => f x = b).card : ℝ) := by
        rw [Finset.sum_boole]
  have hfiber : (Finset.univ.filter fun x : Additive G => f x = b).card ≤
      Nat.card f.ker := by
    by_cases hb : b ∈ Set.range f
    · have hzero : (0 : Additive (G →* ℂˣ)) ∈ Set.range f := ⟨0, f.map_zero⟩
      have heq := AddMonoidHom.card_fiber_eq_of_mem_range f hb hzero
      rw [heq]
      exact le_of_eq (calc
          (Finset.univ.filter fun x : Additive G => f x = 0).card =
              Fintype.card {x : Additive G // f x = 0} :=
            (Fintype.subtype_card _ (by simp)).symm
          _ = Fintype.card f.ker := by
            apply Fintype.card_congr
            exact {
              toFun := fun x => ⟨x, x.2⟩
              invFun := fun x => ⟨x, x.2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          _ = Nat.card f.ker := Nat.card_eq_fintype_card.symm)
    · have hnone : ∀ x : Additive G, f x ≠ b := by
        intro x hx
        exact hb ⟨x, hx⟩
      simp [hnone]
  have hfiberR : ((Finset.univ.filter fun x : Additive G => f x = b).card : ℝ) ≤
      Nat.card f.ker := by
    exact_mod_cast hfiber
  have hcard : Nat.card f.ker * f.ker.index = Nat.card (Additive G) :=
    f.ker.card_mul_index
  have hcardR : (Nat.card f.ker : ℝ) * f.ker.index = Fintype.card (Additive G) := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast hcard
  have hG : (0 : ℝ) < Fintype.card (Additive G) := by positivity
  have hindex : (0 : ℝ) < f.ker.index := by
    exact_mod_cast (show 0 < f.ker.index from Finite.card_pos)
  have hker : (Nat.card f.ker : ℝ) ≠ 0 := by
    exact_mod_cast (show Nat.card f.ker ≠ 0 from Nat.ne_of_gt Nat.card_pos)
  calc
    ‖∑ x : Additive G, if f x = b then u x else 0‖ / Fintype.card (Additive G) ≤
        (Nat.card f.ker : ℝ) / Fintype.card (Additive G) :=
      (div_le_div_iff_of_pos_right hG).2 (hsum.trans hfiberR)
    _ = 1 / (f.ker.index : ℝ) := by
      rw [← hcardR]
      field_simp [hker, hindex.ne']

lemma norm_expect_twisted_unit_commutator_le_inv_index
    (G : Type) [Group G] [Fintype G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (chi : commutator G →* ℂˣ)
    (alpha beta : G →* ℂˣ) :
    ‖𝔼 x : Additive G, (alpha x.toMul : ℂ) *
      (𝔼 y : Additive G,
        (chi (derivedCommutator G x.toMul y.toMul) : ℂ) * (beta y.toMul : ℂ))‖ ≤
      1 / ((commutatorCharMap G hcentral (unitCharToComplex chi)).ker.index : ℝ) := by
  classical
  let f := commutatorUnitCharMap G hcentral chi
  let b : Additive (G →* ℂˣ) := Additive.ofMul beta⁻¹
  have hrewrite :
      (𝔼 x : Additive G, (alpha x.toMul : ℂ) *
        (𝔼 y : Additive G,
          (chi (derivedCommutator G x.toMul y.toMul) : ℂ) * (beta y.toMul : ℂ))) =
        𝔼 x : Additive G, if f x = b then (alpha x.toMul : ℂ) else 0 := by
    apply Finset.expect_congr rfl
    intro x _
    let gamma := commutatorUnitChar G hcentral chi x.toMul * beta
    have hinner :
        (𝔼 y : Additive G,
          (chi (derivedCommutator G x.toMul y.toMul) : ℂ) * (beta y.toMul : ℂ)) =
          if gamma = 1 then 1 else 0 := by
      change (𝔼 y : Additive G, unitCharToComplex gamma y) = _
      rw [AddChar.expect_eq_ite]
      rw [if_congr (unitCharToComplex_eq_zero_iff gamma) rfl rfl]
    have hcond : gamma = 1 ↔ f x = b := by
      change commutatorUnitChar G hcentral chi x.toMul * beta = 1 ↔
        commutatorUnitChar G hcentral chi x.toMul = beta⁻¹
      constructor
      · intro h
        apply MonoidHom.ext
        intro y
        have hy := DFunLike.congr_fun h y
        exact (mul_eq_one_iff_eq_inv).mp hy
      · intro h
        apply MonoidHom.ext
        intro y
        have hy := DFunLike.congr_fun h y
        exact (mul_eq_one_iff_eq_inv).mpr hy
    rw [hinner]
    by_cases hx : f x = b
    · rw [if_pos (hcond.mpr hx), if_pos hx, mul_one]
    · rw [if_neg (fun h => hx (hcond.mp h)), if_neg hx, mul_zero]
  rw [hrewrite]
  have hker : f.ker =
      (commutatorCharMap G hcentral (unitCharToComplex chi)).ker := by
    simpa [f] using commutatorUnitCharMap_ker_eq G hcentral chi
  rw [← hker]
  exact norm_expect_unitCharMap_fiber_le_inv_index G f b
    (fun x => (alpha x.toMul : ℂ))
    (fun x => by
      change ‖unitCharToComplex alpha x‖ ≤ 1
      exact ((unitCharToComplex alpha).norm_apply x).le)

def bfcCoreCommutatorIntersection (G : Type) [Group G] : Subgroup G :=
  commutator G ⊓ bfcCore G

@[reducible]
def bfcCoreCommutatorIntersectionCommGroup (G : Type) [Group G] :
    CommGroup (bfcCoreCommutatorIntersection G) :=
  CommGroup.mk fun x y => by
    apply Subtype.ext
    exact (x.2.2 y.1 y.2.1).symm

def bfcCoreDerivedEmbeddingToIntersection (G : Type) [Group G] :
    let C := bfcCore G
    letI := C.toGroup
    commutator C →* bfcCoreCommutatorIntersection G := by
  let C := bfcCore G
  letI := C.toGroup
  let f := bfcCoreDerivedEmbedding G
  refine {
    toFun := fun x => ⟨f x, ?_⟩
    map_one' := by ext; simp [f]
    map_mul' := by intro x y; ext; simp [f] }
  constructor
  · have hxmap : (x.1.1 : G) ∈ Subgroup.map C.subtype (commutator C) :=
      ⟨x.1, x.2, rfl⟩
    rw [Subgroup.map_subtype_commutator] at hxmap
    have hle : ⁅C, C⁆ ≤ commutator G := by
      simpa [commutator_def] using
        (Subgroup.commutator_mono (show C ≤ ⊤ from le_top)
          (show C ≤ ⊤ from le_top))
    exact hle hxmap
  · have hxmap : (x.1.1 : G) ∈ Subgroup.map C.subtype (commutator C) :=
      ⟨x.1, x.2, rfl⟩
    exact Subgroup.map_subtype_le (commutator C) hxmap

lemma bfcCoreDerivedEmbeddingToIntersection_injective (G : Type) [Group G] :
    let C := bfcCore G
    letI := C.toGroup
    Function.Injective (bfcCoreDerivedEmbeddingToIntersection G) := by
  let C := bfcCore G
  letI := C.toGroup
  change Function.Injective (bfcCoreDerivedEmbeddingToIntersection G)
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z : bfcCoreCommutatorIntersection G => (z : G)) hxy

def bfcCoreDerivedEquivIntersectionRange (G : Type) [Group G] :
    let C := bfcCore G
    letI := C.toGroup
    commutator C ≃* (bfcCoreDerivedEmbeddingToIntersection G).range := by
  let C := bfcCore G
  letI := C.toGroup
  exact MonoidHom.ofInjective (bfcCoreDerivedEmbeddingToIntersection_injective G)

def bfcCoreCharacterOnIntersectionRange
    (G : Type) [Group G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (chi : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      commutator C →* ℂˣ) :
    let C := bfcCore G
    letI := C.toGroup
    letI := commutatorCommGroupOfLeCenter C hcentral
    letI := bfcCoreCommutatorIntersectionCommGroup G
    (bfcCoreDerivedEmbeddingToIntersection G).range →* ℂˣ := by
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  letI := bfcCoreCommutatorIntersectionCommGroup G
  exact chi.comp (bfcCoreDerivedEquivIntersectionRange G).symm.toMonoidHom

noncomputable def extendedBfcCoreCharacter
    (G : Type) [Group G] [Finite G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (chi : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      commutator C →* ℂˣ) :
    letI := bfcCoreCommutatorIntersectionCommGroup G
    bfcCoreCommutatorIntersection G →* ℂˣ := by
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  letI := bfcCoreCommutatorIntersectionCommGroup G
  exact Classical.choose (MonoidHom.restrict_surjective
    (M := ℂ) (bfcCoreDerivedEmbeddingToIntersection G).range
    (bfcCoreCharacterOnIntersectionRange G hcentral chi))

lemma extendedBfcCoreCharacter_apply_embedding
    (G : Type) [Group G] [Finite G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (chi : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      commutator C →* ℂˣ)
    (d : let C := bfcCore G; letI := C.toGroup; commutator C) :
    letI := bfcCoreCommutatorIntersectionCommGroup G
    extendedBfcCoreCharacter G hcentral chi
        (bfcCoreDerivedEmbeddingToIntersection G d) = chi d := by
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  letI := bfcCoreCommutatorIntersectionCommGroup G
  have hspec := Classical.choose_spec (MonoidHom.restrict_surjective
    (M := ℂ) (bfcCoreDerivedEmbeddingToIntersection G).range
    (bfcCoreCharacterOnIntersectionRange G hcentral chi))
  have hd := DFunLike.congr_fun hspec
    ⟨bfcCoreDerivedEmbeddingToIntersection G d, ⟨d, rfl⟩⟩
  have heq : (bfcCoreDerivedEquivIntersectionRange G).symm
      ⟨bfcCoreDerivedEmbeddingToIntersection G d, ⟨d, rfl⟩⟩ = d := by
    apply (bfcCoreDerivedEquivIntersectionRange G).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  simpa [extendedBfcCoreCharacter, bfcCoreCharacterOnIntersectionRange, heq] using hd

def bfcCoreCharacterExtensionKernel (G : Type) [Group G] :
    letI := bfcCoreCommutatorIntersectionCommGroup G
    Subgroup (bfcCoreCommutatorIntersection G →* ℂˣ) := by
  letI := bfcCoreCommutatorIntersectionCommGroup G
  exact (MonoidHom.restrictHom
    (bfcCoreDerivedEmbeddingToIntersection G).range ℂˣ).ker

lemma mem_bfcCoreCharacterExtensionKernel_annihilator_iff
    (G : Type) [Group G] [Finite G]
    (z : bfcCoreCommutatorIntersection G) :
    letI := bfcCoreCommutatorIntersectionCommGroup G
    z ∈ unitCharacterAnnihilator (bfcCoreCommutatorIntersection G)
      (bfcCoreCharacterExtensionKernel G) ↔
      z ∈ (bfcCoreDerivedEmbeddingToIntersection G).range := by
  letI := bfcCoreCommutatorIntersectionCommGroup G
  let E := (bfcCoreDerivedEmbeddingToIntersection G).range
  let X := bfcCoreCharacterExtensionKernel G
  change (∀ eta : X, eta.1 z = 1) ↔ z ∈ E
  rw [← CommGroup.forall_monoidHom_apply_eq_one_iff ℂ E z]
  constructor
  · intro h phi hphi
    let eta : X := ⟨phi, by
      change (MonoidHom.restrictHom E ℂˣ) phi = 1
      apply MonoidHom.ext
      intro y
      change phi y.1 = 1
      exact hphi y.1 y.2⟩
    exact h eta
  · intro h eta
    apply h eta.1
    intro y hy
    have heta := eta.2
    change (MonoidHom.restrictHom E ℂˣ) eta.1 = 1 at heta
    have hyval := DFunLike.congr_fun heta ⟨y, hy⟩
    simpa using hyval

noncomputable def bfcCoreCharacterZeroExtension
    (G : Type) [Group G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (chi : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      commutator C →* ℂˣ)
    (z : bfcCoreCommutatorIntersection G) : ℂ := by
  classical
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  exact if hz : z ∈ (bfcCoreDerivedEmbeddingToIntersection G).range then
    (chi ((bfcCoreDerivedEquivIntersectionRange G).symm ⟨z, hz⟩) : ℂ)
  else 0

lemma expect_extendedBfcCoreCharacter_mul_extensionKernel
    (G : Type) [Group G] [Finite G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (chi : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      commutator C →* ℂˣ)
    (z : bfcCoreCommutatorIntersection G) :
    letI := bfcCoreCommutatorIntersectionCommGroup G
    let X := bfcCoreCharacterExtensionKernel G
    letI := Fintype.ofFinite X
    (𝔼 eta : X,
      (((extendedBfcCoreCharacter G hcentral chi * eta.1) z : ℂˣ) : ℂ)) =
      bfcCoreCharacterZeroExtension G hcentral chi z := by
  classical
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  letI := bfcCoreCommutatorIntersectionCommGroup G
  let X := bfcCoreCharacterExtensionKernel G
  letI := Fintype.ofFinite X
  let theta := extendedBfcCoreCharacter G hcentral chi
  have heval := expect_unitCharacterEvaluation_eq_indicator
    (bfcCoreCommutatorIntersection G) X z
  have hfactor : (𝔼 eta : X, (((theta * eta.1) z : ℂˣ) : ℂ)) =
      (theta z : ℂ) * (𝔼 eta : X, ((eta.1 z : ℂˣ) : ℂ)) := by
    rw [Finset.mul_expect]
    rfl
  change (𝔼 eta : X, (((theta * eta.1) z : ℂˣ) : ℂ)) =
    bfcCoreCharacterZeroExtension G hcentral chi z
  rw [hfactor, heval]
  by_cases hz : z ∈ (bfcCoreDerivedEmbeddingToIntersection G).range
  · let d := (bfcCoreDerivedEquivIntersectionRange G).symm ⟨z, hz⟩
    have hdval : bfcCoreDerivedEmbeddingToIntersection G d = z := by
      change ((bfcCoreDerivedEquivIntersectionRange G) d).1 = z
      rw [MulEquiv.apply_symm_apply]
    have htheta : theta z = chi d := by
      rw [← hdval]
      exact extendedBfcCoreCharacter_apply_embedding G hcentral chi d
    rw [mem_bfcCoreCharacterExtensionKernel_annihilator_iff G z]
    simp [bfcCoreCharacterZeroExtension, hz, htheta, d, complexPropIndicator]
  · rw [mem_bfcCoreCharacterExtensionKernel_annihilator_iff G z]
    simp [bfcCoreCharacterZeroExtension, hz, complexPropIndicator]

noncomputable def leftSubgroupPart {G : Type} [Group G]
    (K : Subgroup G) [K.Normal] (x : G) : K :=
  ⟨x * (Quotient.out (x : G ⧸ K))⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change (x : G ⧸ K) *
      ((Quotient.out (x : G ⧸ K) : G) : G ⧸ K)⁻¹ = 1
    rw [QuotientGroup.out_eq']
    simp⟩

lemma leftSubgroupPart_mul_out {G : Type} [Group G]
    (K : Subgroup G) [K.Normal] (x : G) :
    (leftSubgroupPart K x : G) * Quotient.out (x : G ⧸ K) = x := by
  simp [leftSubgroupPart]

lemma leftSubgroupPart_mul_out_eq {G : Type} [Group G]
    (K : Subgroup G) [K.Normal] (k : K) (q : G ⧸ K) :
    leftSubgroupPart K (k * Quotient.out q) = k := by
  have hquot : (((k : G) * Quotient.out q : G) : G ⧸ K) = q := by
    change ((k : G) : G ⧸ K) *
      ((Quotient.out q : G) : G ⧸ K) = q
    rw [(QuotientGroup.eq_one_iff _).2 k.2, QuotientGroup.out_eq']
    simp
  apply Subtype.ext
  simp [leftSubgroupPart, hquot]

lemma subgroup_mul_out_quotient {G : Type} [Group G]
    (K : Subgroup G) [K.Normal] (k : K) (q : G ⧸ K) :
    (((k : G) * Quotient.out q : G) : G ⧸ K) = q := by
  change ((k : G) : G ⧸ K) *
    ((Quotient.out q : G) : G ⧸ K) = q
  rw [(QuotientGroup.eq_one_iff _).2 k.2, QuotientGroup.out_eq']
  simp

noncomputable def groupEquivSubgroupProdQuotient
    (G : Type) [Group G] (K : Subgroup G) [K.Normal] :
    G ≃ K × (G ⧸ K) where
  toFun x := (leftSubgroupPart K x, (x : G ⧸ K))
  invFun p := p.1 * Quotient.out p.2
  left_inv x := leftSubgroupPart_mul_out K x
  right_inv p := by
    apply Prod.ext
    · exact leftSubgroupPart_mul_out_eq K p.1 p.2
    · exact subgroup_mul_out_quotient K p.1 p.2

def bfcCoreMixedCommutator
    (G : Type) [Group G] (a : G) (d : bfcCore G) :
    bfcCoreCommutatorIntersection G := by
  let C := bfcCore G
  refine ⟨⁅a, d.1⁆, ?_, ?_⟩
  · rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top d.1)
  · have hCnormal : C.Normal := by
      dsimp [C, bfcCore]
      infer_instance
    have hconj : a * d.1 * a⁻¹ ∈ C := hCnormal.conj_mem d.1 d.2 a
    have hinv : d.1⁻¹ ∈ C := C.inv_mem d.2
    simpa [commutatorElement_def, mul_assoc] using C.mul_mem hconj hinv

lemma bfcCoreMixedCommutator_mul_right
    (G : Type) [Group G] (a : G) (d e : bfcCore G) :
    bfcCoreMixedCommutator G a (d * e) =
      bfcCoreMixedCommutator G a d * bfcCoreMixedCommutator G a e := by
  apply Subtype.ext
  change ⁅a, d.1 * e.1⁆ = ⁅a, d.1⁆ * ⁅a, e.1⁆
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hcomm : d.1 * ⁅a, e.1⁆ = ⁅a, e.1⁆ * d.1 := by
    exact (d.2 (⁅a, e.1⁆) (bfcCoreMixedCommutator G a e).2.1).symm
  calc
    ⁅a, d.1⁆ * d.1 * ⁅a, e.1⁆ * d.1⁻¹ =
        ⁅a, d.1⁆ * (d.1 * ⁅a, e.1⁆) * d.1⁻¹ := by simp [mul_assoc]
    _ = ⁅a, d.1⁆ * (⁅a, e.1⁆ * d.1) * d.1⁻¹ := by rw [hcomm]
    _ = ⁅a, d.1⁆ * ⁅a, e.1⁆ := by simp [mul_assoc]

def bfcCoreTwistAddChar
    (G : Type) [Group G]
    (theta : letI := bfcCoreCommutatorIntersectionCommGroup G;
      bfcCoreCommutatorIntersection G →* ℂˣ)
    (a : G) : AddChar (Additive (bfcCore G)) ℂ where
  toFun d := (theta (bfcCoreMixedCommutator G a d.toMul) : ℂ)
  map_zero_eq_one' := by
    have hzero : bfcCoreMixedCommutator G a 1 = 1 := by
      apply Subtype.ext
      simp [bfcCoreMixedCommutator]
    simp [hzero]
  map_add_eq_mul' := by
    intro d e
    change (theta (bfcCoreMixedCommutator G a (d.toMul * e.toMul)) : ℂ) = _
    rw [bfcCoreMixedCommutator_mul_right]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) (map_mul theta _ _)

lemma mem_CommProbRange_of_probability_tendsto_centerIndex_bounded
    (W : ℕ → FiniteCommProbWitness) {p : ℝ}
    (hprob : Filter.Tendsto (fun n => (W n).probability)
      Filter.atTop (𝓝 p))
    (N : ℕ) (hindex : ∀ n, (W n).centerIndex ≤ N) :
    p ∈ CommProbRange := by
  let values : ℕ → ℝ := fun n => (W n).probability
  let candidates : Fin (N + 1) × Fin (N ^ 2 + 1) → ℝ := fun x =>
    (((x.2.1 : ℕ) : ℚ) / (((x.1.1 : ℕ) : ℚ) ^ 2) : ℚ)
  have hvalues_subset : Set.range values ⊆ Set.range candidates := by
    rintro _ ⟨n, rfl⟩
    let Wn := W n
    letI := Wn.group
    letI := Wn.finite
    have hb : (Subgroup.center Wn.carrier).index ≤ N := hindex n
    have ha : Nat.card (CenterCommutingQuotientPairs Wn.carrier) ≤
        (Subgroup.center Wn.carrier).index ^ 2 :=
      card_centerCommutingQuotientPairs_le Wn.carrier
    let b : Fin (N + 1) :=
      ⟨(Subgroup.center Wn.carrier).index, Nat.lt_succ_of_le hb⟩
    let a : Fin (N ^ 2 + 1) :=
      ⟨Nat.card (CenterCommutingQuotientPairs Wn.carrier),
        Nat.lt_succ_of_le (ha.trans (Nat.pow_le_pow_left hb 2))⟩
    refine ⟨(b, a), ?_⟩
    simp [values, candidates, Wn, b, a, FiniteCommProbWitness.probability,
      commProb_eq_centerQuotientRatio]
  have hvalues_finite : (Set.range values).Finite :=
    (Set.finite_range candidates).subset hvalues_subset
  have hp_values : p ∈ Set.range values :=
    hvalues_finite.isClosed.mem_of_tendsto hprob
      (Filter.Eventually.of_forall fun n => ⟨n, rfl⟩)
  rcases hp_values with ⟨n, hn⟩
  rw [← hn]
  exact ⟨(W n).carrier, (W n).group, rfl⟩

end

end Submission.Helpers
