import Mathlib.RepresentationTheory.FinGroupCharZero
import Submission.Helpers

namespace Submission.Helpers

open CategoryTheory
open scoped ComplexConjugate MonoidAlgebra

noncomputable section

section CharacterInner

variable {G : Type*} [Group G] [Fintype G]

def classFunctionInner (f h : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * conj (h g)

def classFunctionNormSq (f : G → ℂ) : ℝ :=
  (Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (f g)

omit [Group G] in
lemma classFunctionNormSq_nonneg (f : G → ℂ) : 0 ≤ classFunctionNormSq f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

lemma classFunctionNormSq_eq_zero_iff (f : G → ℂ) :
    classFunctionNormSq f = 0 ↔ f = 0 := by
  have hcard : (Nat.card G : ℝ)⁻¹ ≠ 0 := by
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  rw [classFunctionNormSq, mul_eq_zero, or_iff_right hcard]
  constructor
  · intro hsum
    funext g
    apply Complex.normSq_eq_zero.mp
    have hle : Complex.normSq (f g) ≤ ∑ x : G, Complex.normSq (f x) :=
      Finset.single_le_sum (fun x _ => Complex.normSq_nonneg (f x)) (Finset.mem_univ g)
    exact le_antisymm (by simpa [hsum] using hle) (Complex.normSq_nonneg _)
  · rintro rfl
    simp

omit [Group G] in
lemma classFunctionNormSq_add (f h : G → ℂ) :
    classFunctionNormSq (f + h) =
      classFunctionNormSq f + classFunctionNormSq h +
        2 * (classFunctionInner f h).re := by
  have hinner :
      (classFunctionInner f h).re =
        (Nat.card G : ℝ)⁻¹ * ∑ g : G, (f g * conj (h g)).re := by
    rw [classFunctionInner, Complex.mul_re]
    simp
  rw [classFunctionNormSq, classFunctionNormSq, classFunctionNormSq, hinner]
  simp_rw [Pi.add_apply, Complex.normSq_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

omit [Group G] in
lemma classFunctionNormSq_sub (f h : G → ℂ) :
    classFunctionNormSq (f - h) =
      classFunctionNormSq f + classFunctionNormSq h -
        2 * (classFunctionInner f h).re := by
  simpa [sub_eq_add_neg, classFunctionInner, classFunctionNormSq, Complex.normSq_neg]
    using classFunctionNormSq_add f (-h)

omit [Group G] in
lemma classFunctionInner_sub_left (f h k : G → ℂ) :
    classFunctionInner (f - h) k =
      classFunctionInner f k - classFunctionInner h k := by
  rw [classFunctionInner, classFunctionInner, classFunctionInner]
  simp_rw [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

lemma FDRep.char_inv_eq_conj (A : FDRep ℂ G) (g : G) :
    A.character g⁻¹ = conj (A.character g) := by
  exact Representation.char_inv_eq_conj A.ρ g

lemma classFunctionInner_character (A B : FDRep ℂ G) :
    classFunctionInner A.character B.character =
      Module.finrank ℂ (B ⟶ A) := by
  have h := FDRep.scalar_product_char_eq_finrank_equivariant B A
  rw [classFunctionInner, ← Fintype.card_eq_nat_card, ← invOf_eq_inv, ← smul_eq_mul]
  have hsum :
      ∑ g : G, A.character g * conj (B.character g) =
        ∑ g : G, A.character g * B.character g⁻¹ := by
    apply Finset.sum_congr rfl
    intro g _
    rw [FDRep.char_inv_eq_conj]
  rw [hsum]
  exact h

lemma classFunctionInner_representation_character
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    classFunctionInner ρ.character σ.character =
      Module.finrank ℂ (Representation.IntertwiningMap σ ρ) := by
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ ρ
  rw [classFunctionInner]
  have hsum :
      ∑ g : G, ρ.character g * conj (σ.character g) =
        ∑ g : G, ρ.character g * σ.character g⁻¹ := by
    apply Finset.sum_congr rfl
    intro g _
    rw [Representation.char_inv_eq_conj]
  rw [hsum]
  exact h

lemma classFunctionNormSq_character (A : FDRep ℂ G) :
    classFunctionNormSq A.character = Module.finrank ℂ (A ⟶ A) := by
  have h := classFunctionInner_character A A
  rw [classFunctionInner] at h
  have hnorm :
      ((classFunctionNormSq A.character : ℝ) : ℂ) =
        (Nat.card G : ℂ)⁻¹ *
          ∑ g : G, A.character g * conj (A.character g) := by
    rw [classFunctionNormSq]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have hc :
      ((classFunctionNormSq A.character : ℝ) : ℂ) =
        (Module.finrank ℂ (A ⟶ A) : ℂ) := hnorm.trans h
  exact_mod_cast congrArg Complex.re hc

lemma classFunctionNormSq_representation_character
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    classFunctionNormSq ρ.character =
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) := by
  have h := classFunctionInner_representation_character ρ ρ
  rw [classFunctionInner] at h
  have hnorm :
      ((classFunctionNormSq ρ.character : ℝ) : ℂ) =
        (Nat.card G : ℂ)⁻¹ *
          ∑ g : G, ρ.character g * conj (ρ.character g) := by
    rw [classFunctionNormSq]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have hc :
      ((classFunctionNormSq ρ.character : ℝ) : ℂ) =
        (Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) : ℂ) := hnorm.trans h
  exact_mod_cast congrArg Complex.re hc

lemma classFunctionNormSq_irreducible_character
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    classFunctionNormSq ρ.character = 1 := by
  rw [classFunctionNormSq_representation_character]
  exact_mod_cast Representation.IsIrreducible.finrank_intertwiningMap_self ρ

end CharacterInner

section RepresentationDecomposition

variable {G : Type*} [Group G]

lemma Representation.character_prod
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    (ρ.prod σ).character = ρ.character + σ.character := by
  funext g
  exact LinearMap.trace_prodMap' (ρ g) (σ g)

noncomputable def Subrepresentation.prodEquivOfIsCompl
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) (h : IsCompl S T) :
    (S.toRepresentation.prod T.toRepresentation).Equiv ρ := by
  have hsub : IsCompl S.toSubmodule T.toSubmodule := by
    constructor
    · rw [disjoint_iff, ← Subrepresentation.toSubmodule_inf]
      change (S ⊓ T).toSubmodule = (⊥ : Subrepresentation ρ).toSubmodule
      exact congrArg Subrepresentation.toSubmodule h.disjoint.eq_bot
    · rw [codisjoint_iff, ← Subrepresentation.toSubmodule_sup]
      change (S ⊔ T).toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule
      exact congrArg Subrepresentation.toSubmodule h.codisjoint.eq_top
  refine Representation.Equiv.mk
    (S.toSubmodule.prodEquivOfIsCompl T.toSubmodule hsub) ?_
  intro g
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change ρ g (x : V) + ρ g (y : V) = ρ g ((x : V) + (y : V))
  rw [map_add]

lemma Subrepresentation.character_add_character_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) (h : IsCompl S T) :
    S.toRepresentation.character + T.toRepresentation.character = ρ.character := by
  rw [← Representation.character_prod]
  exact Representation.char_iso
    (Submission.Helpers.Subrepresentation.prodEquivOfIsCompl S T h)

lemma Subrepresentation.finrank_add_finrank_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) (h : IsCompl S T) :
    Module.finrank ℂ S.toSubmodule + Module.finrank ℂ T.toSubmodule =
      Module.finrank ℂ V := by
  have he := (Submission.Helpers.Subrepresentation.prodEquivOfIsCompl S T h).toLinearEquiv.finrank_eq
  simpa [Module.finrank_prod] using he

noncomputable def Representation.IntertwiningMap.equivRange
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f) :
    ρ.Equiv f.range.toRepresentation := by
  refine Representation.Equiv.mk (LinearEquiv.ofInjective f.toLinearMap hf) ?_
  intro g
  ext v
  change f.toLinearMap (ρ g v) = σ g (f.toLinearMap v)
  simpa only [LinearMap.comp_apply] using congrArg (fun F => F v) (f.isIntertwining' g)

end RepresentationDecomposition

section CharacterCancellation

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
lemma FDRep.character_eq_zero_of_finrank_eq_zero (B : FDRep ℂ G)
    (hB : Module.finrank ℂ B = 0) : B.character = 0 := by
  letI : Subsingleton B := Module.finrank_zero_iff.mp hB
  funext g
  rw [FDRep.character]
  have hzero : B.ρ g = 0 := Subsingleton.elim _ _
  rw [hzero]
  simp

theorem exists_fdRep_character_eq_sub_of_normSq_eq_one
    (A B : FDRep ℂ G)
    (hnorm : classFunctionNormSq (A.character - B.character) = 1)
    (hdim : Module.finrank ℂ B < Module.finrank ℂ A) :
    ∃ C : FDRep ℂ G, C.character = A.character - B.character := by
  classical
  induction hBdim : Module.finrank ℂ B using Nat.strong_induction_on generalizing A B with
  | h n ih =>
      by_cases hn : n = 0
      · have hBzero : Module.finrank ℂ B = 0 := hBdim.trans hn
        refine ⟨A, ?_⟩
        rw [FDRep.character_eq_zero_of_finrank_eq_zero B hBzero]
        simp
      · have hBpos : 0 < Module.finrank ℂ B := by omega
        letI : Nontrivial B := Module.finrank_pos_iff.mp hBpos
        letI : NeZero (Nat.card G : ℂ) :=
          ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
        let ρA : Representation ℂ G A := A.ρ
        let ρB : Representation ℂ G B := B.ρ
        letI : Nontrivial ρB.asModule := ρB.asModuleEquiv.toEquiv.nontrivial
        letI : ρA.IsSemisimpleRepresentation := by infer_instance
        letI : ρB.IsSemisimpleRepresentation := by infer_instance
        letI : IsSemisimpleModule ℂ[G] ρB.asModule :=
          (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρB).mp
            inferInstance
        obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule ℂ[G]
          ρB.asModule
        letI : IsSimpleModule ℂ[G] S := hS
        let σ : Representation ℂ G S := Representation.ofModule' S
        letI : σ.IsIrreducible := by
          rw [Representation.irreducible_iff_isSimpleModule_asModule]
          let e : σ.asModule ≃ₗ[ℂ[G]] S :=
            { toFun := σ.asModuleEquiv
              invFun := σ.asModuleEquiv.symm
              left_inv := σ.asModuleEquiv.symm_apply_apply
              right_inv := σ.asModuleEquiv.apply_symm_apply
              map_add' := σ.asModuleEquiv.map_add
              map_smul' := by
                intro r x
                rw [σ.asModuleEquiv_map_smul]
                change σ.asAlgebraHom r (σ.asModuleEquiv x) = r • σ.asModuleEquiv x
                simp [σ, Representation.asAlgebraHom, Representation.ofModule'] }
          exact IsSimpleModule.congr e
        letI : Nontrivial S := IsSimpleModule.nontrivial ℂ[G] S
        let incl : Representation.IntertwiningMap σ ρB :=
          { toLinearMap :=
              ρB.asModuleEquiv.toLinearMap.comp (S.subtype.restrictScalars ℂ)
            isIntertwining' g := by
              ext v
              change ρB.asModuleEquiv (S.subtype (σ g v)) =
                ρB g (ρB.asModuleEquiv (S.subtype v))
              change ρB.asModuleEquiv
                (S.subtype ((MonoidAlgebra.of ℂ G g) • v)) = _
              rw [S.subtype.map_smul, ρB.asModuleEquiv_map_smul,
                Representation.asAlgebraHom_of] }
        have hincl_injective : Function.Injective incl := by
          intro x y hxy
          apply S.injective_subtype
          apply ρB.asModuleEquiv.injective
          simpa [incl] using hxy
        letI : FiniteDimensional ℂ S :=
          FiniteDimensional.of_injective incl.toLinearMap hincl_injective
        have hincl : incl ≠ 0 := by
          have hlin : incl.toLinearMap ≠ 0 :=
            LinearMap.ne_zero_of_injective hincl_injective
          intro hi
          apply hlin
          simpa [incl] using congrArg Representation.IntertwiningMap.toLinearMap hi
        have hmB :
            0 < Module.finrank ℂ (Representation.IntertwiningMap σ ρB) :=
          Module.finrank_pos_iff_exists_ne_zero.mpr ⟨incl, hincl⟩
        have hmA :
            0 < Module.finrank ℂ (Representation.IntertwiningMap σ ρA) := by
          by_contra hmA'
          have hmA0 :
              Module.finrank ℂ (Representation.IntertwiningMap σ ρA) = 0 :=
            Nat.eq_zero_of_not_pos hmA'
          have hnormσ : classFunctionNormSq σ.character = 1 :=
            classFunctionNormSq_irreducible_character σ
          have hplus :
              classFunctionNormSq ((A.character - B.character) + σ.character) =
                2 - 2 * (Module.finrank ℂ
                  (Representation.IntertwiningMap σ ρB) : ℝ) := by
            rw [classFunctionNormSq_add, hnorm, hnormσ, classFunctionInner_sub_left,
              show A.character = ρA.character from rfl,
              show B.character = ρB.character from rfl,
              classFunctionInner_representation_character ρA σ,
              classFunctionInner_representation_character ρB σ, hmA0]
            norm_num
            ring
          have hplus_nonpos :
              classFunctionNormSq ((A.character - B.character) + σ.character) ≤ 0 := by
            rw [hplus]
            have hmB' :
                (1 : ℝ) ≤ Module.finrank ℂ
                  (Representation.IntertwiningMap σ ρB) := by exact_mod_cast hmB
            linarith
          have hplus_zero :
              classFunctionNormSq ((A.character - B.character) + σ.character) = 0 :=
            le_antisymm hplus_nonpos
              (classFunctionNormSq_nonneg ((A.character - B.character) + σ.character))
          have hfun :
              (A.character - B.character) + σ.character = 0 :=
            (classFunctionNormSq_eq_zero_iff _).mp hplus_zero
          have hone := congrFun hfun 1
          simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, FDRep.char_one,
            Representation.char_one] at hone
          have hc :
              (Module.finrank ℂ A : ℂ) + (Module.finrank ℂ S : ℂ) =
                (Module.finrank ℂ B : ℂ) := by
            linear_combination hone
          have hnat :
              Module.finrank ℂ A + Module.finrank ℂ S =
                Module.finrank ℂ B := by exact_mod_cast hc
          have hSpos : 0 < Module.finrank ℂ S := by
            exact Module.finrank_pos_iff.mpr inferInstance
          omega
        obtain ⟨f, hf⟩ :=
          Module.finrank_pos_iff_exists_ne_zero.mp hmA
        have hfinj : Function.Injective f :=
          (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
        obtain ⟨AT, hAT⟩ := exists_isCompl f.range
        obtain ⟨BT, hBT⟩ := exists_isCompl incl.range
        let A' : FDRep ℂ G := FDRep.of AT.toRepresentation
        let B' : FDRep ℂ G := FDRep.of BT.toRepresentation
        have hcharRangeA :
            σ.character = f.range.toRepresentation.character :=
          Representation.char_iso
            (Submission.Helpers.Representation.IntertwiningMap.equivRange f hfinj)
        have hcharRangeB :
            σ.character = incl.range.toRepresentation.character :=
          Representation.char_iso
            (Submission.Helpers.Representation.IntertwiningMap.equivRange incl hincl_injective)
        have hcharA :
            f.range.toRepresentation.character + AT.toRepresentation.character =
              A.character :=
          Subrepresentation.character_add_character_eq f.range AT hAT
        have hcharB :
            incl.range.toRepresentation.character + BT.toRepresentation.character =
              B.character :=
          Subrepresentation.character_add_character_eq incl.range BT hBT
        have hvirt :
            A'.character - B'.character = A.character - B.character := by
          funext g
          have hrangeA := congrFun hcharRangeA g
          have hrangeB := congrFun hcharRangeB g
          have ha :
              f.range.toRepresentation.character g + AT.toRepresentation.character g =
                A.character g := by
            simpa only [Pi.add_apply] using congrFun hcharA g
          have hb :
              incl.range.toRepresentation.character g + BT.toRepresentation.character g =
                B.character g := by
            simpa only [Pi.add_apply] using congrFun hcharB g
          change AT.toRepresentation.character g - BT.toRepresentation.character g =
            A.character g - B.character g
          rw [← ha, ← hb, ← hrangeA, ← hrangeB]
          ring
        have hnorm' :
            classFunctionNormSq (A'.character - B'.character) = 1 := by
          rw [hvirt]
          exact hnorm
        have hdimRangeA :
            Module.finrank ℂ S =
              Module.finrank ℂ f.range.toSubmodule :=
          (Submission.Helpers.Representation.IntertwiningMap.equivRange f hfinj).toLinearEquiv.finrank_eq
        have hdimRangeB :
            Module.finrank ℂ S =
              Module.finrank ℂ incl.range.toSubmodule :=
          (Submission.Helpers.Representation.IntertwiningMap.equivRange incl
            hincl_injective).toLinearEquiv.finrank_eq
        have hdimAeq :
            Module.finrank ℂ f.range.toSubmodule + Module.finrank ℂ AT.toSubmodule =
              Module.finrank ℂ A :=
          Subrepresentation.finrank_add_finrank_eq f.range AT hAT
        have hdimBeq :
            Module.finrank ℂ incl.range.toSubmodule + Module.finrank ℂ BT.toSubmodule =
              Module.finrank ℂ B :=
          Subrepresentation.finrank_add_finrank_eq incl.range BT hBT
        have hdim' : Module.finrank ℂ B' < Module.finrank ℂ A' := by
          change Module.finrank ℂ BT.toSubmodule < Module.finrank ℂ AT.toSubmodule
          omega
        have hmeasure : Module.finrank ℂ B' < n := by
          change Module.finrank ℂ BT.toSubmodule < n
          have hSpos : 0 < Module.finrank ℂ S :=
            Module.finrank_pos_iff.mpr inferInstance
          omega
        obtain ⟨C, hC⟩ := ih (Module.finrank ℂ B') hmeasure A' B' hnorm' hdim' rfl
        refine ⟨C, hC.trans hvirt⟩

end CharacterCancellation

end

end Submission.Helpers
