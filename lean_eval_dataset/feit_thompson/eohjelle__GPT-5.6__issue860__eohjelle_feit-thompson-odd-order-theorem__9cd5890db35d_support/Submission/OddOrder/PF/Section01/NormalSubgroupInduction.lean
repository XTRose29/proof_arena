import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Submission.OddOrder.MathlibSupport.RepresentationAutomorphismTwist
import Submission.OddOrder.PF.Section01.Induction
import Submission.OddOrder.PF.Section01.IrreducibleCharacter

/-!
Induction from a normal subgroup, after Peterfalvi (1.5)(a)-(c).

The central construction is the ambient conjugation action on class
functions of a normal subgroup.  Restriction of an induced class function is
first computed as the average of all conjugates, then regrouped over its
orbit with the inertia multiplicity.  Orthogonality of irreducible characters
turns this into the induced norm formula and the induction-orbit dichotomy.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

namespace FiniteMulAction

variable {A : Type u} {M : Type v} [Group A] [Fintype A]
  [AddCommMonoid M] [MulAction A M]

local instance orbitFinite (m : M) : Finite (MulAction.orbit A m) :=
  (Finite.finite_mulAction_orbit m).to_subtype

noncomputable local instance orbitFintype (m : M) : Fintype (MulAction.orbit A m) :=
  Fintype.ofFinite _

noncomputable local instance stabilizerFintype (m : M) :
    Fintype (MulAction.stabilizer A m) :=
  Fintype.ofFinite _

/-- The canonical surjection from an acting group to one orbit. -/
def orbitMap (m : M) (a : A) : MulAction.orbit A m :=
  ⟨a • m, MulAction.mem_orbit m a⟩

/-- Every fiber of the orbit map is a torsor for the stabilizer. -/
noncomputable def stabilizerEquivOrbitMapFiber (m : M)
    (y : MulAction.orbit A m) :
    MulAction.stabilizer A m ≃ {a : A // orbitMap m a = y} := by
  classical
  choose a₀ ha₀ using y.property
  refine
    { toFun := fun s ↦ ⟨a₀ * s, ?_⟩
      invFun := fun a ↦ ⟨a₀⁻¹ * a, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Subtype.ext
    change (a₀ * (s : A)) • m = (y : M)
    rw [mul_smul, s.property]
    exact ha₀
  · rw [MulAction.mem_stabilizer_iff]
    have ha : (a : A) • m = (y : M) := congrArg Subtype.val a.property
    rw [mul_smul, ha, ← ha₀, inv_smul_smul]
  · intro s
    apply Subtype.ext
    simp
  · intro a
    apply Subtype.ext
    simp

/-- Regrouping a sum over a finite group by the orbit map. -/
theorem sum_smul_eq_card_stabilizer_nsmul_sum_orbit (m : M) :
    ∑ a : A, a • m =
      Fintype.card (MulAction.stabilizer A m) •
        ∑ y : MulAction.orbit A m, (y : M) := by
  classical
  rw [← Fintype.sum_fiberwise (orbitMap m) (fun a : A ↦ a • m)]
  calc
    ∑ y : MulAction.orbit A m, ∑ a : {a : A // orbitMap m a = y}, (a : A) • m =
        ∑ y : MulAction.orbit A m,
          Fintype.card (MulAction.stabilizer A m) • (y : M) := by
            apply Fintype.sum_congr
            intro y
            rw [Fintype.card_congr (stabilizerEquivOrbitMapFiber m y)]
            rw [← Finset.card_univ, ← Finset.sum_const]
            apply Finset.sum_congr rfl
            intro a _
            exact congrArg Subtype.val a.property
    _ = _ := by rw [Finset.smul_sum]

end FiniteMulAction

namespace CategoryTheorySupport

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂

/-- Equivalences of categories preserve simple objects when the inverse
functor preserves zero morphisms. -/
theorem simple_equivalence_functor_obj
    {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
    {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
    (e : C ≌ D) [e.inverse.PreservesZeroMorphisms]
    (X : C) [Simple X] : Simple (e.functor.obj X) := by
  refine ⟨?_⟩
  intro Y f hf
  let i : X ≅ e.inverse.obj (e.functor.obj X) := e.unitIso.app X
  let u : e.inverse.obj (e.functor.obj X) ⟶ X := i.inv
  haveI : IsIso u := by change IsIso i.inv; infer_instance
  let g : e.inverse.obj Y ⟶ X := e.inverse.map f ≫ u
  haveI : Mono (e.inverse.map f) := by infer_instance
  haveI : Mono g := by dsimp [g]; infer_instance
  constructor
  · intro hfIso
    haveI : IsIso f := hfIso
    haveI : IsIso (e.inverse.map f) := by infer_instance
    haveI : IsIso g := by dsimp [g]; infer_instance
    have hg : g ≠ 0 := (Simple.mono_isIso_iff_nonzero g).mp inferInstance
    intro hfzero
    apply hg
    dsimp [g]
    rw [hfzero, e.inverse.map_zero, zero_comp]
  · intro hfne
    have hmapne : e.inverse.map f ≠ 0 := by
      intro hmap
      apply hfne
      exact (e.inverse.map_eq_zero_iff).mp hmap
    have hgne : g ≠ 0 := by
      intro hg
      apply hmapne
      apply (cancel_mono u).mp
      rw [zero_comp]
      exact hg
    haveI : IsIso g := (Simple.mono_isIso_iff_nonzero g).mpr hgne
    haveI : IsIso (e.inverse.map f) :=
      IsIso.of_isIso_comp_right (e.inverse.map f) u
    exact isIso_of_reflects_iso f e.inverse

end CategoryTheorySupport

namespace ClassFunction

variable {G : Type u} {k : Type v} [Group G] [Field k]

/-- Ambient inverse conjugation of a class function on a normal subgroup. -/
def normalConjugate (H : Subgroup G) [H.Normal] (x : G)
    (f : ClassFunction H k) : ClassFunction H k where
  val h := f ((MulAut.conjNormal x).symm h)
  property y h := by
    change f ((MulAut.conjNormal x).symm (y * h * y⁻¹)) =
      f ((MulAut.conjNormal x).symm h)
    rw [map_mul, map_mul, map_inv]
    exact ClassFunction.conj_apply f ((MulAut.conjNormal x).symm y)
      ((MulAut.conjNormal x).symm h)

@[simp]
theorem normalConjugate_apply (H : Subgroup G) [H.Normal] (x : G)
    (f : ClassFunction H k) (h : H) :
    normalConjugate H x f h = f ((MulAut.conjNormal x).symm h) :=
  rfl

@[simp]
theorem normalConjugate_one (H : Subgroup G) [H.Normal]
    (f : ClassFunction H k) : normalConjugate H 1 f = f := by
  ext h
  change f ((MulAut.conjNormal 1).symm h) = f h
  apply congrArg f
  apply Subtype.ext
  rw [MulAut.conjNormal_symm_apply]
  simp

theorem normalConjugate_mul (H : Subgroup G) [H.Normal] (x y : G)
    (f : ClassFunction H k) :
    normalConjugate H (x * y) f =
      normalConjugate H x (normalConjugate H y f) := by
  ext h
  simp only [normalConjugate_apply]
  apply congrArg f
  apply Subtype.ext
  simp only [MulAut.conjNormal_symm_apply]
  group

@[simp]
theorem normalConjugate_inv_self (H : Subgroup G) [H.Normal] (x : G)
    (f : ClassFunction H k) :
    normalConjugate H x⁻¹ (normalConjugate H x f) = f := by
  simpa using (normalConjugate_mul H x⁻¹ x f).symm

@[simp]
theorem normalConjugate_self_inv (H : Subgroup G) [H.Normal] (x : G)
    (f : ClassFunction H k) :
    normalConjugate H x (normalConjugate H x⁻¹ f) = f := by
  simpa using (normalConjugate_mul H x x⁻¹ f).symm

/-- Ambient conjugation is a genuine action on class functions of a normal
subgroup. -/
@[reducible]
def normalConjugationMulAction (H : Subgroup G) [H.Normal] :
    MulAction G (ClassFunction H k) where
  smul x f := normalConjugate H x f
  one_smul := normalConjugate_one H
  mul_smul := normalConjugate_mul H

/-- The inertia subgroup of a class function under ambient conjugation. -/
def inertia (H : Subgroup G) [H.Normal] (f : ClassFunction H k) : Subgroup G := by
  letI := normalConjugationMulAction (k := k) H
  exact MulAction.stabilizer G f

theorem mem_inertia_iff (H : Subgroup G) [H.Normal]
    (f : ClassFunction H k) (x : G) :
    x ∈ inertia H f ↔ normalConjugate H x f = f := by
  change normalConjugate H x f = f ↔ _
  rfl

/-- Inner conjugation by the normal subgroup fixes every class function. -/
theorem normalConjugate_coe (H : Subgroup G) [H.Normal]
    (f : ClassFunction H k) (x : H) :
    normalConjugate H (x : G) f = f := by
  ext h
  rw [normalConjugate_apply]
  let y : H := x⁻¹
  have harg : (MulAut.conjNormal (x : G)).symm h = y * h * y⁻¹ := by
    apply Subtype.ext
    simp [y, MulAut.conjNormal_symm_apply]
  rw [harg]
  exact ClassFunction.conj_apply f y h

/-- The normal subgroup lies in the inertia subgroup of every one of its
class functions. -/
theorem le_inertia (H : Subgroup G) [H.Normal] (f : ClassFunction H k) :
    H ≤ inertia H f := by
  intro x hx
  rw [mem_inertia_iff]
  exact normalConjugate_coe H f ⟨x, hx⟩

/-- The relative inertia index appearing in Peterfalvi (1.5). -/
def inertiaIndex (H : Subgroup G) [H.Normal] (f : ClassFunction H k) : ℕ :=
  Nat.card (inertia H f) / Nat.card H

/-- The orbit of a class function of a normal subgroup under ambient
conjugation.  Keeping this as an explicit range makes the orbit independent
of any ambient `MulAction` instance. -/
def normalOrbit (H : Subgroup G) [H.Normal] (f : ClassFunction H k) :
    Set (ClassFunction H k) :=
  Set.range fun x : G ↦ normalConjugate H x f

instance normalOrbitFinite [Finite G] (H : Subgroup G) [H.Normal]
    (f : ClassFunction H k) : Finite (normalOrbit H f) :=
  (Set.finite_range fun x : G ↦ normalConjugate H x f).to_subtype

noncomputable instance normalOrbitFintype [Fintype G] (H : Subgroup G)
    [H.Normal] (f : ClassFunction H k) : Fintype (normalOrbit H f) :=
  Fintype.ofFinite _

/-- Ambient conjugation preserves the character of a simple representation,
up to twisting that representation by the corresponding group automorphism. -/
theorem isIrreducibleCharacter_normalConjugate
    (H : Subgroup G) [H.Normal] (x : G)
    (chi : IrreducibleCharacter H k) :
    IsIrreducibleCharacter H k
      (normalConjugate H x (chi : ClassFunction H k)) := by
  let V := chi.representation
  letI : CategoryTheory.Simple V := chi.representation_simple
  let a : MulAut H := (MulAut.conjNormal x).symm
  let e := Action.resEquiv (FGModuleCat k) a
  let W : FDRep k H := e.functor.obj V
  have hsimple : CategoryTheory.Simple W := by
    letI : e.inverse.PreservesZeroMorphisms := by infer_instance
    exact CategoryTheorySupport.simple_equivalence_functor_obj e V
  refine ⟨W, hsimple, ?_⟩
  ext h
  change V.character (a h) = chi ((MulAut.conjNormal x).symm h)
  exact chi.representation_character ((MulAut.conjNormal x).symm h)

/-- Ambient conjugation as an operation on irreducible characters. -/
def _root_.Submission.OddOrder.PF.IrreducibleCharacter.normalConjugate
    (H : Subgroup G) [H.Normal] (x : G)
    (chi : IrreducibleCharacter H k) : IrreducibleCharacter H k :=
  ⟨ClassFunction.normalConjugate H x (chi : ClassFunction H k),
    isIrreducibleCharacter_normalConjugate H x chi⟩

@[simp]
theorem _root_.Submission.OddOrder.PF.IrreducibleCharacter.coe_normalConjugate
    (H : Subgroup G) [H.Normal] (x : G)
    (chi : IrreducibleCharacter H k) :
    (chi.normalConjugate H x : ClassFunction H k) =
      ClassFunction.normalConjugate H x (chi : ClassFunction H k) :=
  rfl

section Finite

variable [Fintype G]

/-- Conjugating the inducing class function only reindexes the induction
sum. -/
theorem induce_normalConjugate
    (H : Subgroup G) [H.Normal] [Fintype H] (x : G)
    (f : ClassFunction H k) :
    induce H (normalConjugate H x f) = induce H f := by
  classical
  ext g
  simp only [induce_apply, inductionValue]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight x)
    (fun z : G ↦ inductionKernel H (normalConjugate H x f) z g)
    (fun z : G ↦ inductionKernel H f z g) fun z ↦ ?_
  change inductionKernel H (normalConjugate H x f) z g =
    inductionKernel H f (z * x) g
  let a : G := z⁻¹ * g * z
  have hmem : x⁻¹ * a * x ∈ H ↔ a ∈ H := by
    constructor
    · intro ha
      have := (inferInstance : H.Normal).conj_mem (x⁻¹ * a * x) ha x
      simpa [mul_assoc] using this
    · intro ha
      simpa using (inferInstance : H.Normal).conj_mem a ha x⁻¹
  by_cases hz : z⁻¹ * g * z ∈ H
  · have hxz : (z * x)⁻¹ * g * (z * x) ∈ H := by
      have := hmem.mpr (by simpa [a] using hz)
      simpa [a, mul_inv_rev, mul_assoc] using this
    rw [inductionKernel_of_mem H _ z g hz,
      inductionKernel_of_mem H _ (z * x) g hxz,
      normalConjugate_apply]
    apply congrArg f
    apply Subtype.ext
    simp only [MulAut.conjNormal_symm_apply]
    group
  · have hxz : (z * x)⁻¹ * g * (z * x) ∉ H := by
      intro hxz
      apply hz
      apply hmem.mp
      simpa [a, mul_inv_rev, mul_assoc] using hxz
    rw [inductionKernel_of_notMem H _ z g hz,
      inductionKernel_of_notMem H _ (z * x) g hxz]

/-- Restriction of induction from a normal subgroup is the normalized sum of
all ambient conjugates.  This is the ungrouped form of Peterfalvi (1.5)(a). -/
theorem restrict_induce_eq_average_normalConjugates
    (H : Subgroup G) [H.Normal] [Fintype H] (f : ClassFunction H k) :
    restrict H (induce H f) =
      (Nat.card H : k)⁻¹ • ∑ x : G, normalConjugate H x f := by
  classical
  ext h
  rw [restrict_apply, induce_apply_formula]
  simp only [smul_apply]
  congr 1
  let eval : ClassFunction H k →ₗ[k] k :=
    { toFun := fun g ↦ g h
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hsum := map_sum eval (fun x : G ↦ normalConjugate H x f)
  have hsum' : eval (∑ x : G, normalConjugate H x f) =
      ∑ x : G, eval (normalConjugate H x f) := by
    exact hsum Finset.univ
  change (∑ x : G, if hx : x⁻¹ * (h : G) * x ∈ H then
      f ⟨x⁻¹ * (h : G) * x, hx⟩ else 0) =
    (∑ x : G, normalConjugate H x f) h
  rw [show (∑ x : G, normalConjugate H x f) h =
      ∑ x : G, normalConjugate H x f h by exact hsum']
  apply Finset.sum_congr rfl
  intro x _
  have hx : x⁻¹ * (h : G) * x ∈ H := by
    simpa using (inferInstance : H.Normal).conj_mem (h : G) h.property x⁻¹
  rw [dif_pos hx, normalConjugate_apply]
  apply congrArg f
  apply Subtype.ext
  exact (MulAut.conjNormal_symm_apply x h).symm

/-- Peterfalvi (1.5)(a): restriction of an induced class function from a
normal subgroup is the sum of its ambient conjugacy class, with inertia
multiplicity. -/
theorem cfResInd_sum_cfclass [CharZero k]
    (H : Subgroup G) [H.Normal] [Fintype H] (f : ClassFunction H k) :
    restrict H (induce H f) =
      (inertiaIndex H f : k) •
        ∑ xi : normalOrbit H f, (xi : ClassFunction H k) := by
  classical
  letI : MulAction G (ClassFunction H k) := normalConjugationMulAction H
  letI : Finite (MulAction.orbit G f) :=
    (Finite.finite_mulAction_orbit f).to_subtype
  letI : Fintype (MulAction.orbit G f) := Fintype.ofFinite _
  have hsum :=
    FiniteMulAction.sum_smul_eq_card_stabilizer_nsmul_sum_orbit
      (A := G) (M := ClassFunction H k) f
  have hsumNat :
      ∑ x : G, x • f =
        Nat.card (MulAction.stabilizer G f) •
          ∑ xi : MulAction.orbit G f, (xi : ClassFunction H k) := by
    calc
      _ = @Fintype.card (MulAction.stabilizer G f)
            (FiniteMulAction.stabilizerFintype f) •
          ∑ xi : MulAction.orbit G f, (xi : ClassFunction H k) := hsum
      _ = _ := by
        rw [@Nat.card_eq_fintype_card (MulAction.stabilizer G f)
          (FiniteMulAction.stabilizerFintype f)]
  have hsum' :
      ∑ x : G, normalConjugate H x f =
        Nat.card (inertia H f) •
          ∑ xi : normalOrbit H f, (xi : ClassFunction H k) := by
    exact hsumNat
  rw [restrict_induce_eq_average_normalConjugates, hsum']
  have hdvd : Nat.card H ∣ Nat.card (inertia H f) :=
    Subgroup.card_dvd_of_le (le_inertia H f)
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul]
  apply congrArg (· • ∑ xi : normalOrbit H f, (xi : ClassFunction H k))
  rw [inertiaIndex, Nat.cast_div_charZero hdvd, div_eq_inv_mul]

/-- Peterfalvi (1.5)(b), norm formula: the norm of a character induced
from a normal subgroup is its inertia index. -/
theorem cfnorm_Ind_irr [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Invertible (Nat.card H : k)] (chi : IrreducibleCharacter H k) :
    characterPairing
        (induce H (chi : ClassFunction H k))
        (induce H (chi : ClassFunction H k)) =
      (inertiaIndex H (chi : ClassFunction H k) : k) := by
  classical
  let chiOrbit : normalOrbit H (chi : ClassFunction H k) :=
    ⟨(chi : ClassFunction H k), 1, normalConjugate_one H _⟩
  have horbit_pairing
      (xi : normalOrbit H (chi : ClassFunction H k)) :
      characterPairing (chi : ClassFunction H k) (xi : ClassFunction H k) =
        if xi = chiOrbit then 1 else 0 := by
    obtain ⟨x, hx⟩ := xi.property
    let psi : IrreducibleCharacter H k := chi.normalConjugate H x
    have hpsi : (psi : ClassFunction H k) = (xi : ClassFunction H k) := hx
    rw [← hpsi, IrreducibleCharacter.characterPairing_eq_ite]
    by_cases hxi : xi = chiOrbit
    · have hchi : chi = psi := by
        apply Subtype.ext
        exact (hpsi.trans (congrArg Subtype.val hxi)).symm
      rw [if_pos hchi, if_pos hxi]
    · have hchi : chi ≠ psi := by
        intro hchi
        apply hxi
        apply Subtype.ext
        exact hpsi.symm.trans (congrArg Subtype.val hchi).symm
      rw [if_neg hchi, if_neg hxi]
  have hpairsum :
      characterPairing (chi : ClassFunction H k)
          (∑ xi : normalOrbit H (chi : ClassFunction H k),
            (xi : ClassFunction H k)) = 1 := by
    change IrreducibleCharacter.pairingLeft (chi : ClassFunction H k)
      (∑ xi : normalOrbit H (chi : ClassFunction H k),
        (xi : ClassFunction H k)) = 1
    rw [map_sum]
    change (∑ xi : normalOrbit H (chi : ClassFunction H k),
      characterPairing (chi : ClassFunction H k) (xi : ClassFunction H k)) = 1
    simp_rw [horbit_pairing]
    simp
  rw [frobeniusReciprocity, cfResInd_sum_cfclass]
  change IrreducibleCharacter.pairingLeft (chi : ClassFunction H k)
      ((inertiaIndex H (chi : ClassFunction H k) : k) •
        ∑ xi : normalOrbit H (chi : ClassFunction H k),
          (xi : ClassFunction H k)) = _
  rw [map_smul]
  change (inertiaIndex H (chi : ClassFunction H k) : k) •
      characterPairing (chi : ClassFunction H k)
        (∑ xi : normalOrbit H (chi : ClassFunction H k),
          (xi : ClassFunction H k)) = _
  rw [hpairsum, smul_eq_mul, mul_one]

/-- Peterfalvi (1.5)(b), at the class-function level: if the inertia
subgroup is contained in the inducing subgroup, the induced class function
has norm one.  Upgrading this to `IsIrreducibleCharacter` only requires a
future identification of `ClassFunction.induce` with the character of
Mathlib's induced representation. -/
theorem inertia_Ind_norm_one [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Invertible (Nat.card H : k)] (chi : IrreducibleCharacter H k)
    (hI : inertia H (chi : ClassFunction H k) ≤ H) :
    characterPairing
        (induce H (chi : ClassFunction H k))
        (induce H (chi : ClassFunction H k)) = 1 := by
  have hinertia : inertia H (chi : ClassFunction H k) = H :=
    le_antisymm hI (le_inertia H _)
  rw [cfnorm_Ind_irr]
  simp [inertiaIndex, hinertia]

/-- Alias retaining the source-oriented name for the norm-one intermediate
form used to prove `inertia_Ind_irr`. -/
theorem inertia_Ind_irr_norm_one [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Invertible (Nat.card H : k)] (chi : IrreducibleCharacter H k)
    (hI : inertia H (chi : ClassFunction H k) ≤ H) :
    characterPairing
        (induce H (chi : ClassFunction H k))
        (induce H (chi : ClassFunction H k)) = 1 :=
  inertia_Ind_norm_one H chi hI

/-- Peterfalvi (1.5)(c): two irreducible characters of a normal subgroup
are either ambient-conjugate, in which case their inductions agree, or their
inductions are orthogonal. -/
theorem cfclass_Ind_cases [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Invertible (Nat.card H : k)]
    (chi₁ chi₂ : IrreducibleCharacter H k) :
    ((∃ x : G, normalConjugate H x (chi₁ : ClassFunction H k) =
          (chi₂ : ClassFunction H k)) ∧
        induce H (chi₁ : ClassFunction H k) =
          induce H (chi₂ : ClassFunction H k)) ∨
      ((¬ ∃ x : G, normalConjugate H x (chi₁ : ClassFunction H k) =
          (chi₂ : ClassFunction H k)) ∧
        characterPairing
          (induce H (chi₁ : ClassFunction H k))
          (induce H (chi₂ : ClassFunction H k)) = 0) := by
  classical
  by_cases horbit : ∃ x : G,
      normalConjugate H x (chi₁ : ClassFunction H k) =
        (chi₂ : ClassFunction H k)
  · left
    refine ⟨horbit, ?_⟩
    obtain ⟨x, hx⟩ := horbit
    exact (induce_normalConjugate H x (chi₁ : ClassFunction H k)).symm.trans
      (congrArg (induce H) hx)
  · right
    refine ⟨horbit, ?_⟩
    have horbit_pairing_zero
        (xi : normalOrbit H (chi₂ : ClassFunction H k)) :
        characterPairing (chi₁ : ClassFunction H k)
          (xi : ClassFunction H k) = 0 := by
      obtain ⟨x, hx⟩ := xi.property
      let psi : IrreducibleCharacter H k := chi₂.normalConjugate H x
      have hpsi : (psi : ClassFunction H k) = (xi : ClassFunction H k) := hx
      rw [← hpsi]
      apply IrreducibleCharacter.characterPairing_eq_zero
      intro hchi
      apply horbit
      refine ⟨x⁻¹, ?_⟩
      have hval : (chi₁ : ClassFunction H k) = (psi : ClassFunction H k) :=
        congrArg Subtype.val hchi
      rw [hval, IrreducibleCharacter.coe_normalConjugate,
        normalConjugate_inv_self]
    rw [frobeniusReciprocity, cfResInd_sum_cfclass]
    change IrreducibleCharacter.pairingLeft (chi₁ : ClassFunction H k)
      ((inertiaIndex H (chi₂ : ClassFunction H k) : k) •
        ∑ xi : normalOrbit H (chi₂ : ClassFunction H k),
          (xi : ClassFunction H k)) = 0
    rw [map_smul, map_sum]
    change (inertiaIndex H (chi₂ : ClassFunction H k) : k) •
      (∑ xi : normalOrbit H (chi₂ : ClassFunction H k),
        characterPairing (chi₁ : ClassFunction H k)
          (xi : ClassFunction H k)) = 0
    simp_rw [horbit_pairing_zero]
    simp

end Finite

end ClassFunction

end

end Submission.OddOrder.PF
