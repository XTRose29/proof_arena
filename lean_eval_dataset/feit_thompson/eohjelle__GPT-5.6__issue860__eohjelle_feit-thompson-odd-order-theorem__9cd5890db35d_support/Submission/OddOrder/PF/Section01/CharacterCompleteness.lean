import Mathlib.RepresentationTheory.Maschke
import Submission.OddOrder.PF.Section01.IrreducibleCharacter

/-!
Completeness of the ordinary irreducible characters of a finite group.

The proof uses the standard semisimple group-algebra argument.  A class
function determines a central element of the group algebra.  If it pairs to
zero with every irreducible character, that central element has trace zero on
every simple module.  Schur's lemma then makes each such action zero, and
Maschke's theorem makes the regular module a sum of its simple submodules.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators MonoidAlgebra
open CategoryTheory

universe u v w

variable {G : Type u} {k : Type v} [Group G] [Field k] [Fintype G]

namespace ClassFunction

/-- The central group-algebra element whose coefficient at `g` is
`f g⁻¹`.  This convention matches `characterPairing`. -/
def centralElement (f : ClassFunction G k) : k[G] :=
  Finsupp.equivFunOnFinite.symm (fun g ↦ f g⁻¹)

@[simp]
theorem centralElement_apply (f : ClassFunction G k) (g : G) :
    centralElement f g = f g⁻¹ := by
  simp [centralElement]

theorem centralElement_eq_sum (f : ClassFunction G k) :
    centralElement f = ∑ g : G, MonoidAlgebra.single g (f g⁻¹) := by
  classical
  exact Finsupp.equivFunOnFinite_symm_eq_sum _

/-- The group-algebra element attached to a class function is central. -/
theorem centralElement_mem_center (f : ClassFunction G k) :
    centralElement f ∈ Set.center k[G] := by
  refine ⟨?_, fun _ _ ↦ (mul_assoc _ _ _).symm, fun _ _ ↦ mul_assoc _ _ _⟩
  intro a
  rw [commute_iff_eq]
  induction a using MonoidAlgebra.induction_on with
  | hM x =>
      ext h
      simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply,
        MonoidAlgebra.mul_single_apply, centralElement_apply, one_mul, mul_one]
      simp only [mul_inv_rev, inv_inv]
      have hf := ClassFunction.conj_apply f x (h⁻¹ * x)
      simpa [mul_assoc] using hf
  | hadd a b ha hb =>
      simpa only [mul_add, add_mul] using congrArg₂ (fun x y ↦ x + y) ha hb
  | hsmul c a ha =>
      calc
        centralElement f * (c • a) = c • (centralElement f * a) :=
          mul_smul_comm _ _ _
        _ = c • (a * centralElement f) := congrArg (fun x ↦ c • x) ha
        _ = (c • a) * centralElement f := (smul_mul_assoc _ _ _).symm

/-- A representation evaluates the central element attached to `f` with trace
equal to the unnormalized character pairing with `f`. -/
theorem trace_asAlgebraHom_centralElement
    {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V) (f : ClassFunction G k) :
    LinearMap.trace k V (rho.asAlgebraHom (centralElement f)) =
      ∑ g : G, rho.character g * f g⁻¹ := by
  classical
  rw [centralElement_eq_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Representation.asAlgebraHom_single, map_smul]
  simp [Representation.character, mul_comm]

end ClassFunction

/-- A central group-algebra element acts as an intertwiner on every
representation. -/
def centralElementIntertwiner
    {V : Type w} [AddCommGroup V] [Module k V]
    (rho : _root_.Representation k G V) (f : ClassFunction G k) :
    _root_.Representation.IntertwiningMap rho rho where
  toLinearMap := rho.asAlgebraHom (ClassFunction.centralElement f)
  isIntertwining' g := by
    ext v
    rw [← Representation.asAlgebraHom_of rho g,
      ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp,
      ← map_mul, ← map_mul]
    exact congrArg (fun q : Module.End k V ↦ q v)
      (congrArg rho.asAlgebraHom
        ((ClassFunction.centralElement_mem_center f).comm
          (MonoidAlgebra.of k G g)).eq)

@[simp]
theorem centralElementIntertwiner_toLinearMap
    {V : Type w} [AddCommGroup V] [Module k V]
    (rho : _root_.Representation k G V) (f : ClassFunction G k) :
    (centralElementIntertwiner rho f).toLinearMap =
      rho.asAlgebraHom (ClassFunction.centralElement f) :=
  rfl

/-- If a class function pairs to zero with an irreducible representation,
its central element acts by zero on that representation.  Centrality and
Schur's lemma turn the action into a scalar, and characteristic zero lets its
zero trace detect that scalar. -/
theorem centralElementIntertwiner_eq_zero_of_pairing_eq_zero
    [IsAlgClosed k] [CharZero k]
    {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : _root_.Representation k G V) [rho.IsIrreducible]
    (f : ClassFunction G k)
    (hpair : characterPairing (ClassFunction.ofRepresentation rho) f = 0) :
    centralElementIntertwiner rho f = 0 := by
  have hcard : (Nat.card G : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsum : ∑ g : G, rho.character g * f g⁻¹ = 0 := by
    have h := hpair
    simp only [characterPairing, ClassFunction.ofRepresentation_apply] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hcard)
  have htrace :
      LinearMap.trace k V (centralElementIntertwiner rho f).toLinearMap = 0 := by
    rw [centralElementIntertwiner_toLinearMap,
      ClassFunction.trace_asAlgebraHom_centralElement]
    exact hsum
  obtain ⟨c, hc⟩ :=
    (_root_.Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := rho)).2
        (centralElementIntertwiner rho f)
  have htracec :
      LinearMap.trace k V
        (algebraMap k (_root_.Representation.IntertwiningMap rho rho) c).toLinearMap = 0 := by
    rw [hc]
    exact htrace
  letI : Nontrivial rho.asModule := IsSimpleModule.nontrivial k[G] rho.asModule
  letI : Nontrivial V := inferInstanceAs (Nontrivial rho.asModule)
  have hfin : (Module.finrank k V : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  have hcfin : c * (Module.finrank k V : k) = 0 := by
    have hone :
        (1 : _root_.Representation.IntertwiningMap rho rho).toLinearMap =
          LinearMap.id :=
      rfl
    have htracec' : LinearMap.trace k V (c • LinearMap.id) = 0 := by
      simpa only [
        _root_.Representation.IntertwiningMap.algebraMap_apply,
        _root_.Representation.IntertwiningMap.toLinearMap_smul, hone] using htracec
    simpa only [map_smul, LinearMap.trace_id, smul_eq_mul] using htracec'
  have hc0 : c = 0 := (mul_eq_zero.mp hcfin).resolve_right hfin
  rw [← hc, hc0, map_zero]

/-- An irreducible unbundled representation gives a simple object of `FDRep`.
This bridges Mathlib's module-theoretic irreducibility API and the categorical
notion used in `IrreducibleCharacter`. -/
theorem simple_fdRep_of_isIrreducible
    [IsAlgClosed k] [CharZero k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : _root_.Representation k G V) [rho.IsIrreducible] :
    CategoryTheory.Simple (FDRep.of rho) := by
  letI : IsSimpleModule k[G] rho.asModule :=
    (_root_.Representation.irreducible_iff_isSimpleModule_asModule rho).mp
      inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial k[G] rho.asModule
  let F := CategoryTheory.forget₂ (FDRep k G) (Rep k G)
  refine ⟨?_⟩
  intro Y f hfmono
  constructor
  · intro _ hzero
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hid : 𝟙 (FDRep.of rho) = 0 := by
      rw [← CategoryTheory.cancel_epi f]
      simpa [hzero]
    have hx0 := congrArg
      (fun q : FDRep.of rho ⟶ FDRep.of rho ↦ q.hom.hom x) hid
    exact hx (by simpa using hx0)
  · intro hne
    haveI : CategoryTheory.Mono (F.map f) := F.map_mono f
    have hinj : Function.Injective (F.map f).hom :=
      (Rep.mono_iff_injective (F.map f)).mp inferInstance
    have hmapne : F.map f ≠ 0 := by
      intro hf
      apply hne
      apply F.map_injective
      simpa using hf
    have htne : (F.map f).hom ≠ 0 := by
      intro ht
      apply hmapne
      apply Rep.hom_injective
      simpa using ht
    letI : IsSimpleModule k[G]
        (_root_.Representation.asModule (F.obj (FDRep.of rho)).ρ) := by
      change IsSimpleModule k[G] rho.asModule
      infer_instance
    let moduleMap :=
      _root_.Representation.IntertwiningMap.equivLinearMapAsModule
        (F.obj Y).ρ (F.obj (FDRep.of rho)).ρ (F.map f).hom
    have hmoduleMap : moduleMap ≠ 0 := by
      intro hm
      apply htne
      rw [← LinearEquiv.map_eq_zero_iff
        (_root_.Representation.IntertwiningMap.equivLinearMapAsModule
          (F.obj Y).ρ (F.obj (FDRep.of rho)).ρ)]
      exact hm
    have hsurj : Function.Surjective moduleMap :=
      LinearMap.surjective_of_ne_zero hmoduleMap
    have hsurj' : Function.Surjective (F.map f).hom := by
      exact hsurj
    haveI : CategoryTheory.IsIso (F.map f) :=
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective (F.map f)).mpr
        ⟨hinj, hsurj'⟩
    exact (CategoryTheory.isIso_iff_of_reflects_iso f F).mp inferInstance

/-- Orthogonality to all irreducible characters forces the associated central
element to act by zero on every irreducible representation. -/
theorem centralElementIntertwiner_eq_zero_of_forall_pairing_eq_zero
    [IsAlgClosed k] [CharZero k]
    (f : ClassFunction G k)
    (horth : ∀ chi : IrreducibleCharacter G k,
      characterPairing (chi : ClassFunction G k) f = 0)
    {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : _root_.Representation k G V) [rho.IsIrreducible] :
    centralElementIntertwiner rho f = 0 := by
  let W := Fin (Module.finrank k V) → k
  let e : V ≃ₗ[k] W := (Module.finBasis k V).equivFun
  let sigma : _root_.Representation k G W :=
    e.conjRingEquiv.toMonoidHom.comp rho
  let equiv : _root_.Representation.Equiv rho sigma :=
    _root_.Representation.Equiv.mk e (by
      intro g
      ext x
      simp [sigma, e])
  let moduleMap : rho.asModule →ₗ[k[G]] sigma.asModule :=
    _root_.Representation.IntertwiningMap.equivLinearMapAsModule rho sigma
      equiv.toIntertwiningMap
  let moduleEquiv : rho.asModule ≃ₗ[k[G]] sigma.asModule :=
    LinearEquiv.ofBijective moduleMap equiv.bijective
  letI : sigma.IsIrreducible := by
    rw [_root_.Representation.irreducible_iff_isSimpleModule_asModule]
    exact IsSimpleModule.congr moduleEquiv.symm
  letI : CategoryTheory.Simple (FDRep.of sigma) :=
    simple_fdRep_of_isIrreducible sigma
  apply centralElementIntertwiner_eq_zero_of_pairing_eq_zero
  have h := horth (IrreducibleCharacter.ofFDRep (FDRep.of sigma))
  change characterPairing (ClassFunction.ofRepresentation sigma) f = 0 at h
  have hchar :
      ClassFunction.ofRepresentation sigma =
        ClassFunction.ofRepresentation rho := by
    ext g
    change LinearMap.trace k W (sigma g) = LinearMap.trace k V (rho g)
    change LinearMap.trace k W (e.conj (rho g)) =
      LinearMap.trace k V (rho g)
    exact LinearMap.trace_conj' (rho g) e
  rw [hchar] at h
  exact h

/-- Left multiplication by the central group-algebra element, as an
endomorphism of the regular module. -/
def centralElementRegularEnd (f : ClassFunction G k) :
    Module.End k[G] k[G] where
  toFun a := ClassFunction.centralElement f * a
  map_add' _ _ := mul_add _ _ _
  map_smul' a b := by
    change ClassFunction.centralElement f * (a * b) =
      a * (ClassFunction.centralElement f * b)
    calc
      ClassFunction.centralElement f * (a * b) =
          (ClassFunction.centralElement f * a) * b :=
        (mul_assoc _ _ _).symm
      _ = (a * ClassFunction.centralElement f) * b := by
        rw [(ClassFunction.centralElement_mem_center f).comm a]
      _ = a * (ClassFunction.centralElement f * b) := mul_assoc _ _ _

@[simp]
theorem centralElementRegularEnd_apply (f : ClassFunction G k) (a : k[G]) :
    centralElementRegularEnd f a = ClassFunction.centralElement f * a :=
  rfl

/-- If `f` is orthogonal to every irreducible character, every simple
submodule of the regular module lies in the kernel of multiplication by its
central element. -/
theorem simpleSubmodule_le_ker_centralElementRegularEnd
    [IsAlgClosed k] [CharZero k]
    (f : ClassFunction G k)
    (horth : ∀ chi : IrreducibleCharacter G k,
      characterPairing (chi : ClassFunction G k) f = 0)
    (S : Submodule k[G] k[G]) [IsSimpleModule k[G] S] :
    S ≤ LinearMap.ker (centralElementRegularEnd f) := by
  intro s hs
  letI : FiniteDimensional k S :=
    FiniteDimensional.of_injective (S.subtype.restrictScalars k)
      S.subtype_injective
  let rho := _root_.Representation.ofModule' (k := k) (G := G) S
  have hrho : rho.asAlgebraHom = Algebra.lsmul k k S := by
    simp [rho, _root_.Representation.ofModule',
      _root_.Representation.asAlgebraHom_def]
  let e : rho.asModule ≃ₗ[k[G]] S := {
    rho.asModuleEquiv with
    map_smul' a x := by
      calc
        rho.asModuleEquiv (a • x) =
            rho.asAlgebraHom a (rho.asModuleEquiv x) :=
          rho.asModuleEquiv_map_smul a x
        _ = a • rho.asModuleEquiv x := by
          rw [hrho]
          rfl }
  letI : rho.IsIrreducible := by
    rw [_root_.Representation.irreducible_iff_isSimpleModule_asModule]
    exact IsSimpleModule.congr e
  have hz := centralElementIntertwiner_eq_zero_of_forall_pairing_eq_zero
    f horth rho
  let sS : S := ⟨s, hs⟩
  have hx : rho.asAlgebraHom (ClassFunction.centralElement f) sS = 0 := by
    have hlin := congrArg
      (fun q : _root_.Representation.IntertwiningMap rho rho ↦ q.toLinearMap) hz
    have h := congrArg (fun q ↦ q sS) hlin
    simpa only [centralElementIntertwiner_toLinearMap,
      _root_.Representation.IntertwiningMap.zero_toLinearMap,
      LinearMap.zero_apply, Pi.zero_apply, zero_apply] using h
  have hsS : ClassFunction.centralElement f • sS = 0 := by
    rw [hrho] at hx
    exact hx
  change ClassFunction.centralElement f * s = 0
  exact congrArg Subtype.val hsS

/-- A class function orthogonal to every irreducible character has zero
associated central group-algebra element. -/
theorem centralElement_eq_zero_of_forall_pairing_eq_zero
    [IsAlgClosed k] [CharZero k]
    (f : ClassFunction G k)
    (horth : ∀ chi : IrreducibleCharacter G k,
      characterPairing (chi : ClassFunction G k) f = 0) :
    ClassFunction.centralElement f = 0 := by
  letI : NeZero (Nat.card G : k) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hker : LinearMap.ker (centralElementRegularEnd f) = ⊤ := by
    apply top_unique
    rw [← IsSemisimpleModule.sSup_simples_eq_top k[G] k[G]]
    apply sSup_le
    intro S hS
    letI : IsSimpleModule k[G] S := hS
    exact simpleSubmodule_le_ker_centralElementRegularEnd f horth S
  have hend : centralElementRegularEnd f = 0 :=
    LinearMap.ker_eq_top.mp hker
  have h := congrArg (fun q : Module.End k[G] k[G] ↦ q 1) hend
  simpa only [centralElementRegularEnd_apply, mul_one, LinearMap.zero_apply] using h

/-- Nondegeneracy in the second argument against all irreducible characters. -/
theorem classFunction_eq_zero_of_forall_irreducible_pairing_eq_zero
    [IsAlgClosed k] [CharZero k]
    (f : ClassFunction G k)
    (horth : ∀ chi : IrreducibleCharacter G k,
      characterPairing (chi : ClassFunction G k) f = 0) :
    f = 0 := by
  have hz := centralElement_eq_zero_of_forall_pairing_eq_zero f horth
  ext g
  change f g = 0
  calc
    f g = ClassFunction.centralElement f g⁻¹ := by simp
    _ = (0 : k[G]) g⁻¹ := congrArg (fun a : k[G] ↦ a g⁻¹) hz
    _ = 0 := rfl

section Completeness

variable [IsAlgClosed k] [CharZero k]

local instance characterCompletenessInvertibleCard :
    Invertible (Nat.card G : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- The Fourier expansion of a class function in the orthonormal family of
irreducible characters. -/
def irreducibleCharacterExpansion (f : ClassFunction G k) :
    ClassFunction G k :=
  ∑ chi : IrreducibleCharacter G k,
    characterPairing (chi : ClassFunction G k) f •
      (chi : ClassFunction G k)

/-- The irreducible-character expansion has the same pairing against every
irreducible character as the original class function. -/
theorem characterPairing_irreducibleCharacterExpansion
    (f : ClassFunction G k) (psi : IrreducibleCharacter G k) :
    characterPairing (psi : ClassFunction G k)
        (irreducibleCharacterExpansion f) =
      characterPairing (psi : ClassFunction G k) f := by
  classical
  change (IrreducibleCharacter.pairingLeft (psi : ClassFunction G k))
      (irreducibleCharacterExpansion f) = _
  rw [irreducibleCharacterExpansion, map_sum]
  simp [IrreducibleCharacter.pairingLeft,
    IrreducibleCharacter.characterPairing_eq_ite]

/-- Every class function is equal to its irreducible-character expansion. -/
theorem irreducibleCharacterExpansion_eq (f : ClassFunction G k) :
    irreducibleCharacterExpansion f = f := by
  have hz : f - irreducibleCharacterExpansion f = 0 :=
    classFunction_eq_zero_of_forall_irreducible_pairing_eq_zero _ (by
      intro chi
      change (IrreducibleCharacter.pairingLeft (chi : ClassFunction G k))
        (f - irreducibleCharacterExpansion f) = 0
      rw [map_sub]
      change characterPairing (chi : ClassFunction G k) f -
        characterPairing (chi : ClassFunction G k)
          (irreducibleCharacterExpansion f) = 0
      rw [characterPairing_irreducibleCharacterExpansion]
      exact sub_self _)
  exact (sub_eq_zero.mp hz).symm

/-- Completeness (the second orthogonality theorem): ordinary irreducible
characters span the full vector space of class functions. -/
theorem irreducibleCharacter_span_eq_top :
    Submodule.span k
        (Set.range (fun chi : IrreducibleCharacter G k ↦
          (chi : ClassFunction G k))) = ⊤ := by
  apply top_unique
  intro f _
  rw [← irreducibleCharacterExpansion_eq f]
  rw [irreducibleCharacterExpansion]
  apply Submodule.sum_mem
  intro chi _
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self chi))

end Completeness

end

end Submission.OddOrder.PF
