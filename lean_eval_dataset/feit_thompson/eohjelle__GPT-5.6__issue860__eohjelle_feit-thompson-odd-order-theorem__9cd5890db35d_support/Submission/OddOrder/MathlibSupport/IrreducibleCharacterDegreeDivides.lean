import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.ClassEquation
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.NumberTheory.Niven
import Mathlib.RingTheory.Finiteness.Finsupp
import Submission.OddOrder.MathlibSupport.IrreducibleCommutantScalar
import Submission.OddOrder.PF.Section01.IrreducibleCharacter

/-!
# Degrees of irreducible characters divide the group order

The proof is the standard algebraic-integer argument: character values are
algebraic integers, conjugacy-class sums act by algebraic-integer scalars on
an irreducible representation, and character orthogonality shows that the
quotient of the group order by the degree is both rational and integral.
-/

namespace Submission.OddOrder.MathlibSupport

noncomputable section

open scoped MonoidAlgebra

universe u v w

variable {G : Type u} {k : Type v} {V : Type w}
variable [Group G] [Fintype G]
variable [Field k] [IsAlgClosed k] [CharZero k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Character values of a finite-group representation in characteristic zero
are algebraic integers. -/
theorem representation_character_isIntegral
    (rho : Representation k G V) (g : G) :
    IsIntegral ℤ (rho.character g) := by
  rw [Representation.character,
    Module.End.trace_eq_sum_roots_charpoly_of_splits
      (IsAlgClosed.splits (rho g).charpoly)]
  apply IsIntegral.multiset_sum
  intro mu hmu
  have hroot : (rho g).charpoly.IsRoot mu :=
    (Polynomial.mem_roots (Polynomial.Monic.ne_zero (LinearMap.charpoly_monic (rho g)))).mp hmu
  have heigen : Module.End.HasEigenvalue (rho g) mu :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (rho g) mu).mpr hroot
  obtain ⟨x, hx⟩ := heigen.exists_hasEigenvector
  have hpowEnd : (rho g) ^ Fintype.card G = 1 := by
    rw [← map_pow, pow_card_eq_one, map_one]
  have hpowScalar : mu ^ Fintype.card G = 1 := by
    have hxpow := hx.pow_apply (Fintype.card G)
    rw [hpowEnd] at hxpow
    apply smul_left_injective k hx.2
    simpa using hxpow.symm
  exact IsIntegral.of_pow Fintype.card_pos (hpowScalar ▸ isIntegral_one)

/-- The endomorphism obtained by summing a representation over the conjugacy
class of `x`. -/
def conjugacyClassEnd (rho : Representation k G V) (x : G) :
    Module.End k V := by
  classical
  exact ∑ y : G, if IsConj y x then rho y else 0

/-- A conjugacy-class sum commutes with every represented group element. -/
theorem conjugacyClassEnd_commute (rho : Representation k G V) (x g : G) :
    Commute (conjugacyClassEnd rho x) (rho g) := by
  classical
  have hreindex :
      (∑ y : G, rho g * (if IsConj y x then rho y else 0)) =
        ∑ y : G, (if IsConj y x then rho y else 0) * rho g := by
    refine Fintype.sum_equiv (MulAut.conj g).toEquiv
      (fun y : G ↦ rho g * (if IsConj y x then rho y else 0))
      (fun y : G ↦ (if IsConj y x then rho y else 0) * rho g)
      fun y ↦ ?_
    change rho g * (if IsConj y x then rho y else 0) =
      (if IsConj (g * y * g⁻¹) x then rho (g * y * g⁻¹) else 0) * rho g
    have hyconj : IsConj y (g * y * g⁻¹) :=
      isConj_iff.mpr ⟨g, rfl⟩
    have hiff : IsConj (g * y * g⁻¹) x ↔ IsConj y x :=
      ⟨fun h ↦ hyconj.trans h, fun h ↦ hyconj.symm.trans h⟩
    by_cases hy : IsConj y x
    · rw [if_pos hy, if_pos (hiff.mpr hy)]
      rw [← map_mul, ← map_mul]
      simp [mul_assoc]
    · rw [if_neg hy, if_neg (not_congr hiff |>.mpr hy)]
      simp
  change
    (∑ y : G, (if IsConj y x then rho y else 0)) * rho g =
      rho g * ∑ y : G, (if IsConj y x then rho y else 0)
  simpa only [Finset.sum_mul, Finset.mul_sum] using hreindex.symm

/-- The integral group-ring conjugacy-class sum. -/
def conjugacyClassSumInt (x : G) : ℤ[G] := by
  classical
  exact ∑ y : G, if IsConj y x then MonoidAlgebra.single y 1 else 0

/-- Extend a representation from `k[G]` to the integral group ring by
coefficient change. -/
def integralRepresentationHom (rho : Representation k G V) :
    ℤ[G] →+* Module.End k V :=
  rho.asAlgebraHom.toRingHom.comp
    (MonoidAlgebra.mapRingHom G (Int.castRingHom k))

@[simp]
theorem integralRepresentationHom_conjugacyClassSumInt
    (rho : Representation k G V) (x : G) :
    integralRepresentationHom rho (conjugacyClassSumInt x) =
      conjugacyClassEnd rho x := by
  classical
  simp only [integralRepresentationHom, conjugacyClassSumInt,
    conjugacyClassEnd, map_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : IsConj y x
  · rw [if_pos hy, if_pos hy]
    simp
  · rw [if_neg hy, if_neg hy]
    simp

/-- Conjugacy-class endomorphisms are integral because they are images of
elements of the finite integral group ring. -/
theorem conjugacyClassEnd_isIntegral
    (rho : Representation k G V) (x : G) :
    IsIntegral ℤ (conjugacyClassEnd rho x) := by
  letI : Module.Finite ℤ ℤ[G] := MonoidAlgebra.moduleFinite
  rw [← integralRepresentationHom_conjugacyClassSumInt rho x]
  exact map_isIntegral_int (integralRepresentationHom rho)
    (IsIntegral.of_finite ℤ (conjugacyClassSumInt x))

/-- Schur's lemma turns a conjugacy-class sum into a scalar, and integrality
of the group-ring element makes that scalar an algebraic integer. -/
theorem exists_integral_scalar_conjugacyClassEnd
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (x : G) :
    ∃ c : k, IsIntegral ℤ c ∧
      conjugacyClassEnd rho x = c • (1 : Module.End k V) := by
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_commute_irreducible rho
    (conjugacyClassEnd rho x) (conjugacyClassEnd_commute rho x)
  refine ⟨c, ?_, hc⟩
  letI : Nontrivial rho.asModule :=
    IsSimpleModule.nontrivial k[G] rho.asModule
  letI : Nontrivial V := inferInstanceAs (Nontrivial rho.asModule)
  have hIntegral : IsIntegral ℤ (c • (1 : Module.End k V)) := by
    rw [← hc]
    exact conjugacyClassEnd_isIntegral rho x
  have hcast : c • (1 : Module.End k V) =
      algebraMap k (Module.End k V) c := by
    simp [Algebra.smul_def]
  rw [hcast] at hIntegral
  exact (isIntegral_algebraMap_iff
    (FaithfulSMul.algebraMap_injective k (Module.End k V))).mp hIntegral

/-- Cardinality of the conjugacy class represented by `x`. -/
def conjugacyClassCard (x : G) : ℕ := by
  classical
  exact (Finset.univ.filter fun y : G ↦ IsConj y x).card

/-- The trace of a conjugacy-class sum is the class cardinality times the
character value. -/
theorem trace_conjugacyClassEnd (rho : Representation k G V) (x : G) :
    LinearMap.trace k V (conjugacyClassEnd rho x) =
      (conjugacyClassCard x : k) * rho.character x := by
  classical
  rw [conjugacyClassEnd]
  simp only [map_sum]
  calc
    (∑ y : G, LinearMap.trace k V
        (if IsConj y x then rho y else 0)) =
        ∑ y : G, if IsConj y x then rho.character x else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : IsConj y x
      · rw [if_pos hy, if_pos hy]
        change rho.character y = rho.character x
        obtain ⟨g, hg⟩ := isConj_iff.mp hy
        rw [← hg, rho.char_conj]
      · rw [if_neg hy, if_neg hy]
        simp
    _ = (conjugacyClassCard x : k) * rho.character x := by
      rw [← Finset.sum_filter]
      simp [conjugacyClassCard, Finset.sum_const, nsmul_eq_mul]

/-- The class cardinality times an irreducible character value, divided by
the character degree, is an algebraic integer. -/
theorem conjugacyClassCard_mul_character_div_finrank_isIntegral
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (x : G) :
    IsIntegral ℤ
      (((conjugacyClassCard x : ℕ) : k) * rho.character x /
        (Module.finrank k V : k)) := by
  obtain ⟨c, hcInt, hc⟩ := exists_integral_scalar_conjugacyClassEnd rho x
  letI : Nontrivial rho.asModule :=
    IsSimpleModule.nontrivial k[G] rho.asModule
  letI : Nontrivial V := inferInstanceAs (Nontrivial rho.asModule)
  have hdNat : Module.finrank k V ≠ 0 := (Module.finrank_pos (R := k) (M := V)).ne'
  have hd : (Module.finrank k V : k) ≠ 0 := Nat.cast_ne_zero.mpr hdNat
  have htrace := congrArg (LinearMap.trace k V) hc
  rw [trace_conjugacyClassEnd rho x] at htrace
  have htrace' :
      (conjugacyClassCard x : k) * rho.character x =
        c * (Module.finrank k V : k) := by
    simpa using htrace
  have heq :
      (conjugacyClassCard x : k) * rho.character x /
          (Module.finrank k V : k) = c :=
    (div_eq_iff hd).mpr htrace'
  rw [heq]
  exact hcInt

/-- A fixed representative of a conjugacy class. -/
def conjugacyClassRepresentative (C : ConjClasses G) : G :=
  (ConjClasses.exists_rep C).choose

@[simp]
theorem mk_conjugacyClassRepresentative (C : ConjClasses G) :
    ConjClasses.mk (conjugacyClassRepresentative C) = C :=
  (ConjClasses.exists_rep C).choose_spec

open scoped Classical in
/-- The fiber of the quotient map over a conjugacy class has the cardinality
computed by `conjugacyClassCard` at the chosen representative. -/
theorem card_conjClasses_mk_fiber (C : ConjClasses G) :
    Fintype.card {g : G // ConjClasses.mk g = C} =
      conjugacyClassCard (conjugacyClassRepresentative C) := by
  classical
  let e : {g : G // ConjClasses.mk g = C} ≃
      {g : G // IsConj g (conjugacyClassRepresentative C)} :=
    Equiv.subtypeEquivProp (funext fun g ↦ propext (by
      constructor
      · intro hg
        exact ConjClasses.mk_eq_mk_iff_isConj.mp
          (hg.trans (mk_conjugacyClassRepresentative C).symm)
      · intro hg
        exact (ConjClasses.mk_eq_mk_iff_isConj.mpr hg).trans
          (mk_conjugacyClassRepresentative C)))
  rw [conjugacyClassCard, ← Fintype.card_subtype]
  exact Fintype.card_congr e

open scoped Classical in
/-- Orthogonality's character sum, regrouped by conjugacy classes. -/
theorem sum_character_mul_inv_eq_sum_conjugacyClasses
    (rho : Representation k G V) :
    (∑ g : G, rho.character g * rho.character g⁻¹) =
      ∑ C : ConjClasses G,
        (conjugacyClassCard (conjugacyClassRepresentative C) : k) *
          rho.character (conjugacyClassRepresentative C) *
            rho.character (conjugacyClassRepresentative C)⁻¹ := by
  classical
  rw [← Fintype.sum_fiberwise ConjClasses.mk
    (fun g : G ↦ rho.character g * rho.character g⁻¹)]
  apply Finset.sum_congr rfl
  intro C _
  calc
    (∑ g : {g : G // ConjClasses.mk g = C},
        rho.character (g : G) * rho.character (g : G)⁻¹) =
        ∑ _g : {g : G // ConjClasses.mk g = C},
          rho.character (conjugacyClassRepresentative C) *
            rho.character (conjugacyClassRepresentative C)⁻¹ := by
      apply Finset.sum_congr rfl
      intro g _
      have hgConj : IsConj (g : G) (conjugacyClassRepresentative C) :=
        ConjClasses.mk_eq_mk_iff_isConj.mp
          (g.property.trans (mk_conjugacyClassRepresentative C).symm)
      obtain ⟨z, hz⟩ := isConj_iff.mp hgConj
      have hchar : rho.character (g : G) =
          rho.character (conjugacyClassRepresentative C) := by
        have h := rho.char_conj (g : G) z
        rw [hz] at h
        exact h.symm
      have hzInv : z * (g : G)⁻¹ * z⁻¹ =
          (conjugacyClassRepresentative C)⁻¹ := by
        calc
          z * (g : G)⁻¹ * z⁻¹ = (z * (g : G) * z⁻¹)⁻¹ := conj_inv.symm
          _ = (conjugacyClassRepresentative C)⁻¹ := congrArg Inv.inv hz
      have hcharInv : rho.character (g : G)⁻¹ =
          rho.character (conjugacyClassRepresentative C)⁻¹ := by
        have h := rho.char_conj (g : G)⁻¹ z
        rw [hzInv] at h
        exact h.symm
      rw [hchar, hcharInv]
    _ = (conjugacyClassCard (conjugacyClassRepresentative C) : k) *
          rho.character (conjugacyClassRepresentative C) *
            rho.character (conjugacyClassRepresentative C)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      change (Fintype.card {g : G // ConjClasses.mk g = C} : k) *
          (rho.character (conjugacyClassRepresentative C) *
            rho.character (conjugacyClassRepresentative C)⁻¹) = _
      rw [card_conjClasses_mk_fiber C]
      ring

/-- If the quotient of two natural numbers is an algebraic integer after
embedding in a characteristic-zero field, then the denominator divides the
numerator. -/
theorem nat_dvd_of_cast_div_isIntegral
    (n d : ℕ) (hd : d ≠ 0)
    (h : IsIntegral ℤ ((n : k) / (d : k))) : d ∣ n := by
  let q : ℚ := (n : ℚ) / (d : ℚ)
  have hcast : (q : k) = (n : k) / (d : k) := by simp [q]
  have hi : IsIntegral ℤ (q : k) := hcast ▸ h
  have hq : IsIntegral ℤ q := IsIntegral.ratCast_iff.mp hi
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  have hden : q.den = 1 := by rw [← hz]; simp
  exact (Rat.den_div_natCast_eq_one_iff n d hd).mp hden

/-- The degree of an irreducible finite-group representation over an
algebraically closed characteristic-zero field divides the group order. -/
theorem irreducibleRepresentation_finrank_dvd_natCard
    (rho : Representation k G V) [Representation.IsIrreducible rho] :
    Module.finrank k V ∣ Nat.card G := by
  classical
  letI : Nontrivial rho.asModule :=
    IsSimpleModule.nontrivial k[G] rho.asModule
  letI : Nontrivial V := inferInstanceAs (Nontrivial rho.asModule)
  have hd : Module.finrank k V ≠ 0 :=
    (Module.finrank_pos (R := k) (M := V)).ne'
  let S : k :=
    ∑ C : ConjClasses G,
      ((conjugacyClassCard (conjugacyClassRepresentative C) : k) *
          rho.character (conjugacyClassRepresentative C) /
            (Module.finrank k V : k)) *
        rho.character (conjugacyClassRepresentative C)⁻¹
  have hSIntegral : IsIntegral ℤ S := by
    dsimp only [S]
    apply IsIntegral.sum
    intro C _
    exact
      (conjugacyClassCard_mul_character_div_finrank_isIntegral rho
        (conjugacyClassRepresentative C)).mul
        (representation_character_isIntegral rho
          (conjugacyClassRepresentative C)⁻¹)
  have hcardCast : (Nat.card G : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero hcardCast
  letI : Nonempty (rho.Equiv rho) := ⟨Representation.Equiv.refl rho⟩
  have horth :
      (Nat.card G : k)⁻¹ *
          ∑ g : G, rho.character g * rho.character g⁻¹ = 1 := by
    simpa only [if_pos (show Nonempty (rho.Equiv rho) from inferInstance)] using
      rho.char_orthonormal rho
  have hsum :
      (∑ g : G, rho.character g * rho.character g⁻¹) =
        (Nat.card G : k) := by
    calc
      _ = (Nat.card G : k) *
          ((Nat.card G : k)⁻¹ *
            ∑ g : G, rho.character g * rho.character g⁻¹) := by
        field_simp
      _ = (Nat.card G : k) := by rw [horth, mul_one]
  have hquot :
      (Nat.card G : k) / (Module.finrank k V : k) = S := by
    calc
      (Nat.card G : k) / (Module.finrank k V : k) =
          (∑ g : G, rho.character g * rho.character g⁻¹) /
            (Module.finrank k V : k) := by rw [hsum]
      _ = (∑ C : ConjClasses G,
            (conjugacyClassCard (conjugacyClassRepresentative C) : k) *
              rho.character (conjugacyClassRepresentative C) *
                rho.character (conjugacyClassRepresentative C)⁻¹) /
            (Module.finrank k V : k) := by
          rw [sum_character_mul_inv_eq_sum_conjugacyClasses rho]
      _ = S := by
        rw [div_eq_mul_inv, Finset.sum_mul]
        dsimp only [S]
        apply Finset.sum_congr rfl
        intro C _
        ring
  apply nat_dvd_of_cast_div_isIntegral (k := k) (Nat.card G)
    (Module.finrank k V) hd
  rw [hquot]
  exact hSIntegral

end

end Submission.OddOrder.MathlibSupport

namespace Submission.OddOrder.PF.IrreducibleCharacter

noncomputable section

open CategoryTheory

universe u v

variable {G : Type u} {k : Type v}
variable [Group G] [Fintype G]
variable [Field k] [IsAlgClosed k] [CharZero k]

/-- The degree of an irreducible character divides the order of its finite
group. -/
theorem finrank_representation_dvd_natCard
    (theta : IrreducibleCharacter G k) :
    Module.finrank k theta.representation ∣ Nat.card G := by
  let V := theta.representation
  let rho := V.ρ
  letI : Simple V := theta.representation_simple
  letI : Representation.IsIrreducible rho := by
    refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
    · refine ⟨⊥, ⊤, fun h ↦ ?_⟩
      apply id_nonzero V
      apply Action.Hom.ext
      apply InducedCategory.hom_ext
      apply ModuleCat.hom_ext
      ext x
      have hx : x = 0 := by
        have hmem : x ∈ (⊥ : Subrepresentation rho).toSubmodule := by
          rw [h]
          exact Submodule.mem_top
        exact hmem
      simp [hx]
    · intro U
      let W : FDRep k G := FDRep.of U.toRepresentation
      let i : W ⟶ V :=
        { hom := InducedCategory.homMk
            (ModuleCat.ofHom U.toSubmodule.subtype)
          comm := fun g ↦ by
            ext x
            rfl }
      let F := forget₂ (FDRep k G) (Rep k G)
      have hFi : Function.Injective (F.map i).hom := by
        intro x y hxy
        exact Subtype.ext hxy
      letI : Mono (F.map i) := (Rep.mono_iff_injective (F.map i)).2 hFi
      letI : Mono i :=
        F.mono_of_mono_map (show Mono (F.map i) from inferInstance)
      by_cases hi : i = 0
      · left
        apply SetLike.ext
        intro x
        constructor
        · intro hx
          let y : W := ⟨x, hx⟩
          have hy := ConcreteCategory.congr_hom hi y
          change x = 0 at hy
          rw [hy]
          exact Submodule.zero_mem _
        · intro hx
          have hx0 : x = 0 := hx
          rw [hx0]
          exact Submodule.zero_mem _
      · right
        haveI : IsIso i := (Simple.mono_isIso_iff_nonzero i).2 hi
        apply SetLike.ext
        intro x
        constructor
        · intro _
          exact Submodule.mem_top
        · intro _
          let y : W := (inv i) x
          have hy := ConcreteCategory.congr_hom (IsIso.inv_hom_id i) x
          change (y : V) = x at hy
          exact hy ▸ y.property
  exact
    Submission.OddOrder.MathlibSupport.irreducibleRepresentation_finrank_dvd_natCard rho

end

end Submission.OddOrder.PF.IrreducibleCharacter
