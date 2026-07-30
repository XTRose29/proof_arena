import Mathlib.LinearAlgebra.Basis.Basic
import Submission.OddOrder.PF.Section01.ClassFunctionSupport
import Submission.OddOrder.PF.Section01.Induction
import Submission.OddOrder.PF.Section01.IrreducibleCharacter

/-!
Restriction to a normal complement, after Peterfalvi (1.3)(a)-(b).

The source proof uses the positive-definite scalar product on complex class
functions.  Our class-function pairing is the equivalent finite-group
bilinear form with inversion in the second argument.  Its nondegeneracy on
functions supported by a normal subgroup is proved below with conjugacy-class
indicators.  This lets the restriction/induction argument retain the source
theorem's arbitrary-basis hypothesis.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

namespace ClassFunction

variable {G : Type u} {k : Type v} [Group G] [Field k]

/-- The indicator of the conjugacy class of `x`, bundled as a class function. -/
def conjugacyIndicator (x : G) : ClassFunction G k := by
  classical
  exact
    { val := fun y ↦ if IsConj y x then 1 else 0
      property := fun z y ↦ by
        have hy : IsConj y (z * y * z⁻¹) :=
          isConj_iff.mpr ⟨z, rfl⟩
        have hiff : IsConj (z * y * z⁻¹) x ↔ IsConj y x :=
          ⟨fun h ↦ hy.trans h, fun h ↦ hy.symm.trans h⟩
        change (if IsConj (z * y * z⁻¹) x then 1 else 0) =
          if IsConj y x then 1 else 0
        exact if_congr hiff rfl rfl }

open scoped Classical in
@[simp]
theorem conjugacyIndicator_apply (x y : G) :
    conjugacyIndicator (k := k) x y = if IsConj y x then 1 else 0 :=
  rfl

/-- A conjugacy-class indicator based at a point of a normal subgroup is
supported on that subgroup. -/
theorem conjugacyIndicator_mem_supportedOn_normal (A : Subgroup G) [A.Normal]
    {x : G} (hx : x ∈ A) :
    conjugacyIndicator (k := k) x ∈ supportedOn (A : Set G) := by
  classical
  rw [mem_supportedOn_iff]
  intro y hy
  rw [conjugacyIndicator_apply]
  split_ifs with hconj
  · exfalso
    apply hy
    obtain ⟨z, hz⟩ := isConj_iff.mp hconj.symm
    rw [← hz]
    exact (inferInstance : A.Normal).conj_mem x hx z
  · rfl

end ClassFunction

section PairingBasics

variable {G : Type u} {k : Type v} [Group G] [Field k] [Fintype G]

/-- The inversion convention makes the class-function pairing symmetric over
the commutative coefficient field. -/
theorem characterPairing_comm (f g : ClassFunction G k) :
    characterPairing f g = characterPairing g f := by
  unfold characterPairing
  congr 1
  symm
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun x ↦ ?_
  simp only [Equiv.inv_apply, inv_inv]
  exact mul_comm _ _

/-- Pairing with a fixed right argument, as a linear functional. -/
def characterPairingRight (g : ClassFunction G k) : ClassFunction G k →ₗ[k] k where
  toFun f := characterPairing f g
  map_add' f₁ f₂ := characterPairing_add_left f₁ f₂ g
  map_smul' a f := by
    change characterPairing (a • f) g = a * characterPairing f g
    exact characterPairing_smul_left a f g

/-- Pairing with a fixed left argument, as a linear functional. -/
def characterPairingLeft (f : ClassFunction G k) : ClassFunction G k →ₗ[k] k where
  toFun g := characterPairing f g
  map_add' g₁ g₂ := characterPairing_add_right f g₁ g₂
  map_smul' a g := by
    change characterPairing f (a • g) = a * characterPairing f g
    exact characterPairing_smul_right a f g

open scoped Classical in
/-- Pairing against the indicator of the inverse conjugacy class isolates the
value at `x`, up to the two nonzero cardinality factors. -/
theorem characterPairing_conjugacyIndicator_inv (f : ClassFunction G k) (x : G) :
    characterPairing (ClassFunction.conjugacyIndicator (k := k) x⁻¹) f =
      (Nat.card G : k)⁻¹ *
        ((Finset.univ.filter fun y : G ↦ IsConj y x⁻¹).card : k) * f x := by
  classical
  have hvalue (y : G) (hy : IsConj y x⁻¹) : f y⁻¹ = f x := by
    obtain ⟨z, hz⟩ := isConj_iff.mp hy
    have hinv : z * y⁻¹ * z⁻¹ = x := by
      calc
        z * y⁻¹ * z⁻¹ = (z * y * z⁻¹)⁻¹ := conj_inv.symm
        _ = (x⁻¹)⁻¹ := congrArg Inv.inv hz
        _ = x := inv_inv x
    calc
      f y⁻¹ = f (z * y⁻¹ * z⁻¹) := (ClassFunction.conj_apply f z y⁻¹).symm
      _ = f x := by rw [hinv]
  have hsum :
    (∑ y : G, ClassFunction.conjugacyIndicator (k := k) x⁻¹ y * f y⁻¹) =
        ∑ y : G, if IsConj y x⁻¹ then f x else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : IsConj y x⁻¹
      · rw [ClassFunction.conjugacyIndicator_apply, if_pos hy, one_mul,
          if_pos hy, hvalue y hy]
      · rw [ClassFunction.conjugacyIndicator_apply, if_neg hy, zero_mul,
          if_neg hy]
  have hsum' :
      (∑ y : G, if IsConj y x⁻¹ then f x else 0) =
        ((Finset.univ.filter fun y : G ↦ IsConj y x⁻¹).card : k) * f x := by
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]
  unfold characterPairing
  rw [hsum, hsum']
  simp only [mul_assoc]

/-- The pairing is nondegenerate on the class functions supported by a normal
subgroup.  This is the algebraic replacement for the norm argument in the
Coq proof of Peterfalvi (1.3)(a). -/
theorem eq_zero_of_mem_supportedOn_normal_of_pairing_eq_zero [CharZero k]
    (A : Subgroup G) [A.Normal] {f : ClassFunction G k}
    (hf : f ∈ ClassFunction.supportedOn (A : Set G))
    (horth : ∀ g ∈ ClassFunction.supportedOn (A : Set G),
      characterPairing g f = 0) :
    f = 0 := by
  classical
  apply ClassFunction.ext
  intro x
  simp only [ClassFunction.zero_apply]
  by_cases hx : x ∈ A
  · have hxinv : x⁻¹ ∈ A := A.inv_mem hx
    let e := ClassFunction.conjugacyIndicator (k := k) x⁻¹
    have he : e ∈ ClassFunction.supportedOn (A : Set G) :=
      ClassFunction.conjugacyIndicator_mem_supportedOn_normal A hxinv
    have hzero := horth e he
    rw [characterPairing_conjugacyIndicator_inv] at hzero
    have hcardG : (Nat.card G : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hclassPos :
        0 < (Finset.univ.filter fun y : G ↦ IsConj y x⁻¹).card := by
      rw [Finset.card_pos]
      exact ⟨x⁻¹, Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsConj.refl _⟩⟩
    have hclass :
        ((Finset.univ.filter fun y : G ↦ IsConj y x⁻¹).card : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr hclassPos.ne'
    exact (mul_eq_zero.mp hzero).resolve_left
      (mul_ne_zero (inv_ne_zero hcardG) hclass)
  · exact ClassFunction.eq_zero_of_mem_supportedOn hf hx

/-- Orthogonality to an arbitrary basis of the functions supported on a
normal subgroup detects support on the complement. -/
theorem mem_supportedOn_compl_iff_pairing_basis_eq_zero [CharZero k]
    (A : Subgroup G) [A.Normal] {β : Type*} [Fintype β]
    (Phi : Module.Basis β k (ClassFunction.supportedOn (A : Set G)))
    (D : ClassFunction G k) :
    D ∈ ClassFunction.supportedOn (A : Set G)ᶜ ↔
      ∀ j, characterPairing (Phi j).val D = 0 := by
  classical
  constructor
  · intro hD j
    apply characterPairing_eq_zero_of_inverseDisjoint_supportedOn
      (hf := (Phi j).property) (hg := hD)
    intro x hxA hxAc
    exact hxAc (A.inv_mem hxA)
  · intro horth
    obtain ⟨fA, hfA, fAc, hfAc, hsum⟩ :=
      ClassFunction.exists_add_supportedOn_compl (A : Set G)
        (IsConjStable.normal A) D
    have hPhi (j : β) :
        characterPairing (Phi j).val fA = 0 := by
      have hcomp : characterPairing (Phi j).val fAc = 0 := by
        apply characterPairing_eq_zero_of_inverseDisjoint_supportedOn
          (hf := (Phi j).property) (hg := hfAc)
        intro x hxA hxAc
        exact hxAc (A.inv_mem hxA)
      have htotal := horth j
      rw [← hsum, characterPairing_add_right, hcomp, add_zero] at htotal
      exact htotal
    have hfAzero : fA = 0 := by
      apply eq_zero_of_mem_supportedOn_normal_of_pairing_eq_zero A hfA
      intro g hg
      let gs : ClassFunction.supportedOn (R := k) (A : Set G) := ⟨g, hg⟩
      have hreprSub :
          ∑ j, (Phi.repr gs j) • Phi j = gs := Phi.sum_repr gs
      have hrepr :
          ∑ j, (Phi.repr gs j) • (Phi j).val = g := by
        have h := congrArg
          (ClassFunction.supportedOn (R := k) (A : Set G)).subtype hreprSub
        simpa only [map_sum, map_smul, Submodule.subtype_apply] using h
      change characterPairingRight fA g = 0
      rw [← hrepr, map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_smul]
      change (Phi.repr gs j) *
        characterPairing (Phi j).val fA = 0
      rw [hPhi, mul_zero]
    rw [hfAzero, zero_add] at hsum
    rw [← hsum]
    exact hfAc

/-- Peterfalvi (1.3)(a), `equiv_restrict_compl`: agreement on a normal
subgroup is equivalent to the coefficient identities obtained by pairing an
arbitrary support basis with irreducible-character expansions and applying
Frobenius reciprocity.

The family `chi` is kept abstract: the proof only uses the displayed finite
expansion, so it applies in particular to the family of irreducible
characters. -/
theorem equiv_restrict_compl [CharZero k]
    (H : Subgroup G) [Fintype H] (A : Subgroup H) [A.Normal]
    {β ι : Type*} [Fintype β] [Fintype ι]
    (Phi : Module.Basis β k (ClassFunction.supportedOn (A : Set H)))
    (chi : ι → ClassFunction H k) (mu : ClassFunction G k) (d : ι → k) :
    Set.EqOn (↑(ClassFunction.restrict H mu) : H → k)
        (↑(∑ i, d i • chi i : ClassFunction H k) : H → k) (A : Set H) ↔
      ∀ j, (∑ i, d i * characterPairing (Phi j).val (chi i)) =
        characterPairing (ClassFunction.induce H (Phi j).val) mu := by
  classical
  let total : ClassFunction H k := ∑ i, d i • chi i
  let D : ClassFunction H k := ClassFunction.restrict H mu - total
  have hpairD (j : β) :
      characterPairing (Phi j).val D =
        characterPairing (Phi j).val (ClassFunction.restrict H mu) -
          ∑ i, d i * characterPairing (Phi j).val (chi i) := by
    change characterPairingLeft (Phi j).val D = _
    rw [show D = ClassFunction.restrict H mu - total by rfl, map_sub]
    change characterPairing (Phi j).val (ClassFunction.restrict H mu) -
      characterPairingLeft (Phi j).val total = _
    rw [show total = ∑ i, d i • chi i by rfl, map_sum]
    simp only [map_smul, smul_eq_mul, characterPairingLeft]
    rfl
  calc
    Set.EqOn (↑(ClassFunction.restrict H mu) : H → k)
        (↑(∑ i, d i • chi i : ClassFunction H k) : H → k) (A : Set H) ↔
        D ∈ ClassFunction.vanishingOn (A : Set H) := by
      simpa only [total, D] using
        (ClassFunction.eqOn_iff_sub_mem_vanishingOn
          (A := (A : Set H)) (ClassFunction.restrict H mu) total)
    _ ↔ D ∈ ClassFunction.supportedOn (A : Set H)ᶜ := by
      rw [ClassFunction.vanishingOn_eq_supportedOn_compl]
    _ ↔ ∀ j, characterPairing (Phi j).val D = 0 :=
      mem_supportedOn_compl_iff_pairing_basis_eq_zero A Phi D
    _ ↔ ∀ j, (∑ i, d i * characterPairing (Phi j).val (chi i)) =
        characterPairing (ClassFunction.induce H (Phi j).val) mu := by
      constructor
      · intro hzero j
        have hreciprocity := ClassFunction.frobeniusReciprocity H (Phi j).val mu
        have hrestrict :
            characterPairing (Phi j).val (ClassFunction.restrict H mu) =
              ∑ i, d i * characterPairing (Phi j).val (chi i) := by
          rw [← sub_eq_zero, ← hpairD]
          exact hzero j
        exact hrestrict.symm.trans hreciprocity.symm
      · intro heq j
        rw [hpairD, sub_eq_zero]
        have hreciprocity := ClassFunction.frobeniusReciprocity H (Phi j).val mu
        exact hreciprocity.symm.trans (heq j).symm

/-- Peterfalvi (1.3)(b), `equiv_restrict_compl_ortho`: an orthonormal ambient
family with the prescribed induction formulas restricts to the original
family on `A`; every ambient class function orthogonal to that family
vanishes on `A`. -/
theorem equiv_restrict_compl_ortho [CharZero k]
    (H : Subgroup G) [Fintype H] (A : Subgroup H) [A.Normal]
    {β ι : Type*} [Fintype β] [Fintype ι] [DecidableEq ι]
    (Phi : Module.Basis β k (ClassFunction.supportedOn (A : Set H)))
    (chi : ι → ClassFunction H k) (mu : ι → ClassFunction G k)
    (horth : ∀ i j, characterPairing (mu i) (mu j) = if i = j then 1 else 0)
    (hinduce : ∀ j, ClassFunction.induce H (Phi j).val =
      ∑ i, characterPairing (Phi j).val (chi i) • mu i) :
    (∀ i, Set.EqOn (↑(ClassFunction.restrict H (mu i)) : H → k)
      (↑(chi i) : H → k) (A : Set H)) ∧
      ∀ nu : ClassFunction G k,
        (∀ i, characterPairing nu (mu i) = 0) →
          ClassFunction.restrict H nu ∈ ClassFunction.vanishingOn (A : Set H) := by
  classical
  constructor
  · intro i
    let d : ι → k := fun q ↦ if q = i then 1 else 0
    have hsumChi : (∑ q, d q • chi q) = chi i := by
      simp [d]
    rw [← hsumChi]
    apply (equiv_restrict_compl H A Phi chi (mu i) d).2
    intro j
    have hpair :
        characterPairing (ClassFunction.induce H (Phi j).val) (mu i) =
          characterPairing (Phi j).val (chi i) := by
      rw [hinduce j]
      change characterPairingRight (mu i)
        (∑ q, characterPairing (Phi j).val (chi q) • mu q) = _
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      change (∑ q, characterPairing (Phi j).val (chi q) *
        characterPairing (mu q) (mu i)) =
          characterPairing (Phi j).val (chi i)
      simp [horth]
    simpa [d] using hpair.symm
  · intro nu hnu
    have hinduceZero (j : β) :
        characterPairing (ClassFunction.induce H (Phi j).val) nu = 0 := by
      rw [hinduce j]
      change characterPairingRight nu
        (∑ i, characterPairing (Phi j).val (chi i) • mu i) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_smul]
      change characterPairing (Phi j).val (chi i) *
        characterPairing (mu i) nu = 0
      have hz : characterPairing (mu i) nu = 0 :=
        (characterPairing_comm (mu i) nu).trans (hnu i)
      rw [hz, mul_zero]
    have heq :
        Set.EqOn (↑(ClassFunction.restrict H nu) : H → k)
          (↑(∑ _i : ι, (0 : k) • chi _i : ClassFunction H k) : H → k)
          (A : Set H) := by
      apply (equiv_restrict_compl H A Phi chi nu (fun _ ↦ 0)).2
      intro j
      simp only [zero_mul, Finset.sum_const_zero]
      exact (hinduceZero j).symm
    rw [ClassFunction.mem_vanishingOn_iff]
    intro x hx
    have := heq hx
    simpa using this

end PairingBasics

end

end Submission.OddOrder.PF
