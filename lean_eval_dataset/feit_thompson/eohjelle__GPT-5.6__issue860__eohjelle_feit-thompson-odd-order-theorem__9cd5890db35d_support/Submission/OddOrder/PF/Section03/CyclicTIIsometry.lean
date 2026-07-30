import Submission.OddOrder.PF.Section01.RestrictionComplementEquivalenceSet
import Submission.OddOrder.PF.Section03.CyclicTIIsometryBasis
import Submission.OddOrder.PF.Section03.IrreducibleCharacterBasis

/-!
# The cyclic-TI character isometry

This file ports Peterfalvi (3.2)(a)--(e).  The orthonormal rectangle from
`CyclicTIIsometryBasis` determines a linear map on all class functions by its
values on irreducible characters.  The same construction over `ℤ` gives the
map on virtual characters, so preservation of integrality is part of the
data rather than a separate predicate.

The last part of the file transports the cyclic-TI support basis to the
literal subgroup copy `W.subgroupOf G`.  This is the only representation in
which Mathlib's induction and restriction operators can be applied.  The
public statements transport the result back to the original type `W`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {G W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance cyclicTIIsometryInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private def characterPairingBilinear
    {H : Type u} [Group H] [Fintype H] :
    ClassFunction H k →ₗ[k] ClassFunction H k →ₗ[k] k where
  toFun f := characterPairingLeft f
  map_add' f g := by
    ext z
    exact characterPairing_add_left f g z
  map_smul' a f := by
    ext z
    exact characterPairing_smul_left a f z

private def pullbackCharacterPairing
    {A B : Type u} [Group A] [Group B] [Fintype A] [Fintype B]
    (L : ClassFunction A k →ₗ[k] ClassFunction B k) :
    ClassFunction A k →ₗ[k] ClassFunction A k →ₗ[k] k where
  toFun f := (characterPairingLeft (L f)).comp L
  map_add' f g := by
    ext z
    change characterPairing (L (f + g)) (L z) =
      characterPairing (L f) (L z) + characterPairing (L g) (L z)
    rw [map_add, characterPairing_add_left]
  map_smul' a f := by
    ext z
    change characterPairing (L (a • f)) (L z) =
      a • characterPairing (L f) (L z)
    rw [map_smul, characterPairing_smul_left]
    rfl

namespace CyclicTIIsometryBasisData

variable {h : CyclicTIHypothesis G W W₁ W₂ defW}

/-- The virtual character assigned to an irreducible character of `W` by
the orthonormal rectangle. -/
def imageIrreducible
    (data : CyclicTIIsometryBasisData (k := k) h)
    (chi : IrreducibleCharacter W k) : VirtualCharacter G k :=
  let p := IrreducibleCharacter.cyclicTICharacterIndex defW chi
  data.xi p.1 p.2

@[simp]
theorem imageIrreducible_cyclicTICharacter
    (data : CyclicTIIsometryBasisData (k := k) h)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    data.imageIrreducible
        (IrreducibleCharacter.cyclicTICharacter defW i j) =
      data.xi i j := by
  simp [imageIrreducible]

@[simp]
theorem imageIrreducible_trivial
    (data : CyclicTIIsometryBasisData (k := k) h) :
    data.imageIrreducible
        (IrreducibleCharacter.trivial : IrreducibleCharacter W k) =
      ambientTrivialVirtualCharacter := by
  rw [← IrreducibleCharacter.cyclicTICharacter_trivial defW,
    imageIrreducible_cyclicTICharacter, data.xi_trivial_trivial]

/-- The images of the irreducible characters of `W` form an orthonormal
family of class functions on `G`. -/
theorem characterPairing_imageIrreducible
    (data : CyclicTIIsometryBasisData (k := k) h)
    (chi psi : IrreducibleCharacter W k) :
    characterPairing
        (VirtualCharacter.realize (data.imageIrreducible chi))
        (VirtualCharacter.realize (data.imageIrreducible psi)) =
      if chi = psi then 1 else 0 := by
  let p := IrreducibleCharacter.cyclicTICharacterIndex defW chi
  let q := IrreducibleCharacter.cyclicTICharacterIndex defW psi
  have hpq : p = q ↔ chi = psi :=
    (IrreducibleCharacter.cyclicTICharacterEquiv defW).symm.injective.eq_iff
  simpa only [imageIrreducible, p, q, hpq] using
    data.characterPairing_xi p.1 q.1 p.2 q.2

/-- Extend the image of irreducibles linearly to all class functions. -/
def classFunctionMap
    (data : CyclicTIIsometryBasisData (k := k) h) :
    ClassFunction W k →ₗ[k] ClassFunction G k :=
  (Finsupp.linearCombination k fun chi : IrreducibleCharacter W k ↦
      VirtualCharacter.realize (data.imageIrreducible chi)).comp
    (ClassFunction.irreducibleCharacterBasis
      (G := W) (k := k)).repr.toLinearMap

@[simp]
theorem classFunctionMap_irreducible
    (data : CyclicTIIsometryBasisData (k := k) h)
    (chi : IrreducibleCharacter W k) :
    data.classFunctionMap (chi : ClassFunction W k) =
      VirtualCharacter.realize (data.imageIrreducible chi) := by
  rw [← ClassFunction.irreducibleCharacterBasis_apply
    (G := W) (k := k) chi]
  change
    (Finsupp.linearCombination k fun chi : IrreducibleCharacter W k ↦
      VirtualCharacter.realize (data.imageIrreducible chi))
        ((ClassFunction.irreducibleCharacterBasis
          (G := W) (k := k)).repr
            (ClassFunction.irreducibleCharacterBasis
              (G := W) (k := k) chi)) = _
  rw [Module.Basis.repr_self, Finsupp.linearCombination_single, one_smul]

/-- Integral extension of the same assignment. -/
def virtualMap
    (data : CyclicTIIsometryBasisData (k := k) h) :
    VirtualCharacter W k →+ VirtualCharacter G k :=
  (Finsupp.linearCombination ℤ fun chi : IrreducibleCharacter W k ↦
      data.imageIrreducible chi).toAddMonoidHom

@[simp]
theorem virtualMap_single
    (data : CyclicTIIsometryBasisData (k := k) h)
    (chi : IrreducibleCharacter W k) (z : ℤ) :
    data.virtualMap (Finsupp.single chi z) =
      z • data.imageIrreducible chi := by
  simp [virtualMap]

/-- The integral and linear extensions agree after realization. -/
theorem realize_virtualMap
    (data : CyclicTIIsometryBasisData (k := k) h)
    (z : VirtualCharacter W k) :
    VirtualCharacter.realize (data.virtualMap z) =
      data.classFunctionMap (VirtualCharacter.realize z) := by
  induction z using Finsupp.induction with
  | zero => simp [virtualMap, classFunctionMap]
  | single_add chi n z hchi hn ih =>
      have hsingleOne :
          VirtualCharacter.realize
              (data.virtualMap
                (Finsupp.single chi 1 : VirtualCharacter W k)) =
            data.classFunctionMap
              (VirtualCharacter.realize
                (Finsupp.single chi 1 : VirtualCharacter W k)) := by
        rw [data.virtualMap_single]
        simpa only [one_zsmul, VirtualCharacter.realize_single,
          Int.cast_one, one_smul] using
            (data.classFunctionMap_irreducible chi).symm
      have hsingle :
          VirtualCharacter.realize
              (data.virtualMap
                (Finsupp.single chi n : VirtualCharacter W k)) =
            data.classFunctionMap
              (VirtualCharacter.realize
                (Finsupp.single chi n : VirtualCharacter W k)) := by
        have hrewrite :
            (Finsupp.single chi n : VirtualCharacter W k) =
              n • (Finsupp.single chi 1 : VirtualCharacter W k) := by
          simp
        rw [hrewrite]
        simpa only [map_zsmul] using congrArg (fun x ↦ n • x) hsingleOne
      calc
        VirtualCharacter.realize
            (data.virtualMap (Finsupp.single chi n + z)) =
          VirtualCharacter.realize
              (data.virtualMap (Finsupp.single chi n)) +
            VirtualCharacter.realize (data.virtualMap z) := by
              rw [map_add, map_add]
        _ = data.classFunctionMap
              (VirtualCharacter.realize (Finsupp.single chi n)) +
            data.classFunctionMap (VirtualCharacter.realize z) := by
              rw [hsingle, ih]
        _ = data.classFunctionMap
            (VirtualCharacter.realize (Finsupp.single chi n) +
              VirtualCharacter.realize z) := by rw [map_add]
        _ = data.classFunctionMap
            (VirtualCharacter.realize (Finsupp.single chi n + z)) := by
              exact congrArg data.classFunctionMap
                (VirtualCharacter.realize_add
                  (Finsupp.single chi n) z).symm

/-- The linear extension preserves the character pairing on arbitrary class
functions, not just on virtual characters. -/
theorem classFunctionMap_pairing
    (data : CyclicTIIsometryBasisData (k := k) h)
    (phi psi : ClassFunction W k) :
    characterPairing (data.classFunctionMap phi)
        (data.classFunctionMap psi) =
      characterPairing phi psi := by
  let b := ClassFunction.irreducibleCharacterBasis (G := W) (k := k)
  have hbilinear :
      pullbackCharacterPairing data.classFunctionMap =
        characterPairingBilinear (H := W) (k := k) := by
    apply b.ext
    intro chi
    apply b.ext
    intro psi
    have hbchi : b chi = (chi : ClassFunction W k) := by simp [b]
    have hbpsi : b psi = (psi : ClassFunction W k) := by simp [b]
    change characterPairing
      (data.classFunctionMap (b chi))
      (data.classFunctionMap (b psi)) =
        characterPairing (b chi) (b psi)
    rw [hbchi, hbpsi, data.classFunctionMap_irreducible,
      data.classFunctionMap_irreducible,
      data.characterPairing_imageIrreducible,
      IrreducibleCharacter.characterPairing_eq_ite]
  exact DFunLike.congr_fun
    (DFunLike.congr_fun hbilinear phi) psi

@[simp]
theorem classFunctionMap_trivial
    (data : CyclicTIIsometryBasisData (k := k) h) :
    data.classFunctionMap
        ((IrreducibleCharacter.trivial : IrreducibleCharacter W k) :
          ClassFunction W k) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
        ClassFunction G k) := by
  rw [classFunctionMap_irreducible, imageIrreducible_trivial]
  simp [ambientTrivialVirtualCharacter]

@[simp]
theorem virtualMap_cyclicTIVirtualCharacter
    (data : CyclicTIIsometryBasisData (k := k) h)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    data.virtualMap (cyclicTIVirtualCharacter defW i j) =
      ambientTrivialVirtualCharacter -
        data.xi i IrreducibleCharacter.trivial -
        data.xi IrreducibleCharacter.trivial j + data.xi i j := by
  simp [cyclicTIVirtualCharacter, imageIrreducible_cyclicTICharacter,
    data.xi_trivial_trivial]

/-- On each cyclic-TI support basis vector, the constructed map is ordinary
induction. -/
theorem classFunctionMap_cyclicTIVirtualCharacter
    (data : CyclicTIIsometryBasisData (k := k) h)
    {i : IrreducibleCharacter W₁ k}
    {j : IrreducibleCharacter W₂ k}
    (hi : i ≠ IrreducibleCharacter.trivial)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    data.classFunctionMap
        (VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j)) =
      h.induceClassFunction
        (VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j)) := by
  rw [← data.realize_virtualMap]
  rw [data.virtualMap_cyclicTIVirtualCharacter i j,
    ← data.induce_eq i j hi hj]
  exact h.realize_induceVirtualCharacter
    (cyclicTIVirtualCharacter defW i j)

/-- The map agrees with induction on the whole subspace supported on the
cyclic-TI set. -/
theorem classFunctionMap_induce_of_supported
    (data : CyclicTIIsometryBasisData (k := k) h)
    (phi : ClassFunction W k)
    (hphi : phi ∈
      ClassFunction.supportedOn (cyclicTISetInW W W₁ W₂)) :
    data.classFunctionMap phi = h.induceClassFunction phi := by
  let phiV : ClassFunction.supportedOn (R := k)
      (cyclicTISetInW W W₁ W₂) := ⟨phi, hphi⟩
  have hrepr := h.cyclicTIVirtualBasis.sum_repr phiV
  have hreprVal :
      (∑ p, (h.cyclicTIVirtualBasis.repr phiV p) •
          (h.cyclicTIVirtualBasis p : ClassFunction W k)) = phi := by
    have := congrArg
      (ClassFunction.supportedOn (R := k)
        (cyclicTISetInW W W₁ W₂)).subtype hrepr
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using this
  rw [← hreprVal, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [map_smul, map_smul]
  congr 1
  rw [h.cyclicTIVirtualBasis_val p]
  exact data.classFunctionMap_cyclicTIVirtualCharacter p.1.2 p.2.2

end CyclicTIIsometryBasisData

/-- The complete data of Peterfalvi's cyclic-TI isometry. -/
structure CyclicTIIsometryData
    (h : CyclicTIHypothesis G W W₁ W₂ defW) where
  basisData : CyclicTIIsometryBasisData (k := k) h
  linearMap : ClassFunction W k →ₗ[k] ClassFunction G k
  virtualMap : VirtualCharacter W k →+ VirtualCharacter G k
  realize_virtualMap : ∀ z,
    VirtualCharacter.realize (virtualMap z) =
      linearMap (VirtualCharacter.realize z)
  pairing : ∀ phi psi,
    characterPairing (linearMap phi) (linearMap psi) =
      characterPairing phi psi
  map_trivial :
    linearMap
        ((IrreducibleCharacter.trivial : IrreducibleCharacter W k) :
          ClassFunction W k) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
        ClassFunction G k)
  induce_supported : ∀ phi,
    phi ∈ ClassFunction.supportedOn (cyclicTISetInW W W₁ W₂) →
      linearMap phi = h.induceClassFunction phi

namespace CyclicTIIsometryData

/-- The integral image of an irreducible source character has squared norm
one. -/
theorem virtualMap_irreducible_normSq
    {h : CyclicTIHypothesis G W W₁ W₂ defW}
    (iso : CyclicTIIsometryData (k := k) h)
    (chi : IrreducibleCharacter W k) :
    normSq (iso.virtualMap (Finsupp.single chi 1)) = 1 := by
  have hpair :
      characterPairing
          (VirtualCharacter.realize
            (iso.virtualMap (Finsupp.single chi 1)))
          (VirtualCharacter.realize
            (iso.virtualMap (Finsupp.single chi 1))) = 1 := by
    rw [iso.realize_virtualMap, iso.pairing]
    simpa using
      (IrreducibleCharacter.characterPairing_self chi)
  rw [VirtualCharacter.characterPairing_realize] at hpair
  exact Int.cast_injective (α := k) (by simpa [normSq] using hpair)

/-- Every irreducible source character is sent to a signed irreducible
character of `G`.  This is Coq's `cycTIiso_dirr` in explicit Lean form. -/
theorem exists_signed_irreducible_image
    {h : CyclicTIHypothesis G W W₁ W₂ defW}
    (iso : CyclicTIIsometryData (k := k) h)
    (chi : IrreducibleCharacter W k) :
    ∃ (psi : IrreducibleCharacter G k) (epsilon : ℤ),
      IsSign epsilon ∧
      iso.linearMap (chi : ClassFunction W k) =
        (epsilon : k) • (psi : ClassFunction G k) := by
  let z := iso.virtualMap (Finsupp.single chi 1)
  obtain ⟨psi, epsilon, hepsilon, hz⟩ :=
    eq_signed_single_of_normSq_eq_one z
      (iso.virtualMap_irreducible_normSq chi)
  refine ⟨psi, epsilon, hepsilon, ?_⟩
  calc
    iso.linearMap (chi : ClassFunction W k) =
        iso.linearMap
          (VirtualCharacter.realize
            (Finsupp.single chi 1 : VirtualCharacter W k)) := by simp
    _ = VirtualCharacter.realize
          (iso.virtualMap
            (Finsupp.single chi 1 : VirtualCharacter W k)) :=
      (iso.realize_virtualMap _).symm
    _ = VirtualCharacter.realize z := rfl
    _ = (epsilon : k) • (psi : ClassFunction G k) := by
      rw [hz, VirtualCharacter.realize_single]

end CyclicTIIsometryData

namespace CyclicTIHypothesis

/-- Construct the full cyclic-TI isometry data from the orthonormal
rectangle. -/
def cyclicTIIsometryData
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    CyclicTIIsometryData (k := k) h := by
  let basis := h.cyclicTIIsometryBasisData (k := k)
  exact
    { basisData := basis
      linearMap := basis.classFunctionMap
      virtualMap := basis.virtualMap
      realize_virtualMap := basis.realize_virtualMap
      pairing := basis.classFunctionMap_pairing
      map_trivial := basis.classFunctionMap_trivial
      induce_supported := basis.classFunctionMap_induce_of_supported }

/-- Peterfalvi's linear cyclic-TI isometry. -/
def cyclicTIIsometry
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    ClassFunction W k →ₗ[k] ClassFunction G k :=
  (h.cyclicTIIsometryData (k := k)).linearMap

/-- Integral form of the cyclic-TI isometry. -/
def cyclicTIIsometryVirtual
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    VirtualCharacter W k →+ VirtualCharacter G k :=
  (h.cyclicTIIsometryData (k := k)).virtualMap

theorem realize_cyclicTIIsometryVirtual
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (z : VirtualCharacter W k) :
    VirtualCharacter.realize (h.cyclicTIIsometryVirtual z) =
      h.cyclicTIIsometry (VirtualCharacter.realize z) :=
  (h.cyclicTIIsometryData (k := k)).realize_virtualMap z

/-- Peterfalvi (3.2)(a): preservation of the character pairing. -/
theorem cyclicTIIsometry_pairing
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (phi psi : ClassFunction W k) :
    characterPairing (h.cyclicTIIsometry phi)
        (h.cyclicTIIsometry psi) =
      characterPairing phi psi :=
  (h.cyclicTIIsometryData (k := k)).pairing phi psi

/-- Peterfalvi (3.2)(b): the trivial character is fixed. -/
@[simp]
theorem cyclicTIIsometry_trivial
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    h.cyclicTIIsometry
        ((IrreducibleCharacter.trivial : IrreducibleCharacter W k) :
          ClassFunction W k) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
        ClassFunction G k) :=
  (h.cyclicTIIsometryData (k := k)).map_trivial

/-- Peterfalvi (3.2)(c): on functions supported on the cyclic-TI set, the
isometry is induction. -/
theorem cyclicTIIsometry_induce
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (phi : ClassFunction W k)
    (hphi : phi ∈
      ClassFunction.supportedOn (cyclicTISetInW W W₁ W₂)) :
    h.cyclicTIIsometry phi = h.induceClassFunction phi :=
  (h.cyclicTIIsometryData (k := k)).induce_supported phi hphi

/-- Value of the linear isometry on an irreducible character. -/
@[simp]
theorem cyclicTIIsometry_irreducible
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    h.cyclicTIIsometry
        (IrreducibleCharacter.cyclicTICharacter defW i j :
          ClassFunction W k) =
      VirtualCharacter.realize
        ((h.cyclicTIIsometryData (k := k)).basisData.xi i j) := by
  simpa [cyclicTIIsometry, cyclicTIIsometryData] using
    CyclicTIIsometryBasisData.classFunctionMap_irreducible
      (h.cyclicTIIsometryData (k := k)).basisData
      (IrreducibleCharacter.cyclicTICharacter defW i j)

/-- Value of the integral isometry on an irreducible character. -/
@[simp]
theorem cyclicTIIsometryVirtual_irreducible
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    h.cyclicTIIsometryVirtual
        (Finsupp.single
          (IrreducibleCharacter.cyclicTICharacter defW i j) 1) =
      (h.cyclicTIIsometryData (k := k)).basisData.xi i j := by
  simp [cyclicTIIsometryVirtual, cyclicTIIsometryData]

/-! ## The canonical subgroup-copy adapter -/

/-- The cyclic-TI set transported to the literal copy of `W` inside `G`. -/
def cyclicTISetInSubgroupOf
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    Set (W.subgroupOf G) :=
  (Subgroup.subgroupOfEquivOfLe h.le_group) ⁻¹'
    cyclicTISetInW W W₁ W₂

theorem cyclicTISetInSubgroupOf_conjStable
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    IsConjStable h.cyclicTISetInSubgroupOf := by
  intro x g
  change
    Subgroup.subgroupOfEquivOfLe h.le_group (x * g * x⁻¹) ∈
        cyclicTISetInW W W₁ W₂ ↔
      Subgroup.subgroupOfEquivOfLe h.le_group g ∈
        cyclicTISetInW W W₁ W₂
  simp only [map_mul, map_inv]
  exact h.set_conjStable
    (Subgroup.subgroupOfEquivOfLe h.le_group x)
    (Subgroup.subgroupOfEquivOfLe h.le_group g)

theorem cyclicTISetInSubgroupOf_invStable
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    IsInvStable h.cyclicTISetInSubgroupOf := by
  intro x
  change
    Subgroup.subgroupOfEquivOfLe h.le_group x⁻¹ ∈
        cyclicTISetInW W W₁ W₂ ↔
      Subgroup.subgroupOfEquivOfLe h.le_group x ∈
        cyclicTISetInW W W₁ W₂
  rw [map_inv]
  exact h.set_invStable
    (Subgroup.subgroupOfEquivOfLe h.le_group x)

/-- Transport class functions between `W` and its literal subgroup copy in
`G`. -/
def classFunctionSubgroupOfEquiv
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    ClassFunction W k ≃ₗ[k] ClassFunction (W.subgroupOf G) k where
  toLinearMap := ClassFunction.toSubgroupOf W G h.le_group
  invFun := ClassFunction.comap
    (Subgroup.subgroupOfEquivOfLe h.le_group).symm.toMonoidHom
  left_inv f := by
    ext w
    simp [ClassFunction.toSubgroupOf_apply, ClassFunction.comap_apply]
  right_inv f := by
    ext w
    simp [ClassFunction.toSubgroupOf_apply, ClassFunction.comap_apply]

@[simp]
theorem classFunctionSubgroupOfEquiv_apply
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (f : ClassFunction W k) (w : W.subgroupOf G) :
    h.classFunctionSubgroupOfEquiv f w =
      f (Subgroup.subgroupOfEquivOfLe h.le_group w) :=
  rfl

/-- The subgroup-copy transport preserves the character pairing. -/
theorem characterPairing_classFunctionSubgroupOfEquiv
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (f g : ClassFunction W k) :
    characterPairing (h.classFunctionSubgroupOfEquiv f)
        (h.classFunctionSubgroupOfEquiv g) =
      characterPairing f g := by
  let H : Subgroup G := W.subgroupOf G
  let e : H ≃* W := Subgroup.subgroupOfEquivOfLe h.le_group
  have hcard : Nat.card H = Nat.card W := Nat.card_congr e.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv e.toEquiv
  intro x
  rfl

/-- Transport the support subspace, including its support proof, to the
literal subgroup copy. -/
def cyclicTISupportedSubgroupOfEquiv
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    ClassFunction.supportedOn (R := k) (cyclicTISetInW W W₁ W₂) ≃ₗ[k]
      ClassFunction.supportedOn (R := k) h.cyclicTISetInSubgroupOf where
  toFun f :=
    ⟨h.classFunctionSubgroupOfEquiv f, by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      exact f.property
        (Subgroup.subgroupOfEquivOfLe h.le_group x) hx⟩
  invFun f :=
    ⟨h.classFunctionSubgroupOfEquiv.symm f, by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      apply f.property
      simpa [cyclicTISetInSubgroupOf] using hx⟩
  left_inv f := by
    apply Subtype.ext
    exact h.classFunctionSubgroupOfEquiv.left_inv f.val
  right_inv f := by
    apply Subtype.ext
    exact h.classFunctionSubgroupOfEquiv.right_inv f.val
  map_add' f g := by
    apply Subtype.ext
    simp
  map_smul' a f := by
    apply Subtype.ext
    simp

/-- The cyclic-TI support basis in the literal subgroup copy. -/
def cyclicTIVirtualBasisSubgroupOf
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    Module.Basis (CyclicTINontrivialIndex W₁ W₂ k) k
      (ClassFunction.supportedOn (R := k) h.cyclicTISetInSubgroupOf) :=
  h.cyclicTIVirtualBasis.map h.cyclicTISupportedSubgroupOfEquiv

@[simp]
theorem cyclicTIVirtualBasisSubgroupOf_val
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    (h.cyclicTIVirtualBasisSubgroupOf p :
        ClassFunction (W.subgroupOf G) k) =
      h.classFunctionSubgroupOfEquiv
        (VirtualCharacter.realize
          (cyclicTIVirtualCharacter defW p.1.1 p.2.1)) := by
  simp [cyclicTIVirtualBasisSubgroupOf,
    cyclicTISupportedSubgroupOfEquiv]

end CyclicTIHypothesis

namespace CyclicTIIsometryData

private theorem restrict_and_vanish
    {h : CyclicTIHypothesis G W W₁ W₂ defW}
    (iso : CyclicTIIsometryData (k := k) h) :
    (∀ chi : IrreducibleCharacter W k,
      Set.EqOn
        (↑(ClassFunction.restrict (W.subgroupOf G)
          (iso.linearMap (chi : ClassFunction W k))) :
            W.subgroupOf G → k)
        (↑(h.classFunctionSubgroupOfEquiv
          (chi : ClassFunction W k)) : W.subgroupOf G → k)
        h.cyclicTISetInSubgroupOf) ∧
    ∀ nu : ClassFunction G k,
      (∀ chi : IrreducibleCharacter W k,
        characterPairing nu
          (iso.linearMap (chi : ClassFunction W k)) = 0) →
      ClassFunction.restrict (W.subgroupOf G) nu ∈
        ClassFunction.vanishingOn h.cyclicTISetInSubgroupOf := by
  let chi : IrreducibleCharacter W k →
      ClassFunction (W.subgroupOf G) k :=
    fun q ↦ h.classFunctionSubgroupOfEquiv (q : ClassFunction W k)
  let mu : IrreducibleCharacter W k → ClassFunction G k :=
    fun q ↦ iso.linearMap (q : ClassFunction W k)
  have horth (q r : IrreducibleCharacter W k) :
      characterPairing (mu q) (mu r) = if q = r then 1 else 0 := by
    rw [iso.pairing]
    exact IrreducibleCharacter.characterPairing_eq_ite q r
  have hinduce (p : CyclicTINontrivialIndex W₁ W₂ k) :
      ClassFunction.induce (W.subgroupOf G)
          (h.cyclicTIVirtualBasisSubgroupOf p).val =
        ∑ q, characterPairing
            (h.cyclicTIVirtualBasisSubgroupOf p).val (chi q) • mu q := by
    let phi : ClassFunction W k :=
      VirtualCharacter.realize
        (cyclicTIVirtualCharacter defW p.1.1 p.2.1)
    have hval :
        (h.cyclicTIVirtualBasisSubgroupOf p).val =
          h.classFunctionSubgroupOfEquiv phi := by
      exact h.cyclicTIVirtualBasisSubgroupOf_val p
    have hexpand :
        (∑ q : IrreducibleCharacter W k,
          characterPairing (q : ClassFunction W k) phi •
            (q : ClassFunction W k)) = phi :=
      ClassFunction.sum_irreducibleCharacterBasis_eq phi
    calc
      ClassFunction.induce (W.subgroupOf G)
          (h.cyclicTIVirtualBasisSubgroupOf p).val =
          h.induceClassFunction phi := by
        rw [hval]
        rfl
      _ = iso.linearMap phi := by
        symm
        exact iso.induce_supported phi
          (h.cyclicTIVirtualCharacter_mem_supportedOn p.1.1 p.2.1)
      _ = iso.linearMap
          (∑ q : IrreducibleCharacter W k,
            characterPairing (q : ClassFunction W k) phi •
              (q : ClassFunction W k)) := by rw [hexpand]
      _ = ∑ q : IrreducibleCharacter W k,
          characterPairing (q : ClassFunction W k) phi • mu q := by
        simp only [map_sum, map_smul, mu]
      _ = ∑ q : IrreducibleCharacter W k,
          characterPairing
              (h.cyclicTIVirtualBasisSubgroupOf p).val (chi q) •
            mu q := by
        apply Finset.sum_congr rfl
        intro q hq
        congr 1
        rw [hval]
        change characterPairing (q : ClassFunction W k) phi =
          characterPairing
            (h.classFunctionSubgroupOfEquiv phi)
            (h.classFunctionSubgroupOfEquiv
              (q : ClassFunction W k))
        rw [h.characterPairing_classFunctionSubgroupOfEquiv]
        exact characterPairing_comm _ _
  exact equiv_restrict_compl_ortho_set
    (W.subgroupOf G) h.cyclicTISetInSubgroupOf
    h.cyclicTISetInSubgroupOf_conjStable
    h.cyclicTISetInSubgroupOf_invStable
    h.cyclicTIVirtualBasisSubgroupOf chi mu horth hinduce

/-- Peterfalvi (3.2)(d), for any data satisfying the cyclic-TI isometry
specification: restriction agrees with the original class function on the
cyclic-TI set. -/
theorem restrict
    {h : CyclicTIHypothesis G W W₁ W₂ defW}
    (iso : CyclicTIIsometryData (k := k) h)
    (phi : ClassFunction W k) :
    Set.EqOn
      (fun w : W ↦ iso.linearMap phi
        ⟨w, h.le_group w.property⟩)
      (↑phi : W → k)
      (cyclicTISetInW W W₁ W₂) := by
  have hirr := iso.restrict_and_vanish.1
  rw [← ClassFunction.sum_irreducibleCharacterBasis_eq phi]
  intro w hw
  simp only [map_sum, map_smul, ClassFunction.finset_sum_apply,
    ClassFunction.smul_apply]
  apply Finset.sum_congr rfl
  intro chi hchi
  congr 1
  exact hirr chi (show
    (⟨⟨w, h.le_group w.property⟩, w.property⟩ : W.subgroupOf G) ∈
      h.cyclicTISetInSubgroupOf by exact hw)

/-- Peterfalvi (3.2)(e), for arbitrary cyclic-TI isometry data: a class
function orthogonal to its image vanishes on the cyclic-TI set. -/
theorem orthogonal_vanish
    {h : CyclicTIHypothesis G W W₁ W₂ defW}
    (iso : CyclicTIIsometryData (k := k) h)
    (nu : ClassFunction G k)
    (horth : ∀ chi : IrreducibleCharacter W k,
      characterPairing nu
        (iso.linearMap (chi : ClassFunction W k)) = 0) :
    Set.EqOn
      (fun w : W ↦ nu ⟨w, h.le_group w.property⟩)
      0 (cyclicTISetInW W W₁ W₂) := by
  have hvanish := iso.restrict_and_vanish.2 nu horth
  intro w hw
  exact ClassFunction.eq_zero_of_mem_vanishingOn hvanish
    (show
      (⟨⟨w, h.le_group w.property⟩, w.property⟩ : W.subgroupOf G) ∈
        h.cyclicTISetInSubgroupOf by exact hw)

end CyclicTIIsometryData

namespace CyclicTIHypothesis

/-- Canonical form of Peterfalvi (3.2)(d). -/
theorem cyclicTIIsometry_restrict
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (phi : ClassFunction W k) :
    Set.EqOn
      (fun w : W ↦ h.cyclicTIIsometry phi
        ⟨w, h.le_group w.property⟩)
      (↑phi : W → k)
      (cyclicTISetInW W W₁ W₂) :=
  (h.cyclicTIIsometryData (k := k)).restrict phi

/-- Canonical form of Peterfalvi (3.2)(e). -/
theorem orthogonal_cyclicTIIsometry_vanish
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (nu : ClassFunction G k)
    (horth : ∀ chi : IrreducibleCharacter W k,
      characterPairing nu
        (h.cyclicTIIsometry (chi : ClassFunction W k)) = 0) :
    Set.EqOn
      (fun w : W ↦ nu ⟨w, h.le_group w.property⟩)
      0 (cyclicTISetInW W W₁ W₂) :=
  (h.cyclicTIIsometryData (k := k)).orthogonal_vanish nu horth

end CyclicTIHypothesis

end

end Submission.OddOrder.PF
