import Submission.OddOrder.MathlibSupport.WielandtFixpoint
import Submission.OddOrder.MathlibSupport.MinimalNormalUnder
import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Submission.OddOrder.MathlibSupport.FrattiniQuotientAutomorphism
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# The homocyclic semidirect cover in Wielandt's fixed-point argument

This file ports `iso_quotient_homocyclic_sdprod`, the second large lemma of
`wielandt_fixpoint.v`.  The source constructs the cover inside a regular
matrix representation.  Here we use the equivalent group-extension
description.  A free homocyclic group `W` of exponent `p ^ m` has Frattini
quotient isomorphic to the elementary abelian kernel `V`.  Automorphisms of
that quotient lift, and the kernel of the quotient map on automorphism
groups is a `p`-group.  Pulling this extension back along the conjugation
action of `G` and applying Schur--Zassenhaus produces the required actor
`G₁` and the semidirect cover.

The public package deliberately retains the subgroups `W` and `G₁` of an
ambient source group `D`, as in the Coq statement.  It additionally records
the exponent-`m` coordinates and the actor isomorphism used immediately by
the trace calculation in `solvable_Wielandt_fixpoint`.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative Matrix

universe u v

/-- Source-faithful data supplied by Coq's
`is_iso_quotient_homocyclic_sdprod` variant. -/
structure IsoQuotientHomocyclicSdprod
    {E : Type u} [Group E] (p m : ℕ) (V G : Subgroup E) where
  /-- Ambient group of the covering semidirect product. -/
  D : Type u
  [groupD : Group D]
  [finiteD : Finite D]
  /-- Homocyclic normal factor. -/
  W : Subgroup D
  [commutative_W : IsMulCommutative W]
  /-- Lifted copy of the actor. -/
  G₁ : Subgroup D
  normal_W : W.Normal
  complement : W.IsComplement' G₁
  /-- Quotient map back to the original ambient group. -/
  f : D →* E
  homocyclic : IsHomocyclicPGroup p W
  /-- The stronger, exponent-specific form needed by the matrix argument. -/
  homocyclic_at_m :
    ∃ d : ℕ, Nonempty (W ≃* (Fin d → Multiplicative (ZMod (p ^ m))))
  pow_eq_one : ∀ w : W, w ^ (p ^ m) = 1
  exponent_W : Monoid.exponent W = p ^ m
  card_W : Nat.card W = Nat.card V ^ m
  ker_f : f.ker = (abelianPowerSubgroup p 1 W).map W.subtype
  map_W : W.map f = V
  map_G₁ : G₁.map f = G
  /-- Restriction of `f` identifies the lifted actor with `G`. -/
  actorEquiv : G₁ ≃* G
  actorEquiv_apply :
    ∀ g : G₁, G.subtype (actorEquiv g) = f (G₁.subtype g)

namespace IsoQuotientHomocyclicSdprod

attribute [instance] groupD finiteD commutative_W

variable {E : Type u} [Group E] {p m : ℕ} {V G : Subgroup E}

/-- Conjugation action of the lifted actor on the homocyclic factor. -/
noncomputable def actor (X : IsoQuotientHomocyclicSdprod p m V G) :
    X.G₁ →* MulAut X.W := by
  letI : X.W.Normal := X.normal_W
  exact (MulAut.conjNormal : X.D →* MulAut X.W).comp X.G₁.subtype

@[simp]
theorem actor_apply_val (X : IsoQuotientHomocyclicSdprod p m V G)
    (g : X.G₁) (w : X.W) :
    ((X.actor g w : X.W) : X.D) =
      (g : X.D) * (w : X.D) * (g : X.D)⁻¹ := by
  letI : X.W.Normal := X.normal_W
  rfl

/-- Pull a subgroup of the original actor back to the lifted actor. -/
def pullbackActorSubgroup
    (X : IsoQuotientHomocyclicSdprod p m V G) (A : Subgroup G) :
    Subgroup X.G₁ := A.comap X.actorEquiv.toMonoidHom

@[simp]
theorem pullbackActorSubgroup_map
    (X : IsoQuotientHomocyclicSdprod p m V G) (A : Subgroup G) :
    (X.pullbackActorSubgroup A).map X.actorEquiv.toMonoidHom = A := by
  exact Subgroup.map_comap_eq_self_of_surjective X.actorEquiv.surjective A

theorem natCard_pullbackActorSubgroup
    (X : IsoQuotientHomocyclicSdprod p m V G) (A : Subgroup G) :
    Nat.card (X.pullbackActorSubgroup A) = Nat.card A := by
  let e₀ :=
    (X.pullbackActorSubgroup A).equivMapOfInjective
      X.actorEquiv.toMonoidHom X.actorEquiv.injective
  let e : X.pullbackActorSubgroup A ≃* A :=
    e₀.trans (MulEquiv.subgroupCongr (X.pullbackActorSubgroup_map A))
  exact Nat.card_congr e.toEquiv

/-- The quotient map restricted to the homocyclic factor, with its codomain
restricted to `V`. -/
noncomputable def quotientHom
    (X : IsoQuotientHomocyclicSdprod p m V G) : X.W →* V :=
  (X.f.comp X.W.subtype).codRestrict V fun w ↦ by
    change X.f (w : X.D) ∈ V
    have hw : X.f (w : X.D) ∈ X.W.map X.f := ⟨w, w.2, rfl⟩
    simpa only [X.map_W] using hw

/-- Additive form of the cover quotient. -/
noncomputable def quotientAdd
    (X : IsoQuotientHomocyclicSdprod p m V G) :
    Additive X.W →+ Additive V :=
  MonoidHom.toAdditive X.quotientHom

theorem quotientHom_surjective
    (X : IsoQuotientHomocyclicSdprod p m V G) :
    Function.Surjective X.quotientHom := by
  intro v
  have hv : (v : E) ∈ X.W.map X.f := X.map_W.symm ▸ v.2
  rcases hv with ⟨w, hw, hwv⟩
  exact ⟨⟨w, hw⟩, Subtype.ext hwv⟩

theorem quotientAdd_surjective
    (X : IsoQuotientHomocyclicSdprod p m V G) :
    Function.Surjective X.quotientAdd :=
  X.quotientHom_surjective

@[simp]
theorem quotientHom_actor
    (X : IsoQuotientHomocyclicSdprod p m V G)
    (g : X.G₁) (w : X.W) :
    V.subtype (X.quotientHom (X.actor g w)) =
      G.subtype (X.actorEquiv g) * V.subtype (X.quotientHom w) *
        (G.subtype (X.actorEquiv g))⁻¹ := by
  change X.f (((X.actor g w : X.W) : X.D)) = _
  rw [X.actor_apply_val, map_mul, map_mul, map_inv, X.actorEquiv_apply]
  rfl

/-- The canonical `ZMod (p ^ m)` model carried by the homocyclic factor. -/
abbrev ZModModel (X : IsoQuotientHomocyclicSdprod p m V G) :=
  Additive X.W

noncomputable instance zmodModelModule
    (X : IsoQuotientHomocyclicSdprod p m V G) :
    Module (ZMod (p ^ m)) X.ZModModel :=
  AddCommGroup.zmodModule fun x ↦ by
    change x.toMul ^ (p ^ m) = 1
    exact X.pow_eq_one x.toMul

/-- Linear action of the lifted actor on the canonical prime-power cover. -/
noncomputable def actorRepresentation
    (X : IsoQuotientHomocyclicSdprod p m V G) :
    Representation (ZMod (p ^ m)) X.G₁ X.ZModModel where
  toFun g :=
    (MonoidHom.toAdditive (X.actor g).toMonoidHom).toZModLinearMap (p ^ m)
  map_one' := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul ((X.actor 1) x.toMul) = x
    simp
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro x
    change Additive.ofMul ((X.actor (g * h)) x.toMul) =
      Additive.ofMul ((X.actor g) ((X.actor h) x.toMul))
    rw [map_mul]
    rfl

@[simp]
theorem actorRepresentation_apply
    (X : IsoQuotientHomocyclicSdprod p m V G)
    (g : X.G₁) (x : X.ZModModel) :
    X.actorRepresentation g x = Additive.ofMul (X.actor g x.toMul) :=
  rfl

/-- An additive equivalence between `ZMod n` modules is automatically
linear. -/
noncomputable def zmodLinearEquivOfAddEquiv
    {n : ℕ} {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod n) M] [Module (ZMod n) N] (e : M ≃+ N) :
    M ≃ₗ[ZMod n] N where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' c x := ZMod.map_smul e.toAddMonoidHom c x

noncomputable instance zmodModelFree
    (X : IsoQuotientHomocyclicSdprod p m V G) :
    Module.Free (ZMod (p ^ m)) X.ZModModel := by
  rcases X.homocyclic_at_m with ⟨d, ⟨e⟩⟩
  let emul : X.W ≃* Multiplicative (Fin d → ZMod (p ^ m)) :=
    e.trans (MulEquiv.piMultiplicative
      (fun _ : Fin d ↦ ZMod (p ^ m))).symm
  let eadd : X.ZModModel ≃+ (Fin d → ZMod (p ^ m)) :=
    MulEquiv.toAdditiveLeft emul
  let elin : X.ZModModel ≃ₗ[ZMod (p ^ m)]
      (Fin d → ZMod (p ^ m)) :=
    zmodLinearEquivOfAddEquiv eadd
  exact Module.Free.of_equiv elin.symm

noncomputable instance zmodModelFinite
    (X : IsoQuotientHomocyclicSdprod p m V G) :
    Module.Finite (ZMod (p ^ m)) X.ZModModel := by
  rcases X.homocyclic_at_m with ⟨d, ⟨e⟩⟩
  let emul : X.W ≃* Multiplicative (Fin d → ZMod (p ^ m)) :=
    e.trans (MulEquiv.piMultiplicative
      (fun _ : Fin d ↦ ZMod (p ^ m))).symm
  let eadd : X.ZModModel ≃+ (Fin d → ZMod (p ^ m)) :=
    MulEquiv.toAdditiveLeft emul
  let elin : X.ZModModel ≃ₗ[ZMod (p ^ m)]
      (Fin d → ZMod (p ^ m)) :=
    zmodLinearEquivOfAddEquiv eadd
  exact Module.Finite.equiv elin.symm

end IsoQuotientHomocyclicSdprod

/-! ## Prime-power coordinate lifting -/

namespace PrimePowerCoordinateLift

variable {p m d : ℕ} [Fact p.Prime]

private theorem prime_dvd_prime_pow (hm : 0 < m) : p ∣ p ^ m :=
  dvd_pow_self p (Nat.ne_zero_of_lt hm)

/-- Reduction from `ZMod (p ^ m)` to its prime residue field. -/
noncomputable def residueHom (hm : 0 < m) : ZMod (p ^ m) →+* ZMod p :=
  ZMod.castHom (prime_dvd_prime_pow hm) (ZMod p)

theorem residueHom_surjective (hm : 0 < m) :
    Function.Surjective (residueHom (p := p) hm) :=
  ZMod.castHom_surjective (prime_dvd_prime_pow hm)

/-- A fixed set-theoretic section of prime reduction. -/
noncomputable def residueSection (hm : 0 < m) : ZMod p → ZMod (p ^ m) :=
  (residueHom_surjective (p := p) hm).hasRightInverse.choose

@[simp]
theorem residueHom_residueSection (hm : 0 < m) (x : ZMod p) :
    residueHom (p := p) hm (residueSection (p := p) hm x) = x :=
  (residueHom_surjective (p := p) hm).hasRightInverse.choose_spec x

/-- An element whose residue modulo `p` is nonzero is a unit modulo
`p ^ m`. -/
theorem isUnit_of_residue_ne_zero (hm : 0 < m) (x : ZMod (p ^ m))
    (hx : residueHom (p := p) hm x ≠ 0) : IsUnit x := by
  rw [← ZMod.natCast_zmod_val x]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hm).2
  intro hdiv
  apply hx
  rw [← ZMod.natCast_zmod_val x]
  rw [map_natCast]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hdiv

/-- Entrywise lift of a matrix over the prime field. -/
noncomputable def liftMatrix (hm : 0 < m)
    (A : Matrix (Fin d) (Fin d) (ZMod p)) :
    Matrix (Fin d) (Fin d) (ZMod (p ^ m)) :=
  fun i j ↦ residueSection (p := p) hm (A i j)

@[simp]
theorem map_liftMatrix (hm : 0 < m)
    (A : Matrix (Fin d) (Fin d) (ZMod p)) :
    (liftMatrix (p := p) hm A).map (residueHom (p := p) hm) = A := by
  ext i j
  exact residueHom_residueSection (p := p) hm (A i j)

/-- Every invertible matrix over `ZMod p` lifts to an invertible matrix
over `ZMod (p ^ m)`. -/
noncomputable def liftGL (hm : 0 < m)
    (A : GL (Fin d) (ZMod p)) : GL (Fin d) (ZMod (p ^ m)) := by
  let M := liftMatrix (p := p) hm (A : Matrix (Fin d) (Fin d) (ZMod p))
  have hdetmap :
      residueHom (p := p) hm M.det =
        (A : Matrix (Fin d) (Fin d) (ZMod p)).det := by
    rw [RingHom.map_det]
    simpa [M] using congrArg Matrix.det
      (map_liftMatrix (p := p) hm
        (A : Matrix (Fin d) (Fin d) (ZMod p)))
  have hdet : IsUnit M.det :=
    isUnit_of_residue_ne_zero (p := p) hm M.det
      (hdetmap.symm ▸ Matrix.GeneralLinearGroup.det_ne_zero A)
  exact Matrix.GeneralLinearGroup.mk'' M hdet

@[simp]
theorem map_liftGL (hm : 0 < m) (A : GL (Fin d) (ZMod p)) :
    Matrix.GeneralLinearGroup.map (residueHom (p := p) hm)
      (liftGL (p := p) hm A) = A := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change residueHom (p := p) hm
      (residueSection (p := p) hm ((A : Matrix (Fin d) (Fin d) (ZMod p)) i j)) =
    (A : Matrix (Fin d) (Fin d) (ZMod p)) i j
  exact residueHom_residueSection (p := p) hm _

theorem mapGL_surjective (hm : 0 < m) :
    Function.Surjective
      (Matrix.GeneralLinearGroup.map (n := Fin d) (residueHom (p := p) hm)) :=
  fun A ↦ ⟨liftGL (p := p) hm A, map_liftGL (p := p) hm A⟩

section CoordinateAutomorphisms

variable (n d : ℕ)

/-- Additive equivalences of `ZMod n`-modules are automatically linear. -/
noncomputable def addEquivToZModLinearEquiv
    (e : (Fin d → ZMod n) ≃+ (Fin d → ZMod n)) :
    (Fin d → ZMod n) ≃ₗ[ZMod n] (Fin d → ZMod n) where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' c x := ZMod.map_smul e.toAddMonoidHom c x

/-- Linear and multiplicative automorphisms of a coordinate `ZMod` group
are the same data. -/
noncomputable def zmodLinearEquivMulAut :
    ((Fin d → ZMod n) ≃ₗ[ZMod n] (Fin d → ZMod n)) ≃*
      MulAut (Multiplicative (Fin d → ZMod n)) where
  toFun e := AddEquiv.toMultiplicative e.toAddEquiv
  invFun a := addEquivToZModLinearEquiv n d
    (AddEquiv.toMultiplicative.symm a)
  left_inv e := by ext x; rfl
  right_inv a := by ext x; rfl
  map_mul' e₁ e₂ := by ext x; rfl

/-- Matrix coordinates identify the general linear group with the
automorphism group of the corresponding homocyclic additive group. -/
noncomputable def matrixMulAutEquiv :
    GL (Fin d) (ZMod n) ≃* MulAut (Multiplicative (Fin d → ZMod n)) :=
  Matrix.GeneralLinearGroup.toLin.trans <|
    (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod n) (Fin d → ZMod n)).trans <|
      zmodLinearEquivMulAut n d

@[simp]
theorem matrixMulAutEquiv_apply (A : GL (Fin d) (ZMod n))
    (x : Fin d → ZMod n) :
    (matrixMulAutEquiv n d A (Multiplicative.ofAdd x)).toAdd =
      (A : Matrix (Fin d) (Fin d) (ZMod n)) *ᵥ x := by
  rfl

end CoordinateAutomorphisms

/-- Coordinatewise reduction on the homocyclic group. -/
noncomputable def coordinateReduction (hm : 0 < m) :
    Multiplicative (Fin d → ZMod (p ^ m)) →*
      Multiplicative (Fin d → ZMod p) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun x i ↦ residueHom (p := p) hm (x i)
      map_zero' := by ext; exact map_zero (residueHom (p := p) hm)
      map_add' := by
        intro x y
        ext i
        exact map_add (residueHom (p := p) hm) (x i) (y i) }

theorem coordinateReduction_surjective (hm : 0 < m) :
    Function.Surjective (coordinateReduction (p := p) (d := d) hm) := by
  intro x
  refine ⟨Multiplicative.ofAdd
    (fun i ↦ residueSection (p := p) hm (x.toAdd i)), ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  exact residueHom_residueSection (p := p) hm (x.toAdd i)

/-- Reduction commutes with the matrix automorphisms. -/
theorem coordinateReduction_matrixMulAut (hm : 0 < m)
    (A : GL (Fin d) (ZMod (p ^ m)))
    (x : Multiplicative (Fin d → ZMod (p ^ m))) :
    coordinateReduction (p := p) (d := d) hm
        (matrixMulAutEquiv (p ^ m) d A x) =
      matrixMulAutEquiv p d
        (Matrix.GeneralLinearGroup.map (residueHom (p := p) hm) A)
        (coordinateReduction (p := p) (d := d) hm x) := by
  apply Multiplicative.toAdd.injective
  change
    (coordinateReduction (p := p) (d := d) hm
      (matrixMulAutEquiv (p ^ m) d A
        (Multiplicative.ofAdd x.toAdd))).toAdd =
      (matrixMulAutEquiv p d
        (Matrix.GeneralLinearGroup.map (residueHom (p := p) hm) A)
        (Multiplicative.ofAdd
          (coordinateReduction (p := p) (d := d) hm x).toAdd)).toAdd
  ext i
  simp only [matrixMulAutEquiv_apply]
  change residueHom (p := p) hm
      (((A : Matrix (Fin d) (Fin d) (ZMod (p ^ m))) *ᵥ x.toAdd) i) = _
  simp only [Matrix.mulVec, dotProduct]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact map_mul (residueHom (p := p) hm) _ _

/-- The kernel of coordinate reduction consists exactly of `p`th powers. -/
theorem coordinateReduction_ker (hm : 0 < m) :
    (coordinateReduction (p := p) (d := d) hm).ker =
      abelianPowerSubgroup p 1
        (Multiplicative (Fin d → ZMod (p ^ m))) := by
  ext x
  constructor
  · intro hx
    change coordinateReduction (p := p) (d := d) hm x = 1 at hx
    have hxcoord : ∀ i, p ∣ (x.toAdd i).val := by
      intro i
      have hi := congrArg (fun y : Multiplicative (Fin d → ZMod p) ↦ y.toAdd i) hx
      change residueHom (p := p) hm (x.toAdd i) = 0 at hi
      rw [← ZMod.natCast_zmod_val (x.toAdd i)] at hi
      rw [map_natCast] at hi
      exact (ZMod.natCast_eq_zero_iff _ _).mp hi
    let y : Multiplicative (Fin d → ZMod (p ^ m)) :=
      Multiplicative.ofAdd (fun i ↦ ((x.toAdd i).val / p : ℕ))
    refine ⟨y, ?_⟩
    apply Multiplicative.toAdd.injective
    change (y ^ (p ^ 1)).toAdd = x.toAdd
    rw [toAdd_pow, pow_one]
    funext i
    rw [nsmul_eq_mul, mul_comm]
    change (((x.toAdd i).val / p : ℕ) : ZMod (p ^ m)) * p = x.toAdd i
    rw [← Nat.cast_mul]
    rw [Nat.div_mul_cancel (hxcoord i)]
    exact ZMod.natCast_zmod_val (x.toAdd i)
  · rintro ⟨y, rfl⟩
    change coordinateReduction (p := p) (d := d) hm (y ^ (p ^ 1)) = 1
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    ext i
    simp [pow_one, residueHom]

/-- The coordinate group over `ZMod (p ^ m)` is a finite `p`-group. -/
theorem coordinate_isPGroup :
    IsPGroup p (Multiplicative (Fin d → ZMod (p ^ m))) := by
  apply IsPGroup.of_card (n := m * d)
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_fin, Nat.card_zmod]
  exact (pow_mul p m d).symm

/-- On prime-power coordinates, the Frattini subgroup is precisely the
kernel of coefficient reduction. -/
theorem coordinate_frattini_eq_ker (hm : 0 < m) :
    frattini (Multiplicative (Fin d → ZMod (p ^ m))) =
      (coordinateReduction (p := p) (d := d) hm).ker := by
  rw [frattini_eq_abelianPowerSubgroup_one
    (coordinate_isPGroup (p := p) (m := m) (d := d))]
  exact (coordinateReduction_ker (p := p) (d := d) hm).symm

/-- The Frattini quotient of the coordinate cover is its coefficientwise
reduction modulo `p`. -/
noncomputable def coordinateFrattiniEquiv (hm : 0 < m) :
    (Multiplicative (Fin d → ZMod (p ^ m)) ⧸
        frattini (Multiplicative (Fin d → ZMod (p ^ m)))) ≃*
      Multiplicative (Fin d → ZMod p) :=
  (QuotientGroup.quotientMulEquivOfEq
      (coordinate_frattini_eq_ker (p := p) (d := d) hm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (coordinateReduction (p := p) (d := d) hm)
      (coordinateReduction_surjective (p := p) (d := d) hm))

@[simp]
theorem coordinateFrattiniEquiv_apply_mk (hm : 0 < m)
    (x : Multiplicative (Fin d → ZMod (p ^ m))) :
    coordinateFrattiniEquiv (p := p) (d := d) hm
        (QuotientGroup.mk'
          (frattini (Multiplicative (Fin d → ZMod (p ^ m)))) x) =
      coordinateReduction (p := p) (d := d) hm x := by
  simp [coordinateFrattiniEquiv,
    QuotientGroup.quotientKerEquivOfSurjective]

/-- Action on the Frattini quotient, expressed in prime coordinates. -/
noncomputable def coordinateFrattiniMulAutHom (hm : 0 < m) :
    MulAut (Multiplicative (Fin d → ZMod (p ^ m))) →*
      MulAut (Multiplicative (Fin d → ZMod p)) :=
  (MulAut.congr (coordinateFrattiniEquiv (p := p) (d := d) hm)).toMonoidHom.comp
    (frattiniQuotientMulAutHom
      (Multiplicative (Fin d → ZMod (p ^ m))))

/-- Every automorphism of the elementary Frattini quotient lifts to the
prime-power coordinate group. -/
theorem coordinateFrattiniMulAutHom_surjective (hm : 0 < m) :
    Function.Surjective
      (coordinateFrattiniMulAutHom (p := p) (d := d) hm) := by
  intro a
  let A : GL (Fin d) (ZMod p) :=
    (matrixMulAutEquiv p d).symm a
  let B : GL (Fin d) (ZMod (p ^ m)) := liftGL (p := p) hm A
  refine ⟨matrixMulAutEquiv (p ^ m) d B, ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := coordinateReduction_surjective (p := p) (d := d) hm y
  have hsymm :
      (coordinateFrattiniEquiv (p := p) (d := d) hm).symm
          (coordinateReduction (p := p) (d := d) hm x) =
        QuotientGroup.mk'
          (frattini (Multiplicative (Fin d → ZMod (p ^ m)))) x := by
    apply (coordinateFrattiniEquiv (p := p) (d := d) hm).injective
    simpa using
      (coordinateFrattiniEquiv_apply_mk (p := p) (d := d) hm x).symm
  change
    coordinateFrattiniEquiv (p := p) (d := d) hm
        (frattiniQuotientMulAutHom
          (Multiplicative (Fin d → ZMod (p ^ m)))
          (matrixMulAutEquiv (p ^ m) d B)
          ((coordinateFrattiniEquiv (p := p) (d := d) hm).symm
            (coordinateReduction (p := p) (d := d) hm x))) =
      a (coordinateReduction (p := p) (d := d) hm x)
  rw [show
    (coordinateFrattiniEquiv (p := p) (d := d) hm).symm
        (coordinateReduction (p := p) (d := d) hm x) = _ from hsymm]
  calc
    coordinateFrattiniEquiv (p := p) (d := d) hm
        (frattiniQuotientMulAutHom
          (Multiplicative (Fin d → ZMod (p ^ m)))
          (matrixMulAutEquiv (p ^ m) d B)
          (QuotientGroup.mk'
            (frattini (Multiplicative (Fin d → ZMod (p ^ m)))) x)) =
        coordinateFrattiniEquiv (p := p) (d := d) hm
          (QuotientGroup.mk'
            (frattini (Multiplicative (Fin d → ZMod (p ^ m))))
            (matrixMulAutEquiv (p ^ m) d B x)) := by
      exact congrArg (coordinateFrattiniEquiv (p := p) (d := d) hm)
        (frattiniQuotientMulAutHom_apply_mk
          (matrixMulAutEquiv (p ^ m) d B) x)
    _ = coordinateReduction (p := p) (d := d) hm
          (matrixMulAutEquiv (p ^ m) d B x) :=
      coordinateFrattiniEquiv_apply_mk (p := p) (d := d) hm _
    _ = a (coordinateReduction (p := p) (d := d) hm x) := by
      simpa [A, B] using
        (coordinateReduction_matrixMulAut (p := p) (d := d) hm B x)

/-- In coordinate groups the canonical map on Frattini-quotient
automorphisms is surjective. -/
theorem frattiniQuotientMulAutHom_surjective (hm : 0 < m) :
    Function.Surjective
      (frattiniQuotientMulAutHom
        (Multiplicative (Fin d → ZMod (p ^ m)))) := by
  intro a
  let e := coordinateFrattiniEquiv (p := p) (d := d) hm
  obtain ⟨b, hb⟩ :=
    coordinateFrattiniMulAutHom_surjective (p := p) (d := d) hm
      (MulAut.congr e a)
  refine ⟨b, ?_⟩
  apply (MulAut.congr e).injective
  exact hb

end PrimePowerCoordinateLift

namespace IsoQuotientHomocyclicSdprod

variable {E : Type u} [Group E] {p m : ℕ} {V G : Subgroup E}

/-- The quotient from the prime-power cover is semilinear for reduction of
scalars from `ZMod (p ^ m)` to `ZMod p`. -/
theorem quotientAdd_smul_residue
    (X : IsoQuotientHomocyclicSdprod p m V G)
    [Fact p.Prime] [IsMulCommutative V]
    [Module (ZMod p) (Additive V)]
    (hm : 0 < m) (r : ZMod (p ^ m)) (x : X.ZModModel) :
    X.quotientAdd (r • x) =
      PrimePowerCoordinateLift.residueHom (p := p) hm r •
        X.quotientAdd x := by
  letI : NeZero (p ^ m) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hr : r = (r.val : ZMod (p ^ m)) :=
    (ZMod.natCast_zmod_val r).symm
  have hres :
      PrimePowerCoordinateLift.residueHom (p := p) hm r =
        (r.val : ZMod p) := by
    calc
      PrimePowerCoordinateLift.residueHom (p := p) hm r =
          PrimePowerCoordinateLift.residueHom (p := p) hm
            (r.val : ZMod (p ^ m)) := congrArg _ hr
      _ = (r.val : ZMod p) := map_natCast _ r.val
  calc
    X.quotientAdd (r • x) =
        X.quotientAdd ((r.val : ZMod (p ^ m)) • x) :=
      congrArg X.quotientAdd (congrArg (fun s : ZMod (p ^ m) ↦ s • x) hr)
    _ = X.quotientAdd (r.val • x) := by
      rw [Nat.cast_smul_eq_nsmul]
    _ = r.val • X.quotientAdd x := map_nsmul X.quotientAdd r.val x
    _ = (r.val : ZMod p) • X.quotientAdd x := by
      rw [Nat.cast_smul_eq_nsmul]
    _ = PrimePowerCoordinateLift.residueHom (p := p) hm r •
        X.quotientAdd x := by rw [hres]

/-- The kernel of the additive cover quotient consists exactly of the
`p`-multiples in the prime-power model. -/
theorem quotientAdd_eq_zero_iff_prime_smul
    (X : IsoQuotientHomocyclicSdprod p m V G) (x : X.ZModModel) :
    X.quotientAdd x = 0 ↔
      ∃ y : X.ZModModel, (p : ZMod (p ^ m)) • y = x := by
  constructor
  · intro hx
    change X.quotientHom x.toMul = 1 at hx
    have hxf : X.W.subtype x.toMul ∈ X.f.ker := by
      change X.f (X.W.subtype x.toMul) = 1
      exact congrArg Subtype.val hx
    rw [X.ker_f] at hxf
    rcases hxf with ⟨y, hy, hyx⟩
    have hxpow :
        x.toMul ∈ abelianPowerSubgroup p 1 X.W := by
      rw [← X.W.subtype_injective hyx]
      exact hy
    rcases (mem_abelianPowerSubgroup_iff p 1 x.toMul).mp hxpow with
      ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    rw [Nat.cast_smul_eq_nsmul, toMul_nsmul]
    simpa [pow_one] using hy
  · rintro ⟨y, hy⟩
    have hyMul : y.toMul ^ p = x.toMul := by
      have := congrArg Additive.toMul hy
      simpa [Nat.cast_smul_eq_nsmul] using this
    have hxpow : x.toMul ∈ abelianPowerSubgroup p 1 X.W :=
      (mem_abelianPowerSubgroup_iff p 1 x.toMul).2
        ⟨y.toMul, by simpa [pow_one] using hyMul⟩
    have hxf : X.W.subtype x.toMul ∈ X.f.ker := by
      rw [X.ker_f]
      exact ⟨x.toMul, hxpow, rfl⟩
    change X.quotientHom x.toMul = 1
    apply V.subtype_injective
    exact hxf

end IsoQuotientHomocyclicSdprod

/-! ## Lifting a coprime action from a Frattini quotient -/

/-- A lift of an action through the automorphism group of a Frattini
quotient.  The actor is allowed to be replaced by an isomorphic group; this
is exactly the complement produced by Schur--Zassenhaus. -/
structure CoprimeFrattiniActionLift
    (P : Type v) (A V : Type u) [Group P] [Group A] [Group V]
    (q : P ⧸ frattini P ≃* V) (rho : A →* MulAut V) where
  K : Type (max u v)
  [groupK : Group K]
  [finiteK : Finite K]
  action : K →* MulAut P
  actorEquiv : K ≃* A
  quotient_compat : ∀ k x,
    q (QuotientGroup.mk' (frattini P) (action k x)) =
      rho (actorEquiv k) (q (QuotientGroup.mk' (frattini P) x))

namespace CoprimeFrattiniActionLift

attribute [instance] groupK finiteK

end CoprimeFrattiniActionLift

/-- A coprime actor lifts through a surjective Frattini-quotient
automorphism map. -/
theorem exists_coprimeFrattiniActionLift
    {P : Type v} {A V : Type u}
    [Group P] [Finite P] [Group A] [Finite A] [Group V]
    {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P)
    (hqsurj : Function.Surjective (frattiniQuotientMulAutHom P))
    (hcop : Nat.Coprime p (Nat.card A))
    (q : P ⧸ frattini P ≃* V) (rho : A →* MulAut V) :
    Nonempty (CoprimeFrattiniActionLift P A V q rho) := by
  classical
  let qAut : MulAut P →* MulAut (P ⧸ frattini P) :=
    frattiniQuotientMulAutHom P
  let rhoQ : A →* MulAut (P ⧸ frattini P) :=
    (MulAut.congr q.symm).toMonoidHom.comp rho
  let left : MulAut P × A →* MulAut (P ⧸ frattini P) :=
    qAut.comp (MonoidHom.fst (MulAut P) A)
  let right : MulAut P × A →* MulAut (P ⧸ frattini P) :=
    rhoQ.comp (MonoidHom.snd (MulAut P) A)
  let B : Subgroup (MulAut P × A) := left.eqLocus right
  let proj : B →* A :=
    (MonoidHom.snd (MulAut P) A).comp B.subtype
  have hproj : Function.Surjective proj := by
    intro a
    obtain ⟨b, hb⟩ := hqsurj (rhoQ a)
    refine ⟨⟨(b, a), ?_⟩, rfl⟩
    exact hb
  let N : Subgroup B := proj.ker
  let kerEmbed : N →* qAut.ker :=
    (((MonoidHom.fst (MulAut P) A).comp B.subtype).comp N.subtype).codRestrict
      qAut.ker fun n ↦ by
        change qAut n.1.1.1 = 1
        have hnB : qAut n.1.1.1 = rhoQ n.1.1.2 := n.1.2
        have hnA : n.1.1.2 = 1 := n.2
        simpa [hnA] using hnB
  have hkerEmbed : Function.Injective kerEmbed := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val hxy
    · calc
        x.1.1.2 = 1 := x.2
        _ = y.1.1.2 := y.2.symm
  have hN : IsPGroup p N :=
    (frattiniQuotientMulAutHom_ker_isPGroup hP).of_injective
      kerEmbed hkerEmbed
  letI : N.Normal := inferInstance
  have hindex : N.index = Nat.card A := by
    rw [Subgroup.index_ker, proj.range_eq_top_of_surjective hproj,
      Subgroup.card_top]
  obtain ⟨r, hr⟩ := hN.exists_card_eq
  have hNcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hr, hindex]
    exact hcop.pow_left r
  obtain ⟨K, hK⟩ := N.exists_right_complement'_of_coprime hNcop
  let actorHom : K →* A := proj.comp K.subtype
  have hactorHom_inj : Function.Injective actorHom := by
    intro x y hxy
    have hxyN : (x : B) * (y : B)⁻¹ ∈ N := by
      change proj ((x : B) * (y : B)⁻¹) = 1
      change actorHom x * (actorHom y)⁻¹ = 1
      rw [hxy, mul_inv_cancel]
    have hxyK : (x : B) * (y : B)⁻¹ ∈ K :=
      K.mul_mem x.2 (K.inv_mem y.2)
    have hxyOne : (x : B) * (y : B)⁻¹ = 1 := by
      have hbot : (x : B) * (y : B)⁻¹ ∈ (⊥ : Subgroup B) :=
        hK.disjoint.le_bot ⟨hxyN, hxyK⟩
      simpa using hbot
    exact Subtype.ext (mul_inv_eq_one.mp hxyOne)
  have hactorHom_surj : Function.Surjective actorHom := by
    intro a
    obtain ⟨b, hb⟩ := hproj a
    obtain ⟨nk, hnk⟩ := hK.2 b
    refine ⟨nk.2, ?_⟩
    have happ := congrArg proj hnk
    change proj (nk.1 : B) * proj (nk.2 : B) = proj b at happ
    rw [nk.1.2, one_mul, hb] at happ
    exact happ
  let actorEquiv : K ≃* A :=
    MulEquiv.ofBijective actorHom ⟨hactorHom_inj, hactorHom_surj⟩
  let liftAction : K →* MulAut P :=
    ((MonoidHom.fst (MulAut P) A).comp B.subtype).comp K.subtype
  refine ⟨
    { K := K
      action := liftAction
      actorEquiv := actorEquiv
      quotient_compat := ?_ }⟩
  intro k x
  have hkB : qAut (liftAction k) = rhoQ (actorEquiv k) := by
    exact k.1.2
  calc
    q (QuotientGroup.mk' (frattini P) (liftAction k x)) =
        q (qAut (liftAction k) (QuotientGroup.mk' (frattini P) x)) := by
      exact congrArg q (frattiniQuotientMulAutHom_apply_mk (liftAction k) x).symm
    _ = q (rhoQ (actorEquiv k) (QuotientGroup.mk' (frattini P) x)) := by
      exact congrArg q (DFunLike.congr_fun hkB _)
    _ = rho (actorEquiv k) (q (QuotientGroup.mk' (frattini P) x)) := by
      simp [rhoQ, actorEquiv, actorHom]

/-- Kernel of a semidirect-product lift when the two factor images are
disjoint and the actor map is faithful. -/
theorem SemidirectProduct.ker_lift_eq_map_ker_inl
    {N A H : Type*} [Group N] [Group A] [Group H]
    {phi : A →* MulAut N} (fn : N →* H) (fg : A →* H)
    (hcompat : ∀ a,
      fn.comp (phi a).toMonoidHom =
        (MulAut.conj (fg a)).toMonoidHom.comp fn)
    (hdisj : Disjoint fn.range fg.range)
    (hfg : Function.Injective fg) :
    (SemidirectProduct.lift fn fg hcompat).ker =
      fn.ker.map (SemidirectProduct.inl : N →* N ⋊[phi] A) := by
  ext x
  constructor
  · intro hx
    change fn x.left * fg x.right = 1 at hx
    have heq : fn x.left = (fg x.right)⁻¹ :=
      eq_inv_of_mul_eq_one_left hx
    have hleft : fn x.left ∈ fn.range := ⟨x.left, rfl⟩
    have hright : fn x.left ∈ fg.range := by
      refine ⟨x.right⁻¹, ?_⟩
      simpa [heq]
    have hfn : fn x.left = 1 := by
      have hbot : fn x.left ∈ (⊥ : Subgroup H) :=
        hdisj.le_bot ⟨hleft, hright⟩
      simpa using hbot
    have hfgone : fg x.right = 1 := by
      simpa [hfn] using hx
    have hxright : x.right = 1 := hfg (hfgone.trans fg.map_one.symm)
    refine ⟨x.left, hfn, ?_⟩
    ext <;> simp [hxright]
  · rintro ⟨n, hn, rfl⟩
    change fn n = 1 at hn
    change SemidirectProduct.lift fn fg hcompat
      (SemidirectProduct.inl n) = 1
    simp [hn]

/-! ## The homocyclic semidirect cover -/

set_option maxHeartbeats 1000000

/-- Lean form of Coq's `iso_quotient_homocyclic_sdprod`. -/
noncomputable def iso_quotient_homocyclic_sdprod
    {E : Type u} [Group E] [Finite E]
    (V G : Subgroup E) (p m : ℕ) [Fact p.Prime]
    (hmin : IsMinimalNormalUnder V G)
    (hcop : Nat.Coprime p (Nat.card G))
    (hV : IsElementaryAbelianGroup p V) (hm : 0 < m) :
    IsoQuotientHomocyclicSdprod p m V G := by
  classical
  letI : IsMulCommutative V := hV.commutative
  letI hmod : Module (ZMod p) (Additive V) :=
    elementaryAbelianZModModule V p hV.pow_eq_one
  letI : Fintype (Additive V) := Fintype.ofFinite (Additive V)
  letI hfin : Module.Finite (ZMod p) (Additive V) := by
    exact ⟨⟨Finset.univ, by
      rw [Finset.coe_univ, Submodule.span_univ]⟩⟩
  letI hfree : Module.Free (ZMod p) (Additive V) := by infer_instance
  letI hsrc : StrongRankCondition (ZMod p) := by infer_instance
  let d := Module.finrank (ZMod p) (Additive V)
  let b := @Module.finBasis (ZMod p) (Additive V)
    inferInstance inferInstance hmod hfree hsrc hfin
  let eadd : Additive V ≃+ (Fin d → ZMod p) := b.equivFun.toAddEquiv
  let W₀ := Multiplicative (Fin d → ZMod (p ^ m))
  let Wp := Multiplicative (Fin d → ZMod p)
  let eV : Wp ≃* V := by
    dsimp [Wp]
    exact (AddEquiv.toMultiplicativeRight eadd).symm
  let qCoord : W₀ ⧸ frattini W₀ ≃* Wp := by
    dsimp [W₀, Wp]
    exact PrimePowerCoordinateLift.coordinateFrattiniEquiv
      (p := p) (d := d) hm
  let q : W₀ ⧸ frattini W₀ ≃* V := qCoord.trans eV
  let rho : G →* MulAut V :=
    V.normalizerMonoidHom.comp (Subgroup.inclusion hmin.le_normalizer)
  have hW₀p : IsPGroup p W₀ := by
    dsimp [W₀]
    exact PrimePowerCoordinateLift.coordinate_isPGroup
      (p := p) (m := m) (d := d)
  have hqAut : Function.Surjective (frattiniQuotientMulAutHom W₀) := by
    dsimp [W₀]
    exact PrimePowerCoordinateLift.frattiniQuotientMulAutHom_surjective
      (p := p) (d := d) hm
  let C : CoprimeFrattiniActionLift W₀ G V q rho :=
    Classical.choice
      (exists_coprimeFrattiniActionLift hW₀p hqAut hcop q rho)
  let K := C.K
  letI : Group K := C.groupK
  letI : Finite K := C.finiteK
  let qMap : W₀ →* V :=
    q.toMonoidHom.comp (QuotientGroup.mk' (frattini W₀))
  have hqMapSurj : Function.Surjective qMap :=
    q.surjective.comp (QuotientGroup.mk'_surjective (frattini W₀))
  have hqMapKer : qMap.ker = frattini W₀ := by
    ext x
    constructor
    · intro hx
      change qMap x = 1 at hx
      have hmk : QuotientGroup.mk' (frattini W₀) x = 1 := by
        apply q.injective
        simpa [qMap] using hx
      exact (QuotientGroup.eq_one_iff x).mp hmk
    · intro hx
      change q (QuotientGroup.mk' (frattini W₀) x) = 1
      have hmk : QuotientGroup.mk' (frattini W₀) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hx
      calc
        q (QuotientGroup.mk' (frattini W₀) x) = q 1 := congrArg q hmk
        _ = 1 := map_one q
  let fW : W₀ →* E := V.subtype.comp qMap
  let fK : K →* E := G.subtype.comp C.actorEquiv.toMonoidHom
  have hfKinj : Function.Injective fK :=
    G.subtype_injective.comp C.actorEquiv.injective
  have hfWrange : fW.range = V := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (qMap w).2
    · intro hx
      obtain ⟨w, hw⟩ := hqMapSurj ⟨x, hx⟩
      exact ⟨w, congrArg Subtype.val hw⟩
  have hfKrange : fK.range = G := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (C.actorEquiv k).2
    · intro hx
      obtain ⟨k, hk⟩ := C.actorEquiv.surjective ⟨x, hx⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hcardV : Nat.card V = p ^ d := by
    dsimp [d]
    exact (Nat.card_congr Additive.ofMul).trans <| by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V))
  have hVGcop : Nat.Coprime (Nat.card V) (Nat.card G) := by
    rw [hcardV]
    exact hcop.pow_left d
  have hdisj : Disjoint fW.range fK.range := by
    rw [hfWrange, hfKrange]
    exact Subgroup.disjoint_of_coprime_natCard hVGcop
  have hcompat : ∀ k,
      fW.comp (C.action k).toMonoidHom =
        (MulAut.conj (fK k)).toMonoidHom.comp fW := by
    intro k
    ext x
    change V.subtype (qMap (C.action k x)) =
      G.subtype (C.actorEquiv k) * V.subtype (qMap x) *
        (G.subtype (C.actorEquiv k))⁻¹
    have hx := C.quotient_compat k x
    exact congrArg Subtype.val hx
  let D := W₀ ⋊[C.action] K
  letI : Finite D := by
    dsimp [D]
    exact Finite.of_equiv (W₀ × K)
      (SemidirectProduct.equivProd (N := W₀) (G := K)
        (φ := C.action)).symm
  let inW : W₀ →* D := SemidirectProduct.inl
  let inK : K →* D := SemidirectProduct.inr
  let W : Subgroup D := inW.range
  let G₁ : Subgroup D := inK.range
  letI : W.Normal := by
    dsimp [W, inW, D]
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  let eW : W₀ ≃* W :=
    MonoidHom.ofInjective (SemidirectProduct.inl_injective
      (N := W₀) (G := K) (φ := C.action))
  letI : IsMulCommutative W := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply eW.symm.injective
    calc
      eW.symm (x * y) = eW.symm x * eW.symm y := map_mul eW.symm x y
      _ = eW.symm y * eW.symm x := mul_comm _ _
      _ = eW.symm (y * x) := (map_mul eW.symm y x).symm
  let eK : K ≃* G₁ :=
    MonoidHom.ofInjective (SemidirectProduct.inr_injective
      (N := W₀) (G := K) (φ := C.action))
  have hcomplement : W.IsComplement' G₁ := by
    change Function.Bijective
      (fun x : W × G₁ ↦ (x.1 : D) * (x.2 : D))
    constructor
    · rintro
        ⟨⟨_, ⟨a, rfl⟩⟩, ⟨_, ⟨b, rfl⟩⟩⟩
        ⟨⟨_, ⟨c, rfl⟩⟩, ⟨_, ⟨z, rfl⟩⟩⟩ hab
      have hac : a = c := by
        simpa [inW, inK, D] using
          congrArg SemidirectProduct.left hab
      have hbz : b = z := by
        simpa [inW, inK, D] using
          congrArg SemidirectProduct.right hab
      subst c
      subst z
      rfl
    · intro x
      refine ⟨⟨⟨inW x.left, ⟨x.left, rfl⟩⟩,
        ⟨inK x.right, ⟨x.right, rfl⟩⟩⟩, ?_⟩
      exact SemidirectProduct.inl_left_mul_inr_right x
  let f : D →* E := SemidirectProduct.lift fW fK hcompat
  have hf_inW (w : W₀) : f (inW w) = fW w := by
    exact SemidirectProduct.lift_inl fW fK hcompat w
  have hf_inK (k : K) : f (inK k) = fK k := by
    exact SemidirectProduct.lift_inr fW fK hcompat k
  have hfker0 : f.ker = fW.ker.map inW := by
    dsimp [f, inW, D]
    exact SemidirectProduct.ker_lift_eq_map_ker_inl
      fW fK hcompat hdisj hfKinj
  have hfWker : fW.ker = abelianPowerSubgroup p 1 W₀ := by
    rw [show fW.ker = qMap.ker by
      ext x
      change V.subtype (qMap x) = V.subtype 1 ↔ qMap x = 1
      exact V.subtype_injective.eq_iff]
    rw [hqMapKer, frattini_eq_abelianPowerSubgroup_one hW₀p]
  have hpowerMap :
      (abelianPowerSubgroup p 1 W).map W.subtype =
        (abelianPowerSubgroup p 1 W₀).map inW := by
    have hepower :
        (abelianPowerSubgroup p 1 W₀).map eW.toMonoidHom =
          abelianPowerSubgroup p 1 W := by
      exact eW.map_range_powMonoidHom (p ^ 1)
    calc
      (abelianPowerSubgroup p 1 W).map W.subtype =
          ((abelianPowerSubgroup p 1 W₀).map eW.toMonoidHom).map W.subtype := by
        rw [hepower]
      _ = (abelianPowerSubgroup p 1 W₀).map
          (W.subtype.comp eW.toMonoidHom) :=
        Subgroup.map_map (abelianPowerSubgroup p 1 W₀)
          W.subtype eW.toMonoidHom
      _ = (abelianPowerSubgroup p 1 W₀).map inW := by
        congr 1
  have hfker : f.ker =
      (abelianPowerSubgroup p 1 W).map W.subtype := by
    calc
      f.ker = fW.ker.map inW := hfker0
      _ = (abelianPowerSubgroup p 1 W₀).map inW := by rw [hfWker]
      _ = (abelianPowerSubgroup p 1 W).map W.subtype := hpowerMap.symm
  have hmapW : W.map f = V := by
    ext x
    constructor
    · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
      rw [hf_inW]
      exact (qMap w).2
    · intro hx
      obtain ⟨w, hw⟩ := hqMapSurj ⟨x, hx⟩
      refine ⟨inW w, ⟨w, rfl⟩, ?_⟩
      rw [hf_inW]
      exact congrArg Subtype.val hw
  have hmapG₁ : G₁.map f = G := by
    ext x
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      rw [hf_inK]
      exact (C.actorEquiv k).2
    · intro hx
      obtain ⟨k, hk⟩ := C.actorEquiv.surjective ⟨x, hx⟩
      refine ⟨inK k, ⟨k, rfl⟩, ?_⟩
      rw [hf_inK]
      exact congrArg Subtype.val hk
  have hVne : 1 < Nat.card V := V.one_lt_card_iff_ne_bot.mpr hmin.ne_bot
  have hd : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd0
    rw [hd0, pow_zero] at hcardV
    exact (Nat.ne_of_gt hVne) hcardV
  have hpowW₀ : ∀ x : W₀, x ^ (p ^ m) = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow]
    funext i
    exact ZModModule.char_nsmul_eq_zero (p ^ m) (x.toAdd i)
  have hexponentW₀ : Monoid.exponent W₀ = p ^ m := by
    apply dvd_antisymm
    · exact Monoid.exponent_dvd_of_forall_pow_eq_one hpowW₀
    · let i : Fin d := ⟨0, hd⟩
      let ev : W₀ →* Multiplicative (ZMod (p ^ m)) :=
        AddMonoidHom.toMultiplicative
          { toFun := fun x : Fin d → ZMod (p ^ m) ↦ x i
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
      have hev : Function.Surjective ev := by
        intro z
        refine ⟨Multiplicative.ofAdd (fun _ ↦ z.toAdd), rfl⟩
      simpa [W₀, Monoid.exponent_multiplicative, ZMod.exponent] using
        (MonoidHom.exponent_dvd (f := ev) hev)
  have hhomocyclic : IsHomocyclicPGroup p W := by
    apply IsHomocyclicPGroup.of_mulEquiv
      (H := W₀) (K := W)
      ⟨d, m, hm, ⟨by
        exact MulEquiv.piMultiplicative
          (fun _ : Fin d ↦ ZMod (p ^ m))⟩⟩
      eW.symm
  have hhomocyclicAtM :
      ∃ r : ℕ, Nonempty (W ≃* (Fin r → Multiplicative (ZMod (p ^ m)))) :=
    ⟨d, ⟨eW.symm.trans (by
      exact MulEquiv.piMultiplicative
        (fun _ : Fin d ↦ ZMod (p ^ m)))⟩⟩
  have hpowW : ∀ w : W, w ^ (p ^ m) = 1 := by
    intro w
    apply eW.symm.injective
    simp [hpowW₀]
  have hexponentW : Monoid.exponent W = p ^ m := by
    exact (Monoid.exponent_eq_of_mulEquiv eW).symm.trans hexponentW₀
  have hcardW : Nat.card W = Nat.card V ^ m := by
    calc
      Nat.card W = Nat.card W₀ := Nat.card_congr eW.symm.toEquiv
      _ = (p ^ m) ^ d := by
        dsimp [W₀]
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
          Nat.card_fin, Nat.card_zmod]
      _ = p ^ (m * d) := (pow_mul p m d).symm
      _ = p ^ (d * m) := by rw [Nat.mul_comm]
      _ = (p ^ d) ^ m := pow_mul p d m
      _ = Nat.card V ^ m := by rw [hcardV]
  let actorEquiv : G₁ ≃* G := eK.symm.trans C.actorEquiv
  refine
    { D := D
      W := W
      G₁ := G₁
      normal_W := inferInstance
      complement := hcomplement
      f := f
      homocyclic := hhomocyclic
      homocyclic_at_m := hhomocyclicAtM
      pow_eq_one := hpowW
      exponent_W := hexponentW
      card_W := hcardW
      ker_f := hfker
      map_W := hmapW
      map_G₁ := hmapG₁
      actorEquiv := actorEquiv
      actorEquiv_apply := ?_ }
  intro g
  change G.subtype (actorEquiv g) = f (G₁.subtype g)
  let k : K := eK.symm g
  have hk : inK k = G₁.subtype g := by
    exact congrArg Subtype.val (eK.apply_symm_apply g)
  calc
    G.subtype (actorEquiv g) = G.subtype (C.actorEquiv k) := by
      simp [actorEquiv, k]
    _ = fK k := rfl
    _ = f (inK k) := (hf_inK k).symm
    _ = f (G₁.subtype g) := congrArg f hk

end Submission.OddOrder.MathlibSupport
