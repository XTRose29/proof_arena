import ChallengeDeps

namespace Submission.GroupAlgebra

open scoped MonoidAlgebra

/-- The coefficient-sum augmentation of a group algebra. -/
noncomputable def augmentation (k G : Type*) [Field k] [Group G] :
    MonoidAlgebra k G →ₐ[k] k :=
  MonoidAlgebra.lift k k G (1 : G →* k)

/-- The augmentation ideal of a group algebra. -/
noncomputable def augmentationIdeal (k G : Type*) [Field k] [Group G] :
    Ideal (MonoidAlgebra k G) :=
  RingHom.ker (augmentation k G).toRingHom

noncomputable instance augmentationIdeal_isTwoSided
    (k G : Type*) [Field k] [Group G] : (augmentationIdeal k G).IsTwoSided where
  mul_mem_of_left b ha := by
    change augmentation k G (_ * b) = 0
    rw [map_mul]
    change augmentation k G _ = 0 at ha
    rw [ha, zero_mul]

/-- Right multiplication, viewed as a linear endomorphism over the coefficient field. -/
noncomputable def rightMul (k G : Type*) [Field k] [Group G] (a : MonoidAlgebra k G) :
    MonoidAlgebra k G →ₗ[k] MonoidAlgebra k G where
  toFun x := x * a
  map_add' x y := add_mul x y a
  map_smul' r x := by simp [Algebra.smul_def, mul_assoc]

/-- The left regular representation, with the carrier kept syntactically as a
group algebra (rather than its underlying finitely-supported function type). -/
noncomputable def leftRegular (k G : Type*) [Field k] [Group G] :
    Representation k G (MonoidAlgebra k G) where
  toFun g :=
    { toFun := fun x ↦ MonoidAlgebra.single g 1 * x
      map_add' := fun x y ↦ by rw [mul_add]
      map_smul' := fun r x ↦ mul_smul_comm _ _ _ }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

/-- The kernel of right multiplication is stable under the left regular action. -/
noncomputable def rightMulKernelSubrepresentation (k G : Type*) [Field k] [Group G]
    (a : MonoidAlgebra k G) :
    Subrepresentation (leftRegular k G) where
  toSubmodule := LinearMap.ker (rightMul k G a)
  apply_mem_toSubmodule g v hv := by
    rw [LinearMap.mem_ker] at hv ⊢
    change v * a = 0 at hv
    change (MonoidAlgebra.single g 1 * v) * a = 0
    rw [mul_assoc, hv, mul_zero]

/-- A representation supplies its underlying multiplicative action. -/
@[reducible]
def representationMulAction {k G V : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (rho : Representation k G V) : MulAction G V where
  smul g v := rho g v
  one_smul v := by
    change rho 1 v = v
    exact DFunLike.congr_fun (map_one rho) v
  mul_smul g h v := by
    change rho (g * h) v = rho g (rho h v)
    simpa only [Module.End.mul_apply] using DFunLike.congr_fun (map_mul rho g h) v

section FixedVectors

variable {k G : Type*} [Field k] [Group G]

/-- A vector fixed by the left regular action has constant coefficients. -/
theorem leftRegular_fixed_coeff_eq (b : MonoidAlgebra k G)
    (hb : ∀ g, leftRegular k G g b = b) (g : G) : b.coeff g = b.coeff 1 := by
  have h := congrArg (fun x : MonoidAlgebra k G ↦ x.coeff g) (hb g)
  change (MonoidAlgebra.single g 1 * b).coeff g = b.coeff g at h
  have hcalc : (MonoidAlgebra.single g 1 * b).coeff g = b.coeff 1 := by
    simp only [MonoidAlgebra.coeff, MonoidAlgebra.single_mul_apply, inv_mul_cancel, one_mul]
  exact h.symm.trans hcalc

/-- Multiplying a left-regular fixed vector on the right only scales it by
the augmentation. -/
theorem leftRegular_fixed_mul (b a : MonoidAlgebra k G)
    (hb : ∀ g, leftRegular k G g b = b) :
    b * a = augmentation k G a • b := by
  ext g
  change (b * a).coeff g = augmentation k G a * b.coeff g
  have hmul : (b * a).coeff g = a.sum (fun h r ↦ b.coeff (g * h⁻¹) * r) := by
    simpa only [MonoidAlgebra.coeff] using MonoidAlgebra.mul_apply_right b a g
  rw [hmul]
  simp_rw [leftRegular_fixed_coeff_eq b hb]
  simp only [augmentation, MonoidAlgebra.lift_apply, MonoidHom.one_apply, smul_eq_mul, mul_one]
  change (a : G →₀ k).sum (fun _ r ↦ b.coeff 1 * r) =
    (a : G →₀ k).sum (fun _ r ↦ r) * b.coeff 1
  rw [mul_comm]
  classical
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]

end FixedVectors

section PGroup

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Finite G]

/-- Over the defining field of a finite `p`-group, an element with nonzero
augmentation acts injectively by right multiplication. -/
theorem rightMul_injective_of_augmentation_ne_zero (hG : IsPGroup p G)
    (a : MonoidAlgebra (ZMod p) G) (ha : augmentation (ZMod p) G a ≠ 0) :
    Function.Injective (fun b ↦ b * a) := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI := Fintype.ofFinite G
  letI : Fintype (MonoidAlgebra (ZMod p) G) := Finsupp.fintype
  let W := rightMulKernelSubrepresentation (ZMod p) G a
  letI : Finite W.toSubmodule :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : MulAction G W.toSubmodule :=
    representationMulAction W.toRepresentation
  change Function.Injective (rightMul (ZMod p) G a)
  rw [← LinearMap.ker_eq_bot]
  change W.toSubmodule = ⊥
  by_contra hW
  haveI : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hp_card : p ∣ Nat.card W.toSubmodule := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact dvd_pow_self p (Nat.ne_of_gt (Module.finrank_pos_iff.mpr inferInstance))
  have hzero_fixed : (0 : W.toSubmodule) ∈ MulAction.fixedPoints G W.toSubmodule := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact map_zero (W.toRepresentation g)
  obtain ⟨b, hb_fixed, hb⟩ :=
    hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point W.toSubmodule hp_card hzero_fixed
  have hb_coeff : ∀ g, leftRegular (ZMod p) G g b = b := by
    intro g
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb_fixed g)
  have hb_mem : b.1 * a = 0 := by
    exact LinearMap.mem_ker.mp b.2
  have hscale : augmentation (ZMod p) G a • b.1 = 0 := by
    rw [← leftRegular_fixed_mul b.1 a hb_coeff, hb_mem]
  have hb_zero : b = 0 := by
    apply Subtype.ext
    exact (smul_eq_zero.mp hscale).resolve_left ha
  exact hb hb_zero.symm

/-- An element of the modular group algebra is a unit exactly when its
augmentation is nonzero. -/
theorem isUnit_iff_augmentation_ne_zero (hG : IsPGroup p G)
    (a : MonoidAlgebra (ZMod p) G) :
    IsUnit a ↔ augmentation (ZMod p) G a ≠ 0 := by
  constructor
  · intro ha hzero
    have : IsUnit (augmentation (ZMod p) G a) := ha.map _
    simp [hzero] at this
  · intro ha
    classical
    letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    letI := Fintype.ofFinite G
    letI : Fintype (MonoidAlgebra (ZMod p) G) := Finsupp.fintype
    rw [IsUnit.isUnit_iff_mulRight_bijective, ← Finite.injective_iff_bijective]
    exact rightMul_injective_of_augmentation_ne_zero p G hG a ha

/-- The augmentation ideal of a finite modular `p`-group algebra is
nilpotent. -/
theorem augmentationIdeal_isNilpotent (hG : IsPGroup p G) :
    IsNilpotent (augmentationIdeal (ZMod p) G) := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI := Fintype.ofFinite G
  letI : Fintype (MonoidAlgebra (ZMod p) G) := Finsupp.fintype
  letI : IsArtinianRing (MonoidAlgebra (ZMod p) G) :=
    IsArtinianRing.of_finite (ZMod p) (MonoidAlgebra (ZMod p) G)
  have hle : augmentationIdeal (ZMod p) G ≤
      Ideal.jacobson (⊥ : Ideal (MonoidAlgebra (ZMod p) G)) := by
    intro x hx
    rw [Ideal.mem_jacobson_iff]
    intro y
    have hu : IsUnit (y * x + 1) :=
      (isUnit_iff_augmentation_ne_zero p G hG _).mpr (by
        rw [map_add, map_mul, map_one]
        change augmentation (ZMod p) G x = 0 at hx
        rw [hx, mul_zero, zero_add]
        exact one_ne_zero)
    obtain ⟨u, hu⟩ := hu
    refine ⟨↑u⁻¹, ?_⟩
    simp only [Ideal.mem_bot]
    calc
      ↑u⁻¹ * y * x + ↑u⁻¹ - 1 = ↑u⁻¹ * (y * x + 1) - 1 := by
        rw [mul_assoc, mul_add, mul_one]
      _ = 0 := by rw [← hu, Units.inv_mul, sub_self]
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot
    (R := MonoidAlgebra (ZMod p) G)
  refine ⟨n, eq_bot_iff.mpr ?_⟩
  exact (Ideal.pow_right_mono hle n).trans (le_of_eq hn)

end PGroup

end Submission.GroupAlgebra
