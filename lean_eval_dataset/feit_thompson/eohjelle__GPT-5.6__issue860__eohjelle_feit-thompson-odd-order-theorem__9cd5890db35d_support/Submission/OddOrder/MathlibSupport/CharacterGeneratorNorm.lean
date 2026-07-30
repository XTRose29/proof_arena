import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Submission.OddOrder.MathlibSupport.CharacterValueCyclotomic

/-!
# The algebraic norm of character values on cyclic generators

For a complex representation of a finite cyclic group, the character values
on the generators form one complete cyclotomic Galois orbit.  Their product is
therefore the field norm of an algebraic integer and hence an integer.  Taking
complex norm-squares turns that integer into the square of its absolute value.

This is the algebraic-integer half of MathComp's
`sum_norm2_char_generators` (Isaacs, Lemma 3.14).
-/

namespace Submission.OddOrder.MathlibSupport

noncomputable section

open Module
open scoped BigOperators Cyclotomic

universe u

/-- The elements which generate a finite cyclic group. -/
def cyclicGenerators (L : Type u) [Group L] [Fintype L] : Finset L := by
  classical
  exact Finset.univ.filter fun x => Subgroup.zpowers x = ⊤

@[simp]
theorem mem_cyclicGenerators {L : Type u} [Group L] [Fintype L]
    {x : L} :
    x ∈ cyclicGenerators L ↔ Subgroup.zpowers x = ⊤ := by
  simp [cyclicGenerators]

private theorem zpowers_pow_eq_top_iff_coprime_card
    {L : Type u} [Group L] [Fintype L]
    {g : L} (hg : ∀ x : L, x ∈ Subgroup.zpowers g) (k : ℕ) :
    Subgroup.zpowers (g ^ k) = ⊤ ↔ Nat.Coprime k (Fintype.card L) := by
  have horder : orderOf g = Fintype.card L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  constructor
  · intro htop
    have hmem : g ∈ Subgroup.zpowers (g ^ k) := by
      rw [htop]
      exact Subgroup.mem_top g
    simpa [horder] using (mem_zpowers_pow_iff.mp hmem)
  · intro hcop
    apply (Subgroup.eq_top_iff' _).2
    intro x
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    exact Subgroup.zpow_mem _
      (mem_zpowers_pow_iff.mpr (by simpa [horder] using hcop)) m

/-- Powers indexed by units modulo the group order enumerate the generators
of a finite cyclic group without repetition. -/
private theorem prod_character_generators_eq_prod_units
    {L : Type u} [Group L] [Fintype L]
    {M : Type*} [CommMonoid M]
    (g : L) (hg : ∀ x : L, x ∈ Subgroup.zpowers g) (f : L → M) :
    ∏ x ∈ cyclicGenerators L, f x =
      ∏ a : (ZMod (Fintype.card L))ˣ, f (g ^ a.val.val) := by
  classical
  symm
  refine Finset.prod_bij
    (fun a (_ha : a ∈ (Finset.univ : Finset (ZMod (Fintype.card L))ˣ)) =>
      g ^ a.val.val) ?_ ?_ ?_ ?_
  · intro a _ha
    rw [mem_cyclicGenerators,
      zpowers_pow_eq_top_iff_coprime_card hg]
    exact ZMod.val_coe_unit_coprime a
  · intro a₁ _ha₁ a₂ _ha₂ hpow
    apply Units.ext
    rw [pow_eq_pow_iff_modEq,
      orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card] at hpow
    rw [← ZMod.natCast_zmod_val (a₁ : ZMod (Fintype.card L)),
      ← ZMod.natCast_zmod_val (a₂ : ZMod (Fintype.card L))]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hpow
  · intro x hx
    have hxgen : Subgroup.zpowers x = ⊤ := mem_cyclicGenerators.mp hx
    obtain ⟨a, ha, _hauniq⟩ := IsCyclic.unique_zpow_zmod hg x
    have hcop : Nat.Coprime a.val (Fintype.card L) := by
      apply (zpowers_pow_eq_top_iff_coprime_card hg a.val).mp
      simpa [ha] using hxgen
    let b : (ZMod (Fintype.card L))ˣ := ZMod.unitOfCoprime a.val hcop
    refine ⟨b, Finset.mem_univ b, ?_⟩
    have hb : (b : ZMod (Fintype.card L)) = a := by
      simpa [b] using (ZMod.natCast_zmod_val a)
    have hbval : b.val.val = a.val := congrArg ZMod.val hb
    exact (congrArg (fun k : ℕ => g ^ k) hbval).trans ha.symm
  · intro a _ha
    rfl

/-- The product of the character values on all generators of a finite cyclic
group is an integer. -/
theorem character_generator_product_intCast
    {L : Type u} [Group L] [Fintype L] [IsCyclic L]
    (V : FDRep ℂ L) :
    ∃ z : ℤ, ∏ x ∈ cyclicGenerators L, V.character x = (z : ℂ) := by
  classical
  let n := Fintype.card L
  letI : NeZero n := ⟨Fintype.card_ne_zero⟩
  letI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero n ℚ
  letI : IsGalois ℚ (CyclotomicField n ℚ) :=
    IsCyclotomicExtension.isGalois {n} ℚ (CyclotomicField n ℚ)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L)
  let ι : CyclotomicField n ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ζK : CyclotomicField n ℚ :=
    IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)
  have hζK : IsPrimitiveRoot ζK n :=
    IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  have hζℂval : IsPrimitiveRoot (ι ζK) n :=
    hζK.map_of_injective ι.injective
  let ζℂ : ℂˣ := Units.mk0 (ι ζK)
    (hζℂval.ne_zero (NeZero.ne n))
  have hζℂ : IsPrimitiveRoot ζℂ n := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [ζℂ] using hζℂval
  let T : Module.End ℂ V := V.ρ g
  have hTpow : T ^ n = 1 := by
    have horder : orderOf g = n := by
      simpa [n, Nat.card_eq_fintype_card] using
        (orderOf_eq_card_of_forall_mem_zpowers hg)
    have hgn : g ^ n = 1 := by
      exact orderOf_dvd_iff_pow_eq_one.mp (horder.symm ▸ dvd_rfl)
    simp [T, ← map_pow, hgn]
  let d : ZMod n → ℕ := fun i =>
    Module.finrank ℂ
      (Module.End.eigenspace T
        (primitiveRootUnitWeight hζℂ i : ℂ))
  let q : CyclotomicField n ℚ :=
    ∑ i : ZMod n, (d i : CyclotomicField n ℚ) * ζK ^ i.val
  have hweight (i : ZMod n) :
      (primitiveRootUnitWeight hζℂ i : ℂ) = (ι ζK) ^ i.val := by
    conv_lhs =>
      rw [← ZMod.natCast_zmod_val i,
        primitiveRootUnitWeight_natCast]
    rfl
  have hq_action (σ : Gal(CyclotomicField n ℚ/ℚ)) :
      ι (σ q) =
        V.character
          (g ^ (IsCyclotomicExtension.Rat.galEquivZMod
            n (CyclotomicField n ℚ) σ).val.val) := by
    let k := (IsCyclotomicExtension.Rat.galEquivZMod
      n (CyclotomicField n ℚ) σ).val.val
    have hσζ : σ ζK = ζK ^ k := by
      exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
        n (CyclotomicField n ℚ) σ hζK.pow_eq_one
    have htrace := trace_pow_eq_sum_primitiveRootUnitWeight
      hζℂ T hTpow k
    change ι (σ q) = LinearMap.trace ℂ V (V.ρ (g ^ k))
    rw [map_pow]
    rw [htrace]
    simp only [q, map_sum, map_mul, map_natCast, map_pow, hσζ]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hweight]
    congr 1
    · simp only [d]
      rw [hweight i]
    · rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hq_integral : IsIntegral ℤ q := by
    apply IsIntegral.sum
    intro i _hi
    exact (isIntegral_natCast (d i)).mul
      ((hζK.isIntegral (NeZero.pos n)).pow i.val)
  have hnorm_integral : IsIntegral ℤ (Algebra.norm ℚ q) :=
    @Algebra.isIntegral_norm ℤ _ (CyclotomicField n ℚ) ℚ _ _ _ _ _
      (CyclotomicField.instIsScalarTower n ℤ ℚ) q hq_integral
  obtain ⟨z : ℤ, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnorm_integral
  refine ⟨z, ?_⟩
  calc
    ∏ x ∈ cyclicGenerators L, V.character x =
        ∏ a : (ZMod n)ˣ, V.character (g ^ a.val.val) := by
      simpa [n] using
        (prod_character_generators_eq_prod_units g hg V.character)
    _ = ∏ σ : Gal(CyclotomicField n ℚ/ℚ),
          V.character
            (g ^ (IsCyclotomicExtension.Rat.galEquivZMod
              n (CyclotomicField n ℚ) σ).val.val) := by
      symm
      exact Fintype.prod_equiv
        (IsCyclotomicExtension.Rat.galEquivZMod
          n (CyclotomicField n ℚ)).toEquiv
        (fun σ : Gal(CyclotomicField n ℚ/ℚ) =>
          V.character
            (g ^ (IsCyclotomicExtension.Rat.galEquivZMod
              n (CyclotomicField n ℚ) σ).val.val))
        (fun a : (ZMod n)ˣ => V.character (g ^ a.val.val))
        (fun _ => rfl)
    _ = ∏ σ : Gal(CyclotomicField n ℚ/ℚ), ι (σ q) := by
      apply Finset.prod_congr rfl
      intro σ _hσ
      exact (hq_action σ).symm
    _ = ι (algebraMap ℚ (CyclotomicField n ℚ) (Algebra.norm ℚ q)) := by
      rw [Algebra.norm_eq_prod_automorphisms, map_prod]
    _ = ((Algebra.norm ℚ q : ℚ) : ℂ) := by
      simp [ι]
    _ = (z : ℂ) := by
      rw [← hz]
      simp

/-- For a complex representation of a finite cyclic group, the product of
the squared absolute values of its character on the generators is a natural
number.  No nonvanishing hypothesis is needed for the integrality statement. -/
theorem character_generator_normSq_product_natCast
    {L : Type u} [Group L] [Fintype L] [IsCyclic L]
    (V : FDRep ℂ L) :
    ∃ m : ℕ,
      (∏ x ∈ cyclicGenerators L, Complex.normSq (V.character x)) =
        (m : ℝ) := by
  obtain ⟨z, hz⟩ := character_generator_product_intCast V
  refine ⟨z.natAbs ^ 2, ?_⟩
  calc
    ∏ x ∈ cyclicGenerators L, Complex.normSq (V.character x) =
        Complex.normSq (∏ x ∈ cyclicGenerators L, V.character x) := by
      exact (map_prod Complex.normSq _ _).symm
    _ = Complex.normSq (z : ℂ) := by rw [hz]
    _ = (z : ℝ) * (z : ℝ) := Complex.normSq_intCast z
    _ = (z.natAbs ^ 2 : ℕ) := by
      norm_num [pow_two, Int.natCast_natAbs]

end

end Submission.OddOrder.MathlibSupport
