import Mathlib.GroupTheory.SemidirectProduct
import Submission.OddOrder.MathlibSupport.CharacteristicMulAutRestriction
import Submission.OddOrder.MathlibSupport.Critical
import Submission.OddOrder.MathlibSupport.OddPGroupOmegaAction

/-!
The omega-one detection step for automorphisms of critical subgroups.

The source proves this by induction on element orders inside the critical
subgroup.  The port packages the exact prime-order consequence needed by
`critical_odd`, using the already established odd coprime omega-one action
theorem after restriction to the characteristic subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- A prime-order automorphism, of order different from `p`, which fixes the
ambient image of `Ω₁(H)` pointwise also fixes the critical subgroup `H`
pointwise.  This is the precise omega-one fixer step used in the construction
of MathComp's `critical_odd`. -/
theorem critical_fixes_of_fixes_map_omegaOne_of_prime_order
    {p q : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : IsCritical H) (hHp : IsPGroup p H)
    (hHodd : Odd (Nat.card H)) (hq : q.Prime) (hqp : q ≠ p)
    (a : MulAut G) (haOrder : orderOf a = q)
    (haOmega : a ∈ fixingSubgroup (MulAut G)
      (((omegaOne p H).map H.subtype : Subgroup G) : Set G)) :
    a ∈ fixingSubgroup (MulAut G) (H : Set G) := by
  classical
  letI : H.Characteristic := hH.characteristic
  let g : MulAut H := characteristicRestrictMulAutHom H a
  have haPow : a ^ q = 1 := by
    rw [← haOrder]
    exact pow_orderOf_eq_one a
  have hgPow : g ^ q = 1 := by
    dsimp [g]
    rw [← map_pow, haPow, map_one]
  have hgOmega : ∀ z : H, z ∈ omegaOne p H → g z = z := by
    intro z hz
    have hfix := haOmega
    rw [mem_fixingSubgroup_iff] at hfix
    apply Subtype.ext
    simpa [g] using hfix (z : G) ⟨z, hz, rfl⟩
  have hgOne : g = 1 := by
    by_contra hgNe
    have hgOrder : orderOf g = q := by
      rcases (Nat.dvd_prime hq).mp
          (orderOf_dvd_of_pow_eq_one hgPow) with hgOrder | hgOrder
      · exact (hgNe (orderOf_eq_one_iff.mp hgOrder)).elim
      · exact hgOrder
    let C : Subgroup (MulAut H) := Subgroup.zpowers g
    let phi : C →* MulAut H := C.subtype
    let X := H ⋊[phi] C
    letI : Finite X := by
      dsimp [X]
      exact Finite.of_equiv (H × C)
        (SemidirectProduct.equivProd (N := H) (G := C) (φ := phi)).symm
    let K : Subgroup X :=
      (SemidirectProduct.inl : H →* X).range
    let A : Subgroup X :=
      (SemidirectProduct.inr : C →* X).range
    let eK : H ≃* K :=
      MonoidHom.ofInjective
        (SemidirectProduct.inl_injective (N := H) (G := C) (φ := phi))
    let eA : C ≃* A :=
      MonoidHom.ofInjective
        (SemidirectProduct.inr_injective (N := H) (G := C) (φ := phi))
    have hKp : IsPGroup p K := hHp.of_equiv eK
    have hKodd : Odd (Nat.card K) := by
      rw [show Nat.card K = Nat.card H from Nat.card_congr eK.toEquiv.symm]
      exact hHodd
    have hAcard : Nat.card A = q := by
      calc
        Nat.card A = Nat.card C := Nat.card_congr eA.toEquiv.symm
        _ = q := by simpa [C, Nat.card_zpowers] using hgOrder
    have hAq : IsPGroup q A := by
      letI : Fact q.Prime := ⟨hq⟩
      apply IsPGroup.of_card (n := 1)
      rw [hAcard, pow_one]
    have hcop : (Nat.card K).Coprime (Nat.card A) := by
      letI : Fact q.Prime := ⟨hq⟩
      exact IsPGroup.coprime_card_of_ne p q (Ne.symm hqp)
        K A hKp hAq
    letI : K.Normal := by
      dsimp [K]
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      infer_instance
    have hnorm : A ≤ Subgroup.normalizer (K : Set X) := by
      rw [K.normalizer_eq_top]
      exact le_top
    have homega : A ≤ Subgroup.centralizer
        (((omegaOne p K).map K.subtype : Subgroup X) : Set X) := by
      intro ac hac
      rcases hac with ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rcases hw with ⟨wK, hwK, rfl⟩
      let z : H := eK.symm wK
      have hzOmega : z ∈ omegaOne p H := by
        apply map_omegaOne_le p eK.symm.toMonoidHom
        exact Subgroup.mem_map_of_mem eK.symm.toMonoidHom hwK
      have hgz : g • z = z := by
        change g z = z
        exact hgOmega z hzOmega
      have hcz : (c : MulAut H) • z = z :=
        smul_eq_self_of_mem_zpowers c.property hgz
      change (c : MulAut H) z = z at hcz
      have hwEq : K.subtype wK = SemidirectProduct.inl z := by
        exact congrArg Subtype.val (eK.apply_symm_apply wK).symm
      rw [hwEq]
      apply SemidirectProduct.ext
      · simpa [X, phi] using hcz.symm
      · simp [X, phi]
    have hcentral : A ≤ Subgroup.centralizer (K : Set X) :=
      coprime_odd_faithful_omegaOne_of_odd_card
        hKp hnorm hcop hKodd homega
    let c : C := ⟨g, Subgroup.mem_zpowers g⟩
    have hcA : (SemidirectProduct.inr c : X) ∈ A := ⟨c, rfl⟩
    apply hgNe
    apply MulEquiv.ext
    intro z
    have hzK : (SemidirectProduct.inl z : X) ∈ K := ⟨z, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp
      (hcentral hcA) (SemidirectProduct.inl z : X) hzK
    have hleft := congrArg SemidirectProduct.left hcomm
    simpa [X, phi, c] using hleft.symm
  rw [← characteristicRestrictMulAutHom_ker_eq_fixingSubgroup H,
    MonoidHom.mem_ker]
  exact hgOne

end Submission.OddOrder.MathlibSupport
