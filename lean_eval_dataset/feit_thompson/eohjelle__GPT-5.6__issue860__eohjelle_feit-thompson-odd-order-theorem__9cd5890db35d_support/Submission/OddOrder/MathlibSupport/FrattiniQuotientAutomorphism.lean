import Submission.OddOrder.MathlibSupport.CharacteristicQuotientAction
import Submission.OddOrder.MathlibSupport.CoprimeSolvableCentralProduct
import Submission.OddOrder.MathlibSupport.FrattiniPGroup
import Submission.OddOrder.MathlibSupport.PGroupPrimeOrderCriterion
import Mathlib.GroupTheory.SemidirectProduct

/-!
Automorphisms of a finite `p`-group acting on its Frattini quotient.

The kernel statement is the automorphism form of the Burnside basis
theorem: automorphisms which act trivially modulo the Frattini subgroup form
a `p`-group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- The canonical action of the automorphism group on the Frattini quotient. -/
noncomputable def frattiniQuotientMulAutHom
    (P : Type u) [Group P] :
    MulAut P →* MulAut (P ⧸ frattini P) := by
  letI : MulAction.QuotientAction (MulAut P) (frattini P) :=
    characteristicQuotientAction (frattini P)
  letI : MulDistribMulAction (MulAut P) (P ⧸ frattini P) :=
    (QuotientGroup.mk'_surjective (frattini P)).mulDistribMulAction
      (QuotientGroup.mk' (frattini P)) (fun _ _ ↦ rfl)
  exact MulDistribMulAction.toMulAut (MulAut P) (P ⧸ frattini P)

/-- The quotient action is induced by the original automorphism. -/
@[simp] theorem frattiniQuotientMulAutHom_apply_mk
    {P : Type u} [Group P]
    (a : MulAut P) (x : P) :
    frattiniQuotientMulAutHom P a
        (QuotientGroup.mk' (frattini P) x) =
      QuotientGroup.mk' (frattini P) (a x) := by
  classical
  letI : MulAction.QuotientAction (MulAut P) (frattini P) :=
    characteristicQuotientAction (frattini P)
  letI : MulDistribMulAction (MulAut P) (P ⧸ frattini P) :=
    (QuotientGroup.mk'_surjective (frattini P)).mulDistribMulAction
      (QuotientGroup.mk' (frattini P)) (fun _ _ ↦ rfl)
  change a • (x : P ⧸ frattini P) = (a x : P ⧸ frattini P)
  exact MulAction.Quotient.smul_coe (frattini P) a x

/-- The Burnside-basis kernel theorem for finite `p`-groups. -/
theorem frattiniQuotientMulAutHom_ker_isPGroup
    {P : Type u} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) :
    IsPGroup p (frattiniQuotientMulAutHom P).ker := by
  classical
  apply isPGroup_of_prime_order_elements
  intro q hq hqp a haOrder
  letI : Fact q.Prime := ⟨hq⟩
  let B : Subgroup (MulAut P) :=
    (frattiniQuotientMulAutHom P).ker
  let C : Subgroup B := Subgroup.zpowers a
  let phi : C →* MulAut P := B.subtype.comp C.subtype
  let X := P ⋊[phi] C
  let K : Subgroup X := (SemidirectProduct.inl : P →* X).range
  let A : Subgroup X := (SemidirectProduct.inr : C →* X).range
  let eK : P ≃* K :=
    MonoidHom.ofInjective
      (SemidirectProduct.inl_injective (N := P) (G := C) (φ := phi))
  let eA : C ≃* A :=
    MonoidHom.ofInjective
      (SemidirectProduct.inr_injective (N := P) (G := C) (φ := phi))
  letI : Finite X := by
    dsimp [X]
    exact Finite.of_equiv (P × C)
      (SemidirectProduct.equivProd (N := P) (G := C) (φ := phi)).symm
  have hKp : IsPGroup p K := hP.of_equiv eK
  letI : Group.IsNilpotent K := hKp.isNilpotent
  letI : IsSolvable K := inferInstance
  have hAcard : Nat.card A = q := by
    calc
      Nat.card A = Nat.card C := Nat.card_congr eA.toEquiv.symm
      _ = q := by simpa [C, Nat.card_zpowers] using haOrder
  have hAq : IsPGroup q A := by
    apply IsPGroup.of_card
    rw [hAcard, pow_one]
  have hcop : (Nat.card K).Coprime (Nat.card A) :=
    IsPGroup.coprime_card_of_ne p q (Ne.symm hqp) K A hKp hAq
  letI : K.Normal := by
    dsimp [K]
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hnorm : A ≤ Subgroup.normalizer (K : Set X) := by
    rw [K.normalizer_eq_top]
    exact le_top
  let F : Subgroup X :=
    (frattini P).map (SemidirectProduct.inl : P →* X)
  have hFK : F ≤ K := by
    rintro _ ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  have hcomm : ⁅A, K⁆ ≤ F := by
    apply Subgroup.commutator_le.mpr
    intro g hg k hk
    rcases hg with ⟨c, rfl⟩
    rcases hk with ⟨x, rfl⟩
    have hcKer :
        frattiniQuotientMulAutHom P (phi c) = 1 := by
      exact (C.subtype c).property
    have hcFix :
        QuotientGroup.mk' (frattini P) (phi c x) =
          QuotientGroup.mk' (frattini P) x := by
      calc
        QuotientGroup.mk' (frattini P) (phi c x) =
            frattiniQuotientMulAutHom P (phi c)
              (QuotientGroup.mk' (frattini P) x) :=
          (frattiniQuotientMulAutHom_apply_mk (phi c) x).symm
        _ = QuotientGroup.mk' (frattini P) x := by rw [hcKer]; rfl
    have hdiff : phi c x * x⁻¹ ∈ frattini P := by
      apply (QuotientGroup.eq_one_iff (phi c x * x⁻¹)).mp
      change QuotientGroup.mk' (frattini P) (phi c x * x⁻¹) = 1
      rw [map_mul, map_inv, hcFix, mul_inv_cancel]
    refine ⟨phi c x * x⁻¹, hdiff, ?_⟩
    rw [map_mul, map_inv, SemidirectProduct.inl_aut]
    simp only [map_inv, commutatorElement_def]
  have hdecomp : K ≤ ⁅A, K⁆ ⊔ centralizerWithin K A :=
    le_commutator_sup_centralizerWithin_of_coprime hnorm hcop
  have hdecompF : K ≤ F ⊔ centralizerWithin K A :=
    hdecomp.trans (sup_le_sup hcomm le_rfl)
  let FK : Subgroup K := F.subgroupOf K
  let D : Subgroup K := (centralizerWithin K A).subgroupOf K
  have hsup : FK ⊔ D = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hFK (centralizerWithin_le_left K A)]
    apply top_unique
    intro k _hk
    exact hdecompF k.property
  have hFKfrattini : FK ≤ frattini K := by
    have hmap : frattini P ≤
        (frattini K).comap eK.toMonoidHom :=
      frattini_le_comap_frattini_of_surjective eK.surjective
    intro z hz
    change (z : X) ∈ F at hz
    rcases hz with ⟨x, hx, hxz⟩
    have hxK : eK x ∈ frattini K := hmap hx
    have heq : eK x = z := by
      apply Subtype.ext
      exact hxz
    exact heq ▸ hxK
  have hDsup : D ⊔ frattini K = ⊤ := by
    apply top_unique
    rw [← hsup]
    exact sup_le (hFKfrattini.trans le_sup_right) le_sup_left
  have hDtop : D = ⊤ := frattini_nongenerating hDsup
  apply Subtype.ext
  change (a : MulAut P) = 1
  apply MulEquiv.ext
  intro x
  let ac : C := ⟨a, Subgroup.mem_zpowers a⟩
  let kx : K := eK x
  have hkxD : kx ∈ D := by
    rw [hDtop]
    trivial
  have hkxCent : (kx : X) ∈ centralizerWithin K A := hkxD
  have hacA : SemidirectProduct.inr ac ∈ A := ⟨ac, rfl⟩
  have hmul :=
    (mem_centralizerWithin.mp hkxCent).2
      (SemidirectProduct.inr ac) hacA
  have hleft := congrArg SemidirectProduct.left hmul
  have hkxval : (kx : X) = SemidirectProduct.inl x := rfl
  rw [hkxval] at hleft
  dsimp [X] at hleft
  simp only [one_mul, map_one, mul_one] at hleft
  have hfix : phi ac x = x := hleft
  simpa [phi, ac, B, C] using hfix

end Submission.OddOrder.MathlibSupport
