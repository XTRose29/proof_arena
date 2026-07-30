import Submission.OddOrder.BG.Section03.OddPrimeSemidirectCharacteristic
import Submission.OddOrder.BG.Section03.OddPrimeSemidirectNonabelianReduction
import Submission.OddOrder.MathlibSupport.CharacteristicPerfectPGroup

/-!
The nonabelian faithful branch of Bender-Glauberman Theorem 3.4 has an
extraspecial prime-power kernel.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V] [Finite V]

noncomputable section

/-- All Section 3 reductions before the extraspecial representation theorem. -/
theorem kernel_commutator_le_representation_ker_of_extraspecial_cases
    [IsSolvable G]
    (rho : Representation k G V)
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hRprime : (Nat.card R).Prime)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : Representation.invariants
      (rho.comp R.subtype : Representation k R V) = ⊥)
    (ih : OddPrimeSemidirectGlobalInductionHypothesis.{u, v, w}
      k (Nat.card G))
    (extraspecialCase :
      ∀ (q : ℕ), q.Prime → IsPGroup q K → ⁅R, K⁆ = K → K ≠ ⊥ →
      ∀ (W : Type w) [AddCommGroup W] [Module k W] [Finite W]
        (sigma : Representation k G W) [Representation.IsIrreducible sigma],
        Function.Injective sigma →
        Representation.invariants
          (sigma.comp R.subtype : Representation k R W) = ⊥ →
        ¬IsMulCommutative K →
        (Subgroup.center K).map K.subtype ≤ Subgroup.center G →
        IsCyclic (Subgroup.center G) →
        IsExtraspecial K →
        centralizerWithin K R = (Subgroup.center K).map K.subtype →
        False) :
    ⁅R, K⁆ ≤ rho.ker := by
  apply kernel_commutator_le_representation_ker_of_nonabelian_cases
    rho hKR hnormK hcop hodd hRprime hGcard hfix ih
  intro q hq hKq hperfect hKne W _ _ _ sigma _ hsigma hfixsigma
    hKnonabelian hcyclicCenter
  have hchar : ∀ (H : Subgroup K) [H.Characteristic],
      IsMulCommutative H →
      H.map K.subtype ≤ Subgroup.centralizer (R : Set G) := by
    intro H _ hHcomm
    have hHlt : H < ⊤ := by
      apply lt_of_le_of_ne le_top
      intro hHtop
      apply hKnonabelian
      apply IsMulCommutative.of_comm
      intro x y
      let xH : H := ⟨x, by rw [hHtop]; trivial⟩
      let yH : H := ⟨y, by rw [hHtop]; trivial⟩
      letI : IsMulCommutative H := hHcomm
      exact congrArg Subtype.val (mul_comm' xH yH)
    exact properCharacteristic_map_le_centralizer sigma hsigma hKR hnormK
      hcop hodd hRprime hGcard hfixsigma (ih.toSubgroup sigma) H hHlt
  obtain ⟨hspecial, hfixed, hcenterPow⟩ :=
    isSpecial_and_centralizerWithin_eq_center_of_characteristic_abelian
      hq hKq hKnonabelian hKR hnormK hRprime hperfect hchar
  have hmapCenter : (Subgroup.center K).map K.subtype ≤
      Subgroup.center G := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨kr, hkr, _⟩ := hKR.existsUnique g
    have hkcomm : (kr.1 : G) * (z : G) = (z : G) * (kr.1 : G) := by
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hz kr.1)
    have hzfixed : (z : G) ∈ centralizerWithin K R := by
      rw [hfixed]
      exact ⟨z, hz, rfl⟩
    have hrcomm : (kr.2 : G) * (z : G) = (z : G) * (kr.2 : G) :=
      Subgroup.mem_centralizer_iff.mp hzfixed.2 kr.2 kr.2.property
    rw [← hkr]
    calc
      (kr.1 : G) * (kr.2 : G) * (z : G) =
          (kr.1 : G) * ((kr.2 : G) * (z : G)) := by group
      _ = (kr.1 : G) * ((z : G) * (kr.2 : G)) := by rw [hrcomm]
      _ = ((kr.1 : G) * (z : G)) * (kr.2 : G) := by group
      _ = ((z : G) * (kr.1 : G)) * (kr.2 : G) := by rw [hkcomm]
      _ = (z : G) * ((kr.1 : G) * (kr.2 : G)) := by group
  let centerHom : Subgroup.center K →* Subgroup.center G :=
    { toFun := fun z ↦ ⟨((z : K) : G),
        hmapCenter ⟨z, z.property, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hcenterHom : Function.Injective centerHom := by
    intro x y hxy
    have hG := congrArg Subtype.val hxy
    change ((x : K) : G) = ((y : K) : G) at hG
    apply Subtype.ext
    apply Subtype.ext
    exact hG
  letI : IsCyclic (Subgroup.center G) := hcyclicCenter
  letI : IsCyclic (Subgroup.center K) :=
    isCyclic_of_injective centerHom hcenterHom
  have hcenterNe : Subgroup.center K ≠ ⊥ := by
    intro hbot
    apply hKnonabelian
    exact (_root_.commutator_eq_bot_iff K).mp (by
      rw [hspecial.commutator_eq_center, hbot])
  obtain ⟨z, hzorder⟩ :=
    (IsCyclic.exists_ofOrder_eq_natCard (α := Subgroup.center K))
  have hcardDvd : Nat.card (Subgroup.center K) ∣ q := by
    rw [← hzorder]
    exact orderOf_dvd_of_pow_eq_one (hcenterPow z)
  have hcenterCard : Nat.card (Subgroup.center K) = q := by
    rcases (Nat.dvd_prime hq).mp hcardDvd with hone | hqcard
    · exact False.elim
        ((Subgroup.one_lt_card_iff_ne_bot (Subgroup.center K)).mpr hcenterNe
          |>.ne hone.symm)
    · exact hqcard
  let hextra : IsExtraspecial K :=
    { toIsSpecial := hspecial
      center_card_prime := by rw [hcenterCard]; exact hq }
  exact extraspecialCase q hq hKq hperfect hKne W sigma hsigma hfixsigma
    hKnonabelian hmapCenter hcyclicCenter hextra hfixed

end

end Submission.OddOrder.BG.Section03
