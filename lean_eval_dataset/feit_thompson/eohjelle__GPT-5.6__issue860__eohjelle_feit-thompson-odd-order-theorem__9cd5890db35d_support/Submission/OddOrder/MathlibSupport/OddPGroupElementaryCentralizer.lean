import Submission.OddOrder.MathlibSupport.CoprimeNilpotentCentralizer
import Submission.OddOrder.MathlibSupport.OddPGroupOmegaAction

/-!
Elementary-abelian detection for odd coprime actions.

This is `BGsection1.coprime_odd_faithful_cent_abelem`, Bender--Glauberman
Corollary 1.12, in the set-valued `pTorsionCentralizerWithin` notation used
by Section 6.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]

/-- `BGsection1.coprime_odd_faithful_cent_abelem`. -/
theorem coprime_odd_faithful_centralizes_of_pTorsionCentralizer
    {p : ℕ} [Fact p.Prime] {K R E : Subgroup G}
    (hE : IsPElementaryIn p K E)
    (hKp : IsPGroup p K)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : (Nat.card K).Coprime (Nat.card R))
    (hodd : Odd (Nat.card K))
    (hfix : R ≤ Subgroup.centralizer
      (pTorsionCentralizerWithin p K E)) :
    R ≤ Subgroup.centralizer (K : Set G) := by
  classical
  letI : Group.IsNilpotent K := hKp.isNilpotent
  let C : Subgroup G := centralizerWithin K R
  let CC : Subgroup G := centralizerWithin K C
  have hEK : E ≤ K := hE.1
  have hEcomm : IsMulCommutative E := hE.2.commutative
  letI : IsMulCommutative E := hEcomm
  have hEpow (e : E) : e ^ p = 1 := hE.2.pow_eq_one e
  have hEC : E ≤ C := by
    intro e he
    refine ⟨hEK he, ?_⟩
    intro r hr
    have heCentE : e ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val
        (mul_comm (⟨x, hx⟩ : E) (⟨e, he⟩ : E))
    have hePow : e ^ p = 1 :=
      congrArg Subtype.val (hEpow ⟨e, he⟩)
    exact (Subgroup.mem_centralizer_iff.mp (hfix hr) e
      ⟨hEK he, heCentE, hePow⟩).symm
  have hCCK : CC ≤ K := centralizerWithin_le_left K C
  have hnormCC : R ≤ Subgroup.normalizer (CC : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hnormK hr) x).mp hx.1, ?_⟩
      intro c hc
      have hrc : r * c = c * r := by
        exact (mem_centralizerWithin.mp hc).2 r hr
      have hcr : Commute c r := hrc.symm
      have hxc : c * x = x * c := hx.2 c hc
      calc
        c * (r * x * r⁻¹) = (c * r) * x * r⁻¹ := by group
        _ = (r * c) * x * r⁻¹ := by rw [hcr.eq]
        _ = r * (c * x) * r⁻¹ := by group
        _ = r * (x * c) * r⁻¹ := by rw [hxc]
        _ = r * x * (c * r⁻¹) := by group
        _ = r * x * (r⁻¹ * c) := by rw [hcr.inv_right.eq]
        _ = (r * x * r⁻¹) * c := by group
    · exact (Subgroup.card_map_of_injective
        (MulAut.conj r).injective).ge
  let toK : CC →* K :=
    { toFun := fun c ↦ ⟨c, hCCK c.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hCCp : IsPGroup p CC :=
    hKp.of_injective toK (fun a b hab ↦
      Subtype.ext (congrArg (fun z : K ↦ (z : G)) hab))
  have hcopCC : (Nat.card CC).Coprime (Nat.card R) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hCCK)
  have hoddCC : Odd (Nat.card CC) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_le hCCK)
  have homegaCC : R ≤ Subgroup.centralizer
      (((omegaOne p CC).map CC.subtype : Subgroup G) : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    rw [Subgroup.map_le_iff_le_comap]
    apply omegaOne_le
    intro x hxpow
    change (x : G) ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hxK : (x : G) ∈ K := hCCK x.property
    have hxCentE : (x : G) ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact x.property.2 e (hEC he)
    have hxPowG : (x : G) ^ p = 1 := congrArg Subtype.val hxpow
    exact (Subgroup.mem_centralizer_iff.mp (hfix hr) (x : G)
      ⟨hxK, hxCentE, hxPowG⟩).symm
  have hcentralCC : R ≤ Subgroup.centralizer (CC : Set G) :=
    coprime_odd_faithful_omegaOne_of_odd_card
      hCCp hnormCC hcopCC hoddCC homegaCC
  have hself : CC ≤ C := by
    intro x hx
    refine ⟨hCCK hx, ?_⟩
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp
      (hcentralCC hr) x hx).symm
  exact coprime_nilpotent_centralizes_of_selfCentralizing_fixedPoints
    hnormK hcop hself

end Submission.OddOrder.MathlibSupport
