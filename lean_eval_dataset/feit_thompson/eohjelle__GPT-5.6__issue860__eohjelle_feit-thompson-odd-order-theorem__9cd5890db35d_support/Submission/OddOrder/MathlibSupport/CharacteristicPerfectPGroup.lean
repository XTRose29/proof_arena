import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.CentralCommutatorPowers
import Submission.OddOrder.MathlibSupport.Extraspecial
import Submission.OddOrder.MathlibSupport.FrattiniPGroup
import Submission.OddOrder.MathlibSupport.NilpotentNormalCenter
import Submission.OddOrder.MathlibSupport.PerfectActionAbelianization
import Submission.OddOrder.MathlibSupport.PerfectActionCentralSubgroup
import Submission.OddOrder.MathlibSupport.UpperCentralDerived

/-!
The characteristic-subgroup core of `abelian_charsimple_special`.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}

/-- Under a perfect prime-order action, if every characteristic abelian
subgroup of a `p`-group centralizes the actor, then the derived subgroup and
the fixed subgroup both equal the center. -/
theorem commutator_eq_center_and_centralizerWithin_eq_center
    {q : ℕ} (hq : q.Prime) (hKq : IsPGroup q K)
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hRprime : (Nat.card R).Prime)
    (hperfect : ⁅R, K⁆ = K)
    (hchar : ∀ (H : Subgroup K) [H.Characteristic],
      IsMulCommutative H →
      H.map K.subtype ≤ Subgroup.centralizer (R : Set G)) :
    _root_.commutator K = Subgroup.center K ∧
      centralizerWithin K R = (Subgroup.center K).map K.subtype := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  letI : Group.IsNilpotent K := hKq.isNilpotent
  have hcharCenter : (Subgroup.center K).map K.subtype ≤
      Subgroup.centralizer (R : Set G) :=
    hchar (Subgroup.center K) inferInstance
  have hchar_le_center (H : Subgroup K) [H.Characteristic]
      (hHcomm : IsMulCommutative H) : H ≤ Subgroup.center K := by
    have hnormH : K ≤
        Subgroup.normalizer (H.map K.subtype : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      exact characteristic_map_subtype_invariant_under_normalizer
        K K H Subgroup.le_normalizer
    have hHcentral : H.map K.subtype ≤
        Subgroup.centralizer (K : Set G) :=
      le_centralizer_of_normalized_of_centralized_of_perfect_action
        hnormH (by
          rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
            Subgroup.commutator_comm]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
            (hchar H hHcomm)) hperfect
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxmap : (x : G) ∈ H.map K.subtype := ⟨x, hx, rfl⟩
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hHcentral hxmap) y y.property
  let H0 : Subgroup K :=
    Subgroup.upperCentralSeries K 2 ⊓ _root_.commutator K
  letI : H0.Characteristic := by
    dsimp [H0]
    apply Subgroup.characteristic_iff_map_le.mpr
    intro e
    rw [Subgroup.map_inf_eq _ _ _ e.injective]
    exact inf_le_inf
      (Subgroup.characteristic_iff_map_le.mp
        (inferInstance : (Subgroup.upperCentralSeries K 2).Characteristic) e)
      (Subgroup.characteristic_iff_map_le.mp
        (inferInstance : (_root_.commutator K).Characteristic) e)
  have hH0comm : IsMulCommutative H0 := by
    simpa [H0] using
      (inf_upperCentralSeries_two_commutator_isMulCommutative (G := K))
  have hH0center : H0 ≤ Subgroup.center K :=
    hchar_le_center H0 hH0comm
  let Z : Subgroup K := Subgroup.center K
  let pi : K →* K ⧸ Z := QuotientGroup.mk' Z
  let Dq : Subgroup (K ⧸ Z) := _root_.commutator (K ⧸ Z)
  have hmapD : (_root_.commutator K).map pi = Dq := by
    change ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆.map pi =
      ⁅(⊤ : Subgroup (K ⧸ Z)), (⊤ : Subgroup (K ⧸ Z))⁆
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective pi (QuotientGroup.mk'_surjective Z)]
  have hcomapCenter :
      (Subgroup.center (K ⧸ Z)).comap pi =
        Subgroup.upperCentralSeries K 2 := by
    simpa [Z, pi] using
      (Subgroup.comap_upperCentralSeries_quotient_center (G := K) 1)
  have hDqInf : Dq ⊓ Subgroup.center (K ⧸ Z) = ⊥ := by
    apply le_bot_iff.mp
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
    have hxZ2 : x ∈ Subgroup.upperCentralSeries K 2 := by
      have hx : x ∈ (Subgroup.center (K ⧸ Z)).comap pi := hy.2
      rw [hcomapCenter] at hx
      exact hx
    have hxDq : pi x ∈ Dq := hy.1
    rw [← hmapD] at hxDq
    rcases hxDq with ⟨d, hdD, hdx⟩
    have hz : d⁻¹ * x ∈ Z := QuotientGroup.eq.mp hdx
    have hZleZ2 : Z ≤ Subgroup.upperCentralSeries K 2 := by
      dsimp [Z]
      rw [← Subgroup.upperCentralSeries_one K]
      exact Subgroup.upperCentralSeries_mono K (by omega)
    have hdZ2 : d ∈ Subgroup.upperCentralSeries K 2 := by
      have heq : d = x * (d⁻¹ * x)⁻¹ := by group
      rw [heq]
      exact (Subgroup.upperCentralSeries K 2).mul_mem hxZ2
        ((Subgroup.upperCentralSeries K 2).inv_mem (hZleZ2 hz))
    have hdZ : d ∈ Z := hH0center ⟨hdZ2, hdD⟩
    apply Subgroup.mem_bot.mpr
    calc
      pi x = pi d := hdx.symm
      _ = 1 := (QuotientGroup.eq_one_iff d).mpr hdZ
  have hDqbot : Dq = ⊥ := by
    by_contra hDq
    have hmeet := nilpotent_normal_inf_center_ne_bot Dq hDq
    exact hmeet hDqInf
  have hcomm_le_center : _root_.commutator K ≤ Subgroup.center K := by
    have hmapbot : (_root_.commutator K).map pi = ⊥ := hmapD.trans hDqbot
    have hle := (Subgroup.map_eq_bot_iff (_root_.commutator K)).mp hmapbot
    simpa [pi, Z, QuotientGroup.ker_mk'] using hle
  have hcenter_le_comm : Subgroup.center K ≤ _root_.commutator K := by
    apply (Subgroup.map_le_map_iff_of_injective K.subtype_injective).mp
    rw [Subgroup.map_subtype_commutator]
    exact (le_inf (Subgroup.map_subtype_le _) hcharCenter).trans
      (centralizerWithin_le_commutator_of_prime_perfect_action
        hKR hnormK hRprime hperfect)
  have hcommCenter : _root_.commutator K = Subgroup.center K :=
    le_antisymm hcomm_le_center hcenter_le_comm
  refine ⟨hcommCenter, le_antisymm ?_ ?_⟩
  · exact (centralizerWithin_le_commutator_of_prime_perfect_action
      hKR hnormK hRprime hperfect).trans_eq
        (K.map_subtype_commutator.symm.trans
          (congrArg (fun H : Subgroup K ↦ H.map K.subtype) hcommCenter))
  · exact le_inf (Subgroup.map_subtype_le _) hcharCenter

/-- Mathlib-shaped `abelian_charsimple_special`: the characteristic-abelian
hypothesis makes the prime-power kernel special, and its actor-fixed subgroup
is its center. -/
theorem isSpecial_and_centralizerWithin_eq_center_of_characteristic_abelian
    {q : ℕ} (hq : q.Prime) (hKq : IsPGroup q K)
    (hKnonabelian : ¬IsMulCommutative K)
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hRprime : (Nat.card R).Prime)
    (hperfect : ⁅R, K⁆ = K)
    (hchar : ∀ (H : Subgroup K) [H.Characteristic],
      IsMulCommutative H →
      H.map K.subtype ≤ Subgroup.centralizer (R : Set G)) :
    IsSpecial K ∧
      centralizerWithin K R = (Subgroup.center K).map K.subtype ∧
      ∀ z : Subgroup.center K, z ^ q = 1 := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  have hcore := commutator_eq_center_and_centralizerWithin_eq_center
    hq hKq hKR hnormK hRprime hperfect hchar
  rcases hcore with ⟨hcomm, hfixed⟩
  have hchar_le_center (H : Subgroup K) [H.Characteristic]
      (hHcomm : IsMulCommutative H) : H ≤ Subgroup.center K := by
    have hnormH : K ≤
        Subgroup.normalizer (H.map K.subtype : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      exact characteristic_map_subtype_invariant_under_normalizer
        K K H Subgroup.le_normalizer
    have hcentralR : R ≤
        Subgroup.centralizer (H.map K.subtype : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
        Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hchar H hHcomm)
    have hHcentral : H.map K.subtype ≤
        Subgroup.centralizer (K : Set G) :=
      le_centralizer_of_normalized_of_centralized_of_perfect_action
        hnormH hcentralR hperfect
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp
      (hHcentral ⟨x, hx, rfl⟩) y y.property
  letI : Nontrivial K := by
    by_contra htriv
    haveI : Subsingleton K := not_nontrivial_iff_subsingleton.mp htriv
    exact hKnonabelian inferInstance
  obtain ⟨e, he, hcard⟩ := hKq.nontrivial_iff_card.mp inferInstance
  have hPe : iteratedPowerSubgroup q e K = ⊥ := by
    apply le_bot_iff.mp
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    apply Subgroup.mem_bot.mpr
    rw [← hcard]
    exact pow_card_eq_one'
  have hPone : iteratedPowerSubgroup q 1 K ≤ Subgroup.center K := by
    refine Nat.decreasingInduction'
      (P := fun n ↦ iteratedPowerSubgroup q n K ≤ Subgroup.center K)
      (m := 1) (n := e) ?_ he ?_
    · intro n _hne h1n ih
      have hn : 0 < n := Nat.zero_lt_of_lt h1n
      have hPcomm : IsMulCommutative (iteratedPowerSubgroup q n K) :=
        iteratedPowerSubgroup_isMulCommutative_of_succ_le_center
          hcomm.le q n hn ih
      exact hchar_le_center (iteratedPowerSubgroup q n K) hPcomm
    · rw [hPe]
      exact bot_le
  have hpowCenter (x : K) : x ^ q ∈ Subgroup.center K := by
    simpa using hPone (pow_mem_iteratedPowerSubgroup q 1 x)
  let Z : Subgroup K := Subgroup.center K
  let pi : K →* K ⧸ Z := QuotientGroup.mk' Z
  letI : IsMulCommutative (K ⧸ Z) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      simpa [Z] using hcomm.le)
  have hpowQuotient (x : K ⧸ Z) : x ^ q = 1 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z x
    change pi (x ^ q) = 1
    exact (QuotientGroup.eq_one_iff (x ^ q)).mpr (hpowCenter x)
  have hfrattiniQuotient : frattini (K ⧸ Z) = ⊥ :=
    IsPGroup.frattini_eq_bot_of_isMulCommutative_of_pow_prime hpowQuotient
  have hfrattini_le : frattini K ≤ Subgroup.center K := by
    have hle := frattini_le_comap_frattini_of_surjective
      (φ := pi) (QuotientGroup.mk'_surjective Z)
    rw [hfrattiniQuotient, MonoidHom.comap_bot,
      QuotientGroup.ker_mk'] at hle
    simpa [Z] using hle
  have hcenter_le : Subgroup.center K ≤ frattini K := by
    rw [← hcomm]
    exact IsPGroup.commutator_le_frattini hKq
  have hcenterPow : ∀ z : Subgroup.center K, z ^ q = 1 :=
    center_pow_eq_one_of_commutator_eq_center_of_pow_mem_center
      q hcomm hpowCenter
  exact ⟨⟨le_antisymm hfrattini_le hcenter_le, hcomm⟩, hfixed, hcenterPow⟩

end Submission.OddOrder.MathlibSupport
