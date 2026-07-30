import Submission.OddOrder.MathlibSupport.AbelianPGroupOmegaAction
import Submission.OddOrder.MathlibSupport.CharacteristicPerfectCoprimePGroup
import Submission.OddOrder.MathlibSupport.CommutatorSup
import Submission.OddOrder.MathlibSupport.CoprimeSolvableCentralProduct
import Submission.OddOrder.MathlibSupport.NilpotencyClassTwoPowers
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial

/-!
Odd coprime actions on finite `p`-groups.

The main theorem is `BGsection1.coprime_odd_faithful_Ohm1` (Bender--
Glauberman Theorem 1.11).  We use strong induction on the normal `p`-factor;
the perfect noncommutative branch is the characteristic-special reduction,
and its final power calculation uses the class-two `p`th-power homomorphism.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}

omit [Finite G] in
/-- Centralization of omega one descends to every subgroup. -/
theorem centralizes_map_omegaOne_of_le
    {p : ℕ} {H : Subgroup G} (hHK : H ≤ K)
    (homega : R ≤ Subgroup.centralizer
      (((omegaOne p K).map K.subtype : Subgroup G) : Set G)) :
    R ≤ Subgroup.centralizer
      (((omegaOne p H).map H.subtype : Subgroup G) : Set G) := by
  let toK : H →* K :=
    { toFun := fun h ↦ ⟨h, hHK h.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hmap : (omegaOne p H).map H.subtype ≤
      (omegaOne p K).map K.subtype := by
    rintro _ ⟨h, hh, rfl⟩
    let hK : K := toK h
    have hhK : hK ∈ omegaOne p K :=
      map_omegaOne_le p toK (Subgroup.mem_map_of_mem toK hh)
    exact ⟨hK, hhK, rfl⟩
  exact homega.trans (Subgroup.centralizer_le hmap)

/-- The final special-group power calculation in the odd omega-one theorem. -/
theorem special_perfect_action_centralizes_of_centralizes_omegaOne
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hKp : IsPGroup p K)
    (hKspecial : IsSpecial K)
    (hcenterPow : ∀ z : Subgroup.center K, z ^ p = 1)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hperfect : ⁅R, K⁆ = K)
    (homega : R ≤ Subgroup.centralizer
      (((omegaOne p K).map K.subtype : Subgroup G) : Set G)) :
    R ≤ Subgroup.centralizer (K : Set G) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hcentral : _root_.commutator K ≤ Subgroup.center K :=
    hKspecial.commutator_eq_center.le
  have hcommPow : ∀ c : K, c ∈ _root_.commutator K → c ^ p = 1 := by
    intro c hc
    exact congrArg (fun z : Subgroup.center K ↦ (z : K))
      (hcenterPow ⟨c, hcentral hc⟩)
  let f : K →* K :=
    primePowerMonoidHomOfCommutatorLeCenter
      p hp hpodd hcentral hcommPow
  have hcross : ⁅R, K⁆ ≤ (omegaOne p K).map K.subtype := by
    rw [Subgroup.commutator_le]
    intro r hr k hk
    let rn : Subgroup.normalizer (K : Set G) := ⟨r, hnormK hr⟩
    let x : K := ⟨k, hk⟩
    let y : K := K.normalizerMonoidHom rn x
    have hxpowCenter : x ^ p ∈ Subgroup.center K := by
      rw [← hKspecial.frattini_eq_center]
      exact IsPGroup.pow_prime_mem_frattini hKp x
    let z : Subgroup.center K := ⟨x ^ p, hxpowCenter⟩
    have hzpow : (z : K) ^ p = 1 :=
      congrArg (fun t : Subgroup.center K ↦ (t : K)) (hcenterPow z)
    have hzOmega : (z : K) ∈ omegaOne p K :=
      mem_omegaOne_of_pow_eq_one p hzpow
    have hzOmegaG : ((z : K) : G) ∈ (omegaOne p K).map K.subtype :=
      ⟨(z : K), hzOmega, rfl⟩
    have hrz : r * ((z : K) : G) = ((z : K) : G) * r :=
      (Subgroup.mem_centralizer_iff.mp (homega hr) _ hzOmegaG).symm
    have hypow : y ^ p = x ^ p := by
      change (K.normalizerMonoidHom rn x) ^ p = x ^ p
      rw [← map_pow]
      apply Subtype.ext
      change r * (((x ^ p : K) : G)) * r⁻¹ = ((x ^ p : K) : G)
      simpa [z] using congrArg (fun t : G ↦ t * r⁻¹) hrz
    have hfpow : f y = f x := by
      change y ^ p = x ^ p
      exact hypow
    let c : K := y * x⁻¹
    have hfc : f c = 1 := by
      dsimp [c]
      rw [map_mul, map_inv, hfpow, mul_inv_cancel]
    have hcpow : c ^ p = 1 := by
      simpa [f] using hfc
    refine ⟨c, mem_omegaOne_of_pow_eq_one p hcpow, ?_⟩
    change ((c : K) : G) = ⁅r, k⁆
    simp [c, y, x, rn, commutatorElement_def, mul_assoc]
  have hKomega : K ≤ (omegaOne p K).map K.subtype := by
    intro k hk
    apply hcross
    rw [hperfect]
    exact hk
  exact homega.trans (Subgroup.centralizer_le hKomega)

/-- `BGsection1.coprime_odd_faithful_Ohm1`, in an omega-one subgroup form. -/
theorem coprime_odd_faithful_omegaOne
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (hKp : IsPGroup p K)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : (Nat.card K).Coprime (Nat.card R))
    (homega : R ≤ Subgroup.centralizer
      (((omegaOne p K).map K.subtype : Subgroup G) : Set G)) :
    R ≤ Subgroup.centralizer (K : Set G) := by
  classical
  let hp : p.Prime := Fact.out
  let P : ℕ → Prop := fun n ↦
    ∀ (K' : Subgroup G), Nat.card K' = n →
      IsPGroup p K' →
      R ≤ Subgroup.normalizer (K' : Set G) →
      (Nat.card K').Coprime (Nat.card R) →
      R ≤ Subgroup.centralizer
        (((omegaOne p K').map K'.subtype : Subgroup G) : Set G) →
      R ≤ Subgroup.centralizer (K' : Set G)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [P]
      intro K' hcard hK'p hnormK' hcop' homega'
      letI : Group.IsNilpotent K' := hK'p.isNilpotent
      let D : Subgroup G := ⁅R, K'⁆
      let C : Subgroup G := centralizerWithin K' R
      have hDK : D ≤ K' := by
        dsimp [D]
        exact Subgroup.le_normalizer_iff_commutator_le_right.mp hnormK'
      have hdecomp : K' ≤ D ⊔ C := by
        simpa [D, C] using
          le_commutator_sup_centralizerWithin_of_coprime hnormK' hcop'
      rcases lt_or_eq_of_le hDK with hDlt | hDeq
      · have hcardD : Nat.card D < n := by
          rw [← hcard]
          exact natCard_subgroup_lt_of_lt hDlt
        let toK : D →* K' :=
          { toFun := fun d ↦ ⟨d, hDK d.property⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl }
        have hDp : IsPGroup p D :=
          hK'p.of_injective toK (fun a b hab ↦
            Subtype.ext (congrArg (fun z : K' ↦ (z : G)) hab))
        have hnormD : R ≤ Subgroup.normalizer (D : Set G) := by
          dsimp [D]
          exact Subgroup.normalizer_commutator_ge_left R K'
        have hcopD : (Nat.card D).Coprime (Nat.card R) :=
          hcop'.coprime_dvd_left (Subgroup.card_dvd_of_le hDK)
        have homegaD : R ≤ Subgroup.centralizer
            (((omegaOne p D).map D.subtype : Subgroup G) : Set G) :=
          centralizes_map_omegaOne_of_le hDK homega'
        have hcentralD : R ≤ Subgroup.centralizer (D : Set G) :=
          ih (Nat.card D) hcardD D rfl hDp hnormD hcopD homegaD
        have hcentralC : R ≤ Subgroup.centralizer (C : Set G) := by
          intro r hr
          rw [Subgroup.mem_centralizer_iff]
          intro c hc
          exact ((mem_centralizerWithin.mp hc).2 r hr).symm
        have hRD : ⁅R, D⁆ ≤ (⊥ : Subgroup G) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentralD).le
        have hRC : ⁅R, C⁆ ≤ (⊥ : Subgroup G) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentralC).le
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact le_bot_iff.mp
          (commutator_le_of_le_sup_of_normal hdecomp hRD hRC)
      · have hperfect : ⁅R, K'⁆ = K' := by
          simpa [D] using hDeq
        by_cases hK'comm : IsMulCommutative K'
        · exact coprime_abelian_pGroup_centralized_of_pTorsion_centralized
            hK'p hK'comm hnormK' hcop' (by
              intro r hr
              rw [Subgroup.mem_centralizer_iff]
              intro x hx
              let xK : K' := ⟨x, hx.1⟩
              have hxpow : xK ^ p = 1 := by
                apply Subtype.ext
                exact hx.2
              have hxOmega : xK ∈ omegaOne p K' :=
                mem_omegaOne_of_pow_eq_one p hxpow
              have hxMap : (x : G) ∈ (omegaOne p K').map K'.subtype :=
                ⟨xK, hxOmega, rfl⟩
              exact Subgroup.mem_centralizer_iff.mp
                (homega' hr) x hxMap)
        · have hchar : ∀ (A : Subgroup K') [A.Characteristic],
              IsMulCommutative A →
              A.map K'.subtype ≤ Subgroup.centralizer (R : Set G) := by
            intro A _ hAcomm
            letI : IsMulCommutative A := hAcomm
            let HA : Subgroup G := A.map K'.subtype
            have hHAK : HA ≤ K' := by
              dsimp [HA]
              exact Subgroup.map_subtype_le A
            have hAneTop : A ≠ ⊤ := by
              intro hAtop
              apply hK'comm
              refine ⟨⟨fun x y ↦ ?_⟩⟩
              let xA : A := ⟨x, by rw [hAtop]; trivial⟩
              let yA : A := ⟨y, by rw [hAtop]; trivial⟩
              exact congrArg Subtype.val
                (show xA * yA = yA * xA from mul_comm xA yA)
            have hAlt : A < (⊤ : Subgroup K') :=
              lt_top_iff_ne_top.mpr hAneTop
            have hcardA : Nat.card A < Nat.card K' := by
              simpa using natCard_subgroup_lt_of_lt hAlt
            have hcardHAeq : Nat.card HA = Nat.card A := by
              dsimp [HA]
              exact Subgroup.card_map_of_injective K'.subtype_injective
            have hcardHA : Nat.card HA < n := by
              rw [hcardHAeq, ← hcard]
              exact hcardA
            let toK : HA →* K' :=
              { toFun := fun a ↦ ⟨a, hHAK a.property⟩
                map_one' := rfl
                map_mul' := fun _ _ ↦ rfl }
            have hHAp : IsPGroup p HA :=
              hK'p.of_injective toK (fun a b hab ↦
                Subtype.ext (congrArg (fun z : K' ↦ (z : G)) hab))
            have hnormHA : R ≤ Subgroup.normalizer (HA : Set G) := by
              rw [Subgroup.le_normalizer_iff]
              exact characteristic_map_subtype_invariant_under_normalizer
                K' R A hnormK'
            have hcopHA : (Nat.card HA).Coprime (Nat.card R) :=
              hcop'.coprime_dvd_left (Subgroup.card_dvd_of_le hHAK)
            have homegaHA : R ≤ Subgroup.centralizer
                (((omegaOne p HA).map HA.subtype : Subgroup G) : Set G) :=
              centralizes_map_omegaOne_of_le hHAK homega'
            have hcentralHA : R ≤ Subgroup.centralizer (HA : Set G) :=
              ih (Nat.card HA) hcardHA HA rfl hHAp hnormHA hcopHA homegaHA
            intro a ha
            rw [Subgroup.mem_centralizer_iff]
            intro r hr
            exact (Subgroup.mem_centralizer_iff.mp
              (hcentralHA hr) a ha).symm
          obtain ⟨hKspecial, _hfixed, hcenterPow⟩ :=
            isSpecial_and_centralizerWithin_eq_center_of_characteristic_abelian_coprime
              hp hK'p hK'comm hnormK' hcop' hperfect hchar
          exact special_perfect_action_centralizes_of_centralizes_omegaOne
            hp hpodd hK'p hKspecial hcenterPow hnormK' hperfect homega'
  exact hP (Nat.card K) K rfl hKp hnormK hcop homega

/-- Source-shaped form of `coprime_odd_faithful_Ohm1`, deriving oddness of
the prime from oddness of the nontrivial `p`-group. -/
theorem coprime_odd_faithful_omegaOne_of_odd_card
    {p : ℕ} [Fact p.Prime]
    (hKp : IsPGroup p K)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : (Nat.card K).Coprime (Nat.card R))
    (hodd : Odd (Nat.card K))
    (homega : R ≤ Subgroup.centralizer
      (((omegaOne p K).map K.subtype : Subgroup G) : Set G)) :
    R ≤ Subgroup.centralizer (K : Set G) := by
  by_cases hK : K = ⊥
  · subst K
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk1 : k = 1 := Subgroup.mem_bot.mp hk
    subst k
    simp
  · letI : Nontrivial K :=
      (Subgroup.nontrivial_iff_ne_bot K).mpr hK
    have hpodd : Odd p := hodd.of_dvd_nat
      (hKp.card_eq_or_dvd.resolve_left
        (ne_of_gt (Finite.one_lt_card (α := K))))
    exact coprime_odd_faithful_omegaOne
      hpodd hKp hnormK hcop homega

end Submission.OddOrder.MathlibSupport
