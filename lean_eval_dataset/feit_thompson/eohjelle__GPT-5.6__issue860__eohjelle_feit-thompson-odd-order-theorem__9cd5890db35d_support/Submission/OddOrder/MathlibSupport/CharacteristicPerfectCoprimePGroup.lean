import Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect
import Submission.OddOrder.MathlibSupport.CharacteristicPerfectPGroup
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
The characteristic-subgroup core of `abelian_charsimple_special` for an
arbitrary coprime actor.

The prime-order version lives in `CharacteristicPerfectPGroup`.  The only
place where primeness of the actor was used there is the assertion that fixed
points of the induced perfect action on the abelianization are trivial.  The
action-norm argument proves that assertion for every coprime actor.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}

private theorem centralizerWithin_le_commutator_of_perfect_coprime_action_of_normal
    [K.Normal]
    (hcop : (Nat.card K).Coprime (Nat.card R))
    (hperfect : ⁅R, K⁆ = K) :
    centralizerWithin K R ≤ ⁅K, K⁆ := by
  classical
  let N : Subgroup G := ⁅K, K⁆
  letI : N.Normal := by
    dsimp [N]
    infer_instance
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Kq : Subgroup (G ⧸ N) := K.map q
  let Rq : Subgroup (G ⧸ N) := R.map q
  letI : Kq.Normal :=
    Subgroup.Normal.map (inferInstance : K.Normal) q
      (QuotientGroup.mk'_surjective N)
  have hKqComm : ⁅Kq, Kq⁆ = ⊥ := by
    dsimp [Kq]
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    simp [q, QuotientGroup.ker_mk', N]
  letI : IsMulCommutative Kq := by
    have hcent : Kq ≤ Subgroup.centralizer (Kq : Set (G ⧸ N)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKqComm
    refine ⟨⟨fun x y ↦ ?_⟩⟩
    apply Subtype.ext
    exact hcent y.property x x.property
  have hperfectq : ⁅Rq, Kq⁆ = Kq := by
    dsimp [Rq, Kq]
    rw [← Subgroup.map_commutator, hperfect]
  have hcopq : (Nat.card Kq).Coprime (Nat.card Rq) := by
    have hKdiv : Nat.card Kq ∣ Nat.card K :=
      Subgroup.card_map_dvd K q
    have hRdiv : Nat.card Rq ∣ Nat.card R :=
      Subgroup.card_map_dvd R q
    exact (hcop.coprime_dvd_left hKdiv).coprime_dvd_right hRdiv
  have hnormKq : Rq ≤ Subgroup.normalizer (Kq : Set (G ⧸ N)) := by
    rw [Kq.normalizer_eq_top]
    exact le_top
  intro c hc
  let cq : Kq := ⟨q c, ⟨c, hc.1, rfl⟩⟩
  have hfix : ∀ r : Rq,
      (r : G ⧸ N) * (cq : G ⧸ N) * (r : G ⧸ N)⁻¹ =
        (cq : G ⧸ N) := by
    intro r
    rcases r.property with ⟨r₀, hr₀, hr⟩
    have hcomm : r₀ * c = c * r₀ :=
      (mem_centralizerWithin.mp hc).2 r₀ hr₀
    change (r : G ⧸ N) * q c * (r : G ⧸ N)⁻¹ = q c
    rw [← hr]
    calc
      q r₀ * q c * (q r₀)⁻¹ = q (r₀ * c * r₀⁻¹) := by simp
      _ = q c := by rw [hcomm]; simp
  have hcq : cq = 1 :=
    Submission.OddOrder.BG.Section06.fixed_eq_one_of_abelian_perfect_coprime_conjugation
      hnormKq hcopq hperfectq cq hfix
  change c ∈ N
  apply (QuotientGroup.eq_one_iff c).mp
  exact congrArg Subtype.val hcq

/-- Under a perfect coprime action, the actor-fixed subgroup is contained in
the derived subgroup. -/
theorem centralizerWithin_le_commutator_of_perfect_coprime_action
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : (Nat.card K).Coprime (Nat.card R))
    (hperfect : ⁅R, K⁆ = K) :
    centralizerWithin K R ≤ ⁅K, K⁆ := by
  classical
  let L : Subgroup G := K ⊔ R
  let KL : Subgroup L := K.subgroupOf L
  let RL : Subgroup L := R.subgroupOf L
  have hKLmap : KL.map L.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le (show K ≤ L from le_sup_left)
  have hRLmap : RL.map L.subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le (show R ≤ L from le_sup_right)
  have hcardKL : Nat.card KL = Nat.card K :=
    natCard_subgroupOf_eq (show K ≤ L from le_sup_left)
  have hcardRL : Nat.card RL = Nat.card R :=
    natCard_subgroupOf_eq (show R ≤ L from le_sup_right)
  have hnormKLambient : L ≤ Subgroup.normalizer (K : Set G) := by
    dsimp [L]
    exact sup_le Subgroup.le_normalizer hnormK
  letI : KL.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormKLambient
  have hcopL : (Nat.card KL).Coprime (Nat.card RL) := by
    simpa [hcardKL, hcardRL] using hcop
  have hperfectL : ⁅RL, KL⁆ = KL := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, hRLmap, hKLmap, hperfect]
  have hinside : centralizerWithin KL RL ≤ ⁅KL, KL⁆ :=
    centralizerWithin_le_commutator_of_perfect_coprime_action_of_normal
      hcopL hperfectL
  intro c hc
  let cL : L := ⟨c, (show K ≤ L from le_sup_left) hc.1⟩
  have hcL : cL ∈ centralizerWithin KL RL := by
    refine ⟨hc.1, ?_⟩
    intro r hr
    apply Subtype.ext
    exact (mem_centralizerWithin.mp hc).2 (r : G) hr
  have hcMap : (c : G) ∈ ⁅KL, KL⁆.map L.subtype :=
    ⟨cL, hinside hcL, rfl⟩
  rw [Subgroup.map_commutator, hKLmap] at hcMap
  exact hcMap

/-- Under a perfect coprime action, if every characteristic abelian subgroup
of a `p`-group centralizes the actor, then the derived subgroup and the fixed
subgroup both equal the center. -/
theorem commutator_eq_center_and_centralizerWithin_eq_center_of_characteristic_abelian_coprime
    {p : ℕ} (hp : p.Prime) (hKp : IsPGroup p K)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : (Nat.card K).Coprime (Nat.card R))
    (hperfect : ⁅R, K⁆ = K)
    (hchar : ∀ (H : Subgroup K) [H.Characteristic],
      IsMulCommutative H →
      H.map K.subtype ≤ Subgroup.centralizer (R : Set G)) :
    _root_.commutator K = Subgroup.center K ∧
      centralizerWithin K R = (Subgroup.center K).map K.subtype := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Group.IsNilpotent K := hKp.isNilpotent
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
      (centralizerWithin_le_commutator_of_perfect_coprime_action
        hnormK hcop hperfect)
  have hcommCenter : _root_.commutator K = Subgroup.center K :=
    le_antisymm hcomm_le_center hcenter_le_comm
  refine ⟨hcommCenter, le_antisymm ?_ ?_⟩
  · exact (centralizerWithin_le_commutator_of_perfect_coprime_action
      hnormK hcop hperfect).trans_eq
        (K.map_subtype_commutator.symm.trans
          (congrArg (fun H : Subgroup K ↦ H.map K.subtype) hcommCenter))
  · exact le_inf (Subgroup.map_subtype_le _) hcharCenter

/-- Coprime-actor form of MathComp's `abelian_charsimple_special`: the
characteristic-abelian hypothesis makes the prime-power kernel special, and
its actor-fixed subgroup is its center. -/
theorem isSpecial_and_centralizerWithin_eq_center_of_characteristic_abelian_coprime
    {p : ℕ} (hp : p.Prime) (hKp : IsPGroup p K)
    (hKnonabelian : ¬IsMulCommutative K)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : (Nat.card K).Coprime (Nat.card R))
    (hperfect : ⁅R, K⁆ = K)
    (hchar : ∀ (H : Subgroup K) [H.Characteristic],
      IsMulCommutative H →
      H.map K.subtype ≤ Subgroup.centralizer (R : Set G)) :
    IsSpecial K ∧
      centralizerWithin K R = (Subgroup.center K).map K.subtype ∧
      ∀ z : Subgroup.center K, z ^ p = 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hcore :=
    commutator_eq_center_and_centralizerWithin_eq_center_of_characteristic_abelian_coprime
      hp hKp hnormK hcop hperfect hchar
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
  obtain ⟨e, he, hcard⟩ := hKp.nontrivial_iff_card.mp inferInstance
  have hPe : iteratedPowerSubgroup p e K = ⊥ := by
    apply le_bot_iff.mp
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    apply Subgroup.mem_bot.mpr
    rw [← hcard]
    exact pow_card_eq_one'
  have hPone : iteratedPowerSubgroup p 1 K ≤ Subgroup.center K := by
    refine Nat.decreasingInduction'
      (P := fun n ↦ iteratedPowerSubgroup p n K ≤ Subgroup.center K)
      (m := 1) (n := e) ?_ he ?_
    · intro n _hne h1n ih
      have hn : 0 < n := Nat.zero_lt_of_lt h1n
      have hPcomm : IsMulCommutative (iteratedPowerSubgroup p n K) :=
        iteratedPowerSubgroup_isMulCommutative_of_succ_le_center
          hcomm.le p n hn ih
      exact hchar_le_center (iteratedPowerSubgroup p n K) hPcomm
    · rw [hPe]
      exact bot_le
  have hpowCenter (x : K) : x ^ p ∈ Subgroup.center K := by
    simpa using hPone (pow_mem_iteratedPowerSubgroup p 1 x)
  let Z : Subgroup K := Subgroup.center K
  let pi : K →* K ⧸ Z := QuotientGroup.mk' Z
  letI : IsMulCommutative (K ⧸ Z) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      simpa [Z] using hcomm.le)
  have hpowQuotient (x : K ⧸ Z) : x ^ p = 1 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z x
    change pi (x ^ p) = 1
    exact (QuotientGroup.eq_one_iff (x ^ p)).mpr (hpowCenter x)
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
    exact IsPGroup.commutator_le_frattini hKp
  have hcenterPow : ∀ z : Subgroup.center K, z ^ p = 1 :=
    center_pow_eq_one_of_commutator_eq_center_of_pow_mem_center
      p hcomm hpowCenter
  exact ⟨⟨le_antisymm hfrattini_le hcenter_le, hcomm⟩, hfixed, hcenterPow⟩

end Submission.OddOrder.MathlibSupport
