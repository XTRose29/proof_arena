import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Submission.OddOrder.MathlibSupport.CommutatorSup
import Submission.OddOrder.MathlibSupport.CyclicPrimePowerAutomorphism
import Submission.OddOrder.MathlibSupport.NilpotencyClassPowerMaps
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial
import Submission.OddOrder.MathlibSupport.PGroupCenter
import Submission.OddOrder.MathlibSupport.PrimeIndex

/-!
`BGsection4.v: Ohm1_extremal_odd` for finite odd `p`-groups.

The abelian branch follows from the `p`th-power homomorphism.  In the
noncommutative branch, conjugation on the cyclic maximal subgroup has order
dividing `p`; the odd prime-power unit calculation shows that it fixes all
`p`th powers.  The derived subgroup is consequently central of exponent `p`,
reducing the result to the same power-map argument.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative commutatorElement

universe u

variable {G : Type u} [Group G]

/-- If a homomorphism realizes the `p`th-power map, its kernel is the first
omega subgroup. -/
theorem omegaOne_eq_ker_of_apply_eq_pow (p : ℕ) (f : G →* G)
    (hf : ∀ x : G, f x = x ^ p) :
    omegaOne p G = f.ker := by
  apply le_antisymm
  · apply omegaOne_le
    intro x hx
    simpa [hf x] using hx
  · intro x hx
    apply mem_omegaOne_of_pow_eq_one
    simpa [hf x] using hx

/-- In a commutative group, the first omega subgroup is the kernel of the
`p`th-power homomorphism. -/
theorem omegaOne_eq_powMonoidHom_ker [IsMulCommutative G] (p : ℕ) :
    omegaOne p G = (powMonoidHom p : G →* G).ker :=
  omegaOne_eq_ker_of_apply_eq_pow (G := G) p
    (powMonoidHom p : G →* G) fun _ ↦ rfl

/-- The first omega subgroup of a nontrivial finite cyclic `p`-group has
order `p`. -/
theorem card_omegaOne_of_isCyclic_isPGroup [Finite G] [IsCyclic G]
    {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (hcard : Nat.card G ≠ 1) :
    Nat.card (omegaOne p G) = p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp_dvd : p ∣ Nat.card G :=
    hG.card_eq_or_dvd.resolve_left hcard
  rw [omegaOne_eq_powMonoidHom_ker,
    IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hp_dvd]

/-- In the noncommutative cyclic-maximal case, the cyclic subgroup has
order at least `p²`. -/
theorem exists_card_zpowers_eq_prime_pow_add_two_of_not_commutative
    [Finite G] {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (x : G) (hindex : (Subgroup.zpowers x).index = p)
    (hnoncommutative : ¬ IsMulCommutative G) :
    ∃ n : ℕ, Nat.card (Subgroup.zpowers x) = p ^ (n + 2) := by
  letI : Fact p.Prime := ⟨hp⟩
  let H : Subgroup G := Subgroup.zpowers x
  obtain ⟨m, hm⟩ := (hG.to_subgroup H).exists_card_eq
  have hGcard : Nat.card G = p ^ (m + 1) := by
    rw [← H.card_mul_index, hm, hindex, pow_succ]
  have hm2 : 2 ≤ m := by
    by_contra hmnot
    have hmle : m ≤ 1 := by omega
    interval_cases m
    · have hGprime : Nat.card G = p := by simpa using hGcard
      letI : IsCyclic G := isCyclic_of_prime_card hGprime
      exact hnoncommutative inferInstance
    · have hGsq : Nat.card G = p ^ 2 := by simpa using hGcard
      exact hnoncommutative
        (IsPGroup.isMulCommutative_of_card_eq_prime_sq hGsq)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm2
  refine ⟨n, ?_⟩
  change Nat.card H = p ^ (n + 2)
  simpa [Nat.add_comm] using hm

/-- A cyclic coatom together with one mixed commutator bound controls the
whole derived subgroup.  This is the lattice-theoretic step used in the
noncommutative cyclic-maximal case. -/
theorem commutator_le_of_isCoatom_isCyclic_of_commutator_le
    (H A : Subgroup G) [A.Normal] (hH : IsCoatom H) [IsCyclic H]
    (hmixed : ⁅H, ⊤⁆ ≤ A) :
    _root_.commutator G ≤ A := by
  obtain ⟨y, _, hy⟩ := SetLike.exists_of_lt hH.lt_top
  let Y : Subgroup G := Subgroup.zpowers y
  have hHYtop : H ⊔ Y = ⊤ := by
    rcases hH.le_iff.mp le_sup_left with htop | heq
    · exact htop
    · exfalso
      apply hy
      rw [← heq]
      exact (show Y ≤ H ⊔ Y from le_sup_right) (Subgroup.mem_zpowers y)
  have hHH : ⁅H, H⁆ ≤ A :=
    (Subgroup.commutator_mono le_rfl le_top).trans hmixed
  have hHY : ⁅H, Y⁆ ≤ A :=
    (Subgroup.commutator_mono le_rfl le_top).trans hmixed
  have hYH : ⁅Y, H⁆ ≤ A := by
    rw [Subgroup.commutator_comm]
    exact hHY
  have hYY : ⁅Y, Y⁆ ≤ A := by
    calc
      ⁅Y, Y⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        let aY : Y := ⟨a, ha⟩
        let bY : Y := ⟨b, hb⟩
        exact (congrArg Subtype.val (mul_comm aY bY)).symm)
      _ ≤ A := bot_le
  have hHsup : ⁅H, H ⊔ Y⁆ ≤ A :=
    commutator_sup_le_of_normal hHH hHY
  have hYsup : ⁅Y, H ⊔ Y⁆ ≤ A :=
    commutator_sup_le_of_normal hYH hYY
  have hsup : ⁅H ⊔ Y, H ⊔ Y⁆ ≤ A := by
    rw [Subgroup.commutator_comm]
    exact commutator_sup_le_of_normal
      (by simpa [Subgroup.commutator_comm] using hHsup)
      (by simpa [Subgroup.commutator_comm] using hYsup)
  simpa [hHYtop, _root_.commutator_def] using hsup

/-- A normal subgroup of prime order in a finite `p`-group is central. -/
theorem normal_le_center_of_card_eq_prime [Finite G]
    {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (A : Subgroup G) [A.Normal] (hAcard : Nat.card A = p) :
    A ≤ Subgroup.center G := by
  letI : Fact p.Prime := ⟨hp⟩
  have hAne : A ≠ ⊥ := by
    intro hA
    have hpone : p = 1 := by
      rw [← hAcard, hA]
      exact Nat.card_unique
    exact hp.ne_one hpone
  letI : Fact (Nat.card A).Prime := ⟨hAcard ▸ hp⟩
  rcases ((Subgroup.center G).subgroupOf A).eq_bot_or_eq_top_of_prime_card with
    hbot | htop
  · have hdisjoint : Disjoint A (Subgroup.center G) :=
      (disjoint_comm.mp (Subgroup.subgroupOf_eq_bot.mp hbot))
    have hinf : A ⊓ Subgroup.center G = ⊥ := disjoint_iff.mp hdisjoint
    exact (normal_inf_center_ne_bot hG A hAne hinf).elim
  · exact Subgroup.subgroupOf_eq_top.mp htop

/-- The converse of `commutator_le_center_of_nilpotencyClass_le_two`. -/
theorem nilpotencyClass_le_two_of_commutator_le_center
    [Group.IsNilpotent G]
    (hcentral : _root_.commutator G ≤ Subgroup.center G) :
    Group.nilpotencyClass G ≤ 2 := by
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ,
    Subgroup.top_lowerCentralSeries_one,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro g _
  exact Subgroup.mem_center_iff.mp (hcentral hz) g

/-- If conjugation fixes all `p`th powers in a cyclic normal subgroup, its
mixed commutators are contained in that subgroup's first omega subgroup. -/
theorem commutator_le_map_omegaOne_of_conjNormal_pow_eq
    (p : ℕ) (H : Subgroup G) [H.Normal] [IsCyclic H]
    (hfix : ∀ (g : G) (h : H), MulAut.conjNormal g (h ^ p) = h ^ p) :
    ⁅H, ⊤⁆ ≤ (omegaOne p H).map H.subtype := by
  rw [Subgroup.commutator_le]
  intro h hh g _
  let hH : H := ⟨h, hh⟩
  let c : H := MulAut.conjNormal g hH * hH⁻¹
  have hcpow : c ^ p = 1 := by
    rw [mul_pow]
    change MulAut.conjNormal g hH ^ p * (hH⁻¹) ^ p = 1
    rw [← map_pow, hfix]
    simp
  have hcA : (c : G) ∈ (omegaOne p H).map H.subtype := by
    exact ⟨c, mem_omegaOne_of_pow_eq_one p hcpow, rfl⟩
  have hcval : (c : G) = ⁅g, h⁆ := by
    simp [c, hH, commutatorElement_def, mul_assoc]
  rw [← commutatorElement_inv]
  exact ((omegaOne p H).map H.subtype).inv_mem (hcval ▸ hcA)

/-- Conjugation on a cyclic normal subgroup of index `p` has order dividing
`p`. -/
theorem conjNormal_pow_prime_eq_one_of_cyclic_index_prime
    [Finite G] {p : ℕ} (H : Subgroup G) [H.Normal] [IsCyclic H]
    (hindex : H.index = p) (g : G) :
    (MulAut.conjNormal g : MulAut H) ^ p = 1 := by
  have hgp : g ^ p ∈ H := by
    apply (QuotientGroup.eq_one_iff (g ^ p)).mp
    change (g : G ⧸ H) ^ p = 1
    rw [← hindex, H.index_eq_card]
    exact pow_card_eq_one'
  rw [← map_pow]
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  change g ^ p * (h : G) * (g ^ p)⁻¹ = h
  let gp : H := ⟨g ^ p, hgp⟩
  have hcomm : gp * h = h * gp := mul_comm gp h
  have hcommval := congrArg Subtype.val hcomm
  change g ^ p * (h : G) = (h : G) * g ^ p at hcommval
  rw [hcommval, mul_inv_cancel_right]

/-- A power-map form of `Ohm1_extremal_odd`.  Once the `p`th-power operation is
a homomorphism, the result follows without a classification: its range lies
between the `p`th powers of the cyclic maximal subgroup and that subgroup.
The latter inclusion must be strict, since otherwise a `p`th root of the
given generator would generate the whole group. -/
theorem omegaOne_isElementaryAbelianOfRank_two_of_cyclic_index_prime_of_powerMonoidHom
    [Finite G]
    {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (hnotcyclic : ¬ IsCyclic G) (x : G)
    (hindex : (Subgroup.zpowers x).index = p)
    (f : G →* G) (hf : ∀ y : G, f y = y ^ p) :
    IsElementaryAbelianOfRank p 2 (omegaOne p G) := by
  letI : Fact p.Prime := ⟨hp⟩
  let H : Subgroup G := Subgroup.zpowers x
  letI : H.Normal := normal_of_index_eq_prime hp hG hindex
  let K : Subgroup G := H.map f
  have hHcard_ne_one : Nat.card H ≠ 1 := by
    intro hHcard
    have hGcard : Nat.card G = p := by
      rw [← H.card_mul_index, hHcard, hindex, one_mul]
    exact hnotcyclic (isCyclic_of_prime_card hGcard)
  have hp_dvd_cardH : p ∣ Nat.card H :=
    (hG.to_subgroup H).card_eq_or_dvd.resolve_left hHcard_ne_one
  have hKH : K ≤ H := by
    rintro y ⟨z, hz, rfl⟩
    rw [hf]
    exact H.pow_mem hz p
  have hKrange : K ≤ f.range :=
    Subgroup.map_le_range (f := f) H
  have hRangeH : f.range ≤ H := by
    rintro _ ⟨y, rfl⟩
    rw [hf]
    apply (QuotientGroup.eq_one_iff (y ^ p)).mp
    change (y : G ⧸ H) ^ p = 1
    rw [← hindex, H.index_eq_card]
    exact pow_card_eq_one'
  let KH : Subgroup H := K.subgroupOf H
  let LH : Subgroup H := f.range.subgroupOf H
  have hKH_eq_range :
      KH = (powMonoidHom p : H →* H).range := by
    ext y
    constructor
    · rintro ⟨a, ha, hay⟩
      refine ⟨⟨a, ha⟩, ?_⟩
      apply Subtype.ext
      change a ^ p = y
      rw [← hf a, hay]
      rfl
    · rintro ⟨a, hay⟩
      refine ⟨a, a.property, ?_⟩
      have hayval := congrArg Subtype.val hay
      change f a = y
      rw [hf]
      exact hayval
  have hKHindex : KH.index = p := by
    rw [hKH_eq_range, IsCyclic.index_powMonoidHom_range]
    exact Nat.gcd_eq_right hp_dvd_cardH
  have hKHcoatom : IsCoatom KH :=
    isCoatom_of_index_eq_prime hp hKHindex
  have hKHLH : KH ≤ LH := by
    intro y hy
    exact hKrange hy
  have hLH_ne_top : LH ≠ ⊤ := by
    intro hLHtop
    have hRangeEqH : f.range = H := by
      apply le_antisymm hRangeH
      intro y hy
      have hyLH : (⟨y, hy⟩ : H) ∈ LH := by
        rw [hLHtop]
        exact Subgroup.mem_top _
      exact hyLH
    have hxrange : x ∈ f.range := hRangeEqH.symm.le (Subgroup.mem_zpowers x)
    obtain ⟨y, hy⟩ := hxrange
    have hypow : y ^ p = x := by
      simpa [hf y] using hy
    have hy_not_mem : y ∉ H := by
      intro hyH
      have hxK : x ∈ K := ⟨y, hyH, by simpa [hf y] using hypow⟩
      have hHK : H ≤ K := by
        simpa [H] using (Subgroup.zpowers_le.mpr hxK)
      have hK_eq_H : K = H := le_antisymm hKH hHK
      apply hKHcoatom.ne_top
      apply Subgroup.subgroupOf_eq_top.mpr
      simpa [hK_eq_H]
    have hHzpowers : H ≤ Subgroup.zpowers y := by
      apply Subgroup.zpowers_le.mpr
      rw [← hypow]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) p
    have hHcoatom : IsCoatom H :=
      isCoatom_of_index_eq_prime hp hindex
    rcases hHcoatom.le_iff.mp hHzpowers with htop | heq
    · exact hnotcyclic
        (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨y, htop⟩)
    · exact hy_not_mem (heq.symm ▸ Subgroup.mem_zpowers y)
  have hLH_eq_KH : LH = KH := by
    rcases hKHcoatom.le_iff.mp hKHLH with htop | heq
    · exact (hLH_ne_top htop).elim
    · exact heq
  have hRangeEqK : f.range = K := by
    apply le_antisymm
    · intro y hy
      have hyH := hRangeH hy
      have hyLH : (⟨y, hyH⟩ : H) ∈ LH := hy
      rw [hLH_eq_KH] at hyLH
      exact hyLH
    · exact hKrange
  have hKindex : K.index = p ^ 2 := by
    rw [← K.relIndex_mul_index hKH, hindex]
    change KH.index * p = p ^ 2
    rw [hKHindex, pow_two]
  have hkerCard : Nat.card f.ker = p ^ 2 := by
    rw [← Subgroup.index_range, hRangeEqK, hKindex]
  have homegaKer : omegaOne p G = f.ker :=
    omegaOne_eq_ker_of_apply_eq_pow p f hf
  refine
    { isPGroup := omegaOne_isPGroup p hG
      commutative := ?_
      pow_eq_one := ?_
      card_eq := ?_ }
  · rw [homegaKer]
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hkerCard
  · intro y
    apply Subtype.ext
    have hyker : (y : G) ∈ f.ker := by
      rw [← homegaKer]
      exact y.property
    simpa [hf (y : G)] using hyker
  · rw [homegaKer]
    exact hkerCard

/-- The abelian branch of MathComp's `Ohm1_extremal_odd`: a noncyclic finite
abelian `p`-group with a cyclic subgroup of index `p` has elementary-abelian
first omega subgroup of rank two. -/
theorem omegaOne_isElementaryAbelianOfRank_two_of_cyclic_index_prime_of_commutative
    [Finite G] [IsMulCommutative G]
    {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (hnotcyclic : ¬ IsCyclic G) (x : G)
    (hindex : (Subgroup.zpowers x).index = p) :
    IsElementaryAbelianOfRank p 2 (omegaOne p G) :=
  omegaOne_isElementaryAbelianOfRank_two_of_cyclic_index_prime_of_powerMonoidHom
    hp hG hnotcyclic x hindex (powMonoidHom p) fun _ ↦ rfl

/-- A small-nilpotency-class reduction of `Ohm1_extremal_odd`.  This is the
form needed after controlling conjugation on the cyclic maximal subgroup:
the class bound and the exponent-`p` derived subgroup make `p`th powers a
homomorphism, after which the range argument above applies. -/
theorem omegaOne_isElementaryAbelianOfRank_two_of_cyclic_index_prime_of_smallNilpotencyClass
    [Finite G] {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (hodd : Odd (Nat.card G)) (hnotcyclic : ¬ IsCyclic G) (x : G)
    (hindex : (Subgroup.zpowers x).index = p)
    (hclass : Group.nilpotencyClass G ≤ if 3 < p then 3 else 2)
    (hcommPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1) :
    IsElementaryAbelianOfRank p 2 (omegaOne p G) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Nontrivial G := Nontrivial.of_not_isCyclic hnotcyclic
  letI : Group.IsNilpotent G := hG.isNilpotent
  have hpodd : Odd p := hodd.of_dvd_nat
    (hG.card_eq_or_dvd.resolve_left (ne_of_gt (Finite.one_lt_card (α := G))))
  let f : G →* G :=
    primePowerMonoidHomOfSmallNilpotencyClass
      p hp hpodd hclass hcommPow
  apply
    omegaOne_isElementaryAbelianOfRank_two_of_cyclic_index_prime_of_powerMonoidHom
      hp hG hnotcyclic x hindex f
  intro y
  simp [f]

/-- The cyclic-maximal theorem assuming the precise conjugation statement
supplied by the odd prime-power automorphism calculation: conjugation fixes
all `p`th powers in the cyclic maximal subgroup. -/
theorem omegaOne_isElementaryAbelianOfRank_two_of_cyclic_index_prime_of_conj_pow_fixed
    [Finite G] {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (hodd : Odd (Nat.card G)) (hnotcyclic : ¬ IsCyclic G) (x : G)
    (hindex : (Subgroup.zpowers x).index = p)
    (hfix : ∀ (g h : G), h ∈ Subgroup.zpowers x →
      g * h ^ p * g⁻¹ = h ^ p) :
    IsElementaryAbelianOfRank p 2 (omegaOne p G) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Nontrivial G := Nontrivial.of_not_isCyclic hnotcyclic
  letI : Group.IsNilpotent G := hG.isNilpotent
  let H : Subgroup G := Subgroup.zpowers x
  letI : H.Normal := normal_of_index_eq_prime hp hG hindex
  let A : Subgroup G := (omegaOne p H).map H.subtype
  letI : A.Normal := by
    dsimp [A]
    infer_instance
  have hHcard_ne_one : Nat.card H ≠ 1 := by
    intro hHcard
    have hGcard : Nat.card G = p := by
      rw [← H.card_mul_index, hHcard, hindex, one_mul]
    exact hnotcyclic (isCyclic_of_prime_card hGcard)
  have hAcard : Nat.card A = p := by
    dsimp [A]
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact card_omegaOne_of_isCyclic_isPGroup hp (hG.to_subgroup H) hHcard_ne_one
  have hAcenter : A ≤ Subgroup.center G :=
    normal_le_center_of_card_eq_prime hp hG A hAcard
  have hfix' : ∀ (g : G) (h : H),
      MulAut.conjNormal g (h ^ p) = h ^ p := by
    intro g h
    apply Subtype.ext
    simpa using hfix g h h.property
  have hmixed : ⁅H, ⊤⁆ ≤ A := by
    simpa [A] using
      commutator_le_map_omegaOne_of_conjNormal_pow_eq p H hfix'
  have hHcoatom : IsCoatom H :=
    isCoatom_of_index_eq_prime hp hindex
  have hcommA : _root_.commutator G ≤ A :=
    commutator_le_of_isCoatom_isCyclic_of_commutator_le H A hHcoatom hmixed
  have hcentral : _root_.commutator G ≤ Subgroup.center G :=
    hcommA.trans hAcenter
  have hclass2 : Group.nilpotencyClass G ≤ 2 :=
    nilpotencyClass_le_two_of_commutator_le_center hcentral
  have hclass : Group.nilpotencyClass G ≤ if 3 < p then 3 else 2 := by
    exact hclass2.trans (by split_ifs <;> omega)
  have hcommPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1 := by
    intro r hr
    have hrA := hcommA hr
    change r ∈ (omegaOne p H).map H.subtype at hrA
    obtain ⟨a, ha, rfl⟩ := hrA
    have haker : a ∈ (powMonoidHom p : H →* H).ker := by
      rw [← omegaOne_eq_powMonoidHom_ker]
      exact ha
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp haker)
  exact
    omegaOne_isElementaryAbelianOfRank_two_of_cyclic_index_prime_of_smallNilpotencyClass
      hp hG hodd hnotcyclic x hindex hclass hcommPow

/-- `BGsection4.v: Ohm1_extremal_odd` (Bender--Glauberman Lemma 4.5(b)).
A noncyclic finite odd `p`-group with a cyclic subgroup of index `p` has
elementary-abelian first omega subgroup of rank two. -/
theorem omegaOne_isElementaryAbelian_rank_two_of_cyclic_subgroup_index_prime
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hnotcyclic : ¬ IsCyclic G) (x : G)
    (hindex : (Subgroup.zpowers x).index = p) :
    IsElementaryAbelianOfRank p 2 (omegaOne p G) := by
  let hp : p.Prime := Fact.out
  by_cases hcommutative : IsMulCommutative G
  · letI : IsMulCommutative G := hcommutative
    exact
      omegaOne_isElementaryAbelianOfRank_two_of_cyclic_index_prime_of_commutative
        hp hG hnotcyclic x hindex
  · letI : Nontrivial G := Nontrivial.of_not_isCyclic hnotcyclic
    have hpodd : Odd p := hodd.of_dvd_nat
      (hG.card_eq_or_dvd.resolve_left
        (ne_of_gt (Finite.one_lt_card (α := G))))
    obtain ⟨n, hHcard⟩ :=
      exists_card_zpowers_eq_prime_pow_add_two_of_not_commutative
        hp hG x hindex hcommutative
    let H : Subgroup G := Subgroup.zpowers x
    letI : H.Normal := normal_of_index_eq_prime hp hG hindex
    have hfix : ∀ (g h : G), h ∈ Subgroup.zpowers x →
        g * h ^ p * g⁻¹ = h ^ p := by
      intro g h hh
      let hH : H := ⟨h, hh⟩
      have hconjPow : (MulAut.conjNormal g : MulAut H) ^ p = 1 :=
        conjNormal_pow_prime_eq_one_of_cyclic_index_prime H hindex g
      have hfixed : MulAut.conjNormal g (hH ^ p) = hH ^ p :=
        mulAut_fix_pow_prime_of_pow_eq_one
          hp hpodd hHcard (MulAut.conjNormal g) hconjPow hH
      simpa [hH] using congrArg Subtype.val hfixed
    exact
      omegaOne_isElementaryAbelianOfRank_two_of_cyclic_index_prime_of_conj_pow_fixed
        hp hG hodd hnotcyclic x hindex hfix

/-- Reduction of `Ohm1_extremal_odd` to its noncommutative branch.  The
additional hypothesis is exactly the branch supplied in MathComp by the
classification of odd `p`-groups with a cyclic maximal subgroup. -/
theorem omegaOne_isElementaryAbelianOfRank_two_of_cyclic_index_prime_of_noncommutative_branch
    [Finite G] {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (hodd : Odd (Nat.card G)) (hnotcyclic : ¬ IsCyclic G) (x : G)
    (hindex : (Subgroup.zpowers x).index = p)
    (hnoncommutative : ¬ IsMulCommutative G →
      IsElementaryAbelianOfRank p 2 (omegaOne p G)) :
    IsElementaryAbelianOfRank p 2 (omegaOne p G) := by
  by_cases hcommutative : IsMulCommutative G
  · letI : IsMulCommutative G := hcommutative
    exact
      omegaOne_isElementaryAbelianOfRank_two_of_cyclic_index_prime_of_commutative
        hp hG hnotcyclic x hindex
  · exact hnoncommutative hcommutative

end Submission.OddOrder.MathlibSupport
