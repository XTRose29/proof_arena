import Submission.OddOrder.BG.Section03.SemidirectProperKernel
import Submission.OddOrder.MathlibSupport.PrimeOrderCentralizer
import Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow

/-!
A coprime prime-order action splits off its fixed subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped Pointwise commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}

/-- For a coprime factorization with prime-order complement, every kernel
element is a product of a mixed-commutator element and an element centralizing
the complement. This is the specialized form of Bender-Glauberman Proposition
1.6(a) needed in Theorem 3.4. -/
theorem le_commutator_sup_centralizerWithin_of_prime_complement
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hRprime : (Nat.card R).Prime) :
    K ≤ ⁅R, K⁆ ⊔ centralizerWithin K R := by
  classical
  letI : K.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hKR.sup_eq_top]
    exact sup_le Subgroup.le_normalizer hnormK
  let H : Subgroup G := ⁅R, K⁆
  have hHK : H ≤ K := by
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hnormK
  have hnormH : R ≤ Subgroup.normalizer (H : Set G) := by
    exact Subgroup.normalizer_commutator_ge_left R K
  let L : Subgroup G := R ⊔ H
  let HL : Subgroup L := H.subgroupOf L
  let RL : Subgroup L := R.subgroupOf L
  have hcomp : HL.IsComplement' RL := by
    simpa [L, HL, RL] using
      Submission.OddOrder.BG.Section03.properKernel_subgroupOf_isComplement
        hKR hHK hnormH
  have hcardHL : Nat.card HL = Nat.card H :=
    natCard_subgroupOf_eq (show H ≤ L from le_sup_right)
  have hcardRL : Nat.card RL = Nat.card R :=
    natCard_subgroupOf_eq (show R ≤ L from le_sup_left)
  let p := Nat.card R
  letI : Fact p.Prime := ⟨hRprime⟩
  have hpRL : IsPGroup p RL := by
    apply IsPGroup.of_card
    rw [hcardRL, pow_one]
  have hindexRL : RL.index = Nat.card H := by
    rw [hcomp.index_eq_card, hcardHL]
  have hcopH : Nat.Coprime (Nat.card H) p :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hHK)
  have hpNotIndex : ¬p ∣ RL.index := by
    rw [hindexRL]
    exact hRprime.coprime_iff_not_dvd.mp hcopH.symm
  let PR : Sylow p L := hpRL.toSylow hpNotIndex
  have hnormL : K ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk x hx
    have hmapH : H.map (MulAut.conj k) ≤ H := by
      have hkH : k ∈ Subgroup.normalizer (H : Set G) :=
        Subgroup.normalizer_commutator_ge_right R K hk
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hkH
      exact hkH.le
    have hmapR : R.map (MulAut.conj k) ≤ L := by
      rintro y ⟨r, hr, rfl⟩
      change k * r * k⁻¹ ∈ L
      rw [show k * r * k⁻¹ = ⁅k, r⁆ * r by
        simpa using (conj_eq_commutatorElement_mul (g₁ := k) (g₂ := r))]
      apply L.mul_mem
      · apply (show H ≤ L from le_sup_right)
        change ⁅k, r⁆ ∈ ⁅R, K⁆
        rw [Subgroup.commutator_comm R K]
        exact Subgroup.commutator_mem_commutator hk hr
      · exact (show R ≤ L from le_sup_left) hr
    have hmapL : L.map (MulAut.conj k) ≤ L := by
      dsimp [L]
      rw [Subgroup.map_sup]
      exact sup_le hmapR (hmapH.trans le_sup_right)
    have hxmap := Subgroup.mem_map_of_mem (MulAut.conj k : G →* G) hx
    exact hmapL (by simpa [MulAut.conj_apply] using hxmap)
  intro k hk
  let kn : Subgroup.normalizer (L : Set G) := ⟨k, hnormL hk⟩
  let e : MulAut L := L.normalizerMonoidHom kn
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L (e • PR) PR
  obtain ⟨hr, hhr, _hunique⟩ := hcomp.existsUnique l
  let h : G := hr.1
  let r : G := hr.2
  have hhH : h ∈ H := hr.1.property
  have hrR : r ∈ R := hr.2.property
  have hlhr : h * r = (l : G) := congrArg Subtype.val hhr
  let c : G := h * (r * k * r⁻¹)
  have hcK : c ∈ K := by
    apply K.mul_mem (hHK hhH)
    exact (Subgroup.le_normalizer_iff.mp hnormK r hrR k hk)
  have hlsub : MulAut.conj l • (e • RL) = RL := by
    change ((l • (e • PR) : Sylow p L) : Subgroup L) =
      (PR : Subgroup L)
    rw [hl]
  have hlforward : ∀ a : G, a ∈ R →
      (l : G) * k * a * ((l : G) * k)⁻¹ ∈ R := by
    intro a ha
    let aRL : RL := ⟨⟨a, (show R ≤ L from le_sup_left) ha⟩, ha⟩
    have hea : e (aRL : L) ∈ e • RL :=
      Subgroup.smul_mem_pointwise_smul (aRL : L) e RL aRL.property
    have hlea : MulAut.conj l (e (aRL : L)) ∈
        MulAut.conj l • (e • RL) :=
      Subgroup.smul_mem_pointwise_smul (e (aRL : L)) (MulAut.conj l)
        (e • RL) hea
    rw [hlsub] at hlea
    have hleaR : ((MulAut.conj l) (e (aRL : L)) : G) ∈ R := hlea
    simpa [e, kn, aRL, Subgroup.normalizerMonoidHom,
      HSMul.hSMul, MulAut.conj_apply, mul_inv_rev, mul_assoc] using hleaR
  have hlambient :
      (MulAut.conj ((l : G) * k) • R : Subgroup G) = R := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      obtain ⟨a, ha, rfl⟩ :=
        (Subgroup.mem_smul_pointwise_iff_exists y
          (MulAut.conj ((l : G) * k)) R).mp hy
      exact hlforward a ha
    · have hcard :
          Nat.card (MulAut.conj ((l : G) * k) • R : Subgroup G) = Nat.card R :=
        Nat.card_congr
          (Subgroup.equivSMul (MulAut.conj ((l : G) * k)) R).symm.toEquiv
      exact hcard.ge
  have hcr : c * r = (l : G) * k := by
    dsimp [c]
    rw [← hlhr]
    group
  have hlkNorm : (l : G) * k ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (MulAut.conj ((l : G) * k) • R : Subgroup G) = R
    exact hlambient
  have hrNorm : r ∈ Subgroup.normalizer (R : Set G) := R.le_normalizer hrR
  have hcNorm : c ∈ Subgroup.normalizer (R : Set G) := by
    have hcEq : c = ((l : G) * k) * r⁻¹ := by
      rw [← hcr]
      group
    rw [hcEq]
    exact (Subgroup.normalizer (R : Set G)).mul_mem hlkNorm
      ((Subgroup.normalizer (R : Set G)).inv_mem hrNorm)
  have hcCentral : c ∈ centralizerWithin K R := by
    refine ⟨hcK, ?_⟩
    intro a ha
    have hcommK : ⁅c, a⁆ ∈ K := by
      apply hHK
      have hmem : ⁅c, a⁆ ∈ ⁅K, R⁆ :=
        Subgroup.commutator_mem_commutator hcK ha
      simpa [H, Subgroup.commutator_comm R K] using hmem
    have hcommR : ⁅c, a⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp hcNorm a).mp ha)
        (R.inv_mem ha)
    have hcommOne : ⁅c, a⁆ = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hKR.disjoint]
      exact ⟨hcommK, hcommR⟩
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcommOne).symm
  have hkcH : k * c⁻¹ ∈ H := by
    have hcomm : ⁅k, r⁆ ∈ H := by
      have hmem : ⁅k, r⁆ ∈ ⁅K, R⁆ :=
        Subgroup.commutator_mem_commutator hk hrR
      simpa [H, Subgroup.commutator_comm R K] using hmem
    have heq : k * c⁻¹ = ⁅k, r⁆ * h⁻¹ := by
      dsimp [c]
      rw [mul_inv_rev]
      group
    rw [heq]
    exact H.mul_mem hcomm (H.inv_mem hhH)
  have hdecomp : (k * c⁻¹) * c = k := by group
  rw [← hdecomp]
  exact (H ⊔ centralizerWithin K R).mul_mem
    ((show H ≤ H ⊔ centralizerWithin K R from le_sup_left) hkcH)
    ((show centralizerWithin K R ≤ H ⊔ centralizerWithin K R from le_sup_right)
      hcCentral)

end Submission.OddOrder.MathlibSupport
