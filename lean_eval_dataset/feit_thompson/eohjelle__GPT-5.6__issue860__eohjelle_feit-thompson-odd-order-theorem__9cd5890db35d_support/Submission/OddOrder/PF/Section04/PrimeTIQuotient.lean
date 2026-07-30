import Submission.OddOrder.MathlibSupport.ComplementQuotient
import Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy
import Submission.OddOrder.PF.Section04.PrimeTIHypothesis

/-!
# Peterfalvi Section 4: quotienting the prime-TI hypothesis

This file ports `primeTIhyp_quotient` from `PFsection4.v`.  If a normal
subgroup `M` of `L` lies in the semidirect-product kernel `K`, then all the
prime-TI data descend to `L / M`, provided the image of `W₂` is nontrivial.

The centralizer step is the solvable-actor half of coprime quotient
centralizer lifting: the acting subgroup is cyclic, while the quotient
kernel need not be solvable.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport

universe u

variable {Gamma : Type u} [Group Gamma]

/-- The quotient ambient group used when a subgroup of `L` is factored out.

The normality instance on `M.subgroupOf L` is only needed when the group
structure or the quotient map is used. -/
abbrev primeTIQuotientGroup (L M : Subgroup Gamma) :=
  L ⧸ M.subgroupOf L

/-- The image in `L / M` of a fixed ambient subgroup. -/
def primeTIQuotientImage (L M H : Subgroup Gamma)
    [(M.subgroupOf L).Normal] :
    Subgroup (primeTIQuotientGroup L M) :=
  (H.subgroupOf L).map (QuotientGroup.mk' (M.subgroupOf L))

namespace PrimeTIHypothesis

variable {L K W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

private theorem subgroupOf_ne_bot_of_ne_bot
    {H J : Subgroup Gamma} (hHJ : H ≤ J) (hH : H ≠ ⊥) :
    H.subgroupOf J ≠ ⊥ := by
  intro hbot
  apply hH
  apply le_bot_iff.mp
  intro x hx
  let xJ : J := ⟨x, hHJ hx⟩
  have hxSub : xJ ∈ H.subgroupOf J := hx
  rw [hbot] at hxSub
  exact Subgroup.mem_bot.mpr
    (congrArg Subtype.val (Subgroup.mem_bot.mp hxSub))

private theorem subgroupOf_directProduct_sup
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    W₁.subgroupOf L ⊔ W₂.subgroupOf L = W.subgroupOf L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le h.complement_le_group,
    Subgroup.map_subgroupOf_eq_of_le
      (h.fixed_le_kernel.trans h.kernel_le_group),
    Subgroup.map_subgroupOf_eq_of_le h.directProduct_le_group]
  calc
    W₁ ⊔ W₂ =
        ((W₁.subgroupOf W) ⊔ (W₂.subgroupOf W)).map W.subtype := by
          rw [Subgroup.map_sup,
            Subgroup.map_subgroupOf_eq_of_le defW.left_le,
            Subgroup.map_subgroupOf_eq_of_le defW.right_le]
    _ = (⊤ : Subgroup W).map W.subtype := by
      rw [defW.complement.sup_eq_top]
    _ = W := by
      rw [← MonoidHom.range_eq_map, W.range_subtype]

private theorem centralizerWithin_subgroupOf_zpowers
    (h : PrimeTIHypothesis L K W W₁ W₂ defW)
    (x : L) (hxW₁ : x ∈ W₁.subgroupOf L) (hx : x ≠ 1) :
    centralizerWithin (K.subgroupOf L) (Subgroup.zpowers x) =
      W₂.subgroupOf L := by
  let x₁ : W₁ := ⟨(x : Gamma), hxW₁⟩
  have hx₁ : x₁ ≠ 1 := by
    intro hx₁one
    apply hx
    apply Subtype.ext
    simpa only [x₁, Subgroup.coe_one] using
      congrArg Subtype.val hx₁one
  have hcent := h.centralizer_kernel x₁ hx₁
  ext z
  constructor
  · intro hz
    have hzGamma :
        (z : Gamma) ∈
          centralizerWithin K (Subgroup.zpowers (x : Gamma)) := by
      refine ⟨hz.1, ?_⟩
      intro y hy
      have hyMap :
          y ∈ (Subgroup.zpowers x).map L.subtype := by
        rwa [MonoidHom.map_zpowers]
      rcases hyMap with ⟨yL, hyL, rfl⟩
      exact congrArg Subtype.val (hz.2 yL hyL)
    rw [hcent] at hzGamma
    exact hzGamma
  · intro hz
    have hzGamma :
        (z : Gamma) ∈
          centralizerWithin K (Subgroup.zpowers (x : Gamma)) := by
      rw [hcent]
      exact hz
    refine ⟨hzGamma.1, ?_⟩
    intro y hy
    apply Subtype.ext
    apply hzGamma.2 (y : Gamma)
    change (y : Gamma) ∈ Subgroup.zpowers (L.subtype x)
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_of_mem L.subtype hy

/-- Peterfalvi 4.3's quotient lemma (`primeTIhyp_quotient`).

The quotient is taken in the subgroup type `L`, so normality has exactly the
same scope as the source assumption `M <| L`. -/
theorem quotient
    [Finite Gamma]
    (h : PrimeTIHypothesis L K W W₁ W₂ defW)
    (M : Subgroup Gamma)
    (hMK : M ≤ K)
    [(M.subgroupOf L).Normal]
    (hW₂q : primeTIQuotientImage L M W₂ ≠ ⊥) :
    ∃ defWq : IsInternalDirectProductIn
        (primeTIQuotientImage L M W₁)
        (primeTIQuotientImage L M W₂)
        (primeTIQuotientImage L M W),
      PrimeTIHypothesis
        (⊤ : Subgroup (primeTIQuotientGroup L M))
        (primeTIQuotientImage L M K)
        (primeTIQuotientImage L M W)
        (primeTIQuotientImage L M W₁)
        (primeTIQuotientImage L M W₂)
        defWq := by
  classical
  let ML : Subgroup L := M.subgroupOf L
  let KL : Subgroup L := K.subgroupOf L
  let WL : Subgroup L := W.subgroupOf L
  let W₁L : Subgroup L := W₁.subgroupOf L
  let W₂L : Subgroup L := W₂.subgroupOf L
  let Q := L ⧸ ML
  let q : L →* Q := QuotientGroup.mk' ML
  let Kq : Subgroup Q := KL.map q
  let Wq : Subgroup Q := WL.map q
  let W₁q : Subgroup Q := W₁L.map q
  let W₂q : Subgroup Q := W₂L.map q

  have hW₂qne : W₂q ≠ ⊥ := by
    simpa only [W₂q, W₂L, q, Q, ML, primeTIQuotientImage] using hW₂q

  have hMLKL : ML ≤ KL := by
    intro m hm
    exact hMK hm
  letI : KL.Normal := h.kernel_normal

  have hKqNormal : Kq.Normal :=
    Subgroup.Normal.map (inferInstance : KL.Normal) q
      (QuotientGroup.mk'_surjective ML)
  letI : Kq.Normal := hKqNormal

  have hcompq : Kq.IsComplement' W₁q := by
    exact h.semidirect_complement.quotient_isComplement hMLKL

  have hW₁Lne : W₁L ≠ ⊥ :=
    subgroupOf_ne_bot_of_ne_bot h.complement_le_group h.complement_ne_bot
  have hW₁qne : W₁q ≠ ⊥ := by
    exact h.semidirect_complement.quotient_right_ne_bot
      hMLKL hW₁Lne

  have hW₁Lcyclic : IsCyclic W₁L :=
    (Subgroup.subgroupOfEquivOfLe h.complement_le_group).isCyclic.mpr
      h.complement_cyclic
  letI : IsCyclic W₁L := hW₁Lcyclic
  have hW₁qcyclic : IsCyclic W₁q :=
    isCyclic_of_surjective (q.subgroupMap W₁L)
      (q.subgroupMap_surjective W₁L)

  have hW₂Lcyclic : IsCyclic W₂L :=
    (Subgroup.subgroupOfEquivOfLe
      (h.fixed_le_kernel.trans h.kernel_le_group)).isCyclic.mpr
      h.fixed_cyclic
  letI : IsCyclic W₂L := hW₂Lcyclic
  have hW₂qcyclic : IsCyclic W₂q :=
    isCyclic_of_surjective (q.subgroupMap W₂L)
      (q.subgroupMap_surjective W₂L)

  have hWLcyclic : IsCyclic WL :=
    (Subgroup.subgroupOfEquivOfLe h.directProduct_le_group).isCyclic.mpr
      h.cyclic
  letI : IsCyclic WL := hWLcyclic
  have hWqcyclic : IsCyclic Wq :=
    isCyclic_of_surjective (q.subgroupMap WL)
      (q.subgroupMap_surjective WL)
  letI : IsCyclic Wq := hWqcyclic
  letI : IsMulCommutative Wq := inferInstance

  have hW₁div : Nat.card W₁q ∣ Nat.card W₁ := by
    simpa only [W₁q, W₁L,
      natCard_subgroupOf_eq h.complement_le_group] using
      Subgroup.card_map_dvd W₁L q
  have hW₂div : Nat.card W₂q ∣ Nat.card W₂ := by
    simpa only [W₂q, W₂L,
      natCard_subgroupOf_eq
        (h.fixed_le_kernel.trans h.kernel_le_group)] using
      Subgroup.card_map_dvd W₂L q
  have hWfactorsCoprime :
      Nat.Coprime (Nat.card W₁q) (Nat.card W₂q) :=
    (h.factor_card_coprime.coprime_dvd_left hW₁div).coprime_dvd_right
      hW₂div

  have hWsupL : W₁L ⊔ W₂L = WL := by
    simpa only [W₁L, W₂L, WL] using
      subgroupOf_directProduct_sup h
  have hWsupq : W₁q ⊔ W₂q = Wq := by
    calc
      W₁q ⊔ W₂q = (W₁L ⊔ W₂L).map q := by
        rw [Subgroup.map_sup]
      _ = WL.map q := by rw [hWsupL]
      _ = Wq := rfl

  have hW₁qWq : W₁q ≤ Wq := by
    exact Subgroup.map_mono (by
      intro x hx
      exact defW.left_le hx)
  have hW₂qWq : W₂q ≤ Wq := by
    exact Subgroup.map_mono (by
      intro x hx
      exact defW.right_le hx)
  have hWdisjoint : Disjoint W₁q W₂q :=
    Subgroup.disjoint_of_coprime_natCard hWfactorsCoprime
  have hWdisjointSub :
      Disjoint (W₁q.subgroupOf Wq) (W₂q.subgroupOf Wq) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hWdisjoint]
    exact hz
  have hWsupSub :
      W₁q.subgroupOf Wq ⊔ W₂q.subgroupOf Wq = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW₁qWq hW₂qWq,
      hWsupq]
    exact Subgroup.subgroupOf_self Wq
  have hWcomp :
      (W₁q.subgroupOf Wq).IsComplement'
        (W₂q.subgroupOf Wq) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hWdisjointSub
    rw [← Subgroup.normal_mul (W₁q.subgroupOf Wq)
      (W₂q.subgroupOf Wq), hWsupSub]
    rfl
  have hWcommute : ∀ x : W₁q, ∀ y : W₂q,
      Commute (x : Q) (y : Q) := by
    intro x y
    rcases x.property with ⟨xL, hxL, hx⟩
    rcases y.property with ⟨yL, hyL, hy⟩
    rw [← hx, ← hy]
    have hcommL : Commute xL yL := by
      rw [commute_iff_eq]
      apply Subtype.ext
      exact (defW.commute
        ⟨(xL : Gamma), hxL⟩ ⟨(yL : Gamma), hyL⟩).eq
    exact hcommL.map q
  let defWq : IsInternalDirectProductIn W₁q W₂q Wq :=
    { left_le := hW₁qWq
      right_le := hW₂qWq
      complement := hWcomp
      commute := hWcommute }

  have hKqW₁qCoprime :
      Nat.Coprime (Nat.card Kq) (Nat.card W₁q) := by
    have hKdiv : Nat.card Kq ∣ Nat.card K := by
      simpa only [Kq, KL, natCard_subgroupOf_eq h.kernel_le_group] using
        Subgroup.card_map_dvd KL q
    exact (h.kernel_complement_card_coprime.coprime_dvd_left hKdiv).coprime_dvd_right
      hW₁div

  have hKqTopNormal :
      (Kq.subgroupOf (⊤ : Subgroup Q)).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : Kq.Normal) ⊤
  have hKqW₁qDisjointSub :
      Disjoint (Kq.subgroupOf (⊤ : Subgroup Q))
        (W₁q.subgroupOf (⊤ : Subgroup Q)) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hcompq.disjoint]
    exact hz
  have hKqW₁qSupSub :
      Kq.subgroupOf (⊤ : Subgroup Q) ⊔
        W₁q.subgroupOf (⊤ : Subgroup Q) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (show Kq ≤ (⊤ : Subgroup Q) from le_top)
      (show W₁q ≤ (⊤ : Subgroup Q) from le_top), hcompq.sup_eq_top]
    exact Subgroup.subgroupOf_self ⊤
  have hKqW₁qCompSub :
      (Kq.subgroupOf (⊤ : Subgroup Q)).IsComplement'
        (W₁q.subgroupOf (⊤ : Subgroup Q)) := by
    letI : (Kq.subgroupOf (⊤ : Subgroup Q)).Normal := hKqTopNormal
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      hKqW₁qDisjointSub
    rw [← Subgroup.normal_mul (Kq.subgroupOf (⊤ : Subgroup Q))
      (W₁q.subgroupOf (⊤ : Subgroup Q)), hKqW₁qSupSub]
    rfl
  have hsemidirectq :
      IsInternalSemidirectProductIn Kq W₁q (⊤ : Subgroup Q) := by
    refine ⟨le_top, le_top, hKqTopNormal, hKqW₁qCompSub⟩

  have hHallq :
      IsHall (primeSupport (Nat.card W₁q))
        (W₁q.subgroupOf (⊤ : Subgroup Q)) := by
    rw [← natCard_subgroupOf_eq
      (show W₁q ≤ (⊤ : Subgroup Q) from le_top)]
    apply isHall_primeSupport
    rw [hKqW₁qCompSub.index_eq_card]
    simpa only [natCard_subgroupOf_eq
      (show W₁q ≤ (⊤ : Subgroup Q) from le_top),
      natCard_subgroupOf_eq
        (show Kq ≤ (⊤ : Subgroup Q) from le_top)] using
      hKqW₁qCoprime.symm

  have hW₂qKq : W₂q ≤ Kq := by
    exact Subgroup.map_mono (by
      intro x hx
      exact h.fixed_le_kernel hx)

  have hoddq : Odd (Nat.card Wq) := by
    apply h.odd_card.of_dvd_nat
    simpa only [Wq, WL,
      natCard_subgroupOf_eq h.directProduct_le_group] using
      Subgroup.card_map_dvd WL q

  have hcentralq : ∀ x : W₁q, x ≠ 1 →
      centralizerWithin Kq (Subgroup.zpowers (x : Q)) = W₂q := by
    intro x hx
    rcases x.property with ⟨xL, hxW₁L, hxmap⟩
    have hxL : xL ≠ 1 := by
      intro hxLone
      apply hx
      apply Subtype.ext
      rw [← hxmap, hxLone, map_one]
      symm
      exact Subgroup.coe_one W₁q
    have hcentL :
        centralizerWithin KL (Subgroup.zpowers xL) = W₂L := by
      simpa only [KL, W₂L] using
        centralizerWithin_subgroupOf_zpowers h xL hxW₁L hxL
    have hMLdivK : Nat.card ML ∣ Nat.card K := by
      have hdiv : Nat.card ML ∣ Nat.card KL :=
        Subgroup.card_dvd_of_le hMLKL
      simpa only [KL, natCard_subgroupOf_eq h.kernel_le_group] using hdiv
    have hXdivW₁ : Nat.card (Subgroup.zpowers xL) ∣ Nat.card W₁ := by
      have hdiv : Nat.card (Subgroup.zpowers xL) ∣ Nat.card W₁L :=
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxW₁L)
      simpa only [W₁L,
        natCard_subgroupOf_eq h.complement_le_group] using hdiv
    have hcop :
        Nat.Coprime (Nat.card ML) (Nat.card (Subgroup.zpowers xL)) :=
      (h.kernel_complement_card_coprime.coprime_dvd_left hMLdivK).coprime_dvd_right
        hXdivW₁
    letI : IsSolvable (Subgroup.zpowers xL) :=
      _root_.isSolvable_of_comm (fun a b ↦ mul_comm' a b)
    have hmapCent :=
      map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        hMLKL hcop
    calc
      centralizerWithin Kq (Subgroup.zpowers (x : Q)) =
          centralizerWithin Kq
            ((Subgroup.zpowers xL).map q) := by
              rw [MonoidHom.map_zpowers, hxmap]
      _ = (centralizerWithin KL (Subgroup.zpowers xL)).map q := by
        exact hmapCent.symm
      _ = W₂L.map q := by rw [hcentL]
      _ = W₂q := rfl

  refine ⟨defWq, ?_⟩
  exact
    { semidirect := hsemidirectq
      complement_ne_bot := hW₁qne
      complement_hall := hHallq
      complement_cyclic := hW₁qcyclic
      fixed_ne_bot := hW₂qne
      fixed_le_kernel := hW₂qKq
      fixed_cyclic := hW₂qcyclic
      centralizer_kernel := hcentralq
      odd_card := hoddq }

end PrimeTIHypothesis

end

end Submission.OddOrder.PF
