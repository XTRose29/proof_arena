import Submission.OddOrder.BG.Section03.FrobeniusNormalizer
import Submission.OddOrder.MathlibSupport.NormalizedTI
import Submission.OddOrder.MathlibSupport.PGroupNormalizer
import Submission.OddOrder.MathlibSupport.SubgroupCardinality
import Submission.OddOrder.PF.Section05.InducedIrreducibles

/-!
# Normalized-TI Sylow and Frobenius-centralizer adapters

This file supplies the two subgroup-type changes used in the first case of
Peterfalvi's Section 6 coherence argument.  The first is the Lean analogue
of the `Sylow_subnorm` step: a local Sylow subgroup whose ambient normalizer
is trapped by normalized TI is already Sylow in the ambient group.  The
second identifies the centralizer of a nonidentity central kernel element in
a Frobenius group.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.MathlibSupport
open scoped Classical

universe u

/-- Normalized TI passes from an ambient subgroup to its subgroup type.

The inclusion hypotheses ensure that the two subgroup preimages are copies
of the original subgroups rather than proper intersections. -/
theorem normalizedTI_subgroupOf
    {Gamma : Type u} [Group Gamma]
    {D L H : Subgroup Gamma}
    (hHD : H ≤ D) (_hLD : L ≤ D)
    (hTI : IsNormalizedTI (subgroupNonidentity H) D L) :
    IsNormalizedTI
      (subgroupNonidentity (H.subgroupOf D))
      (⊤ : Subgroup D) (L.subgroupOf D) := by
  rw [isNormalizedTI_iff_mem_conj]
  rcases (isNormalizedTI_iff_mem_conj.mp hTI) with
    ⟨⟨a, haH, haOne⟩, _, hmem⟩
  refine ⟨?_, le_top, ?_⟩
  · refine ⟨⟨a, hHD haH⟩, haH, ?_⟩
    intro haDOne
    exact haOne (congrArg Subtype.val haDOne)
  · intro a ha g _
    have haGamma : (a : Gamma) ∈ subgroupNonidentity H := by
      refine ⟨ha.1, ?_⟩
      intro haOne'
      exact ha.2 (Subtype.ext haOne')
    have hbase := hmem haGamma g.property
    constructor
    · intro hconj
      apply hbase.mp
      refine ⟨hconj.1, ?_⟩
      intro hOne
      exact hconj.2 (Subtype.ext hOne)
    · intro hgL
      have hconj := hbase.mpr hgL
      refine ⟨hconj.1, ?_⟩
      intro hOne
      exact hconj.2 (congrArg Subtype.val hOne)

/-- In normalized TI, the normalizer of the underlying subgroup lies in the
specified relative normalizer. -/
private theorem normalizer_le_of_normalizedTI
    {G : Type u} [Group G]
    {H L : Subgroup G}
    (hTI : IsNormalizedTI
      (subgroupNonidentity H) (⊤ : Subgroup G) L) :
    Subgroup.normalizer (H : Set G) ≤ L := by
  intro g hg
  rcases (isNormalizedTI_iff_mem_conj.mp hTI) with
    ⟨⟨a, haH, haOne⟩, _, hmem⟩
  apply (hmem ⟨haH, haOne⟩ (Subgroup.mem_top g)).mp
  refine ⟨((Subgroup.mem_set_normalizer_iff''.mp hg) a).mp haH, ?_⟩
  intro hconjOne
  apply haOne
  have hback := congrArg (fun x : G => g * x * g⁻¹) hconjOne
  simpa [mul_assoc] using hback

/-- A local Sylow subgroup is ambient Sylow when normalized TI traps its
ambient normalizer. -/
private theorem exists_sylow_eq_of_normalizedTI_not_dvd_index
    {G : Type u} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    {H L : Subgroup G}
    (hHL : H ≤ L)
    (hHp : IsPGroup p H)
    (hindex : ¬ p ∣ (H.subgroupOf L).index)
    (hTI : IsNormalizedTI
      (subgroupNonidentity H) (⊤ : Subgroup G) L) :
    ∃ P : Sylow p G, (P : Subgroup G) = H := by
  have hHLp : IsPGroup p (H.subgroupOf L) :=
    hHp.of_equiv (Subgroup.subgroupOfEquivOfLe hHL).symm
  let PL : Sylow p L := hHLp.toSylow hindex
  have hnormalizer : Subgroup.normalizer (H : Set G) ≤ L :=
    normalizer_le_of_normalizedTI hTI
  rcases hHp.exists_le_sylow with ⟨P, hHP⟩
  have hPeq : (P : Subgroup G) = H := by
    by_contra hne
    have hHltP : H < (P : Subgroup G) :=
      lt_of_le_of_ne hHP (Ne.symm hne)
    let R : Subgroup G :=
      (P : Subgroup G) ⊓ Subgroup.normalizer (H : Set G)
    have hHltR : H < R := by
      exact lt_inf_normalizer_of_isPGroup P.isPGroup' hHltP
    have hRL : R ≤ L := inf_le_right.trans hnormalizer
    let RL : Subgroup L := R.subgroupOf L
    have hRLp : IsPGroup p RL := by
      exact (P.isPGroup'.to_le inf_le_left).of_equiv
        (Subgroup.subgroupOfEquivOfLe hRL).symm
    have hPLRL : (PL : Subgroup L) ≤ RL := by
      intro x hx
      change (x : G) ∈ R
      apply hHltR.le
      have hxHL : x ∈ H.subgroupOf L := by
        simpa only [PL, IsPGroup.toSylow_coe] using hx
      exact Subgroup.mem_subgroupOf.mp hxHL
    have hRLeq : RL = (PL : Subgroup L) :=
      PL.is_maximal' hRLp hPLRL
    have hReq : R = H := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hRL]
      change RL.map L.subtype = H
      rw [hRLeq]
      simpa only [PL, IsPGroup.toSylow_coe] using
        Subgroup.map_subgroupOf_eq_of_le hHL
    exact hHltR.ne hReq.symm
  exact ⟨P, hPeq⟩

/-- The `Sylow_subnorm` adapter in the subgroup configuration used by
Sibley's theorem.

Here the `p`-group and complement hypotheses live in the source subgroup
type `L`, while the resulting Sylow subgroup lives in the ambient subgroup
type `G`. -/
theorem exists_sylow_subgroupOf_eq_of_normalizedTI_isComplement
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {p : ℕ} [Fact p.Prime]
    {G L H : Subgroup Gamma}
    (hLG : L ≤ G) (hHL : H ≤ L)
    (W : Subgroup L)
    (hHp : IsPGroup p (H.subgroupOf L))
    (hTI : IsNormalizedTI (subgroupNonidentity H) G L)
    (hcomp : (H.subgroupOf L).IsComplement' W)
    (hpW : ¬ p ∣ Nat.card W) :
    ∃ P : Sylow p G, (P : Subgroup G) = H.subgroupOf G := by
  have hHG : H ≤ G := hHL.trans hLG
  let HG : Subgroup G := H.subgroupOf G
  let LG : Subgroup G := L.subgroupOf G
  have hHGLG : HG ≤ LG := by
    intro x hx
    exact hHL hx
  let HLG : Subgroup LG := HG.subgroupOf LG
  have hcardHLG : Nat.card HLG = Nat.card (H.subgroupOf L) := by
    calc
      Nat.card HLG = Nat.card HG := natCard_subgroupOf_eq hHGLG
      _ = Nat.card H := natCard_subgroupOf_eq hHG
      _ = Nat.card (H.subgroupOf L) :=
        (natCard_subgroupOf_eq hHL).symm
  have hindexEq : HLG.index = Nat.card W := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := HLG))
    calc
      Nat.card HLG * HLG.index = Nat.card LG := HLG.card_mul_index
      _ = Nat.card L := natCard_subgroupOf_eq hLG
      _ = Nat.card (H.subgroupOf L) * Nat.card W := hcomp.card_mul.symm
      _ = Nat.card HLG * Nat.card W := by rw [hcardHLG]
  have hHpH : IsPGroup p H :=
    hHp.of_equiv (Subgroup.subgroupOfEquivOfLe hHL)
  have hHpG : IsPGroup p HG :=
    hHpH.of_equiv (Subgroup.subgroupOfEquivOfLe hHG).symm
  have hindex : ¬ p ∣ HLG.index := by
    rw [hindexEq]
    exact hpW
  have hTIG : IsNormalizedTI
      (subgroupNonidentity HG) (⊤ : Subgroup G) LG := by
    simpa only [HG, LG] using normalizedTI_subgroupOf hHG hLG hTI
  simpa only [HG, LG, HLG] using
    exists_sylow_eq_of_normalizedTI_not_dvd_index
      hHGLG hHpG hindex hTIG

/-- In a Frobenius decomposition, the centralizer of a nonidentity element
of the kernel's center is exactly the kernel. -/
theorem centralizerWithin_top_zpowers_eq_frobeniusKernel
    {G : Type u} [Group G]
    {H R : Subgroup G}
    (hFrob : IsFrobeniusDecomposition H R)
    {z : G} (hzCenter : z ∈ centerWithin H) (hzOne : z ≠ 1) :
    centralizerWithin (⊤ : Subgroup G) (Subgroup.zpowers z) = H := by
  apply le_antisymm
  · intro x hx
    rcases hFrob.existsUnique_kernel_mul_complement x with
      ⟨⟨k, r⟩, hkr, _⟩
    have hkz : (k : G) * z = z * (k : G) :=
      hzCenter.2 (k : G) k.property
    have hrz : (r : G) * z = z * (r : G) := by
      apply mul_left_cancel (a := (k : G))
      calc
        (k : G) * ((r : G) * z) =
            ((k : G) * (r : G)) * z := by rw [mul_assoc]
        _ = x * z := by rw [hkr]
        _ = z * x := (hx.2 z (Subgroup.mem_zpowers z)).symm
        _ = z * ((k : G) * (r : G)) := by rw [hkr]
        _ = (z * (k : G)) * (r : G) := by rw [mul_assoc]
        _ = ((k : G) * z) * (r : G) := by rw [hkz]
        _ = (k : G) * (z * (r : G)) := by rw [mul_assoc]
    let zH : H := ⟨z, hzCenter.1⟩
    have hfix :
        (r : G) * (zH : G) * (r : G)⁻¹ = (zH : G) := by
      calc
        (r : G) * (zH : G) * (r : G)⁻¹ =
            (zH : G) * (r : G) * (r : G)⁻¹ := by rw [hrz]
        _ = zH := by simp
    have hrOne : r = 1 := by
      by_contra hr
      have hzHOne := hFrob.fixedPointFree r hr zH hfix
      exact hzOne (congrArg Subtype.val hzHOne)
    rw [← hkr, hrOne]
    simpa only [Subgroup.coe_one, mul_one] using k.property
  · intro x hxH
    refine ⟨Subgroup.mem_top x, ?_⟩
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxz : Commute x z := hzCenter.2 x hxH
    exact (hxz.zpow_right n).symm.eq

/-- Frobenius-kernel centralizers in the subgroup configuration used by
Sibley's theorem.

The Frobenius decomposition is stated in the source subgroup type `L`, but
the resulting equality is the one needed in the ambient subgroup type `G`
by `constant_irr_mod_TI_Sylow`. -/
theorem centralizerWithin_subgroupOf_zpowers_eq_frobeniusKernel
    {Gamma : Type u} [Group Gamma]
    {G L H : Subgroup Gamma}
    (hLG : L ≤ G) (hHL : H ≤ L)
    {R : Subgroup L}
    (hFrob : IsFrobeniusDecomposition (H.subgroupOf L) R)
    {z : G}
    (hzCenter : z ∈ centerWithin (H.subgroupOf G))
    (hzOne : z ≠ 1) :
    centralizerWithin (L.subgroupOf G) (Subgroup.zpowers z) =
      H.subgroupOf G := by
  let zL : L := ⟨(z : Gamma), hHL hzCenter.1⟩
  have hzLCenter : zL ∈ centerWithin (H.subgroupOf L) := by
    refine ⟨hzCenter.1, ?_⟩
    intro x hx
    let xG : G := ⟨(x : Gamma), hLG x.property⟩
    have hcommG : xG * z = z * xG := hzCenter.2 xG hx
    have hcommGamma :
        (x : Gamma) * (z : Gamma) = (z : Gamma) * (x : Gamma) :=
      congrArg (fun y : G => (y : Gamma)) hcommG
    apply Subtype.ext
    exact hcommGamma
  have hzLOne : zL ≠ 1 := by
    intro hzL
    apply hzOne
    have hzGamma : (z : Gamma) = 1 :=
      congrArg (fun y : L => (y : Gamma)) hzL
    apply Subtype.ext
    exact hzGamma
  have hcentralL :
      centralizerWithin (⊤ : Subgroup L) (Subgroup.zpowers zL) =
        H.subgroupOf L :=
    centralizerWithin_top_zpowers_eq_frobeniusKernel
      hFrob hzLCenter hzLOne
  ext x
  constructor
  · intro hx
    let xL : L := ⟨(x : Gamma), hx.1⟩
    have hxL : xL ∈
        centralizerWithin (⊤ : Subgroup L) (Subgroup.zpowers zL) := by
      refine ⟨Subgroup.mem_top xL, ?_⟩
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcommG : (z ^ n) * x = x * (z ^ n) :=
        hx.2 (z ^ n)
          (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) n)
      have hcommGamma :
          (z : Gamma) ^ n * (x : Gamma) =
            (x : Gamma) * (z : Gamma) ^ n :=
        congrArg (fun y : G => (y : Gamma)) hcommG
      apply Subtype.ext
      exact hcommGamma
    rw [hcentralL] at hxL
    exact hxL
  · intro hxH
    let xL : L := ⟨(x : Gamma), hHL hxH⟩
    have hxL : xL ∈
        centralizerWithin (⊤ : Subgroup L) (Subgroup.zpowers zL) := by
      rw [hcentralL]
      exact hxH
    refine ⟨hHL hxH, ?_⟩
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcommL : (zL ^ n) * xL = xL * (zL ^ n) :=
      hxL.2 (zL ^ n)
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers zL) n)
    have hcommGamma :
        (z : Gamma) ^ n * (x : Gamma) =
          (x : Gamma) * (z : Gamma) ^ n :=
      congrArg (fun y : L => (y : Gamma)) hcommL
    apply Subtype.ext
    exact hcommGamma

end

end Submission.OddOrder.PF
