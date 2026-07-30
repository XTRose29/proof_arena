import Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Centralizers in coprime solvable quotients

A quotient by a normal subgroup carries the centralizer of a coprime
subgroup onto the corresponding centralizer in the quotient.  The reverse
inclusion is the fixed-coset lifting step: solvable Schur--Zassenhaus
conjugacy adjusts a representative by an element of the quotient kernel.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- In a finite solvable group, quotienting by a normal subgroup coprime to
`R` carries `C_K(R)` onto the centralizer of the image of `R`.

The easy inclusion maps commuting representatives.  For the reverse
inclusion, `R` and the conjugate of `R` by a lift are complements to the
kernel inside their join.  Solvable complement conjugacy supplies a kernel
element that corrects the lift to centralize `R`. -/
theorem map_centralizer_quotient_eq_of_coprime
    {K : Type u} [Group K] [Finite K] [IsSolvable K]
    {N R : Subgroup K} [N.Normal]
    (hcop : Nat.Coprime (Nat.card N) (Nat.card R)) :
    (Subgroup.centralizer (R : Set K)).map (QuotientGroup.mk' N) =
      Subgroup.centralizer
        (R.map (QuotientGroup.mk' N) : Set (K ⧸ N)) := by
  classical
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨r, hr, rfl⟩
    exact congrArg q (Subgroup.mem_centralizer_iff.mp hc r hr)
  · intro z hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
    let Rg : Subgroup K := R.map (MulAut.conj g).toMonoidHom
    have hRgL : Rg ≤ N ⊔ R := by
      rintro _ ⟨r, hr, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp hz (q r)
        (Subgroup.mem_map_of_mem q hr)
      change q r * q g = q g * q r at hcomm
      have hqeq : q (g * r * g⁻¹) = q r := by
        change q g * q r * (q g)⁻¹ = q r
        rw [← hcomm]
        group
      have hker : (g * r * g⁻¹)⁻¹ * r ∈ N :=
        QuotientGroup.eq.mp hqeq
      change g * r * g⁻¹ ∈ N ⊔ R
      rw [show g * r * g⁻¹ =
          r * ((g * r * g⁻¹)⁻¹ * r)⁻¹ by group]
      exact (N ⊔ R).mul_mem
        ((show R ≤ N ⊔ R from le_sup_right) hr)
        ((show N ≤ N ⊔ R from le_sup_left) (N.inv_mem hker))
    let L : Subgroup K := N ⊔ R
    let NL : Subgroup L := N.subgroupOf L
    let RL : Subgroup L := R.subgroupOf L
    let RgL : Subgroup L := Rg.subgroupOf L
    letI : NL.Normal := by
      dsimp [NL]
      exact Subgroup.Normal.subgroupOf (inferInstance : N.Normal) L
    have hcardNL : Nat.card NL = Nat.card N :=
      natCard_subgroupOf_eq le_sup_left
    have hcardRL : Nat.card RL = Nat.card R :=
      natCard_subgroupOf_eq le_sup_right
    have hdisNR : Disjoint N R :=
      Subgroup.disjoint_of_coprime_natCard hcop
    have hdisNLRL : Disjoint NL RL := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hdisNR]
      exact hx
    have hsupNLRL : NL ⊔ RL = ⊤ := by
      change N.subgroupOf L ⊔ R.subgroupOf L = ⊤
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_self L
    have hcompRL : NL.IsComplement' RL := by
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisNLRL
      rw [← Subgroup.normal_mul NL RL, hsupNLRL]
      rfl
    have hcardRg : Nat.card Rg = Nat.card R := by
      dsimp [Rg]
      exact Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hcardRgL : Nat.card RgL = Nat.card RL := by
      rw [natCard_subgroupOf_eq hRgL, hcardRg,
        natCard_subgroupOf_eq le_sup_right]
    have hcompRgL : NL.IsComplement' RgL := by
      apply Subgroup.isComplement'_of_coprime
      · rw [hcardRgL]
        exact hcompRL.card_mul
      · rw [hcardNL, hcardRgL, hcardRL]
        exact hcop
    have hcopNLindex : Nat.Coprime (Nat.card NL) NL.index := by
      rw [hcompRL.symm.index_eq_card, hcardNL, hcardRL]
      exact hcop
    obtain ⟨n, hn⟩ :=
      Subgroup.solvable_complement_conjugacy
        hcopNLindex hcompRL hcompRgL
    let nK : K := ((n : NL) : L)
    have hnN : nK ∈ N := n.property
    let c : K := nK⁻¹ * g
    have hconjR (r : K) (hr : r ∈ R) : c * r * c⁻¹ ∈ R := by
      have hxRg : g * r * g⁻¹ ∈ Rg := by
        exact ⟨r, hr, rfl⟩
      let xL : L := ⟨g * r * g⁻¹, hRgL hxRg⟩
      have hxRgL : xL ∈ RgL := hxRg
      rw [hn] at hxRgL
      rcases hxRgL with ⟨s, hs, hns⟩
      have hnsK : nK * (s : K) * nK⁻¹ = g * r * g⁻¹ :=
        congrArg (fun y : L ↦ (y : K)) hns
      rw [show c * r * c⁻¹ = (s : K) by
        dsimp [c]
        calc
          nK⁻¹ * g * r * (nK⁻¹ * g)⁻¹ =
              nK⁻¹ * (g * r * g⁻¹) * nK := by group
          _ = nK⁻¹ * (nK * (s : K) * nK⁻¹) * nK := by rw [← hnsK]
          _ = (s : K) := by group]
      exact hs
    have hqn : q nK = 1 :=
      QuotientGroup.eq_one_iff nK |>.mpr hnN
    have hqc : q c = q g := by
      simp [c, hqn]
    refine ⟨c, ?_, hqc⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro r hr
    have hur : c * r * c⁻¹ ∈ R := hconjR r hr
    have hcomm := Subgroup.mem_centralizer_iff.mp hz (q r)
      (Subgroup.mem_map_of_mem q hr)
    change q r * q g = q g * q r at hcomm
    have hqeq : q (c * r * c⁻¹) = q r := by
      change q c * q r * (q c)⁻¹ = q r
      rw [hqc, ← hcomm]
      group
    have hdiffN : (c * r * c⁻¹)⁻¹ * r ∈ N :=
      QuotientGroup.eq.mp hqeq
    have hdiffR : (c * r * c⁻¹)⁻¹ * r ∈ R :=
      R.mul_mem (R.inv_mem hur) hr
    have hdiffOne : (c * r * c⁻¹)⁻¹ * r = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hdisNR]
      exact ⟨hdiffN, hdiffR⟩
    have hconjEq : c * r * c⁻¹ = r :=
      inv_mul_eq_one.mp hdiffOne
    symm
    calc
      c * r = (c * r * c⁻¹) * c := by group
      _ = r * c := by rw [hconjEq]

end Submission.OddOrder.MathlibSupport
