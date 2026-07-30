import Submission.OddOrder.PF.Section09.PTypeCorePairing

/-!
# Peterfalvi Section 9: the Boolean orthogonal decomposition

This module carries out the integral two-stage projection in (9.11.7),
shows that its remaining coefficient is Boolean, and supplies the pairing
calculation from (9.11.8) which eliminates the nonzero Boolean case.

The reusable Fourier and virtual-character pairing facts live in
`PTypeCorePairing`; only the three Boolean-phase interfaces are exported here.
-/

namespace Submission.OddOrder.PF

noncomputable section

open PTypeCorePairingInternal
open scoped BigOperators Classical

universe u

namespace PTypeCoreBooleanInternal

local instance invertibleNatCardComplex
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private theorem pairing_neg_left
    {Q : Type u} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ) :
    characterPairing (-f) g = -characterPairing f g := by
  rw [← neg_one_smul ℂ f, characterPairing_smul_left]
  ring

private theorem pairing_neg_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ) :
    characterPairing f (-g) = -characterPairing f g := by
  rw [← neg_one_smul ℂ g, characterPairing_smul_right]
  ring

private theorem pairing_sub_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    characterPairing f (g - h) =
      characterPairing f g - characterPairing f h := by
  rw [sub_eq_add_neg, characterPairing_add_right, pairing_neg_right,
    sub_eq_add_neg]

private theorem pairing_finset_sum_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f : ClassFunction Q ℂ) {I : Type*}
    (s : Finset I) (g : I → ClassFunction Q ℂ) :
    characterPairing f (∑ i ∈ s, g i) =
      ∑ i ∈ s, characterPairing f (g i) := by
  exact map_sum (characterPairingLeft f) g s

private theorem pairing_add_self_of_orthogonal
    {Q : Type u} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ)
    (hfg : characterPairing f g = 0) :
    characterPairing (f + g) (f + g) =
      characterPairing f f + characterPairing g g := by
  have hgf : characterPairing g f = 0 := by
    rw [characterPairing_comm, hfg]
  rw [characterPairing_add_left, characterPairing_add_right,
    characterPairing_add_right, hfg, hgf]
  ring

private theorem pairing_eq_zero_of_left_span
    {Q : Type u} [Group Q] [Fintype Q]
    (T : Finset (ClassFunction Q ℂ)) (psi : ClassFunction Q ℂ)
    (hgenerator : ∀ gamma ∈ T, characterPairing gamma psi = 0)
    {Gamma : ClassFunction Q ℂ}
    (hGamma : Gamma ∈ AddSubgroup.closure
      (↑T : Set (ClassFunction Q ℂ))) :
    characterPairing Gamma psi = 0 := by
  induction hGamma using AddSubgroup.closure_induction with
  | mem gamma hgamma => exact hgenerator gamma hgamma
  | zero => simp
  | add a b ha hb iha ihb =>
      rw [characterPairing_add_left, iha, ihb, add_zero]
  | neg a ha iha => rw [pairing_neg_left, iha, neg_zero]

private theorem pairing_eq_zero_of_right_span
    {Q : Type u} [Group Q] [Fintype Q]
    (f : ClassFunction Q ℂ) (T : Finset (ClassFunction Q ℂ))
    (hgenerator : ∀ psi ∈ T, characterPairing f psi = 0)
    {Delta : ClassFunction Q ℂ}
    (hDelta : Delta ∈ AddSubgroup.closure
      (↑T : Set (ClassFunction Q ℂ))) :
    characterPairing f Delta = 0 := by
  induction hDelta using AddSubgroup.closure_induction with
  | mem psi hpsi => exact hgenerator psi hpsi
  | zero => simp
  | add a b ha hb iha ihb =>
      rw [characterPairing_add_right, iha, ihb, add_zero]
  | neg a ha iha => rw [pairing_neg_right, iha, neg_zero]

private theorem virtual_self_pairing_eq_nat
    {Q : Type u} [Group Q] [Fintype Q]
    {f : ClassFunction Q ℂ}
    (hf : ClassFunction.IsVirtual f) :
    ∃ n : ℕ, characterPairing f f = (n : ℂ) := by
  obtain ⟨v, rfl⟩ := hf
  refine ⟨Int.toNat (normSq v), ?_⟩
  rw [VirtualCharacter.characterPairing_realize]
  exact_mod_cast (Int.toNat_of_nonneg (normSq_nonneg v)).symm

private theorem pairing_member_sum_eq_one
    {Q : Type u} [Group Q] [Fintype Q]
    (T : Finset (ClassFunction Q ℂ))
    (horthonormal : ∀ alpha ∈ T, ∀ gamma ∈ T,
      characterPairing alpha gamma =
        if alpha = gamma then 1 else 0)
    {phi : ClassFunction Q ℂ} (hphi : phi ∈ T) :
    characterPairing phi (∑ psi ∈ T, psi) = 1 := by
  rw [pairing_finset_sum_right, Finset.sum_eq_single phi]
  · rw [horthonormal phi hphi phi hphi, if_pos rfl]
  · intro psi hpsi hne
    rw [horthonormal phi hphi psi hpsi, if_neg hne.symm]
  · exact fun h ↦ (h hphi).elim

private theorem boolean_norm_arithmetic
    (scale nGamma nDelta : ℕ) (z : ℤ)
    (hscalePos : 0 < scale) (hnGammaPos : 0 < nGamma)
    (hnorm :
      (1 + (scale : ℤ) ^ 2 : ℤ) =
        (nGamma : ℤ) +
          ((scale : ℤ) ^ 2 + 2 * (scale : ℤ) * (z ^ 2 - z)) +
          (nDelta : ℤ)) :
    nGamma = 1 ∧ nDelta = 0 ∧ (z = 0 ∨ z = 1) := by
  have hbalance :
      (nGamma : ℤ) + (nDelta : ℤ) +
        2 * (scale : ℤ) * (z ^ 2 - z) = 1 := by
    calc
      _ = (1 + (scale : ℤ) ^ 2) - (scale : ℤ) ^ 2 := by
        rw [hnorm]
        ring
      _ = 1 := by ring
  have hzQuadraticNonneg : 0 ≤ z ^ 2 - z := by
    by_cases hzNonneg : 0 ≤ z
    · by_cases hzZero : z = 0
      · simp [hzZero]
      · have hzOne : 1 ≤ z := by omega
        nlinarith [mul_nonneg hzNonneg (show 0 ≤ z - 1 by omega)]
    · have hzNonpos : z ≤ 0 := by omega
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hzNonpos
        (show z - 1 ≤ 0 by omega)]
  have htermNonneg : 0 ≤ 2 * (scale : ℤ) * (z ^ 2 - z) :=
    mul_nonneg (mul_nonneg (by norm_num) (Int.natCast_nonneg scale))
      hzQuadraticNonneg
  have hnGammaCastPos : (1 : ℤ) ≤ (nGamma : ℤ) := by
    exact_mod_cast hnGammaPos
  have hnDeltaCastNonneg : (0 : ℤ) ≤ (nDelta : ℤ) :=
    Int.natCast_nonneg nDelta
  have hnGammaOne : nGamma = 1 := by
    have : (nGamma : ℤ) = 1 := by omega
    exact_mod_cast this
  have hnDeltaZero : nDelta = 0 := by
    have : (nDelta : ℤ) = 0 := by omega
    exact_mod_cast this
  have htermZero : 2 * (scale : ℤ) * (z ^ 2 - z) = 0 := by omega
  have htwoScaleNe : (2 * (scale : ℤ) : ℤ) ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (by exact_mod_cast (Nat.ne_of_gt hscalePos))
  have hzQuadraticZero : z ^ 2 - z = 0 :=
    (mul_eq_zero.mp htermZero).resolve_left htwoScaleNe
  have hzProductZero : z * (z - 1) = 0 := by
    calc
      z * (z - 1) = z ^ 2 - z := by ring
      _ = 0 := hzQuadraticZero
  have hzCases : z = 0 ∨ z = 1 := by
    rcases mul_eq_zero.mp hzProductZero with hz | hz
    · exact Or.inl hz
    · exact Or.inr (by omega)
  exact ⟨hnGammaOne, hnDeltaZero, hzCases⟩

/-! ## The two integral projections -/

/-- The two successive integral orthogonal projections at the start of
Peterfalvi (9.11.7): first onto `T₄`, then onto `T₁`. -/
theorem pTypeCore_two_stage_orthogonal_split
    {Q : Type u} [Group Q] [Fintype Q]
    (T₄ T₁ : Finset (ClassFunction Q ℂ))
    (hT₄virtual : ∀ alpha ∈ T₄, ClassFunction.IsVirtual alpha)
    (hT₄orthonormal : ∀ alpha ∈ T₄, ∀ gamma ∈ T₄,
      characterPairing alpha gamma =
        if alpha = gamma then 1 else 0)
    (hT₁virtual : ∀ alpha ∈ T₁, ClassFunction.IsVirtual alpha)
    (hT₁orthonormal : ∀ alpha ∈ T₁, ∀ gamma ∈ T₁,
      characterPairing alpha gamma =
        if alpha = gamma then 1 else 0)
    {beta : ClassFunction Q ℂ}
    (hbeta : ClassFunction.IsVirtual beta) :
    ∃ Gamma B Delta : ClassFunction Q ℂ,
      Gamma ∈ AddSubgroup.closure
        (↑T₄ : Set (ClassFunction Q ℂ)) ∧
      B ∈ AddSubgroup.closure
        (↑T₁ : Set (ClassFunction Q ℂ)) ∧
      ClassFunction.IsVirtual Gamma ∧
      ClassFunction.IsVirtual B ∧
      ClassFunction.IsVirtual Delta ∧
      beta = Gamma + B + Delta ∧
      (∀ alpha ∈ T₄, characterPairing (B + Delta) alpha = 0) ∧
      (∀ alpha ∈ T₁, characterPairing Delta alpha = 0) ∧
      characterPairing Gamma (B + Delta) = 0 ∧
      characterPairing B Delta = 0 := by
  obtain ⟨Gamma, rem, hGammaSpan, hGammaVirtual, hremVirtual,
      hbetaSplit, hremT₄, hGammaRem⟩ :=
    orthogonal_split_virtual T₄ hT₄virtual hT₄orthonormal hbeta
  obtain ⟨B, Delta, hBSpan, hBVirtual, hDeltaVirtual,
      hremSplit, hDeltaT₁, hBDelta⟩ :=
    orthogonal_split_virtual T₁ hT₁virtual hT₁orthonormal hremVirtual
  refine ⟨Gamma, B, Delta, hGammaSpan, hBSpan, hGammaVirtual,
    hBVirtual, hDeltaVirtual, ?_, ?_, hDeltaT₁, ?_, hBDelta⟩
  · calc
      beta = Gamma + rem := hbetaSplit
      _ = Gamma + B + Delta := by rw [hremSplit]; abel
  · intro alpha halpha
    rw [← hremSplit]
    exact hremT₄ alpha halpha
  · rw [← hremSplit]
    exact hGammaRem

/-! ## Eliminating the Boolean coefficient -/

/-- The final pairing calculation in (9.11.8).  If the distinguished
coefficient differs by one from all other `T₁` coefficients and
`T₁.card = 2 * scale`, then the nonzero Boolean case would force an
integer multiple of `scale` to be one. -/
theorem pTypeCore_bool_eq_false_of_alpha_pairing
    {Q : Type u} [Group Q] [Fintype Q]
    (T₁ : Finset (ClassFunction Q ℂ))
    {alpha beta Gamma phi : ClassFunction Q ℂ}
    (halpha : ClassFunction.IsVirtual alpha)
    (hphiVirtual : ClassFunction.IsVirtual phi)
    (hphi : phi ∈ T₁)
    (scale : ℕ) (hscale : 1 < scale)
    (hcard : T₁.card = 2 * scale)
    (hpairDiff : ∀ eta ∈ T₁, eta ≠ phi →
      characterPairing alpha (phi - eta) = -1)
    (hGamma : characterPairing alpha Gamma = 0)
    (halphaBeta : characterPairing alpha beta = (scale : ℂ))
    (b : Bool)
    (hdecomp : beta = Gamma - (scale : ℂ) • phi +
      (b.toNat : ℂ) • ∑ eta ∈ T₁, eta) :
    b = false := by
  classical
  obtain ⟨c, hc⟩ := pTypeCore_virtual_pairing_isInt halpha hphiVirtual
  let x : ℤ := c + 1
  have hphiPair :
      characterPairing alpha phi = ((x - 1 : ℤ) : ℂ) := by
    rw [hc]
    congr 1
    dsimp only [x]
    omega
  have hother (eta : ClassFunction Q ℂ)
      (heta : eta ∈ T₁) (hne : eta ≠ phi) :
      characterPairing alpha eta = (x : ℂ) := by
    have h := hpairDiff eta heta hne
    rw [pairing_sub_right, hphiPair] at h
    have hx : ((x - 1 : ℤ) : ℂ) -
        characterPairing alpha eta = (-1 : ℂ) := by
      simpa using h
    push_cast at hx
    linear_combination -hx
  have hsumPair :
      characterPairing alpha (∑ eta ∈ T₁, eta) =
        (((2 * scale : ℕ) : ℤ) * x - 1 : ℤ) := by
    rw [pairing_finset_sum_right, ← T₁.add_sum_erase
      (fun eta ↦ characterPairing alpha eta) hphi]
    have hrest :
        ∑ eta ∈ T₁.erase phi, characterPairing alpha eta =
          ((T₁.card - 1 : ℕ) : ℂ) * (x : ℂ) := by
      calc
        _ = ∑ _eta ∈ T₁.erase phi, (x : ℂ) := by
          apply Finset.sum_congr rfl
          intro eta heta
          exact hother eta (Finset.mem_of_mem_erase heta)
            (Finset.ne_of_mem_erase heta)
        _ = ((T₁.erase phi).card : ℂ) * (x : ℂ) := by simp
        _ = ((T₁.card - 1 : ℕ) : ℂ) * (x : ℂ) := by
          rw [Finset.card_erase_of_mem hphi]
    rw [hphiPair, hrest, hcard]
    have hpredCast : (((2 * scale - 1 : ℕ) : ℂ)) =
        ((2 * scale : ℕ) : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * scale)]
      norm_num
    rw [hpredCast]
    push_cast
    ring
  have hpaired :
      (scale : ℂ) =
        -(scale : ℂ) * ((x - 1 : ℤ) : ℂ) +
          (b.toNat : ℂ) *
            ((((2 * scale : ℕ) : ℤ) * x - 1 : ℤ) : ℂ) := by
    calc
      (scale : ℂ) = characterPairing alpha beta := halphaBeta.symm
      _ = _ := by
        rw [hdecomp, characterPairing_add_right, pairing_sub_right,
          characterPairing_smul_right, characterPairing_smul_right,
          hGamma, hphiPair, hsumPair]
        ring
  cases b with
  | false => rfl
  | true =>
      simp only [Bool.toNat_true, Nat.cast_one, one_mul] at hpaired
      have hint : (scale : ℤ) =
          -(scale : ℤ) * (x - 1) +
            (((2 * scale : ℕ) : ℤ) * x - 1) := by
        apply Int.cast_injective (α := ℂ)
        push_cast
        simpa using hpaired
      have hsx : (scale : ℤ) * x = 1 := by
        rw [Nat.cast_mul, Nat.cast_ofNat] at hint
        nlinarith
      have hsnonneg : (0 : ℤ) ≤ scale := by positivity
      by_cases hx : x ≤ 0
      · have hprod : (scale : ℤ) * x ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hsnonneg hx
        omega
      · have hxone : (1 : ℤ) ≤ x := by omega
        have hscaleLe : (scale : ℤ) ≤ (scale : ℤ) * x := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hxone hsnonneg
        omega

/-! ## The Boolean decomposition -/

/-- Generic integral-lattice form of Peterfalvi (9.11.7).  Two orthogonal
projections, a norm calculation, and a nonzero detector leave exactly one
Boolean coefficient in the `T₁` component. -/
theorem pTypeCore_bool_decomposition_of_orthogonal_splits
    {Q : Type u} [Group Q] [Fintype Q]
    (T₄ T₁ : Finset (ClassFunction Q ℂ))
    (hT₄virtual : ∀ alpha ∈ T₄, ClassFunction.IsVirtual alpha)
    (hT₄orthonormal : ∀ alpha ∈ T₄, ∀ gamma ∈ T₄,
      characterPairing alpha gamma =
        if alpha = gamma then 1 else 0)
    (hT₁virtual : ∀ alpha ∈ T₁, ClassFunction.IsVirtual alpha)
    (hT₁orthonormal : ∀ alpha ∈ T₁, ∀ gamma ∈ T₁,
      characterPairing alpha gamma =
        if alpha = gamma then 1 else 0)
    (hcross : ∀ gamma ∈ T₄, ∀ psi ∈ T₁,
      characterPairing gamma psi = 0)
    {beta phi : ClassFunction Q ℂ} {scale : ℕ}
    (hbetaVirtual : ClassFunction.IsVirtual beta)
    (hphi : phi ∈ T₁)
    (hcard : T₁.card = 2 * scale)
    (hbetaNorm : characterPairing beta beta =
      ((1 + scale ^ 2 : ℕ) : ℂ))
    (hbetaDiff : ∀ psi ∈ T₁, psi ≠ phi →
      characterPairing beta (phi - psi) = -(scale : ℂ))
    (hdetector : ∃ detector : ClassFunction Q ℂ,
      detector ∈ AddSubgroup.closure
        (↑T₄ : Set (ClassFunction Q ℂ)) ∧
      characterPairing beta detector ≠ 0) :
    ∃ Gamma : ClassFunction Q ℂ,
      Gamma ∈ AddSubgroup.closure
        (↑T₄ : Set (ClassFunction Q ℂ)) ∧
      characterPairing Gamma Gamma = 1 ∧
      ∃ b : Bool,
        beta = Gamma - (scale : ℂ) • phi +
          (b.toNat : ℂ) • (∑ psi ∈ T₁, psi) := by
  classical
  obtain ⟨Gamma, B, Delta, hGammaSpan, hBSpan, hGammaVirtual,
      hBVirtual, hDeltaVirtual, hbetaThree, hrestT₄, hDeltaT₁,
      hGammaRest, hBDelta⟩ :=
    pTypeCore_two_stage_orthogonal_split T₄ T₁ hT₄virtual
      hT₄orthonormal hT₁virtual hT₁orthonormal hbetaVirtual

  have hGammaT₁ : ∀ psi ∈ T₁,
      characterPairing Gamma psi = 0 := by
    intro psi hpsi
    exact pairing_eq_zero_of_left_span T₄ psi
      (fun gamma hgamma ↦ hcross gamma hgamma psi hpsi) hGammaSpan
  have hBPair : ∀ psi ∈ T₁,
      characterPairing B psi = characterPairing beta psi := by
    intro psi hpsi
    have h := congrArg
      (fun f : ClassFunction Q ℂ ↦ characterPairing f psi) hbetaThree
    simp only [characterPairing_add_left, hGammaT₁ psi hpsi,
      hDeltaT₁ psi hpsi, zero_add, add_zero] at h
    exact h.symm

  obtain ⟨z₀, hz₀⟩ :=
    pTypeCore_virtual_pairing_isInt hbetaVirtual (hT₁virtual phi hphi)
  let z : ℤ := (scale : ℤ) + z₀
  have hzCast : (z : ℂ) =
      (scale : ℂ) + characterPairing beta phi := by
    dsimp only [z]
    push_cast
    rw [hz₀]
  have hcoefficient : ∀ psi ∈ T₁,
      characterPairing B psi =
        if psi = phi then (z : ℂ) - (scale : ℂ) else (z : ℂ) := by
    intro psi hpsi
    rw [hBPair psi hpsi]
    by_cases hpsiPhi : psi = phi
    · subst psi
      rw [if_pos rfl, hzCast]
      ring
    · rw [if_neg hpsiPhi]
      have hdiff := hbetaDiff psi hpsi hpsiPhi
      rw [pairing_sub_right] at hdiff
      rw [hzCast]
      linear_combination -hdiff

  have hBExpansion :
      B = ∑ psi ∈ T₁, characterPairing B psi • psi :=
    pTypeCore_eq_sum_pairing_smul_of_mem_closure
      T₁ hT₁orthonormal hBSpan
  have hsplitExpansion :
      (∑ psi ∈ T₁, characterPairing B psi • psi) =
        characterPairing B phi • phi +
          ∑ psi ∈ T₁ \ {phi}, characterPairing B psi • psi := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hphi]
  have hsplitSum :
      (∑ psi ∈ T₁, psi) =
        phi + ∑ psi ∈ T₁ \ {phi}, psi := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hphi]
  have hrestExpansion :
      (∑ psi ∈ T₁ \ {phi}, characterPairing B psi • psi) =
        (z : ℂ) • ∑ psi ∈ T₁ \ {phi}, psi := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro psi hpsi
    have hpsiT₁ := (Finset.mem_sdiff.mp hpsi).1
    have hpsiNe : psi ≠ phi := by
      simpa using (Finset.mem_sdiff.mp hpsi).2
    rw [hcoefficient psi hpsiT₁, if_neg hpsiNe]
  have hBFormula :
      B = -(scale : ℂ) • phi +
        (z : ℂ) • (∑ psi ∈ T₁, psi) := by
    calc
      B = ∑ psi ∈ T₁, characterPairing B psi • psi := hBExpansion
      _ = characterPairing B phi • phi +
          ∑ psi ∈ T₁ \ {phi}, characterPairing B psi • psi :=
        hsplitExpansion
      _ = ((z : ℂ) - (scale : ℂ)) • phi +
          (z : ℂ) • ∑ psi ∈ T₁ \ {phi}, psi := by
        rw [hcoefficient phi hphi, if_pos rfl, hrestExpansion]
      _ = -(scale : ℂ) • phi +
          (z : ℂ) • (∑ psi ∈ T₁, psi) := by
        rw [hsplitSum]
        module

  let sumT₁ : ClassFunction Q ℂ := ∑ psi ∈ T₁, psi
  have hphiNorm : characterPairing phi phi = 1 := by
    rw [hT₁orthonormal phi hphi phi hphi, if_pos rfl]
  have hsumNorm : characterPairing sumT₁ sumT₁ = (T₁.card : ℂ) := by
    exact pTypeCore_pairing_orthonormal_sum_self T₁ hT₁orthonormal
  have hphiSum : characterPairing phi sumT₁ = 1 := by
    exact pairing_member_sum_eq_one T₁ hT₁orthonormal hphi
  have hsumPhi : characterPairing sumT₁ phi = 1 := by
    rw [characterPairing_comm, hphiSum]
  have hBNorm : characterPairing B B =
      (((scale : ℤ) ^ 2 +
        2 * (scale : ℤ) * (z ^ 2 - z) : ℤ) : ℂ) := by
    rw [hBFormula]
    change characterPairing
        (-(scale : ℂ) • phi + (z : ℂ) • sumT₁)
        (-(scale : ℂ) • phi + (z : ℂ) • sumT₁) = _
    simp only [characterPairing_add_left, characterPairing_add_right,
      characterPairing_smul_left, characterPairing_smul_right,
      hphiNorm, hphiSum, hsumPhi, hsumNorm]
    rw [hcard]
    push_cast
    ring

  have hnormTotal :
      characterPairing beta beta =
        characterPairing Gamma Gamma +
          characterPairing B B + characterPairing Delta Delta := by
    have hsplit : beta = Gamma + (B + Delta) := by
      calc
        beta = Gamma + B + Delta := hbetaThree
        _ = Gamma + (B + Delta) := by abel
    calc
      characterPairing beta beta =
          characterPairing (Gamma + (B + Delta))
            (Gamma + (B + Delta)) := by rw [hsplit]
      _ = characterPairing Gamma Gamma +
          characterPairing (B + Delta) (B + Delta) :=
        pairing_add_self_of_orthogonal Gamma (B + Delta) hGammaRest
      _ = characterPairing Gamma Gamma +
          (characterPairing B B + characterPairing Delta Delta) := by
        rw [pairing_add_self_of_orthogonal B Delta hBDelta]
      _ = _ := by ring

  obtain ⟨detector, hdetectorSpan, hdetectorPair⟩ := hdetector
  have hrestDetector : characterPairing (B + Delta) detector = 0 :=
    pairing_eq_zero_of_right_span (B + Delta) T₄ hrestT₄ hdetectorSpan
  have hGammaNe : Gamma ≠ 0 := by
    intro hGammaZero
    apply hdetectorPair
    have hsplit : beta = Gamma + (B + Delta) := by
      calc
        beta = Gamma + B + Delta := hbetaThree
        _ = Gamma + (B + Delta) := by abel
    rw [hsplit, characterPairing_add_left, hGammaZero, hrestDetector]
    simp

  obtain ⟨nGamma, hnGamma⟩ :=
    virtual_self_pairing_eq_nat hGammaVirtual
  obtain ⟨nDelta, hnDelta⟩ :=
    virtual_self_pairing_eq_nat hDeltaVirtual
  have hnGammaPos : 0 < nGamma := by
    apply Nat.pos_of_ne_zero
    intro hnGammaZero
    apply hGammaNe
    apply pTypeCore_virtual_eq_zero_of_pairing_self_eq_zero hGammaVirtual
    rw [hnGamma, hnGammaZero]
    norm_num
  have hnormComplex :
      ((1 + scale ^ 2 : ℕ) : ℂ) =
        (nGamma : ℂ) +
          (((scale : ℤ) ^ 2 +
            2 * (scale : ℤ) * (z ^ 2 - z) : ℤ) : ℂ) +
          (nDelta : ℂ) := by
    calc
      ((1 + scale ^ 2 : ℕ) : ℂ) = characterPairing beta beta :=
        hbetaNorm.symm
      _ = characterPairing Gamma Gamma +
          characterPairing B B + characterPairing Delta Delta := hnormTotal
      _ = _ := by rw [hnGamma, hBNorm, hnDelta]
  have hnormInt :
      (1 + (scale : ℤ) ^ 2 : ℤ) =
        (nGamma : ℤ) +
          ((scale : ℤ) ^ 2 + 2 * (scale : ℤ) * (z ^ 2 - z)) +
          (nDelta : ℤ) := by
    exact_mod_cast hnormComplex
  have hscalePos : 0 < scale := by
    have hcardPos : 0 < T₁.card := Finset.card_pos.mpr ⟨phi, hphi⟩
    omega
  obtain ⟨hnGammaOne, hnDeltaZero, hzCases⟩ :=
    boolean_norm_arithmetic scale nGamma nDelta z hscalePos hnGammaPos hnormInt

  have hGammaNorm : characterPairing Gamma Gamma = 1 := by
    rw [hnGamma, hnGammaOne]
    norm_num
  have hDeltaZero : Delta = 0 := by
    apply pTypeCore_virtual_eq_zero_of_pairing_self_eq_zero hDeltaVirtual
    rw [hnDelta, hnDeltaZero]
    norm_num
  refine ⟨Gamma, hGammaSpan, hGammaNorm, ?_⟩
  rcases hzCases with hz | hz
  · refine ⟨false, ?_⟩
    calc
      beta = Gamma + B + Delta := hbetaThree
      _ = Gamma - (scale : ℂ) • phi := by
        rw [hBFormula, hDeltaZero, hz]
        simp
        module
      _ = Gamma - (scale : ℂ) • phi +
          (false.toNat : ℂ) • (∑ psi ∈ T₁, psi) := by simp
  · refine ⟨true, ?_⟩
    calc
      beta = Gamma + B + Delta := hbetaThree
      _ = Gamma - (scale : ℂ) • phi +
          (1 : ℂ) • (∑ psi ∈ T₁, psi) := by
        rw [hBFormula, hDeltaZero, hz]
        norm_num
        module
      _ = Gamma - (scale : ℂ) • phi +
          (true.toNat : ℂ) • (∑ psi ∈ T₁, psi) := by simp

end PTypeCoreBooleanInternal

end

end Submission.OddOrder.PF
