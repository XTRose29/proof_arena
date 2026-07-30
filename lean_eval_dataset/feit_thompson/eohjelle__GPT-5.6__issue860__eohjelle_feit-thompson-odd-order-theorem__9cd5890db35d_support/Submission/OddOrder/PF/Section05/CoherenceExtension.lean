import Submission.OddOrder.PF.Section05.SubcoherentProperties
import Submission.OddOrder.PF.Section03.CyclicTIPairingExchange

/-!
# Extending coherent families

This file ports the last part of the coherence argument in
`PFsection5.v`, from Peterfalvi (5.6) through (5.8).  As elsewhere in the
Lean port, duplicate-free source sequences are represented by sets and their
integral spans by `AddSubgroup.closure`.

The source coefficient field `algC` carries an order on its rational-real
subfield.  Lean's `ℂ` is intentionally unordered.  In `extend_coherent` the
source inequality is therefore stated after applying `Complex.re`.  Every
quantity occurring there is a natural degree or a natural squared norm by
`subcoherent.source_character`, so this is precisely the ordered statement
used in the source proof and introduces no additional order hypothesis.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical Pointwise

universe u

local instance coherenceExtensionInvertibleCard
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

section AbstractCoherence

variable {L G : Type u} [Group L] [Fintype L] [Group G] [Fintype G]

/-- The summand `chi(1)^2 / [chi,chi]` in Peterfalvi's degree bound,
transported from the ordered rational-real subfield of `algC` to `ℝ`. -/
def coherenceDegreeWeight
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : ClassFunction Q ℂ) : ℝ :=
  (chi 1).re ^ 2 / (characterPairing chi chi).re

/-- The degree bound attached to a finite family. -/
def coherenceDegreeSum
    {Q : Type u} [Group Q] [Fintype Q]
    (S : Set (ClassFunction Q ℂ)) (hS : S.Finite) : ℝ :=
  ∑ chi ∈ hS.toFinset, coherenceDegreeWeight chi

private theorem pairing_neg_left
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (-phi) psi = -characterPairing phi psi := by
  rw [← neg_one_smul ℂ phi, characterPairing_smul_left]
  ring

private theorem pairing_neg_right
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing phi (-psi) = -characterPairing phi psi := by
  rw [← neg_one_smul ℂ psi, characterPairing_smul_right]
  ring

private theorem pairing_sub_left
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    characterPairing (phi - psi) theta =
      characterPairing phi theta - characterPairing psi theta := by
  rw [sub_eq_add_neg, characterPairing_add_left,
    pairing_neg_left, sub_eq_add_neg]

private theorem pairing_sub_right
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    characterPairing phi (psi - theta) =
      characterPairing phi psi - characterPairing phi theta := by
  rw [sub_eq_add_neg, characterPairing_add_right,
    pairing_neg_right, sub_eq_add_neg]

private theorem pairing_self_sub_of_orthogonal
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ)
    (horth : characterPairing phi psi = 0) :
    characterPairing (phi - psi) (phi - psi) =
      characterPairing phi phi + characterPairing psi psi := by
  rw [pairing_sub_left, pairing_sub_right, pairing_sub_right,
    horth, characterPairing_comm psi phi, horth]
  ring

private theorem pairing_self_add_of_orthogonal
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ)
    (horth : characterPairing phi psi = 0) :
    characterPairing (phi + psi) (phi + psi) =
      characterPairing phi phi + characterPairing psi psi := by
  rw [characterPairing_add_left, characterPairing_add_right,
    characterPairing_add_right, horth,
    characterPairing_comm psi phi, horth]
  ring

private theorem pairing_finset_sum_left
    {Q : Type u} [Group Q] [Fintype Q]
    {I : Type*} (s : Finset I) (f : I → ClassFunction Q ℂ)
    (psi : ClassFunction Q ℂ) :
    characterPairing (∑ i ∈ s, f i) psi =
      ∑ i ∈ s, characterPairing (f i) psi := by
  exact map_sum (characterPairingRight psi) (fun i ↦ f i) s

private theorem pairing_finset_sum_right
    {Q : Type u} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) {I : Type*}
    (s : Finset I) (f : I → ClassFunction Q ℂ) :
    characterPairing phi (∑ i ∈ s, f i) =
      ∑ i ∈ s, characterPairing phi (f i) := by
  exact map_sum (characterPairingLeft phi) (fun i ↦ f i) s

private theorem inverseLinear_involutive
    {Q : Type u} [Group Q] (phi : ClassFunction Q ℂ) :
    ClassFunction.inverseLinear (ClassFunction.inverseLinear phi) = phi := by
  ext x
  simp

private theorem pairing_inverseLinear
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (ClassFunction.inverseLinear phi)
        (ClassFunction.inverseLinear psi) = characterPairing phi psi := by
  unfold characterPairing
  congr 1
  refine Fintype.sum_equiv (Equiv.inv Q) _ _ fun x ↦ ?_
  simp only [Equiv.inv_apply, ClassFunction.inverseLinear_apply, inv_inv]

private theorem pairing_inverseLinear_left
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (ClassFunction.inverseLinear phi) psi =
      characterPairing phi (ClassFunction.inverseLinear psi) := by
  calc
    characterPairing (ClassFunction.inverseLinear phi) psi =
        characterPairing (ClassFunction.inverseLinear phi)
          (ClassFunction.inverseLinear
            (ClassFunction.inverseLinear psi)) := by
          rw [inverseLinear_involutive]
    _ = characterPairing phi (ClassFunction.inverseLinear psi) :=
      pairing_inverseLinear phi (ClassFunction.inverseLinear psi)

private theorem inverse_sub_supported
    {Q : Type u} [Group Q] (phi : ClassFunction Q ℂ) :
    phi - ClassFunction.inverseLinear phi ∈
      ClassFunction.supportedOn (nonidentitySet Q) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxone : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp

private theorem virtual_pairing_isInt
    {Q : Type u} [Group Q] [Fintype Q]
    {phi psi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hpsi : ClassFunction.IsVirtual psi) :
    ∃ z : ℤ, characterPairing phi psi = (z : ℂ) := by
  obtain ⟨v, rfl⟩ := hphi
  obtain ⟨w, rfl⟩ := hpsi
  exact ⟨coeffDot v w, VirtualCharacter.characterPairing_realize v w⟩

private theorem pairing_self_eq_sum_irreducible_coeff_sq
    {Q : Type u} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) :
    characterPairing phi phi =
      ∑ chi : IrreducibleCharacter Q ℂ,
        characterPairing (chi : ClassFunction Q ℂ) phi *
          characterPairing (chi : ClassFunction Q ℂ) phi := by
  calc
    characterPairing phi phi =
        characterPairing (irreducibleCharacterExpansion phi)
          phi := by rw [irreducibleCharacterExpansion_eq]
    _ = _ := by
      change characterPairingRight phi
          (irreducibleCharacterExpansion phi) = _
      rw [irreducibleCharacterExpansion, map_sum]
      apply Finset.sum_congr rfl
      intro chi _
      rw [map_smul]
      rfl

private theorem pairing_self_re_nonneg_of_real_coeff
    {Q : Type u} [Group Q] [Fintype Q]
    {phi : ClassFunction Q ℂ}
    (hreal : ∀ chi : IrreducibleCharacter Q ℂ,
      ∃ r : ℝ,
        characterPairing (chi : ClassFunction Q ℂ) phi = (r : ℂ)) :
    0 ≤ (characterPairing phi phi).re := by
  rw [pairing_self_eq_sum_irreducible_coeff_sq]
  change 0 ≤ Complex.reCLM
    (∑ chi : IrreducibleCharacter Q ℂ,
      characterPairing (chi : ClassFunction Q ℂ) phi *
        characterPairing (chi : ClassFunction Q ℂ) phi)
  rw [map_sum]
  apply Finset.sum_nonneg
  intro chi hchi
  obtain ⟨r, hr⟩ := hreal chi
  change 0 ≤ (characterPairing (chi : ClassFunction Q ℂ) phi *
    characterPairing (chi : ClassFunction Q ℂ) phi).re
  rw [hr]
  norm_num
  exact mul_self_nonneg r

private theorem virtual_eq_zero_of_pairing_self_eq_zero
    {Q : Type u} [Group Q] [Fintype Q]
    {phi : ClassFunction Q ℂ} (hphi : ClassFunction.IsVirtual phi)
    (hzero : characterPairing phi phi = 0) : phi = 0 := by
  obtain ⟨z, hz⟩ := hphi
  have hcast : ((normSq z : ℤ) : ℂ) = 0 := by
    rw [← VirtualCharacter.characterPairing_realize_self, hz]
    exact hzero
  have hnorm0 : normSq z = 0 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_zero] using hcast
  have hz0 : z = 0 := (normSq_eq_zero_iff z).mp hnorm0
  rw [← hz, hz0]
  simp

private theorem source_degree_re_pos
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {phi : ClassFunction L ℂ} (hphi : phi ∈ S) :
    0 < (phi 1).re := by
  obtain ⟨d, hd⟩ :=
    (hsub.source_character phi hphi).exists_nat_degree
  have hd0 : d ≠ 0 := by
    intro hdzero
    apply hsub.degree_ne_zero phi hphi
    rw [hd, hdzero]
    simp
  rw [hd]
  norm_num [Nat.pos_of_ne_zero hd0]

private theorem source_norm_re_pos
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {phi : ClassFunction L ℂ} (hphi : phi ∈ S) :
    0 < (characterPairing phi phi).re := by
  obtain ⟨n, hn⟩ := (hsub.source_virtual phi hphi).exists_nat_norm
  have hn0 : n ≠ 0 := by
    intro hnzero
    have hpair0 : characterPairing phi phi = 0 := by
      rw [hn, hnzero]
      simp
    have hphi0 := virtual_eq_zero_of_pairing_self_eq_zero
      (hsub.source_virtual phi hphi) hpair0
    exact hsub.zero_not_mem (hphi0 ▸ hphi)
  rw [hn]
  norm_num [Nat.pos_of_ne_zero hn0]

private theorem generator_mem_closure
    {Q : Type u} [Group Q] {S : Set (ClassFunction Q ℂ)}
    {phi : ClassFunction Q ℂ} (hphi : phi ∈ S) :
    phi ∈ AddSubgroup.closure S :=
  AddSubgroup.subset_closure hphi

private theorem inverse_mem_closure
    {Q : Type u} [Group Q] {S : Set (ClassFunction Q ℂ)}
    (hclosed : cfConjC_closed S)
    {phi : ClassFunction Q ℂ} (hphi : phi ∈ AddSubgroup.closure S) :
    ClassFunction.inverseLinear phi ∈ AddSubgroup.closure S := by
  induction hphi using AddSubgroup.closure_induction with
  | mem phi hphi => exact AddSubgroup.subset_closure (hclosed phi hphi)
  | zero => simpa using (AddSubgroup.closure S).zero_mem
  | add phi psi hphi hpsi ihphi ihpsi =>
      simpa only [map_add] using (AddSubgroup.closure S).add_mem ihphi ihpsi
  | neg phi hphi ihphi =>
      simpa only [map_neg] using (AddSubgroup.closure S).neg_mem ihphi

private theorem sub_supported_of_one_eq
    (phi psi : ClassFunction L ℂ) (h : phi 1 = psi 1) :
    phi - psi ∈ ClassFunction.supportedOn (nonidentitySet L) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxone : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp [h]

private theorem pairClosure_data
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {chi psi : ClassFunction L ℂ} (hchi : chi ∈ S) (hpsi : psi ∈ S)
    (hdegree : chi 1 = psi 1)
    {u : ClassFunction L ℂ}
    (hu : u ∈ AddSubgroup.closure
      ({chi - psi,
        chi - ClassFunction.inverseLinear chi} : Set (ClassFunction L ℂ))) :
    u ∈ AddSubgroup.closure S ∧
      u ∈ ClassFunction.supportedOn (nonidentitySet L) := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact ⟨(AddSubgroup.closure S).sub_mem
          (AddSubgroup.subset_closure hchi)
          (AddSubgroup.subset_closure hpsi),
          sub_supported_of_one_eq _ _ hdegree⟩
      · exact ⟨(AddSubgroup.closure S).sub_mem
          (AddSubgroup.subset_closure hchi)
          (AddSubgroup.subset_closure (hsub.inverse_mem chi hchi)),
          inverse_sub_supported chi⟩
  | zero =>
      exact ⟨(AddSubgroup.closure S).zero_mem,
        (ClassFunction.supportedOn (R := ℂ) (nonidentitySet L)).zero_mem⟩
  | add a b ha hb iha ihb =>
      exact ⟨(AddSubgroup.closure S).add_mem iha.1 ihb.1,
        (ClassFunction.supportedOn (R := ℂ) (nonidentitySet L)).add_mem
          iha.2 ihb.2⟩
  | neg a ha iha =>
      exact ⟨(AddSubgroup.closure S).neg_mem iha.1,
        (ClassFunction.supportedOn (R := ℂ) (nonidentitySet L)).neg_mem
          iha.2⟩

private theorem virtual_of_mem_imageClosure
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {chi : ClassFunction L ℂ} (hchi : chi ∈ S)
    {X : ClassFunction G ℂ}
    (hX : X ∈ AddSubgroup.closure
      (↑(R chi) : Set (ClassFunction G ℂ))) :
    ClassFunction.IsVirtual X := by
  induction hX using AddSubgroup.closure_induction with
  | mem alpha halpha => exact hsub.image_virtual chi hchi alpha halpha
  | zero => exact ClassFunction.IsVirtual.zero
  | add a b ha hb iha ihb => exact iha.add ihb
  | neg a ha iha => exact iha.neg

private theorem imageClosures_orthogonal
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {a b : ClassFunction L ℂ} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (habInv : a ≠ ClassFunction.inverseLinear b)
    {X Y : ClassFunction G ℂ}
    (hX : X ∈ AddSubgroup.closure
      (↑(R a) : Set (ClassFunction G ℂ)))
    (hY : Y ∈ AddSubgroup.closure
      (↑(R b) : Set (ClassFunction G ℂ))) :
    characterPairing X Y = 0 := by
  have habPair : characterPairing a b = 0 :=
    hsub.pairwise_orthogonal ha hb hab
  have habInvPair :
      characterPairing a (ClassFunction.inverseLinear b) = 0 :=
    hsub.pairwise_orthogonal ha (hsub.inverse_mem b hb) habInv
  have hgenerator {alpha : ClassFunction G ℂ} (halpha : alpha ∈ R a)
      {beta : ClassFunction G ℂ} (hbeta : beta ∈ R b) :
      characterPairing alpha beta = 0 :=
    hsub.image_orthogonal b hb a ha habPair habInvPair
      alpha halpha beta hbeta
  have hright {alpha : ClassFunction G ℂ} (halpha : alpha ∈ R a)
      {Y : ClassFunction G ℂ}
      (hY : Y ∈ AddSubgroup.closure
        (↑(R b) : Set (ClassFunction G ℂ))) :
      characterPairing alpha Y = 0 := by
    induction hY using AddSubgroup.closure_induction with
    | mem beta hbeta => exact hgenerator halpha hbeta
    | zero => simp
    | add y z hy hz ihy ihz =>
        rw [characterPairing_add_right, ihy, ihz, add_zero]
    | neg y hy ihy => rw [pairing_neg_right, ihy, neg_zero]
  induction hX using AddSubgroup.closure_induction with
  | mem alpha halpha => exact hright halpha hY
  | zero => simp
  | add x z hx hz ihx ihz =>
      rw [characterPairing_add_left, ihx, ihz, add_zero]
  | neg x hx ihx => rw [pairing_neg_left, ihx, neg_zero]

private theorem orthonormal_subset_norm
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {chi : ClassFunction L ℂ} (hchi : chi ∈ S)
    (E : Finset (ClassFunction G ℂ)) (hER : E ⊆ R chi) :
    characterPairing (∑ alpha ∈ E, alpha) (∑ alpha ∈ E, alpha) =
      (E.card : ℂ) := by
  rw [pairing_finset_sum_left]
  calc
    (∑ alpha ∈ E, characterPairing alpha (∑ beta ∈ E, beta)) =
        ∑ _alpha ∈ E, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      rw [pairing_finset_sum_right, Finset.sum_eq_single alpha]
      · rw [hsub.image_orthonormal chi hchi alpha (hER halpha)
          alpha (hER halpha), if_pos rfl]
      · intro beta hbeta hne
        rw [hsub.image_orthonormal chi hchi alpha (hER halpha)
          beta (hER hbeta), if_neg hne.symm]
      · exact fun h ↦ (h halpha).elim
    _ = (E.card : ℂ) := by simp

private theorem orthonormal_subset_full
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {chi : ClassFunction L ℂ} (hchi : chi ∈ S)
    (E : Finset (ClassFunction G ℂ)) (hER : E ⊆ R chi) :
    characterPairing (∑ alpha ∈ E, alpha)
        (∑ alpha ∈ R chi, alpha) = (E.card : ℂ) := by
  rw [pairing_finset_sum_left]
  calc
    (∑ alpha ∈ E,
        characterPairing alpha (∑ beta ∈ R chi, beta)) =
        ∑ _alpha ∈ E, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      rw [pairing_finset_sum_right, Finset.sum_eq_single alpha]
      · rw [hsub.image_orthonormal chi hchi alpha (hER halpha)
          alpha (hER halpha), if_pos rfl]
      · intro beta hbeta hne
        rw [hsub.image_orthonormal chi hchi alpha (hER halpha)
          beta hbeta, if_neg hne.symm]
      · exact fun h ↦ (h (hER halpha)).elim
    _ = (E.card : ℂ) := by simp

/- Peterfalvi (5.6): a coherent family extends below the degree bound. -/
set_option maxHeartbeats 2000000 in
theorem extend_coherent
    {S S1 : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    (hS1 : cfConjC_subset S1 S)
    {xi1 chi : ClassFunction L ℂ}
    (hxi1 : xi1 ∈ S1) (hchi : chi ∈ S) (hchiNot : chi ∉ S1)
    (hcoh : coherent S1 (nonidentitySet L) tau)
    (hdiv : ∃ a : ℕ, chi 1 = (a : ℂ) * xi1 1)
    (hbound : 2 * (chi 1).re * (xi1 1).re <
      coherenceDegreeSum S1 (hsub.finite.subset hS1.1)) :
    coherent ({chi, ClassFunction.inverseLinear chi} ∪ S1)
      (nonidentitySet L) tau := by
  classical
  obtain ⟨tau1, hcoh1⟩ := hcoh
  obtain ⟨a, hdegree⟩ := hdiv
  let psi : ClassFunction L ℂ := (a : ℂ) • xi1
  let beta : ClassFunction L ℂ := chi - psi
  have hxi1S : xi1 ∈ S := hS1.1 hxi1
  have hchiXi1 : characterPairing chi xi1 = 0 := by
    rw [characterPairing_comm]
    exact subset_ortho_subcoherent hsub hS1.1 hchi hchiNot xi1 hxi1
  have hinvChiNot : ClassFunction.inverseLinear chi ∉ S1 := by
    intro hinvMem
    have hinvBack := hS1.2 _ hinvMem
    rw [inverseLinear_involutive] at hinvBack
    exact hchiNot hinvBack
  have hinvChiXi1 :
      characterPairing (ClassFunction.inverseLinear chi) xi1 = 0 :=
    hsub.pairwise_orthogonal (hsub.inverse_mem chi hchi) hxi1S
      (fun heq ↦ hinvChiNot (heq ▸ hxi1))
  have hpsiVirtual : ClassFunction.IsVirtual psi := by
    simpa only [psi] using
      (hsub.source_virtual xi1 hxi1S).natCast_smul a
  have hchiPsi : characterPairing chi psi = 0 := by
    simp only [psi, characterPairing_smul_right, hchiXi1, mul_zero]
  have hinvChiPsi :
      characterPairing (ClassFunction.inverseLinear chi) psi = 0 := by
    simp only [psi, characterPairing_smul_right, hinvChiXi1, mul_zero]
  have hbetaSpan : beta ∈ AddSubgroup.closure S := by
    apply (AddSubgroup.closure S).sub_mem (generator_mem_closure hchi)
    simpa only [psi, Nat.cast_smul_eq_nsmul] using
      (AddSubgroup.closure S).nsmul_mem (generator_mem_closure hxi1S) a
  have hbetaOff : beta ∈ ClassFunction.supportedOn (nonidentitySet L) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxone : x = 1 := by
      simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp only [beta, psi, ClassFunction.sub_apply,
      ClassFunction.smul_apply, smul_eq_mul, hdegree, sub_self]
  have htauBetaVirtual : ClassFunction.IsVirtual (tau beta) :=
    hsub.tau_virtual beta hbetaSpan hbetaOff
  obtain ⟨X, hXspan, hXVirtual, Y, hYVirtual,
      hdecomp, hXY, hYR⟩ :=
    subcoherent_split hsub hchi htauBetaVirtual

  have hYeq : Y = (a : ℂ) • tau1 xi1 := by
    have hS1fin : S1.Finite := hsub.finite.subset hS1.1
    let S1f := hS1fin.toFinset
    have hxi1pos : 0 < (xi1 1).re := source_degree_re_pos hsub hxi1S
    have hxi1ne : (xi1 1).re ≠ 0 := ne_of_gt hxi1pos
    have hnormReal {eta : ClassFunction L ℂ} (heta : eta ∈ S1) :
        characterPairing eta eta =
          ((characterPairing eta eta).re : ℂ) := by
      obtain ⟨n, hn⟩ :=
        (hsub.source_virtual eta (hS1.1 heta)).exists_nat_norm
      rw [hn]
      norm_num
    let coeff : ClassFunction L ℂ → ℝ := fun eta ↦
      (eta 1).re / (xi1 1).re / (characterPairing eta eta).re
    let P : ClassFunction G ℂ :=
      ∑ eta ∈ S1f, (coeff eta : ℂ) • tau1 eta
    have hPpair (eta : ClassFunction L ℂ) (heta : eta ∈ S1) :
        characterPairing P (tau1 eta) =
          (((eta 1).re / (xi1 1).re : ℝ) : ℂ) := by
      simp only [P]
      rw [pairing_finset_sum_left, Finset.sum_eq_single eta]
      · rw [characterPairing_smul_left,
          hcoh1.isometry eta (generator_mem_closure heta)
            eta (generator_mem_closure heta), hnormReal heta]
        have hn0 : (characterPairing eta eta).re ≠ 0 :=
          ne_of_gt (source_norm_re_pos hsub (hS1.1 heta))
        norm_num [coeff]
        field_simp [hxi1ne, hn0]
      · intro z hz hzne
        have hzS1 : z ∈ S1 := by simpa [S1f] using hz
        rw [characterPairing_smul_left,
          hcoh1.isometry z (generator_mem_closure hzS1)
            eta (generator_mem_closure heta),
          hsub.pairwise_orthogonal (hS1.1 hzS1) (hS1.1 heta) hzne,
          mul_zero]
      · intro hnot
        exact (hnot (by simpa [S1f] using heta)).elim
    have hPpairXi1 : characterPairing P (tau1 xi1) = 1 := by
      simpa [hxi1ne] using hPpair xi1 hxi1
    have hPnormRe :
        (characterPairing P P).re =
          coherenceDegreeSum S1 hS1fin / (xi1 1).re ^ 2 := by
      simp only [P]
      rw [pairing_finset_sum_right]
      change Complex.reCLM
          (∑ eta ∈ S1f,
            characterPairing P ((coeff eta : ℂ) • tau1 eta)) = _
      rw [map_sum]
      rw [coherenceDegreeSum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro eta heta
      have hetaS1 : eta ∈ S1 := by simpa [S1f] using heta
      rw [characterPairing_smul_right, hPpair eta hetaS1]
      have hn0 : (characterPairing eta eta).re ≠ 0 :=
        ne_of_gt (source_norm_re_pos hsub (hS1.1 hetaS1))
      norm_num [coeff, coherenceDegreeWeight]
      field_simp [hxi1ne, hn0]
    have hdegreeRe :
        (chi 1).re = (a : ℝ) * (xi1 1).re := by
      rw [hdegree]
      norm_num
    have hPnormLarge :
        2 * (a : ℝ) < (characterPairing P P).re := by
      rw [hPnormRe]
      have hsquare : 0 < (xi1 1).re ^ 2 := sq_pos_of_pos hxi1pos
      apply (lt_div_iff₀ hsquare).2
      rw [hdegreeRe] at hbound
      nlinarith [hbound]

    have hcohR := coherent_ortho_supp hsub hS1 hcoh1 hchi hchiNot
    have hXorthTau (u : ClassFunction L ℂ)
        (hu : u ∈ AddSubgroup.closure S1) :
        characterPairing X (tau1 u) = 0 := by
      rw [characterPairing_comm]
      have horth {V : ClassFunction G ℂ}
          (hV : V ∈ AddSubgroup.closure
            (↑(R chi) : Set (ClassFunction G ℂ))) :
          characterPairing (tau1 u) V = 0 := by
        induction hV using AddSubgroup.closure_induction with
        | mem alpha halpha =>
            exact hcohR (tau1 u) ⟨u, hu, rfl⟩ alpha halpha
        | zero => simp
        | add x z hx hz ihx ihz =>
            rw [characterPairing_add_right, ihx, ihz, add_zero]
        | neg x hx ihx => rw [pairing_neg_right, ihx, neg_zero]
      exact horth hXspan

    obtain ⟨d1, hd1⟩ :=
      (hsub.source_character xi1 hxi1S).exists_nat_degree
    obtain ⟨n1, hn1⟩ :=
      (hsub.source_virtual xi1 hxi1S).exists_nat_norm
    have htauXi1Virtual : ClassFunction.IsVirtual (tau1 xi1) :=
      hcoh1.mapsToVirtual xi1 (generator_mem_closure hxi1)
    obtain ⟨b, hb⟩ := virtual_pairing_isInt hYVirtual htauXi1Virtual
    let lam : ℤ := (a : ℤ) * (n1 : ℤ) - b
    have hbase :
        characterPairing Y (tau1 xi1) =
          (a : ℂ) * characterPairing xi1 xi1 - (lam : ℂ) := by
      rw [hb, hn1]
      simp only [lam]
      push_cast
      ring

    have hYpair (eta : ClassFunction L ℂ) (heta : eta ∈ S1) :
        characterPairing Y (tau1 eta) =
          (a : ℂ) * characterPairing xi1 eta -
            (lam : ℂ) *
              (((eta 1).re / (xi1 1).re : ℝ) : ℂ) := by
      obtain ⟨d, hd⟩ :=
        (hsub.source_character eta (hS1.1 heta)).exists_nat_degree
      let u : ClassFunction L ℂ :=
        (d1 : ℂ) • eta - (d : ℂ) • xi1
      have huSpan : u ∈ AddSubgroup.closure S1 := by
        apply (AddSubgroup.closure S1).sub_mem
        · simpa only [Nat.cast_smul_eq_nsmul] using
            (AddSubgroup.closure S1).nsmul_mem
              (generator_mem_closure heta) d1
        · simpa only [Nat.cast_smul_eq_nsmul] using
            (AddSubgroup.closure S1).nsmul_mem
              (generator_mem_closure hxi1) d
      have huOff :
          u ∈ ClassFunction.supportedOn (nonidentitySet L) := by
        rw [ClassFunction.mem_supportedOn_iff]
        intro x hx
        have hxone : x = 1 := by
          simpa [nonidentitySet] using not_not.mp hx
        subst x
        simp only [u, ClassFunction.sub_apply, ClassFunction.smul_apply,
          smul_eq_mul, hd, hd1]
        push_cast
        ring
      have huSpanS : u ∈ AddSubgroup.closure S :=
        AddSubgroup.closure_mono hS1.1 huSpan
      have huAgree : tau1 u = tau u := hcoh1.agrees u huSpan huOff
      have hiso := hsub.tau_isometry beta hbetaSpan hbetaOff
        u huSpanS huOff
      have htarget :
          characterPairing (tau beta) (tau u) =
            -((d1 : ℂ) * characterPairing Y (tau1 eta) -
              (d : ℂ) * characterPairing Y (tau1 xi1)) := by
        rw [← huAgree, hdecomp, pairing_sub_left,
          hXorthTau u huSpan, zero_sub]
        simp only [u, map_sub, map_smul,
          pairing_sub_right, characterPairing_smul_right]
      have hchiEta : characterPairing chi eta = 0 := by
        rw [characterPairing_comm]
        exact subset_ortho_subcoherent hsub hS1.1 hchi hchiNot eta heta
      have hchiXi1' : characterPairing chi xi1 = 0 := by
        rw [characterPairing_comm]
        exact subset_ortho_subcoherent hsub hS1.1 hchi hchiNot xi1 hxi1
      have hsource :
          characterPairing beta u =
            -((a : ℂ) *
              ((d1 : ℂ) * characterPairing xi1 eta -
                (d : ℂ) * characterPairing xi1 xi1)) := by
        simp only [beta, psi, u, pairing_sub_left, pairing_sub_right,
          characterPairing_smul_left, characterPairing_smul_right,
          hchiEta, hchiXi1', zero_mul]
        ring
      rw [htarget, hsource] at hiso
      have hrel := neg_inj.mp hiso
      rw [hbase] at hrel
      have hd1C : (d1 : ℂ) ≠ 0 := by
        rw [← hd1]
        exact hsub.degree_ne_zero xi1 hxi1S
      have hratio :
          (d : ℂ) / (d1 : ℂ) =
            (((eta 1).re / (xi1 1).re : ℝ) : ℂ) := by
        rw [hd, hd1]
        norm_num
      rw [← hratio]
      field_simp [hd1C]
      linear_combination hrel

    let Z : ClassFunction G ℂ :=
      Y - ((a : ℂ) • tau1 xi1 - (lam : ℂ) • P)
    have hZorth (eta : ClassFunction L ℂ) (heta : eta ∈ S1) :
        characterPairing Z (tau1 eta) = 0 := by
      simp only [Z]
      rw [pairing_sub_left, pairing_sub_left,
        characterPairing_smul_left,
        hcoh1.isometry xi1 (generator_mem_closure hxi1)
          eta (generator_mem_closure heta),
        characterPairing_smul_left, hYpair eta heta, hPpair eta heta]
      ring
    have hZorthP : characterPairing Z P = 0 := by
      simp only [P]
      rw [pairing_finset_sum_right]
      apply Finset.sum_eq_zero
      intro eta heta
      have hetaS1 : eta ∈ S1 := by simpa [S1f] using heta
      rw [characterPairing_smul_right, hZorth eta hetaS1, mul_zero]

    have hirrVirtual (rho : IrreducibleCharacter G ℂ) :
        ClassFunction.IsVirtual (rho : ClassFunction G ℂ) := by
      refine ⟨Finsupp.single rho 1, ?_⟩
      simp
    have hPairPReal (rho : IrreducibleCharacter G ℂ) :
        ∃ r : ℝ,
          characterPairing (rho : ClassFunction G ℂ) P = (r : ℂ) := by
      let q : ClassFunction L ℂ → ℤ := fun eta ↦
        if heta : eta ∈ S1 then
          Classical.choose
            (virtual_pairing_isInt (hirrVirtual rho)
              (hcoh1.mapsToVirtual eta (generator_mem_closure heta)))
        else 0
      have hq (eta : ClassFunction L ℂ) (heta : eta ∈ S1) :
          characterPairing (rho : ClassFunction G ℂ) (tau1 eta) =
            (q eta : ℂ) := by
        simp only [q, dif_pos heta]
        exact Classical.choose_spec
          (virtual_pairing_isInt (hirrVirtual rho)
            (hcoh1.mapsToVirtual eta (generator_mem_closure heta)))
      refine ⟨∑ eta ∈ S1f, coeff eta * (q eta : ℝ), ?_⟩
      simp only [P]
      rw [pairing_finset_sum_right]
      simp only [characterPairing_smul_right]
      push_cast
      apply Finset.sum_congr rfl
      intro eta heta
      have hetaS1 : eta ∈ S1 := by simpa [S1f] using heta
      rw [hq eta hetaS1]
    have hZreal (rho : IrreducibleCharacter G ℂ) :
        ∃ r : ℝ,
          characterPairing (rho : ClassFunction G ℂ) Z = (r : ℂ) := by
      obtain ⟨zY, hzY⟩ :=
        virtual_pairing_isInt (hirrVirtual rho) hYVirtual
      obtain ⟨zXi, hzXi⟩ :=
        virtual_pairing_isInt (hirrVirtual rho) htauXi1Virtual
      obtain ⟨rP, hrP⟩ := hPairPReal rho
      refine ⟨(zY : ℝ) - ((a : ℝ) * (zXi : ℝ) -
        (lam : ℝ) * rP), ?_⟩
      simp only [Z]
      rw [pairing_sub_right, pairing_sub_right,
        characterPairing_smul_right, characterPairing_smul_right,
        hzY, hzXi, hrP]
      push_cast
      ring
    have hZnonneg : 0 ≤ (characterPairing Z Z).re :=
      pairing_self_re_nonneg_of_real_coeff hZreal

    have hZAminus :
        characterPairing Z
          ((a : ℂ) • tau1 xi1 - (lam : ℂ) • P) = 0 := by
      rw [pairing_sub_right, characterPairing_smul_right,
        characterPairing_smul_right, hZorth xi1 hxi1, hZorthP,
        mul_zero, mul_zero, sub_self]
    have hAminusZ :
        characterPairing
          ((a : ℂ) • tau1 xi1 - (lam : ℂ) • P) Z = 0 := by
      rw [characterPairing_comm]
      exact hZAminus
    have hYdecomp :
        Y = ((a : ℂ) • tau1 xi1 - (lam : ℂ) • P) + Z := by
      simp only [Z]
      module
    have hPxi1Right : characterPairing (tau1 xi1) P = 1 := by
      rw [characterPairing_comm, hPpairXi1]
    have hAminusNorm :
        characterPairing
            ((a : ℂ) • tau1 xi1 - (lam : ℂ) • P)
            ((a : ℂ) • tau1 xi1 - (lam : ℂ) • P) =
          (a : ℂ) ^ 2 * characterPairing xi1 xi1 +
            (lam : ℂ) ^ 2 * characterPairing P P -
            2 * (a : ℂ) * (lam : ℂ) := by
      rw [pairing_sub_left, pairing_sub_right, pairing_sub_right]
      simp only [characterPairing_smul_left,
        characterPairing_smul_right]
      rw [hcoh1.isometry xi1 (generator_mem_closure hxi1)
          xi1 (generator_mem_closure hxi1),
        hPpairXi1, hPxi1Right]
      ring
    have hYnormRe :
        (characterPairing Y Y).re =
          (a : ℝ) ^ 2 * (characterPairing xi1 xi1).re +
            (lam : ℝ) ^ 2 * (characterPairing P P).re -
            2 * (a : ℝ) * (lam : ℝ) +
            (characterPairing Z Z).re := by
      rw [hYdecomp,
        pairing_self_add_of_orthogonal _ _ hAminusZ,
        hAminusNorm]
      norm_num [Complex.mul_re, pow_two]

    let chic := ClassFunction.inverseLinear chi
    let S0 : Set (ClassFunction L ℂ) := {beta, chi - chic}
    have hS0Span : AddSubgroup.closure S0 ≤ AddSubgroup.closure S := by
      apply (AddSubgroup.closure_le _).mpr
      intro u hu
      simp only [S0, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with (rfl | rfl)
      · exact hbetaSpan
      · exact (AddSubgroup.closure S).sub_mem
          (generator_mem_closure hchi)
          (generator_mem_closure (hsub.inverse_mem chi hchi))
    have hchiDiffOff :
        chi - chic ∈ ClassFunction.supportedOn (nonidentitySet L) := by
      simpa only [chic] using inverse_sub_supported chi
    have hS0Off : ∀ u ∈ AddSubgroup.closure S0,
        u ∈ ClassFunction.supportedOn (nonidentitySet L) := by
      intro u hu
      induction hu using AddSubgroup.closure_induction with
      | mem u hu =>
          simp only [S0, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
          rcases hu with (rfl | rfl)
          · exact hbetaOff
          · exact hchiDiffOff
      | zero =>
          exact (ClassFunction.supportedOn (R := ℂ)
            (nonidentitySet L)).zero_mem
      | add u v hu hv ihu ihv =>
          exact (ClassFunction.supportedOn (R := ℂ)
            (nonidentitySet L)).add_mem ihu ihv
      | neg u hu ihu =>
          exact (ClassFunction.supportedOn (R := ℂ)
            (nonidentitySet L)).neg_mem ihu
    have hnorm := subcoherent_norm hsub hchi hpsiVirtual
      hchiPsi hinvChiPsi tau
      (fun u hu v hv ↦ hsub.tau_isometry u (hS0Span hu) (hS0Off u hu)
        v (hS0Span hv) (hS0Off v hv))
      (fun u hu ↦ hsub.tau_virtual u (hS0Span hu) (hS0Off u hu))
      rfl hXVirtual hYVirtual hdecomp hXY hYR
    obtain ⟨nX, hnX⟩ := hnorm.1
    have htotal :
        characterPairing X X + characterPairing Y Y =
          characterPairing chi chi +
            (a : ℂ) ^ 2 * characterPairing xi1 xi1 := by
      calc
        characterPairing X X + characterPairing Y Y =
            characterPairing (X - Y) (X - Y) :=
          (pairing_self_sub_of_orthogonal X Y hXY).symm
        _ = characterPairing (tau beta) (tau beta) := by rw [hdecomp]
        _ = characterPairing beta beta :=
          hsub.tau_isometry beta hbetaSpan hbetaOff
            beta hbetaSpan hbetaOff
        _ = characterPairing chi chi + characterPairing psi psi :=
          pairing_self_sub_of_orthogonal chi psi hchiPsi
        _ = _ := by
          simp only [psi, characterPairing_smul_left,
            characterPairing_smul_right]
          ring
    have hgap :
        characterPairing Y Y + (nX : ℂ) =
          (a : ℂ) ^ 2 * characterPairing xi1 xi1 := by
      linear_combination htotal - hnX
    have hgapRe := congrArg Complex.re hgap
    norm_num [Complex.add_re, Complex.mul_re, pow_two] at hgapRe
    rw [hYnormRe] at hgapRe
    have hmaster :
        (lam : ℝ) ^ 2 * (characterPairing P P).re +
            (characterPairing Z Z).re + (nX : ℝ) =
          2 * (a : ℝ) * (lam : ℝ) := by
      nlinarith [hgapRe]
    have haPos : 0 < (a : ℝ) := by
      have hchiPos := source_degree_re_pos hsub hchi
      nlinarith [hdegreeRe, hxi1pos]
    have hlam0 : lam = 0 := by
      by_contra hlam0
      have hlamR : (lam : ℝ) ≠ 0 := by exact_mod_cast hlam0
      have hlamSqPos : 0 < (lam : ℝ) ^ 2 := sq_pos_of_ne_zero hlamR
      have hlamLeSqInt : lam ≤ lam ^ 2 := by
        by_cases hnonpos : lam ≤ 0
        · nlinarith [sq_nonneg lam]
        · have hnonneg : 0 ≤ lam := by omega
          have hone : 0 ≤ lam - 1 := by omega
          nlinarith [mul_nonneg hnonneg hone]
      have hlamLeSq : (lam : ℝ) ≤ (lam : ℝ) ^ 2 := by
        exact_mod_cast hlamLeSqInt
      have hstrict :
          2 * (a : ℝ) * (lam : ℝ) <
            (lam : ℝ) ^ 2 * (characterPairing P P).re := by
        calc
          2 * (a : ℝ) * (lam : ℝ) ≤
              2 * (a : ℝ) * (lam : ℝ) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hlamLeSq (by positivity)
          _ = (lam : ℝ) ^ 2 * (2 * (a : ℝ)) := by ring
          _ < (lam : ℝ) ^ 2 * (characterPairing P P).re :=
            mul_lt_mul_of_pos_left hPnormLarge hlamSqPos
      have hnXnonneg : 0 ≤ (nX : ℝ) := by positivity
      have hreverse :
          (lam : ℝ) ^ 2 * (characterPairing P P).re ≤
            2 * (a : ℝ) * (lam : ℝ) := by
        nlinarith [hmaster, hZnonneg, hnXnonneg]
      exact (not_lt_of_ge hreverse) hstrict
    have hZnormZero : (characterPairing Z Z).re = 0 := by
      have hnXnonneg : 0 ≤ (nX : ℝ) := by positivity
      rw [hlam0] at hmaster
      norm_num at hmaster
      nlinarith [hZnonneg]

    let cZ : IrreducibleCharacter G ℂ → ℝ := fun rho ↦
      Classical.choose (hZreal rho)
    have hcZ (rho : IrreducibleCharacter G ℂ) :
        characterPairing (rho : ClassFunction G ℂ) Z = (cZ rho : ℂ) :=
      Classical.choose_spec (hZreal rho)
    have hnormSum :
        (characterPairing Z Z).re =
          ∑ rho : IrreducibleCharacter G ℂ, cZ rho ^ 2 := by
      rw [pairing_self_eq_sum_irreducible_coeff_sq]
      change Complex.reCLM
          (∑ rho : IrreducibleCharacter G ℂ,
            characterPairing (rho : ClassFunction G ℂ) Z *
              characterPairing (rho : ClassFunction G ℂ) Z) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro rho _
      change (characterPairing (rho : ClassFunction G ℂ) Z *
        characterPairing (rho : ClassFunction G ℂ) Z).re = _
      rw [hcZ rho]
      norm_num [pow_two]
    have hsumZero :
        (∑ rho : IrreducibleCharacter G ℂ, cZ rho ^ 2) = 0 := by
      rw [← hnormSum, hZnormZero]
    have hcoeffZero (rho : IrreducibleCharacter G ℂ) :
        characterPairing (rho : ClassFunction G ℂ) Z = 0 := by
      have hle : cZ rho ^ 2 ≤
          ∑ z : IrreducibleCharacter G ℂ, cZ z ^ 2 :=
        Finset.single_le_sum (fun z _ ↦ sq_nonneg (cZ z))
          (Finset.mem_univ rho)
      have hcrho : cZ rho = 0 := by
        rw [hsumZero] at hle
        nlinarith [sq_nonneg (cZ rho)]
      rw [hcZ rho, hcrho]
      simp
    have hZzero : Z = 0 :=
      classFunction_eq_zero_of_forall_irreducible_pairing_eq_zero Z hcoeffZero
    have : Y - (a : ℂ) • tau1 xi1 = 0 := by
      simpa [Z, hlam0] using hZzero
    exact sub_eq_zero.mp this

  apply extend_coherent_with hsub hS1 hcoh1 hxi1 hchi hchiNot a X hdegree
  · rw [← hYeq]
    exact hXY
  · simpa only [beta, psi, hYeq] using hdecomp

/-- Peterfalvi (5.7).  A subcoherent family all of whose members have the
same degree is coherent.  The pairwise formulation retains the empty-family
case without choosing a distinguished degree. -/
theorem uniform_degree_coherence
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    (hdeg : ∀ chi ∈ S, ∀ psi ∈ S, chi 1 = psi 1) :
    coherent S (nonidentitySet L) tau := by
  classical
  by_cases hS0 : S = ∅
  · subst S
    exact nil_coherent tau (nonidentitySet L)
  obtain ⟨chi1, hchi1⟩ := Set.nonempty_iff_ne_empty.mpr hS0
  obtain ⟨d, hchi1d⟩ :=
    (hsub.source_character chi1 hchi1).exists_nat_degree
  have hdegree (xi : ClassFunction L ℂ) (hxi : xi ∈ S) :
      xi 1 = (d : ℂ) :=
    (hdeg xi hxi chi1 hchi1).trans hchi1d
  obtain ⟨N, hN⟩ :=
    (hsub.source_character chi1 hchi1).isVirtual.exists_nat_norm

  let chi2 := ClassFunction.inverseLinear chi1
  have hchi2 : chi2 ∈ S := hsub.inverse_mem chi1 hchi1
  have hchi2_ne : chi2 ≠ chi1 := hsub.inverse_ne chi1 hchi1
  have hchi2Norm : characterPairing chi2 chi2 = (N : ℂ) := by
    simp only [chi2]
    rw [pairing_inverseLinear, hN]

  let D : ClassFunction L ℂ → ClassFunction G ℂ :=
    fun xi ↦ tau (chi1 - xi)
  have hDiffData (xi : ClassFunction L ℂ) (hxi : xi ∈ S) :
      (chi1 - xi ∈ AddSubgroup.closure S) ∧
      (chi1 - xi ∈ ClassFunction.supportedOn (nonidentitySet L)) ∧
      ClassFunction.IsVirtual (D xi) := by
    have hspan : chi1 - xi ∈ AddSubgroup.closure S :=
      (AddSubgroup.closure S).sub_mem
        (AddSubgroup.subset_closure hchi1)
        (AddSubgroup.subset_closure hxi)
    have hoff := sub_supported_of_one_eq chi1 xi
      ((hdegree chi1 hchi1).trans (hdegree xi hxi).symm)
    exact ⟨hspan, hoff, hsub.tau_virtual _ hspan hoff⟩

  have hDotD (xi eta : ClassFunction L ℂ)
      (hxi : xi ∈ S) (heta : eta ∈ S)
      (hxi1 : xi ≠ chi1) (heta1 : eta ≠ chi1) :
      characterPairing (D xi) (D eta) =
        (N : ℂ) + characterPairing xi eta := by
    simp only [D]
    rw [hsub.tau_isometry _ (hDiffData xi hxi).1
      (hDiffData xi hxi).2.1 _ (hDiffData eta heta).1
      (hDiffData eta heta).2.1]
    have h1eta : characterPairing chi1 eta = 0 :=
      hsub.pairwise_orthogonal hchi1 heta (Ne.symm heta1)
    have hxi1Pair : characterPairing xi chi1 = 0 :=
      hsub.pairwise_orthogonal hxi hchi1 hxi1
    rw [pairing_sub_left, pairing_sub_right, pairing_sub_right,
      hN, h1eta, hxi1Pair]
    ring

  have hDchi2 : D chi2 = ∑ alpha ∈ R chi1, alpha := by
    simpa only [D, chi2] using hsub.tau_inverse_sub chi1 hchi1
  have hRcard : (R chi1).card = N + N := by
    apply Nat.cast_injective (R := ℂ)
    rw [← orthonormal_subset_norm hsub hchi1 (R chi1)
      (fun _ h ↦ h), ← hDchi2,
      hDotD chi2 chi2 hchi2 hchi2 hchi2_ne hchi2_ne,
      hchi2Norm]
    push_cast
    rfl

  let SumR : Finset (ClassFunction G ℂ) → ClassFunction G ℂ :=
    fun E ↦ ∑ alpha ∈ E, alpha
  let Xspec : ClassFunction G ℂ → Prop := fun X ↦
    X ∈ AddSubgroup.closure (↑(R chi1) : Set (ClassFunction G ℂ)) ∧
    ClassFunction.IsVirtual X ∧
    characterPairing X X = (N : ℂ) ∧
    ∃ E : Finset (ClassFunction G ℂ),
      E ⊆ R chi1 ∧ E.card = N ∧ X = SumR E
  let XiSpec : ClassFunction G ℂ → ClassFunction L ℂ → Prop :=
    fun X xi ↦
      X - D xi ∈ AddSubgroup.closure
        (↑(R xi) : Set (ClassFunction G ℂ)) ∧
      characterPairing X (D xi) = (N : ℂ)

  have haveX (xi : ClassFunction L ℂ) (hxi : xi ∈ S)
      (hxi1 : xi ≠ chi1) (hxi2 : xi ≠ chi2) :
      ∃ X, Xspec X ∧ XiSpec X xi := by
    obtain ⟨X, hXspan, hXvirt, Y1, hY1virt,
      hDsplit, hXY1, hY1R⟩ :=
      subcoherent_split hsub hchi1 (hDiffData xi hxi).2.2
    obtain ⟨X1, hX1span, hX1virt, Y, hYvirt,
      hY1split, hX1Y, hYR⟩ :=
      subcoherent_split hsub hxi hY1virt

    have hchi1xi : characterPairing chi1 xi = 0 :=
      hsub.pairwise_orthogonal hchi1 hxi (Ne.symm hxi1)
    have hchi2xi : characterPairing chi2 xi = 0 :=
      hsub.pairwise_orthogonal hchi2 hxi (Ne.symm hxi2)
    have hinvXi_ne_chi1 : ClassFunction.inverseLinear xi ≠ chi1 := by
      intro heq
      apply hxi2
      calc
        xi = ClassFunction.inverseLinear
            (ClassFunction.inverseLinear xi) :=
          (inverseLinear_involutive xi).symm
        _ = ClassFunction.inverseLinear chi1 := congrArg _ heq
        _ = chi2 := rfl
    have hxiChi1 : characterPairing xi chi1 = 0 :=
      hsub.pairwise_orthogonal hxi hchi1 hxi1
    have hinvXiChi1 :
        characterPairing (ClassFunction.inverseLinear xi) chi1 = 0 :=
      hsub.pairwise_orthogonal (hsub.inverse_mem xi hxi) hchi1
        hinvXi_ne_chi1

    have hchi1_ne_invXi : chi1 ≠ ClassFunction.inverseLinear xi :=
      Ne.symm hinvXi_ne_chi1
    have hXorthRxi (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R xi) :
        characterPairing X alpha = 0 :=
      imageClosures_orthogonal hsub hchi1 hxi (Ne.symm hxi1)
        hchi1_ne_invXi hXspan (AddSubgroup.subset_closure halpha)

    let Y2 := X + Y
    have hY2virt : ClassFunction.IsVirtual Y2 := hXvirt.add hYvirt
    have hY2R (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R xi) :
        characterPairing Y2 alpha = 0 := by
      simp only [Y2]
      rw [characterPairing_add_left, hXorthRxi alpha halpha,
        hYR alpha halpha, zero_add]
    have hX1Y2 : characterPairing X1 Y2 = 0 := by
      have horth {V : ClassFunction G ℂ}
          (hV : V ∈ AddSubgroup.closure
            (↑(R xi) : Set (ClassFunction G ℂ))) :
          characterPairing V Y2 = 0 := by
        induction hV using AddSubgroup.closure_induction with
        | mem alpha halpha =>
            rw [characterPairing_comm]
            exact hY2R alpha halpha
        | zero => simp
        | add a b ha hb iha ihb =>
            rw [characterPairing_add_left, iha, ihb, add_zero]
        | neg a ha iha => rw [pairing_neg_left, iha, neg_zero]
      exact horth hX1span
    have hD2split : tau (xi - chi1) = X1 - Y2 := by
      calc
        tau (xi - chi1) = -(D xi) := by
          have harg : xi - chi1 = -(chi1 - xi) := by module
          rw [harg, map_neg]
        _ = X1 - Y2 := by
          rw [hDsplit, hY1split]
          simp only [Y2]
          module

    have hdata1 {u : ClassFunction L ℂ}
        (hu : u ∈ AddSubgroup.closure
          ({chi1 - xi,
            chi1 - ClassFunction.inverseLinear chi1} : Set _)) :=
      pairClosure_data hsub hchi1 hxi
        ((hdegree chi1 hchi1).trans (hdegree xi hxi).symm) hu
    have hnorm1 := subcoherent_norm hsub hchi1
      (hsub.source_character xi hxi).isVirtual hchi1xi
      (by simpa only [chi2] using hchi2xi) tau
      (fun u hu v hv ↦ hsub.tau_isometry u (hdata1 hu).1
        (hdata1 hu).2 v (hdata1 hv).1 (hdata1 hv).2)
      (fun u hu ↦ hsub.tau_virtual u (hdata1 hu).1 (hdata1 hu).2)
      rfl hXvirt hY1virt hDsplit hXY1 hY1R

    have hdata2 {u : ClassFunction L ℂ}
        (hu : u ∈ AddSubgroup.closure
          ({xi - chi1,
            xi - ClassFunction.inverseLinear xi} : Set _)) :=
      pairClosure_data hsub hxi hchi1
        ((hdegree xi hxi).trans (hdegree chi1 hchi1).symm) hu
    have hnorm2 := subcoherent_norm hsub hxi
      (hsub.source_character chi1 hchi1).isVirtual hxiChi1
      hinvXiChi1 tau
      (fun u hu v hv ↦ hsub.tau_isometry u (hdata2 hu).1
        (hdata2 hu).2 v (hdata2 hv).1 (hdata2 hv).2)
      (fun u hu ↦ hsub.tau_virtual u (hdata2 hu).1 (hdata2 hu).2)
      rfl hX1virt hY2virt hD2split hX1Y2 hY2R

    obtain ⟨nX1, hnX1⟩ := hnorm2.1
    obtain ⟨nY, hnY⟩ := hYvirt.exists_nat_norm
    have hY1LE : normLE xi Y1 := by
      refine ⟨nX1 + nY, ?_⟩
      rw [hY1split, pairing_self_sub_of_orthogonal X1 Y hX1Y,
        hnX1, hnY]
      push_cast
      ring
    obtain ⟨hXnorm, hY1norm, E, hER, hXsum⟩ := hnorm1.2 hY1LE
    have hgap : ((nX1 + nY : ℕ) : ℂ) = 0 := by
      rw [hY1split, pairing_self_sub_of_orthogonal X1 Y hX1Y,
        hnX1, hnY] at hY1norm
      push_cast at hY1norm ⊢
      linear_combination hY1norm
    have hgapNat : nX1 + nY = 0 := by
      apply Nat.cast_injective (R := ℂ)
      simpa only [Nat.cast_zero] using hgap
    have hnY0 : nY = 0 := by omega
    have hY0 : Y = 0 := by
      apply virtual_eq_zero_of_pairing_self_eq_zero hYvirt
      rw [hnY, hnY0]
      simp
    have hEcard : E.card = N := by
      apply Nat.cast_injective (R := ℂ)
      rw [← orthonormal_subset_norm hsub hchi1 E hER,
        ← hXsum, hXnorm, hN]
    have hXiSpan : X - D xi ∈ AddSubgroup.closure
        (↑(R xi) : Set (ClassFunction G ℂ)) := by
      have heq : X - D xi = X1 := by
        rw [hDsplit, hY1split, hY0]
        module
      rw [heq]
      exact hX1span
    have hXDi : characterPairing X (D xi) = (N : ℂ) := by
      rw [hDsplit, pairing_sub_right, hXY1, sub_zero, hXnorm, hN]
    refine ⟨X, ?_, hXiSpan, hXDi⟩
    exact ⟨hXspan, hXvirt, hXnorm.trans hN,
      E, hER, hEcard, hXsum⟩

  obtain ⟨X, hXspec, hXD⟩ :
      ∃ X, Xspec X ∧
        ∀ xi ∈ S, xi ≠ chi1 → xi ≠ chi2 →
          characterPairing X (D xi) = (N : ℂ) := by
    by_cases hAway : ∃ xi ∈ S, xi ≠ chi1 ∧ xi ≠ chi2
    · obtain ⟨xi1, hxi1, hxi1_ne, hxi1_ne2⟩ := hAway
      obtain ⟨X, hXsp, hXi1⟩ := haveX xi1 hxi1 hxi1_ne hxi1_ne2
      refine ⟨X, hXsp, ?_⟩
      intro xi hxi hxi_ne hxi_ne2
      by_cases heq : xi = xi1
      · subst xi
        exact hXi1.2
      by_cases heqInv : xi = ClassFunction.inverseLinear xi1
      · have hchi1_ne_invXi1 :
            chi1 ≠ ClassFunction.inverseLinear xi1 := by
          intro h
          apply hxi1_ne2
          calc
            xi1 = ClassFunction.inverseLinear
                (ClassFunction.inverseLinear xi1) :=
              (inverseLinear_involutive xi1).symm
            _ = ClassFunction.inverseLinear chi1 := congrArg _ h.symm
            _ = chi2 := rfl
        have hsumSpan : (∑ alpha ∈ R xi1, alpha) ∈
            AddSubgroup.closure (↑(R xi1) : Set _) := by
          apply AddSubgroup.sum_mem
          intro alpha halpha
          exact AddSubgroup.subset_closure halpha
        have horth :
            characterPairing X (∑ alpha ∈ R xi1, alpha) = 0 :=
          imageClosures_orthogonal hsub hchi1 hxi1 (Ne.symm hxi1_ne)
            hchi1_ne_invXi1 hXsp.1 hsumSpan
        have hDinv : D (ClassFunction.inverseLinear xi1) =
            D xi1 + ∑ alpha ∈ R xi1, alpha := by
          rw [← hsub.tau_inverse_sub xi1 hxi1]
          simp only [D, ← map_add]
          congr 1
          module
        rw [heqInv, hDinv, characterPairing_add_right,
          hXi1.2, horth, add_zero]
      · obtain ⟨X', hX'sp, hXi⟩ := haveX xi hxi hxi_ne hxi_ne2
        let A := X - D xi1
        let B := X' - D xi
        have hAX' : characterPairing A X' = 0 :=
          imageClosures_orthogonal hsub hxi1 hchi1 hxi1_ne
            hxi1_ne2 hXi1.1 hX'sp.1
        have hchi1_ne_invXi :
            chi1 ≠ ClassFunction.inverseLinear xi := by
          intro h
          apply hxi_ne2
          calc
            xi = ClassFunction.inverseLinear
                (ClassFunction.inverseLinear xi) :=
              (inverseLinear_involutive xi).symm
            _ = ClassFunction.inverseLinear chi1 := congrArg _ h.symm
            _ = chi2 := rfl
        have hXB : characterPairing X B = 0 :=
          imageClosures_orthogonal hsub hchi1 hxi (Ne.symm hxi_ne)
            hchi1_ne_invXi hXsp.1 hXi.1
        have hxi1_ne_invXi :
            xi1 ≠ ClassFunction.inverseLinear xi := by
          intro h
          apply heqInv
          calc
            xi = ClassFunction.inverseLinear
                (ClassFunction.inverseLinear xi) :=
              (inverseLinear_involutive xi).symm
            _ = ClassFunction.inverseLinear xi1 := congrArg _ h.symm
        have hAB : characterPairing A B = 0 :=
          imageClosures_orthogonal hsub hxi1 hxi (Ne.symm heq)
            hxi1_ne_invXi hXi1.1 hXi.1
        have hD1B : characterPairing (D xi1) B = 0 := by
          have hdecomp : D xi1 = X - A := by
            simp only [A]
            module
          rw [hdecomp, pairing_sub_left, hXB, hAB, sub_self]
        have hpairXi1Xi : characterPairing xi1 xi = 0 :=
          hsub.pairwise_orthogonal hxi1 hxi (Ne.symm heq)
        have hXX' : characterPairing X X' = (N : ℂ) := by
          have hx : X = A + D xi1 := by
            simp only [A]
            module
          have hx' : X' = D xi + B := by
            simp only [B]
            module
          rw [hx, characterPairing_add_left, hAX', zero_add,
            hx', characterPairing_add_right, hD1B, add_zero,
            hDotD xi1 xi hxi1 hxi hxi1_ne hxi_ne,
            hpairXi1Xi, add_zero]
        have hdiffVirtual : ClassFunction.IsVirtual (X - X') :=
          hXsp.2.1.sub hX'sp.2.1
        have hdiffNorm :
            characterPairing (X - X') (X - X') = 0 := by
          rw [pairing_sub_left, pairing_sub_right, pairing_sub_right,
            hXsp.2.2.1, hXX', characterPairing_comm X' X, hXX',
            hX'sp.2.2.1]
          ring
        have hXXeq : X = X' :=
          sub_eq_zero.mp
            (virtual_eq_zero_of_pairing_self_eq_zero
              hdiffVirtual hdiffNorm)
        rw [hXXeq]
        exact hXi.2
    · have hNle : N ≤ (R chi1).card := by
        rw [hRcard]
        omega
      obtain ⟨E, hER, hEcard⟩ :=
        Finset.exists_subset_card_eq hNle
      let X := SumR E
      have hXspan : X ∈ AddSubgroup.closure
          (↑(R chi1) : Set (ClassFunction G ℂ)) := by
        apply AddSubgroup.sum_mem
        intro alpha halpha
        exact AddSubgroup.subset_closure (hER halpha)
      have hXvirt := virtual_of_mem_imageClosure hsub hchi1 hXspan
      have hXnorm : characterPairing X X = (N : ℂ) := by
        rw [show X = ∑ alpha ∈ E, alpha by rfl,
          orthonormal_subset_norm hsub hchi1 E hER, hEcard]
      refine ⟨X, ⟨hXspan, hXvirt, hXnorm,
        E, hER, hEcard, rfl⟩, ?_⟩
      intro xi hxi hxi1 hxi2
      exact (hAway ⟨xi, hxi, hxi1, hxi2⟩).elim

  have hXDchi2 : characterPairing X (D chi2) = (N : ℂ) := by
    obtain ⟨E, hER, hEcard, hXsum⟩ := hXspec.2.2.2
    rw [hDchi2, hXsum,
      orthonormal_subset_full hsub hchi1 E hER, hEcard]

  refine pivot_coherence hsub hchi1 hXspec.2.1 ?_ ?_
  · intro eta heta heta1
    refine ⟨1, ?_, ?_⟩
    · simpa using hdeg eta heta chi1 hchi1
    · have hpair : characterPairing X (D eta) = (N : ℂ) := by
        by_cases heta2 : eta = chi2
        · subst eta
          exact hXDchi2
        · exact hXD eta heta heta1 heta2
      have hneg : tau (eta - (1 : ℂ) • chi1) = -(D eta) := by
        simp only [one_smul, D]
        have harg : eta - chi1 = -(chi1 - eta) := by module
        rw [harg, map_neg]
      norm_num only [Nat.cast_one, one_smul, one_mul,
        neg_one_mul] at hneg ⊢
      rw [hneg, pairing_neg_left, characterPairing_comm, hpair, hN]
  · exact hXspec.2.2.1.trans hN.symm

/-- Equal-degree pairs lie in a dual-closed coherent subfamily.  This is the
set form of the corollary following Peterfalvi (5.7). -/
theorem pair_degree_coherence
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {phi1 phi2 : ClassFunction L ℂ}
    (hphi1 : phi1 ∈ S) (hphi2 : phi2 ∈ S)
    (hdeg : phi1 1 = phi2 1) :
    ∃ S1 : Set (ClassFunction L ℂ),
      phi1 ∈ S1 ∧ phi2 ∈ S1 ∧ cfConjC_subset S1 S ∧
        coherent S1 (nonidentitySet L) tau := by
  let inv : ClassFunction L ℂ → ClassFunction L ℂ :=
    ClassFunction.inverseLinear (G := L) (k := ℂ)
  let S1 : Set (ClassFunction L ℂ) :=
    {phi1, inv phi1, phi2, inv phi2}
  have hS1S : S1 ⊆ S := by
    intro phi hphi
    simp only [S1, Set.mem_insert_iff, Set.mem_singleton_iff] at hphi
    rcases hphi with rfl | rfl | rfl | rfl
    · exact hphi1
    · exact hsub.inverse_mem phi1 hphi1
    · exact hphi2
    · exact hsub.inverse_mem phi2 hphi2
  have hclosed : cfConjC_closed S1 := by
    intro phi hphi
    simp only [S1, Set.mem_insert_iff, Set.mem_singleton_iff] at hphi ⊢
    rcases hphi with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (inverseLinear_involutive phi1)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (inverseLinear_involutive phi2)))
  have hunif : ∀ chi ∈ S1, ∀ psi ∈ S1, chi 1 = psi 1 := by
    intro chi hchi psi hpsi
    simp only [S1, Set.mem_insert_iff, Set.mem_singleton_iff] at hchi hpsi
    rcases hchi with rfl | rfl | rfl | rfl <;>
      rcases hpsi with rfl | rfl | rfl | rfl <;>
      simp [inv, ClassFunction.inverseLinear_apply, hdeg]
  refine ⟨S1, by simp [S1], by simp [S1], ⟨hS1S, hclosed⟩, ?_⟩
  exact uniform_degree_coherence
    (subset_subcoherent hsub ⟨hS1S, hclosed⟩) hunif

end AbstractCoherence

variable {Gamma : Type} [Group Gamma] [Fintype Gamma]
  {G L K H W W₁ W₂ : Subgroup Gamma}
  {A A₀ : Set Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

attribute [local instance] subgroupCoeTCToAmbient
  subgroupOfCoeTCToAmbient

namespace PrimeDadeHypothesis

/-- Peterfalvi (5.8).  On a coherent prime-Dade family, a reduced column is
sent either to its signed cyclic-TI column or to the negative signed dual
column.  In the latter case the equal-degree ambiguity consists only of the
column and its dual. -/
theorem coherent_prDade_TIred
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (S : Set (ClassFunction L ℂ))
    (k : IrreducibleCharacter W₂ ℂ)
    (tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hS : cfConjC_subset S
      (↑(seqIndD (k := ℂ) (K.subgroupOf L)
        pd.signalizerInKernel ⊥) : Set (ClassFunction L ℂ)))
    (hnr : ∀ phi ∈ S, ClassFunction.inverseLinear phi ≠ phi)
    (hirr : ∃ zeta : IrreducibleCharacter L ℂ,
      (zeta : ClassFunction L ℂ) ∈ S)
    (hkS : pd.prDade_prTI.primeTIRed isoL k ∈ S)
    (hcoh : coherent_with S (nonidentitySet L)
      (Dade pd.prDade_hyp) tau₁) :
    let j := IrreducibleCharacter.dual k
    tau₁ (pd.prDade_prTI.primeTIRed isoL k) =
        (pd.prDade_prTI.primeTISign isoL k : ℂ) •
          ∑ i : IrreducibleCharacter W₁ ℂ,
            isoG.cyclicTIImage (i, k) ∨
      tau₁ (pd.prDade_prTI.primeTIRed isoL k) =
          (-(pd.prDade_prTI.primeTISign isoL k : ℂ)) •
            ∑ i : IrreducibleCharacter W₁ ℂ,
              isoG.cyclicTIImage (i, j) ∧
        ∀ ell : IrreducibleCharacter W₂ ℂ,
          pd.prDade_prTI.primeTIRed isoL ell ∈ S →
          pd.prDade_prTI.primeTIRed isoL ell 1 =
            pd.prDade_prTI.primeTIRed isoL k 1 →
          ell = k ∨ ell = j := by
  classical
  let pti := pd.prDade_prTI
  let mu : IrreducibleCharacter W₂ ℂ → ClassFunction L ℂ :=
    pti.primeTIRed isoL
  let eta (i : IrreducibleCharacter W₁ ℂ)
      (r : IrreducibleCharacter W₂ ℂ) : ClassFunction G ℂ :=
    isoG.cyclicTIImage (i, r)
  let j := IrreducibleCharacter.dual k
  let eps : ℂ := (pti.primeTISign isoL k : ℂ)
  let C : Finset (ClassFunction G ℂ) :=
    pd.primeDadeSignedColumn isoL isoG k k
  let D0 : Finset (ClassFunction G ℂ) :=
    pd.primeDadeSignedColumn isoL isoG k j
  let D : Finset (ClassFunction G ℂ) := D0.image fun alpha ↦ -alpha
  change tau₁ (mu k) = eps • ∑ i, eta i k ∨
    tau₁ (mu k) = (-eps) • ∑ i, eta i j ∧
      ∀ ell, mu ell ∈ S → mu ell 1 = mu k 1 → ell = k ∨ ell = j
  obtain ⟨R, hsub, hRirr, hRred⟩ :=
    pd.prDade_subcoherent isoL isoG S hS hnr
  have hself : cfConjC_subset S S := ⟨Set.Subset.rfl, hsub.inverse_mem⟩
  obtain ⟨E, hER, hphi⟩ :=
    mem_coherent_sum_subseq hsub hself hcoh hkS
  have hRk : R (mu k) = C ∪ D := by
    simpa [mu, C, D, D0, j,
      PrimeDadeHypothesis.primeDadeReducedImageFamily] using hRred k
  have hECU : E ⊆ C ∪ D := by
    intro alpha halpha
    have ha := hER halpha
    rw [hRk] at ha
    exact ha
  have hk0 : k ≠ IrreducibleCharacter.trivial := by
    intro hk
    subst k
    apply hnr (mu IrreducibleCharacter.trivial) hkS
    change ClassFunction.inverseLinear
        (pti.primeTIRed isoL IrreducibleCharacter.trivial) =
      pti.primeTIRed isoL IrreducibleCharacter.trivial
    rw [pti.prTIred_aut isoL,
      IrreducibleCharacter.dual_trivial]
  have hjk : j ≠ k := by
    intro hjk
    apply hnr (mu k) hkS
    change ClassFunction.inverseLinear (pti.primeTIRed isoL k) =
      pti.primeTIRed isoL k
    rw [pti.prTIred_aut isoL]
    exact congrArg (pti.primeTIRed isoL) (by simpa [j] using hjk)
  have hkj : k ≠ j := Ne.symm hjk
  have hj0 : j ≠ IrreducibleCharacter.trivial := by
    intro hj0
    apply hk0
    calc
      k = IrreducibleCharacter.dual j :=
        (IrreducibleCharacter.dual_dual k).symm
      _ = IrreducibleCharacter.trivial := by
        rw [hj0, IrreducibleCharacter.dual_trivial]
  have heps0 : eps ≠ 0 :=
    Int.cast_ne_zero.mpr
      (isSign_ne_zero (pti.primeTISign_isSign isoL k))
  have hmuSpan : mu k ∈ AddSubgroup.closure S :=
    AddSubgroup.subset_closure hkS
  have hEnorm :
      characterPairing (∑ alpha ∈ E, alpha) (∑ alpha ∈ E, alpha) =
        (E.card : ℂ) := orthonormal_subset_norm hsub hkS E hER
  have hEcardCast : (E.card : ℂ) = (Nat.card W₁ : ℂ) := by
    rw [← hEnorm, ← hphi,
      hcoh.isometry (mu k) hmuSpan (mu k) hmuSpan]
    exact pti.cfnorm_prTIred isoL k
  have hEcard : E.card = Nat.card W₁ := by
    exact_mod_cast hEcardCast
  have hCcard : C.card = Nat.card W₁ := by
    simpa [C] using pd.card_primeDadeSignedColumn isoL isoG k k
  have hD0card : D0.card = Nat.card W₁ := by
    simpa [D0, j] using pd.card_primeDadeSignedColumn isoL isoG k j
  have hDcard : D.card = Nat.card W₁ := by
    simp only [D]
    rw [Finset.card_image_iff.mpr]
    · exact hD0card
    · exact Set.injOn_of_injective neg_injective

  obtain ⟨zeta, hzetaS⟩ := hirr
  obtain ⟨Ezeta, hEzetaR, hzetaSum⟩ :=
    mem_coherent_sum_subseq hsub hself hcoh hzetaS
  have hzetaPair (w : IrreducibleCharacter W ℂ) :
      characterPairing (tau₁ (zeta : ClassFunction L ℂ))
        (isoG.linearMap (w : ClassFunction W ℂ)) = 0 := by
    rw [hzetaSum, pairing_finset_sum_left]
    apply Finset.sum_eq_zero
    intro alpha halpha
    exact hRirr (zeta : ClassFunction L ℂ) hzetaS zeta.property
      w alpha (hEzetaR halpha)
  have hzetaVanish : Set.EqOn
      (fun w : W ↦ tau₁ (zeta : ClassFunction L ℂ)
        ⟨w, pd.prDade_cycTI.le_group w.property⟩)
      0 (cyclicTISetInW W W₁ W₂) :=
    isoG.orthogonal_vanish (tau₁ (zeta : ClassFunction L ℂ)) hzetaPair
  obtain ⟨dz, hdz⟩ :=
    (hsub.source_character (zeta : ClassFunction L ℂ) hzetaS).exists_nat_degree
  obtain ⟨dm, hdm⟩ :=
    (hsub.source_character (mu k) hkS).exists_nat_degree
  have hdz0 : (dz : ℂ) ≠ 0 := by
    rw [← hdz]
    exact hsub.degree_ne_zero (zeta : ClassFunction L ℂ) hzetaS
  let zeta1 : ClassFunction L ℂ :=
    (dz : ℂ) • mu k - (dm : ℂ) • (zeta : ClassFunction L ℂ)
  have hzeta1Span : zeta1 ∈ AddSubgroup.closure S := by
    apply (AddSubgroup.closure S).sub_mem
    · rw [Nat.cast_smul_eq_nsmul]
      exact (AddSubgroup.closure S).nsmul_mem hmuSpan dz
    · rw [Nat.cast_smul_eq_nsmul]
      exact (AddSubgroup.closure S).nsmul_mem
        (AddSubgroup.subset_closure hzetaS) dm
  have hzeta1Off : zeta1 ∈
      ClassFunction.supportedOn (nonidentitySet L) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hx1 : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp [zeta1, hdz, hdm, mul_comm]
  have hzetaSeq : (zeta : ClassFunction L ℂ) ∈
      seqIndD (k := ℂ) (K.subgroupOf L) pd.signalizerInKernel ⊥ :=
    hS.1 hzetaS
  obtain ⟨theta, htheta, hzetaEq⟩ := seqIndP.mp hzetaSeq
  have hzetaSupport : (zeta : ClassFunction L ℂ) ∈
      ClassFunction.supportedOn (primeDadeSupport L A) := by
    rw [hzetaEq]
    exact pd.prDade_Ind_irr_on theta (mem_Iirr_kerD.mp htheta).2
  have hmuSupport : mu k ∈
      ClassFunction.supportedOn (primeDadeSupport L A) := by
    simpa [mu] using pd.prDade_TIred_on isoL k hk0
  have hzeta1Support : zeta1 ∈
      ClassFunction.supportedOn (primeDadeSupport L A) := by
    simpa [zeta1] using
      (ClassFunction.supportedOn (R := ℂ) (primeDadeSupport L A)).sub_mem
        ((ClassFunction.supportedOn (R := ℂ) (primeDadeSupport L A)).smul_mem
          (dz : ℂ) hmuSupport)
        ((ClassFunction.supportedOn (R := ℂ) (primeDadeSupport L A)).smul_mem
          (dm : ℂ) hzetaSupport)
  have hzeta1Agree : tau₁ zeta1 = Dade pd.prDade_hyp zeta1 :=
    hcoh.agrees zeta1 hzeta1Span hzeta1Off
  have hphiVanish : Set.EqOn
      (fun w : W ↦ tau₁ (mu k)
        ⟨w, pd.prDade_cycTI.le_group w.property⟩)
      0 (cyclicTISetInW W W₁ W₂) := by
    intro x hxV
    let xG : G := ⟨(x : Gamma), pd.prDade_cycTI.le_group x.property⟩
    let xL : L := ⟨(x : Gamma), pti.directProduct_le_group x.property⟩
    have hxAmbient : (x : Gamma) ∈ cyclicTISet W W₁ W₂ := by
      simpa [cyclicTISetInW] using hxV
    have hxK : (x : Gamma) ∉ K := pd.prDade_supp_disjoint hxAmbient
    have hxOne : (x : Gamma) ≠ 1 := by
      intro hx1
      apply hxK
      simpa [hx1] using K.one_mem
    have hxA : (x : Gamma) ∉ A := by
      intro hxA
      exact hxK (pd.prDade_def.set_le_kernel_diff_one hxA).1
    have hxNotSupport : xL ∉ primeDadeSupport L A := by
      rw [mem_primeDadeSupport, not_or]
      exact ⟨hxOne, hxA⟩
    have hzeta1x : zeta1 xL = 0 :=
      ClassFunction.eq_zero_of_mem_supportedOn hzeta1Support hxNotSupport
    have hxA0 : (x : Gamma) ∈ A₀ := by
      rw [pd.prDade_def.dadeSet_eq]
      refine Or.inr ⟨(x : Gamma), hxAmbient, 1, L.one_mem, ?_⟩
      simp
    have hDadeX : Dade pd.prDade_hyp zeta1 xG = 0 := by
      have h := Dade_id pd.prDade_hyp zeta1 hxA0
      simpa [xG, xL, hzeta1x] using h
    have htauZeta1X : tau₁ zeta1 xG = 0 := by
      rw [hzeta1Agree, hDadeX]
    have htauZetaX : tau₁ (zeta : ClassFunction L ℂ) xG = 0 := by
      simpa [xG] using hzetaVanish hxV
    change tau₁ (mu k) xG = 0
    have hexpand := htauZeta1X
    simp only [zeta1, map_sub, map_smul, ClassFunction.sub_apply,
      ClassFunction.smul_apply, smul_eq_mul, htauZetaX, mul_zero,
      sub_zero] at hexpand
    exact (mul_eq_zero.mp hexpand).resolve_left hdz0

  let i0 : IrreducibleCharacter W₁ ℂ := IrreducibleCharacter.trivial
  let c (i : IrreducibleCharacter W₁ ℂ) : ClassFunction G ℂ :=
    eps • eta i k
  let d (i : IrreducibleCharacter W₁ ℂ) : ClassFunction G ℂ :=
    -(eps • eta i j)
  have hpairTrivial (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing (tau₁ (mu k))
        (eta i IrreducibleCharacter.trivial) = 0 := by
    rw [hphi, pairing_finset_sum_left]
    apply Finset.sum_eq_zero
    intro alpha halpha
    have ha := hECU halpha
    rw [Finset.mem_union] at ha
    rcases ha with haC | haD
    · obtain ⟨q, rfl⟩ :=
        (pd.mem_primeDadeSignedColumn isoL isoG k k _).1
          (by simpa [C] using haC)
      rw [characterPairing_smul_left,
        isoG.characterPairing_cyclicTIImage,
        if_neg (by intro h; exact hk0 (congrArg Prod.snd h)), mul_zero]
    · obtain ⟨beta, hbeta, rfl⟩ :=
            Finset.mem_image.mp (by
              change alpha ∈ D0.image
                (fun beta : ClassFunction G ℂ ↦ -beta) at haD
              exact haD)
      obtain ⟨q, rfl⟩ :=
        (pd.mem_primeDadeSignedColumn isoL isoG k j _).1
          (by simpa [D0] using hbeta)
      rw [pairing_neg_left, characterPairing_smul_left,
        isoG.characterPairing_cyclicTIImage,
        if_neg (by intro h; exact hj0 (congrArg Prod.snd h)),
        mul_zero, neg_zero]
  have hrow (r : IrreducibleCharacter W₂ ℂ)
      (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing (tau₁ (mu k)) (eta i r) =
        characterPairing (tau₁ (mu k)) (eta i0 r) := by
    have hx := isoG.pairing_exchange hphiVanish
      i i0 r IrreducibleCharacter.trivial
    change characterPairing (tau₁ (mu k)) (eta i r) +
        characterPairing (tau₁ (mu k))
          (eta i0 IrreducibleCharacter.trivial) =
      characterPairing (tau₁ (mu k))
          (eta i IrreducibleCharacter.trivial) +
        characterPairing (tau₁ (mu k)) (eta i0 r) at hx
    rw [hpairTrivial i, hpairTrivial i0, add_zero, zero_add] at hx
    exact hx
  have hpairK (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing (tau₁ (mu k)) (eta i k) =
        if c i ∈ E then eps else 0 := by
    rw [hphi, pairing_finset_sum_left]
    by_cases hci : c i ∈ E
    · rw [if_pos hci, Finset.sum_eq_single (c i)]
      · simp only [c]
        rw [characterPairing_smul_left,
          isoG.characterPairing_cyclicTIImage, if_pos rfl, mul_one]
      · intro alpha halpha hne
        have ha := hECU halpha
        rw [Finset.mem_union] at ha
        rcases ha with haC | haD
        · obtain ⟨q, rfl⟩ :=
            (pd.mem_primeDadeSignedColumn isoL isoG k k _).1
              (by simpa [C] using haC)
          have hqi : q ≠ i := by
            intro h
            subst q
            exact hne (by rfl)
          rw [characterPairing_smul_left,
            isoG.characterPairing_cyclicTIImage,
            if_neg (by intro h; exact hqi (congrArg Prod.fst h)), mul_zero]
        · obtain ⟨beta, hbeta, rfl⟩ :=
            Finset.mem_image.mp (by
              change alpha ∈ D0.image
                (fun beta : ClassFunction G ℂ ↦ -beta) at haD
              exact haD)
          obtain ⟨q, rfl⟩ :=
            (pd.mem_primeDadeSignedColumn isoL isoG k j _).1
              (by simpa [D0] using hbeta)
          rw [pairing_neg_left, characterPairing_smul_left,
            isoG.characterPairing_cyclicTIImage,
            if_neg (by intro h; exact hjk (congrArg Prod.snd h)),
            mul_zero, neg_zero]
      · intro hnot
        exfalso
        exact hnot (by simpa only [c] using hci)
    · simp only [hci, if_false]
      apply Finset.sum_eq_zero
      intro alpha halpha
      have ha := hECU halpha
      rw [Finset.mem_union] at ha
      rcases ha with haC | haD
      · obtain ⟨q, rfl⟩ :=
          (pd.mem_primeDadeSignedColumn isoL isoG k k _).1
            (by simpa [C] using haC)
        have hqi : q ≠ i := by
          intro h
          subst q
          apply hci
          simpa [c, eps, eta] using halpha
        rw [characterPairing_smul_left,
          isoG.characterPairing_cyclicTIImage,
          if_neg (by intro h; exact hqi (congrArg Prod.fst h)), mul_zero]
      · obtain ⟨beta, hbeta, rfl⟩ :=
            Finset.mem_image.mp (by
              change alpha ∈ D0.image
                (fun beta : ClassFunction G ℂ ↦ -beta) at haD
              exact haD)
        obtain ⟨q, rfl⟩ :=
          (pd.mem_primeDadeSignedColumn isoL isoG k j _).1
            (by simpa [D0] using hbeta)
        rw [pairing_neg_left, characterPairing_smul_left,
          isoG.characterPairing_cyclicTIImage,
          if_neg (by intro h; exact hjk (congrArg Prod.snd h)),
          mul_zero, neg_zero]
  have hpairJ (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing (tau₁ (mu k)) (eta i j) =
        if d i ∈ E then -eps else 0 := by
    rw [hphi, pairing_finset_sum_left]
    by_cases hdi : d i ∈ E
    · rw [if_pos hdi, Finset.sum_eq_single (d i)]
      · simp only [d]
        rw [pairing_neg_left, characterPairing_smul_left,
          isoG.characterPairing_cyclicTIImage, if_pos rfl, mul_one]
      · intro alpha halpha hne
        have ha := hECU halpha
        rw [Finset.mem_union] at ha
        rcases ha with haC | haD
        · obtain ⟨q, rfl⟩ :=
            (pd.mem_primeDadeSignedColumn isoL isoG k k _).1
              (by simpa [C] using haC)
          rw [characterPairing_smul_left,
            isoG.characterPairing_cyclicTIImage,
            if_neg (by intro h; exact hkj (congrArg Prod.snd h)), mul_zero]
        · obtain ⟨beta, hbeta, rfl⟩ :=
            Finset.mem_image.mp (by
              change alpha ∈ D0.image
                (fun beta : ClassFunction G ℂ ↦ -beta) at haD
              exact haD)
          obtain ⟨q, rfl⟩ :=
            (pd.mem_primeDadeSignedColumn isoL isoG k j _).1
              (by simpa [D0] using hbeta)
          have hqi : q ≠ i := by
            intro h
            subst q
            exact hne (by rfl)
          rw [pairing_neg_left, characterPairing_smul_left,
            isoG.characterPairing_cyclicTIImage,
            if_neg (by intro h; exact hqi (congrArg Prod.fst h)),
            mul_zero, neg_zero]
      · intro hnot
        exfalso
        exact hnot (by simpa only [d] using hdi)
    · simp only [hdi, if_false]
      apply Finset.sum_eq_zero
      intro alpha halpha
      have ha := hECU halpha
      rw [Finset.mem_union] at ha
      rcases ha with haC | haD
      · obtain ⟨q, rfl⟩ :=
          (pd.mem_primeDadeSignedColumn isoL isoG k k _).1
            (by simpa [C] using haC)
        rw [characterPairing_smul_left,
          isoG.characterPairing_cyclicTIImage,
          if_neg (by intro h; exact hkj (congrArg Prod.snd h)), mul_zero]
      · obtain ⟨beta, hbeta, rfl⟩ :=
            Finset.mem_image.mp (by
              change alpha ∈ D0.image
                (fun beta : ClassFunction G ℂ ↦ -beta) at haD
              exact haD)
        obtain ⟨q, rfl⟩ :=
          (pd.mem_primeDadeSignedColumn isoL isoG k j _).1
            (by simpa [D0] using hbeta)
        have hqi : q ≠ i := by
          intro h
          subst q
          apply hdi
          simpa [d, eps, eta] using halpha
        rw [pairing_neg_left, characterPairing_smul_left,
          isoG.characterPairing_cyclicTIImage,
          if_neg (by intro h; exact hqi (congrArg Prod.fst h)),
          mul_zero, neg_zero]

  have hcConst (i : IrreducibleCharacter W₁ ℂ) : c i ∈ E ↔ c i0 ∈ E := by
    have hp := hrow k i
    rw [hpairK i, hpairK i0] at hp
    constructor
    · intro hi
      by_contra h0
      rw [if_pos hi, if_neg h0] at hp
      exact heps0 hp
    · intro h0
      by_contra hi
      rw [if_neg hi, if_pos h0] at hp
      exact heps0 hp.symm
  have hdConst (i : IrreducibleCharacter W₁ ℂ) : d i ∈ E ↔ d i0 ∈ E := by
    have hp := hrow j i
    rw [hpairJ i, hpairJ i0] at hp
    have hneps0 : -eps ≠ 0 := neg_ne_zero.mpr heps0
    constructor
    · intro hi
      by_contra h0
      rw [if_pos hi, if_neg h0] at hp
      exact hneps0 hp
    · intro h0
      by_contra hi
      rw [if_neg hi, if_pos h0] at hp
      exact hneps0 hp.symm
  have hEne : E.Nonempty :=
    Finset.card_pos.mp (by rw [hEcard]; exact Nat.card_pos)
  obtain ⟨alpha, halphaE⟩ := hEne
  have halphaU := hECU halphaE
  rw [Finset.mem_union] at halphaU
  rcases halphaU with halphaC | halphaD
  · obtain ⟨q, hq⟩ :=
      (pd.mem_primeDadeSignedColumn isoL isoG k k alpha).1
        (by simpa [C] using halphaC)
    have hcqE : c q ∈ E := by
      have h := halphaE
      rw [hq] at h
      simpa [c, eps, eta] using h
    have hc0E : c i0 ∈ E := (hcConst q).1 hcqE
    have hCE : C ⊆ E := by
      intro beta hbeta
      obtain ⟨r, rfl⟩ :=
        (pd.mem_primeDadeSignedColumn isoL isoG k k beta).1
          (by simpa [C] using hbeta)
      simpa [c, eps, eta] using (hcConst r).2 hc0E
    have hCEq : C = E :=
      Finset.eq_of_subset_of_card_le hCE (by rw [hEcard, hCcard])
    left
    rw [hphi, ← hCEq]
    simpa [C, eps, eta] using
      pd.sum_primeDadeSignedColumn isoL isoG k k
  · obtain ⟨beta, hbetaD0, hbetaEq⟩ :=
      Finset.mem_image.mp (by
        change alpha ∈ D0.image
          (fun beta : ClassFunction G ℂ ↦ -beta) at halphaD
        exact halphaD)
    obtain ⟨q, hq⟩ :=
      (pd.mem_primeDadeSignedColumn isoL isoG k j beta).1
        (by simpa [D0] using hbetaD0)
    have hdqE : d q ∈ E := by
      have h := halphaE
      rw [← hbetaEq, hq] at h
      simpa [d, eps, eta] using h
    have hd0E : d i0 ∈ E := (hdConst q).1 hdqE
    have hDE : D ⊆ E := by
      intro gamma hgamma
      obtain ⟨beta, hbeta, rfl⟩ :=
        Finset.mem_image.mp (by
          change gamma ∈ D0.image
            (fun beta : ClassFunction G ℂ ↦ -beta) at hgamma
          exact hgamma)
      obtain ⟨r, rfl⟩ :=
        (pd.mem_primeDadeSignedColumn isoL isoG k j beta).1
          (by simpa [D0] using hbeta)
      simpa [d, eps, eta] using (hdConst r).2 hd0E
    have hDEq : D = E :=
      Finset.eq_of_subset_of_card_le hDE (by rw [hEcard, hDcard])
    have hphiNeg : tau₁ (mu k) = (-eps) • ∑ i, eta i j := by
      rw [hphi, ← hDEq]
      calc
        (∑ gamma ∈ D, gamma) = -(∑ gamma ∈ D0, gamma) := by
          simp only [D]
          rw [Finset.sum_image
            (Set.injOn_of_injective neg_injective)]
          rw [Finset.sum_neg_distrib]
        _ = (-eps) • ∑ i, eta i j := by
          rw [show ∑ gamma ∈ D0, gamma = eps • ∑ i, eta i j by
            simpa [D0, eps, eta] using
              pd.sum_primeDadeSignedColumn isoL isoG k j]
          module
    right
    refine ⟨hphiNeg, ?_⟩
    intro ell hellS hdeg
    have hell0 : ell ≠ IrreducibleCharacter.trivial := by
      intro hell
      subst ell
      apply hnr (mu IrreducibleCharacter.trivial) hellS
      change ClassFunction.inverseLinear
          (pti.primeTIRed isoL IrreducibleCharacter.trivial) =
        pti.primeTIRed isoL IrreducibleCharacter.trivial
      rw [pti.prTIred_aut isoL,
        IrreducibleCharacter.dual_trivial]
    by_contra hnot
    push_neg at hnot
    rcases hnot with ⟨hellk, hellj⟩
    have hkDualEll : k ≠ IrreducibleCharacter.dual ell := by
      intro hkdual
      apply hellj
      calc
        ell = IrreducibleCharacter.dual
            (IrreducibleCharacter.dual ell) :=
          (IrreducibleCharacter.dual_dual ell).symm
        _ = IrreducibleCharacter.dual k := by rw [← hkdual]
        _ = j := rfl

    let T := pti.uniform_prTIred_seq isoL k
    obtain ⟨_, huniform⟩ :=
      pd.uniform_prTIred_coherent isoL isoG k hk0
    obtain ⟨tau₂, htau₂, _, htau₂Agree⟩ := huniform
    have hkT : mu k ∈ T := by
      exact ⟨k, ⟨hk0, rfl⟩, rfl⟩
    have hellT : mu ell ∈ T := by
      exact ⟨ell, ⟨hell0, hdeg⟩, rfl⟩
    have hdiffS : mu k - mu ell ∈ AddSubgroup.closure S :=
      (AddSubgroup.closure S).sub_mem hmuSpan
        (AddSubgroup.subset_closure hellS)
    have hdiffT : mu k - mu ell ∈ AddSubgroup.closure T :=
      (AddSubgroup.closure T).sub_mem
        (AddSubgroup.subset_closure hkT)
        (AddSubgroup.subset_closure hellT)
    have hdiffOff : mu k - mu ell ∈
        ClassFunction.supportedOn (nonidentitySet L) :=
      sub_supported_of_one_eq (mu k) (mu ell) hdeg.symm
    have hdiffEq :
        tau₁ (mu k) - tau₁ (mu ell) =
          tau₂ (mu k) - tau₂ (mu ell) := by
      rw [← map_sub, ← map_sub,
        hcoh.agrees (mu k - mu ell) hdiffS hdiffOff,
        htau₂Agree (mu k - mu ell) hdiffT hdiffOff]

    obtain ⟨Eell, hEellR, hellSum⟩ :=
      mem_coherent_sum_subseq hsub hself hcoh hellS
    have hRell : R (mu ell) =
        pd.primeDadeReducedImageFamily isoL isoG ell := by
      simpa [mu] using hRred ell
    have hpairEll :
        characterPairing (tau₁ (mu ell)) (eta i0 k) = 0 := by
      rw [hellSum, pairing_finset_sum_left]
      apply Finset.sum_eq_zero
      intro alpha halpha
      have haR := hEellR halpha
      rw [hRell, PrimeDadeHypothesis.primeDadeReducedImageFamily,
        Finset.mem_union] at haR
      rcases haR with ha | ha
      · obtain ⟨q, rfl⟩ :=
          (pd.mem_primeDadeSignedColumn isoL isoG ell ell _).1 ha
        rw [characterPairing_smul_left,
          isoG.characterPairing_cyclicTIImage,
          if_neg (by intro h; exact hellk (congrArg Prod.snd h)),
          mul_zero]
      · obtain ⟨beta, hbeta, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨q, rfl⟩ :=
          (pd.mem_primeDadeSignedColumn isoL isoG ell
            (IrreducibleCharacter.dual ell) _).1 hbeta
        rw [pairing_neg_left, characterPairing_smul_left,
          isoG.characterPairing_cyclicTIImage,
          if_neg (by
            intro h
            exact hkDualEll (congrArg Prod.snd h).symm),
          mul_zero, neg_zero]
    have hpairPhi :
        characterPairing (tau₁ (mu k)) (eta i0 k) = 0 := by
      rw [hphiNeg, characterPairing_smul_left,
        pairing_finset_sum_left]
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro i _
      simp only [eta]
      rw [isoG.characterPairing_cyclicTIImage,
        if_neg (by intro h; exact hjk (congrArg Prod.snd h))]
    have htau₂k : tau₂ (mu k) = eps • ∑ i, eta i k := by
      simpa [mu, eps, eta] using htau₂ k
    have htau₂ell : tau₂ (mu ell) = eps • ∑ i, eta i ell := by
      simpa [mu, eps, eta] using htau₂ ell
    have hpairTau₂k :
        characterPairing (tau₂ (mu k)) (eta i0 k) = eps := by
      rw [htau₂k, characterPairing_smul_left,
        pairing_finset_sum_left, Finset.sum_eq_single i0]
      · simp only [eta]
        rw [isoG.characterPairing_cyclicTIImage, if_pos rfl, mul_one]
      · intro i _ hi
        simp only [eta]
        rw [isoG.characterPairing_cyclicTIImage,
          if_neg (by intro h; exact hi (congrArg Prod.fst h))]
      · simp
    have hpairTau₂ell :
        characterPairing (tau₂ (mu ell)) (eta i0 k) = 0 := by
      rw [htau₂ell, characterPairing_smul_left,
        pairing_finset_sum_left]
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro i _
      simp only [eta]
      rw [isoG.characterPairing_cyclicTIImage,
        if_neg (by intro h; exact hellk (congrArg Prod.snd h))]
    have hp := congrArg
      (fun f : ClassFunction G ℂ ↦ characterPairing f (eta i0 k))
      hdiffEq
    rw [pairing_sub_left, pairing_sub_left, hpairPhi, hpairEll,
      hpairTau₂k, hpairTau₂ell, sub_zero, sub_zero] at hp
    exact heps0 hp.symm

end PrimeDadeHypothesis

end

end Submission.OddOrder.PF
