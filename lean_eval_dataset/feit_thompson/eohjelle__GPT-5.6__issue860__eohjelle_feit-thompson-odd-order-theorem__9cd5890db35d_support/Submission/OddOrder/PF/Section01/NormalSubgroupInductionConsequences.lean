import Submission.OddOrder.PF.Section01.BrauerPermutation
import Submission.OddOrder.PF.Section01.NormalSubgroupInduction

/-!
# Consequences of normal-subgroup character induction

This file continues the port of `PFsection1.v` immediately after Peterfalvi
1.5(c).  It covers the three source consequences
`not_cfclass_Ind_ortho`, `cfclass_Ind_irrP`, and `card_imset_Ind_irr`, then
Peterfalvi 1.5(d), `scaled_cfResInd_sum_cfclass`, and 1.5(e),
`odd_induced_orthogonal`.

The bundled action below lets the source's conjugacy classes of irreducible
characters be represented directly as `MulAction.orbit`s.  In particular,
the cardinality formula is proved by identifying every fiber of induction
with one such orbit and computing its size from the inertia subgroup.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u v

namespace IrreducibleCharacter

variable {G : Type u} {k : Type v} [Group G] [Field k]

/-- Ambient conjugation is an action on the irreducible characters of a
normal subgroup. -/
instance normalConjugationMulAction (H : Subgroup G) [H.Normal] :
    MulAction G (IrreducibleCharacter H k) where
  smul x chi := chi.normalConjugate H x
  one_smul chi := by
    apply Subtype.ext
    exact ClassFunction.normalConjugate_one H (chi : ClassFunction H k)
  mul_smul x y chi := by
    apply Subtype.ext
    exact ClassFunction.normalConjugate_mul H x y (chi : ClassFunction H k)

/-- The stabilizer of a bundled irreducible character is the inertia
subgroup of its underlying class function. -/
theorem stabilizer_eq_inertia (H : Subgroup G) [H.Normal]
    (chi : IrreducibleCharacter H k) :
    MulAction.stabilizer G chi =
      ClassFunction.inertia H (chi : ClassFunction H k) := by
  ext x
  rw [MulAction.mem_stabilizer_iff, ClassFunction.mem_inertia_iff]
  constructor
  · exact fun h => congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

end IrreducibleCharacter

namespace ClassFunction

variable {G : Type u} {k : Type v} [Group G] [Field k] [Fintype G]

/-- The relative inertia index is positive. -/
theorem inertiaIndex_pos (H : Subgroup G) [H.Normal] [Fintype H]
    (f : ClassFunction H k) : 0 < inertiaIndex H f := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_dvd_of_le (le_inertia H f))
  · exact Nat.card_pos

/-- Two induced irreducible characters are equal exactly when one inducing
character is an ambient conjugate of the other. -/
theorem cfclass_Ind_eq_iff [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Invertible (Nat.card H : k)]
    (chi₁ chi₂ : IrreducibleCharacter H k) :
    induce H (chi₁ : ClassFunction H k) =
        induce H (chi₂ : ClassFunction H k) ↔
      ∃ x : G, normalConjugate H x (chi₁ : ClassFunction H k) =
        (chi₂ : ClassFunction H k) := by
  constructor
  · intro hind
    rcases cfclass_Ind_cases H chi₁ chi₂ with horbit | hortho
    · exact horbit.1
    · exfalso
      have hnorm := cfnorm_Ind_irr H chi₁
      have hzero :
          characterPairing (induce H (chi₁ : ClassFunction H k))
            (induce H (chi₁ : ClassFunction H k)) = 0 := by
        calc
          _ = characterPairing (induce H (chi₁ : ClassFunction H k))
              (induce H (chi₂ : ClassFunction H k)) :=
            congrArg
              (characterPairing (induce H (chi₁ : ClassFunction H k))) hind
          _ = 0 := hortho.2
      have hcast : (inertiaIndex H (chi₁ : ClassFunction H k) : k) ≠ 0 :=
        Nat.cast_ne_zero.mpr (inertiaIndex_pos H _).ne'
      exact hcast (hnorm.symm.trans hzero)
  · rintro ⟨x, hx⟩
    exact (induce_normalConjugate H x (chi₁ : ClassFunction H k)).symm.trans
      (congrArg (induce H) hx)

/-- Source `cfclass_Ind_irrP`: equality of inductions is equivalent to
membership in the ambient conjugacy orbit. -/
theorem cfclass_Ind_irrP [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Invertible (Nat.card H : k)]
    (chi₁ chi₂ : IrreducibleCharacter H k) :
    chi₁ ∈ MulAction.orbit G chi₂ ↔
      induce H (chi₁ : ClassFunction H k) =
        induce H (chi₂ : ClassFunction H k) := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨x, hx⟩
    apply Eq.symm
    apply (cfclass_Ind_eq_iff H chi₂ chi₁).2
    refine ⟨x, ?_⟩
    exact congrArg Subtype.val hx
  · intro hind
    obtain ⟨x, hx⟩ := (cfclass_Ind_eq_iff H chi₂ chi₁).1 hind.symm
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

/-- Source `not_cfclass_Ind_ortho`: irreducible characters in distinct
ambient conjugacy orbits induce to orthogonal class functions. -/
theorem not_cfclass_Ind_ortho [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Invertible (Nat.card H : k)]
    (chi₁ chi₂ : IrreducibleCharacter H k)
    (hnot : chi₁ ∉ MulAction.orbit G chi₂) :
    characterPairing (induce H (chi₁ : ClassFunction H k))
      (induce H (chi₂ : ClassFunction H k)) = 0 := by
  have hnot' : ¬ ∃ x : G,
      normalConjugate H x (chi₁ : ClassFunction H k) =
        (chi₂ : ClassFunction H k) := by
    rintro ⟨x, hx⟩
    apply hnot
    rw [MulAction.mem_orbit_iff]
    refine ⟨x⁻¹, ?_⟩
    apply Subtype.ext
    change normalConjugate H x⁻¹ (chi₂ : ClassFunction H k) =
      (chi₁ : ClassFunction H k)
    rw [← hx, normalConjugate_inv_self]
  rcases cfclass_Ind_cases H chi₁ chi₂ with horbit | hortho
  · exact (hnot' horbit.1).elim
  · exact hortho.2

/-- The value at the identity of induction is the subgroup index times the
value of the inducing class function at the identity. -/
theorem induce_one [CharZero k] (H : Subgroup G) [Fintype H]
    (f : ClassFunction H k) :
    induce H f 1 = (H.index : k) * f 1 := by
  classical
  rw [induce_apply_formula]
  have hterm (x : G) :
      (if hx : x⁻¹ * (1 : G) * x ∈ H then
        f ⟨x⁻¹ * 1 * x, hx⟩ else 0) = f 1 := by
    rw [dif_pos (by simp)]
    apply congrArg f
    apply Subtype.ext
    simp
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  rw [← Subgroup.card_mul_index H, Nat.cast_mul]
  field_simp

/-- Peterfalvi 1.5(d), source `scaled_cfResInd_sum_cfclass`: after scaling
by degree over norm, restriction of an induced irreducible character is the
index times the degree-weighted orbit sum. -/
theorem scaled_cfResInd_sum_cfclass [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Invertible (Nat.card H : k)] (chi : IrreducibleCharacter H k) :
    let chiG := induce H (chi : ClassFunction H k)
    (chiG 1 / characterPairing chiG chiG) • restrict H chiG =
      (H.index : k) •
        ∑ xi : normalOrbit H (chi : ClassFunction H k),
          (xi : ClassFunction H k) 1 • (xi : ClassFunction H k) := by
  classical
  dsimp only
  let orbitSum : ClassFunction H k :=
    ∑ xi : normalOrbit H (chi : ClassFunction H k),
      (xi : ClassFunction H k)
  have hres : restrict H (induce H (chi : ClassFunction H k)) =
      (inertiaIndex H (chi : ClassFunction H k) : k) • orbitSum :=
    cfResInd_sum_cfclass H (chi : ClassFunction H k)
  have hnorm := cfnorm_Ind_irr H chi
  have hone : induce H (chi : ClassFunction H k) 1 =
      (H.index : k) * chi 1 := induce_one H _
  have horbit_one (xi : normalOrbit H (chi : ClassFunction H k)) :
      (xi : ClassFunction H k) 1 = chi 1 := by
    obtain ⟨x, hx⟩ := xi.property
    calc
      _ = normalConjugate H x (chi : ClassFunction H k) 1 :=
        congrArg (fun f : ClassFunction H k => f 1) hx.symm
      _ = chi 1 := by simp
  have hweighted :
      (∑ xi : normalOrbit H (chi : ClassFunction H k),
        (xi : ClassFunction H k) 1 • (xi : ClassFunction H k)) =
        chi 1 • orbitSum := by
    simp_rw [horbit_one]
    rw [Finset.smul_sum]
  have hrne : (inertiaIndex H (chi : ClassFunction H k) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (inertiaIndex_pos H _).ne'
  rw [hres, hnorm, hone, hweighted]
  rw [smul_smul, div_mul_cancel₀ _ hrne, smul_smul]

/-- If induction of `chi` is irreducible, then its inertia subgroup is
exactly the inducing subgroup. -/
theorem inertia_eq_of_induce_isIrreducible [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Invertible (Nat.card H : k)] (chi : IrreducibleCharacter H k)
    (hirr : IsIrreducibleCharacter G k
      (induce H (chi : ClassFunction H k))) :
    inertia H (chi : ClassFunction H k) = H := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let psi : IrreducibleCharacter G k :=
    ⟨induce H (chi : ClassFunction H k), hirr⟩
  have hnormone :
      characterPairing (induce H (chi : ClassFunction H k))
        (induce H (chi : ClassFunction H k)) = 1 :=
    IrreducibleCharacter.characterPairing_self psi
  have hcast : (inertiaIndex H (chi : ClassFunction H k) : k) = 1 :=
    (cfnorm_Ind_irr H chi).symm.trans hnormone
  have hindex : inertiaIndex H (chi : ClassFunction H k) = 1 := by
    exact_mod_cast hcast
  have hindex' :
      Nat.card (inertia H (chi : ClassFunction H k)) / Nat.card H = 1 := by
    simpa only [inertiaIndex] using hindex
  have hdvd : Nat.card H ∣ Nat.card (inertia H (chi : ClassFunction H k)) :=
    Subgroup.card_dvd_of_le (le_inertia H _)
  have hcard : Nat.card (inertia H (chi : ClassFunction H k)) =
      Nat.card H := by
    symm
    calc
      Nat.card H = Nat.card H * 1 := by simp
      _ = Nat.card H *
          (Nat.card (inertia H (chi : ClassFunction H k)) / Nat.card H) := by
        rw [hindex']
      _ = Nat.card (inertia H (chi : ClassFunction H k)) :=
        Nat.mul_div_cancel' hdvd
  exact (Subgroup.eq_of_le_of_card_ge (le_inertia H _) hcard.le).symm

/-- Bundle the irreducible induction witnesses on a finite family. -/
def induceIrreducibleOn [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal]
    (X : Finset (IrreducibleCharacter H k))
    (hInd : ∀ chi ∈ X, IsIrreducibleCharacter G k
      (induce H (chi : ClassFunction H k)))
    (chi : {chi // chi ∈ X}) : IrreducibleCharacter G k :=
  ⟨induce H (chi.1 : ClassFunction H k), hInd chi.1 chi.2⟩

/-- Source `card_imset_Ind_irr`: a conjugation-stable finite family whose
members induce irreducibly has cardinality equal to the subgroup index times
the number of distinct induced irreducible characters. -/
theorem card_imset_Ind_irr [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Invertible (Nat.card H : k)]
    (X : Finset (IrreducibleCharacter H k))
    (hInd : ∀ chi ∈ X, IsIrreducibleCharacter G k
      (induce H (chi : ClassFunction H k)))
    (hstable : ∀ chi ∈ X, ∀ x : G, chi.normalConjugate H x ∈ X) :
    X.card = H.index *
      (Finset.univ.image (induceIrreducibleOn H X hInd)).card := by
  classical
  let XType := {chi // chi ∈ X}
  let F : XType → IrreducibleCharacter G k :=
    induceIrreducibleOn H X hInd
  have hfiber (a : XType) :
      {b ∈ (Finset.univ : Finset XType) | F b = F a}.card = H.index := by
    let e : {b : XType // F b = F a} ≃
        MulAction.orbit G (a.1 : IrreducibleCharacter H k) :=
      { toFun := fun b =>
          ⟨b.1.1, (cfclass_Ind_irrP H b.1.1 a.1).2
            (congrArg Subtype.val b.2)⟩
        invFun := fun psi =>
          let hmem : psi.1 ∈ X := by
            have horbit := psi.property
            rw [MulAction.mem_orbit_iff] at horbit
            obtain ⟨x, hx⟩ := horbit
            rw [← hx]
            exact hstable a.1 a.2 x
          let b : XType := ⟨psi.1, hmem⟩
          ⟨b, by
            apply Subtype.ext
            exact (cfclass_Ind_irrP H psi.1 a.1).1 psi.property⟩
        left_inv := by
          intro b
          apply Subtype.ext
          rfl
        right_inv := by
          intro psi
          apply Subtype.ext
          rfl }
    have hstab : MulAction.stabilizer G
        (a.1 : IrreducibleCharacter H k) = H :=
      (IrreducibleCharacter.stabilizer_eq_inertia H a.1).trans
        (inertia_eq_of_induce_isIrreducible H a.1 (hInd a.1 a.2))
    have hindex := MulAction.index_stabilizer G
      (a.1 : IrreducibleCharacter H k)
    rw [hstab] at hindex
    have horbit :
        Nat.card (MulAction.orbit G (a.1 : IrreducibleCharacter H k)) =
          H.index := by
      rw [Nat.card_coe_set_eq]
      exact hindex.symm
    calc
      _ = Nat.card {b : XType // F b = F a} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ = Nat.card (MulAction.orbit G (a.1 : IrreducibleCharacter H k)) :=
        Nat.card_congr e
      _ = H.index := horbit
  have hpartition :=
    Finset.card_eq_sum_card_image F (Finset.univ : Finset XType)
  calc
    X.card = Fintype.card XType := by simp [XType]
    _ = ∑ y ∈ Finset.univ.image F,
        {a ∈ (Finset.univ : Finset XType) | F a = y}.card := by
      rw [← hpartition, Finset.card_univ]
    _ = ∑ _y ∈ Finset.univ.image F, H.index := by
      apply Finset.sum_congr rfl
      intro y hy
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
      exact hfiber a
    _ = H.index * (Finset.univ.image F).card := by
      simp [Nat.mul_comm]
    _ = H.index *
        (Finset.univ.image (induceIrreducibleOn H X hInd)).card := rfl

end ClassFunction

namespace IrreducibleCharacter

variable {G k : Type u} [Group G] [Field k] [Fintype G]
  [IsAlgClosed k] [CharZero k]

/-- Contragredient duality commutes with ambient conjugation. -/
theorem dual_normalConjugate (H : Subgroup G) [H.Normal]
    (x : G) (chi : IrreducibleCharacter H k) :
    dual (chi.normalConjugate H x) = (dual chi).normalConjugate H x := by
  ext h
  simp only [dual_apply, coe_normalConjugate,
    ClassFunction.normalConjugate_apply]
  apply congrArg chi
  apply Subtype.ext
  simp

end IrreducibleCharacter

namespace ClassFunction

variable {G k : Type u} [Group G] [Field k]

/-- Pullback along inversion commutes with induction.  This is the
class-function form of the source identity `conj_cfInd`. -/
theorem inverseLinear_induce [Fintype G] [CharZero k]
    (H : Subgroup G) [Fintype H] (f : ClassFunction H k) :
    inverseLinear (induce H f) = induce H (inverseLinear f) := by
  classical
  ext g
  rw [inverseLinear_apply, induce_apply_formula, induce_apply_formula]
  apply congrArg ((Nat.card H : k)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x⁻¹ * g * x ∈ H
  · have hxinv : x⁻¹ * g⁻¹ * x ∈ H := by
      have heq : (x⁻¹ * g * x)⁻¹ = x⁻¹ * g⁻¹ * x := by group
      rw [← heq]
      exact H.inv_mem hx
    rw [dif_pos hxinv, dif_pos hx, inverseLinear_apply]
    apply congrArg f
    apply Subtype.ext
    change x⁻¹ * g⁻¹ * x = (x⁻¹ * g * x)⁻¹
    group
  · have hxinv : x⁻¹ * g⁻¹ * x ∉ H := by
      intro hxinv
      apply hx
      have heq : (x⁻¹ * g⁻¹ * x)⁻¹ = x⁻¹ * g * x := by group
      rw [← heq]
      exact H.inv_mem hxinv
    rw [dif_neg hxinv, dif_neg hx]

/-- In an odd-cardinality group, if the square of an element fixes a class
function under ambient conjugation, then the element itself fixes it. -/
theorem normalConjugate_eq_self_of_square_eq_self
    (H : Subgroup G) [H.Normal] (x : G) (f : ClassFunction H k)
    (hodd : Odd (Nat.card G))
    (hsquare : normalConjugate H (x ^ 2) f = f) :
    normalConjugate H x f = f := by
  have hxpow : (x ^ 2) ^ (Nat.card G).gcdB 2 = x := by
    let hcop : (Nat.card G).Coprime 2 := hodd.coprime_two_right
    change (powCoprime hcop).symm (powCoprime hcop x) = x
    exact (powCoprime hcop).symm_apply_apply x
  rw [← mem_inertia_iff] at hsquare ⊢
  rw [← hxpow]
  exact (inertia H f).zpow_mem hsquare _

private theorem odd_card_subgroup (H : Subgroup G)
    (hodd : Odd (Nat.card G)) : Odd (Nat.card H) := by
  apply Odd.of_dvd_nat hodd
  simpa only [Subgroup.card_top] using
    (Subgroup.card_dvd_of_le (show H ≤ (⊤ : Subgroup G) from le_top))

/-- Peterfalvi 1.5(e), source `odd_induced_orthogonal`: in odd order, the
induction of a nontrivial irreducible character of a normal subgroup is
orthogonal to its contragredient. -/
theorem odd_induced_orthogonal [Fintype G] [IsAlgClosed k] [CharZero k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    (hodd : Odd (Nat.card G)) (chi : IrreducibleCharacter H k)
    (hne : chi ≠ IrreducibleCharacter.trivial) :
    characterPairing (induce H (chi : ClassFunction H k))
      (inverseLinear (induce H (chi : ClassFunction H k))) = 0 := by
  letI : Invertible (Nat.card H : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hinvchi : inverseLinear (chi : ClassFunction H k) =
      (IrreducibleCharacter.dual chi : ClassFunction H k) := by
    ext h
    rw [inverseLinear_apply, IrreducibleCharacter.dual_apply]
  rw [inverseLinear_induce H, hinvchi]
  rcases cfclass_Ind_cases H chi (IrreducibleCharacter.dual chi) with
    horbit | hortho
  · obtain ⟨x, hx⟩ := horbit.1
    have hdualconj :
        (IrreducibleCharacter.dual chi).normalConjugate H x = chi := by
      calc
        _ = IrreducibleCharacter.dual (chi.normalConjugate H x) :=
          (IrreducibleCharacter.dual_normalConjugate H x chi).symm
        _ = IrreducibleCharacter.dual (IrreducibleCharacter.dual chi) := by
          apply congrArg IrreducibleCharacter.dual
          apply Subtype.ext
          exact hx
        _ = chi := IrreducibleCharacter.dual_dual chi
    have hsquare : normalConjugate H (x ^ 2) (chi : ClassFunction H k) =
        (chi : ClassFunction H k) := by
      rw [pow_two, normalConjugate_mul]
      calc
        normalConjugate H x
            (normalConjugate H x (chi : ClassFunction H k)) =
            normalConjugate H x
              (IrreducibleCharacter.dual chi : ClassFunction H k) :=
          congrArg (normalConjugate H x) hx
        _ = (chi : ClassFunction H k) := congrArg Subtype.val hdualconj
    have hxfix : normalConjugate H x (chi : ClassFunction H k) =
        (chi : ClassFunction H k) :=
      normalConjugate_eq_self_of_square_eq_self H x _ hodd hsquare
    have hself : IrreducibleCharacter.dual chi = chi := by
      apply Subtype.ext
      exact hx.symm.trans hxfix
    have hoddH : Odd (Nat.card H) := odd_card_subgroup H hodd
    exact (hne ((odd_eq_conj_irr1 hoddH chi).mp hself)).elim
  · exact hortho.2

end ClassFunction

end

end Submission.OddOrder.PF
