import Submission.CharacterCancellation

namespace Submission.Helpers

open scoped MonoidAlgebra

noncomputable section

section WeightedPermutationTrace

variable {k ι V : Type*} [Field k] [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

lemma trace_weightedPermutation
    (e : ι ≃ ι) (A : ι → V →ₗ[k] V) (T : (ι → V) →ₗ[k] (ι → V))
    (hT : ∀ f x, T f x = A x (f (e x))) :
    LinearMap.trace k (ι → V) T =
      ∑ x : ι, if e x = x then LinearMap.trace k V (A x) else 0 := by
  classical
  let b := Module.Free.chooseBasis k V
  let B := Pi.basis (fun _ : ι => b)
  rw [LinearMap.trace_eq_matrix_trace k B, Matrix.trace, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : e x = x
  · simp only [hx, if_pos]
    rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_repr,
      Pi.basis_apply, hT]
    simp [hx, LinearMap.toMatrix_apply]
  · simp only [hx]
    apply Finset.sum_eq_zero
    intro i _
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_repr,
      Pi.basis_apply, hT]
    simp [hx]

end WeightedPermutationTrace

section InducedModel

variable {G X : Type*} [Group G] [MulAction G X]

def TransitiveActionData.cocycle (D : TransitiveActionData G X) (g : G) (x : X) :
    D.Stabilizer :=
  ⟨(D.transporter x)⁻¹ * g * D.transporter (g⁻¹ • x), by
    change (D.transporter x)⁻¹ * g * D.transporter (g⁻¹ • x) ∈
      MulAction.stabilizer G D.base
    rw [MulAction.mem_stabilizer_iff]
    simp only [mul_smul, D.transporter_smul, smul_inv_smul]
    calc
      (D.transporter x)⁻¹ • x =
          (D.transporter x)⁻¹ • (D.transporter x • D.base) :=
        congrArg ((D.transporter x)⁻¹ • ·) (D.transporter_smul x).symm
      _ = D.base := inv_smul_smul _ _⟩

@[simp]
lemma TransitiveActionData.cocycle_one (D : TransitiveActionData G X) (x : X) :
    D.cocycle 1 x = 1 := by
  apply Subtype.ext
  simp [TransitiveActionData.cocycle]

@[simp]
lemma TransitiveActionData.cocycle_mul (D : TransitiveActionData G X)
    (g h : G) (x : X) :
    D.cocycle (g * h) x = D.cocycle g x * D.cocycle h (g⁻¹ • x) := by
  apply Subtype.ext
  simp [TransitiveActionData.cocycle, mul_smul, mul_assoc]

noncomputable def TransitiveActionData.inducedModel
    (D : TransitiveActionData G X)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ D.Stabilizer V) : Representation ℂ G (X → V) where
  toFun g :=
    { toFun := fun f x => rho (D.cocycle g x) (f (g⁻¹ • x))
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [mul_smul]

lemma TransitiveActionData.inducedModel_character
    [Fintype X] [DecidableEq X]
    (D : TransitiveActionData G X)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ D.Stabilizer V) (g : G) :
    (D.inducedModel rho).character g =
      ∑ x : X, if g⁻¹ • x = x then rho.character (D.cocycle g x) else 0 := by
  rw [Representation.character]
  exact trace_weightedPermutation (MulAction.toPerm g⁻¹)
    (fun x => rho (D.cocycle g x)) (D.inducedModel rho g) (fun _ _ => rfl)

lemma TransitiveActionData.inducedModel_character_one
    [Fintype X] [DecidableEq X]
    (D : TransitiveActionData G X)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ D.Stabilizer V) :
    (D.inducedModel rho).character 1 =
      (Fintype.card X : ℂ) * Module.finrank ℂ V := by
  rw [D.inducedModel_character]
  simp

lemma TransitiveActionData.inducedModel_character_of_isFixedPointFree
    [Fintype X] [DecidableEq X]
    (D : TransitiveActionData G X)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ D.Stabilizer V) {g : G}
    (hg : IsFixedPointFree (X := X) g) :
    (D.inducedModel rho).character g = 0 := by
  rw [D.inducedModel_character]
  apply Finset.sum_eq_zero
  intro x _
  rw [if_neg]
  exact isFixedPointFree_inv hg x

lemma TransitiveActionData.fromStabilizer_cocycle
    (D : TransitiveActionData G X) (g : G) (x : X) (hx : g • x = x) :
    D.fromStabilizer x (D.cocycle g x) = g := by
  have hxi : g⁻¹ • x = x := by
    have h := congrArg (g⁻¹ • ·) hx
    simpa [mul_smul] using h.symm
  simp [TransitiveActionData.fromStabilizer, TransitiveActionData.cocycle,
    hxi, mul_assoc]

lemma TransitiveActionData.inducedModel_character_of_fixed
    [Fintype X] [DecidableEq X]
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ D.Stabilizer V) {g : G} (hg : g ≠ 1)
    (x : X) (hx : g • x = x) :
    (D.inducedModel rho).character g = rho.character (D.cocycle g x) := by
  rw [D.inducedModel_character]
  have hxi : g⁻¹ • x = x := by
    have h := congrArg (g⁻¹ • ·) hx
    simpa [mul_smul] using h.symm
  rw [Finset.sum_eq_single x]
  · simp [hxi]
  · intro y _ hyx
    rw [if_neg]
    intro hyi
    apply hyx
    apply hfrob g hg y x
    · have h := congrArg (g • ·) hyi
      simpa [mul_smul] using h.symm
    · exact hx
  · simp

lemma extendedCharacter_of_fixed
    [Fintype G] [Fintype X]
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ D.Stabilizer V) {g : G} (hg : g ≠ 1)
    (x : X) (hx : g • x = x) :
    extendedCharacter D hfrob rho g = rho.character (D.cocycle g x) := by
  have hc : ((D.cocycle g x : D.Stabilizer) : G) ≠ 1 := by
    intro he
    apply hg
    calc
      g = D.fromStabilizer x (D.cocycle g x) :=
        (D.fromStabilizer_cocycle g x hx).symm
      _ = D.fromStabilizer x 1 := by
        congr 1
        exact Subtype.ext he
      _ = 1 := by simp [TransitiveActionData.fromStabilizer]
  calc
    extendedCharacter D hfrob rho g =
        extendedCharacter D hfrob rho (D.fromStabilizer x (D.cocycle g x)) :=
      congrArg (extendedCharacter D hfrob rho)
        (D.fromStabilizer_cocycle g x hx).symm
    _ = rho.character (D.cocycle g x) :=
      extendedCharacter_fromStabilizer D hfrob rho x (D.cocycle g x) hc

end InducedModel

section FiniteExtension

variable {G X : Type} [Group G] [MulAction G X]

lemma Representation.trivial_character
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (g : G) :
    (Representation.trivial ℂ G V).character g = Module.finrank ℂ V := by
  rw [Representation.character]
  change LinearMap.trace ℂ V LinearMap.id = Module.finrank ℂ V
  simp

noncomputable def extensionPositive
    [Fintype X] (D : TransitiveActionData G X)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ D.Stabilizer V) : FDRep ℂ G :=
  FDRep.of ((D.inducedModel rho).prod (Representation.trivial ℂ G V))

noncomputable def extensionNegative
    [Fintype X] (D : TransitiveActionData G X)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] : FDRep ℂ G :=
  FDRep.of (D.inducedModel (Representation.trivial ℂ D.Stabilizer V))

lemma extension_character_sub
    [Fintype G] [Fintype X]
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ D.Stabilizer V) :
    (extensionPositive D rho).character - (extensionNegative (V := V) D).character =
      extendedCharacter D hfrob rho := by
  classical
  unfold extensionPositive extensionNegative
  funext g
  rw [Pi.sub_apply]
  change ((D.inducedModel rho).prod (Representation.trivial ℂ G V)).character g -
      (D.inducedModel (Representation.trivial ℂ D.Stabilizer V)).character g =
    extendedCharacter D hfrob rho g
  rw [congrFun (Representation.character_prod (D.inducedModel rho)
    (Representation.trivial ℂ G V)) g]
  change (D.inducedModel rho).character g +
      (Representation.trivial ℂ G V).character g -
        (D.inducedModel (Representation.trivial ℂ D.Stabilizer V)).character g =
    extendedCharacter D hfrob rho g
  by_cases hg : g = 1
  · subst g
    rw [D.inducedModel_character_one, D.inducedModel_character_one,
      extendedCharacter_one]
    simp
  · by_cases hfree : IsFixedPointFree (X := X) g
    · rw [D.inducedModel_character_of_isFixedPointFree rho hfree,
        D.inducedModel_character_of_isFixedPointFree
          (Representation.trivial ℂ D.Stabilizer V) hfree,
        extendedCharacter_of_isFixedPointFree D hfrob rho hfree]
      rw [Representation.trivial_character]
      simp
    · have hfixed : ∃ x : X, g • x = x := by
        by_contra h
        apply hfree
        intro x hx
        exact h ⟨x, hx⟩
      obtain ⟨x, hx⟩ := hfixed
      rw [D.inducedModel_character_of_fixed hfrob rho hg x hx,
        D.inducedModel_character_of_fixed hfrob
          (Representation.trivial ℂ D.Stabilizer V) hg x hx,
        extendedCharacter_of_fixed D hfrob rho hg x hx]
      rw [Representation.trivial_character, Representation.trivial_character]
      simp

end FiniteExtension

section FrobeniusCounting

variable {G X : Type*} [Group G] [MulAction G X]

def FrobeniusKernelPred (g : G) : Prop :=
  g = 1 ∨ IsFixedPointFree (X := X) g

noncomputable def complementKernelEquivFixedNontrivial :
    {g : G // ¬FrobeniusKernelPred (X := X) g} ≃ FixedNontrivial G X :=
  Equiv.subtypeEquiv (Equiv.refl G) (by
    intro g
    simp [FrobeniusKernelPred, IsFixedPointFree])

theorem TransitiveActionData.isPretransitive (D : TransitiveActionData G X) :
    MulAction.IsPretransitive G X where
  exists_smul_eq x y :=
    ⟨D.transporter y * (D.transporter x)⁻¹, by
      calc
        (D.transporter y * (D.transporter x)⁻¹) • x =
            D.transporter y • ((D.transporter x)⁻¹ • x) := by
          simp only [mul_smul]
        _ = D.transporter y • D.base := by
          congr 1
          calc
            (D.transporter x)⁻¹ • x =
                (D.transporter x)⁻¹ • (D.transporter x • D.base) :=
              congrArg ((D.transporter x)⁻¹ • ·) (D.transporter_smul x).symm
            _ = D.base := inv_smul_smul _ _
        _ = y := D.transporter_smul y⟩

lemma TransitiveActionData.card_nontrivial_stabilizer_add_one
    [Finite G] (D : TransitiveActionData G X) :
    Nat.card {h : D.Stabilizer // (h : G) ≠ 1} + 1 =
      Nat.card D.Stabilizer := by
  classical
  have hpartition := Nat.card_congr
    (Equiv.sumCompl (fun h : D.Stabilizer => (h : G) = 1))
  rw [Nat.card_sum] at hpartition
  have hone : Nat.card {h : D.Stabilizer // (h : G) = 1} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · constructor
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      exact a.2.trans b.2.symm
    · exact ⟨⟨1, by simp⟩⟩
  rw [hone] at hpartition
  change 1 + Nat.card {h : D.Stabilizer // (h : G) ≠ 1} =
    Nat.card D.Stabilizer at hpartition
  omega

lemma TransitiveActionData.card_fixedNontrivial
    [Finite G] [Finite X]
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y) :
    Nat.card (FixedNontrivial G X) =
      Nat.card X * Nat.card {h : D.Stabilizer // (h : G) ≠ 1} := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (D.fixedEquiv hfrob)).symm

lemma TransitiveActionData.card_group
    [Finite G] [Finite X] (D : TransitiveActionData G X) :
    Nat.card G = Nat.card X * Nat.card D.Stabilizer := by
  letI : MulAction.IsPretransitive G X := D.isPretransitive
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G D.base)
  rw [Nat.card_prod] at h
  simpa [TransitiveActionData.Stabilizer, MulAction.orbit_eq_univ] using h.symm

lemma TransitiveActionData.card_frobeniusKernelPred
    [Finite G] [Finite X]
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y) :
    Nat.card {g : G // FrobeniusKernelPred (X := X) g} = Nat.card X := by
  classical
  have hpartition := Nat.card_congr
    (Equiv.sumCompl (FrobeniusKernelPred (G := G) (X := X)))
  rw [Nat.card_sum] at hpartition
  have hcompl :
      Nat.card {g : G // ¬FrobeniusKernelPred (X := X) g} =
        Nat.card (FixedNontrivial G X) :=
    Nat.card_congr complementKernelEquivFixedNontrivial
  rw [hcompl, D.card_fixedNontrivial hfrob, D.card_group,
    ← D.card_nontrivial_stabilizer_add_one] at hpartition
  simp only [Nat.mul_add, Nat.mul_one] at hpartition
  omega

end FrobeniusCounting

section ExtensionNorm

variable {G X V : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

lemma extendedCharacter_of_frobeniusKernelPred
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    (rho : Representation ℂ D.Stabilizer V) {g : G}
    (hg : FrobeniusKernelPred (X := X) g) :
    extendedCharacter D hfrob rho g = Module.finrank ℂ V := by
  rcases hg with rfl | hg
  · exact extendedCharacter_one D hfrob rho
  · exact extendedCharacter_of_isFixedPointFree D hfrob rho hg

lemma extendedCharacter_fixedEquiv_apply
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    (rho : Representation ℂ D.Stabilizer V)
    (z : X × {h : D.Stabilizer // (h : G) ≠ 1}) :
    extendedCharacter D hfrob rho (D.fixedEquiv hfrob z).1 =
      rho.character z.2.1 := by
  change extendedCharacter D hfrob rho (D.fromStabilizer z.1 z.2.1) = _
  exact extendedCharacter_fromStabilizer D hfrob rho z.1 z.2.1 z.2.2

lemma sum_normSq_irreducible_character
    {H : Type*} [Group H] [Fintype H]
    (rho : Representation ℂ H V) [rho.IsIrreducible] :
    ∑ h : H, Complex.normSq (rho.character h) = (Nat.card H : ℝ) := by
  have hnorm := classFunctionNormSq_irreducible_character rho
  rw [classFunctionNormSq] at hnorm
  have hcard : (Nat.card H : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hcard] at hnorm
  exact hnorm

lemma classFunctionNormSq_extendedCharacter_of_irreducible
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    (rho : Representation ℂ D.Stabilizer V) [rho.IsIrreducible] :
    classFunctionNormSq (extendedCharacter D hfrob rho) = 1 := by
  classical
  letI : Finite (FixedNontrivial G X) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (FixedNontrivial G X) := Fintype.ofFinite _
  let d : ℂ := Module.finrank ℂ V
  let q : ℝ := Complex.normSq d
  have hkernelSum :
      (∑ z : {g : G // FrobeniusKernelPred (X := X) g},
          Complex.normSq (extendedCharacter D hfrob rho z.1)) =
        (Nat.card X : ℝ) * q := by
    calc
      (∑ z : {g : G // FrobeniusKernelPred (X := X) g},
          Complex.normSq (extendedCharacter D hfrob rho z.1)) =
          ∑ _z : {g : G // FrobeniusKernelPred (X := X) g}, q := by
        apply Finset.sum_congr rfl
        intro z _
        rw [extendedCharacter_of_frobeniusKernelPred D hfrob rho z.2]
      _ = (Nat.card X : ℝ) * q := by
        simp [← Nat.card_eq_fintype_card, D.card_frobeniusKernelPred hfrob]
  have hfixedSum :
      (∑ z : FixedNontrivial G X,
          Complex.normSq (extendedCharacter D hfrob rho z.1)) =
        (Nat.card X : ℝ) *
          ∑ h : {h : D.Stabilizer // (h : G) ≠ 1},
            Complex.normSq (rho.character h.1) := by
    rw [← (D.fixedEquiv hfrob).sum_comp, Fintype.sum_prod_type]
    simp_rw [extendedCharacter_fixedEquiv_apply D hfrob rho]
    simp [← Nat.card_eq_fintype_card]
  have hstabilizerSum :
      (∑ h : {h : D.Stabilizer // (h : G) ≠ 1},
          Complex.normSq (rho.character h.1)) + q =
        (Nat.card D.Stabilizer : ℝ) := by
    have hpartition := Fintype.sum_subtype_add_sum_subtype
      (fun h : D.Stabilizer => (h : G) = 1)
      (fun h => Complex.normSq (rho.character h))
    have htotal := sum_normSq_irreducible_character rho
    have hidentity :
        (∑ h : {h : D.Stabilizer // (h : G) = 1},
            Complex.normSq (rho.character h.1)) = q := by
      let one : {h : D.Stabilizer // (h : G) = 1} := ⟨1, by simp⟩
      rw [Finset.sum_eq_single one]
      · simp [one, q, d]
      · intro h _ hne
        exfalso
        apply hne
        apply Subtype.ext
        apply Subtype.ext
        exact h.2
      · simp
    calc
      (∑ h : {h : D.Stabilizer // (h : G) ≠ 1},
          Complex.normSq (rho.character h.1)) + q =
          q + ∑ h : {h : D.Stabilizer // (h : G) ≠ 1},
            Complex.normSq (rho.character h.1) := add_comm _ _
      _ = ∑ h : D.Stabilizer, Complex.normSq (rho.character h) := by
        rw [← hidentity]
        simpa only using hpartition
      _ = (Nat.card D.Stabilizer : ℝ) := htotal
  have hcomplementSum :
      (∑ z : {g : G // ¬FrobeniusKernelPred (X := X) g},
          Complex.normSq (extendedCharacter D hfrob rho z.1)) =
        ∑ z : FixedNontrivial G X,
          Complex.normSq (extendedCharacter D hfrob rho z.1) := by
    let e := complementKernelEquivFixedNontrivial (G := G) (X := X)
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro z _
    rfl
  have hgroupSum :
      ∑ g : G, Complex.normSq (extendedCharacter D hfrob rho g) =
        (Nat.card G : ℝ) := by
    have hpartition := Fintype.sum_subtype_add_sum_subtype
      (FrobeniusKernelPred (G := G) (X := X))
      (fun g => Complex.normSq (extendedCharacter D hfrob rho g))
    rw [← hpartition, hkernelSum, hcomplementSum, hfixedSum,
      ← mul_add, add_comm q, hstabilizerSum, ← Nat.cast_mul, ← D.card_group]
  rw [classFunctionNormSq, hgroupSum]
  have hcard : (Nat.card G : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

end ExtensionNorm

section IrreducibleExtension

variable {G X V : Type} [Group G] [Fintype G] [Fintype X] [MulAction G X]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem exists_fdRep_character_eq_extended_of_irreducible
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    (rho : Representation ℂ D.Stabilizer V) [rho.IsIrreducible] :
    ∃ C : FDRep ℂ G, C.character = extendedCharacter D hfrob rho := by
  classical
  let A := extensionPositive D rho
  let B := extensionNegative (V := V) D
  have hvirtual : A.character - B.character = extendedCharacter D hfrob rho :=
    extension_character_sub D hfrob rho
  have hnorm : classFunctionNormSq (A.character - B.character) = 1 := by
    rw [hvirtual]
    exact classFunctionNormSq_extendedCharacter_of_irreducible D hfrob rho
  have hVpos : 0 < Module.finrank ℂ V := by
    letI : IsSimpleModule ℂ[D.Stabilizer] rho.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule rho).mp inferInstance
    letI : Nontrivial rho.asModule := IsSimpleModule.nontrivial ℂ[D.Stabilizer] rho.asModule
    letI : Nontrivial V := rho.asModuleEquiv.symm.toEquiv.nontrivial
    exact Module.finrank_pos_iff.mpr inferInstance
  have hdim : Module.finrank ℂ B < Module.finrank ℂ A := by
    have hdegree := congrFun hvirtual 1
    simp only [Pi.sub_apply, FDRep.char_one, extendedCharacter_one] at hdegree
    have hc :
        (Module.finrank ℂ A : ℂ) =
          (Module.finrank ℂ B : ℂ) + Module.finrank ℂ V := by
      linear_combination hdegree
    have hn :
        Module.finrank ℂ A = Module.finrank ℂ B + Module.finrank ℂ V := by
      exact_mod_cast hc
    omega
  obtain ⟨C, hC⟩ := exists_fdRep_character_eq_sub_of_normSq_eq_one A B hnorm hdim
  exact ⟨C, hC.trans hvirtual⟩

end IrreducibleExtension

section ArbitraryExtension

variable {G X : Type} [Group G] [Fintype G] [Fintype X] [MulAction G X]

lemma extendedCharacter_prod
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ D.Stabilizer V)
    (sigma : Representation ℂ D.Stabilizer W) :
    extendedCharacter D hfrob (rho.prod sigma) =
      extendedCharacter D hfrob rho + extendedCharacter D hfrob sigma := by
  classical
  funext g
  unfold extendedCharacter
  simp only [Pi.add_apply]
  by_cases hg : g ≠ 1 ∧ ∃ x : X, g • x = x
  · rw [dif_pos hg, dif_pos hg, dif_pos hg]
    exact congrFun (Representation.character_prod rho sigma) _
  · rw [dif_neg hg, dif_neg hg, dif_neg hg]
    simp [Module.finrank_prod]

lemma extendedCharacter_iso
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {rho : Representation ℂ D.Stabilizer V}
    {sigma : Representation ℂ D.Stabilizer W} (e : rho.Equiv sigma) :
    extendedCharacter D hfrob rho = extendedCharacter D hfrob sigma := by
  classical
  have hchar : rho.character = sigma.character := Representation.char_iso e
  have hdim : Module.finrank ℂ V = Module.finrank ℂ W :=
    e.toLinearEquiv.finrank_eq
  funext g
  unfold extendedCharacter
  by_cases hg : g ≠ 1 ∧ ∃ x : X, g • x = x
  · rw [dif_pos hg, dif_pos hg, hchar]
  · rw [dif_neg hg, dif_neg hg, hdim]

omit [Fintype G] [Fintype X] [MulAction G X] in
lemma Representation.character_eq_zero_of_finrank_eq_zero
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (hV : Module.finrank ℂ V = 0) :
    rho.character = 0 := by
  letI : Subsingleton V := Module.finrank_zero_iff.mp hV
  funext g
  rw [Representation.character]
  have hzero : rho g = 0 := Subsingleton.elim _ _
  rw [hzero]
  simp

theorem exists_fdRep_character_eq_extended
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ D.Stabilizer V) :
    ∃ C : FDRep ℂ G, C.character = extendedCharacter D hfrob rho := by
  classical
  induction hdim : Module.finrank ℂ V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hn : n = 0
      · have hVzero : Module.finrank ℂ V = 0 := hdim.trans hn
        let Z : FDRep ℂ G :=
          FDRep.of (Representation.trivial ℂ G (Fin 0 → ℂ))
        refine ⟨Z, ?_⟩
        have hrhozero := Representation.character_eq_zero_of_finrank_eq_zero rho hVzero
        funext g
        rw [extendedCharacter]
        by_cases hg : g ≠ 1 ∧ ∃ x : X, g • x = x
        · rw [dif_pos hg, hrhozero]
          simp [Z, FDRep.character]
        · rw [dif_neg hg, hVzero]
          simp [Z, FDRep.character]
      · have hVpos : 0 < Module.finrank ℂ V := by omega
        letI : Nontrivial V := Module.finrank_pos_iff.mp hVpos
        by_cases hirr : rho.IsIrreducible
        · letI : rho.IsIrreducible := hirr
          exact exists_fdRep_character_eq_extended_of_irreducible D hfrob rho
        · letI : NeZero (Nat.card D.Stabilizer : ℂ) :=
            ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
          letI : rho.IsSemisimpleRepresentation := by infer_instance
          have hproper : ∃ S : Subrepresentation rho, S ≠ ⊥ ∧ S ≠ ⊤ := by
            by_contra hnone
            apply hirr
            letI : Nontrivial (Subrepresentation rho) := by
              apply nontrivial_of_ne (⊥ : Subrepresentation rho) ⊤
              intro h
              have hsub := congrArg Subrepresentation.toSubmodule h
              change (⊥ : Submodule ℂ V) = ⊤ at hsub
              exact bot_ne_top hsub
            apply IsSimpleOrder.of_forall_eq_top
            intro S hSbot
            by_contra hStop
            exact hnone ⟨S, hSbot, hStop⟩
          obtain ⟨S, hSbot, hStop⟩ := hproper
          obtain ⟨T, hST⟩ := exists_isCompl S
          have hTbot : T ≠ ⊥ := by
            intro hT
            apply hStop
            have htop := hST.codisjoint.eq_top
            simpa [hT] using htop
          have hSsub : S.toSubmodule ≠ ⊥ := by
            intro h
            apply hSbot
            apply Subrepresentation.toSubmodule_injective
            change S.toSubmodule = (⊥ : Submodule ℂ V)
            exact h
          have hTsub : T.toSubmodule ≠ ⊥ := by
            intro h
            apply hTbot
            apply Subrepresentation.toSubmodule_injective
            change T.toSubmodule = (⊥ : Submodule ℂ V)
            exact h
          letI : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hSsub
          letI : Nontrivial T.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hTsub
          have hdimST :
              Module.finrank ℂ S.toSubmodule + Module.finrank ℂ T.toSubmodule =
                Module.finrank ℂ V :=
            Subrepresentation.finrank_add_finrank_eq S T hST
          have hSlt : Module.finrank ℂ S.toSubmodule < n := by
            have hTpos : 0 < Module.finrank ℂ T.toSubmodule :=
              Module.finrank_pos_iff.mpr inferInstance
            omega
          have hTlt : Module.finrank ℂ T.toSubmodule < n := by
            have hSpos : 0 < Module.finrank ℂ S.toSubmodule :=
              Module.finrank_pos_iff.mpr inferInstance
            omega
          obtain ⟨CS, hCS⟩ := ih (Module.finrank ℂ S.toSubmodule) hSlt
            S.toRepresentation rfl
          obtain ⟨CT, hCT⟩ := ih (Module.finrank ℂ T.toSubmodule) hTlt
            T.toRepresentation rfl
          let C : FDRep ℂ G := FDRep.of (Representation.prod CS.ρ CT.ρ)
          refine ⟨C, ?_⟩
          have hdecomp := extendedCharacter_iso D hfrob
            (Submission.Helpers.Subrepresentation.prodEquivOfIsCompl S T hST)
          rw [show C.character = CS.character + CT.character from
            Representation.character_prod CS.ρ CT.ρ, hCS, hCT,
            ← extendedCharacter_prod D hfrob S.toRepresentation T.toRepresentation,
            hdecomp]

end ArbitraryExtension

end

end Submission.Helpers
