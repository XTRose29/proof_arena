import Mathlib

namespace Submission.Helpers

open scoped ComplexConjugate ComplexOrder

section Action

variable {G X : Type*} [Group G] [MulAction G X]

def IsFixedPointFree (g : G) : Prop := ∀ x : X, g • x ≠ x

lemma isFixedPointFree_inv {g : G} (hg : IsFixedPointFree (X := X) g) :
    IsFixedPointFree (X := X) g⁻¹ := by
  intro x hx
  apply hg x
  have := congrArg (g • ·) hx
  simpa [mul_smul] using this.symm

lemma isFixedPointFree_conj_iff (a g : G) :
    IsFixedPointFree (X := X) (a * g * a⁻¹) ↔ IsFixedPointFree (X := X) g := by
  constructor
  · intro h x hx
    apply h (a • x)
    simp [mul_smul, hx]
  · intro h x hx
    apply h (a⁻¹ • x)
    have := congrArg (fun y => a⁻¹ • y) hx
    simpa [mul_smul] using this

lemma pow_eq_one_or_isFixedPointFree
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    {g : G} (hg : IsFixedPointFree (X := X) g) (n : ℕ) :
    g ^ n = 1 ∨ IsFixedPointFree (X := X) (g ^ n) := by
  by_cases hpow : g ^ n = 1
  · exact Or.inl hpow
  · refine Or.inr fun x hx => ?_
    have hfix : g ^ n • (g • x) = g • x := by
      rw [← mul_smul, (Commute.pow_left (Commute.refl g) n).eq]
      simp only [mul_smul, hx]
    exact hg x (hfrob (g ^ n) hpow x (g • x) hx hfix).symm

structure TransitiveActionData (G X : Type*) [Group G] [MulAction G X] where
  base : X
  transporter : X → G
  transporter_smul : ∀ x : X, transporter x • base = x

noncomputable def TransitiveActionData.ofTransitive
    (G X : Type*) [Group G] [MulAction G X] (base : X)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) : TransitiveActionData G X where
  base := base
  transporter x := Classical.choose (htrans base x)
  transporter_smul x := Classical.choose_spec (htrans base x)

def TransitiveActionData.Stabilizer (D : TransitiveActionData G X) : Subgroup G :=
  MulAction.stabilizer G D.base

def FixedNontrivial (G X : Type*) [Group G] [MulAction G X] :=
  {g : G // g ≠ 1 ∧ ∃ x : X, g • x = x}

def TransitiveActionData.fromStabilizer (D : TransitiveActionData G X) (x : X)
    (h : D.Stabilizer) : G := D.transporter x * (h : G) * (D.transporter x)⁻¹

lemma TransitiveActionData.fromStabilizer_ne_one (D : TransitiveActionData G X) (x : X)
    {h : D.Stabilizer} (hh : (h : G) ≠ 1) : D.fromStabilizer x h ≠ 1 := by
  intro heq
  apply hh
  have := congrArg (fun z : G => (D.transporter x)⁻¹ * z * D.transporter x) heq
  simpa [TransitiveActionData.fromStabilizer, mul_assoc] using this

lemma TransitiveActionData.fromStabilizer_fixes (D : TransitiveActionData G X) (x : X)
    (h : D.Stabilizer) : D.fromStabilizer x h • x = x := by
  calc
    D.fromStabilizer x h • x =
        D.fromStabilizer x h • (D.transporter x • D.base) :=
      congrArg (D.fromStabilizer x h • ·) (D.transporter_smul x).symm
    _ = D.transporter x • ((h : G) • D.base) := by
      simp [TransitiveActionData.fromStabilizer, mul_smul]
    _ = D.transporter x • D.base := congrArg (D.transporter x • ·) h.2
    _ = x := D.transporter_smul x

noncomputable def TransitiveActionData.fixedEquiv (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y) :
    (X × {h : D.Stabilizer // (h : G) ≠ 1}) ≃ FixedNontrivial G X := by
  let f : (X × {h : D.Stabilizer // (h : G) ≠ 1}) → FixedNontrivial G X :=
    fun z => ⟨D.fromStabilizer z.1 z.2.1,
      D.fromStabilizer_ne_one z.1 z.2.2,
      z.1, D.fromStabilizer_fixes z.1 z.2.1⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨x, h⟩ ⟨y, k⟩ heq
    have hval : D.fromStabilizer x h.1 = D.fromStabilizer y k.1 :=
      congrArg Subtype.val heq
    have hxy : x = y := hfrob _ (D.fromStabilizer_ne_one x h.2) x y
      (D.fromStabilizer_fixes x h.1) (hval ▸ D.fromStabilizer_fixes y k.1)
    subst y
    have hhk : (h.1 : G) = (k.1 : G) := by
      have := congrArg (fun z : G => (D.transporter x)⁻¹ * z * D.transporter x) hval
      simpa [TransitiveActionData.fromStabilizer, mul_assoc] using this
    cases h
    cases k
    simp_all
  · rintro ⟨g, hg, x, hx⟩
    let h : D.Stabilizer :=
      ⟨(D.transporter x)⁻¹ * g * D.transporter x, by
        change (D.transporter x)⁻¹ * g * D.transporter x ∈
          MulAction.stabilizer G D.base
        rw [MulAction.mem_stabilizer_iff]
        simp only [mul_smul]
        rw [D.transporter_smul x, hx]
        calc
          (D.transporter x)⁻¹ • x =
              (D.transporter x)⁻¹ • (D.transporter x • D.base) :=
            congrArg ((D.transporter x)⁻¹ • ·) (D.transporter_smul x).symm
          _ = D.base := inv_smul_smul _ _⟩
    have hh : (h : G) ≠ 1 := by
      intro heq
      apply hg
      have := congrArg (fun z : G => D.transporter x * z * (D.transporter x)⁻¹) heq
      simpa [h, mul_assoc] using this
    refine ⟨⟨x, ⟨h, hh⟩⟩, Subtype.ext ?_⟩
    simp [f, TransitiveActionData.fromStabilizer, h, mul_assoc]

end Action

section Characters

lemma trace_inv_eq_conj_trace_of_finite_group
    {G n : Type*} [Group G] [Fintype G] [Fintype n] [DecidableEq n]
    (A : G →* (Matrix n n ℂ)ˣ) (g : G) :
    (↑(A g⁻¹) : Matrix n n ℂ).trace = conj (↑(A g) : Matrix n n ℂ).trace := by
  let P : Matrix n n ℂ :=
    ∑ h : G, Matrix.conjTranspose (↑(A h) : Matrix n n ℂ) *
      (↑(A h) : Matrix n n ℂ)
  have hP : P.PosDef := by
    refine Matrix.posDef_sum Finset.univ_nonempty fun h _ => ?_
    exact Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_of_isUnit (A h).isUnit)
  have hPinv :
      Matrix.conjTranspose (↑(A g) : Matrix n n ℂ) * P *
        (↑(A g) : Matrix n n ℂ) = P := by
    calc
      _ = ∑ h : G,
          Matrix.conjTranspose (↑(A g) : Matrix n n ℂ) *
            (Matrix.conjTranspose (↑(A h) : Matrix n n ℂ) *
              (↑(A h) : Matrix n n ℂ)) *
              (↑(A g) : Matrix n n ℂ) := by simp [P, Finset.mul_sum, Finset.sum_mul]
      _ = ∑ h : G,
          Matrix.conjTranspose (↑(A (h * g)) : Matrix n n ℂ) *
            (↑(A (h * g)) : Matrix n n ℂ) := by
            apply Finset.sum_congr rfl
            intro h _
            simp only [map_mul, Units.val_mul, Matrix.conjTranspose_mul]
            noncomm_ring
      _ = P := by
        exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun _ => rfl
  let U : (Matrix n n ℂ)ˣ := hP.isUnit.unit
  have hU : (↑U : Matrix n n ℂ) = P := hP.isUnit.unit_spec
  have hrel :
      Matrix.conjTranspose (↑(A g) : Matrix n n ℂ) * (↑U : Matrix n n ℂ) =
        (↑U : Matrix n n ℂ) * (↑((A g)⁻¹) : Matrix n n ℂ) := by
    calc
      _ = Matrix.conjTranspose (↑(A g) : Matrix n n ℂ) * P := by rw [hU]
      _ = (Matrix.conjTranspose (↑(A g) : Matrix n n ℂ) * P *
            (↑(A g) : Matrix n n ℂ)) * (↑((A g)⁻¹) : Matrix n n ℂ) := by simp
      _ = P * (↑((A g)⁻¹) : Matrix n n ℂ) := by rw [hPinv]
      _ = _ := by rw [hU]
  have hinv :
      (↑(A g⁻¹) : Matrix n n ℂ) =
        (↑U⁻¹ : Matrix n n ℂ) * Matrix.conjTranspose (↑(A g) : Matrix n n ℂ) *
          (↑U : Matrix n n ℂ) := by
    rw [map_inv]
    calc
      (↑((A g)⁻¹) : Matrix n n ℂ) =
          (↑U⁻¹ : Matrix n n ℂ) *
            ((↑U : Matrix n n ℂ) * (↑((A g)⁻¹) : Matrix n n ℂ)) := by simp
      _ = (↑U⁻¹ : Matrix n n ℂ) *
            (Matrix.conjTranspose (↑(A g) : Matrix n n ℂ) * (↑U : Matrix n n ℂ)) := by
              rw [hrel]
      _ = _ := by noncomm_ring
  have htrace :
      ((↑U⁻¹ : Matrix n n ℂ) * Matrix.conjTranspose (↑(A g) : Matrix n n ℂ) *
        (↑U : Matrix n n ℂ)).trace =
          (Matrix.conjTranspose (↑(A g) : Matrix n n ℂ)).trace := by
    simpa using Matrix.trace_units_conj U⁻¹
      (Matrix.conjTranspose (↑(A g) : Matrix n n ℂ))
  rw [hinv, htrace, Matrix.trace_conjTranspose]
  rfl

lemma Representation.char_inv_eq_conj
    {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = conj (ρ.character g) := by
  classical
  let b := Module.Free.chooseBasis ℂ V
  let toMat : (V →ₗ[ℂ] V) →*
      Matrix (Module.Free.ChooseBasisIndex ℂ V) (Module.Free.ChooseBasisIndex ℂ V) ℂ :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.toMonoidHom
  let A : G →*
      (Matrix (Module.Free.ChooseBasisIndex ℂ V) (Module.Free.ChooseBasisIndex ℂ V) ℂ)ˣ :=
    (Units.map toMat).comp ρ.toHomUnits
  rw [Representation.character, Representation.character,
    LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.trace_eq_matrix_trace ℂ b]
  exact trace_inv_eq_conj_trace_of_finite_group A g

noncomputable def extendedCharacter
    {G X V : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ D.Stabilizer V) (g : G) : ℂ := by
  classical
  exact if hg : g ≠ 1 ∧ ∃ x : X, g • x = x then
    ρ.character (((D.fixedEquiv hfrob).symm
      (⟨g, hg⟩ : FixedNontrivial G X)).2.1)
  else Module.finrank ℂ V

lemma extendedCharacter_one
    {G X V : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ D.Stabilizer V) :
    extendedCharacter D hfrob ρ 1 = Module.finrank ℂ V := by
  simp [extendedCharacter]

lemma extendedCharacter_of_isFixedPointFree
    {G X V : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ D.Stabilizer V) {g : G}
    (hg : IsFixedPointFree (X := X) g) :
    extendedCharacter D hfrob ρ g = Module.finrank ℂ V := by
  rw [extendedCharacter, dif_neg]
  rintro ⟨_, x, hx⟩
  exact hg x hx

lemma extendedCharacter_fromStabilizer
    {G X V : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ D.Stabilizer V) (x : X) (h : D.Stabilizer)
    (hh : (h : G) ≠ 1) :
    extendedCharacter D hfrob ρ (D.fromStabilizer x h) = ρ.character h := by
  let z : X × {h : D.Stabilizer // (h : G) ≠ 1} := ⟨x, h, hh⟩
  let e := D.fixedEquiv hfrob
  rw [extendedCharacter, dif_pos ⟨D.fromStabilizer_ne_one x hh,
    x, D.fromStabilizer_fixes x h⟩]
  change ρ.character ((e.symm (e z)).2.1) = ρ.character h
  rw [e.symm_apply_apply]

lemma extendedCharacter_inv_eq_conj
    {G X V : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ D.Stabilizer V) (g : G) :
    extendedCharacter D hfrob ρ g⁻¹ = conj (extendedCharacter D hfrob ρ g) := by
  classical
  by_cases hg : g ≠ 1 ∧ ∃ x : X, g • x = x
  · let z := (D.fixedEquiv hfrob).symm ⟨g, hg⟩
    have hgz : D.fromStabilizer z.1 z.2.1 = g := by
      exact congrArg Subtype.val ((D.fixedEquiv hfrob).apply_symm_apply ⟨g, hg⟩)
    have hzinv : ((z.2.1 : D.Stabilizer)⁻¹ : G) ≠ 1 := inv_ne_one.mpr z.2.2
    rw [← hgz]
    have hfrominv :
        (D.fromStabilizer z.1 z.2.1)⁻¹ = D.fromStabilizer z.1 (z.2.1)⁻¹ := by
      simp [TransitiveActionData.fromStabilizer, mul_assoc]
    rw [hfrominv, extendedCharacter_fromStabilizer D hfrob ρ z.1 (z.2.1)⁻¹ hzinv,
      extendedCharacter_fromStabilizer D hfrob ρ z.1 z.2.1 z.2.2,
      Representation.char_inv_eq_conj]
  · have hginv : ¬(g⁻¹ ≠ 1 ∧ ∃ x : X, g⁻¹ • x = x) := by
      rintro ⟨hne, x, hx⟩
      apply hg
      refine ⟨inv_ne_one.mp hne, x, ?_⟩
      have := congrArg (g • ·) hx
      simpa [mul_smul] using this.symm
    rw [extendedCharacter, dif_neg hginv, extendedCharacter, dif_neg hg]
    simp

end Characters

end Submission.Helpers
