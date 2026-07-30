import Submission.OddOrder.PF.Section02.DadeBasicProperties

/-!
# Peterfalvi 2.11: restricting the Dade construction

A Dade hypothesis remains valid after restricting its distinguished set to
an `L`-stable subset.  The canonical signalizer and its first support do not
change on that subset, so the restricted Dade map agrees with the original
map on class functions supported there.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

/-- Peterfalvi 2.11, first part: a Dade hypothesis restricts to an
`L`-stable subset of its distinguished set. -/
theorem restr_Dade_hyp
    {Γ : Type u} [Group Γ]
    {G L : Subgroup Γ} {A A₁ : Set Γ}
    (ddA : DadeHypothesis G L A)
    (hA₁A : A₁ ⊆ A)
    (hA₁L : L ≤ Subgroup.normalizer A₁) :
    DadeHypothesis G L A₁ := by
  rcases ddA with
    ⟨⟨hAL, hAnorm⟩, hLG, hAone, hconj, H, hH, hcop⟩
  refine ⟨⟨hA₁A.trans hAL, hA₁L⟩, hLG, ?_, ?_, ?_⟩
  · exact fun hOne ↦ hAone (hA₁A hOne)
  · intro x hx y hy hxy
    exact hconj (hA₁A hx) (hA₁A hy) hxy
  · refine ⟨H, ?_, ?_⟩
    · intro a ha
      exact hH (hA₁A ha)
    · intro a ha b hb
      exact hcop (hA₁A ha) (hA₁A hb)

/-- On the restricted distinguished set, the canonical signalizer is the
same prescribed signalizer family as before restriction. -/
theorem restr_Dade_signalizer
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A A₁ : Set Γ}
    (ddA : DadeHypothesis G L A)
    (hA₁A : A₁ ⊆ A)
    (hA₁L : L ≤ Subgroup.normalizer A₁)
    (H₁ : Γ → Subgroup Γ)
    (hH₁ : ∀ ⦃a⦄, a ∈ A → DadeSignalizer ddA a = H₁ a) :
    ∀ ⦃a⦄, a ∈ A₁ →
      DadeSignalizer (restr_Dade_hyp ddA hA₁A hA₁L) a = H₁ a := by
  apply def_Dade_signalizer
  intro a ha
  rw [← hH₁ (hA₁A ha)]
  exact Dade_sdprod ddA (hA₁A ha)

/-- Restriction does not change the first Dade support at an index belonging
to the smaller distinguished set. -/
theorem restr_Dade_support1
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A A₁ : Set Γ}
    (ddA : DadeHypothesis G L A)
    (hA₁A : A₁ ⊆ A)
    (hA₁L : L ≤ Subgroup.normalizer A₁) :
    ∀ ⦃a⦄, a ∈ A₁ →
      Dade_support1 (restr_Dade_hyp ddA hA₁A hA₁L) a =
        Dade_support1 ddA a := by
  intro a ha
  unfold Dade_support1
  rw [restr_Dade_signalizer ddA hA₁A hA₁L
    (DadeSignalizer ddA) (fun {_a} _ha ↦ rfl) ha]

/-- The global support of the restricted construction is the union, over the
smaller index set, of the original first supports. -/
theorem restr_Dade_support
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A A₁ : Set Γ}
    (ddA : DadeHypothesis G L A)
    (hA₁A : A₁ ⊆ A)
    (hA₁L : L ≤ Subgroup.normalizer A₁) :
    Dade_support (restr_Dade_hyp ddA hA₁A hA₁L) =
      {x | ∃ a ∈ A₁, x ∈ Dade_support1 ddA a} := by
  ext x
  constructor
  · rintro ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    rwa [restr_Dade_support1 ddA hA₁A hA₁L ha] at hx
  · rintro ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    rwa [restr_Dade_support1 ddA hA₁A hA₁L ha]

/-- The Dade map attached to the restricted hypothesis. -/
noncomputable def restr_Dade
    {Γ : Type u} [Group Γ] [Finite Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A A₁ : Set Γ}
    (ddA : DadeHypothesis G L A)
    (hA₁A : A₁ ⊆ A)
    (hA₁L : L ≤ Subgroup.normalizer A₁) :
    ClassFunction L k →ₗ[k] ClassFunction G k :=
  Dade (restr_Dade_hyp ddA hA₁A hA₁L)

/-- Peterfalvi 2.11, second part: on a class function supported on the
smaller distinguished set, the restricted and original Dade maps agree. -/
theorem restr_DadeE
    {Γ : Type u} [Group Γ] [Finite Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A A₁ : Set Γ}
    (ddA : DadeHypothesis G L A)
    (hA₁A : A₁ ⊆ A)
    (hA₁L : L ≤ Subgroup.normalizer A₁)
    (alpha : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A₁}) :
    restr_Dade ddA hA₁A hA₁L alpha = Dade ddA alpha := by
  let ddA₁ : DadeHypothesis G L A₁ :=
    restr_Dade_hyp ddA hA₁A hA₁L
  apply ClassFunction.ext
  intro x
  by_cases hx₁ : (x : Γ) ∈ Dade_support ddA₁
  · rcases hx₁ with ⟨a, ha, hxa⟩
    have hxa' : (x : Γ) ∈ Dade_support1 ddA a := by
      rwa [restr_Dade_support1 ddA hA₁A hA₁L ha] at hxa
    calc
      restr_Dade ddA hA₁A hA₁L alpha x =
          alpha ⟨a, ddA₁.1.1 ha⟩ := by
        exact DadeE ddA₁ alpha ha x hxa
      _ = alpha ⟨a, ddA.1.1 (hA₁A ha)⟩ := by
        congr 1
      _ = Dade ddA alpha x :=
        (DadeE ddA alpha (hA₁A ha) x hxa').symm
  · have hleft : restr_Dade ddA hA₁A hA₁L alpha x = 0 := by
      exact Dade_eq_zero_of_not_mem ddA₁ alpha x hx₁
    have hright : Dade ddA alpha x = 0 := by
      by_cases hx : (x : Γ) ∈ Dade_support ddA
      · rcases hx with ⟨a, ha, hxa⟩
        have haNot : a ∉ A₁ := by
          intro ha₁
          apply hx₁
          refine ⟨a, ha₁, ?_⟩
          rwa [restr_Dade_support1 ddA hA₁A hA₁L ha₁]
        calc
          Dade ddA alpha x = alpha ⟨a, ddA.1.1 ha⟩ :=
            DadeE ddA alpha ha x hxa
          _ = 0 := ClassFunction.eq_zero_of_mem_supportedOn halpha (by
            simpa using haNot)
      · exact Dade_eq_zero_of_not_mem ddA alpha x hx
    rw [hleft, hright]

end

end Submission.OddOrder.PF
