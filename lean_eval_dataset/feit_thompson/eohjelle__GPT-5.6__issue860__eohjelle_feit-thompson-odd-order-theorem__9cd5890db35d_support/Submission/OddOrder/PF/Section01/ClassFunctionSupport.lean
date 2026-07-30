import Mathlib.Algebra.Group.Indicator
import Submission.OddOrder.PF.Section01.ClassFunction

/-!
Support and complement submodules for class functions.

The API in this file is designed for the restriction/complement argument in
Peterfalvi (1.3): equality on a set is expressed by membership of a difference
in a vanishing submodule, while conjugation-stable indicators split every
class function into complementary supported pieces.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

variable {G : Type u} [Group G]

/-- A subset of a group is stable under conjugation. -/
def IsConjStable (A : Set G) : Prop :=
  ∀ x g, x * g * x⁻¹ ∈ A ↔ g ∈ A

namespace IsConjStable

/-- The complement of a conjugation-stable set is conjugation-stable. -/
theorem compl {A : Set G} (hA : IsConjStable A) : IsConjStable Aᶜ := by
  intro x g
  simpa only [Set.mem_compl_iff, not_iff_not] using hA x g

/-- The underlying set of a normal subgroup is stable under conjugation. -/
theorem normal (N : Subgroup G) [N.Normal] : IsConjStable (N : Set G) := by
  intro x g
  constructor
  · intro hxg
    have h := (inferInstance : N.Normal).conj_mem (x * g * x⁻¹) hxg x⁻¹
    simpa [mul_assoc] using h
  · intro hg
    exact (inferInstance : N.Normal).conj_mem g hg x

end IsConjStable

/-- A subset of a group is stable under taking inverses. -/
def IsInvStable (A : Set G) : Prop :=
  ∀ x, x⁻¹ ∈ A ↔ x ∈ A

namespace IsInvStable

/-- The complement of an inverse-stable set is inverse-stable. -/
theorem compl {A : Set G} (hA : IsInvStable A) : IsInvStable Aᶜ := by
  intro x
  simpa only [Set.mem_compl_iff, not_iff_not] using hA x

/-- The underlying set of every subgroup is inverse-stable. -/
theorem subgroup (H : Subgroup G) : IsInvStable (H : Set G) := by
  intro x
  exact H.inv_mem_iff

end IsInvStable

namespace ClassFunction

variable {R : Type v} [Ring R]

/-- Class functions that vanish outside `A`. -/
def supportedOn (A : Set G) : Submodule R (ClassFunction G R) where
  carrier := {f | ∀ x, x ∉ A → f x = 0}
  zero_mem' := by
    intro x hx
    exact zero_apply x
  add_mem' := by
    intro f g hf hg x hx
    simp only [add_apply, hf x hx, hg x hx, add_zero]
  smul_mem' := by
    intro a f hf x hx
    simp only [smul_apply, hf x hx, smul_zero]

/-- Class functions that vanish on `A`. -/
def vanishingOn (A : Set G) : Submodule R (ClassFunction G R) where
  carrier := {f | ∀ x, x ∈ A → f x = 0}
  zero_mem' := by
    intro x hx
    exact zero_apply x
  add_mem' := by
    intro f g hf hg x hx
    simp only [add_apply, hf x hx, hg x hx, add_zero]
  smul_mem' := by
    intro a f hf x hx
    simp only [smul_apply, hf x hx, smul_zero]

/-- Class functions supported on a subgroup. -/
def supportedOnSubgroup (H : Subgroup G) : Submodule R (ClassFunction G R) :=
  supportedOn (H : Set G)

/-- Class functions vanishing on a subgroup. -/
def vanishingOnSubgroup (H : Subgroup G) : Submodule R (ClassFunction G R) :=
  vanishingOn (H : Set G)

@[simp]
theorem mem_supportedOn_iff {A : Set G} {f : ClassFunction G R} :
    f ∈ supportedOn A ↔ ∀ x, x ∉ A → f x = 0 :=
  Iff.rfl

@[simp]
theorem mem_vanishingOn_iff {A : Set G} {f : ClassFunction G R} :
    f ∈ vanishingOn A ↔ ∀ x, x ∈ A → f x = 0 :=
  Iff.rfl

theorem eq_zero_of_mem_supportedOn {A : Set G} {f : ClassFunction G R}
    (hf : f ∈ supportedOn A) {x : G} (hx : x ∉ A) : f x = 0 :=
  (mem_supportedOn_iff.mp hf) x hx

theorem eq_zero_of_mem_vanishingOn {A : Set G} {f : ClassFunction G R}
    (hf : f ∈ vanishingOn A) {x : G} (hx : x ∈ A) : f x = 0 :=
  (mem_vanishingOn_iff.mp hf) x hx

/-- Vanishing on `A` is the same as being supported on its complement. -/
theorem vanishingOn_eq_supportedOn_compl (A : Set G) :
    vanishingOn (R := R) A = supportedOn (R := R) Aᶜ := by
  ext f
  constructor
  · intro hf x hx
    exact (mem_vanishingOn_iff.mp hf) x (by simpa using hx)
  · intro hf x hx
    exact (mem_supportedOn_iff.mp hf) x (by simpa using hx)

/-- A difference vanishes on `A` exactly when its terms agree on `A`. -/
theorem sub_mem_vanishingOn_iff_eqOn {A : Set G} (f g : ClassFunction G R) :
    f - g ∈ vanishingOn A ↔ Set.EqOn f g A := by
  constructor
  · intro h x hx
    have hzero := (mem_vanishingOn_iff.mp h) x hx
    simpa only [sub_apply, sub_eq_zero] using hzero
  · intro h
    apply mem_vanishingOn_iff.mpr
    intro x hx
    simpa only [sub_apply, sub_eq_zero] using h hx

/-- Equality on `A`, in the orientation convenient for rewriting. -/
theorem eqOn_iff_sub_mem_vanishingOn {A : Set G} (f g : ClassFunction G R) :
    Set.EqOn f g A ↔ f - g ∈ vanishingOn A :=
  (sub_mem_vanishingOn_iff_eqOn f g).symm

/-- Subtracting two restricted class functions vanishes on `A` exactly when
the ambient class functions agree there. -/
theorem restrict_sub_mem_vanishingOn_iff_eqOn (H : Subgroup G) (A : Set H)
    (f g : ClassFunction G R) :
    restrict H f - restrict H g ∈ vanishingOn A ↔
      Set.EqOn (fun x : H ↦ f x) (fun x : H ↦ g x) A := by
  constructor
  · intro h x hx
    have h' :=
      (sub_mem_vanishingOn_iff_eqOn (A := A) (restrict H f) (restrict H g)).mp h hx
    simpa only [restrict_apply] using h'
  · intro h
    apply (sub_mem_vanishingOn_iff_eqOn (A := A) (restrict H f) (restrict H g)).mpr
    intro x hx
    simpa only [restrict_apply] using h hx

/-- Cut a class function down to a conjugation-stable set. -/
def indicator (A : Set G) (hA : IsConjStable A) :
    ClassFunction G R →ₗ[R] ClassFunction G R where
  toFun f :=
    ⟨Set.indicator A (fun g ↦ f g), fun x g ↦ by
      by_cases hg : g ∈ A
      · have hxg : x * g * x⁻¹ ∈ A := (hA x g).2 hg
        rw [Set.indicator_of_mem hxg, Set.indicator_of_mem hg, conj_apply]
      · have hxg : x * g * x⁻¹ ∉ A := fun h ↦ hg ((hA x g).1 h)
        rw [Set.indicator_of_notMem hxg, Set.indicator_of_notMem hg]⟩
  map_add' f g := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  map_smul' a f := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]

@[simp]
theorem indicator_apply_of_mem (A : Set G) (hA : IsConjStable A)
    (f : ClassFunction G R) {x : G} (hx : x ∈ A) :
    indicator A hA f x = f x :=
  Set.indicator_of_mem hx _

@[simp]
theorem indicator_apply_of_notMem (A : Set G) (hA : IsConjStable A)
    (f : ClassFunction G R) {x : G} (hx : x ∉ A) :
    indicator A hA f x = 0 :=
  Set.indicator_of_notMem hx _

/-- The indicator piece on `A` is supported on `A`. -/
theorem indicator_mem_supportedOn (A : Set G) (hA : IsConjStable A)
    (f : ClassFunction G R) : indicator A hA f ∈ supportedOn A := by
  apply mem_supportedOn_iff.mpr
  intro x hx
  exact indicator_apply_of_notMem A hA f hx

/-- The two indicator pieces recover the original class function. -/
theorem indicator_add_indicator_compl (A : Set G) (hA : IsConjStable A)
    (f : ClassFunction G R) :
    indicator A hA f + indicator Aᶜ hA.compl f = f := by
  ext x
  by_cases hx : x ∈ A <;> simp [hx]

/-- Explicit support/complement decomposition of a class function. -/
theorem exists_add_supportedOn_compl (A : Set G) (hA : IsConjStable A)
    (f : ClassFunction G R) :
    ∃ fA ∈ supportedOn A, ∃ fAc ∈ supportedOn Aᶜ, fA + fAc = f := by
  refine ⟨indicator A hA f, indicator_mem_supportedOn A hA f,
    indicator Aᶜ hA.compl f, indicator_mem_supportedOn Aᶜ hA.compl f, ?_⟩
  exact indicator_add_indicator_compl A hA f

/-- Functions supported on a set and its complement have trivial
intersection. -/
theorem supportedOn_inf_compl_eq_bot (A : Set G) :
    supportedOn (R := R) A ⊓ supportedOn (R := R) Aᶜ = ⊥ := by
  apply le_antisymm
  · intro f hf
    change f = 0
    apply ext
    intro x
    simp only [zero_apply]
    by_cases hx : x ∈ A
    · exact eq_zero_of_mem_supportedOn hf.2 (by simpa using hx)
    · exact eq_zero_of_mem_supportedOn hf.1 hx
  · exact bot_le

/-- Conjugation-stable indicators show that support on a set and its
complement span all class functions. -/
theorem supportedOn_sup_compl_eq_top (A : Set G) (hA : IsConjStable A) :
    supportedOn (R := R) A ⊔ supportedOn (R := R) Aᶜ = ⊤ := by
  apply top_unique
  intro f hf
  obtain ⟨fA, hfA, fAc, hfAc, hsum⟩ := exists_add_supportedOn_compl A hA f
  exact Submodule.mem_sup.mpr ⟨fA, hfA, fAc, hfAc, hsum⟩

/-- Support on a conjugation-stable set and on its complement are
complementary submodules. -/
theorem isCompl_supportedOn_compl (A : Set G) (hA : IsConjStable A) :
    IsCompl (supportedOn (R := R) A) (supportedOn (R := R) Aᶜ) :=
  IsCompl.of_eq (supportedOn_inf_compl_eq_bot A)
    (supportedOn_sup_compl_eq_top A hA)

/-- The supported and vanishing submodules attached to a
conjugation-stable set are complementary. -/
theorem isCompl_supportedOn_vanishingOn (A : Set G) (hA : IsConjStable A) :
    IsCompl (supportedOn (R := R) A) (vanishingOn (R := R) A) := by
  rw [vanishingOn_eq_supportedOn_compl]
  exact isCompl_supportedOn_compl A hA

/-- Normal subgroups give the canonical support/complement decomposition used
for character restriction arguments. -/
theorem isCompl_supportedOn_normalSubgroup (N : Subgroup G) [N.Normal] :
    IsCompl (supportedOn (R := R) (N : Set G))
      (supportedOn (R := R) (N : Set G)ᶜ) :=
  isCompl_supportedOn_compl (N : Set G) (IsConjStable.normal N)

end ClassFunction

section PairingOrthogonality

variable {k : Type v} [Field k] [Fintype G]

/-- The pairing is zero when the support of the first class function is
inverse-disjoint from the support of the second. -/
theorem characterPairing_eq_zero_of_inverseDisjoint_supportedOn
    {A B : Set G} {f g : ClassFunction G k}
    (hAB : ∀ x, x ∈ A → x⁻¹ ∉ B)
    (hf : f ∈ ClassFunction.supportedOn A)
    (hg : g ∈ ClassFunction.supportedOn B) :
    characterPairing f g = 0 := by
  have hsum : ∑ x : G, f x * g x⁻¹ = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hxA : x ∈ A
    · rw [ClassFunction.eq_zero_of_mem_supportedOn hg (hAB x hxA), mul_zero]
    · rw [ClassFunction.eq_zero_of_mem_supportedOn hf hxA, zero_mul]
  rw [characterPairing, hsum, mul_zero]

/-- Disjoint supports are pairing-orthogonal when the left support is stable
under inverses. -/
theorem characterPairing_eq_zero_of_disjoint_of_invStable_left
    {A B : Set G} {f g : ClassFunction G k}
    (hAB : Disjoint A B) (hA : IsInvStable A)
    (hf : f ∈ ClassFunction.supportedOn A)
    (hg : g ∈ ClassFunction.supportedOn B) :
    characterPairing f g = 0 := by
  apply characterPairing_eq_zero_of_inverseDisjoint_supportedOn
    (hf := hf) (hg := hg)
  intro x hxA hxB
  exact Set.disjoint_left.mp hAB ((hA x).2 hxA) hxB

/-- Disjoint supports are pairing-orthogonal when the right support is stable
under inverses. -/
theorem characterPairing_eq_zero_of_disjoint_of_invStable_right
    {A B : Set G} {f g : ClassFunction G k}
    (hAB : Disjoint A B) (hB : IsInvStable B)
    (hf : f ∈ ClassFunction.supportedOn A)
    (hg : g ∈ ClassFunction.supportedOn B) :
    characterPairing f g = 0 := by
  apply characterPairing_eq_zero_of_inverseDisjoint_supportedOn
    (hf := hf) (hg := hg)
  intro x hxA hxB
  exact Set.disjoint_left.mp hAB hxA ((hB x).1 hxB)

end PairingOrthogonality

end

end Submission.OddOrder.PF
