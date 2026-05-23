import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Helper lemmas for the nilpotent-from-idempotent result
-/

namespace Submission.NilpotentHelper

variable {R : Type*} [Field R]
  {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]

set_option maxHeartbeats 6400000

/-
An idempotent acts as identity on its range.
-/
lemma idem_eq_on_range (e : Module.End R M) (he : e * e = e)
    (x : M) (hx : x ∈ LinearMap.range e) : e x = x := by
  obtain ⟨ y, rfl ⟩ := hx; simpa using LinearMap.congr_fun he y;

/-
An idempotent acts as zero on its kernel.
-/
lemma idem_eq_zero_on_ker (e : Module.End R M) (he : e * e = e)
    (x : M) (hx : x ∈ LinearMap.ker e) : e x = 0 := by
  exact hx

/-
If e ≠ 0, then range e is nontrivial (has positive finrank).
-/
lemma range_nontrivial_of_ne_zero (e : Module.End R M) (he : e * e = e)
    (hne0 : e ≠ 0) : 0 < Module.finrank R (LinearMap.range e) := by
  contrapose! hne0;
  simp_all +decide [ LinearMap.ext_iff, Submodule.eq_bot_iff ]

/-
If e ≠ 1, then ker e is nontrivial (has positive finrank).
-/
lemma ker_nontrivial_of_ne_one (e : Module.End R M) (he : e * e = e)
    (hne1 : e ≠ 1) : 0 < Module.finrank R (LinearMap.ker e) := by
  by_contra h_contra;
  -- If finrank (ker e) = 0, then ker e = ⊥, so e is injective by the rank-nullity theorem.
  have h_inj : Function.Injective ⇑e := by
    exact LinearMap.ker_eq_bot.mp ( Submodule.finrank_eq_zero.mp ( le_antisymm ( le_of_not_gt h_contra ) ( Nat.zero_le _ ) ) );
  exact hne1 ( LinearMap.ext fun x => h_inj <| by simpa using LinearMap.congr_fun he x )

/-- Combined basis from complementary submodules. -/
noncomputable def combinedBasis {V W : Submodule R M} (hc : IsCompl V W)
    {r s : ℕ} (hr : Module.finrank R V = r) (hs : Module.finrank R W = s) :
    Module.Basis (Fin (r + s)) R M :=
  let bV := (Module.finBasis R V).reindex (finCongr hr)
  let bW := (Module.finBasis R W).reindex (finCongr hs)
  let bProd : Module.Basis (Fin r ⊕ Fin s) R (V × W) := bV.prod bW
  let bM : Module.Basis (Fin r ⊕ Fin s) R M :=
    bProd.map (Submodule.prodEquivOfIsCompl V W hc)
  bM.reindex finSumFinEquiv

lemma combinedBasis_mem_left {V W : Submodule R M} (hc : IsCompl V W)
    {r s : ℕ} (hr : Module.finrank R V = r) (hs : Module.finrank R W = s)
    (i : Fin (r + s)) (hi : i.val < r) :
    (combinedBasis hc hr hs i : M) ∈ V := by
  unfold combinedBasis;
  simp +decide [ hi, finSumFinEquiv ];
  simp +decide [ Fin.addCases, hi ]

lemma combinedBasis_mem_right {V W : Submodule R M} (hc : IsCompl V W)
    {r s : ℕ} (hr : Module.finrank R V = r) (hs : Module.finrank R W = s)
    (i : Fin (r + s)) (hi : r ≤ i.val) :
    (combinedBasis hc hr hs i : M) ∈ W := by
  unfold combinedBasis;
  cases h : finSumFinEquiv.symm i <;> simp_all +decide [ Function.comp ];
  replace h := congr_arg ( fun x => x.elim ( fun x => x.val ) fun x => r + x.val ) h ; simp_all +decide [ finSumFinEquiv ];
  simp_all +decide [ Fin.addCases ];
  grind

end Submission.NilpotentHelper
