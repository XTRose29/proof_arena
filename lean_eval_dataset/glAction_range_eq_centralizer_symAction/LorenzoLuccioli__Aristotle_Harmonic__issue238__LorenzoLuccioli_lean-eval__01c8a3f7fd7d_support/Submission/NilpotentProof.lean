import Mathlib
import Submission.NilpotentHelper

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Core nilpotent proof via basis rotation
-/

namespace Submission.NilpotentProof

open Submission.NilpotentHelper

variable {R : Type*} [Field R]
  {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]

set_option maxHeartbeats 12800000

/-- Helper: (f^n) 0 = 0 for linear maps. -/
lemma pow_apply_zero (f : Module.End R M) (n : ℕ) : (f ^ n) 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- Helper: if f x = 0, then (g * f)^n x = 0 for n ≥ 1. -/
lemma pow_mul_apply_eq_zero (f g : Module.End R M) (x : M) (hfx : f x = 0) (n : ℕ) (hn : 1 ≤ n) :
    ((g * f) ^ n) x = 0 := by
  induction hn <;> simp_all +decide [pow_succ', mul_assoc]

/-
finRotate.symm applied to 0 gives the last index.
-/
lemma finRotate_symm_zero {n : ℕ} (hn : 0 < n) :
    (finRotate n).symm ⟨0, hn⟩ = ⟨n - 1, by omega⟩ := by
  unfold finRotate; aesop;

/-
finRotate.symm applied to m+1 < n gives m.
-/
lemma finRotate_symm_succ {n m : ℕ} (hm : m + 1 < n) :
    (finRotate n).symm ⟨m + 1, hm⟩ = ⟨m, by omega⟩ := by
  simp +decide [ Equiv.symm_apply_eq, finRotate ];
  rcases n with ( _ | _ | n ) <;> norm_cast;
  simp +decide [ finAddFlip, Fin.add_def ];
  simp +decide [ Fin.ext_iff, finSumFinEquiv ];
  simp +decide [ Fin.addCases ];
  grind

/-- T step: (u_inv * e)(bN j) for j < r. -/
lemma step_in_range
    {n r : ℕ} (hn : 0 < n)
    (bN : Module.Basis (Fin n) R M)
    (e u_inv : Module.End R M)
    (hbN_V : ∀ j : Fin n, (j : ℕ) < r → e (bN j) = bN j)
    (hu_inv : ∀ j : Fin n, u_inv (bN j) = bN ((finRotate n).symm j))
    (j : Fin n) (hj : (j : ℕ) < r) :
    (u_inv * e) (bN j) = bN ((finRotate n).symm j) := by
  show u_inv (e (bN j)) = _
  rw [hbN_V j hj, hu_inv]

/-- T step: (u_inv * e)(bN j) for j ≥ r. -/
lemma step_out_range
    {n r : ℕ}
    (bN : Module.Basis (Fin n) R M)
    (e u_inv : Module.End R M)
    (hbN_W : ∀ j : Fin n, ¬ (j : ℕ) < r → e (bN j) = 0)
    (j : Fin n) (hj : ¬ (j : ℕ) < r) :
    (u_inv * e) (bN j) = 0 := by
  show u_inv (e (bN j)) = _
  rw [hbN_W j hj, map_zero]

/-
Key: T^(m+2)(bN m) = 0 for m < r when n = r+s, s > 0.
-/
lemma key_induction
    {n r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hns : n = r + s)
    (bN : Module.Basis (Fin n) R M)
    (e u_inv : Module.End R M)
    (hbN_V : ∀ j : Fin n, (j : ℕ) < r → e (bN j) = bN j)
    (hbN_W : ∀ j : Fin n, ¬ (j : ℕ) < r → e (bN j) = 0)
    (hu_inv : ∀ j : Fin n, u_inv (bN j) = bN ((finRotate n).symm j))
    (m : ℕ) (hm : m < r) :
    ((u_inv * e) ^ (m + 2)) (bN ⟨m, by omega⟩) = 0 := by
  induction m with
  | zero =>
    -- Need: ((u_inv * e)^2)(bN ⟨0, _⟩) = 0
    -- = (u_inv * e)((u_inv * e)(bN ⟨0, _⟩))
    -- = (u_inv * e)(bN((finRotate n).symm ⟨0, _⟩))
    -- = (u_inv * e)(bN ⟨n-1, _⟩)  [since n-1 ≥ r]
    -- = u_inv(e(bN ⟨n-1, _⟩)) = u_inv(0) = 0
    rw [show (0 + 2) = 2 from rfl, show (2 : ℕ) = 1 + 1 from rfl,
        pow_succ, pow_one]
    show (u_inv * e) (u_inv (e (bN ⟨0, _⟩))) = 0
    rw [hbN_V ⟨0, by omega⟩ (by omega), hu_inv]
    have hfin : (finRotate n).symm ⟨0, by omega⟩ = ⟨n - 1, by omega⟩ :=
      finRotate_symm_zero (by omega)
    rw [hfin]
    show u_inv (e (bN ⟨n - 1, _⟩)) = 0
    rw [hbN_W ⟨n - 1, by omega⟩ (by omega : ¬ (n - 1 : ℕ) < r), map_zero]
  | succ m ih =>
    -- Need: ((u_inv * e)^(m+3))(bN ⟨m+1, _⟩) = 0
    -- = ((u_inv * e)^(m+2))((u_inv * e)(bN ⟨m+1, _⟩))
    -- = ((u_inv * e)^(m+2))(bN ⟨m, _⟩)  [by finRotate_symm_succ]
    -- = 0  [by ih]
    rw [show m + 1 + 2 = (m + 2) + 1 from by omega, pow_succ]
    show ((u_inv * e) ^ (m + 2)) (u_inv (e (bN ⟨m + 1, _⟩))) = 0
    rw [hbN_V ⟨m + 1, by omega⟩ (by omega), hu_inv]
    have hfin : (finRotate n).symm ⟨m + 1, by omega⟩ = ⟨m, by omega⟩ :=
      finRotate_symm_succ (by omega)
    rw [hfin]
    exact ih (by omega)

/-- Core: T^n(bN i) = 0 for all basis vectors. -/
lemma nilpotent_iterate
    {n r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hns : n = r + s)
    (bN : Module.Basis (Fin n) R M)
    (e u_inv : Module.End R M)
    (hbN_V : ∀ j : Fin n, (j : ℕ) < r → e (bN j) = bN j)
    (hbN_W : ∀ j : Fin n, ¬ (j : ℕ) < r → e (bN j) = 0)
    (hu_inv : ∀ j : Fin n, u_inv (bN j) = bN ((finRotate n).symm j))
    (i : Fin n) :
    ((u_inv * e) ^ n) (bN i) = 0 := by
  by_cases hi : (i : ℕ) < r
  · -- Use key_induction and the fact that i+2 ≤ n
    have hkey := key_induction hr hs hns bN e u_inv hbN_V hbN_W hu_inv i.val hi
    have hle : i.val + 2 ≤ n := by omega
    have heq : n = (n - (i.val + 2)) + (i.val + 2) := by omega
    calc ((u_inv * e) ^ n) (bN i)
        = ((u_inv * e) ^ ((n - (i.val + 2)) + (i.val + 2))) (bN i) := by rw [← heq]
      _ = ((u_inv * e) ^ (n - (i.val + 2))) (((u_inv * e) ^ (i.val + 2)) (bN i)) := by
            rw [pow_add]; rfl
      _ = ((u_inv * e) ^ (n - (i.val + 2))) 0 := by rw [hkey]
      _ = 0 := pow_apply_zero _ _
  · -- Use pow_mul_apply_eq_zero
    exact pow_mul_apply_eq_zero e u_inv (bN i) (hbN_W i hi) n (by omega)

end Submission.NilpotentProof
