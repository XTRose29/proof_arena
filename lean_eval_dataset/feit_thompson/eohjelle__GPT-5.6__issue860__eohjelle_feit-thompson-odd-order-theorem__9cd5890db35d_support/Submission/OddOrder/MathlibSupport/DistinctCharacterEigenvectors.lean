import Mathlib.RepresentationTheory.Basic

/-!
Linear independence of simultaneous eigenvectors carrying distinct finite
group characters.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u v w x

variable {k : Type u} {Q : Type v} {M : Type w} {I : Type x}
variable [Field k] [Group Q] [Fintype Q]
variable [AddCommGroup M] [Module k M]

/-- The sum of a nontrivial unit-valued character of a finite group is zero. -/
theorem sum_unitsCharacter_eq_zero_of_ne_one
    (chi : Q →* kˣ) (hchi : chi ≠ 1) :
    ∑ q : Q, (chi q : k) = 0 := by
  have hexists : ∃ a : Q, chi a ≠ 1 := by
    by_contra h
    apply hchi
    apply MonoidHom.ext
    intro a
    simpa using not_exists.mp h a
  obtain ⟨a, ha⟩ := hexists
  have ha' : (chi a : k) ≠ 1 := by
    intro h
    apply ha
    apply Units.ext
    simpa using h
  let S : k := ∑ q : Q, (chi q : k)
  have htranslate : (chi a : k) * S = S := by
    calc
      (chi a : k) * S = ∑ q : Q, (chi (a * q) : k) := by
        simp [S, Finset.mul_sum]
      _ = ∑ q : Q, (chi q : k) := by
        exact Function.Bijective.sum_comp (Group.mulLeft_bijective a)
          (fun q : Q ↦ (chi q : k))
      _ = S := rfl
  have hfactor : ((chi a : k) - 1) * S = 0 := by
    calc
      ((chi a : k) - 1) * S = (chi a : k) * S - S := by ring
      _ = 0 := by rw [htranslate, sub_self]
  exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr ha')

/-- Simultaneous eigenvectors for pairwise distinct one-dimensional
characters of a finite group are linearly independent. -/
theorem linearIndependent_of_distinct_unitsCharacters
    [Fintype I]
    (rho : Representation k Q M)
    (chi : I → Q →* kˣ) (hchi : Function.Injective chi)
    (v : I → M) (hv : ∀ i, v i ≠ 0)
    (heigen : ∀ i q, rho q (v i) = (chi i q : k) • v i)
    (hcard : (Fintype.card Q : k) ≠ 0) :
    LinearIndependent k v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let P : Module.End k M :=
    ∑ q : Q, ((chi i q : k)⁻¹) • rho q
  have hweight (j : I) :
      ∑ q : Q, (chi i q : k)⁻¹ * (chi j q : k) =
        if j = i then (Fintype.card Q : k) else 0 := by
    by_cases hji : j = i
    · subst j
      simp
    · have hnontrivial : (chi i)⁻¹ * chi j ≠ 1 := by
        intro h
        apply hji
        apply hchi
        apply MonoidHom.ext
        intro q
        have hq := DFunLike.congr_fun h q
        change (chi i q)⁻¹ * chi j q = 1 at hq
        exact (inv_mul_eq_one.mp hq).symm
      rw [if_neg hji]
      simpa using sum_unitsCharacter_eq_zero_of_ne_one
        ((chi i)⁻¹ * chi j) hnontrivial
  have hP (j : I) :
      P (v j) =
        (if j = i then (Fintype.card Q : k) else 0) • v j := by
    calc
      P (v j) =
          ∑ q : Q, ((chi i q : k)⁻¹ * (chi j q : k)) • v j := by
        simp [P, heigen, mul_smul]
      _ = (∑ q : Q, (chi i q : k)⁻¹ * (chi j q : k)) • v j := by
        rw [Finset.sum_smul]
      _ = (if j = i then (Fintype.card Q : k) else 0) • v j := by
        rw [hweight]
  have hprojected : ∑ j : I, c j • P (v j) = 0 := by
    calc
      ∑ j : I, c j • P (v j) = P (∑ j : I, c j • v j) := by
        simp
      _ = 0 := by rw [hc, map_zero]
  rw [Finset.sum_eq_single i] at hprojected
  · simp only [hP, if_pos, smul_smul] at hprojected
    have hcoef : c i * (Fintype.card Q : k) = 0 :=
      (smul_eq_zero.mp hprojected).resolve_right (hv i)
    exact (mul_eq_zero.mp hcoef).resolve_right hcard
  · intro j _ hji
    rw [hP, if_neg hji]
    simp
  · simp

end Submission.OddOrder.MathlibSupport
