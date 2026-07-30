import Submission.Helpers
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Filter Function

namespace Submission

lemma differentiableOn_iteratedDeriv_of_isOpen
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa using hf
  | succ n hn =>
      rw [iteratedDeriv_succ]
      exact hn.deriv hU

lemma tendstoLocallyUniformlyOn_iteratedDeriv
    {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hlocal : TendstoLocallyUniformlyOn F f atTop U)
    (hF : ∀ j : ℕ, DifferentiableOn ℂ (F j) U) (n : ℕ) :
    TendstoLocallyUniformlyOn
      (fun j ↦ iteratedDeriv n (F j)) (iteratedDeriv n f) atTop U := by
  induction n with
  | zero => simpa using hlocal
  | succ n hn =>
      have hderiv := hn.deriv
        (Eventually.of_forall fun j ↦
          differentiableOn_iteratedDeriv_of_isOpen hU (hF j) n) hU
      simpa only [Function.comp_def, iteratedDeriv_succ] using hderiv

lemma tendsto_taylorCoeff_of_locallyUniformlyOn
    {U : Set ℂ} (hU : IsOpen U) (hzero : (0 : ℂ) ∈ U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hlocal : TendstoLocallyUniformlyOn F f atTop U)
    (hF : ∀ j : ℕ, DifferentiableOn ℂ (F j) U) (n : ℕ) :
    Tendsto (fun j ↦ taylorCoeff (F j) n) atTop
      (nhds (taylorCoeff f n)) := by
  have hcoeff :=
    (tendstoLocallyUniformlyOn_iteratedDeriv hU hlocal hF n).tendsto_at hzero
  simpa only [taylorCoeff] using hcoeff.div_const (n.factorial : ℂ)

end Submission
