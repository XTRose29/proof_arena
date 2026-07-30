import Submission.Escaping

open LeanEval.ComplexAnalysis.FatouJuliaProblem

namespace Submission

theorem julia_cantor_dichotomy (c : ℂ) :
    (c ∈ Mandelbrot → IsConnected (FilledJulia c)) ∧
    (c ∉ Mandelbrot → Nonempty ((FilledJulia c) ≃ₜ (ℕ → Bool))) := by
  exact ⟨Connected.isConnected_filledJulia_of_mem_mandelbrot,
    Escaping.homeomorph_cantor_of_not_mem_mandelbrot⟩

end Submission
