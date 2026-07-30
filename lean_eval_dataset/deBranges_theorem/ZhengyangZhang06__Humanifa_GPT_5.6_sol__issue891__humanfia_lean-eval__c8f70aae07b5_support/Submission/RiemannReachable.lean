import Submission.RiemannApproximation

namespace Submission

inductive NormalizedDiskEmbedding.ReachableFrom
    {U : Set ℂ} {x : ℂ} (E₀ : NormalizedDiskEmbedding U x) :
    NormalizedDiskEmbedding U x → Type
  | refl : E₀.ReachableFrom E₀
  | step {E F : NormalizedDiskEmbedding U x} :
      E₀.ReachableFrom E → E.OmittedPointStep F → E₀.ReachableFrom F

def ReachableNormalizedDiskEmbedding
    {U : Set ℂ} {x : ℂ} (E₀ : NormalizedDiskEmbedding U x) :=
  {E : NormalizedDiskEmbedding U x // Nonempty (E₀.ReachableFrom E)}

instance {U : Set ℂ} {x : ℂ} (E₀ : NormalizedDiskEmbedding U x) :
    Nonempty (ReachableNormalizedDiskEmbedding E₀) :=
  ⟨⟨E₀, ⟨NormalizedDiskEmbedding.ReachableFrom.refl⟩⟩⟩

end Submission
