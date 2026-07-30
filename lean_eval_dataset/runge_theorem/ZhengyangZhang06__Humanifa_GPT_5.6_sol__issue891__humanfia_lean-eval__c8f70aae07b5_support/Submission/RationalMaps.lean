import Submission.RationalMapSmul

noncomputable section

namespace Submission.Helpers

/-- The complex vector space of continuous functions on `K` which are represented
by one rational function with no pole on `K`. -/
def rationalMaps (K : Set ℂ) : Submodule ℂ C(K, ℂ) where
  carrier := IsRationalMap K
  zero_mem' := isRationalMap_zero K
  add_mem' := isRationalMap_add K
  smul_mem' := isRationalMap_smul K

end Submission.Helpers
