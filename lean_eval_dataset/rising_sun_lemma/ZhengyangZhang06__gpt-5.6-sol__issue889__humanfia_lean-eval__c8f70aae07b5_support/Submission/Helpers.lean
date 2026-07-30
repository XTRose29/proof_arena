import Mathlib

open Set
open scoped Topology

namespace Submission.Helpers

theorem open_preconnected_eq_Ioo {s : Set ℝ} (hs_open : IsOpen s)
    (hs_nonempty : s.Nonempty) (hs_preconnected : IsPreconnected s)
    (hs_bddBelow : BddBelow s) (hs_bddAbove : BddAbove s) :
    s = Ioo (sInf s) (sSup s) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨l, u, hxlu, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hs_open.mem_nhds hx)
    constructor
    · refine (csInf_lt_iff hs_bddBelow hs_nonempty).2 ?_
      refine ⟨(l + x) / 2, hlu ?_, by linarith [hxlu.1]⟩
      constructor <;> linarith [hxlu.1, hxlu.2]
    · refine (lt_csSup_iff hs_bddAbove hs_nonempty).2 ?_
      refine ⟨(x + u) / 2, hlu ?_, by linarith [hxlu.2]⟩
      constructor <;> linarith [hxlu.1, hxlu.2]
  · exact
      (show IsConnected s from ⟨hs_nonempty, hs_preconnected⟩).Ioo_csInf_csSup_subset
        hs_bddBelow hs_bddAbove

end Submission.Helpers
