import Submission.OddOrder.PF.Section14.FTType2Exclusion
import Submission.OddOrder.BG.Section07.MinimalCounterexample

/-!
# The Feit--Thompson odd-order theorem

The exceptional pair supplied by Peterfalvi (8.8) is oriented by the orders
of its two cyclic factors.  The type-II results of Section 14 then rule out
that orientation.  The all-type-I alternative was already excluded in
Section 12, so no minimal simple odd-order counterexample exists.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped Classical

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance (priority := 10) oddOrderTheoremFintype
    (X : Type*) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-- The contradiction attached to an exceptional pair after orienting its
two cyclic factors by cardinality. -/
private theorem oriented_typeP_pair_contradiction
    {S T W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pairST : typeP_pair S T W W₁ W₂ defW)
    (hlt : Nat.card W₁ < Nat.card W₂) : False := by
  classical
  let xdefW : IsInternalDirectProductIn W₂ W₁ W := defW.swap
  let pairTS : typeP_pair T S W W₂ W₁ xdefW :=
    typeP_pair_sym S T W W₁ W₂ defW xdefW pairST

  obtain ⟨U, StypeP⟩ := typeP_pairW S T W W₁ W₂ defW pairST
  obtain ⟨V, TtypeP⟩ := typeP_pairW T S W W₂ W₁ xdefW pairTS
  let ctxS : FTTypePSetupContext S U W W₁ W₂ defW :=
    ⟨pairST.S_maximal, StypeP⟩
  let ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW :=
    ⟨pairST.T_maximal, TtypeP⟩

  have Stype2 : FTtype S = 2 := FTtypeP_max_typeII ctxS hlt
  have Ttype2 : FTtype T = 2 := FTtypeP_min_typeII ctxS ctxT hlt
  have hTypeIIS :=
    compl_of_typeII S U W W₁ W₂ defW ctxS.maxS ctxS.StypeP Stype2
  have hTypeIIT :=
    compl_of_typeII T V W W₂ W₁ xdefW ctxT.maxS ctxT.StypeP Ttype2
  have hUne : U ≠ ⊥ := hTypeIIS.1.2.1
  have hVne : V ≠ ⊥ := hTypeIIT.1.2.1

  have hUS : U ≤ S := by
    exact le_sup_left.trans (Ptype_Fcore_sdprod ctxS.ptypeCtx).2.1
  have hVT : V ≤ T := by
    exact le_sup_left.trans (Ptype_Fcore_sdprod ctxT.ptypeCtx).2.1
  have hNUproper : Subgroup.normalizer (U : Set G) < ⊤ :=
    mFT_norm_proper U hUne (hUS.trans_lt (mmax_proper ctxS.maxS))
  have hNVproper : Subgroup.normalizer (V : Set G) < ⊤ :=
    mFT_norm_proper V hVne (hVT.trans_lt (mmax_proper ctxT.maxS))

  obtain ⟨L, maxL, sNUL⟩ :=
    mmax_exists (Subgroup.normalizer (U : Set G)) hNUproper
  obtain ⟨M, maxM, sNVM⟩ :=
    mmax_exists (Subgroup.normalizer (V : Set G)) hNVproper
  have maxNU_L : L ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (U : Set G) : Set G) :=
    ⟨maxL, sNUL⟩
  have maxNV_M : M ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (V : Set G) : Set G) :=
    ⟨maxM, sNVM⟩

  obtain ⟨frobL, sUH, _⟩ :=
    FTtypeII_support_facts ctxS T L Stype2 pairST maxNU_L
  obtain ⟨frobM, sVH, _⟩ :=
    FTtypeII_support_facts ctxT S M Ttype2 pairTS maxNV_M
  let fctxL : FTFrobeniusContext L := ⟨maxL, frobL⟩
  let fctxM : FTFrobeniusContext M := ⟨maxM, frobM⟩
  have Ltype1 : FTtype L = 1 := FT_Frobenius_type1 fctxL
  have Mtype1 : FTtype M = 1 := FT_Frobenius_type1 fctxM

  obtain ⟨tau₁L, cohL⟩ := FTtype1_coherence L maxL Ltype1
  obtain ⟨tau₁M, cohM⟩ := FTtype1_coherence M maxM Mtype1
  let typeCtxL : FTType1Context L := ⟨maxL, Ltype1⟩
  let typeCtxM : FTType1Context M := ⟨maxM, Mtype1⟩
  obtain ⟨phi, Lphi, phi1⟩ := FTtype1_ref_irr typeCtxL
  obtain ⟨psi, Mpsi, psi1⟩ := FTtype1_ref_irr typeCtxM

  exact FTtype2_exclusion ctxS ctxT pairST hlt
    maxNU_L maxL sNUL sUH frobL Ltype1 tau₁L phi cohL Lphi
      (by simpa only [FTtype1CoreIndex] using phi1)
    maxNV_M maxM sNVM frobM Mtype1 tau₁M psi cohM Mpsi
      (by simpa only [FTtype1CoreIndex] using psi1)

/-- `PFsection14.v: no_minSimple_odd_group`.

There is no finite minimal simple counterexample of odd order. -/
theorem no_minSimple_odd_group
    (G : Type) [Group G] [Finite G] [IsMinSimpleOddGroup G] : False := by
  classical
  rcases FTtypeP_pair_cases (G := G) with hall | hpair
  · exact not_all_FTtype1 hall
  · obtain ⟨S, T, _, W, W₁, W₂, defW, pairST⟩ := hpair
    by_cases hlt : Nat.card W₁ < Nat.card W₂
    · exact oriented_typeP_pair_contradiction pairST hlt
    · have hrev : Nat.card W₂ < Nat.card W₁ := by
        have hne : Nat.card W₁ ≠ Nat.card W₂ :=
          pairST.cyclic_ti.factor_card_ne
        omega
      let xdefW : IsInternalDirectProductIn W₂ W₁ W := defW.swap
      let pairTS : typeP_pair T S W W₂ W₁ xdefW :=
        typeP_pair_sym S T W W₁ W₂ defW xdefW pairST
      exact oriented_typeP_pair_contradiction pairTS hrev

/-- `PFsection14.v: Feit_Thompson`.

Every finite group of odd order is solvable. -/
theorem Feit_Thompson
    {G : Type} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) : IsSolvable G :=
  minSimpleOdd_ind no_minSimple_odd_group hodd

/-- `PFsection14.v: simple_odd_group_prime`.

A finite simple group of odd order has prime order. -/
theorem simple_odd_group_prime
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hodd : Odd (Nat.card G)) : (Nat.card G).Prime :=
  minSimpleOdd_prime no_minSimple_odd_group hodd

end

end Submission.OddOrder.PF
