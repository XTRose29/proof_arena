import Submission.OddOrder.BG.Section03.FrobeniusNilpotentKernel
import Submission.OddOrder.MathlibSupport.ComplementQuotient
import Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy

/-!
# Prime Frobenius kernels after quotienting

This file packages the quotient step used in `BGsection15.v`.  A prime-order
complement remains a prime-order complement after quotienting the normal
kernel factor, while a centralizer contained in the quotienting subgroup
becomes trivial.  The prime Frobenius kernel theorem then makes the quotient
kernel nilpotent.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

/-- A subgroup quotient is canonically isomorphic to the image of the
subgroup in the corresponding ambient quotient. -/
private def subgroupQuotientEquivImage
    {G : Type u} [Group G] (N K : Subgroup G) [N.Normal] :
    (K ⧸ N.subgroupOf K) ≃* K.map (QuotientGroup.mk' N) := by
  letI : (N.subgroupOf K).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : N.Normal) K
  exact QuotientGroup.liftEquiv (N.subgroupOf K)
    ((QuotientGroup.mk' N).subgroupMap_surjective K) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

/-- Let `G = K ⋊ R` be finite and solvable, with `R` of prime order.  If
`N ◁ G` lies in `K`, has order coprime to `R`, and contains every element
of `K` centralized by `R`, then `K / N` is nilpotent.

This is the quotient form of `prime_Frobenius_sol_kernel_nil`: the complement
and its prime cardinality descend to `G / N`, while the coprime quotient
centralizer theorem turns `C_K(R) ≤ N` into a trivial centralizer. -/
theorem primeFrobeniusQuotientKernel_nilpotent
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {K R N : Subgroup G} [K.Normal] [N.Normal]
    (hKR : K.IsComplement' R)
    (hNK : N ≤ K)
    (hcop : Nat.Coprime (Nat.card N) (Nat.card R))
    (hRprime : (Nat.card R).Prime)
    (hcent : centralizerWithin K R ≤ N) :
    Group.IsNilpotent (K ⧸ N.subgroupOf K) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Kq : Subgroup (G ⧸ N) := K.map q
  let Rq : Subgroup (G ⧸ N) := R.map q
  letI : Kq.Normal :=
    Subgroup.Normal.map (inferInstance : K.Normal) q
      (QuotientGroup.mk'_surjective N)
  letI : IsSolvable R := isSolvable_subgroup_of_isSolvable R
  letI : IsSolvable (G ⧸ N) := isSolvable_quotient_of_isSolvable N

  have hcompq : Kq.IsComplement' Rq := by
    simpa [Kq, Rq, q] using hKR.quotient_isComplement hNK
  have hcardRq : Nat.card Rq = Nat.card R := by
    let f : R → Rq := q.subgroupMap R
    have hf : Function.Bijective f :=
      ⟨hKR.quotientRight_subgroupMap_injective hNK,
        q.subgroupMap_surjective R⟩
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have hprimeRq : (Nat.card Rq).Prime := by
    rw [hcardRq]
    exact hRprime

  have hmapCent :=
    map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
      (N := N) (Y := K) (R := R) hNK hcop
  have hmapCentBot : (centralizerWithin K R).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (centralizerWithin K R)).mpr
    simpa [q, QuotientGroup.ker_mk'] using hcent
  have hcentq : centralizerWithin Kq Rq = ⊥ := by
    change centralizerWithin
      (K.map (QuotientGroup.mk' N))
      (R.map (QuotientGroup.mk' N)) = ⊥
    rw [← hmapCent, hmapCentBot]

  have hnilKq : Group.IsNilpotent Kq :=
    prime_Frobenius_sol_kernel_nil hcompq
      (show Kq.Normal from inferInstance)
      (show IsSolvable (G ⧸ N) from inferInstance)
      hprimeRq hcentq
  letI : Group.IsNilpotent Kq := hnilKq
  exact Group.nilpotent_of_mulEquiv
    (subgroupQuotientEquivImage N K).symm

end

end Submission.OddOrder.BG.Section03
