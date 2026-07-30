import Submission.OddOrder.BG.Section07.NormedSubgroups

/-!
# Bender--Glauberman, Section 7: the centralizer core action

This is the setup and observation immediately preceding Lemma 7.1 in
`BGsection7.v`: the prime-complement core of `C_G(A)` acts by conjugation on
the maximal `q`-subgroups normalized by `A`.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The prime-complement core `K = O_{pi(A)'}(C_G(A))`. -/
def centralPrimeComplementCore (A : Subgroup G) : Subgroup G :=
  primeSetCore (primeSupport (Nat.card A))ᶜ
    (Subgroup.centralizer (A : Set G))

/-- A prime-set core lies in its ambient subgroup. -/
theorem primeSetCore_le (pi : Set ℕ) (X : Subgroup G) :
    primeSetCore pi X ≤ X := by
  rw [primeSetCore]
  exact sSup_le fun _ hK => hK.1

/-- The prime-set core is normal in its ambient subgroup. -/
theorem primeSetCore_normal (pi : Set ℕ) (X : Subgroup G) :
    ((primeSetCore pi X).subgroupOf X).Normal := by
  have hcoreX : primeSetCore pi X ≤ X := primeSetCore_le pi X
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hcoreX]
  rw [primeSetCore, sSup_eq_iSup']
  let S : Set (Subgroup G) :=
    {K : Subgroup G |
      K ≤ X ∧ (K.subgroupOf X).Normal ∧ IsPiNumber pi (Nat.card K)}
  change X ≤ Subgroup.normalizer
    ((⨆ K : S, (K : Subgroup G) : Subgroup G) : Set G)
  refine (show X ≤ ⨅ K : S, Subgroup.normalizer (K : Subgroup G) by
    intro x hx
    rw [Subgroup.mem_iInf]
    intro K
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer K.property.1).mp
      K.property.2.1 hx) |>.trans
        (Subgroup.iInf_normalizer_le_normalizer_iSup
          (fun K : S => (K : Subgroup G)))

/-- The specialized setup fact `K <| C_G(A)` from `BGsection7.v`. -/
theorem centralPrimeComplementCore_normal (A : Subgroup G) :
    ((centralPrimeComplementCore A).subgroupOf
      (Subgroup.centralizer (A : Set G))).Normal :=
  primeSetCore_normal _ _

/-- `BGsection7.v: cent_core_acts_max_norm`.  Every element of the centralizer
prime-complement core preserves the family of maximal `q`-subgroups
normalized by `A` under conjugation. -/
theorem cent_core_acts_max_norm (q : ℕ) (A Q : Subgroup G) (x : G)
    (hx : x ∈ centralPrimeComplementCore A) :
    Q.map (MulAut.conj x).toMonoidHom ∈
        max_normed_pgroups (A : Set G) ({q} : Set ℕ) ↔
      Q ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) := by
  have hxC : x ∈ Subgroup.centralizer (A : Set G) :=
    primeSetCore_le _ _ hx
  have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G) hxC
  exact norm_acts_max_norm A Q ({q} : Set ℕ) x hxN

end Submission.OddOrder.BG.Section07
