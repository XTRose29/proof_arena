import Submission.OddOrder.BG.Section10.CorePredicates
import Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial
import Submission.OddOrder.MathlibSupport.Hall
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Bender--Glauberman Section 12: the three tau prime sets

This file ports the definitions and elementary equivariance/disjointness
facts at the start of `BGsection12.v`.  Numerical `p`-rank one and two are
expanded into the corresponding cardinal-rank lower bound together with
exclusion of the next elementary-abelian rank.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open scoped Pointwise

universe u

/-- `BGsection12.v: tau1`: primes outside `sigma(M)` for which `M` has
exact elementary-abelian rank one and which do not divide `|M'|`. -/
def tau1Primes
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ∉ sigmaPrimes M ∧
    HasElementaryAbelianRankAtLeast p 1 M ∧
    ¬ HasElementaryAbelianRankAtLeast p 2 M ∧
    ¬ p ∣ Nat.card (_root_.commutator M)}

/-- `BGsection12.v: tau2`: primes outside `sigma(M)` for which `M` has
exact elementary-abelian rank two. -/
def tau2Primes
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ∉ sigmaPrimes M ∧
    HasElementaryAbelianRankAtLeast p 2 M ∧
    ¬ HasElementaryAbelianRankAtLeast p 3 M}

/-- `BGsection12.v: tau3`: primes outside `sigma(M)` for which `M` has
exact elementary-abelian rank one and which divide `|M'|`. -/
def tau3Primes
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ∉ sigmaPrimes M ∧
    HasElementaryAbelianRankAtLeast p 1 M ∧
    ¬ HasElementaryAbelianRankAtLeast p 2 M ∧
    p ∣ Nat.card (_root_.commutator M)}

/-- `BGsection12.v: sigma_complement`.

The final field is an exact proposition-valued rendering of MathComp's
`group_set (E2 * E1)`: the pointwise product is the carrier of a subgroup.
It is deliberately not replaced by a stronger normalizer condition. -/
structure sigma_complement
    {G : Type u} [Group G] [Finite G]
    (M E E₁ E₂ E₃ : Subgroup G) : Prop where
  E_le_M : E ≤ M
  hall_E : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)
  E₁_le_E : E₁ ≤ E
  hall_E₁ : IsHall (tau1Primes M) (E₁.subgroupOf E)
  E₂_le_E : E₂ ≤ E
  hall_E₂ : IsHall (tau2Primes M) (E₂.subgroupOf E)
  E₃_le_E : E₃ ≤ E
  hall_E₃ : IsHall (tau3Primes M) (E₃.subgroupOf E)
  product_is_group :
    ∃ K : Subgroup G, (K : Set G) = (E₂ : Set G) * (E₁ : Set G)

private theorem hasElementaryAbelianRankAtLeast_map_mulEquiv_iff
    {G : Type u} [Group G] [Finite G]
    {p n : ℕ} (H : Subgroup G) (e : G ≃* G) :
    HasElementaryAbelianRankAtLeast p n
        (H.map e.toMonoidHom) ↔
      HasElementaryAbelianRankAtLeast p n H := by
  constructor
  · rintro ⟨A, hAH, hA⟩
    refine ⟨A.map e.symm.toMonoidHom, ?_,
      hA.map_of_injective e.symm.toMonoidHom e.symm.injective⟩
    have hmapped := Subgroup.map_mono hAH
      (f := e.symm.toMonoidHom)
    simpa [Subgroup.map_map] using hmapped
  · rintro ⟨A, hAH, hA⟩
    exact ⟨A.map e.toMonoidHom, Subgroup.map_mono hAH,
      hA.map_of_injective e.toMonoidHom e.injective⟩

private theorem commutator_natCard_map_mulEquiv
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (e : G ≃* G) :
    Nat.card (_root_.commutator (H.map e.toMonoidHom)) =
      Nat.card (_root_.commutator H) := by
  let eH : H ≃* H.map e.toMonoidHom := e.subgroupMap H
  have hmap : (_root_.commutator H).map eH.toMonoidHom =
      _root_.commutator (H.map e.toMonoidHom) := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr eH.surjective]
    rfl
  rw [← hmap, Subgroup.card_map_of_injective eH.injective]

/-- `BGsection12.v: tau1J`. -/
theorem tau1J
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (x : G) :
    tau1Primes (M.map (MulAut.conj x).toMonoidHom) =
      tau1Primes M := by
  ext p
  simp only [tau1Primes, Set.mem_setOf_eq, sigmaPrimes_conj,
    hasElementaryAbelianRankAtLeast_map_mulEquiv_iff,
    hasElementaryAbelianRankAtLeast_map_mulEquiv_iff,
    commutator_natCard_map_mulEquiv]

/-- `BGsection12.v: tau2J`. -/
theorem tau2J
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (x : G) :
    tau2Primes (M.map (MulAut.conj x).toMonoidHom) =
      tau2Primes M := by
  ext p
  simp only [tau2Primes, Set.mem_setOf_eq, sigmaPrimes_conj,
    hasElementaryAbelianRankAtLeast_map_mulEquiv_iff,
    hasElementaryAbelianRankAtLeast_map_mulEquiv_iff]

/-- `BGsection12.v: tau3J`. -/
theorem tau3J
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (x : G) :
    tau3Primes (M.map (MulAut.conj x).toMonoidHom) =
      tau3Primes M := by
  ext p
  simp only [tau3Primes, Set.mem_setOf_eq, sigmaPrimes_conj,
    hasElementaryAbelianRankAtLeast_map_mulEquiv_iff,
    hasElementaryAbelianRankAtLeast_map_mulEquiv_iff,
    commutator_natCard_map_mulEquiv]

/-- `BGsection12.v: tau2'1`: `tau1(M)` and `tau2(M)` are disjoint. -/
theorem tau2'1
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    tau1Primes M ⊆ (tau2Primes M)ᶜ := by
  intro p hp₁ hp₂
  exact hp₁.2.2.2.1 hp₂.2.2.1

/-- `BGsection12.v: tau3'1`: `tau1(M)` and `tau3(M)` are disjoint. -/
theorem tau3'1
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    tau1Primes M ⊆ (tau3Primes M)ᶜ := by
  intro p hp₁ hp₃
  exact hp₁.2.2.2.2 hp₃.2.2.2.2

/-- `BGsection12.v: tau3'2`: `tau2(M)` and `tau3(M)` are disjoint. -/
theorem tau3'2
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    tau2Primes M ⊆ (tau3Primes M)ᶜ := by
  intro p hp₂ hp₃
  exact hp₃.2.2.2.1 hp₂.2.2.1

end Submission.OddOrder.BG.Section12
