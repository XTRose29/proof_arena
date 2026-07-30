import Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient
import Submission.OddOrder.MathlibSupport.Solvability

/-!
Elementary-abelian subgroups lift across the prime-complement core.

This is the subgroup-existence content of MathComp's
`p_rank_p'quotient`: the inverse image of an elementary-abelian `p`-group
has a complement to the normal `p'`-kernel, and that complement maps
isomorphically to the given quotient subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

noncomputable section

universe u

/-- Quotienting a finite solvable group by its `p'`-core cannot create an
elementary-abelian subgroup of rank three at `p`. -/
theorem no_elementaryAbelian_rank_three_quotient_pPrimeCore
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (_hsol : IsSolvable G)
    (hRank : ¬ ∃ E : Subgroup G,
      IsElementaryAbelianOfRank p 3 E) :
    ¬ ∃ E : Subgroup (G ⧸ pPrimeCore p G),
      IsElementaryAbelianOfRank p 3 E := by
  classical
  rintro ⟨E, hE⟩
  let N : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let L : Subgroup G := E.comap q
  have hNL : N ≤ L := by
    dsimp [L, q]
    exact QuotientGroup.le_comap_mk' N E
  let NL : Subgroup L := N.subgroupOf L
  letI : NL.Normal := by
    dsimp [NL]
    exact (inferInstance : N.Normal).subgroupOf L
  let f : L →* E :=
    (q.comp L.subtype).codRestrict E (fun x ↦ x.property)
  have hfker : f.ker = NL := by
    ext x
    constructor
    · intro hx
      have hfx : f x = 1 := hx
      have hxq : q (x : G) = 1 := congrArg Subtype.val hfx
      change (x : L) ∈ NL
      change (x : G) ∈ N
      exact (QuotientGroup.eq_one_iff (x : G)).mp hxq
    · intro hx
      change (x : G) ∈ N at hx
      change f x = 1
      apply Subtype.ext
      change q (x : G) = 1
      exact (QuotientGroup.eq_one_iff (x : G)).mpr hx
  have hfsurj : Function.Surjective f := by
    intro e
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (e : G ⧸ N)
    let gL : L := ⟨g, by
      change q g ∈ E
      rw [hg]
      exact e.property⟩
    refine ⟨gL, ?_⟩
    apply Subtype.ext
    exact hg
  have hNLcard : Nat.card NL = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
  have hNLindex : NL.index = Nat.card E := by
    calc
      NL.index = f.ker.index := congrArg Subgroup.index hfker.symm
      _ = Nat.card f.range := Subgroup.index_ker f
      _ = Nat.card E := by
        rw [MonoidHom.range_eq_top.mpr hfsurj]
        simp
  have hcop : (Nat.card NL).Coprime NL.index := by
    rw [hNLcard, hNLindex, hE.card_eq]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).symm.pow_right 3
  obtain ⟨C, hcomp⟩ := NL.exists_right_complement'_of_coprime hcop
  have hCcard : Nat.card C = p ^ 3 := by
    calc
      Nat.card C = NL.index := hcomp.symm.index_eq_card.symm
      _ = Nat.card E := hNLindex
      _ = p ^ 3 := hE.card_eq
  let fC : C →* E := f.comp C.subtype
  have hfCinj : Function.Injective fC := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro x hx
      have hxNL : (x : L) ∈ NL := by
        rw [← hfker]
        exact hx
      have hxbot : (x : L) ∈ (⊥ : Subgroup L) :=
        hcomp.disjoint.symm.le_bot ⟨x.property, hxNL⟩
      rw [Subgroup.mem_bot] at hxbot ⊢
      exact Subtype.ext hxbot
    · exact bot_le
  letI : IsMulCommutative E := hE.commutative
  have hCelem : IsElementaryAbelianOfRank p 3 C :=
    { isPGroup := IsPGroup.of_card (n := 3) hCcard
      commutative := isMulCommutative_iff.mpr (fun x y ↦ by
        apply hfCinj
        simp only [map_mul]
        exact mul_comm _ _)
      pow_eq_one := fun x ↦ by
        apply hfCinj
        rw [map_pow, map_one]
        exact hE.pow_eq_one (fC x)
      card_eq := hCcard }
  apply hRank
  exact ⟨C.map L.subtype,
    hCelem.map_of_injective L.subtype L.subtype_injective⟩

end

end Submission.OddOrder.MathlibSupport
