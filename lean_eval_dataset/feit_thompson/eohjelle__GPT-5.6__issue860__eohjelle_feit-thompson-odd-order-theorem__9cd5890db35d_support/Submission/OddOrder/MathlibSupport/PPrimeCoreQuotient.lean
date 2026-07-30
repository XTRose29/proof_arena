import Submission.OddOrder.MathlibSupport.PPrimeCore

/-!
Quotient behavior of the `p'`-core.

Quotienting by the `p'`-core leaves a group with trivial `p'`-core.  This is
the mathlib-facing form of MathComp's `trivg_pcore_quotient` used in Appendix B.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- The `p'`-core of the quotient by the `p'`-core is trivial. -/
theorem pPrimeCore_quotient_self_eq_bot :
    pPrimeCore p (G ⧸ pPrimeCore p G) = ⊥ := by
  let N : Subgroup G := pPrimeCore p G
  letI : N.Normal := by
    dsimp [N]
    infer_instance
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Pbar : Subgroup (G ⧸ N) := pPrimeCore p (G ⧸ N)
  letI : Pbar.Normal := by
    dsimp [Pbar]
    infer_instance
  let P : Subgroup G := Pbar.comap q
  have hNP : N ≤ P := by
    exact QuotientGroup.le_comap_mk' N Pbar
  let f : P →* G ⧸ N := q.comp P.subtype
  have hfker : f.ker = N.subgroupOf P := by
    ext x
    change q (x : G) = 1 ↔ (x : G) ∈ N
    exact QuotientGroup.eq_one_iff (x : G)
  have hfrange : f.range = Pbar := by
    dsimp [f]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    dsimp [P]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N) Pbar
  have hrel : N.relIndex P = Nat.card Pbar := by
    calc
      N.relIndex P = (N.subgroupOf P).index := rfl
      _ = f.ker.index := congrArg (fun H : Subgroup P => H.index) hfker.symm
      _ = Nat.card f.range := Subgroup.index_ker f
      _ = Nat.card Pbar := congrArg (fun H : Subgroup (G ⧸ N) => Nat.card H) hfrange
  have hsubcard : Nat.card (N.subgroupOf P) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hPcoprime : IsPPrimeSubgroup p P := by
    rw [IsPPrimeSubgroup, ← (N.subgroupOf P).card_mul_index, hsubcard]
    change Nat.Coprime p (Nat.card N * N.relIndex P)
    rw [hrel, Nat.coprime_mul_iff_right]
    exact ⟨pPrimeCore_coprime_card, pPrimeCore_coprime_card⟩
  have hPN : P ≤ N := le_pPrimeCore hPcoprime (by
    dsimp [P]
    infer_instance)
  have hP_eq : P = N := le_antisymm hPN hNP
  change Pbar = ⊥
  calc
    Pbar = P.map q :=
      (Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective N) Pbar).symm
    _ = N.map q := congrArg (fun H : Subgroup G => H.map q) hP_eq
    _ = ⊥ := by simp [q]

end Submission.OddOrder.MathlibSupport
