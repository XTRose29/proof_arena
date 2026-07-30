import Submission.WielandtJoin

namespace Submission.Helpers

open scoped Pointwise

/-- Wielandt's local-subnormality hypothesis restricts to every subgroup
containing the subgroup under consideration. -/
theorem localSubnormal_restrict
    {G : Type*} [Group G] {H M : Subgroup G}
    (hHM : H ≤ M)
    (hlocal : ∀ g : G,
      (H.subgroupOf (H ⊔ (MulAut.conj g) • H)).IsSubnormal) :
    ∀ g : M,
      ((H.subgroupOf M).subgroupOf
        ((H.subgroupOf M) ⊔
          (MulAut.conj g) • (H.subgroupOf M))).IsSubnormal := by
  intro g
  let J : Subgroup G := H ⊔ (MulAut.conj (g : G)) • H
  have hconjle : (MulAut.conj (g : G)) • H ≤ M :=
    Subgroup.conj_smul_le_of_le hHM g
  have hJle : J ≤ M :=
    sup_le hHM hconjle
  have hJsub :
      J.subgroupOf M =
        (H.subgroupOf M) ⊔
          (MulAut.conj g) • (H.subgroupOf M) := by
    dsimp only [J]
    rw [Subgroup.subgroupOf_sup hHM hconjle,
      ← Subgroup.conj_smul_subgroupOf hHM g]
  have hs : (H.subgroupOf J).IsSubnormal :=
    hlocal (g : G)
  have hpull :=
    hs.comap (Subgroup.subgroupOfEquivOfLe hJle).toMonoidHom
  have heq :
      (H.subgroupOf J).comap
          (Subgroup.subgroupOfEquivOfLe hJle).toMonoidHom =
        (H.subgroupOf M).subgroupOf (J.subgroupOf M) := by
    ext z
    simp [Subgroup.mem_subgroupOf]
  rw [← hJsub]
  rwa [heq] at hpull

end Submission.Helpers
