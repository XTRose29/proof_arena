import Submission.SylowBlocks

namespace Submission.Helpers

/-- A proper subnormal subgroup is properly contained in its ambient
normalizer. -/
theorem lt_normalizer_of_isSubnormal {G : Type*} [Group G]
    {H : Subgroup G} (hH : H.IsSubnormal) (hHtop : H ≠ ⊤) :
    H < Subgroup.normalizer (H : Set G) := by
  rcases Subgroup.IsSubnormal.iff_eq_top_or_exists.mp hH with htop |
      ⟨K, hHK, -, hnormal⟩
  · exact (hHtop htop).elim
  · have hKle : K ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHK.le).mp hnormal
    exact hHK.trans_le hKle

/-- The iterated normalizer of `H` inside `M`, kept as a subgroup of the
ambient group. -/
def normalizerTower {G : Type*} [Group G]
    (H M : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => M ⊓ Subgroup.normalizer (normalizerTower H M n : Set G)

@[simp]
theorem normalizerTower_zero {G : Type*} [Group G]
    (H M : Subgroup G) :
    normalizerTower H M 0 = H :=
  rfl

theorem normalizerTower_succ {G : Type*} [Group G]
    (H M : Subgroup G) (n : ℕ) :
    normalizerTower H M (n + 1) =
      M ⊓ Subgroup.normalizer (normalizerTower H M n : Set G) :=
  rfl

theorem normalizerTower_le {G : Type*} [Group G]
    {H M : Subgroup G} (hHM : H ≤ M) (n : ℕ) :
    normalizerTower H M n ≤ M := by
  cases n with
  | zero => exact hHM
  | succ n => exact inf_le_left

theorem normalizerTower_mono {G : Type*} [Group G]
    {H M : Subgroup G} (hHM : H ≤ M) :
    Monotone (normalizerTower H M) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [normalizerTower_succ]
  exact le_inf (normalizerTower_le hHM n)
    (normalizerTower H M n).le_normalizer

theorem normalizerTower_subgroupOf_succ {G : Type*} [Group G]
    {H M : Subgroup G} (hHM : H ≤ M) (n : ℕ) :
    (normalizerTower H M (n + 1)).subgroupOf M =
      Subgroup.normalizer
        ((normalizerTower H M n).subgroupOf M : Set M) := by
  rw [normalizerTower_succ, inf_comm,
    Subgroup.inf_subgroupOf_right,
    Subgroup.subgroupOf_normalizer_eq (normalizerTower_le hHM n)]

theorem normalizerTower_lt_one_of_ne {G : Type*} [Group G]
    {H M : Subgroup G} (hHM : H ≤ M)
    (hH : (H.subgroupOf M).IsSubnormal) (hne : H ≠ M) :
    H < normalizerTower H M 1 := by
  have hle : H ≤ normalizerTower H M 1 := by
    rw [normalizerTower_succ, normalizerTower_zero]
    exact le_inf hHM H.le_normalizer
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hsubEq :
      H.subgroupOf M =
        (normalizerTower H M 1).subgroupOf M :=
    congr_arg (Subgroup.subgroupOf · M) heq
  rw [normalizerTower_subgroupOf_succ hHM, normalizerTower_zero] at hsubEq
  have hproper :
      H.subgroupOf M ≠ ⊤ := by
    intro htop
    apply hne
    exact le_antisymm hHM (Subgroup.subgroupOf_eq_top.mp htop)
  exact (lt_normalizer_of_isSubnormal hH hproper).ne hsubEq

theorem normalizerTower_eventually_stable {G : Type*} [Group G] [Finite G]
    {H M : Subgroup G} (hHM : H ≤ M) :
    ∃ n, normalizerTower H M n = normalizerTower H M (n + 1) := by
  classical
  by_contra h
  have hne : ∀ n, normalizerTower H M n ≠
      normalizerTower H M (n + 1) :=
    fun n hn => h ⟨n, hn⟩
  have hstrict : StrictMono (normalizerTower H M) :=
    strictMono_nat_of_lt_succ fun n =>
      lt_of_le_of_ne
        (normalizerTower_mono hHM (Nat.le_succ n))
        (hne n)
  exact not_injective_infinite_finite (normalizerTower H M) hstrict.injective

/-- A proper subnormal subgroup of a finite group has a maximal proper
normal overgroup.  Maximality is only asserted among normal overgroups
which still contain `H`. -/
theorem exists_maximal_normal_overgroup
    {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : H.IsSubnormal) (hHtop : H ≠ ⊤) :
    ∃ N : Subgroup G,
      H ≤ N ∧ N < ⊤ ∧ N.Normal ∧
        ∀ K : Subgroup G, H ≤ K → N ≤ K → K < ⊤ → K.Normal → K = N := by
  classical
  obtain ⟨N₀, hN₀normal, hHN₀, hN₀top⟩ :=
    hH.exists_normal_and_le_and_lt_top_of_ne hHtop
  let P := fun N : Subgroup G => H ≤ N ∧ N < ⊤ ∧ N.Normal
  obtain ⟨N, hN₀N, hNmax⟩ :=
    Finite.exists_le_maximal (p := P) (a := N₀)
      ⟨hHN₀, hN₀top, hN₀normal⟩
  refine
    ⟨N, hHN₀.trans hN₀N, hNmax.prop.2.1, hNmax.prop.2.2, ?_⟩
  intro K hHK hNK hKtop hKnormal
  exact le_antisymm
    (hNmax.2 ⟨hHK, hKtop, hKnormal⟩ hNK) hNK

open scoped Pointwise

theorem isCoatom_conj_smul {G : Type*} [Group G]
    {M : Subgroup G} (hM : IsCoatom M) (g : G) :
    IsCoatom ((MulAut.conj g) • M) := by
  rw [Subgroup.pointwise_smul_def]
  exact
    (OrderIso.isCoatom_iff
      ((MulAut.conj g : G ≃* G).mapSubgroup) M).2 hM

/-- The unique-maximal-subgroup endpoint in Wielandt's criterion.

If `H` is subnormal in its unique maximal overgroup and is subnormal in
every join with a conjugate, then that maximal overgroup is normal. -/
theorem isSubnormal_of_unique_coatom_of_local
    {G : Type*} [Group G] [Finite G] {H M : Subgroup G}
    (hM : IsCoatom M) (hHM : H ≤ M)
    (hH_M : (H.subgroupOf M).IsSubnormal)
    (hunique : ∀ K : Subgroup G, IsCoatom K → H ≤ K → K = M)
    (hlocal : ∀ g : G,
      (H.subgroupOf (H ⊔ (MulAut.conj g) • H)).IsSubnormal) :
    H.IsSubnormal := by
  classical
  by_cases htop :
      ∃ g : G, H ⊔ (MulAut.conj g) • H = ⊤
  · obtain ⟨g, hg⟩ := htop
    have := hlocal g
    rw [hg] at this
    exact Subgroup.IsSubnormal.trans le_top this .top
  · have htop' : ∀ g : G,
        H ⊔ (MulAut.conj g) • H ≠ ⊤ :=
      fun g hg => htop ⟨g, hg⟩
    have hconj : ∀ g : G, (MulAut.conj g) • H ≤ M := by
      intro g
      let J : Subgroup G := H ⊔ (MulAut.conj g) • H
      obtain hJ | ⟨K, hK, hJK⟩ := eq_top_or_exists_le_coatom J
      · exact (htop' g hJ).elim
      · have hHK : H ≤ K := le_sup_left.trans hJK
        rw [hunique K hK hHK] at hJK
        exact le_sup_right.trans hJK
    have hnormal : M.Normal := by
      apply Subgroup.Normal.of_conjugate_fixed
      intro g
      apply hunique
      · exact isCoatom_conj_smul hM g
      · apply (Subgroup.subset_pointwise_smul_iff).2
        simpa [MulAut.inv_def] using hconj g⁻¹
    exact Subgroup.IsSubnormal.trans hHM hH_M hnormal.isSubnormal

end Submission.Helpers
