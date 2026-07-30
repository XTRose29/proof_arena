import Submission.WielandtSelection
import Submission.WielandtRestriction

open scoped Pointwise

namespace Submission.Helpers

universe u

/-- Conjugation acting pointwise on subgroups agrees with mapping by the
corresponding inner automorphism. -/
theorem conj_smul_subgroup_eq_map
    {G : Type u} [Group G] (g : G) (H : Subgroup G) :
    (MulAut.conj g) • H =
      H.map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Subgroup.mem_map_equiv]
  simp [MulAut.inv_def]

/-- The conjugates of `H` which are contained in `U`. -/
def conjugateSubgroupsIn {G : Type u} [Group G]
    (H U : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ g : G, X = (MulAut.conj g) • H ∧ X ≤ U}

theorem mem_conjugateSubgroupsIn_self
    {G : Type u} [Group G] {H U : Subgroup G} (hHU : H ≤ U) :
    H ∈ conjugateSubgroupsIn H U := by
  refine ⟨1, ?_, hHU⟩
  simp

theorem conjugateSubgroupsIn_bounded
    {G : Type u} [Group G] (H U : Subgroup G) :
    ∀ X ∈ conjugateSubgroupsIn H U, X ≤ U := by
  rintro X ⟨g, rfl, hXU⟩
  exact hXU

theorem conjugateSubgroupsIn_mono
    {G : Type u} [Group G] (H : Subgroup G) {U V : Subgroup G}
    (hUV : U ≤ V) :
    conjugateSubgroupsIn H U ⊆ conjugateSubgroupsIn H V := by
  rintro X ⟨g, rfl, hXU⟩
  exact ⟨g, rfl, hXU.trans hUV⟩

theorem conjugateSubgroupsIn_invariant
    {G : Type u} [Group G] (H U : Subgroup G) :
    ∀ g : U, ∀ X ∈ conjugateSubgroupsIn H U,
      (MulAut.conj (g : G)) • X ∈ conjugateSubgroupsIn H U := by
  rintro g X ⟨a, rfl, hXU⟩
  refine ⟨(g : G) * a, ?_, Subgroup.conj_smul_le_of_le hXU g⟩
  simp [smul_smul]

theorem sSup_conjugateSubgroupsIn_le
    {G : Type u} [Group G] (H U : Subgroup G) :
    sSup (conjugateSubgroupsIn H U) ≤ U :=
  sSup_le (conjugateSubgroupsIn_bounded H U)

/-- Transport subnormality in a conjugated overgroup back along the
ambient conjugation equivalence. -/
theorem isSubnormal_conj_subgroupOf
    {G : Type u} [Group G] {H U : Subgroup G}
    (a : G)
    (hsub :
      (H.subgroupOf ((MulAut.conj a⁻¹) • U)).IsSubnormal) :
    (((MulAut.conj a) • H).subgroupOf U).IsSubnormal := by
  let V : Subgroup G := (MulAut.conj a⁻¹) • U
  have hmapV :
      V.map (MulAut.conj a).toMonoidHom = U := by
    change (MulAut.conj a) • V = U
    simp [V, smul_smul]
  let e₀ : V ≃* V.map (MulAut.conj a).toMonoidHom :=
    (MulAut.conj a).subgroupMap V
  let e : V ≃* U :=
    e₀.trans (MulEquiv.subgroupCongr hmapV)
  have hmapped :=
    Subgroup.IsSubnormal.map (f := e.toMonoidHom) e.surjective hsub
  have heq :
      (H.subgroupOf V).map e.toMonoidHom =
        ((MulAut.conj a) • H).subgroupOf U := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (a * (z : G) * a⁻¹) ∈ (MulAut.conj a) • H
      exact
        Subgroup.smul_mem_pointwise_smul (z : G) (MulAut.conj a) H hz
    · intro hy
      change (y : G) ∈ (MulAut.conj a) • H at hy
      obtain ⟨z, hz, hzy⟩ := hy
      refine ⟨⟨z, ?_⟩, hz, ?_⟩
      · change z ∈ (MulAut.conj a⁻¹) • U
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        have hzU : a * z * a⁻¹ ∈ U := by
          have hzy' : a * z * a⁻¹ = (y : G) := by
            simpa [MulAut.conj_apply] using hzy
          rw [hzy']
          exact y.property
        simpa [MulAut.inv_def] using hzU
      · apply Subtype.ext
        exact hzy
  rwa [heq] at hmapped

/-- The join of all conjugates of `H` contained in `U` is normalized by
`U`. -/
theorem le_normalizer_sSup_conjugateSubgroupsIn
    {G : Type u} [Group G] (H U : Subgroup G) :
    U ≤ Subgroup.normalizer
      ((sSup (conjugateSubgroupsIn H U) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (MulAut.conj g) • sSup (conjugateSubgroupsIn H U) =
    sSup (conjugateSubgroupsIn H U)
  have hforward (a : U) :
      (MulAut.conj (a : G)) • sSup (conjugateSubgroupsIn H U) ≤
        sSup (conjugateSubgroupsIn H U) := by
    rw [Subgroup.pointwise_smul_def, sSup_eq_iSup]
    simp_rw [Subgroup.map_iSup]
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    rw [← Subgroup.pointwise_smul_def]
    exact
      le_iSup_of_le ((MulAut.conj (a : G)) • X)
        (le_iSup_of_le
          (conjugateSubgroupsIn_invariant H U a X hX) le_rfl)
  apply le_antisymm (hforward ⟨g, hg⟩)
  apply (Subgroup.subset_pointwise_smul_iff).2
  simpa [MulAut.inv_def] using hforward (⟨g, hg⟩ : U)⁻¹

/-- In a counterexample to the zipper conclusion, a maximal overgroup of
`H` is the full normalizer of the join of the conjugates of `H` which it
contains. -/
theorem normalizer_sSup_conjugateSubgroupsIn_eq_coatom
    {G : Type u} [Group G] [Finite G]
    (H M : Subgroup G) (hM : IsCoatom M) (hHM : H ≤ M)
    (hproper :
      ∀ U : Subgroup G, U < ⊤ →
        ∀ X ∈ conjugateSubgroupsIn H U,
          (X.subgroupOf U).IsSubnormal)
    (hnot : ¬H.IsSubnormal) :
    Subgroup.normalizer
        ((sSup (conjugateSubgroupsIn H M) : Subgroup G) : Set G) = M := by
  let J : Subgroup G := sSup (conjugateSubgroupsIn H M)
  have hJM : J ≤ M :=
    sSup_conjugateSubgroupsIn_le H M
  have hHJ : H ≤ J := by
    apply le_sSup
    exact mem_conjugateSubgroupsIn_self hHM
  have hJtop : J < (⊤ : Subgroup G) :=
    hJM.trans_lt hM.lt_top
  have hHsubJ : (H.subgroupOf J).IsSubnormal :=
    hproper J hJtop H
      (mem_conjugateSubgroupsIn_self hHJ)
  have hnormalizer_ne :
      Subgroup.normalizer (J : Set G) ≠ ⊤ := by
    intro htop
    have hJnormal : J.Normal :=
      Subgroup.normalizer_eq_top_iff.mp htop
    exact hnot
      (Subgroup.IsSubnormal.trans hHJ hHsubJ hJnormal.isSubnormal)
  change Subgroup.normalizer (J : Set G) = M
  exact
    (hM.ne_top_iff_eq
      (le_normalizer_sSup_conjugateSubgroupsIn H M)).mp hnormalizer_ne

/-- Distinct maximal overgroups in a zipper counterexample cannot have
strictly nested families of contained conjugates. -/
theorem not_conjugateSubgroupsIn_ssubset_of_coatom
    {G : Type u} [Group G] [Finite G]
    (H M N : Subgroup G)
    (hM : IsCoatom M) (hN : IsCoatom N)
    (hHM : H ≤ M)
    (hproper :
      ∀ U : Subgroup G, U < ⊤ →
        ∀ X ∈ conjugateSubgroupsIn H U,
          (X.subgroupOf U).IsSubnormal)
    (hnot : ¬H.IsSubnormal) :
    ¬conjugateSubgroupsIn H M ⊂ conjugateSubgroupsIn H N := by
  intro hstrict
  obtain ⟨X, hXN, hXnotM, hXnormalizes⟩ :=
    exists_mem_diff_le_normalizer_sSup_of_bounded
      N (conjugateSubgroupsIn H N) (conjugateSubgroupsIn H M)
      (conjugateSubgroupsIn_bounded H N)
      (fun Y hY =>
        hproper N hN.lt_top Y hY)
      (conjugateSubgroupsIn_invariant H N)
      hstrict
  have hXMle : X ≤ M := by
    rw [normalizer_sSup_conjugateSubgroupsIn_eq_coatom
      H M hM hHM hproper hnot] at hXnormalizes
    exact hXnormalizes
  apply hXnotM
  obtain ⟨g, hXg, -⟩ := hXN
  exact ⟨g, hXg, hXMle⟩

/-- Wielandt's zipper dichotomy, in the form used by the local
subnormality criterion.

If every conjugate of `H` is subnormal in every proper subgroup which
contains it, then either `H` is subnormal in the ambient group or `H` has a
unique maximal overgroup. -/
theorem wielandt_zipper_dichotomy_of_proper
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (hproper :
      ∀ U : Subgroup G, U < ⊤ →
        ∀ X ∈ conjugateSubgroupsIn H U,
          (X.subgroupOf U).IsSubnormal) :
    H.IsSubnormal ∨
      ∃ M : Subgroup G, IsCoatom M ∧ H ≤ M ∧
        ∀ N : Subgroup G, IsCoatom N → H ≤ N → N = M := by
  classical
  by_cases hH : H.IsSubnormal
  · exact Or.inl hH
  right
  obtain hHtop | ⟨M, hM, hHM⟩ :=
    eq_top_or_exists_le_coatom H
  · exact (hH (hHtop ▸ Subgroup.IsSubnormal.top)).elim
  refine ⟨M, hM, hHM, ?_⟩
  intro N hN hHN
  by_contra hNM
  let C :=
    {K : Subgroup G // IsCoatom K ∧ H ≤ K ∧ K ≠ M}
  letI : Nonempty C :=
    ⟨⟨N, hN, hHN, hNM⟩⟩
  obtain ⟨N₀, hN₀max⟩ :=
    Finite.exists_max
      (fun K : C =>
        (conjugateSubgroupsIn H M ∩
          conjugateSubgroupsIn H K.1).ncard)
  let Sₘ : Set (Subgroup G) :=
    conjugateSubgroupsIn H M
  let Sₙ : Set (Subgroup G) :=
    conjugateSubgroupsIn H N₀.1
  let S₀ : Set (Subgroup G) :=
    Sₘ ∩ Sₙ
  have hfamilies_ne : Sₘ ≠ Sₙ := by
    intro heq
    have hnormalizerM :=
      normalizer_sSup_conjugateSubgroupsIn_eq_coatom
        H M hM hHM hproper hH
    have hnormalizerN :=
      normalizer_sSup_conjugateSubgroupsIn_eq_coatom
        H N₀.1 N₀.2.1 N₀.2.2.1 hproper hH
    apply N₀.2.2.2
    calc
      N₀.1 =
          Subgroup.normalizer
            ((sSup (conjugateSubgroupsIn H N₀.1) :
              Subgroup G) : Set G) :=
        hnormalizerN.symm
      _ =
          Subgroup.normalizer
            ((sSup (conjugateSubgroupsIn H M) :
              Subgroup G) : Set G) := by
        rw [show conjugateSubgroupsIn H N₀.1 = Sₙ from rfl,
          ← heq]
      _ = M := hnormalizerM
  have hnot_mn : ¬Sₘ ⊆ Sₙ := by
    intro hle
    exact
      (not_conjugateSubgroupsIn_ssubset_of_coatom
        H M N₀.1 hM N₀.2.1 hHM hproper hH)
        ((Set.ssubset_iff_subset_ne).2 ⟨hle, hfamilies_ne⟩)
  have hnot_nm : ¬Sₙ ⊆ Sₘ := by
    intro hle
    exact
      (not_conjugateSubgroupsIn_ssubset_of_coatom
        H N₀.1 M N₀.2.1 hM N₀.2.2.1 hproper hH)
        ((Set.ssubset_iff_subset_ne).2
          ⟨hle, hfamilies_ne.symm⟩)
  have hS₀m : S₀ ⊂ Sₘ := by
    apply (Set.ssubset_iff_subset_ne).2
    refine ⟨Set.inter_subset_left, ?_⟩
    intro heq
    apply hnot_mn
    intro X hX
    have hXS₀ : X ∈ S₀ := by
      rw [heq]
      exact hX
    exact hXS₀.2
  have hS₀n : S₀ ⊂ Sₙ := by
    apply (Set.ssubset_iff_subset_ne).2
    refine ⟨Set.inter_subset_right, ?_⟩
    intro heq
    apply hnot_nm
    intro X hX
    have hXS₀ : X ∈ S₀ := by
      rw [heq]
      exact hX
    exact hXS₀.1
  obtain ⟨Xₘ, hXₘm, hXₘnot, hXₘnormalizes⟩ :=
    exists_mem_diff_le_normalizer_sSup_of_bounded
      M Sₘ S₀
      (conjugateSubgroupsIn_bounded H M)
      (fun X hX => hproper M hM.lt_top X hX)
      (conjugateSubgroupsIn_invariant H M)
      hS₀m
  obtain ⟨Xₙ, hXₙn, hXₙnot, hXₙnormalizes⟩ :=
    exists_mem_diff_le_normalizer_sSup_of_bounded
      N₀.1 Sₙ S₀
      (conjugateSubgroupsIn_bounded H N₀.1)
      (fun X hX => hproper N₀.1 N₀.2.1.lt_top X hX)
      (conjugateSubgroupsIn_invariant H N₀.1)
      hS₀n
  let K : Subgroup G := sSup S₀
  have hKM : K ≤ M := by
    apply sSup_le
    intro X hX
    exact (conjugateSubgroupsIn_bounded H M X hX.1)
  have hHK : H ≤ K := by
    apply le_sSup
    exact
      ⟨mem_conjugateSubgroupsIn_self hHM,
        mem_conjugateSubgroupsIn_self N₀.2.2.1⟩
  have hKtop : K < (⊤ : Subgroup G) :=
    hKM.trans_lt hM.lt_top
  have hHsubK : (H.subgroupOf K).IsSubnormal :=
    hproper K hKtop H
      (mem_conjugateSubgroupsIn_self hHK)
  have hnormalizer_ne :
      Subgroup.normalizer (K : Set G) ≠ ⊤ := by
    intro htop
    have hKnormal : K.Normal :=
      Subgroup.normalizer_eq_top_iff.mp htop
    exact hH
      (Subgroup.IsSubnormal.trans hHK hHsubK hKnormal.isSubnormal)
  obtain hnormalizer_top | ⟨L, hL, hnormalizerL⟩ :=
    eq_top_or_exists_le_coatom (Subgroup.normalizer (K : Set G))
  · exact (hnormalizer_ne hnormalizer_top).elim
  have hHL : H ≤ L :=
    hHK.trans (K.le_normalizer.trans hnormalizerL)
  have hXₘLle : Xₘ ≤ L :=
    hXₘnormalizes.trans hnormalizerL
  have hXₙLle : Xₙ ≤ L :=
    hXₙnormalizes.trans hnormalizerL
  have hXₘL : Xₘ ∈ conjugateSubgroupsIn H L := by
    obtain ⟨g, hg, -⟩ := hXₘm
    exact ⟨g, hg, hXₘLle⟩
  have hXₙL : Xₙ ∈ conjugateSubgroupsIn H L := by
    obtain ⟨g, hg, -⟩ := hXₙn
    exact ⟨g, hg, hXₙLle⟩
  have hLneM : L ≠ M := by
    intro hLM
    apply hXₙnot
    refine ⟨?_, hXₙn⟩
    simpa [Sₘ, hLM] using hXₙL
  let Lc : C :=
    ⟨L, hL, hHL, hLneM⟩
  have hS₀mL :
      S₀ ⊂
        Sₘ ∩ conjugateSubgroupsIn H L := by
    apply (Set.ssubset_iff_subset_ne).2
    refine ⟨?_, ?_⟩
    · intro X hX
      refine ⟨hX.1, ?_⟩
      obtain ⟨g, hg, -⟩ := hX.1
      refine ⟨g, hg, ?_⟩
      exact (le_sSup hX).trans
        (K.le_normalizer.trans hnormalizerL)
    · intro heq
      apply hXₘnot
      rw [heq]
      exact ⟨hXₘm, hXₘL⟩
  have hcard_lt :
      S₀.ncard <
        (Sₘ ∩ conjugateSubgroupsIn H L).ncard :=
    Set.ncard_lt_ncard hS₀mL
  have hcard_max :
      (Sₘ ∩ conjugateSubgroupsIn H L).ncard ≤ S₀.ncard := by
    simpa [Sₘ, Sₙ, S₀, Lc] using hN₀max Lc
  exact (not_lt_of_ge hcard_max hcard_lt).elim

/-- Wielandt's local subnormality criterion for finite groups. -/
theorem isSubnormal_of_subnormal_in_sup_conjugate
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (hlocal :
      ∀ g : G,
        (H.subgroupOf (H ⊔ (MulAut.conj g) • H)).IsSubnormal) :
    H.IsSubnormal := by
  classical
  induction hcard : Nat.card G using Nat.strong_induction_on
      generalizing G with
  | h n ih =>
      have hproper :
          ∀ U : Subgroup G, U < ⊤ →
            ∀ X ∈ conjugateSubgroupsIn H U,
              (X.subgroupOf U).IsSubnormal := by
        intro U hU X hX
        obtain ⟨a, rfl, hXU⟩ := hX
        let V : Subgroup G :=
          (MulAut.conj a⁻¹) • U
        have hVtop : V < (⊤ : Subgroup G) := by
          apply lt_top_iff_ne_top.mpr
          intro hV
          have hs :=
            congr_arg
              (fun K : Subgroup G => (MulAut.conj a) • K) hV
          have hUtop : U = ⊤ := by
            simpa [V, smul_smul] using hs
          exact hU.ne hUtop
        have hHV : H ≤ V := by
          intro y hy
          change y ∈ (MulAut.conj a⁻¹) • U
          rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
          have hay :
              (MulAut.conj a) • y ∈ U :=
            hXU
              (Subgroup.smul_mem_pointwise_smul
                y (MulAut.conj a) H hy)
          simpa [MulAut.inv_def] using hay
        have hcardV : Nat.card V < n := by
          rw [← hcard]
          exact subgroup_card_lt hVtop
        have hsubV : (H.subgroupOf V).IsSubnormal := by
          apply ih (Nat.card V) hcardV
              (H.subgroupOf V)
          · exact localSubnormal_restrict hHV hlocal
          · rfl
        exact isSubnormal_conj_subgroupOf a hsubV
      rcases
          wielandt_zipper_dichotomy_of_proper H hproper with
        hsubnormal | ⟨M, hM, hHM, hunique⟩
      · exact hsubnormal
      · exact isSubnormal_of_unique_coatom_of_local
          hM hHM
          (hproper M hM.lt_top H
            (mem_conjugateSubgroupsIn_self hHM))
          hunique hlocal

end Submission.Helpers
