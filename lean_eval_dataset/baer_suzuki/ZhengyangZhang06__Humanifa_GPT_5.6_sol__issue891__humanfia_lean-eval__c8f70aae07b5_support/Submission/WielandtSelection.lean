import Submission.WielandtFiniteJoin

open scoped Pointwise

namespace Submission.Helpers

universe u

/-- The family obtained by viewing all members of `S` which lie in `N` as
subgroups of `N`. -/
def restrictedSubgroupFamily {G : Type u} [Group G]
    (N : Subgroup G) (S : Set (Subgroup G)) : Set (Subgroup N) :=
  {Y | ∃ X ∈ S, X ≤ N ∧ Y = X.subgroupOf N}

/-- Mapping a restricted family back into the ambient group recovers its
join, provided every member of the original family lies in the restricting
subgroup. -/
theorem map_sSup_restrictedSubgroupFamily
    {G : Type u} [Group G] (N : Subgroup G) (S : Set (Subgroup G))
    (hSN : ∀ X ∈ S, X ≤ N) :
    (sSup (restrictedSubgroupFamily N S)).map N.subtype = sSup S := by
  apply le_antisymm
  · rw [sSup_eq_iSup, Subgroup.map_iSup]
    apply iSup_le
    intro Y
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hY
    obtain ⟨X, hXS, hXN, rfl⟩ := hY
    rw [Subgroup.map_subgroupOf_eq_of_le hXN]
    exact le_sSup hXS
  · apply sSup_le
    intro X hXS
    rw [← Subgroup.map_subgroupOf_eq_of_le (hSN X hXS)]
    apply Subgroup.map_mono
    apply le_sSup
    exact ⟨X, hXS, hSN X hXS, rfl⟩

/-- A family of subgroups closed under all ambient conjugations has normal
join. -/
theorem normal_sSup_of_conj_closed
    {G : Type u} [Group G] (S : Set (Subgroup G))
    (hS : ∀ g : G, ∀ X ∈ S, (MulAut.conj g) • X ∈ S) :
    (sSup S).Normal := by
  apply Subgroup.Normal.of_conjugate_fixed
  intro g
  have hforward (a : G) :
      (MulAut.conj a) • sSup S ≤ sSup S := by
    rw [Subgroup.pointwise_smul_def, sSup_eq_iSup]
    simp_rw [Subgroup.map_iSup]
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    rw [← Subgroup.pointwise_smul_def]
    exact
      le_iSup_of_le ((MulAut.conj a) • X)
        (le_iSup_of_le (hS a X hX) le_rfl)
  apply le_antisymm (hforward g)
  apply (Subgroup.subset_pointwise_smul_iff).2
  simpa [MulAut.inv_def] using hforward g⁻¹

/-- Wielandt's selection lemma for a finite group.

If `S` is a conjugation-stable family of subnormal subgroups and `S₀` is a
proper subfamily, some member of `S \ S₀` normalizes the join of `S₀`. -/
theorem exists_mem_diff_le_normalizer_sSup
    {G : Type u} [Group G] [Finite G]
    (S S₀ : Set (Subgroup G))
    (hsubnormal : ∀ X ∈ S, X.IsSubnormal)
    (hinvariant :
      ∀ g : G, ∀ X ∈ S, (MulAut.conj g) • X ∈ S)
    (hproper : S₀ ⊂ S) :
    ∃ X ∈ S, X ∉ S₀ ∧
      X ≤ Subgroup.normalizer ((sSup S₀ : Subgroup G) : Set G) := by
  classical
  induction hcard : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
      let K : Subgroup G := sSup S₀
      have hS₀S : S₀ ⊆ S :=
        hproper.le
      have hKsubnormal : K.IsSubnormal := by
        apply isSubnormal_sSup_finite
        intro X hXS₀
        exact hsubnormal X (hS₀S hXS₀)
      obtain ⟨X₀, hX₀S, hX₀not⟩ :=
        Set.exists_of_ssubset hproper
      by_cases hKtop : K = ⊤
      · refine ⟨X₀, hX₀S, hX₀not, ?_⟩
        change X₀ ≤ Subgroup.normalizer (K : Set G)
        rw [hKtop, Subgroup.normalizer_eq_top]
        exact le_top
      obtain ⟨N, hNnormal, hKN, hNtop⟩ :=
        hKsubnormal.exists_normal_and_le_and_lt_top_of_ne hKtop
      let S₁ : Set (Subgroup G) :=
        {X | X ∈ S ∧ X ≤ N}
      have hS₀S₁ : S₀ ⊆ S₁ := by
        intro X hXS₀
        exact ⟨hS₀S hXS₀, (le_sSup hXS₀).trans hKN⟩
      by_cases hS₁S₀ : S₁ = S₀
      · have hS₁invariant :
            ∀ g : G, ∀ X ∈ S₁,
              (MulAut.conj g) • X ∈ S₁ := by
          intro g X hX
          refine ⟨hinvariant g X hX.1, ?_⟩
          rintro y ⟨x, hx, rfl⟩
          exact hNnormal.conj_mem x (hX.2 hx) g
        have hS₀invariant :
            ∀ g : G, ∀ X ∈ S₀,
              (MulAut.conj g) • X ∈ S₀ := by
          intro g X hX
          rw [← hS₁S₀] at hX ⊢
          exact hS₁invariant g X hX
        have hKnormal : K.Normal := by
          exact normal_sSup_of_conj_closed S₀ hS₀invariant
        refine ⟨X₀, hX₀S, hX₀not, ?_⟩
        letI : K.Normal := hKnormal
        exact Subgroup.le_normalizer_of_normal
      have hS₀properS₁ : S₀ ⊂ S₁ := by
        exact (Set.ssubset_iff_subset_ne).2 ⟨hS₀S₁, Ne.symm hS₁S₀⟩
      let T : Set (Subgroup N) :=
        restrictedSubgroupFamily N S₁
      let T₀ : Set (Subgroup N) :=
        restrictedSubgroupFamily N S₀
      have hT₀T : T₀ ⊆ T := by
        intro Y hY
        obtain ⟨X, hXS₀, hXN, rfl⟩ := hY
        exact ⟨X, hS₀S₁ hXS₀, hXN, rfl⟩
      obtain ⟨X₁, hX₁S₁, hX₁notS₀⟩ :=
        Set.exists_of_ssubset hS₀properS₁
      have hT₀properT : T₀ ⊂ T := by
        apply (Set.ssubset_iff_of_subset hT₀T).2
        refine
          ⟨X₁.subgroupOf N,
            ⟨X₁, hX₁S₁, hX₁S₁.2, rfl⟩, ?_⟩
        rintro ⟨Z, hZS₀, hZN, hZX₁⟩
        apply hX₁notS₀
        have hmaps :
            (X₁.subgroupOf N).map N.subtype =
              (Z.subgroupOf N).map N.subtype :=
          congr_arg (Subgroup.map N.subtype) hZX₁
        rw [Subgroup.map_subgroupOf_eq_of_le hX₁S₁.2,
          Subgroup.map_subgroupOf_eq_of_le hZN] at hmaps
        rwa [hmaps]
      have hTsubnormal :
          ∀ Y ∈ T, Y.IsSubnormal := by
        intro Y hY
        obtain ⟨X, hXS₁, _hXN, rfl⟩ := hY
        exact (hsubnormal X hXS₁.1).subgroupOf
      have hTinvariant :
          ∀ g : N, ∀ Y ∈ T,
            (MulAut.conj g) • Y ∈ T := by
        intro g Y hY
        obtain ⟨X, hXS₁, hXN, rfl⟩ := hY
        refine
          ⟨(MulAut.conj (g : G)) • X,
            ⟨hinvariant (g : G) X hXS₁.1,
              Subgroup.conj_smul_le_of_le hXN g⟩,
            Subgroup.conj_smul_le_of_le hXN g, ?_⟩
        exact Subgroup.conj_smul_subgroupOf hXN g
      have hcardN : Nat.card N < n := by
        rw [← hcard]
        exact subgroup_card_lt hNtop
      obtain ⟨Y, hYT, hYnotT₀, hYnormalizes⟩ :=
        ih (Nat.card N) hcardN T T₀ hTsubnormal hTinvariant
          hT₀properT rfl
      obtain ⟨X, hXS₁, hXN, hYX⟩ := hYT
      have hXnotS₀ : X ∉ S₀ := by
        intro hXS₀
        apply hYnotT₀
        exact ⟨X, hXS₀, hXN, hYX⟩
      have hS₀N : ∀ Z ∈ S₀, Z ≤ N := by
        intro Z hZS₀
        exact (le_sSup hZS₀).trans hKN
      have hjoinT₀ :
          sSup T₀ = K.subgroupOf N := by
        apply (Subgroup.map_subtype_inj).mp
        rw [map_sSup_restrictedSubgroupFamily N S₀ hS₀N,
          Subgroup.map_subgroupOf_eq_of_le hKN]
      refine ⟨X, hXS₁.1, hXnotS₀, ?_⟩
      intro x hx
      have hxY : (⟨x, hXN hx⟩ : N) ∈ Y := by
        rw [hYX]
        exact hx
      have hxnormalizesN :
          (⟨x, hXN hx⟩ : N) ∈
            Subgroup.normalizer (K.subgroupOf N : Set N) := by
        rw [← hjoinT₀]
        exact hYnormalizes hxY
      rw [← Subgroup.subgroupOf_normalizer_eq hKN] at hxnormalizesN
      exact hxnormalizesN

/-- Ambient-group form of the selection lemma for a family bounded by `U`.
The hypotheses and conclusion remain phrased using subgroups of `G`, while
subnormality and conjugation invariance are checked inside `U`. -/
theorem exists_mem_diff_le_normalizer_sSup_of_bounded
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (S S₀ : Set (Subgroup G))
    (hbounded : ∀ X ∈ S, X ≤ U)
    (hsubnormal :
      ∀ X ∈ S, (X.subgroupOf U).IsSubnormal)
    (hinvariant :
      ∀ g : U, ∀ X ∈ S,
        (MulAut.conj (g : G)) • X ∈ S)
    (hproper : S₀ ⊂ S) :
    ∃ X ∈ S, X ∉ S₀ ∧
      X ≤ Subgroup.normalizer ((sSup S₀ : Subgroup G) : Set G) := by
  classical
  let T : Set (Subgroup U) :=
    restrictedSubgroupFamily U S
  let T₀ : Set (Subgroup U) :=
    restrictedSubgroupFamily U S₀
  have hS₀S : S₀ ⊆ S :=
    hproper.le
  have hT₀T : T₀ ⊆ T := by
    intro Y hY
    obtain ⟨X, hXS₀, hXU, rfl⟩ := hY
    exact ⟨X, hS₀S hXS₀, hXU, rfl⟩
  obtain ⟨X₀, hX₀S, hX₀not⟩ :=
    Set.exists_of_ssubset hproper
  have hT₀properT : T₀ ⊂ T := by
    apply (Set.ssubset_iff_of_subset hT₀T).2
    refine
      ⟨X₀.subgroupOf U,
        ⟨X₀, hX₀S, hbounded X₀ hX₀S, rfl⟩, ?_⟩
    rintro ⟨Z, hZS₀, hZU, hZX₀⟩
    apply hX₀not
    have hmaps :
        (X₀.subgroupOf U).map U.subtype =
          (Z.subgroupOf U).map U.subtype :=
      congr_arg (Subgroup.map U.subtype) hZX₀
    rw [Subgroup.map_subgroupOf_eq_of_le (hbounded X₀ hX₀S),
      Subgroup.map_subgroupOf_eq_of_le hZU] at hmaps
    rwa [hmaps]
  have hTsubnormal :
      ∀ Y ∈ T, Y.IsSubnormal := by
    intro Y hY
    obtain ⟨X, hXS, _hXU, rfl⟩ := hY
    exact hsubnormal X hXS
  have hTinvariant :
      ∀ g : U, ∀ Y ∈ T,
        (MulAut.conj g) • Y ∈ T := by
    intro g Y hY
    obtain ⟨X, hXS, hXU, rfl⟩ := hY
    refine
      ⟨(MulAut.conj (g : G)) • X,
        hinvariant g X hXS,
        Subgroup.conj_smul_le_of_le hXU g, ?_⟩
    exact Subgroup.conj_smul_subgroupOf hXU g
  obtain ⟨Y, hYT, hYnotT₀, hYnormalizes⟩ :=
    exists_mem_diff_le_normalizer_sSup T T₀
      hTsubnormal hTinvariant hT₀properT
  obtain ⟨X, hXS, hXU, hYX⟩ := hYT
  have hXnotS₀ : X ∉ S₀ := by
    intro hXS₀
    apply hYnotT₀
    exact ⟨X, hXS₀, hXU, hYX⟩
  have hS₀U : ∀ Z ∈ S₀, Z ≤ U := by
    intro Z hZS₀
    exact hbounded Z (hS₀S hZS₀)
  have hjoinT₀ :
      sSup T₀ = (sSup S₀).subgroupOf U := by
    apply (Subgroup.map_subtype_inj).mp
    rw [map_sSup_restrictedSubgroupFamily U S₀ hS₀U,
      Subgroup.map_subgroupOf_eq_of_le (sSup_le hS₀U)]
  refine ⟨X, hXS, hXnotS₀, ?_⟩
  intro x hx
  have hxY : (⟨x, hXU hx⟩ : U) ∈ Y := by
    rw [hYX]
    exact hx
  have hxnormalizesU :
      (⟨x, hXU hx⟩ : U) ∈
        Subgroup.normalizer ((sSup S₀).subgroupOf U : Set U) := by
    rw [← hjoinT₀]
    exact hYnormalizes hxY
  rw [← Subgroup.subgroupOf_normalizer_eq (sSup_le hS₀U)] at hxnormalizesU
  exact hxnormalizesU

end Submission.Helpers
