import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.FittingNilpotent
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCores
import Submission.OddOrder.MathlibSupport.SylowIntersection

/-!
# Fitting subgroups and characteristic subgroups of Sylow subgroups

This file packages the Frattini-argument step used in
`BGsection4.rank2_char_Sylow_normal`.  If the ambient derived subgroup is
contained in the Fitting subgroup, then the Fitting subgroup together with
the normalizer of any Sylow subgroup generates the whole group.  The
nilpotent prime-core decomposition of the Fitting subgroup then shows that a
characteristic subgroup of the Sylow subgroup lying in its derived subgroup
is normal in the ambient group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- If the derived subgroup lies in the Fitting subgroup, the Fitting
subgroup and the normalizer of a Sylow subgroup generate the ambient group.
This is the Frattini-argument part of Bender--Glauberman Theorem 4.20(b). -/
theorem fittingCore_sup_normalizer_sylow_eq_top
    {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (hder : _root_.commutator G ≤ fittingCore G) :
    fittingCore G ⊔ Subgroup.normalizer (S : Set G) = ⊤ := by
  let N : Subgroup G := fittingCore G ⊔ (S : Subgroup G)
  letI : N.Normal := by
    apply Subgroup.Normal.of_commutator_le
    exact hder.trans (show fittingCore G ≤ N from le_sup_left)
  have hfrattini : Subgroup.normalizer (S : Set G) ⊔ N = ⊤ :=
    S.normalizer_sup_eq_top' (show (S : Subgroup G) ≤ N from le_sup_right)
  apply top_unique
  rw [← hfrattini]
  apply sup_le
  · exact le_sup_right
  · apply sup_le
    · exact le_sup_left
    · exact Subgroup.le_normalizer.trans le_sup_right

/-- Inside the finite nilpotent Fitting subgroup, its `p`-core is the
intersection with any ambient Sylow `p`-subgroup. -/
theorem map_pCore_fittingCore_eq_inf_sylow
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    (pCore p (fittingCore G)).map (fittingCore G).subtype =
      (S : Subgroup G) ⊓ fittingCore G := by
  rw [pCore_eq_sylow_of_isNilpotent (normalIntersectionSylow S (fittingCore G))]
  exact map_normalIntersectionSylow_eq_inf S (fittingCore G)

/-- The Fitting subgroup normalizes a characteristic subgroup of a Sylow
subgroup when that characteristic subgroup lies in both the Sylow derived
subgroup and the ambient Fitting subgroup. -/
theorem fittingCore_le_normalizer_of_characteristic_sylow
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) {T : Subgroup G}
    (hTS : T ≤ (S : Subgroup G))
    (hchar : (T.subgroupOf (S : Subgroup G)).Characteristic)
    (hTder : T ≤ (_root_.commutator S).map (S : Subgroup G).subtype)
    (hder : _root_.commutator G ≤ fittingCore G) :
    fittingCore G ≤ Subgroup.normalizer (T : Set G) := by
  let F : Subgroup G := fittingCore G
  let Fp : Subgroup G := (pCore p F).map F.subtype
  let Fp' : Subgroup G := (pPrimeCore p F).map F.subtype
  letI : (T.subgroupOf (S : Subgroup G)).Characteristic := hchar

  have hTfit : T ≤ F := by
    exact hTder.trans (by
      rw [Subgroup.map_subtype_commutator]
      exact (Subgroup.commutator_mono le_top le_top).trans hder)
  have hFpEq : Fp = (S : Subgroup G) ⊓ F := by
    simpa [Fp, F] using map_pCore_fittingCore_eq_inf_sylow S
  have hTFp : T ≤ Fp := by
    rw [hFpEq]
    exact le_inf hTS hTfit

  have hNormS : Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    simpa [Subgroup.map_subgroupOf_eq_of_le hTS] using
      (characteristic_map_subtype_invariant_under_normalizer
        (S : Subgroup G) (Subgroup.normalizer (S : Set G))
          (T.subgroupOf (S : Subgroup G)) le_rfl)
  have hFpS : Fp ≤ (S : Subgroup G) := by
    rw [hFpEq]
    exact inf_le_left
  have hFpNorm : Fp ≤ Subgroup.normalizer (T : Set G) :=
    hFpS.trans (Subgroup.le_normalizer.trans hNormS)

  have hFpCentFp' : Fp ≤ Subgroup.centralizer (Fp' : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hx with ⟨xF, hxF, rfl⟩
    rcases hy with ⟨yF, hyF, rfl⟩
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp
        (pCore_le_centralizer_pPrimeCore p hxF) yF hyF)
  have hFp'CentT : Fp' ≤ Subgroup.centralizer (T : Set G) :=
    (Subgroup.le_centralizer_iff.mp hFpCentFp').trans
      (Subgroup.centralizer_le hTFp)
  have hFp'Norm : Fp' ≤ Subgroup.normalizer (T : Set G) :=
    hFp'CentT.trans (Subgroup.centralizer_le_normalizer (T : Set G))

  have hdecomp : Fp ⊔ Fp' = F := by
    calc
      Fp ⊔ Fp' = ((pCore p F) ⊔ pPrimeCore p F).map F.subtype := by
        simp only [Fp, Fp', Subgroup.map_sup]
      _ = (⊤ : Subgroup F).map F.subtype := by
        rw [sup_pCore_pPrimeCore_eq_top_of_isNilpotent]
      _ = F := by
        rw [← MonoidHom.range_eq_map, F.range_subtype]
  change F ≤ Subgroup.normalizer (T : Set G)
  rw [← hdecomp]
  exact sup_le hFpNorm hFp'Norm

/-- A characteristic subgroup of a Sylow subgroup which lies in the Sylow
derived subgroup is normal as soon as the ambient derived subgroup lies in
the Fitting subgroup. -/
theorem normal_of_characteristic_sylow_of_le_derived_of_derived_le_fittingCore
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) {T : Subgroup G}
    (hTS : T ≤ (S : Subgroup G))
    (hchar : (T.subgroupOf (S : Subgroup G)).Characteristic)
    (hTder : T ≤ (_root_.commutator S).map (S : Subgroup G).subtype)
    (hder : _root_.commutator G ≤ fittingCore G) :
    T.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← fittingCore_sup_normalizer_sylow_eq_top S hder]
  exact sup_le
    (fittingCore_le_normalizer_of_characteristic_sylow
      S hTS hchar hTder hder)
    (by
      letI : (T.subgroupOf (S : Subgroup G)).Characteristic := hchar
      rw [Subgroup.le_normalizer_iff]
      simpa [Subgroup.map_subgroupOf_eq_of_le hTS] using
        (characteristic_map_subtype_invariant_under_normalizer
          (S : Subgroup G) (Subgroup.normalizer (S : Set G))
            (T.subgroupOf (S : Subgroup G)) le_rfl))

end Submission.OddOrder.MathlibSupport
