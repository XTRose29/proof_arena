import ChallengeDeps
import Submission.Helpers

open LeanEval.RepresentationTheory.FrobeniusDeterminant
open MvPolynomial Matrix

namespace Submission

open Scratch

theorem frobenius_group_determinant (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    ∃ (r : ℕ) (p : Fin r → MvPolynomial G ℂ),
      r = Nat.card (ConjClasses G) ∧
      (∀ j, Irreducible (p j)) ∧
      (∀ i j, i ≠ j → ¬ Associated (p i) (p j)) ∧
      groupDeterminant G = ∏ j, (p j) ^ (p j).totalDegree := by
  classical
  letI : NeZero (Nat.card G : ℂ) := by
    simpa only [Fintype.card_eq_nat_card] using
      (NeZero.charZero : NeZero (Fintype.card G : ℂ))
  letI : IsSemisimpleRing (MonoidAlgebra ℂ G) := inferInstance
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
      ℂ (MonoidAlgebra ℂ G)
  have hn : n = Nat.card (ConjClasses G) :=
    wedderburn_block_count_eq_conjClasses n d hd e
  have hnpos : 0 < n := by
    rw [hn]
    exact Nat.card_pos
  let i0 : Fin n := ⟨0, hnpos⟩
  let epsilon : ℂ := ((↑((Equiv.inv G).sign) : ℤ) : ℂ)
  have hepsilon_unit : IsUnit epsilon := by
    exact (Equiv.inv G).sign.isUnit.map (Int.castRingHom ℂ)
  have hepsilon : epsilon ≠ 0 := hepsilon_unit.ne_zero
  obtain ⟨u, hu⟩ :=
    IsAlgClosed.exists_pow_nat_eq epsilon (NeZero.pos (d i0))
  have hu0 : u ≠ 0 := by
    intro hzero
    apply hepsilon
    rw [← hu, hzero]
    exact zero_pow (NeZero.ne (d i0))
  let phi := groupBlockPolynomialEquiv n d e
  let q : Fin n → MvPolynomial (BlockVar n d) ℂ :=
    adjustedBlockFactor n d i0 u
  let p : Fin n → MvPolynomial G ℂ := fun i => phi.symm (q i)
  have hp_irreducible (i : Fin n) : Irreducible (p i) := by
    exact (MulEquiv.irreducible_iff phi.symm.toMulEquiv).mpr
      (adjustedBlockFactor_irreducible n d hd i0 hu0 i)
  have hp_not_associated (i j : Fin n) (hij : i ≠ j) :
      ¬ Associated (p i) (p j) := by
    intro h
    apply adjustedBlockFactor_not_associated n d hd i0 hu0 i j hij
    simpa [p, q, phi] using h.map phi
  have hp_homogeneous (i : Fin n) : (p i).IsHomogeneous (d i) := by
    exact groupBlockPolynomialEquiv_symm_isHomogeneous n d e
      (adjustedBlockFactor_isHomogeneous n d i0 u i)
  have hp_totalDegree (i : Fin n) : (p i).totalDegree = d i :=
    (hp_homogeneous i).totalDegree (hp_irreducible i).ne_zero
  have hfactor : testGroupDeterminant ℂ G = ∏ i, (p i) ^ d i := by
    apply phi.injective
    rw [map_groupDeterminant_eq_blockFactors n d e]
    simp only [map_prod, map_pow, p, phi, AlgEquiv.apply_symm_apply]
    exact (prod_adjustedBlockFactor_pow n d i0 u epsilon hu).symm
  refine ⟨n, p, hn, hp_irreducible, hp_not_associated, ?_⟩
  rw [show groupDeterminant G = testGroupDeterminant ℂ G by rfl, hfactor]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hp_totalDegree]

end Submission
