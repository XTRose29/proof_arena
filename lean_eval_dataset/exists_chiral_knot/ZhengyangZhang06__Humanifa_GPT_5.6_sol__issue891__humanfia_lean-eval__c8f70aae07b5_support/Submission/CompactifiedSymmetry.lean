import Submission.Milnor
import Submission.Symmetry

open LeanEval.KnotTheory

namespace Submission.CompactifiedSymmetry

noncomputable section

def ambientHomeomorph {K : Knot} (S : Symmetry.NegativeSymmetry K) : R3 ≃ₜ R3 where
  toFun := S.F
  invFun := S.Finv
  left_inv := S.inv_left
  right_inv := S.inv_right
  continuous_toFun := S.smooth.continuous
  continuous_invFun := S.smooth_inv.continuous

def sphereHomeomorph {K : Knot} (S : Symmetry.NegativeSymmetry K) :
    Milnor.CSphere ≃ₜ Milnor.CSphere :=
  Milnor.onePointSphereHomeomorph.symm |>.trans
    (ambientHomeomorph S).onePointCongr |>.trans
      Milnor.onePointSphereHomeomorph

theorem onePointSphereHomeomorph_symm_compactify (p : R3) :
    Milnor.onePointSphereHomeomorph.symm (Milnor.compactify p).1 =
      (p : OnePoint R3) := by
  rw [Homeomorph.symm_apply_eq]
  exact (Milnor.onePointSphereHomeomorph_coe p).symm

theorem onePointSphereHomeomorph_symm_north :
    Milnor.onePointSphereHomeomorph.symm Milnor.north =
      (OnePoint.infty : OnePoint R3) := by
  rw [Homeomorph.symm_apply_eq]
  exact Milnor.onePointSphereHomeomorph_infty.symm

@[simp] theorem sphereHomeomorph_compactify {K : Knot}
    (S : Symmetry.NegativeSymmetry K) (p : R3) :
    sphereHomeomorph S (Milnor.compactify p).1 = (Milnor.compactify (S.F p)).1 := by
  simp [sphereHomeomorph, ambientHomeomorph, Homeomorph.trans_apply,
    onePointSphereHomeomorph_symm_compactify]

@[simp] theorem sphereHomeomorph_north {K : Knot}
    (S : Symmetry.NegativeSymmetry K) :
    sphereHomeomorph S Milnor.north = Milnor.north := by
  simp [sphereHomeomorph, ambientHomeomorph, Homeomorph.trans_apply,
    onePointSphereHomeomorph_symm_north]

theorem sphereHomeomorph_curve
    (S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot) (t : ℝ) :
    sphereHomeomorph S (Milnor.compactify (AlgebraicTrefoil.curve t)).1 =
      (Milnor.compactify (AlgebraicTrefoil.curve (S.sigma.f t))).1 := by
  rw [sphereHomeomorph_compactify]
  exact congrArg (fun p : R3 => (Milnor.compactify p).1) (S.map_curve t)

theorem polynomial_zero_iff_image
    (S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot) (q : Milnor.CSphere) :
    Milnor.polynomial (sphereHomeomorph S q) = 0 ↔ Milnor.polynomial q = 0 := by
  rw [Milnor.polynomial_zero_iff_range, Milnor.polynomial_zero_iff_range]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨S.sigma.finv t, ?_⟩
    apply (sphereHomeomorph S).injective
    rw [sphereHomeomorph_curve, S.sigma.right_inv]
    exact ht
  · rintro ⟨t, rfl⟩
    exact ⟨S.sigma.f t, (sphereHomeomorph_curve S t).symm⟩

abbrev Complement := {q : Milnor.CSphere // Milnor.polynomial q ≠ 0}

def complementHomeomorph
    (S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot) : Complement ≃ₜ Complement :=
  (sphereHomeomorph S).subtype fun q => (not_congr (polynomial_zero_iff_image S q)).symm

@[simp] theorem complementHomeomorph_apply
    (S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot) (q : Complement) :
    (complementHomeomorph S q).1 = sphereHomeomorph S q.1 :=
  rfl

end

end Submission.CompactifiedSymmetry
