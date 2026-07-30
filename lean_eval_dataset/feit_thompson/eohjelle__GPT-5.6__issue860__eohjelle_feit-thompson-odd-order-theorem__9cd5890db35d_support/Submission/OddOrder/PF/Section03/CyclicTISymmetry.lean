import Submission.OddOrder.PF.Section03.CyclicTIUniqueness

/-!
# Symmetry and construction independence of the cyclic-TI isometry

This file ports the final block of `PFsection3.v`, namely `cycTIisoC`,
`cycTIiso_irrelC`, and `cycTIiso_irrel`.  Swapping the two internal direct
factors swaps the two irreducible-character indices but does not change the
resulting cyclic-TI isometry.  For a fixed ordering of the factors, the map is
also independent of the proofs used to construct it.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {G W W₁ W₂ : Subgroup Gamma}

private theorem cyclicTICharacter_swap_of_proofs
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (xdefW : IsInternalDirectProductIn W₂ W₁ W)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    IrreducibleCharacter.cyclicTICharacter xdefW j i =
      IrreducibleCharacter.cyclicTICharacter defW i j := by
  have hxdef : xdefW = defW.swap := Subsingleton.elim _ _
  rw [hxdef]
  exact IrreducibleCharacter.cyclicTICharacter_swap defW i j

namespace CyclicTIHypothesis

/-- `PFsection3.v: cycTIisoC`: swapping the complementary cyclic factors and
the two character indices leaves the cyclic-TI isometry unchanged. -/
theorem cycTIisoC
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (xdefW : IsInternalDirectProductIn W₂ W₁ W)
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (xh : CyclicTIHypothesis G W W₂ W₁ xdefW)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    h.cyclicTIIsometry
        (IrreducibleCharacter.cyclicTICharacter defW i j :
          ClassFunction W k) =
      xh.cyclicTIIsometry
        (IrreducibleCharacter.cyclicTICharacter xdefW j i :
          ClassFunction W k) := by
  symm
  apply h.eq_in_cycTIiso
  · exact
      (xh.cyclicTIIsometryData (k := k)).exists_signed_irreducible_image
        (IrreducibleCharacter.cyclicTICharacter xdefW j i)
  · intro w hw
    have hwswap : w ∈ cyclicTISetInW W W₂ W₁ := by
      simpa only [cyclicTISetInW_swap W W₁ W₂] using hw
    calc
      xh.cyclicTIIsometry
            (IrreducibleCharacter.cyclicTICharacter xdefW j i :
              ClassFunction W k)
            ⟨w, h.le_group w.property⟩ =
          (IrreducibleCharacter.cyclicTICharacter xdefW j i :
            ClassFunction W k) w :=
        xh.cyclicTIIsometry_restrict
          (IrreducibleCharacter.cyclicTICharacter xdefW j i :
            ClassFunction W k) hwswap
      _ = (IrreducibleCharacter.cyclicTICharacter defW i j :
            ClassFunction W k) w := by
        exact congrArg
          (fun chi : IrreducibleCharacter W k =>
            (chi : ClassFunction W k) w)
          (cyclicTICharacter_swap_of_proofs defW xdefW i j)

/-- `PFsection3.v: cycTIiso_irrelC`: the full cyclic-TI linear isometry is
unchanged when the two complementary factors are interchanged. -/
theorem cycTIiso_irrelC
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (xdefW : IsInternalDirectProductIn W₂ W₁ W)
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (xh : CyclicTIHypothesis G W W₂ W₁ xdefW) :
    h.cyclicTIIsometry (k := k) = xh.cyclicTIIsometry := by
  let b := ClassFunction.irreducibleCharacterBasis (G := W) (k := k)
  apply b.ext
  intro chi
  have hbchi : b chi = (chi : ClassFunction W k) := by
    simp [b]
  rw [hbchi]
  obtain ⟨i, j, hchi⟩ :=
    IrreducibleCharacter.exists_cyclicTICharacter defW chi
  rw [hchi]
  simpa only [cyclicTICharacter_swap_of_proofs defW xdefW i j] using
    (cycTIisoC defW xdefW h xh i j)

/-- `PFsection3.v: cycTIiso_irrel`: for fixed ordered factors, the cyclic-TI
isometry is independent of the direct-product and cyclic-TI witnesses used in
its construction. -/
theorem cycTIiso_irrel
    (defW defW' : IsInternalDirectProductIn W₁ W₂ W)
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (h' : CyclicTIHypothesis G W W₁ W₂ defW') :
    h.cyclicTIIsometry (k := k) = h'.cyclicTIIsometry := by
  have hdef : defW' = defW := Subsingleton.elim _ _
  subst defW'
  have hh : h' = h := Subsingleton.elim _ _
  subst h'
  rfl

end CyclicTIHypothesis

end

end Submission.OddOrder.PF
