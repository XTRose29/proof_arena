import Submission.OddOrder.PF.Section02.DadeSupportConjugation
import Submission.OddOrder.PF.Section02.DadeCosetPower

/-!
# Peterfalvi 2.4(b): overlap of first Dade supports

An element common to two first supports gives conjugate representatives of
the corresponding Dade right cosets.  Coprime-power extraction recovers the
right factors, and the Dade conjugacy hypothesis moves the conjugator into
`L`.
-/

namespace Submission.OddOrder.PF

open scoped Pointwise

universe u

/-- Peterfalvi 2.4(b): intersecting first supports have `L`-conjugate
arguments. -/
theorem Dade_support1_TI
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) {a b : Γ}
    (ha : a ∈ A) (hb : b ∈ A)
    (hinter : (Dade_support1 ddA a ∩ Dade_support1 ddA b).Nonempty) :
    ∃ x : Γ, x ∈ L ∧ b = x⁻¹ * a * x := by
  rcases hinter with ⟨y, hya, hyb⟩
  change
    ∃ u ∈ ((DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ)),
      ∃ ga ∈ G, ga⁻¹ * u * ga = y at hya
  change
    ∃ v ∈ ((DadeSignalizer ddA b : Set Γ) * ({b} : Set Γ)),
      ∃ gb ∈ G, gb⁻¹ * v * gb = y at hyb
  rcases hya with ⟨u, hu, ga, hga, huga⟩
  rcases hyb with ⟨v, hv, gb, hgb, hvgb⟩
  let g : Γ := ga * gb⁻¹
  have hg : g ∈ G := G.mul_mem hga (G.inv_mem hgb)
  have huv : g⁻¹ * u * g = v := by
    dsimp [g]
    calc
      (ga * gb⁻¹)⁻¹ * u * (ga * gb⁻¹) =
          gb * (ga⁻¹ * u * ga) * gb⁻¹ := by group
      _ = gb * y * gb⁻¹ := by rw [huga]
      _ = v := by rw [← hvgb]; group
  have hab : g⁻¹ * a * g = b :=
    dade_coset_conj_right_factor ddA ha hb hu hv huv
  have hbClassG : b ∈ conjugacyClassWithin G a :=
    ⟨g, hg, hab⟩
  rcases ddA.2.2.2.1 ha hb hbClassG with ⟨x, hx, hxab⟩
  exact ⟨x, hx, hxab.symm⟩

end Submission.OddOrder.PF
