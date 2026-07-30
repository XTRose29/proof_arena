import Submission.JordanHelpers
import Submission.Separation

namespace Submission.Components

open Function Set
open Winding Separation

noncomputable section

theorem frontier_component_subset_range (r : C(Circle, ℂ)) {x : ℂ}
    (hx : x ∈ (Set.range r)ᶜ) :
    frontier (connectedComponentIn (Set.range r)ᶜ x) ⊆ Set.range r := by
  exact _root_.Submission.JordanHelpers.frontier_connectedComponentIn_compl_range_subset
    r r.continuous hx

theorem windingAround_ne_zero_of_bounded_component
    (r : C(Circle, ℂ)) (hinj : Function.Injective r) {x : ℂ}
    (hx : x ∈ (Set.range r)ᶜ)
    (hxb : Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x)) :
    windingAround r x hx ≠ 0 := by
  intro hw
  let gx := aroundMap r x
  have hgx : ∀ z, gx z ≠ 0 := aroundMap_ne_zero r hx
  obtain ⟨l, hl⟩ :=
    (hasLog_iff_winding_eq_zero gx hgx).mpr hw
  have hrclosed : Topology.IsClosedEmbedding r :=
    r.continuous.isClosedEmbedding hinj
  obtain ⟨L, hL⟩ := l.exists_extension hrclosed
  let U := connectedComponentIn (Set.range r)ᶜ x
  have hopenRange : IsOpen (Set.range r)ᶜ :=
    (isCompact_range r.continuous).isClosed.isOpen_compl
  have hUopen : IsOpen U := hopenRange.connectedComponentIn
  apply no_nonzero_extension_over_bounded_open U hUopen hxb x
    (mem_connectedComponentIn hx) 1 one_ne_zero (fun z ↦ Complex.exp (L z))
  · exact L.continuous.cexp.continuousOn
  · intro z _hz
    exact Complex.exp_ne_zero _
  · intro z hz
    obtain ⟨t, rfl⟩ := frontier_component_subset_range r hx hz
    have hLt : L (r t) = l t := by
      exact DFunLike.congr_fun hL t
    rw [hLt, hl]
    simp [gx]

theorem bounded_components_eq
    (r : C(Circle, ℂ)) (hinj : Function.Injective r) {x y : ℂ}
    (hx : x ∈ (Set.range r)ᶜ) (hy : y ∈ (Set.range r)ᶜ)
    (hxb : Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x))
    (hyb : Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ y)) :
    connectedComponentIn (Set.range r)ᶜ x =
      connectedComponentIn (Set.range r)ᶜ y := by
  let Ux := connectedComponentIn (Set.range r)ᶜ x
  let Uy := connectedComponentIn (Set.range r)ᶜ y
  by_contra hne
  have hopenRange : IsOpen (Set.range r)ᶜ :=
    (isCompact_range r.continuous).isClosed.isOpen_compl
  have hUxopen : IsOpen Ux := hopenRange.connectedComponentIn
  have hUyopen : IsOpen Uy := hopenRange.connectedComponentIn
  have hyUy : y ∈ Uy := mem_connectedComponentIn hy
  have hyncl : y ∉ closure Ux := by
    intro hycl
    obtain ⟨z, hzUy, hzUx⟩ := mem_closure_iff.mp hycl Uy hUyopen hyUy
    have hxz : Ux = connectedComponentIn (Set.range r)ᶜ z :=
      connectedComponentIn_eq hzUx
    have hyz : Uy = connectedComponentIn (Set.range r)ᶜ z :=
      connectedComponentIn_eq hzUy
    exact hne (hxz.trans hyz.symm)
  let gx := aroundMap r x
  let gy := aroundMap r y
  have hgx : ∀ z, gx z ≠ 0 := aroundMap_ne_zero r hx
  have hgy : ∀ z, gy z ≠ 0 := aroundMap_ne_zero r hy
  let ax := windingAround r x hx
  let ay := windingAround r y hy
  have hax : ax ≠ 0 := windingAround_ne_zero_of_bounded_component r hinj hx hxb
  have hay : ay ≠ 0 := windingAround_ne_zero_of_bounded_component r hinj hy hyb
  let px := zpowMap gx hgx ay
  let py := zpowMap gy hgy (-ax)
  have hpx0 : ∀ z, px z ≠ 0 := zpowMap_ne_zero gx hgx ay
  have hpy0 : ∀ z, py z ≠ 0 := zpowMap_ne_zero gy hgy (-ax)
  let q : C(Circle, ℂ) := px * py
  have hq0 : ∀ z, q z ≠ 0 := fun z ↦ mul_ne_zero (hpx0 z) (hpy0 z)
  have hpxw : winding px hpx0 = ay * ax := by
    exact winding_zpow gx hgx ay
  have hpyw : winding py hpy0 = (-ax) * ay := by
    exact winding_zpow gy hgy (-ax)
  have hqwind : winding q hq0 = 0 := by
    calc
      winding q hq0 = winding (px * py)
          (fun z ↦ mul_ne_zero (hpx0 z) (hpy0 z)) :=
        winding_congr rfl _ _
      _ = winding px hpx0 + winding py hpy0 :=
        winding_mul px py hpx0 hpy0
      _ = ay * ax + (-ax) * ay := by rw [hpxw, hpyw]
      _ = 0 := by ring
  obtain ⟨l, hl⟩ := (hasLog_iff_winding_eq_zero q hq0).mpr hqwind
  have hrclosed : Topology.IsClosedEmbedding r :=
    r.continuous.isClosedEmbedding hinj
  obtain ⟨L, hL⟩ := l.exists_extension hrclosed
  let H : ℂ → ℂ := fun z ↦ Complex.exp (L z) * (z - y) ^ ax
  have hHcont : ContinuousOn H (closure Ux) := by
    apply L.continuous.cexp.continuousOn.mul
    exact (continuous_id.sub continuous_const).continuousOn.zpow₀ ax fun z hz ↦
      Or.inl (sub_ne_zero.mpr fun hzy ↦ hyncl (hzy ▸ hz))
  have hH0 : ∀ z ∈ closure Ux, H z ≠ 0 := by
    intro z hz
    exact mul_ne_zero (Complex.exp_ne_zero _)
      (zpow_ne_zero ax (sub_ne_zero.mpr fun hzy ↦ hyncl (hzy ▸ hz)))
  apply no_nonzero_extension_over_bounded_open Ux hUxopen hxb x
    (mem_connectedComponentIn hx) ay hay H hHcont hH0
  intro z hz
  obtain ⟨t, rfl⟩ := frontier_component_subset_range r hx hz
  have hLt : L (r t) = l t := DFunLike.congr_fun hL t
  change Complex.exp (L (r t)) * (r t - y) ^ ax = (r t - x) ^ ay
  rw [hLt, hl]
  change ((r t - x) ^ ay * (r t - y) ^ (-ax)) * (r t - y) ^ ax =
    (r t - x) ^ ay
  rw [mul_assoc, zpow_neg_mul_zpow_self ax (sub_ne_zero.mpr fun h ↦ hy ⟨t, h⟩),
    mul_one]

end

end Submission.Components
