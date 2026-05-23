import Mathlib

namespace Submission

theorem mulCayley_connected_iff_closure_eq_top {G : Type*} [Group G]
    (S : Set G) :
    (SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤ := by
  let C := SimpleGraph.mulCayley S
  let H := Subgroup.closure S
  let leftMulHom (a : G) : C →g C :=
    { toFun := fun x => a * x
      map_rel' := by
        intro x y hxy
        rwa [SimpleGraph.mulCayley_adj_mul_iff_right] }
  have reachable_left_mul (a : G) {x y : G} (hxy : C.Reachable x y) :
      C.Reachable (a * x) (a * y) := by
    exact hxy.map (leftMulHom a)
  constructor
  · intro hconn
    apply le_antisymm le_top
    intro g _
    have hr : C.Reachable 1 g := hconn 1 g
    rcases hr with ⟨p⟩
    have walk_mem : ∀ {u v : G}, C.Walk u v → u⁻¹ * v ∈ H := by
      intro u v p
      induction p with
      | nil => simp [H]
      | cons h p ih =>
          rename_i u v w
          rw [SimpleGraph.mulCayley_adj] at h
          rcases h with ⟨_, hs | hs⟩
          · have hstep : u⁻¹ * v ∈ H := Subgroup.subset_closure hs
            have hmul : (u⁻¹ * v) * (v⁻¹ * w) ∈ H := H.mul_mem hstep ih
            simpa [mul_assoc, H] using hmul
          · have hstep : u⁻¹ * v ∈ H := by
              have hinv : (v⁻¹ * u)⁻¹ ∈ H := H.inv_mem (Subgroup.subset_closure hs)
              simpa [mul_inv_rev, H] using hinv
            have hmul : (u⁻¹ * v) * (v⁻¹ * w) ∈ H := H.mul_mem hstep ih
            simpa [mul_assoc, H] using hmul
    have hp := walk_mem p
    simpa [H] using hp
  · intro htop
    have reachable_mul {a b : G} (ha : C.Reachable 1 a) (hb : C.Reachable 1 b) :
        C.Reachable 1 (a * b) := by
      have hb' : C.Reachable a (a * b) := by
        simpa using reachable_left_mul a hb
      exact ha.trans hb'
    have reachable_inv {a : G} (ha : C.Reachable 1 a) : C.Reachable 1 a⁻¹ := by
      have hsymm : C.Reachable a 1 := ha.symm
      have hmap : C.Reachable (a⁻¹ * a) (a⁻¹ * 1) := reachable_left_mul a⁻¹ hsymm
      simpa using hmap
    let R : Subgroup G :=
      { carrier := {g | C.Reachable 1 g}
        one_mem' := by exact SimpleGraph.Reachable.refl 1
        mul_mem' := by
          intro a b ha hb
          exact reachable_mul ha hb
        inv_mem' := by
          intro a ha
          exact reachable_inv ha }
    have hS : S ≤ R := by
      intro s hs
      by_cases h1 : s = 1
      · simp [R, h1]
      · have hne : (1 : G) ≠ s := by
          simpa [eq_comm] using h1
        have hadj : C.Adj 1 s := by
          rw [SimpleGraph.mulCayley_adj]
          simp [hne, hs]
        exact hadj.reachable
    have hle : H ≤ R := (Subgroup.closure_le R).2 hS
    constructor
    intro a b
    have hb : b ∈ H := by
      change b ∈ Subgroup.closure S
      rw [htop]
      trivial
    have ha : a ∈ H := by
      change a ∈ Subgroup.closure S
      rw [htop]
      trivial
    have hdiff : a⁻¹ * b ∈ H := H.mul_mem (H.inv_mem ha) hb
    have hr : C.Reachable 1 (a⁻¹ * b) := hle hdiff
    have hmap : C.Reachable (a * 1) (a * (a⁻¹ * b)) := reachable_left_mul a hr
    simpa [mul_assoc] using hmap

end Submission
