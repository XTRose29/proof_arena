import Mathlib
import Submission.Helpers

namespace Submission

theorem brauer_fowler :
    ∃ f : ℕ → ℕ, ∀ (G : Type) [Group G] [Finite G],
      IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
      ∀ t : G, orderOf t = 2 →
        Nat.card G ≤ f (Nat.card (Subgroup.centralizer ({t} : Set G))) := by
  refine ⟨fun n => (2 * n * n).factorial, ?_⟩
  intro G _ _ hsimple hnoncomm t ht
  classical
  letI : IsSimpleGroup G := hsimple
  letI := Fintype.ofFinite G

  have hcenter : Subgroup.center G = ⊥ := by
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnoncomm
      letI : IsMulCommutative G := Subgroup.center_eq_top_iff.mp h
      exact (hab (mul_comm' a b)).elim

  have ht_ne_one : t ≠ 1 := by
    intro ht1
    rw [ht1, orderOf_one] at ht
    omega

  let C := Subgroup.centralizer ({t} : Set G)
  have hC : C ≠ ⊤ := by
    intro hCtop
    have htcenter : t ∈ Subgroup.center G :=
      (Subgroup.centralizer_eq_top_iff_subset.mp hCtop) (by simp)
    have ht1 : t = 1 := by simpa [hcenter] using htcenter
    exact ht_ne_one ht1

  let I := MulAction.orbit (ConjAct G) t
  have horder (a : I) : orderOf (a : G) = 2 := by
    rcases ConjAct.mem_orbit_conjAct.mp a.2 with ⟨u, hu⟩
    exact (hu.orderOf_eq (u : G)).trans ht

  have hmc : Fintype.card I * Fintype.card C = Fintype.card G := by
    simpa only [I, C, Nat.card_eq_fintype_card] using
      Helpers.nat_card_conj_orbit_mul_centralizer t

  have hIpos : 0 < Fintype.card I := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨t, MulAction.mem_orbit_self t⟩⟩

  have hItwo : 2 ≤ Fintype.card I := by
    rw [Nat.two_le_iff]
    refine ⟨hIpos.ne', ?_⟩
    intro hIone
    have hcard : Nat.card C = Nat.card G := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      simpa [hIone] using hmc
    exact hC (Subgroup.eq_top_of_card_eq C hcard)

  let D := {p : I × I // p.2 ≠ p.1}
  let N := {x : G // x ≠ 1}
  let product : D → N := fun d =>
    ⟨(d.1.1 : G) * (d.1.2 : G), by
      intro hprod
      have hne : (d.1.1 : G) ≠ (d.1.2 : G) := fun h =>
        d.2 (Subtype.ext h.symm)
      have hnot := mul_notMem_of_orderOf_eq_two
        (horder d.1.1) (horder d.1.2) hne
      apply hnot
      simp [hprod]⟩
  let fiber (x : N) : Finset D := Finset.univ.filter fun d => product d = x

  obtain ⟨x, -, hxmax⟩ := Finset.exists_max_image (Finset.univ : Finset N)
    (fun y => (fiber y).card) ⟨⟨t, ht_ne_one⟩, Finset.mem_univ _⟩

  have hDcard : Fintype.card D =
      Fintype.card I * (Fintype.card I - 1) := by
    simpa only [D] using (Helpers.card_prod_ne (α := I))

  have hDle : Fintype.card D ≤ Fintype.card N * (fiber x).card := by
    calc
      Fintype.card D =
          ∑ y ∈ (Finset.univ : Finset N), (fiber y).card := by
        simpa [fiber] using
          (Finset.card_eq_sum_card_fiberwise
            (s := (Finset.univ : Finset D))
            (t := (Finset.univ : Finset N))
            (f := product) (by intro d hd; simp))
      _ ≤ ∑ _y ∈ (Finset.univ : Finset N), (fiber x).card := by
        exact Finset.sum_le_sum fun y hy => hxmax y (by simp)
      _ = Fintype.card N * (fiber x).card := by simp

  have hDpos : 0 < Fintype.card D := by
    rw [hDcard]
    exact Nat.mul_pos hIpos (Nat.sub_pos_of_lt (by omega))

  have hfiber_pos : 0 < (fiber x).card := by
    by_contra h
    have hzero : (fiber x).card = 0 := Nat.eq_zero_of_not_pos h
    have hDzero : Fintype.card D = 0 :=
      Nat.eq_zero_of_le_zero (by simpa [hzero] using hDle)
    exact (Nat.ne_of_gt hDpos) hDzero

  obtain ⟨d0, hd0⟩ := Finset.card_pos.mp hfiber_pos
  let dbase : ↥(fiber x) := ⟨d0, hd0⟩

  have hproduct (d : ↥(fiber x)) :
      (d.1.1.1 : G) * (d.1.1.2 : G) = (x : G) := by
    have hdmem := d.2
    change d.1 ∈ Finset.univ.filter (fun e => product e = x) at hdmem
    have hd : product d.1 = x := (Finset.mem_filter.mp hdmem).2
    simpa only [product] using congrArg Subtype.val hd

  have hsemiconj (d : ↥(fiber x)) :
      SemiconjBy (d.1.1.1 : G) (x : G) (x : G)⁻¹ := by
    have ha := inv_eq_self_of_orderOf_eq_two (horder d.1.1.1)
    have hb := inv_eq_self_of_orderOf_eq_two (horder d.1.1.2)
    have haa : (d.1.1.1 : G) * (d.1.1.1 : G) = 1 := by
      calc
        (d.1.1.1 : G) * (d.1.1.1 : G) =
            (d.1.1.1 : G)⁻¹ * (d.1.1.1 : G) := by rw [ha]
        _ = 1 := by simp
    show (d.1.1.1 : G) * (x : G) = (x : G)⁻¹ * (d.1.1.1 : G)
    calc
      (d.1.1.1 : G) * (x : G) =
          (d.1.1.1 : G) * ((d.1.1.1 : G) * (d.1.1.2 : G)) := by
            rw [hproduct d]
      _ = (d.1.1.2 : G) := by rw [← mul_assoc, haa, one_mul]
      _ = (x : G)⁻¹ * (d.1.1.1 : G) := by
        rw [← hproduct d, mul_inv_rev, ha, hb, mul_assoc, haa, mul_one]

  let Cx := Subgroup.centralizer ({(x : G)} : Set G)
  let embed : ↥(fiber x) → Cx := fun d =>
    ⟨(d.1.1.1 : G) * (dbase.1.1.1 : G), by
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa only [inv_inv] using
        ((hsemiconj d).inv_right.mul_left (hsemiconj dbase)).eq⟩

  have hembed : Function.Injective embed := by
    intro d e hde
    have hfirst_val : (d.1.1.1 : G) = (e.1.1.1 : G) := by
      have h := congrArg Subtype.val hde
      change (d.1.1.1 : G) * (dbase.1.1.1 : G) =
        (e.1.1.1 : G) * (dbase.1.1.1 : G) at h
      exact mul_right_cancel h
    have hfirst : d.1.1.1 = e.1.1.1 := Subtype.ext hfirst_val
    have hsecond_val : (d.1.1.2 : G) = (e.1.1.2 : G) := by
      apply mul_left_cancel (a := (d.1.1.1 : G))
      calc
        (d.1.1.1 : G) * (d.1.1.2 : G) = (x : G) := hproduct d
        _ = (e.1.1.1 : G) * (e.1.1.2 : G) := (hproduct e).symm
        _ = (d.1.1.1 : G) * (e.1.1.2 : G) := by rw [hfirst_val]
    have hsecond : d.1.1.2 = e.1.1.2 := Subtype.ext hsecond_val
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hfirst hsecond

  have hfiber_le : (fiber x).card ≤ Fintype.card Cx := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective embed hembed

  have hcount : Fintype.card I * (Fintype.card I - 1) ≤
      Fintype.card G * (fiber x).card := by
    calc
      Fintype.card I * (Fintype.card I - 1) = Fintype.card D := hDcard.symm
      _ ≤ Fintype.card N * (fiber x).card := hDle
      _ ≤ Fintype.card G * (fiber x).card := by
        exact Nat.mul_le_mul_right _
          (Fintype.card_le_of_injective (fun y : N => (y : G)) Subtype.val_injective)

  have hpred : Fintype.card I - 1 ≤ Fintype.card C * (fiber x).card := by
    apply Nat.le_of_mul_le_mul_left _ hIpos
    have hcount' := hcount
    rw [← hmc] at hcount'
    simpa only [Nat.mul_assoc] using hcount'

  have hIle : Fintype.card I ≤ 2 * (Fintype.card C * (fiber x).card) := by
    omega

  have hGle : Fintype.card G ≤
      2 * Fintype.card C * Fintype.card C * (fiber x).card := by
    rw [← hmc]
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_right (Fintype.card C) hIle

  have hGleCx : Fintype.card G ≤
      2 * Fintype.card C * Fintype.card C * Fintype.card Cx :=
    hGle.trans (Nat.mul_le_mul_left _ hfiber_le)

  have hCx : Cx ≠ ⊤ := by
    intro hCxtop
    have hxcenter : (x : G) ∈ Subgroup.center G :=
      (Subgroup.centralizer_eq_top_iff_subset.mp hCxtop) (by simp)
    have hx1 : (x : G) = 1 := by simpa [hcenter] using hxcenter
    exact x.2 hx1

  have hindex : Cx.index ≤ 2 * Fintype.card C * Fintype.card C := by
    have hCxcardpos : 0 < Fintype.card Cx :=
      Fintype.card_pos_iff.mpr ⟨⟨1, Cx.one_mem⟩⟩
    have hindex_card : Cx.index * Fintype.card Cx = Fintype.card G := by
      simpa only [Nat.card_eq_fintype_card] using Cx.index_mul_card
    refine Nat.le_of_mul_le_mul_right ?_ hCxcardpos
    rw [hindex_card]
    exact hGleCx

  have hfinal : Nat.card G ≤
      (2 * Fintype.card C * Fintype.card C).factorial :=
    (Helpers.card_le_factorial_index_of_ne_top Cx hCx).trans (Nat.factorial_le hindex)
  simpa only [C, Nat.card_eq_fintype_card] using hfinal

end Submission
