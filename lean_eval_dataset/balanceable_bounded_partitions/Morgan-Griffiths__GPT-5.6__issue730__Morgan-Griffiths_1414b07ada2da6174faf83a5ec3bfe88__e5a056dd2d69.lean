import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/balanceable_bounded_partitions_8b215d0efe/Core.lean
open scoped BigOperators
open Finset Multiset
namespace BBP

/-- all the small sums, expressed with sub-multisets. -/
def Reaches (s : Multiset ℕ) : Prop :=
  ∀ t : ℕ, t ≤ s.sum → ∃ u : Multiset ℕ, u ≤ s ∧ u.sum = t

lemma reaches_replicate_one (c : ℕ) : Reaches (Multiset.replicate c 1) := by
  intro t ht
  refine ⟨Multiset.replicate t 1, ?_, ?_⟩
  · -- counts or exists
    exact (Multiset.replicate_le_replicate _).2 (by simpa using ht)
  · simp

lemma reaches_add_one_coin {s : Multiset ℕ} (hs : Reaches s) {a : ℕ}
    (ha : a ≤ s.sum + 1) : Reaches (s + {a}) := by
  intro t ht
  by_cases h : t ≤ s.sum
  · obtain ⟨u, hu, hut⟩ := hs t h
    refine ⟨u, hu.trans ?_, hut⟩
    exact Multiset.le_add_right _ _
  · have htbig : s.sum < t := Nat.lt_of_not_ge h
    have hta : a ≤ t := by omega
    have hsub : t - a ≤ s.sum := by
      have := ht
      simp [Multiset.sum_add] at this
      omega
    obtain ⟨u, hu, hut⟩ := hs (t-a) hsub
    refine ⟨u + {a}, ?_, ?_⟩
    · exact Multiset.add_le_add_right hu
    · simp [Multiset.sum_add, hut]
      omega

lemma reaches_ones_add {k c : ℕ} (hc : k - 1 ≤ c)
    (w : Multiset ℕ) (hw : ∀ a ∈ w, a ≤ k) :
    Reaches (Multiset.replicate c 1 + w) := by
  induction w using Multiset.induction_on with
  | empty => simpa using reaches_replicate_one c
  | @cons a w ih =>
    have ha : a ≤ k := hw _ (by simp)
    have hw' : ∀ b ∈ w, b ≤ k := by intro b hb; exact hw _ (by simp [hb])
    have hi := ih hw'
    have hak : k ≤ c + 1 := by omega
    have hasum : a ≤ (Multiset.replicate c 1 + w).sum + 1 := by
      simp [Multiset.sum_add] -- maybe
      have : a ≤ c + 1 := le_trans ha hak
      simpa using (le_trans this (by
        have : c + 1 ≤ c + w.sum + 1 := by omega
        exact this))
    have hh := reaches_add_one_coin hi hasum
    -- rearrange
    change Reaches (Multiset.replicate c 1 + ({a} + w))
    simpa [add_assoc, add_comm, add_left_comm] using hh

/-- Counting all the elements over a containing finset. -/
lemma sum_count_mul (s : Multiset ℕ) (U : Finset ℕ)
    (hU : ∀ a ∈ s, a ∈ U) :
    (∑ a ∈ U, s.count a * a) = s.sum := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    have hx : x ∈ U := hU _ (by simp)
    have hs : ∀ a ∈ s, a ∈ U := by intro a ha; exact hU _ (by simp [ha])
    specialize ih hs
    -- count_cons, sum linear
    simp [Multiset.count_cons, ih, Finset.sum_add_distrib, hx,
      Nat.add_mul]
    omega

/-- The list of block weights other than `m`. -/
noncomputable def blocks (k m : ℕ) (s : Multiset ℕ) : Multiset ℕ :=
  ∑ a ∈ (Finset.Icc 1 k).erase m, Multiset.replicate (s.count a / m) a

def lost (k m : ℕ) (s : Multiset ℕ) : ℕ :=
  ∑ a ∈ (Finset.Icc 1 k).erase m, (s.count a % m) * a

lemma sum_blocks (k m : ℕ) (s : Multiset ℕ) :
    (blocks k m s).sum =
      ∑ a ∈ (Finset.Icc 1 k).erase m, (s.count a / m) * a := by
  classical
  simp [blocks, Multiset.sum_sum, Multiset.sum_replicate, Nat.nsmul_eq_mul]

lemma mem_blocks_le {k m : ℕ} (s : Multiset ℕ) :
    ∀ a ∈ blocks k m s, a ≤ k := by
  classical
  intro a ha
  -- membership in finset-sum of multisets
  change a ∈ (∑ b ∈ (Finset.Icc 1 k).erase m,
    Multiset.replicate (s.count b / m) b) at ha
  rcases (Multiset.mem_sum.mp ha) with ⟨b, hb, hb'⟩
  have hbI : b ∈ Finset.Icc 1 k := Finset.mem_of_mem_erase hb
  have hab : a = b := (Multiset.mem_replicate.mp hb').2
  simpa [hab] using (Finset.mem_Icc.mp hbI).2

end BBP

namespace BBP
open scoped BigOperators
open Finset Multiset
lemma total_blocks {k m : ℕ} (hm : m ∈ Finset.Icc 1 k)
    (s : Multiset ℕ) (hs : ∀ a ∈ s, 1 ≤ a ∧ a ≤ k) :
    s.sum = m * (s.count m + (blocks k m s).sum) + lost k m s := by
  classical
  have hU : ∀ a ∈ s, a ∈ Finset.Icc 1 k := by
    intro a ha; exact Finset.mem_Icc.mpr (hs a ha)
  have hcount := sum_count_mul s (Finset.Icc 1 k) hU
  -- split out m
  have herase := Finset.sum_erase_add (Finset.Icc 1 k) (fun a => s.count a * a) hm
  -- express others
  have hterm (a : ℕ) : s.count a * a =
      ((s.count a / m) * a) * m + (s.count a % m) * a := by
    calc
      s.count a * a = (s.count a % m + m * (s.count a / m)) * a := by
        rw [Nat.mod_add_div]
      _ = ((s.count a / m) * a) * m + (s.count a % m) * a := by ring
  have hothers :
      (∑ a ∈ (Finset.Icc 1 k).erase m, s.count a * a) =
        (∑ a ∈ (Finset.Icc 1 k).erase m, (s.count a / m) * a) * m
          + lost k m s := by
    simp_rw [hterm]
    simp [Finset.sum_add_distrib, Finset.sum_mul, lost]
  rw [← hcount]
  rw [← herase]
  rw [hothers, sum_blocks]
  ring
end BBP
namespace BBP
open scoped BigOperators
open Finset Multiset

def inflate (m : ℕ) (u : Multiset ℕ) : Multiset ℕ :=
  u.bind (fun a => Multiset.replicate m a)

lemma inflate_le {m : ℕ} {u v : Multiset ℕ} (h : u ≤ v) :
    inflate m u ≤ inflate m v := by
  rcases Multiset.le_iff_exists_add.mp h with ⟨d, rfl⟩
  apply Multiset.le_iff_exists_add.mpr
  refine ⟨inflate m d, ?_⟩
  simp [inflate, Multiset.add_bind]


lemma sum_inflate (m : ℕ) (u : Multiset ℕ) : (inflate m u).sum = u.sum * m := by
  classical
  simp [inflate, Multiset.sum_bind, Multiset.sum_replicate]
  -- multiplication was on the other side
  simpa [mul_comm] using
    (Multiset.sum_map_mul_right (s:=u) (f:=(fun x : ℕ => x)) (a:=m))

lemma replicate_bind_const (a m q : ℕ) :
    (Multiset.replicate q a).bind (fun a : ℕ => Multiset.replicate m a)
      = Multiset.replicate (q*m) a := by
  induction q with
  | zero => simp
  | succ q ih =>
    simp [Multiset.replicate_succ, Multiset.add_bind, ih, add_mul]
    rw [add_comm]
    exact (Multiset.replicate_add _ _ _).symm

lemma inflate_sum_blocks (k m : ℕ) (s : Multiset ℕ) :
    inflate m (blocks k m s) =
      ∑ a ∈ (Finset.Icc 1 k).erase m,
        Multiset.replicate ((s.count a / m) * m) a := by
  classical
  unfold inflate blocks
  generalize (Finset.Icc 1 k).erase m = E
  -- induction finset twice-sum notation simplified via `sum_bind`? add_bind over finset sums
  induction E using Finset.induction with
  | empty => simp
  | @insert a E ha ih =>
    simp [Finset.sum_insert, ha, Multiset.add_bind, ih, replicate_bind_const]

lemma count_finset_replicate (E : Finset ℕ) (f : ℕ → ℕ) (x : ℕ) :
    Multiset.count x (∑ a ∈ E, Multiset.replicate (f a) a) =
      if x ∈ E then f x else 0 := by
  classical
  induction E using Finset.induction with
  | empty => simp
  | @insert a E ha ih =>
    by_cases hxa : x = a
    · subst x
      simp [Finset.sum_insert, ha, Multiset.count_add,
        Multiset.count_replicate, ha, ih]
    · simp [Finset.sum_insert, ha, Multiset.count_add,
        Multiset.count_replicate, hxa, Ne.symm hxa, ih]

lemma base_le {k m : ℕ} (hm : m ∈ Finset.Icc 1 k)
    (s : Multiset ℕ) (hs : ∀ a ∈ s, 1 ≤ a ∧ a ≤ k) :
    Multiset.replicate (s.count m) m + inflate m (blocks k m s) ≤ s := by
  classical
  rw [inflate_sum_blocks]
  apply Multiset.le_iff_count.mpr
  intro x
  rw [Multiset.count_add]
  simp [Multiset.count_replicate, count_finset_replicate]
  by_cases hx : x ∈ (Finset.Icc 1 k).erase m
  · have hne : m ≠ x := Ne.symm (Finset.mem_erase.mp hx).1
    have hxI := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hx))
    simp [hxI.1, hxI.2, hne, Ne.symm hne]
    exact Nat.div_mul_le_self _ _
  · by_cases hxm : m = x
    · subst x
      simp
    · by_cases cond : 1 ≤ x ∧ x ≤ k
      · exfalso
        apply hx
        exact Finset.mem_erase.mpr ⟨by exact Ne.symm hxm, Finset.mem_Icc.mpr cond⟩
      · simp [hxm, cond]

end BBP
namespace BBP
open scoped BigOperators
open Finset Multiset

lemma subset_good
    {k h m : ℕ} (s : Multiset ℕ)
    (hs : ∀ a ∈ s, 1 ≤ a ∧ a ≤ k)
    (hsum : s.sum = 2*h)
    (hdvd : ∀ a, 1 ≤ a → a ≤ k → a ∣ h)
    (hm : m ∈ Finset.Icc 1 k)
    (hcm : k-1 ≤ s.count m)
    (hl : lost k m s ≤ h) :
    ∃ v : Multiset ℕ, v ≤ s ∧ v.sum = h := by
  classical
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  let A : Multiset ℕ := Multiset.replicate (s.count m) 1
  let B : Multiset ℕ := blocks k m s
  have hreach : Reaches (A+B) := by
    apply reaches_ones_add hcm
    exact mem_blocks_le s
  have hdiv := hdvd m (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
  have htot := total_blocks hm s hs
  have hbound : h / m ≤ (A+B).sum := by
    have hmle : h ≤ m * (s.count m + (blocks k m s).sum) := by
      rw [hsum] at htot
      omega
    have hx : h/m ≤ s.count m + (blocks k m s).sum := by
      apply Nat.le_of_mul_le_mul_right (c:=m) ?_ hmpos
      rw [Nat.div_mul_cancel hdiv]
      simpa [mul_comm] using hmle
    simpa [A, B, Multiset.sum_add] using hx

  obtain ⟨u, hu, hus⟩ := hreach (h/m) hbound
  -- split at A
  let u₁ := u ∩ A
  let u₂ := u - A
  have hu₁ : u₁ ≤ A := Multiset.inter_le_right
  have hu₂ : u₂ ≤ B := by
    apply Multiset.sub_le_iff_le_add'.2
    -- u ≤ A + B
    simpa [add_comm] using hu
  have u_eq : u = u₁ + u₂ := by
    have := Multiset.sub_add_inter u A
    -- u₂ + u₁ = u
    simpa [u₁, u₂, add_comm] using this.symm
  -- interpret u₁
  let v₁ : Multiset ℕ := u₁.map (fun _ => m)
  let v₂ : Multiset ℕ := inflate m u₂
  have hv₁ : v₁ ≤ Multiset.replicate (s.count m) m := by
    have := Multiset.map_le_map (f:= fun _ : ℕ => m) hu₁
    simpa [A, v₁] using this
  have hv₂ : v₂ ≤ inflate m (blocks k m s) := by
    exact inflate_le hu₂
  have hv0 : v₁ + v₂ ≤
      Multiset.replicate (s.count m) m + inflate m (blocks k m s) := by
    calc
      _ ≤ Multiset.replicate (s.count m) m + v₂ := Multiset.add_le_add_right hv₁
      _ ≤ _ := Multiset.add_le_add_left hv₂
  have hv : v₁ + v₂ ≤ s := hv0.trans (base_le hm s hs)
  refine ⟨v₁+v₂, hv, ?_⟩
  have sv₁ : v₁.sum = u₁.card * m := by simp [v₁]
  have allone : ∀ x ∈ u₁, x = 1 := by
    intro x hx
    have hxa : x ∈ A := Multiset.mem_of_le hu₁ hx
    exact (Multiset.mem_replicate.mp (by simpa [A] using hxa)).2
  have lemma_one (r : Multiset ℕ) : (∀ x ∈ r, x = 1) → r.sum = r.card := by
    intro ha
    induction r using Multiset.induction_on with
    | empty => simp
    | @cons x t ih =>
      have ex : x = 1 := ha x (by simp)
      have it : ∀ z ∈ t, z = 1 := by intro z hz; exact ha z (by simp [hz])
      simp [ex, ih it]
      omega
  have ones : u₁.sum = u₁.card := lemma_one u₁ allone
  have horig : h / m * m = h := Nat.div_mul_cancel hdiv
  have su : u₁.sum + u₂.sum = h/m := by
    have := hus
    rw [u_eq, Multiset.sum_add] at this
    exact this
  rw [Multiset.sum_add, sv₁, sum_inflate, ← ones, ← horig, ← su]
  ring

end BBP
namespace BBP
open scoped BigOperators
open Finset Multiset
lemma lcm_pos (k : ℕ) : 0 < Nat.lcmUpto k := Nat.pos_of_ne_zero (by simp [Nat.lcmUpto])
lemma dvd_lcm {k a:ℕ} (h1:1≤a) (h2:a≤k) : a ∣ Nat.lcmUpto k :=
  Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨h1,h2⟩)

/-- The two-size obstruction. -/
def badparts (h i : ℕ) : Multiset ℕ :=
    Multiset.replicate (2*h/i) i +
      (if 2*h % i = 0 then 0 else {2*h % i})

lemma badparts_sum (h i:ℕ) : (badparts h i).sum = 2*h := by
  classical
  unfold badparts
  simp [Multiset.sum_add, Multiset.sum_replicate]
  by_cases hz : 2 * h % i = 0
  · simp [hz]
    have he := Nat.mod_add_div (2*h) i
    calc
      2 * h / i * i = i * (2*h/i) := by ac_rfl
      _ = 2*h := by omega
  · simp [hz, Multiset.sum_add]
    have he := Nat.mod_add_div (2*h) i
    calc
      2*h/i*i + 2*h%i = 2*h%i + i*(2*h/i) := by ac_rfl
      _ = 2*h := he

lemma badparts_pos {h i} (hi : 0 < i) : ∀ a ∈ badparts h i, 0 < a := by
  intro a ha
  rcases (Multiset.mem_add.mp ha) with h'|h'
  · have : a = i := (Multiset.mem_replicate.mp h').2
    omega
  · split_ifs at h'
    · simp at h'
    · have : a = 2*h % i := by simpa using h'
      omega

lemma badparts_bound {h i k} (hi : 0 < i) (hik : i ≤ k) :
    ∀ a ∈ badparts h i, a ≤ k := by
  intro a ha
  rcases (Multiset.mem_add.mp ha) with h'|h'
  · rw [(Multiset.mem_replicate.mp h').2]; exact hik
  · split_ifs at h'
    · simp at h'
    · have hx : a = 2*h % i := by simpa using h'
      have := Nat.mod_lt (2*h) hi
      omega

lemma sum_of_sub_le (s t : Multiset ℕ) (h : s ≤ t) : s.sum ≤ t.sum := by
  rcases Multiset.le_iff_exists_add.mp h with ⟨u,rfl⟩
  simp [Multiset.sum_add]

end BBP
namespace BBP
lemma balanced_of_half {h : ℕ} {s : Multiset ℕ} (hs : s.sum = 2*h)
    (hv : ∃ v : Multiset ℕ, v ≤ s ∧ v.sum = h) :
    ∃ u v : Multiset ℕ, u + v = s ∧ u.sum = v.sum := by
  rcases hv with ⟨u, hu, hu'⟩
  obtain ⟨v, hv⟩ := Multiset.le_iff_exists_add.mp hu
  refine ⟨u, v, hv.symm, ?_⟩
  -- calculate complementary sum
  rw [hv, Multiset.sum_add, hu'] at hs
  omega
end BBP

-- END INLINED FILE: Mathlib/Support/balanceable_bounded_partitions_8b215d0efe/Core.lean

-- BEGIN INLINED FILE: Mathlib/Support/balanceable_bounded_partitions_8b215d0efe/Lower.lean
open scoped BigOperators
open Finset Multiset
namespace BBP

/-- A balanced decomposition of an even-sum multiset has a part of the half sum. -/
lemma half_of_balanced {h : ℕ} {s : Multiset ℕ} (hs : s.sum = 2*h)
    (hb : ∃ u v : Multiset ℕ, u + v = s ∧ u.sum = v.sum) :
    ∃ u : Multiset ℕ, u ≤ s ∧ u.sum = h := by
  rcases hb with ⟨u, v, huv, heq⟩
  have hu : u ≤ s := Multiset.le_iff_exists_add.mpr ⟨v, huv.symm⟩
  have hcalc : u.sum = h := by
    rw [← huv, Multiset.sum_add, heq] at hs
    omega
  exact ⟨u, hu, hcalc⟩

/-- Any balanced decomposition makes the total sum twice one of the sums. -/
lemma even_of_balanced {s : Multiset ℕ}
    (hb : ∃ u v : Multiset ℕ, u + v = s ∧ u.sum = v.sum) :
    ∃ h : ℕ, s.sum = 2*h := by
  rcases hb with ⟨u,v, huv, heq⟩
  refine ⟨u.sum, ?_⟩
  rw [← huv, Multiset.sum_add, heq]
  omega

private lemma mod_double_fixed {i r : ℕ} (hi : 0 < i) (hr : r < i)
    (he : (2*r) % i = r) : r = 0 := by
  by_cases hc : 2*r < i
  · have hm : (2*r) % i = 2*r := Nat.mod_eq_of_lt hc
    rw [hm] at he
    omega
  · have hc' : i ≤ 2*r := by omega
    have hl : 2*r - i < i := by omega
    have hm : (2*r) % i = 2*r - i := by
      rw [Nat.mod_eq_sub_mod hc']
      exact Nat.mod_eq_of_lt hl
    rw [hm] at he
    omega

/-- For the special two-size multiset, a submultiset of exactly half its sum
can exist only when the large entry size divides that half. -/
lemma dvd_of_badparts_half {h i : ℕ} (hi : 0 < i)
    (hex : ∃ u : Multiset ℕ, u ≤ badparts h i ∧ u.sum = h) :
    i ∣ h := by
  classical
  rcases hex with ⟨u, hu, hus⟩
  let A : Multiset ℕ := Multiset.replicate (2*h / i) i
  let r : ℕ := 2*h % i
  let E : Multiset ℕ := if r = 0 then 0 else {r}
  have hut : u ≤ A + E := by
    simpa [A, E, r, badparts] using hu
  let u₁ : Multiset ℕ := u ∩ A
  let u₂ : Multiset ℕ := u - A
  have hu₁ : u₁ ≤ A := Multiset.inter_le_right
  have hu₂ : u₂ ≤ E := by
    exact (Multiset.sub_le_iff_le_add').2 hut
  have ueq : u = u₁ + u₂ := by
    have hh := Multiset.sub_add_inter u A
    -- hh : u - A + u ∩ A = u
    simpa [u₁, u₂, add_comm] using hh.symm
  have hrep : ∃ c ≤ 2*h / i, u₁ = Multiset.replicate c i := by
    have hh : u₁ ≤ Multiset.replicate (2*h / i) i := by simpa [A] using hu₁
    exact (Multiset.le_replicate_iff).1 hh
  rcases hrep with ⟨c, hc, hcu⟩
  by_cases rz : r = 0
  · have hE : E = 0 := by simp [E, rz]
    have hz : u₂ = 0 := (Multiset.le_zero.mp (by simpa [hE] using hu₂))
    refine ⟨c, ?_⟩
    have sh : h = c * i := by
      have := hus
      rw [ueq, Multiset.sum_add, hcu, hz] at this
      simpa using this.symm
    -- divisibility witness is h = i * c
    -- `Dvd` for naturals uses i * _
    simpa [mul_comm] using sh
  · have hu₂' : u₂ ≤ {r} := by simpa [E, rz] using hu₂
    rcases (Multiset.le_singleton.mp hu₂') with hz | hz
    · -- no exceptional element
      refine ⟨c, ?_⟩
      have sh : h = c * i := by
        have := hus
        rw [ueq, Multiset.sum_add, hcu, hz] at this
        simpa using this.symm
      simpa [mul_comm] using sh
    · -- the exceptional element is taken; this is impossible unless its residue is zero
      have sh : h = c * i + r := by
        have := hus
        rw [ueq, Multiset.sum_add, hcu, hz] at this
        simpa using this.symm
      have rlt : r < i := by
        dsimp [r]
        exact Nat.mod_lt _ hi
      have hrhi : h % i = r := by
        rw [sh]
        -- remove the multiple of i
        have hrmod : r % i = r := Nat.mod_eq_of_lt rlt
        simp [Nat.add_mod, Nat.mul_mod, hi.ne', hrmod]
      have he : (2*r) % i = r := by
        have hx : (2*h) % i = r := by rfl
        rw [Nat.mul_mod] at hx
        -- replace h mod i
        simpa [hrhi] using hx
      have zr : r = 0 := mod_double_fixed hi rlt he
      exact False.elim (rz zr)

/-- Thus a balanced decomposition of `badparts` forces divisibility. -/
lemma dvd_of_badparts_balanced {h i : ℕ} (hi : 0 < i)
    (hb : ∃ u v : Multiset ℕ, u + v = badparts h i ∧ u.sum = v.sum) :
    i ∣ h := by
  apply dvd_of_badparts_half hi
  exact half_of_balanced (badparts_sum h i) hb

end BBP

-- END INLINED FILE: Mathlib/Support/balanceable_bounded_partitions_8b215d0efe/Lower.lean

-- BEGIN INLINED FILE: Mathlib/Support/balanceable_bounded_partitions_8b215d0efe/Progress.lean
open scoped BigOperators
open Finset
lemma step2 (n:ℕ) (hn:6≤n) :
 (n+1)*(n+1)*((n+1)-1)*((n+1)+1) ≤
    2*(n*n*(n-1)*(n+1)) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hn
  simp
  ring_nf
  nlinarith
lemma pow2 (k:ℕ) (hk:16≤k) :
 k*k*(k-1)*(k+1) ≤ 2^k := by -- threshold? want ≤2^k not 2^(k+?)
 -- for k=16 LHS=16*16*15*17=65280 ≤65536 =2^16 yes
 induction k, hk using Nat.le_induction with
 | base => norm_num
 | succ n hn ih =>
   calc
     (n+1)*(n+1)*((n+1)-1)*((n+1)+1) ≤ 2*(n*n*(n-1)*(n+1)) := step2 n (le_trans (by decide) hn)
     _ ≤ 2*(2^n) := Nat.mul_le_mul_left 2 ih
     _ = 2^(n+1) := by ring
lemma lcmstrongbig (k:ℕ) (hk:16≤k) :
 (k-1)*k*k ≤ Nat.lcmUpto k := by
 have hp := pow2 k hk
 have hpw := Chebyshev.two_pow_le_mul_lcmUpto k
 have hchain : k*k*(k-1)*(k+1) ≤ (k+1)* Nat.lcmUpto k := le_trans hp hpw
 apply Nat.le_of_mul_le_mul_right (c:=k+1) ?_ (by omega)
 simpa [mul_assoc, mul_left_comm, mul_comm] using hchain
lemma lcmstrongsmall (k:ℕ) (h7:7≤k) (h16:k<16) :
 (k-1)*k*k ≤ Nat.lcmUpto k := by
 interval_cases k <;> decide
lemma lcmstrong (k:ℕ) (h7:7≤k) : (k-1)*k*k ≤ Nat.lcmUpto k := by
 by_cases h16 : 16 ≤ k
 · exact lcmstrongbig k h16
 · exact lcmstrongsmall k h7 (by omega)
lemma sumIcc_le (k:ℕ) : (∑ a ∈ Finset.Icc 1 k, a) ≤ k*k := by
 calc
  (∑ a ∈ Finset.Icc 1 k, a) ≤ (Finset.Icc 1 k).card • k :=
    Finset.sum_le_card_nsmul _ _ _ (by intro x hx; exact (Finset.mem_Icc.mp hx).2)
  _ = k*k := by simp [Nat.card_Icc]
lemma sumErase_le (k m:ℕ) : (∑ a ∈ (Finset.Icc 1 k).erase m, a) ≤ k*k := by
 exact le_trans (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)) (sumIcc_le k)
lemma lost_bound_large (k m : ℕ) (s: Multiset ℕ) (hm : m ∈ Finset.Icc 1 k)
 (hk:7≤k) : BBP.lost k m s ≤ Nat.lcmUpto k := by
 classical
 have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
 -- expand
 calc
  BBP.lost k m s = ∑ a ∈ (Finset.Icc 1 k).erase m, (s.count a % m) * a := rfl
  _ ≤ ∑ a ∈ (Finset.Icc 1 k).erase m, (m-1)*a := by
    apply Finset.sum_le_sum
    intro a ha
    apply Nat.mul_le_mul_right a
    have hx : s.count a % m < m := Nat.mod_lt _ hmpos
    omega
  _ = (m-1) * (∑ a ∈ (Finset.Icc 1 k).erase m, a) := by
    rw [Finset.mul_sum]
  _ ≤ (m-1) * (k*k) := Nat.mul_le_mul_left _ (sumErase_le k m)
  _ ≤ (k-1) * k*k := by
    have hmle : m ≤ k := (Finset.mem_Icc.mp hm).2
    have : m-1 ≤ k-1 := Nat.sub_le_sub_right hmle 1
    nlinarith
  _ ≤ Nat.lcmUpto k := lcmstrong k hk
lemma exists_high_large (k:ℕ) (hk:7≤k) (s:Multiset ℕ)
 (hs : ∀ a ∈ s, 1 ≤ a ∧ a ≤ k)
 (hsum : s.sum = 2 * Nat.lcmUpto k) :
 ∃ m ∈ Finset.Icc 1 k, k-1 ≤ s.count m := by
 classical
 by_contra hne
 push_neg at hne
 have hc : ∀ a ∈ Finset.Icc 1 k, s.count a ≤ k-2 := by
  intro a ha
  have hnot := hne a ha
  omega
 have hU : ∀ a ∈ s, a ∈ Finset.Icc 1 k := by
  intro a ha; exact Finset.mem_Icc.mpr (hs a ha)
 have heq := BBP.sum_count_mul s (Finset.Icc 1 k) hU
 have hle : s.sum ≤ (k-2)*(k*k) := by
  rw [← heq]
  calc
   (∑ a ∈ Finset.Icc 1 k, s.count a * a) ≤ ∑ a ∈ Finset.Icc 1 k, (k-2)*a := by
     apply Finset.sum_le_sum
     intro a ha
     exact Nat.mul_le_mul_right _ (hc a ha)
   _ = (k-2) * (∑ a ∈ Finset.Icc 1 k, a) := by rw [Finset.mul_sum]
   _ ≤ (k-2)*(k*k) := Nat.mul_le_mul_left _ (sumIcc_le k)
 have hbig := lcmstrong k hk
 rw [hsum] at hle
 have hx : 2*((k-1)*k*k) ≤ (k-2)*(k*k) :=
  le_trans (Nat.mul_le_mul_left 2 hbig) hle
 have hx' : (2*(k-1)) ≤ (k-2) := by
  apply Nat.le_of_mul_le_mul_right (c:=k*k) ?_ (by positivity)
  simpa [mul_assoc] using hx
 omega
lemma exists_high_small (k:ℕ) (hk:0<k) (hsmall:k<7) (s:Multiset ℕ)
 (hs : ∀ a ∈ s, 1 ≤ a ∧ a ≤ k)
 (hsum : s.sum = 2 * Nat.lcmUpto k) :
 ∃ m ∈ Finset.Icc 1 k, k-1 ≤ s.count m := by
 classical
 by_cases h1 : k = 1
 · subst k
   refine ⟨1, by decide, ?_⟩
   simp
 have hk2 : 2 ≤ k := by omega
 by_contra hne
 push_neg at hne
 have hc : ∀ a ∈ Finset.Icc 1 k, s.count a ≤ k-2 := by
  intro a ha
  have hnot := hne a ha
  omega
 have hU : ∀ a ∈ s, a ∈ Finset.Icc 1 k := by
  intro a ha; exact Finset.mem_Icc.mpr (hs a ha)
 have heq := BBP.sum_count_mul s (Finset.Icc 1 k) hU
 have hle : s.sum ≤ (k-2) * (∑ a ∈ Finset.Icc 1 k, a) := by
  rw [← heq]
  calc
   (∑ a ∈ Finset.Icc 1 k, s.count a * a)
       ≤ ∑ a ∈ Finset.Icc 1 k, (k-2)*a := by
        apply Finset.sum_le_sum
        intro a ha
        exact Nat.mul_le_mul_right _ (hc a ha)
   _ = (k-2) * (∑ a ∈ Finset.Icc 1 k, a) := by rw [Finset.mul_sum]
 rw [hsum] at hle
 interval_cases k
 case «2» => exact (by decide : ¬ (2*Nat.lcmUpto 2 ≤ (2-2)*(∑ a ∈ Finset.Icc 1 2, a))) hle
 case «3» => exact (by decide : ¬ (2*Nat.lcmUpto 3 ≤ (3-2)*(∑ a ∈ Finset.Icc 1 3, a))) hle
 case «4» => exact (by decide : ¬ (2*Nat.lcmUpto 4 ≤ (4-2)*(∑ a ∈ Finset.Icc 1 4, a))) hle
 case «5» => exact (by decide : ¬ (2*Nat.lcmUpto 5 ≤ (5-2)*(∑ a ∈ Finset.Icc 1 5, a))) hle
 case «6» => exact (by decide : ¬ (2*Nat.lcmUpto 6 ≤ (6-2)*(∑ a ∈ Finset.Icc 1 6, a))) hle
lemma lost_bound_simple (k m:ℕ) (s:Multiset ℕ) (hmpos : 0 < m) :
 BBP.lost k m s ≤ (m-1)*(∑ a ∈ (Finset.Icc 1 k).erase m, a) := by
 classical
 unfold BBP.lost
 calc
  (∑ a ∈ (Finset.Icc 1 k).erase m, s.count a % m * a)
    ≤ ∑ a ∈ (Finset.Icc 1 k).erase m, (m-1)*a := by
      apply Finset.sum_le_sum
      intro a ha
      apply Nat.mul_le_mul_right a
      have hx := Nat.mod_lt (s.count a) hmpos
      omega
  _ = (m-1)*(∑ a ∈ (Finset.Icc 1 k).erase m, a) := by rw [Finset.mul_sum]
lemma lost_dvd (k m : ℕ) (s:Multiset ℕ)
 (hm: m ∈ Finset.Icc 1 k)
 (hs : ∀ a ∈ s, 1 ≤ a ∧ a ≤ k)
 (hsum : s.sum = 2*Nat.lcmUpto k) : m ∣ BBP.lost k m s := by
 have hdk : m ∣ Nat.lcmUpto k := BBP.dvd_lcm (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
 have htot := BBP.total_blocks hm s hs
 rw [hsum] at htot
 have hmul : m ∣ m * (s.count m + (BBP.blocks k m s).sum) := dvd_mul_right _ _
 have h2 : m ∣ 2 * Nat.lcmUpto k := dvd_mul_of_dvd_right hdk 2
 rw [htot] at h2
 exact (Nat.dvd_add_right hmul).mp h2
-- Try a general lemma when the simple+dvisibility arithmetic works by assumption bound
lemma lost_of_bound (k m C H : ℕ) (s:Multiset ℕ)
 (hm: m ∈ Finset.Icc 1 k)
 (hs : ∀ a ∈ s, 1 ≤ a ∧ a ≤ k)
 (hsum : s.sum = 2*Nat.lcmUpto k)
 (hsC : (∑ a ∈ (Finset.Icc 1 k).erase m, a) = C)
 (hH : Nat.lcmUpto k = H)
 (harith : ∀ d : ℕ, m*d ≤ (m-1)*C → m*d ≤ H) :
 BBP.lost k m s ≤ Nat.lcmUpto k := by
 have hb := lost_bound_simple k m s (Finset.mem_Icc.mp hm).1
 rw [hsC] at hb
 obtain ⟨d, hd⟩ := lost_dvd k m s hm hs hsum
 rw [hd] at hb ⊢
 rw [hH]
 exact harith d hb
lemma sumErase_formula (k m:ℕ) (hm: m ∈ Finset.Icc 1 k) :
 (∑ a ∈ (Finset.Icc 1 k).erase m, a) = (∑ a ∈ Finset.Icc 1 k, a) - m := by
 have h := Finset.sum_erase_add (Finset.Icc 1 k) (fun a => a) hm
 omega
lemma lost_ok_small_indices (k m : ℕ) (s:Multiset ℕ)
 (hm: m ∈ Finset.Icc 1 k)
 (hs : ∀ a ∈ s, 1 ≤ a ∧ a ≤ k)
 (hsum : s.sum = 2*Nat.lcmUpto k)
 (hcase : (k=1) ∨ (k=2) ∨ (k=3) ∨ (k=4 ∧ m ≤ 3) ∨ (k=5) ∨ (k=6 ∧ m ≤5)) :
 BBP.lost k m s ≤ Nat.lcmUpto k := by
 classical
 rcases hcase with c|c|c|c|c|c
 · subst k
   have mm : m=1 := by have := Finset.mem_Icc.mp hm; omega
   subst m
   apply lost_of_bound 1 1 0 1 s hm hs hsum (by decide) (by decide)
   intro d hd; omega
 · subst k
   have mx : m ≤ 2 := (Finset.mem_Icc.mp hm).2
   have mn : 1 ≤ m := (Finset.mem_Icc.mp hm).1
   interval_cases m
   all_goals try omega
   all_goals apply lost_of_bound _ _ (∑ a ∈ (Finset.Icc 1 _).erase _, a) (Nat.lcmUpto _) s hm hs hsum rfl rfl
   all_goals intro d hd
   all_goals rw [sumErase_formula _ _ hm] at hd
   all_goals have htot : (∑ a ∈ Finset.Icc 1 2, a) = 3 := by decide
   all_goals rw [htot] at hd
   all_goals norm_num at hd
   all_goals have hval : Nat.lcmUpto 2 = 2 := by decide
   all_goals omega
 · subst k -- three
   have mx : m ≤ 3 := (Finset.mem_Icc.mp hm).2
   have mn : 1 ≤ m := (Finset.mem_Icc.mp hm).1
   interval_cases m
   all_goals try omega
   all_goals apply lost_of_bound _ _ (∑ a ∈ (Finset.Icc 1 _).erase _, a) (Nat.lcmUpto _) s hm hs hsum rfl rfl
   all_goals intro d hd
   all_goals rw [sumErase_formula _ _ hm] at hd
   all_goals have htot : (∑ a ∈ Finset.Icc 1 3, a) = 6 := by decide
   all_goals rw [htot] at hd
   all_goals norm_num at hd
   all_goals have hval : Nat.lcmUpto 3 = 6 := by decide
   all_goals omega
 · rcases c with ⟨keq, mmle⟩ -- four restricted
   subst k
   have mx : m ≤ 3 := mmle
   have mn : 1 ≤ m := (Finset.mem_Icc.mp hm).1
   interval_cases m
   all_goals try omega
   all_goals apply lost_of_bound _ _ (∑ a ∈ (Finset.Icc 1 _).erase _, a) (Nat.lcmUpto _) s hm hs hsum rfl rfl
   all_goals intro d hd
   all_goals rw [sumErase_formula _ _ hm] at hd
   all_goals have htot : (∑ a ∈ Finset.Icc 1 4, a) = 10 := by decide
   all_goals rw [htot] at hd
   all_goals norm_num at hd
   all_goals have hval : Nat.lcmUpto 4 = 12 := by decide
   all_goals omega
 · subst k -- five
   have mx : m ≤ 5 := (Finset.mem_Icc.mp hm).2
   have mn : 1 ≤ m := (Finset.mem_Icc.mp hm).1
   interval_cases m
   all_goals try omega
   all_goals apply lost_of_bound _ _ (∑ a ∈ (Finset.Icc 1 _).erase _, a) (Nat.lcmUpto _) s hm hs hsum rfl rfl
   all_goals intro d hd
   all_goals rw [sumErase_formula _ _ hm] at hd
   all_goals have htot : (∑ a ∈ Finset.Icc 1 5, a) = 15 := by decide
   all_goals rw [htot] at hd
   all_goals norm_num at hd
   all_goals have hval : Nat.lcmUpto 5 = 60 := by decide
   all_goals omega
 · rcases c with ⟨keq, mmle⟩
   subst k
   have mx : m ≤ 5 := mmle
   have mn : 1 ≤ m := (Finset.mem_Icc.mp hm).1
   interval_cases m
   all_goals try omega
   all_goals apply lost_of_bound _ _ (∑ a ∈ (Finset.Icc 1 _).erase _, a) (Nat.lcmUpto _) s hm hs hsum rfl rfl
   all_goals intro d hd
   all_goals rw [sumErase_formula _ _ hm] at hd
   all_goals have htot : (∑ a ∈ Finset.Icc 1 6, a) = 21 := by decide
   all_goals rw [htot] at hd
   all_goals norm_num at hd
   all_goals have hval : Nat.lcmUpto 6 = 60 := by decide
   all_goals omega
lemma lost_when_other_low (k m:ℕ) (s:Multiset ℕ) (hm:m∈Finset.Icc 1 k)
 (hc : ∀ a ∈ (Finset.Icc 1 k).erase m, s.count a ≤ k-2) :
 BBP.lost k m s ≤ (k-2)*(∑ a ∈ (Finset.Icc 1 k).erase m, a) := by
 classical
 unfold BBP.lost
 calc
  (∑ a ∈ (Finset.Icc 1 k).erase m, s.count a % m * a)
   ≤ ∑ a ∈ (Finset.Icc 1 k).erase m, (k-2)*a := by
    apply Finset.sum_le_sum; intro a ha
    apply Nat.mul_le_mul_right
    exact le_trans (Nat.mod_le _ _) (hc a ha)
  _ = _ := by rw [Finset.mul_sum]
lemma exists_good (k:ℕ) (hk:0<k) (s:Multiset ℕ)
 (hs: ∀ a ∈ s, 1 ≤ a ∧ a ≤ k) (hsum:s.sum=2*Nat.lcmUpto k) :
 ∃ m ∈ Finset.Icc 1 k, k-1 ≤ s.count m ∧ BBP.lost k m s ≤ Nat.lcmUpto k := by
 classical
 by_cases big : 7 ≤ k
 · obtain ⟨m,hm,hc⟩ := exists_high_large k big s hs hsum
   exact ⟨m,hm,hc, lost_bound_large k m s hm big⟩
 have small : k < 7 := by omega
 obtain ⟨m, hm, hc⟩ := exists_high_small k hk small s hs hsum
 by_cases ck : k = 4 ∨ k = 6
 · rcases ck with rfl|rfl
   · by_cases alt : m ≤ 3
     · exact ⟨m,hm,hc, lost_ok_small_indices 4 m s hm hs hsum (by aesop)⟩
     · have me : m=4 := by have := Finset.mem_Icc.mp hm; omega
       -- maybe some other high below
       by_cases other : ∃ j ∈ Finset.Icc 1 3, 3 ≤ s.count j
       · obtain ⟨j,hj,hj'⟩ := other
         have hj4 : j ∈ Finset.Icc 1 4 := by
          have := Finset.mem_Icc.mp hj
          exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
         exact ⟨j,hj4, by simpa using hj', lost_ok_small_indices 4 j s hj4 hs hsum (by right;right;right;left; exact ⟨rfl,(Finset.mem_Icc.mp hj).2⟩)⟩
       · push_neg at other
         refine ⟨m,hm,hc, ?_⟩
         have low : ∀ a ∈ (Finset.Icc 1 4).erase m, s.count a ≤ 2 := by
          intro a ha
          have haI := Finset.mem_Icc.mp (Finset.mem_of_mem_erase ha)
          have ha3 : a ∈ Finset.Icc 1 3 := Finset.mem_Icc.mpr ⟨haI.1, by have := (Finset.mem_erase.mp ha).1; omega⟩
          have z := other a ha3
          omega
         have lb := lost_when_other_low 4 m s hm low
         rw [sumErase_formula _ _ hm] at lb
         have hv : (∑ a ∈ Finset.Icc 1 4, a)=10 := by decide
         rw [hv] at lb
         have hv2 : Nat.lcmUpto 4 = 12 := by decide
         rw [hv2]
         omega
   · by_cases alt : m ≤ 5
     · exact ⟨m,hm,hc, lost_ok_small_indices 6 m s hm hs hsum (by aesop)⟩
     · have me : m=6 := by have := Finset.mem_Icc.mp hm; omega
       by_cases other : ∃ j ∈ Finset.Icc 1 5, 5 ≤ s.count j
       · obtain ⟨j,hj,hj'⟩ := other
         have hj6 : j ∈ Finset.Icc 1 6 := by have t:= Finset.mem_Icc.mp hj; exact Finset.mem_Icc.mpr ⟨t.1, by omega⟩
         exact ⟨j,hj6, by simpa using hj', lost_ok_small_indices 6 j s hj6 hs hsum (by aesop)⟩
       · push_neg at other
         refine ⟨m,hm,hc, ?_⟩
         have low : ∀ a ∈ (Finset.Icc 1 6).erase m, s.count a ≤ 4 := by
          intro a ha
          have haI := Finset.mem_Icc.mp (Finset.mem_of_mem_erase ha)
          have ha5 : a ∈ Finset.Icc 1 5 := Finset.mem_Icc.mpr ⟨haI.1, by have := (Finset.mem_erase.mp ha).1; omega⟩
          have z := other a ha5; omega
         have lb := lost_when_other_low 6 m s hm low
         rw [sumErase_formula _ _ hm] at lb
         have hv : (∑ a ∈ Finset.Icc 1 6, a)=21 := by decide
         rw [hv] at lb
         have hv2 : Nat.lcmUpto 6 = 60 := by decide
         rw [hv2]
         omega
 · have cases : k=1 ∨ k=2 ∨ k=3 ∨ k=5 := by omega
   have lc : (k=1) ∨ (k=2) ∨ (k=3) ∨ (k=4 ∧ m≤3) ∨ (k=5) ∨ (k=6 ∧ m≤5) := by aesop
   exact ⟨m,hm,hc,lost_ok_small_indices k m s hm hs hsum lc⟩

-- END INLINED FILE: Mathlib/Support/balanceable_bounded_partitions_8b215d0efe/Progress.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval
namespace Combinatorics

/--
A partition is `k`-bounded if all of its members are at most `k`.

For example, `12 = 3 + 2 + 2 + 2 + 2 + 1` is a `3`-bounded partition
of `12`.
-/
def Bounded {n : ℕ} (k : ℕ) (p : n.Partition) : Prop :=
  ∀ i ∈ p.parts, i ≤ k

/--
A partition is balanceable if it can be decomposed into two multisets of
the same size.

For example, `12 = (3 + 2 + 1) + (2 + 2 + 2)` is a balanceable partition
of `12`.
-/
def Balanceable {n : ℕ} (p : n.Partition) : Prop :=
  ∃ s₁ s₂, s₁ + s₂ = p.parts ∧ s₁.sum = s₂.sum



end Combinatorics
end LeanEval

open LeanEval.Combinatorics
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem minimal_balanceable_of_bounded (k : ℕ) (hk : 0 < k) :
    Minimal (fun n => 0 < n ∧ ∀ p : n.Partition, Bounded k p → Balanceable p) (2 * (Finset.Icc 1 k).lcm id) :=
/-ResultProofBegin-/by
  classical
  let h := Nat.lcmUpto k
  have he : (Finset.Icc 1 k).lcm id = h := rfl
  change Minimal _ (2 * h)
  refine ⟨?_, ?_⟩
  · constructor
    · have hp := BBP.lcm_pos k
      dsimp [h]
      omega
    · intro p hb
      have hs : ∀ a ∈ p.parts, 1 ≤ a ∧ a ≤ k := by
        intro a ha
        exact ⟨p.parts_pos ha, hb a ha⟩
      have sm : p.parts.sum = 2 * Nat.lcmUpto k := by
        simpa [h] using p.parts_sum
      obtain ⟨m, hm, hc, hl⟩ := exists_good k hk p.parts hs sm
      apply BBP.balanced_of_half (h:=Nat.lcmUpto k) sm
      exact BBP.subset_good p.parts hs sm (fun a h1 h2 => BBP.dvd_lcm h1 h2) hm hc hl
  · intro y hy hle
    rcases hy with ⟨hypos, hyall⟩
    have hkone : 1 ≤ k := by omega
    let pone : y.Partition :=
      ⟨Multiset.replicate y 1,
        (by
          intro a ha
          have hx : a = 1 := (Multiset.mem_replicate.mp ha).2
          omega),
        (by simp)⟩
    have hb1 : Balanceable pone := by
      apply hyall pone
      intro a ha
      have hx : a = 1 := (Multiset.mem_replicate.mp (by simpa [pone] using ha)).2
      omega
    have hev : ∃ x : ℕ, (pone.parts).sum = 2*x := by
      apply BBP.even_of_balanced
      exact hb1
    rcases hev with ⟨x, hx0⟩
    have hx : y = 2*x := by
      simpa [pone] using hx0
    subst y
    have hxpos : 0 < x := by
      omega
    have halldvd : ∀ a ∈ Finset.Icc 1 k, a ∣ x := by
      intro a ha
      have hapos : 0 < a := (Finset.mem_Icc.mp ha).1
      have hale : a ≤ k := (Finset.mem_Icc.mp ha).2
      let pa : (2*x).Partition :=
        ⟨BBP.badparts x a,
          (by
            intro z hz
            exact BBP.badparts_pos hapos z hz),
          BBP.badparts_sum x a⟩
      have hbpa : Balanceable pa := by
        apply hyall pa
        intro b hb
        exact BBP.badparts_bound hapos hale b (by simpa [pa] using hb)
      have hbal : ∃ u v : Multiset ℕ,
            u + v = BBP.badparts x a ∧ u.sum = v.sum := by
        simpa [Balanceable, pa] using hbpa
      exact BBP.dvd_of_badparts_balanced hapos hbal
    have hlcm : Nat.lcmUpto k ∣ x := by
      change (Finset.Icc 1 k).lcm id ∣ x
      apply Finset.lcm_dvd
      intro a ha
      exact halldvd a ha
    have hfloor : Nat.lcmUpto k ≤ x := Nat.le_of_dvd hxpos hlcm
    dsimp [h]
    omega
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
