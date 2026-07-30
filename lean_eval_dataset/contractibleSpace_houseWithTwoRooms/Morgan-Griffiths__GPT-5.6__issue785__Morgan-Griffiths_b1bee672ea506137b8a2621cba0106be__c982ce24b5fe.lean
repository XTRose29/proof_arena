import ChallengeDeps

-- BEGIN INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Reduction.lean

namespace HouseSupport
open Set
abbrev V := ℝ × ℝ × ℝ

/-- The polyhedron as a set of triples, kept in a separate namespace so that
some small cubical calculations do not have to refer to the statement. -/
def house : Set V :=
  (Icc 0 4 ×ˢ Icc 0 3 ×ˢ {0, 1, 2} \
    (Ioo 2 3 ×ˢ Ioo 1 2 ×ˢ {0} ∪ Ioo 1 3 ×ˢ Ioo 1 2 ×ˢ {1} ∪ Ioo 1 2 ×ˢ Ioo 1 2 ×ˢ {2})) ∪
  ({1} ×ˢ Icc 1 2 ×ˢ Icc 1 2 ∪ {2} ×ˢ Icc 1 3 ×ˢ Icc 0 2 ∪ {3} ×ˢ Icc 1 2 ×ˢ Icc 0 1 ∪
    Icc 1 2 ×ˢ {1, 2} ×ˢ Icc 1 2 ∪ Icc 2 3 ×ˢ {1, 2} ×ˢ Icc 0 1) ∪
  (Icc 0 4 ×ˢ {0, 3} ×ˢ Icc 0 2 ∪ {0, 4} ×ˢ Icc 0 3 ×ˢ Icc 0 2)

-- closedness is useful for the last (two dimensional) gluing.

theorem house_closed : IsClosed house := by
  -- a horizontal sheet with a rectangular hole is the difference of a closed
  -- sheet and an *open vertical prism*.  This avoids the often troublesome
  -- "open-within-the-sheet" calculation.
  let S (z:ℝ) : Set V := Icc 0 4 ×ˢ Icc 0 3 ×ˢ {z}
  let O (a b : ℝ) : Set V := Ioo a b ×ˢ Ioo 1 2 ×ˢ (Set.univ : Set ℝ)
  have hS (z:ℝ) : IsClosed (S z) :=
    (isClosed_Icc.prod (isClosed_Icc.prod isClosed_singleton))
  have hO (a b:ℝ) : IsOpen (O a b) :=
    (isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_univ))
  have hflooreq :
      (Icc (0:ℝ) 4 ×ˢ Icc (0:ℝ) 3 ×ˢ ({0,1,2}:Set ℝ) \
        (Ioo (2:ℝ) 3 ×ˢ Ioo (1:ℝ) 2 ×ˢ ({0}:Set ℝ) ∪
         Ioo (1:ℝ) 3 ×ˢ Ioo (1:ℝ) 2 ×ˢ ({1}:Set ℝ) ∪
         Ioo (1:ℝ) 2 ×ˢ Ioo (1:ℝ) 2 ×ˢ ({2}:Set ℝ)))
      = (S 0 \ O 2 3) ∪ (S 1 \ O 1 3) ∪ (S 2 \ O 1 2) := by
    ext p
    rcases p with ⟨x,y,z⟩
    -- after membership in products, this is just the three alternatives for z
    simp [S, O]
    -- simp leaves a small propositional formula over z = 0,1,2 and the
    -- interval tests. These are disjoint numerals.
    aesop
  have hfloor : IsClosed
      (Icc (0:ℝ) 4 ×ˢ Icc (0:ℝ) 3 ×ˢ ({0,1,2}:Set ℝ) \
        (Ioo (2:ℝ) 3 ×ˢ Ioo (1:ℝ) 2 ×ˢ ({0}:Set ℝ) ∪
         Ioo (1:ℝ) 3 ×ˢ Ioo (1:ℝ) 2 ×ˢ ({1}:Set ℝ) ∪
         Ioo (1:ℝ) 2 ×ˢ Ioo (1:ℝ) 2 ×ˢ ({2}:Set ℝ))) := by
    have hc := ((hS 0).sdiff (hO 2 3)).union ((hS 1).sdiff (hO 1 3))
      |>.union ((hS 2).sdiff (hO 1 2))
    exact (congrArg IsClosed hflooreq).mpr hc
  have hc12 : IsClosed ({1, (2:ℝ)} : Set ℝ) := isClosed_singleton.union isClosed_singleton
  have hc03 : IsClosed ({0, (3:ℝ)} : Set ℝ) := isClosed_singleton.union isClosed_singleton
  have hc04 : IsClosed ({0, (4:ℝ)} : Set ℝ) := isClosed_singleton.union isClosed_singleton
  have hi : IsClosed
      (({(1:ℝ)}:Set ℝ) ×ˢ Icc 1 2 ×ˢ Icc 1 2 ∪ {2} ×ˢ Icc 1 3 ×ˢ Icc 0 2 ∪ {3} ×ˢ Icc 1 2 ×ˢ Icc 0 1 ∪
        Icc 1 2 ×ˢ ({1,2}:Set ℝ) ×ˢ Icc 1 2 ∪ Icc 2 3 ×ˢ ({1,2}:Set ℝ) ×ˢ Icc 0 1 : Set V) := by
    exact (((isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc)).union
      (isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc))).union
      (isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc))).union
        (isClosed_Icc.prod (hc12.prod isClosed_Icc)) |>.union
        (isClosed_Icc.prod (hc12.prod isClosed_Icc))
  have he : IsClosed
      (Icc (0:ℝ) 4 ×ˢ ({0,3}:Set ℝ) ×ˢ Icc 0 2 ∪
        ({0,4}:Set ℝ) ×ˢ Icc 0 3 ×ˢ Icc 0 2 : Set V) := by
    exact (isClosed_Icc.prod (hc03.prod isClosed_Icc)).union
      (hc04.prod (isClosed_Icc.prod isClosed_Icc))
  -- parentheses in `house` are `(floor ∪ interior) ∪ exterior`.
  exact (hfloor.union hi).union he

end HouseSupport

-- END INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Reduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Box.lean
namespace HouseSupport
open Set
noncomputable section
def bigBox : Set V := Icc (0:ℝ) 4 ×ˢ Icc (0:ℝ) 3 ×ˢ Icc (0:ℝ) 2
lemma convex_bigBox : Convex ℝ bigBox :=
  (convex_Icc 0 4).prod ((convex_Icc 0 3).prod (convex_Icc 0 2))
lemma nonempty_bigBox : bigBox.Nonempty :=
  ⟨(0,(0,0)), ⟨⟨by norm_num, by norm_num⟩, ⟨⟨by norm_num, by norm_num⟩,
      ⟨by norm_num, by norm_num⟩⟩⟩⟩
lemma house_subset_bigBox : house ⊆ bigBox := by
  intro p hp
  unfold house at hp
  rcases hp with ha|hc
  · rcases ha with hf|hi
    · exact ⟨hf.1.1, hf.1.2.1, by
        have hz := hf.1.2.2
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with h|h|h <;> constructor <;> linarith⟩
    · rcases hi with h1234 | h5
      · rcases h1234 with h123 | h4
        · rcases h123 with hab | h3
          · rcases hab with h1 | h2
            · exact ⟨by rw [show p.1=1 by simpa using h1.1]; norm_num,
                ⟨by linarith [h1.2.1.1], by linarith [h1.2.1.2]⟩,
                  ⟨by linarith [h1.2.2.1], by linarith [h1.2.2.2]⟩⟩
            · exact ⟨by rw [show p.1=2 by simpa using h2.1]; norm_num,
                ⟨by linarith [h2.2.1.1], by linarith [h2.2.1.2]⟩, h2.2.2⟩
          · exact ⟨by rw [show p.1=3 by simpa using h3.1]; norm_num,
              ⟨by linarith [h3.2.1.1], by linarith [h3.2.1.2]⟩,
              ⟨by linarith [h3.2.2.1], by linarith [h3.2.2.2]⟩⟩
        · have hy := h4.2.1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          exact ⟨⟨by linarith [h4.1.1], by linarith [h4.1.2]⟩,
            ⟨by rcases hy with h|h <;> linarith,
              by rcases hy with h|h <;> linarith⟩,
            ⟨by linarith [h4.2.2.1], by linarith [h4.2.2.2]⟩⟩
      · have hy := h5.2.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        exact ⟨⟨by linarith [h5.1.1], by linarith [h5.1.2]⟩,
          ⟨by rcases hy with h|h <;> linarith,
            by rcases hy with h|h <;> linarith⟩,
          ⟨by linarith [h5.2.2.1], by linarith [h5.2.2.2]⟩⟩

  · rcases hc with h|h
    · have hy := h.2.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      exact ⟨h.1, ⟨by rcases hy with h|h <;> linarith,
                      by rcases hy with h|h <;> linarith⟩, h.2.2⟩
    · have hx := h.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      exact ⟨⟨by rcases hx with h|h <;> linarith,
                by rcases hx with h|h <;> linarith⟩, h.2.1, h.2.2⟩

lemma contractible_of_retract_of_convex {A B : Set V}
    (cv : Convex ℝ B) (hne : B.Nonempty) (inc : A ⊆ B)
    (r : C((B:Set V),(A:Set V)))
    (hr : ∀ x:(A:Set V), r ⟨x.1,inc x.2⟩ = x) :
    ContractibleSpace A := by
  classical
  obtain ⟨b,hb⟩ := hne
  let c : (A:Set V) := r ⟨b,hb⟩
  apply (contractible_iff_id_nullhomotopic (A:Set V)).2
  refine ⟨c, ?_⟩
  refine ⟨?_⟩
  let F : (unitInterval × (A:Set V)) → (B:Set V) := fun q =>
    ⟨(1-(q.1:ℝ)) • (q.2.1 : V) + (q.1:ℝ) • b,
      cv (inc q.2.2) hb (by exact sub_nonneg.mpr q.1.2.2)
        q.1.2.1 (by ring)⟩
  have Fc : Continuous F := by
    unfold F
    apply Continuous.subtype_mk ?_ _
    fun_prop
  refine ⟨⟨(fun q => r (F q)), r.continuous.comp Fc⟩, ?_, ?_⟩
  · intro x
    change r ⟨(1-(0:ℝ)) • (x.1:V) + 0 • b, _⟩ = x
    simpa using hr x
  · intro x
    change (r ⟨_, _⟩ : (A:Set V)) = c
    apply congrArg (fun t : (B:Set V) => r t)
      (Subtype.ext (by change (1-(1:ℝ)) • (x.1:V) + 1 • b = b; module))
end
end HouseSupport

-- END INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Box.lean

-- BEGIN INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Tail.lean

namespace HouseSupport
open Set
noncomputable section

/-- denominator for radial projection of the square. The free edge is `u=0`;
the pole is at `(-1,1/2)` (strictly outside). Thus the formula, unlike
projection from the missing edge, has no bad point on the square. -/
def sd (u v : ℝ) : ℝ := max ((u+1)/2) |2*v-1|
def su (u v : ℝ) : ℝ := -1 + (u+1) / sd u v
def sv (u v : ℝ) : ℝ := (1/2:ℝ) + (v-1/2) / sd u v

lemma sd_pos {u v:ℝ} (hu : 0 ≤ u) : 0 < sd u v := by
  unfold sd
  have h : 0 < (u+1)/2 := by linarith
  exact lt_of_lt_of_le h (le_max_left _ _)

lemma sd_le_one {u v:ℝ} (hu : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : sd u v ≤ 1 := by
  unfold sd
  have a : (u+1)/2 ≤ (1:ℝ) := by linarith
  have b : |2*v-1| ≤ (1:ℝ) := (abs_le).2 ⟨by linarith, by linarith⟩
  exact (max_le a b)

/-- elementary estimates for the homogeneous square formula -/
lemma sm_bounds {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ su u v ∧ su u v ≤ 1 ∧ 0 ≤ sv u v ∧ sv u v ≤ 1 := by
  have hp : 0 < sd u v := sd_pos hu0
  have hle : sd u v ≤ (1:ℝ) := sd_le_one hu1 hv0 hv1
  have ha : (u+1)/2 ≤ sd u v := le_max_left _ _
  have hb : |2*v-1| ≤ sd u v := le_max_right _ _
  have huplus : 0 < u+1 := by linarith
  have hlow : sd u v ≤ (u+1) := le_trans hle (by linarith)
  have us0 : 0 ≤ su u v := by
    unfold su
    have hh : (1:ℝ) ≤ (u+1) / sd u v := (le_div_iff₀ hp).2 (by simpa using hlow)
    linarith
  have us1 : su u v ≤ 1 := by
    unfold su
    have h : (u+1) ≤ 2 * sd u v := by linarith
    have h' := (div_le_iff₀ hp).2 h
    linarith
  have hb' : |v - (1/2:ℝ)| * 2 ≤ sd u v := by
    have he : |2*v-1| = 2 * |v-(1/2:ℝ)| := by
      rw [show 2*v-1 = 2*(v-(1/2:ℝ)) by ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [he] at hb
    linarith
  have hvupper : (v- (1/2:ℝ)) / sd u v ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ hp).2
    have h : v-(1/2:ℝ) ≤ |v-(1/2:ℝ)| := le_abs_self _
    nlinarith
  have hvlower : -(1/2:ℝ) ≤ (v-(1/2:ℝ)) / sd u v := by
    apply (le_div_iff₀ hp).2
    have h : -|v-(1/2:ℝ)| ≤ v-(1/2:ℝ) := neg_abs_le _
    nlinarith
  refine ⟨us0, us1, ?_, ?_⟩
  · unfold sv
    linarith
  · unfold sv
    linarith

/-- The image is on the three-sided horn. -/
lemma sm_horn {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    su u v = 1 ∨ sv u v = 0 ∨ sv u v = 1 := by
  have hp : 0 < sd u v := sd_pos hu0
  have hcases : sd u v = (u+1)/2 ∨ sd u v = |2*v-1| := by
    unfold sd
    rcases (max_cases ((u+1)/2) |2*v-1|) with h|h
    · exact Or.inl h.1
    · exact Or.inr h.1
  rcases hcases with h | h
  · left
    unfold su
    rw [h]
    have hne : (u+1)/2 ≠ 0 := by linarith
    field_simp [hne]
    <;> ring
  · have hne : 2*v-1 ≠ 0 := by
      have : |2*v-1| ≠ 0 := by linarith
      exact (abs_ne_zero.mp this)
    have hab : 0 ≤ 2*v-1 ∨ 2*v-1 ≤ 0 := le_total 0 _
    rcases hab with hv | hv
    · right; right
      unfold sv
      rw [h, abs_of_nonneg hv]
      field_simp [hne]
      <;> ring
    · right; left
      unfold sv
      rw [h, abs_of_nonpos hv]
      field_simp [hne]
      <;> ring

/-- On the horn the radial projection is the identity. -/
lemma sm_fix {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (h : u = 1 ∨ v = 0 ∨ v = 1) :
    su u v = u ∧ sv u v = v := by
  have hp := sd_pos (v:=v) hu0
  have hle := sd_le_one (v:=v) hu1 hv0 hv1
  have heq : sd u v = 1 := by
    rcases h with h|h|h
    · -- first term is one
      have : (1:ℝ) ≤ sd u v := by
        unfold sd
        rw [h]
        norm_num
      exact le_antisymm hle this
    · have hb : (1:ℝ) ≤ sd u v := by
        unfold sd
        rw [h]
        norm_num
      exact le_antisymm hle hb
    · have hb : (1:ℝ) ≤ sd u v := by
        unfold sd
        rw [h]
        norm_num
      exact le_antisymm hle hb
  unfold su sv
  rw [heq]
  constructor <;> ring


/-- The map on affine coordinates of the square is continuous on the square. -/
private lemma hd_cont : Continuous (fun p : ℝ × ℝ =>
    max ((p.1+1)/2) |2*p.2-1|) := by
  apply Continuous.max
  · fun_prop
  · fun_prop

private lemma hd_ne (p : ℝ × ℝ) (hp : p ∈ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) :
    max ((p.1+1)/2) |2*p.2-1| ≠ 0 := by
  have hu : 0 ≤ p.1 := hp.1.1
  have h := sd_pos (v:=p.2) hu
  exact ne_of_gt (by simpa [sd] using h)
lemma continuousOn_su : ContinuousOn (fun p : ℝ × ℝ => su p.1 p.2)
    (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
  unfold su sd
  have hnum : Continuous (fun p : ℝ × ℝ => p.1 + 1) := by fun_prop
  have hd := hd_cont
  have hquot : ContinuousOn
      (fun p : ℝ × ℝ => (p.1+1) / max ((p.1+1)/2) |2*p.2-1|)
      (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :=
    (hnum.continuousOn.div₀ hd.continuousOn (by
       intro p hp; exact hd_ne p hp))
  exact (continuousOn_const.add hquot)

-- a more convenient direct proof, also for the second coordinate
lemma continuousOn_sv : ContinuousOn (fun p : ℝ × ℝ => sv p.1 p.2)
    (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
  unfold sv sd
  have hnum : Continuous (fun p : ℝ × ℝ => p.2 - (1/2:ℝ)) := by fun_prop
  have hd := hd_cont
  have hquot : ContinuousOn
      (fun p : ℝ × ℝ => (p.2-(1/2:ℝ)) / max ((p.1+1)/2) |2*p.2-1|)
      (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :=
    (hnum.continuousOn.div₀ hd.continuousOn (by
      intro p hp; exact hd_ne p hp))
  exact (continuousOn_const.add hquot)

/-- One of the four panels left over after the cubical sweeps. -/
def panel : Set V := Icc (1:ℝ) 2 ×ˢ ({1}:Set ℝ) ×ˢ Icc (0:ℝ) 1
def panelR : Set V := house ∪ panel

lemma panel_closed : IsClosed panel :=
  isClosed_Icc.prod (isClosed_singleton.prod isClosed_Icc)
lemma panelR_closed : IsClosed panelR := house_closed.union panel_closed

lemma panel_horn_mem {x y z : ℝ}
    (hx : x ∈ Icc (1:ℝ) 2) (hy : y = 1) (hz : z ∈ Icc (0:ℝ) 1)
    (h : x = 2 ∨ z = 0 ∨ z = 1) : ((x,(y,z)):V) ∈ house := by
  rcases hx with ⟨hx0,hx1⟩
  rcases hz with ⟨hz0,hz1⟩
  subst y
  unfold house
  -- `simp` is a painless way to avoid the association of the displayed finite
  -- unions.
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_prod, Set.mem_Icc,
    Set.mem_Ioo, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases h with hx | hz | hz
  · left; right
    --(((a ∨ b) ∨ c) ∨ d) ∨ e ; use b
    exact Or.inl (Or.inl (Or.inl (Or.inr
      ⟨hx, ⟨⟨by norm_num, by norm_num⟩, ⟨hz0, by linarith⟩⟩⟩)))
  · left; left
    refine ⟨⟨⟨by linarith, by linarith⟩, ⟨⟨by linarith, by linarith⟩, ?_⟩⟩, ?_⟩
    · simp [hz]
    · intro hf
      aesop
  · left; left
    refine ⟨⟨⟨by linarith, by linarith⟩, ⟨⟨by linarith, by linarith⟩, ?_⟩⟩, ?_⟩
    · simp [hz]
    · intro hf
      aesop

lemma panel_inter_house {x y z : ℝ}
    (hx : x ∈ Icc (1:ℝ) 2) (hy : y = 1) (hz : z ∈ Icc (0:ℝ) 1)
    (hh : ((x,(y,z)):V) ∈ house) : x=2 ∨ z=0 ∨ z=1 := by
  rcases hx with ⟨hx0,hx1⟩
  rcases hz with ⟨hz0,hz1⟩
  subst y
  classical
  by_contra hn
  push_neg at hn
  rcases hn with ⟨hx2, hz0', hz1'⟩
  have hxx : x < 2 := lt_of_le_of_ne hx1 hx2
  have hzz0 : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hz0')
  have hzz1 : z < 1 := lt_of_le_of_ne hz1 hz1'
  unfold house at hh
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_prod, Set.mem_Icc,
    Set.mem_Ioo, Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  rcases hh with hf | he
  · rcases hf with hf | hw
    · rcases hf.1.2.2 with hz | hz
      · linarith
      · rcases hz with hz | hz <;> linarith
    · rcases hw with h1234 | h5
      · rcases h1234 with h123 | h4
        · rcases h123 with hab | h3
          · rcases hab with h1 | h2
            · have hz' := h1.2.2.1
              linarith
            · exact hx2 h2.1
          · have hx' := h3.1
            linarith
        · have hz' := h4.2.2.1
          linarith
      · have hx' := h5.1.1
        linarith

  · rcases he with he | he
    · rcases he.2.1 with h | h <;> norm_num at h
    · rcases he.1 with h | h <;> linarith

def pp (p:V) : V :=
  (1 + su (p.1-1) p.2.2, p.2.1, sv (p.1-1) p.2.2)

lemma pp_continuousOn : ContinuousOn pp panel := by
  let A : V → (ℝ × ℝ) := fun p => (p.1-1, p.2.2)
  have hA : Continuous A := by unfold A; fun_prop
  have hMaps : MapsTo A panel (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
    intro p hp
    exact ⟨⟨by exact sub_nonneg.mpr hp.1.1,
               by linarith [hp.1.2]⟩,
      hp.2.2⟩
  have hu : ContinuousOn (fun p : V => su (A p).1 (A p).2) panel :=
    continuousOn_su.comp hA.continuousOn hMaps
  have hv : ContinuousOn (fun p : V => sv (A p).1 (A p).2) panel :=
    continuousOn_sv.comp hA.continuousOn hMaps
  change ContinuousOn
    (fun p : V => (1 + su (p.1-1) p.2.2, p.2.1,
       sv (p.1-1) p.2.2)) panel
  exact (continuousOn_const.add hu).prodMk
    ((continuous_fst.comp continuous_snd).continuousOn.prodMk hv)

lemma pp_mem_house {p : V} (hp : p ∈ panel) : pp p ∈ house := by
  rcases p with ⟨x,y,z⟩
  rcases hp with ⟨hx,hy,hz⟩
  have hy' : y = 1 := by simpa using hy
  have b := sm_bounds (u:=x-1) (v:=z)
    (by linarith [hx.1]) (by linarith [hx.2]) hz.1 hz.2
  have e := sm_horn (u:=x-1) (v:=z)
    (by linarith [hx.1]) (by linarith [hx.2]) hz.1 hz.2
  unfold pp
  apply panel_horn_mem
  · exact ⟨by linarith [b.1], by linarith [b.2.1]⟩
  · exact hy'
  · exact ⟨b.2.2.1, b.2.2.2⟩
  · rcases e with e | e | e
    · left; linarith
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)

lemma pp_fix_house {p : V} (hp : p ∈ panel) (hh : p ∈ house) : pp p = p := by
  rcases p with ⟨x,y,z⟩
  rcases hp with ⟨hx,hy,hz⟩
  have hy' : y = 1 := by simpa using hy
  have edge := panel_inter_house hx hy' hz hh
  have e' : x - 1 = 1 ∨ z=0 ∨ z=1 := by
    rcases edge with e | e
    · left; linarith
    · exact Or.inr e
  have eqs := sm_fix (u:=x-1) (v:=z)
    (by linarith [hx.1]) (by linarith [hx.2]) hz.1 hz.2 e'
  unfold pp
  dsimp
  have hx' : 1 + su (x-1) z = x := by linarith [eqs.1]
  simp [hx', eqs.2]

lemma panel_retraction :
    ∃ r : C((panelR : Set V), (house : Set V)),
      ∀ x : (house : Set V), r ⟨x.1, Or.inl x.2⟩ = x := by
  classical
  let f : V → V := fun p => if p ∈ panel then pp p else p
  have fpanel : ∀ p ∈ panel, f p = pp p := by
    intro p hp; simp [f, hp]
  have fhouse : ∀ p ∈ house, f p = p := by
    intro p hp
    unfold f
    split_ifs with h
    · exact pp_fix_house h hp
    · rfl
  have fmap : ∀ p ∈ panelR, f p ∈ house := by
    intro p hp
    rcases hp with hp | hp
    · simpa [fhouse p hp] using hp
    · have hp' := pp_mem_house hp
      simpa [f, hp] using hp'
  have hfP : ContinuousOn f panel := by
    exact pp_continuousOn.congr (by intro p hp; exact fpanel p hp)
  have hfH : ContinuousOn f house := by
    exact continuous_id.continuousOn.congr (by intro p hp; exact fhouse p hp)
  have hfR : ContinuousOn f panelR := by
    exact hfH.union_of_isClosed hfP house_closed panel_closed
  have hfc : Continuous (fun x : (panelR : Set V) =>
      (⟨f x, fmap x x.2⟩ : (house : Set V))) := by
    apply Continuous.subtype_mk ?_ _
    exact (continuousOn_iff_continuous_restrict.mp hfR)
  refine ⟨⟨(fun x => (⟨f x, fmap x x.2⟩ : (house : Set V))), hfc⟩, ?_⟩
  intro x
  apply Subtype.ext
  exact fhouse x x.2

end
end HouseSupport

-- END INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Tail.lean

-- BEGIN INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Sweep.lean
namespace HouseSupport
open Set
noncomputable section

structure At where
  n : Nat
  edge : Bool
  deriving DecidableEq, Repr

@[match_pattern] def E (n:Nat) : At := ⟨n,true⟩
@[match_pattern] def P (n:Nat) : At := ⟨n,false⟩

inductive Ax | X | Y | Z
  deriving DecidableEq, Repr

structure Q where
  x : At
  y : At
  z : At
  deriving DecidableEq, Repr

def lo (a:At) : ℝ := a.n
def hi (a:At) : ℝ := a.n + (if a.edge then 1 else 0)
def carrA (a:At) : Set ℝ := Icc (lo a) (hi a)
def ca (c:Q) : Set V := carrA c.x ×ˢ carrA c.y ×ˢ carrA c.z

def qa (c:Q) : Ax → At
 | Ax.X => c.x
 | Ax.Y => c.y
 | Ax.Z => c.z

def coord (p:V) : Ax → ℝ
 | Ax.X => p.1
 | Ax.Y => p.2.1
 | Ax.Z => p.2.2

lemma mem_ca (c:Q) (p:V) :
    p ∈ ca c ↔ (coord p Ax.X ∈ carrA (qa c Ax.X) ∧
      coord p Ax.Y ∈ carrA (qa c Ax.Y) ∧ coord p Ax.Z ∈ carrA (qa c Ax.Z)) := by
  rfl

def witha (c:Q) (i:Ax) (a:At) : Q := match i with
 | .X => ⟨a,c.y,c.z⟩
 | .Y => ⟨c.x,a,c.z⟩
 | .Z => ⟨c.x,c.y,a⟩

def fac (c:Q) (i:Ax) (b:Bool) : Q :=
  witha c i (P ((qa c i).n + (if b then 1 else 0)))

def kterm (b:Bool) (u:ℝ) : ℝ := if b then (2-u)/2 else (u+1)/2
def jterm (e:Bool) (v:ℝ) : ℝ := if e then |2*v-1| else 0
def den (b:Bool) (u:ℝ) (e:Bool) (v:ℝ) (d:Bool) (w:ℝ) : ℝ :=
  max (kterm b u) (max (jterm e v) (jterm d w))
def kout (b:Bool) (u s:ℝ) : ℝ := if b then 2 + (u-2)/s else -1 + (u+1)/s
def jout (e:Bool) (v s:ℝ) : ℝ := if e then (1/2:ℝ) + (v-1/2)/s else v

lemma den_pos {b e d:Bool} {u v w:ℝ} (hu0:0≤u) (hu1:u≤1) :
    0 < den b u e v d w := by
  unfold den kterm
  have : 0 < (if b then (2-u)/2 else (u+1)/2) := by
    cases b <;> simp <;> linarith
  exact lt_of_lt_of_le this (le_max_left _ _)

lemma den_le {b e d:Bool} {u v w:ℝ}
 (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) (hw0:0≤w) (hw1:w≤1) :
 den b u e v d w ≤ 1 := by
  unfold den
  apply max_le
  · unfold kterm; cases b <;> simp <;> linarith
  · apply max_le <;> unfold jterm
    · cases e <;> simp
      exact (abs_le).2 ⟨by linarith, by linarith⟩
    · cases d <;> simp
      exact (abs_le).2 ⟨by linarith, by linarith⟩

-- side-coordinate bounds; a useful elementary division estimate
lemma jout_bounds {v s:ℝ} (hp:0<s) (ht: |2*v-1| ≤ s) :
    0 ≤ (1/2:ℝ) + (v-1/2)/s ∧ (1/2:ℝ) + (v-1/2)/s ≤ 1 := by
  have ha : |v-(1/2:ℝ)| * 2 ≤ s := by
    have he : |2*v-1| = 2 * |v-(1/2:ℝ)| := by
      rw [show 2*v-1=2*(v-(1/2:ℝ)) by ring]
      rw [abs_mul, abs_of_nonneg (by norm_num:(0:ℝ)≤2)]
    rw [he] at ht
    linarith
  constructor
  · apply (sub_nonneg.mp ?_ : _)
    -- easier by lower bound on quotient
    have h : -(1/2:ℝ) ≤ (v-(1/2:ℝ))/s := by
      apply (le_div_iff₀ hp).2
      have hx : -|v-(1/2:ℝ)| ≤ v-(1/2:ℝ) := neg_abs_le _
      nlinarith
    linarith
  · have h : (v-(1/2:ℝ))/s ≤ (1/2:ℝ) := by
      apply (div_le_iff₀ hp).2
      have hx : v-(1/2:ℝ) ≤ |v-(1/2:ℝ)| := le_abs_self _
      nlinarith
    linarith

lemma side_edge {v s:ℝ} (hp:0<s) (h : s = |2*v-1|) :
    (1/2:ℝ) + (v-1/2)/s = 0 ∨ (1/2:ℝ) + (v-1/2)/s = 1 := by
  have hn : 2*v-1 ≠ 0 := by
    have : |2*v-1| ≠ 0 := by rw [← h]; linarith
    exact abs_ne_zero.mp this
  rcases le_total 0 (2*v-1) with hx|hx
  · right
    rw [h, abs_of_nonneg hx]
    field_simp [hn]
    <;> ring
  · left
    rw [h, abs_of_nonpos hx]
    field_simp [hn]
    <;> ring

/-- the calculation of the cubical elementary collapse. The first coordinate is
normal to the deleted face; `b=true` means the upper face. `e,d` tell whether
the other two coordinates are present (a square, cube, or edge). -/
lemma cube_calc {b e d:Bool} {u v w:ℝ}
 (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) (hw0:0≤w) (hw1:w≤1) :
 let s := den b u e v d w
 ( (0 ≤ kout b u s ∧ kout b u s ≤ 1) ∧
   (0 ≤ jout e v s ∧ jout e v s ≤ 1) ∧
   (0 ≤ jout d w s ∧ jout d w s ≤ 1)) ∧
 ((kout b u s = (if b then 0 else 1)) ∨
   (e = true ∧ (jout e v s = 0 ∨ jout e v s = 1)) ∨
   (d = true ∧ (jout d w s = 0 ∨ jout d w s = 1))) := by
  dsimp
  let s := den b u e v d w
  change
   (((0 ≤ kout b u s ∧ kout b u s ≤ 1) ∧
    (0 ≤ jout e v s ∧ jout e v s ≤ 1) ∧
    (0 ≤ jout d w s ∧ jout d w s ≤ 1)) ∧
    (kout b u s = (if b then 0 else 1) ∨
     (e = true ∧ (jout e v s = 0 ∨ jout e v s = 1)) ∨
     (d = true ∧ (jout d w s = 0 ∨ jout d w s = 1))))
  have hp : 0 < s := den_pos hu0 hu1
  have hle : s ≤ (1:ℝ) := den_le hu0 hu1 hv0 hv1 hw0 hw1
  have hk : kterm b u ≤ s := le_max_left _ _
  have he : jterm e v ≤ s := le_trans (le_max_left _ _) (le_max_right _ _)
  have hd : jterm d w ≤ s := le_trans (le_max_right _ _) (le_max_right _ _)
  have kbounds : 0 ≤ kout b u s ∧ kout b u s ≤ 1 := by
    unfold kout
    cases b <;> simp_all [kterm] -- maybe
    · have hlow : s ≤ u+1 := le_trans hle (by linarith)
      have hhigh : u+1 ≤ 2*s := by linarith
      have h1 : (1:ℝ) ≤ (u+1)/s := (le_div_iff₀ hp).2 (by linarith)
      have h2 : (u+1)/s ≤ (2:ℝ) := (div_le_iff₀ hp).2 (by linarith)
      constructor <;> linarith
    · have hlow : s ≤ 2-u := le_trans hle (by linarith)
      have hhigh : 2-u ≤ 2*s := by linarith
      have h1 : (1:ℝ) ≤ (2-u)/s := (le_div_iff₀ hp).2 (by linarith)
      have h2 : (2-u)/s ≤ (2:ℝ) := (div_le_iff₀ hp).2 (by linarith)
      have hx : (u-2)/s = -((2-u)/s) := by ring
      constructor <;> linarith
  have ebounds : 0 ≤ jout e v s ∧ jout e v s ≤1 := by
    cases e
    · change 0 ≤ v ∧ v ≤ 1
      exact ⟨hv0,hv1⟩
    · change 0 ≤ (1/2:ℝ) + (v-1/2)/s ∧ (1/2:ℝ)+(v-1/2)/s ≤ 1
      exact jout_bounds hp (by simpa [jterm] using he)
  have dbounds : 0 ≤ jout d w s ∧ jout d w s ≤1 := by
    cases d
    · change 0 ≤ w ∧ w ≤ 1
      exact ⟨hw0,hw1⟩
    · change 0 ≤ (1/2:ℝ) + (w-1/2)/s ∧ (1/2:ℝ)+(w-1/2)/s ≤ 1
      exact jout_bounds hp (by simpa [jterm] using hd)
  refine ⟨⟨kbounds, ebounds, dbounds⟩, ?_⟩
  -- a maximum term is attained
  have which : s = kterm b u ∨ s = jterm e v ∨ s = jterm d w := by
    dsimp [s, den]
    rcases (max_cases (kterm b u) (max (jterm e v) (jterm d w))) with h|h
    · exact Or.inl h.1
    · rcases (max_cases (jterm e v) (jterm d w)) with h'|h'
      · exact Or.inr (Or.inl (by rw [h.1, h'.1]))
      · exact Or.inr (Or.inr (by rw [h.1, h'.1]))
  rcases which with h|h|h
  · left
    cases b <;> simp [kout, kterm] at h ⊢
    · rw [h]
      have hn : (u+1)/2 ≠ 0 := by linarith
      field_simp [hn] <;> ring
    · rw [h]
      have hn : 2-u ≠ 0 := by linarith
      field_simp [hn] <;> ring
  · cases e with
    | false => simp [jterm] at h; linarith
    | true =>
      right; left
      refine ⟨rfl, ?_⟩
      exact side_edge hp (by simpa [jterm] using h)
  · cases d with
    | false => simp [jterm] at h; linarith
    | true =>
      right; right
      refine ⟨rfl, ?_⟩
      exact side_edge hp (by simpa [jterm] using h)

lemma cube_fix {b e d:Bool} {u v w:ℝ}
 (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) (hw0:0≤w) (hw1:w≤1)
 (H : u = (if b then 0 else 1) ∨
       (e = true ∧ (v=0 ∨ v=1)) ∨ (d=true ∧ (w=0 ∨ w=1))) :
 let s := den b u e v d w
 kout b u s = u ∧ jout e v s = v ∧ jout d w s = w := by
  dsimp
  let s := den b u e v d w
  change kout b u s = u ∧ jout e v s = v ∧ jout d w s = w
  have hp : 0 < s := den_pos hu0 hu1
  have hle : s ≤ (1:ℝ) := den_le hu0 hu1 hv0 hv1 hw0 hw1
  have hge : (1:ℝ) ≤ s := by
    rcases H with h|h|h
    · have h' : (1:ℝ) ≤ kterm b u := by
        cases b <;> simp_all [kterm]
      exact h'.trans (le_max_left _ _)
    · rcases h with ⟨he,hv⟩
      have h' : (1:ℝ) ≤ jterm e v := by
        subst e
        rcases hv with h|h <;> simp [jterm, h] <;> norm_num
      exact h'.trans (le_trans (le_max_left _ _) (le_max_right _ _))
    · rcases h with ⟨he,hv⟩
      have h' : (1:ℝ) ≤ jterm d w := by
        subst d
        rcases hv with h|h <;> simp [jterm, h] <;> norm_num
      exact h'.trans (le_trans (le_max_right _ _) (le_max_right _ _))
  have hS : s = 1 := le_antisymm hle hge
  rw [hS]
  constructor
  · cases b <;> simp [kout] <;> ring
  constructor <;> cases e <;> cases d <;> simp [jout] <;> ring

structure Mov where
  cube : Q
  k : Ax
  upper : Bool
  deriving DecidableEq, Repr

def free (m:Mov) : Q := fac m.cube m.k m.upper

def uu (c:Q) (p:V) (i:Ax) : ℝ := coord p i - lo (qa c i)

def good (m:Mov) (p:V) : Prop :=
 match m.k with
 | .X =>
   (uu m.cube p .X = (if m.upper then 0 else 1)) ∨
   ((qa m.cube .Y).edge = true ∧
      (uu m.cube p .Y = 0 ∨ uu m.cube p .Y = 1)) ∨
   ((qa m.cube .Z).edge = true ∧
      (uu m.cube p .Z = 0 ∨ uu m.cube p .Z = 1))
 | .Y =>
   (uu m.cube p .Y = (if m.upper then 0 else 1)) ∨
   ((qa m.cube .X).edge = true ∧
      (uu m.cube p .X = 0 ∨ uu m.cube p .X = 1)) ∨
   ((qa m.cube .Z).edge = true ∧
      (uu m.cube p .Z = 0 ∨ uu m.cube p .Z = 1))
 | .Z =>
   (uu m.cube p .Z = (if m.upper then 0 else 1)) ∨
   ((qa m.cube .X).edge = true ∧
      (uu m.cube p .X = 0 ∨ uu m.cube p .X = 1)) ∨
   ((qa m.cube .Y).edge = true ∧
      (uu m.cube p .Y = 0 ∨ uu m.cube p .Y = 1))

/-- radial projection for a cubical elementary collapse; coordinates not
present in the cell are simply left alone. -/
def proj (m:Mov) (p:V) : V :=
 match m.k with
 | .X =>
   let u := uu m.cube p .X
   let v := uu m.cube p .Y
   let w := uu m.cube p .Z
   let s := den m.upper u (qa m.cube .Y).edge v (qa m.cube .Z).edge w
   (lo (qa m.cube .X) + kout m.upper u s,
    lo (qa m.cube .Y) + jout (qa m.cube .Y).edge v s,
    lo (qa m.cube .Z) + jout (qa m.cube .Z).edge w s)
 | .Y =>
   let u := uu m.cube p .Y
   let v := uu m.cube p .X
   let w := uu m.cube p .Z
   let s := den m.upper u (qa m.cube .X).edge v (qa m.cube .Z).edge w
   (lo (qa m.cube .X) + jout (qa m.cube .X).edge v s,
    lo (qa m.cube .Y) + kout m.upper u s,
    lo (qa m.cube .Z) + jout (qa m.cube .Z).edge w s)
 | .Z =>
   let u := uu m.cube p .Z
   let v := uu m.cube p .X
   let w := uu m.cube p .Y
   let s := den m.upper u (qa m.cube .X).edge v (qa m.cube .Y).edge w
   (lo (qa m.cube .X) + jout (qa m.cube .X).edge v s,
    lo (qa m.cube .Y) + jout (qa m.cube .Y).edge w s,
    lo (qa m.cube .Z) + kout m.upper u s)

lemma norm_bounds (a:At) {x:ℝ} (h : x ∈ carrA a) :
    0 ≤ x - lo a ∧ x - lo a ≤ 1 := by
  rcases h with ⟨h0,h1⟩
  unfold hi lo at *
  have hh : (if a.edge then (1:ℝ) else 0) ≤ 1 := by cases a.edge <;> norm_num
  constructor
  · linarith
  · split at h1
    · norm_num at hh ⊢
      linarith
    · norm_num at hh ⊢
      linarith

lemma norm_zero (a:At) {x:ℝ} (h : x ∈ carrA a) (ha : a.edge = false) :
    x - lo a = 0 := by
  rcases h with ⟨h0,h1⟩
  unfold hi lo at *
  simp [ha] at h1
  have : (x:ℝ) = a.n := by linarith
  simp [this]

lemma mem_add (a:At) (t:ℝ) :
    lo a + t ∈ carrA a ↔ 0 ≤ t ∧ t ≤ (if a.edge then 1 else 0) := by
  unfold carrA hi lo
  simp only [Set.mem_Icc]
  constructor
  · intro h
    constructor <;> linarith [h.1, h.2]
  · intro h
    constructor <;> linarith [h.1, h.2]

lemma proj_mem_good (m:Mov)
 (hed : (qa m.cube m.k).edge = true) {p:V} (hp : p ∈ ca m.cube) :
 proj m p ∈ ca m.cube ∧ good m (proj m p) := by
  rcases m with ⟨⟨a,b,c⟩, k, side⟩
  rcases hp with ⟨ha,hb,hc⟩
  cases k
  · -- X is the normal coordinate
    change a.edge = true at hed
    have au := norm_bounds a ha; have bv := norm_bounds b hb
    have cw := norm_bounds c hc
    have hca0 := cube_calc (b:=side) (e:=b.edge) (d:=c.edge)
      au.1 au.2 bv.1 bv.2 cw.1 cw.2
    -- abbreviations
    let u := p.1 - lo a
    let v := p.2.1 - lo b
    let w := p.2.2 - lo c
    let S := den side u b.edge v c.edge w
    change (((lo a + kout side u S ∈ carrA a) ∧
       (lo b + jout b.edge v S ∈ carrA b) ∧
       (lo c + jout c.edge w S ∈ carrA c)) ∧
      ((lo a + kout side u S - lo a = (if side then 0 else 1)) ∨
       (b.edge = true ∧
          (lo b + jout b.edge v S - lo b = 0 ∨
           lo b + jout b.edge v S - lo b = 1)) ∨
       (c.edge = true ∧
          (lo c + jout c.edge w S - lo c = 0 ∨
           lo c + jout c.edge w S - lo c = 1))))
    -- rewrite the membership intervals using `mem_add`
    have hcalc :
       (((0 ≤ kout side u S ∧ kout side u S ≤ 1) ∧
         (0 ≤ jout b.edge v S ∧ jout b.edge v S ≤ 1) ∧
         (0 ≤ jout c.edge w S ∧ jout c.edge w S ≤ 1)) ∧
        (kout side u S = (if side then 0 else 1) ∨
          (b.edge = true ∧ (jout b.edge v S = 0 ∨ jout b.edge v S = 1)) ∨
          (c.edge = true ∧ (jout c.edge w S = 0 ∨ jout c.edge w S = 1)))) := by
       exact hca0
    have vz : b.edge = false → v = 0 := fun h => norm_zero b hb h
    have wz : c.edge = false → w = 0 := fun h => norm_zero c hc h
    rcases hcalc with ⟨⟨hk,hj,hl⟩, horn⟩
    have ma : lo a + kout side u S ∈ carrA a :=
      (mem_add a _).2 (by simpa [hed] using hk)
    have mb : lo b + jout b.edge v S ∈ carrA b := by
      apply (mem_add b _).2
      cases h:b.edge
      · have z : v=0 := vz h
        simpa [jout, h, z] 
      · simpa [h] using hj
    have mc : lo c + jout c.edge w S ∈ carrA c := by
      apply (mem_add c _).2
      cases h:c.edge
      · have z : w=0 := wz h
        simpa [jout, h, z]
      · simpa [h] using hl
    refine ⟨⟨ma,mb,mc⟩, ?_⟩
    -- `uu` of a projected coordinate just cancels its origin.
    simpa [add_sub_cancel_left] using horn
  · -- Y
    change b.edge = true at hed
    have au := norm_bounds a ha; have bv := norm_bounds b hb
    have cw := norm_bounds c hc
    let u := p.2.1 - lo b
    let v := p.1 - lo a
    let w := p.2.2 - lo c
    let S := den side u a.edge v c.edge w
    have hcalc := cube_calc (b:=side) (e:=a.edge) (d:=c.edge)
      bv.1 bv.2 au.1 au.2 cw.1 cw.2
    change (((lo a + jout a.edge v S ∈ carrA a) ∧
       (lo b + kout side u S ∈ carrA b) ∧
       (lo c + jout c.edge w S ∈ carrA c)) ∧
      ((lo b + kout side u S - lo b = (if side then 0 else 1)) ∨
       (a.edge = true ∧
          (lo a + jout a.edge v S - lo a = 0 ∨
           lo a + jout a.edge v S - lo a = 1)) ∨
       (c.edge = true ∧
          (lo c + jout c.edge w S - lo c = 0 ∨
           lo c + jout c.edge w S - lo c = 1))))
    change
       (((0 ≤ kout side u S ∧ kout side u S ≤ 1) ∧
         (0 ≤ jout a.edge v S ∧ jout a.edge v S ≤ 1) ∧
         (0 ≤ jout c.edge w S ∧ jout c.edge w S ≤ 1)) ∧ _) at hcalc
    rcases hcalc with ⟨⟨hk,hj,hl⟩, horn⟩
    have vz : a.edge = false → v=0 := fun h => norm_zero a ha h
    have wz : c.edge = false → w=0 := fun h => norm_zero c hc h
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · apply (mem_add a _).2
      cases h:a.edge
      · simpa [jout, h, vz h]
      · simpa [h] using hj
    · exact (mem_add b _).2 (by simpa [hed] using hk)
    · apply (mem_add c _).2
      cases h:c.edge
      · simpa [jout, h, wz h]
      · simpa [h] using hl
    · simpa [add_sub_cancel_left] using horn
  · -- Z
    change c.edge = true at hed
    have au := norm_bounds a ha; have bv := norm_bounds b hb
    have cw := norm_bounds c hc
    let u := p.2.2 - lo c
    let v := p.1 - lo a
    let w := p.2.1 - lo b
    let S := den side u a.edge v b.edge w
    have hcalc := cube_calc (b:=side) (e:=a.edge) (d:=b.edge)
      cw.1 cw.2 au.1 au.2 bv.1 bv.2
    change (((lo a + jout a.edge v S ∈ carrA a) ∧
       (lo b + jout b.edge w S ∈ carrA b) ∧
       (lo c + kout side u S ∈ carrA c)) ∧
      ((lo c + kout side u S - lo c = (if side then 0 else 1)) ∨
       (a.edge = true ∧
          (lo a + jout a.edge v S - lo a = 0 ∨
           lo a + jout a.edge v S - lo a = 1)) ∨
       (b.edge = true ∧
          (lo b + jout b.edge w S - lo b = 0 ∨
           lo b + jout b.edge w S - lo b = 1))))
    change
       (((0 ≤ kout side u S ∧ kout side u S ≤ 1) ∧
         (0 ≤ jout a.edge v S ∧ jout a.edge v S ≤ 1) ∧
         (0 ≤ jout b.edge w S ∧ jout b.edge w S ≤ 1)) ∧ _) at hcalc
    rcases hcalc with ⟨⟨hk,hj,hl⟩, horn⟩
    have vz : a.edge = false → v=0 := fun h => norm_zero a ha h
    have wz : b.edge = false → w=0 := fun h => norm_zero b hb h
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · apply (mem_add a _).2
      cases h:a.edge
      · simpa [jout, h, vz h]
      · simpa [h] using hj
    · apply (mem_add b _).2
      cases h:b.edge
      · simpa [jout, h, wz h]
      · simpa [h] using hl
    · exact (mem_add c _).2 (by simpa [hed] using hk)
    · simpa [add_sub_cancel_left] using horn

lemma proj_fix (m:Mov)
 (hed : (qa m.cube m.k).edge = true) {p:V} (hp : p ∈ ca m.cube)
 (hgood : good m p) : proj m p = p := by
  rcases m with ⟨⟨a,b,c⟩, k, side⟩
  rcases hp with ⟨ha,hb,hc⟩
  cases k
  · change a.edge = true at hed
    let u := p.1 - lo a
    let v := p.2.1 - lo b
    let w := p.2.2 - lo c
    let S := den side u b.edge v c.edge w
    have A := norm_bounds a ha; have B := norm_bounds b hb; have C := norm_bounds c hc
    have eqs := cube_fix (b:=side) (e:=b.edge) (d:=c.edge)
       A.1 A.2 B.1 B.2 C.1 C.2 hgood
    change (lo a + kout side u S, lo b + jout b.edge v S, lo c + jout c.edge w S) = p
    change kout side u S = u ∧ jout b.edge v S = v ∧ jout c.edge w S = w at eqs
    rcases p with ⟨px,py,pz⟩
    dsimp [u,v,w] at *
    obtain ⟨h1,h2,h3⟩ := eqs
    apply Prod.ext
    · dsimp; linarith
    · apply Prod.ext <;> dsimp <;> linarith
  · change b.edge = true at hed
    let u := p.2.1 - lo b
    let v := p.1 - lo a
    let w := p.2.2 - lo c
    let S := den side u a.edge v c.edge w
    have A := norm_bounds a ha; have B := norm_bounds b hb; have C := norm_bounds c hc
    have eqs := cube_fix (b:=side) (e:=a.edge) (d:=c.edge)
       B.1 B.2 A.1 A.2 C.1 C.2 hgood
    change (lo a + jout a.edge v S, lo b + kout side u S, lo c + jout c.edge w S) = p
    change kout side u S = u ∧ jout a.edge v S = v ∧ jout c.edge w S = w at eqs
    rcases p with ⟨px,py,pz⟩
    dsimp [u,v,w] at *
    obtain ⟨h1,h2,h3⟩ := eqs
    apply Prod.ext
    · dsimp; linarith
    · apply Prod.ext <;> dsimp <;> linarith
  · change c.edge = true at hed
    let u := p.2.2 - lo c
    let v := p.1 - lo a
    let w := p.2.1 - lo b
    let S := den side u a.edge v b.edge w
    have A := norm_bounds a ha; have B := norm_bounds b hb; have C := norm_bounds c hc
    have eqs := cube_fix (b:=side) (e:=a.edge) (d:=b.edge)
       C.1 C.2 A.1 A.2 B.1 B.2 hgood
    change (lo a + jout a.edge v S, lo b + jout b.edge w S, lo c + kout side u S) = p
    change kout side u S = u ∧ jout a.edge v S = v ∧ jout b.edge w S = w at eqs
    rcases p with ⟨px,py,pz⟩
    dsimp [u,v,w] at *
    obtain ⟨h1,h2,h3⟩ := eqs
    apply Prod.ext
    · dsimp; linarith
    · apply Prod.ext <;> dsimp <;> linarith

lemma ca_closed (q:Q) : IsClosed (ca q) :=
  isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)

lemma proj_cont (m:Mov) (hed : (qa m.cube m.k).edge = true) :
    ContinuousOn (proj m) (ca m.cube) := by
  -- the displayed formula is continuous; its denominator is positive on the cell
  have hn : ∀ p ∈ ca m.cube,
      match m.k with
      | .X => den m.upper (uu m.cube p .X) (qa m.cube .Y).edge (uu m.cube p .Y)
          (qa m.cube .Z).edge (uu m.cube p .Z) ≠ 0
      | .Y => den m.upper (uu m.cube p .Y) (qa m.cube .X).edge (uu m.cube p .X)
          (qa m.cube .Z).edge (uu m.cube p .Z) ≠ 0
      | .Z => den m.upper (uu m.cube p .Z) (qa m.cube .X).edge (uu m.cube p .X)
          (qa m.cube .Y).edge (uu m.cube p .Y) ≠ 0 := by
    intro p hp
    rcases hp with ⟨hx,hy,hz⟩
    cases h:m.k
    · exact ne_of_gt (den_pos (norm_bounds _ hx).1 (norm_bounds _ hx).2)
    · exact ne_of_gt (den_pos (norm_bounds _ hy).1 (norm_bounds _ hy).2)
    · exact ne_of_gt (den_pos (norm_bounds _ hz).1 (norm_bounds _ hz).2)
  rcases m with ⟨⟨a,b,c⟩, k, side⟩
  cases k
  all_goals
   -- `fun_prop` knows abs/max and all affine expressions; division is `div₀`.
   -- first package the denominator
   simp only []
  · let U : V → ℝ := fun p => p.1 - lo a
    let W : V → ℝ := fun p => p.2.1 - lo b
    let T : V → ℝ := fun p => p.2.2 - lo c
    let S : V → ℝ := fun p => den side (U p) b.edge (W p) c.edge (T p)
    have hu : Continuous U := by unfold U; fun_prop
    have hv : Continuous W := by unfold W; fun_prop
    have hw : Continuous T := by unfold T; fun_prop
    have hs : Continuous S := by
      unfold S den kterm jterm
      cases side <;> cases b.edge <;> cases c.edge <;> simp <;> fun_prop
    have inv (N: V → ℝ) (hN:Continuous N) : ContinuousOn (fun p => N p / S p) (ca {x:=a,y:=b,z:=c}) :=
      hN.continuousOn.div₀ hs.continuousOn hn
    change ContinuousOn
      (fun p : V =>
        (lo a + (if side then 2 + (U p - 2) / S p else -1 + (U p + 1) / S p),
         lo b + (if b.edge then (1/2:ℝ) + (W p-1/2)/S p else W p),
         lo c + (if c.edge then (1/2:ℝ) + (T p-1/2)/S p else T p))) (ca {x:=a,y:=b,z:=c})
    have A : ContinuousOn (fun p => if side then 2 + (U p - 2)/S p else -1+(U p+1)/S p) (ca {x:=a,y:=b,z:=c}) := by
      cases side <;> simp <;>
        exact continuousOn_const.add (inv _ (by fun_prop))
    have B : ContinuousOn (fun p => if b.edge then (1/2:ℝ)+(W p-1/2)/S p else W p) (ca {x:=a,y:=b,z:=c}) := by
      cases b.edge <;> simp
      · exact hv.continuousOn
      · exact continuousOn_const.add (inv _ (by fun_prop))
    have C : ContinuousOn (fun p => if c.edge then (1/2:ℝ)+(T p-1/2)/S p else T p) (ca {x:=a,y:=b,z:=c}) := by
      cases c.edge <;> simp
      · exact hw.continuousOn
      · exact continuousOn_const.add (inv _ (by fun_prop))
    exact (continuousOn_const.add A).prodMk ((continuousOn_const.add B).prodMk (continuousOn_const.add C))
  · let U : V → ℝ := fun p => p.2.1 - lo b
    let W : V → ℝ := fun p => p.1 - lo a
    let T : V → ℝ := fun p => p.2.2 - lo c
    let S : V → ℝ := fun p => den side (U p) a.edge (W p) c.edge (T p)
    have hw : Continuous W := by unfold W; fun_prop
    have hu : Continuous U := by unfold U; fun_prop
    have ht : Continuous T := by unfold T; fun_prop
    have hs : Continuous S := by unfold S den kterm jterm; cases side <;> cases a.edge <;> cases c.edge <;> simp <;> fun_prop
    have inv (N: V → ℝ) (hN:Continuous N) : ContinuousOn (fun p => N p / S p) (ca {x:=a,y:=b,z:=c}) := hN.continuousOn.div₀ hs.continuousOn hn
    change ContinuousOn
      (fun p : V =>
        (lo a + (if a.edge then (1/2:ℝ)+(W p-1/2)/S p else W p),
         lo b + (if side then 2+(U p-2)/S p else -1+(U p+1)/S p),
         lo c + (if c.edge then (1/2:ℝ)+(T p-1/2)/S p else T p))) _
    have A : ContinuousOn (fun p => if a.edge then (1/2:ℝ)+(W p-1/2)/S p else W p) (ca {x:=a,y:=b,z:=c}) := by cases a.edge <;> simp; exact hw.continuousOn; exact continuousOn_const.add (inv _ (by fun_prop))
    have B : ContinuousOn (fun p => if side then 2+(U p-2)/S p else -1+(U p+1)/S p) (ca {x:=a,y:=b,z:=c}) := by cases side <;> simp <;> exact continuousOn_const.add (inv _ (by fun_prop))
    have C : ContinuousOn (fun p => if c.edge then (1/2:ℝ)+(T p-1/2)/S p else T p) (ca {x:=a,y:=b,z:=c}) := by cases c.edge <;> simp; exact ht.continuousOn; exact continuousOn_const.add (inv _ (by fun_prop))
    exact (continuousOn_const.add A).prodMk ((continuousOn_const.add B).prodMk (continuousOn_const.add C))
  · let U : V → ℝ := fun p => p.2.2 - lo c
    let W : V → ℝ := fun p => p.1 - lo a
    let T : V → ℝ := fun p => p.2.1 - lo b
    let S : V → ℝ := fun p => den side (U p) a.edge (W p) b.edge (T p)
    have hw : Continuous W := by unfold W; fun_prop
    have ht : Continuous T := by unfold T; fun_prop
    have hu : Continuous U := by unfold U; fun_prop
    have hs : Continuous S := by unfold S den kterm jterm; cases side <;> cases a.edge <;> cases b.edge <;> simp <;> fun_prop
    have inv (N: V → ℝ) (hN:Continuous N) : ContinuousOn (fun p => N p / S p) (ca {x:=a,y:=b,z:=c}) := hN.continuousOn.div₀ hs.continuousOn hn
    change ContinuousOn
      (fun p : V =>
        (lo a + (if a.edge then (1/2:ℝ)+(W p-1/2)/S p else W p),
         lo b + (if b.edge then (1/2:ℝ)+(T p-1/2)/S p else T p),
         lo c + (if side then 2+(U p-2)/S p else -1+(U p+1)/S p))) _
    have A : ContinuousOn (fun p => if a.edge then (1/2:ℝ)+(W p-1/2)/S p else W p) (ca {x:=a,y:=b,z:=c}) := by cases a.edge <;> simp; exact hw.continuousOn; exact continuousOn_const.add (inv _ (by fun_prop))
    have B : ContinuousOn (fun p => if b.edge then (1/2:ℝ)+(T p-1/2)/S p else T p) (ca {x:=a,y:=b,z:=c}) := by cases b.edge <;> simp; exact ht.continuousOn; exact continuousOn_const.add (inv _ (by fun_prop))
    have C : ContinuousOn (fun p => if side then 2+(U p-2)/S p else -1+(U p+1)/S p) (ca {x:=a,y:=b,z:=c}) := by cases side <;> simp <;> exact continuousOn_const.add (inv _ (by fun_prop))
    exact (continuousOn_const.add A).prodMk ((continuousOn_const.add B).prodMk (continuousOn_const.add C))


end
end HouseSupport

-- END INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Sweep.lean

-- BEGIN INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Collapse.lean
namespace HouseSupport
open Set
noncomputable section

/-- Gluing lemma for one elementary cubical collapse.  The set `T` is the part of
 the complex which is left over.  On the cube we use the radial map `proj`, and
 on `T` the identity.  The two elementary set-theoretic hypotheses say precisely
 that their intersection is the (five-sided, or lower dimensional) good
 boundary. -/
lemma collapse_patch (m:Mov) (hed : (qa m.cube m.k).edge = true)
    (T : Set V) (hT : IsClosed T)
    (hface : ∀ p, p ∈ ca m.cube → good m p → p ∈ T)
    (hinter : ∀ p, p ∈ ca m.cube → p ∈ T → good m p) :
    ∃ r : C(((ca m.cube ∪ T):Set V), (T:Set V)),
      ∀ x : (T:Set V), r ⟨x.1, Or.inr x.2⟩ = x := by
  classical
  let f : V → V := fun p => if p ∈ ca m.cube then proj m p else p
  have fT (p:V) (hp:p∈T) : f p = p := by
    unfold f
    split_ifs with h
    · exact proj_fix m hed h (hinter p h hp)
    · rfl
  have fc (p:V) (hp:p∈ca m.cube) : f p = proj m p := by
    simp [f, hp]
  have fcontc : ContinuousOn f (ca m.cube) := by
    exact (proj_cont m hed).congr (fun p hp => (fc p hp))
  have fcontt : ContinuousOn f T := by
    -- On the remainder the map is literally the identity.
    exact continuousOn_id.congr (fun p hp => (fT p hp))
  have fcont : ContinuousOn f (ca m.cube ∪ T) :=
    fcontc.union_of_isClosed fcontt (ca_closed _) hT
  have frange : ∀ p ∈ ca m.cube ∪ T, f p ∈ T := by
    intro p hp
    rcases hp with hp | hp
    · rw [fc p hp]
      have z := proj_mem_good m hed hp
      exact hface _ z.1 z.2
    · rw [fT p hp]
      exact hp
  let rr : ((ca m.cube ∪ T):Set V) → (T:Set V) :=
    fun p => ⟨f p.1, frange p.1 p.2⟩
  have rrcont : Continuous rr := by
    -- continuous-on on a set is continuity out of the corresponding subtype
    apply Continuous.subtype_mk _ _
    exact continuousOn_iff_continuous_restrict.mp fcont
  refine ⟨⟨rr, rrcont⟩, ?_⟩
  intro x
  apply Subtype.ext
  exact fT x.1 x.2

end
end HouseSupport

namespace HouseSupport
open Set
noncomputable section

/-- Integral length of an atom. -/
def alen (a:At) : Nat := if a.edge then 1 else 0

lemma hi_cast (a:At) : hi a = ( (a.n + alen a : Nat) : ℝ) := by
  unfold hi alen
  cases a.edge <;> norm_num

lemma lo_cast (a:At) : lo a = (a.n:ℝ) := rfl

def sepA (a d:At) : Prop := a.n + alen a < d.n ∨ d.n + alen d < a.n
def lowA (a d:At) : Prop := d.n + alen d ≤ a.n
def highA (a d:At) : Prop := a.n + 1 ≤ d.n
instance (a d:At) : Decidable (sepA a d) := by unfold sepA alen; infer_instance
instance (a d:At) : Decidable (lowA a d) := by unfold lowA alen; infer_instance
instance (a d:At) : Decidable (highA a d) := by unfold highA; infer_instance

lemma sepA_not {a d:At} {t:ℝ}
    (ha : t ∈ carrA a) (hd : t ∈ carrA d) (h:sepA a d) : False := by
  rcases ha with ⟨ha0,ha1⟩
  rcases hd with ⟨hd0,hd1⟩
  simp [hi_cast, lo_cast] at ha0 ha1 hd0 hd1
  rcases h with h|h
  · have hh : ((a.n + alen a : Nat):ℝ) < (d.n:ℝ) := by exact_mod_cast h
    push_cast at hh
    linarith
  · have hh : ((d.n + alen d : Nat):ℝ) < (a.n:ℝ) := by exact_mod_cast h
    push_cast at hh
    linarith

lemma lowA_eq {a d:At} {t:ℝ}
    (ha : t ∈ carrA a) (hd : t ∈ carrA d) (h:lowA a d) : t - lo a = 0 := by
  rcases ha with ⟨ha0,ha1⟩
  rcases hd with ⟨hd0,hd1⟩
  simp [hi_cast, lo_cast] at ha0 ha1 hd0 hd1
  have hh : ((d.n + alen d : Nat):ℝ) ≤ (a.n:ℝ) := by exact_mod_cast h
  push_cast at hh
  dsimp [lo]
  linarith

lemma highA_eq {a d:At} {t:ℝ}
    (ea : a.edge = true)
    (ha : t ∈ carrA a) (hd : t ∈ carrA d) (h:highA a d) : t - lo a = 1 := by
  rcases ha with ⟨ha0,ha1⟩
  rcases hd with ⟨hd0,hd1⟩
  simp [hi_cast, lo_cast] at ha0 ha1 hd0 hd1
  have hh : ((a.n + 1 : Nat):ℝ) ≤ (d.n:ℝ) := by exact_mod_cast h
  have al : alen a = 1 := by simp [alen, ea]
  rw [al] at ha1
  have hh' : ((a.n:Nat):ℝ) + 1 ≤ (d.n:ℝ) := by exact_mod_cast h
  push_cast at hh
  dsimp [lo]
  norm_num at ha1
  push_cast at ha1
  linarith

lemma facet_mem {c:Q} {i:Ax} (he:(qa c i).edge = true)
    {b:Bool} {p:V} (hp:p∈ ca c)
    (hz : uu c p i = (if b then 1 else 0)) : p ∈ ca (fac c i b) := by
  rcases c with ⟨a,d,e⟩
  rcases hp with ⟨ha,hd,hf⟩
  rcases p with ⟨x,y,z⟩
  cases i <;> dsimp [fac, witha, qa, ca, uu, coord, carrA, hi, lo] at *
  · -- X
    refine ⟨?_, hd, hf⟩
    -- point atom
    constructor <;> simp [P, hi, lo]
    all_goals
      cases b <;> simp_all [P, hi, lo] <;> try linarith
    -- try arithmetic
  · refine ⟨ha, ?_, hf⟩
    constructor <;> simp [P, hi, lo]
    all_goals cases b <;> simp_all [P, hi, lo] <;> try linarith
  · refine ⟨ha, hd, ?_⟩
    constructor <;> simp [P, hi, lo]
    all_goals cases b <;> simp_all [P, hi, lo] <;> try linarith

/-- cells with pairwise integer endpoints can only meet across one of these
certified boundary positions. `okCell` is a conveniently decidable certificate. -/
def disjQ (c q:Q) : Prop :=
  sepA c.x q.x ∨ sepA c.y q.y ∨ sepA c.z q.z

-- a certificate that every intersection point of q with the collapsing cell is good
def okCell (m:Mov) (q:Q) : Prop :=
  disjQ m.cube q ∨
  match m.k with
  | .X =>
    (if m.upper then lowA m.cube.x q.x else highA m.cube.x q.x) ∨
    (m.cube.y.edge = true ∧ (lowA m.cube.y q.y ∨ highA m.cube.y q.y)) ∨
    (m.cube.z.edge = true ∧ (lowA m.cube.z q.z ∨ highA m.cube.z q.z))
  | .Y =>
    (if m.upper then lowA m.cube.y q.y else highA m.cube.y q.y) ∨
    (m.cube.x.edge = true ∧ (lowA m.cube.x q.x ∨ highA m.cube.x q.x)) ∨
    (m.cube.z.edge = true ∧ (lowA m.cube.z q.z ∨ highA m.cube.z q.z))
  | .Z =>
    (if m.upper then lowA m.cube.z q.z else highA m.cube.z q.z) ∨
    (m.cube.x.edge = true ∧ (lowA m.cube.x q.x ∨ highA m.cube.x q.x)) ∨
    (m.cube.y.edge = true ∧ (lowA m.cube.y q.y ∨ highA m.cube.y q.y))
instance (c q:Q) : Decidable (disjQ c q) := by unfold disjQ; infer_instance
instance (m:Mov) (q:Q) : Decidable (okCell m q) := by
  unfold okCell
  cases m.k <;> dsimp <;> infer_instance

lemma okCell_good (m:Mov) (q:Q)
    (hed : (qa m.cube m.k).edge = true) {p:V}
    (hp:p∈ca m.cube) (hq:p∈ca q) (hok:okCell m q) : good m p := by
  rcases m with ⟨⟨a,b,c⟩, k, u⟩
  rcases q with ⟨d,e,f⟩
  rcases hp with ⟨ha,hb,hc⟩
  rcases hq with ⟨hd,he,hf⟩
  -- common impossibility
  have notdis : ¬ disjQ {x:=a,y:=b,z:=c} {x:=d,y:=e,z:=f} := by
    intro h
    rcases h with h|h|h
    · exact sepA_not ha hd h
    · exact sepA_not hb he h
    · exact sepA_not hc hf h
  change disjQ {x:=a,y:=b,z:=c} {x:=d,y:=e,z:=f} ∨ _ at hok
  rcases hok with bad|hok
  · exact (notdis bad).elim
  cases k
  · -- X
    change a.edge = true at hed
    change (if u then lowA a d else highA a d) ∨
      (b.edge = true ∧ (lowA b e ∨ highA b e)) ∨
      (c.edge = true ∧ (lowA c f ∨ highA c f)) at hok
    change
      (uu {x:=a,y:=b,z:=c} p .X = (if u then 0 else 1)) ∨
       (b.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .Y=0 ∨ uu {x:=a,y:=b,z:=c} p .Y=1)) ∨
       (c.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .Z=0 ∨ uu {x:=a,y:=b,z:=c} p .Z=1))
    rcases hok with hk|hk|hk
    · left
      cases u
      · -- upper false -> high
        simpa [uu, coord, qa] using (highA_eq hed ha hd hk)
      · simpa [uu, coord, qa] using (lowA_eq ha hd hk)
    · right; left
      refine ⟨hk.1, ?_⟩
      rcases hk.2 with t|t
      · left; exact lowA_eq hb he t
      · right; exact highA_eq hk.1 hb he t
    · right; right
      refine ⟨hk.1, ?_⟩
      rcases hk.2 with t|t
      · left; exact lowA_eq hc hf t
      · right; exact highA_eq hk.1 hc hf t
  · -- Y
    change b.edge = true at hed
    change (if u then lowA b e else highA b e) ∨
      (a.edge = true ∧ (lowA a d ∨ highA a d)) ∨
      (c.edge = true ∧ (lowA c f ∨ highA c f)) at hok
    change
      (uu {x:=a,y:=b,z:=c} p .Y = (if u then 0 else 1)) ∨
       (a.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .X=0 ∨ uu {x:=a,y:=b,z:=c} p .X=1)) ∨
       (c.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .Z=0 ∨ uu {x:=a,y:=b,z:=c} p .Z=1))
    rcases hok with hk|hk|hk
    · left; cases u
      · simpa [uu, coord, qa] using (highA_eq hed hb he hk)
      · simpa [uu, coord, qa] using (lowA_eq hb he hk)
    · right; left; refine ⟨hk.1, ?_⟩
      rcases hk.2 with t|t
      · left; exact lowA_eq ha hd t
      · right; exact highA_eq hk.1 ha hd t
    · right; right; refine ⟨hk.1, ?_⟩
      rcases hk.2 with t|t
      · left; exact lowA_eq hc hf t
      · right; exact highA_eq hk.1 hc hf t
  · -- Z
    change c.edge = true at hed
    change (if u then lowA c f else highA c f) ∨
      (a.edge = true ∧ (lowA a d ∨ highA a d)) ∨
      (b.edge = true ∧ (lowA b e ∨ highA b e)) at hok
    change
      (uu {x:=a,y:=b,z:=c} p .Z = (if u then 0 else 1)) ∨
       (a.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .X=0 ∨ uu {x:=a,y:=b,z:=c} p .X=1)) ∨
       (b.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .Y=0 ∨ uu {x:=a,y:=b,z:=c} p .Y=1))
    rcases hok with hk|hk|hk
    · left; cases u
      · simpa [uu, coord, qa] using (highA_eq hed hc hf hk)
      · simpa [uu, coord, qa] using (lowA_eq hc hf hk)
    · right; left; refine ⟨hk.1, ?_⟩
      rcases hk.2 with t|t
      · left; exact lowA_eq ha hd t
      · right; exact highA_eq hk.1 ha hd t
    · right; right; refine ⟨hk.1, ?_⟩
      rcases hk.2 with t|t
      · left; exact lowA_eq hb he t
      · right; exact highA_eq hk.1 hb he t

end
end HouseSupport

-- END INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Collapse.lean

-- BEGIN INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Complex.lean
namespace HouseSupport
open Set
noncomputable section

def cells (L:List Q) : Set V := {p | ∃ q ∈ L, p ∈ ca q}
lemma mem_cells {L:List Q} {p:V} : p∈cells L ↔ ∃ q∈L, p∈ca q := Iff.rfl
lemma cells_closed (L:List Q) : IsClosed (cells L) := by
  induction L with
  | nil =>
    have h : cells [] = (∅:Set V) := by ext p; simp [cells]
    rw [h]
    exact isClosed_empty
  | cons a l ih =>
    have h : cells (a::l) = ca a ∪ cells l := by
      ext p; simp [cells]
    rw [h]
    exact (ca_closed _).union ih

/-- A combinatorial sub-cell test.  Certificates use it rather than literal
list membership for a face: all our lists keep maximal tiles only.  Integer
endpoints make interval containment a decidable (and very cheap) test. -/
def subA (a b:At) : Prop := b.n ≤ a.n ∧ a.n + alen a ≤ b.n + alen b
instance (a b:At) : Decidable (subA a b) := by unfold subA; infer_instance
def subQ (a b:Q) : Prop := subA a.x b.x ∧ subA a.y b.y ∧ subA a.z b.z
instance (a b:Q) : Decidable (subQ a b) := by unfold subQ; infer_instance

lemma subA_sound {a b:At} (h:subA a b) : carrA a ⊆ carrA b := by
  rintro t ⟨l,u⟩
  change (lo b ≤ t ∧ t ≤ hi b)
  rw [hi_cast, lo_cast]
  rw [hi_cast] at u
  rw [lo_cast] at l
  constructor
  · have c : (b.n:ℝ) ≤ (a.n:ℝ) := by exact_mod_cast h.1
    exact c.trans l
  · have c : ((a.n + alen a:Nat):ℝ) ≤ ((b.n + alen b:Nat):ℝ) := by
      exact_mod_cast h.2
    exact u.trans c
lemma subQ_sound {a b:Q} (h:subQ a b) : ca a ⊆ ca b := by
  intro p hp
  rcases hp with ⟨hx,hy,hz⟩
  exact ⟨subA_sound h.1 hx, subA_sound h.2.1 hy, subA_sound h.2.2 hz⟩

def present (c:Q) (L:List Q) : Prop := ∃ q ∈ L, subQ c q
instance (c:Q) (L:List Q) : Decidable (present c L) := by
  unfold present; infer_instance
lemma present_mem {c:Q} {L:List Q} (h:present c L) {p:V}
    (hp:p∈ca c) : p∈cells L := by
  obtain ⟨q,hq,small⟩ := h
  exact ⟨q,hq, subQ_sound small hp⟩

def covered (m:Mov) (L:List Q) : Prop :=
  present (fac m.cube m.k (!m.upper)) L ∧
  match m.k with
  | .X =>
    (if m.cube.y.edge then (present (fac m.cube .Y false) L ∧ present (fac m.cube .Y true) L) else True) ∧
    (if m.cube.z.edge then (present (fac m.cube .Z false) L ∧ present (fac m.cube .Z true) L) else True)
  | .Y =>
    (if m.cube.x.edge then (present (fac m.cube .X false) L ∧ present (fac m.cube .X true) L) else True) ∧
    (if m.cube.z.edge then (present (fac m.cube .Z false) L ∧ present (fac m.cube .Z true) L) else True)
  | .Z =>
    (if m.cube.x.edge then (present (fac m.cube .X false) L ∧ present (fac m.cube .X true) L) else True) ∧
    (if m.cube.y.edge then (present (fac m.cube .Y false) L ∧ present (fac m.cube .Y true) L) else True)
instance (m:Mov) (L:List Q) : Decidable (covered m L) := by
 unfold covered
 cases m.k <;> dsimp <;> infer_instance

lemma covered_mem (m:Mov) (L:List Q)
 (hed:(qa m.cube m.k).edge = true) {p:V}
 (hp:p∈ca m.cube) (hg:good m p) (H:covered m L) : p∈cells L := by
  rcases m with ⟨⟨a,b,c⟩, k, side⟩
  rcases H with ⟨hn,hs⟩
  cases k
  · change a.edge = true at hed
    rcases hs with ⟨hy,hz⟩
    change (uu {x:=a,y:=b,z:=c} p .X = (if side then 0 else 1)) ∨
      (b.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .Y=0 ∨ uu {x:=a,y:=b,z:=c} p .Y=1)) ∨
      (c.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .Z=0 ∨ uu {x:=a,y:=b,z:=c} p .Z=1)) at hg
    rcases hg with t|t|t
    · apply present_mem (c:=fac {x:=a,y:=b,z:=c} .X (!side)) hn
      exact facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.X) hed hp
        (by cases side <;> simpa using t)
    · rcases t with ⟨eb,t|t⟩
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .Y false) L ∧ present (fac {x:=a,y:=b,z:=c} .Y true) L) := by simpa [eb] using hy
        exact present_mem Hside.1 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.Y) eb hp (by simpa using t))
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .Y false) L ∧ present (fac {x:=a,y:=b,z:=c} .Y true) L) := by simpa [eb] using hy
        exact present_mem Hside.2 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.Y) eb hp (by simpa using t))
    · rcases t with ⟨eb,t|t⟩
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .Z false) L ∧ present (fac {x:=a,y:=b,z:=c} .Z true) L) := by simpa [eb] using hz
        exact present_mem Hside.1 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.Z) eb hp (by simpa using t))
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .Z false) L ∧ present (fac {x:=a,y:=b,z:=c} .Z true) L) := by simpa [eb] using hz
        exact present_mem Hside.2 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.Z) eb hp (by simpa using t))
  · change b.edge = true at hed
    rcases hs with ⟨hx,hz⟩
    change (uu {x:=a,y:=b,z:=c} p .Y = (if side then 0 else 1)) ∨
      (a.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .X=0 ∨ uu {x:=a,y:=b,z:=c} p .X=1)) ∨
      (c.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .Z=0 ∨ uu {x:=a,y:=b,z:=c} p .Z=1)) at hg
    rcases hg with t|t|t
    · apply present_mem (c:=fac {x:=a,y:=b,z:=c} .Y (!side)) hn
      exact facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.Y) hed hp
        (by cases side <;> simpa using t)
    · rcases t with ⟨eb,t|t⟩
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .X false) L ∧ present (fac {x:=a,y:=b,z:=c} .X true) L) := by simpa [eb] using hx
        exact present_mem Hside.1 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.X) eb hp (by simpa using t))
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .X false) L ∧ present (fac {x:=a,y:=b,z:=c} .X true) L) := by simpa [eb] using hx
        exact present_mem Hside.2 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.X) eb hp (by simpa using t))
    · rcases t with ⟨eb,t|t⟩
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .Z false) L ∧ present (fac {x:=a,y:=b,z:=c} .Z true) L) := by simpa [eb] using hz
        exact present_mem Hside.1 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.Z) eb hp (by simpa using t))
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .Z false) L ∧ present (fac {x:=a,y:=b,z:=c} .Z true) L) := by simpa [eb] using hz
        exact present_mem Hside.2 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.Z) eb hp (by simpa using t))
  · change c.edge = true at hed
    rcases hs with ⟨hx,hy⟩
    change (uu {x:=a,y:=b,z:=c} p .Z = (if side then 0 else 1)) ∨
      (a.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .X=0 ∨ uu {x:=a,y:=b,z:=c} p .X=1)) ∨
      (b.edge = true ∧ (uu {x:=a,y:=b,z:=c} p .Y=0 ∨ uu {x:=a,y:=b,z:=c} p .Y=1)) at hg
    rcases hg with t|t|t
    · apply present_mem (c:=fac {x:=a,y:=b,z:=c} .Z (!side)) hn
      exact facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.Z) hed hp
        (by cases side <;> simpa using t)
    · rcases t with ⟨eb,t|t⟩
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .X false) L ∧ present (fac {x:=a,y:=b,z:=c} .X true) L) := by simpa [eb] using hx
        exact present_mem Hside.1 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.X) eb hp (by simpa using t))
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .X false) L ∧ present (fac {x:=a,y:=b,z:=c} .X true) L) := by simpa [eb] using hx
        exact present_mem Hside.2 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.X) eb hp (by simpa using t))
    · rcases t with ⟨eb,t|t⟩
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .Y false) L ∧ present (fac {x:=a,y:=b,z:=c} .Y true) L) := by simpa [eb] using hy
        exact present_mem Hside.1 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.Y) eb hp (by simpa using t))
      · have Hside : (present (fac {x:=a,y:=b,z:=c} .Y false) L ∧ present (fac {x:=a,y:=b,z:=c} .Y true) L) := by simpa [eb] using hy
        exact present_mem Hside.2 (facet_mem (c:={x:=a,y:=b,z:=c}) (i:=.Y) eb hp (by simpa using t))

lemma step_cells (m:Mov) (L:List Q)
 (hed:(qa m.cube m.k).edge=true)
 (hcov:covered m L)
 (hok : ∀ q ∈ L, okCell m q) :
 ∃ r : C(((ca m.cube ∪ cells L):Set V), (cells L:Set V)),
   ∀ x:(cells L:Set V), r ⟨x.1, Or.inr x.2⟩ = x := by
  apply collapse_patch m hed (cells L) (cells_closed L)
  · intro p hp hg
    exact covered_mem m L hed hp hg hcov
  · intro p hp hL
    rcases hL with ⟨q,hq,mem⟩
    exact okCell_good m q hed hp mem (hok q hq)

end
end HouseSupport

-- END INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Complex.lean

-- BEGIN INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Tower.lean
namespace HouseSupport
open Set
noncomputable section

-- append the cells of a list of moves to the residual complex
def tower : List Mov → List Q → List Q
 | [], L => L
 | m::s, L => m.cube :: tower s L

lemma cells_cons (q:Q) (L:List Q) : cells (q::L) = ca q ∪ cells L := by
 ext p; simp [cells]

def legal : List Mov → List Q → Prop
 | [], L => True
 | m::s, L =>
    (qa m.cube m.k).edge = true ∧
    covered m (tower s L) ∧
    (∀ q ∈ tower s L, okCell m q) ∧ legal s L
-- decidability, important: certificates can be checked by kernel computation on concrete lists
instance (s:List Mov) (L:List Q) : Decidable (legal s L) := by
 induction s with
 | nil => simp [legal]; infer_instance
 | cons m s ih =>
   unfold legal
   infer_instance


lemma sub_cons (q:Q) (L:List Q) : cells L ⊆ cells (q::L) := by
 rw [cells_cons]; exact subset_union_right
lemma sub_tower (s:List Mov) (L:List Q) : cells L ⊆ cells (tower s L) := by
 induction s with
 | nil => exact fun _ h => h
 | cons m s ih =>
   intro p hp
   exact sub_cons _ _ (ih hp)

lemma tower_retract (s:List Mov) (L:List Q) (H:legal s L) :
 ∃ r : C((cells (tower s L):Set V),(cells L:Set V)),
   ∀ x:(cells L:Set V), r ⟨x.1, sub_tower s L x.2⟩ = x := by
  induction s with
  | nil =>
    refine ⟨ContinuousMap.id _, ?_⟩
    intro x; rfl
  | cons m s ih =>
    rcases H with ⟨he,hc,ho,ht⟩
    obtain ⟨r1,hr1⟩ := step_cells m (tower s L) he hc ho
    obtain ⟨r2, hr2⟩ := ih ht
    -- replace the domain of the small step by the equal `cells (cube::tail)`.
    have eqn : cells (tower (m::s) L) = ca m.cube ∪ cells (tower s L) :=
      cells_cons _ _
    let rr0 : C((cells (tower (m::s) L):Set V),
                 ((ca m.cube ∪ cells (tower s L)):Set V)) :=
      ⟨(fun x => ⟨x.1, eqn ▸ x.2⟩), by
        exact continuous_subtype_val.subtype_mk _⟩
    let small : C((cells (tower (m::s) L):Set V),
                   (cells (tower s L):Set V)) := r1.comp rr0
    let rr : C((cells (tower (m::s) L):Set V),(cells L:Set V)) :=
       r2.comp small
    refine ⟨rr, ?_⟩
    intro x
    change r2 (r1 (rr0 ⟨x.1, sub_tower (m::s) L x.2⟩)) = x
    have a : rr0 ⟨x.1, sub_tower (m::s) L x.2⟩ =
        (⟨x.1, Or.inr (sub_tower s L x.2)⟩ : ((ca m.cube ∪ cells (tower s L)):Set V)) := by
      apply Subtype.ext
      rfl
    have b : r1 (rr0 ⟨x.1, sub_tower (m::s) L x.2⟩) =
         (⟨x.1, sub_tower s L x.2⟩ : (cells (tower s L):Set V)) :=
      calc
       _ = r1 (⟨x.1, Or.inr (sub_tower s L x.2)⟩ : ((ca m.cube ∪ cells (tower s L)):Set V)) := congrArg (fun t => r1 t) a
       _ = _ := hr1 (⟨x.1, sub_tower s L x.2⟩ : (cells (tower s L):Set V))
    rw [b]
    exact hr2 x

end
end HouseSupport

-- END INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Tower.lean

-- BEGIN INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Residual.lean
set_option maxHeartbeats 2000000
namespace HouseSupport
open Set
noncomputable section

def residual0 : List Q := [
    ⟨E 0, E 0, P 0⟩, ⟨E 0, E 1, P 0⟩, ⟨E 0, E 2, P 0⟩, ⟨E 1, E 0, P 0⟩ ,
    ⟨E 1, E 1, P 0⟩, ⟨E 1, E 2, P 0⟩, ⟨E 2, E 0, P 0⟩, ⟨E 2, E 2, P 0⟩ ,
    ⟨E 3, E 0, P 0⟩, ⟨E 3, E 1, P 0⟩, ⟨E 3, E 2, P 0⟩, ⟨E 0, E 0, P 1⟩ ,
    ⟨E 0, E 1, P 1⟩, ⟨E 0, E 2, P 1⟩, ⟨E 1, E 0, P 1⟩, ⟨E 1, E 2, P 1⟩ ,
    ⟨E 2, E 0, P 1⟩, ⟨E 2, E 2, P 1⟩, ⟨E 3, E 0, P 1⟩, ⟨E 3, E 1, P 1⟩ ,
    ⟨E 3, E 2, P 1⟩, ⟨E 0, E 0, P 2⟩, ⟨E 0, E 1, P 2⟩, ⟨E 0, E 2, P 2⟩ ,
    ⟨E 1, E 0, P 2⟩, ⟨E 1, E 2, P 2⟩, ⟨E 2, E 0, P 2⟩, ⟨E 2, E 1, P 2⟩ ,
    ⟨E 2, E 2, P 2⟩, ⟨E 3, E 0, P 2⟩, ⟨E 3, E 1, P 2⟩, ⟨E 3, E 2, P 2⟩ ,
    ⟨P 1, E 1, E 1⟩, ⟨P 2, E 1, E 0⟩, ⟨P 2, E 1, E 1⟩, ⟨P 2, E 2, E 0⟩ ,
    ⟨P 2, E 2, E 1⟩, ⟨P 3, E 1, E 0⟩, ⟨E 1, P 1, E 1⟩, ⟨E 1, P 2, E 1⟩ ,
    ⟨E 2, P 1, E 0⟩, ⟨E 2, P 2, E 0⟩, ⟨E 0, P 0, E 0⟩, ⟨E 0, P 0, E 1⟩ ,
    ⟨E 0, P 3, E 0⟩, ⟨E 0, P 3, E 1⟩, ⟨E 1, P 0, E 0⟩, ⟨E 1, P 0, E 1⟩ ,
    ⟨E 1, P 3, E 0⟩, ⟨E 1, P 3, E 1⟩, ⟨E 2, P 0, E 0⟩, ⟨E 2, P 0, E 1⟩ ,
    ⟨E 2, P 3, E 0⟩, ⟨E 2, P 3, E 1⟩, ⟨E 3, P 0, E 0⟩, ⟨E 3, P 0, E 1⟩ ,
    ⟨E 3, P 3, E 0⟩, ⟨E 3, P 3, E 1⟩, ⟨P 0, E 0, E 0⟩, ⟨P 0, E 0, E 1⟩ ,
    ⟨P 0, E 1, E 0⟩, ⟨P 0, E 1, E 1⟩, ⟨P 0, E 2, E 0⟩, ⟨P 0, E 2, E 1⟩ ,
    ⟨P 4, E 0, E 0⟩, ⟨P 4, E 0, E 1⟩, ⟨P 4, E 1, E 0⟩, ⟨P 4, E 1, E 1⟩ ,
    ⟨P 4, E 2, E 0⟩, ⟨P 4, E 2, E 1⟩, ⟨E 1, P 1, E 0⟩
  ]

lemma subtest : cells residual0 ⊆ panelR := by
  intro p h
  rcases p with ⟨x,y,z⟩
  simp [residual0, cells, ca, carrA, lo, hi, E, P] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 0 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 0 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 0 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 0 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 0 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 0 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 0 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 0 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 0 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 0 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 0 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 1 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 1 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 1 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 1 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 1 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 1 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 1 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 1 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 1 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 1 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inl ?_))
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    intros; linarith
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 2 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl ?_)
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by intros; linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 2 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl ?_)
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by intros; linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 2 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl ?_)
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by intros; linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 2 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl ?_)
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by intros; linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 2 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl ?_)
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by intros; linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 2 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl ?_)
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by intros; linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 2 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl ?_)
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by intros; linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 2 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl ?_)
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by intros; linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 2 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl ?_)
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by intros; linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 2 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl ?_)
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by intros; linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ze : z = 2 := by linarith
    subst z
    simp [panelR, panel, house]
    refine Or.inl (Or.inl ?_)
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by intros; linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 1 := by linarith
    subst x
    simp [panelR, panel, house]
    
    aesop
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 2 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ?_))))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 2 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ?_))))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 2 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ?_))))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 2 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ?_))))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 3 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ?_))))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 1 := by linarith
    subst y
    simp [panelR, panel, house]
    
    aesop
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 2 := by linarith
    subst y
    simp [panelR, panel, house]
    aesop
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 1 := by linarith
    subst y
    simp [panelR, panel, house]
    aesop
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 2 := by linarith
    subst y
    simp [panelR, panel, house]
    aesop
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 0 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 0 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 3 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 3 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 0 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 0 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 3 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 3 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 0 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 0 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 3 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 3 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 0 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 0 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 3 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 3 := by linarith
    subst y
    simp [panelR, panel, house]
    refine Or.inr (Or.inl ?_)
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 0 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 0 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 0 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 0 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 0 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 0 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 4 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 4 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 4 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 4 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 4 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have xe : x = 4 := by linarith
    subst x
    simp [panelR, panel, house]
    refine Or.inl (Or.inr (Or.inr ?_))
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rcases h with ⟨⟨hx,hy,hz⟩, hx',hy',hz'⟩
    norm_num at hx hy hz hx' hy' hz' ⊢
    have ye : y = 1 := by linarith
    subst y
    simp [panelR, panel, house]
    aesop

lemma panel_cells : panel ⊆ cells residual0 := by
  intro p hp
  rcases p with ⟨x,y,z⟩
  rcases hp with ⟨hx, hy, hz⟩
  have ye : y = 1 := by simpa using hy
  subst y
  refine ⟨⟨E 1, P 1, E 0⟩, ?_, ?_⟩
  · native_decide
  · rcases hx with ⟨hx,hx'⟩
    rcases hz with ⟨hz,hz'⟩
    exact ⟨⟨by simpa [carrA, lo, hi, E], by norm_num [carrA, lo, hi,E] at *; linarith⟩, by dsimp [carrA,lo,hi,P]; norm_num,
      ⟨by norm_num [carrA,lo,hi,E] at *; linarith, by norm_num [carrA,lo,hi,E] at *; linarith⟩⟩
end
end HouseSupport

-- END INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Residual.lean

-- BEGIN INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Incl.lean
namespace HouseSupport
open Set
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

-- convenient little pieces of the residual presentation.
private lemma sqmem (i j k : Nat) (h : ⟨E i, E j, P k⟩ ∈ residual0)
    {x y z : ℝ}
    (hx0 : (i:ℝ) ≤ x) (hx1 : x ≤ (i:ℝ)+1)
    (hy0 : (j:ℝ) ≤ y) (hy1 : y ≤ (j:ℝ)+1)
    (hz : z = (k:ℝ)) : ((x,(y,z)):V) ∈ cells residual0 := by
  refine ⟨⟨E i,E j,P k⟩, h, ?_⟩
  change (x ∈ carrA (E i) ∧ y ∈ carrA (E j) ∧ z ∈ carrA (P k))
  constructor
  · simpa [carrA, lo, hi, E] using And.intro hx0 hx1
  constructor
  · simpa [carrA, lo, hi, E] using And.intro hy0 hy1
  · subst z
    simp [carrA, lo, hi, P]

private lemma xemem (i j k : Nat) (h : ⟨P i, E j, E k⟩ ∈ residual0)
    {x y z : ℝ}
    (hx : x = (i:ℝ)) (hy0 : (j:ℝ) ≤ y) (hy1 : y ≤ (j:ℝ)+1)
    (hz0 : (k:ℝ) ≤ z) (hz1 : z ≤ (k:ℝ)+1) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  refine ⟨⟨P i, E j, E k⟩, h, ?_⟩
  change (x ∈ carrA (P i) ∧ y ∈ carrA (E j) ∧ z ∈ carrA (E k))
  constructor
  · subst x; simp [carrA,lo,hi,P]
  constructor
  · simpa [carrA,lo,hi,E] using And.intro hy0 hy1
  · simpa [carrA,lo,hi,E] using And.intro hz0 hz1

private lemma yemem (i j k : Nat) (h : ⟨E i, P j, E k⟩ ∈ residual0)
    {x y z : ℝ}
    (hx0 : (i:ℝ) ≤ x) (hx1 : x ≤ (i:ℝ)+1)
    (hy : y = (j:ℝ))
    (hz0 : (k:ℝ) ≤ z) (hz1 : z ≤ (k:ℝ)+1) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  refine ⟨⟨E i, P j, E k⟩, h, ?_⟩
  change (x ∈ carrA (E i) ∧ y ∈ carrA (P j) ∧ z ∈ carrA (E k))
  constructor
  · simpa [carrA,lo,hi,E] using And.intro hx0 hx1
  constructor
  · subst y; simp [carrA,lo,hi,P]
  · simpa [carrA,lo,hi,E] using And.intro hz0 hz1

lemma floor0_cells {x y : ℝ} (xa : 0 ≤ x) (xb : x ≤ 4)
    (ya : 0 ≤ y) (yb : y ≤ 3)
    (no : ¬ (x ∈ Ioo (2:ℝ) 3 ∧ y ∈ Ioo (1:ℝ) 2)) :
     ((x,(y,(0:ℝ))):V) ∈ cells residual0 := by
  norm_num at *
  by_cases x1 : x ≤ 1
  · by_cases y1 : y ≤ 1
    · exact sqmem 0 0 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith)
        (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases y2 : y < 2
      · exact sqmem 0 1 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · exact sqmem 0 2 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
  · by_cases x2 : x ≤ 2
    · by_cases y1 : y ≤ 1
      · exact sqmem 1 0 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y2 : y < 2
        · exact sqmem 1 1 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · exact sqmem 1 2 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases x3 : x < 3
      · -- the only absent square
        by_cases y1 : y ≤ 1
        · exact sqmem 2 0 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exfalso
            have t := no (by linarith) (by linarith) (by linarith); linarith
          · exact sqmem 2 2 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y1 : y ≤ 1
        · exact sqmem 3 0 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exact sqmem 3 1 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
          · exact sqmem 3 2 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith) (by norm_num)

lemma floor1_cells {x y : ℝ} (xa : 0 ≤ x) (xb : x ≤ 4)
    (ya : 0 ≤ y) (yb : y ≤ 3)
    (no : ¬ (x ∈ Ioo (1:ℝ) 3 ∧ y ∈ Ioo (1:ℝ) 2)) :
     ((x,(y,(1:ℝ))):V) ∈ cells residual0 := by
  norm_num at *
  by_cases x1 : x ≤ 1
  · by_cases y1 : y ≤ 1
    · exact sqmem 0 0 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases y2 : y < 2
      · exact sqmem 0 1 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · exact sqmem 0 2 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
  · by_cases x3 : x < 3
    · by_cases x2 : x ≤ 2
      · by_cases y1 : y ≤ 1
        · exact sqmem 1 0 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exfalso; have t := no (by linarith) (by linarith) (by linarith); linarith
          · exact sqmem 1 2 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y1 : y ≤ 1
        · exact sqmem 2 0 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exfalso; have t := no (by linarith) (by linarith) (by linarith); linarith
          · exact sqmem 2 2 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases y1 : y ≤ 1
      · exact sqmem 3 0 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y2 : y < 2
        · exact sqmem 3 1 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · exact sqmem 3 2 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)

lemma floor2_cells {x y : ℝ} (xa : 0 ≤ x) (xb : x ≤ 4)
    (ya : 0 ≤ y) (yb : y ≤ 3)
    (no : ¬ (x ∈ Ioo (1:ℝ) 2 ∧ y ∈ Ioo (1:ℝ) 2)) :
     ((x,(y,(2:ℝ))):V) ∈ cells residual0 := by
  norm_num at *
  by_cases x1 : x ≤ 1
  · by_cases y1 : y ≤ 1
    · exact sqmem 0 0 2 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases y2 : y < 2
      · exact sqmem 0 1 2 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · exact sqmem 0 2 2 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
  · by_cases x2 : x < 2
    · by_cases y1 : y ≤ 1
      · exact sqmem 1 0 2 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y2 : y < 2
        · exfalso
          have t := no (by linarith) (by linarith) (by linarith)
          linarith
        · exact sqmem 1 2 2 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases x3 : x ≤ 3
      · by_cases y1 : y ≤ 1
        · exact sqmem 2 0 2 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exact sqmem 2 1 2 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
          · exact sqmem 2 2 2 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y1 : y ≤ 1
        · exact sqmem 3 0 2 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exact sqmem 3 1 2 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
          · exact sqmem 3 2 2 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)

-- the brick intervals on a vertical point-x sheet which occur below
private lemma vx1 {x y z:ℝ} (xx:x=(1:ℝ)) (ya: (1:ℝ) ≤ y) (yb:y ≤ 2)
    (za:(1:ℝ) ≤ z) (zb:z ≤ 2) : ((x,(y,z)):V) ∈ cells residual0 := by
  exact xemem 1 1 1 (by native_decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith)
private lemma vx2 {x y z:ℝ} (xx:x=(2:ℝ)) (ya: (1:ℝ) ≤ y) (yb:y ≤ 3)
    (za:(0:ℝ) ≤ z) (zb:z ≤ 2) : ((x,(y,z)):V) ∈ cells residual0 := by
  by_cases yy : y ≤ 2 <;> by_cases zz : z ≤ 1
  · exact xemem 2 1 0 (by native_decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
  · exact xemem 2 1 1 (by native_decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
  · exact xemem 2 2 0 (by native_decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
  · exact xemem 2 2 1 (by native_decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
private lemma vx3 {x y z:ℝ} (xx:x=(3:ℝ)) (ya: (1:ℝ) ≤ y) (yb:y ≤ 2)
    (za:(0:ℝ) ≤ z) (zb:z ≤ 1) : ((x,(y,z)):V) ∈ cells residual0 := by
  exact xemem 3 1 0 (by native_decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)

private lemma vy12top {x y z:ℝ} (xa:(1:ℝ) ≤ x) (xb:x ≤ 2)
    (hy : y = 1 ∨ y = 2) (za:(1:ℝ) ≤ z) (zb:z ≤ 2) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  rcases hy with hh|hh
  · exact yemem 1 1 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
  · exact yemem 1 2 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
private lemma vy23low {x y z:ℝ} (xa:(2:ℝ) ≤ x) (xb:x ≤ 3)
    (hy : y = 1 ∨ y = 2) (za:(0:ℝ) ≤ z) (zb:z ≤ 1) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  rcases hy with hh|hh
  · exact yemem 2 1 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
  · exact yemem 2 2 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)

private lemma vboundary_y {x y z:ℝ} (xa:(0:ℝ) ≤ x) (xb:x ≤ 4)
    (hy : y = 0 ∨ y = 3) (za:(0:ℝ) ≤ z) (zb:z ≤ 2) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  rcases hy with hh|hh
  · by_cases x1:x ≤ 1
    · by_cases z1:z ≤ 1
      · exact yemem 0 0 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
      · exact yemem 0 0 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
    · by_cases x2:x ≤ 2
      · by_cases z1:z ≤ 1
        · exact yemem 1 0 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
        · exact yemem 1 0 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
      · by_cases x3:x ≤ 3
        · by_cases z1:z ≤ 1
          · exact yemem 2 0 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
          · exact yemem 2 0 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
        · by_cases z1:z ≤ 1
          · exact yemem 3 0 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
          · exact yemem 3 0 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
  · by_cases x1:x ≤ 1
    · by_cases z1:z ≤ 1
      · exact yemem 0 3 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
      · exact yemem 0 3 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
    · by_cases x2:x ≤ 2
      · by_cases z1:z ≤ 1
        · exact yemem 1 3 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
        · exact yemem 1 3 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
      · by_cases x3:x ≤ 3
        · by_cases z1:z ≤ 1
          · exact yemem 2 3 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
          · exact yemem 2 3 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
        · by_cases z1:z ≤ 1
          · exact yemem 3 3 0 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
          · exact yemem 3 3 1 (by native_decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)

private lemma vboundary_x {x y z:ℝ} (hx:x=0 ∨ x=4)
    (ya:(0:ℝ) ≤ y) (yb:y ≤ 3) (za:(0:ℝ) ≤ z) (zb:z ≤ 2) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  rcases hx with hh|hh
  · by_cases y1:y ≤ 1
    · by_cases z1:z ≤ 1
      · exact xemem 0 0 0 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
      · exact xemem 0 0 1 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    · by_cases y2:y ≤ 2
      · by_cases z1:z ≤ 1
        · exact xemem 0 1 0 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
        · exact xemem 0 1 1 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
      · by_cases z1:z ≤ 1
        · exact xemem 0 2 0 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
        · exact xemem 0 2 1 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
  · by_cases y1:y ≤ 1
    · by_cases z1:z ≤ 1
      · exact xemem 4 0 0 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
      · exact xemem 4 0 1 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    · by_cases y2:y ≤ 2
      · by_cases z1:z ≤ 1
        · exact xemem 4 1 0 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
        · exact xemem 4 1 1 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
      · by_cases z1:z ≤ 1
        · exact xemem 4 2 0 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
        · exact xemem 4 2 1 (by native_decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)


/-- Every closed tile of the residual list is present in the other direction as well.
Together with `subtest` this identifies the small list with the house and the small
extra panel.  This direction is best done with the rectangular membership
lemmas above: using `simp` on the house separates the horizontal sheets from the
five inside walls and the two outside walls. -/
lemma panelR_cells : panelR ⊆ cells residual0 := by
  intro p hp
  rcases hp with h | h
  · rcases p with ⟨x,y,z⟩
    change ((x,(y,z)):V) ∈ house at h
    simp [house] at h
    -- `simp` writes the two members of a pair-set as two disjuncts.  At the
    -- right outside wall that already splits `x=0,4`.
    rcases h with h | h | h | h
    · -- the floors, or one of the five walls in the middle
      rcases h with hf | hi
      · rcases hf with ⟨⟨⟨xa,xb⟩,⟨ya,yb⟩,hz⟩, hn01, hn2⟩
        rcases hn01 with ⟨hn0,hn1⟩
        rcases hz with hz | hz | hz
        · subst z
          -- stripping an open rectangle off a closed sheet only excludes its
          -- strict interior; the helpers take just this assertion.
          apply floor0_cells xa xb ya yb
          intro bad
          rcases bad with ⟨⟨u0,u1⟩,⟨v0,v1⟩⟩
          exact hn0 u0 u1 v0 v1 rfl
        · subst z
          apply floor1_cells xa xb ya yb
          intro bad
          rcases bad with ⟨⟨u0,u1⟩,⟨v0,v1⟩⟩
          exact hn1 u0 u1 v0 v1 rfl
        · subst z
          apply floor2_cells xa xb ya yb
          intro bad
          rcases bad with ⟨⟨u0,u1⟩,⟨v0,v1⟩⟩
          exact hn2 u0 u1 v0 v1 rfl
      · rcases hi with h | h
        · rcases h with h | h
          · rcases h with h | h
            · rcases h with h | h
              · -- x=1 upper room
                rcases h with ⟨xe, ⟨ya,za⟩, yb, zb⟩
                exact vx1 xe ya yb za zb
              · -- x=2 long middle sheet
                rcases h with ⟨xe, ⟨ya,za⟩, yb, zb⟩
                exact vx2 xe ya yb za zb
            · -- x=3 lower sheet
              rcases h with ⟨xe, ⟨ya,za⟩, yb, zb⟩
              exact vx3 xe ya yb za zb
          · rcases h with ⟨xa, hy, za, zb⟩
            exact vy12top xa.1 xa.2 hy za zb
        · rcases h with ⟨xa, hy, za, zb⟩
          exact vy23low xa.1 xa.2 hy za zb
    · rcases h with ⟨xa,hy,za,zb⟩
      exact vboundary_y xa.1 xa.2 hy za zb
    · obtain ⟨⟨ya,za⟩,yb,zb⟩ := ‹(0 ≤ y ∧ 0 ≤ z) ∧ y ≤ 3 ∧ z ≤ 2›
      exact vboundary_x (Or.inl h) ya yb za zb
    · obtain ⟨⟨ya,za⟩,yb,zb⟩ := ‹(0 ≤ y ∧ 0 ≤ z) ∧ y ≤ 3 ∧ z ≤ 2›
      exact vboundary_x (Or.inr h) ya yb za zb
  · exact panel_cells h

end
end HouseSupport

-- END INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Incl.lean

-- BEGIN INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Cert.lean
namespace HouseSupport
open Set
-- computational table
def moves0 : List Mov := [
  ⟨⟨E 1, E 1, E 1⟩, .Z, true⟩,
  ⟨⟨E 1, E 1, E 0⟩, .Z, true⟩,
  ⟨⟨E 0, E 1, E 0⟩, .X, true⟩,
  ⟨⟨E 0, E 0, E 0⟩, .Y, true⟩,
  ⟨⟨E 0, E 2, E 0⟩, .Y, false⟩,
  ⟨⟨E 1, E 0, E 0⟩, .X, false⟩,
  ⟨⟨E 1, E 2, E 0⟩, .X, false⟩,
  ⟨⟨E 2, E 0, E 0⟩, .X, false⟩,
  ⟨⟨E 2, E 1, E 0⟩, .Z, false⟩,
  ⟨⟨E 2, E 1, E 1⟩, .Z, false⟩,
  ⟨⟨E 2, E 0, E 1⟩, .Y, true⟩,
  ⟨⟨E 1, E 0, E 1⟩, .X, true⟩,
  ⟨⟨E 0, E 0, E 1⟩, .X, true⟩,
  ⟨⟨E 0, E 1, E 1⟩, .Y, false⟩,
  ⟨⟨E 0, E 2, E 1⟩, .Y, false⟩,
  ⟨⟨E 1, E 2, E 1⟩, .X, false⟩,
  ⟨⟨E 2, E 2, E 1⟩, .Y, false⟩,
  ⟨⟨E 3, E 0, E 0⟩, .X, false⟩,
  ⟨⟨E 3, E 0, E 1⟩, .X, false⟩,
  ⟨⟨E 3, E 1, E 0⟩, .Y, false⟩,
  ⟨⟨E 3, E 1, E 1⟩, .X, false⟩,
  ⟨⟨E 3, E 2, E 0⟩, .Y, false⟩,
  ⟨⟨E 2, E 2, E 0⟩, .X, true⟩,
  ⟨⟨E 3, E 2, E 1⟩, .X, false⟩,
  ⟨⟨E 1, P 2, E 0⟩, .X, false⟩,
  ⟨⟨E 3, P 1, E 1⟩, .X, false⟩,
  ⟨⟨E 3, P 2, E 1⟩, .X, false⟩]
set_option maxRecDepth 40000
set_option maxHeartbeats 20000000 in
lemma moves0_legal : legal moves0 residual0 := by
  decide
end HouseSupport
namespace HouseSupport
open Set
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 30000000

def boundedQ (q:Q) : Prop :=
  q.x.n + alen q.x ≤ 4 ∧ q.y.n + alen q.y ≤ 3 ∧ q.z.n + alen q.z ≤ 2
instance (q:Q) : Decidable (boundedQ q) := by unfold boundedQ; infer_instance

lemma tower_bounded : (tower moves0 residual0).Forall boundedQ := by
  decide
lemma ca_big {q:Q} (h:boundedQ q) : ca q ⊆ bigBox := by
 intro p hp
 rcases p with ⟨x,y,z⟩
 rcases hp with ⟨hx,hy,hz⟩
 change ( (0:ℝ) ≤ x ∧ x ≤ 4) ∧ ((0:ℝ) ≤ y ∧ y ≤ 3) ∧ ((0:ℝ) ≤ z ∧ z ≤ 2)
 dsimp [carrA] at hx hy hz
 rw [lo_cast, hi_cast] at hx hy hz
 rcases h with ⟨bx,byy,bz⟩
 constructor
 · constructor
   · exact le_trans (by norm_num) hx.1
   · exact le_trans hx.2 (by exact_mod_cast bx)
 constructor
 · constructor
   · exact le_trans (by norm_num) hy.1
   · exact le_trans hy.2 (by exact_mod_cast byy)
 · constructor
   · exact le_trans (by norm_num) hz.1
   · exact le_trans hz.2 (by exact_mod_cast bz)

lemma cells_big : cells (tower moves0 residual0) ⊆ bigBox := by
 intro p hp
 obtain ⟨q,hql,hpq⟩ := hp
 have extForall : ∀ (l:List Q), l.Forall boundedQ → ∀ a ∈ l, boundedQ a := by
   intro l
   induction l with
   | nil =>
     intro hh a ha
     simp at ha
   | cons b t ih =>
     intro hh a ha
     have hh' : boundedQ b ∧ t.Forall boundedQ := (List.forall_cons _ _ _).mp hh
     have ha' : a = b ∨ a ∈ t := (List.mem_cons.mp ha)
     rcases ha' with hab|hat
     · simpa [hab] using hh'.1
     · exact ih hh'.2 a hat
 exact ca_big (extForall _ tower_bounded q hql) hpq

private lemma cubemem (i j k:Nat)
    (h : ⟨E i,E j,E k⟩ ∈ tower moves0 residual0)
    {x y z:ℝ}
    (hx0:(i:ℝ) ≤ x) (hx1:x ≤ (i:ℝ)+1)
    (hy0:(j:ℝ) ≤ y) (hy1:y ≤ (j:ℝ)+1)
    (hz0:(k:ℝ) ≤ z) (hz1:z ≤ (k:ℝ)+1) :
    ((x,(y,z)):V) ∈ cells (tower moves0 residual0) := by
 refine ⟨⟨E i,E j,E k⟩, h, ?_⟩
 change (x ∈ carrA (E i) ∧ y ∈ carrA (E j) ∧ z ∈ carrA (E k))
 constructor
 · simpa [carrA, lo, hi, E] using And.intro hx0 hx1
 constructor
 · simpa [carrA, lo, hi, E] using And.intro hy0 hy1
 · simpa [carrA, lo, hi, E] using And.intro hz0 hz1

lemma big_cells : bigBox ⊆ cells (tower moves0 residual0) := by
 rintro ⟨x,y,z⟩ ⟨⟨x0,x4⟩,⟨y0,y3⟩,⟨z0,z2⟩⟩
 by_cases xx1 : x ≤ 1
 · by_cases yy1 : y ≤ 1
   · by_cases zz1 : z ≤ 1
     · exact cubemem 0 0 0 (by decide)
        (by norm_num; linarith) (by norm_num; linarith)
        (by norm_num; linarith) (by norm_num; linarith)
        (by norm_num; linarith) (by norm_num; linarith)
     · exact cubemem 0 0 1 (by decide)
        (by norm_num; linarith) (by norm_num; linarith)
        (by norm_num; linarith) (by norm_num; linarith)
        (by norm_num; linarith) (by norm_num; linarith)
   · by_cases yy2 : y ≤ 2
     · by_cases zz1 : z ≤ 1
       · exact cubemem 0 1 0 (by decide)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
       · exact cubemem 0 1 1 (by decide)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
     · by_cases zz1 : z ≤ 1
       · exact cubemem 0 2 0 (by decide)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
       · exact cubemem 0 2 1 (by decide)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
 · by_cases xx2 : x ≤ 2
   · by_cases yy1 : y ≤ 1
     · by_cases zz1 : z ≤ 1
       · exact cubemem 1 0 0 (by decide)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
       · exact cubemem 1 0 1 (by decide)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith)
     · by_cases yy2 : y ≤ 2
       · by_cases zz1 : z ≤ 1
         · exact cubemem 1 1 0 (by decide)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
         · exact cubemem 1 1 1 (by decide)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
       · by_cases zz1 : z ≤ 1
         · exact cubemem 1 2 0 (by decide)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
         · exact cubemem 1 2 1 (by decide)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
   · by_cases xx3 : x ≤ 3
     · by_cases yy1 : y ≤ 1
       · by_cases zz1 : z ≤ 1
         · exact cubemem 2 0 0 (by decide)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
         · exact cubemem 2 0 1 (by decide)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
       · by_cases yy2 : y ≤ 2
         · by_cases zz1 : z ≤ 1
           · exact cubemem 2 1 0 (by decide)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
           · exact cubemem 2 1 1 (by decide)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
         · by_cases zz1 : z ≤ 1
           · exact cubemem 2 2 0 (by decide)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
           · exact cubemem 2 2 1 (by decide)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
     · by_cases yy1 : y ≤ 1
       · by_cases zz1 : z ≤ 1
         · exact cubemem 3 0 0 (by decide)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
         · exact cubemem 3 0 1 (by decide)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith)
       · by_cases yy2 : y ≤ 2
         · by_cases zz1 : z ≤ 1
           · exact cubemem 3 1 0 (by decide)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
           · exact cubemem 3 1 1 (by decide)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
         · by_cases zz1 : z ≤ 1
           · exact cubemem 3 2 0 (by decide)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
           · exact cubemem 3 2 1 (by decide)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith)

lemma moves0_cells : cells (tower moves0 residual0) = bigBox :=
 Set.Subset.antisymm cells_big big_cells
end
end HouseSupport

-- END INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/Cert.lean

-- BEGIN INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/InclK.lean
namespace HouseSupport.K
open Set
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

-- convenient little pieces of the residual presentation.
private lemma sqmem (i j k : Nat) (h : ⟨E i, E j, P k⟩ ∈ residual0)
    {x y z : ℝ}
    (hx0 : (i:ℝ) ≤ x) (hx1 : x ≤ (i:ℝ)+1)
    (hy0 : (j:ℝ) ≤ y) (hy1 : y ≤ (j:ℝ)+1)
    (hz : z = (k:ℝ)) : ((x,(y,z)):V) ∈ cells residual0 := by
  refine ⟨⟨E i,E j,P k⟩, h, ?_⟩
  change (x ∈ carrA (E i) ∧ y ∈ carrA (E j) ∧ z ∈ carrA (P k))
  constructor
  · simpa [carrA, lo, hi, E] using And.intro hx0 hx1
  constructor
  · simpa [carrA, lo, hi, E] using And.intro hy0 hy1
  · subst z
    simp [carrA, lo, hi, P]

private lemma xemem (i j k : Nat) (h : ⟨P i, E j, E k⟩ ∈ residual0)
    {x y z : ℝ}
    (hx : x = (i:ℝ)) (hy0 : (j:ℝ) ≤ y) (hy1 : y ≤ (j:ℝ)+1)
    (hz0 : (k:ℝ) ≤ z) (hz1 : z ≤ (k:ℝ)+1) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  refine ⟨⟨P i, E j, E k⟩, h, ?_⟩
  change (x ∈ carrA (P i) ∧ y ∈ carrA (E j) ∧ z ∈ carrA (E k))
  constructor
  · subst x; simp [carrA,lo,hi,P]
  constructor
  · simpa [carrA,lo,hi,E] using And.intro hy0 hy1
  · simpa [carrA,lo,hi,E] using And.intro hz0 hz1

private lemma yemem (i j k : Nat) (h : ⟨E i, P j, E k⟩ ∈ residual0)
    {x y z : ℝ}
    (hx0 : (i:ℝ) ≤ x) (hx1 : x ≤ (i:ℝ)+1)
    (hy : y = (j:ℝ))
    (hz0 : (k:ℝ) ≤ z) (hz1 : z ≤ (k:ℝ)+1) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  refine ⟨⟨E i, P j, E k⟩, h, ?_⟩
  change (x ∈ carrA (E i) ∧ y ∈ carrA (P j) ∧ z ∈ carrA (E k))
  constructor
  · simpa [carrA,lo,hi,E] using And.intro hx0 hx1
  constructor
  · subst y; simp [carrA,lo,hi,P]
  · simpa [carrA,lo,hi,E] using And.intro hz0 hz1

lemma floor0_cells {x y : ℝ} (xa : 0 ≤ x) (xb : x ≤ 4)
    (ya : 0 ≤ y) (yb : y ≤ 3)
    (no : ¬ (x ∈ Ioo (2:ℝ) 3 ∧ y ∈ Ioo (1:ℝ) 2)) :
     ((x,(y,(0:ℝ))):V) ∈ cells residual0 := by
  norm_num at *
  by_cases x1 : x ≤ 1
  · by_cases y1 : y ≤ 1
    · exact sqmem 0 0 0 (by decide) (by norm_num; linarith) (by norm_num; linarith)
        (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases y2 : y < 2
      · exact sqmem 0 1 0 (by decide) (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · exact sqmem 0 2 0 (by decide) (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
  · by_cases x2 : x ≤ 2
    · by_cases y1 : y ≤ 1
      · exact sqmem 1 0 0 (by decide) (by norm_num; linarith) (by norm_num; linarith)
          (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y2 : y < 2
        · exact sqmem 1 1 0 (by decide) (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · exact sqmem 1 2 0 (by decide) (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases x3 : x < 3
      · -- the only absent square
        by_cases y1 : y ≤ 1
        · exact sqmem 2 0 0 (by decide) (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exfalso
            have t := no (by linarith) (by linarith) (by linarith); linarith
          · exact sqmem 2 2 0 (by decide) (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y1 : y ≤ 1
        · exact sqmem 3 0 0 (by decide) (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exact sqmem 3 1 0 (by decide) (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
          · exact sqmem 3 2 0 (by decide) (by norm_num; linarith) (by norm_num; linarith)
              (by norm_num; linarith) (by norm_num; linarith) (by norm_num)

lemma floor1_cells {x y : ℝ} (xa : 0 ≤ x) (xb : x ≤ 4)
    (ya : 0 ≤ y) (yb : y ≤ 3)
    (no : ¬ (x ∈ Ioo (1:ℝ) 3 ∧ y ∈ Ioo (1:ℝ) 2)) :
     ((x,(y,(1:ℝ))):V) ∈ cells residual0 := by
  norm_num at *
  by_cases x1 : x ≤ 1
  · by_cases y1 : y ≤ 1
    · exact sqmem 0 0 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases y2 : y < 2
      · exact sqmem 0 1 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · exact sqmem 0 2 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
  · by_cases x3 : x < 3
    · by_cases x2 : x ≤ 2
      · by_cases y1 : y ≤ 1
        · exact sqmem 1 0 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exfalso; have t := no (by linarith) (by linarith) (by linarith); linarith
          · exact sqmem 1 2 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y1 : y ≤ 1
        · exact sqmem 2 0 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exfalso; have t := no (by linarith) (by linarith) (by linarith); linarith
          · exact sqmem 2 2 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases y1 : y ≤ 1
      · exact sqmem 3 0 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y2 : y < 2
        · exact sqmem 3 1 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · exact sqmem 3 2 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)

lemma floor2_cells {x y : ℝ} (xa : 0 ≤ x) (xb : x ≤ 4)
    (ya : 0 ≤ y) (yb : y ≤ 3)
    (no : ¬ (x ∈ Ioo (1:ℝ) 2 ∧ y ∈ Ioo (1:ℝ) 2)) :
     ((x,(y,(2:ℝ))):V) ∈ cells residual0 := by
  norm_num at *
  by_cases x1 : x ≤ 1
  · by_cases y1 : y ≤ 1
    · exact sqmem 0 0 2 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases y2 : y < 2
      · exact sqmem 0 1 2 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · exact sqmem 0 2 2 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
  · by_cases x2 : x < 2
    · by_cases y1 : y ≤ 1
      · exact sqmem 1 0 2 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y2 : y < 2
        · exfalso
          have t := no (by linarith) (by linarith) (by linarith)
          linarith
        · exact sqmem 1 2 2 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
    · by_cases x3 : x ≤ 3
      · by_cases y1 : y ≤ 1
        · exact sqmem 2 0 2 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exact sqmem 2 1 2 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
          · exact sqmem 2 2 2 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
      · by_cases y1 : y ≤ 1
        · exact sqmem 3 0 2 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
        · by_cases y2 : y < 2
          · exact sqmem 3 1 2 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)
          · exact sqmem 3 2 2 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num)

-- the brick intervals on a vertical point-x sheet which occur below
private lemma vx1 {x y z:ℝ} (xx:x=(1:ℝ)) (ya: (1:ℝ) ≤ y) (yb:y ≤ 2)
    (za:(1:ℝ) ≤ z) (zb:z ≤ 2) : ((x,(y,z)):V) ∈ cells residual0 := by
  exact xemem 1 1 1 (by decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith)
private lemma vx2 {x y z:ℝ} (xx:x=(2:ℝ)) (ya: (1:ℝ) ≤ y) (yb:y ≤ 3)
    (za:(0:ℝ) ≤ z) (zb:z ≤ 2) : ((x,(y,z)):V) ∈ cells residual0 := by
  by_cases yy : y ≤ 2 <;> by_cases zz : z ≤ 1
  · exact xemem 2 1 0 (by decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
  · exact xemem 2 1 1 (by decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
  · exact xemem 2 2 0 (by decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
  · exact xemem 2 2 1 (by decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
private lemma vx3 {x y z:ℝ} (xx:x=(3:ℝ)) (ya: (1:ℝ) ≤ y) (yb:y ≤ 2)
    (za:(0:ℝ) ≤ z) (zb:z ≤ 1) : ((x,(y,z)):V) ∈ cells residual0 := by
  exact xemem 3 1 0 (by decide) (by norm_num; exact xx) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)

private lemma vy12top {x y z:ℝ} (xa:(1:ℝ) ≤ x) (xb:x ≤ 2)
    (hy : y = 1 ∨ y = 2) (za:(1:ℝ) ≤ z) (zb:z ≤ 2) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  rcases hy with hh|hh
  · exact yemem 1 1 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
  · exact yemem 1 2 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
private lemma vy23low {x y z:ℝ} (xa:(2:ℝ) ≤ x) (xb:x ≤ 3)
    (hy : y = 1 ∨ y = 2) (za:(0:ℝ) ≤ z) (zb:z ≤ 1) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  rcases hy with hh|hh
  · exact yemem 2 1 0 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
  · exact yemem 2 2 0 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)

private lemma vboundary_y {x y z:ℝ} (xa:(0:ℝ) ≤ x) (xb:x ≤ 4)
    (hy : y = 0 ∨ y = 3) (za:(0:ℝ) ≤ z) (zb:z ≤ 2) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  rcases hy with hh|hh
  · by_cases x1:x ≤ 1
    · by_cases z1:z ≤ 1
      · exact yemem 0 0 0 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
      · exact yemem 0 0 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
    · by_cases x2:x ≤ 2
      · by_cases z1:z ≤ 1
        · exact yemem 1 0 0 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
        · exact yemem 1 0 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
      · by_cases x3:x ≤ 3
        · by_cases z1:z ≤ 1
          · exact yemem 2 0 0 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
          · exact yemem 2 0 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
        · by_cases z1:z ≤ 1
          · exact yemem 3 0 0 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
          · exact yemem 3 0 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
  · by_cases x1:x ≤ 1
    · by_cases z1:z ≤ 1
      · exact yemem 0 3 0 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
      · exact yemem 0 3 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
    · by_cases x2:x ≤ 2
      · by_cases z1:z ≤ 1
        · exact yemem 1 3 0 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
        · exact yemem 1 3 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
      · by_cases x3:x ≤ 3
        · by_cases z1:z ≤ 1
          · exact yemem 2 3 0 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
          · exact yemem 2 3 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
        · by_cases z1:z ≤ 1
          · exact yemem 3 3 0 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)
          · exact yemem 3 3 1 (by decide) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith)

private lemma vboundary_x {x y z:ℝ} (hx:x=0 ∨ x=4)
    (ya:(0:ℝ) ≤ y) (yb:y ≤ 3) (za:(0:ℝ) ≤ z) (zb:z ≤ 2) :
    ((x,(y,z)):V) ∈ cells residual0 := by
  rcases hx with hh|hh
  · by_cases y1:y ≤ 1
    · by_cases z1:z ≤ 1
      · exact xemem 0 0 0 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
      · exact xemem 0 0 1 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    · by_cases y2:y ≤ 2
      · by_cases z1:z ≤ 1
        · exact xemem 0 1 0 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
        · exact xemem 0 1 1 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
      · by_cases z1:z ≤ 1
        · exact xemem 0 2 0 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
        · exact xemem 0 2 1 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
  · by_cases y1:y ≤ 1
    · by_cases z1:z ≤ 1
      · exact xemem 4 0 0 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
      · exact xemem 4 0 1 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    · by_cases y2:y ≤ 2
      · by_cases z1:z ≤ 1
        · exact xemem 4 1 0 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
        · exact xemem 4 1 1 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
      · by_cases z1:z ≤ 1
        · exact xemem 4 2 0 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
        · exact xemem 4 2 1 (by decide) (by norm_num; exact hh) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)


-- The small extra square is a single entry of the residual list; here and
-- in the finite tile tests below we use kernel reduction rather than native
-- reflection.
lemma panel_cells : panel ⊆ cells residual0 := by
  intro p hp
  rcases p with ⟨x,y,z⟩
  rcases hp with ⟨hx, hy, hz⟩
  have ye : y = 1 := by simpa using hy
  subst y
  refine ⟨⟨E 1, P 1, E 0⟩, ?_, ?_⟩
  · decide
  · rcases hx with ⟨hx,hx'⟩
    rcases hz with ⟨hz,hz'⟩
    exact ⟨⟨by simpa [carrA, lo, hi, E], by norm_num [carrA, lo, hi,E] at *; linarith⟩,
      by dsimp [carrA,lo,hi,P]; norm_num,
      ⟨by norm_num [carrA,lo,hi,E] at *; linarith,
       by norm_num [carrA,lo,hi,E] at *; linarith⟩⟩

/-- Every closed tile of the residual list is present in the other direction as well.
Together with `subtest` this identifies the small list with the house and the small
extra panel.  This direction is best done with the rectangular membership
lemmas above: using `simp` on the house separates the horizontal sheets from the
five inside walls and the two outside walls. -/
lemma panelR_cells : panelR ⊆ cells residual0 := by
  intro p hp
  rcases hp with h | h
  · rcases p with ⟨x,y,z⟩
    change ((x,(y,z)):V) ∈ house at h
    simp [house] at h
    -- `simp` writes the two members of a pair-set as two disjuncts.  At the
    -- right outside wall that already splits `x=0,4`.
    rcases h with h | h | h | h
    · -- the floors, or one of the five walls in the middle
      rcases h with hf | hi
      · rcases hf with ⟨⟨⟨xa,xb⟩,⟨ya,yb⟩,hz⟩, hn01, hn2⟩
        rcases hn01 with ⟨hn0,hn1⟩
        rcases hz with hz | hz | hz
        · subst z
          -- stripping an open rectangle off a closed sheet only excludes its
          -- strict interior; the helpers take just this assertion.
          apply floor0_cells xa xb ya yb
          intro bad
          rcases bad with ⟨⟨u0,u1⟩,⟨v0,v1⟩⟩
          exact hn0 u0 u1 v0 v1 rfl
        · subst z
          apply floor1_cells xa xb ya yb
          intro bad
          rcases bad with ⟨⟨u0,u1⟩,⟨v0,v1⟩⟩
          exact hn1 u0 u1 v0 v1 rfl
        · subst z
          apply floor2_cells xa xb ya yb
          intro bad
          rcases bad with ⟨⟨u0,u1⟩,⟨v0,v1⟩⟩
          exact hn2 u0 u1 v0 v1 rfl
      · rcases hi with h | h
        · rcases h with h | h
          · rcases h with h | h
            · rcases h with h | h
              · -- x=1 upper room
                rcases h with ⟨xe, ⟨ya,za⟩, yb, zb⟩
                exact vx1 xe ya yb za zb
              · -- x=2 long middle sheet
                rcases h with ⟨xe, ⟨ya,za⟩, yb, zb⟩
                exact vx2 xe ya yb za zb
            · -- x=3 lower sheet
              rcases h with ⟨xe, ⟨ya,za⟩, yb, zb⟩
              exact vx3 xe ya yb za zb
          · rcases h with ⟨xa, hy, za, zb⟩
            exact vy12top xa.1 xa.2 hy za zb
        · rcases h with ⟨xa, hy, za, zb⟩
          exact vy23low xa.1 xa.2 hy za zb
    · rcases h with ⟨xa,hy,za,zb⟩
      exact vboundary_y xa.1 xa.2 hy za zb
    · obtain ⟨⟨ya,za⟩,yb,zb⟩ := ‹(0 ≤ y ∧ 0 ≤ z) ∧ y ≤ 3 ∧ z ≤ 2›
      exact vboundary_x (Or.inl h) ya yb za zb
    · obtain ⟨⟨ya,za⟩,yb,zb⟩ := ‹(0 ≤ y ∧ 0 ≤ z) ∧ y ≤ 3 ∧ z ≤ 2›
      exact vboundary_x (Or.inr h) ya yb za zb
  · exact panel_cells h

end
end HouseSupport.K

-- END INLINED FILE: Mathlib/Support/contractibleSpace_houseWithTwoRooms_927aa5c8f8/InclK.lean

-- BEGIN INLINED FILE: Main.lean
open LeanEval.Topology
open Set (Icc Ioo)

namespace Submission

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem contractibleSpace_houseWithTwoRooms : ContractibleSpace HouseWithTwoRooms :=
/-ResultProofBegin-/by
  classical
  change ContractibleSpace HouseSupport.house
  have hsub : HouseSupport.house ⊆ HouseSupport.bigBox :=
    HouseSupport.house_subset_bigBox
  have hHP : HouseSupport.house ⊆ HouseSupport.panelR := fun p hp => Or.inl hp
  have hPB : HouseSupport.panelR ⊆ HouseSupport.bigBox := by
    intro p hp
    rcases hp with hp | hp
    · exact hsub hp
    · exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
        ⟨by
           have hh : p.2.1 = 1 := by simpa using hp.2.1
           linarith,
         by
           have hh : p.2.1 = 1 := by simpa using hp.2.1
           linarith⟩,
        ⟨by linarith [hp.2.2.1], by linarith [hp.2.2.2]⟩⟩
  -- The remaining three-dimensional part is the cubical sweep. At its end
  -- only the displayed lower panel is present; the planar horn is proved in
  -- `Tail` independently of the sweep.
  obtain ⟨rp, hp⟩ :
      ∃ r : C((HouseSupport.bigBox:Set (ℝ × ℝ × ℝ)),
              (HouseSupport.panelR:Set (ℝ × ℝ × ℝ))),
        ∀ x : (HouseSupport.panelR:Set (ℝ × ℝ × ℝ)),
          r ⟨x.1, hPB x.2⟩ = x := by
    -- It is enough to supply the (entirely finite) collapse table.  `Tower`
    -- proves the gluing, including the lower-dimensional cells of the sweep.
    obtain ⟨moves, residual, hleg, hfirst, hlast⟩ :
        ∃ (moves : List HouseSupport.Mov) (residual : List HouseSupport.Q),
          HouseSupport.legal moves residual ∧
          HouseSupport.cells (HouseSupport.tower moves residual) = HouseSupport.bigBox ∧
          HouseSupport.cells residual = HouseSupport.panelR := by
      -- The bottom carrier has a particularly small cubical presentation.  We
      -- fix it now, rather than leaving both ends of the table unspecified.
      -- `subtest` proves the difficult "no extra open square" direction by
      -- checking every one of its seventy-one cells.  What is left for the
      -- table is its converse, together with the moves.
      have hsmall := HouseSupport.subtest
      suffices H : ∃ moves : List HouseSupport.Mov,
          HouseSupport.legal moves HouseSupport.residual0 ∧
          HouseSupport.cells (HouseSupport.tower moves HouseSupport.residual0)
            = HouseSupport.bigBox ∧
          HouseSupport.panelR ⊆ HouseSupport.cells HouseSupport.residual0 by
        rcases H with ⟨ms, ok, top, bot⟩
        exact ⟨ms, HouseSupport.residual0, ok, top,
          Set.Subset.antisymm hsmall bot⟩
      -- the point-panel (one of the vertical tiles) is already in the
      -- closed carrier.  The three substantially larger horizontal levels can
      -- now be discharged by `floor0_cells`, `floor1_cells`, `floor2_cells`:
      -- these are handy endpoint-sensitive versions (at 2 and 3 one must use
      -- the tile on the other side of the deleted open square).
      have lower_panel : HouseSupport.panel ⊆
          HouseSupport.cells HouseSupport.residual0 := HouseSupport.K.panel_cells
      -- The sweep consists of the twenty four boxes and three exposed squares.
      -- `moves0` records the elementary cubical pairs in their removal
      -- order.  Its certificate is completely finite (`legal` is the
      -- decidable face/sub-face test); the carrier equality just subdivides
      -- each of the three intervals into its integer unit intervals.
      exact ⟨HouseSupport.moves0, HouseSupport.moves0_legal,
        HouseSupport.moves0_cells, HouseSupport.K.panelR_cells⟩
    obtain ⟨rr, hrr⟩ := HouseSupport.tower_retract moves residual hleg
    -- change source and target along the two carrier equalities
    let to0 : C((HouseSupport.bigBox:Set (ℝ × ℝ × ℝ)),
                 (HouseSupport.cells (HouseSupport.tower moves residual):Set (ℝ × ℝ × ℝ))) :=
       ⟨(fun x => ⟨x.1, hfirst.symm ▸ x.2⟩), by exact continuous_subtype_val.subtype_mk _⟩
    let out : C((HouseSupport.cells residual:Set (ℝ × ℝ × ℝ)),
                 (HouseSupport.panelR:Set (ℝ × ℝ × ℝ))) :=
       ⟨(fun x => ⟨x.1, hlast ▸ x.2⟩), by exact continuous_subtype_val.subtype_mk _⟩
    let R : C((HouseSupport.bigBox:Set (ℝ × ℝ × ℝ)),
                (HouseSupport.panelR:Set (ℝ × ℝ × ℝ))) := out.comp (rr.comp to0)
    refine ⟨R, ?_⟩
    intro x
    apply Subtype.ext
    -- the intermediate point is the same residual point, independently of
    -- the proof of membership used in the subtypes
    let xr : (HouseSupport.cells residual:Set (ℝ × ℝ × ℝ)) :=
       ⟨x.1, hlast.symm ▸ x.2⟩
    change (out (rr (to0 ⟨x.1, hPB x.2⟩)) : (HouseSupport.panelR:Set (ℝ × ℝ × ℝ))).1 = x.1
    have a : to0 ⟨x.1, hPB x.2⟩ =
       ⟨xr.1, HouseSupport.sub_tower moves residual xr.2⟩ := by
       apply Subtype.ext
       rfl
    rw [a, hrr xr]
    rfl

  obtain ⟨rt, ht⟩ := HouseSupport.panel_retraction
  let r : C((HouseSupport.bigBox:Set (ℝ × ℝ × ℝ)),
             (HouseSupport.house:Set (ℝ × ℝ × ℝ))) := rt.comp rp
  apply HouseSupport.contractible_of_retract_of_convex
      HouseSupport.convex_bigBox HouseSupport.nonempty_bigBox hsub r
  intro x
  change rt (rp ⟨x.1, hsub x.2⟩) = x
  rw [hp ⟨x.1, Or.inl x.2⟩]
  exact ht x
/-ResultProofEnd-/
/-ResultEnd-/

end Submission

-- END INLINED FILE: Main.lean
