import ChallengeDeps

namespace Submission.Helpers

open LeanEval.Topology
open Set
open unitInterval

noncomputable section

abbrev Point := ℝ × ℝ × ℝ

inductive Face
  | xNeg
  | xPos
  | yNeg
  | yPos
  | zNeg
  | zPos

structure Cell where
  x : ℝ
  y : ℝ
  z : ℝ
  face : Face

def Cell.set (c : Cell) : Set Point :=
  Icc c.x (c.x + 1) ×ˢ Icc c.y (c.y + 1) ×ˢ Icc c.z (c.z + 1)

def stdCube : Set Point := Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1

def toStd (c : Cell) (p : Point) : Point :=
  match c.face with
  | .xNeg => (p.1 - c.x, p.2.1 - c.y, p.2.2 - c.z)
  | .xPos => (c.x + 1 - p.1, p.2.1 - c.y, p.2.2 - c.z)
  | .yNeg => (p.2.1 - c.y, p.1 - c.x, p.2.2 - c.z)
  | .yPos => (c.y + 1 - p.2.1, p.1 - c.x, p.2.2 - c.z)
  | .zNeg => (p.2.2 - c.z, p.1 - c.x, p.2.1 - c.y)
  | .zPos => (c.z + 1 - p.2.2, p.1 - c.x, p.2.1 - c.y)

def fromStd (c : Cell) (p : Point) : Point :=
  match c.face with
  | .xNeg => (c.x + p.1, c.y + p.2.1, c.z + p.2.2)
  | .xPos => (c.x + 1 - p.1, c.y + p.2.1, c.z + p.2.2)
  | .yNeg => (c.x + p.2.1, c.y + p.1, c.z + p.2.2)
  | .yPos => (c.x + p.2.1, c.y + 1 - p.1, c.z + p.2.2)
  | .zNeg => (c.x + p.2.1, c.y + p.2.2, c.z + p.1)
  | .zPos => (c.x + p.2.1, c.y + p.2.2, c.z + 1 - p.1)

lemma fromStd_toStd (c : Cell) (p : Point) : fromStd c (toStd c p) = p := by
  rcases c with ⟨cx, cy, cz, f⟩
  rcases p with ⟨x, y, z⟩
  cases f <;> simp [fromStd, toStd]

lemma toStd_fromStd (c : Cell) (p : Point) : toStd c (fromStd c p) = p := by
  rcases c with ⟨cx, cy, cz, f⟩
  rcases p with ⟨x, y, z⟩
  cases f <;> simp [fromStd, toStd]

lemma continuous_toStd (c : Cell) : Continuous (toStd c) := by
  rcases c with ⟨cx, cy, cz, f⟩
  unfold toStd
  cases f <;> fun_prop

lemma continuous_fromStd (c : Cell) : Continuous (fromStd c) := by
  rcases c with ⟨cx, cy, cz, f⟩
  unfold fromStd
  cases f <;> fun_prop

lemma toStd_mem {c : Cell} {p : Point} (hp : p ∈ c.set) : toStd c p ∈ stdCube := by
  rcases c with ⟨cx, cy, cz, f⟩
  rcases p with ⟨x, y, z⟩
  simp only [Cell.set, Set.mem_prod, Set.mem_Icc] at hp
  rcases hp with ⟨⟨hx0, hx1⟩, ⟨⟨hy0, hy1⟩, hz0, hz1⟩⟩
  cases f <;> simp only [toStd, stdCube, Set.mem_prod, Set.mem_Icc]
  all_goals
    constructor
    · constructor <;> linarith
    · constructor
      · constructor <;> linarith
      · constructor <;> linarith

lemma fromStd_mem {c : Cell} {p : Point} (hp : p ∈ stdCube) : fromStd c p ∈ c.set := by
  rcases c with ⟨cx, cy, cz, f⟩
  rcases p with ⟨x, y, z⟩
  simp only [stdCube, Set.mem_prod, Set.mem_Icc] at hp
  rcases hp with ⟨⟨hx0, hx1⟩, ⟨⟨hy0, hy1⟩, hz0, hz1⟩⟩
  cases f <;> simp only [fromStd, Cell.set, Set.mem_prod, Set.mem_Icc]
  all_goals
    constructor
    · constructor <;> linarith
    · constructor
      · constructor <;> linarith
      · constructor <;> linarith

def stdDenom (p : Point) : ℝ :=
  max (1 / 2) <|
    max ((p.1 + 1) / 2) <|
      max (2 * |p.2.1 - 1 / 2|) (2 * |p.2.2 - 1 / 2|)

def stdCollapse (p : Point) : Point :=
  (-1 + (p.1 + 1) / stdDenom p,
    1 / 2 + (p.2.1 - 1 / 2) / stdDenom p,
    1 / 2 + (p.2.2 - 1 / 2) / stdDenom p)

lemma stdDenom_pos (p : Point) : 0 < stdDenom p :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

lemma stdDenom_le_one {p : Point} (hp : p ∈ stdCube) : stdDenom p ≤ 1 := by
  rcases hp with ⟨⟨hx0, hx1⟩, ⟨⟨hy0, hy1⟩, hz0, hz1⟩⟩
  simp only [stdDenom, max_le_iff]
  refine ⟨by norm_num, by linarith, ?_, ?_⟩
  · have : |p.2.1 - 1 / 2| ≤ 1 / 2 := (abs_le).2 ⟨by linarith, by linarith⟩
    linarith
  · have : |p.2.2 - 1 / 2| ≤ 1 / 2 := (abs_le).2 ⟨by linarith, by linarith⟩
    linarith

lemma xTerm_le_stdDenom (p : Point) : (p.1 + 1) / 2 ≤ stdDenom p :=
  le_trans (le_max_left _ _) (le_max_right _ _)

lemma yTerm_le_stdDenom (p : Point) : 2 * |p.2.1 - 1 / 2| ≤ stdDenom p :=
  le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

lemma zTerm_le_stdDenom (p : Point) : 2 * |p.2.2 - 1 / 2| ≤ stdDenom p :=
  le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

lemma continuous_stdDenom : Continuous stdDenom := by
  unfold stdDenom
  fun_prop

lemma continuous_stdCollapse : Continuous stdCollapse := by
  have hx : Continuous fun p : Point => p.1 := continuous_fst
  have hy : Continuous fun p : Point => p.2.1 := continuous_fst.comp continuous_snd
  have hz : Continuous fun p : Point => p.2.2 := continuous_snd.comp continuous_snd
  have hn : ∀ p : Point, stdDenom p ≠ 0 := fun p => ne_of_gt (stdDenom_pos p)
  have h₁ : Continuous fun p : Point => -1 + (p.1 + 1) / stdDenom p :=
    continuous_const.add ((hx.add continuous_const).div continuous_stdDenom hn)
  have h₂ : Continuous fun p : Point => 1 / 2 + (p.2.1 - 1 / 2) / stdDenom p :=
    continuous_const.add ((hy.sub continuous_const).div continuous_stdDenom hn)
  have h₃ : Continuous fun p : Point => 1 / 2 + (p.2.2 - 1 / 2) / stdDenom p :=
    continuous_const.add ((hz.sub continuous_const).div continuous_stdDenom hn)
  exact h₁.prodMk (h₂.prodMk h₃)

lemma stdCollapse_mem_cube {p : Point} (hp : p ∈ stdCube) : stdCollapse p ∈ stdCube := by
  rcases hp with ⟨⟨hx0, hx1⟩, ⟨⟨hy0, hy1⟩, hz0, hz1⟩⟩
  have hd0 := stdDenom_pos p
  have hd1 := stdDenom_le_one (p := p) ⟨⟨hx0, hx1⟩, ⟨⟨hy0, hy1⟩, hz0, hz1⟩⟩
  have hxt := xTerm_le_stdDenom p
  have hyt := yTerm_le_stdDenom p
  have hzt := zTerm_le_stdDenom p
  have hxl : 1 ≤ (p.1 + 1) / stdDenom p := by
    rw [le_div_iff₀ hd0]
    linarith
  have hxu : (p.1 + 1) / stdDenom p ≤ 2 := by
    rw [div_le_iff₀ hd0]
    linarith
  have hyl : -(1 / 2 : ℝ) ≤ (p.2.1 - 1 / 2) / stdDenom p := by
    rw [le_div_iff₀ hd0]
    have ha : -(stdDenom p / 2) ≤ p.2.1 - 1 / 2 := by
      have := abs_le.mp (show |p.2.1 - 1 / 2| ≤ stdDenom p / 2 by linarith)
      linarith
    linarith
  have hyu : (p.2.1 - 1 / 2) / stdDenom p ≤ 1 / 2 := by
    rw [div_le_iff₀ hd0]
    have ha : p.2.1 - 1 / 2 ≤ stdDenom p / 2 := by
      have := abs_le.mp (show |p.2.1 - 1 / 2| ≤ stdDenom p / 2 by linarith)
      linarith
    linarith
  have hzl : -(1 / 2 : ℝ) ≤ (p.2.2 - 1 / 2) / stdDenom p := by
    rw [le_div_iff₀ hd0]
    have ha : -(stdDenom p / 2) ≤ p.2.2 - 1 / 2 := by
      have := abs_le.mp (show |p.2.2 - 1 / 2| ≤ stdDenom p / 2 by linarith)
      linarith
    linarith
  have hzu : (p.2.2 - 1 / 2) / stdDenom p ≤ 1 / 2 := by
    rw [div_le_iff₀ hd0]
    have ha : p.2.2 - 1 / 2 ≤ stdDenom p / 2 := by
      have := abs_le.mp (show |p.2.2 - 1 / 2| ≤ stdDenom p / 2 by linarith)
      linarith
    linarith
  exact
    ⟨⟨by simp [stdCollapse]; linarith, by simp [stdCollapse]; linarith⟩,
      ⟨⟨by simp [stdCollapse]; linarith, by simp [stdCollapse]; linarith⟩,
        by simp [stdCollapse]; constructor <;> linarith⟩⟩

def stdBoundary (p : Point) : Prop :=
  p.1 = 1 ∨ p.2.1 = 0 ∨ p.2.1 = 1 ∨ p.2.2 = 0 ∨ p.2.2 = 1

def stdHorn : Set Point := {p | p ∈ stdCube ∧ stdBoundary p}

lemma stdCollapse_boundary {p : Point} (hp : p ∈ stdCube) : stdBoundary (stdCollapse p) := by
  rcases hp with ⟨⟨hx0, hx1⟩, ⟨⟨hy0, hy1⟩, hz0, hz1⟩⟩
  have hd0 := stdDenom_pos p
  rcases max_choice (1 / 2 : ℝ)
      (max ((p.1 + 1) / 2)
        (max (2 * |p.2.1 - 1 / 2|) (2 * |p.2.2 - 1 / 2|))) with hhalf | hrest
  · left
    have hd : stdDenom p = 1 / 2 := by simpa [stdDenom] using hhalf
    have hx : p.1 = 0 := by
      have := xTerm_le_stdDenom p
      linarith
    simp [stdCollapse, hd, hx]
    norm_num
  · rcases max_choice ((p.1 + 1) / 2)
        (max (2 * |p.2.1 - 1 / 2|) (2 * |p.2.2 - 1 / 2|)) with hx | hyz
    · left
      have hd : stdDenom p = (p.1 + 1) / 2 := by rw [stdDenom, hrest, hx]
      simp only [stdCollapse, hd]
      field_simp
      linarith
    · rcases max_choice (2 * |p.2.1 - 1 / 2|) (2 * |p.2.2 - 1 / 2|) with hy | hz
      · have hd : stdDenom p = 2 * |p.2.1 - 1 / 2| := by
          rw [stdDenom, hrest, hyz, hy]
        have habs : |p.2.1 - 1 / 2| = stdDenom p / 2 := by linarith
        rcases (abs_eq (by positivity : (0 : ℝ) ≤ stdDenom p / 2)).mp habs with ha | ha
        · right; right; left
          change 1 / 2 + (p.2.1 - 1 / 2) / stdDenom p = 1
          field_simp
          linarith
        · right; left
          change 1 / 2 + (p.2.1 - 1 / 2) / stdDenom p = 0
          field_simp
          linarith
      · have hd : stdDenom p = 2 * |p.2.2 - 1 / 2| := by
          rw [stdDenom, hrest, hyz, hz]
        have habs : |p.2.2 - 1 / 2| = stdDenom p / 2 := by linarith
        rcases (abs_eq (by positivity : (0 : ℝ) ≤ stdDenom p / 2)).mp habs with ha | ha
        · right; right; right; right
          change 1 / 2 + (p.2.2 - 1 / 2) / stdDenom p = 1
          field_simp
          linarith
        · right; right; right; left
          change 1 / 2 + (p.2.2 - 1 / 2) / stdDenom p = 0
          field_simp
          linarith

lemma stdCollapse_mem_horn {p : Point} (hp : p ∈ stdCube) : stdCollapse p ∈ stdHorn :=
  ⟨stdCollapse_mem_cube hp, stdCollapse_boundary hp⟩

lemma stdCollapse_eq_self {p : Point} (hp : p ∈ stdCube) (h : stdBoundary p) :
    stdCollapse p = p := by
  rcases p with ⟨x, y, z⟩
  have hdle := stdDenom_le_one hp
  rcases h with hx | hy | hy | hz | hz
  · have hd : stdDenom (x, y, z) = 1 := by
      have := xTerm_le_stdDenom (x, y, z)
      linarith
    simp [stdCollapse, hd]
  · have hd : stdDenom (x, y, z) = 1 := by
      have := yTerm_le_stdDenom (x, y, z)
      rw [hy] at this
      norm_num at this ⊢
      linarith
    simp [stdCollapse, hd]
  · have hd : stdDenom (x, y, z) = 1 := by
      have := yTerm_le_stdDenom (x, y, z)
      rw [hy] at this
      norm_num at this ⊢
      linarith
    simp [stdCollapse, hd]
  · have hd : stdDenom (x, y, z) = 1 := by
      have := zTerm_le_stdDenom (x, y, z)
      rw [hz] at this
      norm_num at this ⊢
      linarith
    simp [stdCollapse, hd]
  · have hd : stdDenom (x, y, z) = 1 := by
      have := zTerm_le_stdDenom (x, y, z)
      rw [hz] at this
      norm_num at this ⊢
      linarith
    simp [stdCollapse, hd]

def Cell.horn (c : Cell) : Set Point := toStd c ⁻¹' stdHorn

def cellCollapse (c : Cell) (p : Point) : Point :=
  fromStd c (stdCollapse (toStd c p))

lemma Cell.isClosed_set (c : Cell) : IsClosed c.set :=
  isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)

lemma continuous_cellCollapse (c : Cell) : Continuous (cellCollapse c) :=
  (continuous_fromStd c).comp (continuous_stdCollapse.comp (continuous_toStd c))

lemma cellCollapse_mem_horn {c : Cell} {p : Point} (hp : p ∈ c.set) :
    cellCollapse c p ∈ c.horn := by
  change toStd c (fromStd c (stdCollapse (toStd c p))) ∈ stdHorn
  rw [toStd_fromStd]
  exact stdCollapse_mem_horn (toStd_mem hp)

lemma cellCollapse_eq_self {c : Cell} {p : Point} (hp : p ∈ c.horn) :
    cellCollapse c p = p := by
  unfold cellCollapse
  rw [stdCollapse_eq_self hp.1 hp.2, fromStd_toStd]

def ValidStep (c : Cell) (s : Set Point) : Prop :=
  c.horn ⊆ s ∧ c.set ∩ s ⊆ c.horn

noncomputable def collapseAmbient (c : Cell) : Point → Point := by
  classical
  exact c.set.piecewise (cellCollapse c) id

lemma collapseAmbient_mem {c : Cell} {s : Set Point} (h : ValidStep c s) {p : Point}
    (hp : p ∈ c.set ∪ s) : collapseAmbient c p ∈ s := by
  classical
  by_cases hc : p ∈ c.set
  · simpa [collapseAmbient, hc] using h.1 (cellCollapse_mem_horn hc)
  · simpa [collapseAmbient, hc] using hp.resolve_left hc

lemma collapseAmbient_eq_self {c : Cell} {s : Set Point} (h : ValidStep c s) {p : Point}
    (hp : p ∈ s) : collapseAmbient c p = p := by
  classical
  by_cases hc : p ∈ c.set
  · have hh : p ∈ c.horn := h.2 ⟨hc, hp⟩
    simp [collapseAmbient, hc, cellCollapse_eq_self hh]
  · simp [collapseAmbient, hc]

lemma continuousOn_collapseAmbient {c : Cell} {s : Set Point} (h : ValidStep c s)
    (hs : IsClosed s) : ContinuousOn (collapseAmbient c) (c.set ∪ s) := by
  classical
  have hc : ContinuousOn (collapseAmbient c) c.set :=
    (continuous_cellCollapse c).continuousOn.congr fun p hp => by
      simp [collapseAmbient, hp]
  have hs' : ContinuousOn (collapseAmbient c) s :=
    continuous_id.continuousOn.congr fun p hp => collapseAmbient_eq_self h hp
  exact hc.union_of_isClosed hs' c.isClosed_set hs

def collapseMap (c : Cell) (s : Set Point) (h : ValidStep c s) (hs : IsClosed s) :
    ContinuousMap {p : Point // p ∈ c.set ∪ s} {p : Point // p ∈ s} :=
  ⟨fun p => ⟨collapseAmbient c p, collapseAmbient_mem h p.2⟩,
    (continuousOn_iff_continuous_restrict.mp (continuousOn_collapseAmbient h hs)).subtype_mk _⟩

lemma collapseMap_eq_self (c : Cell) (s : Set Point) (h : ValidStep c s) (hs : IsClosed s)
    (p : s) : collapseMap c s h hs ⟨p, Or.inr p.2⟩ = p := by
  apply Subtype.ext
  exact collapseAmbient_eq_self h p.2

def floor0 : Set Point :=
  (Icc 0 4 ×ˢ Icc 0 3 ×ˢ ({0} : Set ℝ)) \
    (Ioo 2 3 ×ˢ Ioo 1 2 ×ˢ (Set.univ : Set ℝ))

def floor1 : Set Point :=
  (Icc 0 4 ×ˢ Icc 0 3 ×ˢ ({1} : Set ℝ)) \
    (Ioo 1 3 ×ˢ Ioo 1 2 ×ˢ (Set.univ : Set ℝ))

def floor2 : Set Point :=
  (Icc 0 4 ×ˢ Icc 0 3 ×ˢ ({2} : Set ℝ)) \
    (Ioo 1 2 ×ˢ Ioo 1 2 ×ˢ (Set.univ : Set ℝ))

lemma isClosed_houseWithTwoRooms : IsClosed HouseWithTwoRooms := by
  have hf0 : IsClosed floor0 :=
    (isClosed_Icc.prod (isClosed_Icc.prod isClosed_singleton)).sdiff
      (isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_univ))
  have hf1 : IsClosed floor1 :=
    (isClosed_Icc.prod (isClosed_Icc.prod isClosed_singleton)).sdiff
      (isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_univ))
  have hf2 : IsClosed floor2 :=
    (isClosed_Icc.prod (isClosed_Icc.prod isClosed_singleton)).sdiff
      (isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_univ))
  rw [show HouseWithTwoRooms = (floor0 ∪ floor1 ∪ floor2) ∪
      ({1} ×ˢ Icc 1 2 ×ˢ Icc 1 2 ∪ {2} ×ˢ Icc 1 3 ×ˢ Icc 0 2 ∪
        {3} ×ˢ Icc 1 2 ×ˢ Icc 0 1 ∪ Icc 1 2 ×ˢ {1, 2} ×ˢ Icc 1 2 ∪
        Icc 2 3 ×ˢ {1, 2} ×ˢ Icc 0 1) ∪
      (Icc 0 4 ×ˢ {0, 3} ×ˢ Icc 0 2 ∪ {0, 4} ×ˢ Icc 0 3 ×ˢ Icc 0 2) by
    unfold HouseWithTwoRooms
    congr 2
    ext p
    rcases p with ⟨x, y, z⟩
    simp only [floor0, floor1, floor2, Set.mem_sdiff, Set.mem_union, Set.mem_prod,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, and_true]
    constructor <;> aesop]
  apply IsClosed.union
  · apply IsClosed.union
    · exact (hf0.union hf1).union hf2
    · exact ((((isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc)).union
          (isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc))).union
          (isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc))).union
          (isClosed_Icc.prod ((by simp : IsClosed ({1, 2} : Set ℝ)).prod isClosed_Icc))).union
          (isClosed_Icc.prod ((by simp : IsClosed ({1, 2} : Set ℝ)).prod isClosed_Icc))
  · exact (isClosed_Icc.prod ((by simp : IsClosed ({0, 3} : Set ℝ)).prod isClosed_Icc)).union
      ((by simp : IsClosed ({0, 4} : Set ℝ)).prod (isClosed_Icc.prod isClosed_Icc))

def upperXPanel : Set Point := ({3} : Set ℝ) ×ˢ Icc 1 2 ×ˢ Icc 1 2

def upperYPanel : Set Point := Icc 2 3 ×ˢ ({1} : Set ℝ) ×ˢ Icc 1 2

def lowerXPanel : Set Point := ({1} : Set ℝ) ×ˢ Icc 1 2 ×ˢ Icc 0 1

def lowerYPanel : Set Point := Icc 1 2 ×ˢ ({1} : Set ℝ) ×ˢ Icc 0 1

def cubicalSpine : Set Point :=
  HouseWithTwoRooms ∪ upperXPanel ∪ upperYPanel ∪ lowerXPanel ∪ lowerYPanel

lemma isClosed_cubicalSpine : IsClosed cubicalSpine := by
  have hux : IsClosed upperXPanel := isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc)
  have huy : IsClosed upperYPanel := isClosed_Icc.prod (isClosed_singleton.prod isClosed_Icc)
  have hlx : IsClosed lowerXPanel := isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc)
  have hly : IsClosed lowerYPanel := isClosed_Icc.prod (isClosed_singleton.prod isClosed_Icc)
  exact (((isClosed_houseWithTwoRooms.union hux).union huy).union hlx).union hly

def remaining : List Cell → Set Point
  | [] => cubicalSpine
  | c :: cs => c.set ∪ remaining cs

lemma isClosed_remaining : ∀ cs, IsClosed (remaining cs)
  | [] => isClosed_cubicalSpine
  | c :: cs => c.isClosed_set.union (isClosed_remaining cs)

lemma spine_subset_remaining (cs : List Cell) : cubicalSpine ⊆ remaining cs := by
  intro p hp
  induction cs with
  | nil => exact hp
  | cons c cs ih => exact Or.inr ih

def ValidSequence : List Cell → Prop
  | [] => True
  | c :: cs => ValidStep c (remaining cs) ∧ ValidSequence cs

def retractSequence : (cs : List Cell) → ValidSequence cs →
    ContinuousMap (remaining cs) cubicalSpine
  | [], _ => ContinuousMap.id _
  | c :: cs, h =>
      (retractSequence cs h.2).comp (collapseMap c (remaining cs) h.1 (isClosed_remaining cs))

lemma retractSequence_eq_self : ∀ (cs : List Cell) (h : ValidSequence cs)
    (p : cubicalSpine),
      retractSequence cs h ⟨p, spine_subset_remaining cs p.2⟩ = p
  | [], _, _ => rfl
  | c :: cs, h, p => by
      rcases h with ⟨hc, hcs⟩
      change retractSequence cs hcs
        (collapseMap c (remaining cs) hc (isClosed_remaining cs)
          ⟨p, Or.inr (spine_subset_remaining cs p.2)⟩) = p
      have hcollapse :
          collapseMap c (remaining cs) hc (isClosed_remaining cs)
              ⟨p, Or.inr (spine_subset_remaining cs p.2)⟩ =
            ⟨p, spine_subset_remaining cs p.2⟩ :=
        collapseMap_eq_self c (remaining cs) hc (isClosed_remaining cs)
          ⟨p, spine_subset_remaining cs p.2⟩
      rw [hcollapse]
      exact retractSequence_eq_self cs hcs p

def collapseSequence : List Cell :=
  [⟨2, 1, 0, .zNeg⟩,
   ⟨2, 1, 1, .zNeg⟩,
   ⟨2, 2, 1, .yNeg⟩,
   ⟨3, 2, 1, .xNeg⟩,
   ⟨3, 1, 1, .yPos⟩,
   ⟨3, 0, 1, .yPos⟩,
   ⟨2, 0, 1, .xPos⟩,
   ⟨1, 0, 1, .xPos⟩,
   ⟨0, 0, 1, .xPos⟩,
   ⟨0, 1, 1, .yNeg⟩,
   ⟨0, 2, 1, .yNeg⟩,
   ⟨1, 2, 1, .xNeg⟩,
   ⟨1, 1, 1, .zPos⟩,
   ⟨1, 1, 0, .zPos⟩,
   ⟨1, 2, 0, .yNeg⟩,
   ⟨0, 2, 0, .xPos⟩,
   ⟨0, 1, 0, .yPos⟩,
   ⟨0, 0, 0, .yPos⟩,
   ⟨1, 0, 0, .xNeg⟩,
   ⟨2, 0, 0, .xNeg⟩,
   ⟨3, 0, 0, .xNeg⟩,
   ⟨3, 1, 0, .yNeg⟩,
   ⟨3, 2, 0, .yNeg⟩,
   ⟨2, 2, 0, .xPos⟩]

set_option maxHeartbeats 0 in
lemma valid_collapseSequence : ValidSequence collapseSequence := by
  simp only [collapseSequence, ValidSequence]
  repeat' constructor
  all_goals
    intro p hp
    rcases p with ⟨x, y, z⟩
    simp only [Cell.horn, stdHorn, stdCube, stdBoundary, toStd, Set.mem_preimage,
      Set.mem_setOf_eq, remaining, Cell.set, Set.mem_inter_iff, Set.mem_union,
      Set.mem_prod, Set.mem_Icc, cubicalSpine, upperXPanel, upperYPanel, lowerXPanel,
      lowerYPanel, HouseWithTwoRooms, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp ⊢
    grind (splits := 80)

def box : Set Point := Icc 0 4 ×ˢ Icc 0 3 ×ˢ Icc 0 2

set_option maxHeartbeats 0 in
lemma box_subset_remaining : box ⊆ remaining collapseSequence := by
  rintro ⟨x, y, z⟩ hp
  simp only [box, Set.mem_prod, Set.mem_Icc] at hp
  simp only [collapseSequence, remaining, Cell.set, Set.mem_union, Set.mem_prod, Set.mem_Icc]
  grind (splits := 80)

def boxToSpine : ContinuousMap box cubicalSpine :=
  (retractSequence collapseSequence valid_collapseSequence).comp
    ⟨fun p => ⟨p, box_subset_remaining p.2⟩, continuous_subtype_val.subtype_mk _⟩

lemma boxToSpine_eq_self (p : cubicalSpine) (hp : (p : Point) ∈ box) :
    boxToSpine ⟨p, hp⟩ = p := by
  exact retractSequence_eq_self collapseSequence valid_collapseSequence p

abbrev PlanePoint := ℝ × ℝ

def stdSquare : Set PlanePoint := Icc 0 1 ×ˢ Icc 0 1

def embedSquare (p : PlanePoint) : Point := (p.1, p.2, 1 / 2)

def projectSquare (p : Point) : PlanePoint := (p.1, p.2.1)

def squareCollapse (p : PlanePoint) : PlanePoint :=
  projectSquare (stdCollapse (embedSquare p))

def squareBoundary (p : PlanePoint) : Prop := p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1

lemma embedSquare_mem {p : PlanePoint} (hp : p ∈ stdSquare) : embedSquare p ∈ stdCube := by
  rcases hp with ⟨hx, hy⟩
  simp only [embedSquare, stdCube, Set.mem_prod, Set.mem_Icc]
  exact ⟨hx, hy, by norm_num⟩

lemma continuous_squareCollapse : Continuous squareCollapse := by
  have he : Continuous embedSquare := by unfold embedSquare; fun_prop
  have hc := continuous_stdCollapse.comp he
  exact (continuous_fst.comp hc).prodMk ((continuous_fst.comp continuous_snd).comp hc)

lemma squareCollapse_mem {p : PlanePoint} (hp : p ∈ stdSquare) :
    squareCollapse p ∈ stdSquare := by
  have h := stdCollapse_mem_cube (embedSquare_mem hp)
  exact ⟨h.1, h.2.1⟩

lemma squareCollapse_boundary {p : PlanePoint} (hp : p ∈ stdSquare) :
    squareBoundary (squareCollapse p) := by
  have h := stdCollapse_boundary (embedSquare_mem hp)
  simp only [stdBoundary, squareBoundary, squareCollapse, projectSquare] at h ⊢
  simpa [embedSquare, stdCollapse] using h

lemma squareCollapse_eq_self {p : PlanePoint} (hp : p ∈ stdSquare)
    (h : squareBoundary p) : squareCollapse p = p := by
  have he : stdBoundary (embedSquare p) := by
    simpa [stdBoundary, embedSquare, squareBoundary] using h
  have hc := stdCollapse_eq_self (embedSquare_mem hp) he
  have hproj := congrArg projectSquare hc
  simpa [squareCollapse, projectSquare, embedSquare] using hproj

inductive Panel
  | upperX
  | upperY
  | lowerX
  | lowerY

def Panel.set : Panel → Set Point
  | .upperX => upperXPanel
  | .upperY => upperYPanel
  | .lowerX => lowerXPanel
  | .lowerY => lowerYPanel

def panelToStd : Panel → Point → PlanePoint
  | .upperX, p => (2 - p.2.1, p.2.2 - 1)
  | .upperY, p => (3 - p.1, p.2.2 - 1)
  | .lowerX, p => (2 - p.2.1, p.2.2)
  | .lowerY, p => (p.1 - 1, p.2.2)

def panelFromStd : Panel → PlanePoint → Point
  | .upperX, p => (3, 2 - p.1, 1 + p.2)
  | .upperY, p => (3 - p.1, 1, 1 + p.2)
  | .lowerX, p => (1, 2 - p.1, p.2)
  | .lowerY, p => (1 + p.1, 1, p.2)

lemma panelFrom_to {k : Panel} {p : Point} (hp : p ∈ k.set) :
    panelFromStd k (panelToStd k p) = p := by
  rcases p with ⟨x, y, z⟩
  cases k <;> simp [Panel.set, upperXPanel, upperYPanel, lowerXPanel, lowerYPanel,
    panelFromStd, panelToStd, Prod.ext_iff] at hp ⊢
  all_goals grind

lemma panelTo_from (k : Panel) (p : PlanePoint) :
    panelToStd k (panelFromStd k p) = p := by
  rcases p with ⟨u, v⟩
  cases k <;> simp [panelToStd, panelFromStd]

lemma panelToStd_mem {k : Panel} {p : Point} (hp : p ∈ k.set) :
    panelToStd k p ∈ stdSquare := by
  rcases p with ⟨x, y, z⟩
  cases k <;> simp only [Panel.set, upperXPanel, upperYPanel, lowerXPanel, lowerYPanel,
    Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hp
  all_goals
    rcases hp with ⟨hx, hy, hz⟩
    simp only [panelToStd, stdSquare, Set.mem_prod, Set.mem_Icc]
    constructor <;> constructor <;> linarith

lemma panelFromStd_mem {k : Panel} {p : PlanePoint} (hp : p ∈ stdSquare) :
    panelFromStd k p ∈ k.set := by
  rcases p with ⟨u, v⟩
  simp only [stdSquare, Set.mem_prod, Set.mem_Icc] at hp
  rcases hp with ⟨⟨hu0, hu1⟩, hv0, hv1⟩
  cases k <;> simp only [panelFromStd, Panel.set, upperXPanel, upperYPanel, lowerXPanel,
    lowerYPanel, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc]
  · exact ⟨trivial, ⟨by linarith, by linarith⟩, by constructor <;> linarith⟩
  · exact ⟨⟨by linarith, by linarith⟩, trivial, by constructor <;> linarith⟩
  · exact ⟨trivial, ⟨by linarith, by linarith⟩, ⟨hv0, hv1⟩⟩
  · exact ⟨⟨by linarith, by linarith⟩, trivial, ⟨hv0, hv1⟩⟩

lemma continuous_panelToStd (k : Panel) : Continuous (panelToStd k) := by
  cases k <;> unfold panelToStd <;> fun_prop

lemma continuous_panelFromStd (k : Panel) : Continuous (panelFromStd k) := by
  cases k <;> unfold panelFromStd <;> fun_prop

def Panel.horn (k : Panel) : Set Point :=
  {p | p ∈ k.set ∧ squareBoundary (panelToStd k p)}

def panelCollapse (k : Panel) (p : Point) : Point :=
  panelFromStd k (squareCollapse (panelToStd k p))

lemma Panel.isClosed_set : ∀ k : Panel, IsClosed k.set
  | .upperX => isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc)
  | .upperY => isClosed_Icc.prod (isClosed_singleton.prod isClosed_Icc)
  | .lowerX => isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc)
  | .lowerY => isClosed_Icc.prod (isClosed_singleton.prod isClosed_Icc)

lemma continuous_panelCollapse (k : Panel) : Continuous (panelCollapse k) :=
  (continuous_panelFromStd k).comp (continuous_squareCollapse.comp (continuous_panelToStd k))

lemma panelCollapse_mem_horn {k : Panel} {p : Point} (hp : p ∈ k.set) :
    panelCollapse k p ∈ k.horn := by
  refine ⟨panelFromStd_mem (squareCollapse_mem (panelToStd_mem hp)), ?_⟩
  change squareBoundary (panelToStd k (panelFromStd k (squareCollapse (panelToStd k p))))
  rw [panelTo_from]
  exact squareCollapse_boundary (panelToStd_mem hp)

lemma panelCollapse_eq_self {k : Panel} {p : Point} (hp : p ∈ k.horn) :
    panelCollapse k p = p := by
  unfold panelCollapse
  rw [squareCollapse_eq_self (panelToStd_mem hp.1) hp.2, panelFrom_to hp.1]

def ValidPanelStep (k : Panel) (s : Set Point) : Prop :=
  k.horn ⊆ s ∧ k.set ∩ s ⊆ k.horn

noncomputable def panelCollapseAmbient (k : Panel) : Point → Point := by
  classical
  exact k.set.piecewise (panelCollapse k) id

lemma panelCollapseAmbient_mem {k : Panel} {s : Set Point} (h : ValidPanelStep k s)
    {p : Point} (hp : p ∈ k.set ∪ s) : panelCollapseAmbient k p ∈ s := by
  classical
  by_cases hk : p ∈ k.set
  · simpa [panelCollapseAmbient, hk] using h.1 (panelCollapse_mem_horn hk)
  · simpa [panelCollapseAmbient, hk] using hp.resolve_left hk

lemma panelCollapseAmbient_eq_self {k : Panel} {s : Set Point} (h : ValidPanelStep k s)
    {p : Point} (hp : p ∈ s) : panelCollapseAmbient k p = p := by
  classical
  by_cases hk : p ∈ k.set
  · have hh : p ∈ k.horn := h.2 ⟨hk, hp⟩
    simp [panelCollapseAmbient, hk, panelCollapse_eq_self hh]
  · simp [panelCollapseAmbient, hk]

lemma continuousOn_panelCollapseAmbient {k : Panel} {s : Set Point}
    (h : ValidPanelStep k s) (hs : IsClosed s) :
    ContinuousOn (panelCollapseAmbient k) (k.set ∪ s) := by
  classical
  have hk : ContinuousOn (panelCollapseAmbient k) k.set :=
    (continuous_panelCollapse k).continuousOn.congr fun p hp => by
      simp [panelCollapseAmbient, hp]
  have hs' : ContinuousOn (panelCollapseAmbient k) s :=
    continuous_id.continuousOn.congr fun p hp => panelCollapseAmbient_eq_self h hp
  exact hk.union_of_isClosed hs' k.isClosed_set hs

def panelCollapseMap (k : Panel) (s : Set Point) (h : ValidPanelStep k s) (hs : IsClosed s) :
    ContinuousMap {p : Point // p ∈ k.set ∪ s} {p : Point // p ∈ s} :=
  ⟨fun p => ⟨panelCollapseAmbient k p, panelCollapseAmbient_mem h p.2⟩,
    (continuousOn_iff_continuous_restrict.mp
      (continuousOn_panelCollapseAmbient h hs)).subtype_mk _⟩

lemma panelCollapseMap_eq_self (k : Panel) (s : Set Point) (h : ValidPanelStep k s)
    (hs : IsClosed s) (p : s) : panelCollapseMap k s h hs ⟨p, Or.inr p.2⟩ = p := by
  apply Subtype.ext
  exact panelCollapseAmbient_eq_self h p.2

def panelSequence : List Panel := [.upperX, .upperY, .lowerX, .lowerY]

def panelRemaining : List Panel → Set Point
  | [] => HouseWithTwoRooms
  | k :: ks => k.set ∪ panelRemaining ks

lemma isClosed_panelRemaining : ∀ ks, IsClosed (panelRemaining ks)
  | [] => isClosed_houseWithTwoRooms
  | k :: ks => k.isClosed_set.union (isClosed_panelRemaining ks)

lemma house_subset_panelRemaining (ks : List Panel) : HouseWithTwoRooms ⊆ panelRemaining ks := by
  intro p hp
  induction ks with
  | nil => exact hp
  | cons k ks ih => exact Or.inr ih

def ValidPanelSequence : List Panel → Prop
  | [] => True
  | k :: ks => ValidPanelStep k (panelRemaining ks) ∧ ValidPanelSequence ks

def retractPanelSequence : (ks : List Panel) → ValidPanelSequence ks →
    ContinuousMap (panelRemaining ks) HouseWithTwoRooms
  | [], _ => ContinuousMap.id _
  | k :: ks, h =>
      (retractPanelSequence ks h.2).comp
        (panelCollapseMap k (panelRemaining ks) h.1 (isClosed_panelRemaining ks))

lemma retractPanelSequence_eq_self : ∀ (ks : List Panel) (h : ValidPanelSequence ks)
    (p : HouseWithTwoRooms),
      retractPanelSequence ks h ⟨p, house_subset_panelRemaining ks p.2⟩ = p
  | [], _, _ => rfl
  | k :: ks, h, p => by
      rcases h with ⟨hk, hks⟩
      change retractPanelSequence ks hks
        (panelCollapseMap k (panelRemaining ks) hk (isClosed_panelRemaining ks)
          ⟨p, Or.inr (house_subset_panelRemaining ks p.2)⟩) = p
      have hcollapse :
          panelCollapseMap k (panelRemaining ks) hk (isClosed_panelRemaining ks)
              ⟨p, Or.inr (house_subset_panelRemaining ks p.2)⟩ =
            ⟨p, house_subset_panelRemaining ks p.2⟩ :=
        panelCollapseMap_eq_self k (panelRemaining ks) hk (isClosed_panelRemaining ks)
          ⟨p, house_subset_panelRemaining ks p.2⟩
      rw [hcollapse]
      exact retractPanelSequence_eq_self ks hks p

set_option maxHeartbeats 200000 in
lemma valid_panelSequence : ValidPanelSequence panelSequence := by
  simp only [panelSequence, ValidPanelSequence]
  repeat' constructor
  all_goals
    intro p hp
    rcases p with ⟨x, y, z⟩
    simp only [Panel.horn, squareBoundary, panelToStd, panelRemaining,
      Panel.set, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_prod,
      Set.mem_Icc, Set.mem_singleton_iff, upperXPanel, upperYPanel, lowerXPanel,
      lowerYPanel, HouseWithTwoRooms, Set.mem_sdiff, Set.mem_insert_iff] at hp ⊢
    grind (splits := 30)

lemma panelRemaining_eq_spine : panelRemaining panelSequence = cubicalSpine := by
  ext p
  simp only [panelSequence, panelRemaining, Panel.set, cubicalSpine, Set.mem_union]
  tauto

def spineToPanelRemaining (p : cubicalSpine) : panelRemaining panelSequence :=
  ⟨p, by rw [panelRemaining_eq_spine]; exact p.2⟩

lemma continuous_spineToPanelRemaining : Continuous spineToPanelRemaining := by
  apply Continuous.subtype_mk continuous_subtype_val

def spineToHouse : ContinuousMap cubicalSpine HouseWithTwoRooms :=
  (retractPanelSequence panelSequence valid_panelSequence).comp
    ⟨spineToPanelRemaining, continuous_spineToPanelRemaining⟩

lemma house_subset_spine : HouseWithTwoRooms ⊆ cubicalSpine := by
  intro p hp
  simp only [cubicalSpine, Set.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl hp)))

lemma spineToHouse_eq_self (p : HouseWithTwoRooms) :
    spineToHouse ⟨p, house_subset_spine p.2⟩ = p := by
  simpa [spineToHouse, spineToPanelRemaining] using
    retractPanelSequence_eq_self panelSequence valid_panelSequence p

def boxToHouse : ContinuousMap box HouseWithTwoRooms := spineToHouse.comp boxToSpine

set_option maxHeartbeats 0 in
lemma house_subset_box : HouseWithTwoRooms ⊆ box := by
  rintro ⟨x, y, z⟩ hp
  simp only [HouseWithTwoRooms, Set.mem_union, Set.mem_sdiff, Set.mem_prod, Set.mem_Icc,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  simp only [box, Set.mem_prod, Set.mem_Icc]
  grind (splits := 20)

lemma boxToHouse_eq_self (p : HouseWithTwoRooms) :
    boxToHouse ⟨p, house_subset_box p.2⟩ = p := by
  have hspine : boxToSpine ⟨p, house_subset_box p.2⟩ =
      ⟨p, house_subset_spine p.2⟩ :=
    boxToSpine_eq_self ⟨p, house_subset_spine p.2⟩ (house_subset_box p.2)
  change spineToHouse (boxToSpine ⟨p, house_subset_box p.2⟩) = p
  rw [hspine]
  exact spineToHouse_eq_self p

def houseBase : HouseWithTwoRooms :=
  ⟨(0, 0, 0), by simp [HouseWithTwoRooms]⟩

def contractInBox (p : I × HouseWithTwoRooms) : box :=
  ⟨((1 - p.1.1) * p.2.1.1,
      (1 - p.1.1) * p.2.1.2.1,
      (1 - p.1.1) * p.2.1.2.2), by
    have ht0 : 0 ≤ p.1.1 := p.1.2.1
    have ht1 : p.1.1 ≤ 1 := p.1.2.2
    have hs0 : 0 ≤ 1 - p.1.1 := sub_nonneg.mpr ht1
    have hs1 : 1 - p.1.1 ≤ 1 := by linarith
    have hb := house_subset_box p.2.2
    rcases hb with ⟨⟨hx0, hx4⟩, ⟨⟨hy0, hy3⟩, hz0, hz2⟩⟩
    have hxle : (1 - p.1.1) * p.2.1.1 ≤ p.2.1.1 := by
      simpa using mul_le_mul_of_nonneg_right hs1 hx0
    have hyle : (1 - p.1.1) * p.2.1.2.1 ≤ p.2.1.2.1 := by
      simpa using mul_le_mul_of_nonneg_right hs1 hy0
    have hzle : (1 - p.1.1) * p.2.1.2.2 ≤ p.2.1.2.2 := by
      simpa using mul_le_mul_of_nonneg_right hs1 hz0
    exact
      ⟨⟨mul_nonneg hs0 hx0, hxle.trans hx4⟩,
        ⟨⟨mul_nonneg hs0 hy0, hyle.trans hy3⟩,
          mul_nonneg hs0 hz0, hzle.trans hz2⟩⟩⟩

lemma continuous_contractInBox : Continuous contractInBox := by
  apply Continuous.subtype_mk
  fun_prop

lemma contractInBox_zero (p : HouseWithTwoRooms) :
    contractInBox (0, p) = ⟨p, house_subset_box p.2⟩ := by
  apply Subtype.ext
  simp [contractInBox]

lemma contractInBox_one (p : HouseWithTwoRooms) :
    contractInBox (1, p) = ⟨houseBase, house_subset_box houseBase.2⟩ := by
  apply Subtype.ext
  simp [contractInBox, houseBase]

lemma boxToHouse_contract_zero (p : HouseWithTwoRooms) :
    boxToHouse (contractInBox (0, p)) = p := by
  rw [contractInBox_zero]
  exact boxToHouse_eq_self p

lemma boxToHouse_contract_one (p : HouseWithTwoRooms) :
    boxToHouse (contractInBox (1, p)) = houseBase := by
  rw [contractInBox_one]
  exact boxToHouse_eq_self houseBase

theorem contractibleSpace_houseWithTwoRooms : ContractibleSpace HouseWithTwoRooms := by
  refine (contractible_iff_id_nullhomotopic HouseWithTwoRooms).2
    ⟨houseBase, ⟨⟨⟨fun p => boxToHouse (contractInBox p), ?_⟩, ?_, ?_⟩⟩⟩
  · exact boxToHouse.continuous.comp continuous_contractInBox
  · exact boxToHouse_contract_zero
  · exact boxToHouse_contract_one

end

end Submission.Helpers
