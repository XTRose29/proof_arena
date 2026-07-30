import ChallengeDeps

open LeanEval.Topology
open Set (Icc Ioo)

namespace Submission

noncomputable section

def HouseAmbientBox : Set (ℝ × ℝ × ℝ) :=
  Icc (0 : ℝ) 4 ×ˢ Icc (0 : ℝ) 3 ×ˢ Icc (0 : ℝ) 2

def unitCube (i j k : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc i (i + 1) ×ˢ Icc j (j + 1) ×ˢ Icc k (k + 1)

def horizontalFace (i j k : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc i (i + 1) ×ˢ Icc j (j + 1) ×ˢ ({k} : Set ℝ)

def xFace (i j k : ℝ) : Set (ℝ × ℝ × ℝ) :=
  ({i} : Set ℝ) ×ˢ Icc j (j + 1) ×ˢ Icc k (k + 1)

def yFace (i j k : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc i (i + 1) ×ˢ ({j} : Set ℝ) ×ˢ Icc k (k + 1)

lemma houseWithTwoRooms_origin_mem :
    ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ LeanEval.Topology.HouseWithTwoRooms := by
  simp [LeanEval.Topology.HouseWithTwoRooms]

def houseAmbientBox_origin : HouseAmbientBox :=
  ⟨((0 : ℝ), (0 : ℝ), (0 : ℝ)), by simp [HouseAmbientBox]⟩

instance houseAmbientBox_contractible : ContractibleSpace HouseAmbientBox := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨houseAmbientBox_origin, ⟨?_⟩⟩
  refine
    { toFun := fun q => ?_
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · let a : ℝ := 1 - (q.1 : ℝ)
    refine ⟨(a * (q.2 : ℝ × ℝ × ℝ).1,
        a * (q.2 : ℝ × ℝ × ℝ).2.1,
        a * (q.2 : ℝ × ℝ × ℝ).2.2), ?_⟩
    rcases q with ⟨t, p⟩
    rcases p with ⟨⟨x, y, z⟩, hp⟩
    simp only [HouseAmbientBox, Set.mem_prod, Set.mem_Icc] at hp ⊢
    dsimp [a]
    constructor
    · constructor
      · nlinarith [t.2.1, t.2.2, hp.1.1, hp.1.2]
      · nlinarith [t.2.1, t.2.2, hp.1.1, hp.1.2]
    · constructor
      · constructor
        · nlinarith [t.2.1, t.2.2, hp.2.1.1, hp.2.1.2]
        · nlinarith [t.2.1, t.2.2, hp.2.1.1, hp.2.1.2]
      · constructor
        · nlinarith [t.2.1, t.2.2, hp.2.2.1, hp.2.2.2]
        · nlinarith [t.2.1, t.2.2, hp.2.2.1, hp.2.2.2]
  · apply Continuous.subtype_mk
    fun_prop
  · intro p
    ext <;> simp
  · intro p
    ext <;> simp [houseAmbientBox_origin]

lemma contractibleSpace_of_retract {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] (i : C(Y, X)) (r : C(X, Y))
    (hri : r.comp i = ContinuousMap.id Y) : ContractibleSpace Y := by
  rw [contractible_iff_id_nullhomotopic]
  rcases id_nullhomotopic X with ⟨x₀, hX⟩
  refine ⟨r x₀, ?_⟩
  have h₁ : ContinuousMap.Homotopic ((ContinuousMap.id X).comp i)
      ((ContinuousMap.const X x₀).comp i) := by
    exact ContinuousMap.Homotopic.comp hX (ContinuousMap.Homotopic.refl i)
  have h₂ : ContinuousMap.Homotopic (r.comp ((ContinuousMap.id X).comp i))
      (r.comp ((ContinuousMap.const X x₀).comp i)) := by
    exact ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl r) h₁
  simpa [hri] using h₂

lemma houseWithTwoRooms_subset_ambientBox :
    LeanEval.Topology.HouseWithTwoRooms ⊆ HouseAmbientBox := by
  rintro ⟨x, y, z⟩ hp
  simp only [LeanEval.Topology.HouseWithTwoRooms, HouseAmbientBox, Set.mem_union, Set.mem_diff,
    Set.mem_prod, Set.mem_Icc, Set.mem_Ioo, Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
  grind

def houseWithTwoRooms_inclusion_ambientBox :
    C(LeanEval.Topology.HouseWithTwoRooms, HouseAmbientBox) where
  toFun p := ⟨(p : ℝ × ℝ × ℝ), houseWithTwoRooms_subset_ambientBox p.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

def horizontalHouseClosedModel : Set (ℝ × ℝ × ℝ) :=
  (Icc (0 : ℝ) 2 ×ˢ Icc (0 : ℝ) 3 ×ˢ ({0} : Set ℝ)) ∪
  (Icc (3 : ℝ) 4 ×ˢ Icc (0 : ℝ) 3 ×ˢ ({0} : Set ℝ)) ∪
  (Icc (0 : ℝ) 4 ×ˢ Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)) ∪
  (Icc (0 : ℝ) 4 ×ˢ Icc (2 : ℝ) 3 ×ˢ ({0} : Set ℝ)) ∪
  (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 3 ×ˢ ({1} : Set ℝ)) ∪
  (Icc (3 : ℝ) 4 ×ˢ Icc (0 : ℝ) 3 ×ˢ ({1} : Set ℝ)) ∪
  (Icc (0 : ℝ) 4 ×ˢ Icc (0 : ℝ) 1 ×ˢ ({1} : Set ℝ)) ∪
  (Icc (0 : ℝ) 4 ×ˢ Icc (2 : ℝ) 3 ×ˢ ({1} : Set ℝ)) ∪
  (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 3 ×ˢ ({2} : Set ℝ)) ∪
  (Icc (2 : ℝ) 4 ×ˢ Icc (0 : ℝ) 3 ×ˢ ({2} : Set ℝ)) ∪
  (Icc (0 : ℝ) 4 ×ˢ Icc (0 : ℝ) 1 ×ˢ ({2} : Set ℝ)) ∪
  (Icc (0 : ℝ) 4 ×ˢ Icc (2 : ℝ) 3 ×ˢ ({2} : Set ℝ))

lemma horizontalHouseClosedModel_eq_original :
    horizontalHouseClosedModel =
      (Icc (0 : ℝ) 4 ×ˢ Icc (0 : ℝ) 3 ×ˢ ({0, 1, 2} : Set ℝ) \
        (Ioo (2 : ℝ) 3 ×ˢ Ioo (1 : ℝ) 2 ×ˢ ({0} : Set ℝ) ∪
          Ioo (1 : ℝ) 3 ×ˢ Ioo (1 : ℝ) 2 ×ˢ ({1} : Set ℝ) ∪
          Ioo (1 : ℝ) 2 ×ˢ Ioo (1 : ℝ) 2 ×ˢ ({2} : Set ℝ))) := by
  ext p
  rcases p with ⟨x, y, z⟩
  simp only [horizontalHouseClosedModel, Set.mem_union, Set.mem_diff, Set.mem_prod,
    Set.mem_Icc, Set.mem_Ioo, Set.mem_insert_iff, Set.mem_singleton_iff]
  grind

lemma isClosed_horizontalHouseClosedModel : IsClosed horizontalHouseClosedModel := by
  unfold horizontalHouseClosedModel
  repeat' apply IsClosed.union
  all_goals exact isClosed_Icc.prod (isClosed_Icc.prod isClosed_singleton)

lemma isClosed_verticalHouseMiddle : IsClosed
    ({(1 : ℝ)} ×ˢ Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2 ∪
      {(2 : ℝ)} ×ˢ Icc (1 : ℝ) 3 ×ˢ Icc (0 : ℝ) 2 ∪
      {(3 : ℝ)} ×ˢ Icc (1 : ℝ) 2 ×ˢ Icc (0 : ℝ) 1 ∪
      Icc (1 : ℝ) 2 ×ˢ ({1, 2} : Set ℝ) ×ˢ Icc (1 : ℝ) 2 ∪
      Icc (2 : ℝ) 3 ×ˢ ({1, 2} : Set ℝ) ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ × ℝ)) := by
  repeat' apply IsClosed.union
  · exact isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc)
  · exact isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc)
  · exact isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc)
  · exact isClosed_Icc.prod ((isClosed_singleton.union isClosed_singleton).prod isClosed_Icc)
  · exact isClosed_Icc.prod ((isClosed_singleton.union isClosed_singleton).prod isClosed_Icc)

lemma isClosed_verticalHouseOuter : IsClosed
    (Icc (0 : ℝ) 4 ×ˢ ({0, 3} : Set ℝ) ×ˢ Icc (0 : ℝ) 2 ∪
      ({0, 4} : Set ℝ) ×ˢ Icc (0 : ℝ) 3 ×ˢ Icc (0 : ℝ) 2 : Set (ℝ × ℝ × ℝ)) := by
  apply IsClosed.union
  · exact isClosed_Icc.prod ((isClosed_singleton.union isClosed_singleton).prod isClosed_Icc)
  · exact (isClosed_singleton.union isClosed_singleton).prod (isClosed_Icc.prod isClosed_Icc)

lemma isClosed_houseWithTwoRooms : IsClosed LeanEval.Topology.HouseWithTwoRooms := by
  unfold LeanEval.Topology.HouseWithTwoRooms
  have hhor : IsClosed
      (Icc (0 : ℝ) 4 ×ˢ Icc (0 : ℝ) 3 ×ˢ ({0, 1, 2} : Set ℝ) \
        (Ioo (2 : ℝ) 3 ×ˢ Ioo (1 : ℝ) 2 ×ˢ ({0} : Set ℝ) ∪
          Ioo (1 : ℝ) 3 ×ˢ Ioo (1 : ℝ) 2 ×ˢ ({1} : Set ℝ) ∪
          Ioo (1 : ℝ) 2 ×ˢ Ioo (1 : ℝ) 2 ×ˢ ({2} : Set ℝ))) := by
    rw [← horizontalHouseClosedModel_eq_original]
    exact isClosed_horizontalHouseClosedModel
  simpa [Set.union_assoc] using hhor.union (isClosed_verticalHouseMiddle.union isClosed_verticalHouseOuter)

inductive CubicalTopCell where
  | cube (i j k : ℝ)
  | xSquare (i j k : ℝ)
  | ySquare (i j k : ℝ)
  | hSquare (i j k : ℝ)

def CubicalTopCell.carrier : CubicalTopCell → Set (ℝ × ℝ × ℝ)
  | .cube i j k => unitCube i j k
  | .xSquare i j k => xFace i j k
  | .ySquare i j k => yFace i j k
  | .hSquare i j k => horizontalFace i j k

lemma CubicalTopCell.isClosed_carrier (c : CubicalTopCell) : IsClosed c.carrier := by
  rcases c with ⟨i,j,k⟩ | ⟨i,j,k⟩ | ⟨i,j,k⟩ | ⟨i,j,k⟩
  · exact isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)
  · exact isClosed_singleton.prod (isClosed_Icc.prod isClosed_Icc)
  · exact isClosed_Icc.prod (isClosed_singleton.prod isClosed_Icc)
  · exact isClosed_Icc.prod (isClosed_Icc.prod isClosed_singleton)

def hatcherCollapseCell (m : Fin 28) : CubicalTopCell :=
  match m.1 with
  | 0 => .cube 2 1 0
  | 1 => .cube 2 1 1
  | 2 => .cube 2 0 1
  | 3 => .cube 3 0 1
  | 4 => .cube 1 1 1
  | 5 => .cube 1 1 0
  | 6 => .cube 1 0 0
  | 7 => .cube 2 2 1
  | 8 => .cube 1 0 1
  | 9 => .cube 2 0 0
  | 10 => .cube 3 2 1
  | 11 => .cube 0 0 0
  | 12 => .cube 3 1 1
  | 13 => .cube 1 2 0
  | 14 => .xSquare 3 1 1
  | 15 => .cube 0 1 0
  | 16 => .xSquare 1 1 0
  | 17 => .cube 3 0 0
  | 18 => .cube 0 0 1
  | 19 => .cube 0 2 0
  | 20 => .cube 0 1 1
  | 21 => .ySquare 0 2 0
  | 22 => .cube 0 2 1
  | 23 => .ySquare 3 2 1
  | 24 => .cube 3 1 0
  | 25 => .cube 3 2 0
  | 26 => .cube 1 2 1
  | _ => .cube 2 2 0

def hatcherStage (n : ℕ) : Set (ℝ × ℝ × ℝ) :=
  LeanEval.Topology.HouseWithTwoRooms ∪
    ⋃ (m : Fin 28), (if n ≤ m.1 then (hatcherCollapseCell m).carrier else ∅)

lemma isClosed_hatcherStage (n : ℕ) : IsClosed (hatcherStage n) := by
  unfold hatcherStage
  apply IsClosed.union isClosed_houseWithTwoRooms
  exact isClosed_iUnion_of_finite (fun m : Fin 28 => by
    by_cases h : n ≤ m.1
    · simpa [h] using (hatcherCollapseCell m).isClosed_carrier
    · simp [h])

lemma hatcherStage_last : hatcherStage 28 = LeanEval.Topology.HouseWithTwoRooms := by
  ext p
  constructor
  · intro hp
    rcases hp with hpH | hpU
    · exact hpH
    · rcases Set.mem_iUnion.mp hpU with ⟨m, hm⟩
      have hnot : ¬ 28 ≤ m.1 := by omega
      simp [hnot] at hm
  · intro hp
    exact Or.inl hp

set_option maxHeartbeats 2000000 in
lemma hatcherStage_subset_ambientBox (n : ℕ) : hatcherStage n ⊆ HouseAmbientBox := by
  intro p hp
  rcases hp with hpH | hpU
  · exact houseWithTwoRooms_subset_ambientBox hpH
  · rcases Set.mem_iUnion.mp hpU with ⟨m, hm⟩
    by_cases h : n ≤ m.1
    · have hmem : p ∈ (hatcherCollapseCell m).carrier := by simpa [h] using hm
      fin_cases m <;>
        rcases p with ⟨x,y,z⟩ <;>
        simp [hatcherCollapseCell, CubicalTopCell.carrier, unitCube, xFace, yFace,
          horizontalFace, HouseAmbientBox, Set.mem_prod, Set.mem_Icc,
          Set.mem_singleton_iff] at hmem ⊢ <;>
        grind
    · simp [h] at hm

def lowerZCubeCollapseDen (p : ℝ × ℝ × ℝ) : ℝ :=
  max (1 / 2 : ℝ)
    (max (max |2 * p.1 - 1| |2 * p.2.1 - 1|) ((p.2.2 + 1) / 2))

lemma lowerZCubeCollapseDen_pos (p : ℝ × ℝ × ℝ) : 0 < lowerZCubeCollapseDen p := by
  unfold lowerZCubeCollapseDen
  nlinarith [le_max_left (1 / 2 : ℝ)
    (max (max |2 * p.1 - 1| |2 * p.2.1 - 1|) ((p.2.2 + 1) / 2))]

lemma continuous_lowerZCubeCollapseDen : Continuous lowerZCubeCollapseDen := by
  unfold lowerZCubeCollapseDen
  fun_prop

def lowerZCubeCollapse (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let lam : ℝ := 1 / lowerZCubeCollapseDen p
  (1 / 2 + lam * (p.1 - 1 / 2),
    1 / 2 + lam * (p.2.1 - 1 / 2),
    -1 + lam * (p.2.2 + 1))

lemma continuous_lowerZCubeCollapse : Continuous lowerZCubeCollapse := by
  have hden : Continuous lowerZCubeCollapseDen := continuous_lowerZCubeCollapseDen
  have hlam : Continuous (fun p : ℝ × ℝ × ℝ => 1 / lowerZCubeCollapseDen p) := by
    exact continuous_const.div hden (fun p => ne_of_gt (lowerZCubeCollapseDen_pos p))
  unfold lowerZCubeCollapse
  fun_prop

lemma lowerZCubeCollapseDen_le_one_of_mem_unitCube {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube 0 0 0) : lowerZCubeCollapseDen p ≤ 1 := by
  rcases p with ⟨x,y,z⟩
  simp only [unitCube, Set.mem_prod, Set.mem_Icc] at hp
  unfold lowerZCubeCollapseDen
  simp only
  apply max_le
  · norm_num
  · apply max_le
    · apply max_le
      · rw [abs_le]
        constructor <;> nlinarith [hp.1.1, hp.1.2]
      · rw [abs_le]
        constructor <;> nlinarith [hp.2.1.1, hp.2.1.2]
    · nlinarith [hp.2.2.1, hp.2.2.2]

lemma abs_sub_half_le_den_half (x y z : ℝ) :
    |x - 1 / 2| ≤ lowerZCubeCollapseDen (x,y,z) / 2 := by
  have hle : |2 * x - 1| ≤ lowerZCubeCollapseDen (x,y,z) := by
    unfold lowerZCubeCollapseDen
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hrewrite : |2 * x - 1| = 2 * |x - 1 / 2| := by
    rw [show 2 * x - 1 = (2:ℝ) * (x - 1 / 2) by ring]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  rw [hrewrite] at hle
  nlinarith

lemma abs_sub_half_le_den_half_y (x y z : ℝ) :
    |y - 1 / 2| ≤ lowerZCubeCollapseDen (x,y,z) / 2 := by
  have hle : |2 * y - 1| ≤ lowerZCubeCollapseDen (x,y,z) := by
    unfold lowerZCubeCollapseDen
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hrewrite : |2 * y - 1| = 2 * |y - 1 / 2| := by
    rw [show 2 * y - 1 = (2:ℝ) * (y - 1 / 2) by ring]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  rw [hrewrite] at hle
  nlinarith

lemma lowerZCubeCollapse_mem_unitCube {p : ℝ × ℝ × ℝ} (hp : p ∈ unitCube 0 0 0) :
    lowerZCubeCollapse p ∈ unitCube 0 0 0 := by
  rcases p with ⟨x,y,z⟩
  simp only [unitCube, Set.mem_prod, Set.mem_Icc] at hp ⊢
  dsimp [lowerZCubeCollapse]
  let d : ℝ := lowerZCubeCollapseDen (x,y,z)
  have hdpos : 0 < d := by simpa [d] using lowerZCubeCollapseDen_pos (x,y,z)
  have hdle1 : d ≤ 1 := by
    simpa [d] using lowerZCubeCollapseDen_le_one_of_mem_unitCube (p := (x,y,z)) hp
  have hxabs : |x - 1 / 2| ≤ d / 2 := by simpa [d] using abs_sub_half_le_den_half x y z
  have hyabs : |y - 1 / 2| ≤ d / 2 := by simpa [d] using abs_sub_half_le_den_half_y x y z
  have hzd : (z + 1) / 2 ≤ d := by
    dsimp [d, lowerZCubeCollapseDen]
    exact le_trans (le_max_right (max |2 * x - 1| |2 * y - 1|) ((z + 1) / 2))
      (le_max_right (1 / 2 : ℝ) _)
  have hdlez1 : d ≤ z + 1 := by nlinarith [hdle1, hp.2.2.1]
  rcases abs_le.mp hxabs with ⟨hxl, hxu⟩
  rcases abs_le.mp hyabs with ⟨hyl, hyu⟩
  have hxl_div : -(1 / 2 : ℝ) ≤ (x - 1 / 2) / d := by
    have h := div_le_div_of_nonneg_right hxl (le_of_lt hdpos)
    convert h using 1 <;> field_simp [ne_of_gt hdpos]
  have hxu_div : (x - 1 / 2) / d ≤ (1 / 2 : ℝ) := by
    have h := div_le_div_of_nonneg_right hxu (le_of_lt hdpos)
    convert h using 1 <;> field_simp [ne_of_gt hdpos]
  have hyl_div : -(1 / 2 : ℝ) ≤ (y - 1 / 2) / d := by
    have h := div_le_div_of_nonneg_right hyl (le_of_lt hdpos)
    convert h using 1 <;> field_simp [ne_of_gt hdpos]
  have hyu_div : (y - 1 / 2) / d ≤ (1 / 2 : ℝ) := by
    have h := div_le_div_of_nonneg_right hyu (le_of_lt hdpos)
    convert h using 1 <;> field_simp [ne_of_gt hdpos]
  have hz0ratio : (1 : ℝ) ≤ (z + 1) / d := by
    rw [le_div_iff₀ hdpos]
    simpa using hdlez1
  have hz1ratio : (z + 1) / d ≤ (2 : ℝ) := by
    rw [div_le_iff₀ hdpos]
    nlinarith [hzd]
  have hxexpr : 1 / lowerZCubeCollapseDen (x, y, z) * (x - 1 / 2) = (x - 1 / 2) / d := by
    dsimp [d]
    ring
  have hyexpr : 1 / lowerZCubeCollapseDen (x, y, z) * (y - 1 / 2) = (y - 1 / 2) / d := by
    dsimp [d]
    ring
  have hzexpr : 1 / lowerZCubeCollapseDen (x, y, z) * (z + 1) = (z + 1) / d := by
    dsimp [d]
    ring
  constructor
  · constructor
    · rw [hxexpr]
      nlinarith [hxl_div]
    · rw [hxexpr]
      nlinarith [hxu_div]
  · constructor
    · constructor
      · rw [hyexpr]
        nlinarith [hyl_div]
      · rw [hyexpr]
        nlinarith [hyu_div]
    · constructor
      · rw [hzexpr]
        nlinarith [hz0ratio]
      · rw [hzexpr]
        nlinarith [hz1ratio]

lemma lowerZCubeCollapse_eq_self_of_den_eq_one {p : ℝ × ℝ × ℝ}
    (hden : lowerZCubeCollapseDen p = 1) : lowerZCubeCollapse p = p := by
  rcases p with ⟨x,y,z⟩
  simp [lowerZCubeCollapse, hden]

lemma lowerZCubeCollapseDen_eq_one_of_mem_unitCube_of_boundary {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube 0 0 0)
    (hbd : p.1 = 0 ∨ p.1 = 1 ∨ p.2.1 = 0 ∨ p.2.1 = 1 ∨ p.2.2 = 1) :
    lowerZCubeCollapseDen p = 1 := by
  rcases p with ⟨x,y,z⟩
  have hle : lowerZCubeCollapseDen (x,y,z) ≤ 1 :=
    lowerZCubeCollapseDen_le_one_of_mem_unitCube (p := (x,y,z)) hp
  have hge : 1 ≤ lowerZCubeCollapseDen (x,y,z) := by
    rcases hbd with hx0 | hx1 | hy0 | hy1 | hz1
    · dsimp at hx0
      calc
        (1 : ℝ) = |2 * x - 1| := by simp [hx0]
        _ ≤ lowerZCubeCollapseDen (x,y,z) := by
          unfold lowerZCubeCollapseDen
          exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
    · dsimp at hx1
      calc
        (1 : ℝ) = |2 * x - 1| := by norm_num [hx1]
        _ ≤ lowerZCubeCollapseDen (x,y,z) := by
          unfold lowerZCubeCollapseDen
          exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
    · dsimp at hy0
      calc
        (1 : ℝ) = |2 * y - 1| := by simp [hy0]
        _ ≤ lowerZCubeCollapseDen (x,y,z) := by
          unfold lowerZCubeCollapseDen
          exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
    · dsimp at hy1
      calc
        (1 : ℝ) = |2 * y - 1| := by norm_num [hy1]
        _ ≤ lowerZCubeCollapseDen (x,y,z) := by
          unfold lowerZCubeCollapseDen
          exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
    · dsimp at hz1
      calc
        (1 : ℝ) = (z + 1) / 2 := by simp [hz1]
        _ ≤ lowerZCubeCollapseDen (x,y,z) := by
          unfold lowerZCubeCollapseDen
          exact le_trans (le_max_right (max |2 * x - 1| |2 * y - 1|) ((z + 1) / 2))
            (le_max_right (1 / 2 : ℝ) _)
  exact le_antisymm hle hge

lemma lowerZCubeCollapse_eq_self_of_mem_unitCube_of_boundary {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube 0 0 0)
    (hbd : p.1 = 0 ∨ p.1 = 1 ∨ p.2.1 = 0 ∨ p.2.1 = 1 ∨ p.2.2 = 1) :
    lowerZCubeCollapse p = p := by
  exact lowerZCubeCollapse_eq_self_of_den_eq_one
    (lowerZCubeCollapseDen_eq_one_of_mem_unitCube_of_boundary hp hbd)

def unitSquare2 : Set (ℝ × ℝ) :=
  Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

def lowerEdgeSquareCollapseDen (p : ℝ × ℝ) : ℝ :=
  max (1 / 2 : ℝ) (max |2 * p.1 - 1| ((p.2 + 1) / 2))

lemma lowerEdgeSquareCollapseDen_pos (p : ℝ × ℝ) :
    0 < lowerEdgeSquareCollapseDen p := by
  unfold lowerEdgeSquareCollapseDen
  nlinarith [le_max_left (1 / 2 : ℝ) (max |2 * p.1 - 1| ((p.2 + 1) / 2))]

lemma continuous_lowerEdgeSquareCollapseDen : Continuous lowerEdgeSquareCollapseDen := by
  unfold lowerEdgeSquareCollapseDen
  fun_prop

def lowerEdgeSquareCollapse (p : ℝ × ℝ) : ℝ × ℝ :=
  let lam : ℝ := 1 / lowerEdgeSquareCollapseDen p
  (1 / 2 + lam * (p.1 - 1 / 2), -1 + lam * (p.2 + 1))

lemma continuous_lowerEdgeSquareCollapse : Continuous lowerEdgeSquareCollapse := by
  have hden : Continuous lowerEdgeSquareCollapseDen := continuous_lowerEdgeSquareCollapseDen
  have hlam : Continuous (fun p : ℝ × ℝ => 1 / lowerEdgeSquareCollapseDen p) := by
    exact continuous_const.div hden (fun p => ne_of_gt (lowerEdgeSquareCollapseDen_pos p))
  unfold lowerEdgeSquareCollapse
  fun_prop

lemma lowerEdgeSquareCollapseDen_le_one_of_mem_unitSquare2 {p : ℝ × ℝ}
    (hp : p ∈ unitSquare2) : lowerEdgeSquareCollapseDen p ≤ 1 := by
  rcases p with ⟨x,y⟩
  simp only [unitSquare2, Set.mem_prod, Set.mem_Icc] at hp
  unfold lowerEdgeSquareCollapseDen
  apply max_le
  · norm_num
  · apply max_le
    · rw [abs_le]
      constructor <;> nlinarith [hp.1.1, hp.1.2]
    · nlinarith [hp.2.1, hp.2.2]

lemma lowerEdgeSquare_abs_sub_half_le_den_half (x y : ℝ) :
    |x - 1 / 2| ≤ lowerEdgeSquareCollapseDen (x,y) / 2 := by
  have hle : |2 * x - 1| ≤ lowerEdgeSquareCollapseDen (x,y) := by
    unfold lowerEdgeSquareCollapseDen
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hrewrite : |2 * x - 1| = 2 * |x - 1 / 2| := by
    rw [show 2 * x - 1 = (2:ℝ) * (x - 1 / 2) by ring]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  rw [hrewrite] at hle
  nlinarith

lemma lowerEdgeSquareCollapse_mem_unitSquare2 {p : ℝ × ℝ} (hp : p ∈ unitSquare2) :
    lowerEdgeSquareCollapse p ∈ unitSquare2 := by
  rcases p with ⟨x,y⟩
  simp only [unitSquare2, Set.mem_prod, Set.mem_Icc] at hp ⊢
  dsimp [lowerEdgeSquareCollapse]
  let d : ℝ := lowerEdgeSquareCollapseDen (x,y)
  have hdpos : 0 < d := by simpa [d] using lowerEdgeSquareCollapseDen_pos (x,y)
  have hdle1 : d ≤ 1 := by
    simpa [d] using lowerEdgeSquareCollapseDen_le_one_of_mem_unitSquare2 (p := (x,y)) hp
  have hxabs : |x - 1 / 2| ≤ d / 2 := by
    simpa [d] using lowerEdgeSquare_abs_sub_half_le_den_half x y
  have hyd : (y + 1) / 2 ≤ d := by
    dsimp [d, lowerEdgeSquareCollapseDen]
    exact le_trans (le_max_right |2 * x - 1| ((y + 1) / 2))
      (le_max_right (1 / 2 : ℝ) _)
  have hdley1 : d ≤ y + 1 := by nlinarith [hdle1, hp.2.1]
  rcases abs_le.mp hxabs with ⟨hxl, hxu⟩
  have hxl_div : -(1 / 2 : ℝ) ≤ (x - 1 / 2) / d := by
    have h := div_le_div_of_nonneg_right hxl (le_of_lt hdpos)
    convert h using 1 <;> field_simp [ne_of_gt hdpos]
  have hxu_div : (x - 1 / 2) / d ≤ (1 / 2 : ℝ) := by
    have h := div_le_div_of_nonneg_right hxu (le_of_lt hdpos)
    convert h using 1 <;> field_simp [ne_of_gt hdpos]
  have hy0ratio : (1 : ℝ) ≤ (y + 1) / d := by
    rw [le_div_iff₀ hdpos]
    simpa using hdley1
  have hy1ratio : (y + 1) / d ≤ (2 : ℝ) := by
    rw [div_le_iff₀ hdpos]
    nlinarith [hyd]
  have hxexpr : 1 / lowerEdgeSquareCollapseDen (x, y) * (x - 1 / 2) =
      (x - 1 / 2) / d := by
    dsimp [d]
    ring
  have hyexpr : 1 / lowerEdgeSquareCollapseDen (x, y) * (y + 1) = (y + 1) / d := by
    dsimp [d]
    ring
  constructor
  · constructor
    · rw [hxexpr]
      nlinarith [hxl_div]
    · rw [hxexpr]
      nlinarith [hxu_div]
  · constructor
    · rw [hyexpr]
      nlinarith [hy0ratio]
    · rw [hyexpr]
      nlinarith [hy1ratio]

lemma lowerEdgeSquareCollapse_eq_self_of_den_eq_one {p : ℝ × ℝ}
    (hden : lowerEdgeSquareCollapseDen p = 1) : lowerEdgeSquareCollapse p = p := by
  rcases p with ⟨x,y⟩
  simp [lowerEdgeSquareCollapse, hden]

lemma lowerEdgeSquareCollapseDen_eq_one_of_mem_unitSquare2_of_boundary {p : ℝ × ℝ}
    (hp : p ∈ unitSquare2) (hbd : p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 1) :
    lowerEdgeSquareCollapseDen p = 1 := by
  rcases p with ⟨x,y⟩
  have hle : lowerEdgeSquareCollapseDen (x,y) ≤ 1 :=
    lowerEdgeSquareCollapseDen_le_one_of_mem_unitSquare2 (p := (x,y)) hp
  have hge : 1 ≤ lowerEdgeSquareCollapseDen (x,y) := by
    rcases hbd with hx0 | hx1 | hy1
    · dsimp at hx0
      calc
        (1 : ℝ) = |2 * x - 1| := by simp [hx0]
        _ ≤ lowerEdgeSquareCollapseDen (x,y) := by
          unfold lowerEdgeSquareCollapseDen
          exact le_trans (le_max_left _ _) (le_max_right _ _)
    · dsimp at hx1
      calc
        (1 : ℝ) = |2 * x - 1| := by norm_num [hx1]
        _ ≤ lowerEdgeSquareCollapseDen (x,y) := by
          unfold lowerEdgeSquareCollapseDen
          exact le_trans (le_max_left _ _) (le_max_right _ _)
    · dsimp at hy1
      calc
        (1 : ℝ) = (y + 1) / 2 := by simp [hy1]
        _ ≤ lowerEdgeSquareCollapseDen (x,y) := by
          unfold lowerEdgeSquareCollapseDen
          exact le_trans (le_max_right |2 * x - 1| ((y + 1) / 2))
            (le_max_right (1 / 2 : ℝ) _)
  exact le_antisymm hle hge

lemma lowerEdgeSquareCollapse_eq_self_of_mem_unitSquare2_of_boundary {p : ℝ × ℝ}
    (hp : p ∈ unitSquare2) (hbd : p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 1) :
    lowerEdgeSquareCollapse p = p := by
  exact lowerEdgeSquareCollapse_eq_self_of_den_eq_one
    (lowerEdgeSquareCollapseDen_eq_one_of_mem_unitSquare2_of_boundary hp hbd)

lemma hatcherStage_subset_succ_union_current_cell (m : Fin 28) :
    hatcherStage m.1 ⊆ hatcherStage (m.1 + 1) ∪ (hatcherCollapseCell m).carrier := by
  intro p hp
  rcases hp with hpH | hpU
  · left; exact Or.inl hpH
  · rcases Set.mem_iUnion.mp hpU with ⟨i, hi⟩
    by_cases hmi : m.1 ≤ i.1
    · have hmem : p ∈ (hatcherCollapseCell i).carrier := by simpa [hmi] using hi
      by_cases hei : i.1 = m.1
      · right
        have : i = m := by ext; exact hei
        simpa [this] using hmem
      · left; right
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        have hs : m.1 + 1 ≤ i.1 := by omega
        simpa [hs] using hmem
    · simp [hmi] at hi

lemma mem_Icc_zero_four_split {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 4) :
    x ∈ Icc (0 : ℝ) (0 + 1) ∨ x ∈ Icc (1 : ℝ) (1 + 1) ∨
      x ∈ Icc (2 : ℝ) (2 + 1) ∨ x ∈ Icc (3 : ℝ) (3 + 1) := by
  rcases hx with ⟨hx0, hx4⟩
  by_cases hx1 : x ≤ 1
  · exact Or.inl ⟨by simpa, by simpa using hx1⟩
  · have h1x : 1 ≤ x := le_of_not_ge hx1
    by_cases hx2 : x ≤ 2
    · exact Or.inr (Or.inl ⟨by simpa using h1x, by norm_num at hx2 ⊢; exact hx2⟩)
    · have h2x : 2 ≤ x := le_of_not_ge hx2
      by_cases hx3 : x ≤ 3
      · exact Or.inr (Or.inr (Or.inl ⟨by simpa using h2x, by norm_num at hx3 ⊢; exact hx3⟩))
      · have h3x : 3 ≤ x := le_of_not_ge hx3
        exact Or.inr (Or.inr (Or.inr ⟨by simpa using h3x, by norm_num at hx4 ⊢; exact hx4⟩))

lemma mem_Icc_zero_three_split {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 3) :
    y ∈ Icc (0 : ℝ) (0 + 1) ∨ y ∈ Icc (1 : ℝ) (1 + 1) ∨
      y ∈ Icc (2 : ℝ) (2 + 1) := by
  rcases hy with ⟨hy0, hy3⟩
  by_cases hy1 : y ≤ 1
  · exact Or.inl ⟨by simpa, by simpa using hy1⟩
  · have h1y : 1 ≤ y := le_of_not_ge hy1
    by_cases hy2 : y ≤ 2
    · exact Or.inr (Or.inl ⟨by simpa using h1y, by norm_num at hy2 ⊢; exact hy2⟩)
    · have h2y : 2 ≤ y := le_of_not_ge hy2
      exact Or.inr (Or.inr ⟨by simpa using h2y, by norm_num at hy3 ⊢; exact hy3⟩)

lemma mem_Icc_zero_two_split {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 2) :
    z ∈ Icc (0 : ℝ) (0 + 1) ∨ z ∈ Icc (1 : ℝ) (1 + 1) := by
  rcases hz with ⟨hz0, hz2⟩
  by_cases hz1 : z ≤ 1
  · exact Or.inl ⟨by simpa, by simpa using hz1⟩
  · have h1z : 1 ≤ z := le_of_not_ge hz1
    exact Or.inr ⟨by simpa using h1z, by norm_num at hz2 ⊢; exact hz2⟩

lemma mem_unitCube_of_mem_Icc {i j k x y z : ℝ}
    (hx : x ∈ Icc i (i + 1)) (hy : y ∈ Icc j (j + 1)) (hz : z ∈ Icc k (k + 1)) :
    (x, y, z) ∈ unitCube i j k := by
  change x ∈ Icc i (i + 1) ∧ (y, z) ∈ Icc j (j + 1) ×ˢ Icc k (k + 1)
  exact ⟨hx, ⟨hy, hz⟩⟩

lemma mem_hatcherStage_zero_of_mem_collapseCell (m : Fin 28) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ (hatcherCollapseCell m).carrier) : p ∈ hatcherStage 0 := by
  right
  exact Set.mem_iUnion.mpr ⟨m, by simpa using hp⟩

lemma hatcherStage_zero_eq_ambientBox : hatcherStage 0 = HouseAmbientBox := by
  ext p
  constructor
  · intro hp
    exact hatcherStage_subset_ambientBox 0 hp
  · intro hp
    rcases p with ⟨x,y,z⟩
    simp only [HouseAmbientBox, Set.mem_prod, Set.mem_Icc] at hp
    have hxsplit := mem_Icc_zero_four_split (x := x) hp.1
    have hysplit := mem_Icc_zero_three_split (y := y) hp.2.1
    have hzsplit := mem_Icc_zero_two_split (z := z) hp.2.2
    rcases hxsplit with hx0 | hx1 | hx2 | hx3
    · rcases hysplit with hy0 | hy1 | hy2
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨11, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx0) (by simpa using hy0) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨18, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx0) (by simpa using hy0) (by simpa using hz1))
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨15, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx0) (by simpa using hy1) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨20, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx0) (by simpa using hy1) (by simpa using hz1))
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨19, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx0) (by norm_num at hy2 ⊢; exact hy2) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨22, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx0) (by norm_num at hy2 ⊢; exact hy2) (by simpa using hz1))
    · rcases hysplit with hy0 | hy1 | hy2
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨6, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx1) (by simpa using hy0) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨8, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx1) (by simpa using hy0) (by simpa using hz1))
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨5, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx1) (by simpa using hy1) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨4, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx1) (by simpa using hy1) (by simpa using hz1))
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨13, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx1) (by norm_num at hy2 ⊢; exact hy2) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨26, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by simpa using hx1) (by norm_num at hy2 ⊢; exact hy2) (by simpa using hz1))
    · rcases hysplit with hy0 | hy1 | hy2
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨9, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx2 ⊢; exact hx2) (by simpa using hy0) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨2, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx2 ⊢; exact hx2) (by simpa using hy0) (by simpa using hz1))
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨0, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx2 ⊢; exact hx2) (by simpa using hy1) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨1, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx2 ⊢; exact hx2) (by simpa using hy1) (by simpa using hz1))
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨27, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx2 ⊢; exact hx2) (by norm_num at hy2 ⊢; exact hy2) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨7, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx2 ⊢; exact hx2) (by norm_num at hy2 ⊢; exact hy2) (by simpa using hz1))
    · rcases hysplit with hy0 | hy1 | hy2
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨17, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx3 ⊢; exact hx3) (by simpa using hy0) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨3, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx3 ⊢; exact hx3) (by simpa using hy0) (by simpa using hz1))
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨24, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx3 ⊢; exact hx3) (by simpa using hy1) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨12, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx3 ⊢; exact hx3) (by simpa using hy1) (by simpa using hz1))
      · rcases hzsplit with hz0 | hz1
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨25, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx3 ⊢; exact hx3) (by norm_num at hy2 ⊢; exact hy2) (by simpa using hz0))
        · apply mem_hatcherStage_zero_of_mem_collapseCell (⟨10, by norm_num⟩ : Fin 28)
          simpa [hatcherCollapseCell, CubicalTopCell.carrier] using
            (mem_unitCube_of_mem_Icc (by norm_num at hx3 ⊢; exact hx3) (by norm_num at hy2 ⊢; exact hy2) (by simpa using hz1))

lemma lowerZCubeCollapse_mem_nonfree_boundary {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube 0 0 0) :
    (lowerZCubeCollapse p).1 = 0 ∨ (lowerZCubeCollapse p).1 = 1 ∨
      (lowerZCubeCollapse p).2.1 = 0 ∨ (lowerZCubeCollapse p).2.1 = 1 ∨
        (lowerZCubeCollapse p).2.2 = 1 := by
  rcases p with ⟨x,y,z⟩
  simp only [unitCube, Set.mem_prod, Set.mem_Icc] at hp
  dsimp [lowerZCubeCollapse]
  let d : ℝ := lowerZCubeCollapseDen (x,y,z)
  have hdpos : 0 < d := by simpa [d] using lowerZCubeCollapseDen_pos (x,y,z)
  have hxle : |2 * x - 1| ≤ d := by
    dsimp [d, lowerZCubeCollapseDen]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hyle : |2 * y - 1| ≤ d := by
    dsimp [d, lowerZCubeCollapseDen]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hzle : (z + 1) / 2 ≤ d := by
    dsimp [d, lowerZCubeCollapseDen]
    exact le_trans (le_max_right (max |2 * x - 1| |2 * y - 1|) ((z + 1) / 2))
      (le_max_right (1 / 2 : ℝ) _)
  have hhalfle : (1 / 2 : ℝ) ≤ d := by
    dsimp [d, lowerZCubeCollapseDen]
    exact le_max_left _ _
  have hdx_or : d = (1 / 2 : ℝ) ∨ d = |2 * x - 1| ∨ d = |2 * y - 1| ∨ d = (z + 1) / 2 := by
    dsimp [d, lowerZCubeCollapseDen]
    let a : ℝ := (1 / 2 : ℝ)
    let b : ℝ := |2 * x - 1|
    let c : ℝ := |2 * y - 1|
    let e : ℝ := (z + 1) / 2
    change max a (max (max b c) e) = a ∨
      max a (max (max b c) e) = b ∨
      max a (max (max b c) e) = c ∨
      max a (max (max b c) e) = e
    rcases le_total (max (max b c) e) a with hMa | haM
    · left; exact max_eq_left hMa
    · right
      have htop : max a (max (max b c) e) = max (max b c) e := max_eq_right haM
      rcases le_total e (max b c) with he | hbc
      · have hM : max (max b c) e = max b c := max_eq_left he
        rcases le_total c b with hcb | hbc'
        · left
          rw [htop, hM, max_eq_left hcb]
        · right; left
          rw [htop, hM, max_eq_right hbc']
      · right; right
        rw [htop, max_eq_right hbc]
  rcases hdx_or with hdhalf | hdx | hdy | hdz
  · right; right; right; right
    have hz0 : z = 0 := by
      have : (z + 1) / 2 ≤ (1 / 2 : ℝ) := by simpa [hdhalf] using hzle
      nlinarith [hp.2.2.1]
    field_simp [d, hdhalf]
    nlinarith
  · have hrewrite : |2 * x - 1| = 2 * |x - 1 / 2| := by
      rw [show 2 * x - 1 = (2:ℝ) * (x - 1 / 2) by ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hdabs : d = 2 * |x - 1 / 2| := by rw [hdx, hrewrite]
    rcases abs_choice (x - 1 / 2) with hxcase | hxcase
    · right; left
      have hdeq : d = 2 * (x - 1 / 2) := by rw [hdabs, hxcase]
      field_simp [d, ne_of_gt hdpos]
      nlinarith [hdeq]
    · left
      have hdeq : d = 2 * (-(x - 1 / 2)) := by rw [hdabs, hxcase]
      field_simp [d, ne_of_gt hdpos]
      nlinarith [hdeq]
  · have hrewrite : |2 * y - 1| = 2 * |y - 1 / 2| := by
      rw [show 2 * y - 1 = (2:ℝ) * (y - 1 / 2) by ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hdabs : d = 2 * |y - 1 / 2| := by rw [hdy, hrewrite]
    rcases abs_choice (y - 1 / 2) with hycase | hycase
    · right; right; right; left
      have hdeq : d = 2 * (y - 1 / 2) := by rw [hdabs, hycase]
      field_simp [d, ne_of_gt hdpos]
      nlinarith [hdeq]
    · right; right; left
      have hdeq : d = 2 * (-(y - 1 / 2)) := by rw [hdabs, hycase]
      field_simp [d, ne_of_gt hdpos]
      nlinarith [hdeq]
  · right; right; right; right
    field_simp [d, ne_of_gt hdpos]
    nlinarith [hdz]

lemma lowerEdgeSquareCollapse_mem_nonfree_boundary {p : ℝ × ℝ}
    (hp : p ∈ unitSquare2) :
    (lowerEdgeSquareCollapse p).1 = 0 ∨ (lowerEdgeSquareCollapse p).1 = 1 ∨
      (lowerEdgeSquareCollapse p).2 = 1 := by
  rcases p with ⟨x,y⟩
  simp only [unitSquare2, Set.mem_prod, Set.mem_Icc] at hp
  dsimp [lowerEdgeSquareCollapse]
  let d : ℝ := lowerEdgeSquareCollapseDen (x,y)
  have hdpos : 0 < d := by simpa [d] using lowerEdgeSquareCollapseDen_pos (x,y)
  have hyle : (y + 1) / 2 ≤ d := by
    dsimp [d, lowerEdgeSquareCollapseDen]
    exact le_trans (le_max_right |2 * x - 1| ((y + 1) / 2)) (le_max_right (1 / 2 : ℝ) _)
  have hchoice : d = (1 / 2 : ℝ) ∨ d = |2 * x - 1| ∨ d = (y + 1) / 2 := by
    dsimp [d, lowerEdgeSquareCollapseDen]
    let a : ℝ := (1 / 2 : ℝ)
    let b : ℝ := |2 * x - 1|
    let c : ℝ := (y + 1) / 2
    change max a (max b c) = a ∨ max a (max b c) = b ∨ max a (max b c) = c
    rcases le_total (max b c) a with hba | hab
    · left; exact max_eq_left hba
    · right
      have htop : max a (max b c) = max b c := max_eq_right hab
      rcases le_total c b with hcb | hbc
      · left; rw [htop, max_eq_left hcb]
      · right; rw [htop, max_eq_right hbc]
  rcases hchoice with hdhalf | hdx | hdy
  · right; right
    have hy0 : y = 0 := by
      have : (y + 1) / 2 ≤ (1 / 2 : ℝ) := by simpa [hdhalf] using hyle
      nlinarith [hp.2.1]
    field_simp [d, hdhalf]
    nlinarith
  · have hrewrite : |2 * x - 1| = 2 * |x - 1 / 2| := by
      rw [show 2 * x - 1 = (2:ℝ) * (x - 1 / 2) by ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hdabs : d = 2 * |x - 1 / 2| := by rw [hdx, hrewrite]
    rcases abs_choice (x - 1 / 2) with hxcase | hxcase
    · right; left
      have hdeq : d = 2 * (x - 1 / 2) := by rw [hdabs, hxcase]
      field_simp [d, ne_of_gt hdpos]
      nlinarith [hdeq]
    · left
      have hdeq : d = 2 * (-(x - 1 / 2)) := by rw [hdabs, hxcase]
      field_simp [d, ne_of_gt hdpos]
      nlinarith [hdeq]
  · right; right
    field_simp [d, ne_of_gt hdpos]
    nlinarith [hdy]

lemma hatcherStage_succ_subset_stage (m : Fin 28) :
    hatcherStage (m.1 + 1) ⊆ hatcherStage m.1 := by
  intro p hp
  rcases hp with hpH | hpU
  · exact Or.inl hpH
  · right
    rcases Set.mem_iUnion.mp hpU with ⟨i, hi⟩
    by_cases hsucc : m.1 + 1 ≤ i.1
    · have hmem : p ∈ (hatcherCollapseCell i).carrier := by simpa [hsucc] using hi
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      have hm : m.1 ≤ i.1 := by omega
      simpa [hm] using hmem
    · simp [hsucc] at hi

def hatcherStageSuccInclusion (m : Fin 28) :
    C(hatcherStage (m.1 + 1), hatcherStage m.1) where
  toFun p := ⟨(p : ℝ × ℝ × ℝ), hatcherStage_succ_subset_stage m p.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

lemma closedCover_if_mem_continuousOn {α : Type*} [TopologicalSpace α]
    {s t c : Set α} {f : α → α} [∀ x, Decidable (x ∈ t)]
    (hs : s ⊆ t ∪ c) (ht : IsClosed t) (hc : IsClosed c)
    (hf : ContinuousOn f c) (hfix : ∀ x, x ∈ t → x ∈ c → f x = x) :
    ContinuousOn (fun x => if x ∈ t then x else f x) s := by
  have hT : ContinuousOn (fun x => if x ∈ t then x else f x) t := by
    exact continuousOn_id.congr (fun x hx => by simp [hx])
  have hC : ContinuousOn (fun x => if x ∈ t then x else f x) c := by
    exact hf.congr (fun x hx => by
      by_cases hxt : x ∈ t
      · simp [hxt, hfix x hxt hx]
      · simp [hxt])
  exact (hT.union_of_isClosed hC ht hc).mono hs

def closedCoverRetraction {α : Type*} [TopologicalSpace α]
    (s t c : Set α) [∀ x, Decidable (x ∈ t)] (f : α → α)
    (hs : s ⊆ t ∪ c) (ht : IsClosed t) (hc : IsClosed c)
    (hf : ContinuousOn f c) (hmap : Set.MapsTo f c t)
    (hfix : ∀ x, x ∈ t → x ∈ c → f x = x) : C(s, t) where
  toFun p :=
    ⟨if (p : α) ∈ t then (p : α) else f (p : α), by
      by_cases hpt : (p : α) ∈ t
      · simpa [hpt]
      · have hpc : (p : α) ∈ c := by
          rcases hs p.2 with hpT | hpC
          · exact False.elim (hpt hpT)
          · exact hpC
        simpa [hpt] using hmap hpc⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (closedCover_if_mem_continuousOn (s := s) (t := t) (c := c)
      (f := f) hs ht hc hf hfix).restrict

def hatcherStageStepRetractionOfLocal (m : Fin 28) (f : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ)
    (hf : ContinuousOn f (hatcherCollapseCell m).carrier)
    (hmap : Set.MapsTo f (hatcherCollapseCell m).carrier (hatcherStage (m.1 + 1)))
    (hfix : ∀ p, p ∈ hatcherStage (m.1 + 1) →
      p ∈ (hatcherCollapseCell m).carrier → f p = p) :
    C(hatcherStage m.1, hatcherStage (m.1 + 1)) := by
  classical
  exact closedCoverRetraction (hatcherStage m.1) (hatcherStage (m.1 + 1))
    (hatcherCollapseCell m).carrier f
    (hatcherStage_subset_succ_union_current_cell m) (isClosed_hatcherStage (m.1 + 1))
    (hatcherCollapseCell m).isClosed_carrier hf hmap hfix

lemma hatcherStageStepRetractionOfLocal_comp (m : Fin 28)
    (f : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ)
    (hf : ContinuousOn f (hatcherCollapseCell m).carrier)
    (hmap : Set.MapsTo f (hatcherCollapseCell m).carrier (hatcherStage (m.1 + 1)))
    (hfix : ∀ p, p ∈ hatcherStage (m.1 + 1) →
      p ∈ (hatcherCollapseCell m).carrier → f p = p) :
    (hatcherStageStepRetractionOfLocal m f hf hmap hfix).comp
        (hatcherStageSuccInclusion m) =
      ContinuousMap.id (hatcherStage (m.1 + 1)) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  dsimp [hatcherStageStepRetractionOfLocal, hatcherStageSuccInclusion, closedCoverRetraction]
  simp [p.2]

def lowerZTranslatedCubeCollapse (i j k : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let q := lowerZCubeCollapse (p.1 - i, p.2.1 - j, p.2.2 - k)
  (q.1 + i, q.2.1 + j, q.2.2 + k)

lemma continuous_lowerZTranslatedCubeCollapse (i j k : ℝ) :
    Continuous (lowerZTranslatedCubeCollapse i j k) := by
  let F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p =>
    lowerZCubeCollapse (p.1 - i, p.2.1 - j, p.2.2 - k)
  have hF : Continuous F := continuous_lowerZCubeCollapse.comp (by fun_prop)
  change Continuous (fun p => ((F p).1 + i, (F p).2.1 + j, (F p).2.2 + k))
  fun_prop

lemma lowerZTranslatedCubeCollapse_translate_mem_unitCube {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube i j k) :
    (p.1 - i, p.2.1 - j, p.2.2 - k) ∈ unitCube 0 0 0 := by
  rcases p with ⟨x,y,z⟩
  simp only [unitCube, Set.mem_prod, Set.mem_Icc] at hp ⊢
  constructor
  · constructor <;> nlinarith [hp.1.1, hp.1.2]
  · constructor
    · constructor <;> nlinarith [hp.2.1.1, hp.2.1.2]
    · constructor <;> nlinarith [hp.2.2.1, hp.2.2.2]

lemma lowerZTranslatedCubeCollapse_mem_cell {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube i j k) :
    lowerZTranslatedCubeCollapse i j k p ∈ unitCube i j k := by
  have hq : lowerZCubeCollapse (p.1 - i, p.2.1 - j, p.2.2 - k) ∈ unitCube 0 0 0 :=
    lowerZCubeCollapse_mem_unitCube (lowerZTranslatedCubeCollapse_translate_mem_unitCube hp)
  simp only [unitCube, Set.mem_prod, Set.mem_Icc] at hq ⊢
  simp [lowerZTranslatedCubeCollapse]
  constructor
  · constructor <;> nlinarith [hq.1.1, hq.1.2]
  · constructor
    · constructor <;> nlinarith [hq.2.1.1, hq.2.1.2]
    · constructor <;> nlinarith [hq.2.2.1, hq.2.2.2]

lemma lowerZTranslatedCubeCollapse_boundary_or {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube i j k) :
    (lowerZTranslatedCubeCollapse i j k p).1 = i ∨
      (lowerZTranslatedCubeCollapse i j k p).1 = i + 1 ∨
      (lowerZTranslatedCubeCollapse i j k p).2.1 = j ∨
      (lowerZTranslatedCubeCollapse i j k p).2.1 = j + 1 ∨
      (lowerZTranslatedCubeCollapse i j k p).2.2 = k + 1 := by
  let q0 : ℝ × ℝ × ℝ := (p.1 - i, p.2.1 - j, p.2.2 - k)
  have hq0 : q0 ∈ unitCube 0 0 0 := by
    simpa [q0] using lowerZTranslatedCubeCollapse_translate_mem_unitCube hp
  have hbd := lowerZCubeCollapse_mem_nonfree_boundary hq0
  let q : ℝ × ℝ × ℝ := lowerZCubeCollapse q0
  have hrow : lowerZTranslatedCubeCollapse i j k p = (q.1 + i, q.2.1 + j, q.2.2 + k) := by
    simp [lowerZTranslatedCubeCollapse, q, q0]
  rw [hrow]
  simpa [q] using hbd.imp (by intro h; nlinarith [h])
    (fun h => h.imp (by intro h'; nlinarith [h'])
      (fun h => h.imp (by intro h'; nlinarith [h'])
        (fun h => h.imp (by intro h'; nlinarith [h']) (by intro h'; nlinarith [h']))))

lemma lowerZTranslatedCubeCollapse_eq_self_of_boundary {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube i j k)
    (hbd : p.1 = i ∨ p.1 = i + 1 ∨ p.2.1 = j ∨ p.2.1 = j + 1 ∨ p.2.2 = k + 1) :
    lowerZTranslatedCubeCollapse i j k p = p := by
  have hq0 : (p.1 - i, p.2.1 - j, p.2.2 - k) ∈ unitCube 0 0 0 :=
    lowerZTranslatedCubeCollapse_translate_mem_unitCube hp
  have hbd0 : (p.1 - i, p.2.1 - j, p.2.2 - k).1 = 0 ∨
      (p.1 - i, p.2.1 - j, p.2.2 - k).1 = 1 ∨
      (p.1 - i, p.2.1 - j, p.2.2 - k).2.1 = 0 ∨
      (p.1 - i, p.2.1 - j, p.2.2 - k).2.1 = 1 ∨
      (p.1 - i, p.2.1 - j, p.2.2 - k).2.2 = 1 := by
    rcases hbd with hx0 | hx1 | hy0 | hy1 | hz1
    · left; dsimp; nlinarith
    · right; left; dsimp; nlinarith
    · right; right; left; dsimp; nlinarith
    · right; right; right; left; dsimp; nlinarith
    · right; right; right; right; dsimp; nlinarith
  have hcollapse := lowerZCubeCollapse_eq_self_of_mem_unitCube_of_boundary hq0 hbd0
  rcases p with ⟨x,y,z⟩
  simpa [lowerZTranslatedCubeCollapse, hcollapse]

inductive CubeFaceDir where
  | xLow | xHigh | yLow | yHigh | zLow | zHigh
  deriving DecidableEq

def cubeFaceCollapse (d : CubeFaceDir) (i j k : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  match d with
  | .zLow => lowerZTranslatedCubeCollapse i j k p
  | .zHigh =>
      let q := lowerZCubeCollapse (p.1 - i, p.2.1 - j, k + 1 - p.2.2)
      (q.1 + i, q.2.1 + j, k + 1 - q.2.2)
  | .yLow =>
      let q := lowerZCubeCollapse (p.1 - i, p.2.2 - k, p.2.1 - j)
      (q.1 + i, q.2.2 + j, q.2.1 + k)
  | .yHigh =>
      let q := lowerZCubeCollapse (p.1 - i, p.2.2 - k, j + 1 - p.2.1)
      (q.1 + i, j + 1 - q.2.2, q.2.1 + k)
  | .xLow =>
      let q := lowerZCubeCollapse (p.2.1 - j, p.2.2 - k, p.1 - i)
      (q.2.2 + i, q.1 + j, q.2.1 + k)
  | .xHigh =>
      let q := lowerZCubeCollapse (p.2.1 - j, p.2.2 - k, i + 1 - p.1)
      (i + 1 - q.2.2, q.1 + j, q.2.1 + k)

def cubeFaceNonfreeBoundary (d : CubeFaceDir) (i j k : ℝ) : Set (ℝ × ℝ × ℝ) :=
  match d with
  | .zLow => {p | p.1 = i ∨ p.1 = i + 1 ∨ p.2.1 = j ∨ p.2.1 = j + 1 ∨ p.2.2 = k + 1}
  | .zHigh => {p | p.1 = i ∨ p.1 = i + 1 ∨ p.2.1 = j ∨ p.2.1 = j + 1 ∨ p.2.2 = k}
  | .yLow => {p | p.1 = i ∨ p.1 = i + 1 ∨ p.2.2 = k ∨ p.2.2 = k + 1 ∨ p.2.1 = j + 1}
  | .yHigh => {p | p.1 = i ∨ p.1 = i + 1 ∨ p.2.2 = k ∨ p.2.2 = k + 1 ∨ p.2.1 = j}
  | .xLow => {p | p.2.1 = j ∨ p.2.1 = j + 1 ∨ p.2.2 = k ∨ p.2.2 = k + 1 ∨ p.1 = i + 1}
  | .xHigh => {p | p.2.1 = j ∨ p.2.1 = j + 1 ∨ p.2.2 = k ∨ p.2.2 = k + 1 ∨ p.1 = i}

lemma continuous_cubeFaceCollapse (d : CubeFaceDir) (i j k : ℝ) :
    Continuous (cubeFaceCollapse d i j k) := by
  cases d
  · change Continuous (fun p : ℝ × ℝ × ℝ =>
      let q := lowerZCubeCollapse (p.2.1 - j, p.2.2 - k, p.1 - i)
      (q.2.2 + i, q.1 + j, q.2.1 + k))
    let F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p =>
      lowerZCubeCollapse (p.2.1 - j, p.2.2 - k, p.1 - i)
    have hF : Continuous F := continuous_lowerZCubeCollapse.comp (by fun_prop)
    change Continuous (fun p => ((F p).2.2 + i, (F p).1 + j, (F p).2.1 + k))
    fun_prop
  · change Continuous (fun p : ℝ × ℝ × ℝ =>
      let q := lowerZCubeCollapse (p.2.1 - j, p.2.2 - k, i + 1 - p.1)
      (i + 1 - q.2.2, q.1 + j, q.2.1 + k))
    let F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p =>
      lowerZCubeCollapse (p.2.1 - j, p.2.2 - k, i + 1 - p.1)
    have hF : Continuous F := continuous_lowerZCubeCollapse.comp (by fun_prop)
    change Continuous (fun p => (i + 1 - (F p).2.2, (F p).1 + j, (F p).2.1 + k))
    fun_prop
  · change Continuous (fun p : ℝ × ℝ × ℝ =>
      let q := lowerZCubeCollapse (p.1 - i, p.2.2 - k, p.2.1 - j)
      (q.1 + i, q.2.2 + j, q.2.1 + k))
    let F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p =>
      lowerZCubeCollapse (p.1 - i, p.2.2 - k, p.2.1 - j)
    have hF : Continuous F := continuous_lowerZCubeCollapse.comp (by fun_prop)
    change Continuous (fun p => ((F p).1 + i, (F p).2.2 + j, (F p).2.1 + k))
    fun_prop
  · change Continuous (fun p : ℝ × ℝ × ℝ =>
      let q := lowerZCubeCollapse (p.1 - i, p.2.2 - k, j + 1 - p.2.1)
      (q.1 + i, j + 1 - q.2.2, q.2.1 + k))
    let F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p =>
      lowerZCubeCollapse (p.1 - i, p.2.2 - k, j + 1 - p.2.1)
    have hF : Continuous F := continuous_lowerZCubeCollapse.comp (by fun_prop)
    change Continuous (fun p => ((F p).1 + i, j + 1 - (F p).2.2, (F p).2.1 + k))
    fun_prop
  · exact continuous_lowerZTranslatedCubeCollapse i j k
  · change Continuous (fun p : ℝ × ℝ × ℝ =>
      let q := lowerZCubeCollapse (p.1 - i, p.2.1 - j, k + 1 - p.2.2)
      (q.1 + i, q.2.1 + j, k + 1 - q.2.2))
    let F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p =>
      lowerZCubeCollapse (p.1 - i, p.2.1 - j, k + 1 - p.2.2)
    have hF : Continuous F := continuous_lowerZCubeCollapse.comp (by fun_prop)
    change Continuous (fun p => ((F p).1 + i, (F p).2.1 + j, k + 1 - (F p).2.2))
    fun_prop

lemma cubeFaceCollapse_std_mem (d : CubeFaceDir) {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube i j k) :
    match d with
    | .zLow => (p.1 - i, p.2.1 - j, p.2.2 - k) ∈ unitCube 0 0 0
    | .zHigh => (p.1 - i, p.2.1 - j, k + 1 - p.2.2) ∈ unitCube 0 0 0
    | .yLow => (p.1 - i, p.2.2 - k, p.2.1 - j) ∈ unitCube 0 0 0
    | .yHigh => (p.1 - i, p.2.2 - k, j + 1 - p.2.1) ∈ unitCube 0 0 0
    | .xLow => (p.2.1 - j, p.2.2 - k, p.1 - i) ∈ unitCube 0 0 0
    | .xHigh => (p.2.1 - j, p.2.2 - k, i + 1 - p.1) ∈ unitCube 0 0 0 := by
  cases d <;> rcases p with ⟨x,y,z⟩ <;>
    simp [unitCube, Set.mem_prod, Set.mem_Icc] at hp ⊢ <;> grind

lemma cubeFaceCollapse_mem_cell {d : CubeFaceDir} {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube i j k) : cubeFaceCollapse d i j k p ∈ unitCube i j k := by
  rcases p with ⟨x,y,z⟩
  cases d
  · have hq := lowerZCubeCollapse_mem_unitCube (cubeFaceCollapse_std_mem (d := CubeFaceDir.xLow) hp)
    simp only [unitCube, Set.mem_prod, Set.mem_Icc] at hq ⊢
    simp [cubeFaceCollapse]
    constructor
    · constructor <;> nlinarith [hq.2.2.1, hq.2.2.2]
    · constructor
      · constructor <;> nlinarith [hq.1.1, hq.1.2]
      · constructor <;> nlinarith [hq.2.1.1, hq.2.1.2]
  · have hq := lowerZCubeCollapse_mem_unitCube (cubeFaceCollapse_std_mem (d := CubeFaceDir.xHigh) hp)
    simp only [unitCube, Set.mem_prod, Set.mem_Icc] at hq ⊢
    simp [cubeFaceCollapse]
    constructor
    · constructor <;> nlinarith [hq.2.2.1, hq.2.2.2]
    · constructor
      · constructor <;> nlinarith [hq.1.1, hq.1.2]
      · constructor <;> nlinarith [hq.2.1.1, hq.2.1.2]
  · have hq := lowerZCubeCollapse_mem_unitCube (cubeFaceCollapse_std_mem (d := CubeFaceDir.yLow) hp)
    simp only [unitCube, Set.mem_prod, Set.mem_Icc] at hq ⊢
    simp [cubeFaceCollapse]
    constructor
    · constructor <;> nlinarith [hq.1.1, hq.1.2]
    · constructor
      · constructor <;> nlinarith [hq.2.2.1, hq.2.2.2]
      · constructor <;> nlinarith [hq.2.1.1, hq.2.1.2]
  · have hq := lowerZCubeCollapse_mem_unitCube (cubeFaceCollapse_std_mem (d := CubeFaceDir.yHigh) hp)
    simp only [unitCube, Set.mem_prod, Set.mem_Icc] at hq ⊢
    simp [cubeFaceCollapse]
    constructor
    · constructor <;> nlinarith [hq.1.1, hq.1.2]
    · constructor
      · constructor <;> nlinarith [hq.2.2.1, hq.2.2.2]
      · constructor <;> nlinarith [hq.2.1.1, hq.2.1.2]
  · simpa [cubeFaceCollapse] using lowerZTranslatedCubeCollapse_mem_cell (i := i) (j := j) (k := k) hp
  · have hq := lowerZCubeCollapse_mem_unitCube (cubeFaceCollapse_std_mem (d := CubeFaceDir.zHigh) hp)
    simp only [unitCube, Set.mem_prod, Set.mem_Icc] at hq ⊢
    simp [cubeFaceCollapse]
    constructor
    · constructor <;> nlinarith [hq.1.1, hq.1.2]
    · constructor
      · constructor <;> nlinarith [hq.2.1.1, hq.2.1.2]
      · constructor <;> nlinarith [hq.2.2.1, hq.2.2.2]

lemma cubeFaceCollapse_mem_nonfreeBoundary {d : CubeFaceDir} {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube i j k) : cubeFaceCollapse d i j k p ∈ cubeFaceNonfreeBoundary d i j k := by
  rcases p with ⟨x,y,z⟩
  cases d
  · have hbd := lowerZCubeCollapse_mem_nonfree_boundary (cubeFaceCollapse_std_mem (d := CubeFaceDir.xLow) hp)
    simp [cubeFaceCollapse, cubeFaceNonfreeBoundary] at hbd ⊢; grind
  · have hbd := lowerZCubeCollapse_mem_nonfree_boundary (cubeFaceCollapse_std_mem (d := CubeFaceDir.xHigh) hp)
    simp [cubeFaceCollapse, cubeFaceNonfreeBoundary] at hbd ⊢; grind
  · have hbd := lowerZCubeCollapse_mem_nonfree_boundary (cubeFaceCollapse_std_mem (d := CubeFaceDir.yLow) hp)
    simp [cubeFaceCollapse, cubeFaceNonfreeBoundary] at hbd ⊢; grind
  · have hbd := lowerZCubeCollapse_mem_nonfree_boundary (cubeFaceCollapse_std_mem (d := CubeFaceDir.yHigh) hp)
    simp [cubeFaceCollapse, cubeFaceNonfreeBoundary] at hbd ⊢; grind
  · simpa [cubeFaceCollapse, cubeFaceNonfreeBoundary] using
      lowerZTranslatedCubeCollapse_boundary_or (i := i) (j := j) (k := k) hp
  · have hbd := lowerZCubeCollapse_mem_nonfree_boundary (cubeFaceCollapse_std_mem (d := CubeFaceDir.zHigh) hp)
    simp [cubeFaceCollapse, cubeFaceNonfreeBoundary] at hbd ⊢; grind

lemma cubeFaceCollapse_eq_self_of_nonfreeBoundary {d : CubeFaceDir} {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ unitCube i j k) (hbd : p ∈ cubeFaceNonfreeBoundary d i j k) :
    cubeFaceCollapse d i j k p = p := by
  rcases p with ⟨x,y,z⟩
  cases d
  · have hstd := cubeFaceCollapse_std_mem (d := CubeFaceDir.xLow) hp
    have hbdstd : (y - j, z - k, x - i).1 = 0 ∨ (y - j, z - k, x - i).1 = 1 ∨
        (y - j, z - k, x - i).2.1 = 0 ∨ (y - j, z - k, x - i).2.1 = 1 ∨
        (y - j, z - k, x - i).2.2 = 1 := by
      simp [cubeFaceNonfreeBoundary] at hbd ⊢; grind
    have hfix := lowerZCubeCollapse_eq_self_of_mem_unitCube_of_boundary hstd hbdstd
    simp [cubeFaceCollapse, hfix]
  · have hstd := cubeFaceCollapse_std_mem (d := CubeFaceDir.xHigh) hp
    have hbdstd : (y - j, z - k, i + 1 - x).1 = 0 ∨ (y - j, z - k, i + 1 - x).1 = 1 ∨
        (y - j, z - k, i + 1 - x).2.1 = 0 ∨ (y - j, z - k, i + 1 - x).2.1 = 1 ∨
        (y - j, z - k, i + 1 - x).2.2 = 1 := by
      simp [cubeFaceNonfreeBoundary] at hbd ⊢; grind
    have hfix := lowerZCubeCollapse_eq_self_of_mem_unitCube_of_boundary hstd hbdstd
    simp [cubeFaceCollapse, hfix]
  · have hstd := cubeFaceCollapse_std_mem (d := CubeFaceDir.yLow) hp
    have hbdstd : (x - i, z - k, y - j).1 = 0 ∨ (x - i, z - k, y - j).1 = 1 ∨
        (x - i, z - k, y - j).2.1 = 0 ∨ (x - i, z - k, y - j).2.1 = 1 ∨
        (x - i, z - k, y - j).2.2 = 1 := by
      simp [cubeFaceNonfreeBoundary] at hbd ⊢; grind
    have hfix := lowerZCubeCollapse_eq_self_of_mem_unitCube_of_boundary hstd hbdstd
    simp [cubeFaceCollapse, hfix]
  · have hstd := cubeFaceCollapse_std_mem (d := CubeFaceDir.yHigh) hp
    have hbdstd : (x - i, z - k, j + 1 - y).1 = 0 ∨ (x - i, z - k, j + 1 - y).1 = 1 ∨
        (x - i, z - k, j + 1 - y).2.1 = 0 ∨ (x - i, z - k, j + 1 - y).2.1 = 1 ∨
        (x - i, z - k, j + 1 - y).2.2 = 1 := by
      simp [cubeFaceNonfreeBoundary] at hbd ⊢; grind
    have hfix := lowerZCubeCollapse_eq_self_of_mem_unitCube_of_boundary hstd hbdstd
    simp [cubeFaceCollapse, hfix]
  · simpa [cubeFaceCollapse, cubeFaceNonfreeBoundary] using
      lowerZTranslatedCubeCollapse_eq_self_of_boundary (i := i) (j := j) (k := k) hp hbd
  · have hstd := cubeFaceCollapse_std_mem (d := CubeFaceDir.zHigh) hp
    have hbdstd : (x - i, y - j, k + 1 - z).1 = 0 ∨ (x - i, y - j, k + 1 - z).1 = 1 ∨
        (x - i, y - j, k + 1 - z).2.1 = 0 ∨ (x - i, y - j, k + 1 - z).2.1 = 1 ∨
        (x - i, y - j, k + 1 - z).2.2 = 1 := by
      simp [cubeFaceNonfreeBoundary] at hbd ⊢; grind
    have hfix := lowerZCubeCollapse_eq_self_of_mem_unitCube_of_boundary hstd hbdstd
    simp [cubeFaceCollapse, hfix]

inductive SquareEdgeDir where
  | xFaceYLow | yFaceXLow | yFaceXHigh
  deriving DecidableEq

def squareEdgeCollapse (d : SquareEdgeDir) (i j k : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  match d with
  | .xFaceYLow =>
      let q := lowerEdgeSquareCollapse (p.2.2 - k, p.2.1 - j)
      (i, q.2 + j, q.1 + k)
  | .yFaceXLow =>
      let q := lowerEdgeSquareCollapse (p.2.2 - k, p.1 - i)
      (q.2 + i, j, q.1 + k)
  | .yFaceXHigh =>
      let q := lowerEdgeSquareCollapse (p.2.2 - k, i + 1 - p.1)
      (i + 1 - q.2, j, q.1 + k)

def squareEdgeNonfreeBoundary (d : SquareEdgeDir) (i j k : ℝ) : Set (ℝ × ℝ × ℝ) :=
  match d with
  | .xFaceYLow => {p | p.2.2 = k ∨ p.2.2 = k + 1 ∨ p.2.1 = j + 1}
  | .yFaceXLow => {p | p.2.2 = k ∨ p.2.2 = k + 1 ∨ p.1 = i + 1}
  | .yFaceXHigh => {p | p.2.2 = k ∨ p.2.2 = k + 1 ∨ p.1 = i}

def squareCellCarrier (d : SquareEdgeDir) (i j k : ℝ) : Set (ℝ × ℝ × ℝ) :=
  match d with
  | .xFaceYLow => xFace i j k
  | .yFaceXLow => yFace i j k
  | .yFaceXHigh => yFace i j k

lemma continuous_squareEdgeCollapse (d : SquareEdgeDir) (i j k : ℝ) :
    Continuous (squareEdgeCollapse d i j k) := by
  cases d
  · let F : ℝ × ℝ × ℝ → ℝ × ℝ := fun p => lowerEdgeSquareCollapse (p.2.2 - k, p.2.1 - j)
    have hF : Continuous F := continuous_lowerEdgeSquareCollapse.comp (by fun_prop)
    change Continuous (fun p => (i, (F p).2 + j, (F p).1 + k))
    fun_prop
  · let F : ℝ × ℝ × ℝ → ℝ × ℝ := fun p => lowerEdgeSquareCollapse (p.2.2 - k, p.1 - i)
    have hF : Continuous F := continuous_lowerEdgeSquareCollapse.comp (by fun_prop)
    change Continuous (fun p => ((F p).2 + i, j, (F p).1 + k))
    fun_prop
  · let F : ℝ × ℝ × ℝ → ℝ × ℝ := fun p => lowerEdgeSquareCollapse (p.2.2 - k, i + 1 - p.1)
    have hF : Continuous F := continuous_lowerEdgeSquareCollapse.comp (by fun_prop)
    change Continuous (fun p => (i + 1 - (F p).2, j, (F p).1 + k))
    fun_prop

lemma squareEdgeCollapse_std_mem (d : SquareEdgeDir) {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ squareCellCarrier d i j k) :
    match d with
    | .xFaceYLow => (p.2.2 - k, p.2.1 - j) ∈ unitSquare2
    | .yFaceXLow => (p.2.2 - k, p.1 - i) ∈ unitSquare2
    | .yFaceXHigh => (p.2.2 - k, i + 1 - p.1) ∈ unitSquare2 := by
  cases d <;> rcases p with ⟨x,y,z⟩ <;>
    simp [squareCellCarrier, xFace, yFace, unitSquare2, Set.mem_prod, Set.mem_Icc,
      Set.mem_singleton_iff] at hp ⊢ <;> grind

lemma squareEdgeCollapse_mem_cell {d : SquareEdgeDir} {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ squareCellCarrier d i j k) : squareEdgeCollapse d i j k p ∈ squareCellCarrier d i j k := by
  rcases p with ⟨x,y,z⟩
  cases d
  · have hq := lowerEdgeSquareCollapse_mem_unitSquare2 (squareEdgeCollapse_std_mem (d := SquareEdgeDir.xFaceYLow) hp)
    simp only [unitSquare2, Set.mem_prod, Set.mem_Icc] at hq
    simp [squareEdgeCollapse, squareCellCarrier, xFace, Set.mem_prod, Set.mem_Icc,
      Set.mem_singleton_iff]
    constructor
    · constructor <;> nlinarith [hq.2.1, hq.2.2]
    · constructor <;> nlinarith [hq.1.1, hq.1.2]
  · have hq := lowerEdgeSquareCollapse_mem_unitSquare2 (squareEdgeCollapse_std_mem (d := SquareEdgeDir.yFaceXLow) hp)
    simp only [unitSquare2, Set.mem_prod, Set.mem_Icc] at hq
    simp [squareEdgeCollapse, squareCellCarrier, yFace, Set.mem_prod, Set.mem_Icc,
      Set.mem_singleton_iff]
    constructor
    · constructor <;> nlinarith [hq.2.1, hq.2.2]
    · constructor <;> nlinarith [hq.1.1, hq.1.2]
  · have hq := lowerEdgeSquareCollapse_mem_unitSquare2 (squareEdgeCollapse_std_mem (d := SquareEdgeDir.yFaceXHigh) hp)
    simp only [unitSquare2, Set.mem_prod, Set.mem_Icc] at hq
    simp [squareEdgeCollapse, squareCellCarrier, yFace, Set.mem_prod, Set.mem_Icc,
      Set.mem_singleton_iff]
    constructor
    · constructor <;> nlinarith [hq.2.1, hq.2.2]
    · constructor <;> nlinarith [hq.1.1, hq.1.2]

lemma squareEdgeCollapse_mem_nonfreeBoundary {d : SquareEdgeDir} {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ squareCellCarrier d i j k) :
    squareEdgeCollapse d i j k p ∈ squareEdgeNonfreeBoundary d i j k := by
  rcases p with ⟨x,y,z⟩
  cases d
  · have hbd := lowerEdgeSquareCollapse_mem_nonfree_boundary (squareEdgeCollapse_std_mem (d := SquareEdgeDir.xFaceYLow) hp)
    simp [squareEdgeCollapse, squareEdgeNonfreeBoundary] at hbd ⊢; grind
  · have hbd := lowerEdgeSquareCollapse_mem_nonfree_boundary (squareEdgeCollapse_std_mem (d := SquareEdgeDir.yFaceXLow) hp)
    simp [squareEdgeCollapse, squareEdgeNonfreeBoundary] at hbd ⊢; grind
  · have hbd := lowerEdgeSquareCollapse_mem_nonfree_boundary (squareEdgeCollapse_std_mem (d := SquareEdgeDir.yFaceXHigh) hp)
    simp [squareEdgeCollapse, squareEdgeNonfreeBoundary] at hbd ⊢; grind

lemma squareEdgeCollapse_eq_self_of_nonfreeBoundary {d : SquareEdgeDir} {i j k : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ squareCellCarrier d i j k) (hbd : p ∈ squareEdgeNonfreeBoundary d i j k) :
    squareEdgeCollapse d i j k p = p := by
  rcases p with ⟨x,y,z⟩
  cases d
  · have hx : x = i := by
      simpa [squareCellCarrier, xFace, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff] using hp.1
    have hstd := squareEdgeCollapse_std_mem (d := SquareEdgeDir.xFaceYLow) hp
    have hbdstd : (z - k, y - j).1 = 0 ∨ (z - k, y - j).1 = 1 ∨ (z - k, y - j).2 = 1 := by
      simp [squareEdgeNonfreeBoundary] at hbd ⊢; grind
    have hfix := lowerEdgeSquareCollapse_eq_self_of_mem_unitSquare2_of_boundary hstd hbdstd
    ext <;> simp [squareEdgeCollapse, hfix, hx]
  · have hy : y = j := by
      simpa [squareCellCarrier, yFace, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff] using hp.2.1
    have hstd := squareEdgeCollapse_std_mem (d := SquareEdgeDir.yFaceXLow) hp
    have hbdstd : (z - k, x - i).1 = 0 ∨ (z - k, x - i).1 = 1 ∨ (z - k, x - i).2 = 1 := by
      simp [squareEdgeNonfreeBoundary] at hbd ⊢; grind
    have hfix := lowerEdgeSquareCollapse_eq_self_of_mem_unitSquare2_of_boundary hstd hbdstd
    ext <;> simp [squareEdgeCollapse, hfix, hy]
  · have hy : y = j := by
      simpa [squareCellCarrier, yFace, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff] using hp.2.1
    have hstd := squareEdgeCollapse_std_mem (d := SquareEdgeDir.yFaceXHigh) hp
    have hbdstd : (z - k, i + 1 - x).1 = 0 ∨ (z - k, i + 1 - x).1 = 1 ∨ (z - k, i + 1 - x).2 = 1 := by
      simp [squareEdgeNonfreeBoundary] at hbd ⊢; grind
    have hfix := lowerEdgeSquareCollapse_eq_self_of_mem_unitSquare2_of_boundary hstd hbdstd
    ext <;> simp [squareEdgeCollapse, hfix, hy]

def hatcherLocalCollapse (m : Fin 28) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  match m.1 with
  | 0 => cubeFaceCollapse .zLow 2 1 0
  | 1 => cubeFaceCollapse .zLow 2 1 1
  | 2 => cubeFaceCollapse .yHigh 2 0 1
  | 3 => cubeFaceCollapse .xLow 3 0 1
  | 4 => cubeFaceCollapse .zHigh 1 1 1
  | 5 => cubeFaceCollapse .zHigh 1 1 0
  | 6 => cubeFaceCollapse .yHigh 1 0 0
  | 7 => cubeFaceCollapse .yLow 2 2 1
  | 8 => cubeFaceCollapse .xHigh 1 0 1
  | 9 => cubeFaceCollapse .xLow 2 0 0
  | 10 => cubeFaceCollapse .xLow 3 2 1
  | 11 => cubeFaceCollapse .xHigh 0 0 0
  | 12 => cubeFaceCollapse .yLow 3 1 1
  | 13 => cubeFaceCollapse .yLow 1 2 0
  | 14 => squareEdgeCollapse .xFaceYLow 3 1 1
  | 15 => cubeFaceCollapse .yLow 0 1 0
  | 16 => squareEdgeCollapse .xFaceYLow 1 1 0
  | 17 => cubeFaceCollapse .xLow 3 0 0
  | 18 => cubeFaceCollapse .xHigh 0 0 1
  | 19 => cubeFaceCollapse .xHigh 0 2 0
  | 20 => cubeFaceCollapse .yLow 0 1 1
  | 21 => squareEdgeCollapse .yFaceXHigh 0 2 0
  | 22 => cubeFaceCollapse .yLow 0 2 1
  | 23 => squareEdgeCollapse .yFaceXLow 3 2 1
  | 24 => cubeFaceCollapse .yLow 3 1 0
  | 25 => cubeFaceCollapse .yLow 3 2 0
  | 26 => cubeFaceCollapse .xLow 1 2 1
  | _ => cubeFaceCollapse .xHigh 2 2 0

def hatcherCellNonfreeBoundary (m : Fin 28) : Set (ℝ × ℝ × ℝ) :=
  match m.1 with
  | 0 => cubeFaceNonfreeBoundary .zLow 2 1 0
  | 1 => cubeFaceNonfreeBoundary .zLow 2 1 1
  | 2 => cubeFaceNonfreeBoundary .yHigh 2 0 1
  | 3 => cubeFaceNonfreeBoundary .xLow 3 0 1
  | 4 => cubeFaceNonfreeBoundary .zHigh 1 1 1
  | 5 => cubeFaceNonfreeBoundary .zHigh 1 1 0
  | 6 => cubeFaceNonfreeBoundary .yHigh 1 0 0
  | 7 => cubeFaceNonfreeBoundary .yLow 2 2 1
  | 8 => cubeFaceNonfreeBoundary .xHigh 1 0 1
  | 9 => cubeFaceNonfreeBoundary .xLow 2 0 0
  | 10 => cubeFaceNonfreeBoundary .xLow 3 2 1
  | 11 => cubeFaceNonfreeBoundary .xHigh 0 0 0
  | 12 => cubeFaceNonfreeBoundary .yLow 3 1 1
  | 13 => cubeFaceNonfreeBoundary .yLow 1 2 0
  | 14 => squareEdgeNonfreeBoundary .xFaceYLow 3 1 1
  | 15 => cubeFaceNonfreeBoundary .yLow 0 1 0
  | 16 => squareEdgeNonfreeBoundary .xFaceYLow 1 1 0
  | 17 => cubeFaceNonfreeBoundary .xLow 3 0 0
  | 18 => cubeFaceNonfreeBoundary .xHigh 0 0 1
  | 19 => cubeFaceNonfreeBoundary .xHigh 0 2 0
  | 20 => cubeFaceNonfreeBoundary .yLow 0 1 1
  | 21 => squareEdgeNonfreeBoundary .yFaceXHigh 0 2 0
  | 22 => cubeFaceNonfreeBoundary .yLow 0 2 1
  | 23 => squareEdgeNonfreeBoundary .yFaceXLow 3 2 1
  | 24 => cubeFaceNonfreeBoundary .yLow 3 1 0
  | 25 => cubeFaceNonfreeBoundary .yLow 3 2 0
  | 26 => cubeFaceNonfreeBoundary .xLow 1 2 1
  | _ => cubeFaceNonfreeBoundary .xHigh 2 2 0

lemma continuous_hatcherLocalCollapse (m : Fin 28) : Continuous (hatcherLocalCollapse m) := by
  fin_cases m <;> simp [hatcherLocalCollapse, continuous_cubeFaceCollapse, continuous_squareEdgeCollapse]

lemma hatcherLocalCollapse_mem_cell (m : Fin 28) :
    Set.MapsTo (hatcherLocalCollapse m) (hatcherCollapseCell m).carrier (hatcherCollapseCell m).carrier := by
  intro p hp
  fin_cases m
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.zLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.zLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.yHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.xLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.zHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.zHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.yHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.xHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.xLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.xLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.xHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_mem_cell (d := SquareEdgeDir.xFaceYLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_mem_cell (d := SquareEdgeDir.xFaceYLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.xLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.xHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.xHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_mem_cell (d := SquareEdgeDir.yFaceXHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_mem_cell (d := SquareEdgeDir.yFaceXLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.xLow) hp
  · simpa [hatcherLocalCollapse, hatcherCollapseCell, CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_cell (d := CubeFaceDir.xHigh) hp

lemma hatcherLocalCollapse_mem_nonfreeBoundary (m : Fin 28) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ (hatcherCollapseCell m).carrier) :
    hatcherLocalCollapse m p ∈ hatcherCellNonfreeBoundary m := by
  fin_cases m
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.zLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.zLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.yHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.xLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.zHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.zHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.yHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.xHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.xLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.xLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.xHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_mem_nonfreeBoundary (d := SquareEdgeDir.xFaceYLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_mem_nonfreeBoundary (d := SquareEdgeDir.xFaceYLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.xLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.xHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.xHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_mem_nonfreeBoundary (d := SquareEdgeDir.yFaceXHigh) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_mem_nonfreeBoundary (d := SquareEdgeDir.yFaceXLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.yLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.xLow) hp
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_mem_nonfreeBoundary (d := CubeFaceDir.xHigh) hp

lemma hatcherLocalCollapse_eq_self_of_nonfreeBoundary (m : Fin 28) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ (hatcherCollapseCell m).carrier) (hbd : p ∈ hatcherCellNonfreeBoundary m) :
    hatcherLocalCollapse m p = p := by
  fin_cases m
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.zLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.zLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.yHigh) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.xLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.zHigh) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.zHigh) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.yHigh) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.yLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.xHigh) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.xLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.xLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.xHigh) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.yLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.yLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_eq_self_of_nonfreeBoundary (d := SquareEdgeDir.xFaceYLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.yLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_eq_self_of_nonfreeBoundary (d := SquareEdgeDir.xFaceYLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.xLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.xHigh) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.xHigh) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.yLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_eq_self_of_nonfreeBoundary (d := SquareEdgeDir.yFaceXHigh) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.yLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier, squareCellCarrier] using
      squareEdgeCollapse_eq_self_of_nonfreeBoundary (d := SquareEdgeDir.yFaceXLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.yLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.yLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.xLow) hp hbd
  · simpa [hatcherLocalCollapse, hatcherCellNonfreeBoundary, hatcherCollapseCell,
      CubicalTopCell.carrier] using
      cubeFaceCollapse_eq_self_of_nonfreeBoundary (d := CubeFaceDir.xHigh) hp hbd

set_option maxHeartbeats 2000000 in
lemma hatcherCellNonfreeBoundary_subset_stage_succ (m : Fin 28) :
    (hatcherCollapseCell m).carrier ∩ hatcherCellNonfreeBoundary m ⊆ hatcherStage (m.1 + 1) := by
  intro p hp
  rcases p with ⟨x,y,z⟩
  rcases hp with ⟨hcell, hbd⟩
  fin_cases m <;>
    simp only [hatcherStage, Set.mem_union, Set.mem_iUnion] <;>
    simp only [Fin.exists_fin_succ, Fin.val_zero, Fin.val_succ] <;>
    simp [LeanEval.Topology.HouseWithTwoRooms, hatcherCellNonfreeBoundary, cubeFaceNonfreeBoundary,
      squareEdgeNonfreeBoundary, hatcherCollapseCell, CubicalTopCell.carrier, unitCube,
      xFace, yFace, horizontalFace, Set.mem_prod, Set.mem_Icc, Set.mem_Ioo,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hcell hbd ⊢ <;>
    grind (splits := 64)

set_option maxHeartbeats 2000000 in
lemma hatcherStage_succ_inter_cell_subset_nonfreeBoundary (m : Fin 28) {p : ℝ × ℝ × ℝ}
    (hcell : p ∈ (hatcherCollapseCell m).carrier) (hstage : p ∈ hatcherStage (m.1 + 1)) :
    p ∈ hatcherCellNonfreeBoundary m := by
  rcases p with ⟨x,y,z⟩
  fin_cases m <;>
    simp only [hatcherStage, Set.mem_union, Set.mem_iUnion] at hstage <;>
    simp only [Fin.exists_fin_succ, Fin.val_zero, Fin.val_succ] at hstage <;>
    simp [LeanEval.Topology.HouseWithTwoRooms, hatcherCellNonfreeBoundary, cubeFaceNonfreeBoundary,
      squareEdgeNonfreeBoundary, hatcherCollapseCell, CubicalTopCell.carrier, unitCube,
      xFace, yFace, horizontalFace, Set.mem_prod, Set.mem_Icc, Set.mem_Ioo,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hcell hstage ⊢ <;>
    grind (splits := 64)

lemma hatcherLocalCollapse_mapsTo_stage_succ (m : Fin 28) :
    Set.MapsTo (hatcherLocalCollapse m) (hatcherCollapseCell m).carrier (hatcherStage (m.1 + 1)) := by
  intro p hp
  exact hatcherCellNonfreeBoundary_subset_stage_succ m
    ⟨hatcherLocalCollapse_mem_cell m hp, hatcherLocalCollapse_mem_nonfreeBoundary m hp⟩

lemma hatcherLocalCollapse_fix_on_stage_succ_inter_cell (m : Fin 28) :
    ∀ p, p ∈ hatcherStage (m.1 + 1) →
      p ∈ (hatcherCollapseCell m).carrier → hatcherLocalCollapse m p = p := by
  intro p hpstage hpcell
  exact hatcherLocalCollapse_eq_self_of_nonfreeBoundary m hpcell
    (hatcherStage_succ_inter_cell_subset_nonfreeBoundary m hpcell hpstage)

def hatcherStageStepRetraction (m : Fin 28) : C(hatcherStage m.1, hatcherStage (m.1 + 1)) :=
  hatcherStageStepRetractionOfLocal m (hatcherLocalCollapse m)
    (continuous_hatcherLocalCollapse m).continuousOn (hatcherLocalCollapse_mapsTo_stage_succ m)
    (hatcherLocalCollapse_fix_on_stage_succ_inter_cell m)

lemma hatcherStageStepRetraction_comp (m : Fin 28) :
    (hatcherStageStepRetraction m).comp (hatcherStageSuccInclusion m) =
      ContinuousMap.id (hatcherStage (m.1 + 1)) := by
  simpa [hatcherStageStepRetraction] using
    hatcherStageStepRetractionOfLocal_comp m (hatcherLocalCollapse m)
      (continuous_hatcherLocalCollapse m).continuousOn (hatcherLocalCollapse_mapsTo_stage_succ m)
      (hatcherLocalCollapse_fix_on_stage_succ_inter_cell m)

lemma hatcherStage_subset_of_le {a b : ℕ} (hab : a ≤ b) : hatcherStage b ⊆ hatcherStage a := by
  intro p hp
  rcases hp with hpH | hpU
  · exact Or.inl hpH
  · right
    rcases Set.mem_iUnion.mp hpU with ⟨i, hi⟩
    by_cases hb : b ≤ i.1
    · have hmem : p ∈ (hatcherCollapseCell i).carrier := by simpa [hb] using hi
      have ha : a ≤ i.1 := le_trans hab hb
      exact Set.mem_iUnion.mpr ⟨i, by simpa [ha] using hmem⟩
    · simp [hb] at hi

def hatcherStageInclusionOfLe {a b : ℕ} (hab : a ≤ b) : C(hatcherStage b, hatcherStage a) where
  toFun p := ⟨(p : ℝ × ℝ × ℝ), hatcherStage_subset_of_le hab p.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

def hatcherCompositeAux : (n : ℕ) → C(hatcherStage 0, hatcherStage n)
  | 0 => ContinuousMap.id (hatcherStage 0)
  | n + 1 =>
      if h : n < 28 then
        (hatcherStageStepRetraction (⟨n, h⟩ : Fin 28)).comp (hatcherCompositeAux n)
      else
        ContinuousMap.const _ ⟨((0 : ℝ), (0 : ℝ), (0 : ℝ)), by
          left; exact houseWithTwoRooms_origin_mem⟩

lemma hatcherCompositeAux_fix_val (n : ℕ) (hn : n ≤ 28) (p : hatcherStage n) :
    ((hatcherCompositeAux n) (hatcherStageInclusionOfLe (Nat.zero_le n) p) : ℝ × ℝ × ℝ) =
      (p : ℝ × ℝ × ℝ) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have hnlt : n < 28 := by omega
      simp [hatcherCompositeAux, hnlt]
      let q : hatcherStage n := (hatcherStageSuccInclusion (⟨n, hnlt⟩ : Fin 28)) p
      have harg : hatcherCompositeAux n (hatcherStageInclusionOfLe (Nat.zero_le n) q) = q := by
        apply Subtype.ext
        exact ih (by omega) q
      have hstep := ContinuousMap.congr_fun
        (hatcherStageStepRetraction_comp (⟨n, hnlt⟩ : Fin 28)) p
      change ((hatcherStageStepRetraction (⟨n, hnlt⟩ : Fin 28))
        (hatcherCompositeAux n (hatcherStageInclusionOfLe (Nat.zero_le n)
          ((hatcherStageSuccInclusion (⟨n, hnlt⟩ : Fin 28)) p))) : ℝ × ℝ × ℝ) =
        (p : ℝ × ℝ × ℝ)
      rw [harg]
      exact Subtype.ext_iff.mp hstep

def hatcherStageLastToHouse : C(hatcherStage 28, LeanEval.Topology.HouseWithTwoRooms) where
  toFun p := ⟨(p : ℝ × ℝ × ℝ), by simpa [hatcherStage_last] using p.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val
    (fun p => by simpa [hatcherStage_last] using p.2)

def houseAmbientBoxToHatcherStageZero : C(HouseAmbientBox, hatcherStage 0) where
  toFun p := ⟨(p : ℝ × ℝ × ℝ), by
    simpa [hatcherStage_zero_eq_ambientBox] using p.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val
    (fun p => by simpa [hatcherStage_zero_eq_ambientBox] using p.2)

def houseAmbientBoxToHouse : C(HouseAmbientBox, LeanEval.Topology.HouseWithTwoRooms) :=
  hatcherStageLastToHouse.comp ((hatcherCompositeAux 28).comp houseAmbientBoxToHatcherStageZero)

lemma houseAmbientBoxToHouse_comp :
    houseAmbientBoxToHouse.comp houseWithTwoRooms_inclusion_ambientBox =
      ContinuousMap.id LeanEval.Topology.HouseWithTwoRooms := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  have hstage28 : ((p : ℝ × ℝ × ℝ)) ∈ hatcherStage 28 := by
    simpa [hatcherStage_last] using p.2
  have hfix := hatcherCompositeAux_fix_val 28 (by norm_num) ⟨(p : ℝ × ℝ × ℝ), hstage28⟩
  simpa [houseAmbientBoxToHouse, hatcherStageLastToHouse, houseAmbientBoxToHatcherStageZero,
    hatcherStageInclusionOfLe] using hfix

lemma houseWithTwoRooms_retraction_from_ambientBox :
    ∃ r : C(HouseAmbientBox, LeanEval.Topology.HouseWithTwoRooms),
      r.comp houseWithTwoRooms_inclusion_ambientBox =
        ContinuousMap.id LeanEval.Topology.HouseWithTwoRooms := by
  exact ⟨houseAmbientBoxToHouse, houseAmbientBoxToHouse_comp⟩

end



theorem contractibleSpace_houseWithTwoRooms : ContractibleSpace HouseWithTwoRooms := by
  rcases houseWithTwoRooms_retraction_from_ambientBox with ⟨r, hri⟩
  exact contractibleSpace_of_retract houseWithTwoRooms_inclusion_ambientBox r hri


end Submission
