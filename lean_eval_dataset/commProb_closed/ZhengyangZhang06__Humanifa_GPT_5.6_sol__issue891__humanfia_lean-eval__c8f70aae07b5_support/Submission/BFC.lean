import Submission.SmallConjAscent

namespace Submission.Helpers

open scoped commutatorElement

noncomputable section

lemma conjClass_card_eq_of_isConj {G : Type} [Group G] {x y : G} (hxy : IsConj x y) :
    Nat.card (ConjClasses.mk x).carrier = Nat.card (ConjClasses.mk y).carrier := by
  rw [ConjClasses.mk_eq_mk_iff_isConj.mpr hxy]

def conjClassInvEquiv {G : Type} [Group G] (x : G) :
    (ConjClasses.mk x).carrier ≃ (ConjClasses.mk x⁻¹).carrier where
  toFun y := ⟨y.1⁻¹, by
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    obtain ⟨c, hc⟩ := isConj_iff.mp
      (ConjClasses.mk_eq_mk_iff_isConj.mp
        (ConjClasses.mem_carrier_iff_mk_eq.mp y.2))
    apply isConj_iff.mpr
    refine ⟨c, ?_⟩
    have hi := congrArg Inv.inv hc
    simpa [mul_assoc] using hi⟩
  invFun y := ⟨y.1⁻¹, by
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    obtain ⟨c, hc⟩ := isConj_iff.mp
      (ConjClasses.mk_eq_mk_iff_isConj.mp
        (ConjClasses.mem_carrier_iff_mk_eq.mp y.2))
    apply isConj_iff.mpr
    refine ⟨c, ?_⟩
    have hi := congrArg Inv.inv hc
    simpa [mul_assoc] using hi⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp

lemma conjClass_card_inv {G : Type} [Group G] (x : G) :
    Nat.card (ConjClasses.mk x⁻¹).carrier = Nat.card (ConjClasses.mk x).carrier := by
  exact (Nat.card_congr (conjClassInvEquiv x)).symm

def conjClassMulEmbedding {G : Type} [Group G] (x y : G) :
    (ConjClasses.mk (x * y)).carrier ↪
      (ConjClasses.mk x).carrier × (ConjClasses.mk y).carrier := by
  classical
  let conjugator (z : (ConjClasses.mk (x * y)).carrier) : G :=
    (isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp
      (ConjClasses.mem_carrier_iff_mk_eq.mp z.2).symm)).choose
  have conjugator_spec (z : (ConjClasses.mk (x * y)).carrier) :
      conjugator z * (x * y) * (conjugator z)⁻¹ = z.1 :=
    (isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp
      (ConjClasses.mem_carrier_iff_mk_eq.mp z.2).symm)).choose_spec
  refine ⟨fun z =>
    ⟨⟨conjugator z * x * (conjugator z)⁻¹, by
        rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
        exact (isConj_iff.mpr ⟨conjugator z, rfl⟩).symm⟩,
      ⟨conjugator z * y * (conjugator z)⁻¹, by
        rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
        exact (isConj_iff.mpr ⟨conjugator z, rfl⟩).symm⟩⟩, ?_⟩
  intro a b hab
  apply Subtype.ext
  have hprod := congrArg (fun q => q.1.1 * q.2.1) hab
  change a.1 = b.1
  simpa [conj_mul, conjugator_spec] using hprod

lemma conjClass_card_mul_le {G : Type} [Group G] [Finite G] (x y : G) :
    Nat.card (ConjClasses.mk (x * y)).carrier ≤
      Nat.card (ConjClasses.mk x).carrier * Nat.card (ConjClasses.mk y).carrier := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ (conjClassMulEmbedding x y).injective

def mulCayleyLeftHom {G : Type} [Group G] (S : Set G) (a : G) :
    SimpleGraph.mulCayley S →g SimpleGraph.mulCayley S where
  toFun := fun z => a * z
  map_rel' {u v} huv := by
    exact (SimpleGraph.mulCayley_adj_mul_iff_right (s := S) (d := a)).mpr huv

lemma reachable_one_of_mem_closure {G : Type} [Group G] (S : Set G) {x : G}
    (hx : x ∈ Subgroup.closure S) :
    (SimpleGraph.mulCayley S).Reachable 1 x := by
  let C := SimpleGraph.mulCayley S
  refine Subgroup.closure_induction (p := fun z _ => C.Reachable 1 z) ?_ ?_ ?_ ?_ hx
  · intro z hz
    by_cases h : z = 1
    · subst z
      exact SimpleGraph.Reachable.refl 1
    · exact ((SimpleGraph.mulCayley_adj' S 1 z).mpr
        ⟨Ne.symm h, z, hz, Or.inl (one_mul z)⟩).reachable
  · exact SimpleGraph.Reachable.refl 1
  · intro a b _ _ ha hb
    have hab : C.Reachable a (a * b) := by
      simpa [C, mulCayleyLeftHom] using hb.map (mulCayleyLeftHom S a)
    exact ha.trans hab
  · intro a _ ha
    have h : C.Reachable a⁻¹ 1 := by
      simpa [C, mulCayleyLeftHom] using ha.map (mulCayleyLeftHom S a⁻¹)
    exact h.symm

lemma mulCayley_connected_of_closure_eq_top {G : Type} [Group G] (S : Set G)
    (hS : Subgroup.closure S = ⊤) :
    (SimpleGraph.mulCayley S).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, inferInstance⟩
  intro x y
  have hx : (SimpleGraph.mulCayley S).Reachable 1 x :=
    reachable_one_of_mem_closure S (hS ▸ Subgroup.mem_top x)
  have hy : (SimpleGraph.mulCayley S).Reachable 1 y :=
    reachable_one_of_mem_closure S (hS ▸ Subgroup.mem_top y)
  exact hx.symm.trans hy

lemma mulCayley_dist_mul_le_one {G : Type} [Group G] (S : Set G)
    (a : G) (s : S) :
    (SimpleGraph.mulCayley S).dist a (a * s.1) ≤ 1 := by
  by_cases h : a = a * s.1
  · rw [← h]
    simpa only [SimpleGraph.dist_self] using (Nat.zero_le 1)
  · exact le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr
      ((SimpleGraph.mulCayley_adj' S a (a * s.1)).mpr
        ⟨h, s.1, s.2, Or.inl rfl⟩))

lemma dist_getVert_eq_sub_of_shortest {V : Type} {C : SimpleGraph V}
    {u v : V} (p : C.Walk u v) (hp : p.length = C.dist u v)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    C.dist (p.getVert i) (p.getVert j) = j - i := by
  let q := (p.take j).drop i
  have hsub : q.IsSubwalk p :=
    (SimpleGraph.Walk.isSubwalk_drop (p.take j) i).trans (p.isSubwalk_take j)
  have hlen := SimpleGraph.length_eq_dist_of_subwalk hp hsub
  symm
  simpa [q, SimpleGraph.Walk.drop_length, SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.take_getVert, Nat.min_eq_left hj, Nat.min_eq_right hij] using hlen

lemma shortestPath_translate_injective {G : Type} [Group G]
    (S : Set G) {u v : G} (p : (SimpleGraph.mulCayley S).Walk u v)
    (hp : p.length = (SimpleGraph.mulCayley S).dist u v)
    (hconn : (SimpleGraph.mulCayley S).Connected) :
    Function.Injective (fun q : Fin (p.length / 3 + 1) × S =>
      p.getVert (3 * q.1.1) * q.2.1) := by
  intro a b hab
  change p.getVert (3 * a.1.1) * a.2.1 =
    p.getVert (3 * b.1.1) * b.2.1 at hab
  have hindex : a.1 = b.1 := by
    apply Fin.ext
    by_contra hne
    have hlt : a.1.1 < b.1.1 ∨ b.1.1 < a.1.1 := lt_or_gt_of_ne hne
    rcases hlt with hlt | hlt
    · have hai : 3 * a.1.1 ≤ p.length := by
        have ha := a.1.2
        omega
      have hbj : 3 * b.1.1 ≤ p.length := by
        have hb := b.1.2
        omega
      have hdist :
          (SimpleGraph.mulCayley S).dist
              (p.getVert (3 * a.1.1)) (p.getVert (3 * b.1.1)) =
            3 * b.1.1 - 3 * a.1.1 :=
        dist_getVert_eq_sub_of_shortest p hp (by omega) hbj
      have hleft := mulCayley_dist_mul_le_one S (p.getVert (3 * a.1.1)) a.2
      have hright := mulCayley_dist_mul_le_one S (p.getVert (3 * b.1.1)) b.2
      have hright' :
          (SimpleGraph.mulCayley S).dist
              (p.getVert (3 * a.1.1) * a.2.1) (p.getVert (3 * b.1.1)) ≤ 1 := by
        rw [hab, SimpleGraph.dist_comm]
        exact hright
      have hupper := hconn.dist_triangle
        (u := p.getVert (3 * a.1.1))
        (v := p.getVert (3 * a.1.1) * a.2.1)
        (w := p.getVert (3 * b.1.1))
      omega
    · have hbi : 3 * b.1.1 ≤ p.length := by
        have hb := b.1.2
        omega
      have haj : 3 * a.1.1 ≤ p.length := by
        have ha := a.1.2
        omega
      have hdist :
          (SimpleGraph.mulCayley S).dist
              (p.getVert (3 * b.1.1)) (p.getVert (3 * a.1.1)) =
            3 * a.1.1 - 3 * b.1.1 :=
        dist_getVert_eq_sub_of_shortest p hp (by omega) haj
      have hleft := mulCayley_dist_mul_le_one S (p.getVert (3 * b.1.1)) b.2
      have hright := mulCayley_dist_mul_le_one S (p.getVert (3 * a.1.1)) a.2
      have hright' :
          (SimpleGraph.mulCayley S).dist
              (p.getVert (3 * b.1.1) * b.2.1) (p.getVert (3 * a.1.1)) ≤ 1 := by
        rw [← hab, SimpleGraph.dist_comm]
        exact hright
      have hupper := hconn.dist_triangle
        (u := p.getVert (3 * b.1.1))
        (v := p.getVert (3 * b.1.1) * b.2.1)
        (w := p.getVert (3 * a.1.1))
      omega
  have hgen : a.2 = b.2 := by
    apply Subtype.ext
    rw [hindex] at hab
    exact mul_left_cancel hab
  exact Prod.ext hindex hgen

lemma shortestPath_translate_card_le {G : Type} [Group G] [Finite G]
    (S : Set G) {u v : G} (p : (SimpleGraph.mulCayley S).Walk u v)
    (hp : p.length = (SimpleGraph.mulCayley S).dist u v)
    (hconn : (SimpleGraph.mulCayley S).Connected) :
    (p.length / 3 + 1) * Nat.card S ≤ Nat.card G := by
  have h := Nat.card_le_card_of_injective
    (fun q : Fin (p.length / 3 + 1) × S => p.getVert (3 * q.1.1) * q.2.1)
    (shortestPath_translate_injective S p hp hconn)
  simpa [Nat.card_prod, Nat.card_fin] using h

lemma conjClass_card_le_mul_of_mulCayley_adj {G : Type} [Group G] [Finite G]
    {S : Set G} {M : ℕ}
    (hS : ∀ s ∈ S, Nat.card (ConjClasses.mk s).carrier ≤ M)
    {a b : G} (hab : (SimpleGraph.mulCayley S).Adj a b) :
    Nat.card (ConjClasses.mk b).carrier ≤
      Nat.card (ConjClasses.mk a).carrier * M := by
  rcases (SimpleGraph.mulCayley_adj S a b).mp hab with ⟨_, hs | hs⟩
  · let s := a⁻¹ * b
    have hb : b = a * s := by simp [s]
    rw [hb]
    exact (conjClass_card_mul_le a s).trans
      (Nat.mul_le_mul_left _ (hS s hs))
  · let s := b⁻¹ * a
    have hb : b = a * s⁻¹ := by
      simp [s]
    have hsinv : Nat.card (ConjClasses.mk s⁻¹).carrier ≤ M := by
      rw [conjClass_card_inv]
      exact hS s hs
    rw [hb]
    exact (conjClass_card_mul_le a s⁻¹).trans
      (Nat.mul_le_mul_left _ hsinv)

lemma conjClass_card_end_le_start_mul_pow_of_walk {G : Type} [Group G] [Finite G]
    {S : Set G} {M : ℕ}
    (hS : ∀ s ∈ S, Nat.card (ConjClasses.mk s).carrier ≤ M)
    {a b : G} (p : (SimpleGraph.mulCayley S).Walk a b) :
    Nat.card (ConjClasses.mk b).carrier ≤
      Nat.card (ConjClasses.mk a).carrier * M ^ p.length := by
  induction p with
  | nil => simp
  | @cons a c b hac p ih =>
      calc
        Nat.card (ConjClasses.mk b).carrier ≤
            Nat.card (ConjClasses.mk c).carrier * M ^ p.length := ih
        _ ≤ (Nat.card (ConjClasses.mk a).carrier * M) * M ^ p.length :=
          Nat.mul_le_mul_right _ (conjClass_card_le_mul_of_mulCayley_adj hS hac)
        _ = Nat.card (ConjClasses.mk a).carrier * M ^ (p.length + 1) := by
          rw [pow_succ]
          ring
        _ = Nat.card (ConjClasses.mk a).carrier * M ^ (SimpleGraph.Walk.cons hac p).length := by
          simp

lemma mem_smallConjSet_of_mem_conjugatesOfSet_smallConjSet
    {G : Type} [Group G] (M : ℕ) {x : G}
    (hx : x ∈ Group.conjugatesOfSet (SmallConjSet G M)) :
    x ∈ SmallConjSet G M := by
  rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨y, hy, hyx⟩
  change Nat.card (ConjClasses.mk x).carrier ≤ M
  rw [← conjClass_card_eq_of_isConj hyx]
  exact hy

def smallConjElementsEmbeddingConjugatesOfSet
    (G : Type) [Group G] (M : ℕ) :
    SmallConjElements G M ↪ Group.conjugatesOfSet (SmallConjSet G M) where
  toFun x := ⟨x.1, Group.subset_conjugatesOfSet x.2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    change x.1 = y.1
    exact congrArg
      (fun z : Group.conjugatesOfSet (SmallConjSet G M) => (z : G)) h

lemma card_smallConjElements_le_card_conjugatesOfSet
    (G : Type) [Group G] [Finite G] (M : ℕ) :
    Nat.card (SmallConjElements G M) ≤
      Nat.card (Group.conjugatesOfSet (SmallConjSet G M)) :=
  Nat.card_le_card_of_injective _
    (smallConjElementsEmbeddingConjugatesOfSet G M).injective

lemma shortestPath_length_mul_density_lt_three
    {G : Type} [Group G] [Finite G]
    (S : Set G) {u v : G} (p : (SimpleGraph.mulCayley S).Walk u v)
    (hp : p.length = (SimpleGraph.mulCayley S).dist u v)
    (hconn : (SimpleGraph.mulCayley S).Connected)
    {d : ℝ} (hd : 0 < d)
    (hdensity : d * Nat.card G < Nat.card S) :
    (p.length : ℝ) * d < 3 := by
  have hcountN := shortestPath_translate_card_le S p hp hconn
  have hcount : (((p.length / 3 + 1 : ℕ) : ℝ) * Nat.card S) ≤ Nat.card G := by
    exact_mod_cast hcountN
  have hlengthN : p.length < 3 * (p.length / 3 + 1) := by omega
  have hlength : (p.length : ℝ) < 3 * (p.length / 3 + 1 : ℕ) := by
    exact_mod_cast hlengthN
  have hcardG : (0 : ℝ) < Nat.card G := by
    exact_mod_cast (show 0 < Nat.card G from Finite.card_pos)
  have hcardS : (0 : ℝ) < Nat.card S :=
    (mul_pos hd hcardG).trans hdensity
  by_cases hzero : p.length = 0
  · simp [hzero]
  · have hlength_pos : (0 : ℝ) < p.length := by
      exact_mod_cast (Nat.pos_of_ne_zero hzero)
    have hmulDensity := mul_lt_mul_of_pos_left hdensity hlength_pos
    have hmulLength := mul_lt_mul_of_pos_right hlength hcardS
    have hmulCount := mul_le_mul_of_nonneg_left hcount (show (0 : ℝ) ≤ 3 by norm_num)
    apply lt_of_mul_lt_mul_right _ hcardG.le
    nlinarith

lemma shortestPath_length_lt_twelve_div
    {G : Type} [Group G] [Finite G]
    (S : Set G) {u v : G} (path : (SimpleGraph.mulCayley S).Walk u v)
    (hpath : path.length = (SimpleGraph.mulCayley S).dist u v)
    (hconn : (SimpleGraph.mulCayley S).Connected)
    {p : ℝ} (hp : 0 < p)
    (hdensity : p / 4 * Nat.card G < Nat.card S) :
    (path.length : ℝ) < 12 / p := by
  have h := shortestPath_length_mul_density_lt_three S path hpath hconn
    (show 0 < p / 4 by positivity) hdensity
  have hdiv : (path.length : ℝ) < 3 / (p / 4) :=
    (lt_div_iff₀ (show 0 < p / 4 by positivity)).mpr h
  calc
    (path.length : ℝ) < 3 / (p / 4) := hdiv
    _ = 12 / p := by field_simp; ring

def conjClassOneEquiv {G : Type} [Group G] :
    PUnit.{1} ≃ (ConjClasses.mk (1 : G)).carrier where
  toFun _ := ⟨1, ConjClasses.mem_carrier_mk⟩
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv y := by
    apply Subtype.ext
    have hy : IsConj y.1 (1 : G) :=
      ConjClasses.mk_eq_mk_iff_isConj.mp
        (ConjClasses.mem_carrier_iff_mk_eq.mp y.2)
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    have hy_one : y.1 = 1 := by
      calc
        y.1 = c⁻¹ * (c * y.1 * c⁻¹) * c := by group
        _ = 1 := by rw [hc]; simp
    exact hy_one.symm

@[simp] lemma conjClass_card_one {G : Type} [Group G] :
    Nat.card (ConjClasses.mk (1 : G)).carrier = 1 := by
  calc
    Nat.card (ConjClasses.mk (1 : G)).carrier = Nat.card PUnit.{1} :=
      Nat.card_congr (conjClassOneEquiv (G := G)).symm
    _ = 1 := by simp

lemma conjClass_card_le_pow_of_smallConj_density_index_one
    (G : Type) [Group G] [Finite G]
    {p : ℝ} (hp : 0 < p) (N L : ℕ)
    (hdensity : p / 4 * Nat.card G < Nat.card (SmallConjElements G N))
    (hindex : (smallConjSubgroup G N).index = 1)
    (hL : 12 / p < L) (g : G) :
    Nat.card (ConjClasses.mk g).carrier ≤ (N + 1) ^ L := by
  let S := Group.conjugatesOfSet (SmallConjSet G N)
  have htop : smallConjSubgroup G N = ⊤ := Subgroup.index_eq_one.mp hindex
  have hclosure : Subgroup.closure S = ⊤ := by
    change Subgroup.closure (Group.conjugatesOfSet (SmallConjSet G N)) = ⊤ at htop
    exact htop
  have hconn : (SimpleGraph.mulCayley S).Connected :=
    mulCayley_connected_of_closure_eq_top S hclosure
  have hcardN := card_smallConjElements_le_card_conjugatesOfSet G N
  have hcard : (Nat.card (SmallConjElements G N) : ℝ) ≤ Nat.card S := by
    exact_mod_cast hcardN
  have hdensityS : p / 4 * Nat.card G < Nat.card S := hdensity.trans_le hcard
  obtain ⟨path, hpath⟩ := hconn.exists_walk_length_eq_dist 1 g
  have hlength : (path.length : ℝ) < 12 / p :=
    shortestPath_length_lt_twelve_div S path hpath hconn hp hdensityS
  have hlengthLReal : (path.length : ℝ) < L := hlength.trans hL
  have hlengthL : path.length ≤ L := by
    exact_mod_cast hlengthLReal.le
  have hgenerators : ∀ s ∈ S,
      Nat.card (ConjClasses.mk s).carrier ≤ N + 1 := by
    intro s hs
    exact (mem_smallConjSet_of_mem_conjugatesOfSet_smallConjSet N hs).trans
      (Nat.le_succ N)
  have hwalk := conjClass_card_end_le_start_mul_pow_of_walk hgenerators path
  rw [conjClass_card_one, one_mul] at hwalk
  exact hwalk.trans (Nat.pow_le_pow_right (Nat.succ_pos N) hlengthL)

lemma centralizer_singleton_index_eq_conjClass_card
    (G : Type) [Group G] [Finite G] (x : G) :
    (Subgroup.centralizer ({x} : Set G)).index =
      Nat.card (ConjClasses.mk x).carrier := by
  let C := Subgroup.centralizer ({x} : Set G)
  have hclass := card_conjClass_mul_card_commuteFiber G x
  rw [Nat.card_congr (commuteFiberEquivCentralizer x)] at hclass
  have hindex := C.card_mul_index
  have heq : Nat.card C * C.index =
      Nat.card C * Nat.card (ConjClasses.mk x).carrier := by
    calc
      Nat.card C * C.index = Nat.card G := hindex
      _ = Nat.card (ConjClasses.mk x).carrier * Nat.card C := hclass.symm
      _ = Nat.card C * Nat.card (ConjClasses.mk x).carrier := Nat.mul_comm _ _
  exact Nat.eq_of_mul_eq_mul_left Finite.card_pos heq

def subgroupConjClassEmbedding {G : Type} [Group G]
    (H : Subgroup G) (x : H) :
    (ConjClasses.mk x).carrier ↪ (ConjClasses.mk (x : G)).carrier where
  toFun y := ⟨(y.1 : G), by
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    have hy : IsConj y.1 x :=
      ConjClasses.mk_eq_mk_iff_isConj.mp
        (ConjClasses.mem_carrier_iff_mk_eq.mp y.2)
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    apply isConj_iff.mpr
    exact ⟨(c : G), congrArg Subtype.val hc⟩⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun z : (ConjClasses.mk (x : G)).carrier => (z : G)) h

lemma subgroup_conjClass_card_le {G : Type} [Group G] [Finite G]
    (H : Subgroup G) (x : H) :
    Nat.card (ConjClasses.mk x).carrier ≤
      Nat.card (ConjClasses.mk (x : G)).carrier :=
  Nat.card_le_card_of_injective _ (subgroupConjClassEmbedding H x).injective

lemma card_le_card_conjClasses_mul_of_conjClass_card_le
    (G : Type) [Group G] [Finite G] (n : ℕ)
    (hclass : ∀ x : G, Nat.card (ConjClasses.mk x).carrier ≤ n) :
    Nat.card G ≤ Nat.card (ConjClasses G) * n := by
  classical
  letI := Fintype.ofFinite (ConjClasses G)
  rw [← Group.sum_card_conj_classes_eq_card G, finsum_eq_sum_of_fintype]
  calc
    ∑ x : ConjClasses G, Nat.card x.carrier ≤ ∑ _x : ConjClasses G, n := by
      apply Finset.sum_le_sum
      intro x _hx
      rw [← mk_conjClassRep x]
      exact hclass (conjClassRep x)
    _ = Nat.card (ConjClasses G) * n := by
      simp [Nat.card_eq_fintype_card]

lemma sq_card_le_mul_card_commutingPairs_of_conjClass_card_le
    (G : Type) [Group G] [Finite G] (n : ℕ)
    (hclass : ∀ x : G, Nat.card (ConjClasses.mk x).carrier ≤ n) :
    Nat.card G ^ 2 ≤ n * Nat.card (CommutingPairs G) := by
  have hcard := card_le_card_conjClasses_mul_of_conjClass_card_le G n hclass
  have hcomm := card_comm_eq_card_conjClasses_mul_card G
  calc
    Nat.card G ^ 2 = Nat.card G * Nat.card G := by ring
    _ ≤ (Nat.card (ConjClasses G) * n) * Nat.card G :=
      Nat.mul_le_mul_right _ hcard
    _ = n * (Nat.card (ConjClasses G) * Nat.card G) := by ring
    _ = n * Nat.card (CommutingPairs G) := by rw [hcomm]

abbrev CommutatorFiber (G : Type) [Group G] (z : G) :=
  {p : G × G // ⁅p.1, p.2⁆ = z}

def commutingPairsCentralizerInfEmbedding
    (G : Type) [Group G] (x y : G) :
    CommutingPairs
        ((Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G)) : Subgroup G) ↪
      CommutatorFiber G ⁅x, y⁆ where
  toFun p := ⟨(x * (p.1.1 : G), y * (p.1.2 : G)), by
    let a : G := p.1.1
    let b : G := p.1.2
    have hay : Commute a y := by
      show a * y = y * a
      exact Subgroup.mem_centralizer_singleton_iff.mp p.1.1.2.2
    have hab : Commute a b := by
      show a * b = b * a
      exact congrArg (fun z :
        ((Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G)) : Subgroup G) =>
          (z : G)) p.2.eq
    have hxb : Commute x b := by
      show x * b = b * x
      exact (Subgroup.mem_centralizer_singleton_iff.mp p.1.2.2.1).symm
    rw [commutatorElement_mul_left_eq_conj_mul]
    rw [(hay.mul_right hab).commutator_eq]
    simp
    rw [commutatorElement_mul_right_eq_mul_conj]
    rw [hxb.commutator_eq]
    simp⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      have hfirst := congrArg
        (fun z : CommutatorFiber G ⁅x, y⁆ => z.1.1) h
      change x * (a.1.1 : G) = x * (b.1.1 : G) at hfirst
      exact mul_left_cancel hfirst
    · apply Subtype.ext
      have hsecond := congrArg
        (fun z : CommutatorFiber G ⁅x, y⁆ => z.1.2) h
      change y * (a.1.2 : G) = y * (b.1.2 : G) at hsecond
      exact mul_left_cancel hsecond

lemma sq_card_le_pow_five_mul_card_commutatorFiber
    (G : Type) [Group G] [Finite G] (n : ℕ)
    (hclass : ∀ x : G, Nat.card (ConjClasses.mk x).carrier ≤ n)
    (x y : G) :
    Nat.card G ^ 2 ≤ n ^ 5 * Nat.card (CommutatorFiber G ⁅x, y⁆) := by
  let Cx := Subgroup.centralizer ({x} : Set G)
  let Cy := Subgroup.centralizer ({y} : Set G)
  let H := Cx ⊓ Cy
  have hindex : H.index ≤ n ^ 2 := by
    calc
      H.index ≤ Cx.index * Cy.index :=
        Subgroup.index_inf_le (H := Cx) (K := Cy)
      _ = Nat.card (ConjClasses.mk x).carrier *
          Nat.card (ConjClasses.mk y).carrier := by
        rw [centralizer_singleton_index_eq_conjClass_card,
          centralizer_singleton_index_eq_conjClass_card]
      _ ≤ n * n := Nat.mul_le_mul (hclass x) (hclass y)
      _ = n ^ 2 := by ring
  have hcardG : Nat.card G ≤ Nat.card H * n ^ 2 := by
    rw [← H.card_mul_index]
    exact Nat.mul_le_mul_left _ hindex
  have hclassH : ∀ h : H, Nat.card (ConjClasses.mk h).carrier ≤ n := by
    intro h
    exact (subgroup_conjClass_card_le H h).trans (hclass h.1)
  have hcommH : Nat.card H ^ 2 ≤ n * Nat.card (CommutingPairs H) :=
    sq_card_le_mul_card_commutingPairs_of_conjClass_card_le H n hclassH
  have hembed : Nat.card (CommutingPairs H) ≤
      Nat.card (CommutatorFiber G ⁅x, y⁆) :=
    Nat.card_le_card_of_injective _
      (commutingPairsCentralizerInfEmbedding G x y).injective
  calc
    Nat.card G ^ 2 = Nat.card G * Nat.card G := by ring
    _ ≤ (Nat.card H * n ^ 2) * (Nat.card H * n ^ 2) :=
      Nat.mul_le_mul hcardG hcardG
    _ = Nat.card H ^ 2 * n ^ 4 := by ring
    _ ≤ (n * Nat.card (CommutingPairs H)) * n ^ 4 :=
      Nat.mul_le_mul_right _ hcommH
    _ = n ^ 5 * Nat.card (CommutingPairs H) := by ring
    _ ≤ n ^ 5 * Nat.card (CommutatorFiber G ⁅x, y⁆) :=
      Nat.mul_le_mul_left _ hembed

def pairsEquivSigmaCommutatorFiber (G : Type) [Group G] :
    G × G ≃ Σ z : commutatorSet G, CommutatorFiber G z.1 where
  toFun p := ⟨⟨⁅p.1, p.2⁆, commutator_mem_commutatorSet p.1 p.2⟩, ⟨p, rfl⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨z, hz⟩, ⟨p, hp⟩⟩
    change ⁅p.1, p.2⁆ = z at hp
    subst z
    rfl

lemma sum_card_commutatorFiber (G : Type) [Group G] [Fintype G]
    [Fintype (commutatorSet G)] :
    ∑ z : commutatorSet G, Nat.card (CommutatorFiber G z.1) = Nat.card G ^ 2 := by
  classical
  rw [← Nat.card_sigma]
  calc
    Nat.card (Σ z : commutatorSet G, CommutatorFiber G z.1) = Nat.card (G × G) :=
      Nat.card_congr (pairsEquivSigmaCommutatorFiber G).symm
    _ = Nat.card G ^ 2 := by rw [Nat.card_prod, pow_two]

lemma card_commutatorSet_le_pow_five_of_conjClass_card_le
    (G : Type) [Group G] [Finite G] (n : ℕ)
    (hclass : ∀ x : G, Nat.card (ConjClasses.mk x).carrier ≤ n) :
    Nat.card (commutatorSet G) ≤ n ^ 5 := by
  classical
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite (commutatorSet G)
  have hfiber : ∀ z : commutatorSet G,
      Nat.card G ^ 2 ≤ n ^ 5 * Nat.card (CommutatorFiber G z.1) := by
    intro z
    rcases mem_commutatorSet_iff.mp z.2 with ⟨x, y, hxy⟩
    simpa [hxy] using sq_card_le_pow_five_mul_card_commutatorFiber G n hclass x y
  have hsum : Nat.card (commutatorSet G) * Nat.card G ^ 2 ≤
      n ^ 5 * Nat.card G ^ 2 := by
    calc
      Nat.card (commutatorSet G) * Nat.card G ^ 2 =
          ∑ _z : commutatorSet G, Nat.card G ^ 2 := by
            simp [Nat.card_eq_fintype_card]
      _ ≤ ∑ z : commutatorSet G,
          n ^ 5 * Nat.card (CommutatorFiber G z.1) := by
            exact Finset.sum_le_sum fun z _ => hfiber z
      _ = n ^ 5 * ∑ z : commutatorSet G,
          Nat.card (CommutatorFiber G z.1) := by rw [Finset.mul_sum]
      _ = n ^ 5 * Nat.card G ^ 2 := by rw [sum_card_commutatorFiber]
  exact Nat.le_of_mul_le_mul_right hsum (pow_pos Finite.card_pos 2)

def bfcCommutatorBound (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n ^ 5 + 1), Subgroup.cardCommutatorBound k

lemma card_commutator_le_bfcCommutatorBound_of_conjClass_card_le
    (G : Type) [Group G] [Finite G] (n : ℕ)
    (hclass : ∀ x : G, Nat.card (ConjClasses.mk x).carrier ≤ n) :
    Nat.card (commutator G) ≤ bfcCommutatorBound n := by
  have hset := card_commutatorSet_le_pow_five_of_conjClass_card_le G n hclass
  refine (Subgroup.card_commutator_le_of_finite_commutatorSet G).trans ?_
  apply Finset.single_le_sum (s := Finset.range (n ^ 5 + 1))
    (f := Subgroup.cardCommutatorBound)
    (fun _ _ => Nat.zero_le _)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hset)

lemma exists_uniform_conjClass_bound_of_fixed_smallConjIndex_one
    (W : ℕ → FiniteCommProbWitness) {p : ℝ} (hp : 0 < p)
    (hlower : ∀ n, p / 2 < (W n).probability)
    (M : ℕ) (hindex : ∀ n, (W n).smallConjIndex M = 1) :
    ∃ B : ℕ, ∀ n (x : (W n).carrier),
      letI := (W n).group
      Nat.card (ConjClasses.mk x).carrier ≤ B := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (4 / p)
  let N := max M N₀
  obtain ⟨L, hL⟩ := exists_nat_gt (12 / p)
  refine ⟨(N + 1) ^ L, ?_⟩
  intro n x
  let Wn := W n
  letI := Wn.group
  letI := Wn.finite
  have hMN : M ≤ N := Nat.le_max_left M N₀
  have hN₀N : N₀ ≤ N := Nat.le_max_right M N₀
  have hN_ge : (4 / p : ℝ) ≤ N :=
    hN₀.trans (by exact_mod_cast hN₀N)
  have hN_one : (0 : ℝ) < N + 1 := by positivity
  have hrecip : 1 / (((N + 1 : ℕ) : ℝ)) ≤ p / 4 := by
    have hp4 : 0 < p / 4 := by positivity
    rw [Nat.cast_add, Nat.cast_one]
    apply (one_div_le hN_one hp4).2
    calc
      1 / (p / 4) = 4 / p := by field_simp
      _ ≤ N := hN_ge
      _ ≤ (N : ℝ) + 1 := by linarith
  have hdensity : p / 4 * Nat.card Wn.carrier <
      Nat.card (SmallConjElements Wn.carrier N) := by
    have hrecip' : 1 / (((N + 1 : ℕ) : ℝ)) ≤ (p / 2) / 2 := by
      convert hrecip using 1
      ring
    have h := half_mul_card_lt_card_smallConjElements_of_lt_commProb
      Wn.carrier hrecip'
        (by simpa [Wn, FiniteCommProbWitness.probability] using hlower n)
    convert h using 1
    ring
  have htopM : smallConjSubgroup Wn.carrier M = ⊤ :=
    Subgroup.index_eq_one.mp (by
      simpa [Wn, FiniteCommProbWitness.smallConjIndex] using hindex n)
  have htopN : smallConjSubgroup Wn.carrier N = ⊤ := by
    apply top_unique
    rw [← htopM]
    exact smallConjSubgroup_mono Wn.carrier hMN
  exact conjClass_card_le_pow_of_smallConj_density_index_one Wn.carrier hp N L
    hdensity (Subgroup.index_eq_one.mpr htopN) hL x

lemma exists_uniform_commutator_bound_of_fixed_smallConjIndex_one
    (W : ℕ → FiniteCommProbWitness) {p : ℝ} (hp : 0 < p)
    (hlower : ∀ n, p / 2 < (W n).probability)
    (M : ℕ) (hindex : ∀ n, (W n).smallConjIndex M = 1) :
    ∃ B : ℕ, ∀ n,
      letI := (W n).group
      Nat.card (commutator (W n).carrier) ≤ B := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_conjClass_bound_of_fixed_smallConjIndex_one W hp hlower M hindex
  refine ⟨bfcCommutatorBound C, ?_⟩
  intro n
  let Wn := W n
  letI := Wn.group
  letI := Wn.finite
  exact card_commutator_le_bfcCommutatorBound_of_conjClass_card_le
    Wn.carrier C (hC n)

end

end Submission.Helpers
