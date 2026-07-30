import ChallengeDeps
import Submission.Helpers

open LeanEval.Dynamics
open Filter Topology

namespace Submission

/-ResultProofDefinitionsBegin-/

-- helpers for the proof
open Set

/-- A compact space has a minimal nonempty closed forward-invariant set for a
continuous self-map.  This is the little Zorn argument used below. -/
lemma fw_exists_minimal {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [Nonempty Y] (f : Y → Y) (hf : Continuous f) :
    ∃ A : Set Y, A.Nonempty ∧ IsClosed A ∧ (MapsTo f A A) ∧
      ∀ B : Set Y, B.Nonempty → IsClosed B → MapsTo f B B → B ⊆ A → A ⊆ B := by
  classical
  let S : Set (Set Y) := {A : Set Y | A.Nonempty ∧ IsClosed A ∧ MapsTo f A A}
  have hz : ∃ m, Minimal (· ∈ S) m := by
    apply zorn_superset S
    intro c hc hchain
    by_cases hne : c.Nonempty
    · letI : Nonempty c := ⟨⟨hne.choose, hne.choose_spec⟩⟩
      refine ⟨⋂₀ c, ?_, ?_⟩
      · have hdir : DirectedOn (· ⊇ ·) c := by
          intro a ha b hb
          rcases hchain.total ha hb with hab | hba
          · exact ⟨a, ha, by exact Subset.rfl, by exact hab⟩
          · exact ⟨b, hb, by exact hba, by exact Subset.rfl⟩
        have hninter : (⋂₀ c).Nonempty :=
          IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
            (S := c) hdir
            (fun U hU => (hc hU).1)
            (fun U hU => (hc hU).2.1.isCompact)
            (fun U hU => (hc hU).2.1)
        refine ⟨hninter, ?_, ?_⟩
        · exact isClosed_sInter (fun U hU => (hc hU).2.1)
        · intro y hy
          -- every member of the chain contains `f y`
          have : ∀ U ∈ c, f y ∈ U := by
            intro U hU
            have hyU : y ∈ U := Set.mem_sInter.mp hy U hU
            exact (hc hU).2.2 hyU
          exact Set.mem_sInter.mpr this
      · intro U hU
        exact sInter_subset_of_mem hU
    · refine ⟨Set.univ, ?_, ?_⟩
      · refine ⟨Set.univ_nonempty, isClosed_univ, ?_⟩
        intro y hy
        trivial
      · intro U hU
        exfalso
        exact hne ⟨U, hU⟩
  rcases hz with ⟨A, hAmin⟩
  have hAS : A ∈ S := hAmin.1
  refine ⟨A, hAS.1, hAS.2.1, hAS.2.2, ?_⟩
  intro B hBn hBc hBi hBA
  have hBS : B ∈ S := ⟨hBn, hBc, hBi⟩
  exact hAmin.2 hBS hBA



def fwGood {Y : Type*} [MetricSpace Y] (g : Y → Y)
    (d N : ℕ) (e : ℝ) : Set Y :=
  {y | ∃ n : ℕ, N < n ∧ ∀ j : ℕ, j ≤ d → dist (g^[j*n] y) y < e}

lemma fwGood_open {Y : Type*} [MetricSpace Y] (g : Y → Y)
    (hg : Continuous g) (d N : ℕ) (e : ℝ) : IsOpen (fwGood g d N e) := by
  classical
  -- for a fixed witness the finitely many inequalities are open
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  rcases hy with ⟨n, hn, hny⟩
  let V : Set Y := ⋂ j ∈ Finset.range (d+1),
      {z : Y | dist (g^[j*n] z) z < e}
  have hVo : IsOpen V := by
    dsimp [V]
    apply isOpen_biInter_finset
    intro j hj
    exact isOpen_lt ((hg.iterate (j*n)).dist continuous_id) continuous_const
  refine ⟨V, ?_, hVo, ?_⟩
  · intro z hz
    refine ⟨n, hn, ?_⟩
    intro j hjd
    have hjr : j ∈ Finset.range (d+1) := by
      simp only [Finset.mem_range]
      omega
    have hz' : z ∈ {w : Y | dist (g^[j*n] w) w < e} :=
      Set.mem_iInter.mp (Set.mem_iInter.mp hz j) hjr
    exact hz'
  · apply Set.mem_iInter.mpr
    intro j
    apply Set.mem_iInter.mpr
    intro hj
    have hjd : j ≤ d := by
      simpa [Finset.mem_range] using (show j < d+1 from (by exact (Finset.mem_range.mp hj)))
    exact hny j hjd


/-- In a compact system in which every orbit hits every nonempty open set,
the elementary open multiple-return sets are dense.  The only combinatorics
here is van der Waerden in its homothetic-copy form. -/
lemma fwGood_dense {Y : Type*} [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (g : Y → Y) (hg : Continuous g)
    (hhit : ∀ (y : Y) (U : Set Y), IsOpen U → U.Nonempty →
       ∃ i : ℕ, (g^[i]) y ∈ U)
    (d N : ℕ) {e : ℝ} (he : 0 < e) : Dense (fwGood g d N e) := by
  classical
  rw [dense_iff_inter_open]
  intro V hVo hVn
  rcases hVn with ⟨y0, hy0⟩
  -- a very small open ball inside the prescribed open set
  rcases (Metric.isOpen_iff.mp hVo y0 hy0) with ⟨r, hr, hball⟩
  let δ : ℝ := min r (e/4)
  have hδ : 0 < δ := lt_min hr (by linarith)
  have hδe : δ ≤ e/4 := min_le_right _ _
  let U : Set Y := Metric.ball y0 δ
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUn : U.Nonempty := ⟨y0, Metric.mem_ball_self hδ⟩
  have hUV : U ⊆ V := by
    intro z hz
    apply hball
    -- the little ball is still inside the old one
    have hz' : dist z y0 < δ := (Metric.mem_ball.mp hz)
    exact Metric.mem_ball.mpr (lt_of_lt_of_le hz' (min_le_left _ _))
  -- finitely many forward preimages of U cover the compact space
  have hcover : (Set.univ : Set Y) ⊆ ⋃ i : ℕ, (g^[i]) ⁻¹' U := by
    intro z hz
    rcases hhit z U hUo hUn with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  rcases isCompact_univ.elim_finite_subcover
      (fun i : ℕ => (g^[i]) ⁻¹' U)
      (fun i => (hg.iterate i).isOpen_preimage U hUo)
      hcover with ⟨I, hI⟩
  have hchoice : ∀ z : Y, ∃ i : {m // m ∈ I}, (g^[ (i : ℕ) ]) z ∈ U := by
    intro z
    have hz0 : z ∈ (Set.univ : Set Y) := trivial
    have hz := hI hz0
    -- unpack the finite union
    simp only [Set.mem_iUnion] at hz
    rcases hz with ⟨i, hi, hiz⟩
    exact ⟨⟨i, hi⟩, hiz⟩
  -- color a time by one of those finitely many further times
  let C : ℕ → {m // m ∈ I} := fun k => (hchoice ((g^[k]) y0)).choose
  have hC : ∀ k : ℕ, (g^[ ((C k : {m // m ∈ I}) : ℕ) ])
          ((g^[k]) y0) ∈ U := by
    intro k
    exact (hchoice ((g^[k]) y0)).choose_spec
  let q : ℕ := N+1
  let S : Finset ℕ := (Finset.range (d+1)).image (fun j => q*j)
  obtain ⟨a, ha, b, c, hc⟩ :=
    Combinatorics.exists_mono_homothetic_copy S C
  let n : ℕ := a*q
  have hnN : N < n := by
    dsimp [n, q]
    have ha' : 0 < a := ha
    have hbound : N+1 ≤ a * (N+1) := by
      have haone : 1 ≤ a := ha'
      nlinarith
    omega
  let m : ℕ := (c : ℕ)
  let y : Y := (g^[b + m]) y0
  have hret : ∀ j : ℕ, j ≤ d → (g^[j*n]) y ∈ U := by
    intro j hj
    have hjs : q*j ∈ S := by
      dsimp [S]
      apply Finset.mem_image.mpr
      refine ⟨j, ?_, rfl⟩
      simp only [Finset.mem_range]
      omega
    have hcol : C (a • (q*j) + b) = c := hc _ hjs
    have hz := hC (a • (q*j) + b)
    rw [hcol] at hz
    -- write both iterates as one iterate of y0
    change (g^[j*n]) ((g^[b+m]) y0) ∈ U
    have hidx : j*n + (b+m) = m + (a • (q*j) + b) := by
      dsimp [n, m]
      ring
    rw [← Function.iterate_add_apply]
    rw [hidx]
    rw [Function.iterate_add_apply]
    exact hz
  have hyU : y ∈ U := by
    have := hret 0 (by omega)
    simpa using this
  refine ⟨y, hUV hyU, ?_⟩
  refine ⟨n, hnN, ?_⟩
  intro j hj
  have h1 : (g^[j*n]) y ∈ U := hret j hj
  -- two points of the tiny ball have distance < e
  have hd1 : dist ((g^[j*n]) y) y0 < δ := Metric.mem_ball.mp h1
  have hd2 : dist y y0 < δ := Metric.mem_ball.mp hyU
  calc
    dist ((g^[j*n]) y) y ≤ dist ((g^[j*n]) y) y0 + dist y0 y := dist_triangle _ _ _
    _ = dist ((g^[j*n]) y) y0 + dist y y0 := by rw [dist_comm y0 y]
    _ < δ + δ := add_lt_add hd1 hd2
    _ < e := by nlinarith



lemma fw_recurrent_of_hit {Y : Type*} [MetricSpace Y] [CompactSpace Y]
    [Nonempty Y] (g : Y → Y) (hg : Continuous g)
    (hhit : ∀ (y : Y) (U : Set Y), IsOpen U → U.Nonempty →
       ∃ i : ℕ, (g^[i]) y ∈ U) :
    ∃ y : Y, IsMultiplyRecurrent g y := by
  classical
  let E : (ℕ × ℕ × ℕ) → Set Y := fun t =>
    fwGood g t.1 t.2.2 (1 / ((t.2.1 + 1 : ℕ) : ℝ))
  have hpos : ∀ p : ℕ, (0:ℝ) < 1 / ((p+1 : ℕ) : ℝ) := by
    intro p
    positivity
  have hEd : Dense (⋂ t, E t) := by
    apply dense_iInter_of_isOpen
    · intro t
      exact fwGood_open g hg _ _ _
    · intro t
      exact fwGood_dense g hg hhit _ _ (hpos _)
  rcases hEd.exists_mem_open (X := Y) isOpen_univ (Set.univ_nonempty) with ⟨y, hy, _⟩
  have hyE : ∀ d p N : ℕ,
      ∃ n : ℕ, N < n ∧ ∀ j : ℕ, j ≤ d →
        dist (g^[j*n] y) y < (1 / ((p+1 : ℕ) : ℝ)) := by
    intro d p N
    have hmem : y ∈ E (d, p, N) := Set.mem_iInter.mp hy (d,p,N)
    exact hmem
  refine ⟨y, ?_⟩
  intro d hdpos
  -- choose successively larger witnesses with successively smaller errors
  let w : ℕ → ℕ → ℕ := fun p B => (hyE d p B).choose
  have hw : ∀ p B, B < w p B ∧ ∀ j : ℕ, j ≤ d →
          dist (g^[j * (w p B)] y) y < (1 / ((p+1 : ℕ) : ℝ)) := by
    intro p B
    exact (hyE d p B).choose_spec
  let a : ℕ → ℕ := fun k =>
    Nat.rec (w 0 0) (fun r prev => w (r+1) prev) k
  have ha0 : a 0 = w 0 0 := rfl
  have has : ∀ k : ℕ, a (k+1) = w (k+1) (a k) := by
    intro k
    rfl
  have hainc : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro k
    rw [has k]
    exact (hw (k+1) (a k)).1
  have haerr : ∀ k : ℕ, ∀ j : ℕ, j ≤ d →
          dist (g^[j * a k] y) y < (1 / ((k+1 : ℕ) : ℝ)) := by
    intro k j hj
    cases k with
    | zero =>
        simpa [ha0] using (hw 0 0).2 j hj
    | succ k =>
        rw [has k]
        exact (hw (k+1) (a k)).2 j hj
  refine ⟨a, hainc, ?_⟩
  intro j hj hjd
  refine (Metric.tendsto_atTop).2 ?_
  intro ε hε
  have hlim : Tendsto (fun k : ℕ => (1:ℝ) / ((k+1 : ℕ) : ℝ))
        atTop (𝓝 (0:ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hev : ∀ᶠ k : ℕ in atTop, (1:ℝ) / ((k+1 : ℕ) : ℝ) < ε :=
    (tendsto_order.1 hlim).2 ε hε
  rcases (Filter.eventually_atTop.1 hev) with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  exact lt_trans (haerr k j hjd) (hK k hk)

/-ResultProofDefinitionsEnd-/


theorem furstenberg_topological_recurrence {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X] (T : X ≃ₜ X) :
    ∃ x : X, IsMultiplyRecurrent (T : X → X) x := by
  classical
  let f : X → X := (T : X → X)
  have hf : Continuous f := T.continuous
  rcases fw_exists_minimal f hf with ⟨A, hAn, hAc, hAi, hAmin⟩
  let Y := {x : X // x ∈ A}
  letI : Nonempty Y := Set.Nonempty.to_subtype hAn
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hAc.isCompact
  let g : Y → Y := fun y => ⟨f (y:X), hAi y.property⟩
  have hg : Continuous g := by
    exact Continuous.subtype_mk (hf.comp continuous_subtype_val) _
  -- every orbit in this subsystem hits every relatively open set
  have hhit : ∀ (y : Y) (U : Set Y), IsOpen U → U.Nonempty →
       ∃ i : ℕ, (g^[i]) y ∈ U := by
    intro y U hUo hUn
    -- look at the closure in X of the ordinary orbit
    let s : Set X := Set.range (fun n : ℕ => (f^[n]) (y:X))
    let B : Set X := closure s
    have hsn : s.Nonempty := by
      refine ⟨(y:X), ?_⟩
      exact ⟨0, by simp⟩
    have hBn : B.Nonempty := by
      exact hsn.mono (subset_closure (s := s))
    have hBc : IsClosed B := isClosed_closure
    have hsinv : MapsTo f s s := by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      refine ⟨n+1, ?_⟩
      simpa [Function.iterate_succ_apply']
    have hBi : MapsTo f B B := by
      exact hsinv.closure hf
    have hsA : s ⊆ A := by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      exact hAi.iterate n y.property
    have hBA : B ⊆ A := by
      exact (hAc.closure_subset_iff).2 hsA
    have hAB : A ⊆ B := hAmin B hBn hBc hBi hBA
    -- open sets in a subtype are traces of open sets upstairs
    rcases (isOpen_induced_iff.mp hUo) with ⟨O, hOo, hOU⟩
    rcases hUn with ⟨u, hu⟩
    have huO : (u:X) ∈ O := by
      have hu' : u ∈ (fun v : Y => (v:X)) ⁻¹' O := by
        rw [hOU]
        exact hu
      exact hu'
    have hcl : (u:X) ∈ closure s := hAB u.property
    rcases (mem_closure_iff.mp hcl O hOo huO) with ⟨z, hzO, hzs⟩
    rcases hzs with ⟨i, rfl⟩
    have hsem : Function.Semiconj (fun v : Y => (v:X)) g f := by
      intro v
      rfl
    have hv : (((g^[i]) y : Y) : X) = (f^[i]) (y:X) := hsem.iterate_right i y
    refine ⟨i, ?_⟩
    rw [← hOU]
    change (((g^[i]) y : Y) : X) ∈ O
    rw [hv]
    exact hzO
  rcases fw_recurrent_of_hit g hg hhit with ⟨y, hy⟩
  refine ⟨(y:X), ?_⟩
  intro d hd
  rcases hy d hd with ⟨n, hn, hny⟩
  refine ⟨n, hn, ?_⟩
  intro j hj hjd
  have hsub : Tendsto (fun k : ℕ => (g^[j * n k]) y)
        atTop (𝓝 y) := hny j hj hjd
  have hto : Tendsto
        ((fun v : Y => (v:X)) ∘ (fun k : ℕ => (g^[j * n k]) y))
        atTop (𝓝 (y:X)) :=
      (continuous_subtype_val.tendsto y).comp hsub
  have hsem : Function.Semiconj (fun v : Y => (v:X)) g f := by
    intro v
    rfl
  -- the iterates in the subsystem really are the original iterates
  have heq : (fun k : ℕ => (T : X → X)^[j * n k] (y:X)) =
      ((fun v : Y => (v:X)) ∘ (fun k : ℕ => (g^[j * n k]) y)) := by
    funext k
    exact (hsem.iterate_right (j * n k) y).symm
  rw [heq]
  exact hto


end Submission
