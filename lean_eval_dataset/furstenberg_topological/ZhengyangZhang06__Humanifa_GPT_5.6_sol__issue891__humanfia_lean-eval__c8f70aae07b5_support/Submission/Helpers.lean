import Mathlib

open Filter Function Set Topology

namespace Submission.Helpers

private theorem exists_minimal_closed_invariant {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] (f : X → X) :
    ∃ M : Set X, M.Nonempty ∧ IsClosed M ∧ MapsTo f M M ∧
      ∀ A : Set X, A.Nonempty → IsClosed A → MapsTo f A A → A ⊆ M → M ⊆ A := by
  let C : Set (Set X) := {A | A.Nonempty ∧ IsClosed A ∧ MapsTo f A A}
  obtain ⟨M, hM⟩ := zorn_superset C fun c hcC hc ↦ by
    rcases c.eq_empty_or_nonempty with rfl | hcne
    · refine ⟨univ, ⟨Set.univ_nonempty, isClosed_univ, fun _ _ ↦ mem_univ _⟩, ?_⟩
      simp
    · haveI : Nonempty c := hcne.to_subtype
      refine ⟨⋂₀ c, ⟨?_, isClosed_sInter (fun A hA ↦ (hcC hA).2.1), ?_⟩,
        fun A hA ↦ sInter_subset_of_mem hA⟩
      · apply IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        · intro A hA B hB
          rcases hc.total hA hB with hAB | hBA
          · exact ⟨A, hA, Subset.rfl, hAB⟩
          · exact ⟨B, hB, hBA, Subset.rfl⟩
        · exact fun A hA ↦ (hcC hA).1
        · exact fun A hA ↦ (hcC hA).2.1.isCompact
        · exact fun A hA ↦ (hcC hA).2.1
      · intro x hx
        rw [mem_sInter] at hx ⊢
        exact fun A hA ↦ (hcC hA).2.2 (hx A hA)
  refine ⟨M, hM.prop.1, hM.prop.2.1, hM.prop.2.2, ?_⟩
  intro A hAne hAcl hAinv hAM
  exact hM.2 ⟨hAne, hAcl, hAinv⟩ hAM

private theorem coe_restrict_iterate {X : Type*} {f : X → X} {M : Set X}
    (hM : MapsTo f M M) (n : ℕ) (x : M) :
    ((fun y : M ↦ ⟨f y, hM y.2⟩)^[n] x : M) = f^[n] (x : X) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ_apply, iterate_succ_apply, ih]

private theorem denseRange_restrict_iterate {X : Type*} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) {M : Set X} (hMcl : IsClosed M)
    (hMinv : MapsTo f M M)
    (hMmin : ∀ A : Set X, A.Nonempty → IsClosed A → MapsTo f A A → A ⊆ M → M ⊆ A)
    (x : M) :
    DenseRange (fun n : ℕ ↦ (fun y : M ↦ ⟨f y, hMinv y.2⟩)^[n] x) := by
  let orbit : Set X := range fun n : ℕ ↦ f^[n] (x : X)
  have horbit_ne : orbit.Nonempty := range_nonempty _
  have horbit_map : MapsTo f orbit orbit := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n + 1, iterate_succ_apply' f n (x : X)⟩
  have horbit_sub : orbit ⊆ M := by
    rintro _ ⟨n, rfl⟩
    change f^[n] (x : X) ∈ M
    rw [← coe_restrict_iterate hMinv n x]
    exact ((fun y : M ↦ ⟨f y, hMinv y.2⟩)^[n] x).2
  have hclosure_sub : closure orbit ⊆ M := closure_minimal horbit_sub hMcl
  have hclosure_eq : closure orbit = M :=
    Subset.antisymm hclosure_sub <|
      hMmin (closure orbit) horbit_ne.closure isClosed_closure (horbit_map.closure hf)
        hclosure_sub
  rw [DenseRange, Subtype.dense_iff]
  have himage :
      ((fun y : M ↦ (y : X)) ''
          range (fun n : ℕ ↦ (fun y : M ↦ ⟨f y, hMinv y.2⟩)^[n] x)) = orbit := by
    ext y
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (coe_restrict_iterate hMinv n x).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(fun y : M ↦ ⟨f y, hMinv y.2⟩)^[n] x, ⟨n, rfl⟩,
        coe_restrict_iterate hMinv n x⟩
  rw [himage, hclosure_eq]

private def approxReturn {X : Type*} [PseudoMetricSpace X] (f : X → X)
    (d q : ℕ) (ε : ℝ) : Set X :=
  {x | ∃ n : ℕ, q < n ∧ ∀ j : ℕ, j ≤ d → dist (f^[j * n] x) x < ε}

private theorem isOpen_approxReturn {X : Type*} [PseudoMetricSpace X]
    {f : X → X} (hf : Continuous f) (d q : ℕ) (ε : ℝ) :
    IsOpen (approxReturn f d q ε) := by
  have heq : approxReturn f d q ε =
      ⋃ n : {n : ℕ // q < n}, ⋂ j : Fin (d + 1),
        {x | dist (f^[((j : ℕ) * (n : ℕ))] x) x < ε} := by
    ext x
    simp only [approxReturn, mem_setOf_eq, mem_iUnion, mem_iInter]
    constructor
    · rintro ⟨n, hn, h⟩
      exact ⟨⟨n, hn⟩, fun j ↦ h j (Nat.le_of_lt_succ j.2)⟩
    · rintro ⟨n, h⟩
      exact ⟨n, n.2, fun j hj ↦ h ⟨j, Nat.lt_succ_iff.2 hj⟩⟩
  rw [heq]
  exact isOpen_iUnion fun n ↦ isOpen_iInter_of_finite fun j ↦
    isOpen_lt ((hf.iterate _).dist continuous_id) continuous_const

private theorem dense_approxReturn {X : Type*} [MetricSpace X] [CompactSpace X]
    [Nonempty X] {f : X → X} (hf : Continuous f)
    (hdense : ∀ x : X, DenseRange fun n : ℕ ↦ f^[n] x)
    (d q : ℕ) {ε : ℝ} (hε : 0 < ε) : Dense (approxReturn f d q ε) := by
  rw [dense_iff_inter_open]
  intro V hV hVne
  obtain ⟨z, hzV⟩ := hVne
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV z hzV
  let δ := min r (ε / 3)
  have hδ : 0 < δ := lt_min hr (div_pos hε (by norm_num))
  let U := Metric.ball z δ
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUne : U.Nonempty := ⟨z, by simp [U, hδ]⟩
  have hUV : U ⊆ V := by
    intro y hy
    apply hrV
    exact lt_of_lt_of_le hy (min_le_left r (ε / 3))
  have hUdiam : ∀ {x y : X}, x ∈ U → y ∈ U → dist x y < ε := by
    intro x y hx hy
    change dist x z < δ at hx
    change dist y z < δ at hy
    have hx' : dist x z < δ := hx
    have hy' : dist z y < δ := by simpa [dist_comm] using hy
    calc
      dist x y ≤ dist x z + dist z y := dist_triangle x z y
      _ < δ + δ := add_lt_add hx' hy'
      _ ≤ ε / 3 + ε / 3 := add_le_add (min_le_right r (ε / 3)) (min_le_right r (ε / 3))
      _ < ε := by linarith
  have hcover : univ ⊆ ⋃ n : ℕ, (f^[n]) ⁻¹' U := by
    intro x _
    obtain ⟨n, hn⟩ := (hdense x).exists_mem_open hUopen hUne
    exact mem_iUnion.2 ⟨n, hn⟩
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun n : ℕ ↦ (f^[n]) ⁻¹' U)
    (fun n ↦ hUopen.preimage (hf.iterate n)) hcover
  let x₀ : X := Classical.arbitrary X
  have hchoice (s : ℕ) : ∃ i : ℕ, i ∈ I ∧ f^[i] (f^[s] x₀) ∈ U := by
    have hs := hI (show f^[s] x₀ ∈ univ from mem_univ _)
    rcases mem_iUnion.1 hs with ⟨i, hs⟩
    rcases mem_iUnion.1 hs with ⟨hi, hs⟩
    exact ⟨i, hi, hs⟩
  choose c hcI hcU using hchoice
  let C : ℕ → {i : ℕ // i ∈ I} := fun s ↦ ⟨c s, hcI s⟩
  let scale := q + 1
  obtain ⟨a, ha, b, color, hmono⟩ :=
    Combinatorics.exists_mono_homothetic_copy (Finset.range (d + 1))
      (fun s : ℕ ↦ C (scale * s))
  let idx : ℕ → ℕ := fun j ↦ scale * (a * j + b)
  have hcolor (j : ℕ) (hj : j ≤ d) : c (idx j) = c (idx 0) := by
    have hjc := hmono j (Finset.mem_range.2 (Nat.lt_succ_iff.2 hj))
    have h0c := hmono 0 (by simp)
    have h := congrArg Subtype.val (hjc.trans h0c.symm)
    simpa [C, idx, nsmul_eq_mul] using h
  let n := scale * a
  let y := f^[c (idx 0)] (f^[idx 0] x₀)
  have hyU : y ∈ U := hcU (idx 0)
  have hn : q < n := by
    calc
      q < q + 1 := Nat.lt_succ_self q
      _ = scale * 1 := by simp [scale]
      _ ≤ scale * a := Nat.mul_le_mul_left scale ha
      _ = n := rfl
  have hiter (j : ℕ) (hj : j ≤ d) :
      f^[j * n] y = f^[c (idx j)] (f^[idx j] x₀) := by
    calc
      f^[j * n] y = f^[j * n + c (idx 0) + idx 0] x₀ := by
        change f^[j * n] (f^[c (idx 0)] (f^[idx 0] x₀)) = _
        rw [← iterate_add_apply, ← iterate_add_apply]
      _ = f^[c (idx j) + idx j] x₀ := by
        congr 1
        rw [hcolor j hj]
        simp only [n, idx, scale]
        ring
      _ = f^[c (idx j)] (f^[idx j] x₀) := iterate_add_apply _ _ _ _
  refine ⟨y, hUV hyU, ?_⟩
  exact ⟨n, hn, fun j hj ↦ by
    rw [hiter j hj]
    exact hUdiam (hcU (idx j)) hyU⟩

private theorem exists_multiply_recurrent_of_dense_orbits {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X] {f : X → X} (hf : Continuous f)
    (hdense : ∀ x : X, DenseRange fun n : ℕ ↦ f^[n] x) :
    ∃ x : X, ∀ d : ℕ, 1 ≤ d →
      ∃ n : ℕ → ℕ, StrictMono n ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ d → Tendsto (fun k : ℕ ↦ f^[j * n k] x) atTop (𝓝 x) := by
  classical
  let R : ℕ × (ℕ × ℕ) → Set X := fun p ↦
    approxReturn f p.1 p.2.2 (1 / ((p.2.1 : ℝ) + 1))
  have hRopen : ∀ p, IsOpen (R p) := fun p ↦ isOpen_approxReturn hf _ _ _
  have hRdense : ∀ p, Dense (R p) := fun p ↦
    dense_approxReturn hf hdense _ _ (by positivity)
  obtain ⟨x, hx⟩ := (dense_iInter_of_isOpen hRopen hRdense).nonempty
  refine ⟨x, fun d _hd ↦ ?_⟩
  have hxR (m q : ℕ) :
      x ∈ approxReturn f d q (1 / ((m : ℝ) + 1)) := by
    have h := mem_iInter.1 hx (d, (m, q))
    exact h
  have hex (m q : ℕ) : ∃ n : ℕ, q < n ∧
      ∀ j : ℕ, j ≤ d → dist (f^[j * n] x) x < 1 / ((m : ℝ) + 1) := hxR m q
  let pick (m q : ℕ) : ℕ := Classical.choose (hex m q)
  have hpick (m q : ℕ) : q < pick m q ∧
      ∀ j : ℕ, j ≤ d → dist (f^[j * pick m q] x) x < 1 / ((m : ℝ) + 1) :=
    Classical.choose_spec (hex m q)
  let n : ℕ → ℕ := fun k ↦ Nat.rec (pick 0 0) (fun k previous ↦ pick (k + 1) previous) k
  have hn_zero : n 0 = pick 0 0 := by rfl
  have hn_succ (k : ℕ) : n (k + 1) = pick (k + 1) (n k) := by
    simp [n]
  have hn_bound (k j : ℕ) (hj : j ≤ d) :
      dist (f^[j * n k] x) x < 1 / ((k : ℝ) + 1) := by
    rcases k with _ | k
    · rw [hn_zero]
      exact (hpick 0 0).2 j hj
    · rw [hn_succ]
      exact (hpick (k + 1) (n k)).2 j hj
  refine ⟨n, strictMono_nat_of_lt_succ (fun k ↦ ?_), ?_⟩
  · rw [hn_succ]
    exact (hpick (k + 1) (n k)).1
  · intro j _hj hjd
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ (hn_bound k j hjd).le)
      tendsto_one_div_add_atTop_nhds_zero_nat

/-- A continuous self-map of a nonempty compact metric space has a multiply recurrent point. -/
theorem exists_multiply_recurrent_of_continuous {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X] (f : X → X) (hf : Continuous f) :
    ∃ x : X, ∀ d : ℕ, 1 ≤ d →
      ∃ n : ℕ → ℕ, StrictMono n ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ d → Tendsto (fun k : ℕ ↦ f^[j * n k] x) atTop (𝓝 x) := by
  obtain ⟨M, hMne, hMcl, hMinv, hMmin⟩ := exists_minimal_closed_invariant f
  letI : Nonempty M := hMne.to_subtype
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hMcl.isCompact
  let g : M → M := fun x ↦ ⟨f x, hMinv x.2⟩
  have hg : Continuous g := by fun_prop
  have hg_dense (x : M) : DenseRange fun n : ℕ ↦ g^[n] x := by
    simpa only [g] using denseRange_restrict_iterate f hf hMcl hMinv hMmin x
  obtain ⟨x, hx⟩ := exists_multiply_recurrent_of_dense_orbits hg hg_dense
  refine ⟨x, fun d hd ↦ ?_⟩
  obtain ⟨n, hn, hlim⟩ := hx d hd
  refine ⟨n, hn, fun j hj hjd ↦ ?_⟩
  have h := continuous_subtype_val.continuousAt.tendsto.comp (hlim j hj hjd)
  change Tendsto (fun k : ℕ ↦ ((g^[j * n k] x : M) : X)) atTop (𝓝 (x : X)) at h
  simpa only [g, coe_restrict_iterate hMinv] using h

end Submission.Helpers
