import ChallengeDeps

namespace Submission.LIS

open LeanEval.ProgramVerification

def SortedArray (xs : Array Nat) : Prop :=
  xs.toList.Pairwise (· ≤ ·)

theorem getElem_le_of_lt {xs : Array Nat} (hsorted : SortedArray xs)
    {i j : Nat} (hij : i < j) (hj : j < xs.size) :
    xs[i] ≤ xs[j] := by
  rw [SortedArray, List.pairwise_iff_getElem] at hsorted
  have hi : i < xs.toList.length := by simpa using hij.trans hj
  have hj' : j < xs.toList.length := by simpa using hj
  have h := hsorted i j hi hj' hij
  simpa only [Array.getElem_toList] using h

def GoResult (needle : Nat) (xs : Array Nat) (lo hi pos : Nat) : Prop :=
  lo ≤ pos ∧ pos ≤ hi ∧
    (∀ j, (hj : j < xs.size) → j < pos → xs[j] ≤ needle) ∧
    (∀ j, (hj : j < xs.size) → pos ≤ j → needle < xs[j])

theorem go_spec (needle : Nat) (xs : Array Nat) (hsorted : SortedArray xs)
    (lo hi : Nat) (hhi : hi ≤ xs.size) (hlo : lo ≤ hi)
    (hbefore : ∀ j, (hj : j < xs.size) → j < lo → xs[j] ≤ needle)
    (hafter : ∀ j, (hj : j < xs.size) → hi ≤ j → needle < xs[j]) :
    GoResult needle xs lo hi (minRearrange.go needle xs lo hi hhi) := by
  induction lo, hi, hhi using minRearrange.go.induct needle xs with
  | case1 lo hi hhi h mid hmid ih =>
      rw [minRearrange.go.eq_def, dif_pos h, if_pos hmid]
      have hmid_lt : mid < hi := by dsimp [mid]; omega
      have hlo_mid : lo ≤ mid := by dsimp [mid]; omega
      have hnext : mid + 1 ≤ hi := by dsimp [mid]; omega
      have hbefore' :
          ∀ j, (hjsize : j < xs.size) →
            j < mid + 1 → xs[j] ≤ needle := by
        intro j hjsize hj
        by_cases hjlo : j < lo
        · exact hbefore j hjsize hjlo
        · have hjmid : j ≤ mid := by omega
          rcases hjmid.eq_or_lt with hjmid | hjmid
          · simpa [hjmid] using hmid
          · exact (getElem_le_of_lt hsorted hjmid
              (hmid_lt.trans_le hhi)).trans hmid
      obtain ⟨hpos_lo, hpos_hi, hpos_before, hpos_after⟩ :=
        ih hnext hbefore' hafter
      have hresult :
          GoResult needle xs lo hi
            (minRearrange.go needle xs (mid + 1) hi hhi) :=
        ⟨(show lo ≤ mid + 1 by omega).trans hpos_lo,
          hpos_hi, hpos_before, hpos_after⟩
      simpa [mid] using hresult
  | case2 lo hi hhi h mid hmid ih =>
      rw [minRearrange.go.eq_def, dif_pos h, if_neg hmid]
      have hmid_lt : mid < hi := by dsimp [mid]; omega
      have hlo_mid : lo ≤ mid := by dsimp [mid]; omega
      have hneedle : needle < xs[mid] := by omega
      have hafter' :
          ∀ j, (hjsize : j < xs.size) →
            mid ≤ j → needle < xs[j] := by
        intro j hjsize hj
        by_cases hhij : hi ≤ j
        · exact hafter j hjsize hhij
        · rcases hj.eq_or_lt with rfl | hj
          · exact hneedle
          · exact hneedle.trans_le (getElem_le_of_lt hsorted hj hjsize)
      obtain ⟨hpos_lo, hpos_hi, hpos_before, hpos_after⟩ :=
        ih hlo_mid hbefore hafter'
      exact ⟨hpos_lo, hpos_hi.trans hmid_lt.le, hpos_before, hpos_after⟩
  | case3 lo hi hhi h =>
      rw [minRearrange.go.eq_def, dif_neg h]
      have hlohi : lo = hi := by omega
      subst hi
      exact ⟨le_rfl, le_rfl, hbefore, hafter⟩

theorem upperBound_spec (needle : Nat) (xs : Array Nat)
    (hsorted : SortedArray xs) :
    let pos := minRearrange.upperBound needle xs
    pos ≤ xs.size ∧
      (∀ j, (hj : j < xs.size) → j < pos → xs[j] ≤ needle) ∧
      (∀ j, (hj : j < xs.size) → pos ≤ j → needle < xs[j]) := by
  unfold minRearrange.upperBound
  have h := go_spec needle xs hsorted 0 xs.size (by omega) (by omega)
    (by omega) (by omega)
  simpa [GoResult] using ⟨h.2.1, h.2.2.1, h.2.2.2⟩

theorem upperBound_eq_of_boundary (needle : Nat) (xs : Array Nat)
    (hsorted : SortedArray xs) (q : Nat) (hq : q ≤ xs.size)
    (hbefore : ∀ j, (hj : j < xs.size) → j < q → xs[j] ≤ needle)
    (hafter : ∀ j, (hj : j < xs.size) → q ≤ j → needle < xs[j]) :
    minRearrange.upperBound needle xs = q := by
  obtain ⟨hposSize, hposBefore, hposAfter⟩ :=
    upperBound_spec needle xs hsorted
  apply Nat.le_antisymm
  · by_contra hle
    have hqpos : q < minRearrange.upperBound needle xs := by omega
    have hqSize : q < xs.size := hqpos.trans_le hposSize
    exact (Nat.not_le_of_lt (hafter q hqSize le_rfl))
      (hposBefore q hqSize hqpos)
  · by_contra hle
    have hposq : minRearrange.upperBound needle xs < q := by omega
    have hposSize' : minRearrange.upperBound needle xs < xs.size :=
      hposq.trans_le hq
    exact (Nat.not_le_of_lt (hposAfter _ hposSize' le_rfl))
      (hbefore _ hposSize' hposq)

theorem getElem_setBang_eq {xs : Array Nat} {p j x : Nat}
    (hp : p < xs.size) (hj : j < (xs.setIfInBounds p x).size) :
    (xs.setIfInBounds p x)[j] =
      if j = p then x else xs[j]'(by simpa using hj) := by
  simp only [Array.setIfInBounds, dif_pos hp] at hj ⊢
  by_cases h : j = p
  · subst j
    simp
  · rw [if_neg h]
    exact Array.getElem_set_ne (h := Ne.symm h) ..

theorem sortedArray_set_upperBound (needle : Nat) (xs : Array Nat)
    (hsorted : SortedArray xs)
    (hp : minRearrange.upperBound needle xs < xs.size) :
    SortedArray
      (xs.setIfInBounds (minRearrange.upperBound needle xs) needle) := by
  let p := minRearrange.upperBound needle xs
  obtain ⟨_, hbefore, hafter⟩ := upperBound_spec needle xs hsorted
  rw [SortedArray, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < (xs.setIfInBounds p needle).size := by simpa [p] using hi
  have hj' : j < (xs.setIfInBounds p needle).size := by simpa [p] using hj
  have hgoal :
      (xs.setIfInBounds p needle)[i] ≤
        (xs.setIfInBounds p needle)[j] := by
    rw [getElem_setBang_eq (by simpa [p] using hp) hi',
      getElem_setBang_eq (by simpa [p] using hp) hj']
    by_cases hip : i = p
    · subst i
      simpa [hij.ne'] using (hafter j (by simpa using hj) hij.le).le
    · by_cases hjp : j = p
      · subst j
        simpa [hip] using hbefore i (by simpa using hi) hij
      · simp only [if_neg hip, if_neg hjp]
        exact getElem_le_of_lt hsorted hij (by simpa using hj)
  simpa only [Array.getElem_toList, p] using hgoal

theorem upperBound_set_of_lt (x y : Nat) (xs : Array Nat)
    (hsorted : SortedArray xs) (hyx : y < x)
    (hp : minRearrange.upperBound x xs < xs.size) :
    minRearrange.upperBound y
        (xs.setIfInBounds (minRearrange.upperBound x xs) x) =
      minRearrange.upperBound y xs := by
  let p := minRearrange.upperBound x xs
  let q := minRearrange.upperBound y xs
  obtain ⟨hpSize, hpBefore, hpAfter⟩ := upperBound_spec x xs hsorted
  obtain ⟨hqSize, hqBefore, hqAfter⟩ := upperBound_spec y xs hsorted
  have hqp : q ≤ p := by
    by_contra hle
    have hpq : p < q := by omega
    exact (Nat.not_le_of_lt (hpAfter p (by simpa [p] using hp) le_rfl))
      ((hqBefore p (by simpa [p] using hp) (by simpa [q] using hpq)).trans hyx.le)
  apply upperBound_eq_of_boundary y _ (sortedArray_set_upperBound x xs hsorted hp)
      q (by simpa [q] using hqSize)
  · intro j hjsize hjq
    change (xs.setIfInBounds p x)[j] ≤ y
    rw [getElem_setBang_eq (by simpa [p] using hp) hjsize]
    have hjp : j < p := hjq.trans_le hqp
    rw [if_neg (by simpa [p] using hjp.ne)]
    exact hqBefore j (by simpa using hjsize) (by simpa [q] using hjq)
  · intro j hjsize hqj
    change y < (xs.setIfInBounds p x)[j]
    rw [getElem_setBang_eq (by simpa [p] using hp) hjsize]
    by_cases hjp : j = p
    · subst j
      rw [if_pos (by simp [p])]
      exact hyx
    · rw [if_neg (by simpa [p] using hjp)]
      exact hqAfter j (by simpa using hjsize) (by simpa [q] using hqj)

theorem upperBound_set_of_le (x y : Nat) (xs : Array Nat)
    (hsorted : SortedArray xs) (hxy : x ≤ y)
    (hp : minRearrange.upperBound x xs < xs.size) :
    minRearrange.upperBound y
        (xs.setIfInBounds (minRearrange.upperBound x xs) x) =
      max (minRearrange.upperBound y xs)
        (minRearrange.upperBound x xs + 1) := by
  let p := minRearrange.upperBound x xs
  let q := minRearrange.upperBound y xs
  obtain ⟨hpSize, hpBefore, hpAfter⟩ := upperBound_spec x xs hsorted
  obtain ⟨hqSize, hqBefore, hqAfter⟩ := upperBound_spec y xs hsorted
  have hpq : p ≤ q := by
    by_contra hle
    have hqp : q < p := by omega
    exact (Nat.not_le_of_lt
      (hqAfter q (hqp.trans (by simpa [p] using hp)) le_rfl))
      ((hpBefore q (hqp.trans (by simpa [p] using hp))
        (by simpa [p, q] using hqp)).trans hxy)
  rcases hpq.eq_or_lt with hpq | hpq
  · have hqy : minRearrange.upperBound y xs = p := by
      simpa [q] using hpq.symm
    have hnext : p + 1 ≤ (xs.setIfInBounds p x).size := by
      simpa [p] using hp
    have heq := upperBound_eq_of_boundary y _
      (sortedArray_set_upperBound x xs hsorted hp) (p + 1) hnext
      (fun j hjsize hj => by
        change (xs.setIfInBounds p x)[j] ≤ y
        rw [getElem_setBang_eq (by simpa [p] using hp) hjsize]
        by_cases hjp : j = p
        · subst j
          rw [if_pos (by simp [p])]
          exact hxy
        · rw [if_neg (by simpa [p] using hjp)]
          exact hqBefore j (by simpa using hjsize)
            (by rw [hqy]; omega))
      (fun j hjsize hj => by
        change y < (xs.setIfInBounds p x)[j]
        rw [getElem_setBang_eq (by simpa [p] using hp) hjsize]
        have hjp : j ≠ p := by omega
        rw [if_neg (by simpa [p] using hjp)]
        exact hqAfter j (by simpa using hjsize)
          (by rw [hqy]; omega))
    rw [hqy]
    simpa [p] using heq
  · have hmax : max q (p + 1) = q := max_eq_left (by omega)
    rw [hmax]
    apply upperBound_eq_of_boundary y _ (sortedArray_set_upperBound x xs hsorted hp)
      q (by simpa [q] using hqSize)
    · intro j hjsize hjq
      change (xs.setIfInBounds p x)[j] ≤ y
      rw [getElem_setBang_eq (by simpa [p] using hp) hjsize]
      by_cases hjp : j = p
      · subst j
        rw [if_pos (by simp [p])]
        exact hxy
      · rw [if_neg (by simpa [p] using hjp)]
        exact hqBefore j (by simpa using hjsize) (by simpa [q] using hjq)
    · intro j hjsize hqj
      change y < (xs.setIfInBounds p x)[j]
      rw [getElem_setBang_eq (by simpa [p] using hp) hjsize]
      have hjp : j ≠ p := by omega
      rw [if_neg (by simpa [p] using hjp)]
      exact hqAfter j (by simpa using hjsize) (by simpa [q] using hqj)

def IsNDSubseq (s l : List Nat) : Prop :=
  s.Sublist l ∧ s.Pairwise (· ≤ ·)

def IsBoundedNDSubseq (s l : List Nat) (bound : Nat) : Prop :=
  IsNDSubseq s l ∧ ∀ a ∈ s, a ≤ bound

def IsBoundedLNDSLength (l : List Nat) (bound k : Nat) : Prop :=
  (∃ s : List Nat, IsBoundedNDSubseq s l bound ∧ s.length = k) ∧
    ∀ {s : List Nat}, IsBoundedNDSubseq s l bound → s.length ≤ k

def IsLNDSLength (l : List Nat) (k : Nat) : Prop :=
  (∃ s : List Nat, IsNDSubseq s l ∧ s.length = k) ∧
    ∀ {s : List Nat}, IsNDSubseq s l → s.length ≤ k

theorem ndSubseq_append_cases {s l : List Nat} {x : Nat}
    (h : IsNDSubseq s (l ++ [x])) :
    IsNDSubseq s l ∨
      ∃ t : List Nat, s = t ++ [x] ∧ IsBoundedNDSubseq t l x := by
  obtain ⟨s₁, s₂, rfl, hs₁, hs₂⟩ := List.sublist_append_iff.mp h.1
  rcases List.sublist_singleton.mp hs₂ with rfl | rfl
  · left
    exact ⟨by simpa using hs₁, by simpa using h.2⟩
  · right
    refine ⟨s₁, rfl, ?_⟩
    have hp := List.pairwise_append.mp h.2
    refine ⟨⟨hs₁, hp.1⟩, ?_⟩
    intro a ha
    exact hp.2.2 a ha x (by simp)

theorem boundedNDSubseq_append_cases {s l : List Nat} {x bound : Nat}
    (h : IsBoundedNDSubseq s (l ++ [x]) bound) :
    IsBoundedNDSubseq s l bound ∨
      ∃ t : List Nat, s = t ++ [x] ∧
        IsBoundedNDSubseq t l x ∧ x ≤ bound := by
  rcases ndSubseq_append_cases h.1 with hold | ⟨t, rfl, ht⟩
  · exact Or.inl ⟨hold, h.2⟩
  · refine Or.inr ⟨t, rfl, ht, ?_⟩
    exact h.2 x (by simp)

theorem IsBoundedNDSubseq.append_value {s l : List Nat} {x bound : Nat}
    (h : IsBoundedNDSubseq s l x) (hxb : x ≤ bound) :
    IsBoundedNDSubseq (s ++ [x]) (l ++ [x]) bound := by
  refine ⟨⟨h.1.1.append_right [x], ?_⟩, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨h.1.2, by simp, ?_⟩
    intro a ha b hb
    have hbx : b = x := by simpa using hb
    subst b
    exact h.2 a ha
  · intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact (h.2 a ha).trans hxb
    · exact hxb

theorem IsBoundedNDSubseq.weaken_append {s l : List Nat} {x bound : Nat}
    (h : IsBoundedNDSubseq s l bound) :
    IsBoundedNDSubseq s (l ++ [x]) bound := by
  exact ⟨⟨h.1.1.trans (List.sublist_append_left l [x]), h.1.2⟩, h.2⟩

theorem bounded_length_append_of_le {l : List Nat} {x bound k kx : Nat}
    (hk : IsBoundedLNDSLength l bound k)
    (hkx : IsBoundedLNDSLength l x kx) (hxb : x ≤ bound) :
    IsBoundedLNDSLength (l ++ [x]) bound (max k (kx + 1)) := by
  constructor
  · by_cases hmax : kx + 1 ≤ k
    · obtain ⟨s, hs, hslen⟩ := hk.1
      exact ⟨s, hs.weaken_append, by simpa [max_eq_left hmax] using hslen⟩
    · obtain ⟨s, hs, hslen⟩ := hkx.1
      refine ⟨s ++ [x], hs.append_value hxb, ?_⟩
      simp only [List.length_append, List.length_singleton, hslen]
      rw [max_eq_right (by omega)]
  · intro s hs
    rcases boundedNDSubseq_append_cases hs with hold | ⟨t, rfl, ht, _⟩
    · exact (hk.2 hold).trans (Nat.le_max_left _ _)
    · have htlen := hkx.2 ht
      simp only [List.length_append, List.length_singleton]
      omega

theorem bounded_length_append_of_lt {l : List Nat} {x bound k : Nat}
    (hk : IsBoundedLNDSLength l bound k) (hbx : bound < x) :
    IsBoundedLNDSLength (l ++ [x]) bound k := by
  constructor
  · obtain ⟨s, hs, hslen⟩ := hk.1
    exact ⟨s, hs.weaken_append, hslen⟩
  · intro s hs
    rcases boundedNDSubseq_append_cases hs with hold | ⟨_, _, _, hxb⟩
    · exact hk.2 hold
    · omega

theorem lnds_length_append {l : List Nat} {x k kx : Nat}
    (hk : IsLNDSLength l k) (hkx : IsBoundedLNDSLength l x kx) :
    IsLNDSLength (l ++ [x]) (max k (kx + 1)) := by
  constructor
  · by_cases hmax : kx + 1 ≤ k
    · obtain ⟨s, hs, hslen⟩ := hk.1
      refine ⟨s, ⟨hs.1.trans (List.sublist_append_left l [x]), hs.2⟩, ?_⟩
      simpa [max_eq_left hmax] using hslen
    · obtain ⟨s, hs, hslen⟩ := hkx.1
      refine ⟨s ++ [x], (hs.append_value le_rfl).1, ?_⟩
      simp only [List.length_append, List.length_singleton, hslen]
      rw [max_eq_right (by omega)]
  · intro s hs
    rcases ndSubseq_append_cases hs with hold | ⟨t, rfl, ht⟩
    · exact (hk.2 hold).trans (Nat.le_max_left _ _)
    · have htlen := hkx.2 ht
      simp only [List.length_append, List.length_singleton]
      omega

def LoopInvariant (arr : Array Nat) (sentinel ans i : Nat)
    (dp : Array Nat) : Prop :=
  dp.size = arr.size ∧
    SortedArray dp ∧
    IsLNDSLength (arr.toList.take i) ans ∧
    ∀ bound, bound < sentinel →
      IsBoundedLNDSLength (arr.toList.take i) bound
        (minRearrange.upperBound bound dp)

theorem sortedArray_replicate (n value : Nat) :
    SortedArray (Array.replicate n value) := by
  rw [SortedArray, List.pairwise_iff_getElem]
  intro i j hi hj _
  simp

theorem lndsLength_nil : IsLNDSLength [] 0 := by
  simp [IsLNDSLength, IsNDSubseq]

theorem boundedLNDSLength_nil (bound : Nat) :
    IsBoundedLNDSLength [] bound 0 := by
  simp [IsBoundedLNDSLength, IsBoundedNDSubseq, IsNDSubseq]

theorem upperBound_replicate_of_lt {n value bound : Nat} (h : bound < value) :
    minRearrange.upperBound bound (Array.replicate n value) = 0 := by
  apply upperBound_eq_of_boundary bound _ (sortedArray_replicate n value) 0 (by simp)
  · intro j _ hj
    omega
  · intro j _ _
    simpa using h

theorem initial_loopInvariant (arr : Array Nat) (sentinel : Nat) :
    LoopInvariant arr sentinel 0 0 (Array.replicate arr.size sentinel) := by
  refine ⟨by simp, sortedArray_replicate _ _, ?_, ?_⟩
  · simpa using lndsLength_nil
  · intro bound hbound
    rw [upperBound_replicate_of_lt hbound]
    simpa using boundedLNDSLength_nil bound

theorem take_succ_toList {arr : Array Nat} {i : Nat} (hi : i < arr.size) :
    arr.toList.take (i + 1) = arr.toList.take i ++ [arr[i]] := by
  symm
  convert List.take_concat_get' arr.toList i (by simpa using hi) using 1
  simp

theorem loopInvariant_step {arr dp : Array Nat} {sentinel ans i : Nat}
    (hinv : LoopInvariant arr sentinel ans i dp) (hi : i < arr.size)
    (hvalue : arr[i] < sentinel) :
    let pos := minRearrange.upperBound arr[i] dp
    LoopInvariant arr sentinel (max ans (pos + 1)) (i + 1)
      (dp.setIfInBounds pos arr[i]) := by
  let x := arr[i]
  let pos := minRearrange.upperBound x dp
  have hkx : IsBoundedLNDSLength (arr.toList.take i) x pos := by
    exact hinv.2.2.2 x (by simpa [x] using hvalue)
  have hposPrefix : pos ≤ (arr.toList.take i).length := by
    obtain ⟨s, hs, hslen⟩ := hkx.1
    rw [← hslen]
    exact hs.1.1.length_le
  have hposi : pos ≤ i := hposPrefix.trans (List.length_take_le _ _)
  have hpos : pos < dp.size := by
    rw [hinv.1]
    omega
  refine ⟨?_, sortedArray_set_upperBound x dp hinv.2.1 hpos, ?_, ?_⟩
  · simpa only [Array.size_setIfInBounds] using hinv.1
  · rw [take_succ_toList hi]
    exact lnds_length_append hinv.2.2.1 hkx
  · intro bound hbound
    rw [take_succ_toList hi]
    by_cases hbx : bound < x
    · have hold := hinv.2.2.2 bound hbound
      rw [upperBound_set_of_lt x bound dp hinv.2.1 hbx hpos]
      exact bounded_length_append_of_lt hold hbx
    · have hxb : x ≤ bound := by omega
      have hold := hinv.2.2.2 bound hbound
      rw [upperBound_set_of_le x bound dp hinv.2.1 hxb hpos]
      exact bounded_length_append_of_le hold hkx hxb

theorem loop_returns_lnds (arr : Array Nat) (sentinel ans i : Nat)
    (dp : Array Nat) (hi : i ≤ arr.size)
    (hvalues : ∀ j, (hj : j < arr.size) → arr[j] < sentinel)
    (hinv : LoopInvariant arr sentinel ans i dp) :
    IsLNDSLength arr.toList (minRearrange.loop arr ans i dp hi) := by
  induction ans, i, dp, hi using minRearrange.loop.induct arr with
  | case1 ans dp hi =>
      rw [minRearrange.loop.eq_def, dif_pos rfl]
      have htake : arr.toList.take arr.size = arr.toList := by
        rw [show arr.size = arr.toList.length by simp, List.take_length]
      have hk := hinv.2.2.1
      rw [htake] at hk
      exact hk
  | case2 ans i dp hi hne pos ih =>
      rw [minRearrange.loop.eq_def, dif_neg hne]
      have hi' : i < arr.size := by omega
      exact ih (loopInvariant_step hinv hi' (hvalues i hi'))

theorem getElem_le_max {arr : Array Nat} (h : arr ≠ #[]) {i : Nat}
    (hi : i < arr.size) :
    arr[i] ≤ arr.max h := by
  apply Array.le_max_of_mem
  simp

theorem lis_returns_lnds (arr : Array Nat) :
    IsLNDSLength arr.toList (minRearrange.lis arr) := by
  rw [minRearrange.lis.eq_def]
  split
  · rename_i h
    subst arr
    simpa using lndsLength_nil
  · rename_i h
    let sentinel := arr.max h + 1
    let dp := Array.replicate arr.size sentinel
    apply loop_returns_lnds arr sentinel 0 0 dp (by omega)
    · intro j hj
      have := getElem_le_max h hj
      simp only [sentinel]
      omega
    · exact initial_loopInvariant arr sentinel

end Submission.LIS
