import Submission.Helpers

namespace Submission.Path

open Submission.Helpers

def stepBit (p : Nat × Nat) : Bool :=
  p.1 % 2 = 1

def EncodedStep (p : Nat × Nat) : Prop :=
  if stepBit p then
    p = (2 * (pointBefore p).1 + 1, 2 * (pointBefore p).2)
  else
    p = (2 * (pointBefore p).1, 2 * (pointBefore p).2 + 1)

def ValidStep (n : Nat) (p : Nat × Nat) : Prop :=
  EncodedStep p ∧
    ∃ a, 1 ≤ a ∧ a ≤ n ∧
      (pointBefore p).1 + (pointBefore p).2 = a - 1

def horizontalCount (bits : List Bool) : Nat :=
  (bits.filter id).length

def verticalCount (bits : List Bool) : Nat :=
  (bits.filter (!·)).length

def HasCounts (bits : List Bool) (p : Nat × Nat) : Prop :=
  horizontalCount bits = p.1 ∧ verticalCount bits = p.2

def fillTo (cur target : Nat × Nat) : List Bool :=
  List.replicate (target.1 - cur.1) true ++
    List.replicate (target.2 - cur.2) false

def buildThrough : Nat × Nat → List (Nat × Nat) → List Bool
  | _, [] => []
  | cur, p :: ps =>
      fillTo cur (pointBefore p) ++ [stepBit p] ++
        buildThrough (pointAfter p) ps

def endPoint : Nat × Nat → List (Nat × Nat) → Nat × Nat
  | cur, [] => cur
  | _, p :: ps => endPoint (pointAfter p) ps

def ForcesStep (bits : List Bool) (p : Nat × Nat) : Prop :=
  ∃ before after,
    bits = before ++ [stepBit p] ++ after ∧
      HasCounts before (pointBefore p)

def ForcesSteps (bits : List Bool) (points : List (Nat × Nat)) : Prop :=
  ∀ p ∈ points, ForcesStep bits p

theorem horizontalCount_add_verticalCount (bits : List Bool) :
    horizontalCount bits + verticalCount bits = bits.length := by
  have h := bits.length_eq_length_filter_add id
  simpa [horizontalCount, verticalCount, add_comm] using h.symm

theorem hasCounts_fillTo {base : List Bool} {cur target : Nat × Nat}
    (hbase : HasCounts base cur) (hcur : ComponentLE cur target) :
    HasCounts (base ++ fillTo cur target) target := by
  rcases hbase with ⟨hh, hv⟩
  rcases hcur with ⟨hx, hy⟩
  simp [HasCounts, horizontalCount, verticalCount, fillTo] at hh hv ⊢
  omega

theorem encodedStep_pointAfter {p : Nat × Nat} (h : EncodedStep p) :
    if stepBit p then
      pointAfter p = ((pointBefore p).1 + 1, (pointBefore p).2)
    else
      pointAfter p = ((pointBefore p).1, (pointBefore p).2 + 1) := by
  unfold EncodedStep at h
  cases hbit : stepBit p
  · simp only [hbit, Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    apply Prod.ext <;>
      simp only [pointBefore, pointAfter] at hfst hsnd ⊢ <;> omega
  · simp only [hbit, ↓reduceIte] at h ⊢
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    apply Prod.ext <;>
      simp only [pointBefore, pointAfter] at hfst hsnd ⊢ <;> omega

theorem hasCounts_step {base : List Bool} {p : Nat × Nat}
    (hbase : HasCounts base (pointBefore p)) (hencoded : EncodedStep p) :
    HasCounts (base ++ [stepBit p]) (pointAfter p) := by
  have hafter := encodedStep_pointAfter hencoded
  rcases hbase with ⟨hh, hv⟩
  cases hbit : stepBit p
  · simp only [hbit, Bool.false_eq_true, ↓reduceIte] at hafter
    rw [hafter]
    simpa [HasCounts, horizontalCount, verticalCount, hbit] using And.intro hh hv
  · simp only [hbit, ↓reduceIte] at hafter
    rw [hafter]
    simpa [HasCounts, horizontalCount, verticalCount, hbit] using And.intro hh hv

theorem forcesStep_append_right {bits suffix : List Bool} {p : Nat × Nat}
    (h : ForcesStep bits p) :
    ForcesStep (bits ++ suffix) p := by
  obtain ⟨before, after, rfl, hcounts⟩ := h
  exact ⟨before, after ++ suffix, by simp [List.append_assoc], hcounts⟩

theorem buildThrough_spec {n : Nat} {base : List Bool} {cur : Nat × Nat}
    {points : List (Nat × Nat)}
    (hbase : HasCounts base cur)
    (hvalid : ∀ p ∈ points, ValidStep n p)
    (hstart : ∀ p ∈ points, ComponentLE cur (pointBefore p))
    (hfits : points.Pairwise FitsAfter) :
    ForcesSteps (base ++ buildThrough cur points) points ∧
      HasCounts (base ++ buildThrough cur points) (endPoint cur points) := by
  induction points generalizing base cur with
  | nil =>
      exact ⟨by simp [ForcesSteps], by simpa [buildThrough, endPoint] using hbase⟩
  | cons p ps ih =>
      rw [List.pairwise_cons] at hfits
      have hpValid := hvalid p (by simp)
      let before := base ++ fillTo cur (pointBefore p)
      have hbefore : HasCounts before (pointBefore p) :=
        hasCounts_fillTo hbase (hstart p (by simp))
      let nextBase := before ++ [stepBit p]
      have hnext : HasCounts nextBase (pointAfter p) :=
        hasCounts_step hbefore hpValid.1
      have hvalidTail : ∀ q ∈ ps, ValidStep n q :=
        fun q hq => hvalid q (by simp [hq])
      have hstartTail : ∀ q ∈ ps, ComponentLE (pointAfter p) (pointBefore q) :=
        fun q hq => hfits.1 q hq
      obtain ⟨hforcesTail, hend⟩ :=
        ih hnext hvalidTail hstartTail hfits.2
      have hwhole :
          base ++ buildThrough cur (p :: ps) =
            nextBase ++ buildThrough (pointAfter p) ps := by
        simp [buildThrough, before, nextBase, List.append_assoc]
      constructor
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · rw [hwhole]
          apply forcesStep_append_right
          exact ⟨before, [], by simp [nextBase], hbefore⟩
        · rw [hwhole]
          exact hforcesTail q hq
      · rw [hwhole]
        simpa [endPoint] using hend

theorem endPoint_sum_le {n : Nat} {cur : Nat × Nat}
    {points : List (Nat × Nat)} (hcur : cur.1 + cur.2 ≤ n)
    (hvalid : ∀ p ∈ points, ValidStep n p) :
    (endPoint cur points).1 + (endPoint cur points).2 ≤ n := by
  cases points with
  | nil => simpa [endPoint] using hcur
  | cons p ps =>
      have hp := hvalid p (by simp)
      have hafter := encodedStep_pointAfter hp.1
      have hpSum : (pointAfter p).1 + (pointAfter p).2 ≤ n := by
        obtain ⟨a, ha, han, hbefore⟩ := hp.2
        cases hbit : stepBit p <;>
          simp [hbit] at hafter <;> rw [hafter] <;> omega
      apply endPoint_sum_le hpSum
      exact fun q hq => hvalid q (by simp [hq])
termination_by points.length

def completeBits (n : Nat) (points : List (Nat × Nat)) : List Bool :=
  let bits := buildThrough (0, 0) points
  let finish := endPoint (0, 0) points
  bits ++ List.replicate (n - finish.1 - finish.2) false

theorem completeBits_length {n : Nat} {points : List (Nat × Nat)}
    (hvalid : ∀ p ∈ points, ValidStep n p)
    (hfits : points.Pairwise FitsAfter) :
    (completeBits n points).length = n := by
  have hspec := buildThrough_spec (n := n) (base := [])
    (cur := (0, 0)) (points := points) (by simp [HasCounts, horizontalCount,
      verticalCount])
    hvalid (by simp [ComponentLE]) hfits
  have hsum := horizontalCount_add_verticalCount
    (buildThrough (0, 0) points)
  have hend := endPoint_sum_le (n := n) (cur := (0, 0))
    (points := points) (by simp) hvalid
  simp only [completeBits, List.length_append, List.length_replicate]
  have := hspec.2
  simp [HasCounts] at this
  omega

theorem completeBits_forces {n : Nat} {points : List (Nat × Nat)}
    (hvalid : ∀ p ∈ points, ValidStep n p)
    (hfits : points.Pairwise FitsAfter) :
    ForcesSteps (completeBits n points) points := by
  have hspec := buildThrough_spec (n := n) (base := [])
    (cur := (0, 0)) (points := points) (by simp [HasCounts, horizontalCount,
      verticalCount])
    hvalid (by simp [ComponentLE]) hfits
  intro p hp
  exact forcesStep_append_right (hspec.1 p hp)

def leftOfBits (bits : List Bool) (a : Nat) : Bool :=
  bits.getD (a - 1) false

theorem leftBefore_leftOfBits {bits : List Bool} (r : Nat)
    (hr : r ≤ bits.length) :
    leftBefore (leftOfBits bits) (r + 1) =
      horizontalCount (bits.take r) := by
  induction r with
  | zero => simp [leftBefore, leftOfBits, horizontalCount]
  | succ r ih =>
      have hrlt : r < bits.length := by omega
      rw [show r + 1 + 1 = r + 2 by omega, leftBefore_succ,
        ih (by omega), ← List.take_concat_get' bits r hrlt]
      cases hbit : bits[r] <;>
        simp [leftOfBits, horizontalCount, hbit, hrlt]

theorem rightBefore_leftOfBits {bits : List Bool} (r : Nat)
    (hr : r ≤ bits.length) :
    rightBefore (leftOfBits bits) (r + 1) =
      verticalCount (bits.take r) := by
  induction r with
  | zero => simp [rightBefore, leftOfBits, verticalCount]
  | succ r ih =>
      have hrlt : r < bits.length := by omega
      rw [show r + 1 + 1 = r + 2 by omega, rightBefore_succ,
        ih (by omega), ← List.take_concat_get' bits r hrlt]
      cases hbit : bits[r] <;>
        simp [leftOfBits, verticalCount, hbit, hrlt]

theorem forced_pathMidpoint {n : Nat} {bits : List Bool} {p : Nat × Nat}
    (hbits : bits.length = n) (hvalid : ValidStep n p)
    (hforced : ForcesStep bits p) :
    ∃ a, 1 ≤ a ∧ a ≤ n ∧ pathMidpoint (leftOfBits bits) a = p := by
  obtain ⟨a, ha, han, hbeforeSum⟩ := hvalid.2
  obtain ⟨before, after, hdecomp, hcounts⟩ := hforced
  have hbeforeLen : before.length = a - 1 := by
    have hcountSum := horizontalCount_add_verticalCount before
    rw [hcounts.1, hcounts.2, hbeforeSum] at hcountSum
    omega
  have htake : bits.take (a - 1) = before := by
    rw [hdecomp, ← hbeforeLen]
    simp
  have haPred : a - 1 ≤ bits.length := by omega
  have hleftBefore := leftBefore_leftOfBits (bits := bits) (a - 1) haPred
  have hrightBefore := rightBefore_leftOfBits (bits := bits) (a - 1) haPred
  rw [htake, hcounts.1] at hleftBefore
  rw [htake, hcounts.2] at hrightBefore
  have hpredSucc : a - 1 + 1 = a := by omega
  rw [hpredSucc] at hleftBefore hrightBefore
  have hbit : leftOfBits bits a = stepBit p := by
    simp [leftOfBits, hdecomp, hbeforeLen]
  refine ⟨a, ha, han, ?_⟩
  have hencoded := hvalid.1
  unfold EncodedStep at hencoded
  cases hpbit : stepBit p
  · simp only [hpbit, Bool.false_eq_true, ↓reduceIte] at hencoded
    simpa only [pathMidpoint, hbit, hpbit, Bool.false_eq_true, ↓reduceIte,
      hleftBefore, hrightBefore] using hencoded.symm
  · simp only [hpbit, ↓reduceIte] at hencoded
    simpa only [pathMidpoint, hbit, hpbit, ↓reduceIte,
      hleftBefore, hrightBefore] using hencoded.symm

theorem exists_left_for_steps {n : Nat} {points : List (Nat × Nat)}
    (hvalid : ∀ p ∈ points, ValidStep n p)
    (hfits : points.Pairwise FitsAfter) :
    ∃ left : Nat → Bool,
      ∀ p ∈ points, ∃ a, 1 ≤ a ∧ a ≤ n ∧ pathMidpoint left a = p := by
  let bits := completeBits n points
  refine ⟨leftOfBits bits, ?_⟩
  intro p hp
  apply forced_pathMidpoint (n := n)
  · exact completeBits_length hvalid hfits
  · exact hvalid p hp
  · exact completeBits_forces hvalid hfits p hp

end Submission.Path
