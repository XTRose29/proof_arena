/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: dvd_card_connectedComponent_markoffGraph
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 967a90b73db64a1939ef0fba144e183e35e97612
issue_number: 244
-/
import ChallengeDeps
import Submission.markoff
import Mathlib

open LeanEval.Combinatorics
open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

open Classical in
noncomputable section

namespace Submission

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ## Converting MarkoffTriple to tuples -/

def toTuple (x : MarkoffTriple p) : ZMod p × ZMod p × ZMod p :=
  (x.1 0, x.1 1, x.1 2)

lemma toTuple_isMarkoff (x : MarkoffTriple p) :
    Markoff.IsMarkoffSol p (toTuple x) :=
  x.2.2

omit hp in
lemma toTuple_ne_zero (x : MarkoffTriple p) :
    toTuple x ≠ (0, 0, 0) := by
  intro heq
  apply x.2.1
  ext i
  simp only [toTuple, Prod.mk.injEq] at heq
  fin_cases i
  · exact heq.1
  · exact heq.2.1
  · exact heq.2.2

omit hp in
lemma toTuple_injective : Function.Injective (toTuple (p := p)) := by
  intro a b hab
  apply Subtype.ext
  ext i
  simp only [toTuple, Prod.mk.injEq] at hab
  fin_cases i
  · exact hab.1
  · exact hab.2.1
  · exact hab.2.2

/-- Construct a MarkoffTriple from a tuple with proofs. -/
def fromTuple (t : ZMod p × ZMod p × ZMod p)
    (hm : Markoff.IsMarkoffSol p t) (hne : t ≠ (0, 0, 0)) :
    MarkoffTriple p :=
  ⟨fun i => match i with | 0 => t.1 | 1 => t.2.1 | 2 => t.2.2,
   by intro h; apply hne
      exact Prod.ext (congr_fun h 0) (Prod.ext (congr_fun h 1) (congr_fun h 2)),
   hm⟩

lemma toTuple_fromTuple (t : ZMod p × ZMod p × ZMod p)
    (hm : Markoff.IsMarkoffSol p t) (hne : t ≠ (0, 0, 0)) :
    toTuple (fromTuple t hm hne) = t := by
  obtain ⟨a, b, c⟩ := t; rfl

/-! ## Vieta involution on MarkoffTriple -/

def vietaLiftMT (i : Fin 3) (x : MarkoffTriple p) : MarkoffTriple p :=
  fromTuple (Markoff.vieta p i (toTuple x))
    (Markoff.vieta_preserves p i _ (toTuple_isMarkoff x))
    (Markoff.vieta_preserves_nonzero p i _ (toTuple_ne_zero x))

lemma toTuple_vietaLiftMT (i : Fin 3) (x : MarkoffTriple p) :
    toTuple (vietaLiftMT i x) = Markoff.vieta p i (toTuple x) := by
  simp [vietaLiftMT, toTuple_fromTuple]

lemma vietaLiftMT_involutive (i : Fin 3) (x : MarkoffTriple p) :
    vietaLiftMT i (vietaLiftMT i x) = x := by
  apply toTuple_injective
  rw [toTuple_vietaLiftMT, toTuple_vietaLiftMT, Markoff.vieta_involutive]

/-! ## Adjacency -/

lemma vietaLiftMT_adj (i : Fin 3) (x : MarkoffTriple p)
    (hne : vietaLiftMT i x ≠ x) :
    (markoffGraph p).Adj (vietaLiftMT i x) x := by
  fin_cases i <;> simp_all +decide [ markoffGraph ];
  · unfold vietaLiftMT at * ; simp_all +decide [ Markoff.vieta ] ;
    unfold fromTuple; simp +decide [ toTuple ] ;
  · unfold vietaLiftMT; simp +decide [ Markoff.vieta ] ;
    unfold fromTuple; simp +decide [ toTuple ] ;
  · unfold vietaLiftMT; simp +decide [ toTuple ] ;
    unfold fromTuple; simp +decide [ Markoff.vieta ] ;

/-! ## Connected components are Vieta-closed -/

lemma vieta_mem_component_MT
    (c : (markoffGraph p).ConnectedComponent)
    (x : MarkoffTriple p) (hx : (markoffGraph p).connectedComponentMk x = c)
    (i : Fin 3) :
    (markoffGraph p).connectedComponentMk (vietaLiftMT i x) = c := by
  by_cases h : vietaLiftMT i x = x
  · rw [h, hx]
  · rw [← hx]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (SimpleGraph.adj_symm _ (vietaLiftMT_adj i x h))).symm

/-! ## Cardinality lemma -/

lemma card_component_eq_filter (c : (markoffGraph p).ConnectedComponent) :
    Nat.card c =
    (Finset.univ.filter (fun x : MarkoffTriple p =>
      (markoffGraph p).connectedComponentMk x = c)).card := by
  rw [ ← Nat.card_eq_finsetCard ];
  fapply Nat.card_congr;
  exact Equiv.subtypeEquivRight ( by aesop )

/-! ## Main theorem -/

theorem dvd_card_connectedComponent_markoffGraph {p : ℕ} (hp : Nat.Prime p) (hgt : 3 < p) :
    ∀ c : (markoffGraph p).ConnectedComponent, p ∣ Nat.card c := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro c
  let compFinset : Finset (MarkoffTriple p) :=
    Finset.univ.filter (fun x => (markoffGraph p).connectedComponentMk x = c)
  let S : Finset (ZMod p × ZMod p × ZMod p) := compFinset.image toTuple
  have hcard : S.card = Nat.card c := by
    simp only [S]
    rw [Finset.card_image_of_injective _ toTuple_injective]
    rw [card_component_eq_filter]
  rw [← hcard]
  apply Markoff.vieta_closed_card_dvd p (by omega) S
  · intro t ht
    simp only [S, Finset.mem_image] at ht
    obtain ⟨x, _, rfl⟩ := ht
    exact toTuple_isMarkoff x
  · intro t ht
    simp only [S, Finset.mem_image] at ht
    obtain ⟨x, _, rfl⟩ := ht
    exact toTuple_ne_zero x
  · intro t ht i
    simp only [S, compFinset, Finset.mem_image, Finset.mem_filter] at ht ⊢
    obtain ⟨x, ⟨_, hxc⟩, rfl⟩ := ht
    exact ⟨vietaLiftMT i x,
           ⟨Finset.mem_univ _, vieta_mem_component_MT c x hxc i⟩,
           toTuple_vietaLiftMT i x⟩

end Submission
