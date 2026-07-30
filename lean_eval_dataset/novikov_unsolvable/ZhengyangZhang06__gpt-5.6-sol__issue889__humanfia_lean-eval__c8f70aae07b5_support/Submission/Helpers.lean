import ChallengeDeps
import Submission.UniversalMachine

open LeanEval.GroupTheory.NovikovUnsolvableProblem
open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace Submission.Helpers

/-- Concrete words on `n` group generators. -/
abbrev Word (n : ℕ) := List (Fin n × Bool)

/-- An oriented word equation; its orientation is forgotten when it is
compiled into a group relator. -/
abbrev WordRule (n : ℕ) := Word n × Word n

/-- The group relator corresponding to the equation `left = right`. -/
def relatorOfRule {n : ℕ} (rule : WordRule n) : FreeGroup (Fin n) :=
  FreeGroup.mk rule.1 * (FreeGroup.mk rule.2)⁻¹

/-- Compile word equations into the usual relators `left * right⁻¹`. -/
def relatorsOfRules {n : ℕ} (rules : Set (WordRule n)) : Set (FreeGroup (Fin n)) :=
  relatorOfRule '' rules

/-- A finite rule set compiles to a finite group presentation. -/
theorem relatorsOfRules_finite {n : ℕ} {rules : Set (WordRule n)}
    (rules_finite : rules.Finite) : (relatorsOfRules rules).Finite :=
  rules_finite.image relatorOfRule

/-- Every source equation holds in the group presented by its compiled
relators. -/
theorem rule_eq_in_presentedGroup {n : ℕ} {rules : Set (WordRule n)}
    {left right : Word n} (rule_mem : (left, right) ∈ rules) :
    PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk left) =
      PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk right) :=
  PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨(left, right), rule_mem, rfl⟩

/-- One contextual application of an oriented word rule. -/
def RuleStep {n : ℕ} (rules : Set (WordRule n)) (source target : Word n) : Prop :=
  ∃ pre post left right,
    (left, right) ∈ rules ∧
      source = pre ++ left ++ post ∧ target = pre ++ right ++ post

/-- Reflexive, transitive reachability by contextual rule applications. -/
def RuleReaches {n : ℕ} (rules : Set (WordRule n)) : Word n → Word n → Prop :=
  Relation.ReflTransGen (RuleStep rules)

/-- A contextual rule application gives equality in the group presentation
compiled from the rule set. -/
theorem ruleStep_eq_in_presentedGroup {n : ℕ} {rules : Set (WordRule n)}
    {source target : Word n} (step : RuleStep rules source target) :
    PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk source) =
      PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk target) := by
  obtain ⟨pre, post, left, right, rule_mem, rfl, rfl⟩ := step
  calc
    PresentedGroup.mk (relatorsOfRules rules)
        (FreeGroup.mk (pre ++ left ++ post)) =
        PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk pre) *
          (PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk left) *
            PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk post)) := by
      rw [← map_mul, ← map_mul, FreeGroup.mul_mk, FreeGroup.mul_mk,
        List.append_assoc]
    _ = PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk pre) *
          (PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk right) *
            PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk post)) := by
      rw [rule_eq_in_presentedGroup rule_mem]
    _ = PresentedGroup.mk (relatorsOfRules rules)
        (FreeGroup.mk (pre ++ right ++ post)) := by
      rw [← map_mul, ← map_mul, FreeGroup.mul_mk, FreeGroup.mul_mk,
        List.append_assoc]

/-- Every finite rewrite derivation gives equality in the compiled presented
group. This is the machine-to-group direction of the simulation. -/
theorem ruleReaches_eq_in_presentedGroup {n : ℕ} {rules : Set (WordRule n)}
    {source target : Word n} (reaches : RuleReaches rules source target) :
    PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk source) =
      PresentedGroup.mk (relatorsOfRules rules) (FreeGroup.mk target) := by
  induction reaches with
  | refl => rfl
  | tail _ step ih => exact ih.trans (ruleStep_eq_in_presentedGroup step)

/-- The word representing `left * right⁻¹`. -/
def wordDifference {n : ℕ} (left right : Word n) : Word n :=
  left ++ FreeGroup.invRev right

theorem mk_wordDifference {n : ℕ} (left right : Word n) :
    FreeGroup.mk (wordDifference left right) =
      FreeGroup.mk left * (FreeGroup.mk right)⁻¹ := by
  rw [wordDifference, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]

/-- Data sufficient to certify that a finite presentation has an
undecidable word problem. The `encode` field is the effective reduction
from the halting problem to membership in the relators' normal closure. -/
structure NovikovCertificate where
  n : ℕ
  rels : Set (FreeGroup (Fin n))
  finite_rels : rels.Finite
  encode : Code → List (Fin n × Bool)
  encode_computable : Computable encode
  encode_spec :
    ∀ c, (eval c 0).Dom ↔ FreeGroup.mk (encode c) ∈ Subgroup.normalClosure rels

/-- A certificate stated using a finite set of word-equation rules. -/
structure RuleCertificate where
  n : ℕ
  rules : Set (WordRule n)
  rules_finite : rules.Finite
  encode : Code → Word n
  encode_computable : Computable encode
  encode_spec :
    ∀ c, (eval c 0).Dom ↔
      FreeGroup.mk (encode c) ∈ Subgroup.normalClosure (relatorsOfRules rules)

/-- A finite rewriting simulation, split into operational correctness and
the group-theoretic soundness direction. -/
structure RuleSimulationCertificate where
  n : ℕ
  rules : Set (WordRule n)
  rules_finite : rules.Finite
  start : Code → Word n
  start_computable : Computable start
  halt : Word n
  halting_iff_reaches : ∀ c, (eval c 0).Dom ↔ RuleReaches rules (start c) halt
  group_sound :
    ∀ c,
      FreeGroup.mk (wordDifference (start c) halt) ∈
          Subgroup.normalClosure (relatorsOfRules rules) →
        RuleReaches rules (start c) halt

/-- A computable reduction from the halting problem to a presentation's
word problem rules out a word-problem decider. -/
theorem not_wordProblemSolvable_of_reduction {n : ℕ}
    (rels : Set (FreeGroup (Fin n))) (encode : Code → List (Fin n × Bool))
    (encode_computable : Computable encode)
    (encode_spec :
      ∀ c, (eval c 0).Dom ↔ PresentedGroup.mk rels (FreeGroup.mk (encode c)) = 1) :
    ¬ WordProblemSolvable (PresentedGroup.mk rels) := by
  intro wordProblemSolvable
  exact ComputablePred.halting_problem 0 <|
    ComputablePred.computable_of_manyOneReducible
      ⟨encode, encode_computable, encode_spec⟩ wordProblemSolvable

/-- The normal-closure formulation is equivalent to equality with the
identity in the presented group. -/
theorem not_wordProblemSolvable_of_normalClosure_reduction {n : ℕ}
    (rels : Set (FreeGroup (Fin n))) (encode : Code → List (Fin n × Bool))
    (encode_computable : Computable encode)
    (encode_spec :
      ∀ c, (eval c 0).Dom ↔ FreeGroup.mk (encode c) ∈ Subgroup.normalClosure rels) :
    ¬ WordProblemSolvable (PresentedGroup.mk rels) :=
  not_wordProblemSolvable_of_reduction rels encode encode_computable fun c =>
    (encode_spec c).trans PresentedGroup.mk_eq_one_iff.symm

/-- A `NovikovCertificate` packages exactly the finite presentation and
effective halting reduction needed by the benchmark theorem. -/
theorem NovikovCertificate.sound (certificate : NovikovCertificate) :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
      rels.Finite ∧ ¬ WordProblemSolvable (PresentedGroup.mk rels) :=
  ⟨certificate.n, certificate.rels, certificate.finite_rels,
    not_wordProblemSolvable_of_normalClosure_reduction certificate.rels certificate.encode
      certificate.encode_computable certificate.encode_spec⟩

/-- Compile a finite rule-system certificate to a finite-presentation
certificate. -/
def RuleCertificate.toNovikovCertificate (certificate : RuleCertificate) :
    NovikovCertificate where
  n := certificate.n
  rels := relatorsOfRules certificate.rules
  finite_rels := relatorsOfRules_finite certificate.rules_finite
  encode := certificate.encode
  encode_computable := certificate.encode_computable
  encode_spec := certificate.encode_spec

/-- Operational correctness plus group soundness supplies the exact normal
closure certificate. -/
def RuleSimulationCertificate.toRuleCertificate
    (certificate : RuleSimulationCertificate) : RuleCertificate where
  n := certificate.n
  rules := certificate.rules
  rules_finite := certificate.rules_finite
  encode := fun c => wordDifference (certificate.start c) certificate.halt
  encode_computable :=
    Computable.list_append.comp certificate.start_computable
      (Computable.const (FreeGroup.invRev certificate.halt))
  encode_spec := fun c => by
    constructor
    · intro halts
      have reaches := (certificate.halting_iff_reaches c).mp halts
      apply PresentedGroup.mk_eq_one_iff.mp
      calc
        PresentedGroup.mk (relatorsOfRules certificate.rules)
            (FreeGroup.mk (wordDifference (certificate.start c) certificate.halt)) =
            PresentedGroup.mk (relatorsOfRules certificate.rules)
                (FreeGroup.mk (certificate.start c)) *
              (PresentedGroup.mk (relatorsOfRules certificate.rules)
                (FreeGroup.mk certificate.halt))⁻¹ := by
          rw [mk_wordDifference, map_mul, map_inv]
        _ = 1 := by
          rw [ruleReaches_eq_in_presentedGroup reaches]
          exact mul_inv_cancel _
    · intro in_closure
      exact (certificate.halting_iff_reaches c).mpr (certificate.group_sound c in_closure)

/-- A finite word-equation system with a correct halting reduction proves
the benchmark existential directly. -/
theorem RuleCertificate.sound (certificate : RuleCertificate) :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
      rels.Finite ∧ ¬ WordProblemSolvable (PresentedGroup.mk rels) :=
  certificate.toNovikovCertificate.sound

/-- A sound finite rewriting simulation proves the benchmark existential. -/
theorem RuleSimulationCertificate.sound (certificate : RuleSimulationCertificate) :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
      rels.Finite ∧ ¬ WordProblemSolvable (PresentedGroup.mk rels) :=
  certificate.toRuleCertificate.sound

end Submission.Helpers
