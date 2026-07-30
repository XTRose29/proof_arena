import Submission.Helpers
import Mathlib.GroupTheory.HNNExtension

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace Submission.SubgroupReduction

open Submission.Helpers

/-!
# From subgroup membership to a finite-presentation word problem

This file isolates a cancellation-safe group-theoretic reduction.  If
membership in a finitely generated subgroup of a finitely presented group
encodes the halting problem, adjoining one stable letter which centralizes
that subgroup turns membership into an ordinary word problem.  Britton's
lemma supplies the converse.
-/

/-- Embed the base generators above a new stable letter at index zero. -/
def liftLetter {n : ℕ} (letter : Fin n × Bool) : Fin (n + 1) × Bool :=
  (letter.1.succ, letter.2)

/-- Embed a base-group word into the alphabet with one new stable letter. -/
def liftWord {n : ℕ} (word : Word n) : Word (n + 1) :=
  word.map liftLetter

/-- The word `t w (w t)⁻¹`, which is trivial exactly when `t` commutes
with the element represented by `w`. -/
def commutatorWord {n : ℕ} (word : Word n) : Word (n + 1) :=
  (0, true) :: liftWord word ++
    FreeGroup.invRev (liftWord word ++ [(0, true)])

private theorem liftLetter_primrec {n : ℕ} :
    Primrec (@liftLetter n) :=
  (Primrec.fin_succ.comp Primrec.fst).pair Primrec.snd

theorem liftWord_computable {n : ℕ} :
    Computable (@liftWord n) :=
  (Primrec.list_map Primrec.id
    (Primrec₂.mk (liftLetter_primrec.comp Primrec.snd))).to_comp

private theorem invertLetter_primrec {n : ℕ} :
    Primrec (fun letter : Fin n × Bool => (letter.1, !letter.2)) :=
  Primrec.fst.pair ((Primrec.dom_bool (!·)).comp Primrec.snd)

theorem invRev_computable {n : ℕ} :
    Computable (@FreeGroup.invRev (Fin n)) := by
  apply Primrec.to_comp
  exact Primrec.list_reverse.comp <|
    Primrec.list_map Primrec.id
      (Primrec₂.mk (invertLetter_primrec.comp Primrec.snd))

theorem commutatorWord_computable {n : ℕ} :
    Computable (@commutatorWord n) := by
  let stableWord : Word (n + 1) := [(0, true)]
  have lifted : Computable (@liftWord n) := liftWord_computable
  have withStable :
      Computable (fun word : Word n => liftWord word ++ stableWord) :=
    Computable.list_append.comp lifted (Computable.const stableWord)
  have inverse : Computable
      (fun word : Word n => FreeGroup.invRev (liftWord word ++ stableWord)) :=
    invRev_computable.comp withStable
  exact (Computable.list_cons.comp (Computable.const (0, true))
    (Computable.list_append.comp lifted inverse)).of_eq fun word => by
      simp [commutatorWord, stableWord]

theorem mk_liftWord {n : ℕ} (word : Word n) :
    FreeGroup.mk (liftWord word) =
      FreeGroup.map Fin.succ (FreeGroup.mk word) := by
  rw [FreeGroup.map.mk]
  rfl

theorem mk_commutatorWord {n : ℕ} (word : Word n) :
    FreeGroup.mk (commutatorWord word) =
      FreeGroup.of (0 : Fin (n + 1)) *
        FreeGroup.map Fin.succ (FreeGroup.mk word) *
          (FreeGroup.map Fin.succ (FreeGroup.mk word) *
            FreeGroup.of (0 : Fin (n + 1)))⁻¹ := by
  rw [commutatorWord, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk,
    ← FreeGroup.mul_mk]
  have stable_mul :
      FreeGroup.mk ((0, true) :: liftWord word) =
        FreeGroup.of (0 : Fin (n + 1)) *
          FreeGroup.map Fin.succ (FreeGroup.mk word) := by
    change FreeGroup.mk ([(0, true)] ++ liftWord word) = _
    rw [← FreeGroup.mul_mk, mk_liftWord]
    rfl
  rw [stable_mul, mk_liftWord]
  rfl

/-- Data for an undecidable membership problem in a finitely generated
subgroup of a finitely presented group. -/
structure SubgroupMembershipCertificate where
  n : ℕ
  baseRels : Set (FreeGroup (Fin n))
  baseRels_finite : baseRels.Finite
  subgroupGenerators : Finset (Word n)
  encode : Code → Word n
  encode_computable : Computable encode
  encode_spec :
    ∀ c, (eval c 0).Dom ↔
      PresentedGroup.mk baseRels (FreeGroup.mk (encode c)) ∈
        Subgroup.closure
          (PresentedGroup.mk baseRels ∘ FreeGroup.mk ''
            (subgroupGenerators : Set (Word n)))

namespace SubgroupMembershipCertificate

variable (certificate : SubgroupMembershipCertificate)

private abbrev BaseGroup :=
  PresentedGroup certificate.baseRels

/-- The finitely generated subgroup whose membership problem is supplied by
the certificate. -/
def subgroup : Subgroup certificate.BaseGroup :=
  Subgroup.closure
    (PresentedGroup.mk certificate.baseRels ∘ FreeGroup.mk ''
      (certificate.subgroupGenerators : Set (Word certificate.n)))

/-- A base relator, reindexed above the stable letter. -/
def liftedBaseRelators : Set (FreeGroup (Fin (certificate.n + 1))) :=
  FreeGroup.map Fin.succ '' certificate.baseRels

/-- The relator asserting that the stable letter commutes with `word`. -/
def centralizerRelator (word : Word certificate.n) :
    FreeGroup (Fin (certificate.n + 1)) :=
  FreeGroup.of 0 * FreeGroup.map Fin.succ (FreeGroup.mk word) *
    (FreeGroup.map Fin.succ (FreeGroup.mk word) * FreeGroup.of 0)⁻¹

/-- The finite presentation obtained by adjoining a stable letter which
centralizes the specified subgroup generators. -/
def extensionRelators : Set (FreeGroup (Fin (certificate.n + 1))) :=
  certificate.liftedBaseRelators ∪
    certificate.centralizerRelator ''
      (certificate.subgroupGenerators : Set (Word certificate.n))

theorem extensionRelators_finite :
    certificate.extensionRelators.Finite :=
  (certificate.baseRels_finite.image (FreeGroup.map Fin.succ)).union
    (certificate.subgroupGenerators.finite_toSet.image certificate.centralizerRelator)

private abbrev ExtensionGroup :=
  PresentedGroup certificate.extensionRelators

/-- The stable letter in the explicitly presented extension. -/
def stable : certificate.ExtensionGroup :=
  PresentedGroup.of 0

/-- Images of the base generators in the explicitly presented extension. -/
def baseGenerator (i : Fin certificate.n) : certificate.ExtensionGroup :=
  PresentedGroup.of i.succ

private theorem base_lift_eq :
    FreeGroup.lift certificate.baseGenerator =
      (PresentedGroup.mk certificate.extensionRelators).comp
        (FreeGroup.map Fin.succ) := by
  ext i
  rfl

private theorem base_relations_hold
    (r : FreeGroup (Fin certificate.n)) (hr : r ∈ certificate.baseRels) :
    FreeGroup.lift certificate.baseGenerator r = 1 := by
  rw [certificate.base_lift_eq]
  exact PresentedGroup.one_of_mem
    (Or.inl ⟨r, hr, rfl⟩)

/-- The homomorphism from the base presented group into the explicit
centralizing extension. -/
def baseToExtension : certificate.BaseGroup →* certificate.ExtensionGroup :=
  PresentedGroup.toGroup certificate.base_relations_hold

private theorem baseToExtension_comp_mk :
    certificate.baseToExtension.comp
        (PresentedGroup.mk certificate.baseRels) =
      FreeGroup.lift certificate.baseGenerator := by
  apply FreeGroup.ext_hom
  intro i
  change certificate.baseToExtension (PresentedGroup.of i) =
    certificate.baseGenerator i
  exact PresentedGroup.toGroup.of certificate.base_relations_hold

theorem baseToExtension_mk (x : FreeGroup (Fin certificate.n)) :
    certificate.baseToExtension
        (PresentedGroup.mk certificate.baseRels x) =
      PresentedGroup.mk certificate.extensionRelators
        (FreeGroup.map Fin.succ x) := by
  rw [← MonoidHom.comp_apply, certificate.baseToExtension_comp_mk,
    certificate.base_lift_eq, MonoidHom.comp_apply]

theorem baseToExtension_word (word : Word certificate.n) :
    certificate.baseToExtension
        (PresentedGroup.mk certificate.baseRels (FreeGroup.mk word)) =
      PresentedGroup.mk certificate.extensionRelators
        (FreeGroup.mk (liftWord word)) := by
  rw [certificate.baseToExtension_mk, mk_liftWord]

private theorem stable_commutes_generator
    {word : Word certificate.n}
    (word_mem : word ∈ certificate.subgroupGenerators) :
    Commute certificate.stable
      (certificate.baseToExtension
        (PresentedGroup.mk certificate.baseRels (FreeGroup.mk word))) := by
  rw [certificate.baseToExtension_word]
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact Or.inr ⟨word, word_mem, by
    simp [centralizerRelator, mk_liftWord, FreeGroup.of]⟩

theorem stable_commutes_of_mem
    {g : certificate.BaseGroup} (g_mem : g ∈ certificate.subgroup) :
    Commute certificate.stable (certificate.baseToExtension g) := by
  induction g_mem using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨word, word_mem, rfl⟩ := hg
      exact certificate.stable_commutes_generator word_mem
  | one => exact Commute.one_right _
  | mul x y _ _ hx hy => simpa only [map_mul] using hx.mul_right hy
  | inv x _ hx => simpa only [map_inv] using hx.inv_right

private abbrev CentralizingHNN :=
  HNNExtension certificate.BaseGroup certificate.subgroup certificate.subgroup
    (MulEquiv.refl certificate.subgroup)

/-- The stable letter in the comparison HNN extension. -/
def hnnStable : certificate.CentralizingHNN :=
  HNNExtension.t

/-- The canonical embedding of the base group in the comparison HNN
extension. -/
def hnnOf : certificate.BaseGroup →* certificate.CentralizingHNN :=
  HNNExtension.of

/-- Interpret the explicit extension generators in the corresponding HNN
extension. -/
def hnnGenerator : Fin (certificate.n + 1) → certificate.CentralizingHNN :=
  Fin.cases certificate.hnnStable fun i =>
    certificate.hnnOf (PresentedGroup.of i)

private theorem hnn_base_word (word : Word certificate.n) :
    FreeGroup.lift certificate.hnnGenerator
        (FreeGroup.map Fin.succ (FreeGroup.mk word)) =
      certificate.hnnOf
        (PresentedGroup.mk certificate.baseRels (FreeGroup.mk word)) := by
  have hom_eq :
      (FreeGroup.lift certificate.hnnGenerator).comp
          (FreeGroup.map Fin.succ) =
        certificate.hnnOf.comp
          (PresentedGroup.mk certificate.baseRels) := by
    ext i
    rfl
  rw [← MonoidHom.comp_apply, hom_eq, MonoidHom.comp_apply]

private theorem hnn_relations_hold
    (r : FreeGroup (Fin (certificate.n + 1)))
    (hr : r ∈ certificate.extensionRelators) :
    FreeGroup.lift certificate.hnnGenerator r = 1 := by
  rcases hr with ⟨baseRelator, base_mem, rfl⟩ |
      ⟨word, word_mem, rfl⟩
  · have base_one :
        PresentedGroup.mk certificate.baseRels baseRelator = 1 :=
      PresentedGroup.one_of_mem base_mem
    change FreeGroup.lift certificate.hnnGenerator
      (FreeGroup.map Fin.succ baseRelator) = 1
    have hom_eq :
        (FreeGroup.lift certificate.hnnGenerator).comp
            (FreeGroup.map Fin.succ) =
          certificate.hnnOf.comp
            (PresentedGroup.mk certificate.baseRels) := by
      ext i
      rfl
    rw [← MonoidHom.comp_apply, hom_eq, MonoidHom.comp_apply, base_one, map_one]
  · have subgroup_mem :
        PresentedGroup.mk certificate.baseRels (FreeGroup.mk word) ∈
          certificate.subgroup :=
      Subgroup.subset_closure ⟨word, word_mem, rfl⟩
    let member : certificate.subgroup :=
      ⟨PresentedGroup.mk certificate.baseRels (FreeGroup.mk word), subgroup_mem⟩
    rw [centralizerRelator]
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [certificate.hnn_base_word]
    change certificate.hnnStable *
        certificate.hnnOf (member : certificate.BaseGroup) *
      (certificate.hnnOf (member : certificate.BaseGroup) *
        certificate.hnnStable)⁻¹ = 1
    have commute_member :
        certificate.hnnStable *
            certificate.hnnOf (member : certificate.BaseGroup) =
          certificate.hnnOf (member : certificate.BaseGroup) *
            certificate.hnnStable := by
      have relation := HNNExtension.t_mul_of
        (B := certificate.subgroup)
        (φ := MulEquiv.refl certificate.subgroup) member
      have member_fixed :
          (MulEquiv.refl certificate.subgroup) member = member := rfl
      rw [member_fixed] at relation
      exact relation
    rw [commute_member]
    simp

/-- The comparison map from the explicit finite presentation to the HNN
extension used for Britton's lemma. -/
def toHNN : certificate.ExtensionGroup →* certificate.CentralizingHNN :=
  PresentedGroup.toGroup certificate.hnn_relations_hold

theorem toHNN_mk (x : FreeGroup (Fin (certificate.n + 1))) :
    certificate.toHNN
        (PresentedGroup.mk certificate.extensionRelators x) =
      FreeGroup.lift certificate.hnnGenerator x := by
  rfl

/-- Britton's lemma specialized to the centralizing HNN extension: if the
stable letter commutes with a base-group element, that element belongs to
the associated subgroup. -/
theorem mem_subgroup_of_hnn_commute (g : certificate.BaseGroup)
    (commutes :
      certificate.hnnStable * certificate.hnnOf g =
        certificate.hnnOf g * certificate.hnnStable) :
    g ∈ certificate.subgroup := by
  by_contra g_not_mem
  let reduced :
      HNNExtension.NormalWord.ReducedWord certificate.BaseGroup
        certificate.subgroup certificate.subgroup :=
    { head := 1
      toList := [(1, g), (-1, g⁻¹)]
      chain := by
        simp [HNNExtension.toSubgroup, g_not_mem] }
  have reduced_prod_one :
      reduced.prod (MulEquiv.refl certificate.subgroup) = 1 := by
    have commutes' :
        (HNNExtension.t : certificate.CentralizingHNN) *
            HNNExtension.of g =
          HNNExtension.of g *
            (HNNExtension.t : certificate.CentralizingHNN) := by
      simpa [hnnStable, hnnOf] using commutes
    simp [reduced, HNNExtension.NormalWord.ReducedWord.prod]
    rw [commutes']
    simp
  have reduced_in_base :
      reduced.prod (MulEquiv.refl certificate.subgroup) ∈
        (HNNExtension.of.range :
          Subgroup certificate.CentralizingHNN) :=
    ⟨1, by simp [reduced_prod_one]⟩
  have no_stable_letters :=
    HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
      (φ := MulEquiv.refl certificate.subgroup) reduced reduced_in_base
  simp [reduced] at no_stable_letters

theorem commute_iff_mem (word : Word certificate.n) :
    PresentedGroup.mk certificate.extensionRelators
        (FreeGroup.mk (commutatorWord word)) = 1 ↔
      PresentedGroup.mk certificate.baseRels (FreeGroup.mk word) ∈
        certificate.subgroup := by
  constructor
  · intro word_one
    have mapped_one := congrArg certificate.toHNN word_one
    rw [map_one, certificate.toHNN_mk, mk_commutatorWord] at mapped_one
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of] at mapped_one
    rw [certificate.hnn_base_word] at mapped_one
    change certificate.hnnStable *
        certificate.hnnOf
          (PresentedGroup.mk certificate.baseRels (FreeGroup.mk word)) *
      (certificate.hnnOf
          (PresentedGroup.mk certificate.baseRels (FreeGroup.mk word)) *
        certificate.hnnStable)⁻¹ = 1 at mapped_one
    have commutes :
        certificate.hnnStable *
            certificate.hnnOf
              (PresentedGroup.mk certificate.baseRels (FreeGroup.mk word)) =
          certificate.hnnOf
              (PresentedGroup.mk certificate.baseRels (FreeGroup.mk word)) *
            certificate.hnnStable := by
      exact eq_of_mul_inv_eq_one mapped_one
    exact certificate.mem_subgroup_of_hnn_commute _ commutes
  · intro word_mem
    rw [mk_commutatorWord]
    simp only [map_mul, map_inv]
    rw [← certificate.baseToExtension_mk]
    change certificate.stable *
        certificate.baseToExtension
          (PresentedGroup.mk certificate.baseRels (FreeGroup.mk word)) *
      (certificate.baseToExtension
          (PresentedGroup.mk certificate.baseRels (FreeGroup.mk word)) *
        certificate.stable)⁻¹ = 1
    exact mul_inv_eq_one.mpr (certificate.stable_commutes_of_mem word_mem).eq

/-- The computable commutator word associated to a source code. -/
def finalEncode (c : Code) : Word (certificate.n + 1) :=
  commutatorWord (certificate.encode c)

theorem finalEncode_computable :
    Computable certificate.finalEncode :=
  commutatorWord_computable.comp certificate.encode_computable

theorem finalEncode_spec (c : Code) :
    (eval c 0).Dom ↔
      FreeGroup.mk (certificate.finalEncode c) ∈
        Subgroup.normalClosure certificate.extensionRelators := by
  rw [certificate.encode_spec]
  exact (certificate.commute_iff_mem (certificate.encode c)).symm.trans
    PresentedGroup.mk_eq_one_iff

/-- A finitely presented group with an undecidable finitely generated
subgroup-membership problem yields the benchmark finite presentation. -/
theorem sound (certificate : SubgroupMembershipCertificate) :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
      rels.Finite ∧
        ¬ LeanEval.GroupTheory.NovikovUnsolvableProblem.WordProblemSolvable
          (PresentedGroup.mk rels) :=
  (Submission.Helpers.NovikovCertificate.mk
    (certificate.n + 1)
    certificate.extensionRelators
    certificate.extensionRelators_finite
    certificate.finalEncode
    certificate.finalEncode_computable
    certificate.finalEncode_spec).sound

end SubgroupMembershipCertificate

end Submission.SubgroupReduction
