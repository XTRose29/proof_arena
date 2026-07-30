import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Maschke
import Submission.OddOrder.MathlibSupport.SubrepresentationModuleEquiv

/-!
Selecting a simple Maschke constituent on which a normal subgroup acts
nontrivially.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The vectors fixed by a normal subgroup form an ambient
subrepresentation. -/
noncomputable def normalInvariantsSubrepresentation
    (rho : Representation k G V) (N : Subgroup G) [N.Normal] :
    Subrepresentation rho where
  toSubmodule := Representation.invariants (rho.comp N.subtype)
  apply_mem_toSubmodule g := Representation.le_comap_invariants rho N g

@[simp]
theorem normalInvariantsSubrepresentation_toSubmodule
    (rho : Representation k G V) (N : Subgroup G) [N.Normal] :
    (normalInvariantsSubrepresentation rho N).toSubmodule =
      Representation.invariants (rho.comp N.subtype) :=
  rfl

/-- A subrepresentation lies in the normal fixed space exactly when the
normal subgroup acts trivially on it. -/
theorem le_normalInvariantsSubrepresentation_iff
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation rho) :
    U ≤ normalInvariantsSubrepresentation rho N ↔
      N ≤ U.toRepresentation.ker := by
  constructor
  · intro h n hn
    rw [MonoidHom.mem_ker]
    ext x
    change rho n (x : V) = x
    exact (Representation.mem_invariants _ _).mp (h x.property) ⟨n, hn⟩
  · intro h x hx
    rw [show x ∈ normalInvariantsSubrepresentation rho N ↔
      x ∈ Representation.invariants (rho.comp N.subtype) from Iff.rfl,
      Representation.mem_invariants]
    intro n
    have hnker := h n.property
    rw [MonoidHom.mem_ker] at hnker
    exact congrArg Subtype.val (DFunLike.congr_fun hnker ⟨x, hx⟩)

/-- If a normal subgroup acts nontrivially on a finite coprime
representation, it acts nontrivially on some irreducible Maschke
constituent. -/
theorem exists_irreducible_subrepresentation_not_le_ker_of_normal
    [Finite G]
    (rho : Representation k G V)
    (N : Subgroup G) [N.Normal]
    (hcard : (Nat.card G : k) ≠ 0)
    (hN : ¬ N ≤ rho.ker) :
    ∃ U : Subrepresentation rho,
      Representation.IsIrreducible U.toRepresentation ∧
        ¬ N ≤ U.toRepresentation.ker := by
  classical
  letI : NeZero (Nat.card G : k) := ⟨hcard⟩
  letI : IsSemisimpleModule k[G] rho.asModule := by infer_instance
  by_contra hnone
  have hall (U : Subrepresentation rho)
      (hU : Representation.IsIrreducible U.toRepresentation) :
      N ≤ U.toRepresentation.ker := by
    by_contra hnot
    exact hnone ⟨U, hU, hnot⟩
  let F : Subrepresentation rho := normalInvariantsSubrepresentation rho N
  have hsimple_le (m : Submodule k[G] rho.asModule)
      (hm : IsSimpleModule k[G] m) : m ≤ F.asSubmodule := by
    let U : Subrepresentation rho := Subrepresentation.ofSubmodule' m
    have hU : Representation.IsIrreducible U.toRepresentation :=
      (irreducible_toRepresentation_iff_isSimpleModule_asSubmodule rho U).mpr hm
    have hUF : U ≤ F :=
      (le_normalInvariantsSubrepresentation_iff rho N U).mpr (hall U hU)
    intro x hx
    exact hUF hx
  have hsup : sSup {m : Submodule k[G] rho.asModule |
      IsSimpleModule k[G] m} = ⊤ :=
    IsSemisimpleModule.sSup_simples_eq_top k[G] rho.asModule
  have htop : (⊤ : Submodule k[G] rho.asModule) ≤ F.asSubmodule := by
    rw [← hsup]
    exact sSup_le fun m hm ↦ hsimple_le m hm
  have hFtop : F.asSubmodule = ⊤ := eq_top_iff.mpr htop
  apply hN
  intro n hn
  rw [MonoidHom.mem_ker]
  ext v
  have hvF : v ∈ F := by
    change v ∈ F.asSubmodule
    rw [hFtop]
    trivial
  exact (Representation.mem_invariants _ _).mp hvF ⟨n, hn⟩

end Submission.OddOrder.MathlibSupport
