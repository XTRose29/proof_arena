import Submission.OddOrder.BG.AppendixAB.QuadraticConjugation
import Submission.OddOrder.BG.AppendixAB.TwoGenerator
import Submission.OddOrder.MathlibSupport.Cardinality
import Mathlib.GroupTheory.Index

/-!
Functorial transport of quadratic pairs through group homomorphisms.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport

variable {G K : Type*} [Group G] [Group K]

/-- Quadratic p-elements remain quadratic after applying a group
homomorphism, on the image of the acted-on subgroup. -/
theorem IsQuadraticPElement.map {p : ℕ} {E : Subgroup G} {x : G}
    (hx : IsQuadraticPElement p E x) (f : G →* K) :
    IsQuadraticPElement p (E.map f) (f x) := by
  refine ⟨hx.1.map f, ?_⟩
  have hcommutator :
      (⁅E, Subgroup.zpowers x⁆ : Subgroup G).map f =
        ⁅E.map f, Subgroup.zpowers (f x)⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [← hcommutator] at hz
  rcases hz with ⟨y, hy, rfl⟩
  have hxy := Subgroup.mem_centralizer_iff.mp hx.2 y hy
  simpa using congrArg f hxy

/-- The image of a subgroup normalizing `E` normalizes the image of `E`. -/
theorem map_le_normalizer_map (f : G →* K) {A E : Subgroup G}
    (hAE : A ≤ Subgroup.normalizer (E : Set G)) :
    A.map f ≤ Subgroup.normalizer (E.map f : Set K) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨a * e * a⁻¹, (hAE ha e).mp he, ?_⟩
    simp
  · rintro ⟨e, he, hfe⟩
    refine ⟨a⁻¹ * e * a, (Subgroup.mem_normalizer_iff''.mp (hAE ha) e).mp he, ?_⟩
    rw [map_mul, map_mul, map_inv, hfe]
    group

/-- Normalizer membership transports to the image subgroup. -/
theorem map_mem_normalizer_map (f : G →* K) {E : Subgroup G} {x : G}
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) :
    f x ∈ Subgroup.normalizer (E.map f : Set K) := by
  apply map_le_normalizer_map f (A := Subgroup.zpowers x)
  · rw [Subgroup.zpowers_le]
    exact hxE
  · exact ⟨x, Subgroup.mem_zpowers x, rfl⟩

/-- The generated pair in the target is the image of the generated pair in
the source. -/
theorem pairGenerated_map_eq (f : G →* K) (x y : G) :
    pairGenerated (f x) (f y) = (pairGenerated x y).map f := by
  rw [pairGenerated, pairGenerated, Subgroup.map_sup,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]

/-- Oddness of a generated pair descends through every homomorphic image. -/
theorem odd_natCard_pairGenerated_map [Finite G]
    (f : G →* K) {x y : G}
    (hodd : Odd (Nat.card (pairGenerated x y))) :
    Odd (Nat.card (pairGenerated (f x) (f y))) := by
  rw [pairGenerated_map_eq]
  exact hodd.of_dvd_nat ((pairGenerated x y).card_map_dvd f)

/-- The p-group property of the acted-on subgroup descends to its image. -/
theorem isPGroup_map {p : ℕ} {E : Subgroup G}
    (hE : IsPGroup p E) (f : G →* K) :
    IsPGroup p (E.map f) :=
  hE.map f

/-- A complete quadratic-pair hypothesis transports through a homomorphism. -/
theorem quadraticPair_map {p : ℕ} [Finite G]
    (f : G →* K) {E : Subgroup G} {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hodd : Odd (Nat.card (pairGenerated x y)))
    (hE : IsPGroup p E)
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y) :
    f x ∈ Subgroup.normalizer (E.map f : Set K) ∧
    f y ∈ Subgroup.normalizer (E.map f : Set K) ∧
    Odd (Nat.card (pairGenerated (f x) (f y))) ∧
    IsPGroup p (E.map f) ∧
    IsQuadraticPElement p (E.map f) (f x) ∧
    IsQuadraticPElement p (E.map f) (f y) :=
  ⟨map_mem_normalizer_map f hxN, map_mem_normalizer_map f hyN,
    odd_natCard_pairGenerated_map f hodd, hE.map f, hx.map f, hy.map f⟩

end Submission.OddOrder.BG.AppendixAB
