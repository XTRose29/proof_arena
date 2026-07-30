import Submission.OddOrder.MathlibSupport.CentralSylowPrimeCore
import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.SylowIntersection

/-!
Self-centralizing normal abelian subgroups and Sylow subgroups of their
ambient centralizers.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The mathlib-facing data extracted from MathComp's `A ∈ 'SCN(P)`. -/
structure IsSCN (P A : Subgroup G) : Prop where
  le_sylow : A ≤ P
  le_normalizer : P ≤ Subgroup.normalizer (A : Set G)
  commutative : IsMulCommutative A
  centralizerWithin_eq : centralizerWithin P A = A

/-- The centralizer of `A`, regarded as a subgroup of its normalizer. -/
def centralizerInNormalizer (A : Subgroup G) :
    Subgroup (Subgroup.normalizer (A : Set G)) :=
  (Subgroup.centralizer (A : Set G)).subgroupOf
    (Subgroup.normalizer (A : Set G))

instance centralizerInNormalizer_normal (A : Subgroup G) :
    (centralizerInNormalizer A).Normal :=
  Subgroup.normal_subgroupOf_centralizer_normalizer (A : Set G)

/-- Forget the redundant normalizer membership from an element of the
centralizer inside the normalizer. -/
def centralizerInNormalizerEquiv (A : Subgroup G) :
    centralizerInNormalizer A ≃* Subgroup.centralizer (A : Set G) where
  toFun z := ⟨(z : G), z.2⟩
  invFun z :=
    ⟨⟨(z : G), Subgroup.centralizer_le_normalizer (A : Set G) z.2⟩, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Intersect the ambient Sylow subgroup with the centralizer, first inside
the normalizer where the centralizer is normal. -/
noncomputable def scnIntersectionSylow
    (P : Sylow p G) (A : Subgroup G) (hA : IsSCN (P : Subgroup G) A) :
    Sylow p (centralizerInNormalizer A) :=
  normalIntersectionSylow (P.subtype hA.le_normalizer)
    (centralizerInNormalizer A)

/-- The SCN subgroup, realized as a Sylow subgroup of its full ambient
centralizer. -/
noncomputable def scnSylowInCentralizer
    (P : Sylow p G) (A : Subgroup G) (hA : IsSCN (P : Subgroup G) A) :
    Sylow p (Subgroup.centralizer (A : Set G)) :=
  (scnIntersectionSylow P A hA).mapSurjective
    (f := (centralizerInNormalizerEquiv A).toMonoidHom)
    (centralizerInNormalizerEquiv A).surjective

/-- The transported Sylow subgroup of the centralizer has ambient image
exactly `A`. -/
theorem map_scnSylowInCentralizer_eq
    (P : Sylow p G) (A : Subgroup G) (hA : IsSCN (P : Subgroup G) A) :
    (scnSylowInCentralizer P A hA :
      Subgroup (Subgroup.centralizer (A : Set G))).map
        (Subgroup.centralizer (A : Set G)).subtype = A := by
  letI : IsMulCommutative A := hA.commutative
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    simp only [scnSylowInCentralizer, Sylow.coe_mapSurjective] at hc
    rcases hc with ⟨q, hq, hqc⟩
    have hqP : (q : G) ∈ (P : Subgroup G) := by
      have hq' : q ∈
          (P.subtype hA.le_normalizer :
            Subgroup (Subgroup.normalizer (A : Set G))).comap
              (centralizerInNormalizer A).subtype :=
        (coe_normalIntersectionSylow
          (P.subtype hA.le_normalizer) (centralizerInNormalizer A)) ▸ hq
      exact hq'
    have hval : (q : G) = (c : G) := congrArg Subtype.val hqc
    apply le_of_eq hA.centralizerWithin_eq
    constructor
    · change (c : G) ∈ (P : Subgroup G)
      rw [← hval]
      exact hqP
    · exact c.2
  · intro hgA
    let c : Subgroup.centralizer (A : Set G) :=
      ⟨g, Subgroup.le_centralizer A hgA⟩
    let q : centralizerInNormalizer A :=
      (centralizerInNormalizerEquiv A).symm c
    have hqP : (q : G) ∈ (P : Subgroup G) := by
      simpa [q, c, centralizerInNormalizerEquiv] using hA.le_sylow hgA
    have hq : q ∈ (scnIntersectionSylow P A hA :
        Subgroup (centralizerInNormalizer A)) := by
      have hq' : q ∈
          (P.subtype hA.le_normalizer :
            Subgroup (Subgroup.normalizer (A : Set G))).comap
              (centralizerInNormalizer A).subtype := hqP
      exact (coe_normalIntersectionSylow
        (P.subtype hA.le_normalizer) (centralizerInNormalizer A)).symm ▸ hq'
    have hc : c ∈ (scnSylowInCentralizer P A hA :
        Subgroup (Subgroup.centralizer (A : Set G))) := by
      simp only [scnSylowInCentralizer, Sylow.coe_mapSurjective]
      exact ⟨q, hq, (centralizerInNormalizerEquiv A).apply_symm_apply c⟩
    exact ⟨c, hc, rfl⟩

theorem scnSylowInCentralizer_le_center
    (P : Sylow p G) (A : Subgroup G) (hA : IsSCN (P : Subgroup G) A) :
    (scnSylowInCentralizer P A hA :
      Subgroup (Subgroup.centralizer (A : Set G))) ≤
        Subgroup.center (Subgroup.centralizer (A : Set G)) := by
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro c
  apply Subtype.ext
  have hqA : (q : G) ∈ A := by
    have hqmap : (q : G) ∈
        (scnSylowInCentralizer P A hA :
          Subgroup (Subgroup.centralizer (A : Set G))).map
            (Subgroup.centralizer (A : Set G)).subtype :=
      ⟨q, hq, rfl⟩
    simpa only [map_scnSylowInCentralizer_eq P A hA] using hqmap
  exact (Subgroup.mem_centralizer_iff.mp c.2 (q : G) hqA).symm

/-- The `p'`-core of the ambient centralizer complements its SCN Sylow
subgroup. -/
theorem pPrimeCore_isComplement_scnSylowInCentralizer
    (P : Sylow p G) (A : Subgroup G) (hA : IsSCN (P : Subgroup G) A) :
    (pPrimeCore p (Subgroup.centralizer (A : Set G))).IsComplement'
      (scnSylowInCentralizer P A hA :
        Subgroup (Subgroup.centralizer (A : Set G))) :=
  pPrimeCore_isComplement_centralSylow
    (scnSylowInCentralizer P A hA)
    (scnSylowInCentralizer_le_center P A hA)

end Submission.OddOrder.MathlibSupport
