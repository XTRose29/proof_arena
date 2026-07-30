import Submission.OddOrder.BG.Section04.SCNRankThreeEmpty
import Submission.OddOrder.BG.Section05.Equivariance
import Submission.OddOrder.BG.Section07.PrimeSetCoreFunctorial

/-!
# Bender--Glauberman Section 10: the three prime-set cores

This file ports the definitions and elementary conjugation facts at the
start of `BGsection10.v` (through `not_narrow_ideal`).  MathComp's numerical
condition `2 < 'r_p(H)` is expressed by an elementary-abelian subgroup of
cardinal rank three, as in the earlier sections of this port.

The three sets are explicitly restricted to primes.  This does not change
any of the corresponding prime-set cores: only prime divisors are tested by
`IsPiNumber`.  It also makes the primality hypothesis needed by the Sylow
and narrowness APIs available directly from set membership.
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- `BGsection10.v: alpha`: primes for which `H` has elementary-abelian
rank at least three. -/
def alphaPrimes (H : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧
    Submission.OddOrder.BG.Section04.HasElementaryAbelianRankAtLeast p 3 H}

/-- `BGsection10.v: beta`: primes whose Sylow subgroups in `H` are not
narrow.  Narrowness is stated intrinsically on the Sylow subgroup; this is
equivalent to the ambient-subgroup formulation by `isNarrow_map_iff_of_injective`.
-/
def betaPrimes (H : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧
    ∀ P : Sylow p H,
      ¬ Submission.OddOrder.BG.Section05.IsNarrow p (⊤ : Subgroup P)}

/-- The ambient copy of a Sylow subgroup of `H`. -/
def ambientSylow {p : ℕ} (H : Subgroup G) (P : Sylow p H) : Subgroup G :=
  (P : Subgroup H).map H.subtype

/-- `BGsection10.v: sigma`: primes admitting a Sylow subgroup of `H` whose
ambient normalizer is contained in `H`. -/
def sigmaPrimes (H : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧
    ∃ P : Sylow p H,
      Subgroup.normalizer (ambientSylow H P : Set G) ≤ H}

/-- The `alpha(H)`-core of `H`. -/
def alphaCore (H : Subgroup G) : Subgroup G :=
  Submission.OddOrder.BG.Section07.primeSetCore (alphaPrimes H) H

/-- The `beta(H)`-core of `H`. -/
def betaCore (H : Subgroup G) : Subgroup G :=
  Submission.OddOrder.BG.Section07.primeSetCore (betaPrimes H) H

/-- The `sigma(H)`-core of `H`. -/
def sigmaCore (H : Subgroup G) : Subgroup G :=
  Submission.OddOrder.BG.Section07.primeSetCore (sigmaPrimes H) H

private theorem primeSetCore_map_mulEquiv_le
    (pi : Set ℕ) (H : Subgroup G) (e : G ≃* G) :
    (Submission.OddOrder.BG.Section07.primeSetCore pi H).map
        e.toMonoidHom ≤
      Submission.OddOrder.BG.Section07.primeSetCore pi
        (H.map e.toMonoidHom) := by
  let Good : Set (Subgroup G) :=
    {K | K ≤ H ∧ (K.subgroupOf H).Normal ∧
      IsPiNumber pi (Nat.card K)}
  change (sSup Good).map e.toMonoidHom ≤
    Submission.OddOrder.BG.Section07.primeSetCore pi
      (H.map e.toMonoidHom)
  rw [Subgroup.map_le_iff_le_comap]
  apply sSup_le
  intro K hK
  rw [← Subgroup.map_le_iff_le_comap]
  have hKH : K ≤ H := hK.1
  have hmapKH : K.map e.toMonoidHom ≤ H.map e.toMonoidHom :=
    Subgroup.map_mono hKH
  have hHnormK : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hK.2.1
  have hmapHnormK :
      H.map e.toMonoidHom ≤
        Subgroup.normalizer (K.map e.toMonoidHom : Set G) := by
    have hmapped := Subgroup.map_mono hHnormK (f := e.toMonoidHom)
    rwa [Subgroup.map_equiv_normalizer_eq K e] at hmapped
  have hmapNormal :
      ((K.map e.toMonoidHom).subgroupOf
        (H.map e.toMonoidHom)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hmapKH).mpr hmapHnormK
  have hmapPi : IsPiNumber pi (Nat.card (K.map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hK.2.2
  rw [Submission.OddOrder.BG.Section07.primeSetCore]
  exact le_sSup ⟨hmapKH, hmapNormal, hmapPi⟩

/-- Prime-set cores commute with ambient group automorphisms. -/
theorem primeSetCore_map_mulEquiv
    (pi : Set ℕ) (H : Subgroup G) (e : G ≃* G) :
    (Submission.OddOrder.BG.Section07.primeSetCore pi H).map
        e.toMonoidHom =
      Submission.OddOrder.BG.Section07.primeSetCore pi
        (H.map e.toMonoidHom) := by
  apply le_antisymm (primeSetCore_map_mulEquiv_le pi H e)
  have hback := primeSetCore_map_mulEquiv_le pi
    (H.map e.toMonoidHom) e.symm
  have hmapped := Subgroup.map_mono hback (f := e.toMonoidHom)
  simpa [Subgroup.map_map] using hmapped

private theorem alphaPrimes_map_mulEquiv_subset
    (H : Subgroup G) (e : G ≃* G) :
    alphaPrimes H ⊆ alphaPrimes (H.map e.toMonoidHom) := by
  intro p hp
  rcases hp with ⟨hp, E, hEH, hE⟩
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨hp, E.map e.toMonoidHom, Subgroup.map_mono hEH, ?_⟩
  exact
    Submission.OddOrder.BG.Section04.isElementaryAbelianOfRank_map_of_injective
      hE e.toMonoidHom e.injective

/-- `BGsection10.v: alphaJ`, for an arbitrary ambient automorphism. -/
theorem alphaPrimes_map_mulEquiv (H : Subgroup G) (e : G ≃* G) :
    alphaPrimes (H.map e.toMonoidHom) = alphaPrimes H := by
  apply Set.Subset.antisymm
  · intro p hp
    have hback := alphaPrimes_map_mulEquiv_subset
      (H.map e.toMonoidHom) e.symm hp
    simpa [Subgroup.map_map] using hback
  · exact alphaPrimes_map_mulEquiv_subset H e

private theorem isNarrow_top_mapSylow_iff
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] (e : A ≃* B) (P : Sylow p A) :
    Submission.OddOrder.BG.Section05.IsNarrow p
        (⊤ : Subgroup (P.mapSurjective
          (f := e.toMonoidHom) e.surjective)) ↔
      Submission.OddOrder.BG.Section05.IsNarrow p (⊤ : Subgroup P) := by
  let Q : Sylow p B := P.mapSurjective
    (f := e.toMonoidHom) e.surjective
  let eP₀ : P ≃* ((P : Subgroup A).map e.toMonoidHom) :=
    e.subgroupMap (P : Subgroup A)
  let eP : P ≃* Q :=
    eP₀.trans (MulEquiv.subgroupCongr (by rfl))
  have hiff :=
    Submission.OddOrder.BG.Section05.isNarrow_map_mulEquiv_iff
      (p := p) eP (⊤ : Subgroup P)
  rw [Subgroup.map_top_of_surjective eP.toMonoidHom eP.surjective] at hiff
  simpa [Q] using hiff

private theorem betaPrimes_map_mulEquiv_subset
    (H : Subgroup G) (e : G ≃* G) :
    betaPrimes H ⊆ betaPrimes (H.map e.toMonoidHom) := by
  intro p hp
  rcases hp with ⟨hp, hbeta⟩
  letI : Fact p.Prime := ⟨hp⟩
  let eH : H ≃* H.map e.toMonoidHom := e.subgroupMap H
  refine ⟨hp, ?_⟩
  intro Q hQnarrow
  obtain ⟨P, hPQ⟩ :=
    (Sylow.mapSurjective_surjective
      (f := eH.toMonoidHom) eH.surjective p) Q
  rw [← hPQ] at hQnarrow
  exact hbeta P ((isNarrow_top_mapSylow_iff eH P).mp hQnarrow)

/-- `BGsection10.v: betaJ`, for an arbitrary ambient automorphism. -/
theorem betaPrimes_map_mulEquiv (H : Subgroup G) (e : G ≃* G) :
    betaPrimes (H.map e.toMonoidHom) = betaPrimes H := by
  apply Set.Subset.antisymm
  · intro p hp
    have hback := betaPrimes_map_mulEquiv_subset
      (H.map e.toMonoidHom) e.symm hp
    simpa [Subgroup.map_map] using hback
  · exact betaPrimes_map_mulEquiv_subset H e

private theorem exists_ambientSylow_map_mulEquiv
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (e : G ≃* G) (P : Sylow p H) :
    ∃ Q : Sylow p (H.map e.toMonoidHom),
      ambientSylow (H.map e.toMonoidHom) Q =
        (ambientSylow H P).map e.toMonoidHom := by
  let eH₀ : H ≃* H.map (e : G →* G) := e.subgroupMap H
  let eH : H ≃* H.map e.toMonoidHom :=
    eH₀.trans (MulEquiv.subgroupCongr (by rfl))
  let Q : Sylow p (H.map e.toMonoidHom) :=
    P.mapSurjective (f := eH.toMonoidHom) eH.surjective
  refine ⟨Q, ?_⟩
  change
    (((P : Subgroup H).map eH.toMonoidHom).map
        (H.map e.toMonoidHom).subtype) =
      (((P : Subgroup H).map H.subtype).map e.toMonoidHom)
  rw [Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f : H →* G ↦ (P : Subgroup H).map f)
  ext h
  rfl

private theorem sigmaPrimes_map_mulEquiv_subset
    (H : Subgroup G) (e : G ≃* G) :
    sigmaPrimes H ⊆ sigmaPrimes (H.map e.toMonoidHom) := by
  intro p hp
  rcases hp with ⟨hp, P, hnormal⟩
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ⟩ := exists_ambientSylow_map_mulEquiv H e P
  refine ⟨hp, Q, ?_⟩
  have hmapped := Subgroup.map_mono hnormal (f := e.toMonoidHom)
  rw [Subgroup.map_equiv_normalizer_eq (ambientSylow H P) e] at hmapped
  rw [hQ]
  exact hmapped

/-- `BGsection10.v: sigmaJ`, for an arbitrary ambient automorphism. -/
theorem sigmaPrimes_map_mulEquiv (H : Subgroup G) (e : G ≃* G) :
    sigmaPrimes (H.map e.toMonoidHom) = sigmaPrimes H := by
  apply Set.Subset.antisymm
  · intro p hp
    have hback := sigmaPrimes_map_mulEquiv_subset
      (H.map e.toMonoidHom) e.symm hp
    simpa [Subgroup.map_map] using hback
  · exact sigmaPrimes_map_mulEquiv_subset H e

/-- Conjugation invariance of `alphaPrimes`. -/
theorem alphaPrimes_conj (H : Subgroup G) (x : G) :
    alphaPrimes (H.map (MulAut.conj x).toMonoidHom) = alphaPrimes H :=
  alphaPrimes_map_mulEquiv H (MulAut.conj x)

/-- Conjugation invariance of `betaPrimes`. -/
theorem betaPrimes_conj (H : Subgroup G) (x : G) :
    betaPrimes (H.map (MulAut.conj x).toMonoidHom) = betaPrimes H :=
  betaPrimes_map_mulEquiv H (MulAut.conj x)

/-- Conjugation invariance of `sigmaPrimes`. -/
theorem sigmaPrimes_conj (H : Subgroup G) (x : G) :
    sigmaPrimes (H.map (MulAut.conj x).toMonoidHom) = sigmaPrimes H :=
  sigmaPrimes_map_mulEquiv H (MulAut.conj x)

/-- `BGsection10.v: MalphaJ`, for an arbitrary ambient automorphism. -/
theorem alphaCore_map_mulEquiv (H : Subgroup G) (e : G ≃* G) :
    alphaCore (H.map e.toMonoidHom) =
      (alphaCore H).map e.toMonoidHom := by
  rw [alphaCore, alphaCore, alphaPrimes_map_mulEquiv]
  exact (primeSetCore_map_mulEquiv (alphaPrimes H) H e).symm

/-- `BGsection10.v: MbetaJ`, for an arbitrary ambient automorphism. -/
theorem betaCore_map_mulEquiv (H : Subgroup G) (e : G ≃* G) :
    betaCore (H.map e.toMonoidHom) =
      (betaCore H).map e.toMonoidHom := by
  rw [betaCore, betaCore, betaPrimes_map_mulEquiv]
  exact (primeSetCore_map_mulEquiv (betaPrimes H) H e).symm

/-- `BGsection10.v: MsigmaJ`, for an arbitrary ambient automorphism. -/
theorem sigmaCore_map_mulEquiv (H : Subgroup G) (e : G ≃* G) :
    sigmaCore (H.map e.toMonoidHom) =
      (sigmaCore H).map e.toMonoidHom := by
  rw [sigmaCore, sigmaCore, sigmaPrimes_map_mulEquiv]
  exact (primeSetCore_map_mulEquiv (sigmaPrimes H) H e).symm

/-- Conjugation covariance of the `alpha`-core. -/
theorem alphaCore_conj (H : Subgroup G) (x : G) :
    alphaCore (H.map (MulAut.conj x).toMonoidHom) =
      (alphaCore H).map (MulAut.conj x).toMonoidHom :=
  alphaCore_map_mulEquiv H (MulAut.conj x)

/-- Conjugation covariance of the `beta`-core. -/
theorem betaCore_conj (H : Subgroup G) (x : G) :
    betaCore (H.map (MulAut.conj x).toMonoidHom) =
      (betaCore H).map (MulAut.conj x).toMonoidHom :=
  betaCore_map_mulEquiv H (MulAut.conj x)

/-- Conjugation covariance of the `sigma`-core. -/
theorem sigmaCore_conj (H : Subgroup G) (x : G) :
    sigmaCore (H.map (MulAut.conj x).toMonoidHom) =
      (sigmaCore H).map (MulAut.conj x).toMonoidHom :=
  sigmaCore_map_mulEquiv H (MulAut.conj x)

/-- The `alpha`-core is contained in its defining subgroup. -/
theorem alphaCore_le (H : Subgroup G) : alphaCore H ≤ H :=
  Submission.OddOrder.BG.Section07.primeSetCore_le (alphaPrimes H) H

/-- The `beta`-core is contained in its defining subgroup. -/
theorem betaCore_le (H : Subgroup G) : betaCore H ≤ H :=
  Submission.OddOrder.BG.Section07.primeSetCore_le (betaPrimes H) H

/-- The `sigma`-core is contained in its defining subgroup. -/
theorem sigmaCore_le (H : Subgroup G) : sigmaCore H ≤ H :=
  Submission.OddOrder.BG.Section07.primeSetCore_le (sigmaPrimes H) H

/-- The `alpha`-core is normal in its defining subgroup. -/
theorem alphaCore_normal (H : Subgroup G) :
    ((alphaCore H).subgroupOf H).Normal :=
  Submission.OddOrder.BG.Section07.primeSetCore_normal (alphaPrimes H) H

/-- The `beta`-core is normal in its defining subgroup. -/
theorem betaCore_normal (H : Subgroup G) :
    ((betaCore H).subgroupOf H).Normal :=
  Submission.OddOrder.BG.Section07.primeSetCore_normal (betaPrimes H) H

/-- The `sigma`-core is normal in its defining subgroup. -/
theorem sigmaCore_normal (H : Subgroup G) :
    ((sigmaCore H).subgroupOf H).Normal :=
  Submission.OddOrder.BG.Section07.primeSetCore_normal (sigmaPrimes H) H

/-- The `alpha`-core has `alpha(H)`-number cardinality. -/
theorem alphaCore_isPiNumber (H : Subgroup G) :
    IsPiNumber (alphaPrimes H) (Nat.card (alphaCore H)) :=
  Submission.OddOrder.BG.Section07.primeSetCore_isPiNumber
    (alphaPrimes H) H

/-- The `beta`-core has `beta(H)`-number cardinality. -/
theorem betaCore_isPiNumber (H : Subgroup G) :
    IsPiNumber (betaPrimes H) (Nat.card (betaCore H)) :=
  Submission.OddOrder.BG.Section07.primeSetCore_isPiNumber
    (betaPrimes H) H

/-- The `sigma`-core has `sigma(H)`-number cardinality. -/
theorem sigmaCore_isPiNumber (H : Subgroup G) :
    IsPiNumber (sigmaPrimes H) (Nat.card (sigmaCore H)) :=
  Submission.OddOrder.BG.Section07.primeSetCore_isPiNumber
    (sigmaPrimes H) H

/-- `BGsection10.v: not_narrow_ideal`.

If one Sylow subgroup of a finite group is not narrow, then none is. -/
theorem not_narrow_ideal {p : ℕ} [Fact p.Prime]
    (P : Sylow p G)
    (hP :
      ¬ Submission.OddOrder.BG.Section05.IsNarrow p (P : Subgroup G)) :
    p ∈ betaPrimes (⊤ : Subgroup G) := by
  have hPtop :
      ¬ Submission.OddOrder.BG.Section05.IsNarrow p
        (⊤ : Subgroup P) := by
    intro htop
    apply hP
    have hiff :=
      Submission.OddOrder.BG.Section05.isNarrow_map_iff_of_injective
        (p := p) (P : Subgroup G).subtype
          (P : Subgroup G).subtype_injective (⊤ : Subgroup P)
    have hmapTop :
        (⊤ : Subgroup P).map (P : Subgroup G).subtype =
          (P : Subgroup G) := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hmapTop] at hiff
    exact hiff.mpr htop
  refine ⟨Fact.out, ?_⟩
  intro Q hQnarrow
  let topEquiv : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  let R : Sylow p G := Q.mapSurjective
    (f := topEquiv.toMonoidHom) topEquiv.surjective
  have hR :
      ¬ Submission.OddOrder.BG.Section05.IsNarrow p
        (⊤ : Subgroup R) := by
    intro hRnarrow
    let ePR : P ≃* R := Sylow.equiv P R
    have hiff :=
      Submission.OddOrder.BG.Section05.isNarrow_map_mulEquiv_iff
        (p := p) ePR (⊤ : Subgroup P)
    apply hPtop
    simpa using hiff.mp (by simpa using hRnarrow)
  apply hR
  exact (isNarrow_top_mapSylow_iff topEquiv Q).mpr hQnarrow

end Submission.OddOrder.BG.Section10
