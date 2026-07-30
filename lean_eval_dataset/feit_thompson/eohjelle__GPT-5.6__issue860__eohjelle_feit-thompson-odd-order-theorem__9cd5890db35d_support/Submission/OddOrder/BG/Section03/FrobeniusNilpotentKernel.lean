import Submission.OddOrder.BG.Section03.FrobeniusQuotient
import Submission.OddOrder.BG.Section03.FrobeniusNormalSubgroup
import Submission.OddOrder.BG.Section03.FrobeniusZeroInvariants
import Submission.OddOrder.BG.Section03.SemidirectProperKernel
import Submission.OddOrder.BG.Section03.SemiregularConjugation
import Submission.OddOrder.MathlibSupport.ChiefFactorFaithfulPCore
import Submission.OddOrder.MathlibSupport.ChiefStabilizerFitting
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.CoprimeElementaryAbelianComplement
import Submission.OddOrder.MathlibSupport.NilpotentNormalCenter
import Submission.OddOrder.MathlibSupport.PGroupCardCast
import Submission.OddOrder.MathlibSupport.PrimeOrderCentralizer
import Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy

/-!
Bender--Glauberman Theorem 3.7.

A solvable Frobenius kernel with a complement of prime order is nilpotent.
The proof follows the source formalization: choose a maximal ambient-normal
proper subgroup of the kernel, use induction on the corresponding smaller
semidirect product, and then stabilize the chief factors below the Fitting
subgroup.  Equal-characteristic factors are killed by the faithful
chief-factor `p`-core theorem; unequal-characteristic factors are killed by
the Frobenius fixed-vector lemma after quotienting by the maximal subgroup.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative commutatorElement

noncomputable section

universe u

private theorem isChiefFactor_of_maximal_normal
    {G : Type u} [Group G] [Finite G]
    {L K : Subgroup G}
    (hKnormal : K.Normal) (hLK : L < K)
    (hLnormal : L.Normal)
    (hmax : ∀ M : Subgroup G, M.Normal → M < K → L ≤ M → M ≤ L) :
    @IsChiefFactor G _ L K hLnormal := by
  letI : L.Normal := hLnormal
  let q : G →* G ⧸ L := QuotientGroup.mk' L
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective L
  refine ⟨hLK.le, hKnormal, ?_⟩
  refine ⟨?_, Subgroup.Normal.map hKnormal q hqsurj, ?_⟩
  · intro hmap
    have hKL : K ≤ L := by
      have hker : K ≤ q.ker := (Subgroup.map_eq_bot_iff K).mp hmap
      simpa [q, QuotientGroup.ker_mk'] using hker
    exact (not_le_of_gt hLK) hKL
  · intro N hNnormal hNK hNne
    let M : Subgroup G := N.comap q
    have hMnormal : M.Normal := by
      dsimp [M]
      exact Subgroup.Normal.comap hNnormal q
    have hLM : L ≤ M := by
      dsimp [M, q]
      exact QuotientGroup.le_comap_mk' L N
    have hMK : M ≤ K := by
      have hkerK : q.ker ≤ K := by
        simpa [q, QuotientGroup.ker_mk'] using hLK.le
      calc
        M ≤ (K.map q).comap q := Subgroup.comap_mono hNK
        _ = K := Subgroup.comap_map_eq_self hkerK
    by_contra hKN
    have hnKM : ¬ K ≤ M := by
      intro hKM
      apply hKN
      exact Subgroup.map_le_iff_le_comap.mpr hKM
    have hMltK : M < K :=
      lt_of_le_of_ne hMK (fun hMK' ↦ hnKM hMK'.ge)
    have hML : M ≤ L := hmax M hMnormal hMltK hLM
    have hML_eq : M = L := le_antisymm hML hLM
    apply hNne
    calc
      N = M.map q :=
        (Subgroup.map_comap_eq_self_of_surjective hqsurj N).symm
      _ = L.map q := congrArg (fun X : Subgroup G ↦ X.map q) hML_eq
      _ = ⊥ := QuotientGroup.map_mk'_self L

private theorem subgroup_le_ker_chiefFactorConjugationHom_iff
    {G : Type u} [Group G]
    {V U H : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U) :
    H ≤ (chiefFactorConjugationHom hchief).ker ↔ ⁅H, U⁆ ≤ V := by
  letI : U.Normal := hchief.upper_normal
  have hmem (g : G) :
      g ∈ (chiefFactorConjugationHom hchief).ker ↔
        ∀ u : G, u ∈ U → ⁅g, u⁆ ∈ V := by
    exact mem_ker_subgroupConjugationFactorHom_iff
      V U ⊤ Subgroup.le_normalizer_of_normal
        Subgroup.le_normalizer_of_normal ⟨g, trivial⟩
  constructor
  · intro hker
    apply Subgroup.commutator_le.mpr
    intro g hg u hu
    exact (hmem g).mp (hker hg) u hu
  · intro hcomm g hg
    apply (hmem g).mpr
    intro u hu
    exact Subgroup.commutator_le.mp hcomm g hg u hu

/-- The Fitting subgroup centralizes every ambient chief factor contained in
it.  This is the source lemma `Fitting_stab_chief` in the exact form needed
for Theorem 3.7. -/
private theorem fittingCore_stabilizes_chiefFactor
    {G : Type u} [Group G] [Finite G]
    {V U : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U)
    (hUF : U ≤ fittingCore G) :
    ⁅fittingCore G, U⁆ ≤ V := by
  classical
  let F : Subgroup G := fittingCore G
  let q : G →* G ⧸ V := QuotientGroup.mk' V
  let Fq : Subgroup (G ⧸ V) := F.map q
  let Uq : Subgroup (G ⧸ V) := U.map q
  have hUqFq : Uq ≤ Fq := Subgroup.map_mono hUF
  let VF : Subgroup F := V.subgroupOf F
  letI : VF.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : V.Normal) F
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  let eF : (F ⧸ VF) ≃* Fq :=
    QuotientGroup.liftEquiv VF (q.subgroupMap_surjective F) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])
  have hFqnil : Group.IsNilpotent Fq := by
    exact Group.nilpotent_of_mulEquiv eF
  letI : Group.IsNilpotent Fq := hFqnil
  letI : Fq.Normal :=
    Subgroup.Normal.map (inferInstance : F.Normal) q
      (QuotientGroup.mk'_surjective V)
  letI : Uq.Normal :=
    Subgroup.Normal.map hchief.upper_normal q
      (QuotientGroup.mk'_surjective V)
  let UF : Subgroup Fq := Uq.subgroupOf Fq
  letI : UF.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : Uq.Normal) Fq
  have hUFne : UF ≠ ⊥ := by
    intro hbot
    apply hchief.quotient_minimal_normal.ne_bot
    have hmapped := congrArg (fun S : Subgroup Fq ↦ S.map Fq.subtype) hbot
    simpa [UF, Subgroup.map_subgroupOf_eq_of_le hUqFq] using hmapped
  let Zq : Subgroup (G ⧸ V) :=
    (Subgroup.center Fq).map Fq.subtype
  have hZqnormal : Zq.Normal := by
    constructor
    intro z hz g
    exact characteristic_map_subtype_invariant_under_normalizer
      Fq ⊤ (Subgroup.center Fq) (by
        rw [Fq.normalizer_eq_top]) g trivial z hz
  letI : Zq.Normal := hZqnormal
  let C : Subgroup (G ⧸ V) := Uq ⊓ Zq
  letI : C.Normal := by
    dsimp [C]
    infer_instance
  let M : Subgroup Fq := UF ⊓ Subgroup.center Fq
  have hMne : M ≠ ⊥ := by
    dsimp [M]
    exact nilpotent_normal_inf_center_ne_bot UF hUFne
  have hmapM : M.map Fq.subtype = C := by
    dsimp [M, C, Zq, UF]
    rw [Subgroup.map_inf _ _ _ Fq.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hUqFq]
  have hCne : C ≠ ⊥ := by
    rw [← hmapM]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      M Fq.subtype_injective)).mpr hMne
  have hCU : C = Uq :=
    hchief.quotient_minimal_normal.eq_of_normal_le
      (inferInstance : C.Normal) inf_le_left hCne
  have hUqZ : Uq ≤ Zq := by
    rw [← hCU]
    exact inf_le_right
  have hcentral : Fq ≤ Subgroup.centralizer (Uq : Set (G ⧸ V)) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨zF, hzF, rfl⟩ := hUqZ hz
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzF ⟨f, hf⟩)).symm
  have hcommq : ⁅Fq, Uq⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
  have hmap : ⁅F, U⁆.map q = ⊥ := by
    rw [Subgroup.map_commutator]
    exact hcommq
  have hker : ⁅F, U⁆ ≤ q.ker :=
    (Subgroup.map_eq_bot_iff ⁅F, U⁆).mp hmap
  simpa [F, q, QuotientGroup.ker_mk'] using hker

private def PrimeFrobeniusSolKernelNilStatement (n : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Nat.card G = n →
    ∀ (K R : Subgroup G),
      K.IsComplement' R →
      K.Normal →
      IsSolvable G →
      (Nat.card R).Prime →
      centralizerWithin K R = ⊥ →
      Group.IsNilpotent K

private theorem primeFrobeniusSolKernelNilStatement_all (n : ℕ) :
    PrimeFrobeniusSolKernelNilStatement.{u} n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G _ _ hcard K R hKR hKnormal hsol hRprime hcent
      classical
      letI : Fintype G := Fintype.ofFinite G
      letI : IsSolvable G := hsol
      by_cases hKbot : K = ⊥
      · subst K
        infer_instance
      have hRne : R ≠ ⊥ := by
        rw [← R.one_lt_card_iff_ne_bot]
        exact hRprime.one_lt
      have hreg : IsSemiregularConjugation K R := by
        intro r hr k hk
        have hcomm : Commute (r : G) (k : G) := by
          rw [Commute]
          calc
            (r : G) * (k : G) =
                ((r : G) * (k : G) * (r : G)⁻¹) * (r : G) := by group
            _ = (k : G) * (r : G) := by rw [hk]
        have hcyclic : Subgroup.zpowers (r : G) = R :=
          zpowers_eq_of_mem_subgroup_prime_card
            R hRprime r.property (by
              intro hrG
              apply hr
              apply Subtype.ext
              exact hrG)
        have hkcent : (k : G) ∈ centralizerWithin K R := by
          refine ⟨k.property, ?_⟩
          intro y hy
          have hy' : y ∈ Subgroup.zpowers (r : G) := by
            rwa [hcyclic]
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
          exact (hcomm.zpow_left m).eq
        have hkbot : (k : G) ∈ (⊥ : Subgroup G) := by
          rw [← hcent]
          exact hkcent
        apply Subtype.ext
        exact Subgroup.mem_bot.mp hkbot
      have hRnormK : R ≤ Subgroup.normalizer (K : Set G) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr hKnormal]
        exact le_top
      have hFrob : IsFrobeniusDecomposition K R :=
        hreg.isFrobeniusDecomposition hRnormK hKR.sup_eq_top hKbot hRne

      let Good : Subgroup G → Prop := fun L ↦ L.Normal ∧ L < K
      have hbotGood : Good ⊥ :=
        ⟨by infer_instance, bot_lt_iff_ne_bot.mpr hKbot⟩
      obtain ⟨L, _hbotL, hLgood, hLmax⟩ :=
        Finite.exists_le_maximal (p := Good) hbotGood
      letI : L.Normal := hLgood.1
      have hLK : L < K := hLgood.2
      have hRnormL : R ≤ Subgroup.normalizer (L : Set G) := by
        rw [L.normalizer_eq_top]
        exact le_top

      let J : Subgroup G := R ⊔ L
      let LJ : Subgroup J := L.subgroupOf J
      let RJ : Subgroup J := R.subgroupOf J
      letI : LJ.Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer hRnormL
      have hcompJ : LJ.IsComplement' RJ := by
        simpa [J, LJ, RJ] using
          properKernel_subgroupOf_isComplement hKR hLK.le hRnormL
      have hJlt : Nat.card J < Nat.card G := by
        simpa [J] using
          natCard_sup_lt_of_properKernel hKR hLK hRnormL
      have hsolJ : IsSolvable J := isSolvable_sup
      have hRJprime : (Nat.card RJ).Prime := by
        rw [natCard_subgroupOf_eq (show R ≤ J from le_sup_left)]
        exact hRprime
      have hcentJ : centralizerWithin LJ RJ = ⊥ := by
        apply le_bot_iff.mp
        intro x hx
        have hxG : (x : G) ∈ centralizerWithin K R := by
          refine ⟨hLK.le hx.1, ?_⟩
          intro r hr
          let rJ : J := ⟨r, (show R ≤ J from le_sup_left) hr⟩
          have hrJ : rJ ∈ RJ := hr
          exact congrArg Subtype.val (hx.2 rJ hrJ)
        have hxbotG : (x : G) ∈ (⊥ : Subgroup G) := by
          rw [← hcent]
          exact hxG
        exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxbotG))
      have hnilLJ : Group.IsNilpotent LJ := by
        apply ih (Nat.card J)
        · rwa [← hcard]
        · rfl
        · exact hcompJ
        · infer_instance
        · exact hsolJ
        · exact hRJprime
        · exact hcentJ
      have hnilL : Group.IsNilpotent L := by
        letI : Group.IsNilpotent LJ := hnilLJ
        exact Group.nilpotent_of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe
            (show L ≤ J from le_sup_right))
      have hLF : L ≤ fittingCore G :=
        nilpotent_normal_le_fittingCore
          (inferInstance : L.Normal) hnilL
      have hchiefLK : IsChiefFactor L K :=
        isChiefFactor_of_maximal_normal hKnormal hLK hLgood.1
          (fun M hMnormal hMlt hLM ↦ hLmax ⟨hMnormal, hMlt⟩ hLM)
      obtain ⟨q, hqprime, hKq, _hKqpow⟩ :=
        hchiefLK.exists_prime_isPGroup_pow_eq_one
      letI : Fact q.Prime := ⟨hqprime⟩

      have hKF : K ≤ fittingCore G := by
        by_contra hnotKF
        have hFK : fittingCore G ≤ K :=
          hFrob.normal_le_kernel_or_kernel_le
            (N := fittingCore G) |>.resolve_right hnotKF
        apply hnotKF
        apply normal_le_fittingCore_of_stabilizes_chiefFactors hKnormal
        intro V U hVnormal hchief hUF
        letI : V.Normal := hVnormal
        have hUK : U ≤ K := hUF.trans hFK
        have hVK : V ≤ K := hchief.le.trans hUK
        have hLstab : ⁅L, U⁆ ≤ V :=
          (Subgroup.commutator_mono hLF le_rfl).trans
            (fittingCore_stabilizes_chiefFactor hchief hUF)
        let a : G →* MulAut (U ⧸ V.subgroupOf U) :=
          chiefFactorConjugationHom hchief
        have hLa : L ≤ a.ker :=
          (subgroup_le_ker_chiefFactorConjugationHom_iff hchief).mpr hLstab
        let qL : G →* G ⧸ L := QuotientGroup.mk' L
        let Kq : Subgroup (G ⧸ L) := K.map qL
        let Rq : Subgroup (G ⧸ L) := R.map qL
        have hFrobq : IsFrobeniusDecomposition Kq Rq := by
          simpa [qL, Kq, Rq] using hFrob.quotient hLK
        have hKq' : IsPGroup q Kq := by
          simpa [qL, Kq] using hKq

        let qV : G →* G ⧸ V := QuotientGroup.mk' V
        let Uv : Subgroup (G ⧸ V) := U.map qV
        let Rv : Subgroup (G ⧸ V) := R.map qV
        obtain ⟨p, hpprime, hUvP, hUvPow⟩ :=
          hchief.exists_prime_isPGroup_pow_eq_one
        letI : Fact p.Prime := ⟨hpprime⟩
        let E := U ⧸ V.subgroupOf U
        let eE : E ≃* Uv :=
          QuotientGroup.liftEquiv (V.subgroupOf U)
            (qV.subgroupMap_surjective U) (by
              rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])
        letI : IsMulCommutative Uv :=
          hchief.quotient_minimal_normal.isMulCommutative
        letI : IsMulCommutative E := by
          refine ⟨⟨fun x y ↦ eE.injective ?_⟩⟩
          simp only [map_mul]
          exact mul_comm _ _
        have hpowE : ∀ x : E, x ^ p = 1 := by
          intro x
          apply eE.injective
          simpa using hUvPow (eE x)
        letI : Module (ZMod p) (Additive E) :=
          AddCommGroup.zmodModule fun x ↦ by
            change x.toMul ^ p = 1
            exact hpowE x.toMul

        rcases eq_or_ne q p with hqp | hqp
        · have hKqP : IsPGroup p Kq := by
            simpa [hqp] using hKq'
          let qa : G →* G ⧸ a.ker := QuotientGroup.mk' a.ker
          have hLqa : L ≤ qa.ker := by
            simpa [qa, QuotientGroup.ker_mk'] using hLa
          let f : (G ⧸ L) →* (G ⧸ a.ker) :=
            QuotientGroup.lift L qa hLqa
          have hmapK : Kq.map f = K.map qa := by
            dsimp [Kq, qL, f]
            rw [Subgroup.map_map]
            rfl
          have hKqaP : IsPGroup p (K.map qa) := by
            rw [← hmapK]
            exact hKqP.map f
          have hKqaNormal : (K.map qa).Normal :=
            Subgroup.Normal.map hKnormal qa
              (QuotientGroup.mk'_surjective a.ker)
          have hKqaCore : K.map qa ≤ pCore p (G ⧸ a.ker) :=
            le_pCore hKqaP hKqaNormal
          have hcoreBot : pCore p (G ⧸ a.ker) = ⊥ := by
            simpa [a] using
              pCore_quotient_ker_chiefFactorConjugationHom_eq_bot
                hchief hUvP
          have hKmapBot : K.map qa = ⊥ :=
            le_bot_iff.mp (hKqaCore.trans_eq hcoreBot)
          have hKa : K ≤ a.ker := by
            have := (Subgroup.map_eq_bot_iff K).mp hKmapBot
            simpa [qa, QuotientGroup.ker_mk'] using this
          exact
            (subgroup_le_ker_chiefFactorConjugationHom_iff hchief).mp hKa
        · have hpq : p ≠ q := hqp.symm
          have hcopVR : Nat.Coprime (Nat.card V) (Nat.card R) :=
            hFrob.natCard_coprime.coprime_dvd_left
              (Subgroup.card_dvd_of_le hVK)
          have hcentUR : centralizerWithin U R = ⊥ := by
            apply le_bot_iff.mp
            intro x hx
            have hxKR : x ∈ centralizerWithin K R :=
              ⟨hUK hx.1, hx.2⟩
            rw [hcent] at hxKR
            exact hxKR
          have hcentq : centralizerWithin Uv Rv = ⊥ := by
            have hmapcent :=
              map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
                hchief.le hcopVR
            rw [hcentUR, Subgroup.map_bot] at hmapcent
            simpa [qV, Uv, Rv] using hmapcent.symm
          let aQ : (G ⧸ L) →* MulAut E :=
            QuotientGroup.lift L a hLa
          let rhoQ : Representation (ZMod p) (G ⧸ L) (Additive E) :=
            elementaryAbelianActionRepresentation E (G ⧸ L) p aQ
          have heAction (g : G) (x : E) :
              ((eE (a g x) : Uv) : G ⧸ V) =
                qV g * (eE x : G ⧸ V) * (qV g)⁻¹ := by
            obtain ⟨u, rfl⟩ :=
              QuotientGroup.mk'_surjective (V.subgroupOf U) x
            change qV (g * (u : G) * g⁻¹) =
              qV g * qV (u : G) * (qV g)⁻¹
            simp
          have hfix_zero (x : Additive E)
              (hxfix : ∀ r : Rq,
                (rhoQ (r : G ⧸ L)).toFun x = x) : x = 0 := by
            have hxcent : (eE x.toMul : G ⧸ V) ∈
                centralizerWithin Uv Rv := by
              refine ⟨(eE x.toMul).property, ?_⟩
              intro r hr
              rcases hr with ⟨r₀, hr₀, hrEq⟩
              let rQ : Rq := ⟨qL r₀, ⟨r₀, hr₀, rfl⟩⟩
              have hfixed := hxfix rQ
              have hfixed' : a r₀ x.toMul = x.toMul := by
                change Additive.ofMul (a r₀ x.toMul) = x at hfixed
                exact congrArg Additive.toMul hfixed
              have hconj : qV r₀ * (eE x.toMul : G ⧸ V) *
                    (qV r₀)⁻¹ = (eE x.toMul : G ⧸ V) := by
                rw [← heAction, hfixed']
              rw [← hrEq]
              calc
                qV r₀ * (eE x.toMul : G ⧸ V) =
                    (qV r₀ * (eE x.toMul : G ⧸ V) *
                      (qV r₀)⁻¹) * qV r₀ := by group
                _ = (eE x.toMul : G ⧸ V) * qV r₀ := by rw [hconj]
            have hxbot : (eE x.toMul : G ⧸ V) ∈
                (⊥ : Subgroup (G ⧸ V)) := by
              rw [← hcentq]
              exact hxcent
            have hxone : eE x.toMul = 1 := by
              apply Subtype.ext
              exact Subgroup.mem_bot.mp hxbot
            change x.toMul = 1
            apply eE.injective
            simpa using hxone
          letI : NeZero (Nat.card Kq : ZMod p) :=
            neZero_natCard_cast_of_isPGroup hKq' hpq
          have hKqrho :=
            hFrobq.kernel_le_representation_ker_of_invariants_eq_bot
              rhoQ (NeZero.ne _) (by
                apply le_antisymm
                · intro x hx
                  rw [Submodule.mem_bot]
                  apply hfix_zero x
                  intro r
                  exact (Representation.mem_invariants _ x).mp hx r
                · exact bot_le)
          have hKa : K ≤ a.ker := by
            intro k hk
            have hkq : qL k ∈ Kq := ⟨k, hk, rfl⟩
            have hrho := hKqrho hkq
            change rhoQ (qL k) = LinearMap.id at hrho
            change a k = 1
            apply MulEquiv.ext
            intro x
            have hx := LinearMap.congr_fun hrho (Additive.ofMul x)
            change Additive.ofMul (a k x) = Additive.ofMul x at hx
            exact congrArg Additive.toMul hx
          exact
            (subgroup_le_ker_chiefFactorConjugationHom_iff hchief).mp hKa

      let KF : Subgroup (fittingCore G) := K.subgroupOf (fittingCore G)
      letI : Group.IsNilpotent KF := by infer_instance
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hKF)

/-- `BGsection3.v: prime_Frobenius_sol_kernel_nil` (Theorem 3.7).

If `G = K ⋊ R` is solvable, `R` has prime order, and `R` has no
nonidentity fixed point on `K`, then the Frobenius kernel `K` is nilpotent. -/
theorem prime_Frobenius_sol_kernel_nil
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G}
    (hKR : K.IsComplement' R)
    (hKnormal : K.Normal)
    (hsol : IsSolvable G)
    (hRprime : (Nat.card R).Prime)
    (hcent : centralizerWithin K R = ⊥) :
    Group.IsNilpotent K :=
  primeFrobeniusSolKernelNilStatement_all (Nat.card G)
    G rfl K R hKR hKnormal hsol hRprime hcent

end

end Submission.OddOrder.BG.Section03
