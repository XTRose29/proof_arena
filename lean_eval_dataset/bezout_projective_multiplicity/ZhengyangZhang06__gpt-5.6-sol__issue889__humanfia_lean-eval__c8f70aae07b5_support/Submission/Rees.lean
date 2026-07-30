import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.LinearMap
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Spectrum.Prime.Topology

open LinearMap RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise
  IsSMulRegular

universe v u

namespace Submission.Helpers

variable {R : Type u} [CommRing R]

lemma smul_top_quotSMulTop_ne_top_of_smul_top_ne_top {M : Type*}
    [AddCommGroup M] [Module R M] {I : Ideal R} {r : R} (hr : r ∈ I)
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    I • (⊤ : Submodule R (QuotSMulTop r M)) ≠ ⊤ := by
  by_contra eq
  absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
  simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
    Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hr),
    ← Submodule.ideal_span_singleton_smul] using hI

namespace ModuleCat

lemma exists_isRegular_of_exists_subsingleton_ext [Small.{v} R]
    [IsNoetherianRing R] (I : Ideal R) (n : ℕ) (M : ModuleCat.{v} R)
    [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (N : ModuleCat.{v} R) [Module.Finite R N]
    (h_supp : Module.support R N = PrimeSpectrum.zeroLocus I)
    (h_ext : ∀ i < n, Subsingleton (Ext N M i)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs := by
  induction n generalizing M with
  | zero =>
      have : Nontrivial M := (Submodule.nontrivial_iff R).mp
        (nontrivial_of_lt _ _ smul_lt)
      use []
      simp [isRegular_iff]
  | succ n ih =>
      rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at h_supp
      have : Subsingleton (N ⟶ M) :=
        Ext.addEquiv₀.subsingleton_congr.mp (h_ext 0 n.zero_lt_succ)
      have : Subsingleton (N →ₗ[R] M) := ModuleCat.homAddEquiv.symm.subsingleton
      obtain ⟨x, mem_ann, hx⟩ := subsingleton_linearMap_iff.mp this
      obtain ⟨k, hk⟩ := le_of_le_of_eq Ideal.le_radical h_supp mem_ann
      have h_ext' : ∀ i < n,
          Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop (x ^ k) M)) i) := by
        intro i hi
        have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr
          (h_ext i (by omega))
        have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr
          (h_ext (i + 1) (by omega))
        exact AddCommGrpCat.subsingleton_of_isZero <|
          ShortComplex.Exact.isZero_of_both_zeros
            ((Ext.covariant_sequence_exact₃' N
              (hx.pow k).smulShortComplex_shortExact) i (i + 1) rfl)
            (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
      obtain ⟨rs, len, mem, reg⟩ := ih
        (ModuleCat.of R (QuotSMulTop (x ^ k) M))
        (smul_top_quotSMulTop_ne_top_of_smul_top_ne_top hk smul_lt.ne).lt_top
        h_ext'
      use x ^ k :: rs
      simpa [len, hk] using ⟨mem, hx.pow k, reg⟩

lemma subsingleton_ext_of_exists_isRegular [Small.{v} R]
    [IsNoetherianRing R] (I : Ideal R) (N : ModuleCat.{v} R)
    [Module.Finite R N]
    (Nsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I)
    (M : ModuleCat.{v} R) [Module.Finite R M]
    (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ I) (reg : IsRegular M rs) :
    ∀ i < rs.length, Subsingleton (Ext N M i) := by
  generalize len : rs.length = n
  induction n generalizing M rs with
  | zero => simp
  | succ n ih =>
      rintro i hi
      have le_rad := Nsupp
      rw [Module.support_eq_zeroLocus,
        PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at le_rad
      match rs with
      | [] => simp at len
      | a :: rs' =>
          obtain ⟨k, hk⟩ := le_rad (mem a List.mem_cons_self)
          simp only [isRegular_cons_iff] at reg
          simp only [List.mem_cons, forall_eq_or_imp] at mem
          simp only [List.length_cons, Nat.add_left_inj] at len
          match i with
          | 0 =>
              have : Subsingleton (N →ₗ[R] M) :=
                subsingleton_linearMap_iff.mpr ⟨a ^ k, hk, reg.1.pow k⟩
              exact (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton
          | i + 1 =>
              let g := AddCommGrpCat.ofHom
                ((Ext.mk₀ (M.smulShortComplex a).f).postcomp N
                  (add_zero (i + 1)))
              have mono_g : Mono g := by
                apply (Ext.covariant_sequence_exact₁' N
                  reg.1.smulShortComplex_shortExact i (i + 1) rfl).mono_g
                  ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr ?_).eq_zero_of_src _)
                apply ih (ModuleCat.of R (QuotSMulTop a M)) _ rs' mem.2 reg.2 len i
                  (by omega)
                exact (smul_top_quotSMulTop_ne_top_of_smul_top_ne_top
                  mem.1 smul_lt.ne).lt_top
              let gk := AddCommGrpCat.ofHom
                ((Ext.mk₀ (M.smulShortComplex (a ^ k)).f).postcomp N
                  (add_zero (i + 1)))
              have mono_gk : Mono gk := by
                simp only [_root_.ModuleCat.smulShortComplex_f_eq_smul_id,
                  g, gk] at mono_g ⊢
                exact (Ext.postcomp_smul_id_mono_iff (a ^ k) (i + 1)).mpr <|
                  ((Ext.postcomp_smul_id_mono_iff a (i + 1)).mp mono_g).pow k
              have zero_gk : gk = 0 :=
                Ext.postcomp_smul_id_eq_zero_of_mem_annihilator hk (i + 1)
              exact AddCommGrpCat.subsingleton_of_isZero
                (IsZero.of_mono_eq_zero _ zero_gk)

lemma exists_isRegular_of_zeroLocus_eq [Small.{v} R]
    [IsNoetherianRing R] (I J : Ideal R) (n : ℕ) (M : ModuleCat.{v} R)
    [Module.Finite R M] (Ismul_lt : I • (⊤ : Submodule R M) < ⊤)
    (Jsmul_lt : J • (⊤ : Submodule R M) < ⊤)
    (hzero : PrimeSpectrum.zeroLocus (I : Set R) =
      PrimeSpectrum.zeroLocus (J : Set R))
    (rs : List R) (hlen : rs.length = n) (hmem : ∀ r ∈ rs, r ∈ I)
    (hreg : IsRegular M rs) :
    ∃ js : List R, js.length = n ∧ (∀ r ∈ js, r ∈ J) ∧ IsRegular M js := by
  let N := ModuleCat.of R (Shrink.{v} (R ⧸ J))
  have hntr : Nontrivial (R ⧸ J) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    intro htop
    simp [htop] at Jsmul_lt
  letI : Nontrivial N := (Shrink.linearEquiv R (R ⧸ J)).toEquiv.nontrivial
  have hsupp : Module.support R N = PrimeSpectrum.zeroLocus J := by
    rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus,
      annihilator_quotient]
  have hext : ∀ i < n, Subsingleton (Ext N M i) := by
    intro i hi
    have Nsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
      rw [hsupp, ← hzero]
    exact subsingleton_ext_of_exists_isRegular I N Nsupp M Ismul_lt
      rs hmem hreg i (by simpa [hlen] using hi)
  exact exists_isRegular_of_exists_subsingleton_ext J n M Jsmul_lt N hsupp hext

lemma exists_isRegular_tail_of_mem [Small.{v} R] [IsNoetherianRing R]
    (I : Ideal R) (n : ℕ) (M : ModuleCat.{v} R) [Module.Finite R M]
    (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (hlen : rs.length = n + 1)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsRegular M rs)
    {x : R} (hxI : x ∈ I) (hxreg : IsSMulRegular M x) :
    ∃ tail : List R, tail.length = n ∧ (∀ r ∈ tail, r ∈ I) ∧
      IsRegular (QuotSMulTop x M) tail := by
  let N := ModuleCat.of R (Shrink.{v} (R ⧸ I))
  have hntr : Nontrivial (R ⧸ I) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    intro htop
    simp [htop] at smul_lt
  letI : Nontrivial N := (Shrink.linearEquiv R (R ⧸ I)).toEquiv.nontrivial
  have hsupp : Module.support R N = PrimeSpectrum.zeroLocus I := by
    rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus,
      annihilator_quotient]
  have hext : ∀ i < n + 1, Subsingleton (Ext N M i) := by
    intro i hi
    exact subsingleton_ext_of_exists_isRegular I N hsupp.le M smul_lt
      rs hmem hreg i (by simpa [hlen] using hi)
  have hext' : ∀ i < n,
      Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) := by
    intro i hi
    have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr
      (hext i (by omega))
    have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr
      (hext (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <|
      ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' N
          hxreg.smulShortComplex_shortExact) i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
  exact exists_isRegular_of_exists_subsingleton_ext I n
    (ModuleCat.of R (QuotSMulTop x M))
    (smul_top_quotSMulTop_ne_top_of_smul_top_ne_top hxI smul_lt.ne).lt_top
    N hsupp hext'

end ModuleCat

end Submission.Helpers
