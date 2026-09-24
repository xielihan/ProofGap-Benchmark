import Mathlib.Tactic.Measurability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4216

noncomputable section

open MeasureTheory Set
open scoped ENNReal Interval

private abbrev BaseVec (n : ℕ) := Fin n → ℝ

private def baseSimplex (n : ℕ) : Set (BaseVec n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

private def baseIntegrand {n : ℕ} (p x : BaseVec n) : ℝ :=
  ∏ i, Real.rpow (x i) (p i - 1)

private def baseDirichletIntegral {n : ℕ} (p : BaseVec n) : ℝ :=
  ∫ x in baseSimplex n, baseIntegrand p x ∂MeasureTheory.volume

private def simplexAt (n : ℕ) (t : ℝ) : Set (BaseVec n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ t}

private def dirichletLIntegral {n : ℕ} (p : BaseVec n) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in simplexAt n t, ENNReal.ofReal (baseIntegrand p x)

private theorem integrand_nonneg {n : ℕ} (p : BaseVec n) (x : BaseVec n)
    (hx : ∀ i, 0 ≤ x i) :
    0 ≤ baseIntegrand p x := by
  exact Finset.prod_nonneg fun i _ =>
    Real.rpow_nonneg (hx i) (p i - 1)

private theorem measurable_integrand {n : ℕ} (p : BaseVec n) :
    Measurable (baseIntegrand p) := by
  unfold baseIntegrand
  measurability

private theorem measurableSet_simplexAt (n : ℕ) (t : ℝ) :
    MeasurableSet (simplexAt n t) := by
  unfold simplexAt
  measurability

private theorem simplexAt_one (n : ℕ) :
    simplexAt n 1 = baseSimplex n := rfl

private theorem simplexAt_zero (n : ℕ) :
    simplexAt n 0 = ({0} : Set (BaseVec n)) := by
  ext x
  simp only [simplexAt, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hsum⟩
    funext i
    apply le_antisymm
    · exact
        (Finset.single_le_sum
          (fun j _ => hx j) (Finset.mem_univ i)).trans hsum
    · exact hx i
  · rintro rfl
    simp

private theorem dirichletLIntegral_zero {n : ℕ}
    (hn : 0 < n) (p : BaseVec n) :
    dirichletLIntegral p 0 = 0 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [dirichletLIntegral, simplexAt_zero n]
  simp

private def splitVec (n : ℕ) (x : BaseVec (n + 1)) :
    ℝ × BaseVec n :=
  (x 0, fun i => x i.succ)

private def splitRegion (n : ℕ) (t : ℝ) :
    Set (ℝ × BaseVec n) :=
  {q |
    q.1 ∈ Set.Icc 0 t ∧
    q.2 ∈ simplexAt n (t - q.1)}

private theorem splitVec_measurePreserving (n : ℕ) :
    MeasurePreserving (splitVec n)
      (volume : Measure (BaseVec (n + 1)))
      ((volume : Measure ℝ).prod
        (volume : Measure (BaseVec n))) := by
  simpa [splitVec] using
    (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1)))

private theorem splitVec_measurableEmbedding (n : ℕ) :
    MeasurableEmbedding (splitVec n) := by
  change MeasurableEmbedding
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1)))
  exact
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ)
      (0 : Fin (n + 1))).measurableEmbedding

private theorem splitRegion_preimage (n : ℕ) (t : ℝ) :
    splitVec n ⁻¹' splitRegion n t =
      simplexAt (n + 1) t := by
  ext x
  simp only [Set.mem_preimage, splitRegion, Set.mem_setOf_eq,
    Set.mem_Icc, simplexAt, splitVec, Fin.sum_univ_succ]
  constructor
  · rintro ⟨⟨hx0, hx0t⟩, htail, hsum⟩
    constructor
    · intro i
      exact Fin.cases hx0 (fun j => htail j) i
    · linarith
  · rintro ⟨hx, hsum⟩
    have htail : ∀ i : Fin n, 0 ≤ x i.succ :=
      fun i => hx i.succ
    have htailsum : 0 ≤ ∑ i : Fin n, x i.succ :=
      Finset.sum_nonneg fun i _ => htail i
    exact
      ⟨⟨hx 0, by linarith⟩, htail, by linarith⟩

private theorem measurableSet_splitRegion (n : ℕ) (t : ℝ) :
    MeasurableSet (splitRegion n t) := by
  unfold splitRegion simplexAt
  measurability

private theorem integrand_split {n : ℕ}
    (p : BaseVec (n + 1)) (x : BaseVec (n + 1)) :
    baseIntegrand p x =
      Real.rpow (x 0) (p 0 - 1) *
        baseIntegrand (fun i : Fin n => p i.succ)
          (fun i : Fin n => x i.succ) := by
  simp [baseIntegrand, Fin.prod_univ_succ]

private theorem sum_split {n : ℕ} (p : BaseVec (n + 1)) :
    (∑ i, p i) =
      p 0 + ∑ i : Fin n, p i.succ := by
  rw [Fin.sum_univ_succ]

private theorem prod_gamma_split {n : ℕ} (p : BaseVec (n + 1)) :
    (∏ i, Real.Gamma (p i)) =
      Real.Gamma (p 0) *
        ∏ i : Fin n, Real.Gamma (p i.succ) := by
  rw [Fin.prod_univ_succ]

private def splitDensity {n : ℕ} (p : BaseVec (n + 1))
    (q : ℝ × BaseVec n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow q.1 (p 0 - 1)) *
    ENNReal.ofReal
      (baseIntegrand (fun i : Fin n => p i.succ) q.2)

private theorem measurable_splitDensity {n : ℕ}
    (p : BaseVec (n + 1)) :
    Measurable (splitDensity p) := by
  unfold splitDensity
  have hrpow :
      Measurable
        (fun z : ℝ => Real.rpow z (p 0 - 1)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const
      (fun z hz => Or.inl (by simpa using hz))
  exact
    ((hrpow.comp measurable_fst).ennreal_ofReal).mul
      (((measurable_integrand
        (fun i : Fin n => p i.succ)).comp
          measurable_snd).ennreal_ofReal)

private theorem dirichletLIntegral_succ
    (n : ℕ) (p : BaseVec (n + 1)) (t : ℝ) :
    dirichletLIntegral p t =
      ∫⁻ z in Set.Icc (0 : ℝ) t,
        ENNReal.ofReal (Real.rpow z (p 0 - 1)) *
          dirichletLIntegral
            (fun i : Fin n => p i.succ) (t - z) := by
  have hleft :
      dirichletLIntegral p t =
        ∫⁻ x in simplexAt (n + 1) t,
          splitDensity p (splitVec n x) := by
    unfold dirichletLIntegral
    apply setLIntegral_congr_fun
      (measurableSet_simplexAt (n + 1) t)
    intro x hx
    change
      ENNReal.ofReal (baseIntegrand p x) =
        ENNReal.ofReal (Real.rpow (x 0) (p 0 - 1)) *
          ENNReal.ofReal
            (baseIntegrand (fun i : Fin n => p i.succ)
              (fun i : Fin n => x i.succ))
    rw [integrand_split]
    exact ENNReal.ofReal_mul
      (Real.rpow_nonneg (hx.1 0) (p 0 - 1))
  rw [hleft]
  have htransport :=
    (splitVec_measurePreserving n).setLIntegral_comp_preimage_emb
      (splitVec_measurableEmbedding n)
      (splitDensity p) (splitRegion n t)
  rw [splitRegion_preimage] at htransport
  rw [htransport]
  rw [← lintegral_indicator (measurableSet_splitRegion n t)]
  rw [lintegral_prod _ <|
    ((measurable_splitDensity p).indicator
      (measurableSet_splitRegion n t)).aemeasurable]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ Set.Icc (0 : ℝ) t
  · rw [Set.indicator_of_mem hz]
    calc
      (∫⁻ y : BaseVec n,
          (splitRegion n t).indicator
            (splitDensity p) (z, y)) =
          ∫⁻ y in simplexAt n (t - z),
            splitDensity p (z, y) := by
        rw [← lintegral_indicator
          (measurableSet_simplexAt n (t - z))]
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ simplexAt n (t - z)
        · rw [Set.indicator_of_mem hy]
          rw [Set.indicator_of_mem]
          exact ⟨hz, hy⟩
        · rw [Set.indicator_of_notMem hy]
          rw [Set.indicator_of_notMem]
          exact fun h => hy h.2
      _ =
          ENNReal.ofReal (Real.rpow z (p 0 - 1)) *
            dirichletLIntegral
              (fun i : Fin n => p i.succ) (t - z) := by
        unfold splitDensity dirichletLIntegral
        change
          (∫⁻ y in simplexAt n (t - z),
            ENNReal.ofReal (Real.rpow z (p 0 - 1)) *
              ENNReal.ofReal
                (baseIntegrand
                  (fun i : Fin n => p i.succ) y)) =
            ENNReal.ofReal (Real.rpow z (p 0 - 1)) *
              ∫⁻ y in simplexAt n (t - z),
                ENNReal.ofReal
                  (baseIntegrand
                    (fun i : Fin n => p i.succ) y)
        rw [lintegral_const_mul]
        exact
          (measurable_integrand
            (fun i : Fin n => p i.succ)).ennreal_ofReal
  · rw [Set.indicator_of_notMem hz]
    calc
      (∫⁻ y : BaseVec n,
          (splitRegion n t).indicator
            (splitDensity p) (z, y)) =
          ∫⁻ _y : BaseVec n, (0 : ℝ≥0∞) := by
        apply lintegral_congr
        intro y
        rw [Set.indicator_of_notMem]
        exact fun h => hz h.1
      _ = 0 := by simp

private theorem betaScaled_integrable
    (s u A : ℝ) (hs : 0 < s) (hu : 0 < u) (hA : 0 < A) :
    IntervalIntegrable
      (fun x : ℝ =>
        Real.rpow x (s - 1) *
          Real.rpow (A - x) (u - 1))
      volume 0 A := by
  have hmid : 0 < A / 2 := by positivity
  have hsInt :
      IntervalIntegrable
        (fun x : ℝ => Real.rpow x (s - 1))
        volume 0 (A / 2) :=
    intervalIntegral.intervalIntegrable_rpow'
      (by linarith)
  have huContLeft :
      ContinuousOn
        (fun x : ℝ => Real.rpow (A - x) (u - 1))
        [[0, A / 2]] := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [Set.uIcc_of_le hmid.le] at hx
    have hhalf_lt : A / 2 < A := by linarith
    have hxlt : x < A := hx.2.trans_lt hhalf_lt
    have hbase : A - x ≠ 0 :=
      ne_of_gt (sub_pos.mpr hxlt)
    exact
      (Real.continuousAt_rpow_const
        (A - x) (u - 1) (Or.inl hbase)).comp
          (continuous_const.sub continuous_id).continuousAt
  have hleft :
      IntervalIntegrable
        (fun x : ℝ =>
          Real.rpow x (s - 1) *
            Real.rpow (A - x) (u - 1))
        volume 0 (A / 2) :=
    hsInt.mul_continuousOn huContLeft
  have huBase :
      IntervalIntegrable
        (fun y : ℝ => Real.rpow y (u - 1))
        volume 0 (A / 2) :=
    intervalIntegral.intervalIntegrable_rpow'
      (by linarith)
  have huRight :
      IntervalIntegrable
        (fun x : ℝ => Real.rpow (A - x) (u - 1))
        volume (A / 2) A := by
    have h := huBase.comp_sub_left A
    convert h.symm using 1 <;> ring
  have hsContRight :
      ContinuousOn
        (fun x : ℝ => Real.rpow x (s - 1))
        [[A / 2, A]] := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [Set.uIcc_of_le (by linarith : A / 2 ≤ A)] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hmid hx.1
    exact
      (Real.continuousAt_rpow_const x (s - 1)
        (Or.inl hxpos.ne'))
  have hright :
      IntervalIntegrable
        (fun x : ℝ =>
          Real.rpow x (s - 1) *
            Real.rpow (A - x) (u - 1))
        volume (A / 2) A :=
    huRight.continuousOn_mul hsContRight
  exact hleft.trans hright

private theorem betaScaled_value
    (s u A : ℝ) (hs : 0 < s) (hu : 0 < u) (hA : 0 < A) :
    (∫ x in (0 : ℝ)..A,
      Real.rpow x (s - 1) *
        Real.rpow (A - x) (u - 1)) =
      Real.rpow A (s + u - 1) *
        (Real.Gamma s * Real.Gamma u /
          Real.Gamma (s + u)) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc
    (∫ x in (0 : ℝ)..A,
        ((Real.rpow x (s - 1) *
          Real.rpow (A - x) (u - 1) : ℝ) : ℂ)) =
        ∫ x in (0 : ℝ)..A,
          (x : ℂ) ^ ((s : ℂ) - 1) *
            ((A : ℂ) - x) ^ ((u : ℂ) - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hA.le] at hx
      have hx0 : 0 ≤ x := hx.1
      have hAx : 0 ≤ A - x := sub_nonneg.mpr hx.2
      change
        ((Real.rpow x (s - 1) *
          Real.rpow (A - x) (u - 1) : ℝ) : ℂ) =
          (x : ℂ) ^ ((s : ℂ) - 1) *
            ((A : ℂ) - x) ^ ((u : ℂ) - 1)
      rw [Complex.ofReal_mul,
        Real.rpow_eq_pow, Real.rpow_eq_pow,
        Complex.ofReal_cpow hx0,
        Complex.ofReal_cpow hAx]
      push_cast
      ring
    _ = (A : ℂ) ^
          ((s : ℂ) + (u : ℂ) - 1) *
        Complex.betaIntegral (s : ℂ) (u : ℂ) :=
      Complex.betaIntegral_scaled (s : ℂ) (u : ℂ) hA
    _ = (A : ℂ) ^
          ((s : ℂ) + (u : ℂ) - 1) *
        (Complex.Gamma (s : ℂ) *
          Complex.Gamma (u : ℂ) /
            Complex.Gamma ((s : ℂ) + (u : ℂ))) := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div
        (s : ℂ) (u : ℂ) (by simpa) (by simpa)]
    _ = ((Real.rpow A (s + u - 1) *
        (Real.Gamma s * Real.Gamma u /
          Real.Gamma (s + u)) : ℝ) : ℂ) := by
      have hexp :
          (s : ℂ) + (u : ℂ) - 1 =
            ((s + u - 1 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hexp, ← Complex.ofReal_cpow hA.le]
      rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal,
        ← Complex.ofReal_add, Complex.Gamma_ofReal]
      push_cast
      rfl

private theorem betaScaled_lintegral
    (s u A : ℝ) (hs : 0 < s) (hu : 0 < u) (hA : 0 < A) :
    (∫⁻ x in Set.Icc (0 : ℝ) A,
      ENNReal.ofReal
        (Real.rpow x (s - 1) *
          Real.rpow (A - x) (u - 1))) =
      ENNReal.ofReal
        (Real.rpow A (s + u - 1) *
          (Real.Gamma s * Real.Gamma u /
            Real.Gamma (s + u))) := by
  let f : ℝ → ℝ := fun x =>
    Real.rpow x (s - 1) *
      Real.rpow (A - x) (u - 1)
  have hfInterval : IntervalIntegrable f volume 0 A := by
    exact betaScaled_integrable s u A hs hu hA
  have hf :
      IntegrableOn f (Set.Icc (0 : ℝ) A) volume := by
    exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        hA.le).mp hfInterval
  have hf_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) A)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact mul_nonneg
      (Real.rpow_nonneg hx.1 (s - 1))
      (Real.rpow_nonneg (sub_nonneg.mpr hx.2) (u - 1))
  rw [← ofReal_integral_eq_lintegral_ofReal hf hf_nonneg]
  rw [← setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [← intervalIntegral.integral_of_le hA.le]
  exact congrArg ENNReal.ofReal
    (betaScaled_value s u A hs hu hA)

private def dirichletConstant {n : ℕ} (p : BaseVec n) : ℝ :=
  (∏ i, Real.Gamma (p i)) /
    Real.Gamma ((∑ i, p i) + 1)

private theorem dirichletConstant_pos {n : ℕ}
    (p : BaseVec n) (hp : ∀ i, 0 < p i) :
    0 < dirichletConstant p := by
  unfold dirichletConstant
  apply div_pos
  · exact Finset.prod_pos fun i _ =>
      Real.Gamma_pos_of_pos (hp i)
  · apply Real.Gamma_pos_of_pos
    have hsum : 0 ≤ ∑ i, p i :=
      Finset.sum_nonneg fun i _ => (hp i).le
    linarith

private theorem dirichletLIntegral_eq
    {n : ℕ} (p : BaseVec n) (hp : ∀ i, 0 < p i)
    (t : ℝ) (ht : 0 ≤ t) :
    dirichletLIntegral p t =
      ENNReal.ofReal
        (dirichletConstant p *
          Real.rpow t (∑ i, p i)) := by
  induction n generalizing t with
  | zero =>
      letI : ∀ i : Fin 0, IsProbabilityMeasure
          (volume : Measure ℝ) := fun i => Fin.elim0 i
      letI : IsProbabilityMeasure
          (volume : Measure (BaseVec 0)) := inferInstance
      simp [dirichletLIntegral, simplexAt, baseIntegrand,
        dirichletConstant, ht, Real.Gamma_one]
  | succ n ih =>
      by_cases hzero : t = 0
      · subst t
        rw [dirichletLIntegral_zero (Nat.succ_pos n)]
        have hsum_pos : 0 < ∑ i, p i := by
          rw [sum_split]
          exact add_pos_of_pos_of_nonneg (hp 0)
            (Finset.sum_nonneg
              fun i : Fin n => fun _ => (hp i.succ).le)
        have hrpow_zero :
            Real.rpow 0 (∑ i, p i) = 0 :=
          Real.zero_rpow hsum_pos.ne'
        rw [hrpow_zero]
        simp
      · have htpos : 0 < t :=
          lt_of_le_of_ne ht (Ne.symm hzero)
        have hpTail :
            ∀ i : Fin n, 0 < p i.succ :=
          fun i => hp i.succ
        have htailSum_nonneg :
            0 ≤ ∑ i : Fin n, p i.succ :=
          Finset.sum_nonneg fun i _ => (hp i.succ).le
        have hu :
            0 < (∑ i : Fin n, p i.succ) + 1 := by
          linarith
        have hconstant :
            0 ≤ dirichletConstant
              (fun i : Fin n => p i.succ) :=
          (dirichletConstant_pos
            (fun i : Fin n => p i.succ) hpTail).le
        have hbeta :
            (∫⁻ z in Set.Icc (0 : ℝ) t,
              ENNReal.ofReal
                (Real.rpow z (p 0 - 1) *
                  Real.rpow (t - z)
                    (∑ i : Fin n, p i.succ))) =
              ENNReal.ofReal
                (Real.rpow t
                    (p 0 + ∑ i : Fin n, p i.succ) *
                  (Real.Gamma (p 0) *
                    Real.Gamma
                      ((∑ i : Fin n, p i.succ) + 1) /
                    Real.Gamma
                      (p 0 +
                        (∑ i : Fin n, p i.succ) + 1))) := by
          convert betaScaled_lintegral
            (p 0) ((∑ i : Fin n, p i.succ) + 1)
              t (hp 0) hu htpos using 1 <;> ring
        have hgammaTail :
            Real.Gamma
                ((∑ i : Fin n, p i.succ) + 1) ≠ 0 :=
          (Real.Gamma_pos_of_pos hu).ne'
        have halgebra :
            dirichletConstant
                (fun i : Fin n => p i.succ) *
              (Real.rpow t
                  (p 0 + ∑ i : Fin n, p i.succ) *
                (Real.Gamma (p 0) *
                  Real.Gamma
                    ((∑ i : Fin n, p i.succ) + 1) /
                  Real.Gamma
                    (p 0 +
                      (∑ i : Fin n, p i.succ) + 1))) =
              dirichletConstant p *
                Real.rpow t (∑ i, p i) := by
          unfold dirichletConstant
          rw [prod_gamma_split, sum_split]
          field_simp [hgammaTail]
        rw [dirichletLIntegral_succ]
        calc
          (∫⁻ z in Set.Icc (0 : ℝ) t,
              ENNReal.ofReal (Real.rpow z (p 0 - 1)) *
                dirichletLIntegral
                  (fun i : Fin n => p i.succ) (t - z)) =
              ∫⁻ z in Set.Icc (0 : ℝ) t,
                ENNReal.ofReal
                    (Real.rpow z (p 0 - 1)) *
                  ENNReal.ofReal
                    (dirichletConstant
                        (fun i : Fin n => p i.succ) *
                      Real.rpow (t - z)
                        (∑ i : Fin n, p i.succ)) := by
            apply setLIntegral_congr_fun measurableSet_Icc
            intro z hz
            change
              ENNReal.ofReal
                    (Real.rpow z (p 0 - 1)) *
                  dirichletLIntegral
                    (fun i : Fin n => p i.succ) (t - z) =
                ENNReal.ofReal
                    (Real.rpow z (p 0 - 1)) *
                  ENNReal.ofReal
                    (dirichletConstant
                        (fun i : Fin n => p i.succ) *
                      Real.rpow (t - z)
                        (∑ i : Fin n, p i.succ))
            rw [ih
              (fun i : Fin n => p i.succ) hpTail
              (t - z) (sub_nonneg.mpr hz.2)]
          _ =
              ∫⁻ z in Set.Icc (0 : ℝ) t,
                ENNReal.ofReal
                  (dirichletConstant
                      (fun i : Fin n => p i.succ) *
                    (Real.rpow z (p 0 - 1) *
                      Real.rpow (t - z)
                        (∑ i : Fin n, p i.succ))) := by
            apply setLIntegral_congr_fun measurableSet_Icc
            intro z hz
            have hzpow :
                0 ≤ Real.rpow z (p 0 - 1) :=
              Real.rpow_nonneg hz.1 (p 0 - 1)
            calc
              ENNReal.ofReal
                    (Real.rpow z (p 0 - 1)) *
                  ENNReal.ofReal
                    (dirichletConstant
                        (fun i : Fin n => p i.succ) *
                      Real.rpow (t - z)
                        (∑ i : Fin n, p i.succ)) =
                  ENNReal.ofReal
                    (Real.rpow z (p 0 - 1) *
                      (dirichletConstant
                          (fun i : Fin n => p i.succ) *
                        Real.rpow (t - z)
                          (∑ i : Fin n, p i.succ))) :=
                (ENNReal.ofReal_mul hzpow).symm
              _ = ENNReal.ofReal
                    (dirichletConstant
                        (fun i : Fin n => p i.succ) *
                      (Real.rpow z (p 0 - 1) *
                        Real.rpow (t - z)
                          (∑ i : Fin n, p i.succ))) := by
                congr 1
                ring
          _ =
              ENNReal.ofReal
                  (dirichletConstant
                    (fun i : Fin n => p i.succ)) *
                (∫⁻ z in Set.Icc (0 : ℝ) t,
                  ENNReal.ofReal
                    (Real.rpow z (p 0 - 1) *
                      Real.rpow (t - z)
                        (∑ i : Fin n, p i.succ))) := by
            calc
              (∫⁻ z in Set.Icc (0 : ℝ) t,
                  ENNReal.ofReal
                    (dirichletConstant
                        (fun i : Fin n => p i.succ) *
                      (Real.rpow z (p 0 - 1) *
                        Real.rpow (t - z)
                          (∑ i : Fin n, p i.succ)))) =
                  ∫⁻ z in Set.Icc (0 : ℝ) t,
                    ENNReal.ofReal
                        (dirichletConstant
                          (fun i : Fin n => p i.succ)) *
                      ENNReal.ofReal
                        (Real.rpow z (p 0 - 1) *
                          Real.rpow (t - z)
                            (∑ i : Fin n, p i.succ)) := by
                apply setLIntegral_congr_fun measurableSet_Icc
                intro z _
                exact ENNReal.ofReal_mul hconstant
              _ = _ := by
                rw [lintegral_const_mul'
                  _ _ ENNReal.ofReal_ne_top]
          _ =
              ENNReal.ofReal
                  (dirichletConstant
                    (fun i : Fin n => p i.succ)) *
                ENNReal.ofReal
                  (Real.rpow t
                      (p 0 + ∑ i : Fin n, p i.succ) *
                    (Real.Gamma (p 0) *
                      Real.Gamma
                        ((∑ i : Fin n, p i.succ) + 1) /
                      Real.Gamma
                        (p 0 +
                          (∑ i : Fin n, p i.succ) + 1))) := by
            rw [hbeta]
          _ =
              ENNReal.ofReal
                (dirichletConstant p *
                  Real.rpow t (∑ i, p i)) := by
            rw [← ENNReal.ofReal_mul hconstant]
            exact congrArg ENNReal.ofReal halgebra

/-! Exercise 4216. -/

private theorem baseDirichletFormula
    {n : ℕ} (hn : 0 < n) (p : BaseVec n) (hp : ∀ i, 0 < p i) :
    baseDirichletIntegral p =
      (∏ i, Real.Gamma (p i)) / Real.Gamma ((∑ i, p i) + 1) := by
  have hsimpMeas : MeasurableSet (baseSimplex n) := by
    rw [← simplexAt_one]
    exact measurableSet_simplexAt n 1
  have hnonneg :
      0 ≤ᵐ[(volume : Measure (BaseVec n)).restrict
        (baseSimplex n)] baseIntegrand p := by
    filter_upwards [ae_restrict_mem hsimpMeas] with x hx
    exact integrand_nonneg p x hx.1
  have hmeas :
      AEStronglyMeasurable (baseIntegrand p)
        ((volume : Measure (BaseVec n)).restrict
          (baseSimplex n)) :=
    (measurable_integrand p).aestronglyMeasurable.restrict
  have hL :
      (∫⁻ x in baseSimplex n,
        ENNReal.ofReal (baseIntegrand p x)
          ∂(volume : Measure (BaseVec n))) =
        ENNReal.ofReal
          (dirichletConstant p *
            Real.rpow 1 (∑ i, p i)) := by
    simpa [dirichletLIntegral, simplexAt_one] using
      (dirichletLIntegral_eq p hp 1 zero_le_one)
  unfold baseDirichletIntegral
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]
  rw [hL]
  have hvalue_nonneg :
      0 ≤ dirichletConstant p *
        Real.rpow 1 (∑ i, p i) := by
    exact mul_nonneg
      (dirichletConstant_pos p hp).le
      (Real.rpow_nonneg zero_le_one (∑ i, p i))
  rw [ENNReal.toReal_ofReal hvalue_nonneg]
  simp [dirichletConstant]

def simplex (n : ℕ) (b : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ b}

def dirichletIntegrand
    {n : ℕ} (p x : Fin n → ℝ) : ℝ :=
  ∏ i, Real.rpow (x i) (p i - 1)

def dirichletIntegral
    (n : ℕ) (p : Fin n → ℝ) : ℝ :=
  ∫ x in simplex n 1, dirichletIntegrand p x

def scaledDirichletIntegral
    (n : ℕ) (p : Fin n → ℝ) (b : ℝ) : ℝ :=
  ∫ x in simplex n b, dirichletIntegrand p x

def parameterSum {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ i, p i

def gammaProduct {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∏ i, Real.Gamma (p i)

def dirichletValue {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  gammaProduct p / Real.Gamma (parameterSum p + 1)

def betaValue (p q : ℝ) : ℝ :=
  Real.Gamma p * Real.Gamma q / Real.Gamma (p + q)

theorem gap1 (p : ℝ) (hp : 0 < p) :
    (∫ x in (0 : ℝ)..1, Real.rpow x (p - 1)) = 1 / p := by
  simp only [Real.rpow_eq_pow]
  have h :=
    integral_rpow (a := (0 : ℝ)) (b := 1) (r := p - 1)
      (Or.inl (by linarith : (-1 : ℝ) < p - 1))
  rw [h, Real.one_rpow,
    Real.zero_rpow (by linarith : p - 1 + 1 ≠ 0)]
  ring

theorem gap2 (p : ℝ) (hp : 0 < p) :
    1 / p = Real.Gamma p / Real.Gamma (p + 1) := by
  rw [Real.Gamma_add_one hp.ne']
  field_simp [(Real.Gamma_pos_of_pos hp).ne']

theorem gap3 (p : ℝ) (hp : 0 < p) :
    (∫ x in (0 : ℝ)..1, Real.rpow x (p - 1)) =
      Real.Gamma p / Real.Gamma (p + 1) := by
  rw [gap1 p hp, gap2 p hp]

private theorem scaledDirichlet_formula
    {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (b : ℝ) (hb : 0 ≤ b) :
    scaledDirichletIntegral n p b =
      dirichletValue p * Real.rpow b (parameterSum p) := by
  change
    (∫ x in simplexAt n b, baseIntegrand p x) =
      dirichletConstant p * Real.rpow b (∑ i, p i)
  have hsimpMeas : MeasurableSet (simplexAt n b) :=
    measurableSet_simplexAt n b
  have hnonneg :
      0 ≤ᵐ[(volume : Measure (BaseVec n)).restrict
        (simplexAt n b)] baseIntegrand p := by
    filter_upwards [ae_restrict_mem hsimpMeas] with x hx
    exact integrand_nonneg p x hx.1
  have hmeas :
      AEStronglyMeasurable (baseIntegrand p)
        ((volume : Measure (BaseVec n)).restrict
          (simplexAt n b)) :=
    (measurable_integrand p).aestronglyMeasurable.restrict
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]
  rw [show
    (∫⁻ x in simplexAt n b,
      ENNReal.ofReal (baseIntegrand p x)
        ∂(volume : Measure (BaseVec n))) =
      ENNReal.ofReal
        (dirichletConstant p *
          Real.rpow b (∑ i, p i)) by
      simpa [dirichletLIntegral] using
        (dirichletLIntegral_eq p hp b hb)]
  have hvalue_nonneg :
      0 ≤ dirichletConstant p *
        Real.rpow b (∑ i, p i) := by
    exact mul_nonneg
      (dirichletConstant_pos p hp).le
      (Real.rpow_nonneg hb (∑ i, p i))
  rw [ENNReal.toReal_ofReal hvalue_nonneg]

private theorem dirichletValue_factor
    (n : ℕ) (p : Fin (n + 1) → ℝ) (hp : ∀ i, 0 < p i) :
    dirichletValue (fun i => p i.castSucc) *
        betaValue (p (Fin.last n))
          (parameterSum (fun i => p i.castSucc) + 1) =
      dirichletValue p := by
  have htailSum :
      0 < (∑ i : Fin n, p i.castSucc) + 1 := by
    have : 0 ≤ ∑ i : Fin n, p i.castSucc :=
      Finset.sum_nonneg fun i _ => (hp i.castSucc).le
    linarith
  have htotalSum :
      0 < (∑ i : Fin (n + 1), p i) + 1 := by
    have : 0 ≤ ∑ i : Fin (n + 1), p i :=
      Finset.sum_nonneg fun i _ => (hp i).le
    linarith
  have hbetaSum :
      0 <
        p (Fin.last n) +
          ((∑ i : Fin n, p i.castSucc) + 1) := by
    exact add_pos (hp (Fin.last n)) htailSum
  have hgTail :
      Real.Gamma ((∑ i : Fin n, p i.castSucc) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos htailSum).ne'
  have hgTotal :
      Real.Gamma ((∑ i : Fin (n + 1), p i) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos htotalSum).ne'
  have hgBeta :
      Real.Gamma
        (p (Fin.last n) +
          ((∑ i : Fin n, p i.castSucc) + 1)) ≠ 0 :=
    (Real.Gamma_pos_of_pos hbetaSum).ne'
  have hgNormalized :
      Real.Gamma
        (1 + p (Fin.last n) +
          ∑ i : Fin n, p i.castSucc) ≠ 0 := by
    apply (Real.Gamma_pos_of_pos _).ne'
    have htail :
        0 ≤ ∑ i : Fin n, p i.castSucc :=
      Finset.sum_nonneg fun i _ => (hp i.castSucc).le
    linarith [hp (Fin.last n)]
  have hgammaReassoc :
      Real.Gamma
          (p (Fin.last n) +
            ((∑ i : Fin n, p i.castSucc) + 1)) =
        Real.Gamma
          ((∑ i : Fin n, p i.castSucc) +
            p (Fin.last n) + 1) := by
    congr 1
    ring
  have hgCombined :
      Real.Gamma
          ((∑ i : Fin n, p i.castSucc) +
            p (Fin.last n) + 1) ≠ 0 := by
    apply (Real.Gamma_pos_of_pos _).ne'
    have htail :
        0 ≤ ∑ i : Fin n, p i.castSucc :=
      Finset.sum_nonneg fun i _ => (hp i.castSucc).le
    linarith [hp (Fin.last n)]
  unfold dirichletValue betaValue gammaProduct parameterSum
  rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc,
    hgammaReassoc]
  field_simp [hgTail, hgTotal, hgBeta, hgNormalized, hgCombined]
  <;> ring

private theorem beta_identity
    (n : ℕ) (p : Fin (n + 1) → ℝ) (hp : ∀ i, 0 < p i) :
    (∫ t in (0 : ℝ)..1,
        Real.rpow t (p (Fin.last n) - 1) *
          Real.rpow (1 - t)
            (parameterSum (fun i => p i.castSucc))) =
      betaValue (p (Fin.last n))
        (parameterSum (fun i => p i.castSucc) + 1) := by
  have htailSum :
      0 < parameterSum (fun i : Fin n => p i.castSucc) + 1 := by
    unfold parameterSum
    have : 0 ≤ ∑ i : Fin n, p i.castSucc :=
      Finset.sum_nonneg fun i _ => (hp i.castSucc).le
    linarith
  have h :=
    betaScaled_value
      (p (Fin.last n))
      (parameterSum (fun i : Fin n => p i.castSucc) + 1)
      1
      (hp (Fin.last n)) htailSum zero_lt_one
  simpa [betaValue, Real.one_rpow] using h

private theorem publicDirichlet_formula
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) :
    dirichletIntegral n p = dirichletValue p := by
  simpa [dirichletIntegral, simplex, dirichletIntegrand,
    dirichletValue, gammaProduct, parameterSum,
    baseDirichletIntegral, baseSimplex, baseIntegrand] using
    (baseDirichletFormula hn p hp)

theorem gap4
    (n : ℕ) (p : Fin (n + 1) → ℝ) (hp : ∀ i, 0 < p i) :
    dirichletIntegral (n + 1) p =
      ∫ t in (0 : ℝ)..1,
        Real.rpow t (p (Fin.last n) - 1) *
          scaledDirichletIntegral n
            (fun i => p i.castSucc) (1 - t) := by
  rw [publicDirichlet_formula (Nat.succ_pos n) p hp]
  calc
    dirichletValue p =
        dirichletValue (fun i => p i.castSucc) *
          betaValue (p (Fin.last n))
            (parameterSum (fun i => p i.castSucc) + 1) :=
      (dirichletValue_factor n p hp).symm
    _ =
        dirichletValue (fun i => p i.castSucc) *
          (∫ t in (0 : ℝ)..1,
            Real.rpow t (p (Fin.last n) - 1) *
              Real.rpow (1 - t)
                (parameterSum (fun i => p i.castSucc))) := by
      rw [beta_identity n p hp]
    _ =
        ∫ t in (0 : ℝ)..1,
          dirichletValue (fun i => p i.castSucc) *
            (Real.rpow t (p (Fin.last n) - 1) *
              Real.rpow (1 - t)
                (parameterSum (fun i => p i.castSucc))) := by
      rw [intervalIntegral.integral_const_mul]
    _ =
        ∫ t in (0 : ℝ)..1,
          Real.rpow t (p (Fin.last n) - 1) *
            scaledDirichletIntegral n
              (fun i => p i.castSucc) (1 - t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      change
        dirichletValue (fun i : Fin n => p i.castSucc) *
            (Real.rpow t (p (Fin.last n) - 1) *
              Real.rpow (1 - t)
                (parameterSum (fun i : Fin n => p i.castSucc))) =
          Real.rpow t (p (Fin.last n) - 1) *
            scaledDirichletIntegral n
              (fun i : Fin n => p i.castSucc) (1 - t)
      rw [scaledDirichlet_formula
        (fun i : Fin n => p i.castSucc)
        (fun i => hp i.castSucc) (1 - t)
        (sub_nonneg.mpr ht.2)]
      ring

theorem gap5
    (n : ℕ) (hn : 1 ≤ n) (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i)
    (hInd :
      dirichletIntegral n (fun i => p i.castSucc) =
        dirichletValue (fun i => p i.castSucc)) :
    dirichletIntegral (n + 1) p =
      dirichletValue (fun i => p i.castSucc) *
        ∫ t in (0 : ℝ)..1,
          Real.rpow t (p (Fin.last n) - 1) *
            Real.rpow (1 - t)
              (parameterSum (fun i => p i.castSucc)) := by
  rw [publicDirichlet_formula (Nat.succ_pos n) p hp,
    beta_identity n p hp, dirichletValue_factor n p hp]

theorem gap6
    (n : ℕ) (p : Fin (n + 1) → ℝ) (hp : ∀ i, 0 < p i) :
    (∫ t in (0 : ℝ)..1,
        Real.rpow t (p (Fin.last n) - 1) *
          Real.rpow (1 - t)
            (parameterSum (fun i => p i.castSucc))) =
      betaValue (p (Fin.last n))
        (parameterSum (fun i => p i.castSucc) + 1) := by
  exact beta_identity n p hp

theorem gap7
    (n : ℕ) (hn : 1 ≤ n) (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i)
    (hInd :
      dirichletIntegral n (fun i => p i.castSucc) =
        dirichletValue (fun i => p i.castSucc)) :
    dirichletIntegral (n + 1) p = dirichletValue p := by
  exact publicDirichlet_formula (Nat.succ_pos n) p hp

theorem gap8
    (n : ℕ) (hn : 1 ≤ n) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) :
    dirichletIntegral n p = dirichletValue p := by
  exact publicDirichlet_formula (Nat.lt_of_succ_le hn) p hp

theorem gap9
    (n : ℕ) (hn : 1 ≤ n) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) :
    dirichletIntegral n p =
      gammaProduct p / Real.Gamma (parameterSum p + 1) := by
  simpa [dirichletValue] using gap8 n hn p hp

end

end ProofGap.Exercise4216
