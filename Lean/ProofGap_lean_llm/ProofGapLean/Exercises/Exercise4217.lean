import Mathlib.Tactic.Measurability
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4217

noncomputable section

open MeasureTheory Set intervalIntegral
open scoped ENNReal Interval

private abbrev BaseVec (n : ℕ) := Fin n → ℝ

private def baseSimplex (n : ℕ) : Set (BaseVec n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

private def baseIntegrand {n : ℕ} (f : ℝ → ℝ) (p x : BaseVec n) : ℝ :=
  f (∑ i, x i) * ∏ i, Real.rpow (x i) (p i - 1)

private def baseLiouvilleIntegral {n : ℕ} (f : ℝ → ℝ) (p : BaseVec n) : ℝ :=
  ∫ x in baseSimplex n, baseIntegrand f p x ∂MeasureTheory.volume

private def baseOneDimensionalIntegral {n : ℕ} (f : ℝ → ℝ) (p : BaseVec n) : ℝ :=
  ∫ u in (0 : ℝ)..1, f u * Real.rpow u ((∑ i, p i) - 1)

private def weight {n : ℕ} (p x : BaseVec n) : ℝ :=
  ∏ i, Real.rpow (x i) (p i - 1)

private def simplexAt (n : ℕ) (t : ℝ) : Set (BaseVec n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ t}

private def massLIntegral {n : ℕ} (p : BaseVec n) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in simplexAt n t, ENNReal.ofReal (weight p x)

private theorem weight_nonneg {n : ℕ} (p x : BaseVec n)
    (hx : ∀ i, 0 ≤ x i) :
    0 ≤ weight p x := by
  exact Finset.prod_nonneg fun i _ =>
    Real.rpow_nonneg (hx i) (p i - 1)

private theorem measurable_weight {n : ℕ} (p : BaseVec n) :
    Measurable (weight p) := by
  unfold weight
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

private theorem massLIntegral_zero {n : ℕ}
    (hn : 0 < n) (p : BaseVec n) :
    massLIntegral p 0 = 0 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [massLIntegral, simplexAt_zero n]
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

private theorem weight_split {n : ℕ}
    (p x : BaseVec (n + 1)) :
    weight p x =
      Real.rpow (x 0) (p 0 - 1) *
        weight (fun i : Fin n => p i.succ)
          (fun i : Fin n => x i.succ) := by
  simp [weight, Fin.prod_univ_succ]

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
      (weight (fun i : Fin n => p i.succ) q.2)

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
      (((measurable_weight
        (fun i : Fin n => p i.succ)).comp
          measurable_snd).ennreal_ofReal)

private theorem massLIntegral_succ
    (n : ℕ) (p : BaseVec (n + 1)) (t : ℝ) :
    massLIntegral p t =
      ∫⁻ z in Set.Icc (0 : ℝ) t,
        ENNReal.ofReal (Real.rpow z (p 0 - 1)) *
          massLIntegral
            (fun i : Fin n => p i.succ) (t - z) := by
  have hleft :
      massLIntegral p t =
        ∫⁻ x in simplexAt (n + 1) t,
          splitDensity p (splitVec n x) := by
    unfold massLIntegral
    apply setLIntegral_congr_fun
      (measurableSet_simplexAt (n + 1) t)
    intro x hx
    change
      ENNReal.ofReal (weight p x) =
        ENNReal.ofReal (Real.rpow (x 0) (p 0 - 1)) *
          ENNReal.ofReal
            (weight (fun i : Fin n => p i.succ)
              (fun i : Fin n => x i.succ))
    rw [weight_split]
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
            massLIntegral
              (fun i : Fin n => p i.succ) (t - z) := by
        unfold splitDensity massLIntegral
        change
          (∫⁻ y in simplexAt n (t - z),
            ENNReal.ofReal (Real.rpow z (p 0 - 1)) *
              ENNReal.ofReal
                (weight
                  (fun i : Fin n => p i.succ) y)) =
            ENNReal.ofReal (Real.rpow z (p 0 - 1)) *
              ∫⁻ y in simplexAt n (t - z),
                ENNReal.ofReal
                  (weight
                    (fun i : Fin n => p i.succ) y)
        rw [lintegral_const_mul]
        exact
          (measurable_weight
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

def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

def parameterSum {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ i, p i

def gammaProduct {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∏ i, Real.Gamma (p i)

def liouvilleIntegrand
    {n : ℕ} (f : ℝ → ℝ) (p x : Fin n → ℝ) : ℝ :=
  f (∑ i, x i) * ∏ i, Real.rpow (x i) (p i - 1)

def liouvilleIntegral
    (n : ℕ) (f : ℝ → ℝ) (p : Fin n → ℝ) : ℝ :=
  ∫ x in simplex n, liouvilleIntegrand f p x

def liouvilleValue
    {n : ℕ} (f : ℝ → ℝ) (p : Fin n → ℝ) : ℝ :=
  gammaProduct p / Real.Gamma (parameterSum p) *
    ∫ u in (0 : ℝ)..1,
      f u * Real.rpow u (parameterSum p - 1)

def twoSimplex : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}

def twoSimplexIntegral
    (f : ℝ → ℝ) (p q : ℝ) : ℝ :=
  ∫ z in twoSimplex,
    f (z.1 + z.2) *
      Real.rpow z.1 (p - 1) * Real.rpow z.2 (q - 1)

def twoNestedIntegral
    (f : ℝ → ℝ) (p q : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    f u *
      ∫ t in (0 : ℝ)..u,
        Real.rpow t (p - 1) * Real.rpow (u - t) (q - 1)

def twoSeparatedIntegral
    (f : ℝ → ℝ) (p q : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    f u *
      ∫ t in (0 : ℝ)..1,
        Real.rpow t (p - 1) * Real.rpow (1 - t) (q - 1) *
          Real.rpow u (p + q - 1)

def tailFunction (f : ℝ → ℝ) (q t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(1 - t),
    f (t + x) * Real.rpow x (q - 1)

def triangleIntegral (f : ℝ → ℝ) (p q : ℝ) : ℝ :=
  ∫ z in twoSimplex,
    f (z.1 + z.2) *
      Real.rpow z.1 (p - 1) * Real.rpow z.2 (q - 1)

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
  let g : ℝ → ℝ := fun x =>
    Real.rpow x (s - 1) *
      Real.rpow (A - x) (u - 1)
  have hgInterval : IntervalIntegrable g volume 0 A := by
    exact betaScaled_integrable s u A hs hu hA
  have hg :
      IntegrableOn g (Set.Icc (0 : ℝ) A) volume := by
    exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        hA.le).mp hgInterval
  have hg_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) A)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact mul_nonneg
      (Real.rpow_nonneg hx.1 (s - 1))
      (Real.rpow_nonneg (sub_nonneg.mpr hx.2) (u - 1))
  rw [← ofReal_integral_eq_lintegral_ofReal hg hg_nonneg]
  rw [← setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [← intervalIntegral.integral_of_le hA.le]
  exact congrArg ENNReal.ofReal
    (betaScaled_value s u A hs hu hA)

private def massConstant {n : ℕ} (p : BaseVec n) : ℝ :=
  (∏ i, Real.Gamma (p i)) /
    Real.Gamma ((∑ i, p i) + 1)

private theorem massConstant_pos {n : ℕ}
    (p : BaseVec n) (hp : ∀ i, 0 < p i) :
    0 < massConstant p := by
  unfold massConstant
  apply div_pos
  · exact Finset.prod_pos fun i _ =>
      Real.Gamma_pos_of_pos (hp i)
  · apply Real.Gamma_pos_of_pos
    have hsum : 0 ≤ ∑ i, p i :=
      Finset.sum_nonneg fun i _ => (hp i).le
    linarith

private theorem massLIntegral_eq
    {n : ℕ} (p : BaseVec n) (hp : ∀ i, 0 < p i)
    (t : ℝ) (ht : 0 ≤ t) :
    massLIntegral p t =
      ENNReal.ofReal
        (massConstant p *
          Real.rpow t (∑ i, p i)) := by
  induction n generalizing t with
  | zero =>
      letI : ∀ i : Fin 0, IsProbabilityMeasure
          (volume : Measure ℝ) := fun i => Fin.elim0 i
      letI : IsProbabilityMeasure
          (volume : Measure (BaseVec 0)) := inferInstance
      simp [massLIntegral, simplexAt, weight,
        massConstant, ht, Real.Gamma_one]
  | succ n ih =>
      by_cases hzero : t = 0
      · subst t
        rw [massLIntegral_zero (Nat.succ_pos n)]
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
            0 ≤ massConstant
              (fun i : Fin n => p i.succ) :=
          (massConstant_pos
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
            massConstant
                (fun i : Fin n => p i.succ) *
              (Real.rpow t
                  (p 0 + ∑ i : Fin n, p i.succ) *
                (Real.Gamma (p 0) *
                  Real.Gamma
                    ((∑ i : Fin n, p i.succ) + 1) /
                  Real.Gamma
                    (p 0 +
                      (∑ i : Fin n, p i.succ) + 1))) =
              massConstant p *
                Real.rpow t (∑ i, p i) := by
          unfold massConstant
          rw [prod_gamma_split, sum_split]
          field_simp [hgammaTail]
        rw [massLIntegral_succ]
        calc
          (∫⁻ z in Set.Icc (0 : ℝ) t,
              ENNReal.ofReal (Real.rpow z (p 0 - 1)) *
                massLIntegral
                  (fun i : Fin n => p i.succ) (t - z)) =
              ∫⁻ z in Set.Icc (0 : ℝ) t,
                ENNReal.ofReal
                    (Real.rpow z (p 0 - 1)) *
                  ENNReal.ofReal
                    (massConstant
                        (fun i : Fin n => p i.succ) *
                      Real.rpow (t - z)
                        (∑ i : Fin n, p i.succ)) := by
            apply setLIntegral_congr_fun measurableSet_Icc
            intro z hz
            change
              ENNReal.ofReal
                    (Real.rpow z (p 0 - 1)) *
                  massLIntegral
                    (fun i : Fin n => p i.succ) (t - z) =
                ENNReal.ofReal
                    (Real.rpow z (p 0 - 1)) *
                  ENNReal.ofReal
                    (massConstant
                        (fun i : Fin n => p i.succ) *
                      Real.rpow (t - z)
                        (∑ i : Fin n, p i.succ))
            rw [ih
              (fun i : Fin n => p i.succ) hpTail
              (t - z) (sub_nonneg.mpr hz.2)]
          _ =
              ∫⁻ z in Set.Icc (0 : ℝ) t,
                ENNReal.ofReal
                  (massConstant
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
                    (massConstant
                        (fun i : Fin n => p i.succ) *
                      Real.rpow (t - z)
                        (∑ i : Fin n, p i.succ)) =
                  ENNReal.ofReal
                    (Real.rpow z (p 0 - 1) *
                      (massConstant
                          (fun i : Fin n => p i.succ) *
                        Real.rpow (t - z)
                          (∑ i : Fin n, p i.succ))) :=
                (ENNReal.ofReal_mul hzpow).symm
              _ = ENNReal.ofReal
                    (massConstant
                        (fun i : Fin n => p i.succ) *
                      (Real.rpow z (p 0 - 1) *
                        Real.rpow (t - z)
                          (∑ i : Fin n, p i.succ))) := by
                congr 1
                ring
          _ =
              ENNReal.ofReal
                  (massConstant
                    (fun i : Fin n => p i.succ)) *
                (∫⁻ z in Set.Icc (0 : ℝ) t,
                  ENNReal.ofReal
                    (Real.rpow z (p 0 - 1) *
                      Real.rpow (t - z)
                        (∑ i : Fin n, p i.succ))) := by
            calc
              (∫⁻ z in Set.Icc (0 : ℝ) t,
                  ENNReal.ofReal
                    (massConstant
                        (fun i : Fin n => p i.succ) *
                      (Real.rpow z (p 0 - 1) *
                        Real.rpow (t - z)
                          (∑ i : Fin n, p i.succ)))) =
                  ∫⁻ z in Set.Icc (0 : ℝ) t,
                    ENNReal.ofReal
                        (massConstant
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
                  (massConstant
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
                (massConstant p *
                  Real.rpow t (∑ i, p i)) := by
            rw [← ENNReal.ofReal_mul hconstant]
            exact congrArg ENNReal.ofReal halgebra

private def coordinateSum {n : ℕ} (x : BaseVec n) : ℝ :=
  ∑ i, x i

private theorem measurable_coordinateSum (n : ℕ) :
    Measurable (coordinateSum (n := n)) := by
  unfold coordinateSum
  measurability

private def baseDensity {n : ℕ} (p : BaseVec n)
    (x : BaseVec n) : ℝ≥0∞ :=
  ENNReal.ofReal (weight p x)

private theorem measurable_baseDensity {n : ℕ} (p : BaseVec n) :
    Measurable (baseDensity p) :=
  (measurable_weight p).ennreal_ofReal

private def baseMeasure {n : ℕ} (p : BaseVec n) :
    Measure (BaseVec n) :=
  ((volume : Measure (BaseVec n)).withDensity
    (baseDensity p)).restrict (baseSimplex n)

private def pushedMeasure {n : ℕ} (p : BaseVec n) :
    Measure ℝ :=
  (baseMeasure p).map coordinateSum

private def radialConstant {n : ℕ} (p : BaseVec n) : ℝ :=
  (∏ i, Real.Gamma (p i)) /
    Real.Gamma (∑ i, p i)

private theorem parameterSum_pos {n : ℕ}
    (hn : 0 < n) (p : BaseVec n) (hp : ∀ i, 0 < p i) :
    0 < ∑ i, p i := by
  let i : Fin n := ⟨0, hn⟩
  exact (hp i).trans_le
    (Finset.single_le_sum
      (fun j _ => (hp j).le) (Finset.mem_univ i))

private theorem radialConstant_pos {n : ℕ}
    (hn : 0 < n) (p : BaseVec n) (hp : ∀ i, 0 < p i) :
    0 < radialConstant p := by
  unfold radialConstant
  exact div_pos
    (Finset.prod_pos fun i _ =>
      Real.Gamma_pos_of_pos (hp i))
    (Real.Gamma_pos_of_pos
      (parameterSum_pos hn p hp))

private def radialDensity {n : ℕ} (p : BaseVec n)
    (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (radialConstant p *
      Real.rpow u ((∑ i, p i) - 1))

private theorem measurable_radialDensity {n : ℕ}
    (p : BaseVec n) :
    Measurable (radialDensity p) := by
  unfold radialDensity
  have hrpow :
      Measurable
        (fun u : ℝ =>
          Real.rpow u ((∑ i, p i) - 1)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const
      (fun u hu => Or.inl (by simpa using hu))
  exact
    (measurable_const.mul hrpow).ennreal_ofReal

private def radialMeasure {n : ℕ} (p : BaseVec n) :
    Measure ℝ :=
  ((volume : Measure ℝ).withDensity
    (radialDensity p)).restrict (Set.Icc 0 1)

private theorem sum_preimage_Iic_inter_simplex_of_nonneg
    (n : ℕ) (a : ℝ) :
    coordinateSum ⁻¹' Set.Iic a ∩ baseSimplex n =
      simplexAt n (min a 1) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_Iic, coordinateSum, baseSimplex, simplexAt,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxa, hxnonneg, hxone⟩
    exact ⟨hxnonneg, le_min hxa hxone⟩
  · rintro ⟨hxnonneg, hxsum⟩
    exact
      ⟨hxsum.trans (min_le_left a 1),
        hxnonneg, hxsum.trans (min_le_right a 1)⟩

private theorem sum_preimage_Iic_inter_simplex_of_neg
    (n : ℕ) (a : ℝ) (ha : a < 0) :
    coordinateSum ⁻¹' Set.Iic a ∩ baseSimplex n =
      (∅ : Set (BaseVec n)) := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hsum_nonneg : 0 ≤ coordinateSum x := by
    exact Finset.sum_nonneg fun i _ => hx.2.1 i
  exact (not_le_of_gt ha) (hsum_nonneg.trans hx.1)

private theorem Iic_inter_Icc_of_nonneg
    (a : ℝ) :
    Set.Iic a ∩ Set.Icc (0 : ℝ) 1 =
      Set.Icc 0 (min a 1) := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
  constructor
  · rintro ⟨hua, hu0, hu1⟩
    exact ⟨hu0, le_min hua hu1⟩
  · rintro ⟨hu0, hu⟩
    exact
      ⟨hu.trans (min_le_left a 1), hu0,
        hu.trans (min_le_right a 1)⟩

private theorem Iic_inter_Icc_of_neg
    (a : ℝ) (ha : a < 0) :
    Set.Iic a ∩ Set.Icc (0 : ℝ) 1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact (not_le_of_gt ha) (hu.2.1.trans hu.1)

private theorem rpow_lintegral
    (s A : ℝ) (hs : 0 < s) (hA : 0 ≤ A) :
    (∫⁻ u in Set.Icc (0 : ℝ) A,
      ENNReal.ofReal (Real.rpow u (s - 1))) =
      ENNReal.ofReal (Real.rpow A s / s) := by
  have hInterval :
      IntervalIntegrable
        (fun u : ℝ => Real.rpow u (s - 1))
        volume 0 A :=
    intervalIntegral.intervalIntegrable_rpow'
      (by linarith)
  have hIntegrable :
      IntegrableOn
        (fun u : ℝ => Real.rpow u (s - 1))
        (Set.Icc (0 : ℝ) A) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      hA).mp hInterval
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) A)]
        (fun u : ℝ => Real.rpow u (s - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact Real.rpow_nonneg hu.1 (s - 1)
  rw [← ofReal_integral_eq_lintegral_ofReal
    hIntegrable hnonneg]
  rw [← setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [← intervalIntegral.integral_of_le hA]
  have hformula :
      (∫ u in (0 : ℝ)..A,
        Real.rpow u (s - 1)) =
        (Real.rpow A ((s - 1) + 1) -
          Real.rpow 0 ((s - 1) + 1)) /
            ((s - 1) + 1) := by
    exact integral_rpow (Or.inl (by linarith))
  rw [hformula]
  have hs_ne : s ≠ 0 := hs.ne'
  have hzero : Real.rpow 0 s = 0 :=
    Real.zero_rpow hs_ne
  rw [show s - 1 + 1 = s by ring, hzero]
  ring

private theorem pushedMeasure_Iic
    {n : ℕ} (p : BaseVec n) (hp : ∀ i, 0 < p i)
    (a : ℝ) :
    pushedMeasure p (Set.Iic a) =
      if a < 0 then 0
      else
        ENNReal.ofReal
          (massConstant p *
            Real.rpow (min a 1) (∑ i, p i)) := by
  rw [pushedMeasure,
    Measure.map_apply (measurable_coordinateSum n)
      measurableSet_Iic]
  rw [baseMeasure,
    Measure.restrict_apply
      (measurableSet_Iic.preimage
        (measurable_coordinateSum n))]
  by_cases ha : a < 0
  · rw [if_pos ha,
      sum_preimage_Iic_inter_simplex_of_neg n a ha]
    simp
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    rw [if_neg ha,
      sum_preimage_Iic_inter_simplex_of_nonneg n a]
    rw [withDensity_apply _
      (measurableSet_simplexAt n (min a 1))]
    change
      massLIntegral p (min a 1) =
        ENNReal.ofReal
          (massConstant p *
            Real.rpow (min a 1) (∑ i, p i))
    exact massLIntegral_eq p hp (min a 1)
      (le_min ha0 zero_le_one)

private theorem radial_mass_algebra
    {n : ℕ} (hn : 0 < n) (p : BaseVec n)
    (hp : ∀ i, 0 < p i) (A : ℝ) :
    radialConstant p *
        (Real.rpow A (∑ i, p i) / (∑ i, p i)) =
      massConstant p *
        Real.rpow A (∑ i, p i) := by
  have hs : 0 < ∑ i, p i :=
    parameterSum_pos hn p hp
  have hgamma :
      Real.Gamma (∑ i, p i) ≠ 0 :=
    (Real.Gamma_pos_of_pos hs).ne'
  unfold radialConstant massConstant
  rw [Real.Gamma_add_one hs.ne']
  field_simp [hs.ne', hgamma]

private theorem radialMeasure_Iic
    {n : ℕ} (hn : 0 < n) (p : BaseVec n)
    (hp : ∀ i, 0 < p i) (a : ℝ) :
    radialMeasure p (Set.Iic a) =
      if a < 0 then 0
      else
        ENNReal.ofReal
          (massConstant p *
            Real.rpow (min a 1) (∑ i, p i)) := by
  rw [radialMeasure,
    Measure.restrict_apply measurableSet_Iic]
  by_cases ha : a < 0
  · rw [if_pos ha, Iic_inter_Icc_of_neg a ha]
    simp
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    rw [if_neg ha, Iic_inter_Icc_of_nonneg a]
    rw [withDensity_apply _ measurableSet_Icc]
    have hs : 0 < ∑ i, p i :=
      parameterSum_pos hn p hp
    have hC : 0 ≤ radialConstant p :=
      (radialConstant_pos hn p hp).le
    calc
      (∫⁻ u in Set.Icc (0 : ℝ) (min a 1),
          radialDensity p u) =
          ∫⁻ u in Set.Icc (0 : ℝ) (min a 1),
            ENNReal.ofReal (radialConstant p) *
              ENNReal.ofReal
                (Real.rpow u ((∑ i, p i) - 1)) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro u _
        unfold radialDensity
        exact ENNReal.ofReal_mul hC
      _ =
          ENNReal.ofReal (radialConstant p) *
            (∫⁻ u in Set.Icc (0 : ℝ) (min a 1),
              ENNReal.ofReal
                (Real.rpow u ((∑ i, p i) - 1))) := by
        rw [lintegral_const_mul'
          _ _ ENNReal.ofReal_ne_top]
      _ =
          ENNReal.ofReal (radialConstant p) *
            ENNReal.ofReal
              (Real.rpow (min a 1) (∑ i, p i) /
                (∑ i, p i)) := by
        rw [rpow_lintegral
          (∑ i, p i) (min a 1) hs
          (le_min ha0 zero_le_one)]
      _ =
          ENNReal.ofReal
            (radialConstant p *
              (Real.rpow (min a 1) (∑ i, p i) /
                (∑ i, p i))) := by
        rw [ENNReal.ofReal_mul hC]
      _ =
          ENNReal.ofReal
            (massConstant p *
              Real.rpow (min a 1) (∑ i, p i)) :=
        congrArg ENNReal.ofReal
          (radial_mass_algebra hn p hp (min a 1))

private theorem pushedMeasure_eq_radialMeasure
    {n : ℕ} (hn : 0 < n) (p : BaseVec n)
    (hp : ∀ i, 0 < p i) :
    pushedMeasure p = radialMeasure p := by
  have hfinite :
      pushedMeasure p Set.univ < ⊤ := by
    rw [pushedMeasure,
      Measure.map_apply (measurable_coordinateSum n)
        MeasurableSet.univ]
    simp only [Set.preimage_univ]
    rw [baseMeasure,
      Measure.restrict_apply MeasurableSet.univ]
    simp only [Set.univ_inter]
    rw [withDensity_apply _
      (by
        rw [← simplexAt_one]
        exact measurableSet_simplexAt n 1)]
    change massLIntegral p 1 < ⊤
    rw [massLIntegral_eq p hp 1 zero_le_one]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure (pushedMeasure p) := ⟨hfinite⟩
  apply Measure.ext_of_Iic
  intro a
  rw [pushedMeasure_Iic p hp a,
    radialMeasure_Iic hn p hp a]

private theorem baseMeasure_integral_eq
    {n : ℕ} (f : ℝ → ℝ) (p : BaseVec n) :
    (∫ x, f (coordinateSum x) ∂baseMeasure p) =
      baseLiouvilleIntegral f p := by
  have hs : MeasurableSet (baseSimplex n) := by
    rw [← simplexAt_one]
    exact measurableSet_simplexAt n 1
  unfold baseMeasure baseLiouvilleIntegral
  change
    (∫ x in baseSimplex n,
      f (coordinateSum x)
        ∂(volume : Measure (BaseVec n)).withDensity
          (baseDensity p)) =
      ∫ x in baseSimplex n, baseIntegrand f p x
        ∂(volume : Measure (BaseVec n))
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    ((measurable_baseDensity p).aemeasurable.restrict)
    (Filter.Eventually.of_forall fun _ =>
      ENNReal.ofReal_lt_top)
    _ hs]
  apply setIntegral_congr_fun hs
  intro x hx
  simp only [smul_eq_mul]
  rw [baseDensity,
    ENNReal.toReal_ofReal
      (weight_nonneg p x hx.1)]
  unfold baseIntegrand weight coordinateSum
  ring

private theorem radialMeasure_integral_eq
    {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ)
    (p : BaseVec n) (hp : ∀ i, 0 < p i) :
    (∫ u, f u ∂radialMeasure p) =
      radialConstant p * baseOneDimensionalIntegral f p := by
  have hC : 0 ≤ radialConstant p :=
    (radialConstant_pos hn p hp).le
  unfold radialMeasure
  change
    (∫ u in Set.Icc (0 : ℝ) 1, f u
      ∂(volume : Measure ℝ).withDensity
        (radialDensity p)) =
      radialConstant p * baseOneDimensionalIntegral f p
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    ((measurable_radialDensity p).aemeasurable.restrict)
    (Filter.Eventually.of_forall fun _ =>
      ENNReal.ofReal_lt_top)
    _ measurableSet_Icc]
  calc
    (∫ u in Set.Icc (0 : ℝ) 1,
        (radialDensity p u).toReal • f u) =
        ∫ u in Set.Icc (0 : ℝ) 1,
          radialConstant p *
            (f u *
              Real.rpow u ((∑ i, p i) - 1)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u hu
      simp only [smul_eq_mul]
      have hdensity :
          (radialDensity p u).toReal =
            radialConstant p *
              Real.rpow u ((∑ i, p i) - 1) := by
        unfold radialDensity
        exact ENNReal.toReal_ofReal
          (mul_nonneg hC
            (Real.rpow_nonneg hu.1
              ((∑ i, p i) - 1)))
      rw [hdensity]
      ring
    _ =
        radialConstant p *
          (∫ u in Set.Icc (0 : ℝ) 1,
            f u *
              Real.rpow u ((∑ i, p i) - 1)) := by
      rw [MeasureTheory.integral_const_mul]
    _ =
        radialConstant p *
          (∫ u in (0 : ℝ)..1,
            f u *
              Real.rpow u ((∑ i, p i) - 1)) := by
      congr 1
      rw [← setIntegral_congr_set Ioc_ae_eq_Icc]
      rw [← intervalIntegral.integral_of_le zero_le_one]
    _ =
        radialConstant p *
          baseOneDimensionalIntegral f p := by
      rfl

/-! Source: `results/stage1_gpt55/09_重积分与含参积分/exercise_4217_autoformalization_result/exercise_4217.md`. -/

private theorem baseLiouvilleFormula
    {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) (hf : Continuous f)
    (p : BaseVec n) (hp : ∀ i, 0 < p i) :
    baseLiouvilleIntegral f p =
      (∏ i, Real.Gamma (p i)) / Real.Gamma (∑ i, p i) *
        baseOneDimensionalIntegral f p := by
  calc
    baseLiouvilleIntegral f p =
        ∫ x, f (coordinateSum x) ∂baseMeasure p :=
      (baseMeasure_integral_eq f p).symm
    _ = ∫ u, f u ∂pushedMeasure p := by
      unfold pushedMeasure
      exact
        (integral_map_of_stronglyMeasurable
          (measurable_coordinateSum n)
          hf.stronglyMeasurable).symm
    _ = ∫ u, f u ∂radialMeasure p := by
      rw [pushedMeasure_eq_radialMeasure hn p hp]
    _ = radialConstant p *
        baseOneDimensionalIntegral f p :=
      radialMeasure_integral_eq hn f p hp
    _ =
        (∏ i, Real.Gamma (p i)) /
            Real.Gamma (∑ i, p i) *
          baseOneDimensionalIntegral f p := by
      rfl

private theorem publicLiouville_formula
    {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) (hf : Continuous f)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    liouvilleIntegral n f p = liouvilleValue f p := by
  simpa [liouvilleIntegral, simplex, liouvilleIntegrand,
    liouvilleValue, gammaProduct, parameterSum,
    baseLiouvilleIntegral, baseSimplex, baseIntegrand,
    baseOneDimensionalIntegral] using
    (baseLiouvilleFormula hn f hf p hp)

theorem gap1
    (f : ℝ → ℝ) (hf : Continuous f) (p : ℝ) (hp : 0 < p) :
    liouvilleIntegral 1 f (fun _ => p) =
      ∫ u in (0 : ℝ)..1, f u * Real.rpow u (p - 1) := by
  rw [publicLiouville_formula (by norm_num) f hf
    (fun _ : Fin 1 => p) (fun _ => hp)]
  have hg : Real.Gamma p ≠ 0 :=
    (Real.Gamma_pos_of_pos hp).ne'
  simp [liouvilleValue, gammaProduct, parameterSum,
    Fin.sum_univ_succ, Fin.prod_univ_succ, hg]

private def pairParameters (p q : ℝ) : Fin 2 → ℝ :=
  fun i => Fin.cases p (fun _ => q) i

private theorem twoSimplex_eq_liouville
    (f : ℝ → ℝ) (p q : ℝ) :
    twoSimplexIntegral f p q =
      liouvilleIntegral 2 f (pairParameters p q) := by
  let T : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) :=
    MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hT : MeasurePreserving T volume volume :=
    MeasureTheory.volume_preserving_piFinTwo
      (fun _ : Fin 2 => ℝ)
  let g : (ℝ × ℝ) → ℝ := fun z =>
    f (z.1 + z.2) *
      Real.rpow z.1 (p - 1) * Real.rpow z.2 (q - 1)
  have hmap :=
    hT.integral_comp T.measurableEmbedding
      (twoSimplex.indicator g)
  have htwo : MeasurableSet twoSimplex := by
    unfold twoSimplex
    measurability
  have hsimp : MeasurableSet (simplex 2) := by
    unfold simplex
    measurability
  unfold twoSimplexIntegral liouvilleIntegral
  change
    (∫ z in twoSimplex, g z) =
      ∫ x in simplex 2,
        liouvilleIntegrand f (pairParameters p q) x
  rw [← MeasureTheory.integral_indicator htwo,
    ← MeasureTheory.integral_indicator hsimp]
  rw [← hmap]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  have hmem :
      T x ∈ twoSimplex ↔ x ∈ simplex 2 := by
    simp [T, twoSimplex, simplex, Fin.sum_univ_succ, and_assoc]
  by_cases hx : x ∈ simplex 2
  · rw [Set.indicator_of_mem (hmem.mpr hx),
      Set.indicator_of_mem hx]
    simp [g, T, liouvilleIntegrand, pairParameters,
      Fin.sum_univ_succ, Fin.prod_univ_succ]
    ring
  · rw [Set.indicator_of_notMem (not_congr hmem |>.mpr hx),
      Set.indicator_of_notMem hx]

private theorem twoSimplex_formula
    (f : ℝ → ℝ) (hf : Continuous f)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    twoSimplexIntegral f p q =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) *
        ∫ u in (0 : ℝ)..1,
          f u * Real.rpow u (p + q - 1) := by
  rw [twoSimplex_eq_liouville]
  rw [publicLiouville_formula (by norm_num) f hf
    (pairParameters p q) (by
      intro i
      fin_cases i
      · exact hp
      · exact hq)]
  simp [liouvilleValue, gammaProduct, parameterSum,
    pairParameters, Fin.sum_univ_succ, Fin.prod_univ_succ]

private theorem beta_unit_value
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (∫ t in (0 : ℝ)..1,
      Real.rpow t (p - 1) *
        Real.rpow (1 - t) (q - 1)) =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have h := betaScaled_value p q 1 hp hq zero_lt_one
  simpa [Real.one_rpow] using h

private theorem twoNested_formula
    (f : ℝ → ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    twoNestedIntegral f p q =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) *
        ∫ u in (0 : ℝ)..1,
          f u * Real.rpow u (p + q - 1) := by
  unfold twoNestedIntegral
  calc
    (∫ u in (0 : ℝ)..1,
        f u *
          ∫ t in (0 : ℝ)..u,
            Real.rpow t (p - 1) *
              Real.rpow (u - t) (q - 1)) =
        ∫ u in (0 : ℝ)..1,
          (Real.Gamma p * Real.Gamma q /
              Real.Gamma (p + q)) *
            (f u * Real.rpow u (p + q - 1)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with u
      intro hu
      rw [Set.uIoc_of_le zero_le_one] at hu
      rw [betaScaled_value p q u hp hq hu.1]
      ring
    _ =
        Real.Gamma p * Real.Gamma q /
            Real.Gamma (p + q) *
          ∫ u in (0 : ℝ)..1,
            f u * Real.rpow u (p + q - 1) := by
      rw [intervalIntegral.integral_const_mul]

private theorem twoSeparated_formula
    (f : ℝ → ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    twoSeparatedIntegral f p q =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) *
        ∫ u in (0 : ℝ)..1,
          f u * Real.rpow u (p + q - 1) := by
  have hinner (u : ℝ) :
      (∫ t in (0 : ℝ)..1,
        Real.rpow t (p - 1) *
            Real.rpow (1 - t) (q - 1) *
          Real.rpow u (p + q - 1)) =
        (Real.Gamma p * Real.Gamma q /
            Real.Gamma (p + q)) *
          Real.rpow u (p + q - 1) := by
    rw [intervalIntegral.integral_mul_const,
      beta_unit_value p q hp hq]
  unfold twoSeparatedIntegral
  calc
    (∫ u in (0 : ℝ)..1,
        f u *
          ∫ t in (0 : ℝ)..1,
            Real.rpow t (p - 1) *
                Real.rpow (1 - t) (q - 1) *
              Real.rpow u (p + q - 1)) =
        ∫ u in (0 : ℝ)..1,
          (Real.Gamma p * Real.Gamma q /
              Real.Gamma (p + q)) *
            (f u * Real.rpow u (p + q - 1)) := by
      apply intervalIntegral.integral_congr
      intro u _
      change
        f u *
            (∫ t in (0 : ℝ)..1,
              Real.rpow t (p - 1) *
                  Real.rpow (1 - t) (q - 1) *
                Real.rpow u (p + q - 1)) =
          (Real.Gamma p * Real.Gamma q /
              Real.Gamma (p + q)) *
            (f u * Real.rpow u (p + q - 1))
      rw [hinner u]
      ring
    _ =
        Real.Gamma p * Real.Gamma q /
            Real.Gamma (p + q) *
          ∫ u in (0 : ℝ)..1,
            f u * Real.rpow u (p + q - 1) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap2
    (f : ℝ → ℝ) (hf : Continuous f)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    twoSimplexIntegral f p q = twoNestedIntegral f p q := by
  rw [twoSimplex_formula f hf p q hp hq,
    twoNested_formula f p q hp hq]

theorem gap3
    (f : ℝ → ℝ) (hf : Continuous f)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    twoNestedIntegral f p q = twoSeparatedIntegral f p q := by
  rw [twoNested_formula f p q hp hq,
    twoSeparated_formula f p q hp hq]

theorem gap4
    (f : ℝ → ℝ) (hf : Continuous f)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    twoSimplexIntegral f p q =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) *
        ∫ u in (0 : ℝ)..1,
          f u * Real.rpow u (p + q - 1) := by
  exact twoSimplex_formula f hf p q hp hq

private theorem pairParameters_pos
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ∀ i, 0 < pairParameters p q i := by
  intro i
  fin_cases i
  · exact hp
  · exact hq

private theorem twoKernel_integrable
    (f : ℝ → ℝ) (hf : Continuous f)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    Integrable
      (twoSimplex.indicator (fun z : ℝ × ℝ =>
        f (z.1 + z.2) *
          Real.rpow z.1 (p - 1) *
            Real.rpow z.2 (q - 1)))
      ((volume : Measure ℝ).prod volume) := by
  let P : Fin 2 → ℝ := pairParameters p q
  have hP : ∀ i, 0 < P i :=
    pairParameters_pos p q hp hq
  have hsBase : MeasurableSet (baseSimplex 2) := by
    rw [← simplexAt_one]
    exact measurableSet_simplexAt 2 1
  have hweightNonneg :
      0 ≤ᵐ[(volume : Measure (BaseVec 2)).restrict
        (baseSimplex 2)] weight P := by
    filter_upwards [ae_restrict_mem hsBase] with x hx
    exact weight_nonneg P x hx.1
  have hweightInt :
      IntegrableOn (weight P) (baseSimplex 2)
        (volume : Measure (BaseVec 2)) := by
    constructor
    · exact
        (measurable_weight P).aestronglyMeasurable.restrict
    · rw [hasFiniteIntegral_iff_ofReal hweightNonneg]
      change massLIntegral P 1 < ⊤
      rw [massLIntegral_eq P hP 1 zero_le_one]
      exact ENNReal.ofReal_lt_top
  have hbdd :
      BddAbove ((fun u : ℝ => |f u|) '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hf.continuousOn.abs
  rcases hbdd with ⟨C, hC⟩
  have hfactorMeas :
      AEStronglyMeasurable
        (fun x : BaseVec 2 => f (∑ i, x i))
        ((volume : Measure (BaseVec 2)).restrict
          (baseSimplex 2)) := by
    have hsum :
        Measurable (fun x : BaseVec 2 => ∑ i, x i) := by
      measurability
    exact
      (hf.measurable.comp hsum).aestronglyMeasurable.restrict
  have hfactorBound :
      ∀ᵐ x ∂((volume : Measure (BaseVec 2)).restrict
          (baseSimplex 2)),
        ‖f (∑ i, x i)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hsBase] with x hx
    have hsum0 : 0 ≤ ∑ i, x i :=
      Finset.sum_nonneg fun i _ => hx.1 i
    have hmem : (∑ i, x i) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hsum0, hx.2⟩
    simpa [Real.norm_eq_abs] using
      hC ⟨∑ i, x i, hmem, rfl⟩
  have hbaseInt :
      IntegrableOn (baseIntegrand f P) (baseSimplex 2)
        (volume : Measure (BaseVec 2)) := by
    simpa only [baseIntegrand, weight] using
      hweightInt.bdd_mul hfactorMeas hfactorBound
  have hsPublic : MeasurableSet (simplex 2) := by
    unfold simplex
    measurability
  have hfin :
      Integrable
        ((simplex 2).indicator
          (liouvilleIntegrand f P))
        (volume : Measure (Fin 2 → ℝ)) := by
    apply (integrable_indicator_iff hsPublic).2
    simpa [simplex, baseSimplex, liouvilleIntegrand,
      baseIntegrand, P] using hbaseInt
  let T : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) :=
    MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hT : MeasurePreserving T volume volume :=
    MeasureTheory.volume_preserving_piFinTwo
      (fun _ : Fin 2 => ℝ)
  let g : (ℝ × ℝ) → ℝ := fun z =>
    f (z.1 + z.2) *
      Real.rpow z.1 (p - 1) * Real.rpow z.2 (q - 1)
  have hcomp :
      (twoSimplex.indicator g) ∘ T =
        (simplex 2).indicator
          (liouvilleIntegrand f P) := by
    funext x
    change
      twoSimplex.indicator g (T x) =
        (simplex 2).indicator
          (liouvilleIntegrand f P) x
    have hmem :
        T x ∈ twoSimplex ↔ x ∈ simplex 2 := by
      simp [T, twoSimplex, simplex, Fin.sum_univ_succ,
        and_assoc]
    by_cases hx : x ∈ simplex 2
    · rw [Set.indicator_of_mem (hmem.mpr hx),
        Set.indicator_of_mem hx]
      simp [g, T, liouvilleIntegrand, P, pairParameters,
        Fin.sum_univ_succ, Fin.prod_univ_succ]
      ring
    · rw [Set.indicator_of_notMem
          (fun h => hx (hmem.mp h)),
        Set.indicator_of_notMem hx]
  apply
    (hT.integrable_comp_emb T.measurableEmbedding).mp
  rw [hcomp]
  exact hfin

private theorem triangle_tail_identity
    (f : ℝ → ℝ) (hf : Continuous f)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    triangleIntegral f p q =
      ∫ t in (0 : ℝ)..1,
        tailFunction f q t * Real.rpow t (p - 1) := by
  let g : (ℝ × ℝ) → ℝ := fun z =>
    f (z.1 + z.2) *
      Real.rpow z.1 (p - 1) * Real.rpow z.2 (q - 1)
  let H : (ℝ × ℝ) → ℝ := twoSimplex.indicator g
  have hInt :
      Integrable H ((volume : Measure ℝ).prod volume) := by
    exact twoKernel_integrable f hf p q hp hq
  have htwo : MeasurableSet twoSimplex := by
    unfold twoSimplex
    measurability
  have hsection (t : ℝ) :
      (∫ x : ℝ, H (t, x)) =
        (Set.Icc (0 : ℝ) 1).indicator
          (fun s =>
            tailFunction f q s *
              Real.rpow s (p - 1)) t := by
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht]
      have hb : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      have hslice : MeasurableSet (Set.Icc (0 : ℝ) (1 - t)) :=
        measurableSet_Icc
      have hmem (x : ℝ) :
          (t, x) ∈ twoSimplex ↔
            x ∈ Set.Icc (0 : ℝ) (1 - t) := by
        unfold twoSimplex
        simp only [Set.mem_setOf_eq, Set.mem_Icc]
        constructor
        · rintro ⟨_, hx0, hsum⟩
          exact ⟨hx0, by linarith⟩
        · rintro ⟨hx0, hx1⟩
          exact ⟨ht.1, hx0, by linarith⟩
      have htailSet :
          tailFunction f q t =
            ∫ x in Set.Icc (0 : ℝ) (1 - t),
              f (t + x) * Real.rpow x (q - 1) := by
        unfold tailFunction
        rw [← setIntegral_congr_set Ioc_ae_eq_Icc]
        rw [← intervalIntegral.integral_of_le hb]
      calc
        (∫ x : ℝ, H (t, x)) =
            ∫ x in Set.Icc (0 : ℝ) (1 - t), g (t, x) := by
          rw [← MeasureTheory.integral_indicator hslice]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          change
            twoSimplex.indicator g (t, x) =
              (Set.Icc (0 : ℝ) (1 - t)).indicator
                (fun y => g (t, y)) x
          by_cases hx : x ∈ Set.Icc (0 : ℝ) (1 - t)
          · rw [Set.indicator_of_mem (hmem x |>.mpr hx),
              Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem
                (fun h => hx (hmem x |>.mp h)),
              Set.indicator_of_notMem hx]
        _ =
            ∫ x in Set.Icc (0 : ℝ) (1 - t),
              Real.rpow t (p - 1) *
                (f (t + x) * Real.rpow x (q - 1)) := by
          apply setIntegral_congr_fun hslice
          intro x _
          simp only [g]
          ring
        _ =
            Real.rpow t (p - 1) *
              ∫ x in Set.Icc (0 : ℝ) (1 - t),
                f (t + x) * Real.rpow x (q - 1) := by
          rw [MeasureTheory.integral_const_mul]
        _ =
            tailFunction f q t *
              Real.rpow t (p - 1) := by
          rw [← htailSet]
          ring
    · rw [Set.indicator_of_notMem ht]
      have hnone (x : ℝ) : (t, x) ∉ twoSimplex := by
        intro hz
        apply ht
        unfold twoSimplex at hz
        exact ⟨hz.1, by linarith [hz.2.1, hz.2.2]⟩
      have hzero : (fun x : ℝ => H (t, x)) = 0 := by
        funext x
        simp [H, hnone x]
      rw [hzero]
      simp
  unfold triangleIntegral
  change (∫ z in twoSimplex, g z) = _
  rw [← MeasureTheory.integral_indicator htwo]
  change
    (∫ z : ℝ × ℝ, H z
      ∂((volume : Measure ℝ).prod volume)) = _
  rw [MeasureTheory.integral_prod H hInt]
  calc
    (∫ t : ℝ, ∫ x : ℝ, H (t, x)) =
        ∫ t : ℝ,
          (Set.Icc (0 : ℝ) 1).indicator
            (fun s =>
              tailFunction f q s *
                Real.rpow s (p - 1)) t := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      exact hsection t
    _ =
        ∫ t in Set.Icc (0 : ℝ) 1,
          tailFunction f q t *
            Real.rpow t (p - 1) := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ =
        ∫ t in (0 : ℝ)..1,
          tailFunction f q t *
            Real.rpow t (p - 1) := by
      rw [← setIntegral_congr_set Ioc_ae_eq_Icc]
      rw [← intervalIntegral.integral_of_le zero_le_one]

private theorem triangle_formula
    (f : ℝ → ℝ) (hf : Continuous f)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    triangleIntegral f p q =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) *
        ∫ u in (0 : ℝ)..1,
          f u * Real.rpow u (p + q - 1) := by
  simpa [triangleIntegral, twoSimplexIntegral] using
    twoSimplex_formula f hf p q hp hq

theorem gap5
    (n : ℕ) (hn : 1 ≤ n)
    (f : ℝ → ℝ) (hf : Continuous f)
    (p : Fin (n + 1) → ℝ) (hp : ∀ i, 0 < p i)
    (hInd :
      liouvilleIntegral n
          (tailFunction f (p (Fin.last n)))
          (fun i => p i.castSucc) =
        liouvilleValue
          (tailFunction f (p (Fin.last n)))
          (fun i => p i.castSucc)) :
    liouvilleIntegral (n + 1) f p =
      gammaProduct (fun i => p i.castSucc) /
          Real.Gamma (parameterSum (fun i => p i.castSucc)) *
        ∫ t in (0 : ℝ)..1,
          tailFunction f (p (Fin.last n)) t *
            Real.rpow t
              (parameterSum (fun i => p i.castSucc) - 1) := by
  have hnpos : 0 < n := Nat.lt_of_succ_le hn
  have hs :
      0 < parameterSum (fun i : Fin n => p i.castSucc) := by
    unfold parameterSum
    exact parameterSum_pos hnpos
      (fun i : Fin n => p i.castSucc)
      (fun i => hp i.castSucc)
  have hq : 0 < p (Fin.last n) := hp (Fin.last n)
  rw [publicLiouville_formula (Nat.succ_pos n) f hf p hp]
  rw [← triangle_tail_identity f hf
    (parameterSum (fun i : Fin n => p i.castSucc))
    (p (Fin.last n)) hs hq]
  rw [triangle_formula f hf
    (parameterSum (fun i : Fin n => p i.castSucc))
    (p (Fin.last n)) hs hq]
  have hgS :
      Real.Gamma
        (∑ i : Fin n, p i.castSucc) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by
      simpa [parameterSum] using hs)).ne'
  unfold liouvilleValue gammaProduct parameterSum
  rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
  field_simp [hgS]
  <;> ring

theorem gap6
    (n : ℕ) (hn : 1 ≤ n)
    (f : ℝ → ℝ) (hf : Continuous f)
    (p : Fin (n + 1) → ℝ) (hp : ∀ i, 0 < p i) :
    (∫ t in (0 : ℝ)..1,
        tailFunction f (p (Fin.last n)) t *
          Real.rpow t
            (parameterSum (fun i => p i.castSucc) - 1)) =
      triangleIntegral f
        (parameterSum (fun i => p i.castSucc))
        (p (Fin.last n)) := by
  have hs :
      0 < parameterSum (fun i : Fin n => p i.castSucc) := by
    unfold parameterSum
    exact parameterSum_pos (Nat.lt_of_succ_le hn)
      (fun i : Fin n => p i.castSucc)
      (fun i => hp i.castSucc)
  exact
    (triangle_tail_identity f hf
      (parameterSum (fun i : Fin n => p i.castSucc))
      (p (Fin.last n)) hs (hp (Fin.last n))).symm

theorem gap7
    (n : ℕ) (hn : 1 ≤ n)
    (f : ℝ → ℝ) (hf : Continuous f)
    (p : Fin (n + 1) → ℝ) (hp : ∀ i, 0 < p i)
    (hInd :
      liouvilleIntegral n
          (tailFunction f (p (Fin.last n)))
          (fun i => p i.castSucc) =
        liouvilleValue
          (tailFunction f (p (Fin.last n)))
          (fun i => p i.castSucc)) :
    liouvilleIntegral (n + 1) f p = liouvilleValue f p := by
  exact publicLiouville_formula (Nat.succ_pos n) f hf p hp

theorem gap8
    (n : ℕ) (hn : 1 ≤ n)
    (f : ℝ → ℝ) (hf : Continuous f)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    liouvilleIntegral n f p = liouvilleValue f p := by
  exact publicLiouville_formula (Nat.lt_of_succ_le hn) f hf p hp

theorem gap9
    (n : ℕ) (hn : 1 ≤ n)
    (f : ℝ → ℝ) (hf : Continuous f)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    liouvilleIntegral n f p =
      gammaProduct p / Real.Gamma (parameterSum p) *
        ∫ u in (0 : ℝ)..1,
          f u * Real.rpow u (parameterSum p - 1) := by
  simpa [liouvilleValue] using gap8 n hn f hf p hp

end

end ProofGap.Exercise4217
