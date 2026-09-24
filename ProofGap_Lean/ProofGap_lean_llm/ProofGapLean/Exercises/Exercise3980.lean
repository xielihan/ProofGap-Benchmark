import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3980

noncomputable section

open MeasureTheory
open Filter
open scoped Interval
open scoped Topology

def unitDisk : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

def shiftedDisk (t : ℝ) : Set (ℝ × ℝ) :=
  {p | (p.1 - t) ^ 2 + (p.2 - t) ^ 2 ≤ 1}

def baseFunction (u v t : ℝ) : ℝ :=
  Real.sqrt ((u + t) ^ 2 + (v + t) ^ 2)

def derivativeKernel (u v t : ℝ) : ℝ :=
  (u + t + v + t) /
    Real.sqrt ((u + t) ^ 2 + (v + t) ^ 2)

def F (t : ℝ) : ℝ :=
  ∫ p in unitDisk, baseFunction p.1 p.2 t

def g (t : ℝ) : ℝ :=
  ∫ p in unitDisk, derivativeKernel p.1 p.2 t

def G (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, g s

theorem gap1 (t : ℝ) :
    F t =
      ∫ p in unitDisk,
        Real.sqrt ((p.1 + t) ^ 2 + (p.2 + t) ^ 2) := by
  rfl

private lemma baseFunction_hasDerivAt
    (u v t : ℝ)
    (h0 : (u + t) ^ 2 + (v + t) ^ 2 ≠ 0) :
    HasDerivAt (baseFunction u v)
      (derivativeKernel u v t) t := by
  have hinner :
      HasDerivAt
        (fun s : ℝ => (u + s) ^ 2 + (v + s) ^ 2)
        (2 * (u + t) + 2 * (v + t)) t := by
    convert
      ((((hasDerivAt_const t u).add (hasDerivAt_id t)).pow 2).add
        (((hasDerivAt_const t v).add (hasDerivAt_id t)).pow 2))
      using 1 <;> simp [id_eq] <;> ring
  have hpos :
      0 < (u + t) ^ 2 + (v + t) ^ 2 := by
    positivity
  have hsqrt := hinner.sqrt h0
  unfold baseFunction derivativeKernel
  convert hsqrt using 1
  field_simp [(Real.sqrt_pos.2 hpos).ne']
  ring

theorem gap5 (u v t : ℝ)
    (h0 : (u + t) ^ 2 + (v + t) ^ 2 ≠ 0) :
    deriv (baseFunction u v) t =
      derivativeKernel u v t := by
  exact (baseFunction_hasDerivAt u v t h0).deriv

theorem gap6 (u v t : ℝ) :
    |derivativeKernel u v t| ≤ Real.sqrt 2 := by
  unfold derivativeKernel
  by_cases hzero :
      (u + t) ^ 2 + (v + t) ^ 2 = 0
  · rw [hzero, Real.sqrt_zero, div_zero, abs_zero]
    positivity
  · have hpos :
        0 < (u + t) ^ 2 + (v + t) ^ 2 := by
      positivity
    have hsqrtpos :
        0 < Real.sqrt ((u + t) ^ 2 + (v + t) ^ 2) :=
      Real.sqrt_pos.2 hpos
    rw [abs_div, abs_of_pos hsqrtpos]
    apply (div_le_iff₀ hsqrtpos).2
    have hsq :
        |u + t + v + t| ^ 2 ≤
          (Real.sqrt 2 *
            Real.sqrt ((u + t) ^ 2 + (v + t) ^ 2)) ^ 2 := by
      rw [sq_abs, mul_pow, Real.sq_sqrt (by norm_num),
        Real.sq_sqrt hpos.le]
      nlinarith [sq_nonneg ((u + t) - (v + t))]
    exact (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))).mp hsq

private lemma unitDisk_measurable :
    MeasurableSet unitDisk := by
  unfold unitDisk
  exact measurableSet_le
    (show Measurable
      (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) by
      fun_prop)
    measurable_const

private lemma unitDisk_subset_box :
    unitDisk ⊆
      Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
  intro p hp
  unfold unitDisk at hp
  simp only [Set.mem_setOf_eq] at hp
  simp only [Set.mem_prod, Set.mem_Icc]
  constructor
  · constructor <;>
      nlinarith [sq_nonneg (p.1 + 1),
        sq_nonneg (p.1 - 1), sq_nonneg p.2]
  · constructor <;>
      nlinarith [sq_nonneg (p.2 + 1),
        sq_nonneg (p.2 - 1), sq_nonneg p.1]

private lemma unitDisk_isClosed :
    IsClosed unitDisk := by
  unfold unitDisk
  exact isClosed_le
    (show Continuous
      (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) by
      fun_prop)
    continuous_const

private lemma unitDisk_isCompact :
    IsCompact unitDisk :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    unitDisk_isClosed unitDisk_subset_box

private lemma unitDisk_measure_ne_top :
    volume unitDisk ≠ ⊤ := by
  exact ne_of_lt <|
    lt_of_le_of_lt (measure_mono unitDisk_subset_box)
      ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)

private noncomputable def kernelIndicator
    (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  unitDisk.indicator
    (fun q =>
      derivativeKernel q.1 q.2 t) p

private noncomputable def diskBound
    (p : ℝ × ℝ) : ℝ :=
  unitDisk.indicator (fun _ => Real.sqrt 2) p

private lemma kernelIndicator_integral (t : ℝ) :
    (∫ p, kernelIndicator t p) = g t := by
  rw [g, ← MeasureTheory.integral_indicator
    unitDisk_measurable]
  rfl

private lemma diskBound_integrable :
    Integrable diskBound := by
  unfold diskBound
  exact IntegrableOn.integrable_indicator
    (integrableOn_const
      (C := Real.sqrt 2) unitDisk_measure_ne_top)
    unitDisk_measurable

private lemma kernelIndicator_measurable (t : ℝ) :
    AEStronglyMeasurable (kernelIndicator t) := by
  unfold kernelIndicator derivativeKernel
  apply Measurable.aestronglyMeasurable
  apply Measurable.indicator _ unitDisk_measurable
  fun_prop

private lemma kernelIndicator_bound (t : ℝ) (p : ℝ × ℝ) :
    ‖kernelIndicator t p‖ ≤ diskBound p := by
  by_cases hp : p ∈ unitDisk
  · rw [kernelIndicator, diskBound,
      Set.indicator_of_mem hp, Set.indicator_of_mem hp,
      Real.norm_eq_abs]
    exact gap6 p.1 p.2 t
  · rw [kernelIndicator, diskBound,
      Set.indicator_of_notMem hp,
      Set.indicator_of_notMem hp, norm_zero]

private lemma ae_fst_ne_snd :
    ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ p.2 := by
  have hmeas :
      MeasurableSet {p : ℝ × ℝ | p.1 ≠ p.2} := by
    exact (measurableSet_eq_fun
      measurable_fst measurable_snd).compl
  change ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
    p.1 ≠ p.2
  rw [Measure.ae_prod_iff_ae_ae
    hmeas]
  filter_upwards with x
  filter_upwards [Measure.ae_ne volume x] with y hy
  exact hy.symm

private lemma kernelIndicator_continuous
    (p : ℝ × ℝ) (hpne : p.1 ≠ p.2) :
    Continuous (fun t => kernelIndicator t p) := by
  by_cases hp : p ∈ unitDisk
  · simp only [kernelIndicator,
      Set.indicator_of_mem hp]
    apply continuous_iff_continuousAt.2
    intro t
    have hpos :
        0 < (p.1 + t) ^ 2 + (p.2 + t) ^ 2 := by
      have hne :
          (p.1 + t) ^ 2 + (p.2 + t) ^ 2 ≠ 0 := by
        intro hz
        have h1 : p.1 + t = 0 := by
          nlinarith [sq_nonneg (p.1 + t),
            sq_nonneg (p.2 + t)]
        have h2 : p.2 + t = 0 := by
          nlinarith [sq_nonneg (p.1 + t),
            sq_nonneg (p.2 + t)]
        apply hpne
        linarith
      positivity
    unfold derivativeKernel
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact (Real.sqrt_pos.2 hpos).ne'
  · simpa [kernelIndicator, Set.indicator_of_notMem hp] using
      (continuous_const :
        Continuous (fun _ : ℝ => (0 : ℝ)))

private lemma g_continuous : Continuous g := by
  have hcont :
      Continuous (fun t : ℝ =>
        ∫ p, kernelIndicator t p) := by
    apply MeasureTheory.continuous_of_dominated
      (bound := diskBound)
    · intro t
      exact kernelIndicator_measurable t
    · intro t
      filter_upwards with p
      exact kernelIndicator_bound t p
    · exact diskBound_integrable
    · filter_upwards [ae_fst_ne_snd] with p hp
      exact kernelIndicator_continuous p hp
  simpa only [kernelIndicator_integral] using hcont

private lemma baseFunction_eq_complexNorm
    (u v t : ℝ) :
    baseFunction u v t =
      ‖((u + t : ℝ) : ℂ) +
        ((v + t : ℝ) : ℂ) * Complex.I‖ := by
  unfold baseFunction
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]
  ring

private lemma baseFunction_lipschitz
    (u v : ℝ) :
    LipschitzWith (Real.nnabs (Real.sqrt 2))
      (baseFunction u v) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [baseFunction_eq_complexNorm,
    baseFunction_eq_complexNorm]
  calc
    dist
        ‖((u + x : ℝ) : ℂ) +
            ((v + x : ℝ) : ℂ) * Complex.I‖
        ‖((u + y : ℝ) : ℂ) +
            ((v + y : ℝ) : ℂ) * Complex.I‖ ≤
        ‖(((u + x : ℝ) : ℂ) +
              ((v + x : ℝ) : ℂ) * Complex.I) -
          (((u + y : ℝ) : ℂ) +
              ((v + y : ℝ) : ℂ) * Complex.I)‖ :=
      dist_norm_norm_le _ _
    _ = Real.sqrt 2 * |x - y| := by
      rw [Complex.norm_def]
      rw [show
        Complex.normSq
            ((((u + x : ℝ) : ℂ) +
                ((v + x : ℝ) : ℂ) * Complex.I) -
              (((u + y : ℝ) : ℂ) +
                ((v + y : ℝ) : ℂ) * Complex.I)) =
          2 * (x - y) ^ 2 by
        simp [Complex.normSq_apply]
        ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_sq_eq_abs]
    _ =
        (Real.nnabs (Real.sqrt 2) : ℝ) *
          dist x y := by
      rw [Real.coe_nnabs,
        abs_of_nonneg (Real.sqrt_nonneg 2)]
      rfl

private noncomputable def baseIndicator
    (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  unitDisk.indicator
    (fun q => baseFunction q.1 q.2 t) p

private lemma baseIndicator_integral (t : ℝ) :
    (∫ p, baseIndicator t p) = F t := by
  rw [F, ← MeasureTheory.integral_indicator
    unitDisk_measurable]
  rfl

private lemma baseIndicator_measurable (t : ℝ) :
    AEStronglyMeasurable (baseIndicator t) := by
  unfold baseIndicator baseFunction
  apply Measurable.aestronglyMeasurable
  apply Measurable.indicator _ unitDisk_measurable
  fun_prop

private lemma baseIndicator_integrable (t : ℝ) :
    Integrable (baseIndicator t) := by
  unfold baseIndicator
  apply IntegrableOn.integrable_indicator
    (s := unitDisk) _ unitDisk_measurable
  apply ContinuousOn.integrableOn_compact
    unitDisk_isCompact
  unfold baseFunction
  fun_prop

private lemma baseIndicator_lipschitz
    (p : ℝ × ℝ) :
    LipschitzWith (Real.nnabs (diskBound p))
      (fun t => baseIndicator t p) := by
  by_cases hp : p ∈ unitDisk
  · simpa [baseIndicator, diskBound,
      Set.indicator_of_mem hp] using
        baseFunction_lipschitz p.1 p.2
  · simpa [baseIndicator, diskBound,
      Set.indicator_of_notMem hp] using
        (LipschitzWith.const 0 :
          LipschitzWith 0 (fun _ : ℝ => (0 : ℝ)))

private lemma baseIndicator_hasDerivAt
    (p : ℝ × ℝ) (hpne : p.1 ≠ p.2) (t : ℝ) :
    HasDerivAt (fun s => baseIndicator s p)
      (kernelIndicator t p) t := by
  by_cases hp : p ∈ unitDisk
  · simp only [baseIndicator, kernelIndicator,
      Set.indicator_of_mem hp]
    apply baseFunction_hasDerivAt
    intro hz
    have h1 : p.1 + t = 0 := by
      nlinarith [sq_nonneg (p.1 + t),
        sq_nonneg (p.2 + t)]
    have h2 : p.2 + t = 0 := by
      nlinarith [sq_nonneg (p.1 + t),
        sq_nonneg (p.2 + t)]
    apply hpne
    linarith
  · simpa [baseIndicator, kernelIndicator,
      Set.indicator_of_notMem hp] using
        (hasDerivAt_const t (0 : ℝ))

private lemma F_hasDerivAt (t : ℝ) :
    HasDerivAt F (g t) t := by
  have hresult :=
    hasDerivAt_integral_of_dominated_loc_of_lip
      (μ := volume) (F := baseIndicator)
      (F' := kernelIndicator t)
      (bound := diskBound)
      (x₀ := t) (s := Set.univ)
      (univ_mem : Set.univ ∈ 𝓝 t)
      (Filter.Eventually.of_forall
        (fun s => baseIndicator_measurable s))
      (baseIndicator_integrable t)
      (kernelIndicator_measurable t)
      (Filter.Eventually.of_forall fun p => by
        intro x _ y _
        exact baseIndicator_lipschitz p x y)
      diskBound_integrable
      (ae_fst_ne_snd.mono fun p hp =>
        baseIndicator_hasDerivAt p hp t)
  rw [kernelIndicator_integral] at hresult
  convert hresult.2 using 1
  ext s
  exact (baseIndicator_integral s).symm

theorem gap2 (t : ℝ) :
    deriv F t =
      ∫ p in unitDisk,
        derivativeKernel p.1 p.2 t := by
  rw [← g]
  exact (F_hasDerivAt t).deriv

private lemma shiftedDisk_measurable (t : ℝ) :
    MeasurableSet (shiftedDisk t) := by
  unfold shiftedDisk
  exact measurableSet_le
    (show Measurable
      (fun p : ℝ × ℝ =>
        (p.1 - t) ^ 2 + (p.2 - t) ^ 2) by
      fun_prop)
    measurable_const

private lemma translate_mem_shiftedDisk_iff
    (p : ℝ × ℝ) (t : ℝ) :
    p + (t, t) ∈ shiftedDisk t ↔
      p ∈ unitDisk := by
  unfold shiftedDisk unitDisk
  simp only [Set.mem_setOf_eq, Prod.fst_add,
    Prod.snd_add]
  ring_nf

theorem gap3 (t : ℝ) :
    (∫ p in unitDisk,
        derivativeKernel p.1 p.2 t) =
      ∫ p in shiftedDisk t,
        (p.1 + p.2) /
          Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
  let target : (ℝ × ℝ) → ℝ := fun p =>
    (shiftedDisk t).indicator
      (fun q =>
        (q.1 + q.2) /
          Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) p
  have htranslate :=
    integral_add_right_eq_self
      (μ := volume.prod volume) target (t, t)
  rw [← MeasureTheory.integral_indicator
      unitDisk_measurable,
    ← MeasureTheory.integral_indicator
      (shiftedDisk_measurable t)]
  calc
    (∫ p,
        unitDisk.indicator
          (fun q =>
            derivativeKernel q.1 q.2 t) p) =
        ∫ p, target (p + (t, t)) := by
      apply integral_congr_ae
      filter_upwards with p
      by_cases hp : p ∈ unitDisk
      · have hshift :
            p + (t, t) ∈ shiftedDisk t :=
          (translate_mem_shiftedDisk_iff p t).2 hp
        rw [Set.indicator_of_mem hp]
        simp only [target,
          Set.indicator_of_mem hshift,
          Prod.fst_add, Prod.snd_add]
        unfold derivativeKernel
        ring
      · have hshift :
            p + (t, t) ∉ shiftedDisk t := by
          intro h
          exact hp
            ((translate_mem_shiftedDisk_iff p t).1 h)
        rw [Set.indicator_of_notMem hp]
        simp only [target,
          Set.indicator_of_notMem hshift]
    _ = ∫ p, target p := htranslate
    _ =
        ∫ p,
          (shiftedDisk t).indicator
            (fun q =>
              (q.1 + q.2) /
                Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) p := by
      rfl

theorem gap7 (t : ℝ) :
    deriv G t = g t := by
  unfold G
  exact Continuous.deriv_integral g g_continuous 0 t

theorem gap8 (t : ℝ) :
    G t =
      ∫ s in (0 : ℝ)..t,
        ∫ p in unitDisk,
          derivativeKernel p.1 p.2 s := by
  rfl

private lemma kernelIndicator_prod_integrable
    (t : ℝ) :
    Integrable
      (fun z : ℝ × (ℝ × ℝ) =>
        kernelIndicator z.1 z.2)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod
        volume) := by
  have htimeMeasure :
      volume (Set.uIoc (0 : ℝ) t) ≠ ⊤ := by
    exact ne_of_lt <|
      lt_of_le_of_lt
        (measure_mono Set.uIoc_subset_uIcc)
        isCompact_Icc.measure_lt_top
  have htime :
      Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    integrableOn_const htimeMeasure
  have hdom :=
    htime.mul_prod diskBound_integrable
  apply hdom.mono'
  · apply Measurable.aestronglyMeasurable
    unfold kernelIndicator derivativeKernel
    apply Measurable.indicator
    · fun_prop
    · exact unitDisk_measurable.preimage measurable_snd
  · filter_upwards with z
    simpa using kernelIndicator_bound z.1 z.2

theorem gap9 (t : ℝ) :
    (∫ s in (0 : ℝ)..t,
        ∫ p in unitDisk,
          derivativeKernel p.1 p.2 s) =
      ∫ p in unitDisk,
        ∫ s in (0 : ℝ)..t,
          derivativeKernel p.1 p.2 s := by
  have hswap :=
    intervalIntegral_integral_swap
      (μ := volume) (a := (0 : ℝ)) (b := t)
      (f := fun s p => kernelIndicator s p)
      (kernelIndicator_prod_integrable t)
  calc
    (∫ s in (0 : ℝ)..t,
        ∫ p in unitDisk,
          derivativeKernel p.1 p.2 s) =
        ∫ s in (0 : ℝ)..t,
          ∫ p, kernelIndicator s p := by
      apply intervalIntegral.integral_congr
      intro s _
      change g s = ∫ p, kernelIndicator s p
      exact (kernelIndicator_integral s).symm
    _ =
        ∫ p,
          ∫ s in (0 : ℝ)..t,
            kernelIndicator s p := hswap
    _ =
        ∫ p in unitDisk,
          ∫ s in (0 : ℝ)..t,
            derivativeKernel p.1 p.2 s := by
      rw [← MeasureTheory.integral_indicator
        unitDisk_measurable]
      apply integral_congr_ae
      filter_upwards with p
      by_cases hp : p ∈ unitDisk
      · rw [Set.indicator_of_mem hp]
        apply intervalIntegral.integral_congr
        intro s _
        change kernelIndicator s p =
          derivativeKernel p.1 p.2 s
        simp [kernelIndicator, hp]
      · rw [Set.indicator_of_notMem hp]
        have hzero :
            (∫ s in (0 : ℝ)..t,
              kernelIndicator s p) = 0 := by
          simp [kernelIndicator, hp]
        exact hzero

theorem gap11 (u v t : ℝ) :
    (∫ s in (0 : ℝ)..t,
        derivativeKernel u v s) =
      baseFunction u v t - baseFunction u v 0 := by
  have hac :
      AbsolutelyContinuousOnInterval
        (baseFunction u v) 0 t := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    intro x _ y _
    exact baseFunction_lipschitz u v x y
  rw [← hac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (-u)] with s hs _
  have h0 :
      (u + s) ^ 2 + (v + s) ^ 2 ≠ 0 := by
    intro hz
    have hu : u + s = 0 := by
      nlinarith [sq_nonneg (u + s),
        sq_nonneg (v + s)]
    apply hs
    linarith
  exact (baseFunction_hasDerivAt u v s h0).deriv.symm

private lemma baseFunction_integrableOn (t : ℝ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        baseFunction p.1 p.2 t) unitDisk := by
  apply ContinuousOn.integrableOn_compact
    unitDisk_isCompact
  unfold baseFunction
  fun_prop

theorem gap12 (t : ℝ) :
    G t = F t - F 0 := by
  rw [gap8 t, gap9 t]
  simp_rw [gap11]
  unfold F
  rw [MeasureTheory.integral_sub
    (baseFunction_integrableOn t)
    (baseFunction_integrableOn 0)]

theorem gap13 (t : ℝ) :
    deriv F t = deriv G t := by
  rw [(F_hasDerivAt t).deriv]
  unfold G
  rw [Continuous.deriv_integral g g_continuous 0 t]

theorem gap14 (t : ℝ) :
    deriv G t = g t := by
  unfold G
  exact Continuous.deriv_integral g g_continuous 0 t

theorem gap4 (t : ℝ) :
    deriv F t =
      ∫ p in shiftedDisk t,
        (p.1 + p.2) /
          Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
  rw [gap2 t, gap3 t]

theorem gap10 (t : ℝ) :
    G t =
      ∫ p in unitDisk,
        ∫ s in (0 : ℝ)..t,
          derivativeKernel p.1 p.2 s := by
  rw [gap8 t, gap9 t]

theorem gap15 (t : ℝ) :
    deriv F t = g t := by
  rw [gap2]
  rfl

end

end ProofGap.Exercise3980
