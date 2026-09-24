import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3774

noncomputable section

open Filter MeasureTheory Complex Set
open scoped BigOperators Interval Topology FourierTransform

def fourierSine (f : ℝ → ℝ) (n : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), f x * Real.sin (n * x)

def IsPartition (t : ℕ → ℝ) (m : ℕ) (A : ℝ) : Prop :=
  t 0 = 0 ∧ t m = A ∧ ∀ k < m, t k < t (k + 1)

private def realExtension (f : ℝ → ℝ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator f

private def complexExtension (f : ℝ → ℝ) : ℝ → ℂ :=
  fun x => (realExtension f x : ℂ)

private def frequencyR (n : ℝ) : ℝ :=
  n / (2 * Real.pi)

private def fourierValueR (f : ℝ → ℝ) (n : ℝ) : ℂ :=
  ∫ x : ℝ, 𝐞 (-(x * frequencyR n)) • complexExtension f x

private theorem real_inner_eq_mul (x y : ℝ) :
    inner ℝ x y = x * y := by
  conv_lhs =>
    rw [show x = x • (1 : ℝ) by simp,
      show y = y • (1 : ℝ) by simp]
  rw [real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  norm_num

private theorem complexExtension_integrable
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0 : ℝ)) volume) :
    Integrable (complexExtension f) volume := by
  exact (hf.integrable_indicator measurableSet_Ioi).ofReal

private theorem fourierIntegrandR_integrable
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (n : ℝ) :
    Integrable
      (fun x : ℝ => 𝐞 (-(x * frequencyR n)) • complexExtension f x)
      volume := by
  simpa only [real_inner_eq_mul] using
    (Real.fourierIntegral_convergent_iff (f := complexExtension f)
      (frequencyR n)).2 (complexExtension_integrable f hf)

private theorem frequencyR_tendsto :
    Tendsto frequencyR atTop (cocompact ℝ) := by
  have hfreq : Tendsto frequencyR atTop atTop := by
    exact (tendsto_div_const_atTop_of_pos
      (show 0 < 2 * Real.pi by positivity)).2 tendsto_id
  exact hfreq.mono_right atTop_le_cocompact

private theorem fourierValueR_tendsto (f : ℝ → ℝ) :
    Tendsto (fourierValueR f) atTop (𝓝 0) := by
  exact (Real.tendsto_integral_exp_smul_cocompact
    (complexExtension f)).comp frequencyR_tendsto

private theorem pointwise_imaginaryR
    (f : ℝ → ℝ) (n x : ℝ) :
    Complex.im
      (𝐞 (-(x * frequencyR n)) • complexExtension f x) =
      -(realExtension f x * Real.sin (n * x)) := by
  rw [Circle.smul_def, Real.fourierChar_apply]
  change
    (Complex.exp
      ((2 * Real.pi * (-(x * frequencyR n)) : ℝ) * Complex.I) *
        (realExtension f x : ℂ)).im =
      -(realExtension f x * Real.sin (n * x))
  rw [Complex.mul_im, Complex.ofReal_im, mul_zero, zero_add,
    Complex.ofReal_re]
  rw [Complex.exp_im]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  dsimp [frequencyR]
  simp only [mul_zero, add_zero, mul_one]
  field_simp [hpi]
  rw [Real.sin_neg]
  simp [Real.exp_zero, mul_comm]

private theorem fourierValueR_im
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (n : ℝ) :
    (fourierValueR f n).im = -fourierSine f n := by
  have hint := fourierIntegrandR_integrable f hf n
  have him := integral_im hint
  unfold fourierValueR
  have him' :
      Complex.im
        (∫ x : ℝ, 𝐞 (-(x * frequencyR n)) • complexExtension f x) =
      ∫ x : ℝ,
        Complex.im
          (𝐞 (-(x * frequencyR n)) • complexExtension f x) := by
    simpa using him.symm
  rw [him']
  simp_rw [pointwise_imaginaryR f n]
  rw [integral_neg]
  congr 1
  have hind :
      (fun x : ℝ => realExtension f x * Real.sin (n * x)) =
      (Ioi (0 : ℝ)).indicator
        (fun x : ℝ => f x * Real.sin (n * x)) := by
    funext x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp [realExtension, hx]
    · simp [realExtension, hx]
  rw [hind, integral_indicator measurableSet_Ioi]
  rfl

private theorem fourierSine_tendsto
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0 : ℝ)) volume) :
    Tendsto (fourierSine f) atTop (𝓝 0) := by
  have him :
      Tendsto (fun n => (fourierValueR f n).im) atTop (𝓝 0) := by
    simpa using
      Complex.continuous_im.continuousAt.tendsto.comp
        (fourierValueR_tendsto f)
  have hneg := him.neg
  convert hneg using 1
  · funext n
    rw [fourierValueR_im f hf n]
    ring
  · simp

private def globalComplex (g : ℝ → ℝ) : ℝ → ℂ :=
  fun x => (g x : ℂ)

private def globalFourierValue (g : ℝ → ℝ) (n : ℝ) : ℂ :=
  ∫ x : ℝ, 𝐞 (-(x * frequencyR n)) • globalComplex g x

private theorem globalFourierIntegrable
    (g : ℝ → ℝ) (hg : Integrable g volume) (n : ℝ) :
    Integrable
      (fun x : ℝ => 𝐞 (-(x * frequencyR n)) • globalComplex g x)
      volume := by
  simpa only [real_inner_eq_mul] using
    (Real.fourierIntegral_convergent_iff (f := globalComplex g)
      (frequencyR n)).2 hg.ofReal

private theorem globalFourierTendsto (g : ℝ → ℝ) :
    Tendsto (globalFourierValue g) atTop (𝓝 0) := by
  exact (Real.tendsto_integral_exp_smul_cocompact
    (globalComplex g)).comp frequencyR_tendsto

private theorem globalPointwiseImaginary (g : ℝ → ℝ) (n x : ℝ) :
    Complex.im
      (𝐞 (-(x * frequencyR n)) • globalComplex g x) =
      -(g x * Real.sin (n * x)) := by
  rw [Circle.smul_def, Real.fourierChar_apply]
  change
    (Complex.exp
      ((2 * Real.pi * (-(x * frequencyR n)) : ℝ) * Complex.I) *
        (g x : ℂ)).im =
      -(g x * Real.sin (n * x))
  rw [Complex.mul_im, Complex.ofReal_im, mul_zero, zero_add,
    Complex.ofReal_re]
  rw [Complex.exp_im]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  dsimp [frequencyR]
  simp only [mul_zero, add_zero, mul_one]
  field_simp [hpi]
  rw [Real.sin_neg]
  simp [Real.exp_zero, mul_comm]

private theorem globalFourierValue_im
    (g : ℝ → ℝ) (hg : Integrable g volume) (n : ℝ) :
    (globalFourierValue g n).im =
      -(∫ x : ℝ, g x * Real.sin (n * x)) := by
  have hint := globalFourierIntegrable g hg n
  have him := integral_im hint
  unfold globalFourierValue
  have him' :
      Complex.im
        (∫ x : ℝ, 𝐞 (-(x * frequencyR n)) • globalComplex g x) =
      ∫ x : ℝ,
        Complex.im
          (𝐞 (-(x * frequencyR n)) • globalComplex g x) := by
    simpa using him.symm
  rw [him']
  simp_rw [globalPointwiseImaginary g n]
  rw [integral_neg]

private theorem globalSine_tendsto
    (g : ℝ → ℝ) (hg : Integrable g volume) :
    Tendsto (fun n : ℝ => ∫ x : ℝ, g x * Real.sin (n * x))
      atTop (𝓝 0) := by
  have him :
      Tendsto (fun n => (globalFourierValue g n).im) atTop (𝓝 0) := by
    simpa using
      Complex.continuous_im.continuousAt.tendsto.comp
        (globalFourierTendsto g)
  have hneg := him.neg
  convert hneg using 1
  · funext n
    rw [globalFourierValue_im g hg n]
    ring
  · simp

theorem gap1 (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      (∫ x in Set.Ioi A, |f x|) < ε / 3 := by
  have htail :
      Tendsto (fun A : ℝ => ∫ x in Ioi A, |f x|)
        atTop (𝓝 0) := by
    have hanti : Antitone (fun A : ℝ => Ioi A) := by
      intro a b hab x hx
      exact hab.trans_lt hx
    have ht := tendsto_setIntegral_of_antitone
      (f := fun x : ℝ => |f x|)
      (fun A : ℝ => measurableSet_Ioi) hanti ⟨0, hf.norm⟩
    have hinter : (⋂ A : ℝ, Ioi A) = ∅ := by
      ext x
      constructor
      · intro hx
        have hlarge := Set.mem_iInter.mp hx (x + 1)
        change x + 1 < x at hlarge
        linarith
      · intro hx
        simpa using hx
    rw [hinter] at ht
    simpa using ht
  have hevent :
      ∀ᶠ A : ℝ in atTop, (∫ x in Ioi A, |f x|) < ε / 3 :=
    (tendsto_order.1 htail).2 (ε / 3) (by positivity)
  obtain ⟨A, hbound, hApos⟩ :=
    (hevent.and (eventually_gt_atTop (0 : ℝ))).exists
  exact ⟨A, hApos, hbound⟩

theorem gap2 (A : ℝ) (hA : 0 < A) :
    ∃ t : ℕ → ℝ, t 0 = 0 ∧ t 1 = A := by
  refine ⟨fun k => A * (k : ℝ), ?_, ?_⟩
  · simp
  · simp

theorem gap3 (A : ℝ) (hA : 0 < A) :
    ∃ t : ℕ → ℝ, t 0 = 0 ∧ t 0 < t 1 ∧ t 1 = A := by
  refine ⟨fun k => A * (k : ℝ), by simp, ?_, by simp⟩
  simpa using hA

theorem gap4 (A : ℝ) (hA : 0 < A) :
    ∃ t : ℕ → ℝ, t 0 = 0 ∧ t 0 < t 1 ∧ t 1 < t 2 ∧ t 2 = A := by
  refine ⟨fun k => A * (k : ℝ) / 2, by norm_num, ?_, ?_, by norm_num⟩
  · simpa using (half_pos hA)
  · norm_num
    linarith

theorem gap5 (m : ℕ) (hm : 0 < m) (A : ℝ) (hA : 0 < A) :
    ∃ t : ℕ → ℝ, IsPartition t m A := by
  let t : ℕ → ℝ := fun k => A * (k : ℝ) / (m : ℝ)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  refine ⟨t, ?_⟩
  refine ⟨by simp [t], ?_, ?_⟩
  · simp [t, ne_of_gt hmR]
  · intro k hk
    dsimp [t]
    apply (div_lt_div_iff_of_pos_right hmR).2
    have hcast : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self k
    exact mul_lt_mul_of_pos_left hcast hA

theorem gap6 (m : ℕ) (hm : 0 < m) (A : ℝ) (hA : 0 < A) :
    ∃ t : ℕ → ℝ, IsPartition t m A ∧ t (m - 1) < t m := by
  obtain ⟨t, ht⟩ := gap5 m hm A hA
  refine ⟨t, ht, ?_⟩
  have hm1 : m - 1 < m := Nat.sub_lt (Nat.zero_lt_of_lt hm) Nat.zero_lt_one
  have hstep := ht.2.2 (m - 1) hm1
  simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')] using hstep

theorem gap7 (m : ℕ) (hm : 0 < m) (A : ℝ) (hA : 0 < A) :
    ∃ t : ℕ → ℝ, IsPartition t m A ∧ t m = A := by
  obtain ⟨t, ht⟩ := gap5 m hm A hA
  exact ⟨t, ht, ht.2.1⟩

theorem gap8 (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      (∫ x in Set.Ioi A, |f x|) < ε / 3 := by
  exact gap1 f hf ε hε

theorem gap9 (f : ℝ → ℝ) (n A : ℝ) (m : ℕ)
    (t : ℕ → ℝ) (c : ℕ → ℝ)
    (hf : ∀ k < m, IntervalIntegrable f volume (t k) (t (k + 1)))
    (hpart : IsPartition t m A) :
    (∫ x in (0 : ℝ)..A, f x * Real.sin (n * x)) =
      (∑ k ∈ Finset.range m,
        ∫ x in t k..t (k + 1), (f x - c k) * Real.sin (n * x)) +
      ∑ k ∈ Finset.range m,
        c k * ∫ x in t k..t (k + 1), Real.sin (n * x) := by
  have hsin : Continuous (fun x : ℝ => Real.sin (n * x)) := by
    fun_prop
  have hprod :
      ∀ k < m,
        IntervalIntegrable (fun x : ℝ => f x * Real.sin (n * x))
          volume (t k) (t (k + 1)) := by
    intro k hk
    exact (hf k hk).mul_continuousOn hsin.continuousOn
  have htel :=
    intervalIntegral.sum_integral_adjacent_intervals hprod
  rw [hpart.1, hpart.2.1] at htel
  have hdecomp :
      ∀ k < m,
        (∫ x in t k..t (k + 1), f x * Real.sin (n * x)) =
          (∫ x in t k..t (k + 1),
            (f x - c k) * Real.sin (n * x)) +
          c k * ∫ x in t k..t (k + 1), Real.sin (n * x) := by
    intro k hk
    have hsinI :
        IntervalIntegrable (fun x : ℝ => Real.sin (n * x))
          volume (t k) (t (k + 1)) :=
      hsin.intervalIntegrable _ _
    have hfc :
        IntervalIntegrable (fun x : ℝ => f x - c k)
          volume (t k) (t (k + 1)) :=
      (hf k hk).sub (continuous_const.intervalIntegrable _ _)
    have hrem :
        IntervalIntegrable
          (fun x : ℝ => (f x - c k) * Real.sin (n * x))
          volume (t k) (t (k + 1)) :=
      hfc.mul_continuousOn hsin.continuousOn
    have hconst :
        IntervalIntegrable
          (fun x : ℝ => c k * Real.sin (n * x))
          volume (t k) (t (k + 1)) :=
      hsinI.const_mul (c k)
    calc
      (∫ x in t k..t (k + 1), f x * Real.sin (n * x)) =
          ∫ x in t k..t (k + 1),
            ((f x - c k) * Real.sin (n * x) +
              c k * Real.sin (n * x)) := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = (∫ x in t k..t (k + 1),
            (f x - c k) * Real.sin (n * x)) +
          ∫ x in t k..t (k + 1),
            c k * Real.sin (n * x) := by
        exact intervalIntegral.integral_add hrem hconst
      _ = (∫ x in t k..t (k + 1),
            (f x - c k) * Real.sin (n * x)) +
          c k * ∫ x in t k..t (k + 1), Real.sin (n * x) := by
        rw [intervalIntegral.integral_const_mul]
  calc
    (∫ x in (0 : ℝ)..A, f x * Real.sin (n * x)) =
        ∑ k ∈ Finset.range m,
          ∫ x in t k..t (k + 1), f x * Real.sin (n * x) := htel.symm
    _ = ∑ k ∈ Finset.range m,
        ((∫ x in t k..t (k + 1),
            (f x - c k) * Real.sin (n * x)) +
          c k * ∫ x in t k..t (k + 1), Real.sin (n * x)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hdecomp k (Finset.mem_range.mp hk)
    _ = (∑ k ∈ Finset.range m,
          ∫ x in t k..t (k + 1),
            (f x - c k) * Real.sin (n * x)) +
        ∑ k ∈ Finset.range m,
          c k * ∫ x in t k..t (k + 1), Real.sin (n * x) := by
      rw [Finset.sum_add_distrib]

theorem gap10 (f : ℝ → ℝ) (n A : ℝ) (hn : 0 < n)
    (m : ℕ) (t : ℕ → ℝ) (c w : ℕ → ℝ)
    (hpart : IsPartition t m A)
    (hf : ∀ k < m, IntervalIntegrable f volume (t k) (t (k + 1)))
    (hrem : ∀ k < m,
      |∫ x in t k..t (k + 1), (f x - c k) * Real.sin (n * x)| ≤
        w k * (t (k + 1) - t k))
    (hsin : ∀ k < m,
      |∫ x in t k..t (k + 1), Real.sin (n * x)| ≤ 2 / n) :
    |∫ x in (0 : ℝ)..A, f x * Real.sin (n * x)| ≤
      (∑ k ∈ Finset.range m, w k * (t (k + 1) - t k)) +
        2 / n * ∑ k ∈ Finset.range m, |c k| := by
  have hsplit := gap9 f n A m t c hf hpart
  let R : ℕ → ℝ := fun k =>
    ∫ x in t k..t (k + 1), (f x - c k) * Real.sin (n * x)
  let C : ℕ → ℝ := fun k =>
    c k * ∫ x in t k..t (k + 1), Real.sin (n * x)
  have hR :
      |∑ k ∈ Finset.range m, R k| ≤
        ∑ k ∈ Finset.range m, w k * (t (k + 1) - t k) := by
    calc
      |∑ k ∈ Finset.range m, R k| ≤
          ∑ k ∈ Finset.range m, |R k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range m, w k * (t (k + 1) - t k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hrem k (Finset.mem_range.mp hk)
  have hC :
      |∑ k ∈ Finset.range m, C k| ≤
        2 / n * ∑ k ∈ Finset.range m, |c k| := by
    calc
      |∑ k ∈ Finset.range m, C k| ≤
          ∑ k ∈ Finset.range m, |C k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range m, |c k| * (2 / n) := by
        apply Finset.sum_le_sum
        intro k hk
        dsimp [C]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hsin k (Finset.mem_range.mp hk)) (abs_nonneg _)
      _ = 2 / n * ∑ k ∈ Finset.range m, |c k| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  rw [hsplit]
  change
    |(∑ k ∈ Finset.range m, R k) + ∑ k ∈ Finset.range m, C k| ≤ _
  exact (abs_add_le _ _).trans (add_le_add hR hC)

theorem gap11 (f : ℝ → ℝ) (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) A)) :
    ∃ m : ℕ, ∃ t w : ℕ → ℝ,
      IsPartition t m A ∧
        (∀ k < m, ∀ x ∈ Set.Icc (t k) (t (k + 1)),
          ∀ y ∈ Set.Icc (t k) (t (k + 1)), |f x - f y| ≤ w k) ∧
        (∑ k ∈ Finset.range m, w k * (t (k + 1) - t k)) < ε / 3 := by
  let osc : ℝ := ε / (6 * A)
  have hosc : 0 < osc := by
    dsimp [osc]
    positivity
  have huc :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hmod⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) osc hosc
  obtain ⟨m : ℕ, hmgt⟩ := exists_nat_gt (A / δ)
  have hmR : 0 < (m : ℝ) := by
    have hquot : 0 < A / δ := div_pos hA hδ
    exact hquot.trans hmgt
  have hm : 0 < m := by exact_mod_cast hmR
  have hcross : A < (m : ℝ) * δ :=
    (div_lt_iff₀ hδ).1 hmgt
  have hmesh : A / (m : ℝ) < δ := by
    apply (div_lt_iff₀ hmR).2
    nlinarith
  let t : ℕ → ℝ := fun k => A * (k : ℝ) / (m : ℝ)
  let w : ℕ → ℝ := fun _ => osc
  have hpart : IsPartition t m A := by
    refine ⟨by simp [t], ?_, ?_⟩
    · simp [t, ne_of_gt hmR]
    · intro k hk
      dsimp [t]
      apply (div_lt_div_iff_of_pos_right hmR).2
      have hcast : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self k
      exact mul_lt_mul_of_pos_left hcast hA
  have hoscillation :
      ∀ k < m, ∀ x ∈ Set.Icc (t k) (t (k + 1)),
        ∀ y ∈ Set.Icc (t k) (t (k + 1)), |f x - f y| ≤ w k := by
    intro k hk x hx y hy
    have hk1m : k + 1 ≤ m := Nat.succ_le_iff.mpr hk
    have htk0 : 0 ≤ t k := by
      dsimp [t]
      positivity
    have htk1A : t (k + 1) ≤ A := by
      dsimp [t]
      apply (div_le_iff₀ hmR).2
      have hcast : ((k + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hk1m
      nlinarith
    have hxI : x ∈ Set.Icc (0 : ℝ) A :=
      ⟨htk0.trans hx.1, hx.2.trans htk1A⟩
    have hyI : y ∈ Set.Icc (0 : ℝ) A :=
      ⟨htk0.trans hy.1, hy.2.trans htk1A⟩
    have hwidth : t (k + 1) - t k = A / (m : ℝ) := by
      dsimp [t]
      push_cast
      field_simp [ne_of_gt hmR]
      ring
    have habs : |x - y| ≤ t (k + 1) - t k := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hdist : dist x y < δ := by
      rw [Real.dist_eq]
      exact habs.trans_lt (by simpa [hwidth] using hmesh)
    have hout := hmod x hxI y hyI hdist
    rw [Real.dist_eq] at hout
    exact (by simpa [w, osc] using hout.le)
  have hstep :
      ∀ k : ℕ, t (k + 1) - t k = A / (m : ℝ) := by
    intro k
    dsimp [t]
    push_cast
    field_simp [ne_of_gt hmR]
    ring
  have hsum :
      (∑ k ∈ Finset.range m, w k * (t (k + 1) - t k)) =
        ε / 6 := by
    simp_rw [hstep]
    simp only [w, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    dsimp [osc]
    field_simp [ne_of_gt hA, ne_of_gt hmR]
  refine ⟨m, t, w, hpart, hoscillation, ?_⟩
  rw [hsum]
  linarith

theorem gap12 (c : ℕ → ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℝ, ∀ n : ℝ, N < n →
      2 / n * ∑ k ∈ Finset.range m, |c k| < ε / 3 := by
  let S : ℝ := ∑ k ∈ Finset.range m, |c k|
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  let N : ℝ := 6 * S / ε + 1
  refine ⟨N, ?_⟩
  intro n hn
  have hbase : 6 * S / ε < n := by
    dsimp [N] at hn
    linarith
  have hcross : 6 * S < n * ε :=
    (div_lt_iff₀ hε).1 hbase
  have hnpos : 0 < n := by
    have hNnonneg : 0 ≤ 6 * S / ε := by positivity
    dsimp [N] at hn
    linarith
  change 2 / n * S < ε / 3
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hnpos).2
  nlinarith

theorem gap13 (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℝ, ∀ n : ℝ, N < n → |fourierSine f n| < ε := by
  have ht := fourierSine_tendsto f hf
  have hl :
      ∀ᶠ n : ℝ in atTop, -ε < fourierSine f n :=
    (tendsto_order.1 ht).1 (-ε) (by linarith)
  have hu :
      ∀ᶠ n : ℝ in atTop, fourierSine f n < ε :=
    (tendsto_order.1 ht).2 ε hε
  rw [eventually_atTop] at hl hu
  obtain ⟨Nl, hNl⟩ := hl
  obtain ⟨Nu, hNu⟩ := hu
  refine ⟨max Nl Nu, ?_⟩
  intro n hn
  rw [abs_lt]
  exact ⟨hNl n ((le_max_left _ _).trans hn.le),
    hNu n ((le_max_right _ _).trans hn.le)⟩

theorem gap14 (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧
      (∫ x in Set.Ioc (0 : ℝ) η, |f x|) < ε / 3 := by
  let F : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun x => |f x|)
  have habsOn : IntegrableOn (fun x : ℝ => |f x|) (Ioi (0 : ℝ)) volume :=
    hf.norm
  have hF : Integrable F volume :=
    habsOn.integrable_indicator measurableSet_Ioi
  have hmeasure :
      Tendsto
        (volume ∘ fun η : ℝ => Ioc (0 : ℝ) η)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid :
        Tendsto (fun η : ℝ => η) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hof :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hid
    simpa [Function.comp_def, Real.volume_Ioc] using hof
  have htF :=
    hF.tendsto_setIntegral_nhds_zero hmeasure
  have heq :
      ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
        (∫ x in Ioc (0 : ℝ) η, F x) =
          ∫ x in Ioc (0 : ℝ) η, |f x| := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp [F, hx.1]
  have ht :
      Tendsto (fun η : ℝ => ∫ x in Ioc (0 : ℝ) η, |f x|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    htF.congr' heq
  have hbound :
      ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
        (∫ x in Ioc (0 : ℝ) η, |f x|) < ε / 3 :=
    (tendsto_order.1 ht).2 (ε / 3) (by positivity)
  obtain ⟨η, hηbound, hηpos⟩ :=
    (hbound.and self_mem_nhdsWithin).exists
  exact ⟨η, hηpos, hηbound⟩

theorem gap15 (f : ℝ → ℝ) (η A ε : ℝ) (hηA : η < A)
    (hf : IntegrableOn f (Set.Ioc η A)) (hε : 0 < ε) :
    ∃ N : ℝ, ∀ n : ℝ, N < n →
      |∫ x in η..A, f x * Real.sin (n * x)| < ε / 3 := by
  let g : ℝ → ℝ := (Ioc η A).indicator f
  have hg : Integrable g volume :=
    hf.integrable_indicator measurableSet_Ioc
  have ht0 := globalSine_tendsto g hg
  have heq :
      ∀ n : ℝ,
        (∫ x : ℝ, g x * Real.sin (n * x)) =
          ∫ x in η..A, f x * Real.sin (n * x) := by
    intro n
    rw [intervalIntegral.integral_of_le hηA.le]
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
    funext x
    by_cases hx : x ∈ Ioc η A
    · simp [g, hx]
    · simp [g, hx]
  have ht :
      Tendsto
        (fun n : ℝ => ∫ x in η..A, f x * Real.sin (n * x))
        atTop (𝓝 0) :=
    ht0.congr' (Filter.Eventually.of_forall heq)
  have hl :
      ∀ᶠ n : ℝ in atTop,
        -(ε / 3) < ∫ x in η..A, f x * Real.sin (n * x) :=
    (tendsto_order.1 ht).1 (-(ε / 3)) (by linarith)
  have hu :
      ∀ᶠ n : ℝ in atTop,
        (∫ x in η..A, f x * Real.sin (n * x)) < ε / 3 :=
    (tendsto_order.1 ht).2 (ε / 3) (by positivity)
  rw [eventually_atTop] at hl hu
  obtain ⟨Nl, hNl⟩ := hl
  obtain ⟨Nu, hNu⟩ := hu
  refine ⟨max Nl Nu, ?_⟩
  intro n hn
  rw [abs_lt]
  exact ⟨hNl n ((le_max_left _ _).trans hn.le),
    hNu n ((le_max_right _ _).trans hn.le)⟩

theorem gap16 (f : ℝ → ℝ) (η A n : ℝ) (hη : 0 ≤ η) (hηA : η ≤ A)
    (hf : IntegrableOn f (Set.Ioi (0 : ℝ))) :
    |fourierSine f n| ≤
      (∫ x in Set.Ioc (0 : ℝ) η, |f x|) +
        |∫ x in η..A, f x * Real.sin (n * x)| +
        ∫ x in Set.Ioi A, |f x| := by
  let h : ℝ → ℝ := fun x => f x * Real.sin (n * x)
  have hsinMeas : Measurable (fun x : ℝ => Real.sin (n * x)) := by
    fun_prop
  have hsinBound :
      ∀ x : ℝ, ‖Real.sin (n * x)‖ ≤ (1 : ℝ) := by
    intro x
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have hh : IntegrableOn h (Ioi (0 : ℝ)) volume := by
    have htmp := hf.bdd_mul hsinMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hsinBound)
    simpa [h, mul_comm] using htmp
  have hleftOn : IntegrableOn h (Ioc (0 : ℝ) η) volume :=
    hh.mono_set fun _ hx => hx.1
  have hmidOn : IntegrableOn h (Ioc η A) volume :=
    hh.mono_set fun _ hx => hη.trans_lt hx.1
  have hrightOn : IntegrableOn h (Ioi A) volume :=
    hh.mono_set fun _ hx => hη.trans hηA |>.trans_lt hx
  have hleftI : IntervalIntegrable h volume 0 η :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hη).2 hleftOn
  have hmidI : IntervalIntegrable h volume η A :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hηA).2 hmidOn
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hleftI hmidI
  have htail :=
    intervalIntegral.integral_interval_add_Ioi hh hrightOn
  have heq :
      fourierSine f n =
        (∫ x in (0 : ℝ)..η, h x) +
          (∫ x in η..A, h x) +
          ∫ x in Ioi A, h x := by
    unfold fourierSine
    change (∫ x in Ioi (0 : ℝ), h x) = _
    calc
      (∫ x in Ioi (0 : ℝ), h x) =
          (∫ x in (0 : ℝ)..A, h x) +
            ∫ x in Ioi A, h x := htail.symm
      _ = ((∫ x in (0 : ℝ)..η, h x) +
            ∫ x in η..A, h x) +
            ∫ x in Ioi A, h x := by rw [hsplit]
  have habsOn : IntegrableOn (fun x : ℝ => |f x|) (Ioi (0 : ℝ)) volume :=
    hf.norm
  have habsLeft :
      IntegrableOn (fun x : ℝ => |f x|) (Ioc (0 : ℝ) η) volume :=
    habsOn.mono_set fun _ hx => hx.1
  have habsRight :
      IntegrableOn (fun x : ℝ => |f x|) (Ioi A) volume :=
    habsOn.mono_set fun _ hx => hη.trans hηA |>.trans_lt hx
  have hleftBound :
      |∫ x in (0 : ℝ)..η, h x| ≤
        ∫ x in Ioc (0 : ℝ) η, |f x| := by
    rw [intervalIntegral.integral_of_le hη, ← Real.norm_eq_abs]
    calc
      ‖∫ x in Ioc (0 : ℝ) η, h x‖ ≤
          ∫ x in Ioc (0 : ℝ) η, ‖h x‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x in Ioc (0 : ℝ) η, |f x| := by
        apply integral_mono_ae
        · exact hleftOn.norm
        · exact habsLeft
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          dsimp [h]
          rw [abs_mul]
          exact mul_le_of_le_one_right
            (abs_nonneg (f x)) (Real.abs_sin_le_one _)
  have hrightBound :
      |∫ x in Ioi A, h x| ≤ ∫ x in Ioi A, |f x| := by
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ x in Ioi A, h x‖ ≤ ∫ x in Ioi A, ‖h x‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x in Ioi A, |f x| := by
        apply integral_mono_ae
        · exact hrightOn.norm
        · exact habsRight
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          dsimp [h]
          rw [abs_mul]
          exact mul_le_of_le_one_right
            (abs_nonneg (f x)) (Real.abs_sin_le_one _)
  rw [heq]
  change
    |(∫ x in (0 : ℝ)..η, h x) +
        (∫ x in η..A, h x) +
        ∫ x in Ioi A, h x| ≤ _
  have htri :
      |(∫ x in (0 : ℝ)..η, h x) +
          (∫ x in η..A, h x) +
          ∫ x in Ioi A, h x| ≤
        |∫ x in (0 : ℝ)..η, h x| +
          |∫ x in η..A, h x| +
          |∫ x in Ioi A, h x| := by
    linarith [abs_add_le
      (∫ x in (0 : ℝ)..η, h x)
      (∫ x in η..A, h x),
      abs_add_le
        ((∫ x in (0 : ℝ)..η, h x) +
          ∫ x in η..A, h x)
        (∫ x in Ioi A, h x)]
  exact htri.trans (add_le_add (add_le_add hleftBound le_rfl) hrightBound)

theorem gap17 (f : ℝ → ℝ) (η A n ε : ℝ)
    (hleft : (∫ x in Set.Ioc (0 : ℝ) η, |f x|) < ε / 3)
    (hmiddle : |∫ x in η..A, f x * Real.sin (n * x)| < ε / 3)
    (hright : (∫ x in Set.Ioi A, |f x|) < ε / 3) :
    (∫ x in Set.Ioc (0 : ℝ) η, |f x|) +
        |∫ x in η..A, f x * Real.sin (n * x)| +
        ∫ x in Set.Ioi A, |f x| < ε := by
  linarith

theorem gap18 (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℝ, ∀ n : ℝ, N < n → |fourierSine f n| < ε := by
  exact gap13 f hf ε hε

theorem gap19 (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi (0 : ℝ))) :
    Tendsto (fun n : ℕ => fourierSine f n) atTop (nhds 0) := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  exact (fourierSine_tendsto f hf).comp hcast

theorem gap20 (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi (0 : ℝ))) :
    Tendsto (fun n : ℕ => fourierSine f n) atTop (nhds 0) := by
  exact gap19 f hf

end

end ProofGap.Exercise3774
