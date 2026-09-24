import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2960

noncomputable section

open scoped BigOperators Interval

def sec (x : ℝ) : ℝ :=
  1 / Real.cos x

def coefficientIntegral (n : ℕ) : ℝ :=
  8 / Real.pi *
    ∫ x in 0..Real.pi / 4,
      Real.cos (4 * (n : ℝ) * x) / Real.cos x

def recurrenceIntegral (n : ℕ) : ℝ :=
  16 / Real.pi *
      (∫ x in 0..Real.pi / 4,
        (Real.cos ((4 * (n : ℝ) - 1) * x) -
          Real.cos ((4 * (n : ℝ) - 3) * x))) +
    coefficientIntegral (n - 1)

def recurrenceStep (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  16 / Real.pi *
      (Real.sqrt 2 * (-1 : ℝ) ^ n /
        ((4 * (n : ℝ) - 3) * (4 * (n : ℝ) - 1))) +
    c (n - 1)

def coefficientClosed (n : ℕ) : ℝ :=
  16 * Real.sqrt 2 / Real.pi *
      (∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ k /
          ((4 * (k : ℝ) - 3) * (4 * (k : ℝ) - 1))) +
    8 / Real.pi * Real.log (1 + Real.sqrt 2)

def fourierCoefficient (n : ℕ) : ℝ :=
  8 / Real.pi * Real.log (1 + Real.sqrt 2) -
    16 * Real.sqrt 2 / Real.pi *
      ∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ (k - 1) /
          ((4 * (k : ℝ) - 3) * (4 * (k : ℝ) - 1))

def fourierSeries (x : ℝ) : ℝ :=
  4 / Real.pi * Real.log (1 + Real.sqrt 2) +
    ∑' k : ℕ,
      fourierCoefficient (k + 1) *
        Real.cos (4 * (k + 1 : ℝ) * x)

def tanPrimitive (x : ℝ) : ℝ :=
  8 / Real.pi *
    Real.log |Real.tan (x / 2 + Real.pi / 4)|

def ratioPrimitive (x : ℝ) : ℝ :=
  8 / Real.pi *
    Real.log |(1 + Real.sin x) / Real.cos x|

def evalOnQuarter (g : ℝ → ℝ) : ℝ :=
  g (Real.pi / 4) - g 0

private def logSecPrimitive (x : ℝ) : ℝ :=
  8 / Real.pi *
    (Real.log (1 + Real.sin x) - Real.log (Real.cos x))

private theorem hasDerivAt_logSecPrimitive
    (x : ℝ) (hnum : 1 + Real.sin x ≠ 0) (hcos : Real.cos x ≠ 0) :
    HasDerivAt logSecPrimitive (8 / Real.pi * (1 / Real.cos x)) x := by
  have hlognum :
      HasDerivAt (fun y : ℝ => Real.log (1 + Real.sin y))
        (Real.cos x / (1 + Real.sin x)) x := by
    convert (Real.hasDerivAt_sin x).const_add 1 |>.log hnum using 1
  have hlogcos :
      HasDerivAt (fun y : ℝ => Real.log (Real.cos y))
        (-Real.sin x / Real.cos x) x := by
    exact (Real.hasDerivAt_cos x).log hcos
  convert (hlognum.sub hlogcos).const_mul (8 / Real.pi) using 1
  dsimp [logSecPrimitive]
  field_simp [hnum, hcos]
  nlinarith [Real.sin_sq_add_cos_sq x]

private theorem integral_sec_quarter_eq_sub :
    8 / Real.pi * (∫ x in 0..Real.pi / 4, sec x) =
      logSecPrimitive (Real.pi / 4) - logSecPrimitive 0 := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] at hx
    have hsin : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx.1
        (hx.2.trans (by linarith [Real.pi_pos]))
    have hcospos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by
        linarith [hx.2, Real.pi_pos]⟩
    exact hasDerivAt_logSecPrimitive x (by linarith) hcospos.ne'
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] at hx
    have hcospos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by
        linarith [hx.2, Real.pi_pos]⟩
    exact (continuousAt_const.mul
      (continuousAt_const.div Real.continuous_cos.continuousAt
        hcospos.ne')).continuousWithinAt

private theorem logSecPrimitive_eval :
    logSecPrimitive (Real.pi / 4) - logSecPrimitive 0 =
      8 / Real.pi * Real.log (1 + Real.sqrt 2) := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hratio :
      (1 + Real.sqrt 2 / 2) / (Real.sqrt 2 / 2) =
        1 + Real.sqrt 2 := by
    field_simp [hsqrt.ne']
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold logSecPrimitive
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
  simp only [Real.sin_zero, Real.cos_zero, add_zero, Real.log_one,
    sub_zero, mul_zero]
  rw [← Real.log_div (by positivity) (by positivity), hratio]

private theorem tan_three_pi_div_eight :
    Real.tan (3 * Real.pi / 8) =
      (1 + Real.sin (Real.pi / 4)) / Real.cos (Real.pi / 4) := by
  have harg : 3 * Real.pi / 8 = Real.pi / 8 + Real.pi / 4 := by ring
  have hcos3 : Real.cos (3 * Real.pi / 8) ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hratioDouble :
      (1 + Real.sin (Real.pi / 4)) / Real.cos (Real.pi / 4) =
        (1 + 2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8)) /
          (Real.cos (Real.pi / 8) ^ 2 - Real.sin (Real.pi / 8) ^ 2) := by
    rw [show Real.pi / 4 = 2 * (Real.pi / 8) by ring,
      Real.sin_two_mul, Real.cos_two_mul']
  rw [Real.tan_eq_sin_div_cos, div_eq_iff hcos3]
  rw [harg, Real.sin_add, Real.cos_add]
  rw [hratioDouble, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hcosQuarter : Real.cos (Real.pi / 8) ^ 2 -
      Real.sin (Real.pi / 8) ^ 2 ≠ 0 := by
    rw [← Real.cos_two_mul', show 2 * (Real.pi / 8) =
      Real.pi / 4 by ring, Real.cos_pi_div_four]
    positivity
  have hnum : 1 + 2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) =
      (Real.sin (Real.pi / 8) + Real.cos (Real.pi / 8)) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 8)]
  rw [hnum]
  field_simp [hcosQuarter, show Real.sqrt 2 ≠ 0 by positivity]
  ring

private theorem tanPrimitive_eval :
    evalOnQuarter tanPrimitive =
      8 / Real.pi * Real.log (1 + Real.sqrt 2) := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hratio :
      (1 + Real.sqrt 2 / 2) / (Real.sqrt 2 / 2) =
        1 + Real.sqrt 2 := by
    field_simp [hsqrt.ne']
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold evalOnQuarter tanPrimitive
  rw [show Real.pi / 4 / 2 + Real.pi / 4 = 3 * Real.pi / 8 by ring,
    tan_three_pi_div_eight, Real.sin_pi_div_four,
    Real.cos_pi_div_four, hratio]
  simp [Real.tan_pi_div_four, abs_of_pos (by positivity :
    (0 : ℝ) < 1 + Real.sqrt 2)]

private theorem ratioPrimitive_eval :
    evalOnQuarter ratioPrimitive =
      8 / Real.pi * Real.log (1 + Real.sqrt 2) := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hratio :
      (1 + Real.sqrt 2 / 2) / (Real.sqrt 2 / 2) =
        1 + Real.sqrt 2 := by
    field_simp [hsqrt.ne']
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold evalOnQuarter ratioPrimitive
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four, hratio]
  simp [abs_of_pos (by positivity : (0 : ℝ) < 1 + Real.sqrt 2)]

private theorem integral_cos_mul (q : ℝ) (hq : q ≠ 0) (u v : ℝ) :
    (∫ x in u..v, Real.cos (q * x)) =
      Real.sin (q * v) / q - Real.sin (q * u) / q := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hinner : HasDerivAt (fun y : ℝ => q * y) q x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul q
    convert ((Real.hasDerivAt_sin (q * x)).comp x hinner).div_const q using 1
    field_simp [hq]
  · exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable u v

private theorem coefficientIntegral_zero_eval :
    coefficientIntegral 0 =
      8 / Real.pi * Real.log (1 + Real.sqrt 2) := by
  have hint :
      (∫ x in 0..Real.pi / 4,
        Real.cos (0 * x) / Real.cos x) =
        ∫ x in 0..Real.pi / 4, sec x := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp [sec]
  unfold coefficientIntegral
  norm_num only [Nat.cast_zero]
  rw [hint, integral_sec_quarter_eq_sub, logSecPrimitive_eval]

private theorem coefficientIntegral_recurrence (n : ℕ) (hn : 1 ≤ n) :
    coefficientIntegral n =
      16 / Real.pi *
        (∫ x in 0..Real.pi / 4,
          (Real.cos ((4 * (n : ℝ) - 1) * x) -
            Real.cos ((4 * (n : ℝ) - 3) * x))) +
      coefficientIntegral (n - 1) := by
  have hnsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hpoint (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) (Real.pi / 4)) :
      Real.cos (4 * (n : ℝ) * x) / Real.cos x =
        2 * (Real.cos ((4 * (n : ℝ) - 1) * x) -
          Real.cos ((4 * (n : ℝ) - 3) * x)) +
        Real.cos (4 * ((n - 1 : ℕ) : ℝ) * x) / Real.cos x := by
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] at hx
    have hcos : Real.cos x ≠ 0 := ne_of_gt <|
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by
        linarith [hx.2, Real.pi_pos]⟩
    have hid :
        Real.cos (4 * (n : ℝ) * x) -
            Real.cos (4 * (n : ℝ) * x - 4 * x) =
          2 * (Real.cos (4 * (n : ℝ) * x - x) -
            Real.cos (4 * (n : ℝ) * x - 3 * x)) * Real.cos x := by
      rw [Real.cos_sub_cos]
      rw [show (4 * (n : ℝ) * x +
            (4 * (n : ℝ) * x - 4 * x)) / 2 =
          4 * (n : ℝ) * x - 2 * x by ring]
      rw [show (4 * (n : ℝ) * x -
            (4 * (n : ℝ) * x - 4 * x)) / 2 = 2 * x by ring]
      rw [Real.cos_sub_cos]
      rw [show ((4 * (n : ℝ) * x - x) +
            (4 * (n : ℝ) * x - 3 * x)) / 2 =
          4 * (n : ℝ) * x - 2 * x by ring]
      rw [show ((4 * (n : ℝ) * x - x) -
            (4 * (n : ℝ) * x - 3 * x)) / 2 = x by ring,
        Real.sin_two_mul]
      ring
    rw [show 4 * (n : ℝ) * x - 4 * x =
      4 * ((n - 1 : ℕ) : ℝ) * x by rw [hnsub]; ring] at hid
    field_simp [hcos]
    ring_nf at hid ⊢
    linarith
  have hg : IntervalIntegrable
      (fun x : ℝ => 2 * (Real.cos ((4 * (n : ℝ) - 1) * x) -
        Real.cos ((4 * (n : ℝ) - 3) * x)))
      MeasureTheory.volume 0 (Real.pi / 4) :=
    (continuous_const.mul
      ((Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).sub
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)))).intervalIntegrable _ _
  have hp : IntervalIntegrable
      (fun x : ℝ => Real.cos (4 * ((n - 1 : ℕ) : ℝ) * x) /
        Real.cos x) MeasureTheory.volume 0 (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] at hx
    have hcos : Real.cos x ≠ 0 := ne_of_gt <|
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by
        linarith [hx.2, Real.pi_pos]⟩
    exact ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).continuousAt.div
        Real.continuous_cos.continuousAt hcos).continuousWithinAt
  unfold coefficientIntegral
  rw [intervalIntegral.integral_congr hpoint,
    intervalIntegral.integral_add hg hp,
    intervalIntegral.integral_const_mul]
  ring

private theorem coefficientStepIntegral_eval (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in 0..Real.pi / 4,
      (Real.cos ((4 * (n : ℝ) - 1) * x) -
        Real.cos ((4 * (n : ℝ) - 3) * x))) =
      (-1 : ℝ) ^ (n - 1) / (4 * (n : ℝ) - 1) *
          Real.sin (Real.pi / 4) -
        (-1 : ℝ) ^ (n - 1) / (4 * (n : ℝ) - 3) *
          Real.sin (3 * Real.pi / 4) := by
  cases n with
  | zero => omega
  | succ m =>
      let q₁ : ℝ := 4 * ((m + 1 : ℕ) : ℝ) - 1
      let q₃ : ℝ := 4 * ((m + 1 : ℕ) : ℝ) - 3
      have hq₁ : q₁ ≠ 0 := by
        dsimp [q₁]
        push_cast
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      have hq₃ : q₃ ≠ 0 := by
        dsimp [q₃]
        push_cast
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      have hi₁ : IntervalIntegrable (fun x : ℝ => Real.cos (q₁ * x))
          MeasureTheory.volume 0 (Real.pi / 4) :=
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).intervalIntegrable _ _
      have hi₃ : IntervalIntegrable (fun x : ℝ => Real.cos (q₃ * x))
          MeasureTheory.volume 0 (Real.pi / 4) :=
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).intervalIntegrable _ _
      have hangle₁ : q₁ * (Real.pi / 4) =
          ((m + 1 : ℕ) : ℝ) * Real.pi - Real.pi / 4 := by
        dsimp [q₁]
        ring
      have hangle₃ : q₃ * (Real.pi / 4) =
          ((m + 1 : ℕ) : ℝ) * Real.pi - 3 * Real.pi / 4 := by
        dsimp [q₃]
        ring
      change (∫ x in 0..Real.pi / 4,
        Real.cos (q₁ * x) - Real.cos (q₃ * x)) = _
      rw [intervalIntegral.integral_sub hi₁ hi₃,
        integral_cos_mul q₁ hq₁ 0 (Real.pi / 4),
        integral_cos_mul q₃ hq₃ 0 (Real.pi / 4),
        hangle₁, hangle₃,
        Real.sin_nat_mul_pi_sub, Real.sin_nat_mul_pi_sub]
      simp only [mul_zero, Real.sin_zero, zero_div, Nat.add_sub_cancel,
        pow_succ]
      dsimp [q₁, q₃]
      ring

theorem gap1 (f : ℝ → ℝ)
    (hf : ∀ x, f x = sec x) :
    ContinuousOn f (Set.Ioo (-Real.pi / 4) (Real.pi / 4)) := by
  rw [funext hf]
  intro x hx
  apply ContinuousAt.continuousWithinAt
  unfold sec
  exact continuousAt_const.div Real.continuous_cos.continuousAt
    (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by
      linarith [hx.1, Real.pi_pos], by
      linarith [hx.2, Real.pi_pos]⟩))

theorem gap2 (f : ℝ → ℝ) (hf : ∀ x, f x = sec x) :
    Function.Even f := by
  intro x
  rw [hf, hf]
  simp [sec]

theorem gap3 (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = 0) :
    ∀ n : ℕ, 1 ≤ n → s n = 0 := by
  exact hs

theorem gap4 (c : ℕ → ℝ)
    (hc : c 0 =
      8 / Real.pi * ∫ x in 0..Real.pi / 4, sec x) :
    c 0 =
      8 / Real.pi * ∫ x in 0..Real.pi / 4, sec x := by
  exact hc

theorem gap5 (c : ℕ → ℝ)
    (hc : c 0 =
      8 / Real.pi * ∫ x in 0..Real.pi / 4, sec x) :
    c 0 = evalOnQuarter tanPrimitive := by
  rw [hc, integral_sec_quarter_eq_sub, logSecPrimitive_eval,
    tanPrimitive_eval]

theorem gap6 :
    evalOnQuarter tanPrimitive = evalOnQuarter ratioPrimitive := by
  rw [tanPrimitive_eval, ratioPrimitive_eval]

theorem gap7 :
    evalOnQuarter ratioPrimitive =
      8 / Real.pi * Real.log (1 + Real.sqrt 2) := by
  exact ratioPrimitive_eval

theorem gap8 (c : ℕ → ℝ)
    (hc : c 0 =
      8 / Real.pi * ∫ x in 0..Real.pi / 4, sec x) :
    c 0 = 8 / Real.pi * Real.log (1 + Real.sqrt 2) := by
  rw [gap5 c hc, gap6, gap7]

theorem gap9 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n := by
  exact hc

theorem gap10 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      Real.cos (4 * (n : ℝ) * x) -
          Real.cos (4 * (n : ℝ) * x - 4 * x) =
        -2 * Real.sin (4 * (n : ℝ) * x - 2 * x) *
          Real.sin (2 * x) := by
  intro n hn x
  rw [Real.cos_sub_cos]
  congr 2 <;> ring

theorem gap11 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      -2 * Real.sin (4 * (n : ℝ) * x - 2 * x) *
          Real.sin (2 * x) =
        2 * (Real.cos (4 * (n : ℝ) * x - x) -
          Real.cos (4 * (n : ℝ) * x - 3 * x)) *
          Real.cos x := by
  intro n hn x
  rw [Real.cos_sub_cos]
  rw [show ((4 * (n : ℝ) * x - x) +
        (4 * (n : ℝ) * x - 3 * x)) / 2 =
      4 * (n : ℝ) * x - 2 * x by ring]
  rw [show ((4 * (n : ℝ) * x - x) -
        (4 * (n : ℝ) * x - 3 * x)) / 2 = x by ring]
  rw [Real.sin_two_mul]
  ring

theorem gap12 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      Real.cos (4 * (n : ℝ) * x) -
          Real.cos (4 * (n : ℝ) * x - 4 * x) =
        2 * (Real.cos (4 * (n : ℝ) * x - x) -
          Real.cos (4 * (n : ℝ) * x - 3 * x)) *
          Real.cos x := by
  intro n hn x
  rw [gap10 n hn x, gap11 n hn x]

theorem gap13 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = recurrenceIntegral n := by
  intro n hn
  rw [hc n hn]
  simpa [recurrenceIntegral] using coefficientIntegral_recurrence n hn

theorem gap14 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n)
    (hc0 : c 0 = 8 / Real.pi * Real.log (1 + Real.sqrt 2)) :
    ∀ n : ℕ, 1 ≤ n →
      c n =
        16 / Real.pi *
            (((-1 : ℝ) ^ (n - 1) / (4 * (n : ℝ) - 1)) *
                Real.sin (Real.pi / 4) -
              ((-1 : ℝ) ^ (n - 1) / (4 * (n : ℝ) - 3)) *
                Real.sin (3 * Real.pi / 4)) +
          c (n - 1) := by
  intro n hn
  have hprev : coefficientIntegral (n - 1) = c (n - 1) := by
    by_cases hnone : n = 1
    · subst n
      change coefficientIntegral 0 = c 0
      rw [coefficientIntegral_zero_eval, hc0]
    · exact (hc (n - 1) (by omega)).symm
  calc
    c n = coefficientIntegral n := hc n hn
    _ = 16 / Real.pi *
          (∫ x in 0..Real.pi / 4,
            (Real.cos ((4 * (n : ℝ) - 1) * x) -
              Real.cos ((4 * (n : ℝ) - 3) * x))) +
          coefficientIntegral (n - 1) :=
      coefficientIntegral_recurrence n hn
    _ = 16 / Real.pi *
            (((-1 : ℝ) ^ (n - 1) / (4 * (n : ℝ) - 1)) *
                Real.sin (Real.pi / 4) -
              ((-1 : ℝ) ^ (n - 1) / (4 * (n : ℝ) - 3)) *
                Real.sin (3 * Real.pi / 4)) +
          c (n - 1) := by
      rw [coefficientStepIntegral_eval n hn, hprev]

theorem gap15 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n)
    (hc0 : c 0 = 8 / Real.pi * Real.log (1 + Real.sqrt 2)) :
    ∀ n : ℕ, 1 ≤ n → c n = recurrenceStep c n := by
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
      rw [gap14 c hc hc0 (m + 1) hn]
      unfold recurrenceStep
      have hsin3 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
          Real.sin_pi_sub, Real.sin_pi_div_four]
      rw [Real.sin_pi_div_four, hsin3]
      simp only [Nat.add_sub_cancel, pow_succ]
      have hq₁ : 4 * (((m + 1 : ℕ) : ℝ)) - 1 ≠ 0 := by
        push_cast
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      have hq₃ : 4 * (((m + 1 : ℕ) : ℝ)) - 3 ≠ 0 := by
        push_cast
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      field_simp [Real.pi_ne_zero, hq₁, hq₃]
      ring

theorem gap16 (c : ℕ → ℝ)
    (hc : c 0 = 8 / Real.pi * Real.log (1 + Real.sqrt 2))
    (hrec : ∀ n : ℕ, 1 ≤ n → c n = recurrenceStep c n) :
    ∀ n : ℕ, 1 ≤ n →
      c n =
        16 * Real.sqrt 2 / Real.pi *
            (∑ k ∈ Finset.Icc 1 n,
              (-1 : ℝ) ^ k /
                ((4 * (k : ℝ) - 3) * (4 * (k : ℝ) - 1))) +
          c 0 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      rw [hrec 1 (by omega)]
      simp [recurrenceStep]
      ring
  | succ n hn ih =>
      rw [hrec (n + 1) (by omega)]
      unfold recurrenceStep
      simp only [Nat.add_sub_cancel]
      rw [ih]
      rw [Finset.sum_Icc_succ_top (by omega)]
      ring

theorem gap17 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = coefficientClosed n := by
  intro n hn
  have hrec : ∀ m : ℕ, 1 ≤ m →
      coefficientIntegral m = recurrenceStep coefficientIntegral m :=
    gap15 coefficientIntegral (fun _ _ => rfl) coefficientIntegral_zero_eval
  calc
    c n = coefficientIntegral n := hc n hn
    _ = 16 * Real.sqrt 2 / Real.pi *
          (∑ k ∈ Finset.Icc 1 n,
            (-1 : ℝ) ^ k /
              ((4 * (k : ℝ) - 3) * (4 * (k : ℝ) - 1))) +
        coefficientIntegral 0 :=
      gap16 coefficientIntegral coefficientIntegral_zero_eval hrec n hn
    _ = coefficientClosed n := by
      rw [coefficientIntegral_zero_eval]
      rfl

private theorem quarter_period_pos :
    (0 : ℝ) < Real.pi / 4 - -Real.pi / 4 := by
  linarith [Real.pi_pos]

private local instance quarterPeriodFact :
    Fact (0 < Real.pi / 4 - -Real.pi / 4) := ⟨quarter_period_pos⟩

private def secC (x : ℝ) : ℂ := (sec x : ℝ)

private def periodizedSec :
    AddCircle (Real.pi / 4 - -Real.pi / 4) → ℂ :=
  letI : Fact (0 < Real.pi / 4 - -Real.pi / 4) := ⟨quarter_period_pos⟩
  AddCircle.liftIco (Real.pi / 4 - -Real.pi / 4) (-Real.pi / 4) secC

private theorem continuous_secC_on :
    ContinuousOn secC (Set.Icc (-Real.pi / 4) (Real.pi / 4)) := by
  intro x hx
  unfold secC sec
  apply ContinuousAt.continuousWithinAt
  exact Complex.continuous_ofReal.continuousAt.comp
    (continuousAt_const.div Real.continuous_cos.continuousAt
      (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by
        linarith [hx.1, Real.pi_pos], by
        linarith [hx.2, Real.pi_pos]⟩)))

private theorem continuous_periodizedSec : Continuous periodizedSec := by
  letI : Fact (0 < Real.pi / 4 - -Real.pi / 4) := ⟨quarter_period_pos⟩
  unfold periodizedSec
  apply AddCircle.liftIco_continuous
  · change ((sec (-Real.pi / 4) : ℝ) : ℂ) =
      ((sec (-Real.pi / 4 +
        (Real.pi / 4 - -Real.pi / 4)) : ℝ) : ℂ)
    norm_cast
    rw [show -Real.pi / 4 + (Real.pi / 4 - -Real.pi / 4) =
      Real.pi / 4 by ring]
    unfold sec
    rw [show -Real.pi / 4 = -(Real.pi / 4) by ring, Real.cos_neg]
  · convert continuous_secC_on using 1 <;> ring


private theorem fourier_neg_nat_mul_secC (n : ℕ) (x : ℝ) :
    fourier (-(n : ℤ))
        (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) * secC x =
      ((Real.cos (4 * (n : ℝ) * x) / Real.cos x : ℝ) : ℂ) -
        ((Real.sin (4 * (n : ℝ) * x) / Real.cos x : ℝ) : ℂ) *
          Complex.I := by
  rw [fourier_coe_apply]
  have hexp :
      2 * (Real.pi : ℂ) * Complex.I * ((-(n : ℤ) : ℤ) : ℂ) * (x : ℂ) /
          ((Real.pi / 4 - -Real.pi / 4 : ℝ) : ℂ) =
        (-((4 * (n : ℝ) * x : ℝ) : ℂ)) * Complex.I := by
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  rw [hexp, Complex.exp_mul_I]
  simp [secC, sec]
  ring

private theorem integral_even_symmetric (f : ℝ → ℝ)
    (hf : Function.Even f)
    (hneg : IntervalIntegrable f MeasureTheory.volume (-Real.pi / 4) 0)
    (hpos : IntervalIntegrable f MeasureTheory.volume 0 (Real.pi / 4)) :
    (∫ x in -Real.pi / 4..Real.pi / 4, f x) =
      2 * ∫ x in 0..Real.pi / 4, f x := by
  have hleft : (∫ x in -Real.pi / 4..0, f x) =
      ∫ x in 0..Real.pi / 4, f x := by
    calc
      (∫ x in -Real.pi / 4..0, f x) =
          ∫ x in 0..Real.pi / 4, f (-x) := by
        convert (intervalIntegral.integral_comp_neg (a := 0)
          (b := Real.pi / 4) f).symm using 1 <;> ring
      _ = ∫ x in 0..Real.pi / 4, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hf x
  rw [← intervalIntegral.integral_add_adjacent_intervals hneg hpos,
    hleft]
  ring

private theorem integral_odd_symmetric (f : ℝ → ℝ)
    (hf : Function.Odd f)
    (hneg : IntervalIntegrable f MeasureTheory.volume (-Real.pi / 4) 0)
    (hpos : IntervalIntegrable f MeasureTheory.volume 0 (Real.pi / 4)) :
    (∫ x in -Real.pi / 4..Real.pi / 4, f x) = 0 := by
  have hleft : (∫ x in -Real.pi / 4..0, f x) =
      -(∫ x in 0..Real.pi / 4, f x) := by
    calc
      (∫ x in -Real.pi / 4..0, f x) =
          ∫ x in 0..Real.pi / 4, f (-x) := by
        convert (intervalIntegral.integral_comp_neg (a := 0)
          (b := Real.pi / 4) f).symm using 1 <;> ring
      _ = ∫ x in 0..Real.pi / 4, -f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hf x
      _ = -(∫ x in 0..Real.pi / 4, f x) :=
        intervalIntegral.integral_neg
  rw [← intervalIntegral.integral_add_adjacent_intervals hneg hpos,
    hleft]
  ring

private def cosSecTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos (4 * (n : ℝ) * x) / Real.cos x

private def sinSecTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin (4 * (n : ℝ) * x) / Real.cos x

private theorem continuousOn_cosSecTerm (n : ℕ) :
    ContinuousOn (cosSecTerm n)
      (Set.Icc (-Real.pi / 4) (Real.pi / 4)) := by
  intro x hx
  unfold cosSecTerm
  exact ((Real.continuous_cos.comp
    (continuous_const.mul continuous_id)).continuousAt.div
      Real.continuous_cos.continuousAt
      (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by
        linarith [hx.1, Real.pi_pos], by
        linarith [hx.2, Real.pi_pos]⟩))).continuousWithinAt

private theorem continuousOn_sinSecTerm (n : ℕ) :
    ContinuousOn (sinSecTerm n)
      (Set.Icc (-Real.pi / 4) (Real.pi / 4)) := by
  intro x hx
  unfold sinSecTerm
  exact ((Real.continuous_sin.comp
    (continuous_const.mul continuous_id)).continuousAt.div
      Real.continuous_cos.continuousAt
      (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by
        linarith [hx.1, Real.pi_pos], by
        linarith [hx.2, Real.pi_pos]⟩))).continuousWithinAt

private theorem fourierCoeffOn_secC_nat (n : ℕ) :
    fourierCoeffOn (show -Real.pi / 4 < Real.pi / 4 by
      linarith [Real.pi_pos])
        secC (n : ℤ) =
      (((coefficientIntegral n / 2 : ℝ)) : ℂ) := by
  let hab : -Real.pi / 4 < Real.pi / 4 := by linarith [Real.pi_pos]
  have hcosEven : Function.Even (cosSecTerm n) := by
    intro x
    simp [cosSecTerm]
  have hsinOdd : Function.Odd (sinSecTerm n) := by
    intro x
    simp [sinSecTerm]
    ring
  have hcosFull : IntervalIntegrable (cosSecTerm n) MeasureTheory.volume
      (-Real.pi / 4) (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by linarith [Real.pi_pos] :
      -Real.pi / 4 ≤ Real.pi / 4)] using continuousOn_cosSecTerm n
  have hsinFull : IntervalIntegrable (sinSecTerm n) MeasureTheory.volume
      (-Real.pi / 4) (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by linarith [Real.pi_pos] :
      -Real.pi / 4 ≤ Real.pi / 4)] using continuousOn_sinSecTerm n
  have hcosNeg : IntervalIntegrable (cosSecTerm n) MeasureTheory.volume
      (-Real.pi / 4) 0 := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_cosSecTerm n).mono
    intro x hx
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] :
      -Real.pi / 4 ≤ 0)] at hx
    exact ⟨hx.1, hx.2.trans (by positivity)⟩
  have hcosPos : IntervalIntegrable (cosSecTerm n) MeasureTheory.volume
      0 (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_cosSecTerm n).mono
    intro x hx
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] at hx
    exact ⟨(by linarith [hx.1, Real.pi_pos]), hx.2⟩
  have hsinNeg : IntervalIntegrable (sinSecTerm n) MeasureTheory.volume
      (-Real.pi / 4) 0 := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_sinSecTerm n).mono
    intro x hx
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] :
      -Real.pi / 4 ≤ 0)] at hx
    exact ⟨hx.1, hx.2.trans (by positivity)⟩
  have hsinPos : IntervalIntegrable (sinSecTerm n) MeasureTheory.volume
      0 (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_sinSecTerm n).mono
    intro x hx
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] at hx
    exact ⟨(by linarith [hx.1, Real.pi_pos]), hx.2⟩
  have hcosSymm := integral_even_symmetric (cosSecTerm n) hcosEven hcosNeg hcosPos
  have hsinSymm := integral_odd_symmetric (sinSecTerm n) hsinOdd hsinNeg hsinPos
  have hcosC : IntervalIntegrable (fun x : ℝ => ((cosSecTerm n x : ℝ) : ℂ))
      MeasureTheory.volume (-Real.pi / 4) (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Function.comp_apply, Set.uIcc_of_le (by
      linarith [Real.pi_pos] : -Real.pi / 4 ≤ Real.pi / 4)] using
        Complex.continuous_ofReal.comp_continuousOn
          (continuousOn_cosSecTerm n)
  have hsinC : IntervalIntegrable
      (fun x : ℝ => ((sinSecTerm n x : ℝ) : ℂ) * Complex.I)
      MeasureTheory.volume (-Real.pi / 4) (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Function.comp_apply, Set.uIcc_of_le (by
      linarith [Real.pi_pos] : -Real.pi / 4 ≤ Real.pi / 4)] using
        (Complex.continuous_ofReal.comp_continuousOn
          (continuousOn_sinSecTerm n)).mul continuousOn_const
  rw [fourierCoeffOn_eq_integral]
  simp only [smul_eq_mul, Complex.real_smul]
  have hfun :
      (fun x : ℝ =>
        fourier (-(n : ℤ))
            (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) * secC x) =
        fun x => ((cosSecTerm n x : ℝ) : ℂ) -
          ((sinSecTerm n x : ℝ) : ℂ) * Complex.I := by
    funext x
    exact fourier_neg_nat_mul_secC n x
  have hcosIntC :
      (∫ x in -Real.pi / 4..Real.pi / 4,
        ((cosSecTerm n x : ℝ) : ℂ)) =
        ((∫ x in -Real.pi / 4..Real.pi / 4, cosSecTerm n x : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  have hsinIntC :
      (∫ x in -Real.pi / 4..Real.pi / 4,
        ((sinSecTerm n x : ℝ) : ℂ) * Complex.I) =
        ((∫ x in -Real.pi / 4..Real.pi / 4, sinSecTerm n x : ℝ) : ℂ) *
          Complex.I := by
    calc
      (∫ x in -Real.pi / 4..Real.pi / 4,
          ((sinSecTerm n x : ℝ) : ℂ) * Complex.I) =
          (∫ x in -Real.pi / 4..Real.pi / 4,
            ((sinSecTerm n x : ℝ) : ℂ)) * Complex.I :=
        intervalIntegral.integral_mul_const Complex.I _
      _ = ((∫ x in -Real.pi / 4..Real.pi / 4,
          sinSecTerm n x : ℝ) : ℂ) * Complex.I := by
        rw [intervalIntegral.integral_ofReal]
  rw [hfun, intervalIntegral.integral_sub hcosC hsinC]
  rw [hcosIntC, hsinIntC, hcosSymm, hsinSymm]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]
  change
    (((1 / (Real.pi / 4 - -Real.pi / 4) : ℝ) : ℂ) *
        ((2 * ∫ x in 0..Real.pi / 4, cosSecTerm n x : ℝ) : ℂ)) =
      ((coefficientIntegral n / 2 : ℝ) : ℂ)
  rw [← Complex.ofReal_mul]
  norm_cast
  unfold coefficientIntegral cosSecTerm
  field_simp [Real.pi_ne_zero]
  ring

private theorem fourier_nat_reflect (n : ℤ) (x : ℝ) :
    fourier n
        (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) =
      fourier (-n)
        ((-x : ℝ) : AddCircle (Real.pi / 4 - -Real.pi / 4)) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  ring

private theorem secC_neg (x : ℝ) : secC (-x) = secC x := by
  simp [secC, sec, Real.cos_neg]

private theorem fourierCoeffOn_secC_neg_nat (n : ℕ) :
    fourierCoeffOn (by linarith [Real.pi_pos] :
        -Real.pi / 4 < Real.pi / 4) secC (-(n : ℤ)) =
      ((coefficientIntegral n / 2 : ℝ) : ℂ) := by
  have hab : -Real.pi / 4 < Real.pi / 4 := by
    linarith [Real.pi_pos]
  calc
    fourierCoeffOn hab secC (-(n : ℤ)) =
        fourierCoeffOn hab secC (n : ℤ) := by
      rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
      congr 1
      simp only [neg_neg]
      calc
        (∫ x in -Real.pi / 4..Real.pi / 4,
            fourier (n : ℤ)
                (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) * secC x) =
            ∫ x in -Real.pi / 4..Real.pi / 4,
              fourier (-(n : ℤ))
                  ((-x : ℝ) : AddCircle
                    (Real.pi / 4 - -Real.pi / 4)) * secC (-x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          change fourier (n : ℤ)
              (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) * secC x =
            fourier (-(n : ℤ))
              ((-x : ℝ) : AddCircle (Real.pi / 4 - -Real.pi / 4)) * secC (-x)
          rw [secC_neg, fourier_nat_reflect]
        _ = ∫ x in -(Real.pi / 4)..-(-Real.pi / 4),
              fourier (-(n : ℤ))
                  (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) * secC x :=
          intervalIntegral.integral_comp_neg
            (fun x : ℝ => fourier (-(n : ℤ))
              (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) * secC x)
        _ = ∫ x in -Real.pi / 4..Real.pi / 4,
              fourier (-(n : ℤ))
                  (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) * secC x := by
          congr 1 <;> ring
    _ = ((coefficientIntegral n / 2 : ℝ) : ℂ) :=
      fourierCoeffOn_secC_nat n

private theorem fourierCoeff_periodizedSec_nat (n : ℕ) :
    fourierCoeff periodizedSec (n : ℤ) =
      ((coefficientIntegral n / 2 : ℝ) : ℂ) := by
  rw [periodizedSec, fourierCoeff_liftIco_eq]
  convert fourierCoeffOn_secC_nat n using 1 <;> ring

private theorem fourierCoeff_periodizedSec_neg_nat (n : ℕ) :
    fourierCoeff periodizedSec (-(n : ℤ)) =
      ((coefficientIntegral n / 2 : ℝ) : ℂ) := by
  rw [periodizedSec, fourierCoeff_liftIco_eq]
  convert fourierCoeffOn_secC_neg_nat n using 1 <;> ring

private theorem fourierCoeff_periodizedSec_formula (n : ℤ) :
    fourierCoeff periodizedSec n =
      ((coefficientIntegral n.natAbs / 2 : ℝ) : ℂ) := by
  cases n with
  | ofNat n => exact fourierCoeff_periodizedSec_nat n
  | negSucc n =>
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega]
      rw [Int.natAbs_neg]
      exact fourierCoeff_periodizedSec_neg_nat (n + 1)

private def secCDeriv (x : ℝ) : ℂ :=
  ((Real.sin x / Real.cos x ^ 2 : ℝ) : ℂ)

private theorem hasDerivAt_secC (x : ℝ)
    (hx : x ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4)) :
    HasDerivAt secC (secCDeriv x) x := by
  have hcos : Real.cos x ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by
    linarith [hx.1, Real.pi_pos], by
    linarith [hx.2, Real.pi_pos]⟩)
  unfold secC sec secCDeriv
  have hquot : HasDerivAt (fun y : ℝ => 1 / Real.cos y)
      ((0 * Real.cos x - 1 * (-Real.sin x)) / Real.cos x ^ 2) x :=
    (hasDerivAt_const x (1 : ℝ)).div (Real.hasDerivAt_cos x) hcos
  convert hquot.ofReal_comp using 1
  ring

private theorem continuous_secCDeriv_on :
    ContinuousOn secCDeriv
      (Set.Icc (-Real.pi / 4) (Real.pi / 4)) := by
  intro x hx
  unfold secCDeriv
  apply ContinuousAt.continuousWithinAt
  exact Complex.continuous_ofReal.continuousAt.comp
    (Real.continuous_sin.continuousAt.div
      (Real.continuous_cos.continuousAt.pow 2)
      (pow_ne_zero 2 (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by
        linarith [hx.1, Real.pi_pos], by
        linarith [hx.2, Real.pi_pos]⟩))))

private theorem secCDeriv_intervalIntegrable :
    IntervalIntegrable secCDeriv MeasureTheory.volume
      (-Real.pi / 4) (Real.pi / 4) := by
  apply ContinuousOn.intervalIntegrable
  simpa [Set.uIcc_of_le (by linarith [Real.pi_pos] :
    -Real.pi / 4 ≤ Real.pi / 4)] using continuous_secCDeriv_on

private theorem secCDeriv_memLp :
    MeasureTheory.MemLp secCDeriv 2
      (MeasureTheory.volume.restrict
        (Set.Ioc (-Real.pi / 4) (Real.pi / 4))) := by
  have hmeas : MeasureTheory.AEStronglyMeasurable secCDeriv
      (MeasureTheory.volume.restrict
        (Set.Ioc (-Real.pi / 4) (Real.pi / 4))) :=
    (continuous_secCDeriv_on.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas]
  change MeasureTheory.IntegrableOn (fun x => ‖secCDeriv x‖ ^ 2)
    (Set.Ioc (-Real.pi / 4) (Real.pi / 4))
  exact ((continuous_secCDeriv_on.norm.pow 2).integrableOn_Icc).mono_set
    Set.Ioc_subset_Icc_self

private theorem fourierCoeffOn_secC_of_ne_zero (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (by linarith [Real.pi_pos] :
        -Real.pi / 4 < Real.pi / 4) secC n =
      1 / (-2 * (Real.pi : ℂ) * Complex.I * n) *
        (0 - ((Real.pi / 4 - -Real.pi / 4 : ℝ) : ℂ) *
          fourierCoeffOn (by linarith [Real.pi_pos] :
            -Real.pi / 4 < Real.pi / 4) secCDeriv n) := by
  have hab : -Real.pi / 4 < Real.pi / 4 := by
    linarith [Real.pi_pos]
  have hderiv : ∀ x, x ∈ Set.uIcc (-Real.pi / 4) (Real.pi / 4) →
      HasDerivAt secC (secCDeriv x) x := by
    intro x hx
    apply hasDerivAt_secC x
    simpa [Set.uIcc_of_le hab.le] using hx
  rw [fourierCoeffOn_of_hasDerivAt hab hn hderiv
    secCDeriv_intervalIntegrable]
  have hend : secC (Real.pi / 4) - secC (-Real.pi / 4) = 0 := by
    unfold secC
    norm_cast
    unfold sec
    rw [show -Real.pi / 4 = -(Real.pi / 4) by ring, Real.cos_neg]
    exact sub_self _
  rw [hend]
  simp only [mul_zero]
  rw [Complex.ofReal_sub]

private theorem norm_fourierCoeffOn_secC (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn (by linarith [Real.pi_pos] :
        -Real.pi / 4 < Real.pi / 4) secC n‖ =
      ‖fourierCoeffOn (by linarith [Real.pi_pos] :
        -Real.pi / 4 < Real.pi / 4) secCDeriv n‖ /
        (4 * |(n : ℝ)|) := by
  rw [fourierCoeffOn_secC_of_ne_zero n hn]
  simp [norm_mul, norm_div, abs_of_pos Real.pi_pos]
  have hperiod :
      (Real.pi : ℂ) / 4 - -(Real.pi : ℂ) / 4 =
        ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hperiod, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < Real.pi / 2)]
  field_simp [Real.pi_ne_zero]
  ring

private theorem norm_fourierCoeffOn_secC_le (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn (by linarith [Real.pi_pos] :
        -Real.pi / 4 < Real.pi / 4) secC n‖ ≤
      ‖fourierCoeffOn (by linarith [Real.pi_pos] :
        -Real.pi / 4 < Real.pi / 4) secCDeriv n‖ ^ 2 +
        1 / (n : ℝ) ^ 2 := by
  rw [norm_fourierCoeffOn_secC n hn]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have habs : 0 < |(n : ℝ)| := abs_pos.mpr hnR
  let a := ‖fourierCoeffOn (by linarith [Real.pi_pos] :
    -Real.pi / 4 < Real.pi / 4) secCDeriv n‖
  have ha : 0 ≤ a := norm_nonneg _
  have hainv : 0 ≤ |(n : ℝ)|⁻¹ := inv_nonneg.mpr habs.le
  calc
    a / (4 * |(n : ℝ)|) = (a * |(n : ℝ)|⁻¹) / 4 := by
      field_simp [ne_of_gt habs]
    _ ≤ a * |(n : ℝ)|⁻¹ := by
      nlinarith [mul_nonneg ha hainv]
    _ ≤ a ^ 2 + (|(n : ℝ)|⁻¹) ^ 2 := by
      nlinarith [sq_nonneg (a - |(n : ℝ)|⁻¹)]
    _ = a ^ 2 + 1 / (n : ℝ) ^ 2 := by
      simp [one_div, inv_pow]

private theorem summable_fourierCoeffOn_secC :
    Summable (fourierCoeffOn (by linarith [Real.pi_pos] :
      -Real.pi / 4 < Real.pi / 4) secC) := by
  have hab : -Real.pi / 4 < Real.pi / 4 := by
    linarith [Real.pi_pos]
  have hderiv : Summable (fun n : ℤ =>
      ‖fourierCoeffOn hab secCDeriv n‖ ^ 2) :=
    (hasSum_sq_fourierCoeffOn hab secCDeriv_memLp).summable
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  refine (hderiv.add hp).of_norm_bounded_eventually ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  convert norm_fourierCoeffOn_secC_le n hn using 1

private theorem summable_fourierCoeff_periodizedSec :
    Summable (fourierCoeff periodizedSec) := by
  have hab : -Real.pi / 4 < Real.pi / 4 := by
    linarith [Real.pi_pos]
  have heq : fourierCoeff periodizedSec =
      fourierCoeffOn hab secC := by
    funext n
    rw [periodizedSec, fourierCoeff_liftIco_eq]
    congr 2 <;> ring
  rw [heq]
  exact summable_fourierCoeffOn_secC

private theorem coefficientClosed_eq_fourierCoefficient (n : ℕ) :
    coefficientClosed n = fourierCoefficient n := by
  have hsum :
      (∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ k /
          ((4 * (k : ℝ) - 3) * (4 * (k : ℝ) - 1))) =
        -(∑ k ∈ Finset.Icc 1 n,
          (-1 : ℝ) ^ (k - 1) /
            ((4 * (k : ℝ) - 3) * (4 * (k : ℝ) - 1))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hp : (-1 : ℝ) ^ k = -((-1 : ℝ) ^ (k - 1)) := by
      calc
        (-1 : ℝ) ^ k = (-1 : ℝ) ^ ((k - 1) + 1) :=
          congrArg (fun m : ℕ => (-1 : ℝ) ^ m) (by omega)
        _ = -((-1 : ℝ) ^ (k - 1)) := by
          rw [pow_succ]
          ring
    rw [hp]
    ring
  unfold coefficientClosed fourierCoefficient
  rw [hsum]
  ring

private theorem coefficientIntegral_eq_fourierCoefficient (n : ℕ)
    (hn : 1 ≤ n) : coefficientIntegral n = fourierCoefficient n := by
  exact (gap17 coefficientIntegral (fun _ _ => rfl) n hn).trans
    (coefficientClosed_eq_fourierCoefficient n)

private theorem coefficientIntegral_zero_eval' :
    coefficientIntegral 0 =
      8 / Real.pi * Real.log (1 + Real.sqrt 2) := by
  apply gap8 coefficientIntegral
  unfold coefficientIntegral sec
  simp

private theorem fourier_nat_add_neg (n : ℕ) (x : ℝ) :
    fourier (n : ℤ)
          (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) +
        fourier (-(n : ℤ))
          (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) =
      ((2 * Real.cos (4 * (n : ℝ) * x) : ℝ) : ℂ) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  have hpos :
      2 * (Real.pi : ℂ) * Complex.I * ((n : ℤ) : ℂ) * (x : ℂ) /
          ((Real.pi / 4 - -Real.pi / 4 : ℝ) : ℂ) =
        ((4 * (n : ℝ) * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  have hneg :
      2 * (Real.pi : ℂ) * Complex.I * ((-(n : ℤ) : ℤ) : ℂ) * (x : ℂ) /
          ((Real.pi / 4 - -Real.pi / 4 : ℝ) : ℂ) =
        (-((4 * (n : ℝ) * x : ℝ) : ℂ)) * Complex.I := by
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  rw [hpos, hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

private theorem paired_fourier_term (n : ℕ) (x : ℝ) :
    fourierCoeff periodizedSec (n : ℤ) •
          fourier (n : ℤ)
            (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) +
        fourierCoeff periodizedSec (-(n : ℤ)) •
          fourier (-(n : ℤ))
            (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) =
      ((coefficientIntegral n *
        Real.cos (4 * (n : ℝ) * x) : ℝ) : ℂ) := by
  rw [fourierCoeff_periodizedSec_nat,
    fourierCoeff_periodizedSec_neg_nat]
  simp only [smul_eq_mul]
  rw [← mul_add, fourier_nat_add_neg]
  push_cast
  ring

private def fourierTerm (x : ℝ) (n : ℤ) : ℂ :=
  fourierCoeff periodizedSec n •
    fourier n (x : AddCircle (Real.pi / 4 - -Real.pi / 4))

private theorem periodizedSec_coe (x : ℝ)
    (hx₁ : -Real.pi / 4 < x) (hx₂ : x < Real.pi / 4) :
    periodizedSec
        (x : AddCircle (Real.pi / 4 - -Real.pi / 4)) = secC x := by
  unfold periodizedSec
  apply AddCircle.liftIco_coe_apply
  constructor
  · exact hx₁.le
  · convert hx₂ using 1 <;> ring

private theorem hasSum_fourierTerm (x : ℝ) :
    HasSum (fourierTerm x)
      (periodizedSec
        (x : AddCircle (Real.pi / 4 - -Real.pi / 4))) := by
  let F : C(AddCircle (Real.pi / 4 - -Real.pi / 4), ℂ) :=
    ⟨periodizedSec, continuous_periodizedSec⟩
  have hs : Summable (fourierCoeff F) := by
    simpa [F] using summable_fourierCoeff_periodizedSec
  change HasSum (fun i => fourierCoeff F i •
    fourier i (x : AddCircle (Real.pi / 4 - -Real.pi / 4)))
      (F (x : AddCircle (Real.pi / 4 - -Real.pi / 4)))
  exact has_pointwise_sum_fourier_series_of_summable hs
    (x : AddCircle (Real.pi / 4 - -Real.pi / 4))

private theorem fourierTerm_zero (x : ℝ) :
    fourierTerm x 0 = ((coefficientIntegral 0 / 2 : ℝ) : ℂ) := by
  unfold fourierTerm
  rw [fourierCoeff_periodizedSec_formula 0]
  simp [fourier_coe_apply]

theorem gap18 :
    ∀ x, -Real.pi / 4 < x → x < Real.pi / 4 →
      sec x = fourierSeries x := by
  intro x hx₁ hx₂
  have hfull : HasSum (fourierTerm x) (secC x) := by
    rw [← periodizedSec_coe x hx₁ hx₂]
    exact hasSum_fourierTerm x
  have hpaired := hfull.nat_add_neg
  have htailRaw := (hasSum_nat_add_iff' 1).2 hpaired
  have htail :
      HasSum (fun k : ℕ =>
          fourierTerm x ((k + 1 : ℕ) : ℤ) +
            fourierTerm x (-((k + 1 : ℕ) : ℤ)))
        (secC x - fourierTerm x 0) := by
    simpa [add_assoc] using htailRaw
  have hseriesC :
      HasSum (fun k : ℕ =>
          ((fourierCoefficient (k + 1) *
            Real.cos (4 * (k + 1 : ℝ) * x) : ℝ) : ℂ))
        (secC x - ((coefficientIntegral 0 / 2 : ℝ) : ℂ)) := by
    rw [← fourierTerm_zero x]
    apply htail.congr_fun
    intro k
    rw [← coefficientIntegral_eq_fourierCoefficient (k + 1) (by omega)]
    simpa [fourierTerm, Nat.cast_add, Nat.cast_one] using
      (paired_fourier_term (k + 1) x).symm
  have hseriesR :
      HasSum (fun k : ℕ =>
          fourierCoefficient (k + 1) *
            Real.cos (4 * (k + 1 : ℝ) * x))
        (sec x - coefficientIntegral 0 / 2) := by
    convert Complex.reCLM.hasSum hseriesC using 1 <;>
      simp [secC]
  have htsum := hseriesR.tsum_eq
  unfold fourierSeries
  rw [htsum, coefficientIntegral_zero_eval']
  field_simp [Real.pi_ne_zero]
  ring

end

end ProofGap.Exercise2960
