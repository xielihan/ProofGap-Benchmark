import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2475

noncomputable section

def parabola (a b x : ℝ) : ℝ := b * (x / a) ^ 2

def vShape (a b x : ℝ) : ℝ := b * |x / a|

def xAxisVolume (a b : ℝ) : ℝ :=
  2 * Real.pi * ∫ x in 0..a,
    (b ^ 2 * x ^ 2 / a ^ 2 - b ^ 2 * x ^ 4 / a ^ 4)

def yAxisVolume (a b : ℝ) : ℝ :=
  Real.pi * ∫ y in 0..b,
    (a ^ 2 * y / b - a ^ 2 * y ^ 2 / b ^ 2)

private theorem integral_poly_antiderivative
    (f F : ℝ → ℝ) (hf : Continuous f)
    (hF : ∀ x : ℝ, HasDerivAt F (f x) x) (u v : ℝ) :
    (∫ x in u..v, f x) = F v - F u := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  all_goals
    first
    | exact hf.intervalIntegrable u v
    | exact fun x _ => hF x

theorem gap1 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    parabola a b x = vShape a b x ↔ x = -a ∨ x = 0 ∨ x = a := by
  constructor
  · intro h
    unfold parabola vShape at h
    have hcore : (x / a) ^ 2 = |x / a| := by
      have hprod : b * ((x / a) ^ 2 - |x / a|) = 0 := by
        calc
          b * ((x / a) ^ 2 - |x / a|) =
              b * (x / a) ^ 2 - b * |x / a| := by ring
          _ = 0 := sub_eq_zero.mpr h
      have hdiff : (x / a) ^ 2 - |x / a| = 0 :=
        (mul_eq_zero.mp hprod).resolve_left hb.ne'
      exact sub_eq_zero.mp hdiff
    have hxa : x = (x / a) * a := by
      field_simp [ha.ne']
    by_cases hx : 0 ≤ x / a
    · rw [abs_of_nonneg hx] at hcore
      have hfac : (x / a) * (x / a - 1) = 0 := by
        nlinarith [hcore]
      rcases mul_eq_zero.mp hfac with hzero | hone
      · right
        left
        calc
          x = (x / a) * a := hxa
          _ = 0 := by rw [hzero]; ring
      · right
        right
        have hunit : x / a = 1 := by linarith
        calc
          x = (x / a) * a := hxa
          _ = a := by rw [hunit]; ring
    · have hx' : x / a ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx'] at hcore
      have hfac : (x / a) * (x / a + 1) = 0 := by
        nlinarith [hcore]
      rcases mul_eq_zero.mp hfac with hzero | hneg
      · right
        left
        calc
          x = (x / a) * a := hxa
          _ = 0 := by rw [hzero]; ring
      · left
        have hunit : x / a = -1 := by linarith
        calc
          x = (x / a) * a := hxa
          _ = -a := by rw [hunit]; ring
  · intro h
    rcases h with h | h | h
    · subst x
      simp [parabola, vShape, ha.ne']
    · subst x
      simp [parabola, vShape]
    · subst x
      simp [parabola, vShape, ha.ne']

theorem gap2 (a b Vₓ : ℝ) (hV : Vₓ = xAxisVolume a b) :
    Vₓ = 2 * Real.pi * ∫ x in 0..a,
      (b ^ 2 * x ^ 2 / a ^ 2 - b ^ 2 * x ^ 4 / a ^ 4) := by
  simpa [xAxisVolume] using hV

theorem gap3 (a b : ℝ) (ha : 0 < a) :
    2 * Real.pi * (∫ x in 0..a,
      (b ^ 2 * x ^ 2 / a ^ 2 - b ^ 2 * x ^ 4 / a ^ 4)) =
        4 * Real.pi / 15 * a * b ^ 2 := by
  have hfun :
      (fun x : ℝ => b ^ 2 * x ^ 2 / a ^ 2 - b ^ 2 * x ^ 4 / a ^ 4) =
        (fun x : ℝ => (b ^ 2 / a ^ 2) * x ^ 2 -
          (b ^ 2 / a ^ 4) * x ^ 4) := by
    funext x
    ring
  have hcont : Continuous
      (fun x : ℝ => (b ^ 2 / a ^ 2) * x ^ 2 -
        (b ^ 2 / a ^ 4) * x ^ 4) :=
    (continuous_const.mul (continuous_id.pow 2)).sub
      (continuous_const.mul (continuous_id.pow 4))
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun t : ℝ =>
        (b ^ 2 / a ^ 2 / 3) * ((t * t) * t) -
          (b ^ 2 / a ^ 4 / 5) * ((((t * t) * t) * t) * t))
      ((b ^ 2 / a ^ 2) * x ^ 2 -
        (b ^ 2 / a ^ 4) * x ^ 4) x := by
    intro x
    have h1 := hasDerivAt_id x
    have h2 := h1.mul h1
    have h3 := h2.mul h1
    have h4 := h3.mul h1
    have h5 := h4.mul h1
    convert
      (h3.const_mul (b ^ 2 / a ^ 2 / 3)).sub
        (h5.const_mul (b ^ 2 / a ^ 4 / 5)) using 1 <;>
      norm_num <;> ring
  have hint :
      (∫ x in 0..a, (b ^ 2 / a ^ 2) * x ^ 2 -
        (b ^ 2 / a ^ 4) * x ^ 4) =
      (fun x : ℝ =>
        (b ^ 2 / a ^ 2 / 3) * ((x * x) * x) -
          (b ^ 2 / a ^ 4 / 5) * ((((x * x) * x) * x) * x)) a -
      (fun x : ℝ =>
        (b ^ 2 / a ^ 2 / 3) * ((x * x) * x) -
          (b ^ 2 / a ^ 4 / 5) * ((((x * x) * x) * x) * x)) 0 :=
    integral_poly_antiderivative
      (fun x : ℝ => (b ^ 2 / a ^ 2) * x ^ 2 -
        (b ^ 2 / a ^ 4) * x ^ 4)
      (fun x : ℝ =>
        (b ^ 2 / a ^ 2 / 3) * ((x * x) * x) -
          (b ^ 2 / a ^ 4 / 5) * ((((x * x) * x) * x) * x))
      hcont hderiv 0 a
  rw [hfun, hint]
  norm_num
  field_simp [ha.ne'] <;> ring

theorem gap4 (a b Vₓ : ℝ) (ha : 0 < a)
    (hV : Vₓ = xAxisVolume a b) :
    Vₓ = 4 * Real.pi / 15 * a * b ^ 2 := by
  calc
    Vₓ = xAxisVolume a b := hV
    _ = 4 * Real.pi / 15 * a * b ^ 2 := by
      simpa [xAxisVolume] using gap3 a b ha

theorem gap5 (a b Vᵧ : ℝ) (hV : Vᵧ = yAxisVolume a b) :
    Vᵧ = Real.pi * ∫ y in 0..b,
      (a ^ 2 * y / b - a ^ 2 * y ^ 2 / b ^ 2) := by
  simpa [yAxisVolume] using hV

theorem gap6 (a b : ℝ) (hb : 0 < b) :
    Real.pi * (∫ y in 0..b,
      (a ^ 2 * y / b - a ^ 2 * y ^ 2 / b ^ 2)) =
        Real.pi * a ^ 2 * b / 6 := by
  have hfun :
      (fun y : ℝ => a ^ 2 * y / b - a ^ 2 * y ^ 2 / b ^ 2) =
        (fun y : ℝ => (a ^ 2 / b) * y ^ 1 -
          (a ^ 2 / b ^ 2) * y ^ 2) := by
    funext y
    ring
  have hcont : Continuous
      (fun y : ℝ => (a ^ 2 / b) * y ^ 1 -
        (a ^ 2 / b ^ 2) * y ^ 2) :=
    (continuous_const.mul (continuous_id.pow 1)).sub
      (continuous_const.mul (continuous_id.pow 2))
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ =>
        (a ^ 2 / b / 2) * (t * t) -
          (a ^ 2 / b ^ 2 / 3) * ((t * t) * t))
      ((a ^ 2 / b) * y ^ 1 -
        (a ^ 2 / b ^ 2) * y ^ 2) y := by
    intro y
    have h1 := hasDerivAt_id y
    have h2 := h1.mul h1
    have h3 := h2.mul h1
    convert
      (h2.const_mul (a ^ 2 / b / 2)).sub
        (h3.const_mul (a ^ 2 / b ^ 2 / 3)) using 1 <;>
      norm_num <;> ring
  have hint :
      (∫ y in 0..b, (a ^ 2 / b) * y ^ 1 -
        (a ^ 2 / b ^ 2) * y ^ 2) =
      (fun y : ℝ =>
        (a ^ 2 / b / 2) * (y * y) -
          (a ^ 2 / b ^ 2 / 3) * ((y * y) * y)) b -
      (fun y : ℝ =>
        (a ^ 2 / b / 2) * (y * y) -
          (a ^ 2 / b ^ 2 / 3) * ((y * y) * y)) 0 :=
    integral_poly_antiderivative
      (fun y : ℝ => (a ^ 2 / b) * y ^ 1 -
        (a ^ 2 / b ^ 2) * y ^ 2)
      (fun y : ℝ =>
        (a ^ 2 / b / 2) * (y * y) -
          (a ^ 2 / b ^ 2 / 3) * ((y * y) * y))
      hcont hderiv 0 b
  rw [hfun, hint]
  norm_num
  field_simp [hb.ne'] <;> ring

theorem gap7 (a b Vᵧ : ℝ) (hb : 0 < b)
    (hV : Vᵧ = yAxisVolume a b) :
    Vᵧ = Real.pi * a ^ 2 * b / 6 := by
  calc
    Vᵧ = yAxisVolume a b := hV
    _ = Real.pi * a ^ 2 * b / 6 := by
      simpa [yAxisVolume] using gap6 a b hb

end

end ProofGap.Exercise2475
