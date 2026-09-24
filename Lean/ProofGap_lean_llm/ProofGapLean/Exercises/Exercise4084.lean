import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4084

noncomputable section

open MeasureTheory
open scoped Interval

def tripleVolterra (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ xi in (0 : ℝ)..x,
    ∫ eta in (0 : ℝ)..xi,
      ∫ zeta in (0 : ℝ)..eta, f zeta

private theorem primitive_hasDerivAt
    (f : ℝ → ℝ) (hf : Continuous f) (a y : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ z in a..t, f z) (f y) y := by
  apply intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable a y)
  · exact hf.stronglyMeasurable.stronglyMeasurableAtFilter
  · exact hf.continuousAt

private theorem nested_interval_integral_eq_weighted
    (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    (∫ y in a..b, ∫ z in a..y, f z) =
      ∫ y in a..b, f y * (b - y) := by
  let F : ℝ → ℝ := fun y => ∫ z in a..y, f z
  have hF : ∀ y : ℝ, HasDerivAt F (f y) y := by
    intro y
    simpa [F] using primitive_hasDerivAt f hf a y
  have hFc : Continuous F :=
    continuous_iff_continuousAt.2 fun y => (hF y).continuousAt
  have hlincont : Continuous (fun y : ℝ => b - y) :=
    continuous_const.sub continuous_id
  have hweightedcont : Continuous (fun y : ℝ => f y * (b - y)) :=
    hf.mul hlincont
  have hd : ∀ y : ℝ,
      HasDerivAt (fun z : ℝ => F z * (b - z))
        (f y * (b - y) - F y) y := by
    intro y
    have hlin : HasDerivAt (fun z : ℝ => b - z) (-1) y := by
      convert (hasDerivAt_const y b).sub (hasDerivAt_id y) using 1 <;> ring
    convert (hF y).mul hlin using 1 <;> ring
  have hcont : Continuous (fun y : ℝ => f y * (b - y) - F y) :=
    hweightedcont.sub hFc
  have hzero :
      (∫ y in a..b, f y * (b - y) - F y) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hd y) (hcont.intervalIntegrable a b)
    simpa [F] using h
  have hw : IntervalIntegrable (fun y : ℝ => f y * (b - y)) volume a b :=
    hweightedcont.intervalIntegrable a b
  have hFi : IntervalIntegrable F volume a b :=
    hFc.intervalIntegrable a b
  rw [intervalIntegral.integral_sub hw hFi] at hzero
  have heq :
      (∫ y in a..b, f y * (b - y)) = (∫ y in a..b, F y) :=
    sub_eq_zero.mp hzero
  simpa [F] using heq.symm

private theorem primitive_weighted_eq_square
    (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    (∫ y in a..b, (∫ z in a..y, f z) * (b - y)) =
      (1 / 2 : ℝ) * ∫ y in a..b, f y * (b - y) ^ 2 := by
  let F : ℝ → ℝ := fun y => ∫ z in a..y, f z
  have hF : ∀ y : ℝ, HasDerivAt F (f y) y := by
    intro y
    simpa [F] using primitive_hasDerivAt f hf a y
  have hFc : Continuous F :=
    continuous_iff_continuousAt.2 fun y => (hF y).continuousAt
  have hlincont : Continuous (fun y : ℝ => b - y) :=
    continuous_const.sub continuous_id
  have hc : Continuous (fun _ : ℝ => (1 / 2 : ℝ)) := continuous_const
  have hhalfcont :
      Continuous (fun y : ℝ => (1 / 2 : ℝ) * (f y * (b - y) ^ 2)) :=
    hc.mul (hf.mul (hlincont.pow 2))
  have hprimcont : Continuous (fun y : ℝ => F y * (b - y)) :=
    hFc.mul hlincont
  have hq : ∀ y : ℝ,
      HasDerivAt
        (fun z : ℝ => (1 / 2 : ℝ) * ((b - z) * (b - z)))
        (-(b - y)) y := by
    intro y
    have hlin : HasDerivAt (fun z : ℝ => b - z) (-1) y := by
      convert (hasDerivAt_const y b).sub (hasDerivAt_id y) using 1 <;> ring
    have hsq : HasDerivAt
        (fun z : ℝ => (b - z) * (b - z))
        (-2 * (b - y)) y := by
      convert hlin.mul hlin using 1 <;> ring
    have hconst : HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 y :=
      hasDerivAt_const y (1 / 2 : ℝ)
    convert hconst.mul hsq using 1 <;> ring
  have hd : ∀ y : ℝ,
      HasDerivAt
        (fun z : ℝ =>
          F z * ((1 / 2 : ℝ) * ((b - z) * (b - z))))
        ((1 / 2 : ℝ) * (f y * (b - y) ^ 2) - F y * (b - y)) y := by
    intro y
    convert (hF y).mul (hq y) using 1 <;> ring
  have hcont : Continuous
      (fun y : ℝ =>
        (1 / 2 : ℝ) * (f y * (b - y) ^ 2) - F y * (b - y)) :=
    hhalfcont.sub hprimcont
  have hzero :
      (∫ y in a..b,
        (1 / 2 : ℝ) * (f y * (b - y) ^ 2) - F y * (b - y)) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hd y) (hcont.intervalIntegrable a b)
    simpa [F] using h
  have hhalf : IntervalIntegrable
      (fun y : ℝ => (1 / 2 : ℝ) * (f y * (b - y) ^ 2)) volume a b :=
    hhalfcont.intervalIntegrable a b
  have hprim : IntervalIntegrable
      (fun y : ℝ => F y * (b - y)) volume a b :=
    hprimcont.intervalIntegrable a b
  rw [intervalIntegral.integral_sub hhalf hprim] at hzero
  have heq :
      (∫ y in a..b, (1 / 2 : ℝ) * (f y * (b - y) ^ 2)) =
        ∫ y in a..b, F y * (b - y) :=
    sub_eq_zero.mp hzero
  change (∫ y in a..b, F y * (b - y)) =
    (1 / 2 : ℝ) * ∫ y in a..b, f y * (b - y) ^ 2
  calc
    (∫ y in a..b, F y * (b - y)) =
        ∫ y in a..b, (1 / 2 : ℝ) * (f y * (b - y) ^ 2) := heq.symm
    _ = (1 / 2 : ℝ) * ∫ y in a..b, f y * (b - y) ^ 2 := by
      rw [intervalIntegral.integral_const_mul]

private theorem tripleVolterra_eq_square_kernel
    (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    tripleVolterra f x =
      (1 / 2 : ℝ) * ∫ z in (0 : ℝ)..x, f z * (x - z) ^ 2 := by
  let F : ℝ → ℝ := fun y => ∫ z in (0 : ℝ)..y, f z
  have hFd : ∀ y : ℝ, HasDerivAt F (f y) y := by
    intro y
    simpa [F] using primitive_hasDerivAt f hf 0 y
  have hFc : Continuous F :=
    continuous_iff_continuousAt.2 fun y => (hFd y).continuousAt
  unfold tripleVolterra
  change (∫ xi in (0 : ℝ)..x, ∫ eta in (0 : ℝ)..xi, F eta) =
    (1 / 2 : ℝ) * ∫ z in (0 : ℝ)..x, f z * (x - z) ^ 2
  calc
    (∫ xi in (0 : ℝ)..x, ∫ eta in (0 : ℝ)..xi, F eta) =
        ∫ eta in (0 : ℝ)..x, F eta * (x - eta) := by
      exact nested_interval_integral_eq_weighted F hFc 0 x
    _ = (1 / 2 : ℝ) *
        ∫ z in (0 : ℝ)..x, f z * (x - z) ^ 2 := by
      simpa [F] using primitive_weighted_eq_square f hf 0 x

private theorem interval_integral_sub_left (a b : ℝ) :
    (∫ y in a..b, y - a) = (1 / 2 : ℝ) * (b - a) ^ 2 := by
  have hd : ∀ y : ℝ,
      HasDerivAt
        (fun z : ℝ => (1 / 2 : ℝ) * ((z - a) * (z - a)))
        (y - a) y := by
    intro y
    have hlin : HasDerivAt (fun z : ℝ => z - a) 1 y := by
      simpa using (hasDerivAt_id y).sub_const a
    have hsq : HasDerivAt
        (fun z : ℝ => (z - a) * (z - a))
        (2 * (y - a)) y := by
      convert (hlin.mul hlin) using 1 <;> ring
    have hc : HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 y :=
      hasDerivAt_const y (1 / 2 : ℝ)
    convert (hc.mul hsq) using 1 <;> ring
  have hcont : Continuous (fun y : ℝ => y - a) :=
    continuous_id.sub continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hd y) (hcont.intervalIntegrable a b)
  simpa [pow_two] using h

theorem gap1 (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    tripleVolterra f x =
      ∫ xi in (0 : ℝ)..x,
        ∫ zeta in (0 : ℝ)..xi,
          ∫ eta in zeta..xi, f zeta := by
  unfold tripleVolterra
  apply intervalIntegral.integral_congr
  intro xi hxi
  calc
    (∫ eta in (0 : ℝ)..xi, ∫ zeta in (0 : ℝ)..eta, f zeta) =
        ∫ zeta in (0 : ℝ)..xi, f zeta * (xi - zeta) := by
      exact nested_interval_integral_eq_weighted f hf 0 xi
    _ = ∫ zeta in (0 : ℝ)..xi, ∫ eta in zeta..xi, f zeta := by
      apply intervalIntegral.integral_congr
      intro zeta hzeta
      change f zeta * (xi - zeta) = (∫ eta in zeta..xi, f zeta)
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

theorem gap2 (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    tripleVolterra f x =
      ∫ xi in (0 : ℝ)..x,
        ∫ zeta in (0 : ℝ)..xi, f zeta * (xi - zeta) := by
  rw [gap1 f hf x]
  apply intervalIntegral.integral_congr
  intro xi hxi
  apply intervalIntegral.integral_congr
  intro zeta hzeta
  change (∫ eta in zeta..xi, f zeta) = f zeta * (xi - zeta)
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap3 (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    tripleVolterra f x =
      ∫ zeta in (0 : ℝ)..x,
        ∫ xi in zeta..x, f zeta * (xi - zeta) := by
  rw [tripleVolterra_eq_square_kernel f hf x]
  symm
  calc
    (∫ zeta in (0 : ℝ)..x, ∫ xi in zeta..x, f zeta * (xi - zeta)) =
        ∫ zeta in (0 : ℝ)..x,
          (1 / 2 : ℝ) * (f zeta * (x - zeta) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro zeta hzeta
      change (∫ xi in zeta..x, f zeta * (xi - zeta)) =
        (1 / 2 : ℝ) * (f zeta * (x - zeta) ^ 2)
      calc
        (∫ xi in zeta..x, f zeta * (xi - zeta)) =
            f zeta * (∫ xi in zeta..x, xi - zeta) := by
          rw [intervalIntegral.integral_const_mul]
        _ = f zeta * ((1 / 2 : ℝ) * (x - zeta) ^ 2) := by
          exact congrArg (fun r : ℝ => f zeta * r)
            (interval_integral_sub_left zeta x)
        _ = (1 / 2 : ℝ) * (f zeta * (x - zeta) ^ 2) := by
          ring
    _ = (1 / 2 : ℝ) *
        ∫ zeta in (0 : ℝ)..x, f zeta * (x - zeta) ^ 2 := by
      rw [intervalIntegral.integral_const_mul]

theorem gap4 (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    tripleVolterra f x =
      1 / 2 * ∫ zeta in (0 : ℝ)..x, f zeta * (x - zeta) ^ 2 := by
  exact tripleVolterra_eq_square_kernel f hf x

end

end ProofGap.Exercise4084
