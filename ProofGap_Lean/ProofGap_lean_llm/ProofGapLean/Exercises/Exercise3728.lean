import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise3728

noncomputable section

open scoped Interval

def kernel (x y : ℝ) : ℝ :=
  if x ≤ y then x * (1 - y) else y * (1 - x)

def integralFunction (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, kernel x y * v y

def splitIntegral (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y in (0 : ℝ)..x, y * (1 - x) * v y) +
    ∫ y in x..1, x * (1 - y) * v y

def firstDerivative (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(∫ y in (0 : ℝ)..x, y * v y) +
    ∫ y in x..1, (1 - y) * v y

private theorem splitIntegral_factor (v : ℝ → ℝ) :
    splitIntegral v = fun x : ℝ =>
      (1 - x) * (∫ y in (0 : ℝ)..x, y * v y) +
        x * (∫ y in x..1, (1 - y) * v y) := by
  funext x
  have hleft :
      (∫ y in (0 : ℝ)..x, y * (1 - x) * v y) =
        (1 - x) * (∫ y in (0 : ℝ)..x, y * v y) := by
    calc
      (∫ y in (0 : ℝ)..x, y * (1 - x) * v y) =
          ∫ y in (0 : ℝ)..x, (1 - x) * (y * v y) := by
            apply intervalIntegral.integral_congr
            intro y hy
            ring
      _ = (1 - x) * (∫ y in (0 : ℝ)..x, y * v y) := by
        rw [intervalIntegral.integral_const_mul]
  have hright :
      (∫ y in x..1, x * (1 - y) * v y) =
        x * (∫ y in x..1, (1 - y) * v y) := by
    calc
      (∫ y in x..1, x * (1 - y) * v y) =
          ∫ y in x..1, x * ((1 - y) * v y) := by
            apply intervalIntegral.integral_congr
            intro y hy
            ring
      _ = x * (∫ y in x..1, (1 - y) * v y) := by
        rw [intervalIntegral.integral_const_mul]
  unfold splitIntegral
  rw [hleft, hright]

theorem gap1 (v : ℝ → ℝ) (hv : Continuous v) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      integralFunction v x = splitIntegral v x := by
  intro x hx
  have hk : ∀ y : ℝ, kernel x y = min x y - x * y := by
    intro y
    by_cases hxy : x ≤ y
    · unfold kernel
      rw [if_pos hxy, min_eq_left hxy]
      ring
    · have hyx : y ≤ x := le_of_not_ge hxy
      unfold kernel
      rw [if_neg hxy, min_eq_right hyx]
      ring
  have hfun :
      (fun y : ℝ => kernel x y * v y) =
        (fun y : ℝ => (min x y - x * y) * v y) := by
    funext y
    rw [hk y]
  have hc : Continuous (fun y : ℝ => kernel x y * v y) := by
    rw [hfun]
    exact
      (((continuous_const.min continuous_id).sub
          (continuous_const.mul continuous_id)).mul hv)
  have hint (a b : ℝ) :
      IntervalIntegrable (fun y : ℝ => kernel x y * v y)
        MeasureTheory.volume a b :=
    hc.intervalIntegrable a b
  have hleft :
      (∫ y in (0 : ℝ)..x, kernel x y * v y) =
        ∫ y in (0 : ℝ)..x, y * (1 - x) * v y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx.1] at hy
    by_cases hxy : x ≤ y
    · have hyx : y = x := le_antisymm hy.2 hxy
      subst y
      simp [kernel]
    · simp [kernel, hxy]
  have hright :
      (∫ y in x..1, kernel x y * v y) =
        ∫ y in x..1, x * (1 - y) * v y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx.2] at hy
    simp [kernel, hy.1]
  unfold integralFunction splitIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (hint 0 x) (hint x 1),
    hleft, hright]

theorem gap2 (v : ℝ → ℝ) (hv : Continuous v) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (integralFunction v) x =
        x * (1 - x) * v x -
          (∫ y in (0 : ℝ)..x, y * v y) -
          x * (1 - x) * v x +
          ∫ y in x..1, (1 - y) * v y := by
  intro x hx
  have heq : integralFunction v =ᶠ[nhds x] splitIntegral v := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact gap1 v hv y ⟨hy.1.le, hy.2.le⟩
  have hcA : Continuous (fun y : ℝ => y * v y) :=
    continuous_id.mul hv
  have hiA :
      IntervalIntegrable (fun y : ℝ => y * v y)
        MeasureTheory.volume 0 x :=
    hcA.intervalIntegrable 0 x
  have hA :
      HasDerivAt (fun z : ℝ => ∫ y in (0 : ℝ)..z, y * v y)
        (x * v x) x :=
    intervalIntegral.integral_hasDerivAt_right hiA
      hcA.stronglyMeasurable.stronglyMeasurableAtFilter
      hcA.continuousAt
  have hcB : Continuous (fun y : ℝ => (1 - y) * v y) :=
    (continuous_const.sub continuous_id).mul hv
  have hiB :
      IntervalIntegrable (fun y : ℝ => (1 - y) * v y)
        MeasureTheory.volume x 1 :=
    hcB.intervalIntegrable x 1
  have hB :
      HasDerivAt (fun z : ℝ => ∫ y in z..1, (1 - y) * v y)
        (-((1 - x) * v x)) x :=
    intervalIntegral.integral_hasDerivAt_left hiB
      hcB.stronglyMeasurable.stronglyMeasurableAtFilter
      hcB.continuousAt
  have hcalc :=
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).mul hA).add
      ((hasDerivAt_id x).mul hB)
  have hsplit : HasDerivAt (splitIntegral v)
      ((0 - 1) * (∫ y in (0 : ℝ)..x, y * v y) +
        (1 - x) * (x * v x) +
        (1 * (∫ y in x..1, (1 - y) * v y) +
          x * -((1 - x) * v x))) x := by
    rw [splitIntegral_factor]
    exact hcalc
  calc
    deriv (integralFunction v) x = deriv (splitIntegral v) x :=
      heq.deriv_eq
    _ = (0 - 1) * (∫ y in (0 : ℝ)..x, y * v y) +
          (1 - x) * (x * v x) +
          (1 * (∫ y in x..1, (1 - y) * v y) +
            x * -((1 - x) * v x)) := hsplit.deriv
    _ = x * (1 - x) * v x -
          (∫ y in (0 : ℝ)..x, y * v y) -
          x * (1 - x) * v x +
          ∫ y in x..1, (1 - y) * v y := by
      ring

theorem gap3 (v : ℝ → ℝ) (hv : Continuous v) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (integralFunction v) x = firstDerivative v x := by
  intro x hx
  rw [gap2 v hv x hx]
  unfold firstDerivative
  ring

theorem gap4 (v : ℝ → ℝ) (hv : Continuous v) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (integralFunction v)) x =
        -x * v x - (1 - x) * v x := by
  intro x hx
  have heq : deriv (integralFunction v) =ᶠ[nhds x] firstDerivative v := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact gap3 v hv y hy
  have hcA : Continuous (fun y : ℝ => y * v y) :=
    continuous_id.mul hv
  have hiA :
      IntervalIntegrable (fun y : ℝ => y * v y)
        MeasureTheory.volume 0 x :=
    hcA.intervalIntegrable 0 x
  have hA :
      HasDerivAt (fun z : ℝ => ∫ y in (0 : ℝ)..z, y * v y)
        (x * v x) x :=
    intervalIntegral.integral_hasDerivAt_right hiA
      hcA.stronglyMeasurable.stronglyMeasurableAtFilter
      hcA.continuousAt
  have hcB : Continuous (fun y : ℝ => (1 - y) * v y) :=
    (continuous_const.sub continuous_id).mul hv
  have hiB :
      IntervalIntegrable (fun y : ℝ => (1 - y) * v y)
        MeasureTheory.volume x 1 :=
    hcB.intervalIntegrable x 1
  have hB :
      HasDerivAt (fun z : ℝ => ∫ y in z..1, (1 - y) * v y)
        (-((1 - x) * v x)) x :=
    intervalIntegral.integral_hasDerivAt_left hiB
      hcB.stronglyMeasurable.stronglyMeasurableAtFilter
      hcB.continuousAt
  have hfirst :
      HasDerivAt (firstDerivative v)
        (-(x * v x) + -((1 - x) * v x)) x := by
    simpa [firstDerivative] using hA.neg.add hB
  calc
    deriv (deriv (integralFunction v)) x =
        deriv (firstDerivative v) x := heq.deriv_eq
    _ = -x * v x - (1 - x) * v x := by
      rw [hfirst.deriv]
      ring

theorem gap5 (v : ℝ → ℝ) :
    ∀ x : ℝ, -x * v x - (1 - x) * v x = -v x := by
  intro x
  ring

theorem gap6 (v : ℝ → ℝ) (hv : Continuous v) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (integralFunction v)) x = -v x := by
  intro x hx
  rw [gap4 v hv x hx, gap5 v x]

theorem gap7 (v : ℝ → ℝ) (hv : Continuous v) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (integralFunction v)) x = -v x := by
  exact gap6 v hv

end

end ProofGap.Exercise3728
