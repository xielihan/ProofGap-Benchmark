import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3729

noncomputable section

open scoped Interval

def integralFunction (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∫ z in x / y..x * y, (x - y * z) * f z

def partialX (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => integralFunction f s y) x

def mixedXY (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def expandedMixed (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (x - x * y ^ 2) * f (x * y) +
    y * (-2 * x * y) * f (x * y) +
    y * (x - x * y ^ 2) * deriv f (x * y) * x +
    x * f (x * y) +
    (x / y ^ 2) * f (x / y)

def simplifiedMixed (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * (2 - 3 * y ^ 2) * f (x * y) +
    x ^ 2 * y * (1 - y ^ 2) * deriv f (x * y) +
    (x / y ^ 2) * f (x / y)

private theorem hasDerivAt_movingIntervalIntegral
    (g a b : ℝ → ℝ) (y a' b' : ℝ)
    (hg : Continuous g)
    (ha : HasDerivAt a a' y) (hb : HasDerivAt b b' y) :
    HasDerivAt (fun t => ∫ z in a t..b t, g z)
      (g (b y) * b' - g (a y) * a') y := by
  have hG (u : ℝ) :
      HasDerivAt (fun v : ℝ => ∫ z in (0 : ℝ)..v, g z) (g u) u :=
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable (0 : ℝ) u)
      hg.stronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt
  have heq (t : ℝ) :
      (∫ z in a t..b t, g z) =
        (∫ z in (0 : ℝ)..b t, g z) - ∫ z in (0 : ℝ)..a t, g z := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (a t) 0) (hg.intervalIntegrable 0 (b t))]
    rw [intervalIntegral.integral_symm]
    ring
  have hfun :
      (fun t => ∫ z in a t..b t, g z) =
        (fun t => (∫ z in (0 : ℝ)..b t, g z) - ∫ z in (0 : ℝ)..a t, g z) :=
    funext heq
  rw [hfun]
  exact ((hG (b y)).comp y hb).sub ((hG (a y)).comp y ha)

private theorem hasDerivAt_integralFunction_x
    (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (x y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun s => integralFunction f s y)
      (y * (x - x * y ^ 2) * f (x * y) +
        ∫ z in x / y..x * y, f z) x := by
  have ha : HasDerivAt (fun s : ℝ => s / y) (1 / y) x := by
    simpa [div_eq_mul_inv] using
      (hasDerivAt_id x).mul (hasDerivAt_const x y⁻¹)
  have hb : HasDerivAt (fun s : ℝ => s * y) y x := by
    simpa using (hasDerivAt_id x).mul (hasDerivAt_const x y)
  have hIf := hasDerivAt_movingIntervalIntegral
    (g := f) (a := fun s : ℝ => s / y) (b := fun s : ℝ => s * y)
    (y := x) (a' := 1 / y) (b' := y) hf.continuous ha hb
  have hIz := hasDerivAt_movingIntervalIntegral
    (g := fun z : ℝ => z * f z)
    (a := fun s : ℝ => s / y) (b := fun s : ℝ => s * y)
    (y := x) (a' := 1 / y) (b' := y)
    (continuous_id.mul hf.continuous) ha hb
  have hdecomp (s : ℝ) :
      integralFunction f s y =
        s * (∫ z in s / y..s * y, f z) -
          y * (∫ z in s / y..s * y, z * f z) := by
    unfold integralFunction
    calc
      (∫ z in s / y..s * y, (s - y * z) * f z) =
          ∫ z in s / y..s * y, s * f z - y * (z * f z) := by
            apply intervalIntegral.integral_congr
            intro z hz
            ring
      _ = (∫ z in s / y..s * y, s * f z) -
          ∫ z in s / y..s * y, y * (z * f z) := by
            exact intervalIntegral.integral_sub
              ((continuous_const.mul hf.continuous).intervalIntegrable _ _)
              ((continuous_const.mul
                (continuous_id.mul hf.continuous)).intervalIntegrable _ _)
      _ = s * (∫ z in s / y..s * y, f z) -
          y * (∫ z in s / y..s * y, z * f z) := by
            rw [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
  have hfun :
      (fun s => integralFunction f s y) =
        (fun s =>
          s * (∫ z in s / y..s * y, f z) -
            y * (∫ z in s / y..s * y, z * f z)) :=
    funext hdecomp
  have hmain :=
    ((hasDerivAt_id x).mul hIf).sub ((hasDerivAt_const x y).mul hIz)
  simp at hmain
  rw [hfun]
  convert hmain using 1
  field_simp [hy] <;> ring

theorem gap1 (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (x y : ℝ) (hy : y ≠ 0) :
    partialX f x y =
      y * (x - x * y ^ 2) * f (x * y) +
        ∫ z in x / y..x * y, f z := by
  unfold partialX
  exact (hasDerivAt_integralFunction_x f hf x y hy).deriv

theorem gap2 (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (x y : ℝ) (hy : y ≠ 0) :
    mixedXY f x y = expandedMixed f x y := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 y := by
    exact hasDerivAt_id y
  have hxy : HasDerivAt (fun t : ℝ => x * t) x y := by
    simpa using (hasDerivAt_const y x).mul (hasDerivAt_id y)
  have hdiv : HasDerivAt (fun t : ℝ => x / t) (-x / y ^ 2) y := by
    convert (hasDerivAt_const y x).div hid hy using 1 <;>
      field_simp [hy] <;> ring
  have hsquare : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    have hmul :
        HasDerivAt (fun t : ℝ => t * t) (1 * y + y * 1) y :=
      hid.mul hid
    simpa only [pow_two, one_mul, mul_one, two_mul] using hmul
  have hxSquare : HasDerivAt (fun t : ℝ => x * t ^ 2) (x * (2 * y)) y := by
    simpa using (hasDerivAt_const y x).mul hsquare
  have hpoly :
      HasDerivAt (fun t : ℝ => x - x * t ^ 2) (-2 * x * y) y := by
    convert (hasDerivAt_const y x).sub hxSquare using 1 <;> ring
  have hfcomp :
      HasDerivAt (fun t : ℝ => f (x * t)) (deriv f (x * y) * x) y :=
    (hf (x * y)).hasDerivAt.comp y hxy
  have hprod := ((hasDerivAt_id y).mul hpoly).mul hfcomp
  have hmove := hasDerivAt_movingIntervalIntegral
    (g := f) (a := fun t : ℝ => x / t) (b := fun t : ℝ => x * t)
    (y := y) (a' := -x / y ^ 2) (b' := x) hf.continuous hdiv hxy
  simp at hprod hmove
  have hformula :
      HasDerivAt
        (fun t : ℝ =>
          t * (x - x * t ^ 2) * f (x * t) +
            ∫ z in x / t..x * t, f z)
        (expandedMixed f x y) y := by
    convert hprod.add hmove using 1
    unfold expandedMixed
    field_simp [hy] <;> ring
  have heq :
      (fun t : ℝ => partialX f x t) =ᶠ[nhds y]
        (fun t : ℝ =>
          t * (x - x * t ^ 2) * f (x * t) +
            ∫ z in x / t..x * t, f z) :=
    (eventually_ne_nhds hy).mono (fun t ht => gap1 f hf x t ht)
  unfold mixedXY
  calc
    deriv (fun t => partialX f x t) y =
        deriv
          (fun t : ℝ =>
            t * (x - x * t ^ 2) * f (x * t) +
              ∫ z in x / t..x * t, f z) y := heq.deriv_eq
    _ = expandedMixed f x y := hformula.deriv

theorem gap3 (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (x y : ℝ) (hy : y ≠ 0) :
    mixedXY f x y = simplifiedMixed f x y := by
  rw [gap2 f hf x y hy]
  unfold expandedMixed simplifiedMixed
  ring

end

end ProofGap.Exercise3729
