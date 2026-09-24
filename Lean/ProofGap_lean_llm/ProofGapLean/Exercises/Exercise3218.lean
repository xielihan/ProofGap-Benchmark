import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3218

noncomputable section

def u (x y : ℝ) : ℝ :=
  Real.cos (x ^ 2) / y

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def secondXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def secondYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def mixedXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

private theorem hasDerivAt_sq (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
  simpa using (hasDerivAt_id x).pow 2

theorem gap1 :
    ∀ x y : ℝ, y ≠ 0 →
      partialX u x y =
        -(2 * x * Real.sin (x ^ 2) / y) := by
  intro x y hy
  unfold partialX
  change deriv (fun t : ℝ => Real.cos (t ^ 2) / y) x = _
  have h := ((Real.hasDerivAt_cos (x ^ 2)).comp x (hasDerivAt_sq x)).div_const y
  calc
    deriv (fun t : ℝ => Real.cos (t ^ 2) / y) x =
        -Real.sin (x ^ 2) * (2 * x) / y := by
      simpa only [Function.comp_apply] using h.deriv
    _ = -(2 * x * Real.sin (x ^ 2) / y) := by ring

theorem gap2 :
    ∀ x y : ℝ, y ≠ 0 →
      partialY u x y = -(Real.cos (x ^ 2) / y ^ 2) := by
  intro x y hy
  unfold partialY
  change deriv (fun t : ℝ => Real.cos (x ^ 2) / t) y = _
  have h :=
    (hasDerivAt_const y (Real.cos (x ^ 2))).div (hasDerivAt_id y) hy
  calc
    deriv (fun t : ℝ => Real.cos (x ^ 2) / t) y =
        (0 * y - Real.cos (x ^ 2) * 1) / y ^ 2 := by
      simpa only [Pi.div_apply, id_eq] using h.deriv
    _ = -(Real.cos (x ^ 2) / y ^ 2) := by ring

theorem gap3 :
    ∀ x y : ℝ, y ≠ 0 →
      secondXX u x y =
        -((2 * Real.sin (x ^ 2) +
          4 * x ^ 2 * Real.cos (x ^ 2)) / y) := by
  intro x y hy
  unfold secondXX
  have hfun :
      (fun t : ℝ => partialX u t y) =
        (fun t : ℝ => -(2 * t * Real.sin (t ^ 2) / y)) := by
    funext t
    exact gap1 t y hy
  rw [hfun]
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    simpa using
      (hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)
  have hsin :=
    (Real.hasDerivAt_sin (x ^ 2)).comp x (hasDerivAt_sq x)
  have h := ((hlin.mul hsin).div_const y).neg
  calc
    deriv (fun t : ℝ => -(2 * t * Real.sin (t ^ 2) / y)) x =
        -((2 * Real.sin (x ^ 2) +
          2 * x * (Real.cos (x ^ 2) * (2 * x))) / y) := by
      simpa only [Function.comp_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]
        using h.deriv
    _ = -((2 * Real.sin (x ^ 2) +
          4 * x ^ 2 * Real.cos (x ^ 2)) / y) := by ring

theorem gap4 :
    ∀ x y : ℝ, y ≠ 0 →
      secondYY u x y = 2 * Real.cos (x ^ 2) / y ^ 3 := by
  intro x y hy
  unfold secondYY
  change deriv (fun t : ℝ => partialY u x t) y = _
  have hne : ∀ᶠ t : ℝ in nhds y, t ≠ 0 := eventually_ne_nhds hy
  have heq :
      Filter.EventuallyEq (nhds y)
        (fun t : ℝ => partialY u x t)
        (fun t : ℝ => -(Real.cos (x ^ 2) / t ^ 2)) :=
    hne.mono (fun t ht => gap2 x t ht)
  have hbase :=
    ((hasDerivAt_const y (Real.cos (x ^ 2))).div
      (hasDerivAt_sq y) (pow_ne_zero 2 hy)).neg
  have hbase' :
      HasDerivAt (fun t : ℝ => -(Real.cos (x ^ 2) / t ^ 2))
        (-((0 * y ^ 2 - Real.cos (x ^ 2) * (2 * y)) /
          (y ^ 2) ^ 2)) y := by
    simpa only [Pi.div_apply, Pi.neg_apply] using hbase
  have htrans := hbase'.congr_of_eventuallyEq heq
  rw [htrans.deriv]
  field_simp [hy] <;> ring

theorem gap5 :
    ∀ x y : ℝ, y ≠ 0 →
      mixedXY u x y = 2 * x * Real.sin (x ^ 2) / y ^ 2 := by
  intro x y hy
  unfold mixedXY
  change deriv (fun t : ℝ => partialX u x t) y = _
  have hne : ∀ᶠ t : ℝ in nhds y, t ≠ 0 := eventually_ne_nhds hy
  have heq :
      Filter.EventuallyEq (nhds y)
        (fun t : ℝ => partialX u x t)
        (fun t : ℝ => -(2 * x * Real.sin (x ^ 2) / t)) :=
    hne.mono (fun t ht => gap1 x t ht)
  have hbase :=
    ((hasDerivAt_const y (2 * x * Real.sin (x ^ 2))).div
      (hasDerivAt_id y) hy).neg
  have hbase' :
      HasDerivAt (fun t : ℝ => -(2 * x * Real.sin (x ^ 2) / t))
        (-((0 * y - 2 * x * Real.sin (x ^ 2) * 1) / y ^ 2)) y := by
    simpa only [Pi.div_apply, Pi.neg_apply, id_eq] using hbase
  have htrans := hbase'.congr_of_eventuallyEq heq
  rw [htrans.deriv]
  field_simp [hy] <;> ring

end

end ProofGap.Exercise3218
