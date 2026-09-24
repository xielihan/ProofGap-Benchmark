import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3403

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def solvedDifferentialU (u v : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  (-(x * u x y + y * v x y) * dx +
      (x * v x y - y * u x y) * dy) /
    (x ^ 2 + y ^ 2)

def solvedDifferentialV (u v : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  ((y * u x y - x * v x y) * dx -
      (x * u x y + y * v x y) * dy) /
    (x ^ 2 + y ^ 2)

theorem gap1 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hFirst :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        p.1 * u p.1 p.2 - p.2 * v p.1 p.2 = 0) :
    x * differential u x y dx dy - y * differential v x y dx dy =
      v x y * dy - u x y * dx := by
  have hpathX : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hpathY : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have hux : DifferentiableAt ℝ (fun t : ℝ => u t y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      huDiff.comp x hpathX.differentiableAt
  have hvx : DifferentiableAt ℝ (fun t : ℝ => v t y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      hvDiff.comp x hpathX.differentiableAt
  have huy : DifferentiableAt ℝ (fun t : ℝ => u x t) y := by
    simpa [Function.comp_def, Function.uncurry] using
      huDiff.comp y hpathY.differentiableAt
  have hvy : DifferentiableAt ℝ (fun t : ℝ => v x t) y := by
    simpa [Function.comp_def, Function.uncurry] using
      hvDiff.comp y hpathY.differentiableAt
  have hFirstX :
      (fun t : ℝ => t * u t y - y * v t y) =ᶠ[nhds x] (fun _ => 0) := by
    simpa using hpathX.continuousAt.eventually hFirst
  have hFirstY :
      (fun t : ℝ => x * u x t - t * v x t) =ᶠ[nhds y] (fun _ => 0) := by
    simpa using hpathY.continuousAt.eventually hFirst
  have hderivX :
      HasDerivAt (fun t : ℝ => t * u t y - y * v t y)
        (u x y + x * partialX u x y - y * partialX v x y) x := by
    simpa [partialX] using
      (((hasDerivAt_id x).mul hux.hasDerivAt).sub
        ((hasDerivAt_const x y).mul hvx.hasDerivAt))
  have hderivY :
      HasDerivAt (fun t : ℝ => x * u x t - t * v x t)
        (x * partialY u x y - (v x y + y * partialY v x y)) y := by
    simpa [partialY] using
      (((hasDerivAt_const y x).mul huy.hasDerivAt).sub
        ((hasDerivAt_id y).mul hvy.hasDerivAt))
  have hzeroX :
      HasDerivAt (fun t : ℝ => t * u t y - y * v t y) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hFirstX
  have hzeroY :
      HasDerivAt (fun t : ℝ => x * u x t - t * v x t) 0 y :=
    (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hFirstY
  have hx :
      x * partialX u x y - y * partialX v x y = -u x y := by
    linarith [hderivX.unique hzeroX]
  have hy :
      x * partialY u x y - y * partialY v x y = v x y := by
    linarith [hderivY.unique hzeroY]
  calc
    x * differential u x y dx dy - y * differential v x y dx dy =
        (x * partialX u x y - y * partialX v x y) * dx +
          (x * partialY u x y - y * partialY v x y) * dy := by
            simp only [differential]
            ring
    _ = (-u x y) * dx + v x y * dy := by rw [hx, hy]
    _ = v x y * dy - u x y * dx := by ring

theorem gap2 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hSecond :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        p.2 * u p.1 p.2 + p.1 * v p.1 p.2 = 1) :
    y * differential u x y dx dy + x * differential v x y dx dy =
      -(v x y) * dx - u x y * dy := by
  have hpathX : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hpathY : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have hux : DifferentiableAt ℝ (fun t : ℝ => u t y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      huDiff.comp x hpathX.differentiableAt
  have hvx : DifferentiableAt ℝ (fun t : ℝ => v t y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      hvDiff.comp x hpathX.differentiableAt
  have huy : DifferentiableAt ℝ (fun t : ℝ => u x t) y := by
    simpa [Function.comp_def, Function.uncurry] using
      huDiff.comp y hpathY.differentiableAt
  have hvy : DifferentiableAt ℝ (fun t : ℝ => v x t) y := by
    simpa [Function.comp_def, Function.uncurry] using
      hvDiff.comp y hpathY.differentiableAt
  have hSecondX :
      (fun t : ℝ => y * u t y + t * v t y) =ᶠ[nhds x] (fun _ => 1) := by
    simpa using hpathX.continuousAt.eventually hSecond
  have hSecondY :
      (fun t : ℝ => t * u x t + x * v x t) =ᶠ[nhds y] (fun _ => 1) := by
    simpa using hpathY.continuousAt.eventually hSecond
  have hderivX :
      HasDerivAt (fun t : ℝ => y * u t y + t * v t y)
        (y * partialX u x y + (v x y + x * partialX v x y)) x := by
    simpa [partialX] using
      (((hasDerivAt_const x y).mul hux.hasDerivAt).add
        ((hasDerivAt_id x).mul hvx.hasDerivAt))
  have hderivY :
      HasDerivAt (fun t : ℝ => t * u x t + x * v x t)
        ((u x y + y * partialY u x y) + x * partialY v x y) y := by
    simpa [partialY] using
      (((hasDerivAt_id y).mul huy.hasDerivAt).add
        ((hasDerivAt_const y x).mul hvy.hasDerivAt))
  have hzeroX :
      HasDerivAt (fun t : ℝ => y * u t y + t * v t y) 0 x :=
    (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq hSecondX
  have hzeroY :
      HasDerivAt (fun t : ℝ => t * u x t + x * v x t) 0 y :=
    (hasDerivAt_const y (1 : ℝ)).congr_of_eventuallyEq hSecondY
  have hx :
      y * partialX u x y + x * partialX v x y = -v x y := by
    linarith [hderivX.unique hzeroX]
  have hy :
      y * partialY u x y + x * partialY v x y = -u x y := by
    linarith [hderivY.unique hzeroY]
  calc
    y * differential u x y dx dy + x * differential v x y dx dy =
        (y * partialX u x y + x * partialX v x y) * dx +
          (y * partialY u x y + x * partialY v x y) * dy := by
            simp only [differential]
            ring
    _ = (-v x y) * dx + (-u x y) * dy := by rw [hx, hy]
    _ = -(v x y) * dx - u x y * dy := by ring

theorem gap3 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hNonzero : x ^ 2 + y ^ 2 ≠ 0)
    (hFirst :
      x * differential u x y dx dy - y * differential v x y dx dy =
        v x y * dy - u x y * dx)
    (hSecond :
      y * differential u x y dx dy + x * differential v x y dx dy =
        -(v x y) * dx - u x y * dy) :
    differential u x y dx dy =
      solvedDifferentialU u v x y dx dy := by
  unfold solvedDifferentialU
  apply (eq_div_iff hNonzero).2
  calc
    differential u x y dx dy * (x ^ 2 + y ^ 2) =
        x * (x * differential u x y dx dy -
          y * differential v x y dx dy) +
        y * (y * differential u x y dx dy +
          x * differential v x y dx dy) := by ring
    _ = x * (v x y * dy - u x y * dx) +
        y * (-(v x y) * dx - u x y * dy) := by
          rw [hFirst, hSecond]
    _ = -(x * u x y + y * v x y) * dx +
        (x * v x y - y * u x y) * dy := by ring

theorem gap4 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : x ^ 2 + y ^ 2 ≠ 0)
    (hDu :
      differential u x y 1 0 =
        solvedDifferentialU u v x y 1 0) :
    partialX u x y =
      -(x * u x y + y * v x y) / (x ^ 2 + y ^ 2) := by
  simpa [differential, solvedDifferentialU] using hDu

theorem gap5 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : x ^ 2 + y ^ 2 ≠ 0)
    (hDu :
      differential u x y 0 1 =
        solvedDifferentialU u v x y 0 1) :
    partialY u x y =
      (x * v x y - y * u x y) / (x ^ 2 + y ^ 2) := by
  simpa [differential, solvedDifferentialU] using hDu

theorem gap6 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : x ^ 2 + y ^ 2 ≠ 0)
    (hFirst :
      x * differential u x y 1 0 - y * differential v x y 1 0 =
        -u x y)
    (hSecond :
      y * differential u x y 1 0 + x * differential v x y 1 0 =
        -v x y) :
    partialX v x y =
      (y * u x y - x * v x y) / (x ^ 2 + y ^ 2) := by
  have hFirst' :
      x * partialX u x y - y * partialX v x y = -u x y := by
    simpa [differential] using hFirst
  have hSecond' :
      y * partialX u x y + x * partialX v x y = -v x y := by
    simpa [differential] using hSecond
  apply (eq_div_iff hNonzero).2
  calc
    partialX v x y * (x ^ 2 + y ^ 2) =
        -y * (x * partialX u x y - y * partialX v x y) +
          x * (y * partialX u x y + x * partialX v x y) := by ring
    _ = -y * (-u x y) + x * (-v x y) := by rw [hFirst', hSecond']
    _ = y * u x y - x * v x y := by ring

theorem gap7 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : x ^ 2 + y ^ 2 ≠ 0)
    (hFirst :
      x * differential u x y 0 1 - y * differential v x y 0 1 =
        v x y)
    (hSecond :
      y * differential u x y 0 1 + x * differential v x y 0 1 =
        -u x y) :
    partialY v x y =
      -(x * u x y + y * v x y) / (x ^ 2 + y ^ 2) := by
  have hFirst' :
      x * partialY u x y - y * partialY v x y = v x y := by
    simpa [differential] using hFirst
  have hSecond' :
      y * partialY u x y + x * partialY v x y = -u x y := by
    simpa [differential] using hSecond
  apply (eq_div_iff hNonzero).2
  calc
    partialY v x y * (x ^ 2 + y ^ 2) =
        -y * (x * partialY u x y - y * partialY v x y) +
          x * (y * partialY u x y + x * partialY v x y) := by ring
    _ = -y * v x y + x * (-u x y) := by rw [hFirst', hSecond']
    _ = -(x * u x y + y * v x y) := by ring

end

end ProofGap.Exercise3403
