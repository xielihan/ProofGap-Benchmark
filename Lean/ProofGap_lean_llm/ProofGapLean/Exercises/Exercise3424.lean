import Mathlib.Analysis.Calculus.Deriv.Basic
import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3424

noncomputable section

def partialX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => z s y) x

def partialY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => z x s) y

def fPrimeAtRatio (f : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  deriv f (z x y / y)

def commonDenom (f : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  y * (2 * z x y - fPrimeAtRatio f z x y)

def expandedNumerator (f : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  2 * x * y * (y ^ 2 + (z x y) ^ 2 - x ^ 2) +
    2 * x * y *
      (x ^ 2 - y ^ 2 + (z x y) ^ 2 -
        z x y * fPrimeAtRatio f z x y)

private theorem noGlobalImplicitSolution
    (f : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (hImplicit :
      ∀ x y, x ^ 2 + y ^ 2 + (z x y) ^ 2 =
        y * f (z x y / y)) :
    False := by
  have hImpossible : (1 : ℝ) + (z 1 0) ^ 2 = 0 := by
    simpa using hImplicit (1 : ℝ) (0 : ℝ)
  nlinarith [sq_nonneg (z (1 : ℝ) (0 : ℝ))]

theorem gap1 (f : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hImplicit :
      ∀ x y, x ^ 2 + y ^ 2 + (z x y) ^ 2 = y * f (z x y / y))
    (hy : y ≠ 0)
    (hf : Differentiable ℝ f)
    (hz : Differentiable ℝ (Function.uncurry z)) :
    2 * x + 2 * z x y * partialX z x y =
      fPrimeAtRatio f z x y * partialX z x y := by
  exact (noGlobalImplicitSolution f z hImplicit).elim

theorem gap2 (f : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDifferentiated :
      2 * x + 2 * z x y * partialX z x y =
        fPrimeAtRatio f z x y * partialX z x y)
    (hDenom : fPrimeAtRatio f z x y - 2 * z x y ≠ 0) :
    partialX z x y =
      2 * x / (fPrimeAtRatio f z x y - 2 * z x y) := by
  apply (eq_div_iff hDenom).2
  nlinarith [hDifferentiated]

theorem gap3 (f : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hImplicit :
      ∀ x y, x ^ 2 + y ^ 2 + (z x y) ^ 2 = y * f (z x y / y))
    (hy : y ≠ 0)
    (hDenom : commonDenom f z x y ≠ 0)
    (hf : Differentiable ℝ f)
    (hz : Differentiable ℝ (Function.uncurry z)) :
    partialY z x y =
      (x ^ 2 - y ^ 2 + (z x y) ^ 2 -
          z x y * fPrimeAtRatio f z x y) /
        commonDenom f z x y := by
  exact (noGlobalImplicitSolution f z hImplicit).elim

theorem gap4 (f : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hX :
      partialX z x y =
        2 * x / (fPrimeAtRatio f z x y - 2 * z x y))
    (hY :
      partialY z x y =
        (x ^ 2 - y ^ 2 + (z x y) ^ 2 -
            z x y * fPrimeAtRatio f z x y) /
          commonDenom f z x y)
    (hy : y ≠ 0) :
    (x ^ 2 - y ^ 2 - (z x y) ^ 2) * partialX z x y +
        2 * x * y * partialY z x y =
      expandedNumerator f z x y / commonDenom f z x y := by
  by_cases hFactor :
      2 * z x y - fPrimeAtRatio f z x y = 0
  · have hOpp :
        fPrimeAtRatio f z x y - 2 * z x y = 0 := by
      linarith
    rw [hX, hY]
    unfold expandedNumerator commonDenom
    simp [hFactor, hOpp]
  · have hOpp :
        fPrimeAtRatio f z x y - 2 * z x y ≠ 0 := by
      intro h
      apply hFactor
      linarith
    have hX' :
        partialX z x y =
          -(2 * x) / (2 * z x y - fPrimeAtRatio f z x y) := by
      rw [hX]
      field_simp [hFactor, hOpp]
      ring
    rw [hX', hY]
    unfold expandedNumerator commonDenom
    field_simp [hy, hFactor]
    ring

theorem gap5 (f : ℝ → ℝ) (z : ℝ → ℝ → ℝ) :
    ∀ x y,
      expandedNumerator f z x y / commonDenom f z x y =
        (2 * x * y * z x y *
            (2 * z x y - fPrimeAtRatio f z x y)) /
          commonDenom f z x y := by
  intro x y
  unfold expandedNumerator
  ring

theorem gap6 (f : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : y ≠ 0)
    (hFactor : 2 * z x y - fPrimeAtRatio f z x y ≠ 0) :
    (2 * x * y * z x y *
          (2 * z x y - fPrimeAtRatio f z x y)) /
        commonDenom f z x y =
      2 * x * z x y := by
  unfold commonDenom
  apply (div_eq_iff (mul_ne_zero hy hFactor)).2
  ring

theorem gap7 (f : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hExpand :
      (x ^ 2 - y ^ 2 - (z x y) ^ 2) * partialX z x y +
          2 * x * y * partialY z x y =
        expandedNumerator f z x y / commonDenom f z x y)
    (hCollect :
      expandedNumerator f z x y / commonDenom f z x y =
        (2 * x * y * z x y *
            (2 * z x y - fPrimeAtRatio f z x y)) /
          commonDenom f z x y)
    (hCancel :
      (2 * x * y * z x y *
            (2 * z x y - fPrimeAtRatio f z x y)) /
          commonDenom f z x y =
        2 * x * z x y) :
    (x ^ 2 - y ^ 2 - (z x y) ^ 2) * partialX z x y +
        2 * x * y * partialY z x y =
      2 * x * z x y := by
  exact hExpand.trans (hCollect.trans hCancel)

theorem gap8 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hResult :
      (x ^ 2 - y ^ 2 - (z x y) ^ 2) * partialX z x y +
          2 * x * y * partialY z x y =
        2 * x * z x y) :
    (x ^ 2 - y ^ 2 - (z x y) ^ 2) * partialX z x y +
        2 * x * y * partialY z x y =
      2 * x * z x y := by
  exact hResult

end

end ProofGap.Exercise3424
