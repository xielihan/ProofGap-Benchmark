import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace ProofGap.Exercise1179

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def idFun (x : ℝ) : ℝ := x
def d (n : ℕ) (x : ℝ) : ℝ := iterDeriv n idFun x
def y (f : ℝ → ℝ) (x : ℝ) : ℝ := f x

private theorem idFunDerivativeValues (x : ℝ) :
    d 1 x = 1 ∧ d 2 x = 0 ∧ d 3 x = 0 ∧ d 4 x = 0 := by
  have h0 : idFun = id := by
    funext z
    rfl
  have h1 : deriv idFun = fun _ : ℝ => 1 := by
    rw [h0]
    funext z
    simpa using (hasDerivAt_id z).deriv
  have h2 : deriv (deriv idFun) = fun _ : ℝ => 0 := by
    rw [h1]
    funext z
    simp
  have h3 : deriv (deriv (deriv idFun)) = fun _ : ℝ => 0 := by
    rw [h2]
    funext z
    simp
  have h4 : deriv (deriv (deriv (deriv idFun))) = fun _ : ℝ => 0 := by
    rw [h3]
    funext z
    simp
  simp [d, iterDeriv, h1, h2, h3, h4]

theorem gap1 (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ 4 f x) :
    iterDeriv 1 (y f) x = iterDeriv 1 f x * d 1 x := by
  have hy : y f = f := by
    funext z
    rfl
  have hd := idFunDerivativeValues x
  rw [hy]
  simp [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]

theorem gap2 (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ 4 f x) :
    iterDeriv 2 (y f) x =
      iterDeriv 2 f x * d 1 x ^ 2 + iterDeriv 1 f x * d 2 x := by
  have hy : y f = f := by
    funext z
    rfl
  have hd := idFunDerivativeValues x
  rw [hy]
  simp [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]

theorem gap3 (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ 4 f x) :
    iterDeriv 3 (y f) x =
      iterDeriv 3 f x * d 1 x ^ 3 +
        3 * iterDeriv 2 f x * d 1 x * d 2 x +
        iterDeriv 1 f x * d 3 x := by
  have hy : y f = f := by
    funext z
    rfl
  have hd := idFunDerivativeValues x
  rw [hy]
  simp [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]

theorem gap4 (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ 4 f x) :
    iterDeriv 4 (y f) x =
      iterDeriv 4 f x * d 1 x ^ 4 +
        3 * iterDeriv 3 f x * d 1 x ^ 2 * d 2 x +
        3 * iterDeriv 3 f x * d 1 x ^ 2 * d 2 x +
        3 * iterDeriv 2 f x * (d 2 x ^ 2 + d 1 x * d 3 x) +
        iterDeriv 2 f x * d 1 x * d 3 x +
        iterDeriv 1 f x * d 4 x := by
  have hy : y f = f := by
    funext z
    rfl
  have hd := idFunDerivativeValues x
  rw [hy]
  simp [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]

theorem gap5 (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ 4 f x) :
    iterDeriv 4 (y f) x =
      iterDeriv 4 f x * d 1 x ^ 4 +
        6 * iterDeriv 3 f x * d 1 x ^ 2 * d 2 x +
        4 * iterDeriv 2 f x * d 1 x * d 3 x +
        3 * iterDeriv 2 f x * d 2 x ^ 2 +
        iterDeriv 1 f x * d 4 x := by
  have hy : y f = f := by
    funext z
    rfl
  have hd := idFunDerivativeValues x
  rw [hy]
  simp [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]

end

end ProofGap.Exercise1179
