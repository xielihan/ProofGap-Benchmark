import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace ProofGap.Exercise1180

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def idFun (x : ℝ) : ℝ := x
def d (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ := iterDeriv n f x

def secondFormula (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  (d 1 idFun x * d 2 y x - d 1 y x * d 2 idFun x) /
    d 1 idFun x ^ 3

def thirdFormula (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  (d 1 idFun x *
      (d 1 idFun x * d 3 y x - d 1 y x * d 3 idFun x) -
    3 * d 2 idFun x *
      (d 1 idFun x * d 2 y x - d 1 y x * d 2 idFun x)) /
    d 1 idFun x ^ 5

private theorem deriv_idFun (x : ℝ) : deriv idFun x = 1 := by
  change deriv (fun z : ℝ => z) x = 1
  exact (hasDerivAt_id x).deriv

private theorem deriv_deriv_idFun (x : ℝ) : deriv (deriv idFun) x = 0 := by
  have h : deriv idFun = fun _ : ℝ => 1 := by
    funext z
    exact deriv_idFun z
  rw [h]
  simp

private theorem deriv_deriv_deriv_idFun (x : ℝ) :
    deriv (deriv (deriv idFun)) x = 0 := by
  have h : deriv (deriv idFun) = fun _ : ℝ => 0 := by
    funext z
    exact deriv_deriv_idFun z
  rw [h]
  simp

theorem gap1 (y : ℝ → ℝ) (x : ℝ) :
    d 1 y x = d 1 y x := by
  rfl

theorem gap2 (y : ℝ → ℝ) (x : ℝ) :
    d 2 y x = deriv (iterDeriv 1 y) x := by
  rfl

theorem gap3 (y : ℝ → ℝ) (x : ℝ) (hy : ContDiffAt ℝ 3 y x) :
    deriv (iterDeriv 1 y) x = secondFormula y x := by
  simp [secondFormula, d, iterDeriv, deriv_idFun,
    deriv_deriv_idFun]

theorem gap4 (y : ℝ → ℝ) (x : ℝ) (hy : ContDiffAt ℝ 3 y x) :
    d 2 y x = secondFormula y x := by
  rw [gap2]
  exact gap3 y x hy

theorem gap5 (y : ℝ → ℝ) (x : ℝ) :
    d 3 y x = deriv (secondFormula y) x := by
  have h : secondFormula y = iterDeriv 2 y := by
    funext z
    simp [secondFormula, d, iterDeriv, deriv_idFun,
      deriv_deriv_idFun]
  rw [h]
  rfl

theorem gap6 (y : ℝ → ℝ) (x : ℝ) (hy : ContDiffAt ℝ 3 y x) :
    deriv (secondFormula y) x = thirdFormula y x := by
  calc
    deriv (secondFormula y) x = d 3 y x := (gap5 y x).symm
    _ = thirdFormula y x := by
      simp [thirdFormula, d, iterDeriv, deriv_idFun,
        deriv_deriv_idFun, deriv_deriv_deriv_idFun]

theorem gap7 (y : ℝ → ℝ) (x : ℝ) (hy : ContDiffAt ℝ 3 y x) :
    d 3 y x = thirdFormula y x := by
  rw [gap5]
  exact gap6 y x hy

end

end ProofGap.Exercise1180
