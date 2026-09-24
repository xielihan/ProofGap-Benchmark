import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace ProofGap.Exercise985_2

noncomputable section

def y (φ ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.arctan (φ x / ψ x)

def rawDerivative (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ) : ℝ :=
  1 / (1 + φ x ^ 2 / ψ x ^ 2) *
    ((φ' * ψ x - ψ' * φ x) / ψ x ^ 2)

def finalDerivative (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ) : ℝ :=
  (φ' * ψ x - ψ' * φ x) / (φ x ^ 2 + ψ x ^ 2)

theorem gap1 (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ)
    (hφ : HasDerivAt φ φ' x) (hψ : HasDerivAt ψ ψ' x)
    (hden : ψ x ≠ 0) :
    HasDerivAt (y φ ψ) (rawDerivative φ ψ φ' ψ' x) x := by
  unfold y rawDerivative
  have hquot : HasDerivAt (fun z => φ z / ψ z)
      ((φ' * ψ x - φ x * ψ') / ψ x ^ 2) x :=
    hφ.div hψ hden
  have hcomp :=
    (Real.hasDerivAt_arctan (φ x / ψ x)).comp x hquot
  convert hcomp using 1 <;> ring

theorem gap2 (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ)
    (hφ : HasDerivAt φ φ' x) (hψ : HasDerivAt ψ ψ' x)
    (hden : ψ x ≠ 0) :
    HasDerivAt (y φ ψ) (finalDerivative φ ψ φ' ψ' x) x := by
  have hψsq : 0 < ψ x ^ 2 := by
    positivity
  have hsum : φ x ^ 2 + ψ x ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg (φ x)) hψsq)
  have hnormalize :
      1 + φ x ^ 2 / ψ x ^ 2 =
        (φ x ^ 2 + ψ x ^ 2) / ψ x ^ 2 := by
    field_simp [hden]
    ring
  have hderiv :
      rawDerivative φ ψ φ' ψ' x = finalDerivative φ ψ φ' ψ' x := by
    unfold rawDerivative finalDerivative
    rw [hnormalize]
    field_simp [hden, hsum]
  rw [← hderiv]
  exact gap1 φ ψ φ' ψ' x hφ hψ hden

end

end ProofGap.Exercise985_2
