import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise985_4

noncomputable section

def y (φ ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.log (ψ x) / Real.log (φ x)

def quotientDerivative (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ) : ℝ :=
  ((ψ' / ψ x) * Real.log (φ x) -
    (φ' / φ x) * Real.log (ψ x)) / Real.log (φ x) ^ 2

def splitDerivative (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ) : ℝ :=
  ψ' / ψ x * (1 / Real.log (φ x)) -
    φ' / φ x * (Real.log (ψ x) / Real.log (φ x) ^ 2)

theorem gap1 (φ ψ : ℝ → ℝ) (x : ℝ)
    (hφ : 0 < φ x) (hφ1 : φ x ≠ 1) (hψ : 0 < ψ x) :
    y φ ψ x = Real.log (ψ x) / Real.log (φ x) := by
  rfl

theorem gap2 (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ)
    (hdφ : HasDerivAt φ φ' x) (hdψ : HasDerivAt ψ ψ' x)
    (hφ : 0 < φ x) (hφ1 : φ x ≠ 1) (hψ : 0 < ψ x) :
    HasDerivAt (y φ ψ) (quotientDerivative φ ψ φ' ψ' x) x := by
  have hφ0 : φ x ≠ 0 := ne_of_gt hφ
  have hψ0 : ψ x ≠ 0 := ne_of_gt hψ
  have hlogφ : Real.log (φ x) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hφ hφ1
  have hdlogψ :
      HasDerivAt (fun t => Real.log (ψ t)) (ψ' / ψ x) x := by
    convert (Real.hasDerivAt_log hψ0).comp x hdψ using 1 <;>
      simp [div_eq_mul_inv, mul_comm]
  have hdlogφ :
      HasDerivAt (fun t => Real.log (φ t)) (φ' / φ x) x := by
    convert (Real.hasDerivAt_log hφ0).comp x hdφ using 1 <;>
      simp [div_eq_mul_inv, mul_comm]
  have hquot := hdlogψ.div hdlogφ hlogφ
  simpa [y, quotientDerivative, mul_comm] using hquot

theorem gap3 (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ)
    (hdφ : HasDerivAt φ φ' x) (hdψ : HasDerivAt ψ ψ' x)
    (hφ : 0 < φ x) (hφ1 : φ x ≠ 1) (hψ : 0 < ψ x) :
    HasDerivAt (y φ ψ) (splitDerivative φ ψ φ' ψ' x) x := by
  have hlogφ : Real.log (φ x) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hφ hφ1
  have hcoeff :
      splitDerivative φ ψ φ' ψ' x = quotientDerivative φ ψ φ' ψ' x := by
    unfold splitDerivative quotientDerivative
    field_simp [hφ.ne', hψ.ne', hlogφ]
  rw [hcoeff]
  exact gap2 φ ψ φ' ψ' x hdφ hdψ hφ hφ1 hψ

end

end ProofGap.Exercise985_4
