import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise985_3

noncomputable section

def y (φ ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (Real.log (ψ x) / φ x)

def logRate (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ) : ℝ :=
  ((ψ' / ψ x) * φ x - φ' * Real.log (ψ x)) / φ x ^ 2

def finalDerivative (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ) : ℝ :=
  y φ ψ x *
    (1 / φ x * (ψ' / ψ x) - φ' / φ x ^ 2 * Real.log (ψ x))

theorem gap1 (φ ψ : ℝ → ℝ) (x : ℝ)
    (hφ : φ x ≠ 0) (hψ : 0 < ψ x) :
    Real.log (y φ ψ x) = 1 / φ x * Real.log (ψ x) := by
  simp [y, div_eq_mul_inv, mul_comm]

theorem gap2 (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ)
    (hdφ : HasDerivAt φ φ' x) (hdψ : HasDerivAt ψ ψ' x)
    (hφ : φ x ≠ 0) (hψ : 0 < ψ x) :
    HasDerivAt (fun z => Real.log (y φ ψ z))
      (logRate φ ψ φ' ψ' x) x := by
  have hlog : HasDerivAt (fun z => Real.log (ψ z)) (ψ' / ψ x) x := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log (ne_of_gt hψ)).comp x hdψ
  simpa [y, logRate, mul_comm] using hlog.div hdφ hφ

theorem gap3 (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ)
    (hdφ : HasDerivAt φ φ' x) (hdψ : HasDerivAt ψ ψ' x)
    (hφ : φ x ≠ 0) (hψ : 0 < ψ x) :
    HasDerivAt (y φ ψ) (finalDerivative φ ψ φ' ψ' x) x := by
  have hrate :
      logRate φ ψ φ' ψ' x =
        1 / φ x * (ψ' / ψ x) -
          φ' / φ x ^ 2 * Real.log (ψ x) := by
    unfold logRate
    field_simp [hφ, ne_of_gt hψ] <;> ring
  have hexp :
      HasDerivAt (fun z => Real.exp (Real.log (y φ ψ z)))
        (Real.exp (Real.log (y φ ψ x)) * logRate φ ψ φ' ψ' x) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (Real.log (y φ ψ x))).comp x
        (gap2 φ ψ φ' ψ' x hdφ hdψ hφ hψ)
  simpa [y, finalDerivative, hrate] using hexp

end

end ProofGap.Exercise985_3
