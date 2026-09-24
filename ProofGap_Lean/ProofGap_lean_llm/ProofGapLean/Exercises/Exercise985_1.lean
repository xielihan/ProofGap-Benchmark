import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise985_1

noncomputable section

def y (φ ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (φ x ^ 2 + ψ x ^ 2)

theorem gap1 (φ ψ : ℝ → ℝ) (φ' ψ' x : ℝ)
    (hφ : HasDerivAt φ φ' x) (hψ : HasDerivAt ψ ψ' x)
    (hpos : 0 < φ x ^ 2 + ψ x ^ 2) :
    HasDerivAt (y φ ψ)
      ((φ x * φ' + ψ x * ψ') / Real.sqrt (φ x ^ 2 + ψ x ^ 2)) x := by
  unfold y
  have hsqφ : HasDerivAt (fun z => φ z * φ z)
      (φ' * φ x + φ x * φ') x :=
    hφ.mul hφ
  have hsqψ : HasDerivAt (fun z => ψ z * ψ z)
      (ψ' * ψ x + ψ x * ψ') x :=
    hψ.mul hψ
  have hsprod : HasDerivAt
      (fun z => φ z * φ z + ψ z * ψ z)
      ((φ' * φ x + φ x * φ') + (ψ' * ψ x + ψ x * ψ')) x :=
    hsqφ.add hsqψ
  have hs : HasDerivAt (fun z => φ z ^ 2 + ψ z ^ 2)
      ((φ' * φ x + φ x * φ') + (ψ' * ψ x + ψ x * ψ')) x := by
    simpa only [pow_two] using hsprod
  have hs_ne : φ x ^ 2 + ψ x ^ 2 ≠ 0 := ne_of_gt hpos
  have hsqrt_ne : Real.sqrt (φ x ^ 2 + ψ x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  convert (Real.hasDerivAt_sqrt hs_ne).comp x hs using 1 <;>
    field_simp [hsqrt_ne] <;> ring_nf

end

end ProofGap.Exercise985_1
