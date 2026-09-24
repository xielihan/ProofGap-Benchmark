import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1114

noncomputable section

def y (x : ℝ) : ℝ := Real.tan x

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

theorem gap1 (x : ℝ) (hx : Real.cos x ≠ 0) :
    deriv y x = 1 / Real.cos x ^ 2 := by
  change deriv Real.tan x = 1 / Real.cos x ^ 2
  exact (Real.hasDerivAt_tan hx).deriv

theorem gap2 (x : ℝ) (hx : Real.cos x ≠ 0) :
    secondDeriv y x = 2 * Real.sin x / Real.cos x ^ 3 := by
  unfold secondDeriv
  have hcos : ∀ᶠ t in nhds x, Real.cos t ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hx
  have heq :
      (fun t => deriv y t) =ᶠ[nhds x] (fun t => 1 / Real.cos t ^ 2) :=
    hcos.mono fun t ht => gap1 t ht
  calc
    deriv (fun t => deriv y t) x =
        deriv (fun t => 1 / Real.cos t ^ 2) x := heq.deriv_eq
    _ = 2 * Real.sin x / Real.cos x ^ 3 := by
      have hsq :
          HasDerivAt (fun t : ℝ => Real.cos t ^ 2)
            (-2 * Real.cos x * Real.sin x) x := by
        convert (Real.hasDerivAt_cos x).pow 2 using 1 <;> ring
      have hinv :
          HasDerivAt (fun t : ℝ => (Real.cos t ^ 2)⁻¹)
            (2 * Real.sin x / Real.cos x ^ 3) x := by
        convert hsq.inv (pow_ne_zero 2 hx) using 1 <;>
          field_simp [hx] <;> ring
      have hderiv :
          HasDerivAt (fun t : ℝ => 1 / Real.cos t ^ 2)
            (2 * Real.sin x / Real.cos x ^ 3) x := by
        simpa only [one_div] using hinv
      exact hderiv.deriv

end

end ProofGap.Exercise1114
