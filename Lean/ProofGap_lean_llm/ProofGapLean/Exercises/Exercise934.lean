import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise934

noncomputable section

def y (a x : ℝ) : ℝ :=
  x / 2 * Real.sqrt (a ^ 2 - x ^ 2) +
    a ^ 2 / 2 * Real.arcsin (x / a)

def expandedDerivative (a x : ℝ) : ℝ :=
  (1 / 2) * Real.sqrt (a ^ 2 - x ^ 2) -
    x ^ 2 / (2 * Real.sqrt (a ^ 2 - x ^ 2)) +
    a ^ 2 / 2 * (1 / Real.sqrt (a ^ 2 - x ^ 2))

def finalDerivative (a x : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 - x ^ 2)

/-- Source: `proof_gap/exercise_934/1.txt`; supplement `a > 0` with
`|x| < a` so the root and inverse sine are in their strict domains. -/
theorem gap1 (a x : ℝ) (ha : 0 < a) (hx : |x| < a) :
    HasDerivAt (y a) (expandedDerivative a x) x := by
  rcases abs_lt.mp hx with ⟨hxlo, hxhi⟩
  have hu : 0 < a ^ 2 - x ^ 2 := by
    nlinarith
  have hs : 0 < Real.sqrt (a ^ 2 - x ^ 2) := Real.sqrt_pos.2 hu
  have hx_sq : x ^ 2 < a ^ 2 := by
    nlinarith
  have ha_sq : 0 < a ^ 2 := pow_pos ha 2
  have hv : 0 < 1 - (x / a) ^ 2 := by
    have hquot : x ^ 2 / a ^ 2 < 1 := (div_lt_one ha_sq).2 hx_sq
    rw [div_pow]
    linarith
  have hz : x / a ∈ Set.Ioo (-1) 1 := by
    constructor
    · apply (lt_div_iff₀ ha).2
      nlinarith
    · apply (div_lt_iff₀ ha).2
      nlinarith
  have hs_sq : Real.sqrt (a ^ 2 - x ^ 2) ^ 2 = a ^ 2 - x ^ 2 :=
    Real.sq_sqrt hu.le
  have hvroot : 0 < Real.sqrt (1 - (x / a) ^ 2) := Real.sqrt_pos.2 hv
  have hv_sq : Real.sqrt (1 - (x / a) ^ 2) ^ 2 = 1 - (x / a) ^ 2 :=
    Real.sq_sqrt hv.le
  have hscale_sq :
      (a * Real.sqrt (1 - (x / a) ^ 2)) ^ 2 =
        Real.sqrt (a ^ 2 - x ^ 2) ^ 2 := by
    rw [mul_pow, hv_sq, hs_sq]
    field_simp [ha.ne']
  have hscale :
      a * Real.sqrt (1 - (x / a) ^ 2) =
        Real.sqrt (a ^ 2 - x ^ 2) := by
    nlinarith [hscale_sq, mul_pos ha hvroot]
  have hinner :
      HasDerivAt (fun t : ℝ => a ^ 2 - t ^ 2) (-2 * x) x := by
    convert HasDerivAt.sub (hasDerivAt_const x (a ^ 2)) ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [mul_comm]
  have hsqrtBase :
      HasDerivAt Real.sqrt
        (2 * Real.sqrt (a ^ 2 - x ^ 2))⁻¹ (a ^ 2 - x ^ 2) := by
    simpa [one_div] using
      (Real.hasDerivAt_sqrt (x := a ^ 2 - x ^ 2) hu.ne')
  have hsqrt :
      HasDerivAt (fun t : ℝ => Real.sqrt (a ^ 2 - t ^ 2))
        (-x / Real.sqrt (a ^ 2 - x ^ 2)) x := by
    have h := hsqrtBase.comp x hinner
    convert h using 1
    field_simp [hs.ne']
  have hdiv :
      HasDerivAt (fun t : ℝ => t / a) (1 / a) x := by
    simpa using HasDerivAt.div_const (hasDerivAt_id x) a
  have harcsinBase :
      HasDerivAt Real.arcsin
        (Real.sqrt (1 - (x / a) ^ 2))⁻¹ (x / a) := by
    simpa [one_div] using
      (Real.hasDerivAt_arcsin (x := x / a)
        (by nlinarith [hz.1]) (by nlinarith [hz.2]))
  have harcsin :
      HasDerivAt (fun t : ℝ => Real.arcsin (t / a))
        (1 / Real.sqrt (a ^ 2 - x ^ 2)) x := by
    have h := harcsinBase.comp x hdiv
    convert h using 1
    rw [← hscale]
    field_simp [ha.ne', hvroot.ne']
  have hlinear :
      HasDerivAt (fun t : ℝ => t / 2) (1 / 2) x := by
    simpa using HasDerivAt.div_const (hasDerivAt_id x) 2
  have hfirst :
      HasDerivAt
        (fun t : ℝ => t / 2 * Real.sqrt (a ^ 2 - t ^ 2))
        ((1 / 2) * Real.sqrt (a ^ 2 - x ^ 2) -
          x ^ 2 / (2 * Real.sqrt (a ^ 2 - x ^ 2))) x := by
    have h := HasDerivAt.mul hlinear hsqrt
    convert h using 1
    field_simp [hs.ne']
    ring
  have hsecond :
      HasDerivAt
        (fun t : ℝ => a ^ 2 / 2 * Real.arcsin (t / a))
        (a ^ 2 / 2 * (1 / Real.sqrt (a ^ 2 - x ^ 2))) x := by
    simpa using HasDerivAt.mul (hasDerivAt_const x (a ^ 2 / 2)) harcsin
  simpa [y, expandedDerivative] using HasDerivAt.add hfirst hsecond

/-- Source: `proof_gap/exercise_934/2.txt`; strict interiority makes the
square-root denominator positive. -/
theorem gap2 (a x : ℝ) (ha : 0 < a) (hx : |x| < a) :
    expandedDerivative a x = finalDerivative a x := by
  rcases abs_lt.mp hx with ⟨hxlo, hxhi⟩
  have hu : 0 < a ^ 2 - x ^ 2 := by
    nlinarith
  have hs : 0 < Real.sqrt (a ^ 2 - x ^ 2) := Real.sqrt_pos.2 hu
  have hs_sq : Real.sqrt (a ^ 2 - x ^ 2) ^ 2 = a ^ 2 - x ^ 2 :=
    Real.sq_sqrt hu.le
  unfold expandedDerivative finalDerivative
  field_simp [hs.ne'] <;> nlinarith [hs_sq]

/-- Source: `proof_gap/exercise_934/3.txt`; retain the positive scale and open
inverse-trigonometric domain. -/
theorem gap3 (a x : ℝ) (ha : 0 < a) (hx : |x| < a) :
    HasDerivAt (y a) (finalDerivative a x) x := by
  rw [← gap2 a x ha hx]
  exact gap1 a x ha hx

end

end ProofGap.Exercise934
