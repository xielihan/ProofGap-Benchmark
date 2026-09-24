import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise905

noncomputable section

def ratio (x : ℝ) : ℝ := (1 + Real.cos x) / Real.sin x

def y (x : ℝ) : ℝ :=
  -(Real.cos x / (2 * Real.sin x ^ 2)) +
    Real.log (Real.sqrt (ratio x))

def expandedDerivative (x : ℝ) : ℝ :=
  (Real.sin x ^ 3 + 2 * Real.sin x * Real.cos x ^ 2) /
      (2 * Real.sin x ^ 4) +
    (1 / 2 : ℝ) *
      (-Real.sin x / (1 + Real.cos x) -
        Real.cos x / Real.sin x)

def finalDerivative (x : ℝ) : ℝ :=
  Real.cos x ^ 2 / Real.sin x ^ 3

theorem gap1 (x : ℝ) (hsin : Real.sin x ≠ 0)
    (hratio : 0 < ratio x) :
    deriv y x = expandedDerivative x := by
  have hplus : 1 + Real.cos x ≠ 0 := by
    intro h
    have hz : ratio x = 0 := by
      simp [ratio, h]
    exact (ne_of_gt hratio) hz
  have hratio0 : ratio x ≠ 0 := ne_of_gt hratio
  have hden : 2 * Real.sin x ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hsin)
  have hsinSq :
      HasDerivAt (fun t : ℝ => Real.sin t ^ 2)
        (2 * Real.sin x * Real.cos x) x := by
    convert (Real.hasDerivAt_sin x).pow 2 using 1 <;>
      norm_num <;> ring_nf
  have hdenDeriv :
      HasDerivAt (fun t : ℝ => 2 * Real.sin t ^ 2)
        (4 * Real.sin x * Real.cos x) x := by
    convert
      (hasDerivAt_const x (2 : ℝ)).mul hsinSq using 1 <;>
      norm_num <;> ring_nf
  have hfirst :
      HasDerivAt
        (fun t : ℝ => -(Real.cos t / (2 * Real.sin t ^ 2)))
        ((Real.sin x ^ 3 +
            2 * Real.sin x * Real.cos x ^ 2) /
          (2 * Real.sin x ^ 4)) x := by
    convert
      (((Real.hasDerivAt_cos x).div hdenDeriv hden).neg) using 1 <;>
      field_simp [hsin] <;> ring_nf
  have hnum :
      HasDerivAt (fun t : ℝ => 1 + Real.cos t) (-Real.sin x) x := by
    convert
      (hasDerivAt_const x (1 : ℝ)).add (Real.hasDerivAt_cos x) using 1 <;>
      simp
  have hratioDeriv :
      HasDerivAt ratio
        (ratio x *
          (-Real.sin x / (1 + Real.cos x) -
            Real.cos x / Real.sin x)) x := by
    unfold ratio
    convert hnum.div (Real.hasDerivAt_sin x) hsin using 1 <;>
      field_simp [hsin, hplus] <;> ring
  have hlogRatio :
      HasDerivAt (fun t : ℝ => Real.log (ratio t))
        (-Real.sin x / (1 + Real.cos x) -
          Real.cos x / Real.sin x) x := by
    convert
      (Real.hasDerivAt_log hratio0).comp x hratioDeriv using 1 <;>
      field_simp [hratio0] <;> ring
  have hscaledLog :
      HasDerivAt
        (fun t : ℝ => (1 / 2 : ℝ) * Real.log (ratio t))
        ((1 / 2 : ℝ) *
          (-Real.sin x / (1 + Real.cos x) -
            Real.cos x / Real.sin x)) x := by
    convert
      (hasDerivAt_const x (1 / 2 : ℝ)).mul hlogRatio using 1 <;>
      simp
  have hpos : ∀ᶠ t in nhds x, 0 < ratio t :=
    hratioDeriv.continuousAt.eventually (Ioi_mem_nhds hratio)
  have heqLog :
      (fun t : ℝ => Real.log (Real.sqrt (ratio t))) =ᶠ[nhds x]
        (fun t : ℝ => (1 / 2 : ℝ) * Real.log (ratio t)) := by
    filter_upwards [hpos] with t ht
    have hsqrt : Real.sqrt (ratio t) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 ht)
    calc
      Real.log (Real.sqrt (ratio t)) =
          (1 / 2 : ℝ) *
            (Real.log (Real.sqrt (ratio t)) +
              Real.log (Real.sqrt (ratio t))) := by ring
      _ = (1 / 2 : ℝ) *
          Real.log (Real.sqrt (ratio t) ^ 2) := by
        rw [pow_two, Real.log_mul hsqrt hsqrt]
      _ = (1 / 2 : ℝ) * Real.log (ratio t) := by
        rw [Real.sq_sqrt (le_of_lt ht)]
  have hyEq :
      y =ᶠ[nhds x]
        (fun t : ℝ =>
          -(Real.cos t / (2 * Real.sin t ^ 2)) +
            (1 / 2 : ℝ) * Real.log (ratio t)) := by
    filter_upwards [heqLog] with t ht
    change
      -(Real.cos t / (2 * Real.sin t ^ 2)) +
          Real.log (Real.sqrt (ratio t)) =
        -(Real.cos t / (2 * Real.sin t ^ 2)) +
          (1 / 2 : ℝ) * Real.log (ratio t)
    rw [ht]
  calc
    deriv y x =
        deriv
          (fun t : ℝ =>
            -(Real.cos t / (2 * Real.sin t ^ 2)) +
              (1 / 2 : ℝ) * Real.log (ratio t)) x :=
      hyEq.deriv_eq
    _ = expandedDerivative x := by
      simpa only [expandedDerivative] using
        (hfirst.add hscaledLog).deriv

theorem gap2 (x : ℝ) (hsin : Real.sin x ≠ 0)
    (hratio : 0 < ratio x) :
    expandedDerivative x = finalDerivative x := by
  have hplus : 1 + Real.cos x ≠ 0 := by
    intro h
    have hz : ratio x = 0 := by
      simp [ratio, h]
    exact (ne_of_gt hratio) hz
  unfold expandedDerivative finalDerivative
  field_simp [hsin, hplus]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem gap3 (x : ℝ) (hsin : Real.sin x ≠ 0)
    (hratio : 0 < ratio x) :
    deriv y x = finalDerivative x := by
  exact (gap1 x hsin hratio).trans (gap2 x hsin hratio)

end

end ProofGap.Exercise905
