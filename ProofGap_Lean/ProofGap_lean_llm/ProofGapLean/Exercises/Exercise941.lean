import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise941

noncomputable section

def y (x : ℝ) : ℝ :=
  (1 / 12 : ℝ) *
      Real.log ((x ^ 4 - x ^ 2 + 1) / (x ^ 2 + 1) ^ 2) -
    1 / (2 * Real.sqrt 3) *
      Real.arctan (Real.sqrt 3 / (2 * x ^ 2 - 1))

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / 12 : ℝ) *
      ((4 * x ^ 3 - 2 * x) / (x ^ 4 - x ^ 2 + 1) -
        4 * x / (x ^ 2 + 1)) -
    1 / (2 * Real.sqrt 3) *
      (1 / (1 + (Real.sqrt 3 / (2 * x ^ 2 - 1)) ^ 2)) *
      (-4 * Real.sqrt 3 * x / (2 * x ^ 2 - 1) ^ 2)

def finalDerivative (x : ℝ) : ℝ := x ^ 3 / (1 + x ^ 6)

theorem gap1 (x : ℝ) (hx : 2 * x ^ 2 - 1 ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  have hApos : 0 < x ^ 4 - x ^ 2 + 1 := by
    nlinarith [sq_nonneg (x ^ 2 - (1 / 2 : ℝ))]
  have hAne : x ^ 4 - x ^ 2 + 1 ≠ 0 := ne_of_gt hApos
  have hAne' : 1 - x ^ 2 + x ^ 4 ≠ 0 := by
    intro hzero
    apply hAne
    calc
      x ^ 4 - x ^ 2 + 1 = 1 - x ^ 2 + x ^ 4 := by ring
      _ = 0 := hzero
  have hA0 : x ^ 2 * (x ^ 2 - 1) + 1 ≠ 0 := by
    intro hzero
    apply hAne
    calc
      x ^ 4 - x ^ 2 + 1 = x ^ 2 * (x ^ 2 - 1) + 1 := by ring
      _ = 0 := hzero
  have hx2p1 : x ^ 2 + 1 ≠ 0 := by
    positivity
  have hBne : (x ^ 2 + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hx2p1
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_id x).pow 2
  have h4 : HasDerivAt (fun t : ℝ => t ^ 4) (4 * x ^ 3) x := by
    simpa using (hasDerivAt_id x).pow 4
  have hA :
      HasDerivAt (fun t : ℝ => t ^ 4 - t ^ 2 + 1)
        (4 * x ^ 3 - 2 * x) x := by
    convert (h4.sub h2).add (hasDerivAt_const x 1) using 1 <;>
      simp <;> ring_nf
  have hC :
      HasDerivAt (fun t : ℝ => t ^ 2 + 1) (2 * x) x := by
    convert h2.add (hasDerivAt_const x 1) using 1 <;>
      simp <;> ring_nf
  have hB :
      HasDerivAt (fun t : ℝ => (t ^ 2 + 1) ^ 2)
        (4 * x * (x ^ 2 + 1)) x := by
    convert hC.pow 2 using 1 <;> norm_num <;> ring
  have hQne :
      (x ^ 4 - x ^ 2 + 1) / (x ^ 2 + 1) ^ 2 ≠ 0 :=
    div_ne_zero hAne hBne
  have hLogRaw :=
    (Real.hasDerivAt_log hQne).comp x (hA.div hB hBne)
  have hResidual :
      x * ((x ^ 2 + 1) * (x ^ 2 * 4 - 2) -
            4 * (x ^ 2 * (x ^ 2 - 1) + 1)) /
          (x ^ 2 * (x ^ 2 - 1) + 1) =
        x * ((x ^ 2 + 1) * (x ^ 2 * 4 - 2) /
            (x ^ 2 * (x ^ 2 - 1) + 1) - 4) := by
    field_simp [hA0]
    <;> ring
  have hLogCoeff :
      ((x ^ 4 - x ^ 2 + 1) / (x ^ 2 + 1) ^ 2)⁻¹ *
          (((4 * x ^ 3 - 2 * x) * (x ^ 2 + 1) ^ 2 -
              (x ^ 4 - x ^ 2 + 1) * (4 * x * (x ^ 2 + 1))) /
            ((x ^ 2 + 1) ^ 2) ^ 2) =
        (4 * x ^ 3 - 2 * x) / (x ^ 4 - x ^ 2 + 1) -
          4 * x / (x ^ 2 + 1) := by
    field_simp [hQne, hAne, hAne', hx2p1, hBne] <;>
      field_simp [hAne, hAne'] <;> exact hResidual
  have hLog :
      HasDerivAt
        (fun t : ℝ =>
          Real.log ((t ^ 4 - t ^ 2 + 1) / (t ^ 2 + 1) ^ 2))
        ((4 * x ^ 3 - 2 * x) / (x ^ 4 - x ^ 2 + 1) -
          4 * x / (x ^ 2 + 1)) x := by
    rw [hLogCoeff] at hLogRaw
    simpa only [Function.comp_apply] using hLogRaw
  have hD :
      HasDerivAt (fun t : ℝ => 2 * t ^ 2 - 1) (4 * x) x := by
    convert ((hasDerivAt_const x 2).mul h2).sub
      (hasDerivAt_const x 1) using 1 <;> simp <;> ring_nf
  have hW :
      HasDerivAt (fun t : ℝ => Real.sqrt 3 / (2 * t ^ 2 - 1))
        (-4 * Real.sqrt 3 * x / (2 * x ^ 2 - 1) ^ 2) x := by
    convert (hasDerivAt_const x (Real.sqrt 3)).div hD hx using 1 <;>
      simp <;> ring_nf
  have hAtanRaw :=
    (Real.hasDerivAt_arctan
      (Real.sqrt 3 / (2 * x ^ 2 - 1))).comp x hW
  have hAtan :
      HasDerivAt
        (fun t : ℝ =>
          Real.arctan (Real.sqrt 3 / (2 * t ^ 2 - 1)))
        ((1 / (1 + (Real.sqrt 3 / (2 * x ^ 2 - 1)) ^ 2)) *
          (-4 * Real.sqrt 3 * x / (2 * x ^ 2 - 1) ^ 2)) x := by
    convert hAtanRaw using 1 <;>
      simp [Function.comp_apply] <;> ring_nf
  have hTotal :=
    (hLog.const_mul (1 / 12 : ℝ)).sub
      (hAtan.const_mul (1 / (2 * Real.sqrt 3) : ℝ))
  convert hTotal using 1 <;>
    simp [y, expandedDerivative] <;> ring

theorem gap2 (x : ℝ) (hx : 2 * x ^ 2 - 1 ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 3 ≠ 0 := by
    positivity
  have hApos : 0 < x ^ 4 - x ^ 2 + 1 := by
    nlinarith [sq_nonneg (x ^ 2 - (1 / 2 : ℝ))]
  have hA : x ^ 4 - x ^ 2 + 1 ≠ 0 := ne_of_gt hApos
  have hA' : 1 - x ^ 2 + x ^ 4 ≠ 0 := by
    intro hzero
    apply hA
    calc
      x ^ 4 - x ^ 2 + 1 = 1 - x ^ 2 + x ^ 4 := by ring
      _ = 0 := hzero
  have hA0 : x ^ 2 * (x ^ 2 - 1) + 1 ≠ 0 := by
    intro hzero
    apply hA
    calc
      x ^ 4 - x ^ 2 + 1 = x ^ 2 * (x ^ 2 - 1) + 1 := by ring
      _ = 0 := hzero
  have hP : x ^ 2 + 1 ≠ 0 := by
    positivity
  have hF : 1 + x ^ 6 ≠ 0 := by
    positivity
  have hU : (2 * x ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hU3 : (2 * x ^ 2 - 1) ^ 2 + 3 ≠ 0 := by
    positivity
  have hFactor :
      (x ^ 4 - x ^ 2 + 1) * (x ^ 2 + 1) = 1 + x ^ 6 := by
    ring
  have hResidual :
      x * 2 *
          ((x ^ 2 * 4 - 2) * (x ^ 2 + 1) -
            4 * (x ^ 2 * (x ^ 2 - 1) + 1)) =
        x * (x ^ 2 - 1) * 12 := by
    ring
  have hLogRaw :
      (1 / 12 : ℝ) *
          ((4 * x ^ 3 - 2 * x) / (x ^ 4 - x ^ 2 + 1) -
            4 * x / (x ^ 2 + 1)) =
        (x ^ 3 - x) /
          (2 * (x ^ 4 - x ^ 2 + 1) * (x ^ 2 + 1)) := by
    field_simp [hA, hA', hP] <;>
      field_simp [hA, hA'] <;> exact hResidual
  have hLog :
      (1 / 12 : ℝ) *
          ((4 * x ^ 3 - 2 * x) / (x ^ 4 - x ^ 2 + 1) -
            4 * x / (x ^ 2 + 1)) =
        (x ^ 3 - x) / (2 * (1 + x ^ 6)) := by
    calc
      _ = (x ^ 3 - x) /
          (2 * (x ^ 4 - x ^ 2 + 1) * (x ^ 2 + 1)) := hLogRaw
      _ = (x ^ 3 - x) / (2 * (1 + x ^ 6)) := by
        rw [show
          2 * (x ^ 4 - x ^ 2 + 1) * (x ^ 2 + 1) =
            2 * (1 + x ^ 6) by ring]
  have hFrac :
      1 / (1 + (Real.sqrt 3 / (2 * x ^ 2 - 1)) ^ 2) =
        (2 * x ^ 2 - 1) ^ 2 /
          ((2 * x ^ 2 - 1) ^ 2 + 3) := by
    rw [div_pow, hs]
    field_simp [hU, hU3] <;> ring
  have hDA :
      (2 * x ^ 2 - 1) ^ 2 + 3 =
        4 * (x ^ 4 - x ^ 2 + 1) := by
    ring
  have hAtanRaw :
      1 / (2 * Real.sqrt 3) *
          (1 / (1 + (Real.sqrt 3 / (2 * x ^ 2 - 1)) ^ 2)) *
          (-4 * Real.sqrt 3 * x / (2 * x ^ 2 - 1) ^ 2) =
        -x / (2 * (x ^ 4 - x ^ 2 + 1)) := by
    calc
      _ = -2 * x / ((2 * x ^ 2 - 1) ^ 2 + 3) := by
        rw [hFrac]
        field_simp [hs0, hU, hU3] <;> ring
      _ = -x / (2 * (x ^ 4 - x ^ 2 + 1)) := by
        rw [hDA]
        field_simp [hA] <;> ring
  have hAtan :
      1 / (2 * Real.sqrt 3) *
          (1 / (1 + (Real.sqrt 3 / (2 * x ^ 2 - 1)) ^ 2)) *
          (-4 * Real.sqrt 3 * x / (2 * x ^ 2 - 1) ^ 2) =
        -(x ^ 3 + x) / (2 * (1 + x ^ 6)) := by
    calc
      _ = -x / (2 * (x ^ 4 - x ^ 2 + 1)) := hAtanRaw
      _ = -(x ^ 3 + x) / (2 * (1 + x ^ 6)) := by
        rw [← hFactor]
        field_simp [hA, hP] <;> ring
  unfold expandedDerivative finalDerivative
  rw [hLog, hAtan]
  field_simp [hF] <;> ring

theorem gap3 (x : ℝ) (hx : 2 * x ^ 2 - 1 ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise941
