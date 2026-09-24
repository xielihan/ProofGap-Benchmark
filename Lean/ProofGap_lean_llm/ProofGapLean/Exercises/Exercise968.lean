import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise968

noncomputable section

def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

def y (x : ℝ) : ℝ :=
  Real.cosh x / Real.sinh x ^ 2 - Real.log (coth (x / 2))

def expandedDerivative (x : ℝ) : ℝ :=
  (Real.sinh x ^ 3 - 2 * Real.sinh x * Real.cosh x ^ 2) /
      Real.sinh x ^ 4 +
    1 / (2 * Real.sinh (x / 2) ^ 2 * coth (x / 2))

def finalDerivative (x : ℝ) : ℝ := -(2 / Real.sinh x ^ 3)

private theorem hasDerivAt_sinh_cosh_via_exp (x : ℝ) :
    HasDerivAt (fun z : ℝ => Real.sinh z) (Real.cosh x) x ∧
      HasDerivAt (fun z : ℝ => Real.cosh z) (Real.sinh x) x := by
  constructor
  · have h :=
      ((Real.hasDerivAt_exp x).sub
        ((Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg))).div_const 2
    convert h using 1 <;>
      simp [Real.sinh_eq, Real.cosh_eq, Function.comp_def] <;>
      ring_nf
  · have h :=
      ((Real.hasDerivAt_exp x).add
        ((Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg))).div_const 2
    convert h using 1 <;>
      simp [Real.sinh_eq, Real.cosh_eq, Function.comp_def] <;>
      ring_nf

theorem gap1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (expandedDerivative x) x := by
  have hxhalf : 0 < x / 2 := by
    linarith
  have hsinhxPos : 0 < Real.sinh x := by
    rw [Real.sinh_eq]
    have hexp := Real.exp_lt_exp.mpr (show -x < x by linarith)
    linarith
  have hsinhHalfPos : 0 < Real.sinh (x / 2) := by
    rw [Real.sinh_eq]
    have hexp := Real.exp_lt_exp.mpr
      (show -(x / 2) < x / 2 by linarith)
    linarith
  have hsinhx : Real.sinh x ≠ 0 := ne_of_gt hsinhxPos
  have hsinhHalf : Real.sinh (x / 2) ≠ 0 := ne_of_gt hsinhHalfPos
  have hsinhxSq : Real.sinh x ^ 2 ≠ 0 := pow_ne_zero 2 hsinhx
  have hcoshHalf : Real.cosh (x / 2) ≠ 0 :=
    ne_of_gt (Real.cosh_pos (x / 2))
  have hhalf : HasDerivAt (fun z : ℝ => z / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv] using
      (hasDerivAt_id x).mul_const ((2 : ℝ)⁻¹)
  have hsc := hasDerivAt_sinh_cosh_via_exp x
  have hfirst := hsc.2.div (hsc.1.pow 2) hsinhxSq
  simp only [Pi.pow_apply, Nat.reduceSub, pow_one] at hfirst
  have hfirst' :
      HasDerivAt (fun z : ℝ => Real.cosh z / Real.sinh z ^ 2)
        ((Real.sinh x ^ 3 -
            2 * Real.sinh x * Real.cosh x ^ 2) /
          Real.sinh x ^ 4) x := by
    convert hfirst using 1 <;>
      field_simp [hsinhx] <;> ring
  have hscHalf := hasDerivAt_sinh_cosh_via_exp (x / 2)
  have hcoshHalfDeriv := hscHalf.2.comp x hhalf
  have hsinhHalfDeriv := hscHalf.1.comp x hhalf
  have hcothDeriv := hcoshHalfDeriv.div hsinhHalfDeriv hsinhHalf
  simp only [Function.comp_apply] at hcothDeriv
  have hcothDeriv' :
      HasDerivAt
        (fun z : ℝ => Real.cosh (z / 2) / Real.sinh (z / 2))
        (-(1 / (2 * Real.sinh (x / 2) ^ 2))) x := by
    convert hcothDeriv using 1 <;>
      field_simp [hsinhHalf] <;>
      nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  have hcothNe :
      Real.cosh (x / 2) / Real.sinh (x / 2) ≠ 0 :=
    div_ne_zero hcoshHalf hsinhHalf
  unfold y expandedDerivative coth
  convert hfirst'.sub (hcothDeriv'.log hcothNe) using 1 <;>
    field_simp [hsinhx, hsinhHalf, hcoshHalf] <;> ring

theorem gap2 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (finalDerivative x) x := by
  have hxhalf : 0 < x / 2 := by
    linarith
  have hsinhxPos : 0 < Real.sinh x := by
    rw [Real.sinh_eq]
    have hexp := Real.exp_lt_exp.mpr (show -x < x by linarith)
    linarith
  have hsinhHalfPos : 0 < Real.sinh (x / 2) := by
    rw [Real.sinh_eq]
    have hexp := Real.exp_lt_exp.mpr
      (show -(x / 2) < x / 2 by linarith)
    linarith
  have hsinhx : Real.sinh x ≠ 0 := ne_of_gt hsinhxPos
  have hsinhHalf : Real.sinh (x / 2) ≠ 0 := ne_of_gt hsinhHalfPos
  have hcoshHalf : Real.cosh (x / 2) ≠ 0 :=
    ne_of_gt (Real.cosh_pos (x / 2))
  have hdouble :
      Real.sinh x =
        2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    calc
      Real.sinh x = Real.sinh (x / 2 + x / 2) :=
        congrArg Real.sinh (by ring)
      _ = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
        rw [Real.sinh_add]
        ring
  have hsecond :
      1 / (2 * Real.sinh (x / 2) ^ 2 * coth (x / 2)) =
        1 / Real.sinh x := by
    unfold coth
    rw [hdouble]
    field_simp [hsinhHalf, hcoshHalf] <;> ring
  have heq : expandedDerivative x = finalDerivative x := by
    unfold expandedDerivative finalDerivative
    rw [hsecond]
    calc
      (Real.sinh x ^ 3 -
              2 * Real.sinh x * Real.cosh x ^ 2) /
            Real.sinh x ^ 4 +
          1 / Real.sinh x =
          (-2 * Real.sinh x *
              (Real.cosh x ^ 2 - Real.sinh x ^ 2)) /
            Real.sinh x ^ 4 := by
        field_simp [hsinhx] <;> ring
      _ = (-2 * Real.sinh x) / Real.sinh x ^ 4 := by
        rw [Real.cosh_sq_sub_sinh_sq]
        ring
      _ = -(2 / Real.sinh x ^ 3) := by
        field_simp [hsinhx] <;> ring
  rw [← heq]
  exact gap1 x hx

end

end ProofGap.Exercise968
