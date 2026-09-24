import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise886

noncomputable section

def lg (x : ℝ) : ℝ := Real.logb 10 x
def y (x : ℝ) : ℝ := lg (x ^ 2) ^ 3

def chainDerivative (x : ℝ) : ℝ :=
  3 * lg (x ^ 2) ^ 2 * (1 / x ^ 2) * 2 * x * lg (Real.exp 1)

def compactDerivative (x : ℝ) : ℝ :=
  (6 / x) * lg (Real.exp 1) * lg (x ^ 2) ^ 2

def logarithmicForm (x : ℝ) : ℝ :=
  8 * lg (Real.exp 1) ^ 3 * Real.log |x| ^ 3

private theorem hasDerivAt_real_log (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt Real.log x⁻¹ x := by
  exact Real.hasDerivAt_log hx

private theorem hasDerivAt_lg (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt lg (x⁻¹ / Real.log 10) x := by
  simpa [lg, Real.logb] using
    (hasDerivAt_real_log x hx).div_const (Real.log 10)

private theorem compose_hasDerivAt
    {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' (g x)) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun t => f (g t)) (f' * g') x := by
  exact hf.comp x hg

private theorem log_sq_eq_two_log_abs (x : ℝ) (hx : x ≠ 0) :
    Real.log (x ^ 2) = 2 * Real.log |x| := by
  rw [pow_two, Real.log_mul hx hx]
  rw [Real.log_abs]
  ring

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    deriv y x = chainDerivative x := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa [pow_two] using (hasDerivAt_id x).pow 2
  have hinner :
      HasDerivAt (fun t : ℝ => lg (t ^ 2))
        (((x ^ 2)⁻¹ / Real.log 10) * (2 * x)) x := by
    exact compose_hasDerivAt
      (f := lg) (g := fun t : ℝ => t ^ 2)
      (hasDerivAt_lg (x ^ 2) (pow_ne_zero 2 hx)) hsq
  have hcube : HasDerivAt y (chainDerivative x) x := by
    convert hinner.pow 3 using 1 <;>
      simp [chainDerivative, lg, Real.logb, div_eq_mul_inv] <;>
      ring
  exact hcube.deriv

theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    chainDerivative x = compactDerivative x := by
  unfold chainDerivative compactDerivative
  field_simp [hx] <;> ring

theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    deriv y x = compactDerivative x := by
  rw [gap1 x hx, gap2 x hx]

theorem gap4 (x : ℝ) (hx : x ≠ 0) :
    y x = (lg (Real.exp 1) * Real.log (x ^ 2)) ^ 3 := by
  simp [y, lg, Real.logb, div_eq_mul_inv] <;> ring

theorem gap5 (x : ℝ) (hx : x ≠ 0) :
    (lg (Real.exp 1) * Real.log (x ^ 2)) ^ 3 =
      logarithmicForm x := by
  rw [log_sq_eq_two_log_abs x hx]
  unfold logarithmicForm
  ring

theorem gap6 (x : ℝ) (hx : x ≠ 0) :
    y x = logarithmicForm x := by
  rw [gap4 x hx, gap5 x hx]

theorem gap7 (x : ℝ) (hx : x ≠ 0) :
    deriv y x =
      24 * lg (Real.exp 1) ^ 3 * (1 / x) * Real.log |x| ^ 2 := by
  have hlg :
      lg (x ^ 2) = 2 * lg (Real.exp 1) * Real.log |x| := by
    calc
      lg (x ^ 2) = lg (Real.exp 1) * Real.log (x ^ 2) := by
        simp [lg, Real.logb, div_eq_mul_inv] <;> ring
      _ = 2 * lg (Real.exp 1) * Real.log |x| := by
        rw [log_sq_eq_two_log_abs x hx]
        ring
  rw [gap3 x hx]
  unfold compactDerivative
  rw [hlg]
  ring

theorem gap8 (x : ℝ) (hx : x ≠ 0) :
    deriv (fun t : ℝ => Real.log |t|) x =
      (1 / |x|) * (|x| / x) := by
  have hderiv :
      deriv (fun t : ℝ => Real.log |t|) x = 1 / x := by
    simpa only [Real.log_abs, one_div] using
      (hasDerivAt_real_log x hx).deriv
  rw [hderiv]
  have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
  field_simp [habs, hx]

theorem gap9 (x : ℝ) (hx : x ≠ 0) :
    (1 / |x|) * (|x| / x) = 1 / x := by
  have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
  field_simp [habs, hx]

theorem gap10 (x : ℝ) (hx : x ≠ 0) :
    deriv (fun t : ℝ => Real.log |t|) x = 1 / x := by
  rw [gap8 x hx, gap9 x hx]

end

end ProofGap.Exercise886
