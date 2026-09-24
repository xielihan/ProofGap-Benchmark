import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4233

noncomputable section

open scoped Interval

def yCoord (a x : ℝ) : ℝ :=
  a * Real.arcsin (x / a)

def zCoord (a x : ℝ) : ℝ :=
  a / 4 * Real.log ((a - x) / (a + x))

def curveMap (a x : ℝ) : ℝ × ℝ × ℝ :=
  (x, yCoord a x, zCoord a x)

def rawSpeed (a x : ℝ) : ℝ :=
  Real.sqrt
    (1 + a ^ 2 / (a ^ 2 - x ^ 2) +
      a ^ 4 / (4 * (a ^ 2 - x ^ 2) ^ 2))

def speed (a x : ℝ) : ℝ :=
  (3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2))

def curveLength (a x₀ : ℝ) : ℝ :=
  if 0 ≤ x₀ then
    ∫ x in (0 : ℝ)..x₀, speed a x
  else
    ∫ x in x₀..0, speed a x

private theorem integral_speed_eq_antideriv
    (a u v : ℝ) (ha : 0 < a)
    (hua : -a < u) (hua' : u < a)
    (hva : -a < v) (hva' : v < a) :
    (∫ x in u..v,
      (3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2))) =
      (a / 4 * (Real.log (a + v) - Real.log (a - v)) + v) -
        (a / 4 * (Real.log (a + u) - Real.log (a - u)) + u) := by
  let F : ℝ → ℝ := fun t =>
    a / 4 * (Real.log (a + t) - Real.log (a - t)) + t
  have hderiv : ∀ x ∈ Set.uIcc u v,
      HasDerivAt F
        ((3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2))) x := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with hx | hx
    · have hbounds : -a < x ∧ x < a := by
        constructor <;> linarith
      have hp : 0 < a + x := by linarith
      have hm : 0 < a - x := by linarith
      have hd : 0 < a ^ 2 - x ^ 2 := by
        nlinarith [mul_pos hm hp]
      have h₁ : HasDerivAt (fun t : ℝ => Real.log (a + t))
          (1 / (a + x)) x := by
        simpa using
          (((hasDerivAt_const x a).add (hasDerivAt_id x)).log hp.ne')
      have h₂ : HasDerivAt (fun t : ℝ => Real.log (a - t))
          ((-1) / (a - x)) x := by
        simpa using
          (((hasDerivAt_const x a).sub (hasDerivAt_id x)).log hm.ne')
      have hcalc : HasDerivAt F
          (a / 4 * (1 / (a + x) - (-1) / (a - x)) + 1) x := by
        simpa [F] using
          ((h₁.sub h₂).const_mul (a / 4)).add (hasDerivAt_id x)
      convert hcalc using 1
      field_simp [hp.ne', hm.ne', hd.ne']
      <;> ring
    · have hbounds : -a < x ∧ x < a := by
        constructor <;> linarith
      have hp : 0 < a + x := by linarith
      have hm : 0 < a - x := by linarith
      have hd : 0 < a ^ 2 - x ^ 2 := by
        nlinarith [mul_pos hm hp]
      have h₁ : HasDerivAt (fun t : ℝ => Real.log (a + t))
          (1 / (a + x)) x := by
        simpa using
          (((hasDerivAt_const x a).add (hasDerivAt_id x)).log hp.ne')
      have h₂ : HasDerivAt (fun t : ℝ => Real.log (a - t))
          ((-1) / (a - x)) x := by
        simpa using
          (((hasDerivAt_const x a).sub (hasDerivAt_id x)).log hm.ne')
      have hcalc : HasDerivAt F
          (a / 4 * (1 / (a + x) - (-1) / (a - x)) + 1) x := by
        simpa [F] using
          ((h₁.sub h₂).const_mul (a / 4)).add (hasDerivAt_id x)
      convert hcalc using 1
      field_simp [hp.ne', hm.ne', hd.ne']
      <;> ring
  have hcont : ContinuousOn
      (fun x : ℝ =>
        (3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2)))
      (Set.uIcc u v) := by
    intro x hx
    have hbounds : -a < x ∧ x < a := by
      rcases Set.mem_uIcc.mp hx with ⟨hux, hxv⟩ | ⟨hvx, hxu⟩
      · constructor <;> linarith
      · constructor <;> linarith
    have hp : 0 < a + x := by linarith
    have hm : 0 < a - x := by linarith
    have hd : 0 < a ^ 2 - x ^ 2 := by
      nlinarith [mul_pos hm hp]
    have hnum : ContinuousAt
        (fun t : ℝ => 3 * a ^ 2 - 2 * t ^ 2) x :=
      continuousAt_const.sub
        (continuousAt_const.mul (continuousAt_id.pow 2))
    have hden : ContinuousAt
        (fun t : ℝ => 2 * (a ^ 2 - t ^ 2)) x :=
      continuousAt_const.mul
        (continuousAt_const.sub (continuousAt_id.pow 2))
    exact (hnum.div hden (mul_ne_zero (by norm_num) hd.ne')).continuousWithinAt
  simpa [F] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hcont.intervalIntegrable)

theorem gap1 (a x : ℝ) (ha : 0 < a) (hx : |x| < a) :
    rawSpeed a x =
      Real.sqrt
        (1 + a ^ 2 / (a ^ 2 - x ^ 2) +
          a ^ 4 / (4 * (a ^ 2 - x ^ 2) ^ 2)) := by
  rfl

theorem gap2 (a x : ℝ) (ha : 0 < a) (hx : |x| < a) :
    rawSpeed a x = speed a x := by
  unfold rawSpeed speed
  rcases abs_lt.mp hx with ⟨hxa, hax⟩
  have hd : 0 < a ^ 2 - x ^ 2 := by
    have hp : 0 < (a - x) * (a + x) :=
      mul_pos (sub_pos.mpr hax) (by linarith)
    nlinarith
  have hnum : 0 ≤ 3 * a ^ 2 - 2 * x ^ 2 := by
    nlinarith [sq_nonneg a]
  have hden : 0 ≤ 2 * (a ^ 2 - x ^ 2) := by
    nlinarith
  have hs : 0 ≤ (3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2)) :=
    div_nonneg hnum hden
  have hsq :
      1 + a ^ 2 / (a ^ 2 - x ^ 2) +
          a ^ 4 / (4 * (a ^ 2 - x ^ 2) ^ 2) =
        ((3 * a ^ 2 - 2 * x ^ 2) /
          (2 * (a ^ 2 - x ^ 2))) ^ 2 := by
    field_simp [hd.ne']
    <;> ring
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hs]

theorem gap3 (a x : ℝ) (ha : 0 < a) (hx : |x| < a) :
    rawSpeed a x =
      (3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2)) := by
  simpa [speed] using gap2 a x ha hx

theorem gap4 (a x₀ : ℝ) (ha : 0 < a)
    (hx₀ : 0 ≤ x₀) (hxa : x₀ < a) :
    curveLength a x₀ =
      ∫ x in (0 : ℝ)..x₀,
        (3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2)) := by
  simp [curveLength, speed, hx₀]

theorem gap5 (a x₀ : ℝ) (ha : 0 < a)
    (hx₀ : 0 ≤ x₀) (hxa : x₀ < a) :
    (∫ x in (0 : ℝ)..x₀,
        (3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2))) =
      a / 4 * Real.log ((a + x₀) / (a - x₀)) + x₀ := by
  have hp : 0 < a + x₀ := by linarith
  have hm : 0 < a - x₀ := by linarith
  rw [integral_speed_eq_antideriv a 0 x₀ ha (by linarith) ha
    (by linarith) hxa]
  rw [Real.log_div hp.ne' hm.ne']
  simp only [add_zero, sub_zero, sub_self, mul_zero]

theorem gap6 (a x₀ z₀ : ℝ) (ha : 0 < a)
    (hx₀ : 0 ≤ x₀) (hxa : x₀ < a)
    (hz₀ : z₀ = zCoord a x₀) :
    a / 4 * Real.log ((a + x₀) / (a - x₀)) + x₀ =
      |z₀| + |x₀| := by
  have hp : 0 < a + x₀ := by linarith
  have hm : 0 < a - x₀ := by linarith
  have hratio : 1 ≤ (a + x₀) / (a - x₀) := by
    apply (le_div_iff₀ hm).2
    linarith
  have hlog : 0 ≤ Real.log ((a + x₀) / (a - x₀)) :=
    Real.log_nonneg hratio
  have hcoef : 0 ≤ a / 4 := by
    apply div_nonneg ha.le
    norm_num
  have hprod :
      0 ≤ a / 4 * Real.log ((a + x₀) / (a - x₀)) :=
    mul_nonneg hcoef hlog
  have hinv :
      (a - x₀) / (a + x₀) =
        ((a + x₀) / (a - x₀))⁻¹ := by
    rw [inv_div]
  have hzform :
      zCoord a x₀ =
        -(a / 4 * Real.log ((a + x₀) / (a - x₀))) := by
    unfold zCoord
    rw [hinv, Real.log_inv]
    ring
  rw [hz₀, hzform, abs_neg, abs_of_nonneg hprod, abs_of_nonneg hx₀]

theorem gap7 (a x₀ z₀ : ℝ) (ha : 0 < a)
    (hx₀ : 0 ≤ x₀) (hxa : x₀ < a)
    (hz₀ : z₀ = zCoord a x₀) :
    curveLength a x₀ = |z₀| + |x₀| := by
  calc
    curveLength a x₀ =
        ∫ x in (0 : ℝ)..x₀,
          (3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2)) :=
      gap4 a x₀ ha hx₀ hxa
    _ = a / 4 * Real.log ((a + x₀) / (a - x₀)) + x₀ :=
      gap5 a x₀ ha hx₀ hxa
    _ = |z₀| + |x₀| := gap6 a x₀ z₀ ha hx₀ hxa hz₀

theorem gap8 (a x₀ : ℝ) (ha : 0 < a)
    (hxa : -a < x₀) (hx₀ : x₀ < 0) :
    curveLength a x₀ =
      ∫ x in x₀..0,
        (3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2)) := by
  simp [curveLength, speed, not_le.mpr hx₀]

theorem gap9 (a x₀ : ℝ) (ha : 0 < a)
    (hxa : -a < x₀) (hx₀ : x₀ < 0) :
    (∫ x in x₀..0,
        (3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2))) =
      -a / 4 * Real.log ((a + x₀) / (a - x₀)) - x₀ := by
  have hp : 0 < a + x₀ := by linarith
  have hm : 0 < a - x₀ := by linarith
  rw [integral_speed_eq_antideriv a x₀ 0 ha hxa (by linarith)
    (by linarith) ha]
  rw [Real.log_div hp.ne' hm.ne']
  simp only [add_zero, sub_zero, sub_self, mul_zero]
  ring

theorem gap10 (a x₀ z₀ : ℝ) (ha : 0 < a)
    (hxa : -a < x₀) (hx₀ : x₀ < 0)
    (hz₀ : z₀ = zCoord a x₀) :
    -a / 4 * Real.log ((a + x₀) / (a - x₀)) - x₀ =
      |z₀| + |x₀| := by
  have hp : 0 < a + x₀ := by linarith
  have hm : 0 < a - x₀ := by linarith
  have hratio : 1 ≤ (a - x₀) / (a + x₀) := by
    apply (le_div_iff₀ hp).2
    linarith
  have hlog : 0 ≤ Real.log ((a - x₀) / (a + x₀)) :=
    Real.log_nonneg hratio
  have hcoef : 0 ≤ a / 4 := by
    apply div_nonneg ha.le
    norm_num
  have hznonneg : 0 ≤ zCoord a x₀ := by
    unfold zCoord
    exact mul_nonneg hcoef hlog
  have hinv :
      (a - x₀) / (a + x₀) =
        ((a + x₀) / (a - x₀))⁻¹ := by
    rw [inv_div]
  rw [hz₀, abs_of_nonneg hznonneg, abs_of_nonpos hx₀.le]
  unfold zCoord
  rw [hinv, Real.log_inv]
  ring

theorem gap11 (a x₀ z₀ : ℝ) (ha : 0 < a)
    (hxa : -a < x₀) (hx₀ : x₀ < 0)
    (hz₀ : z₀ = zCoord a x₀) :
    curveLength a x₀ = |z₀| + |x₀| := by
  calc
    curveLength a x₀ =
        ∫ x in x₀..0,
          (3 * a ^ 2 - 2 * x ^ 2) / (2 * (a ^ 2 - x ^ 2)) :=
      gap8 a x₀ ha hxa hx₀
    _ = -a / 4 * Real.log ((a + x₀) / (a - x₀)) - x₀ :=
      gap9 a x₀ ha hxa hx₀
    _ = |z₀| + |x₀| := gap10 a x₀ z₀ ha hxa hx₀ hz₀

theorem gap12 (a x₀ z₀ : ℝ) (ha : 0 < a)
    (hx₀ : |x₀| < a) (hz₀ : z₀ = zCoord a x₀) :
    curveLength a x₀ = |z₀| + |x₀| := by
  rcases abs_lt.mp hx₀ with ⟨hleft, hright⟩
  by_cases hnonneg : 0 ≤ x₀
  · exact gap7 a x₀ z₀ ha hnonneg hright hz₀
  · exact gap11 a x₀ z₀ ha hleft (lt_of_not_ge hnonneg) hz₀

end

end ProofGap.Exercise4233
