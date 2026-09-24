import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise898

noncomputable section

def radius (a x : ℝ) : ℝ := Real.sqrt (x ^ 2 + a ^ 2)
def y (a x : ℝ) : ℝ :=
  (x / 2) * radius a x +
    (a ^ 2 / 2) * Real.log (x + radius a x)

def expandedDerivative (a x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * radius a x +
    x ^ 2 / (2 * radius a x) +
      (a ^ 2 / 2) * (1 / radius a x)

private theorem radius_facts (a x : ℝ) (ha : a ≠ 0) :
    0 < x ^ 2 + a ^ 2 ∧
      0 < radius a x ∧
        radius a x ^ 2 = x ^ 2 + a ^ 2 ∧
          0 < x + radius a x := by
  have ha_sq : 0 < a ^ 2 := by
    simpa [pow_two] using (mul_self_pos.mpr ha)
  have hsum_pos : 0 < x ^ 2 + a ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg x) ha_sq
  have hr_pos : 0 < radius a x := by
    simpa only [radius] using Real.sqrt_pos.2 hsum_pos
  have hr_sq : radius a x ^ 2 = x ^ 2 + a ^ 2 := by
    simpa only [radius] using Real.sq_sqrt (le_of_lt hsum_pos)
  have hxradius_pos : 0 < x + radius a x := by
    by_contra h
    have hnonpos : x + radius a x ≤ 0 := le_of_not_gt h
    have hother : 0 ≤ radius a x - x := by linarith
    have hprod :
        (x + radius a x) * (radius a x - x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos hother
    nlinarith [hprod, hr_sq, ha_sq]
  exact ⟨hsum_pos, hr_pos, hr_sq, hxradius_pos⟩

theorem gap1 (a x : ℝ) (ha : a ≠ 0) :
    deriv (y a) x = expandedDerivative a x := by
  obtain ⟨hsum_pos, hr_pos, hr_sq, hxradius_pos⟩ :=
    radius_facts a x ha
  have hr_ne : radius a x ≠ 0 := ne_of_gt hr_pos
  have hradius_exp :
      radius a =
        fun t : ℝ => Real.exp (Real.log (t ^ 2 + a ^ 2) / 2) := by
    funext t
    have ha_sq : 0 < a ^ 2 := by
      simpa [pow_two] using (mul_self_pos.mpr ha)
    have ht_pos : 0 < t ^ 2 + a ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg t) ha_sq
    have hsqrt_sq :
        Real.sqrt (t ^ 2 + a ^ 2) ^ 2 = t ^ 2 + a ^ 2 :=
      Real.sq_sqrt (le_of_lt ht_pos)
    have hexp_sq :
        Real.exp (Real.log (t ^ 2 + a ^ 2) / 2) ^ 2 =
          t ^ 2 + a ^ 2 := by
      calc
        Real.exp (Real.log (t ^ 2 + a ^ 2) / 2) ^ 2 =
            Real.exp
              (Real.log (t ^ 2 + a ^ 2) / 2 +
                Real.log (t ^ 2 + a ^ 2) / 2) := by
          rw [pow_two, Real.exp_add]
        _ = Real.exp (Real.log (t ^ 2 + a ^ 2)) := by
          congr 1
          ring
        _ = t ^ 2 + a ^ 2 := Real.exp_log ht_pos
    change Real.sqrt (t ^ 2 + a ^ 2) =
      Real.exp (Real.log (t ^ 2 + a ^ 2) / 2)
    nlinarith [Real.sqrt_nonneg (t ^ 2 + a ^ 2),
      Real.exp_pos (Real.log (t ^ 2 + a ^ 2) / 2)]
  have hquad :
      HasDerivAt (fun t : ℝ => t ^ 2 + a ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul, add_comm] using
      ((hasDerivAt_id x).mul (hasDerivAt_id x)).add_const (a ^ 2)
  have hraw :
      HasDerivAt
        (fun t : ℝ =>
          Real.exp (Real.log (t ^ 2 + a ^ 2) / 2))
        (Real.exp (Real.log (x ^ 2 + a ^ 2) / 2) *
          (((x ^ 2 + a ^ 2)⁻¹ * (2 * x)) / 2)) x := by
    simpa only [Function.comp_apply] using
      (((Real.hasDerivAt_log (ne_of_gt hsum_pos)).comp x hquad).div_const 2).exp
  have hraw_radius :
      HasDerivAt (radius a)
        (Real.exp (Real.log (x ^ 2 + a ^ 2) / 2) *
          (((x ^ 2 + a ^ 2)⁻¹ * (2 * x)) / 2)) x := by
    rw [hradius_exp]
    exact hraw
  have hradius :
      HasDerivAt (radius a) (x / radius a x) x := by
    convert hraw_radius using 1
    rw [← congrFun hradius_exp x, ← hr_sq]
    field_simp [hr_ne]
  have harg :
      HasDerivAt (fun t : ℝ => t + radius a t)
        (1 + x / radius a x) x :=
    (hasDerivAt_id x).add hradius
  have harg_ne : x + radius a x ≠ 0 := ne_of_gt hxradius_pos
  have hcoef :
      1 / radius a x =
        (x + radius a x)⁻¹ * (1 + x / radius a x) := by
    have hsum_over :
        1 + x / radius a x =
          (x + radius a x) / radius a x := by
      field_simp [hr_ne]
      exact add_comm _ _
    rw [hsum_over]
    field_simp [hr_ne, harg_ne]
  have hlog_raw :
      HasDerivAt (fun t : ℝ => Real.log (t + radius a t))
        ((x + radius a x)⁻¹ * (1 + x / radius a x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_log harg_ne).comp x harg
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log (t + radius a t))
        (1 / radius a x) x := by
    convert hlog_raw using 1
  have hfirst :
      HasDerivAt (fun t : ℝ => (t / 2) * radius a t)
        ((1 / 2 : ℝ) * radius a x +
          (x / 2) * (x / radius a x)) x :=
    ((hasDerivAt_id x).div_const 2).mul hradius
  have hsecond :
      HasDerivAt
        (fun t : ℝ => (a ^ 2 / 2) * Real.log (t + radius a t))
        ((a ^ 2 / 2) * (1 / radius a x)) x :=
    hlog.const_mul (a ^ 2 / 2)
  have htotal :
      HasDerivAt (y a)
        ((1 / 2 : ℝ) * radius a x +
            (x / 2) * (x / radius a x) +
          (a ^ 2 / 2) * (1 / radius a x)) x := by
    simpa only [y] using hfirst.add hsecond
  calc
    deriv (y a) x =
        (1 / 2 : ℝ) * radius a x +
            (x / 2) * (x / radius a x) +
          (a ^ 2 / 2) * (1 / radius a x) := htotal.deriv
    _ = expandedDerivative a x := by
      unfold expandedDerivative
      field_simp [hr_ne]

theorem gap2 (a x : ℝ) (ha : a ≠ 0) :
    expandedDerivative a x = radius a x := by
  obtain ⟨_, hr_pos, hr_sq, _⟩ := radius_facts a x ha
  have hr_ne : radius a x ≠ 0 := ne_of_gt hr_pos
  unfold expandedDerivative
  field_simp [hr_ne] <;> nlinarith [hr_sq]

theorem gap3 (a x : ℝ) (ha : a ≠ 0) :
    deriv (y a) x = radius a x := by
  calc
    deriv (y a) x = expandedDerivative a x := gap1 a x ha
    _ = radius a x := gap2 a x ha

end

end ProofGap.Exercise898
