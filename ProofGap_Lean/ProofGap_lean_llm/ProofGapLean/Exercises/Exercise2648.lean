import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2648

noncomputable section

open scoped Interval

def integrand (x : ℝ) : ℝ :=
  Real.sin x ^ 2 / x

def u (n : ℕ) : ℝ :=
  ∫ x in (n : ℝ) * Real.pi..(n + 1 : ℝ) * Real.pi, integrand x

def lowerBound (n : ℕ) : ℝ :=
  1 / (2 * (n + 1 : ℝ))

private theorem integrand_eq_sin_mul_sinc :
    (fun x : ℝ => integrand x) = fun x => Real.sin x * Real.sinc x := by
  funext x
  by_cases hx : x = 0
  · simp [integrand, hx]
  · rw [Real.sinc_of_ne_zero hx]
    unfold integrand
    ring

private theorem continuous_integrand : Continuous integrand := by
  change Continuous (fun x : ℝ => integrand x)
  rw [integrand_eq_sin_mul_sinc]
  exact Real.continuous_sin.mul Real.continuous_sinc

theorem gap1 :
    ∀ n : ℕ,
      u n ≥
        1 / ((n + 1 : ℝ) * Real.pi) *
          (∫ x in (n : ℝ) * Real.pi..(n + 1 : ℝ) * Real.pi,
            Real.sin x ^ 2) := by
  intro n
  have hab : (n : ℝ) * Real.pi ≤ (n + 1 : ℝ) * Real.pi := by
    apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
    norm_num
  have hleft : Continuous
      (fun x : ℝ => 1 / ((n + 1 : ℝ) * Real.pi) * Real.sin x ^ 2) := by
    fun_prop
  unfold u
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on hab (hleft.intervalIntegrable _ _)
    (continuous_integrand.intervalIntegrable _ _) fun x hx => by
      by_cases hx0 : x = 0
      · simp [integrand, hx0]
      · have hxnonneg : 0 ≤ x := by
          exact (mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le).trans hx.1
        have hxpos : 0 < x := lt_of_le_of_ne hxnonneg (Ne.symm hx0)
        have hrecip : 1 / ((n + 1 : ℝ) * Real.pi) ≤ 1 / x :=
          one_div_le_one_div_of_le hxpos hx.2
        calc
          1 / ((n + 1 : ℝ) * Real.pi) * Real.sin x ^ 2 ≤
              1 / x * Real.sin x ^ 2 :=
            mul_le_mul_of_nonneg_right hrecip (sq_nonneg _)
          _ = integrand x := by
            unfold integrand
            ring

theorem gap2 :
    ∀ n : ℕ,
      1 / ((n + 1 : ℝ) * Real.pi) *
          (∫ x in (n : ℝ) * Real.pi..(n + 1 : ℝ) * Real.pi,
            Real.sin x ^ 2) =
        lowerBound n := by
  intro n
  have hsin_n : Real.sin ((n : ℝ) * Real.pi) = 0 := by
    exact Real.sin_nat_mul_pi n
  have hsin_succ : Real.sin ((n + 1 : ℝ) * Real.pi) = 0 := by
    simpa using Real.sin_nat_mul_pi (n + 1)
  rw [integral_sin_sq, hsin_n, hsin_succ]
  unfold lowerBound
  simp
  field_simp [Real.pi_ne_zero]
  ring

theorem gap3 :
    ∀ n : ℕ, 0 < lowerBound n := by
  intro n
  unfold lowerBound
  positivity

theorem gap4
    (hlower : ∀ n : ℕ, lowerBound n ≤ u n)
    (hpositive : ∀ n : ℕ, 0 < lowerBound n) :
    ∀ n : ℕ, 0 < u n := by
  intro n
  exact (hpositive n).trans_le (hlower n)

theorem gap5 :
    ¬ Summable (fun n : ℕ => lowerBound (n + 1)) := by
  intro hsum
  have hshift : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
    refine (hsum.mul_left 2).congr ?_
    intro n
    unfold lowerBound
    push_cast
    field_simp
    ring
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 2).mp hshift)

theorem gap6
    (hbound : ∀ n : ℕ, lowerBound n ≤ u n)
    (hpos : ∀ n : ℕ, 0 ≤ u n)
    (hdiv : ¬ Summable (fun n : ℕ => lowerBound (n + 1))) :
    ¬ Summable (fun n : ℕ => u (n + 1)) := by
  intro hsum
  apply hdiv
  exact hsum.of_nonneg_of_le
    (fun n => (gap3 (n + 1)).le)
    (fun n => hbound (n + 1))

theorem gap7
    (hdiv : ¬ Summable (fun n : ℕ => u (n + 1))) :
    ¬ Summable (fun n : ℕ => u (n + 1)) := by
  exact hdiv

end

end ProofGap.Exercise2648
