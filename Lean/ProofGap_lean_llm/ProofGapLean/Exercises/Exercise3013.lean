import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ProofGap.Exercise3013

noncomputable section

open Filter
open scoped BigOperators Interval Topology

def coefficient (n : ℕ) : ℝ :=
  (2 * (n : ℝ) + 1) / (n.factorial : ℝ)

def term (x : ℝ) (n : ℕ) : ℝ :=
  coefficient n * x ^ (2 * n)

def f (x : ℝ) : ℝ := ∑' n : ℕ, term x n

def convergenceDomain : Set ℝ := {x | Summable (term x)}

private def baseTerm3013 (x : ℝ) (n : ℕ) : ℝ :=
  (x ^ 2) ^ n / (n.factorial : ℝ)

private def weightedTerm3013 (x : ℝ) (n : ℕ) : ℝ :=
  2 * (n : ℝ) * (x ^ 2) ^ n / (n.factorial : ℝ)

private lemma summable_baseTerm3013 (x : ℝ) :
    Summable (baseTerm3013 x) := by
  simpa [baseTerm3013] using Real.summable_pow_div_factorial (x ^ 2)

private lemma tsum_baseTerm3013 (x : ℝ) :
    (∑' n : ℕ, baseTerm3013 x n) = Real.exp (x ^ 2) := by
  rw [Real.exp_eq_exp_ℝ]
  simpa [baseTerm3013] using
    (NormedSpace.expSeries_div_hasSum_exp (x ^ 2)).tsum_eq

private lemma weightedTerm3013_succ (x : ℝ) (n : ℕ) :
    weightedTerm3013 x (n + 1) =
      2 * x ^ 2 * baseTerm3013 x n := by
  simp only [weightedTerm3013, baseTerm3013, Nat.cast_add, Nat.cast_one,
    Nat.factorial_succ, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

private lemma summable_weightedTerm3013 (x : ℝ) :
    Summable (weightedTerm3013 x) := by
  apply (summable_nat_add_iff (f := weightedTerm3013 x) 1).mp
  convert (summable_baseTerm3013 x).mul_left (2 * x ^ 2) using 1
  ext n
  rw [weightedTerm3013_succ]

private lemma tsum_weightedTerm3013 (x : ℝ) :
    (∑' n : ℕ, weightedTerm3013 x n) =
      2 * x ^ 2 * Real.exp (x ^ 2) := by
  have hsplit := (summable_weightedTerm3013 x).sum_add_tsum_nat_add 1
  calc
    (∑' n : ℕ, weightedTerm3013 x n) =
        ∑' n : ℕ, weightedTerm3013 x (n + 1) := by
      simpa [weightedTerm3013] using hsplit.symm
    _ = ∑' n : ℕ, 2 * x ^ 2 * baseTerm3013 x n :=
      tsum_congr (weightedTerm3013_succ x)
    _ = 2 * x ^ 2 * (∑' n : ℕ, baseTerm3013 x n) := by
      rw [tsum_mul_left]
    _ = 2 * x ^ 2 * Real.exp (x ^ 2) := by
      rw [tsum_baseTerm3013]

private lemma term_eq_base_add_weighted3013 (x : ℝ) (n : ℕ) :
    term x n = baseTerm3013 x n + weightedTerm3013 x n := by
  simp only [term, coefficient, baseTerm3013, weightedTerm3013, pow_mul]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private lemma summable_term3013 (x : ℝ) : Summable (term x) := by
  refine (summable_baseTerm3013 x).add (summable_weightedTerm3013 x) |>.congr ?_
  intro n
  exact (term_eq_base_add_weighted3013 x n).symm

private lemma f_closed3013 (x : ℝ) :
    f x = Real.exp (x ^ 2) * (1 + 2 * x ^ 2) := by
  rw [f]
  calc
    (∑' n : ℕ, term x n) =
        (∑' n : ℕ, baseTerm3013 x n) +
          ∑' n : ℕ, weightedTerm3013 x n := by
      rw [← (summable_baseTerm3013 x).tsum_add
        (summable_weightedTerm3013 x)]
      exact tsum_congr (term_eq_base_add_weighted3013 x)
    _ = Real.exp (x ^ 2) + 2 * x ^ 2 * Real.exp (x ^ 2) := by
      rw [tsum_baseTerm3013, tsum_weightedTerm3013]
    _ = Real.exp (x ^ 2) * (1 + 2 * x ^ 2) := by ring

private lemma coefficient_ratio3013 (n : ℕ) :
    |coefficient n / coefficient (n + 1)| =
      (((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) /
        (2 * (n : ℝ) + 3) := by
  have hn : 0 < (n.factorial : ℝ) := by positivity
  have hn1 : 0 < ((n + 1).factorial : ℝ) := by positivity
  have hc : 0 < coefficient n := by
    unfold coefficient
    positivity
  have hc1 : 0 < coefficient (n + 1) := by
    unfold coefficient
    positivity
  rw [abs_of_pos (div_pos hc hc1)]
  unfold coefficient
  rw [Nat.factorial_succ]
  field_simp
  push_cast
  ring

private lemma rational_tendsto3013 :
    Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) /
          (2 * (n : ℝ) + 3))
      atTop atTop := by
  have hlinear :
      Tendsto (fun n : ℕ => (1 / 3 : ℝ) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  apply Filter.tendsto_atTop_mono' atTop
    (f₁ := fun n : ℕ => (1 / 3 : ℝ) * (n : ℝ))
  · filter_upwards with n
    have hden : 0 < 2 * (n : ℝ) + 3 := by positivity
    rw [le_div_iff₀ hden]
    push_cast
    nlinarith [sq_nonneg (n : ℝ)]
  · exact hlinear

private lemma integral_term3013 (x : ℝ) (n : ℕ) :
    (∫ t in 0..x, term t n) =
      x ^ (2 * n + 1) / (n.factorial : ℝ) := by
  rw [show (fun t : ℝ => term t n) =
      fun t : ℝ => coefficient n * t ^ (2 * n) by rfl]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [coefficient]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hodd : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

private lemma integral_f3013 (x : ℝ) :
    (∫ t in 0..x, f t) = x * Real.exp (x ^ 2) := by
  let g : ℝ → ℝ := fun t => t * Real.exp (t ^ 2)
  have hg (t : ℝ) :
      HasDerivAt g (f t) t := by
    rw [f_closed3013]
    dsimp [g]
    convert
      ((hasDerivAt_id t).mul
        ((hasDerivAt_id t).pow 2).exp) using 1 <;>
      simp only [Pi.pow_apply, id_eq] <;> ring
  have hfcont : Continuous f := by
    rw [show f = fun t : ℝ =>
      Real.exp (t ^ 2) * (1 + 2 * t ^ 2) from funext f_closed3013]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := x) (f := g) (f' := f)
    (fun t _ => hg t) (hfcont.intervalIntegrable _ _)
  simpa [g] using hi

private lemma term_succ3013 (x : ℝ) (n : ℕ) :
    term x (n + 1) =
      (2 / ((n + 1).factorial / (n + 1) : ℝ) +
        1 / ((n + 1).factorial : ℝ)) * x ^ (2 * (n + 1)) := by
  simp only [term, coefficient, Nat.cast_add, Nat.cast_one,
    Nat.factorial_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private def derivSeriesTerm3013 (x : ℝ) (n : ℕ) : ℝ :=
  (2 * (2 * ((n + 1 : ℕ) : ℝ) + 1) / (n.factorial : ℝ)) *
    x ^ (2 * n + 1)

private lemma derivSeriesTerm_decomp3013 (x : ℝ) (n : ℕ) :
    derivSeriesTerm3013 x n =
      x * (2 * weightedTerm3013 x n + 6 * baseTerm3013 x n) := by
  simp only [derivSeriesTerm3013, weightedTerm3013, baseTerm3013,
    Nat.cast_add, Nat.cast_one, pow_add, pow_mul]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private lemma summable_derivSeriesTerm3013 (x : ℝ) :
    Summable (derivSeriesTerm3013 x) := by
  refine ((summable_weightedTerm3013 x).mul_left 2 |>.add
    ((summable_baseTerm3013 x).mul_left 6) |>.mul_left x).congr ?_
  intro n
  exact (derivSeriesTerm_decomp3013 x n).symm

private lemma tsum_derivSeriesTerm3013 (x : ℝ) :
    (∑' n : ℕ, derivSeriesTerm3013 x n) =
      x * (4 * x ^ 2 + 6) * Real.exp (x ^ 2) := by
  calc
    (∑' n : ℕ, derivSeriesTerm3013 x n) =
        ∑' n : ℕ,
          x * (2 * weightedTerm3013 x n + 6 * baseTerm3013 x n) :=
      tsum_congr (derivSeriesTerm_decomp3013 x)
    _ = x * (∑' n : ℕ,
          (2 * weightedTerm3013 x n + 6 * baseTerm3013 x n)) := by
      rw [tsum_mul_left]
    _ = x * (2 * (∑' n : ℕ, weightedTerm3013 x n) +
          6 * (∑' n : ℕ, baseTerm3013 x n)) := by
      rw [(summable_weightedTerm3013 x).mul_left 2 |>.tsum_add
        ((summable_baseTerm3013 x).mul_left 6),
        tsum_mul_left, tsum_mul_left]
    _ = x * (4 * x ^ 2 + 6) * Real.exp (x ^ 2) := by
      rw [tsum_weightedTerm3013, tsum_baseTerm3013]
      ring

private lemma deriv_f3013 (x : ℝ) :
    deriv f x = x * (4 * x ^ 2 + 6) * Real.exp (x ^ 2) := by
  rw [show f = fun t : ℝ =>
    Real.exp (t ^ 2) * (1 + 2 * t ^ 2) from funext f_closed3013]
  convert
    (((hasDerivAt_id x).pow 2).exp.mul
      ((hasDerivAt_const x 1).add
        (((hasDerivAt_id x).pow 2).const_mul 2))).deriv using 1 <;>
    simp [Pi.pow_apply] <;> ring

theorem gap1 :
    ∃ a : ℕ → ℝ,
      (∀ n, a n = coefficient n) ∧
      Tendsto (fun n : ℕ => |a n / a (n + 1)|) atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) /
            (2 * (n : ℝ) + 3))
        atTop atTop := by
  refine ⟨coefficient, fun n => rfl, ?_, rational_tendsto3013⟩
  simpa only [coefficient_ratio3013] using rational_tendsto3013

theorem gap2 :
    Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) /
          (2 * (n : ℝ) + 3))
      atTop atTop := by
  exact rational_tendsto3013

theorem gap3 :
    ∃ a : ℕ → ℝ,
      (∀ n, a n = coefficient n) ∧
      Tendsto (fun n : ℕ => |a n / a (n + 1)|) atTop atTop := by
  exact ⟨coefficient, fun n => rfl, by
    simpa only [coefficient_ratio3013] using rational_tendsto3013⟩

theorem gap4 : convergenceDomain = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact summable_term3013 x

theorem gap5 (x : ℝ) :
    (∫ t in 0..x, f t) =
      ∑' n : ℕ, ∫ t in 0..x, term t n := by
  rw [integral_f3013]
  calc
    x * Real.exp (x ^ 2) =
        x * (∑' n : ℕ, baseTerm3013 x n) := by
      rw [tsum_baseTerm3013]
    _ = ∑' n : ℕ, x * baseTerm3013 x n := by
      rw [tsum_mul_left]
    _ = ∑' n : ℕ, x ^ (2 * n + 1) / (n.factorial : ℝ) := by
      apply tsum_congr
      intro n
      simp only [baseTerm3013, pow_add, pow_mul]
      ring
    _ = ∑' n : ℕ, ∫ t in 0..x, term t n := by
      exact tsum_congr (fun n => (integral_term3013 x n).symm)

theorem gap6 (x : ℝ) :
    (∑' n : ℕ, ∫ t in 0..x, term t n) =
      ∑' n : ℕ, x ^ (2 * n + 1) / (n.factorial : ℝ) := by
  exact tsum_congr (integral_term3013 x)

theorem gap7 (x : ℝ) :
    (∑' n : ℕ, x ^ (2 * n + 1) / (n.factorial : ℝ)) =
      x * (∑' n : ℕ, (x ^ 2) ^ n / (n.factorial : ℝ)) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [pow_add, pow_mul]
  ring

theorem gap8 (x : ℝ) :
    x * (∑' n : ℕ, (x ^ 2) ^ n / (n.factorial : ℝ)) =
      x * Real.exp (x ^ 2) := by
  rw [Real.exp_eq_exp_ℝ]
  congr 1
  simpa using (NormedSpace.expSeries_div_hasSum_exp (x ^ 2)).tsum_eq

theorem gap9 (x : ℝ) :
    (∫ t in 0..x, f t) = x * Real.exp (x ^ 2) := by
  exact integral_f3013 x

theorem gap10 (x : ℝ) :
    f x = deriv (fun y : ℝ => y * Real.exp (y ^ 2)) x := by
  rw [f_closed3013]
  symm
  convert
    ((hasDerivAt_id x).mul
      ((hasDerivAt_id x).pow 2).exp).deriv using 1 <;>
    simp only [Pi.pow_apply, id_eq] <;> ring

theorem gap11 (x : ℝ) :
    deriv (fun y : ℝ => y * Real.exp (y ^ 2)) x =
      Real.exp (x ^ 2) * (1 + 2 * x ^ 2) := by
  convert
    ((hasDerivAt_id x).mul
      ((hasDerivAt_id x).pow 2).exp).deriv using 1 <;>
    simp only [Pi.pow_apply, id_eq] <;> ring

theorem gap12 (x : ℝ) :
    f x = Real.exp (x ^ 2) * (1 + 2 * x ^ 2) := by
  exact f_closed3013 x

theorem gap13 (x : ℝ) :
    f x = ∑' n : ℕ, term x n := by
  rfl

theorem gap14 (x : ℝ) :
    (∑' n : ℕ, term x n) =
      1 + ∑' n : ℕ,
        (2 / ((n + 1).factorial / (n + 1) : ℝ) +
          1 / ((n + 1).factorial : ℝ)) * x ^ (2 * (n + 1)) := by
  have hsplit := (summable_term3013 x).sum_add_tsum_nat_add 1
  calc
    (∑' n : ℕ, term x n) =
        term x 0 + ∑' n : ℕ, term x (n + 1) := by
      simpa using hsplit.symm
    _ = 1 + ∑' n : ℕ,
        (2 / ((n + 1).factorial / (n + 1) : ℝ) +
          1 / ((n + 1).factorial : ℝ)) * x ^ (2 * (n + 1)) := by
      rw [tsum_congr (term_succ3013 x)]
      norm_num [term, coefficient]

theorem gap15 (x : ℝ) :
    1 + ∑' n : ℕ,
        (2 / ((n + 1).factorial / (n + 1) : ℝ) +
          1 / ((n + 1).factorial : ℝ)) * x ^ (2 * (n + 1)) =
      1 + 2 * x ^ 2 * Real.exp (x ^ 2) + Real.exp (x ^ 2) - 1 := by
  calc
    1 + ∑' n : ℕ,
        (2 / ((n + 1).factorial / (n + 1) : ℝ) +
          1 / ((n + 1).factorial : ℝ)) * x ^ (2 * (n + 1)) =
        ∑' n : ℕ, term x n := (gap14 x).symm
    _ = f x := (gap13 x).symm
    _ = Real.exp (x ^ 2) * (1 + 2 * x ^ 2) := gap12 x
    _ = 1 + 2 * x ^ 2 * Real.exp (x ^ 2) +
        Real.exp (x ^ 2) - 1 := by ring

theorem gap16 (x : ℝ) :
    1 + 2 * x ^ 2 * Real.exp (x ^ 2) + Real.exp (x ^ 2) - 1 =
      Real.exp (x ^ 2) * (1 + 2 * x ^ 2) := by
  ring

theorem gap17 (x : ℝ) :
    f x = Real.exp (x ^ 2) * (1 + 2 * x ^ 2) := by
  exact f_closed3013 x

theorem gap18 (x : ℝ) :
    deriv f x =
      ∑' n : ℕ,
        (2 * (2 * ((n + 1 : ℕ) : ℝ) + 1) / (n.factorial : ℝ)) *
          x ^ (2 * n + 1) := by
  change deriv f x = ∑' n : ℕ, derivSeriesTerm3013 x n
  rw [deriv_f3013, tsum_derivSeriesTerm3013]

theorem gap19 (x : ℝ) :
    (∑' n : ℕ,
      (2 * (2 * ((n + 1 : ℕ) : ℝ) + 1) / (n.factorial : ℝ)) *
        x ^ (2 * n + 1)) =
      2 * x * f x + 4 * x * Real.exp (x ^ 2) := by
  change (∑' n : ℕ, derivSeriesTerm3013 x n) =
    2 * x * f x + 4 * x * Real.exp (x ^ 2)
  rw [tsum_derivSeriesTerm3013, f_closed3013]
  ring

theorem gap20 (x : ℝ) :
    deriv f x = 2 * x * f x + 4 * x * Real.exp (x ^ 2) := by
  rw [gap18, gap19]

theorem gap21 (x : ℝ) :
    deriv f x - 2 * x * f x = 4 * x * Real.exp (x ^ 2) := by
  rw [gap20]
  ring

theorem gap22 :
    ∃ C : ℝ, ∀ x : ℝ,
      f x = Real.exp (x ^ 2) * (2 * x ^ 2 + C) := by
  refine ⟨1, ?_⟩
  intro x
  rw [f_closed3013]
  congr 1
  ring

theorem gap23 : f 0 = 1 := by
  rw [f_closed3013]
  norm_num

theorem gap24 (C : ℝ)
    (hC : ∀ x : ℝ, f x = Real.exp (x ^ 2) * (2 * x ^ 2 + C)) :
    C = 1 := by
  have h := hC 0
  rw [gap23] at h
  norm_num at h ⊢
  exact h.symm

theorem gap25 (x : ℝ) :
    f x = Real.exp (x ^ 2) * (2 * x ^ 2 + 1) := by
  rw [f_closed3013]
  congr 1
  ring

end

end ProofGap.Exercise3013
