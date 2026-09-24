import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2187
noncomputable section

open Filter
open scoped BigOperators Interval

def h (n : ℕ) : ℝ := Real.pi / (2 * (n : ℝ))
def leftSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, h n * Real.sin ((i : ℝ) * h n)
def limitExpression (n : ℕ) : ℝ :=
  (h n / 2) / Real.sin (h n / 2) *
    (Real.cos (Real.pi / (4 * (n : ℝ))) -
      Real.cos (((2 * (n : ℝ) - 1) * Real.pi) / (4 * (n : ℝ))))

theorem gap1 (n : ℕ) (hn : 0 < n) :
    leftSum n =
      ∑ i ∈ Finset.range n, h n * Real.sin ((i : ℝ) * h n) := by
  rfl

theorem gap2 (n i : ℕ) (hn : 0 < n) :
    Real.sin ((i : ℝ) * h n) =
      (Real.cos (((2 * (i : ℝ) - 1) / 2) * h n) -
        Real.cos (((2 * (i : ℝ) + 1) / 2) * h n)) /
          (2 * Real.sin (h n / 2)) := by
  have hn1 : 1 ≤ n := hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    positivity
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn1
  have hhpos : 0 < h n / 2 := by
    unfold h
    positivity
  have hhLt : h n / 2 < Real.pi := by
    unfold h
    rw [div_div]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ) * 2)]
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (h n / 2) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hhpos hhLt)
  have hleft :
      (((2 * (i : ℝ) - 1) / 2) * h n) =
        (i : ℝ) * h n - h n / 2 := by
    ring
  have hright :
      (((2 * (i : ℝ) + 1) / 2) * h n) =
        (i : ℝ) * h n + h n / 2 := by
    ring
  rw [hleft, hright, Real.cos_sub, Real.cos_add]
  field_simp [hsin]
  ring

theorem gap3 (n : ℕ) (hn : 0 < n) :
    leftSum n =
      h n / (2 * Real.sin (h n / 2)) *
        ∑ i ∈ Finset.range n,
          (Real.cos (((2 * (i : ℝ) - 1) / 2) * h n) -
            Real.cos (((2 * (i : ℝ) + 1) / 2) * h n)) := by
  unfold leftSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [gap2 n i hn]
  ring

theorem gap4 (n : ℕ) (hn : 0 < n) :
    h n / (2 * Real.sin (h n / 2)) *
        (∑ i ∈ Finset.range n,
          (Real.cos (((2 * (i : ℝ) - 1) / 2) * h n) -
            Real.cos (((2 * (i : ℝ) + 1) / 2) * h n))) =
      h n / (2 * Real.sin (h n / 2)) *
        (Real.cos (h n / 2) -
          Real.cos (((2 * (n : ℝ) - 1) / 2) * h n)) := by
  have htel : ∀ m : ℕ,
      (∑ i ∈ Finset.range m,
        (Real.cos (((2 * (i : ℝ) - 1) / 2) * h n) -
          Real.cos (((2 * (i : ℝ) + 1) / 2) * h n))) =
        Real.cos (h n / 2) -
          Real.cos (((2 * (m : ℝ) - 1) / 2) * h n) := by
    intro m
    induction m with
    | zero =>
        have hz : (((2 * (0 : ℝ) - 1) / 2) * h n) = -(h n / 2) := by
          ring
        simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
        rw [hz, Real.cos_neg]
        ring
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have hs :
            (((2 * ((Nat.succ m : ℕ) : ℝ) - 1) / 2) * h n) =
              (((2 * (m : ℝ) + 1) / 2) * h n) := by
          simp only [Nat.cast_succ]
          ring
        rw [hs]
        ring
  rw [htel n]

theorem gap5 (n : ℕ) (hn : 0 < n) :
    leftSum n =
      h n / (2 * Real.sin (h n / 2)) *
        (Real.cos (h n / 2) -
          Real.cos (((2 * (n : ℝ) - 1) / 2) * h n)) := by
  rw [gap3 n hn]
  exact gap4 n hn

theorem gap6 :
    Tendsto leftSum atTop (nhds (1 : ℝ)) ↔
      Tendsto limitExpression atTop (nhds (1 : ℝ)) := by
  have heq (n : ℕ) (hn : 0 < n) : leftSum n = limitExpression n := by
    rw [gap5 n hn]
    unfold limitExpression
    have hnR : (0 : ℝ) < (n : ℝ) := by
      positivity
    have hnRne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hcoef :
        h n / (2 * Real.sin (h n / 2)) =
          (h n / 2) / Real.sin (h n / 2) := by
      ring
    have hfirst : h n / 2 = Real.pi / (4 * (n : ℝ)) := by
      unfold h
      field_simp [hnRne]
      ring
    have hlast :
        ((2 * (n : ℝ) - 1) / 2) * h n =
          ((2 * (n : ℝ) - 1) * Real.pi) / (4 * (n : ℝ)) := by
      unfold h
      field_simp [hnRne]
      ring
    rw [hcoef, hfirst, hlast]
  have hfun : leftSum = limitExpression := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [leftSum, limitExpression, h]
    · exact heq n (Nat.pos_of_ne_zero hn)
  rw [hfun]

theorem gap7 :
    Tendsto limitExpression atTop (nhds (1 : ℝ)) := by
  let x : ℕ → ℝ := fun n => (Real.pi / 4) * ((n : ℝ)⁻¹)
  have hinv :
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hx : Tendsto x atTop (nhds (0 : ℝ)) := by
    have hmul :
        Tendsto (fun n : ℕ => (Real.pi / 4) * ((n : ℝ)⁻¹))
          atTop (nhds ((Real.pi / 4) * 0)) :=
      tendsto_const_nhds.mul hinv
    simpa [x] using hmul
  have hsinc0 :
      Tendsto (fun n => Real.sinc (x n)) atTop
        (nhds (Real.sinc 0)) :=
    (Real.continuous_sinc.tendsto 0).comp hx
  have hsinc :
      Tendsto (fun n => Real.sinc (x n)) atTop (nhds (1 : ℝ)) := by
    have hs0 : Real.sinc 0 = 1 := by
      simp [Real.sinc]
    simpa [hs0] using hsinc0
  have hsincInv :
      Tendsto (fun n => (Real.sinc (x n))⁻¹) atTop (nhds (1 : ℝ)) := by
    simpa using hsinc.inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)
  have htrig :
      Tendsto (fun n => Real.cos (x n) - Real.sin (x n))
        atTop (nhds (1 : ℝ)) := by
    have hcos := (Real.continuous_cos.tendsto 0).comp hx
    have hsin := (Real.continuous_sin.tendsto 0).comp hx
    simpa using hcos.sub hsin
  have hprod :
      Tendsto
        (fun n => (Real.sinc (x n))⁻¹ *
          (Real.cos (x n) - Real.sin (x n)))
        atTop (nhds (1 : ℝ)) := by
    simpa using hsincInv.mul htrig
  have hev :
      limitExpression =ᶠ[atTop]
        (fun n => (Real.sinc (x n))⁻¹ *
          (Real.cos (x n) - Real.sin (x n))) :=
    (eventually_ge_atTop (1 : ℕ)).mono (by
      intro n hn
      have hnpos : 0 < n := hn
      have hnR : (0 : ℝ) < (n : ℝ) := by
        positivity
      have hnRne : (n : ℝ) ≠ 0 := ne_of_gt hnR
      have hxne : x n ≠ 0 := by
        dsimp [x]
        positivity
      have ha : h n / 2 = x n := by
        dsimp [x, h]
        field_simp [hnRne] <;> ring
      have hb : Real.pi / (4 * (n : ℝ)) = x n := by
        dsimp [x]
        field_simp [hnRne] <;> ring
      have hc :
          ((2 * (n : ℝ) - 1) * Real.pi) / (4 * (n : ℝ)) =
            Real.pi / 2 - x n := by
        dsimp [x]
        field_simp [hnRne] <;> ring
      have hratio :
          x n / Real.sin (x n) = (Real.sinc (x n))⁻¹ := by
        simp [Real.sinc, hxne, inv_div]
      unfold limitExpression
      rw [ha, hb, hc, Real.cos_sub]
      simp only [Real.cos_pi_div_two, Real.sin_pi_div_two,
        zero_mul, one_mul, zero_add]
      rw [hratio])
  exact (tendsto_congr' hev).2 hprod

theorem gap8 :
    Tendsto leftSum atTop (nhds (1 : ℝ)) := by
  exact gap6.mpr gap7

theorem gap9 :
    (∫ x in (0 : ℝ)..(Real.pi / 2), Real.sin x) = 1 := by
  have hderiv :
      deriv (fun x : ℝ => -Real.cos x) = fun x : ℝ => Real.sin x := by
    funext x
    simpa using (Real.hasDerivAt_cos x).neg.deriv
  have hdiff :
      ∀ x ∈ [[(0 : ℝ), Real.pi / 2]],
        DifferentiableAt ℝ (fun y : ℝ => -Real.cos y) x := by
    intro x hx
    exact (Real.hasDerivAt_cos x).neg.differentiableAt
  have hFTC := intervalIntegral.integral_deriv_eq_sub'
    (fun x : ℝ => -Real.cos x) hderiv hdiff
    Real.continuous_sin.continuousOn
  simpa using hFTC

end
end ProofGap.Exercise2187
