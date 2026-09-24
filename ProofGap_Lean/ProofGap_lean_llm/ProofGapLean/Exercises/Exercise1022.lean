import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1022

noncomputable section

open scoped Topology

def f (x : ℝ) : ℝ := Real.cos (Real.log x)

def BoundedOn (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ s, |g x| ≤ M

private theorem trig_nat_two_pi (n : ℕ) :
    Real.cos (2 * Real.pi * (n : ℝ)) = 1 ∧
      Real.sin (2 * Real.pi * (n : ℝ)) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hangle :
          2 * Real.pi * (Nat.succ n : ℝ) =
            2 * Real.pi * (n : ℝ) + 2 * Real.pi := by
        rw [Nat.cast_succ]
        ring
      rw [hangle, Real.cos_add, Real.sin_add]
      rw [ih.1, ih.2]
      simp

private theorem eventually_gt_atTop (a : ℝ) :
    ∀ᶠ b : ℝ in atTop, a < b :=
  Filter.eventually_gt_atTop a

theorem gap1 : BoundedOn f (Set.Ioi 0) := by
  refine ⟨1, zero_le_one, ?_⟩
  intro x hx
  exact Real.abs_cos_le_one (Real.log x)

theorem gap2 : DifferentiableOn ℝ f (Set.Ioi 0) := by
  intro x hx
  have h :=
    (Real.hasDerivAt_cos (Real.log x)).comp x
      (Real.hasDerivAt_log hx.ne')
  simpa only [f] using h.differentiableAt.differentiableWithinAt

theorem gap3 (x : ℝ) (hx : 0 < x) :
    HasDerivAt f (-(Real.sin (Real.log x) / x)) x := by
  simpa [f, div_eq_mul_inv] using
    (Real.hasDerivAt_cos (Real.log x)).comp x
      (Real.hasDerivAt_log hx.ne')

theorem gap4 : Tendsto (deriv f) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have hneg : Tendsto (fun x : ℝ => -(1 / x)) atTop (𝓝 0) := by
    simpa using hinv.neg
  have hb :
      ∀ᶠ x : ℝ in atTop,
        -(1 / x) ≤ deriv f x ∧ deriv f x ≤ 1 / x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hd : deriv f x = -(Real.sin (Real.log x) / x) :=
      (gap3 x hx).deriv
    have habsx : |x| = x := abs_of_pos hx
    have habs : |-(Real.sin (Real.log x) / x)| ≤ 1 / x := by
      rw [abs_neg, abs_div, habsx]
      exact div_le_div_of_nonneg_right
        (Real.abs_sin_le_one (Real.log x)) hx.le
    rw [hd]
    exact abs_le.mp habs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hinv
    (hb.mono ?_) (hb.mono ?_)
  · intro x hx
    exact hx.1
  · intro x hx
    exact hx.2

theorem gap5 : ¬ ∃ L : ℝ, Tendsto f atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hev :
      ∀ᶠ x : ℝ in atTop, dist (f x) L < (1 / 2 : ℝ) := by
    simpa only [Metric.mem_ball] using
      hL.eventually
        (Metric.ball_mem_nhds L (by norm_num : (0 : ℝ) < 1 / 2))
  rcases Filter.eventually_atTop.1 hev with ⟨a, ha⟩
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt a
  have hc : (1 : ℝ) ≤ 2 * Real.pi := by
    linarith [Real.pi_gt_three]
  have hnz :
      (n : ℝ) ≤ 2 * Real.pi * (n : ℝ) := by
    calc
      (n : ℝ) = 1 * (n : ℝ) := by ring
      _ ≤ (2 * Real.pi) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
  have hx0 :
      a ≤ Real.exp (2 * Real.pi * (n : ℝ)) := by
    calc
      a ≤ (n : ℝ) := hn.le
      _ ≤ 2 * Real.pi * (n : ℝ) := hnz
      _ ≤ 2 * Real.pi * (n : ℝ) + 1 := by linarith
      _ ≤ Real.exp (2 * Real.pi * (n : ℝ)) :=
        Real.add_one_le_exp _
  have hx1 :
      a ≤ Real.exp (Real.pi + 2 * Real.pi * (n : ℝ)) := by
    calc
      a ≤ (n : ℝ) := hn.le
      _ ≤ 2 * Real.pi * (n : ℝ) := hnz
      _ ≤ Real.pi + 2 * Real.pi * (n : ℝ) := by
        linarith [Real.pi_pos]
      _ ≤ Real.pi + 2 * Real.pi * (n : ℝ) + 1 := by linarith
      _ ≤ Real.exp (Real.pi + 2 * Real.pi * (n : ℝ)) :=
        Real.add_one_le_exp _
  have h0raw := ha (Real.exp (2 * Real.pi * (n : ℝ))) hx0
  have h1raw :=
    ha (Real.exp (Real.pi + 2 * Real.pi * (n : ℝ))) hx1
  have h0 : dist (1 : ℝ) L < (1 / 2 : ℝ) := by
    simpa [f, (trig_nat_two_pi n).1] using h0raw
  have h1 : dist (-1 : ℝ) L < (1 / 2 : ℝ) := by
    simpa [f, Real.cos_add, (trig_nat_two_pi n).1,
      (trig_nat_two_pi n).2] using h1raw
  rw [Real.dist_eq] at h0 h1
  rcases abs_lt.mp h0 with ⟨h0l, h0u⟩
  rcases abs_lt.mp h1 with ⟨h1l, h1u⟩
  linarith

end

end ProofGap.Exercise1022
