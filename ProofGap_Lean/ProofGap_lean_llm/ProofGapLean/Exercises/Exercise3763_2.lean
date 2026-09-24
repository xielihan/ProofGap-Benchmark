import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3763_2

noncomputable section

open Filter MeasureTheory

def gaussian (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2))

def shiftedGaussian (α x : ℝ) : ℝ :=
  Real.exp (-((x - α) ^ 2))

def gaussianIntegral : ℝ :=
  ∫ x : ℝ, gaussian x

def gaussianTail (u : ℝ) : ℝ :=
  ∫ x in Set.Ioi u, gaussian x

def shiftedTail (A α : ℝ) : ℝ :=
  ∫ x in Set.Ioi A, shiftedGaussian α x

def UniformTailConvergence : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ A α : ℝ, A₀ < A → |shiftedTail A α| < ε

private theorem shiftedTail_eq_gaussianTail (A α : ℝ) :
    shiftedTail A α = gaussianTail (A - α) := by
  unfold shiftedTail gaussianTail
  calc
    (∫ x in Set.Ioi A, shiftedGaussian α x)
        = ∫ x : ℝ, (Set.Ioi A).indicator (shiftedGaussian α) x := by
            symm
            exact integral_indicator measurableSet_Ioi
    _ = ∫ x : ℝ,
          ((Set.Ioi (A - α)).indicator gaussian) (x - α) := by
            apply integral_congr_ae
            filter_upwards with x
            by_cases hx : A < x
            · have hx' : A - α < x - α := sub_lt_sub_right hx α
              simp [Set.indicator_apply, hx, hx', shiftedGaussian, gaussian]
            · have hx' : ¬ A - α < x - α := by
                intro h
                exact hx ((sub_lt_sub_iff_right α).mp h)
              simp [Set.indicator_apply, hx, hx', shiftedGaussian, gaussian]
    _ = ∫ x : ℝ, (Set.Ioi (A - α)).indicator gaussian x := by
          simpa [sub_eq_add_neg] using
            (integral_add_right_eq_self
              ((Set.Ioi (A - α)).indicator gaussian) (-α))
    _ = ∫ x in Set.Ioi (A - α), gaussian x :=
          integral_indicator measurableSet_Ioi

theorem gap1 (α : ℝ) :
    (∫ x : ℝ, shiftedGaussian α x) = gaussianIntegral := by
  change (∫ x : ℝ, gaussian (x - α)) = ∫ x : ℝ, gaussian x
  simpa [sub_eq_add_neg] using
    (integral_add_right_eq_self gaussian (-α))

theorem gap2 :
    gaussianIntegral = Real.sqrt Real.pi := by
  simpa [gaussianIntegral, gaussian] using
    (integral_gaussian (1 : ℝ))

theorem gap3 (α : ℝ) :
    (∫ x : ℝ, shiftedGaussian α x) = Real.sqrt Real.pi := by
  rw [gap1 α, gap2]

theorem gap4 (A L : ℝ) (hA : 0 < A) :
    Tendsto (fun α : ℝ => shiftedTail A α) atTop (nhds L) ↔
      Tendsto (fun α : ℝ => gaussianTail (A - α)) atTop (nhds L) := by
  constructor <;> intro h
  · simpa only [shiftedTail_eq_gaussianTail] using h
  · simpa only [shiftedTail_eq_gaussianTail] using h

theorem gap5 (A : ℝ) (hA : 0 < A) :
    Tendsto (fun α : ℝ => gaussianTail (A - α))
      atTop (nhds gaussianIntegral) := by
  have hg : Integrable gaussian := by
    simpa [gaussian] using
      (integrable_exp_neg_mul_sq (zero_lt_one : (0 : ℝ) < 1))
  have ht :
      Tendsto
        (fun α : ℝ =>
          ∫ x : ℝ, (Set.Ioi (A - α)).indicator gaussian x)
        atTop (nhds (∫ x : ℝ, gaussian x)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => ‖gaussian x‖) ?_ ?_ hg.norm ?_
    · filter_upwards with α
      exact hg.1.indicator measurableSet_Ioi
    · filter_upwards with α
      filter_upwards with x
      by_cases hx : x ∈ Set.Ioi (A - α)
      · simp [hx]
      · simp [hx]
    · filter_upwards with x
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (A - x + 1)] with α hα
      have hxα : A - α < x := by
        linarith
      simp [hxα]
  change Tendsto
    (fun α : ℝ => ∫ x in Set.Ioi (A - α), gaussian x)
    atTop (nhds (∫ x : ℝ, gaussian x))
  apply ht.congr'
  filter_upwards with α
  exact integral_indicator measurableSet_Ioi

theorem gap6 (A : ℝ) (hA : 0 < A) :
    gaussianIntegral = Real.sqrt Real.pi := by
  exact gap2

theorem gap7 (A : ℝ) (hA : 0 < A) :
    Tendsto (fun α : ℝ => shiftedTail A α)
      atTop (nhds (Real.sqrt Real.pi)) := by
  apply (gap4 A (Real.sqrt Real.pi) hA).2
  simpa only [gap6 A hA] using gap5 A hA

theorem gap8 (A : ℝ) (hA : 0 < A) :
    ∃ α : ℝ, A < α ∧
      Real.sqrt Real.pi / 2 < shiftedTail A α := by
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hhalf : Real.sqrt Real.pi / 2 < Real.sqrt Real.pi := by
    linarith
  have hev : ∀ᶠ α : ℝ in atTop,
      Real.sqrt Real.pi / 2 < shiftedTail A α :=
    ((tendsto_order.1 (gap7 A hA)).1 _ hhalf)
  have hevA : ∀ᶠ α : ℝ in atTop, A < α := eventually_gt_atTop A
  rcases (hev.and hevA).exists with ⟨α, htail, hα⟩
  exact ⟨α, hα, htail⟩

theorem gap9 :
    ¬ UniformTailConvergence := by
  intro h
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have heps : 0 < Real.sqrt Real.pi / 2 := by
    linarith
  rcases h (Real.sqrt Real.pi / 2) heps with ⟨A₀, hA₀, huniform⟩
  let A : ℝ := A₀ + 1
  have hA : 0 < A := by
    dsimp [A]
    linarith
  have hA₀A : A₀ < A := by
    dsimp [A]
    linarith
  rcases gap8 A hA with ⟨α, hAα, htail⟩
  have habs : |shiftedTail A α| < Real.sqrt Real.pi / 2 :=
    huniform A α hA₀A
  have hle : shiftedTail A α ≤ |shiftedTail A α| := le_abs_self _
  linarith

theorem gap10 :
    ¬ UniformTailConvergence := by
  exact gap9

end

end ProofGap.Exercise3763_2
