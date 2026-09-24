import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise3762

noncomputable section

open Filter MeasureTheory
open scoped Interval

def gaussian (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2))

def scaledGaussian (α x : ℝ) : ℝ :=
  Real.sqrt α * Real.exp (-(α * x ^ 2))

def halfGaussianIntegral : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), gaussian x

def gaussianTail (u : ℝ) : ℝ :=
  ∫ x in Set.Ioi u, gaussian x

def scaledTail (α A : ℝ) : ℝ :=
  ∫ x in Set.Ioi A, scaledGaussian α x

def UniformTailConvergence : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ A α : ℝ, A₀ < A → 0 ≤ α → |scaledTail α A| < ε

private theorem scaledTail_eq_gaussianTail (α A : ℝ) (hα : 0 < α) :
    scaledTail α A = gaussianTail (Real.sqrt α * A) := by
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hpoint : ∀ x : ℝ,
      scaledGaussian α x =
        Real.sqrt α * gaussian (Real.sqrt α * x) := by
    intro x
    simp [scaledGaussian, gaussian, mul_pow, Real.sq_sqrt hα.le, mul_comm]
  calc
    scaledTail α A =
        Real.sqrt α * ∫ x in Set.Ioi A,
          gaussian (Real.sqrt α * x) := by
      unfold scaledTail
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact hpoint x
    _ = Real.sqrt α *
        ((Real.sqrt α)⁻¹ •
          ∫ x in Set.Ioi (Real.sqrt α * A), gaussian x) := by
      rw [MeasureTheory.integral_comp_mul_left_Ioi
        (g := gaussian) (a := A) (b := Real.sqrt α) hs]
    _ = gaussianTail (Real.sqrt α * A) := by
      simp [smul_eq_mul, gaussianTail, hs.ne']

private theorem integral_Ioi_tendsto_zero
    (f : ℝ → ℝ) (hf : Integrable f) :
    Tendsto (fun A : ℝ => ∫ x in Set.Ioi A, f x) atTop (nhds 0) := by
  have hnorm : Integrable (fun x : ℝ => ‖f x‖) := hf.norm
  have hmeas_all : ∀ A : ℝ,
      AEStronglyMeasurable ((Set.Ioi A).indicator f) := by
    intro A
    exact (hf.indicator measurableSet_Ioi).aestronglyMeasurable
  have hmeas_eventually :
      ∀ᶠ A : ℝ in atTop,
        AEStronglyMeasurable ((Set.Ioi A).indicator f) := by
    filter_upwards with A
    exact hmeas_all A
  have hbound_all : ∀ A : ℝ, ∀ᵐ x : ℝ,
      ‖(Set.Ioi A).indicator f x‖ ≤ ‖f x‖ := by
    intro A
    filter_upwards with x
    by_cases hx : x ∈ Set.Ioi A
    · simp [hx]
    · simp [hx]
  have hbound_eventually :
      ∀ᶠ A : ℝ in atTop, ∀ᵐ x : ℝ,
        ‖(Set.Ioi A).indicator f x‖ ≤ ‖f x‖ := by
    filter_upwards with A
    exact hbound_all A
  have hlim_all : ∀ x : ℝ,
      Tendsto (fun A : ℝ => (Set.Ioi A).indicator f x)
        atTop (nhds (0 : ℝ)) := by
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop x] with A hA
    have hx : x ∉ Set.Ioi A := by
      exact not_lt.mpr hA
    simp [hx]
  have hlim : ∀ᵐ x : ℝ,
      Tendsto (fun A : ℝ => (Set.Ioi A).indicator f x)
        atTop (nhds (0 : ℝ)) := by
    filter_upwards with x
    exact hlim_all x
  have hdom :
      Tendsto
        (fun A : ℝ => ∫ x, (Set.Ioi A).indicator f x)
        atTop (nhds (∫ _x : ℝ, (0 : ℝ))) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := fun x : ℝ => ‖f x‖)
    all_goals assumption
  simpa [MeasureTheory.integral_indicator, measurableSet_Ioi] using hdom

private theorem intervalIntegral_eq_integral_sub_tail
    (f : ℝ → ℝ) (hf : Integrable f) (u : ℝ) (hu : 0 ≤ u) :
    (∫ x in (0 : ℝ)..u, f x) =
      (∫ x in Set.Ioi (0 : ℝ), f x) - ∫ x in Set.Ioi u, f x := by
  have h1 : Integrable ((Set.Ioc (0 : ℝ) u).indicator f) :=
    hf.indicator measurableSet_Ioc
  have h2 : Integrable ((Set.Ioi u).indicator f) :=
    hf.indicator measurableSet_Ioi
  have heq :
      (Set.Ioc (0 : ℝ) u).indicator f + (Set.Ioi u).indicator f =
        (Set.Ioi (0 : ℝ)).indicator f := by
    funext x
    simp only [Pi.add_apply, Set.indicator_apply, Set.mem_Ioc, Set.mem_Ioi]
    split_ifs <;> simp_all <;> linarith
  have hsum :
      (∫ x, (Set.Ioc (0 : ℝ) u).indicator f x) +
          ∫ x, (Set.Ioi u).indicator f x =
        ∫ x, (Set.Ioi (0 : ℝ)).indicator f x := by
    calc
      _ = ∫ x, ((Set.Ioc (0 : ℝ) u).indicator f +
            (Set.Ioi u).indicator f) x :=
        (MeasureTheory.integral_add h1 h2).symm
      _ = _ := by rw [heq]
  have hsum' :
      (∫ x in Set.Ioc (0 : ℝ) u, f x) +
          ∫ x in Set.Ioi u, f x =
        ∫ x in Set.Ioi (0 : ℝ), f x := by
    simpa only [MeasureTheory.integral_indicator, measurableSet_Ioc,
      measurableSet_Ioi] using hsum
  rw [intervalIntegral.integral_of_le hu]
  linarith

theorem gap1 (α : ℝ) (hα : α = 0) :
    (∫ x in Set.Ioi (0 : ℝ), scaledGaussian α x) = 0 := by
  subst α
  simp [scaledGaussian]

theorem gap2 (α : ℝ) (hα : 0 < α) :
    (∫ x in Set.Ioi (0 : ℝ), scaledGaussian α x) =
      halfGaussianIntegral := by
  simpa [scaledTail, gaussianTail, halfGaussianIntegral] using
    scaledTail_eq_gaussianTail α 0 hα

theorem gap3 :
    halfGaussianIntegral = Real.sqrt Real.pi / 2 := by
  simpa [halfGaussianIntegral, gaussian] using
    (integral_gaussian_Ioi (1 : ℝ))

theorem gap4 (α : ℝ) (hα : 0 < α) :
    (∫ x in Set.Ioi (0 : ℝ), scaledGaussian α x) =
      Real.sqrt Real.pi / 2 := by
  rw [gap2 α hα, gap3]

theorem gap5 (α : ℝ) (hα : 0 ≤ α) :
    ∃ L : ℝ,
      Tendsto
        (fun A : ℝ => ∫ x in (0 : ℝ)..A, scaledGaussian α x)
        atTop (nhds L) := by
  rcases hα.eq_or_lt with rfl | hα
  · refine ⟨0, ?_⟩
    simpa [scaledGaussian] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0))
  · have hf : Integrable (scaledGaussian α) := by
      have h := (integrable_exp_neg_mul_sq hα).const_mul (Real.sqrt α)
      simpa [scaledGaussian] using h
    let L : ℝ := ∫ x in Set.Ioi (0 : ℝ), scaledGaussian α x
    refine ⟨L, ?_⟩
    have htail :
        Tendsto (fun A : ℝ => ∫ x in Set.Ioi A, scaledGaussian α x)
          atTop (nhds 0) :=
      integral_Ioi_tendsto_zero (scaledGaussian α) hf
    have hsub :
        Tendsto
          (fun A : ℝ => L - ∫ x in Set.Ioi A, scaledGaussian α x)
          atTop (nhds L) := by
      simpa using tendsto_const_nhds.sub htail
    apply hsub.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with A hA
    exact (intervalIntegral_eq_integral_sub_tail
      (scaledGaussian α) hf A hA).symm

theorem gap6 (A L : ℝ) (hA : 0 < A) :
    Tendsto (fun α : ℝ => scaledTail α A)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto (fun α : ℝ => gaussianTail (Real.sqrt α * A))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  constructor
  · intro h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact scaledTail_eq_gaussianTail α A hα
  · intro h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact (scaledTail_eq_gaussianTail α A hα).symm

theorem gap7 (A : ℝ) (hA : 0 < A) :
    Tendsto (fun α : ℝ => gaussianTail (Real.sqrt α * A))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds halfGaussianIntegral) := by
  have hf : Integrable gaussian := by
    simpa [gaussian] using
      (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 from zero_lt_one))
  have hsplit : ∀ u : ℝ, 0 ≤ u →
      gaussianTail u =
        halfGaussianIntegral - ∫ x in (0 : ℝ)..u, gaussian x := by
    intro u hu
    have h := intervalIntegral_eq_integral_sub_tail gaussian hf u hu
    change (∫ x in Set.Ioi u, gaussian x) =
      (∫ x in Set.Ioi (0 : ℝ), gaussian x) -
        ∫ x in (0 : ℝ)..u, gaussian x
    linarith
  have hgcont : Continuous gaussian := by
    simpa [gaussian] using
      Real.continuous_exp.comp ((continuous_id.pow 2).neg)
  have hpcont : Continuous (fun u : ℝ => ∫ x in (0 : ℝ)..u, gaussian x) :=
    (intervalIntegral.continuous_primitive
      (fun a b => hgcont.intervalIntegrable a b)) 0
  have hp0 :
      Tendsto (fun u : ℝ => ∫ x in (0 : ℝ)..u, gaussian x)
        (nhds 0) (nhds 0) := by
    have hc :
        Tendsto (fun u : ℝ => ∫ x in (0 : ℝ)..u, gaussian x)
          (nhds 0)
          (nhds ((fun u : ℝ => ∫ x in (0 : ℝ)..u, gaussian x) 0)) :=
      hpcont.continuousAt
    simpa using hc
  have hs0 :
      Tendsto (fun α : ℝ => Real.sqrt α * A) (nhds 0) (nhds 0) := by
    have hc :
        Tendsto (fun α : ℝ => Real.sqrt α * A)
          (nhds 0)
          (nhds ((fun α : ℝ => Real.sqrt α * A) 0)) :=
      Real.continuous_sqrt.continuousAt.mul continuousAt_const
    simpa using hc
  have hs :
      Tendsto (fun α : ℝ => Real.sqrt α * A)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    hs0.mono_left inf_le_left
  have ht :
      Tendsto
        (fun α : ℝ => halfGaussianIntegral -
          ∫ x in (0 : ℝ)..(Real.sqrt α * A), gaussian x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds halfGaussianIntegral) := by
    simpa using tendsto_const_nhds.sub (hp0.comp hs)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact (hsplit (Real.sqrt α * A)
    (mul_nonneg (Real.sqrt_nonneg α) (le_of_lt hA))).symm

theorem gap8 (A : ℝ) (hA : 0 < A) :
    halfGaussianIntegral = Real.sqrt Real.pi / 2 := by
  exact gap3

theorem gap9 (A : ℝ) (hA : 0 < A) :
    Tendsto (fun α : ℝ => scaledTail α A)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt Real.pi / 2)) := by
  rw [gap6 A (Real.sqrt Real.pi / 2) hA]
  simpa [gap3] using gap7 A hA

theorem gap10 (A ε₀ : ℝ) (hA : 0 < A) (hε₀ : 0 < ε₀)
    (hε₀c : ε₀ < Real.sqrt Real.pi / 2) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ε₀ < scaledTail α₀ A := by
  have hev :
      ∀ᶠ α in nhdsWithin 0 (Set.Ioi 0), ε₀ < scaledTail α A :=
    (gap9 A hA) (Ioi_mem_nhds hε₀c)
  rcases (hev.and self_mem_nhdsWithin).exists with ⟨α₀, htail, hα₀⟩
  exact ⟨α₀, hα₀, htail⟩

theorem gap11 :
    ¬ UniformTailConvergence := by
  intro h
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hεpos : 0 < Real.sqrt Real.pi / 4 := by positivity
  have hεlt : Real.sqrt Real.pi / 4 < Real.sqrt Real.pi / 2 := by
    linarith
  rcases h (Real.sqrt Real.pi / 4) hεpos with
    ⟨A₀, hA₀, htail⟩
  let A : ℝ := A₀ + 1
  have hA : 0 < A := by
    dsimp [A]
    linarith
  have hA₀A : A₀ < A := by
    dsimp [A]
    linarith
  rcases gap10 A (Real.sqrt Real.pi / 4) hA hεpos hεlt with
    ⟨α₀, hα₀, hlower⟩
  have hupper := htail A α₀ hA₀A (le_of_lt hα₀)
  have habs : scaledTail α₀ A ≤ |scaledTail α₀ A| := le_abs_self _
  linarith

theorem gap12 :
    (∀ α : ℝ, 0 ≤ α →
      ∃ L : ℝ,
        Tendsto
          (fun A : ℝ => ∫ x in (0 : ℝ)..A, scaledGaussian α x)
          atTop (nhds L)) ∧
      ¬ UniformTailConvergence := by
  constructor
  · intro α hα
    exact gap5 α hα
  · exact gap11

end

end ProofGap.Exercise3762
