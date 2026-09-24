import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3764

noncomputable section

open Filter MeasureTheory
open scoped Interval

def gaussian (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2))

def kernel (x y : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 * (1 + y ^ 2))) * Real.sin x

def kernelTail (x A : ℝ) : ℝ :=
  ∫ y in Set.Ioi A, kernel x y

def gaussianTail (u : ℝ) : ℝ :=
  ∫ t in Set.Ioi u, gaussian t

def UniformTailConvergence : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ A x : ℝ, A₀ < A → |kernelTail x A| < ε

private lemma kernel_factor (x y : ℝ) :
    kernel x y =
      (Real.sin x * Real.exp (-(x ^ 2))) *
        gaussian (x * y) := by
  unfold kernel gaussian
  calc
    Real.exp (-(x ^ 2 * (1 + y ^ 2))) * Real.sin x =
        Real.sin x * Real.exp (-(x ^ 2 * (1 + y ^ 2))) := by
      ring
    _ = Real.sin x *
        (Real.exp (-(x ^ 2)) * Real.exp (-((x * y) ^ 2))) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = (Real.sin x * Real.exp (-(x ^ 2))) *
        Real.exp (-((x * y) ^ 2)) := by ring

private lemma integrable_gaussian :
    Integrable gaussian := by
  unfold gaussian
  simpa only [one_mul, neg_mul] using
    (integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos)

private lemma integrableOn_kernel (x : ℝ) :
    IntegrableOn (kernel x) (Set.Ioi 0) := by
  by_cases hx : x = 0
  · subst x
    have hk : kernel 0 = fun _ : ℝ => 0 := by
      funext y
      simp [kernel]
    rw [hk]
    exact integrableOn_zero
  · have hcomp :
        Integrable (fun y : ℝ => gaussian (x * y)) :=
      integrable_gaussian.comp_mul_left' hx
    have hmul :
        Integrable
          (fun y : ℝ =>
            (Real.sin x * Real.exp (-(x ^ 2))) *
              gaussian (x * y)) :=
      hcomp.const_mul _
    exact (hmul.congr (Filter.Eventually.of_forall
      (fun y => (kernel_factor x y).symm))).integrableOn

theorem gap1 (x : ℝ) :
    ∃ L : ℝ,
      Tendsto (fun A : ℝ => ∫ y in (0 : ℝ)..A, kernel x y)
        atTop (nhds L) := by
  refine ⟨∫ y in Set.Ioi 0, kernel x y, ?_⟩
  exact intervalIntegral_tendsto_integral_Ioi
    0 (integrableOn_kernel x) tendsto_id

private lemma kernelTail_formula (x A : ℝ) (hx : 0 < x) :
    kernelTail x A =
      Real.sin x / x * Real.exp (-(x ^ 2)) *
        gaussianTail (A * x) := by
  unfold kernelTail gaussianTail
  calc
    (∫ y in Set.Ioi A, kernel x y) =
        (Real.sin x * Real.exp (-(x ^ 2))) *
          ∫ y in Set.Ioi A, gaussian (x * y) := by
      rw [← MeasureTheory.integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact kernel_factor x y
    _ = (Real.sin x * Real.exp (-(x ^ 2))) *
          (x⁻¹ • ∫ t in Set.Ioi (x * A), gaussian t) := by
      rw [integral_comp_mul_left_Ioi gaussian A hx]
    _ = Real.sin x / x * Real.exp (-(x ^ 2)) *
          ∫ t in Set.Ioi (A * x), gaussian t := by
      simp only [smul_eq_mul]
      rw [mul_comm x A]
      field_simp [hx.ne']

theorem gap2 (x : ℝ) (hx : 0 < x) :
    (∫ y in Set.Ioi (0 : ℝ), kernel x y) =
      Real.sin x / x * Real.exp (-(x ^ 2)) *
        (Real.sqrt Real.pi / 2) := by
  rw [show (∫ y in Set.Ioi (0 : ℝ), kernel x y) =
      Real.sin x / x * Real.exp (-(x ^ 2)) *
        gaussianTail 0 by
    simpa using kernelTail_formula x 0 hx]
  unfold gaussianTail gaussian
  rw [show (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(t ^ 2))) = Real.sqrt Real.pi / 2 by
    simpa using (integral_gaussian_Ioi (1 : ℝ))]

theorem gap3 (x A : ℝ) (hx : 0 < x) (hA : 0 < A) :
    kernelTail x A =
      Real.sin x / x * Real.exp (-(x ^ 2)) *
        gaussianTail (A * x) := by
  exact kernelTail_formula x A hx

private lemma continuous_gaussian :
    Continuous gaussian := by
  unfold gaussian
  exact (continuous_id.pow 2).neg.rexp

private lemma gaussianTail_sub_interval (u : ℝ) :
    gaussianTail u =
      gaussianTail 0 - ∫ t in (0 : ℝ)..u, gaussian t := by
  have hsplit :=
    intervalIntegral.integral_interval_add_Ioi
      (f := gaussian) (a := (0 : ℝ)) (b := u)
      integrable_gaussian.integrableOn
      integrable_gaussian.integrableOn
  unfold gaussianTail
  linarith

private lemma gaussianTail_tendsto_zero :
    Tendsto gaussianTail
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (gaussianTail 0)) := by
  have hint :
      Tendsto
        (fun u : ℝ => ∫ t in (0 : ℝ)..u, gaussian t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hfull :
        Tendsto
          (fun u : ℝ => ∫ t in (0 : ℝ)..u, gaussian t)
          (nhds 0)
          (nhds (∫ t in (0 : ℝ)..(0 : ℝ), gaussian t)) :=
      (intervalIntegral.differentiable_integral_of_continuous
        continuous_gaussian).continuous.continuousAt
    simpa using hfull.mono_left inf_le_left
  have hsub :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => gaussianTail 0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (gaussianTail 0))).sub hint
  simpa only [sub_zero] using
    hsub.congr'
      (Filter.Eventually.of_forall
        (fun u => (gaussianTail_sub_interval u).symm))

theorem gap4 (A : ℝ) (hA : 0 < A) :
    Tendsto (fun x : ℝ => kernelTail x A)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ t in Set.Ioi (0 : ℝ), gaussian t)) := by
  have hsinc :
      Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hs0 :
        Tendsto Real.sinc
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      simpa using
        (Real.continuous_sinc.tendsto 0).mono_left inf_le_left
    refine hs0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.sinc_of_ne_zero (ne_of_gt hx)
  have hexp :
      Tendsto (fun x : ℝ => Real.exp (-(x ^ 2)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hfull :
        Tendsto (fun x : ℝ => Real.exp (-(x ^ 2)))
          (nhds 0) (nhds (Real.exp (-(0 ^ 2)))) :=
      (continuousAt_id.pow 2).neg.rexp
    simpa using hfull.mono_left inf_le_left
  have hAxN :
      Tendsto (fun x : ℝ => A * x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using
      ((tendsto_const_nhds.mul tendsto_id).mono_left inf_le_left :
        Tendsto (fun x : ℝ => A * x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (A * 0)))
  have hAx :
      Tendsto (fun x : ℝ => A * x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [nhdsWithin]
    refine tendsto_inf.2 ⟨hAxN, ?_⟩
    rw [tendsto_principal]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_pos hA hx
  have htail :
      Tendsto (fun x : ℝ => gaussianTail (A * x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (gaussianTail 0)) :=
    gaussianTail_tendsto_zero.comp hAx
  have hprod :
      Tendsto
        (fun x : ℝ =>
          Real.sin x / x * Real.exp (-(x ^ 2)) *
            gaussianTail (A * x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (gaussianTail 0)) := by
    simpa using (hsinc.mul hexp).mul htail
  have hformula :
      ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        kernelTail x A =
          Real.sin x / x * Real.exp (-(x ^ 2)) *
            gaussianTail (A * x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact kernelTail_formula x A hx
  have hformula' :
      ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        Real.sin x / x * Real.exp (-(x ^ 2)) *
            gaussianTail (A * x) =
          kernelTail x A :=
    hformula.mono (fun _ h => h.symm)
  simpa [gaussianTail] using hprod.congr' hformula'

theorem gap5 (A : ℝ) (hA : 0 < A) :
    (∫ t in Set.Ioi (0 : ℝ), gaussian t) =
      Real.sqrt Real.pi / 2 := by
  unfold gaussian
  simpa using (integral_gaussian_Ioi (1 : ℝ))

theorem gap6 (A : ℝ) (hA : 0 < A) :
    Tendsto (fun x : ℝ => kernelTail x A)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.sqrt Real.pi / 2)) := by
  rw [← gap5 A hA]
  exact gap4 A hA

private lemma not_uniform :
    ¬ UniformTailConvergence := by
  intro h
  let ε : ℝ := Real.sqrt Real.pi / 4
  have hspos : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.2 Real.pi_pos
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  rcases h ε hε with ⟨A₀, hA₀, htail⟩
  let A : ℝ := A₀ + 1
  have hA₀A : A₀ < A := by
    dsimp [A]
    linarith
  have hA : 0 < A := hA₀.trans hA₀A
  have hlim :
      Tendsto (fun x : ℝ => kernelTail x A)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Real.sqrt Real.pi / 2)) :=
    gap6 A hA
  have hεL : ε < Real.sqrt Real.pi / 2 := by
    dsimp [ε]
    linarith
  have hev :
      ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ε < kernelTail x A :=
    hlim.eventually (Ioi_mem_nhds hεL)
  rcases (hev.and self_mem_nhdsWithin).exists with
    ⟨x, hxlarge, hxpos⟩
  have hxsmall := htail A x hA₀A
  have hxle : kernelTail x A ≤ |kernelTail x A| :=
    le_abs_self _
  linarith

theorem gap7 :
    ¬ UniformTailConvergence := by
  exact not_uniform

theorem gap8 :
    ¬ UniformTailConvergence := by
  exact not_uniform

end

end ProofGap.Exercise3764
