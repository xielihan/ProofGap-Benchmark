import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1143

noncomputable section

def x (t : ℝ) : ℝ := Real.exp t * Real.cos t
def y (t : ℝ) : ℝ := Real.exp t * Real.sin t
def d1 (t : ℝ) : ℝ := deriv y t / deriv x t
def d2 (t : ℝ) : ℝ := deriv d1 t / deriv x t
def d3 (t : ℝ) : ℝ := deriv d2 t / deriv x t
def θ (t : ℝ) : ℝ := Real.pi / 4 + t

private theorem hasDerivAt_x (t : ℝ) :
    HasDerivAt x (Real.exp t * (Real.cos t - Real.sin t)) t := by
  unfold x
  convert (Real.hasDerivAt_exp t).mul (Real.hasDerivAt_cos t) using 1 <;> ring

private theorem hasDerivAt_y (t : ℝ) :
    HasDerivAt y (Real.exp t * (Real.sin t + Real.cos t)) t := by
  unfold y
  convert (Real.hasDerivAt_exp t).mul (Real.hasDerivAt_sin t) using 1 <;> ring

private theorem d1_formula (t : ℝ) :
    d1 t =
      Real.exp t * (Real.sin t + Real.cos t) /
        (Real.exp t * (Real.cos t - Real.sin t)) := by
  unfold d1
  rw [(hasDerivAt_y t).deriv, (hasDerivAt_x t).deriv]

private theorem d1_simple (t : ℝ) :
    d1 t =
      (Real.sin t + Real.cos t) / (Real.cos t - Real.sin t) := by
  rw [d1_formula]
  field_simp [Real.exp_ne_zero]

private theorem sin_theta_eq (t : ℝ) :
    Real.sin (θ t) =
      (Real.sqrt 2 / 2) * (Real.sin t + Real.cos t) := by
  rw [θ, Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
  ring

private theorem cos_theta_eq (t : ℝ) :
    Real.cos (θ t) =
      (Real.sqrt 2 / 2) * (Real.cos t - Real.sin t) := by
  rw [θ, Real.cos_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
  ring

private theorem cos_sub_sin_ne_of_cos_theta_ne (t : ℝ)
    (h : Real.cos (θ t) ≠ 0) : Real.cos t - Real.sin t ≠ 0 := by
  intro hzero
  apply h
  rw [cos_theta_eq, hzero, mul_zero]

private theorem cos_sub_sin_eq_sqrt_two_mul_cos_theta (t : ℝ) :
    Real.cos t - Real.sin t = Real.sqrt 2 * Real.cos (θ t) := by
  calc
    Real.cos t - Real.sin t =
        (Real.sqrt 2 ^ 2 / 2) * (Real.cos t - Real.sin t) := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ = Real.sqrt 2 *
        ((Real.sqrt 2 / 2) * (Real.cos t - Real.sin t)) := by ring
    _ = Real.sqrt 2 * Real.cos (θ t) := by rw [← cos_theta_eq]

private theorem eventually_cos_theta_ne (t : ℝ)
    (h : Real.cos (θ t) ≠ 0) :
    ∀ᶠ s in nhds t, Real.cos (θ s) ≠ 0 := by
  have hc : Continuous (fun s : ℝ => Real.cos (Real.pi / 4 + s)) :=
    Real.continuous_cos.comp (continuous_const.add continuous_id)
  simpa [θ] using hc.continuousAt.eventually_ne h

theorem gap1 (t : ℝ) (h : Real.cos t - Real.sin t ≠ 0) :
    d1 t =
      Real.exp t * (Real.sin t + Real.cos t) /
        (Real.exp t * (Real.cos t - Real.sin t)) := by
  exact d1_formula t

theorem gap2 (t : ℝ) (h : Real.cos (θ t) ≠ 0) :
    Real.exp t * (Real.sin t + Real.cos t) /
        (Real.exp t * (Real.cos t - Real.sin t)) =
      Real.sin (θ t) / Real.cos (θ t) := by
  have hdiff := cos_sub_sin_ne_of_cos_theta_ne t h
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  rw [sin_theta_eq, cos_theta_eq]
  field_simp [Real.exp_ne_zero, hdiff, hsqrt] <;> ring

theorem gap3 (t : ℝ) (h : Real.cos (θ t) ≠ 0) :
    Real.sin (θ t) / Real.cos (θ t) = Real.tan (θ t) := by
  simpa [Real.tan_eq_sin_div_cos]

theorem gap4 (t : ℝ) (h : Real.cos (θ t) ≠ 0) :
    d1 t = Real.tan (θ t) := by
  have hdiff := cos_sub_sin_ne_of_cos_theta_ne t h
  calc
    d1 t =
        Real.exp t * (Real.sin t + Real.cos t) /
          (Real.exp t * (Real.cos t - Real.sin t)) := gap1 t hdiff
    _ = Real.sin (θ t) / Real.cos (θ t) := gap2 t h
    _ = Real.tan (θ t) := gap3 t h

theorem gap5 (t : ℝ) (h : Real.cos (θ t) ≠ 0) :
    d2 t =
      (1 / Real.cos (θ t) ^ 2) /
        (Real.exp t * (Real.cos t - Real.sin t)) := by
  have hdiff := cos_sub_sin_ne_of_cos_theta_ne t h
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have ha :
      HasDerivAt (fun s : ℝ => Real.sin s + Real.cos s)
        (Real.cos t - Real.sin t) t := by
    convert (Real.hasDerivAt_sin t).add (Real.hasDerivAt_cos t) using 1 <;> ring
  have hb :
      HasDerivAt (fun s : ℝ => Real.cos s - Real.sin s)
        (-Real.sin t - Real.cos t) t := by
    convert (Real.hasDerivAt_cos t).sub (Real.hasDerivAt_sin t) using 1 <;> ring
  have hq :
      HasDerivAt
        (fun s : ℝ =>
          (Real.sin s + Real.cos s) / (Real.cos s - Real.sin s))
        (1 / Real.cos (θ t) ^ 2) t := by
    convert ha.div hb hdiff using 1
    rw [cos_theta_eq]
    field_simp [hdiff, hsqrt]
    nlinarith [Real.sin_sq_add_cos_sq t,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hfun :
      d1 = fun s : ℝ =>
        (Real.sin s + Real.cos s) / (Real.cos s - Real.sin s) :=
    funext d1_simple
  have hd1 : HasDerivAt d1 (1 / Real.cos (θ t) ^ 2) t := by
    rwa [hfun]
  unfold d2
  rw [hd1.deriv, (hasDerivAt_x t).deriv]

theorem gap6 (t : ℝ) (h : Real.cos (θ t) ≠ 0) :
    (1 / Real.cos (θ t) ^ 2) /
        (Real.exp t * (Real.cos t - Real.sin t)) =
      Real.exp (-t) / (Real.sqrt 2 * Real.cos (θ t) ^ 3) := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  rw [cos_sub_sin_eq_sqrt_two_mul_cos_theta, Real.exp_neg]
  field_simp [h, hsqrt, Real.exp_ne_zero] <;> ring

theorem gap7 (t : ℝ) (h : Real.cos (θ t) ≠ 0) :
    d2 t = Real.exp (-t) / (Real.sqrt 2 * Real.cos (θ t) ^ 3) := by
  calc
    d2 t =
        (1 / Real.cos (θ t) ^ 2) /
          (Real.exp t * (Real.cos t - Real.sin t)) := gap5 t h
    _ = Real.exp (-t) / (Real.sqrt 2 * Real.cos (θ t) ^ 3) := gap6 t h

def rawThird (t : ℝ) : ℝ :=
  ((1 / Real.sqrt 2) * Real.exp (-t) *
      (-(Real.cos (θ t))⁻¹ ^ 3 +
        3 * (Real.cos (θ t))⁻¹ ^ 4 * Real.sin (θ t))) /
    (Real.exp t * (Real.cos t - Real.sin t))

def finalThird (t : ℝ) : ℝ :=
  Real.exp (-2 * t) * (2 * Real.sin t + Real.cos t) /
    (Real.sqrt 2 * Real.cos (θ t) ^ 5)

theorem gap8 (t : ℝ) (h : Real.cos (θ t) ≠ 0) :
    d3 t = rawThird t := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have htheta : HasDerivAt θ 1 t := by
    simpa [θ] using (hasDerivAt_id t).const_add (Real.pi / 4)
  have hnum :
      HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg using 1 <;> ring
  have hcos :
      HasDerivAt (fun s : ℝ => Real.cos (θ s))
        (-Real.sin (θ t)) t := by
    convert (Real.hasDerivAt_cos (θ t)).comp t htheta using 1 <;> ring
  have hpow :
      HasDerivAt (fun s : ℝ => Real.cos (θ s) ^ 3)
        (-3 * Real.cos (θ t) ^ 2 * Real.sin (θ t)) t := by
    convert hcos.pow 3 using 1 <;> ring
  have hden :
      HasDerivAt
        (fun s : ℝ => Real.sqrt 2 * Real.cos (θ s) ^ 3)
        (Real.sqrt 2 * (-3 * Real.cos (θ t) ^ 2 * Real.sin (θ t))) t := by
    exact hpow.const_mul (Real.sqrt 2)
  have hg :
      HasDerivAt
        (fun s : ℝ =>
          Real.exp (-s) / (Real.sqrt 2 * Real.cos (θ s) ^ 3))
        ((1 / Real.sqrt 2) * Real.exp (-t) *
          (-(Real.cos (θ t))⁻¹ ^ 3 +
            3 * (Real.cos (θ t))⁻¹ ^ 4 * Real.sin (θ t))) t := by
    convert hnum.div hden (mul_ne_zero hsqrt (pow_ne_zero 3 h)) using 1
    field_simp [h, hsqrt]
    ring
  have hev :
      d2 =ᶠ[nhds t]
        fun s : ℝ => Real.exp (-s) / (Real.sqrt 2 * Real.cos (θ s) ^ 3) :=
    (eventually_cos_theta_ne t h).mono (fun s hs => gap7 s hs)
  have hderiv :
      deriv d2 t =
        (1 / Real.sqrt 2) * Real.exp (-t) *
          (-(Real.cos (θ t))⁻¹ ^ 3 +
            3 * (Real.cos (θ t))⁻¹ ^ 4 * Real.sin (θ t)) := by
    calc
      deriv d2 t =
          deriv
            (fun s : ℝ =>
              Real.exp (-s) / (Real.sqrt 2 * Real.cos (θ s) ^ 3)) t :=
        hev.deriv_eq
      _ = _ := hg.deriv
  unfold d3 rawThird
  rw [hderiv, (hasDerivAt_x t).deriv]

theorem gap9 (t : ℝ) (h : Real.cos (θ t) ≠ 0) :
    rawThird t = finalThird t := by
  have hdiff := cos_sub_sin_ne_of_cos_theta_ne t h
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hexp : Real.exp (-2 * t) = Real.exp (-t) / Real.exp t := by
    rw [← Real.exp_sub]
    congr 1
    ring
  unfold rawThird finalThird
  rw [hexp, sin_theta_eq, cos_theta_eq]
  field_simp [h, hdiff, hsqrt, Real.exp_ne_zero]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem gap10 (t : ℝ) (h : Real.cos (θ t) ≠ 0) :
    d3 t = finalThird t := by
  calc
    d3 t = rawThird t := gap8 t h
    _ = finalThird t := gap9 t h

end

end ProofGap.Exercise1143
