import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3435

noncomputable section

def d1 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x

def d2 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x

def d3 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv (deriv f)) x

def logAbs (x : ℝ) : ℝ :=
  Real.log |x|

def secondTransform (Y : ℝ → ℝ) (x : ℝ) : ℝ :=
  (d2 Y (logAbs x) - d1 Y (logAbs x)) / x ^ 2

def thirdTransform (Y : ℝ → ℝ) (x : ℝ) : ℝ :=
  (d3 Y (logAbs x) - 3 * d2 Y (logAbs x) +
      2 * d1 Y (logAbs x)) / x ^ 3

private theorem hasDerivAt_logAbs {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt logAbs (1 / x) x := by
  have hfun : logAbs = Real.log := by
    funext z
    exact Real.log_abs z
  rw [hfun]
  simpa [one_div] using Real.hasDerivAt_log hx

private theorem second_deriv_eq_aux
    (u Y : ℝ → ℝ) (x : ℝ)
    (hx : x ≠ 0)
    (hCompose : ∀ x, x ≠ 0 → u x = Y (logAbs x))
    (hY : ContDiff ℝ 2 Y) :
    deriv (deriv u) x = secondTransform Y x := by
  have hYsucc : ContDiff ℝ (1 + 1) Y := by
    simpa using hY
  have hYreg := (contDiff_succ_iff_deriv (n := 1)).mp hYsucc
  have hYdiff : Differentiable ℝ Y := hYreg.1
  have hdY : ContDiff ℝ 1 (deriv Y) := hYreg.2.2
  have hdYdiff : Differentiable ℝ (deriv Y) :=
    hdY.differentiable (by decide)
  have hFirst :
      ∀ z, z ≠ 0 →
        deriv u z = deriv Y (logAbs z) / z := by
    intro z hz
    have hEq : u =ᶠ[nhds z] fun w => Y (logAbs w) := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact hCompose w hw
    have hLog := hasDerivAt_logAbs hz
    have hComp :
        HasDerivAt (fun w => Y (logAbs w))
          (deriv Y (logAbs z) * (1 / z)) z :=
      hYdiff.differentiableAt.hasDerivAt.comp z hLog
    calc
      deriv u z = deriv (fun w => Y (logAbs w)) z := hEq.deriv_eq
      _ = deriv Y (logAbs z) * (1 / z) := hComp.deriv
      _ = deriv Y (logAbs z) / z := by
        simp [div_eq_mul_inv]
  have hFirstNear :
      deriv u =ᶠ[nhds x]
        fun z => deriv Y (logAbs z) / z := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    exact hFirst z hz
  have hLog := hasDerivAt_logAbs hx
  have hA :
      HasDerivAt (fun z => deriv Y (logAbs z))
        (deriv (deriv Y) (logAbs x) * (1 / x)) x :=
    hdYdiff.differentiableAt.hasDerivAt.comp x hLog
  have hId : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
  have hQuot := hA.div hId hx
  calc
    deriv (deriv u) x =
        deriv (fun z => deriv Y (logAbs z) / z) x :=
      hFirstNear.deriv_eq
    _ = ((deriv (deriv Y) (logAbs x) * (1 / x)) * x -
          deriv Y (logAbs x)) / x ^ 2 := by
      simpa only [mul_one] using hQuot.deriv
    _ = secondTransform Y x := by
      unfold secondTransform d1 d2
      field_simp [hx] <;> ring

theorem gap1 (u Y : ℝ → ℝ) (x : ℝ)
    (hx : x ≠ 0)
    (hCompose : ∀ x, x ≠ 0 → u x = Y (logAbs x))
    (hY : ContDiff ℝ 1 Y)
    (hu : ContDiff ℝ 1 u) :
    d1 u x = d1 Y (logAbs x) * d1 logAbs x := by
  have hEq : u =ᶠ[nhds x] fun z => Y (logAbs z) := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    exact hCompose z hz
  have hYdiff : Differentiable ℝ Y := hY.differentiable (by decide)
  have hLog := hasDerivAt_logAbs hx
  have hComp :
      HasDerivAt (fun z => Y (logAbs z))
        (deriv Y (logAbs x) * (1 / x)) x :=
    hYdiff.differentiableAt.hasDerivAt.comp x hLog
  unfold d1
  rw [hEq.deriv_eq, hComp.deriv, hLog.deriv]

theorem gap2 (Y : ℝ → ℝ) (x : ℝ)
    (hx : x ≠ 0) :
    d1 Y (logAbs x) * d1 logAbs x =
      (1 / x) * d1 Y (logAbs x) := by
  have hLog := hasDerivAt_logAbs hx
  unfold d1
  rw [hLog.deriv]
  ring

theorem gap3 (u Y : ℝ → ℝ) (x : ℝ)
    (hChain : d1 u x = d1 Y (logAbs x) * d1 logAbs x)
    (hLog :
      d1 Y (logAbs x) * d1 logAbs x =
        (1 / x) * d1 Y (logAbs x)) :
    d1 u x = (1 / x) * d1 Y (logAbs x) := by
  exact hChain.trans hLog

theorem gap4 (u : ℝ → ℝ) :
    ∀ x, d2 u x = deriv (deriv u) x := by
  intro x
  rfl

theorem gap5 (u Y : ℝ → ℝ) (x : ℝ)
    (hx : x ≠ 0)
    (hCompose : ∀ x, x ≠ 0 → u x = Y (logAbs x))
    (hY : ContDiff ℝ 2 Y)
    (hu : ContDiff ℝ 2 u) :
    deriv (deriv u) x = secondTransform Y x := by
  exact second_deriv_eq_aux u Y x hx hCompose hY

theorem gap6 (u Y : ℝ → ℝ) (x : ℝ)
    (hSecondDef : d2 u x = deriv (deriv u) x)
    (hTransform : deriv (deriv u) x = secondTransform Y x) :
    d2 u x = secondTransform Y x := by
  exact hSecondDef.trans hTransform

theorem gap7 (u Y : ℝ → ℝ) (x : ℝ)
    (hx : x ≠ 0)
    (hCompose : ∀ x, x ≠ 0 → u x = Y (logAbs x))
    (hY : ContDiff ℝ 3 Y)
    (hu : ContDiff ℝ 3 u) :
    d3 u x = thirdTransform Y x := by
  have hY2 : ContDiff ℝ 2 Y := hY.of_le (by decide)
  have hYsucc : ContDiff ℝ (2 + 1) Y := by
    simpa using hY
  have hYreg := (contDiff_succ_iff_deriv (n := 2)).mp hYsucc
  have hdY : ContDiff ℝ 2 (deriv Y) := hYreg.2.2
  have hdYsucc : ContDiff ℝ (1 + 1) (deriv Y) := by
    simpa using hdY
  have hdYreg := (contDiff_succ_iff_deriv (n := 1)).mp hdYsucc
  have hddY : ContDiff ℝ 1 (deriv (deriv Y)) := hdYreg.2.2
  have hdYdiff : Differentiable ℝ (deriv Y) := hdYreg.1
  have hddYdiff : Differentiable ℝ (deriv (deriv Y)) :=
    hddY.differentiable (by decide)
  have hSecond :
      deriv (deriv u) =ᶠ[nhds x] secondTransform Y := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    exact second_deriv_eq_aux u Y z hz hCompose hY2
  have hLog := hasDerivAt_logAbs hx
  have hA :
      HasDerivAt (fun z => deriv Y (logAbs z))
        (deriv (deriv Y) (logAbs x) * (1 / x)) x :=
    hdYdiff.differentiableAt.hasDerivAt.comp x hLog
  have hB :
      HasDerivAt (fun z => deriv (deriv Y) (logAbs z))
        (deriv (deriv (deriv Y)) (logAbs x) * (1 / x)) x :=
    hddYdiff.differentiableAt.hasDerivAt.comp x hLog
  have hNum := hB.sub hA
  have hDen := (hasDerivAt_id x).pow 2
  have hQuot := hNum.div hDen (pow_ne_zero 2 hx)
  have hCalc :
      deriv
          (fun z =>
            (deriv (deriv Y) (logAbs z) - deriv Y (logAbs z)) /
              z ^ 2)
          x =
        ((deriv (deriv (deriv Y)) (logAbs x) * (1 / x) -
              deriv (deriv Y) (logAbs x) * (1 / x)) * x ^ 2 -
            (deriv (deriv Y) (logAbs x) - deriv Y (logAbs x)) *
              (2 * x)) /
          (x ^ 2) ^ 2 := by
    convert hQuot.deriv using 1 <;> norm_num <;> ring
  unfold d3
  rw [hSecond.deriv_eq]
  change
    deriv
        (fun z =>
          (deriv (deriv Y) (logAbs z) - deriv Y (logAbs z)) /
            z ^ 2)
        x = thirdTransform Y x
  rw [hCalc]
  unfold thirdTransform d1 d2 d3
  field_simp [hx] <;> ring

theorem gap8 (u Y : ℝ → ℝ)
    (hODE : ∀ x, x ≠ 0 → d3 u x = 6 * u x / x ^ 3)
    (hCompose : ∀ x, x ≠ 0 → u x = Y (logAbs x))
    (hThird : ∀ x, x ≠ 0 → d3 u x = thirdTransform Y x) :
    ∀ t,
      d3 Y t - 3 * d2 Y t + 2 * d1 Y t - 6 * Y t = 0 := by
  intro t
  have hx : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
  have h := hThird (Real.exp t) hx
  rw [hODE (Real.exp t) hx, hCompose (Real.exp t) hx] at h
  simp only [logAbs, abs_of_pos (Real.exp_pos t), Real.log_exp,
    thirdTransform] at h
  field_simp [hx] at h
  linarith

end

end ProofGap.Exercise3435
