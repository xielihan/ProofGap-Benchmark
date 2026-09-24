import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Pseudo.Real

namespace ProofGap.Exercise2848

noncomputable section

def extendedPower (x : ℝ) : ℝ :=
  if x = 0 then Real.exp 1 else Real.rpow (1 + x) (1 / x)

def inDomain (x : ℝ) : Prop :=
  -1 < x

def inPuncturedDomain (x : ℝ) : Prop :=
  inDomain x ∧ x ≠ 0

def firstLogDerivative (x : ℝ) : ℝ :=
  -(1 / x ^ 2) * Real.log (1 + x) + 1 / (x * (1 + x))

def logOnePlusTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (n + 1) / (n + 1)

def expandedFirstLogDerivative (x : ℝ) : ℝ :=
  -(1 / x ^ 2) * (∑' n, logOnePlusTerm x n) + 1 / x - 1 / (1 + x)

def secondLogDerivative (x : ℝ) : ℝ :=
  2 / x ^ 3 * Real.log (1 + x) - 1 / (x ^ 2 * (1 + x)) -
    1 / x ^ 2 + 1 / (1 + x) ^ 2

def thirdLogDerivative (x : ℝ) : ℝ :=
  -(6 / x ^ 4) * Real.log (1 + x) + 2 / (x ^ 3 * (1 + x)) +
    4 / x ^ 3 + 1 / (1 + x) ^ 2 - 1 / x ^ 2 - 2 / (1 + x) ^ 3

def FirstAsymptotic (f : ℝ → ℝ) : Prop :=
  ∃ r : ℝ → ℝ,
    r =o[nhdsWithin 0 ({0}ᶜ : Set ℝ)] (fun x : ℝ => x) ∧
      ∀ x, inPuncturedDomain x →
        deriv f x =
          extendedPower x * ((1 / 2 : ℝ) - x / 3 - 1 / (1 + x) + r x)

def SecondAsymptotic (f : ℝ → ℝ) : Prop :=
  ∃ r₁ r₂ : ℝ → ℝ,
    r₁ =o[nhdsWithin 0 ({0}ᶜ : Set ℝ)] (fun x : ℝ => x) ∧
    r₂ =o[nhdsWithin 0 ({0}ᶜ : Set ℝ)] (fun x : ℝ => x) ∧
      ∀ x, inPuncturedDomain x →
        deriv (deriv f) x =
          extendedPower x *
            (((1 / 2 : ℝ) - x / 3 - 1 / (1 + x) + r₁ x) ^ 2 +
              2 / 3 - x / 2 - 1 / (1 + x) + 1 / (1 + x) ^ 2 + r₂ x)

def IsMVTSelector (f : ℝ → ℝ) (ξ : ℝ → ℝ) : Prop :=
  ∀ x, inPuncturedDomain x →
    ξ x ∈ Set.uIcc 0 x ∧ (f x - f 0) / x = deriv f (ξ x)

def taylorAtZeroTerm (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (deriv^[n]) f 0 / (Nat.factorial n : ℝ) * x ^ n

private def logQuotientCoeffReal (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (n + 1)

private def logQuotientSeriesReal : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ logQuotientCoeffReal

private def logQuotientReal : ℝ → ℝ :=
  logQuotientSeriesReal.sum

private theorem logQuotientSeriesReal_radius :
    logQuotientSeriesReal.radius = 1 := by
  unfold logQuotientSeriesReal
  convert FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto
      ℝ logQuotientCoeffReal one_ne_zero _ using 1
  · norm_num
  have h :=
    (tendsto_natCast_div_add_atTop (1 : ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
  convert h using 1
  ext n
  simp only [logQuotientCoeffReal, norm_div, norm_pow, norm_neg, norm_one,
    one_pow]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n.succ : ℝ) + 1)]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, Nat.cast_succ]
  push_cast
  field_simp

private theorem logQuotientReal_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall logQuotientReal logQuotientSeriesReal 0 1 := by
  simpa only [logQuotientReal, logQuotientSeriesReal_radius] using
    logQuotientSeriesReal.hasFPowerSeriesOnBall
      (show 0 < logQuotientSeriesReal.radius by
        rw [logQuotientSeriesReal_radius]
        norm_num)

private theorem logQuotientReal_zero :
    logQuotientReal 0 = 1 := by
  change FormalMultilinearSeries.ofScalarsSum logQuotientCoeffReal 0 = 1
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  rw [tsum_eq_single 0]
  · norm_num [logQuotientCoeffReal]
  · intro n hn
    simp [logQuotientCoeffReal, hn]

private theorem logQuotientReal_analyticAt :
    AnalyticAt ℝ logQuotientReal 0 :=
  logQuotientReal_hasFPowerSeriesOnBall.analyticAt

private theorem logQuotientReal_iteratedDeriv_zero (n : ℕ) :
    (deriv^[n]) logQuotientReal 0 =
      (Nat.factorial n : ℝ) * logQuotientCoeffReal n := by
  rw [← iteratedDeriv_eq_iterate]
  have h :=
    logQuotientReal_hasFPowerSeriesOnBall.factorial_smul
      (y := (1 : ℝ)) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h
  simpa [logQuotientSeriesReal,
    FormalMultilinearSeries.ofScalars_apply_eq] using h.symm

private theorem logQuotientReal_deriv_zero :
    deriv logQuotientReal 0 = -(1 / 2 : ℝ) := by
  have h := logQuotientReal_iteratedDeriv_zero 1
  norm_num [logQuotientCoeffReal, Function.iterate_one] at h ⊢
  exact h

private theorem logQuotientReal_second_zero :
    deriv (deriv logQuotientReal) 0 = (2 / 3 : ℝ) := by
  have h := logQuotientReal_iteratedDeriv_zero 2
  norm_num [logQuotientCoeffReal, Function.iterate_succ_apply,
    Function.iterate_one] at h ⊢
  exact h

private theorem logQuotientReal_third_zero :
    deriv (deriv (deriv logQuotientReal)) 0 = -(3 / 2 : ℝ) := by
  have h := logQuotientReal_iteratedDeriv_zero 3
  norm_num [logQuotientCoeffReal, Function.iterate_succ_apply,
    Function.iterate_one, Nat.factorial] at h ⊢
  exact h

private theorem hasDerivAt_logQuotientReal_zero :
    HasDerivAt logQuotientReal (-(1 / 2 : ℝ)) 0 :=
  logQuotientReal_analyticAt.differentiableAt.hasDerivAt.congr_deriv
    logQuotientReal_deriv_zero

private theorem hasDerivAt_deriv_logQuotientReal_zero :
    HasDerivAt (deriv logQuotientReal) (2 / 3 : ℝ) 0 :=
  logQuotientReal_analyticAt.deriv.differentiableAt.hasDerivAt.congr_deriv
    logQuotientReal_second_zero

private theorem hasDerivAt_second_logQuotientReal_zero :
    HasDerivAt (deriv (deriv logQuotientReal)) (-(3 / 2 : ℝ)) 0 :=
  logQuotientReal_analyticAt.deriv.deriv.differentiableAt.hasDerivAt.congr_deriv
    logQuotientReal_third_zero

private theorem hasDerivAt_extendedPower_of_punctured
    (x : ℝ) (hx : inPuncturedDomain x) :
    HasDerivAt extendedPower
      (extendedPower x * firstLogDerivative x) x := by
  change -1 < x ∧ x ≠ 0 at hx
  have hplus : 1 + x ≠ 0 := by
    exact ne_of_gt (by linarith [hx.1])
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + y))
        (1 / (1 + x)) x := by
    convert ((hasDerivAt_id x).const_add 1).log hplus using 1 <;> ring
  have hinv :
      HasDerivAt (fun y : ℝ => 1 / y) (-(1 / x ^ 2)) x := by
    simpa only [one_div] using hasDerivAt_inv hx.2
  have hprod :
      HasDerivAt
        (fun y : ℝ => Real.log (1 + y) * (1 / y))
        (firstLogDerivative x) x := by
    convert hlog.mul hinv using 1
    · unfold firstLogDerivative
      field_simp [hx.2, hplus]
      ring
  have hexp :
      HasDerivAt
        (fun y : ℝ => Real.exp (Real.log (1 + y) * (1 / y)))
        (Real.exp (Real.log (1 + x) * (1 / x)) *
          firstLogDerivative x) x :=
    hprod.exp
  have heq :
      extendedPower =ᶠ[nhds x]
        (fun y : ℝ => Real.exp (Real.log (1 + y) * (1 / y))) := by
    filter_upwards [Ioi_mem_nhds hx.1,
      compl_singleton_mem_nhds hx.2] with y hydom hy0
    have hy0' : y ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy0
    change -1 < y at hydom
    unfold extendedPower
    rw [if_neg hy0']
    exact Real.rpow_def_of_pos (by linarith [hydom]) _
  have heqx :
      extendedPower x =
        Real.exp (Real.log (1 + x) * (1 / x)) :=
    heq.self_of_nhds
  convert hexp.congr_of_eventuallyEq heq using 1
  rw [heqx]

private theorem hasDerivAt_firstLogDerivative_of_punctured
    (x : ℝ) (hx : inPuncturedDomain x) :
    HasDerivAt firstLogDerivative (secondLogDerivative x) x := by
  change -1 < x ∧ x ≠ 0 at hx
  have hplus : 1 + x ≠ 0 := ne_of_gt (by linarith [hx.1])
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + y))
        (1 / (1 + x)) x := by
    convert ((hasDerivAt_id x).const_add 1).log hplus using 1 <;> ring
  have hinvpow :
      HasDerivAt (fun y : ℝ => 1 / y ^ 2)
        (-(2 * x) / (x ^ 2) ^ 2) x := by
    convert ((hasDerivAt_id x).pow 2).inv
      (pow_ne_zero 2 hx.2) using 1
    · funext y
      simp [id_eq, one_div]
    · simp [id_eq]
  have hterm1 :=
    hinvpow.neg.mul hlog
  have hprod :
      HasDerivAt (fun y : ℝ => y * (1 + y))
        (1 * (1 + x) + x * 1) x :=
    (hasDerivAt_id x).mul ((hasDerivAt_id x).const_add 1)
  have hterm2 :
      HasDerivAt (fun y : ℝ => 1 / (y * (1 + y)))
        (-(1 * (1 + x) + x * 1) / (x * (1 + x)) ^ 2) x := by
    simpa only [one_div] using hprod.inv (mul_ne_zero hx.2 hplus)
  have h := hterm1.add hterm2
  convert h using 1
  unfold secondLogDerivative
  simp only [Pi.neg_apply]
  field_simp [hx.2, hplus]
  ring

private theorem deriv_extendedPower_eventually_of_punctured
    (x : ℝ) (hx : inPuncturedDomain x) :
    deriv extendedPower =ᶠ[nhds x]
      (fun y => extendedPower y * firstLogDerivative y) := by
  change -1 < x ∧ x ≠ 0 at hx
  filter_upwards [Ioi_mem_nhds hx.1,
    compl_singleton_mem_nhds hx.2] with y hydom hy0
  have hy0' : y ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy0
  exact (hasDerivAt_extendedPower_of_punctured y
    ⟨hydom, hy0'⟩).deriv

private theorem hasDerivAt_deriv_extendedPower_of_punctured
    (x : ℝ) (hx : inPuncturedDomain x) :
    HasDerivAt (deriv extendedPower)
      (extendedPower x *
        (firstLogDerivative x ^ 2 + secondLogDerivative x)) x := by
  have h :=
    (hasDerivAt_extendedPower_of_punctured x hx).mul
      (hasDerivAt_firstLogDerivative_of_punctured x hx)
  apply h.congr_of_eventuallyEq
      (deriv_extendedPower_eventually_of_punctured x hx)
    |>.congr_deriv
  ring

private theorem hasDerivAt_secondLogDerivative_of_punctured
    (x : ℝ) (hx : inPuncturedDomain x) :
    HasDerivAt secondLogDerivative (thirdLogDerivative x) x := by
  change -1 < x ∧ x ≠ 0 at hx
  have hplus : 1 + x ≠ 0 := ne_of_gt (by linarith [hx.1])
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hplusD : HasDerivAt (fun y : ℝ => 1 + y) 1 x :=
    (hasDerivAt_id x).const_add 1
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + y))
        (1 / (1 + x)) x := by
    convert hplusD.log hplus using 1 <;> ring
  have hinv2 :
      HasDerivAt (fun y : ℝ => 1 / y ^ 2)
        (-(2 * x) / (x ^ 2) ^ 2) x := by
    convert ((hasDerivAt_id x).pow 2).inv
      (pow_ne_zero 2 hx.2) using 1
    · funext y
      simp [id_eq, one_div]
    · simp [id_eq]
  have hinv3 :
      HasDerivAt (fun y : ℝ => 1 / y ^ 3)
        (-(3 * x ^ 2) / (x ^ 3) ^ 2) x := by
    convert ((hasDerivAt_id x).pow 3).inv
      (pow_ne_zero 3 hx.2) using 1
    · funext y
      simp [id_eq, one_div]
    · simp [id_eq]
  have hdenom :
      HasDerivAt (fun y : ℝ => y ^ 2 * (1 + y))
        (2 * x * (1 + x) + x ^ 2) x := by
    convert ((hasDerivAt_id x).pow 2).mul hplusD using 1 <;>
      simp [id_eq] <;> ring
  have hinvdenom :
      HasDerivAt (fun y : ℝ => 1 / (y ^ 2 * (1 + y)))
        (-(2 * x * (1 + x) + x ^ 2) /
          (x ^ 2 * (1 + x)) ^ 2) x := by
    simpa only [one_div] using
      hdenom.inv (mul_ne_zero (pow_ne_zero 2 hx.2) hplus)
  have hpluspow :
      HasDerivAt (fun y : ℝ => (1 + y) ^ 2)
        (2 * (1 + x)) x := by
    convert hplusD.pow 2 using 1 <;> ring
  have hinvpluspow :
      HasDerivAt (fun y : ℝ => 1 / (1 + y) ^ 2)
        (-(2 * (1 + x)) / ((1 + x) ^ 2) ^ 2) x := by
    simpa only [one_div] using
      hpluspow.inv (pow_ne_zero 2 hplus)
  have h :=
    ((((hinv3.const_mul 2).mul hlog).sub hinvdenom).sub hinv2).add
      hinvpluspow
  convert h using 1
  · funext y
    unfold secondLogDerivative
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  · unfold thirdLogDerivative
    field_simp [hx.2, hplus]
    ring

private theorem second_deriv_extendedPower_eventually_of_punctured
    (x : ℝ) (hx : inPuncturedDomain x) :
    deriv (deriv extendedPower) =ᶠ[nhds x]
      (fun y => extendedPower y *
        (firstLogDerivative y ^ 2 + secondLogDerivative y)) := by
  change -1 < x ∧ x ≠ 0 at hx
  filter_upwards [Ioi_mem_nhds hx.1,
    compl_singleton_mem_nhds hx.2] with y hydom hy0
  have hy0' : y ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy0
  exact (hasDerivAt_deriv_extendedPower_of_punctured y
    ⟨hydom, hy0'⟩).deriv

private theorem hasDerivAt_second_deriv_extendedPower_of_punctured
    (x : ℝ) (hx : inPuncturedDomain x) :
    HasDerivAt (deriv (deriv extendedPower))
      (extendedPower x *
        (firstLogDerivative x ^ 3 +
          3 * firstLogDerivative x * secondLogDerivative x +
          thirdLogDerivative x)) x := by
  have hext := hasDerivAt_extendedPower_of_punctured x hx
  have hfirst := hasDerivAt_firstLogDerivative_of_punctured x hx
  have hsecond := hasDerivAt_secondLogDerivative_of_punctured x hx
  have hinside :
      HasDerivAt
        (fun y => firstLogDerivative y ^ 2 + secondLogDerivative y)
        (2 * firstLogDerivative x * secondLogDerivative x +
          thirdLogDerivative x) x := by
    convert (hfirst.mul hfirst).add hsecond using 1
    · funext y
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
      ring
    · ring
  have h := hext.mul hinside
  apply h.congr_of_eventuallyEq
    (second_deriv_extendedPower_eventually_of_punctured x hx)
    |>.congr_deriv
  ring

private theorem hasSum_logOnePlusTerm (x : ℝ) (hx : |x| < 1) :
    HasSum (logOnePlusTerm x) (Real.log (1 + x)) := by
  have hs :=
    (Real.hasSum_pow_div_log_of_abs_lt_one
      (x := -x) (by simpa only [abs_neg] using hx)).neg
  have hs' :
      HasSum (logOnePlusTerm x) (- -Real.log (1 - -x)) := by
    apply hs.congr_fun
    intro n
    unfold logOnePlusTerm
    push_cast
    rw [neg_pow]
    ring
  convert hs' using 1
  ring

private theorem logQuotientReal_eq_log_div
    (x : ℝ) (hx : |x| < 1) (hx0 : x ≠ 0) :
    logQuotientReal x = Real.log (1 + x) / x := by
  have hs := (hasSum_logOnePlusTerm x hx).div_const x
  have hs' :
      HasSum (fun n : ℕ => logQuotientCoeffReal n * x ^ n)
        (Real.log (1 + x) / x) := by
    apply hs.congr_fun
    intro n
    unfold logOnePlusTerm logQuotientCoeffReal
    push_cast
    field_simp [hx0]
    ring
  change FormalMultilinearSeries.ofScalarsSum logQuotientCoeffReal x =
    Real.log (1 + x) / x
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using hs'.tsum_eq

private theorem analyticAt_logQuotientReal_of_abs_lt_one
    (x : ℝ) (hx : |x| < 1) :
    AnalyticAt ℝ logQuotientReal x := by
  change AnalyticAt ℝ logQuotientSeriesReal.sum x
  apply logQuotientSeriesReal.analyticOnNhd x
  rw [logQuotientSeriesReal_radius]
  simpa [Metric.mem_eball, edist_dist, Real.dist_eq] using hx

private theorem differentiableAt_logQuotientReal_of_abs_lt_one
    (x : ℝ) (hx : |x| < 1) :
    DifferentiableAt ℝ logQuotientReal x :=
  (analyticAt_logQuotientReal_of_abs_lt_one x hx).differentiableAt

private def analyticExtendedPowerReal (x : ℝ) : ℝ :=
  Real.exp (logQuotientReal x)

private theorem extendedPower_eq_analyticExtendedPowerReal
    (x : ℝ) (hx : |x| < 1) :
    extendedPower x = analyticExtendedPowerReal x := by
  by_cases hx0 : x = 0
  · subst x
    simp [extendedPower, analyticExtendedPowerReal, logQuotientReal_zero]
  · unfold extendedPower analyticExtendedPowerReal
    rw [if_neg hx0, logQuotientReal_eq_log_div x hx hx0]
    convert Real.rpow_def_of_pos (x := 1 + x)
      (by linarith [(abs_lt.mp hx).1]) (1 / x) using 1 <;> ring

private theorem deriv_logQuotientReal_eq_firstLogDerivative
    (x : ℝ) (hx : |x| < 1) (hx0 : x ≠ 0) :
    deriv logQuotientReal x = firstLogDerivative x := by
  have hplus : 1 + x ≠ 0 := by
    exact ne_of_gt (by linarith [(abs_lt.mp hx).1])
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + y))
        (1 / (1 + x)) x := by
    convert ((hasDerivAt_id x).const_add 1).log hplus using 1 <;> ring
  have hdiv :
      HasDerivAt (fun y : ℝ => Real.log (1 + y) / y)
        (firstLogDerivative x) x := by
    convert hlog.div (hasDerivAt_id x) hx0 using 1
    unfold firstLogDerivative
    simp only [id_eq]
    field_simp [hx0, hplus]
    ring
  have heq :
      logQuotientReal =ᶠ[nhds x]
        (fun y : ℝ => Real.log (1 + y) / y) := by
    filter_upwards [
      (isOpen_lt continuous_abs continuous_const).mem_nhds hx,
      compl_singleton_mem_nhds hx0] with y hy hy0
    apply logQuotientReal_eq_log_div y hy
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy0
  exact (hdiv.congr_of_eventuallyEq heq).deriv

private theorem second_deriv_logQuotientReal_eq_secondLogDerivative
    (x : ℝ) (hx : |x| < 1) (hx0 : x ≠ 0) :
    deriv (deriv logQuotientReal) x = secondLogDerivative x := by
  have heq :
      deriv logQuotientReal =ᶠ[nhds x] firstLogDerivative := by
    filter_upwards [
      (isOpen_lt continuous_abs continuous_const).mem_nhds hx,
      compl_singleton_mem_nhds hx0] with y hy hy0
    apply deriv_logQuotientReal_eq_firstLogDerivative y hy
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy0
  exact ((hasDerivAt_firstLogDerivative_of_punctured x
    ⟨(abs_lt.mp hx).1, hx0⟩).congr_of_eventuallyEq heq).deriv

private theorem extendedPower_eventuallyEq_analyticExtendedPowerReal :
    extendedPower =ᶠ[nhds 0] analyticExtendedPowerReal := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
    (show (0 : ℝ) < 1 by norm_num)] with x hx
  apply extendedPower_eq_analyticExtendedPowerReal x
  simpa [Metric.mem_ball, Real.dist_eq] using hx

private theorem hasDerivAt_analyticExtendedPowerReal_zero :
    HasDerivAt analyticExtendedPowerReal (-(Real.exp 1) / 2) 0 := by
  have h := hasDerivAt_logQuotientReal_zero.exp
  convert h using 1 <;>
    simp [analyticExtendedPowerReal, logQuotientReal_zero] <;> ring

private theorem hasDerivAt_extendedPower_zero :
    HasDerivAt extendedPower (-(Real.exp 1) / 2) 0 :=
  hasDerivAt_analyticExtendedPowerReal_zero.congr_of_eventuallyEq
    extendedPower_eventuallyEq_analyticExtendedPowerReal

private def analyticFirstDerivativeReal (x : ℝ) : ℝ :=
  analyticExtendedPowerReal x * deriv logQuotientReal x

private theorem deriv_analyticExtendedPowerReal_eventually :
    deriv analyticExtendedPowerReal =ᶠ[nhds 0] analyticFirstDerivativeReal := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
    (show (0 : ℝ) < 1 by norm_num)] with x hx
  have hx' : |x| < 1 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  have hq :
      HasDerivAt logQuotientReal (deriv logQuotientReal x) x :=
    (differentiableAt_logQuotientReal_of_abs_lt_one x hx').hasDerivAt
  simpa only [analyticExtendedPowerReal, analyticFirstDerivativeReal] using
    hq.exp.deriv

private theorem hasDerivAt_analyticFirstDerivativeReal_zero :
    HasDerivAt analyticFirstDerivativeReal
      ((11 / 12 : ℝ) * Real.exp 1) 0 := by
  have h :=
    hasDerivAt_analyticExtendedPowerReal_zero.mul
      hasDerivAt_deriv_logQuotientReal_zero
  convert h using 1 <;>
    simp [analyticFirstDerivativeReal, analyticExtendedPowerReal,
      logQuotientReal_zero, logQuotientReal_deriv_zero] <;> ring

private theorem hasDerivAt_deriv_analyticExtendedPowerReal_zero :
    HasDerivAt (deriv analyticExtendedPowerReal)
      ((11 / 12 : ℝ) * Real.exp 1) 0 :=
  hasDerivAt_analyticFirstDerivativeReal_zero.congr_of_eventuallyEq
    deriv_analyticExtendedPowerReal_eventually

private theorem hasDerivAt_deriv_extendedPower_zero :
    HasDerivAt (deriv extendedPower)
      ((11 / 12 : ℝ) * Real.exp 1) 0 := by
  apply hasDerivAt_deriv_analyticExtendedPowerReal_zero.congr_of_eventuallyEq
  exact extendedPower_eventuallyEq_analyticExtendedPowerReal.deriv

private def analyticSecondDerivativeReal (x : ℝ) : ℝ :=
  analyticExtendedPowerReal x *
    (deriv logQuotientReal x ^ 2 +
      deriv (deriv logQuotientReal) x)

private theorem deriv_analyticFirstDerivativeReal_eventually :
    deriv analyticFirstDerivativeReal =ᶠ[nhds 0]
      analyticSecondDerivativeReal := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
    (show (0 : ℝ) < 1 by norm_num)] with x hx
  have hx' : |x| < 1 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  have hqAnalytic := analyticAt_logQuotientReal_of_abs_lt_one x hx'
  have hq :
      HasDerivAt logQuotientReal (deriv logQuotientReal x) x :=
    hqAnalytic.differentiableAt.hasDerivAt
  have hq' :
      HasDerivAt (deriv logQuotientReal)
        (deriv (deriv logQuotientReal) x) x :=
    hqAnalytic.deriv.differentiableAt.hasDerivAt
  have h :=
    (show HasDerivAt analyticExtendedPowerReal
        (analyticExtendedPowerReal x * deriv logQuotientReal x) x by
      simpa only [analyticExtendedPowerReal] using hq.exp).mul hq'
  convert h.deriv using 1 <;>
    simp [analyticFirstDerivativeReal, analyticSecondDerivativeReal] <;> ring

private theorem hasDerivAt_analyticSecondDerivativeReal_zero :
    HasDerivAt analyticSecondDerivativeReal
      (-(21 / 8 : ℝ) * Real.exp 1) 0 := by
  have hinner :=
    (hasDerivAt_deriv_logQuotientReal_zero.mul
      hasDerivAt_deriv_logQuotientReal_zero).add
        hasDerivAt_second_logQuotientReal_zero
  have h := hasDerivAt_analyticExtendedPowerReal_zero.mul hinner
  convert h using 1
  · funext x
    change analyticExtendedPowerReal x *
        (deriv logQuotientReal x ^ 2 +
          deriv (deriv logQuotientReal) x) =
      analyticExtendedPowerReal x *
        (deriv logQuotientReal x * deriv logQuotientReal x +
          deriv (deriv logQuotientReal) x)
    ring
  · simp [analyticExtendedPowerReal, logQuotientReal_zero,
      logQuotientReal_deriv_zero, logQuotientReal_second_zero]
    ring

private theorem hasDerivAt_second_analyticExtendedPowerReal_zero :
    HasDerivAt (deriv (deriv analyticExtendedPowerReal))
      (-(21 / 8 : ℝ) * Real.exp 1) 0 := by
  apply hasDerivAt_analyticSecondDerivativeReal_zero.congr_of_eventuallyEq
  exact deriv_analyticExtendedPowerReal_eventually.deriv.trans
    deriv_analyticFirstDerivativeReal_eventually

private theorem hasDerivAt_second_extendedPower_zero :
    HasDerivAt (deriv (deriv extendedPower))
      (-(21 / 8 : ℝ) * Real.exp 1) 0 := by
  apply hasDerivAt_second_analyticExtendedPowerReal_zero.congr_of_eventuallyEq
  exact extendedPower_eventuallyEq_analyticExtendedPowerReal.deriv.deriv

private theorem continuousAt_extendedPower_zero :
    ContinuousAt extendedPower 0 := by
  have hratio :
      Tendsto (fun x : ℝ => Real.log (1 + x) / x)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) := by
    have hslope :=
      (Real.hasDerivAt_log (x := (1 : ℝ)) one_ne_zero).tendsto_slope_zero
    simpa [Real.log_one, div_eq_mul_inv, mul_comm] using hslope
  have hexp :
      Tendsto
        (fun x : ℝ => Real.exp (Real.log (1 + x) / x))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (Real.exp 1)) :=
    (Real.continuous_exp.tendsto 1).comp hratio
  rw [continuousAt_iff_punctured_nhds]
  simpa only [extendedPower, if_pos, one_div] using
    hexp.congr' (by
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num))]
          with x hx0 hxdom
      have hx0' : x ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx0
      change -1 < x at hxdom
      unfold extendedPower
      rw [if_neg hx0']
      convert (Real.rpow_def_of_pos (x := 1 + x)
        (by linarith [hxdom]) (1 / x)).symm using 1 <;> ring)

private theorem hasDerivAt_firstAsymptoticBase_zero :
    HasDerivAt
      (fun x : ℝ => (1 / 2 : ℝ) - x / 3 - 1 / (1 + x))
      (2 / 3 : ℝ) 0 := by
  have hconst :
      HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 0 :=
    hasDerivAt_const 0 _
  have hlinear :
      HasDerivAt (fun x : ℝ => x / 3) (1 / 3 : ℝ) 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).div_const 3
  have hinv :
      HasDerivAt (fun x : ℝ => 1 / (1 + x)) (-1 : ℝ) 0 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) 0).const_add 1).inv
      (by norm_num) using 1
    · funext x
      simp [id_eq, one_div]
    · norm_num
  convert (hconst.sub hlinear).sub hinv using 1 <;> norm_num

private theorem hasDerivAt_secondAsymptoticBase_zero :
    HasDerivAt
      (fun x : ℝ =>
        (2 / 3 : ℝ) - x / 2 - 1 / (1 + x) + 1 / (1 + x) ^ 2)
      (-(3 / 2 : ℝ)) 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => (2 / 3 : ℝ)) 0 0 :=
    hasDerivAt_const 0 _
  have hlinear : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).div_const 2
  have hplus : HasDerivAt (fun x : ℝ => 1 + x) 1 0 :=
    (hasDerivAt_id (𝕜 := ℝ) 0).const_add 1
  have hinv : HasDerivAt (fun x : ℝ => 1 / (1 + x)) (-1 : ℝ) 0 := by
    convert hplus.inv (by norm_num) using 1
    · funext x
      simp [id_eq, one_div]
    · norm_num
  have hinvpow :
      HasDerivAt (fun x : ℝ => 1 / (1 + x) ^ 2) (-2 : ℝ) 0 := by
    convert (hplus.pow 2).inv (by norm_num) using 1
    · funext x
      simp [id_eq, one_div]
    · norm_num
  convert ((hconst.sub hlinear).sub hinv).add hinvpow using 1 <;>
    norm_num

private def logQuotientCoeffComplex (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n / (n + 1)

private def logQuotientSeriesComplex : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ logQuotientCoeffComplex

private def logQuotientComplex : ℂ → ℂ :=
  logQuotientSeriesComplex.sum

private def analyticExtendedPowerComplex (z : ℂ) : ℂ :=
  Complex.exp (logQuotientComplex z)

private theorem logQuotientSeriesComplex_radius :
    logQuotientSeriesComplex.radius = 1 := by
  unfold logQuotientSeriesComplex
  convert FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto
      ℂ logQuotientCoeffComplex one_ne_zero _ using 1
  · norm_num
  have h :=
    (tendsto_natCast_div_add_atTop (1 : ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
  convert h using 1
  ext n
  simp only [logQuotientCoeffComplex, norm_div, norm_pow, norm_neg, norm_one,
    one_pow]
  have hn : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by norm_num
  have hsucc :
      ((n.succ : ℂ) + 1) = ((n.succ + 1 : ℕ) : ℂ) := by norm_num
  rw [hn, hsucc, Complex.norm_natCast, Complex.norm_natCast]
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, Nat.cast_succ]
  push_cast
  field_simp

private theorem logQuotientComplex_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall logQuotientComplex logQuotientSeriesComplex 0 1 := by
  simpa only [logQuotientComplex, logQuotientSeriesComplex_radius] using
    logQuotientSeriesComplex.hasFPowerSeriesOnBall
      (show 0 < logQuotientSeriesComplex.radius by
        rw [logQuotientSeriesComplex_radius]
        norm_num)

private theorem logQuotientComplex_ofReal (y : ℝ) (hy : |y| < 1) :
    logQuotientComplex (y : ℂ) = (logQuotientReal y : ℂ) := by
  have hyReal : y ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [Metric.mem_eball, edist_dist, Real.dist_eq] using hy
  have hyComplex : (y : ℂ) ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [Metric.mem_eball, edist_dist] using hy
  have hr := logQuotientReal_hasFPowerSeriesOnBall.hasSum hyReal
  have hc := logQuotientComplex_hasFPowerSeriesOnBall.hasSum hyComplex
  simp only [zero_add] at hr hc
  have hrComplex :
      HasSum
        (fun n =>
          ((logQuotientSeriesReal n (fun _ : Fin n => y) : ℝ) : ℂ))
        (logQuotientReal y : ℂ) :=
    Complex.hasSum_ofReal.mpr hr
  have hrComplex' :
      HasSum
        (fun n => logQuotientSeriesComplex n (fun _ : Fin n => (y : ℂ)))
        (logQuotientReal y : ℂ) := by
    apply hrComplex.congr
    intro n
    simp [logQuotientSeriesReal, logQuotientSeriesComplex,
      logQuotientCoeffReal, logQuotientCoeffComplex,
      FormalMultilinearSeries.ofScalars_apply_eq]
  exact hc.unique hrComplex'

private theorem analyticExtendedPowerComplex_differentiableOn_closedBall
    (R : NNReal) (hR : (R : ℝ) < 1) :
    DifferentiableOn ℂ analyticExtendedPowerComplex
      (Metric.closedBall 0 R) := by
  intro z hz
  have hzlt : dist z 0 < 1 := by
    exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall] using hz) hR
  have hznorm : ‖z‖ < 1 := by
    simpa [dist_eq_norm] using hzlt
  have hzNN : ‖z‖₊ < (1 : NNReal) := by
    rw [← NNReal.coe_lt_coe]
    simpa using hznorm
  have hzENN :
      (‖z‖₊ : ENNReal) < ((1 : NNReal) : ENNReal) :=
    ENNReal.coe_lt_coe.mpr hzNN
  have hzball : z ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm] using hzENN
  have hq : DifferentiableAt ℂ logQuotientComplex z :=
    (logQuotientComplex_hasFPowerSeriesOnBall.analyticAt_of_mem hzball)
      |>.differentiableAt
  exact
    ((Complex.hasDerivAt_exp (logQuotientComplex z)).comp z hq.hasDerivAt)
      |>.differentiableAt.differentiableWithinAt

private theorem analyticExtendedPowerComplex_re_ofReal
    (y : ℝ) (hy : |y| < 1) :
    (analyticExtendedPowerComplex (y : ℂ)).re = extendedPower y := by
  rw [show analyticExtendedPowerComplex (y : ℂ) =
      Complex.exp (logQuotientComplex (y : ℂ)) by rfl]
  rw [logQuotientComplex_ofReal y hy]
  rw [Complex.exp_ofReal_re]
  exact (extendedPower_eq_analyticExtendedPowerReal y hy).symm

set_option backward.isDefEq.respectTransparency false in
private theorem extendedPower_hasFPowerSeriesOnBall_of_lt_one
    (R : NNReal) (hR0 : 0 < R) (hR1 : (R : ℝ) < 1) :
    ∃ p : FormalMultilinearSeries ℝ ℝ ℝ,
      HasFPowerSeriesOnBall extendedPower p 0 R := by
  letI : IsScalarTower ℂ ℂ ℂ := IsScalarTower.left ℂ
  letI : IsScalarTower ℝ ℂ ℂ := IsScalarTower.complexToReal
  have hc :=
    (analyticExtendedPowerComplex_differentiableOn_closedBall R hR1)
      |>.hasFPowerSeriesOnBall hR0
  have hcRealScalars := hc.restrictScalars (𝕜 := ℝ)
  have hcRealInput :=
    hcRealScalars.compContinuousLinearMap
      (u := Complex.ofRealCLM) (x := (0 : ℝ))
  simp only [Complex.ofRealCLM_enorm, div_one, map_zero] at hcRealInput
  have hcRealOutput :=
    Complex.reCLM.comp_hasFPowerSeriesOnBall hcRealInput
  refine ⟨_, hcRealOutput.congr ?_⟩
  intro y hy
  change (analyticExtendedPowerComplex (y : ℂ)).re = extendedPower y
  apply analyticExtendedPowerComplex_re_ofReal y
  have hyR : |y| < (R : ℝ) := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm] using hy
  exact hyR.trans hR1

theorem gap1
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1) :
    ∀ x, inPuncturedDomain x →
      deriv f x = extendedPower x * firstLogDerivative x := by
  intro x hx
  rw [show f = extendedPower from funext hf]
  exact (hasDerivAt_extendedPower_of_punctured x hx).deriv

theorem gap2
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hfirst :
      ∀ x, inPuncturedDomain x →
        deriv f x = extendedPower x * firstLogDerivative x) :
    ∀ x, |x| < 1 → x ≠ 0 →
      extendedPower x * firstLogDerivative x =
        extendedPower x * expandedFirstLogDerivative x := by
  intro x hx hx0
  congr 1
  unfold firstLogDerivative expandedFirstLogDerivative
  rw [(hasSum_logOnePlusTerm x hx).tsum_eq]
  have hplus : 1 + x ≠ 0 := by
    exact ne_of_gt (by linarith [(abs_lt.mp hx).1])
  field_simp [hx0, hplus]
  ring

theorem gap3
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hfirst :
      ∀ x, inPuncturedDomain x →
        deriv f x = extendedPower x * firstLogDerivative x)
    (hexpand :
      ∀ x, |x| < 1 → x ≠ 0 →
        extendedPower x * firstLogDerivative x =
          extendedPower x * expandedFirstLogDerivative x) :
    ∀ x, |x| < 1 → x ≠ 0 →
      deriv f x = extendedPower x * expandedFirstLogDerivative x := by
  intro x hx hx0
  exact (hfirst x ⟨(abs_lt.mp hx).1, hx0⟩).trans
    (hexpand x hx hx0)

theorem gap4
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hfirst :
      ∀ x, inPuncturedDomain x →
        deriv f x = extendedPower x * firstLogDerivative x)
    (hexpand :
      ∀ x, |x| < 1 → x ≠ 0 →
        extendedPower x * firstLogDerivative x =
          extendedPower x * expandedFirstLogDerivative x)
    (hfirstSeries :
      ∀ x, |x| < 1 → x ≠ 0 →
        deriv f x = extendedPower x * expandedFirstLogDerivative x) :
    FirstAsymptotic f := by
  let base : ℝ → ℝ :=
    fun x => (1 / 2 : ℝ) - x / 3 - 1 / (1 + x)
  let analyticRemainder : ℝ → ℝ :=
    fun x => deriv logQuotientReal x - base x
  let r : ℝ → ℝ :=
    fun x => firstLogDerivative x - base x
  have hrem :
      HasDerivAt analyticRemainder 0 0 := by
    dsimp only [analyticRemainder, base]
    convert hasDerivAt_deriv_logQuotientReal_zero.sub
      hasDerivAt_firstAsymptoticBase_zero using 1 <;>
      simp [logQuotientReal_deriv_zero]
  have hrem0 : analyticRemainder 0 = 0 := by
    dsimp only [analyticRemainder, base]
    rw [logQuotientReal_deriv_zero]
    norm_num
  have hsmall :
      analyticRemainder =o[nhds 0] (fun x : ℝ => x) := by
    simpa only [hrem0, sub_zero, smul_zero] using hrem.isLittleO
  have heq :
      analyticRemainder =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)] r := by
    filter_upwards [
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Metric.ball_mem_nhds (0 : ℝ)
          (show (0 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with x hxball hx0
    have hxabs : |x| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hxball
    have hxne : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx0
    dsimp only [analyticRemainder, r]
    rw [deriv_logQuotientReal_eq_firstLogDerivative x hxabs hxne]
  refine ⟨r,
    (hsmall.mono nhdsWithin_le_nhds).congr' heq
      (Filter.Eventually.of_forall fun _ => rfl), ?_⟩
  intro x hx
  rw [hfirst x hx]
  congr 1
  dsimp only [r, base]
  ring

theorem gap5
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hfirst :
      ∀ x, inPuncturedDomain x →
        deriv f x = extendedPower x * firstLogDerivative x)
    (hexpand :
      ∀ x, |x| < 1 → x ≠ 0 →
        extendedPower x * firstLogDerivative x =
          extendedPower x * expandedFirstLogDerivative x)
    (hfirstSeries :
      ∀ x, |x| < 1 → x ≠ 0 →
        deriv f x = extendedPower x * expandedFirstLogDerivative x)
    (hasymptotic : FirstAsymptotic f) :
    ∃ ξ : ℝ → ℝ, IsMVTSelector f ξ := by
  classical
  have hfeq : f = extendedPower := funext hf
  subst f
  have hexists :
      ∀ x, inPuncturedDomain x →
        ∃ c, c ∈ Set.uIcc 0 x ∧
          (extendedPower x - extendedPower 0) / x =
            deriv extendedPower c := by
    intro x hx
    change -1 < x ∧ x ≠ 0 at hx
    rcases lt_or_gt_of_ne hx.2 with hxneg | hxpos
    · have hcont :
          ContinuousOn extendedPower (Set.Icc x 0) := by
        intro y hy
        by_cases hy0 : y = 0
        · subst y
          exact continuousAt_extendedPower_zero.continuousWithinAt
        · exact
            (hasDerivAt_extendedPower_of_punctured y
              ⟨lt_of_lt_of_le hx.1 hy.1, hy0⟩).continuousAt.continuousWithinAt
      have hdiff :
          DifferentiableOn ℝ extendedPower (Set.Ioo x 0) := by
        intro y hy
        exact
          (hasDerivAt_extendedPower_of_punctured y
            ⟨lt_of_lt_of_le hx.1 hy.1.le, ne_of_lt hy.2⟩).differentiableAt
              |>.differentiableWithinAt
      obtain ⟨c, hc, hder⟩ :=
        exists_deriv_eq_slope extendedPower hxneg hcont hdiff
      refine ⟨c, ?_, ?_⟩
      · rw [Set.uIcc_comm, Set.uIcc_of_le hxneg.le]
        exact ⟨hc.1.le, hc.2.le⟩
      · rw [hder]
        field_simp [hx.2]
        ring
    · have hcont :
          ContinuousOn extendedPower (Set.Icc 0 x) := by
        intro y hy
        by_cases hy0 : y = 0
        · subst y
          exact continuousAt_extendedPower_zero.continuousWithinAt
        · have hydom : inPuncturedDomain y := by
            constructor
            · change -1 < y
              linarith [hy.1]
            · exact hy0
          exact
            (hasDerivAt_extendedPower_of_punctured y hydom).continuousAt
              |>.continuousWithinAt
      have hdiff :
          DifferentiableOn ℝ extendedPower (Set.Ioo 0 x) := by
        intro y hy
        have hydom : inPuncturedDomain y := by
          constructor
          · change -1 < y
            linarith [hy.1]
          · exact ne_of_gt hy.1
        exact
          (hasDerivAt_extendedPower_of_punctured y hydom).differentiableAt
              |>.differentiableWithinAt
      obtain ⟨c, hc, hder⟩ :=
        exists_deriv_eq_slope extendedPower hxpos hcont hdiff
      refine ⟨c, ?_, ?_⟩
      · rw [Set.uIcc_of_le hxpos.le]
        exact ⟨hc.1.le, hc.2.le⟩
      · simpa using hder.symm
  let θ : ℝ → ℝ := fun x =>
    if hx : inPuncturedDomain x then
      Classical.choose (hexists x hx)
    else 0
  refine ⟨θ, ?_⟩
  intro x hx
  dsimp only [θ]
  rw [dif_pos hx]
  exact Classical.choose_spec (hexists x hx)

theorem gap6
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hmvt : ∃ ξ : ℝ → ℝ, IsMVTSelector f ξ) :
    Tendsto (fun x => (f x - f 0) / x) (nhdsWithin 0 ({0}ᶜ : Set ℝ))
      (nhds (deriv f 0)) := by
  have hfeq : f = extendedPower := funext hf
  subst f
  rw [hasDerivAt_extendedPower_zero.deriv]
  simpa [div_eq_mul_inv, mul_comm] using
    hasDerivAt_extendedPower_zero.tendsto_slope_zero

theorem gap7
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hmvt : ∃ ξ : ℝ → ℝ, IsMVTSelector f ξ)
    (hquotient :
      Tendsto (fun x => (f x - f 0) / x) (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds (deriv f 0))) :
    ∃ ξ : ℝ → ℝ, IsMVTSelector f ξ ∧
      Tendsto (fun x => deriv f (ξ x)) (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds (deriv f 0)) := by
  obtain ⟨θ, hθ⟩ := hmvt
  refine ⟨θ, hθ, ?_⟩
  apply hquotient.congr'
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num))]
      with x hx0 hxdom
  exact (hθ x ⟨hxdom, by simpa only [Set.mem_compl_iff,
    Set.mem_singleton_iff] using hx0⟩).2

theorem gap8
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hselector :
      ∃ ξ : ℝ → ℝ, IsMVTSelector f ξ ∧
        Tendsto (fun x => deriv f (ξ x)) (nhdsWithin 0 ({0}ᶜ : Set ℝ))
          (nhds (deriv f 0))) :
    ∃ ξ : ℝ → ℝ, IsMVTSelector f ξ ∧
      Tendsto ξ (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) := by
  obtain ⟨θ, hθ, hderiv⟩ := hselector
  refine ⟨θ, hθ, ?_⟩
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)),
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Metric.ball_mem_nhds 0 hε)]
      with x hx0 hxdom hxε
  have hmem := hθ x ⟨hxdom, by simpa only [Set.mem_compl_iff,
    Set.mem_singleton_iff] using hx0⟩
  have hdist : dist (θ x) 0 ≤ dist x 0 := by
    simpa only [dist_comm] using Real.dist_left_le_of_mem_uIcc hmem.1
  exact lt_of_le_of_lt hdist (by simpa [Metric.mem_ball] using hxε)

theorem gap9
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hselector :
      ∃ ξ : ℝ → ℝ, IsMVTSelector f ξ ∧
        Tendsto ξ (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0)) :
    Tendsto (deriv f) (nhdsWithin 0 ({0}ᶜ : Set ℝ))
      (nhds (-(Real.exp 1) / 2)) := by
  have hfeq : f = extendedPower := funext hf
  subst f
  have hcont :
      Tendsto (deriv extendedPower) (nhds 0)
        (nhds (deriv extendedPower 0)) :=
    hasDerivAt_deriv_extendedPower_zero.continuousAt
  rw [hasDerivAt_extendedPower_zero.deriv] at hcont
  exact hcont.mono_left nhdsWithin_le_nhds

theorem gap10
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hquotient :
      Tendsto (fun x => (f x - f 0) / x) (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds (deriv f 0)))
    (hfirstLimit :
      Tendsto (deriv f) (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds (-(Real.exp 1) / 2))) :
    deriv f 0 = -(Real.exp 1) / 2 := by
  rw [show f = extendedPower from funext hf]
  exact hasDerivAt_extendedPower_zero.deriv

theorem gap11
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hfirstValue : deriv f 0 = -(Real.exp 1) / 2) :
    ∀ x, inPuncturedDomain x →
      deriv (deriv f) x =
        extendedPower x *
          (firstLogDerivative x ^ 2 + secondLogDerivative x) := by
  rw [show f = extendedPower from funext hf]
  intro x hx
  exact (hasDerivAt_deriv_extendedPower_of_punctured x hx).deriv

theorem gap12
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hsecond :
      ∀ x, inPuncturedDomain x →
        deriv (deriv f) x =
          extendedPower x *
            (firstLogDerivative x ^ 2 + secondLogDerivative x)) :
    SecondAsymptotic f := by
  let base₁ : ℝ → ℝ :=
    fun x => (1 / 2 : ℝ) - x / 3 - 1 / (1 + x)
  let base₂ : ℝ → ℝ :=
    fun x => (2 / 3 : ℝ) - x / 2 - 1 / (1 + x) + 1 / (1 + x) ^ 2
  let analyticRemainder₁ : ℝ → ℝ :=
    fun x => deriv logQuotientReal x - base₁ x
  let analyticRemainder₂ : ℝ → ℝ :=
    fun x => deriv (deriv logQuotientReal) x - base₂ x
  let r₁ : ℝ → ℝ := fun x => firstLogDerivative x - base₁ x
  let r₂ : ℝ → ℝ := fun x => secondLogDerivative x - base₂ x
  have hrem₁ : HasDerivAt analyticRemainder₁ 0 0 := by
    dsimp only [analyticRemainder₁, base₁]
    convert hasDerivAt_deriv_logQuotientReal_zero.sub
      hasDerivAt_firstAsymptoticBase_zero using 1 <;>
      simp [logQuotientReal_deriv_zero]
  have hrem₂ : HasDerivAt analyticRemainder₂ 0 0 := by
    dsimp only [analyticRemainder₂, base₂]
    convert hasDerivAt_second_logQuotientReal_zero.sub
      hasDerivAt_secondAsymptoticBase_zero using 1 <;>
      simp [logQuotientReal_second_zero]
  have hrem₁0 : analyticRemainder₁ 0 = 0 := by
    dsimp only [analyticRemainder₁, base₁]
    rw [logQuotientReal_deriv_zero]
    norm_num
  have hrem₂0 : analyticRemainder₂ 0 = 0 := by
    dsimp only [analyticRemainder₂, base₂]
    rw [logQuotientReal_second_zero]
    norm_num
  have hsmall₁ : analyticRemainder₁ =o[nhds 0] (fun x : ℝ => x) := by
    simpa only [hrem₁0, sub_zero, smul_zero] using hrem₁.isLittleO
  have hsmall₂ : analyticRemainder₂ =o[nhds 0] (fun x : ℝ => x) := by
    simpa only [hrem₂0, sub_zero, smul_zero] using hrem₂.isLittleO
  have heq₁ :
      analyticRemainder₁ =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)] r₁ := by
    filter_upwards [
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with x hxball hx0
    have hxabs : |x| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hxball
    have hxne : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx0
    dsimp only [analyticRemainder₁, r₁]
    rw [deriv_logQuotientReal_eq_firstLogDerivative x hxabs hxne]
  have heq₂ :
      analyticRemainder₂ =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)] r₂ := by
    filter_upwards [
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with x hxball hx0
    have hxabs : |x| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hxball
    have hxne : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx0
    dsimp only [analyticRemainder₂, r₂]
    rw [second_deriv_logQuotientReal_eq_secondLogDerivative x hxabs hxne]
  refine ⟨r₁, r₂,
    (hsmall₁.mono nhdsWithin_le_nhds).congr' heq₁
      (Filter.Eventually.of_forall fun _ => rfl),
    (hsmall₂.mono nhdsWithin_le_nhds).congr' heq₂
      (Filter.Eventually.of_forall fun _ => rfl), ?_⟩
  intro x hx
  rw [hsecond x hx]
  congr 1
  dsimp only [r₁, r₂, base₁, base₂]
  ring

theorem gap13
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hsecondAsymptotic : SecondAsymptotic f) :
    (deriv^[2]) f 0 = (11 / 12 : ℝ) * Real.exp 1 := by
  rw [show f = extendedPower from funext hf]
  simpa [Function.iterate_succ_apply, Function.iterate_one] using
    hasDerivAt_deriv_extendedPower_zero.deriv

theorem gap14
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hsecondValue : (deriv^[2]) f 0 = (11 / 12 : ℝ) * Real.exp 1) :
    ∀ x, inPuncturedDomain x →
      (deriv^[3]) f x =
        extendedPower x *
          (firstLogDerivative x ^ 3 +
            3 * firstLogDerivative x * secondLogDerivative x +
            thirdLogDerivative x) := by
  rw [show f = extendedPower from funext hf]
  intro x hx
  simpa [Function.iterate_succ_apply, Function.iterate_one] using
    (hasDerivAt_second_deriv_extendedPower_of_punctured x hx).deriv

theorem gap15
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hthird :
      ∀ x, inPuncturedDomain x →
        (deriv^[3]) f x =
          extendedPower x *
            (firstLogDerivative x ^ 3 +
              3 * firstLogDerivative x * secondLogDerivative x +
              thirdLogDerivative x)) :
    (deriv^[3]) f 0 = -(21 / 8 : ℝ) * Real.exp 1 := by
  rw [show f = extendedPower from funext hf]
  simpa [Function.iterate_succ_apply, Function.iterate_one] using
    hasDerivAt_second_extendedPower_zero.deriv

theorem gap16
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (hfirstValue : deriv f 0 = -(Real.exp 1) / 2)
    (hsecondValue : (deriv^[2]) f 0 = (11 / 12 : ℝ) * Real.exp 1)
    (hthirdValue : (deriv^[3]) f 0 = -(21 / 8 : ℝ) * Real.exp 1) :
    ∀ x, |x| < 1 → f x = ∑' n, taylorAtZeroTerm f x n := by
  rw [show f = extendedPower from funext hf]
  intro x hx
  let R : NNReal := ⟨(|x| + 1) / 2, by positivity⟩
  have hR0 : 0 < R := by
    change 0 < (|x| + 1) / 2
    positivity
  have hxR : |x| < (R : ℝ) := by
    change |x| < (|x| + 1) / 2
    linarith
  have hR1 : (R : ℝ) < 1 := by
    change (|x| + 1) / 2 < 1
    linarith
  obtain ⟨p, hp⟩ :=
    extendedPower_hasFPowerSeriesOnBall_of_lt_one R hR0 hR1
  have hxball : x ∈ Metric.eball (0 : ℝ) R := by
    rw [Metric.eball_coe]
    simpa only [mem_ball_iff_norm, sub_zero, Real.norm_eq_abs] using hxR
  have hs := hp.hasSum_iteratedFDeriv hxball
  simp only [zero_add] at hs
  have hsTaylor :
      HasSum (taylorAtZeroTerm extendedPower x) (extendedPower x) := by
    convert hs using 1
    funext n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp only [iteratedDeriv_eq_iterate, Finset.prod_const, Finset.card_fin,
      taylorAtZeroTerm, smul_eq_mul]
    field_simp
  exact hsTaylor.tsum_eq.symm

theorem gap17
    (f : ℝ → ℝ) (hf : ∀ x, f x = extendedPower x) (hf0 : f 0 = Real.exp 1)
    (htaylor : ∀ x, |x| < 1 → f x = ∑' n, taylorAtZeroTerm f x n) :
    ∀ x, |x| < 1 → Summable (taylorAtZeroTerm f x) := by
  intro x hx
  by_contra hnot
  have hsumzero :
      (∑' n, taylorAtZeroTerm f x n) = 0 :=
    tsum_eq_zero_of_not_summable hnot
  have hfx : f x = 0 := (htaylor x hx).trans hsumzero
  have hext : 0 < extendedPower x := by
    unfold extendedPower
    split_ifs with hx0
    · positivity
    · apply Real.rpow_pos_of_pos
      linarith [(abs_lt.mp hx).1]
  rw [hf x] at hfx
  exact hext.ne' hfx

end

end ProofGap.Exercise2848
