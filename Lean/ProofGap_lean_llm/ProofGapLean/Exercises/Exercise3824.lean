import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3824

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

-- Statement correction: principal values require a puncture at the pole;
-- an ordinary Bochner integral across a nonintegrable pole is defined as 0.
def HasPrincipalValueAt (f : ℝ → ℝ) (p L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∃ A > 0, ∀ l u r : ℝ,
    l ≤ -A → A ≤ u → 0 < r → r ≤ δ →
      |(∫ x in l..(p - r), f x) +
        (∫ x in (p + r)..u, f x) - L| < ε

def principalValueAt (f : ℝ → ℝ) (p : ℝ) : ℝ :=
  sInf {L : ℝ | HasPrincipalValueAt f p L}

def HasDirichletValue (a L : ℝ) : Prop :=
  Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, Real.sin (a * t) / t)
    atTop (nhds L)

def dirichletValue (a : ℝ) : ℝ :=
  sInf {L : ℝ | HasDirichletValue a L}

def sineKernel (a b x : ℝ) : ℝ :=
  Real.sin (a * x) / (x + b)

def cosineKernel (a b x : ℝ) : ℝ :=
  Real.cos (a * x) / (x + b)

private def PrincipalValueAt (c : ℝ) (g : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∃ A > 0, ∀ l u r : ℝ,
    l ≤ -A → A ≤ u → 0 < r → r ≤ δ →
      |(∫ x in l..(c - r), g x) + (∫ x in (c + r)..u, g x) - L| < ε

private theorem laplace_cos (t s : ℝ) (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-t * x) * Real.cos (s * x)) =
      t / (t ^ 2 + s ^ 2) := by
  have hc :=
    integral_exp_mul_complex_Ioi
      (a := ((-t : ℝ) : ℂ) + s * Complex.I)
      (by simpa using neg_lt_zero.mpr ht) (0 : ℝ)
  have hi :
      IntegrableOn
        (fun x : ℝ =>
          Complex.exp ((((-t : ℝ) : ℂ) + s * Complex.I) * x))
        (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_complex_Ioi
      (by simpa using neg_lt_zero.mpr ht) 0
  have hre := integral_re hi
  calc
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-t * x) * Real.cos (s * x)) =
        ∫ x in Ioi (0 : ℝ),
          (Complex.exp
            ((((-t : ℝ) : ℂ) + s * Complex.I) * x)).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change
        Real.exp (-t * x) * Real.cos (s * x) =
          (Complex.exp
            ((((-t : ℝ) : ℂ) + s * Complex.I) * x)).re
      rw [Complex.exp_re]
      have hzre :
          ((((-t : ℝ) : ℂ) + s * Complex.I) * x).re =
            -t * x := by
        simp [Complex.mul_re, Complex.mul_im]
      have hzim :
          ((((-t : ℝ) : ℂ) + s * Complex.I) * x).im =
            s * x := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hzre, hzim]
    _ = (∫ x in Ioi (0 : ℝ),
        Complex.exp
          ((((-t : ℝ) : ℂ) + s * Complex.I) * x)).re := hre
    _ = (-Complex.exp
        ((((-t : ℝ) : ℂ) + s * Complex.I) * 0) /
          (((-t : ℝ) : ℂ) + s * Complex.I)).re :=
      congrArg Complex.re hc
    _ = t / (t ^ 2 + s ^ 2) := by
      rw [Complex.div_re]
      simp only [mul_zero, Complex.exp_zero,
        Complex.neg_re, Complex.neg_im, Complex.one_re,
        Complex.one_im, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, sub_zero,
        Complex.add_im, Complex.ofReal_im, zero_add,
        Complex.normSq_apply, zero_mul, zero_div, add_zero,
        neg_neg]
      field_simp
      ring

private theorem damped_dirichlet (t a : ℝ) (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-t * x) * (Real.sin (a * x) / x)) =
      Real.arctan (a / t) := by
  let J : ℝ → ℝ := fun u =>
    ∫ x in Ioi (0 : ℝ),
      Real.exp (-t * x) * (Real.sin (u * x) / x)
  have hbound :
      Integrable
        (fun x : ℝ => Real.exp (-t * x))
        (volume.restrict (Ioi (0 : ℝ))) := by
    exact
      integrableOn_exp_mul_Ioi
        (a := -t) (neg_lt_zero.mpr ht) 0
  have hJint (u : ℝ) :
      Integrable
        (fun x : ℝ =>
          Real.exp (-t * x) * (Real.sin (u * x) / x))
        (volume.restrict (Ioi (0 : ℝ))) := by
    apply (hbound.const_mul |u|).mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hxabs : 0 < |x| := abs_pos.mpr hx0
      have hsin :
          |Real.sin (u * x) / x| ≤ |u| := by
        rw [abs_div, div_le_iff₀ hxabs]
        calc
          |Real.sin (u * x)| ≤ |u * x| :=
            Real.abs_sin_le_abs
          _ = |u| * |x| := abs_mul u x
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hsin (Real.exp_pos _).le
  have hJderiv (u : ℝ) :
      HasDerivAt J (t / (t ^ 2 + u ^ 2)) u := by
    have hparam :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := volume.restrict (Ioi (0 : ℝ)))
        (F := fun v x : ℝ =>
          Real.exp (-t * x) * (Real.sin (v * x) / x))
        (F' := fun v x : ℝ =>
          Real.exp (-t * x) * Real.cos (v * x))
        (bound := fun x : ℝ => Real.exp (-t * x))
        (s := (Set.univ : Set ℝ))
        (x₀ := u)
        univ_mem
        (by
          filter_upwards [] with v
          fun_prop)
        (hJint u)
        (by fun_prop)
        (by
          filter_upwards with x
          intro v hv
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_pos (Real.exp_pos _)]
          exact mul_le_of_le_one_right
            (Real.exp_pos _).le
            (Real.abs_cos_le_one _))
        hbound
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          intro v hv
          have hx0 : x ≠ 0 := ne_of_gt hx
          have hs :=
            (Real.hasDerivAt_sin (v * x)).comp v
              ((hasDerivAt_id v).mul_const x)
          have hd :=
            ((hasDerivAt_const v (Real.exp (-t * x))).mul
              hs).div_const x
          simpa [Function.comp_def, div_eq_mul_inv,
            mul_comm, mul_left_comm, mul_assoc, hx0] using hd))
    change HasDerivAt J _ u
    have hpderiv := hparam.2
    convert hpderiv using 1
    exact (laplace_cos t u ht).symm
  have harctan (u : ℝ) :
      HasDerivAt (fun v : ℝ => Real.arctan (v / t))
        (t / (t ^ 2 + u ^ 2)) u := by
    convert
      (Real.hasDerivAt_arctan (u / t)).comp u
        ((hasDerivAt_id u).div_const t) using 1
    field_simp [ne_of_gt ht]
  have hconst :=
    is_const_of_deriv_eq_zero
      (f := fun u : ℝ => J u - Real.arctan (u / t))
      (fun u =>
        (hJderiv u).differentiableAt.sub
          (harctan u).differentiableAt)
      (fun u => by
        simpa using
          ((hJderiv u).sub (harctan u)).deriv)
      a 0
  have hJzero : J 0 = 0 := by
    simp [J]
  change
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-t * x) * (Real.sin (a * x) / x)) =
      Real.arctan (a / t)
  change J a = Real.arctan (a / t)
  have hzero : Real.arctan (0 / t) = 0 := by simp
  linarith

private theorem weighted_tail_bound
    (w wp f v : ℝ → ℝ) (K R B : ℝ)
    (hR : 0 < R) (hRB : R ≤ B) (hK : 0 ≤ K)
    (hwderiv : ∀ x ∈ Icc R B, HasDerivAt w (wp x) x)
    (hvderiv : ∀ x : ℝ, HasDerivAt v (f x) x)
    (hwpint : IntervalIntegrable wp volume R B)
    (hfcont : Continuous f)
    (hwnonneg : ∀ x ∈ Icc R B, 0 ≤ w x)
    (hwpnonpos : ∀ x ∈ Icc R B, wp x ≤ 0)
    (hvabs : ∀ x : ℝ, |v x| ≤ K) :
    |∫ x in R..B, w x * f x| ≤ 2 * K * w R := by
  have hwcont : ContinuousOn w [[R, B]] := by
    rw [uIcc_of_le hRB]
    intro x hx
    exact (hwderiv x hx).continuousAt.continuousWithinAt
  have hvcont : ContinuousOn v [[R, B]] :=
    fun x hx => (hvderiv x).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume R B :=
    hfcont.intervalIntegrable R B
  have hibp :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hwcont hvcont
      (fun x hx => hwderiv x (by
        rw [min_eq_left hRB, max_eq_right hRB] at hx
        exact ⟨hx.1.le, hx.2.le⟩))
      (fun x hx => hvderiv x)
      hwpint hfint
  have hformula :
      (∫ x in R..B, w x * f x) =
        w B * v B - w R * v R -
          ∫ x in R..B, wp x * v x := by
    simpa using hibp
  have habsint :
      IntervalIntegrable (fun x => |wp x * v x|) volume R B :=
    (hwpint.mul_continuousOn hvcont).abs
  have hmajorint :
      IntervalIntegrable (fun x => (-wp x) * K) volume R B :=
    by
      simpa [mul_comm] using hwpint.neg.const_mul K
  have hpoint (x : ℝ) (hx : x ∈ Icc R B) :
      |wp x * v x| ≤ (-wp x) * K := by
    rw [abs_mul, abs_of_nonpos (hwpnonpos x hx)]
    exact mul_le_mul_of_nonneg_left
      (hvabs x) (neg_nonneg.mpr (hwpnonpos x hx))
  have hinner :
      |∫ x in R..B, wp x * v x| ≤
        ∫ x in R..B, (-wp x) * K := by
    calc
      |∫ x in R..B, wp x * v x| ≤
          ∫ x in R..B, |wp x * v x| :=
        intervalIntegral.abs_integral_le_integral_abs hRB
      _ ≤ ∫ x in R..B, (-wp x) * K :=
        intervalIntegral.integral_mono_on hRB
          habsint hmajorint hpoint
  have hminus :
      (∫ x in R..B, -wp x) = w R - w B := by
    have hanti :
        (∫ x in R..B, -wp x) =
          (-w B) - (-w R) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => by
          apply (hwderiv x ?_).neg
          rw [uIcc_of_le hRB] at hx
          exact hx)
      exact hwpint.neg
    linarith
  have hinner' :
      |∫ x in R..B, wp x * v x| ≤
        (w R - w B) * K := by
    calc
      |∫ x in R..B, wp x * v x| ≤
          ∫ x in R..B, (-wp x) * K := hinner
      _ = (∫ x in R..B, -wp x) * K := by
        rw [intervalIntegral.integral_mul_const]
      _ = (w R - w B) * K := by rw [hminus]
  have hboundB : |w B * v B| ≤ w B * K := by
    rw [abs_mul, abs_of_nonneg (hwnonneg B ⟨hRB, le_rfl⟩)]
    exact mul_le_mul_of_nonneg_left
      (hvabs B) (hwnonneg B ⟨hRB, le_rfl⟩)
  have hboundR : |w R * v R| ≤ w R * K := by
    rw [abs_mul, abs_of_nonneg (hwnonneg R ⟨le_rfl, hRB⟩)]
    exact mul_le_mul_of_nonneg_left
      (hvabs R) (hwnonneg R ⟨le_rfl, hRB⟩)
  rw [hformula]
  calc
    |w B * v B - w R * v R -
        (∫ x in R..B, wp x * v x)| ≤
        |w B * v B| + |w R * v R| +
          |∫ x in R..B, wp x * v x| := by
      calc
        |_ - _| ≤ |w B * v B - w R * v R| +
            |∫ x in R..B, wp x * v x| := abs_sub _ _
        _ ≤ (|w B * v B| + |w R * v R|) +
            |∫ x in R..B, wp x * v x| := by
          gcongr
          exact abs_sub _ _
        _ = _ := by ring
    _ ≤ w B * K + w R * K + (w R - w B) * K :=
      add_le_add (add_le_add hboundB hboundR) hinner'
    _ = 2 * K * w R := by ring

private theorem sine_tail_bound
    (t a R B : ℝ) (ht : 0 ≤ t) (ha : a ≠ 0)
    (hR : 0 < R) (hRB : R ≤ B) :
    |∫ x in R..B,
        Real.exp (-t * x) * (Real.sin (a * x) / x)| ≤
      2 / (|a| * R) := by
  let w : ℝ → ℝ := fun x => Real.exp (-t * x) / x
  let wp : ℝ → ℝ := fun x =>
    -Real.exp (-t * x) * (t / x + 1 / x ^ 2)
  let f : ℝ → ℝ := fun x => Real.sin (a * x)
  let v : ℝ → ℝ := fun x => -Real.cos (a * x) / a
  have hwderiv (x : ℝ) (hx : x ∈ Icc R B) :
      HasDerivAt w (wp x) x := by
    have hxpos : 0 < x := hR.trans_le hx.1
    have he :
        HasDerivAt (fun y : ℝ => Real.exp (-t * y))
          (-t * Real.exp (-t * x)) x := by
      convert
        (Real.hasDerivAt_exp (-t * x)).comp x
          ((hasDerivAt_const x (-t)).mul
            (hasDerivAt_id x)) using 1 <;> ring
    have hd := he.div (hasDerivAt_id x) (ne_of_gt hxpos)
    convert hd using 1 <;>
      dsimp [w, wp] <;>
      field_simp [ne_of_gt hxpos] <;> ring
  have hvderiv (x : ℝ) :
      HasDerivAt v (f x) x := by
    have hc :=
      (Real.hasDerivAt_cos (a * x)).comp x
        ((hasDerivAt_const x a).mul (hasDerivAt_id x))
    convert hc.neg.div_const a using 1 <;>
      dsimp [v, f] <;> field_simp [ha] <;> ring
  have hwpint : IntervalIntegrable wp volume R B := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hRB]
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hR.trans_le hx.1)
    have he : ContinuousAt (fun y : ℝ => Real.exp (-t * y)) x := by
      fun_prop
    have htx : ContinuousAt (fun y : ℝ => t / y) x :=
      continuousAt_const.div continuousAt_id hx0
    have hone : ContinuousAt (fun y : ℝ => 1 / y ^ 2) x :=
      continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)
    simpa only [wp] using
      (he.neg.mul (htx.add hone)).continuousWithinAt
  have hwnonneg (x : ℝ) (hx : x ∈ Icc R B) : 0 ≤ w x := by
    dsimp [w]
    exact div_nonneg (Real.exp_pos _).le (hR.trans_le hx.1).le
  have hwpnonpos (x : ℝ) (hx : x ∈ Icc R B) : wp x ≤ 0 := by
    have hxpos : 0 < x := hR.trans_le hx.1
    dsimp [wp]
    rw [show -Real.exp (-t * x) *
        (t / x + 1 / x ^ 2) =
      -(Real.exp (-t * x) *
        (t / x + 1 / x ^ 2)) by ring]
    exact neg_nonpos.mpr
      (mul_nonneg (Real.exp_pos _).le
        (add_nonneg (div_nonneg ht hxpos.le) (by positivity)))
  have hvabs (x : ℝ) : |v x| ≤ 1 / |a| := by
    dsimp [v]
    rw [abs_div, abs_neg]
    exact div_le_div_of_nonneg_right
      (Real.abs_cos_le_one _) (abs_nonneg a)
  have hraw :=
    weighted_tail_bound w wp f v (1 / |a|) R B
      hR hRB (by positivity) hwderiv hvderiv hwpint
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))
      hwnonneg hwpnonpos hvabs
  have haw : 0 < |a| := abs_pos.mpr ha
  have hwR :
      w R ≤ 1 / R := by
    dsimp [w]
    have he : Real.exp (-t * R) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    exact (div_le_div_iff_of_pos_right hR).2 he
  calc
    |∫ x in R..B,
        Real.exp (-t * x) * (Real.sin (a * x) / x)| =
        |∫ x in R..B, w x * f x| := by
      apply congrArg abs
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp [w, f]
      ring
    _ ≤ 2 * (1 / |a|) * w R := hraw
    _ ≤ 2 * (1 / |a|) * (1 / R) := by
      gcongr
    _ = 2 / (|a| * R) := by
      field_simp [ne_of_gt haw, ne_of_gt hR]

private theorem cosine_tail_bound
    (a R B : ℝ) (ha : a ≠ 0)
    (hR : 0 < R) (hRB : R ≤ B) :
    |∫ x in R..B, Real.cos (a * x) / x| ≤
      2 / (|a| * R) := by
  let w : ℝ → ℝ := fun x => 1 / x
  let wp : ℝ → ℝ := fun x => -1 / x ^ 2
  let f : ℝ → ℝ := fun x => Real.cos (a * x)
  let v : ℝ → ℝ := fun x => Real.sin (a * x) / a
  have hwderiv (x : ℝ) (hx : x ∈ Icc R B) :
      HasDerivAt w (wp x) x := by
    have hx0 : x ≠ 0 := ne_of_gt (hR.trans_le hx.1)
    have hi :=
      (hasDerivAt_const x (1 : ℝ)).div
        (hasDerivAt_id x) hx0
    convert hi using 1 <;>
      dsimp [w, wp] <;> field_simp [hx0] <;> ring
  have hvderiv (x : ℝ) :
      HasDerivAt v (f x) x := by
    have hs :=
      (Real.hasDerivAt_sin (a * x)).comp x
        ((hasDerivAt_const x a).mul (hasDerivAt_id x))
    convert hs.div_const a using 1 <;>
      dsimp [v, f] <;> field_simp [ha] <;> ring
  have hwpint : IntervalIntegrable wp volume R B := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hRB]
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hR.trans_le hx.1)
    exact
      (continuousAt_const.neg.div
        (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).continuousWithinAt
  have hwnonneg (x : ℝ) (hx : x ∈ Icc R B) : 0 ≤ w x := by
    dsimp [w]
    exact one_div_nonneg.mpr (hR.trans_le hx.1).le
  have hwpnonpos (x : ℝ) (hx : x ∈ Icc R B) : wp x ≤ 0 := by
    dsimp [wp]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg x)
  have hvabs (x : ℝ) : |v x| ≤ 1 / |a| := by
    dsimp [v]
    rw [abs_div]
    exact div_le_div_of_nonneg_right
      (Real.abs_sin_le_one _) (abs_nonneg a)
  have hraw :=
    weighted_tail_bound w wp f v (1 / |a|) R B
      hR hRB (by positivity) hwderiv hvderiv hwpint
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))
      hwnonneg hwpnonpos hvabs
  have haw : 0 < |a| := abs_pos.mpr ha
  calc
    |∫ x in R..B, Real.cos (a * x) / x| =
        |∫ x in R..B, w x * f x| := by
      apply congrArg abs
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp [w, f]
      ring
    _ ≤ 2 * (1 / |a|) * w R := hraw
    _ = 2 / (|a| * R) := by
      dsimp [w]
      field_simp [ne_of_gt haw, ne_of_gt hR]

private def sineExt (a x : ℝ) : ℝ :=
  a * Real.sinc (a * x)

private theorem sineExt_eq (a x : ℝ) (ha : a ≠ 0) (hx : x ≠ 0) :
    sineExt a x = Real.sin (a * x) / x := by
  have hax : a * x ≠ 0 := mul_ne_zero ha hx
  rw [sineExt, Real.sinc_of_ne_zero hax]
  field_simp [ha, hx]

private theorem continuous_sineExt (a : ℝ) :
    Continuous (sineExt a) := by
  exact continuous_const.mul
    (Real.continuous_sinc.comp
      (continuous_const.mul continuous_id))

private theorem abs_sineExt_le (a x : ℝ) :
    |sineExt a x| ≤ |a| := by
  rw [sineExt, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg a)
    (Real.abs_sinc_le_one _)

private theorem damped_sineExt_integrable
    (t a : ℝ) (ht : 0 < t) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-t * x) * sineExt a x)
      (Ioi (0 : ℝ)) := by
  have hexp :
      IntegrableOn (fun x : ℝ => Real.exp (-t * x))
        (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi
      (a := -t) (neg_lt_zero.mpr ht) 0
  apply (hexp.const_mul |a|).mono'
  · exact
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul
        (continuous_sineExt a)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left
        (abs_sineExt_le a x) (Real.exp_pos _).le

private theorem damped_sineExt_integral
    (t a : ℝ) (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-t * x) * sineExt a x) =
      Real.arctan (a / t) := by
  by_cases ha : a = 0
  · simp [ha, sineExt]
  rw [← damped_dirichlet t a ht]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change
    Real.exp (-t * x) * sineExt a x =
      Real.exp (-t * x) * (Real.sin (a * x) / x)
  rw [sineExt_eq a x ha (ne_of_gt hx)]

private theorem damped_sineExt_tail_bound
    (t a R : ℝ) (ht : 0 < t) (ha : a ≠ 0)
    (hR : 0 < R) :
    |∫ x in Ioi R,
        Real.exp (-t * x) * sineExt a x| ≤
      2 / (|a| * R) := by
  have hint :
      IntegrableOn
        (fun x : ℝ => Real.exp (-t * x) * sineExt a x)
        (Ioi R) :=
    (damped_sineExt_integrable t a ht).mono_set
      (fun x hx => hR.trans hx)
  have htend :=
    intervalIntegral_tendsto_integral_Ioi
      (f := fun x : ℝ => Real.exp (-t * x) * sineExt a x)
      R hint (tendsto_id : Tendsto (fun B : ℝ => B) atTop atTop)
  have habstend :
      Tendsto
        (fun B : ℝ =>
          |∫ x in R..B,
            Real.exp (-t * x) * sineExt a x|)
        atTop
        (nhds
          |∫ x in Ioi R,
            Real.exp (-t * x) * sineExt a x|) :=
    continuous_abs.continuousAt.tendsto.comp htend
  apply le_of_tendsto habstend
  filter_upwards [eventually_ge_atTop R] with B hRB
  calc
    |∫ x in R..B,
        Real.exp (-t * x) * sineExt a x| =
        |∫ x in R..B,
          Real.exp (-t * x) *
            (Real.sin (a * x) / x)| := by
      apply congrArg abs
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hRB] at hx
      change
        Real.exp (-t * x) * sineExt a x =
          Real.exp (-t * x) * (Real.sin (a * x) / x)
      rw [sineExt_eq a x ha
        (ne_of_gt (hR.trans_le hx.1))]
    _ ≤ 2 / (|a| * R) :=
      sine_tail_bound t a R B ht.le ha hR hRB

private def τ (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

private theorem τ_pos (n : ℕ) : 0 < τ n := by
  dsimp [τ]
  positivity

private theorem τ_tendsto_zero :
    Tendsto τ atTop (nhds (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem finite_damped_tendsto
    (a R : ℝ) (hR : 0 ≤ R) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in (0 : ℝ)..R,
          Real.exp (-τ n * x) * sineExt a x)
      atTop
      (nhds (∫ x in (0 : ℝ)..R, sineExt a x)) := by
  have hset :
      Tendsto
        (fun n : ℕ =>
          ∫ x in Ioc (0 : ℝ) R,
            Real.exp (-τ n * x) * sineExt a x)
        atTop
        (nhds (∫ x in Ioc (0 : ℝ) R, sineExt a x)) := by
    apply tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Ioc (0 : ℝ) R))
      (F := fun (n : ℕ) (x : ℝ) =>
        Real.exp (-τ n * x) * sineExt a x)
      (f := sineExt a)
      (bound := fun _ : ℝ => |a|)
    · intro n
      exact
        ((Real.continuous_exp.comp
          (continuous_const.mul continuous_id)).mul
          (continuous_sineExt a)).aestronglyMeasurable
    · exact integrableOn_const measure_Ioc_lt_top.ne
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-τ n * x) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by
          nlinarith [τ_pos n, hx.1])
      exact
        (mul_le_mul_of_nonneg_right he
          (abs_nonneg (sineExt a x))).trans
        (by
          simpa using abs_sineExt_le a x)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have harg :
          Tendsto (fun n : ℕ => -τ n * x)
            atTop (nhds (0 : ℝ)) := by
        simpa using τ_tendsto_zero.neg.mul_const x
      have he :
          Tendsto (fun n : ℕ => Real.exp (-τ n * x))
            atTop (nhds (1 : ℝ)) := by
        simpa only [Real.exp_zero] using
          Real.continuous_exp.continuousAt.tendsto.comp harg
      simpa using he.mul_const (sineExt a x)
  simpa only [intervalIntegral.integral_of_le hR] using hset

private theorem arctan_frequency_tendsto
    (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => Real.arctan (a / τ n))
      atTop (nhds (Real.pi / 2 * Real.sign a)) := by
  have hn :
      Tendsto (fun n : ℕ => (n : ℝ) + 1)
        atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
  · have harg :
        Tendsto (fun n : ℕ => a / τ n)
          atTop atBot := by
      have hm := hn.const_mul_atTop_of_neg ha_neg
      convert hm using 1
      funext n
      dsimp [τ]
      field_simp
    have hatan :
        Tendsto (fun n : ℕ => Real.arctan (a / τ n))
          atTop (nhds (-(Real.pi / 2))) :=
      (Real.tendsto_arctan_atBot.mono_right inf_le_left).comp harg
    simpa [Real.sign_of_neg ha_neg] using hatan
  · have harg :
        Tendsto (fun n : ℕ => a / τ n)
          atTop atTop := by
      have hm := hn.const_mul_atTop ha_pos
      convert hm using 1
      funext n
      dsimp [τ]
      field_simp
    have hatan :
        Tendsto (fun n : ℕ => Real.arctan (a / τ n))
          atTop (nhds (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp harg
    simpa [Real.sign_of_pos ha_pos] using hatan

private theorem damped_sineExt_split
    (t a R : ℝ) (ht : 0 < t) (hR : 0 ≤ R) :
    (∫ x in Ioi (0 : ℝ),
        Real.exp (-t * x) * sineExt a x) =
      (∫ x in (0 : ℝ)..R,
        Real.exp (-t * x) * sineExt a x) +
      ∫ x in Ioi R,
        Real.exp (-t * x) * sineExt a x := by
  let F : ℝ → ℝ :=
    fun x => Real.exp (-t * x) * sineExt a x
  have hfull : IntegrableOn F (Ioi (0 : ℝ)) :=
    damped_sineExt_integrable t a ht
  have hleft : IntegrableOn F (Ioc (0 : ℝ) R) :=
    hfull.mono_set Ioc_subset_Ioi_self
  have hright : IntegrableOn F (Ioi R) :=
    hfull.mono_set (fun x hx => hR.trans_lt hx)
  calc
    (∫ x in Ioi (0 : ℝ),
        Real.exp (-t * x) * sineExt a x) =
        ∫ x in Ioc (0 : ℝ) R ∪ Ioi R, F x := by
      rw [Ioc_union_Ioi_eq_Ioi hR]
    _ = (∫ x in Ioc (0 : ℝ) R, F x) +
          ∫ x in Ioi R, F x :=
      setIntegral_union Ioc_disjoint_Ioi_same
        measurableSet_Ioi hleft hright
    _ = (∫ x in (0 : ℝ)..R,
          Real.exp (-t * x) * sineExt a x) +
        ∫ x in Ioi R,
          Real.exp (-t * x) * sineExt a x := by
      rw [intervalIntegral.integral_of_le hR]

private theorem sineExt_initial_bound
    (a r : ℝ) (hr : 0 ≤ r) :
    |∫ x in (0 : ℝ)..r, sineExt a x| ≤ |a| * r := by
  have hf :
      IntervalIntegrable (fun x : ℝ => |sineExt a x|)
        volume 0 r :=
    (continuous_sineExt a).abs.intervalIntegrable 0 r
  have hc :
      IntervalIntegrable (fun _ : ℝ => |a|) volume 0 r :=
    continuous_const.intervalIntegrable 0 r
  calc
    |∫ x in (0 : ℝ)..r, sineExt a x| ≤
        ∫ x in (0 : ℝ)..r, |sineExt a x| :=
      intervalIntegral.abs_integral_le_integral_abs hr
    _ ≤ ∫ x in (0 : ℝ)..r, |a| :=
      intervalIntegral.integral_mono_on hr hf hc
        (fun x hx => abs_sineExt_le a x)
    _ = |a| * r := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul, mul_comm]

private theorem sineExt_tail_bound
    (a R B : ℝ) (ha : a ≠ 0)
    (hR : 0 < R) (hRB : R ≤ B) :
    |∫ x in R..B, sineExt a x| ≤
      2 / (|a| * R) := by
  calc
    |∫ x in R..B, sineExt a x| =
        |∫ x in R..B, Real.sin (a * x) / x| := by
      apply congrArg abs
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hRB] at hx
      exact sineExt_eq a x ha
        (ne_of_gt (hR.trans_le hx.1))
    _ = |∫ x in R..B,
        Real.exp (-(0 : ℝ) * x) *
          (Real.sin (a * x) / x)| := by
      simp
    _ ≤ 2 / (|a| * R) :=
      sine_tail_bound 0 a R B (by norm_num) ha hR hRB

private def OneSidedHasValue (g : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∃ A > 0, ∀ r B : ℝ,
    0 < r → r ≤ δ → A ≤ B →
      |(∫ x in r..B, g x) - L| < ε

private theorem sine_one_sided
    (a : ℝ) (ha : a ≠ 0) :
    OneSidedHasValue
      (fun x : ℝ => Real.sin (a * x) / x)
      (Real.pi / 2 * Real.sign a) := by
  unfold OneSidedHasValue
  intro ε hε
  let C : ℝ := |a|
  have hC : 0 < C := by
    dsimp [C]
    exact abs_pos.mpr ha
  let R : ℝ := max 1 (12 / (C * ε) + 1)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hRgt : 12 / (C * ε) < R := by
    have hadd : 12 / (C * ε) < 12 / (C * ε) + 1 := by
      linarith
    exact hadd.trans_le (le_max_right _ _)
  have hbase : 12 < C * ε * R := by
    have hraw := (div_lt_iff₀ (mul_pos hC hε)).mp hRgt
    nlinarith
  have htailSmall : 2 / (|a| * R) < ε / 6 := by
    change 2 / (C * R) < ε / 6
    apply (div_lt_iff₀ (mul_pos hC hR)).2
    nlinarith
  let J : ℝ := ∫ x in (0 : ℝ)..R, sineExt a x
  let D : ℝ := Real.pi / 2 * Real.sign a
  have hfinite :
      Tendsto
        (fun n : ℕ =>
          ∫ x in (0 : ℝ)..R,
            Real.exp (-τ n * x) * sineExt a x)
        atTop (nhds J) := by
    simpa only [J] using finite_damped_tendsto a R hR.le
  have hatan :
      Tendsto (fun n : ℕ => Real.arctan (a / τ n))
        atTop (nhds D) := by
    simpa only [D] using arctan_frequency_tendsto a ha
  obtain ⟨N₁, hN₁⟩ :=
    (Metric.tendsto_atTop.1 hfinite)
      (ε / 6) (by positivity)
  obtain ⟨N₂, hN₂⟩ :=
    (Metric.tendsto_atTop.1 hatan)
      (ε / 6) (by positivity)
  let n : ℕ := max N₁ N₂
  have hn₁ : N₁ ≤ n := le_max_left _ _
  have hn₂ : N₂ ≤ n := le_max_right _ _
  have hmid :
      |(∫ x in (0 : ℝ)..R,
          Real.exp (-τ n * x) * sineExt a x) - J| <
        ε / 6 := by
    simpa only [Real.dist_eq] using hN₁ n hn₁
  have hatanerr :
      |Real.arctan (a / τ n) - D| < ε / 6 := by
    simpa only [Real.dist_eq] using hN₂ n hn₂
  have hsplit :=
    damped_sineExt_split (τ n) a R (τ_pos n) hR.le
  have hfull :=
    damped_sineExt_integral (τ n) a (τ_pos n)
  have htailset :=
    damped_sineExt_tail_bound
      (τ n) a R (τ_pos n) ha hR
  have hfiniteFull :
      |(∫ x in (0 : ℝ)..R,
          Real.exp (-τ n * x) * sineExt a x) -
        Real.arctan (a / τ n)| ≤
        2 / (|a| * R) := by
    rw [hsplit] at hfull
    rw [← hfull]
    rw [show
      (∫ x in (0 : ℝ)..R,
          Real.exp (-τ n * x) * sineExt a x) -
        ((∫ x in (0 : ℝ)..R,
            Real.exp (-τ n * x) * sineExt a x) +
          ∫ x in Ioi R,
            Real.exp (-τ n * x) * sineExt a x) =
        -(∫ x in Ioi R,
            Real.exp (-τ n * x) * sineExt a x) by ring,
      abs_neg]
    exact htailset
  have hJ : |J - D| < ε / 2 := by
    calc
      |J - D| =
          |(J - (∫ x in (0 : ℝ)..R,
              Real.exp (-τ n * x) * sineExt a x)) +
            (((∫ x in (0 : ℝ)..R,
                Real.exp (-τ n * x) * sineExt a x) -
              Real.arctan (a / τ n)) +
            (Real.arctan (a / τ n) - D))| := by
        congr 1
        ring
      _ ≤ |J - (∫ x in (0 : ℝ)..R,
              Real.exp (-τ n * x) * sineExt a x)| +
            (|(∫ x in (0 : ℝ)..R,
                Real.exp (-τ n * x) * sineExt a x) -
              Real.arctan (a / τ n)| +
            |Real.arctan (a / τ n) - D|) := by
        calc
          |_ + _| ≤
              |J - (∫ x in (0 : ℝ)..R,
                Real.exp (-τ n * x) * sineExt a x)| +
              |((∫ x in (0 : ℝ)..R,
                  Real.exp (-τ n * x) * sineExt a x) -
                Real.arctan (a / τ n)) +
                (Real.arctan (a / τ n) - D)| :=
            abs_add_le _ _
          _ ≤ _ := by
            gcongr
            exact abs_add_le _ _
      _ < ε / 6 + (ε / 6 + ε / 6) := by
        exact add_lt_add
          (by simpa [abs_sub_comm] using hmid)
          (add_lt_add (hfiniteFull.trans_lt htailSmall) hatanerr)
      _ = ε / 2 := by ring
  let δ : ℝ := min 1 (ε / (12 * (C + 1)))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, R, hR, ?_⟩
  intro r B hr hrδ hRB
  have hr1 : r ≤ 1 := hrδ.trans (min_le_left _ _)
  have hrR : r ≤ R := hr1.trans hR1
  have hrB : r ≤ B := hrR.trans hRB
  have hδfrac : r ≤ ε / (12 * (C + 1)) :=
    hrδ.trans (min_le_right _ _)
  have hnearSmall : C * r < ε / 6 := by
    have hCp : 0 < C + 1 := by linarith
    have hmul :=
      mul_le_mul_of_nonneg_left hδfrac hCp.le
    have heq :
        (C + 1) * (ε / (12 * (C + 1))) = ε / 12 := by
      field_simp [ne_of_gt hCp]
    rw [heq] at hmul
    have hCr : C * r ≤ (C + 1) * r := by
      nlinarith
    linarith
  have hnear :
      |∫ x in (0 : ℝ)..r, sineExt a x| < ε / 6 :=
    (sineExt_initial_bound a r hr.le).trans_lt hnearSmall
  have htail :
      |∫ x in R..B, sineExt a x| < ε / 6 :=
    (sineExt_tail_bound a R B ha hR hRB).trans_lt htailSmall
  have hsum₁ :=
    intervalIntegral.integral_add_adjacent_intervals
      (μ := volume)
      ((continuous_sineExt a).intervalIntegrable 0 r)
      ((continuous_sineExt a).intervalIntegrable r R)
  have hsum₂ :=
    intervalIntegral.integral_add_adjacent_intervals
      (μ := volume)
      ((continuous_sineExt a).intervalIntegrable r R)
      ((continuous_sineExt a).intervalIntegrable R B)
  have hdecomp :
      (∫ x in r..B, sineExt a x) =
        J - (∫ x in (0 : ℝ)..r, sineExt a x) +
          ∫ x in R..B, sineExt a x := by
    dsimp [J]
    linarith
  have hraw :
      (∫ x in r..B, Real.sin (a * x) / x) =
        ∫ x in r..B, sineExt a x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hrB] at hx
    exact (sineExt_eq a x ha
      (ne_of_gt (hr.trans_le hx.1))).symm
  rw [hraw, hdecomp]
  calc
    |J - (∫ x in (0 : ℝ)..r, sineExt a x) +
          (∫ x in R..B, sineExt a x) - D| =
        |(J - D) +
          (-(∫ x in (0 : ℝ)..r, sineExt a x) +
            ∫ x in R..B, sineExt a x)| := by
      congr 1
      ring
    _ ≤ |J - D| +
          (|∫ x in (0 : ℝ)..r, sineExt a x| +
            |∫ x in R..B, sineExt a x|) := by
      calc
        |_ + _| ≤ |J - D| +
            |-(∫ x in (0 : ℝ)..r, sineExt a x) +
              ∫ x in R..B, sineExt a x| :=
          abs_add_le _ _
        _ ≤ |J - D| +
            (|-(∫ x in (0 : ℝ)..r, sineExt a x)| +
              |∫ x in R..B, sineExt a x|) := by
          gcongr
          exact abs_add_le _ _
        _ = _ := by rw [abs_neg]
    _ < ε / 2 + (ε / 6 + ε / 6) :=
      add_lt_add hJ (add_lt_add hnear htail)
    _ < ε := by linarith

private theorem sine_kernel_even (a x : ℝ) :
    Real.sin (a * (-x)) / (-x) =
      Real.sin (a * x) / x := by
  rw [show a * (-x) = -(a * x) by ring, Real.sin_neg]
  ring

private theorem cosine_kernel_odd (a x : ℝ) :
    Real.cos (a * (-x)) / (-x) =
      -(Real.cos (a * x) / x) := by
  rw [show a * (-x) = -(a * x) by ring, Real.cos_neg]
  ring

private theorem cosine_intervalIntegrable
    (a p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    IntervalIntegrable
      (fun x : ℝ => Real.cos (a * x) / x)
      volume p q := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hpq]
  apply
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).continuousOn.div
      continuousOn_id
  intro x hx
  exact ne_of_gt (hp.trans_le hx.1)

private theorem principal_sine_kernel
    (a : ℝ) (ha : a ≠ 0) :
    PrincipalValueAt 0
      (fun x : ℝ => Real.sin (a * x) / x)
      (Real.pi * Real.sign a) := by
  unfold PrincipalValueAt
  intro ε hε
  obtain ⟨δ, hδ, A, hA, hm⟩ :=
    sine_one_sided a ha (ε / 2) (by positivity)
  refine ⟨δ, hδ, A, hA, ?_⟩
  intro l u r hl hu hr hrδ
  have hml :=
    hm r (-l) hr hrδ (by linarith)
  have hmu :=
    hm r u hr hrδ hu
  have hreflect :
      (∫ x in l..(-r), Real.sin (a * x) / x) =
        ∫ x in r..(-l), Real.sin (a * x) / x := by
    calc
      (∫ x in l..(-r), Real.sin (a * x) / x) =
          ∫ x in l..(-r),
            Real.sin (a * (-x)) / (-x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact (sine_kernel_even a x).symm
      _ = ∫ x in r..(-l), Real.sin (a * x) / x := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := fun x : ℝ => Real.sin (a * x) / x)
            (a := l) (b := -r))
  simp only [zero_sub, zero_add]
  rw [hreflect]
  calc
    |(∫ x in r..(-l), Real.sin (a * x) / x) +
          (∫ x in r..u, Real.sin (a * x) / x) -
        Real.pi * Real.sign a| =
        |((∫ x in r..(-l), Real.sin (a * x) / x) -
            Real.pi / 2 * Real.sign a) +
          ((∫ x in r..u, Real.sin (a * x) / x) -
            Real.pi / 2 * Real.sign a)| := by
      congr 1
      ring
    _ ≤ |(∫ x in r..(-l), Real.sin (a * x) / x) -
            Real.pi / 2 * Real.sign a| +
          |(∫ x in r..u, Real.sin (a * x) / x) -
            Real.pi / 2 * Real.sign a| :=
      abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hml hmu
    _ = ε := by ring

private theorem principal_cosine_kernel
    (a : ℝ) (ha : a ≠ 0) :
    PrincipalValueAt 0
      (fun x : ℝ => Real.cos (a * x) / x) 0 := by
  unfold PrincipalValueAt
  intro ε hε
  let C : ℝ := |a|
  have hC : 0 < C := by
    dsimp [C]
    exact abs_pos.mpr ha
  let A : ℝ := max 1 (2 / (C * ε) + 1)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hAgt : 2 / (C * ε) < A := by
    have hadd : 2 / (C * ε) < 2 / (C * ε) + 1 := by
      linarith
    exact hadd.trans_le (le_max_right _ _)
  have hbase : 2 < C * ε * A := by
    have hraw := (div_lt_iff₀ (mul_pos hC hε)).mp hAgt
    nlinarith
  refine ⟨1, by norm_num, A, hA, ?_⟩
  intro l u r hl hu hr hr1
  let P : ℝ := -l
  have hP : A ≤ P := by
    dsimp [P]
    linarith
  have hPpos : 0 < P := hA.trans_le hP
  have huPos : 0 < u := hA.trans_le hu
  have hrP : r ≤ P := hr1.trans (hA1.trans hP)
  have hru : r ≤ u := hr1.trans (hA1.trans hu)
  have hreflect :
      (∫ x in l..(-r), Real.cos (a * x) / x) =
        -(∫ x in r..P, Real.cos (a * x) / x) := by
    calc
      (∫ x in l..(-r), Real.cos (a * x) / x) =
          ∫ x in l..(-r),
            -(Real.cos (a * (-x)) / (-x)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change
          Real.cos (a * x) / x =
            -(Real.cos (a * (-x)) / (-x))
        rw [cosine_kernel_odd]
        ring
      _ = -(∫ x in l..(-r),
            Real.cos (a * (-x)) / (-x)) := by
        rw [intervalIntegral.integral_neg]
      _ = -(∫ x in r..P,
            Real.cos (a * x) / x) := by
        dsimp [P]
        congr 1
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := fun x : ℝ => Real.cos (a * x) / x)
            (a := l) (b := -r))
  simp only [zero_sub, zero_add]
  rw [hreflect, sub_zero]
  rcases le_total P u with hPu | huP
  · have hadd :=
      intervalIntegral.integral_add_adjacent_intervals
        (μ := volume)
        (cosine_intervalIntegrable a r P hr hrP)
        (cosine_intervalIntegrable a P u hPpos hPu)
    have heq :
        -(∫ x in r..P, Real.cos (a * x) / x) +
            (∫ x in r..u, Real.cos (a * x) / x) =
          ∫ x in P..u, Real.cos (a * x) / x := by
      linarith
    rw [heq]
    have hb := cosine_tail_bound a P u ha hPpos hPu
    have hbaseP : 2 < C * ε * P := by
      have hmono :
          C * ε * A ≤ C * ε * P := by
        exact mul_le_mul_of_nonneg_left hP
          (mul_nonneg hC.le hε.le)
      exact hbase.trans_le hmono
    have hsmall : 2 / (|a| * P) < ε := by
      change 2 / (C * P) < ε
      apply (div_lt_iff₀ (mul_pos hC hPpos)).2
      nlinarith
    exact hb.trans_lt hsmall
  · have hadd :=
      intervalIntegral.integral_add_adjacent_intervals
        (μ := volume)
        (cosine_intervalIntegrable a r u hr hru)
        (cosine_intervalIntegrable a u P huPos huP)
    have heq :
        -(∫ x in r..P, Real.cos (a * x) / x) +
            (∫ x in r..u, Real.cos (a * x) / x) =
          -(∫ x in u..P, Real.cos (a * x) / x) := by
      linarith
    rw [heq, abs_neg]
    have hb := cosine_tail_bound a u P ha huPos huP
    have hbaseu : 2 < C * ε * u := by
      have hmono :
          C * ε * A ≤ C * ε * u := by
        exact mul_le_mul_of_nonneg_left hu
          (mul_nonneg hC.le hε.le)
      exact hbase.trans_le hmono
    have hsmall : 2 / (|a| * u) < ε := by
      change 2 / (C * u) < ε
      apply (div_lt_iff₀ (mul_pos hC huPos)).2
      nlinarith
    exact hb.trans_lt hsmall

private theorem trig_div_intervalIntegrable
    (num : ℝ → ℝ) (p q : ℝ)
    (hnum : Continuous num)
    (hzero : ∀ x ∈ [[p, q]], x ≠ 0) :
    IntervalIntegrable (fun x => num x / x) volume p q := by
  exact
    (hnum.continuousOn.div continuousOn_id hzero).intervalIntegrable

private theorem principal_sin_cos_linear
    (a c d : ℝ) (ha : a ≠ 0) :
    PrincipalValueAt 0
      (fun x : ℝ =>
        c * (Real.sin (a * x) / x) +
          d * (Real.cos (a * x) / x))
      (c * (Real.pi * Real.sign a) + d * 0) := by
  have hs := principal_sine_kernel a ha
  have hc := principal_cosine_kernel a ha
  unfold PrincipalValueAt at hs hc ⊢
  intro ε hε
  obtain ⟨δs, hδs, As, hAs, hsm⟩ :=
    hs (ε / (2 * (|c| + 1))) (by positivity)
  obtain ⟨δc, hδc, Ac, hAc, hcm⟩ :=
    hc (ε / (2 * (|d| + 1))) (by positivity)
  let δ : ℝ := min 1 (min δs δc)
  let A : ℝ := max 1 (max As Ac)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨δ, hδ, A, hA, ?_⟩
  intro l u r hl hu hr hrδ
  have hr1 : r ≤ 1 := hrδ.trans (min_le_left _ _)
  have hrδs :
      r ≤ δs :=
    hrδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrδc :
      r ≤ δc :=
    hrδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hAsA :
      As ≤ A :=
    (le_max_left As Ac).trans (le_max_right 1 (max As Ac))
  have hAcA :
      Ac ≤ A :=
    (le_max_right As Ac).trans (le_max_right 1 (max As Ac))
  have hse :=
    hsm l u r (hl.trans (neg_le_neg hAsA))
      (hAsA.trans hu) hr hrδs
  have hce :=
    hcm l u r (hl.trans (neg_le_neg hAcA))
      (hAcA.trans hu) hr hrδc
  have hlr : l ≤ -r := by
    have hl1 : l ≤ -1 :=
      hl.trans (neg_le_neg (le_max_left 1 (max As Ac)))
    linarith
  have hru : r ≤ u :=
    hr1.trans ((le_max_left 1 (max As Ac)).trans hu)
  have hsleft :
      IntervalIntegrable
        (fun x : ℝ => Real.sin (a * x) / x)
        volume l (-r) := by
    apply trig_div_intervalIntegrable
      (fun x : ℝ => Real.sin (a * x)) l (-r)
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))
    rw [uIcc_of_le hlr]
    intro x hx
    exact ne_of_lt (hx.2.trans_lt (neg_lt_zero.mpr hr))
  have hcleft :
      IntervalIntegrable
        (fun x : ℝ => Real.cos (a * x) / x)
        volume l (-r) := by
    apply trig_div_intervalIntegrable
      (fun x : ℝ => Real.cos (a * x)) l (-r)
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))
    rw [uIcc_of_le hlr]
    intro x hx
    exact ne_of_lt (hx.2.trans_lt (neg_lt_zero.mpr hr))
  have hsright :
      IntervalIntegrable
        (fun x : ℝ => Real.sin (a * x) / x)
        volume r u := by
    apply trig_div_intervalIntegrable
      (fun x : ℝ => Real.sin (a * x)) r u
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))
    rw [uIcc_of_le hru]
    intro x hx
    exact ne_of_gt (hr.trans_le hx.1)
  have hcright :
      IntervalIntegrable
        (fun x : ℝ => Real.cos (a * x) / x)
        volume r u := by
    apply trig_div_intervalIntegrable
      (fun x : ℝ => Real.cos (a * x)) r u
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))
    rw [uIcc_of_le hru]
    intro x hx
    exact ne_of_gt (hr.trans_le hx.1)
  simp only [zero_sub, zero_add] at hse hce ⊢
  rw [intervalIntegral.integral_add
      (hsleft.const_mul c) (hcleft.const_mul d),
    intervalIntegral.integral_add
      (hsright.const_mul c) (hcright.const_mul d),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  let S : ℝ :=
    (∫ x in l..(-r), Real.sin (a * x) / x) +
      ∫ x in r..u, Real.sin (a * x) / x
  let T : ℝ :=
    (∫ x in l..(-r), Real.cos (a * x) / x) +
      ∫ x in r..u, Real.cos (a * x) / x
  rw [show
    (c * (∫ x in l..(-r), Real.sin (a * x) / x) +
        d * (∫ x in l..(-r), Real.cos (a * x) / x)) +
      (c * (∫ x in r..u, Real.sin (a * x) / x) +
        d * (∫ x in r..u, Real.cos (a * x) / x)) =
      c * S + d * T by
    dsimp [S, T]
    ring]
  change |c * S + d * T -
    (c * (Real.pi * Real.sign a) + d * 0)| < ε
  have hsc : |c| * |S - Real.pi * Real.sign a| < ε / 2 := by
    calc
      |c| * |S - Real.pi * Real.sign a| ≤
          (|c| + 1) * |S - Real.pi * Real.sign a| := by
        exact mul_le_mul_of_nonneg_right
          (by linarith : |c| ≤ |c| + 1)
          (abs_nonneg (S - Real.pi * Real.sign a))
      _ < (|c| + 1) * (ε / (2 * (|c| + 1))) :=
        mul_lt_mul_of_pos_left hse (by positivity)
      _ = ε / 2 := by
        have hcne : |c| + 1 ≠ 0 := by positivity
        field_simp [hcne]
  have htc : |d| * |T - 0| < ε / 2 := by
    calc
      |d| * |T - 0| ≤ (|d| + 1) * |T - 0| := by
        exact mul_le_mul_of_nonneg_right
          (by linarith : |d| ≤ |d| + 1)
          (abs_nonneg (T - 0))
      _ < (|d| + 1) * (ε / (2 * (|d| + 1))) :=
        mul_lt_mul_of_pos_left hce (by positivity)
      _ = ε / 2 := by
        have hdne : |d| + 1 ≠ 0 := by positivity
        field_simp [hdne]
  calc
    |c * S + d * T -
        (c * (Real.pi * Real.sign a) + d * 0)| =
        |c * (S - Real.pi * Real.sign a) +
          d * (T - 0)| := by
      congr 1
      ring
    _ ≤ |c * (S - Real.pi * Real.sign a)| +
          |d * (T - 0)| :=
      abs_add_le _ _
    _ = |c| * |S - Real.pi * Real.sign a| +
          |d| * |T - 0| := by
      rw [abs_mul, abs_mul]
    _ < ε / 2 + ε / 2 := add_lt_add hsc htc
    _ = ε := by ring

private theorem principal_translate
    {g : ℝ → ℝ} {L b : ℝ}
    (h : PrincipalValueAt 0 g L) :
    PrincipalValueAt (-b) (fun x => g (x + b)) L := by
  unfold PrincipalValueAt at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, A, hA, hm⟩ := h ε hε
  let A' : ℝ := A + |b|
  have hA' : 0 < A' := by
    dsimp [A']
    positivity
  refine ⟨δ, hδ, A', hA', ?_⟩
  intro l u r hl hu hr hrδ
  have hl' : l + b ≤ -A := by
    dsimp [A'] at hl
    nlinarith [le_abs_self b]
  have hu' : A ≤ u + b := by
    dsimp [A'] at hu
    nlinarith [neg_abs_le b]
  have hmain := hm (l + b) (u + b) r hl' hu' hr hrδ
  rw [intervalIntegral.integral_comp_add_right,
    intervalIntegral.integral_comp_add_right]
  convert hmain using 1 <;> ring

private theorem principalValue_unique
    {f : ℝ → ℝ} {p L M : ℝ}
    (hL : HasPrincipalValueAt f p L)
    (hM : HasPrincipalValueAt f p M) :
    L = M := by
  by_contra hne
  have hdist : 0 < |L - M| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δL, hδL, AL, hAL, hmL⟩ :=
    hL (|L - M| / 3) (by positivity)
  obtain ⟨δM, hδM, AM, hAM, hmM⟩ :=
    hM (|L - M| / 3) (by positivity)
  let r : ℝ := min δL δM / 2
  let A : ℝ := max AL AM
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrL : r ≤ δL := by
    dsimp [r]
    nlinarith [min_le_left δL δM, hδL, hδM]
  have hrM : r ≤ δM := by
    dsimp [r]
    nlinarith [min_le_right δL δM, hδL, hδM]
  have hleftL : -A ≤ -AL := neg_le_neg (le_max_left AL AM)
  have hleftM : -A ≤ -AM := neg_le_neg (le_max_right AL AM)
  have hrightL : AL ≤ A := le_max_left AL AM
  have hrightM : AM ≤ A := le_max_right AL AM
  have heL := hmL (-A) A r hleftL hrightL hr hrL
  have heM := hmM (-A) A r hleftM hrightM hr hrM
  let Q : ℝ :=
    (∫ x in (-A)..(p - r), f x) +
      ∫ x in (p + r)..A, f x
  have htri : |L - M| ≤ |Q - L| + |Q - M| := by
    calc
      |L - M| = |-(Q - L) + (Q - M)| := by
        congr 1
        ring
      _ ≤ |-(Q - L)| + |Q - M| := abs_add_le _ _
      _ = |Q - L| + |Q - M| := by rw [abs_neg]
  have : |L - M| < |L - M| / 3 + |L - M| / 3 :=
    htri.trans_lt (add_lt_add heL heM)
  linarith

private theorem principalValueAt_eq_of_has
    {f : ℝ → ℝ} {p L : ℝ}
    (h : HasPrincipalValueAt f p L) :
    principalValueAt f p = L := by
  have hset :
      {M : ℝ | HasPrincipalValueAt f p M} = {L} := by
    ext M
    constructor
    · intro hM
      simpa only [Set.mem_singleton_iff] using
        principalValue_unique hM h
    · intro hM
      simpa only [Set.mem_singleton_iff] using hM ▸ h
  unfold principalValueAt
  rw [hset]
  exact csInf_singleton L

private theorem signType_sign_eq_realSign (a : ℝ) :
    (SignType.sign a : ℝ) = Real.sign a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [sign_neg ha, Real.sign_of_neg ha]
    norm_num
  · subst a
    simp
  · rw [sign_pos ha, Real.sign_of_pos ha]
    norm_num

private theorem sineKernel_hasPrincipalValue_nonzero
    (a b : ℝ) (ha : a ≠ 0) :
    HasPrincipalValueAt (sineKernel a b) (-b)
      (Real.pi * Real.sign a * Real.cos (a * b)) := by
  have hzero :=
    principal_sin_cos_linear
      a (Real.cos (a * b)) (-Real.sin (a * b)) ha
  have hshift :=
    principal_translate (b := b) hzero
  change PrincipalValueAt (-b) (sineKernel a b)
    (Real.pi * Real.sign a * Real.cos (a * b))
  convert hshift using 1
  · funext x
    unfold sineKernel
    rw [show a * x = a * (x + b) - a * b by ring,
      Real.sin_sub]
    ring
  · ring

private theorem cosineKernel_hasPrincipalValue_nonzero
    (a b : ℝ) (ha : a ≠ 0) :
    HasPrincipalValueAt (cosineKernel a b) (-b)
      (Real.pi * Real.sign a * Real.sin (a * b)) := by
  have hzero :=
    principal_sin_cos_linear
      a (Real.sin (a * b)) (Real.cos (a * b)) ha
  have hshift :=
    principal_translate (b := b) hzero
  change PrincipalValueAt (-b) (cosineKernel a b)
    (Real.pi * Real.sign a * Real.sin (a * b))
  convert hshift using 1
  · funext x
    unfold cosineKernel
    rw [show a * x = a * (x + b) - a * b by ring,
      Real.cos_sub]
    ring
  · ring

private theorem shiftedSine_hasPrincipalValue_nonzero
    (a b : ℝ) (ha : a ≠ 0) :
    HasPrincipalValueAt
      (fun t : ℝ => Real.sin (a * (t - b)) / t) 0
      (Real.pi * Real.sign a * Real.cos (a * b)) := by
  have h :=
    principal_sin_cos_linear
      a (Real.cos (a * b)) (-Real.sin (a * b)) ha
  change PrincipalValueAt 0
    (fun t : ℝ => Real.sin (a * (t - b)) / t)
    (Real.pi * Real.sign a * Real.cos (a * b))
  convert h using 1
  · funext t
    rw [show a * (t - b) = a * t - a * b by ring,
      Real.sin_sub]
    ring
  · ring

private theorem scaledSine_hasPrincipalValue_nonzero
    (a c : ℝ) (ha : a ≠ 0) :
    HasPrincipalValueAt
      (fun t : ℝ => Real.sin (a * t) * c / t) 0
      (Real.pi * Real.sign a * c) := by
  have h := principal_sin_cos_linear a c 0 ha
  change PrincipalValueAt 0
    (fun t : ℝ => Real.sin (a * t) * c / t)
    (Real.pi * Real.sign a * c)
  convert h using 1
  · funext t
    ring
  ·
    ring

private theorem scaledCosine_hasPrincipalValue_nonzero
    (a c : ℝ) (ha : a ≠ 0) :
    HasPrincipalValueAt
      (fun t : ℝ => Real.cos (a * t) * c / t) 0 0 := by
  have h := principal_sin_cos_linear a 0 c ha
  change PrincipalValueAt 0
    (fun t : ℝ => Real.cos (a * t) * c / t) 0
  convert h using 1
  · funext t
    ring
  ·
    ring

private theorem zero_hasPrincipalValue (p : ℝ) :
    HasPrincipalValueAt (fun _ : ℝ => 0) p 0 := by
  intro ε hε
  refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
  intro l u r hl hu hr hδ
  simpa using hε

private theorem dirichlet_hasValue_nonzero
    (a : ℝ) (ha : a ≠ 0) :
    HasDirichletValue a (Real.pi / 2 * Real.sign a) := by
  unfold HasDirichletValue
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, A, hA, hm⟩ :=
    sine_one_sided a ha (ε / 2) (by positivity)
  let q : ℝ := ε / (4 * (|a| + 1))
  let r : ℝ := min δ q / 2
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrδ : r ≤ δ := by
    dsimp [r]
    nlinarith [min_le_left δ q, hδ, hq]
  have hrq : r ≤ q / 2 := by
    dsimp [r]
    nlinarith [min_le_right δ q]
  let B : ℝ := max A r
  refine ⟨B, ?_⟩
  intro R hBR
  have hAR : A ≤ R := (le_max_left A r).trans hBR
  have hrR : r ≤ R := (le_max_right A r).trans hBR
  have htail := hm r R hr hrδ hAR
  have hnearBound :=
    sineExt_initial_bound a r hr.le
  have hnearSmall :
      |∫ x in (0 : ℝ)..r, sineExt a x| < ε / 2 := by
    refine hnearBound.trans_lt ?_
    have hden : 0 < |a| + 1 := by positivity
    have hqeq : (|a| + 1) * q = ε / 4 := by
      dsimp [q]
      field_simp [hden.ne']
    have hmul :
        |a| * r ≤ (|a| + 1) * (q / 2) := by
      exact mul_le_mul
        (by linarith : |a| ≤ |a| + 1) hrq
        hr.le (by positivity)
    rw [show (|a| + 1) * (q / 2) =
        ((|a| + 1) * q) / 2 by ring, hqeq] at hmul
    linarith
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals
      (μ := volume)
      ((continuous_sineExt a).intervalIntegrable 0 r)
      ((continuous_sineExt a).intervalIntegrable r R)
  have htarget :
      (∫ t in (0 : ℝ)..R, Real.sin (a * t) / t) =
        ∫ t in (0 : ℝ)..R, sineExt a t := by
    apply intervalIntegral.integral_congr_ae
    have hne :
        ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t ht hmem
    exact (sineExt_eq a t ha ht).symm
  have htailExt :
      |(∫ x in r..R, sineExt a x) -
          Real.pi / 2 * Real.sign a| < ε / 2 := by
    rw [show (∫ x in r..R, sineExt a x) =
        ∫ x in r..R, Real.sin (a * x) / x by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hrR] at hx
      exact sineExt_eq a x ha (ne_of_gt (hr.trans_le hx.1))]
    exact htail
  rw [Real.dist_eq, htarget, ← hadd]
  calc
    |(∫ x in (0 : ℝ)..r, sineExt a x) +
          (∫ x in r..R, sineExt a x) -
          Real.pi / 2 * Real.sign a| =
        |(∫ x in (0 : ℝ)..r, sineExt a x) +
          ((∫ x in r..R, sineExt a x) -
            Real.pi / 2 * Real.sign a)| := by
      congr 1
      ring
    _ ≤ |∫ x in (0 : ℝ)..r, sineExt a x| +
          |(∫ x in r..R, sineExt a x) -
            Real.pi / 2 * Real.sign a| :=
      abs_add_le _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add hnearSmall htailExt
    _ = ε := by ring

private theorem dirichletValue_eq (a : ℝ) :
    dirichletValue a = Real.pi / 2 * Real.sign a := by
  by_cases ha : a = 0
  · subst a
    have hzero : HasDirichletValue 0 0 := by
      unfold HasDirichletValue
      simpa using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0))
    have hset :
        {L : ℝ | HasDirichletValue 0 L} = {0} := by
      ext L
      constructor
      · intro hL
        simpa only [Set.mem_singleton_iff] using
          tendsto_nhds_unique hL hzero
      · intro hL
        simpa only [Set.mem_singleton_iff] using hL ▸ hzero
    unfold dirichletValue
    rw [hset, csInf_singleton]
    simp
  · have h := dirichlet_hasValue_nonzero a ha
    have hset :
        {L : ℝ | HasDirichletValue a L} =
          {Real.pi / 2 * Real.sign a} := by
      ext L
      constructor
      · intro hL
        simpa only [Set.mem_singleton_iff] using
          tendsto_nhds_unique hL h
      · intro hL
        simpa only [Set.mem_singleton_iff] using hL ▸ h
    unfold dirichletValue
    rw [hset]
    exact csInf_singleton _

private theorem cosineKernel_zero_has_no_principal_value
    (b L : ℝ) :
    ¬HasPrincipalValueAt (cosineKernel 0 b) (-b) L := by
  intro h
  have hreciprocal :
      HasPrincipalValueAt (fun x : ℝ => 1 / (x + b)) (-b) L := by
    convert h using 1
    funext x
    simp [cosineKernel]
  obtain ⟨δ, hδ, A, hA, hm⟩ :=
    hreciprocal 1 (by norm_num)
  let r : ℝ := δ / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hrδ : r ≤ δ := by
    dsimp [r]
    linarith
  let u : ℝ := max A (r - b + 1)
  have huA : A ≤ u := by
    exact le_max_left _ _
  have hstartu : -b + r < u := by
    have hu := le_max_right A (r - b + 1)
    dsimp [u] at hu ⊢
    linarith
  have hub : 0 < u + b := by
    linarith
  let v : ℝ := Real.exp 3 * (u + b) - b
  have hexp : 1 < Real.exp 3 := by
    exact Real.one_lt_exp_iff.mpr (by norm_num)
  have huv : u < v := by
    have hmul := mul_lt_mul_of_pos_right hexp hub
    dsimp [v]
    linarith
  have hvA : A ≤ v := huA.trans huv.le
  have hvb : 0 < v + b := by
    linarith
  have hleft : -A ≤ -A := le_rfl
  have huApprox :=
    hm (-A) u r hleft huA hr hrδ
  have hvApprox :=
    hm (-A) v r hleft hvA hr hrδ
  let C : ℝ :=
    ∫ x in (-A)..(-b - r), 1 / (x + b)
  let Iu : ℝ :=
    ∫ x in (-b + r)..u, 1 / (x + b)
  let Iv : ℝ :=
    ∫ x in (-b + r)..v, 1 / (x + b)
  have huApprox' : |C + Iu - L| < 1 := by
    simpa [C, Iu] using huApprox
  have hvApprox' : |C + Iv - L| < 1 := by
    simpa [C, Iv] using hvApprox
  have hdiff : |Iv - Iu| < 2 := by
    calc
      |Iv - Iu| =
          |(C + Iv - L) + -(C + Iu - L)| := by
            congr 1
            ring
      _ ≤ |C + Iv - L| + |-(C + Iu - L)| :=
        abs_add_le _ _
      _ = |C + Iv - L| + |C + Iu - L| := by
        rw [abs_neg]
      _ < 1 + 1 := add_lt_add hvApprox' huApprox'
      _ = 2 := by norm_num
  have hintStartU :
      IntervalIntegrable (fun x : ℝ => 1 / (x + b))
        volume (-b + r) u := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro x hx
      rw [uIcc_of_le hstartu.le] at hx
      intro hxb
      linarith [hx.1, hr]
    · exact (continuous_id.add continuous_const).continuousOn
  have hintUV :
      IntervalIntegrable (fun x : ℝ => 1 / (x + b))
        volume u v := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro x hx
      rw [uIcc_of_le huv.le] at hx
      intro hxb
      linarith [hx.1, hub]
    · exact (continuous_id.add continuous_const).continuousOn
  have hadd :
      (∫ x in (-b + r)..u, 1 / (x + b)) +
          (∫ x in u..v, 1 / (x + b)) =
        ∫ x in (-b + r)..v, 1 / (x + b) :=
    intervalIntegral.integral_add_adjacent_intervals
      hintStartU hintUV
  have huvb :
      (∫ x in u..v, 1 / (x + b)) = 3 := by
    have hlog :
        (∫ x in u..v, 1 / (x + b)) =
          Real.log (v + b) - Real.log (u + b) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x : ℝ => Real.log (x + b))
      · intro x hx
        rw [uIcc_of_le huv.le] at hx
        have hxb : x + b ≠ 0 := by
          intro hzero
          linarith [hx.1, hub]
        simpa [one_div] using
          (Real.hasDerivAt_log hxb).comp x
            ((hasDerivAt_id x).add_const b)
      · exact hintUV
    rw [hlog]
    rw [show v + b = Real.exp 3 * (u + b) by
      dsimp [v]
      ring]
    rw [Real.log_mul (Real.exp_ne_zero 3) (ne_of_gt hub),
      Real.log_exp]
    ring
  have hIvIu : Iv - Iu = 3 := by
    dsimp [Iv, Iu]
    linarith [hadd, huvb]
  rw [hIvIu] at hdiff
  norm_num at hdiff

private theorem principalValueAt_cosineKernel_zero (b : ℝ) :
    principalValueAt (cosineKernel 0 b) (-b) = 0 := by
  have hset :
      {L : ℝ | HasPrincipalValueAt (cosineKernel 0 b) (-b) L} =
        ∅ := by
    ext L
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact cosineKernel_zero_has_no_principal_value b L
  unfold principalValueAt
  rw [hset, Real.sInf_empty]

theorem gap1 (a b : ℝ) :
    principalValueAt (sineKernel a b) (-b) =
      principalValueAt (fun t : ℝ => Real.sin (a * (t - b)) / t) 0 := by
  by_cases ha : a = 0
  · subst a
    have hleft : HasPrincipalValueAt (sineKernel 0 b) (-b) 0 := by
      convert zero_hasPrincipalValue (-b) using 1
      funext x
      simp [sineKernel]
    have hright :
        HasPrincipalValueAt
          (fun t : ℝ => Real.sin (0 * (t - b)) / t) 0 0 := by
      simpa using zero_hasPrincipalValue 0
    rw [principalValueAt_eq_of_has hleft,
      principalValueAt_eq_of_has hright]
  · rw [principalValueAt_eq_of_has
        (sineKernel_hasPrincipalValue_nonzero a b ha),
      principalValueAt_eq_of_has
        (shiftedSine_hasPrincipalValue_nonzero a b ha)]

theorem gap2 (a b : ℝ) :
    principalValueAt (sineKernel a b) (-b) =
      principalValueAt
          (fun t : ℝ => Real.sin (a * t) * Real.cos (a * b) / t) 0 -
        principalValueAt
          (fun t : ℝ => Real.cos (a * t) * Real.sin (a * b) / t) 0 := by
  by_cases ha : a = 0
  · subst a
    have hleft : HasPrincipalValueAt (sineKernel 0 b) (-b) 0 := by
      convert zero_hasPrincipalValue (-b) using 1
      funext x
      simp [sineKernel]
    have hsine :
        HasPrincipalValueAt
          (fun t : ℝ =>
            Real.sin (0 * t) * Real.cos (0 * b) / t) 0 0 := by
      simpa using zero_hasPrincipalValue 0
    have hcosine :
        HasPrincipalValueAt
          (fun t : ℝ =>
            Real.cos (0 * t) * Real.sin (0 * b) / t) 0 0 := by
      simpa using zero_hasPrincipalValue 0
    rw [principalValueAt_eq_of_has hleft,
      principalValueAt_eq_of_has hsine,
      principalValueAt_eq_of_has hcosine]
    ring
  · rw [principalValueAt_eq_of_has
        (sineKernel_hasPrincipalValue_nonzero a b ha),
      principalValueAt_eq_of_has
        (scaledSine_hasPrincipalValue_nonzero
          a (Real.cos (a * b)) ha),
      principalValueAt_eq_of_has
        (scaledCosine_hasPrincipalValue_nonzero
          a (Real.sin (a * b)) ha)]
    ring

theorem gap3 (a b : ℝ) :
    principalValueAt (sineKernel a b) (-b) =
      2 * dirichletValue a * Real.cos (a * b) := by
  by_cases ha : a = 0
  · subst a
    have hleft : HasPrincipalValueAt (sineKernel 0 b) (-b) 0 := by
      convert zero_hasPrincipalValue (-b) using 1
      funext x
      simp [sineKernel]
    rw [principalValueAt_eq_of_has hleft, dirichletValue_eq]
    simp
  · rw [principalValueAt_eq_of_has
        (sineKernel_hasPrincipalValue_nonzero a b ha),
      dirichletValue_eq]
    ring

theorem gap4 (a b : ℝ) :
    principalValueAt (sineKernel a b) (-b) =
      Real.pi * (SignType.sign a : ℝ) * Real.cos (a * b) := by
  by_cases ha : a = 0
  · subst a
    have hleft : HasPrincipalValueAt (sineKernel 0 b) (-b) 0 := by
      convert zero_hasPrincipalValue (-b) using 1
      funext x
      simp [sineKernel]
    rw [principalValueAt_eq_of_has hleft]
    simp
  · rw [principalValueAt_eq_of_has
        (sineKernel_hasPrincipalValue_nonzero a b ha),
      signType_sign_eq_realSign]

theorem gap5 (a b : ℝ) :
    principalValueAt (cosineKernel a b) (-b) =
      Real.pi * (SignType.sign a : ℝ) * Real.sin (a * b) := by
  by_cases ha : a = 0
  · subst a
    rw [principalValueAt_cosineKernel_zero]
    simp
  · rw [principalValueAt_eq_of_has
        (cosineKernel_hasPrincipalValue_nonzero a b ha),
      signType_sign_eq_realSign]

end

end ProofGap.Exercise3824
