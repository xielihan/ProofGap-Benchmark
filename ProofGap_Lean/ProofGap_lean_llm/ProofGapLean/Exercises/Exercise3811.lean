import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3811

noncomputable section

open MeasureTheory

def fourierGaussian (b x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2)) * Real.cos (2 * b * x)

def moment (n : ℕ) (b : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    x ^ (2 * n) * Real.exp (-(x ^ 2)) * Real.cos (2 * b * x)

private lemma iteratedDeriv_cos_phase (k : ℕ) :
    iteratedDeriv k Real.cos =
      fun y : ℝ => Real.cos (y + (k : ℝ) * Real.pi / 2) := by
  induction k with
  | zero =>
      ext y
      simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      ext y
      have hd :
          HasDerivAt
            (fun z : ℝ => Real.cos (z + (k : ℝ) * Real.pi / 2))
            (-Real.sin (y + (k : ℝ) * Real.pi / 2)) y :=
        by
          simpa only [Function.comp_apply, id_eq, mul_one] using
            (Real.hasDerivAt_cos
              (y + (k : ℝ) * Real.pi / 2)).comp y
                ((hasDerivAt_id y).add_const ((k : ℝ) * Real.pi / 2))
      rw [hd.deriv]
      rw [show
          y + ((k + 1 : ℕ) : ℝ) * Real.pi / 2 =
            (y + (k : ℝ) * Real.pi / 2) + Real.pi / 2 by
          push_cast
          ring]
      rw [Real.cos_add_pi_div_two]

private lemma iteratedDeriv_fourierGaussian
    (k : ℕ) (b x : ℝ) :
    iteratedDeriv k (fun y : ℝ => fourierGaussian y x) b =
      (2 : ℝ) ^ k * x ^ k * Real.exp (-(x ^ 2)) *
        Real.cos (2 * b * x + (k : ℝ) * Real.pi / 2) := by
  have hfun :
      (fun y : ℝ => fourierGaussian y x) =
        fun y : ℝ => Real.exp (-(x ^ 2)) * Real.cos ((2 * x) * y) := by
    funext y
    simp only [fourierGaussian]
    congr 2
    ring
  rw [hfun, iteratedDeriv_const_mul
    (Real.exp (-(x ^ 2)))
    (by fun_prop :
      ContDiffAt ℝ (k : WithTop ℕ∞)
        (fun y : ℝ => Real.cos ((2 * x) * y)) b)]
  · rw [iteratedDeriv_comp_const_mul Real.contDiff_cos]
    rw [iteratedDeriv_cos_phase]
    simp only [Pi.mul_apply]
    ring

private lemma integrable_fourierGaussian (b : ℝ) :
    Integrable (fourierGaussian b) := by
  apply (integrable_exp_neg_mul_sq (b := (1 : ℝ)) zero_lt_one).mono'
  · unfold fourierGaussian
    fun_prop
  · filter_upwards with x
    unfold fourierGaussian
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    simpa only [neg_mul, one_mul, mul_one] using
      mul_le_mul_of_nonneg_left
        (abs_le.mpr ⟨Real.neg_one_le_cos (2 * b * x),
          Real.cos_le_one (2 * b * x)⟩)
        (Real.exp_pos (-(x ^ 2))).le

private lemma integral_fourierGaussian_univ (b : ℝ) :
    (∫ x : ℝ, fourierGaussian b x) =
      Real.sqrt Real.pi * Real.exp (-(b ^ 2)) := by
  let cf : ℝ → ℂ := fun x =>
    Complex.exp (Complex.I * (2 * b : ℂ) * (x : ℂ)) *
      Complex.exp (-(1 : ℂ) * (x : ℂ) ^ 2)
  have hcf : Integrable cf := by
    have hq := integrable_cexp_quadratic
      (b := (1 : ℂ)) (by norm_num)
      (Complex.I * (2 * b : ℂ)) 0
    refine hq.congr (Filter.Eventually.of_forall (fun x => ?_))
    dsimp [cf]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hfourier :=
    fourierIntegral_gaussian
      (b := (1 : ℂ)) (by norm_num) (2 * b : ℂ)
  have hcpow :
      ((Real.pi : ℂ) ^ (1 / 2 : ℂ)) =
        (Real.sqrt Real.pi : ℂ) := by
    calc
      ((Real.pi : ℂ) ^ (1 / 2 : ℂ)) =
          ((Real.pi : ℂ) ^ (((1 / 2 : ℝ) : ℂ))) := by norm_num
      _ = ((Real.pi ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow Real.pi_pos.le (1 / 2 : ℝ)).symm
      _ = (Real.sqrt Real.pi : ℂ) := by rw [← Real.sqrt_eq_rpow]
  calc
    (∫ x : ℝ, fourierGaussian b x) =
        ∫ x : ℝ, (cf x).re := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      dsimp [cf, fourierGaussian]
      rw [show
          Complex.I * (2 * b : ℂ) * (x : ℂ) =
            ((2 * b * x : ℝ) : ℂ) * Complex.I by
          push_cast
          ring]
      rw [Complex.exp_mul_I]
      rw [show
          -(1 : ℂ) * (x : ℂ) ^ 2 =
            ((-(x ^ 2) : ℝ) : ℂ) by
          push_cast
          ring]
      simp only [Complex.mul_re, Complex.add_re, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re, Complex.I_re, mul_zero, add_zero,
        Complex.add_im, Complex.cos_ofReal_im, Complex.sin_ofReal_im,
        Complex.I_im, zero_add, mul_one, Complex.exp_ofReal_re,
        Complex.exp_ofReal_im, sub_zero, zero_mul]
      ring
    _ = (∫ x : ℝ, cf x).re := integral_re hcf
    _ = (((Real.pi : ℂ) / 1) ^ (1 / 2 : ℂ) *
          Complex.exp (-(2 * b : ℂ) ^ 2 / (4 * 1))).re := by
      rw [hfourier]
    _ = Real.sqrt Real.pi * Real.exp (-(b ^ 2)) := by
      rw [div_one, hcpow]
      simp only [mul_one]
      rw [show
          -(2 * b : ℂ) ^ 2 / (4 : ℂ) =
            ((-(b ^ 2) : ℝ) : ℂ) by
          push_cast
          ring]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.exp_ofReal_re]

private lemma monomial_cos_bound
    (x : ℝ) (k : ℕ) (b : ℝ) (hx : 0 ≤ x) :
    |x ^ k * Real.exp (-(x ^ 2)) *
      Real.cos (2 * b * x + (k : ℝ) * Real.pi / 2)| ≤
        x ^ k * Real.exp (-(x ^ 2)) := by
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hx k),
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right
    (mul_nonneg (pow_nonneg hx k) (Real.exp_pos _).le)
    (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

private lemma integrableOn_monomial_gaussian (k : ℕ) :
    IntegrableOn
      (fun x : ℝ => x ^ k * Real.exp (-(x ^ 2)))
      (Set.Ioi (0 : ℝ)) := by
  simpa only [Real.rpow_natCast, neg_mul, one_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1 : ℝ)) zero_lt_one
      (s := (k : ℝ))
      (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k)))

private lemma integrableOn_iterated_fourierGaussian
    (k : ℕ) (b : ℝ) :
    IntegrableOn
      (fun x : ℝ =>
        iteratedDeriv k (fun y : ℝ => fourierGaussian y x) b)
      (Set.Ioi (0 : ℝ)) := by
  have hmajor :
      IntegrableOn
        (fun x : ℝ =>
          (2 : ℝ) ^ k * (x ^ k * Real.exp (-(x ^ 2))))
        (Set.Ioi (0 : ℝ)) :=
    (integrableOn_monomial_gaussian k).const_mul ((2 : ℝ) ^ k)
  apply hmajor.mono'
  · have heq :
        (fun x : ℝ =>
          iteratedDeriv k (fun y : ℝ => fourierGaussian y x) b) =
            fun x : ℝ =>
              (2 : ℝ) ^ k * x ^ k * Real.exp (-(x ^ 2)) *
                Real.cos (2 * b * x + (k : ℝ) * Real.pi / 2) := by
        funext x
        exact iteratedDeriv_fourierGaussian k b x
    rw [heq]
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with x hx
    rw [iteratedDeriv_fourierGaussian]
    have hbound := monomial_cos_bound x k b hx.le
    rw [show
        (2 : ℝ) ^ k * x ^ k * Real.exp (-(x ^ 2)) *
            Real.cos (2 * b * x + (k : ℝ) * Real.pi / 2) =
          (2 : ℝ) ^ k *
            (x ^ k * Real.exp (-(x ^ 2)) *
              Real.cos (2 * b * x + (k : ℝ) * Real.pi / 2)) by
        ring]
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)]
    exact mul_le_mul_of_nonneg_left hbound
      (pow_nonneg (by norm_num) k)

private lemma hasDerivAt_integral_iterated_fourierGaussian
    (k : ℕ) (b : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        ∫ x in Set.Ioi (0 : ℝ),
          iteratedDeriv k (fun z : ℝ => fourierGaussian z x) y)
      (∫ x in Set.Ioi (0 : ℝ),
        iteratedDeriv (k + 1) (fun z : ℝ => fourierGaussian z x) b) b := by
  let F : ℝ → ℝ → ℝ := fun y x =>
    iteratedDeriv k (fun z : ℝ => fourierGaussian z x) y
  let F' : ℝ → ℝ → ℝ := fun y x =>
    iteratedDeriv (k + 1) (fun z : ℝ => fourierGaussian z x) y
  let bound : ℝ → ℝ := fun x =>
    (2 : ℝ) ^ (k + 1) * (x ^ (k + 1) * Real.exp (-(x ^ 2)))
  have hbound_int :
      Integrable bound (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact
      (integrableOn_monomial_gaussian (k + 1)).const_mul
        ((2 : ℝ) ^ (k + 1))
  refine
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (F := F) (F' := F') (bound := bound) (s := Set.univ)
      Filter.univ_mem ?_ ?_ ?_ ?_ hbound_int ?_).2
  · filter_upwards with y
    have heq :
        F y = fun x : ℝ =>
          (2 : ℝ) ^ k * x ^ k * Real.exp (-(x ^ 2)) *
            Real.cos (2 * y * x + (k : ℝ) * Real.pi / 2) := by
      funext x
      exact iteratedDeriv_fourierGaussian k y x
    rw [heq]
    fun_prop
  · exact integrableOn_iterated_fourierGaussian k b
  · have heq :
        F' b = fun x : ℝ =>
          (2 : ℝ) ^ (k + 1) * x ^ (k + 1) *
            Real.exp (-(x ^ 2)) *
              Real.cos (2 * b * x + ((k + 1 : ℕ) : ℝ) * Real.pi / 2) := by
      funext x
      exact iteratedDeriv_fourierGaussian (k + 1) b x
    rw [heq]
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with x hx y hy
    have hpoint := monomial_cos_bound x (k + 1) y hx.le
    dsimp [F', bound]
    rw [iteratedDeriv_fourierGaussian]
    rw [show
        (2 : ℝ) ^ (k + 1) * x ^ (k + 1) * Real.exp (-(x ^ 2)) *
            Real.cos (2 * y * x + ((k + 1 : ℕ) : ℝ) * Real.pi / 2) =
          (2 : ℝ) ^ (k + 1) *
            (x ^ (k + 1) * Real.exp (-(x ^ 2)) *
              Real.cos
                (2 * y * x + ((k + 1 : ℕ) : ℝ) * Real.pi / 2)) by
        ring]
    rw [abs_mul,
      abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (k + 1))]
    exact mul_le_mul_of_nonneg_left hpoint
      (pow_nonneg (by norm_num) (k + 1))
  · filter_upwards with x y hy
    have hsmooth :
        ContDiff ℝ (⊤ : WithTop ℕ∞)
          (fun z : ℝ => fourierGaussian z x) := by
      unfold fourierGaussian
      fun_prop
    have hd :
        DifferentiableAt ℝ
          (iteratedDeriv k (fun z : ℝ => fourierGaussian z x)) y :=
      (hsmooth.differentiable_iteratedDeriv k (by simp)) y
    dsimp [F, F']
    convert hd.hasDerivAt using 1
    rw [iteratedDeriv_succ]

private lemma iteratedDeriv_integral_fourierGaussian
    (k : ℕ) (b : ℝ) :
    iteratedDeriv k
        (fun y : ℝ => ∫ x in Set.Ioi (0 : ℝ), fourierGaussian y x) b =
      ∫ x in Set.Ioi (0 : ℝ),
        iteratedDeriv k (fun y : ℝ => fourierGaussian y x) b := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have heq :
          iteratedDeriv k
              (fun y : ℝ =>
                ∫ x in Set.Ioi (0 : ℝ), fourierGaussian y x) =
            fun y : ℝ =>
              ∫ x in Set.Ioi (0 : ℝ),
                iteratedDeriv k (fun z : ℝ => fourierGaussian z x) y := by
        funext y
        exact ih y
      rw [heq]
      exact (hasDerivAt_integral_iterated_fourierGaussian k b).deriv

theorem gap1 (n : ℕ) (hn : 0 < n) (b : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), fourierGaussian b x) =
      Real.sqrt Real.pi / 2 * Real.exp (-(b ^ 2)) := by
  have hfull := MeasureTheory.integral_add_compl
    (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      (integrable_fourierGaussian b)
  rw [Set.compl_Ioi] at hfull
  have heven :
      (∫ x in Set.Iic (0 : ℝ), fourierGaussian b x) =
        ∫ x in Set.Ioi (0 : ℝ), fourierGaussian b x := by
    have hneg := integral_comp_neg_Ioi (0 : ℝ) (fourierGaussian b)
    simp only [neg_zero] at hneg
    calc
      (∫ x in Set.Iic (0 : ℝ), fourierGaussian b x) =
          ∫ x in Set.Ioi (0 : ℝ), fourierGaussian b (-x) := hneg.symm
      _ = ∫ x in Set.Ioi (0 : ℝ), fourierGaussian b x := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [fourierGaussian]
  rw [heven, integral_fourierGaussian_univ b] at hfull
  linarith

theorem gap2 (k : ℕ) (b : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ),
      iteratedDeriv k (fun y : ℝ => fourierGaussian y x) b) =
        (2 : ℝ) ^ k *
          ∫ x in Set.Ioi (0 : ℝ),
            x ^ k * Real.exp (-(x ^ 2)) *
              Real.cos (2 * b * x + (k : ℝ) * Real.pi / 2) := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [iteratedDeriv_fourierGaussian]
  ring

theorem gap3 (x : ℝ) (k : ℕ) (b : ℝ) (hx : 0 ≤ x) :
    |x ^ k * Real.exp (-(x ^ 2)) *
      Real.cos (2 * b * x + (k : ℝ) * Real.pi / 2)| ≤
        x ^ k * Real.exp (-(x ^ 2)) := by
  exact monomial_cos_bound x k b hx

theorem gap4 (k : ℕ) :
    IntegrableOn
      (fun x : ℝ => x ^ k * Real.exp (-(x ^ 2)))
      (Set.Ioi (0 : ℝ)) := by
  exact integrableOn_monomial_gaussian k

theorem gap5 (n : ℕ) (hn : 0 < n) (b : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ),
      iteratedDeriv (2 * n) (fun y : ℝ => fourierGaussian y x) b) =
        ∫ x in Set.Ioi (0 : ℝ),
          (2 : ℝ) ^ (2 * n) * x ^ (2 * n) *
            Real.exp (-(x ^ 2)) *
            Real.cos (2 * b * x + (n : ℝ) * Real.pi) := by
  rw [gap2 (2 * n) b, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  have hphase :
      2 * b * x + ((2 * n : ℕ) : ℝ) * Real.pi / 2 =
        2 * b * x + (n : ℝ) * Real.pi := by
    push_cast
    ring
  rw [hphase]
  ring

theorem gap6 (n : ℕ) (hn : 0 < n) (b : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ),
      iteratedDeriv (2 * n) (fun y : ℝ => fourierGaussian y x) b) =
        (2 : ℝ) ^ (2 * n) * (-1 : ℝ) ^ n * moment n b := by
  rw [gap5 n hn b]
  unfold moment
  have hcos (x : ℝ) :
      Real.cos (2 * b * x + (n : ℝ) * Real.pi) =
        (-1 : ℝ) ^ n * Real.cos (2 * b * x) := by
    simpa only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_id] using
      Real.cos_add_nat_mul_pi (2 * b * x) n
  simp_rw [hcos]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  ring

theorem gap7 (n : ℕ) (hn : 0 < n) (b : ℝ) :
    (2 : ℝ) ^ (2 * n) * (-1 : ℝ) ^ n * moment n b =
      Real.sqrt Real.pi / 2 *
        iteratedDeriv (2 * n) (fun y : ℝ => Real.exp (-(y ^ 2))) b := by
  calc
    (2 : ℝ) ^ (2 * n) * (-1 : ℝ) ^ n * moment n b =
        ∫ x in Set.Ioi (0 : ℝ),
          iteratedDeriv (2 * n)
            (fun y : ℝ => fourierGaussian y x) b :=
      (gap6 n hn b).symm
    _ = iteratedDeriv (2 * n)
          (fun y : ℝ =>
            ∫ x in Set.Ioi (0 : ℝ), fourierGaussian y x) b :=
      (iteratedDeriv_integral_fourierGaussian (2 * n) b).symm
    _ = iteratedDeriv (2 * n)
          (fun y : ℝ =>
            Real.sqrt Real.pi / 2 * Real.exp (-(y ^ 2))) b := by
      congr 1
      funext y
      exact gap1 1 (by norm_num) y
    _ = Real.sqrt Real.pi / 2 *
          iteratedDeriv (2 * n)
            (fun y : ℝ => Real.exp (-(y ^ 2))) b := by
      rw [iteratedDeriv_const_mul_field]

theorem gap8 (n : ℕ) (hn : 0 < n) (b : ℝ) :
    moment n b =
      (-1 : ℝ) ^ n * Real.sqrt Real.pi / (2 : ℝ) ^ (2 * n + 1) *
        iteratedDeriv (2 * n) (fun y : ℝ => Real.exp (-(y ^ 2))) b := by
  let D :=
    iteratedDeriv (2 * n) (fun y : ℝ => Real.exp (-(y ^ 2))) b
  have hA : (2 : ℝ) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsquare :
      (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    calc
      (-1 : ℝ) ^ n * (-1 : ℝ) ^ n =
          (-1 : ℝ) ^ (n + n) := (pow_add _ n n).symm
      _ = (-1 : ℝ) ^ (2 * n) := by rw [two_mul]
      _ = ((-1 : ℝ) ^ 2) ^ n := by rw [pow_mul]
      _ = 1 := by norm_num
  have hmain :
      (2 : ℝ) ^ (2 * n) * (-1 : ℝ) ^ n * moment n b =
        Real.sqrt Real.pi / 2 * D := by
    simpa only [D] using gap7 n hn b
  have hpow :
      (2 : ℝ) ^ (2 * n + 1) = 2 * (2 : ℝ) ^ (2 * n) := by
    rw [pow_succ]
    ring
  rw [hpow, div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero (by norm_num) hA)).2
  calc
    moment n b * (2 * (2 : ℝ) ^ (2 * n)) =
        2 * (2 : ℝ) ^ (2 * n) *
          ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * moment n b := by
      rw [hsquare]
      ring
    _ = 2 * (-1 : ℝ) ^ n *
          ((2 : ℝ) ^ (2 * n) * (-1 : ℝ) ^ n * moment n b) := by
      ring
    _ = 2 * (-1 : ℝ) ^ n *
          (Real.sqrt Real.pi / 2 * D) := by rw [hmain]
    _ = (-1 : ℝ) ^ n * Real.sqrt Real.pi * D := by ring

end

end ProofGap.Exercise3811
