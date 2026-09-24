import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3593

noncomputable section

open Filter

abbrev Point2 := ℝ × ℝ

def productFunction (m n : ℝ) (q : Point2) : ℝ :=
  (1 + q.1) ^ m * (1 + q.2) ^ n

def xQuadratic (m : ℝ) (x : ℝ) : ℝ :=
  1 + m * x + m * (m - 1) / 2 * x ^ 2

def yQuadratic (n : ℝ) (y : ℝ) : ℝ :=
  1 + n * y + n * (n - 1) / 2 * y ^ 2

def separatedQuadratic (m n : ℝ) (q : Point2) : ℝ :=
  xQuadratic m q.1 * yQuadratic n q.2

def totalQuadratic (m n : ℝ) (q : Point2) : ℝ :=
  1 + m * q.1 + n * q.2 +
    (1 / 2 : ℝ) *
      (m * (m - 1) * q.1 ^ 2 + 2 * m * n * q.1 * q.2 +
        n * (n - 1) * q.2 ^ 2)

def AgreesToSecondOrder (g p : Point2 → ℝ) : Prop :=
  Asymptotics.IsLittleO (nhds (0, 0))
    (fun q => g q - p q)
    (fun q => ‖q‖ ^ 2)

private theorem one_add_rpow_second_order (a : ℝ) :
    (fun x : ℝ => (1 + x) ^ a - xQuadratic a x) =o[nhds 0]
      (fun x : ℝ => x ^ 2) := by
  let f : ℝ → ℝ := fun x => (1 + x) ^ a
  have hps :
      HasFPowerSeriesOnBall f (binomialSeries ℝ a) 0 1 := by
    simpa [f] using Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)
  have hf : ContDiffOn ℝ 2 f (Metric.eball 0 1) :=
    hps.analyticOnNhd.contDiffOn_of_completeSpace
  have ht := taylor_isLittleO (convex_eball (0 : ℝ) 1)
    (Metric.mem_eball_self (by norm_num : (0 : ENNReal) < 1)) hf
  rw [Metric.isOpen_eball.nhdsWithin_eq
    (Metric.mem_eball_self (by norm_num : (0 : ENNReal) < 1))] at ht
  have hiter (k : ℕ) :
      iteratedDeriv k f 0 =
        ∑ σ : Equiv.Perm (Fin k),
          (binomialSeries ℝ a k) (fun _ => (1 : ℝ)) := by
    unfold iteratedDeriv
    exact hps.iteratedFDeriv_eq_sum_of_completeSpace (fun _ => 1)
  have h0 : iteratedDeriv 0 f 0 = 1 := by
    rw [hiter]
    simp only [binomialSeries_apply, List.prod_ofFn, Fin.prod_const,
      one_pow, smul_eq_mul, mul_one]
    simp
  have h1 : iteratedDeriv 1 f 0 = a := by
    rw [hiter]
    simp only [binomialSeries_apply, List.prod_ofFn, Fin.prod_const,
      one_pow, smul_eq_mul, mul_one]
    simp
  have h2 : iteratedDeriv 2 f 0 = a * (a - 1) := by
    rw [hiter]
    simp only [binomialSeries_apply, List.prod_ofFn, Fin.prod_const,
      one_pow, smul_eq_mul, mul_one, Finset.sum_const, nsmul_eq_mul]
    norm_num
    have hc := Ring.choose_smul_choose (r := a) (n := 2) (k := 1)
      (by norm_num : 1 ≤ 2)
    simpa [nsmul_eq_mul, Ring.choose_one_right] using hc
  have heval :
      taylorWithinEval f 2 (Metric.eball 0 1) 0 =
        xQuadratic a := by
    funext x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [iteratedDerivWithin_of_isOpen_eq_iterate Metric.isOpen_eball
      (Metric.mem_eball_self (by norm_num : (0 : ENNReal) < 1))]
    rw [iteratedDerivWithin_of_isOpen_eq_iterate Metric.isOpen_eball
      (Metric.mem_eball_self (by norm_num : (0 : ENNReal) < 1))]
    rw [iteratedDerivWithin_of_isOpen_eq_iterate Metric.isOpen_eball
      (Metric.mem_eball_self (by norm_num : (0 : ENNReal) < 1))]
    rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate,
      ← iteratedDeriv_eq_iterate, h0, h1, h2]
    norm_num [xQuadratic]
    ring
  rw [heval] at ht
  simpa [f] using ht

private theorem separated_agrees (m n : ℝ) :
    AgreesToSecondOrder (productFunction m n) (separatedQuadratic m n) := by
  let l := nhds ((0, 0) : Point2)
  let N : Point2 → ℝ := fun q => ‖q‖ ^ 2
  have hxT : Tendsto (fun q : Point2 => q.1) l (nhds 0) := by
    simpa [l] using
      (continuous_fst.continuousAt :
        ContinuousAt (fun q : Point2 => q.1) (0, 0))
  have hyT : Tendsto (fun q : Point2 => q.2) l (nhds 0) := by
    simpa [l] using
      (continuous_snd.continuousAt :
        ContinuousAt (fun q : Point2 => q.2) (0, 0))
  have hxSqO :
      (fun q : Point2 => q.1 ^ 2) =O[l] N := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with q
    simp only [N, one_mul, norm_pow]
    have h := show ‖q.1‖ ≤ ‖q‖ by
      simp [Prod.norm_def]
    simpa [norm_norm] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hySqO :
      (fun q : Point2 => q.2 ^ 2) =O[l] N := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with q
    simp only [N, one_mul, norm_pow]
    have h := show ‖q.2‖ ≤ ‖q‖ by
      simp [Prod.norm_def]
    simpa [norm_norm] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hrxCoord :
      (fun q : Point2 => (1 + q.1) ^ m - xQuadratic m q.1)
        =o[l] (fun q => q.1 ^ 2) := by
    simpa [l, Function.comp_def] using
      (one_add_rpow_second_order m).comp_tendsto hxT
  have hryCoord :
      (fun q : Point2 => (1 + q.2) ^ n - yQuadratic n q.2)
        =o[l] (fun q => q.2 ^ 2) := by
    simpa [l, yQuadratic, xQuadratic, Function.comp_def] using
      (one_add_rpow_second_order n).comp_tendsto hyT
  have hrx :
      (fun q : Point2 => (1 + q.1) ^ m - xQuadratic m q.1)
        =o[l] N :=
    hrxCoord.trans_isBigO hxSqO
  have hry :
      (fun q : Point2 => (1 + q.2) ^ n - yQuadratic n q.2)
        =o[l] N :=
    hryCoord.trans_isBigO hySqO
  have hpowYT :
      Tendsto (fun q : Point2 => (1 + q.2) ^ n) l (nhds 1) := by
    have hbase :
        Tendsto (fun y : ℝ => (1 + y) ^ n) (nhds 0) (nhds 1) := by
      have hc :=
        (Real.one_add_rpow_hasFPowerSeriesAt_zero
          (a := n)).analyticAt.continuousAt
      change Tendsto (fun y : ℝ => (1 + y) ^ n) (nhds 0)
        (nhds ((1 + (0 : ℝ)) ^ n)) at hc
      simpa using hc
    exact hbase.comp hyT
  have hpolyXT :
      Tendsto (fun q : Point2 => xQuadratic m q.1) l (nhds 1) := by
    have hcont : Continuous (fun q : Point2 => xQuadratic m q.1) := by
      unfold xQuadratic
      fun_prop
    have hc :=
      (hcont.continuousAt :
        ContinuousAt (fun q : Point2 => xQuadratic m q.1) (0, 0))
    change Tendsto (fun q : Point2 => xQuadratic m q.1) l
      (nhds (xQuadratic m 0)) at hc
    simpa [xQuadratic] using hc
  have ht1 :
      (fun q : Point2 =>
        ((1 + q.1) ^ m - xQuadratic m q.1) * (1 + q.2) ^ n)
        =o[l] N := by
    simpa only [mul_one] using
      hrx.mul_isBigO (hpowYT.isBigO_one ℝ)
  have ht2 :
      (fun q : Point2 =>
        xQuadratic m q.1 * ((1 + q.2) ^ n - yQuadratic n q.2))
        =o[l] N := by
    simpa only [one_mul] using
      (hpolyXT.isBigO_one ℝ).mul_isLittleO hry
  have hsum := ht1.add ht2
  unfold AgreesToSecondOrder
  simpa [l, N, productFunction, separatedQuadratic] using
    (hsum.congr'
      (Filter.Eventually.of_forall fun q => by ring)
      (Filter.Eventually.of_forall fun q => by ring))

private theorem separated_to_total (m n : ℝ) :
    (fun q : Point2 => separatedQuadratic m n q - totalQuadratic m n q)
      =o[nhds (0, 0)] (fun q => ‖q‖ ^ 2) := by
  let l := nhds ((0, 0) : Point2)
  let N : Point2 → ℝ := fun q => ‖q‖ ^ 2
  have hxT : Tendsto (fun q : Point2 => q.1) l (nhds 0) := by
    simpa [l] using
      (continuous_fst.continuousAt :
        ContinuousAt (fun q : Point2 => q.1) (0, 0))
  have hyT : Tendsto (fun q : Point2 => q.2) l (nhds 0) := by
    simpa [l] using
      (continuous_snd.continuousAt :
        ContinuousAt (fun q : Point2 => q.2) (0, 0))
  have hxSqO :
      (fun q : Point2 => q.1 ^ 2) =O[l] N := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with q
    simp only [N, one_mul, norm_pow]
    have h := show ‖q.1‖ ≤ ‖q‖ by simp [Prod.norm_def]
    simpa [norm_norm] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hySqO :
      (fun q : Point2 => q.2 ^ 2) =O[l] N := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with q
    simp only [N, one_mul, norm_pow]
    have h := show ‖q.2‖ ≤ ‖q‖ by simp [Prod.norm_def]
    simpa [norm_norm] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hxSmall :
      (fun q : Point2 => q.1) =o[l] (fun _ => (1 : ℝ)) := by
    rw [Asymptotics.isLittleO_one_iff]
    exact hxT
  have hySmall :
      (fun q : Point2 => q.2) =o[l] (fun _ => (1 : ℝ)) := by
    rw [Asymptotics.isLittleO_one_iff]
    exact hyT
  have hxSqSmall :
      (fun q : Point2 => q.1 ^ 2) =o[l] (fun _ => (1 : ℝ)) := by
    rw [Asymptotics.isLittleO_one_iff]
    simpa using hxT.pow 2
  have h1 :
      (fun q : Point2 => q.1 ^ 2 * q.2) =o[l] N := by
    simpa only [mul_one] using hxSqO.mul_isLittleO hySmall
  have h2 :
      (fun q : Point2 => q.1 * q.2 ^ 2) =o[l] N := by
    simpa [mul_comm] using hySqO.mul_isLittleO hxSmall
  have h3 :
      (fun q : Point2 => q.1 ^ 2 * q.2 ^ 2) =o[l] N := by
    simpa only [mul_one, mul_comm] using hySqO.mul_isLittleO hxSqSmall
  have hsum :=
    ((h1.const_mul_left
      (m * (m - 1) / 2 * n)).add
      (h2.const_mul_left
        (m * (n * (n - 1) / 2)))).add
      (h3.const_mul_left
        (m * (m - 1) / 2 * (n * (n - 1) / 2)))
  simpa [l, N] using
    (hsum.congr'
      (Filter.Eventually.of_forall fun q => by
        unfold separatedQuadratic totalQuadratic xQuadratic yQuadratic
        ring)
      (Filter.Eventually.of_forall fun q => by ring))

theorem gap1 (m n : ℝ) :
    ∀ x y : ℝ, productFunction m n (x, y) =
      (1 + x) ^ m * (1 + y) ^ n := by
  intro x y
  rfl

theorem gap2 (m n : ℝ) :
    AgreesToSecondOrder (productFunction m n) (separatedQuadratic m n) := by
  exact separated_agrees m n

theorem gap3 (m n : ℝ) :
    AgreesToSecondOrder
      (fun q => (1 + q.1) ^ m * (1 + q.2) ^ n)
      (separatedQuadratic m n) := by
  simpa only [productFunction] using gap2 m n

theorem gap4 (m n : ℝ) :
    AgreesToSecondOrder (productFunction m n) (totalQuadratic m n) := by
  unfold AgreesToSecondOrder at *
  have h := (gap2 m n).add (separated_to_total m n)
  simpa only [sub_add_sub_cancel] using h

end

end ProofGap.Exercise3593
