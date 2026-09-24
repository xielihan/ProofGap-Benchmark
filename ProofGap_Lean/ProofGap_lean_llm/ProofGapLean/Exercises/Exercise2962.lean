import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2962

noncomputable section

open Filter

def integratedSawtooth (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    let n : ℕ := k + 1
    (-1 : ℝ) ^ n *
      (Real.cos ((n : ℝ) * x) - 1) / (n : ℝ) ^ 2

def alternatingZetaTwo : ℝ :=
  ∑' k : ℕ,
    let n : ℕ := k + 1
    (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2

def alternatingCosTwo (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    let n : ℕ := k + 1
    (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2

def alternatingSinOne (x : ℝ) : ℝ :=
  ∑'[SummationFilter.conditional ℕ] k : ℕ,
    let n : ℕ := k + 1
    (-1 : ℝ) ^ (n + 1) * Real.sin ((n : ℝ) * x) / (n : ℝ)

def alternatingSinThree (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    let n : ℕ := k + 1
    (-1 : ℝ) ^ n * Real.sin ((n : ℝ) * x) / (n : ℝ) ^ 3

def zetaTwo : ℝ :=
  ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2

def zetaFour : ℝ :=
  ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 4

def alternatingCosFour (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    let n : ℕ := k + 1
    (-1 : ℝ) ^ (n + 1) * Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 4

private theorem tail_hasSum_of_zero {f : ℕ → ℝ} {a : ℝ}
    (h : HasSum f a) (h0 : f 0 = 0) :
    HasSum (fun k : ℕ => f (k + 1)) a := by
  simpa [h0] using ((hasSum_nat_add_iff' 1).2 h)

private theorem conditional_tail_hasSum_of_zero {f : ℕ → ℝ} {a : ℝ}
    (h : HasSum f a (SummationFilter.conditional ℕ)) (h0 : f 0 = 0) :
    HasSum (fun k : ℕ => f (k + 1)) a
      (SummationFilter.conditional ℕ) := by
  have hpartial : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i)
      atTop (nhds a) := by
    simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
      Filter.tendsto_map'_iff, Function.comp_def] using h
  have hpartial' := hpartial.comp (tendsto_add_atTop_nat 1)
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  apply hpartial'.congr'
  filter_upwards with n
  simp only [Function.comp_apply, Finset.sum_range_succ', h0, add_zero]

set_option maxHeartbeats 800000 in
private theorem hasSum_taylorSeries_log_conditional {z : ℂ}
    (hz : ‖z‖ = 1) (hslit : 1 + z ∈ Complex.slitPlane) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * z ^ n / n)
      (Complex.log (1 + z)) (SummationFilter.conditional ℕ) := by
  letI : IsScalarTower ℝ ℂ ℂ := IsScalarTower.of_commMonoid ℝ ℂ
  have hcont : ContinuousOn (fun t : ℝ => ‖(1 + t • z)⁻¹‖)
      (Set.Icc 0 1) := (Complex.continuousOn_one_add_mul_inv hslit).norm
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (IsCompact.bddAbove_image isCompact_Icc hcont)
  have hC_bound {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖(1 + t • z)⁻¹‖ ≤ C := hC _ ⟨t, ht, rfl⟩
  have hC_nonneg : 0 ≤ C :=
    (norm_nonneg ((1 + (0 : ℝ) • z)⁻¹)).trans (hC_bound (by simp))
  have hrem (n : ℕ) :
      ‖Complex.log (1 + z) - Complex.logTaylor (n + 1) z‖ ≤
        C / (n + 1 : ℝ) := by
    let f (w : ℂ) : ℂ := Complex.log (1 + w) - Complex.logTaylor (n + 1) w
    let f' (w : ℂ) : ℂ := (-w) ^ n * (1 + w)⁻¹
    have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt f (f' (0 + t * z)) (0 + t * z) := by
      intro t ht
      rw [zero_add]
      exact Complex.hasDerivAt_log_sub_logTaylor n <|
        StarConvex.add_smul_mem Complex.starConvex_one_slitPlane hslit ht.1 ht.2
    have hcont' : ContinuousOn (fun t : ℝ => f' (0 + t * z))
        (Set.Icc 0 1) := by
      simp only [zero_add]
      exact (Continuous.continuousOn (by fun_prop)).mul <|
        Complex.continuousOn_one_add_mul_inv hslit
    have H : f z = z * ∫ t in (0 : ℝ)..1,
        (-(t * z)) ^ n * (1 + t * z)⁻¹ := by
      convert (intervalIntegral.integral_unitInterval_deriv_eq_sub hcont' hderiv).symm
        using 1
      · simp only [f, zero_add, add_zero, Complex.log_one,
          Complex.logTaylor_at_zero, sub_self, sub_zero]
      · simp only [f', Complex.real_smul, zero_add, smul_eq_mul]
      · exact IsScalarTower.of_commMonoid ℝ ℂ
    have hint : IntervalIntegrable (fun t : ℝ => t ^ n * C)
        MeasureTheory.volume 0 1 :=
      IntervalIntegrable.mul_const
        (Continuous.intervalIntegrable (by fun_prop) 0 1) C
    unfold f at H
    rw [H, norm_mul, hz, one_mul]
    calc
      ‖∫ t in (0 : ℝ)..1, (-(t * z)) ^ n * (1 + t * z)⁻¹‖
          ≤ ∫ t in (0 : ℝ)..1, t ^ n * C := by
            refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hint
            filter_upwards with t ht
            rw [norm_mul, norm_pow, norm_neg, norm_mul, hz, mul_one]
            simp only [Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg ht.1.le]
            exact mul_le_mul_of_nonneg_left
              (by simpa only [Complex.real_smul] using
                hC_bound ⟨ht.1.le, ht.2⟩)
              (pow_nonneg ht.1.le n)
      _ = C / (n + 1 : ℝ) := by
        rw [intervalIntegral.integral_mul_const, mul_comm,
          integral_pow]
        simp [field]
  have hbound_tendsto : Tendsto (fun n : ℕ => C / (n + 1 : ℝ))
      atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((tendsto_add_atTop_iff_nat 1).2
        (tendsto_const_div_atTop_nhds_zero_nat C))
  have hnorm : Tendsto
      (fun n : ℕ => ‖Complex.log (1 + z) -
        Complex.logTaylor (n + 1) z‖) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall hrem) hbound_tendsto
  have hlim_succ : Tendsto (fun n : ℕ => Complex.logTaylor (n + 1) z)
      atTop (nhds (Complex.log (1 + z))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hnorm
  have hlim : Tendsto (fun n : ℕ => Complex.logTaylor n z)
      atTop (nhds (Complex.log (1 + z))) :=
    (tendsto_add_atTop_iff_nat 1).1 hlim_succ
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa only [Function.comp_apply, Complex.logTaylor] using hlim

set_option maxHeartbeats 800000 in
private theorem alternatingCosTwo_hasSum {x : ℝ}
    (hx0 : -Real.pi ≤ x) (hx1 : x ≤ Real.pi) :
    HasSum (fun n : ℕ =>
      (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2)
      (x ^ 2 / 4 - Real.pi ^ 2 / 12) := by
  have hy : (x + Real.pi) / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith) (by positivity)
    · exact (div_le_one (by positivity)).2 (by linarith)
  have h := hasSum_one_div_nat_pow_mul_cos
    (k := 1) (by norm_num) hy
  convert h using 1
  · funext n
    have harg :
        2 * Real.pi * (n : ℝ) *
            ((x + Real.pi) / (2 * Real.pi)) =
          (n : ℝ) * x + (n : ℝ) * Real.pi := by
      field_simp [Real.pi_ne_zero]
    rw [harg, Real.cos_add_nat_mul_pi]
    ring
  · symm
    change
      ((-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 /
          (Nat.factorial (2 * 1) : ℝ) *
          bernoulliFun (2 * 1)
            ((x + Real.pi) / (2 * Real.pi))) =
        x ^ 2 / 4 - Real.pi ^ 2 / 12
    rw [bernoulliFun_two]
    norm_num [Nat.factorial]
    field_simp [Real.pi_ne_zero]
    ring

private theorem bernoulliFun_four_formula (x : ℝ) :
    bernoulliFun 4 x =
      x ^ 4 - 2 * x ^ 3 + x ^ 2 - 1 / 30 := by
  rw [bernoulliFun]
  norm_num [Polynomial.bernoulli, Finset.sum_range_succ,
    bernoulli_eq_bernoulli'_of_ne_one, Nat.factorial,
    show Nat.choose 4 2 = 6 by decide]
  ring

set_option maxHeartbeats 800000 in
private theorem alternatingCosFour_hasSum {x : ℝ}
    (hx0 : -Real.pi ≤ x) (hx1 : x ≤ Real.pi) :
    HasSum (fun n : ℕ =>
      (-1 : ℝ) ^ (n + 1) * Real.cos ((n : ℝ) * x) /
        (n : ℝ) ^ 4)
      (x ^ 4 / 48 - Real.pi ^ 2 * x ^ 2 / 24 +
        7 * Real.pi ^ 4 / 720) := by
  have hy : (x + Real.pi) / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith) (by positivity)
    · exact (div_le_one (by positivity)).2 (by linarith)
  have h := (hasSum_one_div_nat_pow_mul_cos
    (k := 2) (by norm_num) hy).neg
  convert h using 1
  · funext n
    have harg :
        2 * Real.pi * (n : ℝ) *
            ((x + Real.pi) / (2 * Real.pi)) =
          (n : ℝ) * x + (n : ℝ) * Real.pi := by
      field_simp [Real.pi_ne_zero]
    rw [harg, Real.cos_add_nat_mul_pi, pow_succ]
    ring
  · symm
    change
      -((-1 : ℝ) ^ (2 + 1) * (2 * Real.pi) ^ (2 * 2) / 2 /
          (Nat.factorial (2 * 2) : ℝ) *
          bernoulliFun (2 * 2)
            ((x + Real.pi) / (2 * Real.pi))) =
        x ^ 4 / 48 - Real.pi ^ 2 * x ^ 2 / 24 +
          7 * Real.pi ^ 4 / 720
    rw [bernoulliFun_four_formula]
    norm_num [Nat.factorial]
    field_simp [Real.pi_ne_zero]
    ring

private theorem alternatingCosTwo_tail_hasSum {x : ℝ}
    (hx0 : -Real.pi ≤ x) (hx1 : x ≤ Real.pi) :
    HasSum (fun k : ℕ =>
      let n := k + 1
      (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2)
      (x ^ 2 / 4 - Real.pi ^ 2 / 12) := by
  apply tail_hasSum_of_zero (alternatingCosTwo_hasSum hx0 hx1)
  norm_num

private theorem alternatingCosFour_tail_hasSum {x : ℝ}
    (hx0 : -Real.pi ≤ x) (hx1 : x ≤ Real.pi) :
    HasSum (fun k : ℕ =>
      let n := k + 1
      (-1 : ℝ) ^ (n + 1) * Real.cos ((n : ℝ) * x) /
        (n : ℝ) ^ 4)
      (x ^ 4 / 48 - Real.pi ^ 2 * x ^ 2 / 24 +
        7 * Real.pi ^ 4 / 720) := by
  apply tail_hasSum_of_zero (alternatingCosFour_hasSum hx0 hx1)
  norm_num

private theorem alternatingZetaTwo_hasSum :
    HasSum (fun n : ℕ =>
      (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2)
      (Real.pi ^ 2 / 12) := by
  have h := (alternatingCosTwo_hasSum
    (x := 0) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])).neg
  convert h using 1
  · funext n
    rw [mul_zero, Real.cos_zero, mul_one, pow_succ]
    ring
  · ring

private theorem alternatingZetaTwo_tail_hasSum :
    HasSum (fun k : ℕ =>
      let n := k + 1
      (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2)
      (Real.pi ^ 2 / 12) := by
  apply tail_hasSum_of_zero alternatingZetaTwo_hasSum
  norm_num

private theorem zetaTwo_tail_hasSum :
    HasSum (fun k : ℕ => 1 / (k + 1 : ℝ) ^ 2)
      (Real.pi ^ 2 / 6) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    tail_hasSum_of_zero hasSum_zeta_two (by norm_num)

private theorem zetaFour_tail_hasSum :
    HasSum (fun k : ℕ => 1 / (k + 1 : ℝ) ^ 4)
      (Real.pi ^ 4 / 90) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    tail_hasSum_of_zero hasSum_zeta_four (by norm_num)

set_option maxHeartbeats 800000 in
private theorem alternatingSinOne_hasSum {x : ℝ}
    (hx0 : -Real.pi < x) (hx1 : x < Real.pi) :
    HasSum (fun n : ℕ =>
      (-1 : ℝ) ^ (n + 1) * Real.sin ((n : ℝ) * x) / (n : ℝ))
      (x / 2) (SummationFilter.conditional ℕ) := by
  let z : ℂ := Complex.exp (x * Complex.I)
  have hz : ‖z‖ = 1 := by
    simp [z]
  have hhalf : x / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hcos : 0 < Real.cos (x / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  have hfactor :
      1 + z =
        (2 * Real.cos (x / 2) : ℝ) *
          (Real.cos (x / 2) + Real.sin (x / 2) * Complex.I) := by
    dsimp [z]
    rw [Complex.exp_ofReal_mul_I]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, zero_mul]
      rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul]
      ring
    · simp only [Complex.add_im, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        zero_add, mul_one, mul_zero, add_zero, zero_mul]
      rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul]
      ring
  have harg : Complex.arg (1 + z) = x / 2 := by
    rw [hfactor, Complex.ofReal_cos, Complex.ofReal_sin]
    exact Complex.arg_mul_cos_add_sin_mul_I
      (r := 2 * Real.cos (x / 2)) (θ := x / 2)
      (mul_pos (by norm_num) hcos) hhalf
  have hslit : 1 + z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    constructor
    · rw [harg]
      linarith
    · rw [hfactor]
      exact mul_ne_zero
        (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hcos.ne'))
        (by rw [← Complex.exp_ofReal_mul_I]; exact Complex.exp_ne_zero _)
  have hcomplex := hasSum_taylorSeries_log_conditional hz hslit
  have him := Complex.hasSum_im hcomplex
  convert him using 1
  · funext n
    have hpow : z ^ n =
        (Real.cos ((n : ℝ) * x) : ℂ) +
          (Real.sin ((n : ℝ) * x) : ℂ) * Complex.I := by
      calc
        z ^ n = Complex.exp
            ((((n : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
              dsimp [z]
              rw [← Complex.exp_nat_mul]
              congr 1
              push_cast
              ring
        _ = _ := Complex.exp_ofReal_mul_I ((n : ℝ) * x)
    have hsign : ((-1 : ℂ) ^ (n + 1)) =
        (((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) := by norm_cast
    rw [Complex.div_natCast_im, hsign, hpow]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, zero_mul, add_zero, mul_one, zero_add]
  · rw [Complex.log_im, harg]

private theorem alternatingSinOne_tail_hasSum {x : ℝ}
    (hx0 : -Real.pi < x) (hx1 : x < Real.pi) :
    HasSum (fun k : ℕ =>
      let n := k + 1
      (-1 : ℝ) ^ (n + 1) * Real.sin ((n : ℝ) * x) / (n : ℝ))
      (x / 2) (SummationFilter.conditional ℕ) := by
  apply conditional_tail_hasSum_of_zero (alternatingSinOne_hasSum hx0 hx1)
  norm_num

private theorem bernoulliFun_three_formula (x : ℝ) :
    bernoulliFun 3 x = x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x := by
  rw [bernoulliFun]
  norm_num [Polynomial.bernoulli, Finset.sum_range_succ,
    bernoulli_eq_bernoulli'_of_ne_one, Nat.factorial,
    show Nat.choose 3 2 = 3 by decide]
  ring

set_option maxHeartbeats 800000 in
private theorem alternatingSinThree_hasSum {x : ℝ}
    (hx0 : -Real.pi ≤ x) (hx1 : x ≤ Real.pi) :
    HasSum (fun n : ℕ =>
      (-1 : ℝ) ^ n * Real.sin ((n : ℝ) * x) / (n : ℝ) ^ 3)
      (x ^ 3 / 12 - Real.pi ^ 2 * x / 12) := by
  have hy : (x + Real.pi) / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith) (by positivity)
    · exact (div_le_one (by positivity)).2 (by linarith)
  have h := hasSum_one_div_nat_pow_mul_sin
    (k := 1) (by norm_num) hy
  convert h using 1
  · funext n
    have harg :
        2 * Real.pi * (n : ℝ) *
            ((x + Real.pi) / (2 * Real.pi)) =
          (n : ℝ) * x + (n : ℝ) * Real.pi := by
      field_simp [Real.pi_ne_zero]
    rw [harg, Real.sin_add_nat_mul_pi]
    ring
  · symm
    change
      ((-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1 + 1) / 2 /
          (Nat.factorial (2 * 1 + 1) : ℝ) *
          bernoulliFun (2 * 1 + 1)
            ((x + Real.pi) / (2 * Real.pi))) =
        x ^ 3 / 12 - Real.pi ^ 2 * x / 12
    rw [bernoulliFun_three_formula]
    norm_num [Nat.factorial]
    field_simp [Real.pi_ne_zero]
    ring

private theorem alternatingSinThree_tail_hasSum {x : ℝ}
    (hx0 : -Real.pi ≤ x) (hx1 : x ≤ Real.pi) :
    HasSum (fun k : ℕ =>
      let n := k + 1
      (-1 : ℝ) ^ n * Real.sin ((n : ℝ) * x) / (n : ℝ) ^ 3)
      (x ^ 3 / 12 - Real.pi ^ 2 * x / 12) := by
  apply tail_hasSum_of_zero (alternatingSinThree_hasSum hx0 hx1)
  norm_num

theorem gap1 :
    ∀ x, -Real.pi < x → x < Real.pi →
      x ^ 2 / 2 = 2 * integratedSawtooth x := by
  intro x hx0 hx1
  have hsum :=
    (alternatingCosTwo_tail_hasSum hx0.le hx1.le).add
      alternatingZetaTwo_tail_hasSum
  have hintegrated :
      HasSum (fun k : ℕ =>
        let n := k + 1
        (-1 : ℝ) ^ n *
          (Real.cos ((n : ℝ) * x) - 1) / (n : ℝ) ^ 2)
        (x ^ 2 / 4) := by
    convert hsum using 1
    · funext k
      dsimp only
      rw [pow_succ]
      ring
    · ring
  unfold integratedSawtooth
  rw [hintegrated.tsum_eq]
  ring

theorem gap2 :
    alternatingZetaTwo = Real.pi ^ 2 / 12 := by
  exact alternatingZetaTwo_tail_hasSum.tsum_eq

theorem gap3 :
    ∀ x, -Real.pi < x → x < Real.pi →
      x ^ 2 =
        Real.pi ^ 2 / 3 + 4 * alternatingCosTwo x := by
  intro x hx0 hx1
  unfold alternatingCosTwo
  rw [(alternatingCosTwo_tail_hasSum hx0.le hx1.le).tsum_eq]
  ring

theorem gap4 :
    ∀ x, -Real.pi < x → x < Real.pi →
      x ^ 3 =
        2 * Real.pi ^ 2 * alternatingSinOne x +
          12 * alternatingSinThree x := by
  intro x hx0 hx1
  unfold alternatingSinOne alternatingSinThree
  rw [(alternatingSinOne_tail_hasSum hx0 hx1).tsum_eq,
    (alternatingSinThree_tail_hasSum hx0.le hx1.le).tsum_eq]
  ring

theorem gap5 :
    zetaTwo = Real.pi ^ 2 / 6 := by
  exact zetaTwo_tail_hasSum.tsum_eq

theorem gap6 :
    zetaFour = Real.pi ^ 4 / 90 := by
  exact zetaFour_tail_hasSum.tsum_eq

theorem gap7 :
    ∀ x, -Real.pi ≤ x → x ≤ Real.pi →
      x ^ 4 / 4 - Real.pi ^ 4 / 4 =
        2 * Real.pi ^ 2 * alternatingCosTwo x -
          2 * Real.pi ^ 2 * (Real.pi ^ 2 / 6) +
          12 * alternatingCosFour x +
          12 * (Real.pi ^ 4 / 90) := by
  intro x hx0 hx1
  unfold alternatingCosTwo alternatingCosFour
  rw [(alternatingCosTwo_tail_hasSum hx0 hx1).tsum_eq,
    (alternatingCosFour_tail_hasSum hx0 hx1).tsum_eq]
  ring

theorem gap8 :
    ∀ x, -Real.pi ≤ x → x ≤ Real.pi →
      x ^ 4 =
        Real.pi ^ 4 / 5 +
          8 * Real.pi ^ 2 * alternatingCosTwo x +
          48 * alternatingCosFour x := by
  intro x hx0 hx1
  unfold alternatingCosTwo alternatingCosFour
  rw [(alternatingCosTwo_tail_hasSum hx0 hx1).tsum_eq,
    (alternatingCosFour_tail_hasSum hx0 hx1).tsum_eq]
  ring

end

end ProofGap.Exercise2962
