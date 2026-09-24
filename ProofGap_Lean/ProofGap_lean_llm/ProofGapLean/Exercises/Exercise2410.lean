import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2410
noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Interval

def block (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k *
    ∫ x in (k : ℝ) * Real.pi..((k : ℝ) + 1) * Real.pi,
      Real.exp (-x) * Real.sin x

def partialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), block k

def S : ℝ :=
  ∫ x in Ioi (0 : ℝ), Real.exp (-x) * |Real.sin x|

def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x
def primitive (x : ℝ) : ℝ :=
  -Real.exp (-x) * (Real.sin x + Real.cos x) / 2

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (Real.exp (-x) * Real.sin x) x := by
  have he : HasDerivAt (fun y : ℝ => -Real.exp (-y)) (Real.exp (-x)) x := by
    convert ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).neg using 1 <;> ring
  have htrig :
      HasDerivAt (fun y : ℝ => Real.sin y + Real.cos y)
        (Real.cos x - Real.sin x) x := by
    convert (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x) using 1 <;> ring
  have h := (he.mul htrig).div_const 2
  convert h using 1 <;> ring

private theorem abs_sin_on_block (k : ℕ) (x : ℝ)
    (hx : x ∈ Icc ((k : ℝ) * Real.pi) (((k : ℝ) + 1) * Real.pi)) :
    |Real.sin x| = (-1 : ℝ) ^ k * Real.sin x := by
  have h0 : 0 ≤ x - (k : ℝ) * Real.pi := sub_nonneg.mpr hx.1
  have hpi : x - (k : ℝ) * Real.pi ≤ Real.pi := by
    calc
      x - (k : ℝ) * Real.pi ≤
          ((k : ℝ) + 1) * Real.pi - (k : ℝ) * Real.pi :=
        sub_le_sub_right hx.2 _
      _ = Real.pi := by ring
  have hs : 0 ≤ Real.sin (x - (k : ℝ) * Real.pi) :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 hpi
  have hnonneg : 0 ≤ (-1 : ℝ) ^ k * Real.sin x := by
    simpa only [Real.sin_sub_nat_mul_pi] using hs
  calc
    |Real.sin x| = |(-1 : ℝ) ^ k * Real.sin x| := by
      rw [abs_mul]
      simp
    _ = (-1 : ℝ) ^ k * Real.sin x := abs_of_nonneg hnonneg

private theorem abs_block_integral_eq_block (k : ℕ) :
    (∫ x in (k : ℝ) * Real.pi..((k : ℝ) + 1) * Real.pi,
        Real.exp (-x) * |Real.sin x|) = block k := by
  have hab : (k : ℝ) * Real.pi ≤ ((k : ℝ) + 1) * Real.pi := by
    nlinarith [Real.pi_pos]
  unfold block
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  change Real.exp (-x) * |Real.sin x| =
    (-1 : ℝ) ^ k * (Real.exp (-x) * Real.sin x)
  rw [abs_sin_on_block k x hx]
  ring

private theorem abs_integrand_integrableOn :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * |Real.sin x|)
      (Ioi (0 : ℝ)) := by
  apply Integrable.mono' (integrableOn_exp_neg_Ioi 0)
  · exact ((Real.continuous_exp.comp continuous_neg).mul
      Real.continuous_sin.abs).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x)
        (Real.exp_pos (-x)).le)

private theorem exp_neg_nat_mul_pi (k : ℕ) :
    Real.exp (-(k : ℝ) * Real.pi) = Real.exp (-Real.pi) ^ k := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem exp_neg_succ_mul_pi (k : ℕ) :
    Real.exp (-((k : ℝ) + 1) * Real.pi) =
      Real.exp (-Real.pi) ^ (k + 1) := by
  rw [show -((k : ℝ) + 1) * Real.pi =
    -((k + 1 : ℕ) : ℝ) * Real.pi by norm_num]
  exact exp_neg_nat_mul_pi (k + 1)

private theorem geometric_exp_sum (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.exp (-(k : ℝ) * Real.pi) =
      (1 - Real.exp (-(n : ℝ) * Real.pi)) /
        (1 - Real.exp (-Real.pi)) := by
  simp_rw [exp_neg_nat_mul_pi]
  have hq : Real.exp (-Real.pi) ≠ 1 := by
    intro h
    have hzero : -Real.pi = 0 := Real.exp_injective (by simpa using h)
    exact (neg_ne_zero.mpr Real.pi_ne_zero) hzero
  rw [geom_sum_eq hq]
  field_simp [sub_ne_zero.mpr hq, sub_ne_zero.mpr hq.symm]
  ring

theorem gap1 (x : ℝ) (hx : Real.sin x = 0) :
    ∃ k : ℤ, x = (k : ℝ) * Real.pi := by
  rcases Real.sin_eq_zero_iff.mp hx with ⟨k, hk⟩
  exact ⟨k, hk.symm⟩

theorem gap2 (n : ℕ) :
    (∫ x in (0 : ℝ)..((n : ℝ) + 1) * Real.pi,
      Real.exp (-x) * |Real.sin x|) = partialSum n := by
  let f : ℝ → ℝ := fun x => Real.exp (-x) * |Real.sin x|
  have hfcont : Continuous f :=
    (Real.continuous_exp.comp continuous_neg).mul Real.continuous_sin.abs
  induction n with
  | zero =>
      simpa [f, partialSum] using abs_block_integral_eq_block 0
  | succ n ih =>
      have hleft : IntervalIntegrable f volume
          0 (((n : ℝ) + 1) * Real.pi) :=
        hfcont.intervalIntegrable _ _
      have hright : IntervalIntegrable f volume
          (((n : ℝ) + 1) * Real.pi) (((n : ℝ) + 2) * Real.pi) :=
        hfcont.intervalIntegrable _ _
      calc
        (∫ x in (0 : ℝ)..(((n + 1 : ℕ) : ℝ) + 1) * Real.pi,
            Real.exp (-x) * |Real.sin x|) =
            (∫ x in (0 : ℝ)..((n : ℝ) + 1) * Real.pi,
              Real.exp (-x) * |Real.sin x|) +
            ∫ x in ((n : ℝ) + 1) * Real.pi..((n : ℝ) + 2) * Real.pi,
              Real.exp (-x) * |Real.sin x| := by
                change (∫ x in (0 : ℝ)..(((n + 1 : ℕ) : ℝ) + 1) * Real.pi, f x) =
                  (∫ x in (0 : ℝ)..((n : ℝ) + 1) * Real.pi, f x) +
                    ∫ x in ((n : ℝ) + 1) * Real.pi..((n : ℝ) + 2) * Real.pi, f x
                convert
                  (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm
                  using 1 <;> norm_num <;> ring
        _ = partialSum n + block (n + 1) := by
          rw [ih]
          congr 1
          convert abs_block_integral_eq_block (n + 1) using 1 <;> norm_num <;> ring
        _ = partialSum (n + 1) := by
          simp [partialSum, Finset.sum_range_succ, Nat.add_assoc]

theorem gap3 :
    Tendsto partialSum atTop (nhds S) := by
  have hend :
      Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.pi) atTop atTop := by
    have hadd :
        Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    exact hadd.atTop_mul_const Real.pi_pos
  have hlim :=
    intervalIntegral_tendsto_integral_Ioi
      (f := fun x : ℝ => Real.exp (-x) * |Real.sin x|)
      0 abs_integrand_integrableOn hend
  unfold S
  apply hlim.congr'
  filter_upwards [] with n
  exact gap2 n

theorem gap4 (k : ℕ) :
    block k =
      (-1 : ℝ) ^ k *
        (primitive (((k : ℝ) + 1) * Real.pi) -
          primitive ((k : ℝ) * Real.pi)) := by
  have hcont : Continuous
      (fun x : ℝ => Real.exp (-x) * Real.sin x) :=
    (Real.continuous_exp.comp continuous_neg).mul Real.continuous_sin
  unfold block
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => primitive_hasDerivAt x) (hcont.intervalIntegrable _ _)]

theorem gap5 (k : ℕ) :
    block k =
      (1 / 2 : ℝ) *
        (Real.exp (-((k : ℝ) + 1) * Real.pi) +
          Real.exp (-(k : ℝ) * Real.pi)) := by
  rw [gap4]
  have harg :
      ((k : ℝ) + 1) * Real.pi = ((k + 1 : ℕ) : ℝ) * Real.pi := by
    norm_num
  have hs1 : Real.sin (((k : ℝ) + 1) * Real.pi) = 0 := by
    rw [harg]
    exact Real.sin_nat_mul_pi (k + 1)
  have hc1 :
      Real.cos (((k : ℝ) + 1) * Real.pi) = -((-1 : ℝ) ^ k) := by
    rw [harg, Real.cos_nat_mul_pi, pow_succ]
    ring
  have hs0 : Real.sin ((k : ℝ) * Real.pi) = 0 :=
    Real.sin_nat_mul_pi k
  have hc0 : Real.cos ((k : ℝ) * Real.pi) = (-1 : ℝ) ^ k :=
    Real.cos_nat_mul_pi k
  have hexp1 :
      Real.exp (-(((k : ℝ) + 1) * Real.pi)) =
        Real.exp (-((k : ℝ) + 1) * Real.pi) := by
    congr 1
    ring
  have hexp0 :
      Real.exp (-((k : ℝ) * Real.pi)) =
        Real.exp (-(k : ℝ) * Real.pi) := by
    congr 1
    ring
  have hsq : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add]
    simp
  unfold primitive
  rw [hs1, hc1, hs0, hc0, hexp1, hexp0]
  calc
    (-1 : ℝ) ^ k *
        (-Real.exp (-((k : ℝ) + 1) * Real.pi) * (0 + -((-1 : ℝ) ^ k)) / 2 -
          -Real.exp (-(k : ℝ) * Real.pi) * (0 + (-1 : ℝ) ^ k) / 2) =
        ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
          ((1 / 2 : ℝ) *
            (Real.exp (-((k : ℝ) + 1) * Real.pi) +
              Real.exp (-(k : ℝ) * Real.pi))) := by ring
    _ = (1 / 2 : ℝ) *
        (Real.exp (-((k : ℝ) + 1) * Real.pi) +
          Real.exp (-(k : ℝ) * Real.pi)) := by rw [hsq, one_mul]

theorem gap6 :
    Tendsto
      (fun n => (1 / 2 : ℝ) *
        ∑ k ∈ Finset.range (n + 1),
          (Real.exp (-((k : ℝ) + 1) * Real.pi) +
            Real.exp (-(k : ℝ) * Real.pi)))
      atTop (nhds S) := by
  apply gap3.congr'
  filter_upwards [] with n
  unfold partialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact gap5 k

theorem gap7 (n : ℕ) :
    (1 / 2 : ℝ) *
        ∑ k ∈ Finset.range (n + 1),
          (Real.exp (-((k : ℝ) + 1) * Real.pi) +
            Real.exp (-(k : ℝ) * Real.pi)) =
      (1 / 2 : ℝ) *
        (1 + 2 * Real.exp (-Real.pi) *
          ∑ k ∈ Finset.range n, Real.exp (-(k : ℝ) * Real.pi) +
            Real.exp (-((n : ℝ) + 1) * Real.pi)) := by
  let q : ℝ := Real.exp (-Real.pi)
  have hfirst :
      (∑ k ∈ Finset.range (n + 1), q ^ (k + 1)) =
        q * ∑ k ∈ Finset.range (n + 1), q ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ]
    ring
  have hgeom :
      (∑ k ∈ Finset.range n, q ^ k) * (1 - q) = 1 - q ^ n :=
    geom_sum_mul_neg q n
  simp_rw [exp_neg_succ_mul_pi, exp_neg_nat_mul_pi]
  change (1 / 2 : ℝ) *
      (∑ k ∈ Finset.range (n + 1), (q ^ (k + 1) + q ^ k)) =
    (1 / 2 : ℝ) *
      (1 + 2 * q * (∑ k ∈ Finset.range n, q ^ k) + q ^ (n + 1))
  rw [Finset.sum_add_distrib, hfirst, Finset.sum_range_succ, pow_succ]
  nlinarith [hgeom]

theorem gap8 :
    Tendsto
      (fun n => (1 / 2 : ℝ) *
        (1 + 2 * Real.exp (-Real.pi) *
          ∑ k ∈ Finset.range n, Real.exp (-(k : ℝ) * Real.pi) +
            Real.exp (-((n : ℝ) + 1) * Real.pi)))
      atTop (nhds S) := by
  apply gap6.congr'
  filter_upwards [] with n
  exact gap7 n

theorem gap9 (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.exp (-(k : ℝ) * Real.pi) =
      (1 - Real.exp (-(n : ℝ) * Real.pi)) /
        (1 - Real.exp (-Real.pi)) := by
  exact geometric_exp_sum n

theorem gap10 :
    Tendsto
      (fun n => (1 / 2 : ℝ) *
        (1 + 2 * Real.exp (-Real.pi) *
          ((1 - Real.exp (-(n : ℝ) * Real.pi)) /
            (1 - Real.exp (-Real.pi))) +
          Real.exp (-((n : ℝ) + 1) * Real.pi)))
      atTop
      (nhds ((1 / 2 : ℝ) *
        (1 + 2 * Real.exp (-Real.pi) / (1 - Real.exp (-Real.pi))))) := by
  let q : ℝ := Real.exp (-Real.pi)
  have harg :
      Tendsto (fun n : ℝ => -n * Real.pi) atTop atBot := by
    have h := tendsto_id.atTop_mul_const_of_neg
      (neg_lt_zero.mpr Real.pi_pos)
    apply h.congr'
    filter_upwards [] with n
    dsimp only [id_eq]
    ring
  have hzero :
      Tendsto (fun n : ℝ => Real.exp (-n * Real.pi))
        atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      Real.tendsto_exp_atBot.comp harg
  have hzeroSucc :
      Tendsto (fun n : ℝ => Real.exp (-(n + 1) * Real.pi))
        atTop (nhds 0) := by
    have hmul :
        Tendsto (fun n : ℝ => Real.exp (-n * Real.pi) * q)
          atTop (nhds 0) := by
      simpa only [zero_mul] using hzero.mul_const q
    apply hmul.congr'
    filter_upwards [] with n
    dsimp [q]
    rw [← Real.exp_add]
    congr 1
    ring
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hfrac :
      Tendsto
        (fun n : ℝ =>
          (1 - Real.exp (-n * Real.pi)) / (1 - q))
        atTop (nhds (1 / (1 - q))) :=
    by simpa only [sub_zero] using
      (hone.sub hzero).div_const (1 - q)
  have hinside :
      Tendsto
        (fun n : ℝ =>
          1 + (2 * q) *
            ((1 - Real.exp (-n * Real.pi)) / (1 - q)) +
              Real.exp (-(n + 1) * Real.pi))
        atTop (nhds (1 + (2 * q) * (1 / (1 - q)) + 0)) :=
    (hone.add (hfrac.const_mul (2 * q))).add hzeroSucc
  have hscaled := hinside.const_mul (1 / 2 : ℝ)
  dsimp [q] at hscaled ⊢
  convert hscaled using 1 <;> ring

theorem gap11 :
    (1 / 2 : ℝ) *
        (1 + 2 * Real.exp (-Real.pi) / (1 - Real.exp (-Real.pi))) =
      (1 / 2 : ℝ) *
        ((Real.exp Real.pi + 1) / (Real.exp Real.pi - 1)) := by
  have hE : 1 < Real.exp Real.pi := by
    rw [Real.one_lt_exp_iff]
    exact Real.pi_pos
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero Real.pi, (sub_pos.mpr hE).ne']
  ring

theorem gap12 :
    (1 / 2 : ℝ) *
        ((Real.exp Real.pi + 1) / (Real.exp Real.pi - 1)) =
      (1 / 2 : ℝ) * coth (Real.pi / 2) := by
  let x : ℝ := Real.pi / 2
  let E : ℝ := Real.exp x
  have hx : 0 < x := by
    dsimp [x]
    exact half_pos Real.pi_pos
  have hEpos : 0 < E := by
    dsimp [E]
    exact Real.exp_pos _
  have hEgt : 1 < E := by
    dsimp [E]
    rw [Real.one_lt_exp_iff]
    exact hx
  have hsqpos : 0 < E ^ 2 - 1 := by
    have hfac : 0 < (E - 1) * (E + 1) :=
      mul_pos (sub_pos.mpr hEgt) (by linarith)
    nlinarith
  have hdiff : E - E⁻¹ ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, inv_eq_one_div, div_lt_iff₀ hEpos]
    nlinarith [hsqpos]
  have hpi : Real.exp Real.pi = E ^ 2 := by
    dsimp [E, x]
    rw [show Real.pi = Real.pi / 2 + Real.pi / 2 by ring,
      Real.exp_add]
    ring
  unfold coth
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg, hpi]
  change (1 / 2 : ℝ) * ((E ^ 2 + 1) / (E ^ 2 - 1)) =
    (1 / 2 : ℝ) * (((E + E⁻¹) / 2) / ((E - E⁻¹) / 2))
  field_simp [hEpos.ne', hsqpos.ne', hdiff]

private theorem exp_pi_coarse_bounds :
    (22.8 : ℝ) < Real.exp Real.pi ∧ Real.exp Real.pi < 23.7 := by
  let d : ℝ := Real.pi - 3
  have hd0 : 0 < d := by
    dsimp [d]
    linarith [Real.pi_gt_three]
  have hdlo : (0.1415 : ℝ) < d := by
    dsimp [d]
    linarith [Real.pi_gt_d4]
  have hdhi : d < (0.1416 : ℝ) := by
    dsimp [d]
    linarith [Real.pi_lt_d4]
  have hd1 : d < 1 := by linarith
  have hedlo : (1.1415 : ℝ) < Real.exp d := by
    have h := Real.add_one_lt_exp hd0.ne'
    linarith
  have hedle : Real.exp d ≤ 1 / (1 - d) :=
    Real.exp_bound_div_one_sub_of_interval hd0.le hd1
  have hden : 0 < 1 - d := by linarith
  have hrecip : 1 / (1 - d) < (1.165 : ℝ) := by
    rw [div_lt_iff₀ hden]
    nlinarith
  have hedhi : Real.exp d < (1.165 : ℝ) :=
    hedle.trans_lt hrecip
  have helo : (2.718 : ℝ) < Real.exp 1 :=
    (by norm_num : (2.718 : ℝ) < 2.7182818283).trans
      Real.exp_one_gt_d9
  have hehi : Real.exp 1 < (2.719 : ℝ) :=
    Real.exp_one_lt_d9.trans
      (by norm_num : (2.7182818286 : ℝ) < 2.719)
  have hecubeLo : (2.718 : ℝ) ^ 3 < Real.exp 1 ^ 3 := by
    gcongr
  have hecubeHi : Real.exp 1 ^ 3 < (2.719 : ℝ) ^ 3 := by
    gcongr
  have hexp3 : Real.exp (3 : ℝ) = Real.exp 1 ^ 3 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 3
  have hexppi : Real.exp Real.pi = Real.exp 1 ^ 3 * Real.exp d := by
    calc
      Real.exp Real.pi = Real.exp ((3 : ℝ) + d) := by
        congr 1
        dsimp [d]
        ring
      _ = Real.exp 3 * Real.exp d := Real.exp_add 3 d
      _ = Real.exp 1 ^ 3 * Real.exp d := by rw [hexp3]
  constructor
  · rw [hexppi]
    calc
      (22.8 : ℝ) < (2.718 : ℝ) ^ 3 * 1.1415 := by norm_num
      _ < Real.exp 1 ^ 3 * Real.exp d := by
        exact mul_lt_mul hecubeLo hedlo.le (by positivity) (by positivity)
  · rw [hexppi]
    calc
      Real.exp 1 ^ 3 * Real.exp d <
          (2.719 : ℝ) ^ 3 * 1.165 := by
        exact mul_lt_mul hecubeHi hedhi.le (by positivity) (by positivity)
      _ < (23.7 : ℝ) := by norm_num

theorem gap13 :
    |(1 / 2 : ℝ) * coth (Real.pi / 2) - 0.545| < 0.001 := by
  rw [← gap12]
  let E : ℝ := Real.exp Real.pi
  have hbounds : (22.8 : ℝ) < E ∧ E < 23.7 := by
    simpa only [E] using exp_pi_coarse_bounds
  have hden : 0 < E - 1 := by linarith
  have hform :
      (1 / 2 : ℝ) * ((E + 1) / (E - 1)) =
        (1 / 2 : ℝ) + 1 / (E - 1) := by
    field_simp [hden.ne']
    ring
  rw [show Real.exp Real.pi = E by rfl, hform, abs_lt]
  have hrecipLo : (0.044 : ℝ) < 1 / (E - 1) := by
    rw [lt_div_iff₀ hden]
    nlinarith [hbounds.2]
  have hrecipHi : 1 / (E - 1) < (0.046 : ℝ) := by
    rw [div_lt_iff₀ hden]
    nlinarith [hbounds.1]
  constructor <;> nlinarith

theorem gap14 :
    |S - 0.545| < 0.001 := by
  have hclosedS :
      Tendsto
        (fun n : ℕ => (1 / 2 : ℝ) *
          (1 + 2 * Real.exp (-Real.pi) *
            ((1 - Real.exp (-(n : ℝ) * Real.pi)) /
              (1 - Real.exp (-Real.pi))) +
            Real.exp (-((n : ℝ) + 1) * Real.pi)))
        atTop (nhds S) := by
    apply gap8.congr'
    filter_upwards [] with n
    rw [gap9 n]
  have hclosedLimit :
      Tendsto
        (fun n : ℕ => (1 / 2 : ℝ) *
          (1 + 2 * Real.exp (-Real.pi) *
            ((1 - Real.exp (-(n : ℝ) * Real.pi)) /
              (1 - Real.exp (-Real.pi))) +
            Real.exp (-((n : ℝ) + 1) * Real.pi)))
        atTop
        (nhds ((1 / 2 : ℝ) *
          (1 + 2 * Real.exp (-Real.pi) /
            (1 - Real.exp (-Real.pi))))) := by
    simpa only [Function.comp_apply] using
      gap10.comp tendsto_natCast_atTop_atTop
  have hS :
      S = (1 / 2 : ℝ) *
        (1 + 2 * Real.exp (-Real.pi) /
          (1 - Real.exp (-Real.pi))) :=
    tendsto_nhds_unique hclosedS hclosedLimit
  have hexact : S = (1 / 2 : ℝ) * coth (Real.pi / 2) := by
    calc
      S = (1 / 2 : ℝ) *
          (1 + 2 * Real.exp (-Real.pi) /
            (1 - Real.exp (-Real.pi))) := hS
      _ = (1 / 2 : ℝ) *
          ((Real.exp Real.pi + 1) /
            (Real.exp Real.pi - 1)) := gap11
      _ = (1 / 2 : ℝ) * coth (Real.pi / 2) := gap12
  rw [hexact]
  exact gap13

end
end ProofGap.Exercise2410
