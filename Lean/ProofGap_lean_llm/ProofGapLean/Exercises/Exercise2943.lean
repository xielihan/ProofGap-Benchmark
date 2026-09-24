import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2943

noncomputable section

open scoped Interval
open Filter
open Topology

def cosineIntegral (a b : ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
      (∫ x in -Real.pi..0, a * x * Real.cos ((n : ℝ) * x)) +
    1 / Real.pi *
      (∫ x in 0..Real.pi, b * x * Real.cos ((n : ℝ) * x))

def sineIntegral (a b : ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
      (∫ x in -Real.pi..0, a * x * Real.sin ((n : ℝ) * x)) +
    1 / Real.pi *
      (∫ x in 0..Real.pi, b * x * Real.sin ((n : ℝ) * x))

def fourierSeries (a b x : ℝ) : ℝ :=
  (b - a) / 4 * Real.pi +
    2 * (a - b) / Real.pi *
      ∑' k : ℕ,
        Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
          (((2 * k + 1 : ℕ) : ℝ) ^ 2) +
    (a + b) *
      ∑'[SummationFilter.conditional ℕ] k : ℕ,
        (-1 : ℝ) ^ (k + 2) / (k + 1 : ℝ) *
          Real.sin ((k + 1 : ℝ) * x)

def piecewiseValue (a b x : ℝ) : ℝ :=
  if x < 0 then a * x else if x = 0 then 0 else b * x

private def mulCosAntiderivative (c x : ℝ) : ℝ :=
  x * Real.sin (c * x) / c + Real.cos (c * x) / c ^ 2

private theorem hasDerivAt_mulCosAntiderivative
    (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (mulCosAntiderivative c) (x * Real.cos (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (c * y))
        (Real.cos (c * x) * c) x :=
    (Real.hasDerivAt_sin (c * x)).comp x hinner
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos (c * y))
        (-Real.sin (c * x) * c) x :=
    (Real.hasDerivAt_cos (c * x)).comp x hinner
  convert
    (((hasDerivAt_id x).mul hsin).div_const c).add
      (hcos.div_const (c ^ 2)) using 1
  field_simp [hc]
  simp only [id_eq]
  ring

private theorem integral_mul_cos_eq_sub
    (c : ℝ) (hc : c ≠ 0) (u v : ℝ) :
    (∫ x in u..v, x * Real.cos (c * x)) =
      mulCosAntiderivative c v - mulCosAntiderivative c u := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_mulCosAntiderivative c hc x)
    ((continuous_id.mul
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).intervalIntegrable u v)

private def mulSinAntiderivative (c x : ℝ) : ℝ :=
  -(x * Real.cos (c * x)) / c + Real.sin (c * x) / c ^ 2

private theorem hasDerivAt_mulSinAntiderivative
    (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (mulSinAntiderivative c) (x * Real.sin (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos (c * y))
        (-Real.sin (c * x) * c) x :=
    (Real.hasDerivAt_cos (c * x)).comp x hinner
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (c * y))
        (Real.cos (c * x) * c) x :=
    (Real.hasDerivAt_sin (c * x)).comp x hinner
  convert
    ((((hasDerivAt_id x).mul hcos).neg).div_const c).add
      (hsin.div_const (c ^ 2)) using 1
  field_simp [hc]
  simp only [id_eq]
  ring

private theorem integral_mul_sin_eq_sub
    (c : ℝ) (hc : c ≠ 0) (u v : ℝ) :
    (∫ x in u..v, x * Real.sin (c * x)) =
      mulSinAntiderivative c v - mulSinAntiderivative c u := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_mulSinAntiderivative c hc x)
    ((continuous_id.mul
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable u v)

private theorem integral_zero_pi_mul_cos_nat
    (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..Real.pi, x * Real.cos ((n : ℝ) * x)) =
      ((-1 : ℝ) ^ n - 1) / (n : ℝ) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [integral_mul_cos_eq_sub (n : ℝ) hn0]
  simp [mulCosAntiderivative, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi]
  field_simp [hn0]

private theorem integral_neg_pi_zero_mul_cos_nat
    (n : ℕ) (hn : 0 < n) :
    (∫ x in (-Real.pi)..(0 : ℝ), x * Real.cos ((n : ℝ) * x)) =
      (1 - (-1 : ℝ) ^ n) / (n : ℝ) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [integral_mul_cos_eq_sub (n : ℝ) hn0]
  simp [mulCosAntiderivative, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi]
  field_simp [hn0]

private theorem integral_zero_pi_mul_sin_nat
    (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..Real.pi, x * Real.sin ((n : ℝ) * x)) =
      Real.pi / (n : ℝ) * (-1 : ℝ) ^ (n + 1) := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [integral_mul_sin_eq_sub (n : ℝ) hn0]
  simp [mulSinAntiderivative, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi, pow_succ]
  ring

private theorem integral_neg_pi_zero_mul_sin_nat
    (n : ℕ) (hn : 0 < n) :
    (∫ x in (-Real.pi)..(0 : ℝ), x * Real.sin ((n : ℝ) * x)) =
      Real.pi / (n : ℝ) * (-1 : ℝ) ^ (n + 1) := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [integral_mul_sin_eq_sub (n : ℝ) hn0]
  simp [mulSinAntiderivative, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi, pow_succ]
  ring

theorem gap1 (a b : ℝ) (c : ℕ → ℝ)
    (hc : c 0 =
      1 / Real.pi * (∫ x in -Real.pi..0, a * x) +
        1 / Real.pi * ∫ x in 0..Real.pi, b * x) :
    c 0 =
      1 / Real.pi * (∫ x in -Real.pi..0, a * x) +
        1 / Real.pi * ∫ x in 0..Real.pi, b * x := by
  exact hc

theorem gap2 (a b : ℝ) :
    1 / Real.pi * (∫ x in -Real.pi..0, a * x) +
        1 / Real.pi * (∫ x in 0..Real.pi, b * x) =
      (b - a) / 2 * Real.pi := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_id]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap3 (a b : ℝ) (c : ℕ → ℝ)
    (hc : c 0 =
      1 / Real.pi * (∫ x in -Real.pi..0, a * x) +
        1 / Real.pi * ∫ x in 0..Real.pi, b * x) :
    c 0 = (b - a) / 2 * Real.pi := by
  rw [hc]
  exact gap2 a b

theorem gap4 (a b : ℝ) (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral a b n) :
    ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral a b n := by
  exact hc

theorem gap5 (a b : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      cosineIntegral a b n =
        (a - b) / ((n : ℝ) ^ 2 * Real.pi) *
          (1 - (-1 : ℝ) ^ n) := by
  intro n hn
  have hnpos : 0 < n := hn
  have hleft :
      (∫ x in -Real.pi..0,
        a * x * Real.cos ((n : ℝ) * x)) =
        a * ∫ x in -Real.pi..0,
          x * Real.cos ((n : ℝ) * x) := by
    calc
      _ = ∫ x in -Real.pi..0,
          a * (x * Real.cos ((n : ℝ) * x)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
  have hright :
      (∫ x in 0..Real.pi,
        b * x * Real.cos ((n : ℝ) * x)) =
        b * ∫ x in 0..Real.pi,
          x * Real.cos ((n : ℝ) * x) := by
    calc
      _ = ∫ x in 0..Real.pi,
          b * (x * Real.cos ((n : ℝ) * x)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
  unfold cosineIntegral
  rw [hleft, hright, integral_neg_pi_zero_mul_cos_nat n hnpos,
    integral_zero_pi_mul_cos_nat n hnpos]
  field_simp [Real.pi_ne_zero,
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)]
  ring

theorem gap6 (a b : ℝ) (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral a b n) :
    ∀ n : ℕ, 1 ≤ n →
      c n =
        (a - b) / ((n : ℝ) ^ 2 * Real.pi) *
          (1 - (-1 : ℝ) ^ n) := by
  intro n hn
  rw [hc n hn, gap5 a b n hn]

theorem gap7 (a b : ℝ) (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = sineIntegral a b n) :
    ∀ n : ℕ, 1 ≤ n → s n = sineIntegral a b n := by
  exact hs

theorem gap8 (a b : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      sineIntegral a b n =
        (a + b) / (n : ℝ) * (-1 : ℝ) ^ (n + 1) := by
  intro n hn
  have hnpos : 0 < n := hn
  have hleft :
      (∫ x in -Real.pi..0,
        a * x * Real.sin ((n : ℝ) * x)) =
        a * ∫ x in -Real.pi..0,
          x * Real.sin ((n : ℝ) * x) := by
    calc
      _ = ∫ x in -Real.pi..0,
          a * (x * Real.sin ((n : ℝ) * x)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
  have hright :
      (∫ x in 0..Real.pi,
        b * x * Real.sin ((n : ℝ) * x)) =
        b * ∫ x in 0..Real.pi,
          x * Real.sin ((n : ℝ) * x) := by
    calc
      _ = ∫ x in 0..Real.pi,
          b * (x * Real.sin ((n : ℝ) * x)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
  unfold sineIntegral
  rw [hleft, hright, integral_neg_pi_zero_mul_sin_nat n hnpos,
    integral_zero_pi_mul_sin_nat n hnpos]
  field_simp [Real.pi_ne_zero,
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)]

theorem gap9 (a b : ℝ) (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = sineIntegral a b n) :
    ∀ n : ℕ, 1 ≤ n →
      s n = (a + b) / (n : ℝ) * (-1 : ℝ) ^ (n + 1) := by
  intro n hn
  rw [hs n hn, gap8 a b n hn]

set_option maxHeartbeats 800000 in
private theorem hasSum_cos_div_sq {x : ℝ}
    (hx0 : 0 ≤ x) (hx2pi : x ≤ 2 * Real.pi) :
    HasSum (fun n : ℕ =>
      Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2)
      (Real.pi ^ 2 / 6 - Real.pi * x / 2 + x ^ 2 / 4) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hy : x / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hx0 hpi.le
    · exact (div_le_one hpi).2 hx2pi
  have h := hasSum_one_div_nat_pow_mul_cos
    (k := 1) (by norm_num) hy
  change HasSum
    (fun n : ℕ =>
      1 / (n : ℝ) ^ 2 *
        Real.cos (2 * Real.pi * (n : ℝ) *
          (x / (2 * Real.pi))))
    ((-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 /
      (Nat.factorial 2 : ℝ) *
      bernoulliFun 2 (x / (2 * Real.pi))) at h
  rw [bernoulliFun_two] at h
  convert h using 1
  · funext n
    field_simp [Real.pi_ne_zero]
  · field_simp [Real.pi_ne_zero]
    ring

set_option maxHeartbeats 800000 in
private theorem hasSum_odd_cos_div_sq {x : ℝ}
    (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    HasSum (fun k : ℕ =>
      Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
        (((2 * k + 1 : ℕ) : ℝ) ^ 2))
      (Real.pi ^ 2 / 8 - Real.pi * x / 4) := by
  let F : ℕ → ℝ := fun n =>
    Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2
  have hall : HasSum F
      (Real.pi ^ 2 / 6 - Real.pi * x / 2 + x ^ 2 / 4) := by
    exact hasSum_cos_div_sq hx0 (by linarith [Real.pi_pos])
  have htwox0 : 0 ≤ 2 * x := by positivity
  have htwoxpi : 2 * x ≤ 2 * Real.pi := by linarith
  have heven0 :=
    (hasSum_cos_div_sq htwox0 htwoxpi).mul_left (1 / 4 : ℝ)
  have heven : HasSum (fun k : ℕ => F (2 * k))
      (Real.pi ^ 2 / 24 - Real.pi * x / 4 + x ^ 2 / 4) := by
    convert heven0 using 1
    · funext k
      dsimp [F]
      push_cast
      rw [show (2 * (k : ℝ)) ^ 2 = 4 * (k : ℝ) ^ 2 by ring]
      simp only [div_eq_mul_inv, mul_inv_rev]
      norm_num
      ring
    · ring
  have hoddSummable : Summable (fun k : ℕ => F (2 * k + 1)) :=
    hall.summable.comp_injective
      (i := fun k : ℕ => 2 * k + 1) (by
        intro m n h
        exact mul_left_cancel₀ (by decide : (2 : ℕ) ≠ 0)
          (Nat.add_right_cancel h))
  have hsplit :
      HasSum (F ∘ Equiv.natSumNatEquivNat)
        (Real.pi ^ 2 / 6 - Real.pi * x / 2 + x ^ 2 / 4) :=
    (Equiv.hasSum_iff Equiv.natSumNatEquivNat).2 hall
  have hcombined0 :
      HasSum (Sum.elim (fun k : ℕ => F (2 * k))
        (fun k : ℕ => F (2 * k + 1)))
        ((Real.pi ^ 2 / 24 - Real.pi * x / 4 + x ^ 2 / 4) +
          ∑' k : ℕ, F (2 * k + 1)) :=
    heven.sum hoddSummable.hasSum
  have hcombined :
      HasSum (F ∘ Equiv.natSumNatEquivNat)
        ((Real.pi ^ 2 / 24 - Real.pi * x / 4 + x ^ 2 / 4) +
          ∑' k : ℕ, F (2 * k + 1)) := by
    convert hcombined0 using 1
    funext z
    rcases z with k | k <;> rfl
  have hvalue :
      (∑' k : ℕ, F (2 * k + 1)) =
        Real.pi ^ 2 / 8 - Real.pi * x / 4 := by
    have hu := hsplit.unique hcombined
    linarith
  rw [← hvalue]
  exact hoddSummable.hasSum

private theorem hasSum_sawtooth
    (x : ℝ) (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    HasSum
      (fun k : ℕ =>
        (-1 : ℝ) ^ (k + 2) *
          Real.sin ((k + 1 : ℝ) * x) / (k + 1 : ℝ))
      (x / 2) (SummationFilter.conditional ℕ) := by
  let y : ℝ := x + Real.pi
  have hy₀ : 0 < y := by
    dsimp [y]
    linarith
  have hy₁ : y < 2 * Real.pi := by
    dsimp [y]
    linarith
  have hyneg : -(2 * Real.pi) < y := by
    linarith [Real.pi_pos]
  have hcosne : Real.cos y ≠ 1 := by
    intro h
    have hyzero :=
      (Real.cos_eq_one_iff_of_lt_of_lt hyneg hy₁).mp h
    linarith
  have hcoslt : Real.cos y < 1 :=
    lt_of_le_of_ne (Real.cos_le_one y) hcosne
  let q : ℂ := Complex.exp ((y : ℂ) * Complex.I)
  have hqnorm : ‖q‖ = 1 := by
    simpa [q] using Complex.norm_exp_ofReal_mul_I y
  have hqne : q ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [q, Complex.exp_mul_I] at hre
    exact hcosne hre
  have hqre : q.re = Real.cos y := by
    dsimp [q]
    rw [Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hslit : 1 - q ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    change 0 < 1 - q.re
    rw [hqre]
    linarith
  let theta : ℝ := y / 2 - Real.pi / 2
  have htheta : theta ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> dsimp [theta] <;> linarith [Real.pi_pos]
  have hsin : 0 < Real.sin (y / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have hfactor :
      1 - q =
        ((2 * Real.sin (y / 2) : ℝ) : ℂ) *
          (Complex.cos (theta : ℂ) +
            Complex.sin (theta : ℂ) * Complex.I) := by
    dsimp [q]
    rw [Complex.exp_mul_I,
      ← Complex.ofReal_cos y, ← Complex.ofReal_sin y,
      ← Complex.ofReal_cos theta, ← Complex.ofReal_sin theta]
    rw [show y = 2 * (y / 2) by ring,
      Real.cos_two_mul, Real.sin_two_mul]
    simp [theta, Real.cos_sub, Real.sin_sub]
    push_cast
    have htrig :=
      Complex.sin_sq_add_cos_sq (((y / 2 : ℝ) : ℂ))
    have hycast :
        (((y / 2 : ℝ) : ℂ)) = (y : ℂ) / 2 := by
      push_cast
      rfl
    rw [hycast] at htrig
    linear_combination -2 * htrig
  have harg : Complex.arg (1 - q) = theta := by
    rw [hfactor]
    exact Complex.arg_mul_cos_add_sin_mul_I
      (mul_pos two_pos hsin) htheta
  have hlogim :
      (-Complex.log (1 - q)).im = -x / 2 := by
    simp only [Complex.neg_im, Complex.log_im, harg]
    dsimp [theta, y]
    ring
  let w : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  let z : ℕ → ℝ := fun k => Real.sin ((k + 1 : ℝ) * y)
  let u : ℕ → ℝ := fun k => w k * z k
  have hwanti : Antitone w := by
    apply antitone_nat_of_succ_le
    intro k
    dsimp [w]
    exact one_div_le_one_div_of_le (by positivity) (by norm_num)
  have hwzero : Tendsto w atTop (𝓝 0) := by
    have htop :
        Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop
    simpa [w, one_div] using tendsto_inv_atTop_zero.comp htop
  have hqpow_im (k : ℕ) :
      (q ^ (k + 1)).im =
        Real.sin ((k + 1 : ℝ) * y) := by
    dsimp [q]
    rw [← Complex.exp_nat_mul]
    rw [show ((k + 1 : ℕ) : ℂ) * ((y : ℂ) * Complex.I) =
        ((((k + 1 : ℕ) : ℝ) * y : ℝ) : ℂ) * Complex.I by
          push_cast
          ring]
    rw [Complex.exp_mul_I]
    simp only [Complex.add_im, Complex.mul_im,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.I_re, Complex.I_im, zero_add, mul_one,
      mul_zero, add_zero]
    push_cast
    rfl
  have hqbound (N : ℕ) :
      ‖∑ k ∈ Finset.range N, q ^ (k + 1)‖ ≤
        2 / ‖q - 1‖ := by
    have hgeom :
        (∑ k ∈ Finset.range N, q ^ (k + 1)) =
          q * ((q ^ N - 1) / (q - 1)) := by
      calc
        (∑ k ∈ Finset.range N, q ^ (k + 1)) =
            q * ∑ k ∈ Finset.range N, q ^ k := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              rw [pow_succ']
        _ = q * ((q ^ N - 1) / (q - 1)) := by
          rw [geom_sum_eq hqne]
    rw [hgeom, norm_mul, norm_div, hqnorm, one_mul]
    apply div_le_div_of_nonneg_right
    · calc
        ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hqnorm]; norm_num
    · positivity
  have hzbound (N : ℕ) :
      ‖∑ k ∈ Finset.range N, z k‖ ≤
        2 / ‖q - 1‖ := by
    have him :
        (∑ k ∈ Finset.range N, q ^ (k + 1)).im =
          ∑ k ∈ Finset.range N, z k := by
      change Complex.imCLM
          (∑ k ∈ Finset.range N, q ^ (k + 1)) =
        ∑ k ∈ Finset.range N, z k
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact hqpow_im k
    calc
      ‖∑ k ∈ Finset.range N, z k‖ =
          |(∑ k ∈ Finset.range N, q ^ (k + 1)).im| := by
            rw [Real.norm_eq_abs, him]
      _ ≤ ‖∑ k ∈ Finset.range N, q ^ (k + 1)‖ :=
        Complex.abs_im_le_norm _
      _ ≤ 2 / ‖q - 1‖ := hqbound N
  have hcauchy :
      CauchySeq (fun N => ∑ k ∈ Finset.range N, u k) := by
    convert hwanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      hwzero hzbound using 1
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hradial (r : ℝ) (hr₀ : 0 < r) (hr₁ : r < 1) :
      (∑' k : ℕ, u k * r ^ k) =
        (-Complex.log (1 - (r : ℂ) * q) / (r : ℂ)).im := by
    have hrnorm : ‖(r : ℂ) * q‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr₀, hqnorm, mul_one]
      exact hr₁
    have hlog :=
      Complex.hasSum_taylorSeries_neg_log hrnorm
    have hshift :
        HasSum
          (fun k : ℕ =>
            ((r : ℂ) * q) ^ (k + 1) / (k + 1 : ℂ))
          (-Complex.log (1 - (r : ℂ) * q)) := by
      simpa using (hasSum_nat_add_iff' 1).mpr hlog
    have hc :=
      Complex.imCLM.hasSum
        (hshift.mul_left ((r : ℂ)⁻¹))
    calc
      (∑' k : ℕ, u k * r ^ k) =
          ∑' k : ℕ,
            Complex.imCLM
              ((r : ℂ)⁻¹ *
                (((r : ℂ) * q) ^ (k + 1) /
                  (k + 1 : ℂ))) := by
            apply tsum_congr
            intro k
            have heqC :
                (r : ℂ)⁻¹ *
                    (((r : ℂ) * q) ^ (k + 1) /
                      (k + 1 : ℂ)) =
                  (((r ^ k / (k + 1 : ℝ) : ℝ) : ℂ) *
                    q ^ (k + 1)) := by
              rw [mul_pow]
              push_cast
              field_simp [hr₀.ne']
              rw [pow_succ']
              ring
            rw [heqC]
            simp only [Complex.imCLM_apply,
              Complex.mul_im, Complex.ofReal_re,
              Complex.ofReal_im, zero_mul, add_zero,
              hqpow_im]
            dsimp [u, w, z]
            ring
      _ = Complex.imCLM
          ((r : ℂ)⁻¹ *
            -Complex.log (1 - (r : ℂ) * q)) :=
        hc.tsum_eq
      _ = (-Complex.log (1 - (r : ℂ) * q) /
          (r : ℂ)).im := by
        simp [Complex.imCLM_apply, div_eq_mul_inv,
          mul_comm]
  have hab :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hinner :
      ContinuousAt (fun r : ℝ => (1 : ℂ) - (r : ℂ) * q) 1 := by
    fun_prop
  have hlogcont :
      ContinuousAt
        (fun r : ℝ =>
          Complex.log ((1 : ℂ) - (r : ℂ) * q)) 1 := by
    apply hinner.clog
    simpa using hslit
  have hfull :
      ContinuousAt
        (fun r : ℝ =>
          (-Complex.log (1 - (r : ℂ) * q) / (r : ℂ)).im) 1 := by
    exact Complex.continuous_im.continuousAt.comp
      (hlogcont.neg.div
        (Complex.ofRealCLM.continuous.continuousAt)
        (by norm_num))
  have heq :
      ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
        (∑' k : ℕ, u k * r ^ k) =
          (-Complex.log (1 - (r : ℂ) * q) / (r : ℂ)).im := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono
        inf_le_left] with r hr₁ hr₀
    exact hradial r hr₀ hr₁
  have hab' :
      Tendsto
        (fun r : ℝ =>
          (-Complex.log (1 - (r : ℂ) * q) / (r : ℂ)).im)
        (𝓝[<] (1 : ℝ)) (𝓝 l) :=
    hab.congr' heq
  have htarget :
      Tendsto
        (fun r : ℝ =>
          (-Complex.log (1 - (r : ℂ) * q) / (r : ℂ)).im)
        (𝓝[<] (1 : ℝ))
        (𝓝 ((-Complex.log (1 - q)).im)) := by
    simpa using hfull.tendsto.mono_left inf_le_left
  have hlvalue : l = -x / 2 := by
    rw [← hlogim]
    exact tendsto_nhds_unique hab' htarget
  have hu :
      HasSum u (-x / 2) (SummationFilter.conditional ℕ) := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff]
    simpa [Function.comp_def, hlvalue] using hl
  have hneg := hu.neg
  have hseries :
      HasSum
        (fun k : ℕ =>
          (-1 : ℝ) ^ (k + 2) *
            Real.sin ((k + 1 : ℝ) * x) / (k + 1 : ℝ))
        (-(-x / 2)) (SummationFilter.conditional ℕ) := by
    refine hneg.congr_fun ?_
    intro k
    dsimp [u, w, z, y]
    rw [show (k + 1 : ℝ) * (x + Real.pi) =
        (k + 1 : ℝ) * x + (k + 1 : ℕ) * Real.pi by
          push_cast
          ring,
      Real.sin_add_nat_mul_pi]
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  convert hseries using 1 <;> ring

private theorem fourierSeries_eq_piecewiseValue
    (a b x : ℝ) (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    fourierSeries a b x = piecewiseValue a b x := by
  have hsine :
      (∑'[SummationFilter.conditional ℕ] k : ℕ,
        (-1 : ℝ) ^ (k + 2) / (k + 1 : ℝ) *
          Real.sin ((k + 1 : ℝ) * x)) = x / 2 := by
    rw [← (hasSum_sawtooth x hx₀ hx₁).tsum_eq]
    apply tsum_congr
    intro k
    ring
  unfold fourierSeries piecewiseValue
  rw [hsine]
  by_cases hxneg : x < 0
  · have hbase :=
      (hasSum_odd_cos_div_sq (x := -x)
        (by linarith) (by linarith)).tsum_eq
    have hcos :
        (∑' k : ℕ,
          Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
            (((2 * k + 1 : ℕ) : ℝ) ^ 2)) =
          Real.pi ^ 2 / 8 + Real.pi * x / 4 := by
      calc
        (∑' k : ℕ,
          Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
            (((2 * k + 1 : ℕ) : ℝ) ^ 2)) =
            ∑' k : ℕ,
              Real.cos (((2 * k + 1 : ℕ) : ℝ) * (-x)) /
                (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
                  apply tsum_congr
                  intro k
                  rw [show (((2 * k + 1 : ℕ) : ℝ) * (-x)) =
                      -(((2 * k + 1 : ℕ) : ℝ) * x) by ring,
                    Real.cos_neg]
        _ = Real.pi ^ 2 / 8 - Real.pi * (-x) / 4 := hbase
        _ = Real.pi ^ 2 / 8 + Real.pi * x / 4 := by ring
    rw [hcos, if_pos hxneg]
    field_simp [Real.pi_ne_zero]
    ring
  · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
    have hcos :=
      (hasSum_odd_cos_div_sq (x := x)
        hxnonneg (le_of_lt hx₁)).tsum_eq
    rw [hcos, if_neg hxneg]
    by_cases hxzero : x = 0
    · rw [if_pos hxzero]
      subst x
      field_simp [Real.pi_ne_zero]
      ring
    · rw [if_neg hxzero]
      field_simp [Real.pi_ne_zero]
      ring

theorem gap10 (a b : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, -Real.pi < x → x < Real.pi →
      f x = piecewiseValue a b x) :
    ∀ x, -Real.pi < x → x < Real.pi →
      f x = fourierSeries a b x := by
  intro x hx₀ hx₁
  rw [hf x hx₀ hx₁]
  exact (fourierSeries_eq_piecewiseValue a b x hx₀ hx₁).symm

theorem gap11 (a b : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, -Real.pi < x → x < Real.pi →
      f x = fourierSeries a b x) :
    ∀ x, -Real.pi < x → x < Real.pi →
      f x = piecewiseValue a b x := by
  intro x hx₀ hx₁
  rw [hf x hx₀ hx₁]
  exact fourierSeries_eq_piecewiseValue a b x hx₀ hx₁

end

end ProofGap.Exercise2943
