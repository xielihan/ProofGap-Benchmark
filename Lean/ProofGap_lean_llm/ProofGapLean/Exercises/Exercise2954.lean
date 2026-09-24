import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2954

noncomputable section

open scoped Interval

def target (x : ℝ) : ℝ :=
  Real.arcsin (Real.cos x)

def coefficientIntegral (n : ℕ) : ℝ :=
  2 / Real.pi *
    ∫ x in 0..Real.pi,
      target x * Real.cos ((n : ℝ) * x)

def linearizedIntegral (n : ℕ) : ℝ :=
  2 / Real.pi *
    ∫ x in 0..Real.pi,
      (Real.pi / 2 - x) * Real.cos ((n : ℝ) * x)

def antiderivative (n : ℕ) (x : ℝ) : ℝ :=
  2 / Real.pi *
    (Real.pi / (2 * (n : ℝ)) * Real.sin ((n : ℝ) * x) -
      x / (n : ℝ) * Real.sin ((n : ℝ) * x) -
      1 / (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * x))

def antiderivativeEval (n : ℕ) : ℝ :=
  antiderivative n Real.pi - antiderivative n 0

def fourierSeries (x : ℝ) : ℝ :=
  4 / Real.pi *
    ∑' k : ℕ,
      Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
        (((2 * k + 1 : ℕ) : ℝ) ^ 2)

private theorem target_eq_linear {x : ℝ}
    (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    target x = Real.pi / 2 - x := by
  unfold target
  rw [← Real.sin_pi_div_two_sub, Real.arcsin_sin]
  · linarith
  · linarith

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

private theorem target_periodic :
    Function.Periodic target (2 * Real.pi) := by
  intro x
  unfold target
  rw [Real.cos_add_two_pi]

private theorem target_even : Function.Even target := by
  intro x
  simp [target]

private theorem fourierSeries_periodic :
    Function.Periodic fourierSeries (2 * Real.pi) := by
  intro x
  unfold fourierSeries
  congr 1
  apply tsum_congr
  intro k
  congr 1
  rw [show (((2 * k + 1 : ℕ) : ℝ) * (x + 2 * Real.pi)) =
      (((2 * k + 1 : ℕ) : ℝ) * x) +
        ((2 * k + 1 : ℕ) : ℝ) * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi]

private theorem fourierSeries_even : Function.Even fourierSeries := by
  intro x
  unfold fourierSeries
  congr 1
  apply tsum_congr
  intro k
  rw [show (((2 * k + 1 : ℕ) : ℝ) * -x) =
      -(((2 * k + 1 : ℕ) : ℝ) * x) by ring,
    Real.cos_neg]

private theorem fourierSeries_eq_target_Icc {x : ℝ}
    (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    fourierSeries x = target x := by
  have hsum := (hasSum_odd_cos_div_sq hx0 hxpi).tsum_eq
  rw [target_eq_linear hx0 hxpi]
  unfold fourierSeries
  rw [hsum]
  field_simp [Real.pi_ne_zero]
  ring

set_option maxHeartbeats 800000 in
private theorem fourierSeries_eq_target (x : ℝ) :
    fourierSeries x = target x := by
  have hpair :
      Function.Periodic
        (fun y => (target y, fourierSeries y))
        (2 * Real.pi) := by
    intro y
    exact Prod.ext (target_periodic y) (fourierSeries_periodic y)
  obtain ⟨y, hy, hxy⟩ :=
    hpair.exists_mem_Ico₀ Real.two_pi_pos x
  have hy0 : 0 ≤ y := hy.1
  have hy2pi : y < 2 * Real.pi := hy.2
  have hlocal : fourierSeries y = target y := by
    by_cases hypi : y ≤ Real.pi
    · exact fourierSeries_eq_target_Icc hy0 hypi
    · have hz0 : 0 ≤ 2 * Real.pi - y := by linarith
      have hzpi : 2 * Real.pi - y ≤ Real.pi := by
        linarith [Real.pi_pos]
      have hz := fourierSeries_eq_target_Icc hz0 hzpi
      have htargetSym :
          target (2 * Real.pi - y) = target y :=
        (target_periodic.sub_eq' (x := y)).trans (target_even y)
      have hseriesSym :
          fourierSeries (2 * Real.pi - y) = fourierSeries y :=
        (fourierSeries_periodic.sub_eq' (x := y)).trans
          (fourierSeries_even y)
      exact hseriesSym.symm.trans (hz.trans htargetSym)
  have htarget := congrArg Prod.fst hxy
  have hseries := congrArg Prod.snd hxy
  exact hseries.trans (hlocal.trans htarget.symm)

theorem gap1 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    Function.Periodic f (2 * Real.pi) := by
  intro x
  rw [hf, hf]
  unfold target
  rw [Real.cos_add_two_pi]

theorem gap2 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    Continuous f := by
  rw [show f = target by funext x; exact hf x]
  exact Real.continuous_arcsin.comp Real.continuous_cos

theorem gap3 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    Function.Even f := by
  intro x
  rw [hf, hf]
  simp [target]

theorem gap4 (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = 0) :
    ∀ n : ℕ, 1 ≤ n → s n = 0 := by
  exact hs

theorem gap5 (c : ℕ → ℝ)
    (hc : c 0 = 2 / Real.pi * ∫ x in 0..Real.pi, target x) :
    c 0 = 2 / Real.pi * ∫ x in 0..Real.pi, target x := by
  exact hc

theorem gap6 :
    2 / Real.pi * (∫ x in 0..Real.pi, target x) =
      2 / Real.pi * ∫ x in 0..Real.pi, Real.pi / 2 - x := by
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) Real.pi := by
    simpa [Set.uIcc_of_le Real.pi_pos.le] using hx
  exact target_eq_linear hx'.1 hx'.2

theorem gap7 :
    2 / Real.pi * (∫ x in 0..Real.pi, Real.pi / 2 - x) =
      0 := by
  have hsub :
      (∫ x in (0 : ℝ)..Real.pi, Real.pi / 2 - x) =
        (∫ _x in (0 : ℝ)..Real.pi, Real.pi / 2) -
          ∫ x in (0 : ℝ)..Real.pi, x := by
    exact intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _)
  rw [hsub]
  simp only [intervalIntegral.integral_const, integral_id,
    smul_eq_mul]
  ring

theorem gap8 (c : ℕ → ℝ)
    (hc : c 0 = 2 / Real.pi * ∫ x in 0..Real.pi, target x) :
    c 0 = 0 := by
  rw [hc, gap6, gap7]

theorem gap9 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n := by
  exact hc

theorem gap10 :
    ∀ n : ℕ, 1 ≤ n →
      coefficientIntegral n = linearizedIntegral n := by
  intro n hn
  unfold coefficientIntegral linearizedIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) Real.pi := by
    simpa [Set.uIcc_of_le Real.pi_pos.le] using hx
  dsimp only
  rw [target_eq_linear hx'.1 hx'.2]

theorem gap11 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = linearizedIntegral n := by
  intro n hn
  rw [hc n hn, gap10 n hn]

theorem gap12 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = linearizedIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = antiderivativeEval n := by
  intro n hn
  rw [hc n hn]
  unfold linearizedIntegral antiderivativeEval
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hn0 : (n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have harg : HasDerivAt (fun y : ℝ => (n : ℝ) * y)
        (n : ℝ) x := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id x).const_mul (n : ℝ)
    have hsin :=
      (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x harg
    have hcos :=
      (Real.hasDerivAt_cos ((n : ℝ) * x)).comp x harg
    have hfirst :=
      hsin.const_mul (Real.pi / (2 * (n : ℝ)))
    have hsecond :=
      ((hasDerivAt_id x).div_const (n : ℝ)).mul hsin
    have hthird :=
      hcos.const_mul (1 / (n : ℝ) ^ 2)
    have htotal :=
      ((hfirst.sub hsecond).sub hthird).const_mul
        (2 / Real.pi)
    convert htotal using 1 <;>
      simp only [Function.comp_apply, id_eq] <;>
      field_simp [hn0, Real.pi_ne_zero] <;>
      ring
  · apply Continuous.intervalIntegrable
    fun_prop

theorem gap13 :
    ∀ n : ℕ, 1 ≤ n →
      antiderivativeEval n =
        2 / Real.pi * (1 / (n : ℝ) ^ 2) *
          (1 - (-1 : ℝ) ^ n) := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  unfold antiderivativeEval antiderivative
  rw [Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  simp only [mul_zero, zero_div, Real.sin_zero, Real.cos_zero,
    mul_one, sub_zero]
  field_simp [hn0, Real.pi_ne_zero]
  ring

theorem gap14 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n) :
    ∀ n : ℕ, 1 ≤ n →
      c n =
        2 / Real.pi * (1 / (n : ℝ) ^ 2) *
          (1 - (-1 : ℝ) ^ n) := by
  intro n hn
  rw [hc n hn, gap10 n hn,
    gap12 (fun m => linearizedIntegral m) (fun _ _ => rfl) n hn,
    gap13 n hn]

theorem gap15 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n →
      c n =
        2 / Real.pi * (1 / (n : ℝ) ^ 2) *
          (1 - (-1 : ℝ) ^ n)) :
    (∀ k : ℕ, 1 ≤ k → c (2 * k) = 0) ∧
      (∀ k : ℕ,
        c (2 * k + 1) =
          4 / ((((2 * k + 1 : ℕ) : ℝ) ^ 2) * Real.pi)) := by
  constructor
  · intro k hk
    rw [hc (2 * k) (by omega)]
    rw [pow_mul]
    norm_num
  · intro k
    rw [hc (2 * k + 1) (by omega), pow_add, pow_mul]
    norm_num
    field_simp [Real.pi_ne_zero]
    ring

theorem gap16 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    ∀ x, f x = fourierSeries x := by
  intro x
  exact (hf x).trans (fourierSeries_eq_target x).symm

theorem gap17 :
    ∀ x, fourierSeries x = target x := by
  exact fourierSeries_eq_target

theorem gap18 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    ∀ x, f x = target x := by
  exact hf

end

end ProofGap.Exercise2954
