import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2942

noncomputable section

open scoped BigOperators Interval

def f (x : ℝ) : ℝ :=
  |x|

def b (_n : ℕ) : ℝ :=
  0

def a (n : ℕ) : ℝ :=
  if n = 0 then Real.pi
  else
    2 / ((n : ℝ) ^ 2 * Real.pi) *
      ((-1 : ℝ) ^ n - 1)

def primitiveAt (x : ℝ) : ℝ :=
  2 / Real.pi * (x ^ 2 / 2)

def integrationByPartsValue (n : ℕ) : ℝ :=
  (2 / ((n : ℝ) * Real.pi) * Real.pi *
      Real.sin ((n : ℝ) * Real.pi)) -
    2 / ((n : ℝ) * Real.pi) *
      ∫ x in (0 : ℝ)..Real.pi, Real.sin ((n : ℝ) * x)

def absoluteValueSeries (x : ℝ) : ℝ :=
  Real.pi / 2 -
    4 / Real.pi * ∑' k : ℕ,
      Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
        (((2 * k + 1 : ℕ) : ℝ) ^ 2)

private theorem hasDerivAt_sin_div_const_mul
    (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (c * y) / c)
      (Real.cos (c * x)) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => c * y) c x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
  have h :=
    ((Real.hasDerivAt_sin (c * x)).comp x hinner).div_const c
  convert h using 1
  all_goals field_simp [hc]

private theorem hasDerivAt_neg_cos_div_const_mul
    (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -Real.cos (c * y) / c)
      (Real.sin (c * x)) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => c * y) c x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
  have h :=
    (((Real.hasDerivAt_cos (c * x)).comp x hinner).neg).div_const c
  convert h using 1
  all_goals field_simp [hc]

private theorem integral_sin_nat_mul (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..Real.pi, Real.sin ((n : ℝ) * x)) =
      (1 - (-1 : ℝ) ^ n) / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := Real.pi)
      (f := fun x : ℝ => -Real.cos ((n : ℝ) * x) / (n : ℝ))
      (f' := fun x : ℝ => Real.sin ((n : ℝ) * x))
      (fun x _ => hasDerivAt_neg_cos_div_const_mul (n : ℝ) hn0 x)
      ((by fun_prop :
        Continuous (fun x : ℝ => Real.sin ((n : ℝ) * x))).intervalIntegrable
          (0 : ℝ) Real.pi)
  dsimp only at h
  rw [Real.cos_nat_mul_pi] at h
  norm_num at h
  rw [h]
  field_simp [hn0]
  ring

private theorem scaled_integral_eq_parts (n : ℕ) (hn : 0 < n) :
    (2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
      x * Real.cos ((n : ℝ) * x)) =
      integrationByPartsValue n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hibp :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := Real.pi)
      (u := fun x : ℝ => x)
      (v := fun x : ℝ => Real.sin ((n : ℝ) * x) / (n : ℝ))
      (u' := fun _ : ℝ => 1)
      (v' := fun x : ℝ => Real.cos ((n : ℝ) * x))
      (fun x _ => hasDerivAt_id x)
      (fun x _ => hasDerivAt_sin_div_const_mul (n : ℝ) hn0 x)
      ((continuous_const :
        Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable
          (0 : ℝ) Real.pi)
      ((by fun_prop :
        Continuous (fun x : ℝ => Real.cos ((n : ℝ) * x))).intervalIntegrable
          (0 : ℝ) Real.pi)
  simp only [one_mul, zero_mul, sub_zero] at hibp
  rw [intervalIntegral.integral_div] at hibp
  unfold integrationByPartsValue
  rw [hibp]
  field_simp [hn0, Real.pi_ne_zero]

private theorem scaled_integral_formula (n : ℕ) (hn : 0 < n) :
    (2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
      x * Real.cos ((n : ℝ) * x)) =
      2 / ((n : ℝ) ^ 2 * Real.pi) *
        ((-1 : ℝ) ^ n - 1) := by
  rw [scaled_integral_eq_parts n hn]
  unfold integrationByPartsValue
  rw [Real.sin_nat_mul_pi, integral_sin_nat_mul n hn]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp [hn0, Real.pi_ne_zero]
  ring

private theorem cos_mul_abs (n : ℕ) (x : ℝ) :
    Real.cos ((n : ℝ) * |x|) = Real.cos ((n : ℝ) * x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, mul_neg, Real.cos_neg]

private theorem cosine_hasSum_nonneg (y : ℝ)
    (hy0 : 0 ≤ y) (hy2pi : y ≤ 2 * Real.pi) :
    HasSum
      (fun n : ℕ => Real.cos ((n : ℝ) * y) / (n : ℝ) ^ 2)
      (Real.pi ^ 2 / 6 - Real.pi * y / 2 + y ^ 2 / 4) := by
  have ht : y / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hy0 (by positivity)
    · exact (div_le_one (by positivity)).2 hy2pi
  have h :=
    hasSum_one_div_nat_pow_mul_cos (k := 1) (by norm_num) ht
  convert h using 1 with n
  · funext n
    have harg :
        2 * Real.pi * (n : ℝ) * (y / (2 * Real.pi)) =
          (n : ℝ) * y := by
      field_simp [Real.pi_ne_zero]
    rw [harg]
    ring
  · symm
    change
      ((-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 /
          (2 * 1).factorial * bernoulliFun (2 * 1)
            (y / (2 * Real.pi))) =
        Real.pi ^ 2 / 6 - Real.pi * y / 2 + y ^ 2 / 4
    rw [bernoulliFun_two]
    norm_num [Nat.factorial]
    field_simp [Real.pi_ne_zero]
    ring

private theorem cosine_hasSum_abs (x : ℝ) (hx : |x| ≤ 2 * Real.pi) :
    HasSum
      (fun n : ℕ => Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2)
      (Real.pi ^ 2 / 6 - Real.pi * |x| / 2 + |x| ^ 2 / 4) := by
  refine HasSum.congr_fun
    (cosine_hasSum_nonneg |x| (abs_nonneg x) hx) ?_
  intro n
  rw [cos_mul_abs]

private theorem even_cosine_hasSum (x : ℝ) (hx : |2 * x| ≤ 2 * Real.pi) :
    HasSum
      (fun k : ℕ =>
        Real.cos (((2 * k : ℕ) : ℝ) * x) /
          (((2 * k : ℕ) : ℝ) ^ 2))
      ((1 / 4 : ℝ) *
        (Real.pi ^ 2 / 6 - Real.pi * |2 * x| / 2 +
          |2 * x| ^ 2 / 4)) := by
  have hdouble := cosine_hasSum_abs (2 * x) hx
  refine HasSum.congr_fun (hdouble.mul_left (1 / 4 : ℝ)) ?_
  intro k
  by_cases hk : k = 0
  · subst k
    norm_num
  · have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have harg :
        (k : ℝ) * (2 * x) = ((2 * k : ℕ) : ℝ) * x := by
      push_cast
      ring
    rw [harg]
    push_cast
    field_simp [hk0]
    norm_num
    ring

private theorem odd_cosine_summable (x : ℝ) (hx : |x| ≤ 2 * Real.pi) :
    Summable
      (fun k : ℕ =>
        Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
          (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
  have hodd_inj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    simpa [Function.comp_def, Nat.mul_comm, Nat.add_comm] using
      ((add_left_injective 1).comp
        (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)))
  exact (cosine_hasSum_abs x hx).summable.comp_injective hodd_inj

private theorem odd_tsum_eq_sub {g : ℕ → ℝ} {total even : ℝ}
    (hall : HasSum g total)
    (heven : HasSum (fun k : ℕ => g (2 * k)) even)
    (hodd : Summable (fun k : ℕ => g (2 * k + 1))) :
    (∑' k : ℕ, g (2 * k + 1)) = total - even := by
  have hcombined := HasSum.even_add_odd heven hodd.hasSum
  have hunique := hcombined.unique hall
  linarith

private theorem odd_cosine_tsum (x : ℝ)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    (∑' k : ℕ,
      Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
        (((2 * k + 1 : ℕ) : ℝ) ^ 2)) =
      Real.pi ^ 2 / 8 - Real.pi * |x| / 4 := by
  have hxabs : |x| ≤ Real.pi := abs_le.mpr hx
  have htotal :=
    cosine_hasSum_abs x (by linarith [Real.pi_pos])
  have h2abs : |2 * x| ≤ 2 * Real.pi := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hxabs (by norm_num)
  have heven := even_cosine_hasSum x h2abs
  have hsodd :=
    odd_cosine_summable x (by linarith [Real.pi_pos])
  have hsplit :=
    odd_tsum_eq_sub
      (g := fun n : ℕ =>
        Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2)
      htotal heven hsodd
  rw [hsplit]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  nlinarith [sq_abs x]

theorem gap1 :
    Function.Even f := by
  intro x
  simp [f]

theorem gap2 :
    ∀ n : ℕ, b n = 0 := by
  intro n
  rfl

theorem gap3 :
    a 0 =
      2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi, x := by
  rw [integral_id]
  simp only [a, if_pos]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap4 :
    (2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi, x) =
      primitiveAt Real.pi - primitiveAt 0 := by
  rw [integral_id]
  unfold primitiveAt
  field_simp [Real.pi_ne_zero]

theorem gap5 :
    primitiveAt Real.pi - primitiveAt 0 = Real.pi := by
  unfold primitiveAt
  field_simp [Real.pi_ne_zero]
  ring

theorem gap6 :
    a 0 = Real.pi := by
  calc
    a 0 = 2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi, x := gap3
    _ = primitiveAt Real.pi - primitiveAt 0 := gap4
    _ = Real.pi := gap5

theorem gap7 :
    ∀ n : ℕ,
      a n =
        2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
          x * Real.cos ((n : ℝ) * x) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using gap3
  · rw [a, if_neg hn]
    exact (scaled_integral_formula n (Nat.pos_of_ne_zero hn)).symm

theorem gap8 :
    ∀ n : ℕ, 0 < n →
      (2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi,
        x * Real.cos ((n : ℝ) * x)) =
        integrationByPartsValue n := by
  intro n hn
  exact scaled_integral_eq_parts n hn

theorem gap9 :
    ∀ n : ℕ, 0 < n →
      integrationByPartsValue n =
        2 / ((n : ℝ) ^ 2 * Real.pi) *
          ((-1 : ℝ) ^ n - 1) := by
  intro n hn
  unfold integrationByPartsValue
  rw [Real.sin_nat_mul_pi, integral_sin_nat_mul n hn]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp [hn0, Real.pi_ne_zero]
  ring

theorem gap10 :
    ∀ n : ℕ, 0 < n →
      a n =
        2 / ((n : ℝ) ^ 2 * Real.pi) *
          ((-1 : ℝ) ^ n - 1) := by
  intro n hn
  rw [a, if_neg (Nat.ne_of_gt hn)]

theorem gap11 :
    ∀ x : ℝ, x ∈ Set.Icc (-Real.pi) Real.pi →
      f x = absoluteValueSeries x := by
  intro x hx
  unfold f absoluteValueSeries
  rw [odd_cosine_tsum x hx]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap12 :
    ∀ x : ℝ, x ∈ Set.Icc (-Real.pi) Real.pi →
      absoluteValueSeries x = |x| := by
  intro x hx
  simpa [f] using (gap11 x hx).symm

theorem gap13 :
    ∀ x : ℝ, f x = |x| := by
  intro x
  rfl

end

end ProofGap.Exercise2942
