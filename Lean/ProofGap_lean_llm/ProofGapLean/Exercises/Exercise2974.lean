import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2974

noncomputable section

open scoped Interval

def xCoord (a s : ℝ) : ℝ :=
  if s ≤ a then s
  else if s ≤ 2 * a then a
  else if s ≤ 3 * a then 3 * a - s
  else 0

def yCoord (a s : ℝ) : ℝ :=
  if s ≤ a then 0
  else if s ≤ 2 * a then s - a
  else if s ≤ 3 * a then a
  else 4 * a - s

def xCosIntegral (a : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * a) *
    ∫ s in 0..4 * a,
      xCoord a s * Real.cos ((n : ℝ) * Real.pi * s / (2 * a))

def xSinIntegral (a : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * a) *
    ∫ s in 0..4 * a,
      xCoord a s * Real.sin ((n : ℝ) * Real.pi * s / (2 * a))

def yCosIntegral (a : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * a) *
    ∫ s in 0..4 * a,
      yCoord a s * Real.cos ((n : ℝ) * Real.pi * s / (2 * a))

def ySinIntegral (a : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * a) *
    ∫ s in 0..4 * a,
      yCoord a s * Real.sin ((n : ℝ) * Real.pi * s / (2 * a))

def generalSeries (a : ℝ) (c d : ℕ → ℝ) (s : ℝ) : ℝ :=
  c 0 / 2 +
    ∑' k : ℕ,
      let n : ℕ := k + 1
      c n * Real.cos ((n : ℝ) * Real.pi * s / (2 * a)) +
        d n * Real.sin ((n : ℝ) * Real.pi * s / (2 * a))

def xSeries (a s : ℝ) : ℝ :=
  a / 2 -
    4 * a / Real.pi ^ 2 *
      ∑' k : ℕ,
        1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
          Real.cos (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a)) +
    4 * a / Real.pi ^ 2 *
      ∑' k : ℕ,
        (-1 : ℝ) ^ k / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
          Real.sin (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))

def ySeries (a s : ℝ) : ℝ :=
  a / 2 -
    4 * a / Real.pi ^ 2 *
      ∑' k : ℕ,
        1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
          Real.cos (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a)) +
    4 * a / Real.pi ^ 2 *
      ∑' k : ℕ,
        (-1 : ℝ) ^ (k + 1) / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
          Real.sin (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))

private def oddCosineSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
      (((2 * k + 1 : ℕ) : ℝ) ^ 2)

set_option maxHeartbeats 800000 in
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
  convert h using 1
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
          (Nat.factorial (2 * 1) : ℝ) * bernoulliFun (2 * 1)
            (y / (2 * Real.pi))) =
        Real.pi ^ 2 / 6 - Real.pi * y / 2 + y ^ 2 / 4
    rw [bernoulliFun_two]
    norm_num [Nat.factorial]
    field_simp [Real.pi_ne_zero]
    ring


set_option maxHeartbeats 800000 in
private theorem oddCosineSeries_hasSum_lower {x : ℝ}
    (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    HasSum
      (fun k : ℕ =>
        Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
          (((2 * k + 1 : ℕ) : ℝ) ^ 2))
      (Real.pi ^ 2 / 8 - Real.pi * x / 4) := by
  let F : ℕ → ℝ := fun n =>
    Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2
  have hall : HasSum F
      (Real.pi ^ 2 / 6 - Real.pi * x / 2 + x ^ 2 / 4) := by
    exact cosine_hasSum_nonneg x hx0
      (by linarith [Real.pi_pos])
  have htwox0 : 0 ≤ 2 * x := by positivity
  have htwoxpi : 2 * x ≤ 2 * Real.pi := by linarith
  have heven0 :=
    (cosine_hasSum_nonneg (2 * x) htwox0 htwoxpi).mul_left
      (1 / 4 : ℝ)
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

private theorem oddCosineSeries_periodic :
    Function.Periodic oddCosineSeries (2 * Real.pi) := by
  intro x
  unfold oddCosineSeries
  apply tsum_congr
  intro k
  congr 1
  rw [show (((2 * k + 1 : ℕ) : ℝ) * (x + 2 * Real.pi)) =
      (((2 * k + 1 : ℕ) : ℝ) * x) +
        ((2 * k + 1 : ℕ) : ℝ) * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi]

private theorem oddCosineSeries_even :
    Function.Even oddCosineSeries := by
  intro x
  unfold oddCosineSeries
  apply tsum_congr
  intro k
  rw [show (((2 * k + 1 : ℕ) : ℝ) * -x) =
      -(((2 * k + 1 : ℕ) : ℝ) * x) by ring,
    Real.cos_neg]

private theorem oddCosineSeries_eq_lower {x : ℝ}
    (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    oddCosineSeries x =
      Real.pi ^ 2 / 8 - Real.pi * x / 4 := by
  exact (oddCosineSeries_hasSum_lower hx0 hxpi).tsum_eq

private theorem oddCosineSeries_eq_negative {x : ℝ}
    (hxpi : -Real.pi ≤ x) (hx0 : x ≤ 0) :
    oddCosineSeries x =
      Real.pi ^ 2 / 8 + Real.pi * x / 4 := by
  calc
    oddCosineSeries x = oddCosineSeries (-x) :=
      (oddCosineSeries_even x).symm
    _ = Real.pi ^ 2 / 8 - Real.pi * (-x) / 4 :=
      oddCosineSeries_eq_lower (by linarith) (by linarith)
    _ = Real.pi ^ 2 / 8 + Real.pi * x / 4 := by ring

private theorem oddCosineSeries_eq_upper {x : ℝ}
    (hxpi : Real.pi ≤ x) (hx2pi : x ≤ 2 * Real.pi) :
    oddCosineSeries x =
      -3 * Real.pi ^ 2 / 8 + Real.pi * x / 4 := by
  have hz0 : 0 ≤ 2 * Real.pi - x := by linarith
  have hzpi : 2 * Real.pi - x ≤ Real.pi := by linarith
  have hsym :
      oddCosineSeries (2 * Real.pi - x) = oddCosineSeries x :=
    (oddCosineSeries_periodic.sub_eq' (x := x)).trans
      (oddCosineSeries_even x)
  rw [← hsym, oddCosineSeries_eq_lower hz0 hzpi]
  ring

private theorem sin_odd_pi_div_two (k : ℕ) :
    Real.sin (((2 * k + 1 : ℕ) : ℝ) * (Real.pi / 2)) =
      (-1 : ℝ) ^ k := by
  rw [show (((2 * k + 1 : ℕ) : ℝ) * (Real.pi / 2)) =
      Real.pi / 2 + (k : ℝ) * Real.pi by push_cast; ring,
    Real.sin_add_nat_mul_pi, Real.sin_pi_div_two]
  ring

private theorem cos_odd_pi_div_two (k : ℕ) :
    Real.cos (((2 * k + 1 : ℕ) : ℝ) * (Real.pi / 2)) = 0 := by
  rw [show (((2 * k + 1 : ℕ) : ℝ) * (Real.pi / 2)) =
      Real.pi / 2 + (k : ℝ) * Real.pi by push_cast; ring,
    Real.cos_add_nat_mul_pi, Real.cos_pi_div_two, mul_zero]

private theorem shifted_odd_cosine_term (k : ℕ) (x : ℝ) :
    (-1 : ℝ) ^ k / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
        Real.sin (((2 * k + 1 : ℕ) : ℝ) * x) =
      Real.cos (((2 * k + 1 : ℕ) : ℝ) *
          (x - Real.pi / 2)) /
        (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
  rw [mul_sub, Real.cos_sub, sin_odd_pi_div_two,
    cos_odd_pi_div_two]
  ring

private theorem xSeries_as_oddCosineSeries (a s : ℝ) :
    xSeries a s =
      a / 2 -
        4 * a / Real.pi ^ 2 *
          oddCosineSeries (Real.pi * s / (2 * a)) +
        4 * a / Real.pi ^ 2 *
          oddCosineSeries
            (Real.pi * s / (2 * a) - Real.pi / 2) := by
  unfold xSeries oddCosineSeries
  have hcos :
      (∑' k : ℕ,
        1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
          Real.cos (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))) =
        ∑' k : ℕ,
          Real.cos (((2 * k + 1 : ℕ) : ℝ) *
            (Real.pi * s / (2 * a))) /
              (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
    apply tsum_congr
    intro k
    ring
  have hsin :
      (∑' k : ℕ,
        (-1 : ℝ) ^ k / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
          Real.sin (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))) =
        ∑' k : ℕ,
          Real.cos (((2 * k + 1 : ℕ) : ℝ) *
            (Real.pi * s / (2 * a) - Real.pi / 2)) /
              (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
    apply tsum_congr
    intro k
    rw [show (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a)) =
        (((2 * k + 1 : ℕ) : ℝ) * (Real.pi * s / (2 * a))) by ring]
    exact shifted_odd_cosine_term k _
  rw [hcos, hsin]

private theorem ySeries_as_oddCosineSeries (a s : ℝ) :
    ySeries a s =
      a / 2 -
        4 * a / Real.pi ^ 2 *
          oddCosineSeries (Real.pi * s / (2 * a)) -
        4 * a / Real.pi ^ 2 *
          oddCosineSeries
            (Real.pi * s / (2 * a) - Real.pi / 2) := by
  unfold ySeries oddCosineSeries
  rw [show
    (∑' k : ℕ,
      (-1 : ℝ) ^ (k + 1) / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
        Real.sin (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))) =
      -(∑' k : ℕ,
        Real.cos (((2 * k + 1 : ℕ) : ℝ) *
            (Real.pi * s / (2 * a) - Real.pi / 2)) /
          (((2 * k + 1 : ℕ) : ℝ) ^ 2)) by
    rw [← tsum_neg]
    apply tsum_congr
    intro k
    rw [show (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a)) =
        (((2 * k + 1 : ℕ) : ℝ) * (Real.pi * s / (2 * a))) by ring,
      pow_succ]
    have hshift :=
      shifted_odd_cosine_term k (Real.pi * s / (2 * a))
    rw [← hshift]
    ring]
  have hcos :
      (∑' k : ℕ,
        1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
          Real.cos (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))) =
        ∑' k : ℕ,
          Real.cos (((2 * k + 1 : ℕ) : ℝ) *
            (Real.pi * s / (2 * a))) /
              (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
    apply tsum_congr
    intro k
    ring
  rw [hcos]
  ring

private theorem scaled_parameter_le {a s c : ℝ}
    (ha : 0 < a) (h : s ≤ c * a) :
    Real.pi * s / (2 * a) ≤ c * Real.pi / 2 := by
  rw [div_le_iff₀ (by positivity : 0 < 2 * a)]
  nlinarith [mul_le_mul_of_nonneg_left h Real.pi_pos.le]

private theorem scaled_parameter_ge {a s c : ℝ}
    (ha : 0 < a) (h : c * a ≤ s) :
    c * Real.pi / 2 ≤ Real.pi * s / (2 * a) := by
  rw [le_div_iff₀ (by positivity : 0 < 2 * a)]
  nlinarith [mul_le_mul_of_nonneg_left h Real.pi_pos.le]

private theorem xCoord_eq_xSeries (a s : ℝ)
    (ha : 0 < a) (hs0 : 0 ≤ s) (hs4 : s ≤ 4 * a) :
    xCoord a s = xSeries a s := by
  rw [xSeries_as_oddCosineSeries]
  by_cases hsa : s ≤ a
  · have ht0 : 0 ≤ Real.pi * s / (2 * a) := by positivity
    have htha : Real.pi * s / (2 * a) ≤ Real.pi / 2 := by
      simpa using
        (scaled_parameter_le (c := 1) ha (by simpa using hsa))
    have hu0 :
        -Real.pi ≤ Real.pi * s / (2 * a) - Real.pi / 2 := by
      linarith [Real.pi_pos]
    have hu1 :
        Real.pi * s / (2 * a) - Real.pi / 2 ≤ 0 := by linarith
    rw [oddCosineSeries_eq_lower ht0 (by linarith),
      oddCosineSeries_eq_negative hu0 hu1]
    simp [xCoord, hsa]
    field_simp [ha.ne', Real.pi_ne_zero]
    ring
  · by_cases hsa2 : s ≤ 2 * a
    · have ht0 : 0 ≤ Real.pi * s / (2 * a) := by positivity
      have ht1 : Real.pi * s / (2 * a) ≤ Real.pi := by
        simpa using scaled_parameter_le (c := 2) ha hsa2
      have hu0 :
          0 ≤ Real.pi * s / (2 * a) - Real.pi / 2 := by
        have := scaled_parameter_ge (c := 1) ha
          (by simpa using le_of_not_ge hsa)
        linarith
      have hu1 :
          Real.pi * s / (2 * a) - Real.pi / 2 ≤ Real.pi := by
        linarith
      rw [oddCosineSeries_eq_lower ht0 ht1,
        oddCosineSeries_eq_lower hu0 hu1]
      simp [xCoord, hsa, hsa2]
      field_simp [ha.ne', Real.pi_ne_zero]
      ring
    · by_cases hsa3 : s ≤ 3 * a
      · have htpi : Real.pi ≤ Real.pi * s / (2 * a) := by
          simpa using scaled_parameter_ge (c := 2) ha
            (le_of_not_ge hsa2)
        have ht2 : Real.pi * s / (2 * a) ≤ 2 * Real.pi := by
          have h := scaled_parameter_le (c := 4) ha hs4
          nlinarith
        have hu0 :
            0 ≤ Real.pi * s / (2 * a) - Real.pi / 2 := by
          linarith
        have hu1 :
            Real.pi * s / (2 * a) - Real.pi / 2 ≤ Real.pi := by
          have := scaled_parameter_le (c := 3) ha hsa3
          linarith
        rw [oddCosineSeries_eq_upper htpi ht2,
          oddCosineSeries_eq_lower hu0 hu1]
        simp [xCoord, hsa, hsa2, hsa3]
        field_simp [ha.ne', Real.pi_ne_zero]
        ring
      · have htpi : Real.pi ≤ Real.pi * s / (2 * a) := by
          have := scaled_parameter_ge (c := 2) ha
            (le_of_not_ge hsa2)
          linarith
        have ht2 : Real.pi * s / (2 * a) ≤ 2 * Real.pi := by
          have h := scaled_parameter_le (c := 4) ha hs4
          nlinarith
        have hupi :
            Real.pi ≤ Real.pi * s / (2 * a) - Real.pi / 2 := by
          have := scaled_parameter_ge (c := 3) ha
            (le_of_not_ge hsa3)
          linarith
        have hu2 :
            Real.pi * s / (2 * a) - Real.pi / 2 ≤ 2 * Real.pi := by
          linarith
        rw [oddCosineSeries_eq_upper htpi ht2,
          oddCosineSeries_eq_upper hupi hu2]
        simp [xCoord, hsa, hsa2, hsa3]
        field_simp [ha.ne', Real.pi_ne_zero]
        ring

private theorem yCoord_eq_ySeries (a s : ℝ)
    (ha : 0 < a) (hs0 : 0 ≤ s) (hs4 : s ≤ 4 * a) :
    yCoord a s = ySeries a s := by
  rw [ySeries_as_oddCosineSeries]
  by_cases hsa : s ≤ a
  · have ht0 : 0 ≤ Real.pi * s / (2 * a) := by positivity
    have htha : Real.pi * s / (2 * a) ≤ Real.pi / 2 := by
      simpa using
        (scaled_parameter_le (c := 1) ha (by simpa using hsa))
    have hu0 :
        -Real.pi ≤ Real.pi * s / (2 * a) - Real.pi / 2 := by
      linarith [Real.pi_pos]
    have hu1 :
        Real.pi * s / (2 * a) - Real.pi / 2 ≤ 0 := by linarith
    rw [oddCosineSeries_eq_lower ht0 (by linarith),
      oddCosineSeries_eq_negative hu0 hu1]
    simp [yCoord, hsa]
    field_simp [ha.ne', Real.pi_ne_zero]
    ring
  · by_cases hsa2 : s ≤ 2 * a
    · have ht0 : 0 ≤ Real.pi * s / (2 * a) := by positivity
      have ht1 : Real.pi * s / (2 * a) ≤ Real.pi := by
        simpa using scaled_parameter_le (c := 2) ha hsa2
      have hu0 :
          0 ≤ Real.pi * s / (2 * a) - Real.pi / 2 := by
        have := scaled_parameter_ge (c := 1) ha
          (by simpa using le_of_not_ge hsa)
        linarith
      have hu1 :
          Real.pi * s / (2 * a) - Real.pi / 2 ≤ Real.pi := by
        linarith
      rw [oddCosineSeries_eq_lower ht0 ht1,
        oddCosineSeries_eq_lower hu0 hu1]
      simp [yCoord, hsa, hsa2]
      field_simp [ha.ne', Real.pi_ne_zero]
      ring
    · by_cases hsa3 : s ≤ 3 * a
      · have htpi : Real.pi ≤ Real.pi * s / (2 * a) := by
          simpa using scaled_parameter_ge (c := 2) ha
            (le_of_not_ge hsa2)
        have ht2 : Real.pi * s / (2 * a) ≤ 2 * Real.pi := by
          have h := scaled_parameter_le (c := 4) ha hs4
          nlinarith
        have hu0 :
            0 ≤ Real.pi * s / (2 * a) - Real.pi / 2 := by
          linarith
        have hu1 :
            Real.pi * s / (2 * a) - Real.pi / 2 ≤ Real.pi := by
          have := scaled_parameter_le (c := 3) ha hsa3
          linarith
        rw [oddCosineSeries_eq_upper htpi ht2,
          oddCosineSeries_eq_lower hu0 hu1]
        simp [yCoord, hsa, hsa2, hsa3]
        field_simp [ha.ne', Real.pi_ne_zero]
        ring
      · have htpi : Real.pi ≤ Real.pi * s / (2 * a) := by
          have := scaled_parameter_ge (c := 2) ha
            (le_of_not_ge hsa2)
          linarith
        have ht2 : Real.pi * s / (2 * a) ≤ 2 * Real.pi := by
          have h := scaled_parameter_le (c := 4) ha hs4
          nlinarith
        have hupi :
            Real.pi ≤ Real.pi * s / (2 * a) - Real.pi / 2 := by
          have := scaled_parameter_ge (c := 3) ha
            (le_of_not_ge hsa3)
          linarith
        have hu2 :
            Real.pi * s / (2 * a) - Real.pi / 2 ≤ 2 * Real.pi := by
          linarith
        rw [oddCosineSeries_eq_upper htpi ht2,
          oddCosineSeries_eq_upper hupi hu2]
        simp [yCoord, hsa, hsa2, hsa3]
        field_simp [ha.ne', Real.pi_ne_zero]
        ring

private theorem xCoord_first {a s : ℝ} (hsa : s ≤ a) :
    xCoord a s = s := by
  simp [xCoord, hsa]

private theorem xCoord_second {a s : ℝ} (ha : 0 < a)
    (has : a ≤ s) (hs2 : s ≤ 2 * a) :
    xCoord a s = a := by
  unfold xCoord
  split_ifs <;> linarith

private theorem xCoord_third {a s : ℝ} (ha : 0 < a)
    (hs2 : 2 * a ≤ s) (hs3 : s ≤ 3 * a) :
    xCoord a s = 3 * a - s := by
  unfold xCoord
  split_ifs <;> linarith

private theorem xCoord_fourth {a s : ℝ} (ha : 0 < a)
    (hs3 : 3 * a ≤ s) :
    xCoord a s = 0 := by
  unfold xCoord
  split_ifs <;> linarith

private theorem yCoord_first {a s : ℝ} (hsa : s ≤ a) :
    yCoord a s = 0 := by
  simp [yCoord, hsa]

private theorem yCoord_second {a s : ℝ} (ha : 0 < a)
    (has : a ≤ s) (hs2 : s ≤ 2 * a) :
    yCoord a s = s - a := by
  unfold yCoord
  split_ifs <;> linarith

private theorem yCoord_third {a s : ℝ} (ha : 0 < a)
    (hs2 : 2 * a ≤ s) (hs3 : s ≤ 3 * a) :
    yCoord a s = a := by
  unfold yCoord
  split_ifs <;> linarith

private theorem yCoord_fourth {a s : ℝ} (ha : 0 < a)
    (hs3 : 3 * a ≤ s) (hs4 : s ≤ 4 * a) :
    yCoord a s = 4 * a - s := by
  unfold yCoord
  split_ifs <;> linarith

private theorem integral_affine (p q u v : ℝ) :
    (∫ s in u..v, p * s + q) =
      p * (v ^ 2 - u ^ 2) / 2 + q * (v - u) := by
  have hp : IntervalIntegrable (fun s : ℝ => p * s)
      MeasureTheory.volume u v :=
    (continuous_const.mul continuous_id).intervalIntegrable u v
  have hq : IntervalIntegrable (fun _s : ℝ => q)
      MeasureTheory.volume u v :=
    continuous_const.intervalIntegrable u v
  rw [intervalIntegral.integral_add hp hq,
    intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const]
  simp [smul_eq_mul]
  ring

private theorem integral_xCoord_mul_piecewise (a : ℝ) (ha : 0 < a)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ s in 0..4 * a, xCoord a s * g s) =
      (∫ s in 0..a, s * g s) +
        (∫ s in a..2 * a, a * g s) +
          ∫ s in 2 * a..3 * a, (3 * a - s) * g s := by
  have h01 : Set.EqOn
      (fun s : ℝ => s * g s) (fun s => xCoord a s * g s)
      (Set.uIcc 0 a) := by
    intro s hs
    rw [Set.uIcc_of_le ha.le] at hs
    change s * g s = xCoord a s * g s
    rw [xCoord_first hs.2]
  have h12 : Set.EqOn
      (fun s : ℝ => a * g s) (fun s => xCoord a s * g s)
      (Set.uIcc a (2 * a)) := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    change a * g s = xCoord a s * g s
    rw [xCoord_second ha hs.1 hs.2]
  have h23 : Set.EqOn
      (fun s : ℝ => (3 * a - s) * g s)
      (fun s => xCoord a s * g s)
      (Set.uIcc (2 * a) (3 * a)) := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    change (3 * a - s) * g s = xCoord a s * g s
    rw [xCoord_third ha hs.1 hs.2]
  have h34 : Set.EqOn
      (fun _s : ℝ => 0) (fun s => xCoord a s * g s)
      (Set.uIcc (3 * a) (4 * a)) := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    change 0 = xCoord a s * g s
    rw [xCoord_fourth ha hs.1]
    ring
  have hi01 : IntervalIntegrable (fun s => xCoord a s * g s)
      MeasureTheory.volume 0 a :=
    IntervalIntegrable.congr (h01.mono Set.uIoc_subset_uIcc)
      ((continuous_id.mul hg).intervalIntegrable 0 a)
  have hi12 : IntervalIntegrable (fun s => xCoord a s * g s)
      MeasureTheory.volume a (2 * a) :=
    IntervalIntegrable.congr (h12.mono Set.uIoc_subset_uIcc)
      ((continuous_const.mul hg).intervalIntegrable a (2 * a))
  have hi23 : IntervalIntegrable (fun s => xCoord a s * g s)
      MeasureTheory.volume (2 * a) (3 * a) :=
    IntervalIntegrable.congr (h23.mono Set.uIoc_subset_uIcc)
      (((continuous_const.sub continuous_id).mul hg).intervalIntegrable
        (2 * a) (3 * a))
  have hi34 : IntervalIntegrable (fun s => xCoord a s * g s)
      MeasureTheory.volume (3 * a) (4 * a) :=
    IntervalIntegrable.congr (h34.mono Set.uIoc_subset_uIcc)
      (continuous_const.intervalIntegrable (3 * a) (4 * a))
  have hsplit12 :=
    intervalIntegral.integral_add_adjacent_intervals hi01 hi12
  have hsplit23 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hi01.trans hi12) hi23
  have hsplit34 :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hi01.trans hi12).trans hi23) hi34
  calc
    (∫ s in 0..4 * a, xCoord a s * g s) =
        (∫ s in 0..a, xCoord a s * g s) +
          (∫ s in a..2 * a, xCoord a s * g s) +
            (∫ s in 2 * a..3 * a, xCoord a s * g s) +
              ∫ s in 3 * a..4 * a, xCoord a s * g s := by
      rw [← hsplit34, ← hsplit23, ← hsplit12]
    _ = _ := by
      rw [(intervalIntegral.integral_congr h01).symm,
        (intervalIntegral.integral_congr h12).symm,
        (intervalIntegral.integral_congr h23).symm,
        (intervalIntegral.integral_congr h34).symm]
      simp

private theorem integral_yCoord_mul_piecewise (a : ℝ) (ha : 0 < a)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ s in a..4 * a, yCoord a s * g s) =
      (∫ s in a..2 * a, (s - a) * g s) +
        (∫ s in 2 * a..3 * a, a * g s) +
          ∫ s in 3 * a..4 * a, (4 * a - s) * g s := by
  have h12 : Set.EqOn
      (fun s : ℝ => (s - a) * g s) (fun s => yCoord a s * g s)
      (Set.uIcc a (2 * a)) := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    change (s - a) * g s = yCoord a s * g s
    rw [yCoord_second ha hs.1 hs.2]
  have h23 : Set.EqOn
      (fun s : ℝ => a * g s) (fun s => yCoord a s * g s)
      (Set.uIcc (2 * a) (3 * a)) := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    change a * g s = yCoord a s * g s
    rw [yCoord_third ha hs.1 hs.2]
  have h34 : Set.EqOn
      (fun s : ℝ => (4 * a - s) * g s)
      (fun s => yCoord a s * g s)
      (Set.uIcc (3 * a) (4 * a)) := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    change (4 * a - s) * g s = yCoord a s * g s
    rw [yCoord_fourth ha hs.1 hs.2]
  have hi12 : IntervalIntegrable (fun s => yCoord a s * g s)
      MeasureTheory.volume a (2 * a) :=
    IntervalIntegrable.congr (h12.mono Set.uIoc_subset_uIcc)
      (((continuous_id.sub continuous_const).mul hg).intervalIntegrable
        a (2 * a))
  have hi23 : IntervalIntegrable (fun s => yCoord a s * g s)
      MeasureTheory.volume (2 * a) (3 * a) :=
    IntervalIntegrable.congr (h23.mono Set.uIoc_subset_uIcc)
      ((continuous_const.mul hg).intervalIntegrable (2 * a) (3 * a))
  have hi34 : IntervalIntegrable (fun s => yCoord a s * g s)
      MeasureTheory.volume (3 * a) (4 * a) :=
    IntervalIntegrable.congr (h34.mono Set.uIoc_subset_uIcc)
      (((continuous_const.sub continuous_id).mul hg).intervalIntegrable
        (3 * a) (4 * a))
  have hsplit23 :=
    intervalIntegral.integral_add_adjacent_intervals hi12 hi23
  have hsplit34 :=
    intervalIntegral.integral_add_adjacent_intervals (hi12.trans hi23) hi34
  calc
    (∫ s in a..4 * a, yCoord a s * g s) =
        (∫ s in a..2 * a, yCoord a s * g s) +
          (∫ s in 2 * a..3 * a, yCoord a s * g s) +
            ∫ s in 3 * a..4 * a, yCoord a s * g s := by
      rw [← hsplit34, ← hsplit23]
    _ = _ := by
      rw [(intervalIntegral.integral_congr h12).symm,
        (intervalIntegral.integral_congr h23).symm,
        (intervalIntegral.integral_congr h34).symm]

private def affineCosPrimitive (p q w s : ℝ) : ℝ :=
  (p * s + q) * Real.sin (w * s) / w +
    p * Real.cos (w * s) / w ^ 2

private theorem hasDerivAt_affineCosPrimitive
    (p q w : ℝ) (hw : w ≠ 0) (s : ℝ) :
    HasDerivAt (affineCosPrimitive p q w)
      ((p * s + q) * Real.cos (w * s)) s := by
  have hinner : HasDerivAt (fun t : ℝ => w * t) w s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul w
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (w * t))
      (Real.cos (w * s) * w) s :=
    (Real.hasDerivAt_sin (w * s)).comp s hinner
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (w * t))
      (-Real.sin (w * s) * w) s :=
    (Real.hasDerivAt_cos (w * s)).comp s hinner
  have haff : HasDerivAt (fun t : ℝ => p * t + q) p s := by
    simpa only [zero_mul, mul_one, zero_add, add_zero] using
      (((hasDerivAt_const s p).mul (hasDerivAt_id s)).add
        (hasDerivAt_const s q))
  unfold affineCosPrimitive
  convert ((haff.mul hsin).div_const w).add
    ((hcos.const_mul p).div_const (w ^ 2)) using 1
  field_simp [hw]
  ring

private theorem integral_affine_mul_cos (p q w : ℝ) (hw : w ≠ 0)
    (u v : ℝ) :
    (∫ s in u..v, (p * s + q) * Real.cos (w * s)) =
      affineCosPrimitive p q w v - affineCosPrimitive p q w u := by
  have hc : Continuous
      (fun s : ℝ => (p * s + q) * Real.cos (w * s)) := by
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_affineCosPrimitive p q w hw s)
    (hc.intervalIntegrable u v)

private def affineSinPrimitive (p q w s : ℝ) : ℝ :=
  -((p * s + q) * Real.cos (w * s)) / w +
    p * Real.sin (w * s) / w ^ 2

private theorem hasDerivAt_affineSinPrimitive
    (p q w : ℝ) (hw : w ≠ 0) (s : ℝ) :
    HasDerivAt (affineSinPrimitive p q w)
      ((p * s + q) * Real.sin (w * s)) s := by
  have hinner : HasDerivAt (fun t : ℝ => w * t) w s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul w
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (w * t))
      (Real.cos (w * s) * w) s :=
    (Real.hasDerivAt_sin (w * s)).comp s hinner
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (w * t))
      (-Real.sin (w * s) * w) s :=
    (Real.hasDerivAt_cos (w * s)).comp s hinner
  have haff : HasDerivAt (fun t : ℝ => p * t + q) p s := by
    simpa only [zero_mul, mul_one, zero_add, add_zero] using
      (((hasDerivAt_const s p).mul (hasDerivAt_id s)).add
        (hasDerivAt_const s q))
  unfold affineSinPrimitive
  convert ((haff.mul hcos).neg.div_const w).add
    ((hsin.const_mul p).div_const (w ^ 2)) using 1
  field_simp [hw]
  ring

private theorem integral_affine_mul_sin (p q w : ℝ) (hw : w ≠ 0)
    (u v : ℝ) :
    (∫ s in u..v, (p * s + q) * Real.sin (w * s)) =
      affineSinPrimitive p q w v - affineSinPrimitive p q w u := by
  have hc : Continuous
      (fun s : ℝ => (p * s + q) * Real.sin (w * s)) := by
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_affineSinPrimitive p q w hw s)
    (hc.intervalIntegrable u v)

private theorem xCosIntegral_formula (a : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) :
    xCosIntegral a n =
      2 * a / (((n : ℝ) * Real.pi) ^ 2) *
        (Real.cos ((n : ℝ) * Real.pi / 2) - 1 -
          Real.cos (3 * ((n : ℝ) * Real.pi) / 2) +
          Real.cos ((n : ℝ) * Real.pi)) := by
  let w : ℝ := (n : ℝ) * Real.pi / (2 * a)
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hw : w ≠ 0 := by
    dsimp [w]
    positivity
  have harg (s : ℝ) :
      (n : ℝ) * Real.pi * s / (2 * a) = w * s := by
    dsimp [w]
    ring
  have hwa : w * a = (n : ℝ) * Real.pi / 2 := by
    dsimp [w]
    field_simp [ha.ne']
  have hw2 : w * (2 * a) = (n : ℝ) * Real.pi := by
    dsimp [w]
    field_simp [ha.ne']
  have hw3 : w * (3 * a) = 3 * ((n : ℝ) * Real.pi) / 2 := by
    dsimp [w]
    field_simp [ha.ne']
  have hi :
      (∫ s in 0..4 * a,
        xCoord a s *
          Real.cos ((n : ℝ) * Real.pi * s / (2 * a))) =
        (∫ s in 0..a, s * Real.cos (w * s)) +
          (∫ s in a..2 * a, a * Real.cos (w * s)) +
            ∫ s in 2 * a..3 * a,
              (3 * a - s) * Real.cos (w * s) := by
    have hrewrite : (∫ s in 0..4 * a,
        xCoord a s *
          Real.cos ((n : ℝ) * Real.pi * s / (2 * a))) =
        ∫ s in 0..4 * a, xCoord a s * Real.cos (w * s) := by
      apply intervalIntegral.integral_congr
      intro s _
      change xCoord a s *
          Real.cos ((n : ℝ) * Real.pi * s / (2 * a)) =
        xCoord a s * Real.cos (w * s)
      rw [harg]
    rw [hrewrite]
    simpa using integral_xCoord_mul_piecewise a ha
      (fun s => Real.cos (w * s))
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have h1 :
      (∫ s in 0..a, s * Real.cos (w * s)) =
        affineCosPrimitive 1 0 w a -
          affineCosPrimitive 1 0 w 0 := by
    rw [show (∫ s in 0..a, s * Real.cos (w * s)) =
        ∫ s in 0..a, (1 * s + 0) * Real.cos (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_cos 1 0 w hw]
  have h2 :
      (∫ s in a..2 * a, a * Real.cos (w * s)) =
        affineCosPrimitive 0 a w (2 * a) -
          affineCosPrimitive 0 a w a := by
    rw [show (∫ s in a..2 * a, a * Real.cos (w * s)) =
        ∫ s in a..2 * a, (0 * s + a) * Real.cos (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_cos 0 a w hw]
  have h3 :
      (∫ s in 2 * a..3 * a,
          (3 * a - s) * Real.cos (w * s)) =
        affineCosPrimitive (-1) (3 * a) w (3 * a) -
          affineCosPrimitive (-1) (3 * a) w (2 * a) := by
    rw [show (∫ s in 2 * a..3 * a,
          (3 * a - s) * Real.cos (w * s)) =
        ∫ s in 2 * a..3 * a,
          ((-1) * s + 3 * a) * Real.cos (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_cos (-1) (3 * a) w hw]
  unfold xCosIntegral
  rw [hi, h1, h2, h3]
  unfold affineCosPrimitive
  rw [hwa, hw2, hw3]
  simp
  dsimp [w]
  field_simp [ha.ne', hn0, Real.pi_ne_zero]
  ring

private theorem xSinIntegral_formula (a : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) :
    xSinIntegral a n =
      2 * a / ((n : ℝ) ^ 2 * Real.pi ^ 2) *
        (Real.sin ((n : ℝ) * Real.pi / 2) -
          Real.sin (3 * ((n : ℝ) * Real.pi) / 2)) := by
  let w : ℝ := (n : ℝ) * Real.pi / (2 * a)
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hw : w ≠ 0 := by
    dsimp [w]
    positivity
  have harg (s : ℝ) :
      (n : ℝ) * Real.pi * s / (2 * a) = w * s := by
    dsimp [w]
    ring
  have hwa : w * a = (n : ℝ) * Real.pi / 2 := by
    dsimp [w]
    field_simp [ha.ne']
  have hw2 : w * (2 * a) = (n : ℝ) * Real.pi := by
    dsimp [w]
    field_simp [ha.ne']
  have hw3 : w * (3 * a) = 3 * ((n : ℝ) * Real.pi) / 2 := by
    dsimp [w]
    field_simp [ha.ne']
  have hi :
      (∫ s in 0..4 * a,
        xCoord a s *
          Real.sin ((n : ℝ) * Real.pi * s / (2 * a))) =
        (∫ s in 0..a, s * Real.sin (w * s)) +
          (∫ s in a..2 * a, a * Real.sin (w * s)) +
            ∫ s in 2 * a..3 * a,
              (3 * a - s) * Real.sin (w * s) := by
    have hrewrite : (∫ s in 0..4 * a,
        xCoord a s *
          Real.sin ((n : ℝ) * Real.pi * s / (2 * a))) =
        ∫ s in 0..4 * a, xCoord a s * Real.sin (w * s) := by
      apply intervalIntegral.integral_congr
      intro s _
      change xCoord a s *
          Real.sin ((n : ℝ) * Real.pi * s / (2 * a)) =
        xCoord a s * Real.sin (w * s)
      rw [harg]
    rw [hrewrite]
    simpa using integral_xCoord_mul_piecewise a ha
      (fun s => Real.sin (w * s))
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have h1 :
      (∫ s in 0..a, s * Real.sin (w * s)) =
        affineSinPrimitive 1 0 w a -
          affineSinPrimitive 1 0 w 0 := by
    rw [show (∫ s in 0..a, s * Real.sin (w * s)) =
        ∫ s in 0..a, (1 * s + 0) * Real.sin (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_sin 1 0 w hw]
  have h2 :
      (∫ s in a..2 * a, a * Real.sin (w * s)) =
        affineSinPrimitive 0 a w (2 * a) -
          affineSinPrimitive 0 a w a := by
    rw [show (∫ s in a..2 * a, a * Real.sin (w * s)) =
        ∫ s in a..2 * a, (0 * s + a) * Real.sin (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_sin 0 a w hw]
  have h3 :
      (∫ s in 2 * a..3 * a,
          (3 * a - s) * Real.sin (w * s)) =
        affineSinPrimitive (-1) (3 * a) w (3 * a) -
          affineSinPrimitive (-1) (3 * a) w (2 * a) := by
    rw [show (∫ s in 2 * a..3 * a,
          (3 * a - s) * Real.sin (w * s)) =
        ∫ s in 2 * a..3 * a,
          ((-1) * s + 3 * a) * Real.sin (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_sin (-1) (3 * a) w hw]
  unfold xSinIntegral
  rw [hi, h1, h2, h3]
  unfold affineSinPrimitive
  rw [hwa, hw2, hw3]
  simp
  dsimp [w]
  field_simp [ha.ne', hn0, Real.pi_ne_zero]
  ring

private theorem integral_yCoord_mul_piecewise_full
    (a : ℝ) (ha : 0 < a) (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ s in 0..4 * a, yCoord a s * g s) =
      (∫ s in a..2 * a, (s - a) * g s) +
        (∫ s in 2 * a..3 * a, a * g s) +
          ∫ s in 3 * a..4 * a, (4 * a - s) * g s := by
  have h01 : Set.EqOn
      (fun _s : ℝ => 0) (fun s => yCoord a s * g s)
      (Set.uIcc 0 a) := by
    intro s hs
    rw [Set.uIcc_of_le ha.le] at hs
    change 0 = yCoord a s * g s
    rw [yCoord_first hs.2]
    ring
  have h12 : Set.EqOn
      (fun s : ℝ => (s - a) * g s) (fun s => yCoord a s * g s)
      (Set.uIcc a (2 * a)) := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    change (s - a) * g s = yCoord a s * g s
    rw [yCoord_second ha hs.1 hs.2]
  have h23 : Set.EqOn
      (fun s : ℝ => a * g s) (fun s => yCoord a s * g s)
      (Set.uIcc (2 * a) (3 * a)) := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    change a * g s = yCoord a s * g s
    rw [yCoord_third ha hs.1 hs.2]
  have h34 : Set.EqOn
      (fun s : ℝ => (4 * a - s) * g s)
      (fun s => yCoord a s * g s)
      (Set.uIcc (3 * a) (4 * a)) := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    change (4 * a - s) * g s = yCoord a s * g s
    rw [yCoord_fourth ha hs.1 hs.2]
  have hi01 : IntervalIntegrable (fun s => yCoord a s * g s)
      MeasureTheory.volume 0 a :=
    IntervalIntegrable.congr (h01.mono Set.uIoc_subset_uIcc)
      (continuous_const.intervalIntegrable 0 a)
  have hi12 : IntervalIntegrable (fun s => yCoord a s * g s)
      MeasureTheory.volume a (2 * a) :=
    IntervalIntegrable.congr (h12.mono Set.uIoc_subset_uIcc)
      (((continuous_id.sub continuous_const).mul hg).intervalIntegrable
        a (2 * a))
  have hi23 : IntervalIntegrable (fun s => yCoord a s * g s)
      MeasureTheory.volume (2 * a) (3 * a) :=
    IntervalIntegrable.congr (h23.mono Set.uIoc_subset_uIcc)
      ((continuous_const.mul hg).intervalIntegrable (2 * a) (3 * a))
  have hi34 : IntervalIntegrable (fun s => yCoord a s * g s)
      MeasureTheory.volume (3 * a) (4 * a) :=
    IntervalIntegrable.congr (h34.mono Set.uIoc_subset_uIcc)
      (((continuous_const.sub continuous_id).mul hg).intervalIntegrable
        (3 * a) (4 * a))
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hi01
      ((hi12.trans hi23).trans hi34)
  calc
    (∫ s in 0..4 * a, yCoord a s * g s) =
        (∫ s in 0..a, yCoord a s * g s) +
          ∫ s in a..4 * a, yCoord a s * g s := hsplit.symm
    _ = ∫ s in a..4 * a, yCoord a s * g s := by
      rw [(intervalIntegral.integral_congr h01).symm]
      simp
    _ = _ := integral_yCoord_mul_piecewise a ha g hg

private theorem yCosIntegral_formula (a : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) :
    yCosIntegral a n =
      2 * a / ((n : ℝ) ^ 2 * Real.pi ^ 2) *
        (Real.cos ((n : ℝ) * Real.pi) -
          Real.cos ((n : ℝ) * Real.pi / 2) - 1 +
          Real.cos (3 * ((n : ℝ) * Real.pi) / 2)) := by
  let w : ℝ := (n : ℝ) * Real.pi / (2 * a)
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hw : w ≠ 0 := by
    dsimp [w]
    positivity
  have harg (s : ℝ) :
      (n : ℝ) * Real.pi * s / (2 * a) = w * s := by
    dsimp [w]
    ring
  have hwa : w * a = (n : ℝ) * Real.pi / 2 := by
    dsimp [w]
    field_simp [ha.ne']
  have hw2 : w * (2 * a) = (n : ℝ) * Real.pi := by
    dsimp [w]
    field_simp [ha.ne']
  have hw3 : w * (3 * a) = 3 * ((n : ℝ) * Real.pi) / 2 := by
    dsimp [w]
    field_simp [ha.ne']
  have hw4 : w * (4 * a) = 2 * ((n : ℝ) * Real.pi) := by
    dsimp [w]
    field_simp [ha.ne']
    ring
  have hi :
      (∫ s in 0..4 * a,
        yCoord a s *
          Real.cos ((n : ℝ) * Real.pi * s / (2 * a))) =
        (∫ s in a..2 * a, (s - a) * Real.cos (w * s)) +
          (∫ s in 2 * a..3 * a, a * Real.cos (w * s)) +
            ∫ s in 3 * a..4 * a,
              (4 * a - s) * Real.cos (w * s) := by
    have hrewrite : (∫ s in 0..4 * a,
        yCoord a s *
          Real.cos ((n : ℝ) * Real.pi * s / (2 * a))) =
        ∫ s in 0..4 * a, yCoord a s * Real.cos (w * s) := by
      apply intervalIntegral.integral_congr
      intro s _
      change yCoord a s *
          Real.cos ((n : ℝ) * Real.pi * s / (2 * a)) =
        yCoord a s * Real.cos (w * s)
      rw [harg]
    rw [hrewrite]
    simpa using integral_yCoord_mul_piecewise_full a ha
      (fun s => Real.cos (w * s))
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have h1 :
      (∫ s in a..2 * a, (s - a) * Real.cos (w * s)) =
        affineCosPrimitive 1 (-a) w (2 * a) -
          affineCosPrimitive 1 (-a) w a := by
    rw [show (∫ s in a..2 * a, (s - a) * Real.cos (w * s)) =
        ∫ s in a..2 * a,
          (1 * s + (-a)) * Real.cos (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_cos 1 (-a) w hw]
  have h2 :
      (∫ s in 2 * a..3 * a, a * Real.cos (w * s)) =
        affineCosPrimitive 0 a w (3 * a) -
          affineCosPrimitive 0 a w (2 * a) := by
    rw [show (∫ s in 2 * a..3 * a, a * Real.cos (w * s)) =
        ∫ s in 2 * a..3 * a,
          (0 * s + a) * Real.cos (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_cos 0 a w hw]
  have h3 :
      (∫ s in 3 * a..4 * a,
          (4 * a - s) * Real.cos (w * s)) =
        affineCosPrimitive (-1) (4 * a) w (4 * a) -
          affineCosPrimitive (-1) (4 * a) w (3 * a) := by
    rw [show (∫ s in 3 * a..4 * a,
          (4 * a - s) * Real.cos (w * s)) =
        ∫ s in 3 * a..4 * a,
          ((-1) * s + 4 * a) * Real.cos (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_cos (-1) (4 * a) w hw]
  unfold yCosIntegral
  rw [hi, h1, h2, h3]
  unfold affineCosPrimitive
  rw [hwa, hw2, hw3, hw4]
  have hsin4 : Real.sin (2 * ((n : ℝ) * Real.pi)) = 0 := by
    rw [show 2 * ((n : ℝ) * Real.pi) =
      ((2 * n : ℕ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_nat_mul_pi]
  have hcos4 : Real.cos (2 * ((n : ℝ) * Real.pi)) = 1 := by
    convert Real.cos_nat_mul_two_pi n using 1 <;> ring
  rw [hsin4, hcos4]
  simp
  dsimp [w]
  field_simp [ha.ne', hn0, Real.pi_ne_zero]
  ring

private theorem ySinIntegral_formula (a : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) :
    ySinIntegral a n =
      2 * a / ((n : ℝ) ^ 2 * Real.pi ^ 2) *
        (Real.sin (3 * ((n : ℝ) * Real.pi) / 2) -
          Real.sin ((n : ℝ) * Real.pi / 2)) := by
  let w : ℝ := (n : ℝ) * Real.pi / (2 * a)
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hw : w ≠ 0 := by
    dsimp [w]
    positivity
  have harg (s : ℝ) :
      (n : ℝ) * Real.pi * s / (2 * a) = w * s := by
    dsimp [w]
    ring
  have hwa : w * a = (n : ℝ) * Real.pi / 2 := by
    dsimp [w]
    field_simp [ha.ne']
  have hw2 : w * (2 * a) = (n : ℝ) * Real.pi := by
    dsimp [w]
    field_simp [ha.ne']
  have hw3 : w * (3 * a) = 3 * ((n : ℝ) * Real.pi) / 2 := by
    dsimp [w]
    field_simp [ha.ne']
  have hw4 : w * (4 * a) = 2 * ((n : ℝ) * Real.pi) := by
    dsimp [w]
    field_simp [ha.ne']
    ring
  have hi :
      (∫ s in 0..4 * a,
        yCoord a s *
          Real.sin ((n : ℝ) * Real.pi * s / (2 * a))) =
        (∫ s in a..2 * a, (s - a) * Real.sin (w * s)) +
          (∫ s in 2 * a..3 * a, a * Real.sin (w * s)) +
            ∫ s in 3 * a..4 * a,
              (4 * a - s) * Real.sin (w * s) := by
    have hrewrite : (∫ s in 0..4 * a,
        yCoord a s *
          Real.sin ((n : ℝ) * Real.pi * s / (2 * a))) =
        ∫ s in 0..4 * a, yCoord a s * Real.sin (w * s) := by
      apply intervalIntegral.integral_congr
      intro s _
      change yCoord a s *
          Real.sin ((n : ℝ) * Real.pi * s / (2 * a)) =
        yCoord a s * Real.sin (w * s)
      rw [harg]
    rw [hrewrite]
    simpa using integral_yCoord_mul_piecewise_full a ha
      (fun s => Real.sin (w * s))
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have h1 :
      (∫ s in a..2 * a, (s - a) * Real.sin (w * s)) =
        affineSinPrimitive 1 (-a) w (2 * a) -
          affineSinPrimitive 1 (-a) w a := by
    rw [show (∫ s in a..2 * a, (s - a) * Real.sin (w * s)) =
        ∫ s in a..2 * a,
          (1 * s + (-a)) * Real.sin (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_sin 1 (-a) w hw]
  have h2 :
      (∫ s in 2 * a..3 * a, a * Real.sin (w * s)) =
        affineSinPrimitive 0 a w (3 * a) -
          affineSinPrimitive 0 a w (2 * a) := by
    rw [show (∫ s in 2 * a..3 * a, a * Real.sin (w * s)) =
        ∫ s in 2 * a..3 * a,
          (0 * s + a) * Real.sin (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_sin 0 a w hw]
  have h3 :
      (∫ s in 3 * a..4 * a,
          (4 * a - s) * Real.sin (w * s)) =
        affineSinPrimitive (-1) (4 * a) w (4 * a) -
          affineSinPrimitive (-1) (4 * a) w (3 * a) := by
    rw [show (∫ s in 3 * a..4 * a,
          (4 * a - s) * Real.sin (w * s)) =
        ∫ s in 3 * a..4 * a,
          ((-1) * s + 4 * a) * Real.sin (w * s) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine_mul_sin (-1) (4 * a) w hw]
  unfold ySinIntegral
  rw [hi, h1, h2, h3]
  unfold affineSinPrimitive
  rw [hwa, hw2, hw3, hw4]
  have hsin4 : Real.sin (2 * ((n : ℝ) * Real.pi)) = 0 := by
    rw [show 2 * ((n : ℝ) * Real.pi) =
      ((2 * n : ℕ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_nat_mul_pi]
  have hcos4 : Real.cos (2 * ((n : ℝ) * Real.pi)) = 1 := by
    convert Real.cos_nat_mul_two_pi n using 1 <;> ring
  rw [hsin4, hcos4]
  simp
  dsimp [w]
  field_simp [ha.ne', hn0, Real.pi_ne_zero]
  ring

private theorem sin_three_nat_pi_div_two (n : ℕ) :
    Real.sin (3 * ((n : ℝ) * Real.pi) / 2) =
      (-1 : ℝ) ^ n * Real.sin ((n : ℝ) * Real.pi / 2) := by
  rw [show 3 * ((n : ℝ) * Real.pi) / 2 =
      (n : ℝ) * Real.pi + (n : ℝ) * Real.pi / 2 by ring,
    Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  ring

private theorem cos_three_nat_pi_div_two (n : ℕ) :
    Real.cos (3 * ((n : ℝ) * Real.pi) / 2) =
      (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * Real.pi / 2) := by
  rw [show 3 * ((n : ℝ) * Real.pi) / 2 =
      (n : ℝ) * Real.pi + (n : ℝ) * Real.pi / 2 by ring,
    Real.cos_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  ring

private theorem sin_odd_nat_pi_div_two (k : ℕ) :
    Real.sin (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2) =
      (-1 : ℝ) ^ k := by
  rw [show (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2) =
      (k : ℝ) * Real.pi + Real.pi / 2 by push_cast; ring,
    Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi,
    Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

private theorem cos_odd_nat_pi_div_two (k : ℕ) :
    Real.cos (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2) = 0 := by
  rw [show (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2) =
      (k : ℝ) * Real.pi + Real.pi / 2 by push_cast; ring,
    Real.cos_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi,
    Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

private theorem oddIndex_injective :
    Function.Injective (fun k : ℕ => 2 * k + 1) := by
  intro m n h
  exact mul_left_cancel₀ (by decide : (2 : ℕ) ≠ 0)
    (Nat.add_right_cancel h)

private theorem odd_inv_sq_summable :
    Summable (fun k : ℕ =>
      1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
  exact (Real.summable_one_div_nat_pow.mpr
    (by norm_num : 1 < 2)).comp_injective oddIndex_injective

private theorem odd_bounded_div_sq_summable
    (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 1) :
    Summable (fun k : ℕ =>
      u k / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
  apply Summable.of_norm_bounded odd_inv_sq_summable
  intro k
  rw [Real.norm_eq_abs, abs_div,
    abs_of_nonneg (sq_nonneg (((2 * k + 1 : ℕ) : ℝ)))]
  exact div_le_div_of_nonneg_right (hu k)
    (sq_nonneg (((2 * k + 1 : ℕ) : ℝ)))

private theorem odd_cos_summable (a s : ℝ) :
    Summable (fun k : ℕ =>
      1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
        Real.cos (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))) := by
  have h := odd_bounded_div_sq_summable
    (fun k : ℕ =>
      Real.cos (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a)))
    (fun k => Real.abs_cos_le_one _)
  exact h.congr (fun k => by ring)

private theorem odd_signed_sin_summable (a s : ℝ) (r : ℕ) :
    Summable (fun k : ℕ =>
      (-1 : ℝ) ^ (k + r) / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
        Real.sin (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))) := by
  have hbound : ∀ k : ℕ,
      |(-1 : ℝ) ^ (k + r) *
        Real.sin (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))| ≤ 1 := by
    intro k
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact Real.abs_sin_le_one _
  have h := odd_bounded_div_sq_summable
    (fun k : ℕ => (-1 : ℝ) ^ (k + r) *
      Real.sin (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a)))
    hbound
  exact h.congr (fun k => by ring)

private theorem generalSeries_eq_xSeries_of_coefficients
    (a : ℝ) (c d : ℕ → ℝ) (s : ℝ)
    (hc0 : c 0 = a)
    (hce : ∀ k : ℕ, c (2 * (k + 1)) = 0)
    (hco : ∀ k : ℕ,
      c (2 * k + 1) =
        -(4 * a /
          (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2))))
    (hde : ∀ k : ℕ, d (2 * (k + 1)) = 0)
    (hdo : ∀ k : ℕ,
      d (2 * k + 1) =
        4 * a * (-1 : ℝ) ^ k /
          (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2))) :
    generalSeries a c d s = xSeries a s := by
  let C : ℕ → ℝ := fun k =>
    1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
      Real.cos (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))
  let S : ℕ → ℝ := fun k =>
    (-1 : ℝ) ^ k / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
      Real.sin (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))
  let G : ℕ → ℝ := fun k =>
    (-4 * a / Real.pi ^ 2) * C k +
      (4 * a / Real.pi ^ 2) * S k
  let F : ℕ → ℝ := fun k =>
    let n : ℕ := k + 1
    c n * Real.cos ((n : ℝ) * Real.pi * s / (2 * a)) +
      d n * Real.sin ((n : ℝ) * Real.pi * s / (2 * a))
  have hC : Summable C := by
    exact odd_cos_summable a s
  have hS : Summable S := by
    simpa [S] using odd_signed_sin_summable a s 0
  have hG : Summable G := by
    exact (hC.mul_left (-4 * a / Real.pi ^ 2)).add
      (hS.mul_left (4 * a / Real.pi ^ 2))
  have heven : HasSum (fun k => F (2 * k)) (∑' k, G k) := by
    refine HasSum.congr_fun hG.hasSum ?_
    intro k
    dsimp [F, G, C, S]
    rw [hco k, hdo k]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hodd : HasSum (fun k => F (2 * k + 1)) 0 := by
    refine HasSum.congr_fun (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) ?_
    intro k
    dsimp [F]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
      hce k, hde k]
    ring
  have htail : (∑' k, F k) = ∑' k, G k := by
    have h := (HasSum.even_add_odd heven hodd).tsum_eq
    simpa using h
  have hGsum :
      (∑' k, G k) =
        (-4 * a / Real.pi ^ 2) * ∑' k, C k +
          (4 * a / Real.pi ^ 2) * ∑' k, S k := by
    change
      (∑' k, ((-4 * a / Real.pi ^ 2) * C k +
        (4 * a / Real.pi ^ 2) * S k)) = _
    rw [(hC.mul_left _).tsum_add (hS.mul_left _),
      tsum_mul_left, tsum_mul_left]
  unfold generalSeries xSeries
  change c 0 / 2 + ∑' k, F k =
    a / 2 - 4 * a / Real.pi ^ 2 * ∑' k, C k +
      4 * a / Real.pi ^ 2 * ∑' k, S k
  rw [hc0, htail, hGsum]
  ring

private theorem generalSeries_eq_ySeries_of_coefficients
    (a : ℝ) (c d : ℕ → ℝ) (s : ℝ)
    (hc0 : c 0 = a)
    (hce : ∀ k : ℕ, c (2 * (k + 1)) = 0)
    (hco : ∀ k : ℕ,
      c (2 * k + 1) =
        -(4 * a /
          (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2))))
    (hde : ∀ k : ℕ, d (2 * (k + 1)) = 0)
    (hdo : ∀ k : ℕ,
      d (2 * k + 1) =
        4 * a * (-1 : ℝ) ^ (k + 1) /
          (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2))) :
    generalSeries a c d s = ySeries a s := by
  let C : ℕ → ℝ := fun k =>
    1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
      Real.cos (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))
  let S : ℕ → ℝ := fun k =>
    (-1 : ℝ) ^ (k + 1) / (((2 * k + 1 : ℕ) : ℝ) ^ 2) *
      Real.sin (((2 * k + 1 : ℕ) : ℝ) * Real.pi * s / (2 * a))
  let G : ℕ → ℝ := fun k =>
    (-4 * a / Real.pi ^ 2) * C k +
      (4 * a / Real.pi ^ 2) * S k
  let F : ℕ → ℝ := fun k =>
    let n : ℕ := k + 1
    c n * Real.cos ((n : ℝ) * Real.pi * s / (2 * a)) +
      d n * Real.sin ((n : ℝ) * Real.pi * s / (2 * a))
  have hC : Summable C := by
    exact odd_cos_summable a s
  have hS : Summable S := by
    exact odd_signed_sin_summable a s 1
  have hG : Summable G := by
    exact (hC.mul_left (-4 * a / Real.pi ^ 2)).add
      (hS.mul_left (4 * a / Real.pi ^ 2))
  have heven : HasSum (fun k => F (2 * k)) (∑' k, G k) := by
    refine HasSum.congr_fun hG.hasSum ?_
    intro k
    dsimp [F, G, C, S]
    rw [hco k, hdo k]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hodd : HasSum (fun k => F (2 * k + 1)) 0 := by
    refine HasSum.congr_fun (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) ?_
    intro k
    dsimp [F]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
      hce k, hde k]
    ring
  have htail : (∑' k, F k) = ∑' k, G k := by
    have h := (HasSum.even_add_odd heven hodd).tsum_eq
    simpa using h
  have hGsum :
      (∑' k, G k) =
        (-4 * a / Real.pi ^ 2) * ∑' k, C k +
          (4 * a / Real.pi ^ 2) * ∑' k, S k := by
    change
      (∑' k, ((-4 * a / Real.pi ^ 2) * C k +
        (4 * a / Real.pi ^ 2) * S k)) = _
    rw [(hC.mul_left _).tsum_add (hS.mul_left _),
      tsum_mul_left, tsum_mul_left]
  unfold generalSeries ySeries
  change c 0 / 2 + ∑' k, F k =
    a / 2 - 4 * a / Real.pi ^ 2 * ∑' k, C k +
      4 * a / Real.pi ^ 2 * ∑' k, S k
  rw [hc0, htail, hGsum]
  ring

private theorem xMeanIntegral_eq_a (a : ℝ) (ha : 0 < a) :
    1 / (2 * a) * (∫ s in 0..4 * a, xCoord a s) = a := by
  have hpiece :=
    integral_xCoord_mul_piecewise a ha (fun _ => 1) continuous_const
  have hx :
      (∫ s in 0..4 * a, xCoord a s) =
        (∫ s in 0..a, s) +
          (∫ _s in a..2 * a, a) +
            ∫ s in 2 * a..3 * a, 3 * a - s := by
    convert hpiece using 1 <;> simp
  rw [hx]
  rw [show (∫ s in 0..a, s) =
      1 * (a ^ 2 - 0 ^ 2) / 2 + 0 * (a - 0) by
    convert integral_affine 1 0 0 a using 1 <;> ring,
    show (∫ _s in a..2 * a, a) =
      0 * ((2 * a) ^ 2 - a ^ 2) / 2 + a * (2 * a - a) by
    convert integral_affine 0 a a (2 * a) using 1 <;> ring,
    show (∫ s in 2 * a..3 * a, 3 * a - s) =
      (-1) * ((3 * a) ^ 2 - (2 * a) ^ 2) / 2 +
        (3 * a) * (3 * a - 2 * a) by
    convert integral_affine (-1) (3 * a) (2 * a) (3 * a) using 1 <;>
      ring]
  field_simp [ha.ne']
  ring

private theorem yMeanIntegral_eq_a (a : ℝ) (ha : 0 < a) :
    1 / (2 * a) * (∫ s in 0..4 * a, yCoord a s) = a := by
  have hpiece :=
    integral_yCoord_mul_piecewise_full a ha (fun _ => 1) continuous_const
  have hy :
      (∫ s in 0..4 * a, yCoord a s) =
        (∫ s in a..2 * a, s - a) +
          (∫ _s in 2 * a..3 * a, a) +
            ∫ s in 3 * a..4 * a, 4 * a - s := by
    convert hpiece using 1 <;> simp
  rw [hy]
  rw [show (∫ s in a..2 * a, s - a) =
      1 * ((2 * a) ^ 2 - a ^ 2) / 2 + (-a) * (2 * a - a) by
    rw [show (∫ s in a..2 * a, s - a) =
        ∫ s in a..2 * a, 1 * s + (-a) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine],
    show (∫ _s in 2 * a..3 * a, a) =
      0 * ((3 * a) ^ 2 - (2 * a) ^ 2) / 2 +
        a * (3 * a - 2 * a) by
    convert integral_affine 0 a (2 * a) (3 * a) using 1 <;> ring,
    show (∫ s in 3 * a..4 * a, 4 * a - s) =
      (-1) * ((4 * a) ^ 2 - (3 * a) ^ 2) / 2 +
        (4 * a) * (4 * a - 3 * a) by
    convert integral_affine (-1) (4 * a) (3 * a) (4 * a) using 1 <;>
      ring]
  field_simp [ha.ne']
  ring

theorem gap1 (a : ℝ) (c d : ℕ → ℝ) (ha : 0 < a)
    (hc0 : c 0 = 1 / (2 * a) * ∫ s in 0..4 * a, xCoord a s)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = xCosIntegral a n)
    (hd : ∀ n : ℕ, 1 ≤ n → d n = xSinIntegral a n) :
    ∀ s, 0 ≤ s → s ≤ 4 * a →
      xCoord a s = generalSeries a c d s := by
  have hc0a : c 0 = a := hc0.trans (xMeanIntegral_eq_a a ha)
  have hce : ∀ k : ℕ, c (2 * (k + 1)) = 0 := by
    intro k
    rw [hc (2 * (k + 1)) (by omega),
      xCosIntegral_formula a ha (2 * (k + 1)) (by omega),
      cos_three_nat_pi_div_two,
      Even.neg_one_pow (n := 2 * (k + 1)) ⟨k + 1, by omega⟩,
      Real.cos_nat_mul_pi,
      Even.neg_one_pow (n := 2 * (k + 1)) ⟨k + 1, by omega⟩]
    ring
  have hco : ∀ k : ℕ,
      c (2 * k + 1) =
        -(4 * a /
          (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2))) := by
    intro k
    have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
    rw [hc (2 * k + 1) (by omega),
      xCosIntegral_formula a ha (2 * k + 1) (by omega),
      cos_three_nat_pi_div_two, hodd.neg_one_pow,
      cos_odd_nat_pi_div_two, Real.cos_nat_mul_pi]
    push_cast
    rw [hodd.neg_one_pow]
    ring
  have hde : ∀ k : ℕ, d (2 * (k + 1)) = 0 := by
    intro k
    rw [hd (2 * (k + 1)) (by omega),
      xSinIntegral_formula a ha (2 * (k + 1)) (by omega),
      sin_three_nat_pi_div_two,
      Even.neg_one_pow (n := 2 * (k + 1)) ⟨k + 1, by omega⟩]
    ring
  have hdo : ∀ k : ℕ,
      d (2 * k + 1) =
        4 * a * (-1 : ℝ) ^ k /
          (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
    intro k
    have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
    rw [hd (2 * k + 1) (by omega),
      xSinIntegral_formula a ha (2 * k + 1) (by omega),
      sin_three_nat_pi_div_two, hodd.neg_one_pow,
      sin_odd_nat_pi_div_two]
    push_cast
    ring
  intro s hs0 hs4
  exact (xCoord_eq_xSeries a s ha hs0 hs4).trans
    (generalSeries_eq_xSeries_of_coefficients
      a c d s hc0a hce hco hde hdo).symm

theorem gap2 (a : ℝ) (c : ℕ → ℝ) (ha : 0 < a)
    (hc : c 0 = 1 / (2 * a) * ∫ s in 0..4 * a, xCoord a s) :
    c 0 = 1 / (2 * a) * ∫ s in 0..4 * a, xCoord a s := by
  exact hc

theorem gap3 (a : ℝ) (ha : 0 < a) :
    1 / (2 * a) * (∫ s in 0..4 * a, xCoord a s) =
      1 / (2 * a) *
        ((∫ s in 0..a, s) +
          (∫ _s in a..2 * a, a) +
          ∫ s in 2 * a..3 * a, 3 * a - s) := by
  convert congrArg (fun z : ℝ => 1 / (2 * a) * z)
    (integral_xCoord_mul_piecewise a ha (fun _ => 1) continuous_const)
      using 1 <;>
    simp

theorem gap4 (a : ℝ) (ha : 0 < a) :
    1 / (2 * a) *
        ((∫ s in 0..a, s) +
          (∫ _s in a..2 * a, a) +
          ∫ s in 2 * a..3 * a, 3 * a - s) =
      a := by
  rw [show (∫ s in 0..a, s) =
      1 * (a ^ 2 - 0 ^ 2) / 2 + 0 * (a - 0) by
    convert integral_affine 1 0 0 a using 1 <;> ring,
    show (∫ _s in a..2 * a, a) =
      0 * ((2 * a) ^ 2 - a ^ 2) / 2 + a * (2 * a - a) by
    convert integral_affine 0 a a (2 * a) using 1 <;> ring,
    show (∫ s in 2 * a..3 * a, 3 * a - s) =
      (-1) * ((3 * a) ^ 2 - (2 * a) ^ 2) / 2 +
        (3 * a) * (3 * a - 2 * a) by
    convert integral_affine (-1) (3 * a) (2 * a) (3 * a) using 1 <;>
      ring]
  field_simp [ha.ne']
  ring

theorem gap5 (a : ℝ) (c : ℕ → ℝ) (ha : 0 < a)
    (hc : c 0 = 1 / (2 * a) * ∫ s in 0..4 * a, xCoord a s) :
    c 0 = a := by
  rw [hc, xMeanIntegral_eq_a a ha]

theorem gap6 (a : ℝ) (c : ℕ → ℝ) (ha : 0 < a)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = xCosIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → c n = xCosIntegral a n := by
  exact hc

theorem gap7 (a : ℝ) (c : ℕ → ℝ) (ha : 0 < a)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = xCosIntegral a n) :
    ∀ n : ℕ, 1 ≤ n →
      c n =
        2 * a / (((n : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((n : ℝ) * Real.pi / 2) - 1 -
            Real.cos (3 * (n : ℝ) * Real.pi / 2) +
            Real.cos ((n : ℝ) * Real.pi)) := by
  intro n hn
  rw [hc n hn]
  convert xCosIntegral_formula a ha n hn using 1 <;> ring

theorem gap8 (a : ℝ) (c : ℕ → ℝ) (ha : 0 < a)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = xCosIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ,
      (1 ≤ k ∧ n = 2 * k ∧ c n = 0) ∨
        (n = 2 * k + 1 ∧
          c n = -(4 * a /
            (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2)))) := by
  intro n hn
  obtain ⟨k, hnk | hnk⟩ := Nat.even_or_odd' n
  · subst n
    refine ⟨k, Or.inl ⟨by omega, rfl, ?_⟩⟩
    rw [hc (2 * k) (by omega),
      xCosIntegral_formula a ha (2 * k) (by omega),
      cos_three_nat_pi_div_two,
      Even.neg_one_pow (n := 2 * k) ⟨k, by omega⟩,
      Real.cos_nat_mul_pi,
      Even.neg_one_pow (n := 2 * k) ⟨k, by omega⟩]
    ring
  · subst n
    refine ⟨k, Or.inr ⟨rfl, ?_⟩⟩
    have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
    rw [hc (2 * k + 1) (by omega),
      xCosIntegral_formula a ha (2 * k + 1) (by omega),
      cos_three_nat_pi_div_two, hodd.neg_one_pow,
      cos_odd_nat_pi_div_two, Real.cos_nat_mul_pi]
    push_cast
    rw [hodd.neg_one_pow]
    ring

theorem gap9 (a : ℝ) (d : ℕ → ℝ) (ha : 0 < a)
    (hd : ∀ n : ℕ, 1 ≤ n → d n = xSinIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → d n = xSinIntegral a n := by
  exact hd

theorem gap10 (a : ℝ) (d : ℕ → ℝ) (ha : 0 < a)
    (hd : ∀ n : ℕ, 1 ≤ n → d n = xSinIntegral a n) :
    ∀ n : ℕ, 1 ≤ n →
      d n =
        2 * a / ((n : ℝ) ^ 2 * Real.pi ^ 2) *
          (Real.sin ((n : ℝ) * Real.pi / 2) -
            Real.sin (3 * (n : ℝ) * Real.pi / 2)) := by
  intro n hn
  rw [hd n hn]
  convert xSinIntegral_formula a ha n hn using 1 <;> ring

theorem gap11 (a : ℝ) (d : ℕ → ℝ) (ha : 0 < a)
    (hd : ∀ n : ℕ, 1 ≤ n → d n = xSinIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ,
      (1 ≤ k ∧ n = 2 * k ∧ d n = 0) ∨
        (n = 2 * k + 1 ∧
          d n =
            4 * a * (-1 : ℝ) ^ k /
              (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2))) := by
  intro n hn
  obtain ⟨k, hnk | hnk⟩ := Nat.even_or_odd' n
  · subst n
    refine ⟨k, Or.inl ⟨by omega, rfl, ?_⟩⟩
    rw [hd (2 * k) (by omega),
      xSinIntegral_formula a ha (2 * k) (by omega),
      sin_three_nat_pi_div_two,
      Even.neg_one_pow (n := 2 * k) ⟨k, by omega⟩]
    ring
  · subst n
    refine ⟨k, Or.inr ⟨rfl, ?_⟩⟩
    have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
    rw [hd (2 * k + 1) (by omega),
      xSinIntegral_formula a ha (2 * k + 1) (by omega),
      sin_three_nat_pi_div_two, hodd.neg_one_pow,
      sin_odd_nat_pi_div_two]
    push_cast
    ring

theorem gap12 (a : ℝ) (ha : 0 < a) :
    ∀ s, 0 ≤ s → s ≤ 4 * a →
      xCoord a s = xSeries a s := by
  intro s hs0 hs4
  exact xCoord_eq_xSeries a s ha hs0 hs4

theorem gap13 (a : ℝ) (c d : ℕ → ℝ) (ha : 0 < a)
    (hc0 : c 0 = 1 / (2 * a) * ∫ s in 0..4 * a, yCoord a s)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = yCosIntegral a n)
    (hd : ∀ n : ℕ, 1 ≤ n → d n = ySinIntegral a n) :
    ∀ s, 0 ≤ s → s ≤ 4 * a →
      yCoord a s = generalSeries a c d s := by
  have hc0a : c 0 = a := hc0.trans (yMeanIntegral_eq_a a ha)
  have hce : ∀ k : ℕ, c (2 * (k + 1)) = 0 := by
    intro k
    rw [hc (2 * (k + 1)) (by omega),
      yCosIntegral_formula a ha (2 * (k + 1)) (by omega),
      cos_three_nat_pi_div_two,
      Even.neg_one_pow (n := 2 * (k + 1)) ⟨k + 1, by omega⟩,
      Real.cos_nat_mul_pi,
      Even.neg_one_pow (n := 2 * (k + 1)) ⟨k + 1, by omega⟩]
    ring
  have hco : ∀ k : ℕ,
      c (2 * k + 1) =
        -(4 * a /
          (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2))) := by
    intro k
    have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
    rw [hc (2 * k + 1) (by omega),
      yCosIntegral_formula a ha (2 * k + 1) (by omega),
      cos_three_nat_pi_div_two, hodd.neg_one_pow,
      cos_odd_nat_pi_div_two, Real.cos_nat_mul_pi]
    push_cast
    rw [hodd.neg_one_pow]
    ring
  have hde : ∀ k : ℕ, d (2 * (k + 1)) = 0 := by
    intro k
    rw [hd (2 * (k + 1)) (by omega),
      ySinIntegral_formula a ha (2 * (k + 1)) (by omega),
      sin_three_nat_pi_div_two,
      Even.neg_one_pow (n := 2 * (k + 1)) ⟨k + 1, by omega⟩]
    ring
  have hdo : ∀ k : ℕ,
      d (2 * k + 1) =
        4 * a * (-1 : ℝ) ^ (k + 1) /
          (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
    intro k
    have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
    rw [hd (2 * k + 1) (by omega),
      ySinIntegral_formula a ha (2 * k + 1) (by omega),
      sin_three_nat_pi_div_two, hodd.neg_one_pow,
      sin_odd_nat_pi_div_two, pow_succ]
    push_cast
    ring
  intro s hs0 hs4
  exact (yCoord_eq_ySeries a s ha hs0 hs4).trans
    (generalSeries_eq_ySeries_of_coefficients
      a c d s hc0a hce hco hde hdo).symm

theorem gap14 (a : ℝ) (c : ℕ → ℝ) (ha : 0 < a)
    (hc : c 0 = 1 / (2 * a) * ∫ s in a..4 * a, yCoord a s) :
    c 0 = 1 / (2 * a) * ∫ s in a..4 * a, yCoord a s := by
  exact hc

theorem gap15 (a : ℝ) (ha : 0 < a) :
    1 / (2 * a) * (∫ s in a..4 * a, yCoord a s) =
      1 / (2 * a) *
        ((∫ s in a..2 * a, s - a) +
          (∫ _s in 2 * a..3 * a, a) +
          ∫ s in 3 * a..4 * a, 4 * a - s) := by
  convert congrArg (fun z : ℝ => 1 / (2 * a) * z)
    (integral_yCoord_mul_piecewise a ha (fun _ => 1) continuous_const)
      using 1 <;>
    simp

theorem gap16 (a : ℝ) (ha : 0 < a) :
    1 / (2 * a) *
        ((∫ s in a..2 * a, s - a) +
          (∫ _s in 2 * a..3 * a, a) +
          ∫ s in 3 * a..4 * a, 4 * a - s) =
      a := by
  rw [show (∫ s in a..2 * a, s - a) =
      1 * ((2 * a) ^ 2 - a ^ 2) / 2 + (-a) * (2 * a - a) by
    rw [show (∫ s in a..2 * a, s - a) =
        ∫ s in a..2 * a, 1 * s + (-a) by
      apply intervalIntegral.integral_congr
      intro s _
      ring,
      integral_affine],
    show (∫ _s in 2 * a..3 * a, a) =
      0 * ((3 * a) ^ 2 - (2 * a) ^ 2) / 2 +
        a * (3 * a - 2 * a) by
    convert integral_affine 0 a (2 * a) (3 * a) using 1 <;> ring]
  rw [show (∫ s in 3 * a..4 * a, 4 * a - s) =
      (-1) * ((4 * a) ^ 2 - (3 * a) ^ 2) / 2 +
        (4 * a) * (4 * a - 3 * a) by
    convert integral_affine (-1) (4 * a) (3 * a) (4 * a) using 1 <;>
      ring]
  field_simp [ha.ne']
  ring

theorem gap17 (a : ℝ) (c : ℕ → ℝ) (ha : 0 < a)
    (hc : c 0 = 1 / (2 * a) * ∫ s in a..4 * a, yCoord a s) :
    c 0 = a := by
  rw [hc, gap15 a ha, gap16 a ha]

theorem gap18 (a : ℝ) (c : ℕ → ℝ) (ha : 0 < a)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = yCosIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → c n = yCosIntegral a n := by
  exact hc

theorem gap19 (a : ℝ) (c : ℕ → ℝ) (ha : 0 < a)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = yCosIntegral a n) :
    ∀ n : ℕ, 1 ≤ n →
      c n =
        2 * a / ((n : ℝ) ^ 2 * Real.pi ^ 2) *
          (Real.cos ((n : ℝ) * Real.pi) -
            Real.cos ((n : ℝ) * Real.pi / 2) - 1 +
            Real.cos (3 * (n : ℝ) * Real.pi / 2)) := by
  intro n hn
  rw [hc n hn]
  convert yCosIntegral_formula a ha n hn using 1 <;> ring

theorem gap20 (a : ℝ) (c : ℕ → ℝ) (ha : 0 < a)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = yCosIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ,
      (1 ≤ k ∧ n = 2 * k ∧ c n = 0) ∨
        (n = 2 * k + 1 ∧
          c n = -(4 * a /
            (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2)))) := by
  intro n hn
  obtain ⟨k, hnk | hnk⟩ := Nat.even_or_odd' n
  · subst n
    refine ⟨k, Or.inl ⟨by omega, rfl, ?_⟩⟩
    rw [hc (2 * k) (by omega),
      yCosIntegral_formula a ha (2 * k) (by omega),
      cos_three_nat_pi_div_two,
      Even.neg_one_pow (n := 2 * k) ⟨k, by omega⟩,
      Real.cos_nat_mul_pi,
      Even.neg_one_pow (n := 2 * k) ⟨k, by omega⟩]
    ring
  · subst n
    refine ⟨k, Or.inr ⟨rfl, ?_⟩⟩
    have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
    rw [hc (2 * k + 1) (by omega),
      yCosIntegral_formula a ha (2 * k + 1) (by omega),
      cos_three_nat_pi_div_two, hodd.neg_one_pow,
      cos_odd_nat_pi_div_two, Real.cos_nat_mul_pi]
    push_cast
    rw [hodd.neg_one_pow]
    ring

theorem gap21 (a : ℝ) (d : ℕ → ℝ) (ha : 0 < a)
    (hd : ∀ n : ℕ, 1 ≤ n → d n = ySinIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → d n = ySinIntegral a n := by
  exact hd

theorem gap22 (a : ℝ) (d : ℕ → ℝ) (ha : 0 < a)
    (hd : ∀ n : ℕ, 1 ≤ n → d n = ySinIntegral a n) :
    ∀ n : ℕ, 1 ≤ n →
      d n =
        2 * a / ((n : ℝ) ^ 2 * Real.pi ^ 2) *
          (Real.sin (3 * (n : ℝ) * Real.pi / 2) -
            Real.sin ((n : ℝ) * Real.pi / 2)) := by
  intro n hn
  rw [hd n hn]
  convert ySinIntegral_formula a ha n hn using 1 <;> ring

theorem gap23 (a : ℝ) (d : ℕ → ℝ) (ha : 0 < a)
    (hd : ∀ n : ℕ, 1 ≤ n → d n = ySinIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ,
      (1 ≤ k ∧ n = 2 * k ∧ d n = 0) ∨
        (n = 2 * k + 1 ∧
          d n =
            4 * a * (-1 : ℝ) ^ (k + 1) /
              (Real.pi ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ 2))) := by
  intro n hn
  obtain ⟨k, hnk | hnk⟩ := Nat.even_or_odd' n
  · subst n
    refine ⟨k, Or.inl ⟨by omega, rfl, ?_⟩⟩
    rw [hd (2 * k) (by omega),
      ySinIntegral_formula a ha (2 * k) (by omega),
      sin_three_nat_pi_div_two,
      Even.neg_one_pow (n := 2 * k) ⟨k, by omega⟩]
    ring
  · subst n
    refine ⟨k, Or.inr ⟨rfl, ?_⟩⟩
    have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
    rw [hd (2 * k + 1) (by omega),
      ySinIntegral_formula a ha (2 * k + 1) (by omega),
      sin_three_nat_pi_div_two, hodd.neg_one_pow,
      sin_odd_nat_pi_div_two, pow_succ]
    push_cast
    ring

theorem gap24 (a : ℝ) (ha : 0 < a) :
    ∀ s, 0 ≤ s → s ≤ 4 * a →
      yCoord a s = ySeries a s := by
  intro s hs0 hs4
  exact yCoord_eq_ySeries a s ha hs0 hs4

end

end ProofGap.Exercise2974
