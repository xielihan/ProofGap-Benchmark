import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace ProofGap.Exercise2814

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℝ :=
  ((Nat.factorial n : ℝ) ^ 2) / Nat.factorial (2 * n)

def powerTerm (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n * x ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm (k + 1) x)

def HasConvergenceRadius (r : ℝ) : Prop :=
  (∀ x : ℝ, |x| < r → SeriesConvergesAt x) ∧
    (∀ x : ℝ, r < |x| → ¬ SeriesConvergesAt x)

def ratioFormula (n : ℕ) : ℝ :=
  ((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ) /
    (((n + 1 : ℕ) : ℝ) ^ 2)

def endpointMagnitude (n : ℕ) : ℝ :=
  coefficient n * 4 ^ n

def raabeSeq (n : ℕ) : ℝ :=
  (n : ℝ) * (endpointMagnitude n / endpointMagnitude (n + 1) - 1)

private theorem coefficient_pos (n : ℕ) : 0 < coefficient n := by
  unfold coefficient
  positivity

private theorem coefficient_ne_zero (n : ℕ) : coefficient n ≠ 0 :=
  (coefficient_pos n).ne'

private theorem coefficient_ratio (n : ℕ) :
    coefficient n / coefficient (n + 1) =
      ((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ) /
        (((n + 1 : ℕ) : ℝ) ^ 2) := by
  unfold coefficient
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
  rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

private theorem endpoint_stirling_identity (m : ℕ) (hm : m ≠ 0) :
    endpointMagnitude m / Real.sqrt (Real.pi * (m : ℝ)) =
      Stirling.stirlingSeq m ^ 2 /
        (Stirling.stirlingSeq (2 * m) * Real.sqrt Real.pi) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hm)
  unfold endpointMagnitude coefficient Stirling.stirlingSeq
  push_cast
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (m : ℝ))]
  norm_num
  rw [show (((m : ℝ) / Real.exp 1) ^ m) ^ 2 =
      ((m : ℝ) / Real.exp 1) ^ (2 * m) by
        rw [← pow_mul]
        congr 1
        omega]
  rw [show (m : ℝ) * 2 / Real.exp 1 =
      2 * ((m : ℝ) / Real.exp 1) by ring]
  rw [mul_pow]
  rw [show (2 : ℝ) ^ (2 * m) = 4 ^ m by
    rw [pow_mul]
    norm_num]
  ring_nf
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ))]
  rw [show Real.sqrt (4 : ℝ) = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)]
  ring

theorem gap1 :
    (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|) =
      fun n : ℕ => ratioFormula (n + 1) := by
  funext n
  rw [abs_of_pos (div_pos (coefficient_pos _) (coefficient_pos _))]
  exact coefficient_ratio (n + 1)

theorem gap2 :
    Tendsto ratioFormula atTop (𝓝 4) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have htwo :
      Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul h : Tendsto
      (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * 0)))
  have hsub :
      Tendsto (fun n : ℕ => 4 - 2 * (1 / ((n : ℝ) + 1)))
        atTop (𝓝 4) := by
    simpa using (tendsto_const_nhds.sub htwo : Tendsto
      (fun n : ℕ => 4 - 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 (4 - 0)))
  convert hsub using 1
  funext n
  unfold ratioFormula
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem gap3 :
    Tendsto
      (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|)
      atTop (𝓝 4) := by
  rw [gap1]
  exact gap2.comp (tendsto_add_atTop_nat 1)

private theorem tendsto_coefficient_ratio_inv :
    Tendsto
      (fun n : ℕ => |coefficient (n + 2) / coefficient (n + 1)|)
      atTop (𝓝 (1 / 4 : ℝ)) := by
  have hinv := gap3.inv₀ (by norm_num : (4 : ℝ) ≠ 0)
  convert hinv using 1
  · funext n
    rw [abs_of_pos (div_pos (coefficient_pos _) (coefficient_pos _))]
    rw [abs_of_pos (div_pos (coefficient_pos _) (coefficient_pos _))]
    field_simp [coefficient_ne_zero]
  · norm_num

private theorem tendsto_power_ratio (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖powerTerm (n + 2) x‖ / ‖powerTerm (n + 1) x‖)
      atTop (𝓝 (|x| / 4)) := by
  by_cases hx : x = 0
  · subst x
    simp [powerTerm]
  · have hmul :=
      (tendsto_const_nhds (x := |x|)).mul tendsto_coefficient_ratio_inv
    convert hmul using 1
    · funext n
      simp only [powerTerm, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_pos (coefficient_pos _)]
      rw [abs_of_pos (div_pos (coefficient_pos _) (coefficient_pos _))]
      have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
      field_simp [coefficient_ne_zero, hxabs]
      ring
    · ring

theorem gap4 :
    HasConvergenceRadius 4 := by
  constructor
  · intro x hx
    unfold SeriesConvergesAt
    by_cases hx0 : x = 0
    · subst x
      simp [powerTerm]
    · apply summable_of_ratio_test_tendsto_lt_one (l := |x| / 4)
      · nlinarith
      · filter_upwards [] with n
        exact mul_ne_zero (coefficient_ne_zero _) (pow_ne_zero _ hx0)
      · simpa [Nat.add_assoc] using tendsto_power_ratio x
  · intro x hx
    unfold SeriesConvergesAt
    apply not_summable_of_ratio_test_tendsto_gt_one (l := |x| / 4)
    · nlinarith
    · simpa [Nat.add_assoc] using tendsto_power_ratio x

theorem gap5 :
    ∀ x : ℝ, x ∈ Set.Ioo (-4 : ℝ) 4 → SeriesConvergesAt x := by
  intro x hx
  exact gap4.1 x (abs_lt.mpr hx)

theorem gap6 :
    ∀ n : ℕ,
      |powerTerm n (-4)| = endpointMagnitude n := by
  intro n
  unfold powerTerm endpointMagnitude
  rw [abs_mul, abs_pow]
  rw [abs_of_pos (coefficient_pos n)]
  norm_num

theorem gap7 :
    Tendsto
      (fun n : ℕ =>
        endpointMagnitude (n + 1) /
          Real.sqrt (Real.pi * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 1) := by
  have hs₁ :
      Tendsto (fun n : ℕ => Stirling.stirlingSeq (n + 1))
        atTop (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
  have hidx : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hs₂ :
      Tendsto (fun n : ℕ => Stirling.stirlingSeq (2 * (n + 1)))
        atTop (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp hidx
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hratio :=
    (hs₁.mul hs₁).div (hs₂.mul tendsto_const_nhds)
      (mul_ne_zero hsqrt hsqrt)
  convert hratio using 1
  · funext n
    rw [endpoint_stirling_identity (n + 1) (by omega)]
    simp only [Pi.div_apply]
    ring
  · rw [Real.mul_self_sqrt Real.pi_nonneg]
    field_simp [Real.pi_ne_zero]

theorem gap8 :
    Tendsto
      (fun n : ℕ =>
        |powerTerm (n + 1) (-4)| /
          Real.sqrt (Real.pi * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 1) := by
  simpa only [gap6] using gap7

theorem gap9 :
    Tendsto (fun n : ℕ => |powerTerm (n + 1) (-4)|) atTop atTop := by
  have hratio := gap8
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        (1 / 2 : ℝ) ≤
          |powerTerm (n + 1) (-4)| /
            Real.sqrt (Real.pi * ((n + 1 : ℕ) : ℝ)) :=
    hratio.eventually_const_le (by norm_num)
  have hcast :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hmul :
      Tendsto (fun n : ℕ => Real.pi * (((n + 1 : ℕ) : ℝ)))
        atTop atTop :=
    Tendsto.const_mul_atTop Real.pi_pos hcast
  have hsqrt :
      Tendsto
        (fun n : ℕ => Real.sqrt (Real.pi * (((n + 1 : ℕ) : ℝ))))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hmul
  have hlower :
      Tendsto
        (fun n : ℕ =>
          (1 / 2 : ℝ) *
            Real.sqrt (Real.pi * (((n + 1 : ℕ) : ℝ))))
        atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) hsqrt
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [hevent] with n hn
  have hspos :
      0 < Real.sqrt (Real.pi * (((n + 1 : ℕ) : ℝ))) := by positivity
  calc
    (1 / 2 : ℝ) * Real.sqrt (Real.pi * (((n + 1 : ℕ) : ℝ))) ≤
        (|powerTerm (n + 1) (-4)| /
          Real.sqrt (Real.pi * (((n + 1 : ℕ) : ℝ)))) *
            Real.sqrt (Real.pi * (((n + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_right hn hspos.le
    _ = |powerTerm (n + 1) (-4)| := by field_simp

theorem gap10 :
    ¬ SeriesConvergesAt (-4) := by
  intro hsum
  have hzero :
      Tendsto (fun n : ℕ => |powerTerm (n + 1) (-4)|)
        atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using
      (tendsto_norm_zero.comp hsum.tendsto_atTop_zero)
  exact not_tendsto_atTop_of_tendsto_nhds hzero gap9

theorem gap11 :
    (fun n : ℕ => powerTerm (n + 1) 4) =
      fun n : ℕ => endpointMagnitude (n + 1) := by
  rfl

theorem gap12 :
    (fun n : ℕ => raabeSeq (n + 1)) =
      fun n : ℕ => -((n + 1 : ℕ) : ℝ) / (2 * ((n + 1 : ℕ) : ℝ) + 2) := by
  funext n
  unfold raabeSeq endpointMagnitude
  rw [show
    coefficient (n + 1) * 4 ^ (n + 1) /
        (coefficient (n + 1 + 1) * 4 ^ (n + 1 + 1)) =
      (coefficient (n + 1) / coefficient (n + 1 + 1)) / 4 by
        rw [pow_succ]
        field_simp [coefficient_ne_zero]
        ring]
  rw [coefficient_ratio (n + 1)]
  push_cast
  field_simp
  ring

theorem gap13 :
    Tendsto
      (fun n : ℕ => -((n + 1 : ℕ) : ℝ) / (2 * ((n + 1 : ℕ) : ℝ) + 2))
      atTop (𝓝 (-1 / 2 : ℝ)) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  have hscaled :
      Tendsto (fun n : ℕ =>
        (1 / 2 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) + 1)))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul hshift :
        Tendsto (fun n : ℕ =>
          (1 / 2 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) + 1)))
          atTop (𝓝 ((1 / 2 : ℝ) * 0)))
  have hadd :
      Tendsto (fun n : ℕ =>
        (-1 / 2 : ℝ) +
          (1 / 2 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) + 1)))
        atTop (𝓝 (-1 / 2 : ℝ)) := by
    simpa using
      (tendsto_const_nhds.add hscaled :
        Tendsto (fun n : ℕ =>
          (-1 / 2 : ℝ) +
            (1 / 2 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) + 1)))
          atTop (𝓝 ((-1 / 2 : ℝ) + 0)))
  convert hadd using 1
  funext n
  push_cast
  field_simp
  ring

theorem gap14 :
    (-1 / 2 : ℝ) < 1 := by
  norm_num

theorem gap15 :
    Tendsto (fun n : ℕ => raabeSeq (n + 1)) atTop (𝓝 (-1 / 2 : ℝ)) ∧
      (-1 / 2 : ℝ) < 1 := by
  constructor
  · rw [gap12]
    exact gap13
  · exact gap14

theorem gap16 :
    ¬ Summable (fun n : ℕ => endpointMagnitude (n + 1)) := by
  have htop :
      Tendsto (fun n : ℕ => endpointMagnitude (n + 1)) atTop atTop := by
    simpa only [gap6] using gap9
  intro hsum
  exact not_tendsto_atTop_of_tendsto_nhds hsum.tendsto_atTop_zero htop

theorem gap17 :
    ∀ x : ℝ, x ∈ Set.Ioo (-4 : ℝ) 4 ↔ SeriesConvergesAt x := by
  intro x
  constructor
  · intro hx
    exact gap5 x hx
  · intro hsum
    have habs : |x| < 4 := by
      by_contra hnot
      have hle : (4 : ℝ) ≤ |x| := le_of_not_gt hnot
      rcases hle.eq_or_lt with heq | hlt
      · by_cases hx0 : 0 ≤ x
        · rw [abs_of_nonneg hx0] at heq
          have hsum4 : SeriesConvergesAt 4 := by simpa [heq] using hsum
          unfold SeriesConvergesAt at hsum4
          rw [gap11] at hsum4
          exact gap16 hsum4
        · have hxnonpos : x ≤ 0 := le_of_not_ge hx0
          rw [abs_of_nonpos hxnonpos] at heq
          have hxneg4 : x = -4 := by linarith
          have hsumneg4 : SeriesConvergesAt (-4) := by
            simpa [hxneg4] using hsum
          exact gap10 hsumneg4
      · exact (gap4.2 x hlt) hsum
    exact abs_lt.mp habs

end

end ProofGap.Exercise2814
