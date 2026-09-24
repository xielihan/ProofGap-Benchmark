import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

namespace ProofGap.Exercise2930

noncomputable section

open scoped BigOperators

def α : ℝ :=
  Real.arctan (1 / 5 : ℝ)

def β : ℝ :=
  4 * α - Real.pi / 4

def arctanTerm (q : ℕ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n /
    (((2 * n + 1 : ℕ) : ℝ) * (q : ℝ) ^ (2 * n + 1))

def arctanPartial (q m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range m, arctanTerm q n

def firstError : ℝ :=
  |16 * Real.arctan (1 / 5 : ℝ) - 16 * arctanPartial 5 7|

def secondError : ℝ :=
  |4 * Real.arctan (1 / 239 : ℝ) - 4 * arctanPartial 239 2|

def combinedApproximation : ℝ :=
  16 * arctanPartial 5 7 - 4 * arctanPartial 239 2

def combinedError : ℝ :=
  |Real.pi - combinedApproximation|

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem beta_eq_arctan_inv_239 :
    β = Real.arctan (1 / 239 : ℝ) := by
  have hmach := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num [div_eq_mul_inv] at hmach ⊢
  unfold β α
  nlinarith

private def arctanMagnitude (q n : ℕ) : ℝ :=
  (1 / (q : ℝ)) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

private theorem arctanTerm_eq_alternating (q n : ℕ) :
    arctanTerm q n = (-1 : ℝ) ^ n * arctanMagnitude q n := by
  simp only [arctanTerm, arctanMagnitude]
  ring

private theorem arctanMagnitude_antitone (q : ℕ) (hq : 1 ≤ q) :
    Antitone (arctanMagnitude q) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [arctanMagnitude]
  have hq0 : (0 : ℝ) < q := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hq1 : (1 / (q : ℝ)) ≤ 1 := by
    rw [div_le_one₀ hq0]
    exact_mod_cast hq
  have hx0 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
  have hp :
      (1 / (q : ℝ)) ^ (2 * (n + 1) + 1) ≤
        (1 / (q : ℝ)) ^ (2 * n + 1) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hx0 hq1)
  have hd0 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hd1 :
      ((2 * n + 1 : ℕ) : ℝ) ≤ ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
    norm_num
  exact div_le_div₀ (by positivity) hp hd0 hd1

private theorem arctanTerm_hasSum (q : ℕ) (hq : 1 < q) :
    HasSum (arctanTerm q) (Real.arctan (1 / q : ℝ)) := by
  have hnorm : ‖(1 / q : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_lt_one (by positivity)).2 (by exact_mod_cast hq)
  convert Real.hasSum_arctan hnorm using 1
  funext n
  rw [arctanTerm_eq_alternating]
  simp only [arctanMagnitude]
  ring

private theorem arctan_fifth_partial_bounds :
    arctanPartial 5 7 - arctanMagnitude 5 7 <
        Real.arctan (1 / 5 : ℝ) ∧
      Real.arctan (1 / 5 : ℝ) < arctanPartial 5 7 := by
  have hlim :
      Filter.Tendsto
        (fun n => ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * arctanMagnitude 5 i)
        Filter.atTop (nhds (Real.arctan (1 / 5 : ℝ))) := by
    simpa only [← arctanTerm_eq_alternating] using
      (arctanTerm_hasSum 5 (by omega)).tendsto_sum_nat
  have hanti := arctanMagnitude_antitone 5 (by omega)
  have hlo := hanti.alternating_series_le_tendsto hlim 5
  have hhi := hanti.tendsto_le_alternating_series hlim 4
  norm_num [arctanPartial, arctanTerm, arctanMagnitude,
    Finset.sum_range_succ] at hlo hhi ⊢
  constructor <;> linarith

private theorem arctan_239_partial_bounds :
    arctanPartial 239 2 < Real.arctan (1 / 239 : ℝ) ∧
      Real.arctan (1 / 239 : ℝ) <
        arctanPartial 239 2 + arctanMagnitude 239 2 := by
  have hlim :
      Filter.Tendsto
        (fun n => ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * arctanMagnitude 239 i)
        Filter.atTop (nhds (Real.arctan (1 / 239 : ℝ))) := by
    simpa only [← arctanTerm_eq_alternating] using
      (arctanTerm_hasSum 239 (by omega)).tendsto_sum_nat
  have hanti := arctanMagnitude_antitone 239 (by omega)
  have hlo := hanti.alternating_series_le_tendsto hlim 2
  have hhi := hanti.tendsto_le_alternating_series hlim 2
  norm_num [arctanPartial, arctanTerm, arctanMagnitude,
    Finset.sum_range_succ] at hlo hhi ⊢
  constructor <;> linarith

theorem gap1 :
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x * y < 1 →
      Real.arctan x + Real.arctan y =
        Real.arctan ((x + y) / (1 - x * y)) := by
  intro x y _ _ hxy
  exact Real.arctan_add hxy

theorem gap2 :
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x * y < 1 →
      (x + y) / (1 - x * y) = 1 →
      Real.pi / 4 = Real.arctan x + Real.arctan y := by
  intro x y hx hy hxy hratio
  rw [gap1 x y hx hy hxy, hratio, Real.arctan_one]

theorem gap3 :
    Real.pi / 4 =
      Real.arctan (1 / 2 : ℝ) + Real.arctan (1 / 3 : ℝ) := by
  simpa [div_eq_mul_inv] using Real.arctan_inv_2_add_arctan_inv_3.symm

theorem gap4 :
    Real.tan α = (1 / 5 : ℝ) := by
  simp [α]

theorem gap5 :
    Real.tan (2 * α) =
      (2 / 5 : ℝ) / (1 - (1 / 25 : ℝ)) := by
  rw [Real.tan_two_mul, gap4]
  norm_num

theorem gap6 :
    ((2 / 5 : ℝ) / (1 - (1 / 25 : ℝ))) = 5 / 12 := by
  norm_num

theorem gap7 :
    Real.tan (2 * α) = (5 / 12 : ℝ) := by
  rw [gap5, gap6]

theorem gap8 :
    Real.tan (4 * α) =
      (10 / 12 : ℝ) / (1 - (25 / 144 : ℝ)) := by
  rw [show 4 * α = 2 * (2 * α) by ring, Real.tan_two_mul, gap7]
  norm_num

theorem gap9 :
    ((10 / 12 : ℝ) / (1 - (25 / 144 : ℝ))) = 120 / 119 := by
  norm_num

theorem gap10 :
    Real.tan (4 * α) = (120 / 119 : ℝ) := by
  rw [gap8, gap9]

theorem gap11 :
    Real.tan β =
      ((120 / 119 : ℝ) - 1) / (1 + (120 / 119 : ℝ)) := by
  rw [beta_eq_arctan_inv_239, Real.tan_arctan]
  norm_num

theorem gap12 :
    (((120 / 119 : ℝ) - 1) / (1 + (120 / 119 : ℝ))) =
      1 / 239 := by
  norm_num

theorem gap13 :
    Real.tan β = (1 / 239 : ℝ) := by
  rw [gap11, gap12]

theorem gap14 :
    β = Real.arctan (1 / 239 : ℝ) := by
  exact beta_eq_arctan_inv_239

theorem gap15 :
    Real.pi / 4 = 4 * α - β := by
  unfold β
  ring

theorem gap16 :
    4 * α - β =
      4 * Real.arctan (1 / 5 : ℝ) -
        Real.arctan (1 / 239 : ℝ) := by
  rw [gap14]
  rfl

theorem gap17 :
    Real.pi / 4 =
      4 * Real.arctan (1 / 5 : ℝ) -
        Real.arctan (1 / 239 : ℝ) := by
  exact gap15.trans gap16

theorem gap18 :
    Real.pi =
      16 * Real.arctan (1 / 5 : ℝ) -
        4 * Real.arctan (1 / 239 : ℝ) := by
  nlinarith [gap17]

theorem gap19 :
    Real.pi =
      16 * (∑' n : ℕ, arctanTerm 5 n) -
        4 * ∑' n : ℕ, arctanTerm 239 n := by
  have h5 := (arctanTerm_hasSum 5 (by omega)).tsum_eq
  have h239 := (arctanTerm_hasSum 239 (by omega)).tsum_eq
  rw [h5, h239]
  exact gap18

theorem gap20 :
    0 < firstError := by
  rw [firstError, abs_pos]
  intro hzero
  have hlt := arctan_fifth_partial_bounds.2
  nlinarith

theorem gap21 :
    firstError < 16 / (15 * 5 ^ 15 : ℝ) := by
  rw [firstError, abs_of_neg]
  · have hlo := arctan_fifth_partial_bounds.1
    norm_num [arctanMagnitude] at hlo ⊢
    nlinarith
  · have hhi := arctan_fifth_partial_bounds.2
    nlinarith

theorem gap22 :
    (16 / (15 * 5 ^ 15 : ℝ)) <
      (1 / 2 : ℝ) * (1 / 10 ^ 9 : ℝ) := by
  norm_num

theorem gap23 :
    (0 : ℝ) < (1 / 2 : ℝ) * (1 / 10 ^ 9 : ℝ) := by
  norm_num

theorem gap24 :
    0 < secondError := by
  rw [secondError, abs_pos]
  intro hzero
  have hlt := arctan_239_partial_bounds.1
  nlinarith

theorem gap25 :
    secondError < 4 / (5 * 239 ^ 5 : ℝ) := by
  rw [secondError, abs_of_pos]
  · have hhi := arctan_239_partial_bounds.2
    norm_num [arctanMagnitude] at hhi ⊢
    nlinarith
  · have hlo := arctan_239_partial_bounds.1
    nlinarith

theorem gap26 :
    (4 / (5 * 239 ^ 5 : ℝ)) <
      (1 / 2 : ℝ) * (1 / 10 ^ 9 : ℝ) := by
  norm_num

theorem gap27 :
    (0 : ℝ) < (1 / 2 : ℝ) * (1 / 10 ^ 9 : ℝ) := by
  norm_num

theorem gap28 :
    combinedError ≤ firstError + secondError := by
  unfold combinedError combinedApproximation firstError secondError
  calc
    |Real.pi - (16 * arctanPartial 5 7 - 4 * arctanPartial 239 2)| =
        |(16 * Real.arctan (1 / 5 : ℝ) - 16 * arctanPartial 5 7) -
          (4 * Real.arctan (1 / 239 : ℝ) - 4 * arctanPartial 239 2)| := by
            congr 1
            nlinarith [gap18]
    _ ≤ |16 * Real.arctan (1 / 5 : ℝ) - 16 * arctanPartial 5 7| +
          |4 * Real.arctan (1 / 239 : ℝ) - 4 * arctanPartial 239 2| := by
      simpa [abs_sub_comm] using abs_sub_le
        (16 * Real.arctan (1 / 5 : ℝ) - 16 * arctanPartial 5 7)
        0
        (4 * Real.arctan (1 / 239 : ℝ) - 4 * arctanPartial 239 2)

theorem gap29 :
    firstError + secondError < (1 / 10 ^ 9 : ℝ) := by
  nlinarith [gap21.trans gap22, gap25.trans gap26]

theorem gap30 :
    combinedError < (1 / 10 ^ 9 : ℝ) := by
  exact gap28.trans_lt gap29

theorem gap31 :
    (31415926535 / 10000000000 : ℝ) < Real.pi := by
  nlinarith [Real.pi_gt_d20]

theorem gap32 :
    Real.pi < (31415926537 / 10000000000 : ℝ) := by
  nlinarith [Real.pi_lt_d20]

theorem gap33 :
    (31415926535 / 10000000000 : ℝ) <
      (31415926537 / 10000000000 : ℝ) := by
  norm_num

theorem gap34 :
    Approx Real.pi (3141592654 / 1000000000 : ℝ)
      (1 / 10 ^ 9 : ℝ) := by
  rw [Approx, abs_lt]
  constructor <;> nlinarith [gap31, gap32]

end

end ProofGap.Exercise2930
