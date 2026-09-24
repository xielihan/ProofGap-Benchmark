import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1442

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arctan x - (1 / 2) * Real.log (1 + x ^ 2)

def Approx (a b ε : ℝ) : Prop := |a - b| < ε

private theorem hasDerivAt_y_formula (x : ℝ) :
    HasDerivAt y ((1 - x) / (1 + x ^ 2)) x := by
  have hpos : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      norm_num <;> ring
  have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t ^ 2))
      ((1 + x ^ 2)⁻¹ * (2 * x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_log (ne_of_gt hpos)).comp x hinner
  unfold y
  convert (Real.hasDerivAt_arctan x).sub (hlog.const_mul (1 / 2)) using 1 <;>
    field_simp [ne_of_gt hpos] <;>
    ring

private theorem sq_lt_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a ^ 2 < b ^ 2 := by
  have hsum : 0 < b + a := by
    nlinarith
  have hprod : 0 < (b - a) * (b + a) :=
    mul_pos (sub_pos.mpr hab) hsum
  nlinarith

theorem gap1 (x : ℝ) :
    deriv y x = (1 - x) / (1 + x ^ 2) := by
  exact (hasDerivAt_y_formula x).deriv

theorem gap2 : deriv y 1 = 0 := by
  rw [gap1]
  norm_num

theorem gap3 (x : ℝ) (hx : x < 1) : 0 < deriv y x := by
  rw [gap1]
  have hden : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  exact div_pos (sub_pos.mpr hx) hden

theorem gap4 (x : ℝ) (hx : 1 < x) : deriv y x < 0 := by
  rw [gap1]
  have hden : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  exact div_neg_of_neg_of_pos (sub_neg.mpr hx) hden

theorem gap5 : IsMaxOn y Set.univ 1 := by
  have hmono : MonotoneOn y (Set.Iic (1 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic (1 : ℝ))
    · intro z hz
      exact (hasDerivAt_y_formula z).continuousAt.continuousWithinAt
    · intro z hz
      exact (hasDerivAt_y_formula z).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : z < 1 := by
        simpa only [interior_Iic, Set.mem_Iio] using hz
      exact le_of_lt (gap3 z hz')
  have hanti : AntitoneOn y (Set.Ici (1 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici (1 : ℝ))
    · intro z hz
      exact (hasDerivAt_y_formula z).continuousAt.continuousWithinAt
    · intro z hz
      exact (hasDerivAt_y_formula z).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : 1 < z := by
        simpa only [interior_Ici, Set.mem_Ioi] using hz
      exact le_of_lt (gap4 z hz')
  intro x hx
  by_cases h : x ≤ 1
  · exact hmono (Set.mem_Iic.mpr h) (Set.mem_Iic.mpr le_rfl) h
  · have h' : 1 ≤ x := le_of_lt (lt_of_not_ge h)
    exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h') h'

theorem gap6 :
    y 1 = Real.pi / 4 - (1 / 2) * Real.log 2 := by
  norm_num [y, Real.arctan_one]

theorem gap7 :
    Approx (Real.pi / 4 - (1 / 2) * Real.log 2) 0.439 0.001 := by
  have hpi_lower : (3.14 : ℝ) < Real.pi := by
    nlinarith [Real.pi_gt_d20]
  have hpi_upper : Real.pi < (3.142 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  let s : ℝ := 1001355 / 1000000
  have hs : 0 < s := by
    norm_num [s]
  have hs2 : (1.002711836 : ℝ) < s ^ 2 := by
    norm_num [s]
  have hs4 : (1.005431026 : ℝ) < s ^ 4 := by
    calc
      (1.005431026 : ℝ) < (1.002711836 : ℝ) ^ 2 := by norm_num
      _ < (s ^ 2) ^ 2 := sq_lt_sq_of_nonneg (by norm_num) hs2
      _ = s ^ 4 := by ring
  have hs8 : (1.010891548 : ℝ) < s ^ 8 := by
    calc
      (1.010891548 : ℝ) < (1.005431026 : ℝ) ^ 2 := by norm_num
      _ < (s ^ 4) ^ 2 := sq_lt_sq_of_nonneg (by norm_num) hs4
      _ = s ^ 8 := by ring
  have hs16 : (1.021901721 : ℝ) < s ^ 16 := by
    calc
      (1.021901721 : ℝ) < (1.010891548 : ℝ) ^ 2 := by norm_num
      _ < (s ^ 8) ^ 2 := sq_lt_sq_of_nonneg (by norm_num) hs8
      _ = s ^ 16 := by ring
  have hs32 : (1.044283127 : ℝ) < s ^ 32 := by
    calc
      (1.044283127 : ℝ) < (1.021901721 : ℝ) ^ 2 := by norm_num
      _ < (s ^ 16) ^ 2 := sq_lt_sq_of_nonneg (by norm_num) hs16
      _ = s ^ 32 := by ring
  have hs64 : (1.090527249 : ℝ) < s ^ 64 := by
    calc
      (1.090527249 : ℝ) < (1.044283127 : ℝ) ^ 2 := by norm_num
      _ < (s ^ 32) ^ 2 := sq_lt_sq_of_nonneg (by norm_num) hs32
      _ = s ^ 64 := by ring
  have hs128 : (1.189249680 : ℝ) < s ^ 128 := by
    calc
      (1.189249680 : ℝ) < (1.090527249 : ℝ) ^ 2 := by norm_num
      _ < (s ^ 64) ^ 2 := sq_lt_sq_of_nonneg (by norm_num) hs64
      _ = s ^ 128 := by ring
  have hs256 : (1.414314801 : ℝ) < s ^ 256 := by
    calc
      (1.414314801 : ℝ) < (1.189249680 : ℝ) ^ 2 := by norm_num
      _ < (s ^ 128) ^ 2 := sq_lt_sq_of_nonneg (by norm_num) hs128
      _ = s ^ 256 := by ring
  have hs512 : (2 : ℝ) < s ^ 512 := by
    calc
      (2 : ℝ) < (1.414314801 : ℝ) ^ 2 := by norm_num
      _ < (s ^ 256) ^ 2 := sq_lt_sq_of_nonneg (by norm_num) hs256
      _ = s ^ 512 := by ring
  have hlogs_pow : Real.log 2 < Real.log (s ^ 512) :=
    Real.strictMonoOn_log (by norm_num) (pow_pos hs 512) hs512
  rw [Real.log_pow] at hlogs_pow
  have hlogs : Real.log s ≤ (0.001355 : ℝ) := by
    calc
      Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs
      _ = (0.001355 : ℝ) := by norm_num [s]
  have hlog_upper : Real.log 2 < (0.694 : ℝ) := by
    calc
      Real.log 2 < (512 : ℝ) * Real.log s := hlogs_pow
      _ ≤ (512 : ℝ) * (0.001355 : ℝ) :=
        mul_le_mul_of_nonneg_left hlogs (by norm_num)
      _ < (0.694 : ℝ) := by norm_num
  let t : ℝ := 500677 / 500000
  have ht : 0 < t := by
    norm_num [t]
  have ht2 : t ^ 2 < (1.002709834 : ℝ) := by
    norm_num [t]
  have ht4 : t ^ 4 < (1.005427012 : ℝ) := by
    calc
      t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ < (1.002709834 : ℝ) ^ 2 :=
        sq_lt_sq_of_nonneg (sq_nonneg t) ht2
      _ < (1.005427012 : ℝ) := by norm_num
  have ht8 : t ^ 8 < (1.010883477 : ℝ) := by
    calc
      t ^ 8 = (t ^ 4) ^ 2 := by ring
      _ < (1.005427012 : ℝ) ^ 2 :=
        sq_lt_sq_of_nonneg (pow_nonneg (le_of_lt ht) 4) ht4
      _ < (1.010883477 : ℝ) := by norm_num
  have ht16 : t ^ 16 < (1.021885405 : ℝ) := by
    calc
      t ^ 16 = (t ^ 8) ^ 2 := by ring
      _ < (1.010883477 : ℝ) ^ 2 :=
        sq_lt_sq_of_nonneg (pow_nonneg (le_of_lt ht) 8) ht8
      _ < (1.021885405 : ℝ) := by norm_num
  have ht32 : t ^ 32 < (1.044249781 : ℝ) := by
    calc
      t ^ 32 = (t ^ 16) ^ 2 := by ring
      _ < (1.021885405 : ℝ) ^ 2 :=
        sq_lt_sq_of_nonneg (pow_nonneg (le_of_lt ht) 16) ht16
      _ < (1.044249781 : ℝ) := by norm_num
  have ht64 : t ^ 64 < (1.090457606 : ℝ) := by
    calc
      t ^ 64 = (t ^ 32) ^ 2 := by ring
      _ < (1.044249781 : ℝ) ^ 2 :=
        sq_lt_sq_of_nonneg (pow_nonneg (le_of_lt ht) 32) ht32
      _ < (1.090457606 : ℝ) := by norm_num
  have ht128 : t ^ 128 < (1.189097791 : ℝ) := by
    calc
      t ^ 128 = (t ^ 64) ^ 2 := by ring
      _ < (1.090457606 : ℝ) ^ 2 :=
        sq_lt_sq_of_nonneg (pow_nonneg (le_of_lt ht) 64) ht64
      _ < (1.189097791 : ℝ) := by norm_num
  have ht256 : t ^ 256 < (1.413953557 : ℝ) := by
    calc
      t ^ 256 = (t ^ 128) ^ 2 := by ring
      _ < (1.189097791 : ℝ) ^ 2 :=
        sq_lt_sq_of_nonneg (pow_nonneg (le_of_lt ht) 128) ht128
      _ < (1.413953557 : ℝ) := by norm_num
  have ht512 : t ^ 512 < (2 : ℝ) := by
    calc
      t ^ 512 = (t ^ 256) ^ 2 := by ring
      _ < (1.413953557 : ℝ) ^ 2 :=
        sq_lt_sq_of_nonneg (pow_nonneg (le_of_lt ht) 256) ht256
      _ < (2 : ℝ) := by norm_num
  have hlogt_pow : Real.log (t ^ 512) < Real.log 2 :=
    Real.strictMonoOn_log (pow_pos ht 512) (by norm_num) ht512
  rw [Real.log_pow] at hlogt_pow
  have hloginv := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at hloginv
  have hlogt_lower : 1 - t⁻¹ ≤ Real.log t := by
    linarith
  have hlog_lower : (0.692 : ℝ) < Real.log 2 := by
    calc
      (0.692 : ℝ) < (512 : ℝ) * (1 - t⁻¹) := by norm_num [t]
      _ ≤ (512 : ℝ) * Real.log t :=
        mul_le_mul_of_nonneg_left hlogt_lower (by norm_num)
      _ < Real.log 2 := hlogt_pow
  unfold Approx
  rw [abs_lt]
  constructor <;> norm_num <;>
    nlinarith [hpi_lower, hpi_upper, hlog_lower, hlog_upper]

end
end ProofGap.Exercise1442
