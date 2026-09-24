import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1296_1

open Filter
open scoped Topology

noncomputable section

def powerMean (a b s : ℝ) : ℝ :=
  if s = 0 then Real.sqrt (a * b)
  else Real.rpow ((Real.rpow a s + Real.rpow b s) / 2) (1 / s)

def logAverage (a b s : ℝ) : ℝ :=
  Real.log ((Real.rpow a s + Real.rpow b s) / 2)

private theorem exp_log_average_eq_sqrt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.exp ((Real.log a + Real.log b) / 2) = Real.sqrt (a * b) := by
  have hab : 0 ≤ a * b := (mul_pos ha hb).le
  have hsqrt := Real.sq_sqrt hab
  have hexp : (Real.exp ((Real.log a + Real.log b) / 2)) ^ 2 = a * b := by
    calc
      (Real.exp ((Real.log a + Real.log b) / 2)) ^ 2 =
          Real.exp (((Real.log a + Real.log b) / 2) +
            ((Real.log a + Real.log b) / 2)) := by
              rw [pow_two, ← Real.exp_add]
      _ = Real.exp (Real.log a + Real.log b) := by ring_nf
      _ = Real.exp (Real.log a) * Real.exp (Real.log b) :=
        Real.exp_add (Real.log a) (Real.log b)
      _ = a * b := by rw [Real.exp_log ha, Real.exp_log hb]
  nlinarith [Real.exp_pos ((Real.log a + Real.log b) / 2),
    Real.sqrt_nonneg (a * b)]

private theorem slope_zero_eq_div (g : ℝ → ℝ) :
    slope g 0 = fun x => (g x - g 0) / x := by
  funext x
  simp [slope, div_eq_mul_inv, mul_comm]

private theorem hasDerivAt_logAverage (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (logAverage a b) ((Real.log a + Real.log b) / 2) 0 := by
  have hda : HasDerivAt (fun x : ℝ => Real.exp (Real.log a * x))
      (Real.log a) 0 := by
    convert (Real.hasDerivAt_exp (Real.log a * 0)).comp 0
      ((hasDerivAt_id 0).const_mul (Real.log a)) using 1 <;> norm_num
  have hdb : HasDerivAt (fun x : ℝ => Real.exp (Real.log b * x))
      (Real.log b) 0 := by
    convert (Real.hasDerivAt_exp (Real.log b * 0)).comp 0
      ((hasDerivAt_id 0).const_mul (Real.log b)) using 1 <;> norm_num
  have hg := (hda.add hdb).div_const 2
  have hne :
      (Real.exp (Real.log a * 0) + Real.exp (Real.log b * 0)) / 2 ≠ 0 := by
    norm_num
  have hlog := (Real.hasDerivAt_log hne).comp 0 hg
  have heq :
      (Real.log ∘ fun x : ℝ =>
        (Real.exp (Real.log a * x) + Real.exp (Real.log b * x)) / 2) =
        logAverage a b := by
    funext x
    change Real.log ((Real.exp (Real.log a * x) +
      Real.exp (Real.log b * x)) / 2) =
      Real.log ((Real.rpow a x + Real.rpow b x) / 2)
    change Real.log ((Real.exp (Real.log a * x) +
      Real.exp (Real.log b * x)) / 2) =
      Real.log ((a ^ x + b ^ x) / 2)
    rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb]
  rw [← heq]
  simpa [Function.comp_def] using hlog

private theorem powerMean_eq_exp (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : s ≠ 0) :
    powerMean a b s = Real.exp ((1 / s) * logAverage a b s) := by
  have hbase : 0 < (Real.rpow a s + Real.rpow b s) / 2 :=
    div_pos
      (add_pos (Real.rpow_pos_of_pos ha s) (Real.rpow_pos_of_pos hb s))
      (by norm_num)
  rw [powerMean, if_neg hs]
  change ((Real.rpow a s + Real.rpow b s) / 2) ^ (1 / s) =
    Real.exp ((1 / s) * logAverage a b s)
  rw [Real.rpow_def_of_pos hbase]
  unfold logAverage
  congr 1
  ring

private theorem tendsto_exp_logAverage (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun s => Real.exp ((1 / s) * logAverage a b s))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (𝓝 (Real.sqrt (a * b))) := by
  have hslope := (hasDerivAt_logAverage a b ha hb).tendsto_slope
  rw [slope_zero_eq_div] at hslope
  have hzero : logAverage a b 0 = 0 := by
    simp [logAverage]
  have hquot :
      Tendsto (fun s => (1 / s) * logAverage a b s)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (𝓝 ((Real.log a + Real.log b) / 2)) := by
    simpa [hzero, div_eq_mul_inv, one_div, mul_comm] using hslope
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hquot
  rw [exp_log_average_eq_sqrt a b ha hb] at hexp
  simpa [Function.comp_def] using hexp

private theorem rpow_mono_of_pos {x y s : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≤ y) (hs : 0 ≤ s) : Real.rpow x s ≤ Real.rpow y s := by
  change x ^ s ≤ y ^ s
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (Real.strictMonoOn_log.monotoneOn hx hy hxy) hs

private theorem rpow_anti_of_neg {x y s : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≤ y) (hs : s ≤ 0) : Real.rpow y s ≤ Real.rpow x s := by
  change y ^ s ≤ x ^ s
  rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_right
    (Real.strictMonoOn_log.monotoneOn hx hy hxy) hs

private theorem rpow_rpow_one_div {x s : ℝ} (hx : 0 < x) (hs : s ≠ 0) :
    Real.rpow (Real.rpow x s) (1 / s) = x := by
  calc
    Real.rpow (Real.rpow x s) (1 / s) =
        Real.rpow x (s * (1 / s)) := (Real.rpow_mul hx.le s (1 / s)).symm
    _ = Real.rpow x 1 := by
      congr 1
      simp [one_div, hs]
    _ = x := Real.rpow_one x

private theorem sqrt_mul_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    min a b ≤ Real.sqrt (a * b) ∧ Real.sqrt (a * b) ≤ max a b := by
  have hsqrt := Real.sq_sqrt (mul_nonneg ha.le hb.le)
  have hsqrt_nonneg := Real.sqrt_nonneg (a * b)
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    have hlo : a * a ≤ a * b := mul_le_mul_of_nonneg_left hab ha.le
    have hupp : a * b ≤ b * b := mul_le_mul_of_nonneg_right hab hb.le
    constructor <;> nlinarith
  · rw [min_eq_right hba, max_eq_left hba]
    have hlo : b * b ≤ a * b := mul_le_mul_of_nonneg_right hba hb.le
    have hupp : a * b ≤ a * a := mul_le_mul_of_nonneg_left hba ha.le
    constructor <;> nlinarith

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    powerMean a b 0 = Real.sqrt (a * b) := by
  simp [powerMean]

theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (powerMean a b) (𝓝 0)
      (𝓝 (Real.sqrt (a * b))) := by
  intro S hS
  have hlim := tendsto_exp_logAverage a b ha hb
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
      (hlim.eventually hS) with ⟨U, hU, hUS⟩
  apply Filter.mem_of_superset hU
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    change powerMean a b 0 ∈ S
    rw [gap1 a b ha hb]
    exact mem_of_mem_nhds hS
  · change powerMean a b x ∈ S
    rw [powerMean_eq_exp a b x ha hb hx0]
    apply hUS
    exact ⟨hx, by simpa using hx0⟩

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun s => Real.exp ((1 / s) * logAverage a b s))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (𝓝 (Real.sqrt (a * b))) := by
  exact tendsto_exp_logAverage a b ha hb

def f (a b x : ℝ) : ℝ := logAverage a b x

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x => (f a b x - f a b 0) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (𝓝 (deriv (f a b) 0)) := by
  have h : HasDerivAt (f a b) ((Real.log a + Real.log b) / 2) 0 := by
    simpa [f] using hasDerivAt_logAverage a b ha hb
  have hslope := h.tendsto_slope
  rw [slope_zero_eq_div] at hslope
  rw [h.deriv]
  exact hslope

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x => (f a b x - f a b 0) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (𝓝 ((Real.log a + Real.log b) / 2)) := by
  have h : HasDerivAt (f a b) ((Real.log a + Real.log b) / 2) 0 := by
    simpa [f] using hasDerivAt_logAverage a b ha hb
  have hslope := h.tendsto_slope
  rw [slope_zero_eq_div] at hslope
  exact hslope

theorem gap6 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x => (1 / x) * logAverage a b x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (𝓝 ((Real.log a + Real.log b) / 2)) := by
  have hzero : logAverage a b 0 = 0 := by
    simp [logAverage]
  simpa [f, hzero, div_eq_mul_inv, one_div, mul_comm] using
    (gap5 a b ha hb)

theorem gap7 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    deriv (f a b) 0 = (Real.log a + Real.log b) / 2 := by
  have h : HasDerivAt (f a b) ((Real.log a + Real.log b) / 2) 0 := by
    simpa [f] using hasDerivAt_logAverage a b ha hb
  exact h.deriv

theorem gap8 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    powerMean a b 0 = Real.exp (deriv (f a b) 0) := by
  rw [gap1 a b ha hb, gap7 a b ha hb]
  exact (exp_log_average_eq_sqrt a b ha hb).symm

theorem gap9 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.exp (deriv (f a b) 0) =
      Real.exp ((Real.log a + Real.log b) / 2) := by
  rw [gap7 a b ha hb]

theorem gap10 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.exp ((Real.log a + Real.log b) / 2) =
      Real.sqrt (a * b) := by
  exact exp_log_average_eq_sqrt a b ha hb

theorem gap11 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    powerMean a b 0 = Real.sqrt (a * b) := by
  exact gap1 a b ha hb

theorem gap12 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) :
    2 * Real.rpow (min a b) s ≤
      Real.rpow a s + Real.rpow b s := by
  have hm : 0 < min a b := lt_min ha hb
  have hma := rpow_mono_of_pos hm ha (min_le_left a b) hs.le
  have hmb := rpow_mono_of_pos hm hb (min_le_right a b) hs.le
  linarith

theorem gap13 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) :
    Real.rpow a s + Real.rpow b s ≤
      2 * Real.rpow (max a b) s := by
  have hM : 0 < max a b := lt_of_lt_of_le ha (le_max_left a b)
  have haM := rpow_mono_of_pos ha hM (le_max_left a b) hs.le
  have hbM := rpow_mono_of_pos hb hM (le_max_right a b) hs.le
  linarith

theorem gap14 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : s < 0) :
    2 * Real.rpow (max a b) s ≤
      Real.rpow a s + Real.rpow b s ∧
      Real.rpow a s + Real.rpow b s ≤
        2 * Real.rpow (min a b) s := by
  have hm : 0 < min a b := lt_min ha hb
  have hM : 0 < max a b := lt_of_lt_of_le ha (le_max_left a b)
  constructor
  · have hMa := rpow_anti_of_neg ha hM (le_max_left a b) hs.le
    have hMb := rpow_anti_of_neg hb hM (le_max_right a b) hs.le
    linarith
  · have ham := rpow_anti_of_neg hm ha (min_le_left a b) hs.le
    have hbm := rpow_anti_of_neg hm hb (min_le_right a b) hs.le
    linarith

theorem gap15 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) :
    min a b ≤
      Real.rpow ((Real.rpow a s + Real.rpow b s) / 2) (1 / s) := by
  have hm : 0 < min a b := lt_min ha hb
  have havg : 0 < (Real.rpow a s + Real.rpow b s) / 2 :=
    div_pos
      (add_pos (Real.rpow_pos_of_pos ha s) (Real.rpow_pos_of_pos hb s))
      (by norm_num)
  have hlow : Real.rpow (min a b) s ≤
      (Real.rpow a s + Real.rpow b s) / 2 := by
    linarith [gap12 a b s ha hb hs]
  have hp := rpow_mono_of_pos
    (Real.rpow_pos_of_pos hm s) havg hlow (one_div_pos.mpr hs).le
  calc
    min a b = Real.rpow (Real.rpow (min a b) s) (1 / s) :=
      (rpow_rpow_one_div hm hs.ne').symm
    _ ≤ Real.rpow ((Real.rpow a s + Real.rpow b s) / 2) (1 / s) := hp

theorem gap16 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : s ≠ 0) :
    min a b ≤ powerMean a b s ∧ powerMean a b s ≤ max a b := by
  have hm : 0 < min a b := lt_min ha hb
  have hM : 0 < max a b := lt_of_lt_of_le ha (le_max_left a b)
  have havg : 0 < (Real.rpow a s + Real.rpow b s) / 2 :=
    div_pos
      (add_pos (Real.rpow_pos_of_pos ha s) (Real.rpow_pos_of_pos hb s))
      (by norm_num)
  rw [powerMean, if_neg hs]
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · have hbds := gap14 a b s ha hb hsneg
    have hlow : (Real.rpow a s + Real.rpow b s) / 2 ≤
        Real.rpow (min a b) s := by
      linarith [hbds.2]
    have hupp : Real.rpow (max a b) s ≤
        (Real.rpow a s + Real.rpow b s) / 2 := by
      linarith [hbds.1]
    have ht : 1 / s ≤ 0 := (one_div_neg.mpr hsneg).le
    constructor
    · calc
        min a b = Real.rpow (Real.rpow (min a b) s) (1 / s) :=
          (rpow_rpow_one_div hm hs).symm
        _ ≤ Real.rpow ((Real.rpow a s + Real.rpow b s) / 2) (1 / s) :=
          rpow_anti_of_neg havg (Real.rpow_pos_of_pos hm s) hlow ht
    · calc
        Real.rpow ((Real.rpow a s + Real.rpow b s) / 2) (1 / s) ≤
            Real.rpow (Real.rpow (max a b) s) (1 / s) :=
          rpow_anti_of_neg (Real.rpow_pos_of_pos hM s) havg hupp ht
        _ = max a b := rpow_rpow_one_div hM hs
  · have hlow : Real.rpow (min a b) s ≤
        (Real.rpow a s + Real.rpow b s) / 2 := by
      linarith [gap12 a b s ha hb hspos]
    have hupp : (Real.rpow a s + Real.rpow b s) / 2 ≤
        Real.rpow (max a b) s := by
      linarith [gap13 a b s ha hb hspos]
    have ht : 0 ≤ 1 / s := (one_div_pos.mpr hspos).le
    constructor
    · calc
        min a b = Real.rpow (Real.rpow (min a b) s) (1 / s) :=
          (rpow_rpow_one_div hm hs).symm
        _ ≤ Real.rpow ((Real.rpow a s + Real.rpow b s) / 2) (1 / s) :=
          rpow_mono_of_pos (Real.rpow_pos_of_pos hm s) havg hlow ht
    · calc
        Real.rpow ((Real.rpow a s + Real.rpow b s) / 2) (1 / s) ≤
            Real.rpow (Real.rpow (max a b) s) (1 / s) :=
          rpow_mono_of_pos havg (Real.rpow_pos_of_pos hM s) hupp ht
        _ = max a b := rpow_rpow_one_div hM hs

theorem gap17 (a b : ℝ) : min a b ≤ max a b := by
  exact le_trans (min_le_left a b) (le_max_left a b)

theorem gap18 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    min a b ≤ powerMean a b s := by
  by_cases hs : s = 0
  · subst s
    simpa [powerMean] using (sqrt_mul_bounds ha hb).1
  · exact (gap16 a b s ha hb hs).1

theorem gap19 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    powerMean a b s ≤ max a b := by
  by_cases hs : s = 0
  · subst s
    simpa [powerMean] using (sqrt_mul_bounds ha hb).2
  · exact (gap16 a b s ha hb hs).2

theorem gap20 (a b : ℝ) : min a b ≤ max a b := by
  exact gap17 a b

theorem gap21 (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    min a b ≤ powerMean a b s ∧ powerMean a b s ≤ max a b := by
  exact ⟨gap18 a b s ha hb, gap19 a b s ha hb⟩

end

end ProofGap.Exercise1296_1
