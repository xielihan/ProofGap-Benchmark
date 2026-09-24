import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise541

noncomputable section

def original (a x : ℝ) : ℝ := (Real.rpow a x - 1) / x
def inverseLog (a y : ℝ) : ℝ := y / Real.logb a (1 + y)
def normalized (a y : ℝ) : ℝ :=
  1 / Real.logb a (Real.rpow (1 + y) (1 / y))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 541, gap 1; require a valid logarithm base `a≠1`. -/
private theorem reciprocal_logb_exp (a : ℝ) :
    1 / Real.logb a (Real.exp 1) = Real.log a := by
  simp [Real.logb]

private theorem log_one_plus_div_limit :
    Filter.Tendsto (fun y : ℝ => Real.log (1 + y) / y)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hinner : HasDerivAt (fun y : ℝ => 1 + y) 1 0 := by
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
        (hasDerivAt_id (0 : ℝ))
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) 1 0 := by
    simpa using
      (Real.hasDerivAt_log
        (show 1 + (0 : ℝ) ≠ 0 by norm_num)).comp 0 hinner
  simpa [div_eq_mul_inv, mul_comm] using hlog.tendsto_slope_zero

private theorem inverse_eq_log_ratio_eventually
    (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    inverseLog a =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun y : ℝ => Real.log a / (Real.log (1 + y) / y)) := by
  have hgt0 : ∀ᶠ y : ℝ in nhds (0 : ℝ), -1 < y :=
    eventually_gt_nhds (by norm_num)
  have hgt : ∀ᶠ y : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, -1 < y :=
    hgt0.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hgt] with y hy hygt
  have hy0 : y ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
  have hbase : 0 < 1 + y := by
    linarith
  have hloga : Real.log a ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one ha ha1
  have hlogy : Real.log (1 + y) ≠ 0 := by
    intro hzero
    have hone : 1 + y = 1 :=
      Real.strictMonoOn_log.injOn hbase
        (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (by simpa using hzero)
    apply hy0
    linarith
  simp only [inverseLog, Real.logb]
  field_simp [hy0, hloga, hlogy]

private theorem inverse_limit_log
    (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    HasLimitAtZero (inverseLog a) (Real.log a) := by
  have ht :
      Filter.Tendsto
        (fun y : ℝ => Real.log a / (Real.log (1 + y) / y))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.log a / 1)) :=
    tendsto_const_nhds.div log_one_plus_div_limit one_ne_zero
  have heq := inverse_eq_log_ratio_eventually a ha ha1
  simpa [HasLimitAtZero] using ht.congr' heq.symm

private theorem inverse_eq_normalized_eventually
    (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    inverseLog a =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] normalized a := by
  have hgt0 : ∀ᶠ y : ℝ in nhds (0 : ℝ), -1 < y :=
    eventually_gt_nhds (by norm_num)
  have hgt : ∀ᶠ y : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, -1 < y :=
    hgt0.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hgt] with y hy hygt
  have hy0 : y ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
  have hbase : 0 < 1 + y := by
    linarith
  have hloga : Real.log a ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one ha ha1
  have hlogy : Real.log (1 + y) ≠ 0 := by
    intro hzero
    have hone : 1 + y = 1 :=
      Real.strictMonoOn_log.injOn hbase
        (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (by simpa using hzero)
    apply hy0
    linarith
  have hlogpow :
      Real.log (Real.rpow (1 + y) (1 / y)) =
        (1 / y) * Real.log (1 + y) := by
    exact Real.log_rpow hbase (1 / y)
  simp only [inverseLog, normalized, Real.logb]
  rw [hlogpow]
  field_simp [hy0, hloga, hlogy]

private theorem normalized_limit_log
    (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    HasLimitAtZero (normalized a) (Real.log a) := by
  exact (inverse_limit_log a ha ha1).congr'
    (inverse_eq_normalized_eventually a ha ha1)

private theorem original_limit_log (a : ℝ) (ha : 0 < a) :
    HasLimitAtZero (original a) (Real.log a) := by
  have hlin :
      HasDerivAt (fun x : ℝ => Real.log a * x) (Real.log a) 0 := by
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (c := Real.log a)).mul
        (hasDerivAt_id (0 : ℝ))
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (Real.log a * x))
        (Real.log a) 0 := by
    simpa using
      (Real.hasDerivAt_exp (Real.log a * 0)).comp 0 hlin
  have hs :
      Filter.Tendsto
        (fun x : ℝ => (Real.exp (Real.log a * x) - 1) / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.log a)) := by
    simpa [div_eq_mul_inv, mul_comm] using hexp.tendsto_slope_zero
  have hrpow (x : ℝ) :
      Real.rpow a x = Real.exp (Real.log a * x) := by
    exact Real.rpow_def_of_pos ha x
  have heq :
      (fun x : ℝ => (Real.exp (Real.log a * x) - 1) / x) = original a := by
    funext x
    change (Real.exp (Real.log a * x) - 1) / x =
      (Real.rpow a x - 1) / x
    rw [hrpow x]
  rw [← heq]
  exact hs

theorem gap1 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) (L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (inverseLog a) L := by
  constructor
  · intro h
    have hL : L = Real.log a :=
      tendsto_nhds_unique h (original_limit_log a ha)
    simpa [hL] using inverse_limit_log a ha ha1
  · intro h
    have hL : L = Real.log a :=
      tendsto_nhds_unique h (inverse_limit_log a ha ha1)
    simpa [hL] using original_limit_log a ha

/-- Exercise 541, gap 2; require `a≠1`. -/
theorem gap2 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) (L : ℝ) :
    HasLimitAtZero (inverseLog a) L ↔ HasLimitAtZero (normalized a) L := by
  have heq := inverse_eq_normalized_eventually a ha ha1
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 541, gap 3; require `a≠1`. -/
theorem gap3 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    HasLimitAtZero (normalized a) (1 / Real.logb a (Real.exp 1)) := by
  rw [reciprocal_logb_exp a]
  exact normalized_limit_log a ha ha1

/-- Exercise 541, gap 4; require a valid logarithm base. -/
theorem gap4 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    1 / Real.logb a (Real.exp 1) = Real.log a := by
  exact reciprocal_logb_exp a

/-- Exercise 541, gap 5; the final derivative formula also covers `a=1`. -/
theorem gap5 (a : ℝ) (ha : 0 < a) :
    HasLimitAtZero (original a) (Real.log a) := by
  exact original_limit_log a ha

end

end ProofGap.Exercise541
