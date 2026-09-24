import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise544

noncomputable section

def original (x : ℝ) : ℝ := Real.rpow (x + Real.exp x) (1 / x)
def rewritten (x : ℝ) : ℝ :=
  Real.exp 1 *
    Real.rpow (1 + x / Real.exp x) ((Real.exp x / x) * Real.exp (-x))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_544/1.txt`. -/
private theorem rewritten_exponent_eq (x : ℝ) :
    (Real.exp x / x) * Real.exp (-x) = 1 / x := by
  calc
    (Real.exp x / x) * Real.exp (-x) =
        (Real.exp x * Real.exp (-x)) / x := by ring
    _ = 1 / x := by
      rw [← Real.exp_add]
      simp

private theorem rewritten_base_pos {x : ℝ} (hx : -(1 : ℝ) / 2 < x) :
    0 < 1 + x / Real.exp x := by
  have hsum : 0 < Real.exp x + x := by
    have hbound := Real.add_one_le_exp x
    linarith
  have hid :
      1 + x / Real.exp x = (Real.exp x + x) / Real.exp x := by
    field_simp [Real.exp_ne_zero x]
  rw [hid]
  exact div_pos hsum (Real.exp_pos x)

private theorem eventually_valid :
    ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      -(1 : ℝ) / 2 < x ∧ x ≠ 0 := by
  have hnear :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, -(1 : ℝ) / 2 < x :=
    mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (show -(1 : ℝ) / 2 < 0 by norm_num))
  have hpunct :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x ∈ ({0} : Set ℝ)ᶜ :=
    self_mem_nhdsWithin
  filter_upwards [hnear, hpunct] with x hx hmem
  exact ⟨hx, by simpa using hmem⟩

private theorem original_eq_rewritten_of (x : ℝ)
    (hxnear : -(1 : ℝ) / 2 < x) (hx0 : x ≠ 0) :
    original x = rewritten x := by
  have hbase : 0 < 1 + x / Real.exp x := rewritten_base_pos hxnear
  have hfactor :
      x + Real.exp x = Real.exp x * (1 + x / Real.exp x) := by
    calc
      x + Real.exp x = Real.exp x + x := add_comm _ _
      _ = Real.exp x * (1 + x / Real.exp x) := by
        field_simp [Real.exp_ne_zero x]
  have hxmul : x * (1 / x) = 1 := by
    field_simp [hx0]
  have hsplit :
      Real.rpow (Real.exp x * (1 + x / Real.exp x)) (1 / x) =
        Real.rpow (Real.exp x) (1 / x) *
          Real.rpow (1 + x / Real.exp x) (1 / x) := by
    exact Real.mul_rpow (le_of_lt (Real.exp_pos x)) (le_of_lt hbase)
  have hexprpow :
      (Real.exp x).rpow (1 / x) = Real.exp 1 := by
    calc
      (Real.exp x).rpow (1 / x) =
          Real.exp (Real.log (Real.exp x) * (1 / x)) := by
        simpa only using
          (Real.rpow_def_of_pos (Real.exp_pos x) (1 / x))
      _ = Real.exp 1 := by rw [Real.log_exp, hxmul]
  calc
    original x = Real.rpow (x + Real.exp x) (1 / x) := rfl
    _ = Real.rpow (Real.exp x * (1 + x / Real.exp x)) (1 / x) := by
      rw [hfactor]
    _ = Real.rpow (Real.exp x) (1 / x) *
          Real.rpow (1 + x / Real.exp x) (1 / x) := hsplit
    _ = Real.exp 1 * Real.rpow (1 + x / Real.exp x) (1 / x) := by
      rw [hexprpow]
    _ = Real.exp 1 *
          Real.rpow (1 + x / Real.exp x)
            ((Real.exp x / x) * Real.exp (-x)) := by
      rw [rewritten_exponent_eq]
    _ = rewritten x := rfl

private theorem tendsto_log_base_div :
    Filter.Tendsto
      (fun x : ℝ => Real.log (1 + x / Real.exp x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hquot :
      HasDerivAt (fun x : ℝ => x / Real.exp x) 1 0 := by
    simpa using
      ((hasDerivAt_id (𝕜 := ℝ) 0).div
        (Real.hasDerivAt_exp 0) (Real.exp_ne_zero 0))
  have hinner :
      HasDerivAt (fun x : ℝ => 1 + x / Real.exp x) 1 0 := by
    exact hquot.const_add 1
  have houter :
      HasDerivAt Real.log 1 (1 + (0 : ℝ) / Real.exp 0) := by
    convert Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num) using 1 <;>
      norm_num
  have hlog :
      HasDerivAt
        (fun x : ℝ => Real.log (1 + x / Real.exp x)) 1 0 := by
    simpa only [one_mul] using houter.comp 0 hinner
  refine hlog.tendsto_slope.congr' ?_
  apply Filter.Eventually.of_forall
  intro x
  change
    (x - 0)⁻¹ *
        (Real.log (1 + x / Real.exp x) -
          Real.log (1 + 0 / Real.exp 0)) =
      Real.log (1 + x / Real.exp x) / x
  simp only [div_eq_mul_inv, zero_mul, add_zero, Real.log_one, sub_zero]
  exact mul_comm (x⁻¹) (Real.log (1 + x / Real.exp x))

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero rewritten L := by
  unfold HasLimitAtZero
  constructor
  · intro h
    refine h.congr' ?_
    filter_upwards [eventually_valid] with x hx
    exact original_eq_rewritten_of x hx.1 hx.2
  · intro h
    refine h.congr' ?_
    filter_upwards [eventually_valid] with x hx
    exact (original_eq_rewritten_of x hx.1 hx.2).symm

/-- Source: `proof_gap/exercise_544/2.txt`. -/
theorem gap2 : HasLimitAtZero rewritten (Real.exp 1 * Real.exp 1) := by
  unfold HasLimitAtZero
  have hlim :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp 1 *
            Real.exp (Real.log (1 + x / Real.exp x) / x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (Real.exp 1 * Real.exp 1)) :=
    tendsto_const_nhds.mul
      ((Real.continuous_exp.tendsto 1).comp tendsto_log_base_div)
  refine hlim.congr' ?_
  filter_upwards [eventually_valid] with x hx
  have hbase := rewritten_base_pos hx.1
  have hexponent :
      (Real.exp x / x) * Real.exp (-x) = 1 / x :=
    rewritten_exponent_eq x
  have hrpow :
      (1 + x / Real.exp x).rpow (1 / x) =
        Real.exp (Real.log (1 + x / Real.exp x) * (1 / x)) := by
    simpa only using
      (Real.rpow_def_of_pos hbase (1 / x))
  have hpow :
      Real.exp (Real.log (1 + x / Real.exp x) / x) =
        (1 + x / Real.exp x).rpow (1 / x) := by
    simpa only [div_eq_mul_inv, one_mul] using hrpow.symm
  rw [rewritten, hexponent]
  exact congrArg (fun y : ℝ => Real.exp 1 * y) hpow

/-- Source: `proof_gap/exercise_544/3.txt`. -/
theorem gap3 : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
  calc
    Real.exp 1 * Real.exp 1 = Real.exp (1 + 1) := (Real.exp_add 1 1).symm
    _ = Real.exp 2 := by norm_num

/-- Source: `proof_gap/exercise_544/4.txt`. -/
theorem gap4 : HasLimitAtZero original (Real.exp 2) := by
  have h := (gap1 (Real.exp 1 * Real.exp 1)).2 gap2
  simpa only [gap3] using h

end

end ProofGap.Exercise544
