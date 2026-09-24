import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise466

noncomputable section

def original (n : ℕ) (x : ℝ) : ℝ :=
  ((x - Real.sqrt (x ^ 2 - 1)) ^ n + (x + Real.sqrt (x ^ 2 - 1)) ^ n) / x ^ n
def normalized (n : ℕ) (x : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - 1 / x ^ 2)) ^ n +
    (1 + Real.sqrt (1 - 1 / x ^ 2)) ^ n
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_466/1.txt`; divide both summands by `x^n`. -/
theorem gap1 (n : ℕ) (hn : 0 < n) (L : ℝ) :
    HasLimitAtPosInfinity (original n) L ↔
      HasLimitAtPosInfinity (normalized n) L := by
  unfold HasLimitAtPosInfinity
  have heq : original n =ᶠ[Filter.atTop] normalized n := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have harg1 : 0 ≤ x ^ 2 - 1 := by
      rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]
      exact mul_nonneg (sub_nonneg.mpr hx) (by linarith)
    have hquot :
        1 - 1 / x ^ 2 = (x ^ 2 - 1) / x ^ 2 := by
      field_simp [hxne] <;> ring
    have harg2 : 0 ≤ 1 - 1 / x ^ 2 := by
      rw [hquot]
      exact div_nonneg harg1 (sq_nonneg x)
    have hsq :
        (Real.sqrt (x ^ 2 - 1) / x) ^ 2 =
          (Real.sqrt (1 - 1 / x ^ 2)) ^ 2 := by
      calc
        (Real.sqrt (x ^ 2 - 1) / x) ^ 2 =
            (Real.sqrt (x ^ 2 - 1)) ^ 2 / x ^ 2 := by
              rw [div_pow]
        _ = (Real.sqrt (1 - 1 / x ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt harg1, Real.sq_sqrt harg2]
          exact hquot.symm
    have hsqrt_div :
        Real.sqrt (x ^ 2 - 1) / x =
          Real.sqrt (1 - 1 / x ^ 2) := by
      have hleft : 0 ≤ Real.sqrt (x ^ 2 - 1) / x :=
        div_nonneg (Real.sqrt_nonneg _) (le_of_lt hxpos)
      have hright : 0 ≤ Real.sqrt (1 - 1 / x ^ 2) :=
        Real.sqrt_nonneg _
      have hprod :
          (Real.sqrt (x ^ 2 - 1) / x -
              Real.sqrt (1 - 1 / x ^ 2)) *
            (Real.sqrt (x ^ 2 - 1) / x +
              Real.sqrt (1 - 1 / x ^ 2)) = 0 := by
        nlinarith [hsq]
      rcases mul_eq_zero.mp hprod with h | h
      · linarith
      · nlinarith
    have hminus :
        x - Real.sqrt (x ^ 2 - 1) =
          x * (1 - Real.sqrt (1 - 1 / x ^ 2)) := by
      rw [← hsqrt_div]
      field_simp [hxne] <;> ring
    have hplus :
        x + Real.sqrt (x ^ 2 - 1) =
          x * (1 + Real.sqrt (1 - 1 / x ^ 2)) := by
      rw [← hsqrt_div]
      field_simp [hxne] <;> ring
    unfold original normalized
    rw [hminus, hplus]
    simp only [mul_pow]
    field_simp [pow_ne_zero n hxne] <;> ring
  have heq' : normalized n =ᶠ[Filter.atTop] original n := by
    filter_upwards [heq] with x hx
    exact hx.symm
  exact ⟨Filter.Tendsto.congr' heq, Filter.Tendsto.congr' heq'⟩

/-- Source: `proof_gap/exercise_466/2.txt`. -/
theorem gap2 (n : ℕ) (hn : 0 < n) :
    HasLimitAtPosInfinity (normalized n) ((2 : ℝ) ^ n) := by
  unfold HasLimitAtPosInfinity normalized
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hfrac :
      Filter.Tendsto (fun x : ℝ => 1 / x ^ 2) Filter.atTop (nhds 0) := by
    simpa [one_div] using hinv.pow 2
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hinside :
      Filter.Tendsto (fun x : ℝ => 1 - 1 / x ^ 2)
        Filter.atTop (nhds 1) := by
    simpa using hone.sub hfrac
  have hsqrt :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 - 1 / x ^ 2))
        Filter.atTop (nhds 1) := by
    simpa using (Real.continuous_sqrt.tendsto 1).comp hinside
  have hminus := (hone.sub hsqrt).pow n
  have hplus := (hone.add hsqrt).pow n
  have hvalue :
      (1 - (1 : ℝ)) ^ n + (1 + (1 : ℝ)) ^ n = (2 : ℝ) ^ n := by
    norm_num [hn.ne']
  rw [← hvalue]
  exact hminus.add hplus

end

end ProofGap.Exercise466
