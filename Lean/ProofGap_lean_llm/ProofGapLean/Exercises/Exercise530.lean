import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise530

noncomputable section

def original (x : ℝ) : ℝ := x * (Real.log (x + 1) - Real.log x)
def rewritten (x : ℝ) : ℝ :=
  Real.log (Real.rpow (1 + 1 / x) x)
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_530/1.txt`. -/
theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity rewritten L := by
  unfold HasLimitAtPosInfinity
  have heq : original =ᶠ[Filter.atTop] rewritten := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hx1 : x + 1 ≠ 0 := by positivity
    have hbase : 0 < 1 + 1 / x := by positivity
    have hratio : 1 + 1 / x = (x + 1) / x := by
      field_simp [hx0]
    have hlogpow :
        Real.log (Real.rpow (1 + 1 / x) x) =
          x * Real.log (1 + 1 / x) := by
      change Real.log ((1 + 1 / x) ^ x) = _
      exact Real.log_rpow hbase x
    unfold original rewritten
    rw [hlogpow, hratio, Real.log_div hx1 hx0]
  exact ⟨fun h => h.congr' heq, fun h => h.congr' heq.symm⟩

/-- Source: `proof_gap/exercise_530/2.txt`. -/
theorem gap2 : HasLimitAtPosInfinity rewritten (Real.log (Real.exp 1)) := by
  unfold HasLimitAtPosInfinity rewritten
  have hrpow :
      Filter.Tendsto
        (fun x : ℝ => Real.rpow (1 + 1 / x) x)
        Filter.atTop (nhds (Real.exp 1)) := by
    simpa using Real.tendsto_one_add_div_rpow_exp (1 : ℝ)
  exact (Real.continuousAt_log (Real.exp_ne_zero 1)).tendsto.comp hrpow

/-- Source: `proof_gap/exercise_530/3.txt`. -/
theorem gap3 : Real.log (Real.exp 1) = 1 := by
  exact Real.log_exp 1

/-- Source: `proof_gap/exercise_530/4.txt`. -/
theorem gap4 : HasLimitAtPosInfinity original 1 := by
  apply (gap1 1).mpr
  simpa only [gap3] using gap2

end

end ProofGap.Exercise530
