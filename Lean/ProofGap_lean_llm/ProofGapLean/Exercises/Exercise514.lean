import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise514

noncomputable section

def original (x : ℝ) : ℝ := Real.rpow (1 - 2 * x) (1 / x)
def rewritten (x : ℝ) : ℝ :=
  Real.rpow (1 + (-2) * x) ((1 / ((-2) * x)) * (-2))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_514/1.txt`; interpret the variable-index root as `Real.rpow`. -/
private theorem original_limit :
    HasLimitAtZero original (Real.exp (-2)) := by
  unfold HasLimitAtZero
  have hinner :
      HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub
        ((hasDerivAt_const (x := (0 : ℝ)) (c := (2 : ℝ))).mul
          (hasDerivAt_id (𝕜 := ℝ) 0)) using 1 <;> norm_num <;> ring
  have hlog :
      HasDerivAt Real.log ((1 - 2 * (0 : ℝ))⁻¹) (1 - 2 * (0 : ℝ)) :=
    Real.hasDerivAt_log (by norm_num)
  have hderiv :
      HasDerivAt (fun x : ℝ => Real.log (1 - 2 * x)) (-2) 0 := by
    convert hlog.comp 0 hinner using 1 <;> norm_num
  have hslope := hderiv.tendsto_slope
  have hquot :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 - 2 * x) * (1 / x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-2)) := by
    apply hslope.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa using hx
    simp [slope, hx0, one_div, mul_comm]
  have hexp :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log (1 - 2 * x) * (1 / x)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp (-2))) := by
    exact Real.continuous_exp.continuousAt.tendsto.comp hquot
  have hlt0 : ∀ᶠ x : ℝ in nhds 0, x < (1 / 2 : ℝ) :=
    Iio_mem_nhds (by norm_num)
  have hlt :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x < (1 / 2 : ℝ) :=
    Filter.Eventually.filter_mono inf_le_left hlt0
  have hpos :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        0 < 1 - 2 * x := by
    filter_upwards [hlt] with x hx
    linarith
  refine hexp.congr' ?_
  filter_upwards [hpos] with x hx
  simp [original, Real.rpow_def_of_pos hx]

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero rewritten L := by
  unfold HasLimitAtZero
  have hfun :
      original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] rewritten := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa using hx
    have hbase : 1 - 2 * x = 1 + (-2) * x := by
      ring
    have hexponent :
        1 / x = (1 / ((-2) * x)) * (-2) := by
      field_simp [hx0]
    unfold original rewritten
    rw [hbase, hexponent]
  constructor
  · intro h
    exact h.congr' hfun
  · intro h
    exact h.congr' hfun.symm

/-- Source: `proof_gap/exercise_514/2.txt`. -/
theorem gap2 : HasLimitAtZero rewritten (Real.exp (-2)) := by
  exact (gap1 (Real.exp (-2))).mp original_limit

/-- Source: `proof_gap/exercise_514/3.txt`. -/
theorem gap3 : HasLimitAtZero original (Real.exp (-2)) := by
  exact (gap1 (Real.exp (-2))).mpr gap2

end

end ProofGap.Exercise514
