import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise566_1

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.log (x ^ 2 + Real.exp x) / Real.log (x ^ 4 + Real.exp (2 * x))
def rewritten (x : ℝ) : ℝ :=
  (x + Real.log (1 + x ^ 2 * Real.exp (-x))) /
    (2 * x + Real.log (1 + x ^ 4 * Real.exp (-2 * x)))
def normalized (x : ℝ) : ℝ :=
  (1 + Real.log (1 + x ^ 2 * Real.exp (-x)) /
      (x ^ 2 * Real.exp (-x)) * x * Real.exp (-x)) /
    (2 + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) /
      (x ^ 4 * Real.exp (-2 * x)) * x ^ 3 * Real.exp (-2 * x))

/-- Source: `proof_gap/exercise_566_1/1.txt`; compare the punctured limits of the algebraically rewritten expressions. -/
theorem gap1 (L : ℝ) :
    Filter.Tendsto original (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) ↔
      Filter.Tendsto rewritten (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) := by
  have h : original = rewritten := by
    funext x
    have he1 : Real.exp x * Real.exp (-x) = 1 := by
      calc
        Real.exp x * Real.exp (-x) = Real.exp (x + -x) :=
          (Real.exp_add x (-x)).symm
        _ = 1 := by simp
    have he2 : Real.exp (2 * x) * Real.exp (-2 * x) = 1 := by
      calc
        Real.exp (2 * x) * Real.exp (-2 * x) =
            Real.exp (2 * x + (-2 * x)) :=
          (Real.exp_add (2 * x) (-2 * x)).symm
        _ = 1 := by
          rw [show 2 * x + -2 * x = 0 by ring, Real.exp_zero]
    have hfac1 :
        x ^ 2 + Real.exp x =
          Real.exp x * (1 + x ^ 2 * Real.exp (-x)) := by
      calc
        x ^ 2 + Real.exp x = Real.exp x + x ^ 2 := by ring
        _ = Real.exp x + x ^ 2 * (Real.exp x * Real.exp (-x)) := by
          rw [he1, mul_one]
        _ = Real.exp x * (1 + x ^ 2 * Real.exp (-x)) := by ring
    have hfac2 :
        x ^ 4 + Real.exp (2 * x) =
          Real.exp (2 * x) * (1 + x ^ 4 * Real.exp (-2 * x)) := by
      calc
        x ^ 4 + Real.exp (2 * x) = Real.exp (2 * x) + x ^ 4 := by ring
        _ = Real.exp (2 * x) +
            x ^ 4 * (Real.exp (2 * x) * Real.exp (-2 * x)) := by
          rw [he2, mul_one]
        _ = Real.exp (2 * x) *
            (1 + x ^ 4 * Real.exp (-2 * x)) := by ring
    have hlog1 :
        Real.log (x ^ 2 + Real.exp x) =
          x + Real.log (1 + x ^ 2 * Real.exp (-x)) := by
      rw [hfac1,
        Real.log_mul (Real.exp_ne_zero x) (by positivity),
        Real.log_exp]
    have hlog2 :
        Real.log (x ^ 4 + Real.exp (2 * x)) =
          2 * x + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) := by
      rw [hfac2,
        Real.log_mul (Real.exp_ne_zero (2 * x)) (by positivity),
        Real.log_exp]
    unfold original rewritten
    rw [hlog1, hlog2]
  rw [h]

/-- Source: `proof_gap/exercise_566_1/2.txt`. -/
theorem gap2 :
    Filter.Tendsto normalized (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (1 / 2 : ℝ)) := by
  let F := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hx : Filter.Tendsto (fun x : ℝ => x) F (nhds 0) := by
    exact continuousAt_id.tendsto.mono_left inf_le_left
  have hxne : ∀ᶠ x : ℝ in F, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hxmem
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmem
  have hneg : Filter.Tendsto (fun x : ℝ => -x) F (nhds 0) := by
    simpa using hx.neg
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.exp (-x)) F (nhds 1) := by
    simpa using (Real.continuous_exp.continuousAt.tendsto.comp hneg)
  have hneg2 :
      Filter.Tendsto (fun x : ℝ => -2 * x) F (nhds 0) := by
    simpa [neg_mul] using (tendsto_const_nhds.mul hx).neg
  have hexp2 :
      Filter.Tendsto (fun x : ℝ => Real.exp (-2 * x)) F (nhds 1) := by
    simpa using (Real.continuous_exp.continuousAt.tendsto.comp hneg2)
  have hu :
      Filter.Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x)) F (nhds 0) := by
    simpa using (hx.pow 2).mul hexp
  have hv :
      Filter.Tendsto (fun x : ℝ => x ^ 4 * Real.exp (-2 * x)) F (nhds 0) := by
    simpa using (hx.pow 4).mul hexp2
  have huWithin :
      Filter.Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x)) F
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hu, ?_⟩
    filter_upwards [hxne] with x hx0
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      mul_ne_zero (pow_ne_zero 2 hx0) (Real.exp_ne_zero (-x))
  have hvWithin :
      Filter.Tendsto (fun x : ℝ => x ^ 4 * Real.exp (-2 * x)) F
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hv, ?_⟩
    filter_upwards [hxne] with x hx0
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      mul_ne_zero (pow_ne_zero 4 hx0) (Real.exp_ne_zero (-2 * x))
  have hinner :
      HasDerivAt (fun z : ℝ => 1 + z) 1 0 := by
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
        (hasDerivAt_id (𝕜 := ℝ) 0)
  have hderiv :
      HasDerivAt (fun z : ℝ => Real.log (1 + z)) 1 0 := by
    convert
      (Real.hasDerivAt_log
        (show (1 : ℝ) + 0 ≠ 0 by norm_num)).comp 0 hinner
      using 1 <;> norm_num
  have hlog :
      Filter.Tendsto (fun z : ℝ => Real.log (1 + z) / z)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using hderiv.tendsto_slope_zero
  have hratioU :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log (1 + x ^ 2 * Real.exp (-x)) /
            (x ^ 2 * Real.exp (-x))) F (nhds 1) := by
    exact hlog.comp huWithin
  have hratioV :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log (1 + x ^ 4 * Real.exp (-2 * x)) /
            (x ^ 4 * Real.exp (-2 * x))) F (nhds 1) := by
    exact hlog.comp hvWithin
  have hnumCorr :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log (1 + x ^ 2 * Real.exp (-x)) /
              (x ^ 2 * Real.exp (-x)) * x * Real.exp (-x))
        F (nhds 0) := by
    simpa using (hratioU.mul hx).mul hexp
  have hdenCorr :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log (1 + x ^ 4 * Real.exp (-2 * x)) /
              (x ^ 4 * Real.exp (-2 * x)) * x ^ 3 * Real.exp (-2 * x))
        F (nhds 0) := by
    simpa using (hratioV.mul (hx.pow 3)).mul hexp2
  have hnum :
      Filter.Tendsto
        (fun x : ℝ =>
          1 + Real.log (1 + x ^ 2 * Real.exp (-x)) /
              (x ^ 2 * Real.exp (-x)) * x * Real.exp (-x))
        F (nhds 1) := by
    simpa using tendsto_const_nhds.add hnumCorr
  have hden :
      Filter.Tendsto
        (fun x : ℝ =>
          2 + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) /
              (x ^ 4 * Real.exp (-2 * x)) * x ^ 3 * Real.exp (-2 * x))
        F (nhds 2) := by
    simpa using tendsto_const_nhds.add hdenCorr
  change Filter.Tendsto
    (fun x : ℝ =>
      (1 + Real.log (1 + x ^ 2 * Real.exp (-x)) /
          (x ^ 2 * Real.exp (-x)) * x * Real.exp (-x)) /
        (2 + Real.log (1 + x ^ 4 * Real.exp (-2 * x)) /
          (x ^ 4 * Real.exp (-2 * x)) * x ^ 3 * Real.exp (-2 * x)))
    F (nhds (1 / 2 : ℝ))
  simpa only [one_div] using hnum.div hden (by norm_num : (2 : ℝ) ≠ 0)

end

end ProofGap.Exercise566_1
