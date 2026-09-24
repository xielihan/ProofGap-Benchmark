import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise578

noncomputable section

def original (x : ℝ) : ℝ := x - Real.log (Real.cosh x)
def exponentialCosh (x : ℝ) : ℝ :=
  x - Real.log ((Real.exp (2 * x) + 1) / (2 * Real.exp x))
def expanded (x : ℝ) : ℝ :=
  2 * x + Real.log 2 - Real.log (1 + Real.exp (2 * x))
def normalized (x : ℝ) : ℝ :=
  Real.log 2 - Real.log (Real.exp (-2 * x) + 1)
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 578, gap 1. -/
theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity exponentialCosh L := by
  have hfun : original = exponentialCosh := by
    funext x
    unfold original exponentialCosh
    apply congrArg (fun z : ℝ => x - Real.log z)
    have hexp : Real.exp (2 * x) = Real.exp x * Real.exp x := by
      rw [show 2 * x = x + x by ring, Real.exp_add]
    rw [Real.cosh_eq, Real.exp_neg, hexp]
    field_simp [Real.exp_ne_zero] <;> ring
  rw [hfun]

/-- Exercise 578, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAtPosInfinity exponentialCosh L ↔ HasLimitAtPosInfinity expanded L := by
  have hfun : exponentialCosh = expanded := by
    funext x
    unfold exponentialCosh expanded
    have hn : Real.exp (2 * x) + 1 ≠ 0 := by
      have hp := Real.exp_pos (2 * x)
      linarith
    have hd : 2 * Real.exp x ≠ 0 :=
      mul_ne_zero (by norm_num) (Real.exp_ne_zero x)
    rw [Real.log_div hn hd]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero x)]
    rw [Real.log_exp]
    rw [show Real.exp (2 * x) + 1 = 1 + Real.exp (2 * x) by ring]
    ring
  rw [hfun]

/-- Exercise 578, gap 3. -/
theorem gap3 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity expanded L := by
  exact (gap1 L).trans (gap2 L)

/-- Exercise 578, gap 4. -/
theorem gap4 (L : ℝ) :
    HasLimitAtPosInfinity expanded L ↔ HasLimitAtPosInfinity normalized L := by
  have hfun : expanded = normalized := by
    funext x
    unfold expanded normalized
    have he : Real.exp (2 * x) ≠ 0 := Real.exp_ne_zero _
    have hnegexp :
        Real.exp (-2 * x) = (Real.exp (2 * x))⁻¹ := by
      rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
    have hfactor :
        1 + Real.exp (2 * x) =
          Real.exp (2 * x) * (Real.exp (-2 * x) + 1) := by
      rw [hnegexp]
      field_simp [he] <;> ring
    have hb : Real.exp (-2 * x) + 1 ≠ 0 := by
      have hp := Real.exp_pos (-2 * x)
      linarith
    rw [hfactor, Real.log_mul he hb, Real.log_exp]
    ring
  rw [hfun]

/-- Exercise 578, gap 5. -/
theorem gap5 : HasLimitAtPosInfinity normalized (Real.log 2) := by
  have hneg :
      Filter.Tendsto (fun x : ℝ => -2 * x)
        Filter.atTop Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop (-b / 2)] with x hx
    linarith
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.exp (-2 * x))
        Filter.atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp hneg
  have hsum :
      Filter.Tendsto (fun x : ℝ => Real.exp (-2 * x) + 1)
        Filter.atTop (nhds (1 : ℝ)) := by
    simpa using
      (hexp.add
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
            Filter.atTop (nhds 1)))
  have hlog :
      Filter.Tendsto (fun x : ℝ => Real.log (Real.exp (-2 * x) + 1))
        Filter.atTop (nhds (Real.log 1)) := by
    exact
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hsum
  unfold HasLimitAtPosInfinity normalized
  simpa using
    ((tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => Real.log 2)
          Filter.atTop (nhds (Real.log 2))).sub hlog)

/-- Exercise 578, gap 6. -/
theorem gap6 : HasLimitAtPosInfinity expanded (Real.log 2) := by
  exact (gap4 (Real.log 2)).mpr gap5

end

end ProofGap.Exercise578
