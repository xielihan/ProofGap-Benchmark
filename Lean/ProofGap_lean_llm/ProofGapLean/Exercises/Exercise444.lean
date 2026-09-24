import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise444

noncomputable section

def nthRoot (n : ℕ) (x : ℝ) : ℝ := Real.rpow x (1 / (n : ℝ))
def original (n : ℕ) (x : ℝ) : ℝ := (nthRoot n (1 + x) - 1) / x
def rootSum (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range n).sum (fun k => Real.rpow (1 + x) ((k : ℝ) / n))
def cancelled (n : ℕ) (x : ℝ) : ℝ := 1 / rootSum n x
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 444, gap 1; require a positive natural root degree and replace ellipses by a finite sum. -/
private theorem original_limit (n : ℕ) (hn : 0 < n) :
    HasLimitAt (original n) 0 (1 / (n : ℝ)) := by
  have hdRaw :
      HasDerivAt
        (fun y : ℝ => Real.rpow y (1 / (n : ℝ)))
        ((1 / (n : ℝ)) * Real.rpow (1 : ℝ) ((1 / (n : ℝ)) - 1))
        1 := by
    apply Real.hasDerivAt_rpow_const
    norm_num
  have hdBase :
      HasDerivAt
        (fun y : ℝ => Real.rpow y (1 / (n : ℝ)))
        (1 / (n : ℝ)) 1 := by
    simpa using hdRaw
  have hg : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_add (1 : ℝ)
  have hdBaseAtCompPoint :
      HasDerivAt
        (fun y : ℝ => Real.rpow y (1 / (n : ℝ)))
        (1 / (n : ℝ))
        ((fun x : ℝ => 1 + x) 0) := by
    simpa using hdBase
  have hd :
      HasDerivAt
        (fun x : ℝ => Real.rpow (1 + x) (1 / (n : ℝ)))
        (1 / (n : ℝ)) 0 := by
    simpa using hdBaseAtCompPoint.comp 0 hg
  have hslope := hd.tendsto_slope_zero
  unfold HasLimitAt original nthRoot
  simpa [div_eq_mul_inv, mul_comm] using hslope

private theorem cancelled_limit (n : ℕ) (hn : 0 < n) :
    HasLimitAt (cancelled n) 0 (1 / (n : ℝ)) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hterm (k : ℕ) :
      ContinuousAt
        (fun x : ℝ => Real.rpow (1 + x) ((k : ℝ) / (n : ℝ))) 0 := by
    have hb : ContinuousAt (fun x : ℝ => (1 : ℝ) + x) 0 := by
      exact continuousAt_const.add continuousAt_id
    have he :
        ContinuousAt (fun _ : ℝ => (k : ℝ) / (n : ℝ)) 0 :=
      continuousAt_const
    exact hb.rpow he (Or.inl (by norm_num))
  have hsumAux (s : Finset ℕ) :
      ContinuousAt
        (fun x : ℝ =>
          s.sum (fun k => Real.rpow (1 + x) ((k : ℝ) / (n : ℝ)))) 0 := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using
          (continuousAt_const :
            ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0)
    | @insert a s ha ih =>
        simpa [Finset.sum_insert, ha] using (hterm a).add ih
  have hsum :
      Filter.Tendsto (rootSum n) (nhds 0) (nhds (n : ℝ)) := by
    have h := (hsumAux (Finset.range n)).tendsto
    simpa [rootSum] using h
  have hfull :
      Filter.Tendsto (cancelled n) (nhds 0) (nhds (1 / (n : ℝ))) := by
    unfold cancelled
    simpa only [one_div] using hsum.inv₀ hn0
  unfold HasLimitAt
  exact hfull.mono_left inf_le_left

theorem gap1 (n : ℕ) (hn : 0 < n) :
    HasLimitAt (original n) 0 (1 / (n : ℝ)) ↔
      HasLimitAt (cancelled n) 0 (1 / (n : ℝ)) := by
  constructor
  · intro _
    exact cancelled_limit n hn
  · intro _
    exact original_limit n hn

/-- Exercise 444, gap 2; require `n>0`. -/
theorem gap2 (n : ℕ) (hn : 0 < n) :
    HasLimitAt (original n) 0 (1 / (n : ℝ)) ↔
      HasLimitAt (cancelled n) 0 (1 / (n : ℝ)) := by
  exact gap1 n hn

/-- Exercise 444, gap 3; require `n>0`. -/
theorem gap3 (n : ℕ) (hn : 0 < n) :
    HasLimitAt (cancelled n) 0 (1 / (n : ℝ)) := by
  exact cancelled_limit n hn

/-- Exercise 444, gap 4; require `n>0`. -/
theorem gap4 (n : ℕ) (hn : 0 < n) :
    HasLimitAt (original n) 0 (1 / (n : ℝ)) := by
  exact original_limit n hn

end

end ProofGap.Exercise444
