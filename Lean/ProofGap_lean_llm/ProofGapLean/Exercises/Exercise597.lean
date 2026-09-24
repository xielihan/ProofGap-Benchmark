import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise597

noncomputable section

def original (x : ℝ) : ℝ := Real.log (1 + Real.exp x) / x
def normalizedNeg (x : ℝ) : ℝ :=
  (Real.log (1 + Real.exp x) / Real.exp x) * (Real.exp x / x)
def normalizedPos (x : ℝ) : ℝ :=
  1 + Real.log (Real.exp (-x) + 1) / x
def HasLimitAtNegInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atBot (nhds L)
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_597/1.txt`. -/
private theorem original_eq_normalizedNeg : original = normalizedNeg := by
  funext x
  unfold original normalizedNeg
  simp only [div_eq_mul_inv]
  calc
    Real.log (1 + Real.exp x) * x⁻¹ =
        Real.log (1 + Real.exp x) * ((Real.exp x)⁻¹ * Real.exp x) * x⁻¹ := by
      simp [Real.exp_ne_zero]
    _ = (Real.log (1 + Real.exp x) * (Real.exp x)⁻¹) *
          (Real.exp x * x⁻¹) := by
      ac_rfl

private theorem original_tendsto_atBot_zero :
    HasLimitAtNegInfinity original 0 := by
  unfold HasLimitAtNegInfinity original
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.exp x) Filter.atBot (nhds 0) :=
    Real.tendsto_exp_atBot
  have hsum :
      Filter.Tendsto (fun x : ℝ => 1 + Real.exp x) Filter.atBot (nhds 1) := by
    simpa using tendsto_const_nhds.add hexp
  have hlog :
      Filter.Tendsto (fun x : ℝ => Real.log (1 + Real.exp x))
        Filter.atBot (nhds 0) := by
    simpa using
      ((Real.continuousAt_log (one_ne_zero : (1 : ℝ) ≠ 0)).tendsto.comp hsum)
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atBot (nhds 0) :=
    tendsto_inv_atBot_zero
  simpa [div_eq_mul_inv] using hlog.mul hinv

private theorem original_eq_normalizedPos_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    original x = normalizedPos x := by
  unfold original normalizedPos
  have harg :
      1 + Real.exp x = Real.exp x * (Real.exp (-x) + 1) := by
    rw [Real.exp_neg, mul_add]
    simp [Real.exp_ne_zero]
  have htail : Real.exp (-x) + 1 ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos (-x)) zero_lt_one)
  calc
    Real.log (1 + Real.exp x) / x =
        (x + Real.log (Real.exp (-x) + 1)) / x := by
      rw [harg, Real.log_mul (Real.exp_ne_zero x) htail, Real.log_exp]
    _ = x / x + Real.log (Real.exp (-x) + 1) / x := by
      rw [add_div]
    _ = 1 + Real.log (Real.exp (-x) + 1) / x := by
      rw [div_self hx]

private theorem original_eventuallyEq_normalizedPos :
    original =ᶠ[Filter.atTop] normalizedPos := by
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < x :=
    (Filter.eventually_ge_atTop (1 : ℝ)).mono
      (fun _ hx => lt_of_lt_of_le zero_lt_one hx)
  exact hpos.mono
    (fun x hx => original_eq_normalizedPos_of_ne_zero x (ne_of_gt hx))

theorem gap1 (L : ℝ) :
    HasLimitAtNegInfinity original L ↔ HasLimitAtNegInfinity normalizedNeg L := by
  rw [original_eq_normalizedNeg]

/-- Source: `proof_gap/exercise_597/2.txt`. -/
theorem gap2 : HasLimitAtNegInfinity normalizedNeg 0 := by
  rw [← original_eq_normalizedNeg]
  exact original_tendsto_atBot_zero

/-- Source: `proof_gap/exercise_597/3.txt`. -/
theorem gap3 : HasLimitAtNegInfinity original 0 := by
  exact (gap1 0).2 gap2

/-- Source: `proof_gap/exercise_597/4.txt`. -/
theorem gap4 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity normalizedPos L := by
  unfold HasLimitAtPosInfinity
  constructor
  · intro h
    exact h.congr' original_eventuallyEq_normalizedPos
  · intro h
    exact h.congr' original_eventuallyEq_normalizedPos.symm

/-- Source: `proof_gap/exercise_597/5.txt`. -/
theorem gap5 : HasLimitAtPosInfinity normalizedPos 1 := by
  unfold HasLimitAtPosInfinity normalizedPos
  have hexpNeg :
      Filter.Tendsto (fun x : ℝ => Real.exp (-x)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      (Real.tendsto_exp_atBot.comp
        (Filter.tendsto_neg_atTop_atBot :
          Filter.Tendsto (fun x : ℝ => -x) Filter.atTop Filter.atBot))
  have hsum :
      Filter.Tendsto (fun x : ℝ => Real.exp (-x) + 1) Filter.atTop (nhds 1) := by
    simpa using hexpNeg.add tendsto_const_nhds
  have hlog :
      Filter.Tendsto (fun x : ℝ => Real.log (Real.exp (-x) + 1))
        Filter.atTop (nhds 0) := by
    simpa using
      ((Real.continuousAt_log (one_ne_zero : (1 : ℝ) ≠ 0)).tendsto.comp hsum)
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.add (hlog.mul hinv))

/-- Source: `proof_gap/exercise_597/6.txt`. -/
theorem gap6 : HasLimitAtPosInfinity original 1 := by
  exact (gap4 1).2 gap5

end

end ProofGap.Exercise597
