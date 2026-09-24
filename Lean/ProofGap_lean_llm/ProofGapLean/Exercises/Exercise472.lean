import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise472

noncomputable section

def reciprocal (x : ℝ) : ℝ := 1 / x
def f (x : ℝ) : ℝ := Real.sin x / x
def HasLimitAtPosInfinity (g : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto g Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_472/1.txt`. -/
theorem gap1 : HasLimitAtPosInfinity reciprocal 0 := by
  unfold HasLimitAtPosInfinity reciprocal
  simpa only [one_div] using
    (tendsto_inv_atTop_zero :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))

/-- Source: `proof_gap/exercise_472/2.txt`. -/
theorem gap2 (x : ℝ) : |Real.sin x| ≤ 1 := by
  exact (abs_le).2 ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

/-- Source: `proof_gap/exercise_472/3.txt`; squeeze by `1/x` on the positive tail. -/
theorem gap3 : HasLimitAtPosInfinity f 0 := by
  have hrec : Filter.Tendsto reciprocal Filter.atTop (nhds 0) := gap1
  have hneg :
      Filter.Tendsto (fun x : ℝ => -reciprocal x) Filter.atTop (nhds 0) := by
    simpa only [neg_zero] using hrec.neg
  have hbounds :
      ∀ᶠ x : ℝ in Filter.atTop,
        -reciprocal x ≤ f x ∧ f x ≤ reciprocal x := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
    rcases (abs_le.mp (gap2 x)) with ⟨hsin_lower, hsin_upper⟩
    have hlower : (-1 : ℝ) / x ≤ Real.sin x / x :=
      div_le_div_of_nonneg_right hsin_lower hx0
    have hupper : Real.sin x / x ≤ (1 : ℝ) / x :=
      div_le_div_of_nonneg_right hsin_upper hx0
    constructor
    · change -(1 / x) ≤ Real.sin x / x
      calc
        -(1 / x) = (-1 : ℝ) / x := (neg_div x (1 : ℝ)).symm
        _ ≤ Real.sin x / x := hlower
    · change Real.sin x / x ≤ 1 / x
      exact hupper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hneg hrec (hbounds.mono fun _ hx => hx.1) (hbounds.mono fun _ hx => hx.2)

/-- Source: `proof_gap/exercise_472/4.txt`. -/
theorem gap4 : HasLimitAtPosInfinity f 0 := by
  exact gap3

end

end ProofGap.Exercise472
