import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise594

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.sqrt (1 + x + x ^ 2) - Real.sqrt (1 - x + x ^ 2)
def rationalized (x : ℝ) : ℝ :=
  2 * x / (Real.sqrt (1 + x + x ^ 2) + Real.sqrt (1 - x + x ^ 2))
def normalizedNeg (x : ℝ) : ℝ :=
  -2 / (Real.sqrt (1 / x ^ 2 + 1 / x + 1) +
    Real.sqrt (1 / x ^ 2 - 1 / x + 1))
def normalizedPos (x : ℝ) : ℝ :=
  2 / (Real.sqrt (1 / x ^ 2 + 1 / x + 1) +
    Real.sqrt (1 / x ^ 2 - 1 / x + 1))
def HasLimitAtNegInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atBot (nhds L)
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_594/1.txt`. -/
private theorem original_eq_rationalized_fn : original = rationalized := by
  funext x
  unfold original rationalized
  have ha : 0 < 1 + x + x ^ 2 := by
    nlinarith [sq_nonneg (x + (1 / 2 : ℝ))]
  have hb : 0 < 1 - x + x ^ 2 := by
    nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]
  have hsa : 0 < Real.sqrt (1 + x + x ^ 2) := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt (1 - x + x ^ 2) := Real.sqrt_pos.2 hb
  apply (eq_div_iff (ne_of_gt (add_pos hsa hsb))).2
  nlinarith [Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt (le_of_lt hb)]

private theorem rationalized_eq_normalizedNeg {x : ℝ} (hx : x < 0) :
    rationalized x = normalizedNeg x := by
  have hx0 : x ≠ 0 := ne_of_lt hx
  have ha : 0 < 1 + x + x ^ 2 := by
    nlinarith [sq_nonneg (x + (1 / 2 : ℝ))]
  have hA :
      1 + x + x ^ 2 = x ^ 2 * (1 / x ^ 2 + 1 / x + 1) := by
    field_simp [hx0]
  have hB :
      1 - x + x ^ 2 = x ^ 2 * (1 / x ^ 2 - 1 / x + 1) := by
    field_simp [hx0]
  have hsA :
      Real.sqrt (1 + x + x ^ 2) =
        -x * Real.sqrt (1 / x ^ 2 + 1 / x + 1) := by
    rw [hA, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_neg hx]
  have hsB :
      Real.sqrt (1 - x + x ^ 2) =
        -x * Real.sqrt (1 / x ^ 2 - 1 / x + 1) := by
    rw [hB, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_neg hx]
  have hsum :
      Real.sqrt (1 / x ^ 2 + 1 / x + 1) +
          Real.sqrt (1 / x ^ 2 - 1 / x + 1) ≠ 0 := by
    intro h
    have hz : Real.sqrt (1 / x ^ 2 + 1 / x + 1) = 0 := by
      nlinarith [Real.sqrt_nonneg (1 / x ^ 2 + 1 / x + 1),
        Real.sqrt_nonneg (1 / x ^ 2 - 1 / x + 1)]
    have hsqrtzero : Real.sqrt (1 + x + x ^ 2) = 0 := by
      calc
        Real.sqrt (1 + x + x ^ 2) =
            -x * Real.sqrt (1 / x ^ 2 + 1 / x + 1) := hsA
        _ = -x * 0 := congrArg (fun z : ℝ => -x * z) hz
        _ = 0 := mul_zero _
    exact (ne_of_gt (Real.sqrt_pos.2 ha)) hsqrtzero
  unfold rationalized normalizedNeg
  rw [hsA, hsB]
  have hfactor :
      -x * Real.sqrt (1 / x ^ 2 + 1 / x + 1) +
          -x * Real.sqrt (1 / x ^ 2 - 1 / x + 1) =
        -x * (Real.sqrt (1 / x ^ 2 + 1 / x + 1) +
          Real.sqrt (1 / x ^ 2 - 1 / x + 1)) := by
    ring
  rw [hfactor]
  field_simp [hx0, hsum]

private theorem rationalized_eq_normalizedPos {x : ℝ} (hx : 0 < x) :
    rationalized x = normalizedPos x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : 0 < 1 + x + x ^ 2 := by
    nlinarith [sq_nonneg (x + (1 / 2 : ℝ))]
  have hA :
      1 + x + x ^ 2 = x ^ 2 * (1 / x ^ 2 + 1 / x + 1) := by
    field_simp [hx0]
  have hB :
      1 - x + x ^ 2 = x ^ 2 * (1 / x ^ 2 - 1 / x + 1) := by
    field_simp [hx0]
  have hsA :
      Real.sqrt (1 + x + x ^ 2) =
        x * Real.sqrt (1 / x ^ 2 + 1 / x + 1) := by
    rw [hA, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_pos hx]
  have hsB :
      Real.sqrt (1 - x + x ^ 2) =
        x * Real.sqrt (1 / x ^ 2 - 1 / x + 1) := by
    rw [hB, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_pos hx]
  have hsum :
      Real.sqrt (1 / x ^ 2 + 1 / x + 1) +
          Real.sqrt (1 / x ^ 2 - 1 / x + 1) ≠ 0 := by
    intro h
    have hz : Real.sqrt (1 / x ^ 2 + 1 / x + 1) = 0 := by
      nlinarith [Real.sqrt_nonneg (1 / x ^ 2 + 1 / x + 1),
        Real.sqrt_nonneg (1 / x ^ 2 - 1 / x + 1)]
    have hsqrtzero : Real.sqrt (1 + x + x ^ 2) = 0 := by
      calc
        Real.sqrt (1 + x + x ^ 2) =
            x * Real.sqrt (1 / x ^ 2 + 1 / x + 1) := hsA
        _ = x * 0 := congrArg (fun z : ℝ => x * z) hz
        _ = 0 := mul_zero _
    exact (ne_of_gt (Real.sqrt_pos.2 ha)) hsqrtzero
  unfold rationalized normalizedPos
  rw [hsA, hsB]
  have hfactor :
      x * Real.sqrt (1 / x ^ 2 + 1 / x + 1) +
          x * Real.sqrt (1 / x ^ 2 - 1 / x + 1) =
        x * (Real.sqrt (1 / x ^ 2 + 1 / x + 1) +
          Real.sqrt (1 / x ^ 2 - 1 / x + 1)) := by
    ring
  rw [hfactor]
  field_simp [hx0, hsum]

private theorem normalizedNeg_tendsto :
    HasLimitAtNegInfinity normalizedNeg (-1) := by
  unfold HasLimitAtNegInfinity
  have hinv : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atBot (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atBot_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atBot (nhds 0))
  have hp : ContinuousAt (fun y : ℝ => y ^ 2 + y + 1) 0 :=
    ((continuousAt_id.pow 2).add continuousAt_id).add continuousAt_const
  have hm : ContinuousAt (fun y : ℝ => y ^ 2 - y + 1) 0 :=
    ((continuousAt_id.pow 2).sub continuousAt_id).add continuousAt_const
  have hsp : ContinuousAt (fun y : ℝ => Real.sqrt (y ^ 2 + y + 1)) 0 :=
    Real.continuous_sqrt.continuousAt.comp hp
  have hsm : ContinuousAt (fun y : ℝ => Real.sqrt (y ^ 2 - y + 1)) 0 :=
    Real.continuous_sqrt.continuousAt.comp hm
  have hden : ContinuousAt
      (fun y : ℝ => Real.sqrt (y ^ 2 + y + 1) +
        Real.sqrt (y ^ 2 - y + 1)) 0 :=
    hsp.add hsm
  have hden0 :
      Real.sqrt ((0 : ℝ) ^ 2 + 0 + 1) +
          Real.sqrt ((0 : ℝ) ^ 2 - 0 + 1) ≠ 0 := by
    norm_num
  have hquot : ContinuousAt
      (fun y : ℝ => (-2 : ℝ) /
        (Real.sqrt (y ^ 2 + y + 1) + Real.sqrt (y ^ 2 - y + 1))) 0 :=
    continuousAt_const.div hden hden0
  have hfun :
      (fun y : ℝ => (-2 : ℝ) /
        (Real.sqrt (y ^ 2 + y + 1) + Real.sqrt (y ^ 2 - y + 1))) ∘
          (fun x : ℝ => 1 / x) = normalizedNeg := by
    funext x
    simp [normalizedNeg, Function.comp_def, one_div, inv_pow]
  have ht := hquot.tendsto.comp hinv
  rw [hfun] at ht
  convert ht using 1 <;> norm_num

private theorem normalizedPos_tendsto :
    HasLimitAtPosInfinity normalizedPos 1 := by
  unfold HasLimitAtPosInfinity
  have hinv : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hp : ContinuousAt (fun y : ℝ => y ^ 2 + y + 1) 0 :=
    ((continuousAt_id.pow 2).add continuousAt_id).add continuousAt_const
  have hm : ContinuousAt (fun y : ℝ => y ^ 2 - y + 1) 0 :=
    ((continuousAt_id.pow 2).sub continuousAt_id).add continuousAt_const
  have hsp : ContinuousAt (fun y : ℝ => Real.sqrt (y ^ 2 + y + 1)) 0 :=
    Real.continuous_sqrt.continuousAt.comp hp
  have hsm : ContinuousAt (fun y : ℝ => Real.sqrt (y ^ 2 - y + 1)) 0 :=
    Real.continuous_sqrt.continuousAt.comp hm
  have hden : ContinuousAt
      (fun y : ℝ => Real.sqrt (y ^ 2 + y + 1) +
        Real.sqrt (y ^ 2 - y + 1)) 0 :=
    hsp.add hsm
  have hden0 :
      Real.sqrt ((0 : ℝ) ^ 2 + 0 + 1) +
          Real.sqrt ((0 : ℝ) ^ 2 - 0 + 1) ≠ 0 := by
    norm_num
  have hquot : ContinuousAt
      (fun y : ℝ => (2 : ℝ) /
        (Real.sqrt (y ^ 2 + y + 1) + Real.sqrt (y ^ 2 - y + 1))) 0 :=
    continuousAt_const.div hden hden0
  have hfun :
      (fun y : ℝ => (2 : ℝ) /
        (Real.sqrt (y ^ 2 + y + 1) + Real.sqrt (y ^ 2 - y + 1))) ∘
          (fun x : ℝ => 1 / x) = normalizedPos := by
    funext x
    simp [normalizedPos, Function.comp_def, one_div, inv_pow]
  have ht := hquot.tendsto.comp hinv
  rw [hfun] at ht
  convert ht using 1 <;> norm_num

theorem gap1 (L : ℝ) :
    HasLimitAtNegInfinity original L ↔ HasLimitAtNegInfinity rationalized L := by
  unfold HasLimitAtNegInfinity
  rw [original_eq_rationalized_fn]

/-- Source: `proof_gap/exercise_594/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtNegInfinity rationalized L ↔ HasLimitAtNegInfinity normalizedNeg L := by
  unfold HasLimitAtNegInfinity
  have hneg : ∀ᶠ x : ℝ in Filter.atBot, x < 0 := by
    refine Filter.eventually_atBot.2 ?_
    exact ⟨(-1 : ℝ), fun x hx => lt_of_le_of_lt hx (by norm_num)⟩
  have heq : rationalized =ᶠ[Filter.atBot] normalizedNeg := by
    filter_upwards [hneg] with x hx
    exact rationalized_eq_normalizedNeg hx
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Source: `proof_gap/exercise_594/3.txt`. -/
theorem gap3 : HasLimitAtNegInfinity normalizedNeg (-1) := by
  exact normalizedNeg_tendsto

/-- Source: `proof_gap/exercise_594/4.txt`. -/
theorem gap4 : HasLimitAtNegInfinity original (-1) := by
  exact (gap1 (-1)).2 ((gap2 (-1)).2 gap3)

/-- Source: `proof_gap/exercise_594/5.txt`. -/
theorem gap5 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity rationalized L := by
  unfold HasLimitAtPosInfinity
  rw [original_eq_rationalized_fn]

/-- Source: `proof_gap/exercise_594/6.txt`. -/
theorem gap6 (L : ℝ) :
    HasLimitAtPosInfinity rationalized L ↔ HasLimitAtPosInfinity normalizedPos L := by
  unfold HasLimitAtPosInfinity
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < x := by
    refine Filter.eventually_atTop.2 ?_
    exact ⟨(1 : ℝ), fun x hx => lt_of_lt_of_le (by norm_num) hx⟩
  have heq : rationalized =ᶠ[Filter.atTop] normalizedPos := by
    filter_upwards [hpos] with x hx
    exact rationalized_eq_normalizedPos hx
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Source: `proof_gap/exercise_594/7.txt`. -/
theorem gap7 : HasLimitAtPosInfinity normalizedPos 1 := by
  exact normalizedPos_tendsto

/-- Source: `proof_gap/exercise_594/8.txt`. -/
theorem gap8 : HasLimitAtPosInfinity original 1 := by
  exact (gap5 1).2 ((gap6 1).2 gap7)

end

end ProofGap.Exercise594
