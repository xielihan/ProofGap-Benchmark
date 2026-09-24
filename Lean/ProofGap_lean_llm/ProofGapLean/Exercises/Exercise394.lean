import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise394

noncomputable section

def f (x : ℝ) : ℝ := Real.rpow 2 x
def rangeOnInterval : Set ℝ :=
  {y | ∃ x ∈ Set.Ioo (-1 : ℝ) 2, y = f x}

/-- Exercise 394, gap 1; the open interval has an infimum, not a minimum at `-1`. -/
private theorem f_properties : StrictMono f ∧ Continuous f := by
  constructor
  · simpa [f] using
      (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2))
  · have hform :
        f = fun x : ℝ => Real.exp (Real.log 2 * x) := by
      funext x
      simpa [f] using
        (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) x)
    rw [hform]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)

theorem gap1 : sInf rangeOnInterval = f (-1) := by
  have hmono : StrictMono f := f_properties.1
  have hlower : f (-1) ∈ lowerBounds rangeOnInterval := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hmono.monotone hx.1.le
  have hnonempty : rangeOnInterval.Nonempty := by
    refine ⟨f 0, 0, ?_, rfl⟩
    constructor <;> norm_num
  have hbounded : BddBelow rangeOnInterval := ⟨f (-1), hlower⟩
  have hcont : Continuous f := f_properties.2
  apply le_antisymm
  · have htend :
        Filter.Tendsto f
          (nhdsWithin (-1) (Set.Ioi (-1))) (nhds (f (-1))) :=
      hcont.continuousAt.mono_left inf_le_left
    have hlt :
        ∀ᶠ x : ℝ in nhdsWithin (-1) (Set.Ioi (-1)), x < 2 := by
      exact Filter.Eventually.filter_mono inf_le_left
        (Iio_mem_nhds (by norm_num))
    have hevent :
        ∀ᶠ x : ℝ in nhdsWithin (-1) (Set.Ioi (-1)),
          sInf rangeOnInterval ≤ f x := by
      filter_upwards [self_mem_nhdsWithin, hlt] with x hx hxtwo
      exact csInf_le hbounded ⟨x, ⟨hx, hxtwo⟩, rfl⟩
    exact isClosed_Ici.mem_of_tendsto htend hevent
  · exact le_csInf hnonempty hlower

/-- Exercise 394, gap 2. -/
theorem gap2 : f (-1) = 1 / 2 := by
  have hpow :
      Real.rpow 2 (-1) = Real.exp (Real.log 2 * (-1)) := by
    exact Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-1)
  rw [f, hpow]
  simp only [mul_neg, mul_one, Real.exp_neg]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Exercise 394, gap 3; interpret `m₀` as the infimum. -/
theorem gap3 : sInf rangeOnInterval = 1 / 2 := by
  rw [gap1, gap2]

/-- Exercise 394, gap 4; the open interval has a supremum, not a maximum at `2`. -/
theorem gap4 : sSup rangeOnInterval = f 2 := by
  have hmono : StrictMono f := f_properties.1
  have hupper : f 2 ∈ upperBounds rangeOnInterval := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hmono.monotone hx.2.le
  have hnonempty : rangeOnInterval.Nonempty := by
    refine ⟨f 0, 0, ?_, rfl⟩
    constructor <;> norm_num
  have hbounded : BddAbove rangeOnInterval := ⟨f 2, hupper⟩
  have hcont : Continuous f := f_properties.2
  apply le_antisymm
  · exact csSup_le hnonempty hupper
  · have htend :
        Filter.Tendsto f
          (nhdsWithin 2 (Set.Iio 2)) (nhds (f 2)) :=
      hcont.continuousAt.mono_left inf_le_left
    have hgt :
        ∀ᶠ x : ℝ in nhdsWithin 2 (Set.Iio 2), -1 < x := by
      exact Filter.Eventually.filter_mono inf_le_left
        (Ioi_mem_nhds (by norm_num))
    have hevent :
        ∀ᶠ x : ℝ in nhdsWithin 2 (Set.Iio 2),
          f x ≤ sSup rangeOnInterval := by
      filter_upwards [self_mem_nhdsWithin, hgt] with x hxtwo hxone
      exact le_csSup hbounded ⟨x, ⟨hxone, hxtwo⟩, rfl⟩
    exact isClosed_Iic.mem_of_tendsto htend hevent

/-- Exercise 394, gap 5. -/
theorem gap5 : f 2 = 4 := by
  change Real.rpow 2 2 = 4
  norm_num [Real.rpow_two]

/-- Exercise 394, gap 6; interpret `M₀` as the supremum. -/
theorem gap6 : sSup rangeOnInterval = 4 := by
  rw [gap4, gap5]

end

end ProofGap.Exercise394
