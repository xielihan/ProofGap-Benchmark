import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise600

noncomputable section

def f (x : ℝ) : ℝ := x + (Int.floor (x ^ 2) : ℝ)
def leftFilter : Filter ℝ := nhdsWithin 1 (Set.Iio 1)
def rightFilter : Filter ℝ := nhdsWithin 1 (Set.Ioi 1)

/-- Exercise 600, gap 1. -/
theorem gap1 : f 1 = 2 := by
  norm_num [f]

/-- Exercise 600, gap 2. -/
theorem gap2 (L : ℝ) :
    Filter.Tendsto f leftFilter (nhds L) ↔
      Filter.Tendsto (fun x => x + (Int.floor (x ^ 2) : ℝ)) leftFilter (nhds L) := by
  rfl

/-- Exercise 600, gap 3. -/
theorem gap3 :
    Filter.Tendsto (fun x => x + (Int.floor (x ^ 2) : ℝ))
      leftFilter (nhds (1 + 0)) := by
  have hId : Filter.Tendsto (fun x : ℝ => x) leftFilter (nhds 1) := by
    unfold leftFilter
    exact continuousAt_id.mono_left inf_le_left
  have hzero_nhds : ∀ᶠ x : ℝ in nhds 1, 0 < x := by
    exact Ioi_mem_nhds (by norm_num)
  have hzero_within : ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < x :=
    hzero_nhds.filter_mono inf_le_left
  have hEq :
      (fun x : ℝ => x + (Int.floor (x ^ 2) : ℝ)) =ᶠ[leftFilter]
        (fun x : ℝ => x) := by
    unfold leftFilter
    filter_upwards [self_mem_nhdsWithin, hzero_within] with x hx hzero
    have hsquare_lt : x ^ 2 < 1 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ < 1 * x := mul_lt_mul_of_pos_right hx hzero
        _ = x := one_mul x
        _ < 1 := hx
    have hfloor : Int.floor (x ^ 2) = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · calc
          ((0 : ℤ) : ℝ) = 0 := by norm_num
          _ ≤ x ^ 2 := sq_nonneg x
      · simpa using hsquare_lt
    simp [hfloor]
  simpa using hId.congr' hEq.symm

/-- Exercise 600, gap 4. -/
theorem gap4 : (1 : ℝ) + 0 = 1 := by
  norm_num

/-- Exercise 600, gap 5. -/
theorem gap5 : Filter.Tendsto f leftFilter (nhds 1) := by
  apply (gap2 1).2
  simpa using gap3

/-- Exercise 600, gap 6. -/
theorem gap6 (L : ℝ) :
    Filter.Tendsto f rightFilter (nhds L) ↔
      Filter.Tendsto (fun x => x + (Int.floor (x ^ 2) : ℝ)) rightFilter (nhds L) := by
  rfl

/-- Exercise 600, gap 7. -/
theorem gap7 :
    Filter.Tendsto (fun x => x + (Int.floor (x ^ 2) : ℝ))
      rightFilter (nhds (1 + 1)) := by
  have hId : Filter.Tendsto (fun x : ℝ => x) rightFilter (nhds 1) := by
    unfold rightFilter
    exact continuousAt_id.mono_left inf_le_left
  have hBase :
      Filter.Tendsto (fun x : ℝ => x + 1) rightFilter (nhds (1 + 1)) :=
    hId.add tendsto_const_nhds
  have hupper_nhds : ∀ᶠ x : ℝ in nhds 1, x < 5 / 4 := by
    exact Iio_mem_nhds (by norm_num)
  have hupper_within : ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Ioi 1), x < 5 / 4 :=
    hupper_nhds.filter_mono inf_le_left
  have hEq :
      (fun x : ℝ => x + (Int.floor (x ^ 2) : ℝ)) =ᶠ[rightFilter]
        (fun x : ℝ => x + 1) := by
    unfold rightFilter
    filter_upwards [self_mem_nhdsWithin, hupper_within] with x hx hupper
    have hxpos : 0 < x := lt_trans (by norm_num) hx
    have hsquare_lower : 1 < x ^ 2 := by
      calc
        (1 : ℝ) < x := hx
        _ = 1 * x := (one_mul x).symm
        _ < x * x := mul_lt_mul_of_pos_right hx hxpos
        _ = x ^ 2 := (pow_two x).symm
    have hsquare_upper : x ^ 2 < 2 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ < (5 / 4) * x := mul_lt_mul_of_pos_right hupper hxpos
        _ < (5 / 4) * (5 / 4) :=
          mul_lt_mul_of_pos_left hupper (by norm_num)
        _ < 2 := by norm_num
    have hfloor : Int.floor (x ^ 2) = 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · calc
          ((1 : ℤ) : ℝ) = 1 := by norm_num
          _ ≤ x ^ 2 := le_of_lt hsquare_lower
      · calc
          x ^ 2 < 2 := hsquare_upper
          _ = ((1 : ℤ) : ℝ) + 1 := by norm_num
    simp [hfloor]
  exact hBase.congr' hEq.symm

/-- Exercise 600, gap 8. -/
theorem gap8 : (1 : ℝ) + 1 = 2 := by
  norm_num

/-- Exercise 600, gap 9. -/
theorem gap9 : Filter.Tendsto f rightFilter (nhds 2) := by
  apply (gap6 2).2
  rw [← gap8]
  exact gap7

end

end ProofGap.Exercise600
