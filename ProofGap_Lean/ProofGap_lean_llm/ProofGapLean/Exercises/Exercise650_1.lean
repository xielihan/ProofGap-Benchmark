import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise650_1

/-- Exercise 650_1, gap 1. -/
theorem gap1 :
    Filter.Tendsto (fun x : ℝ => (2 * x - x ^ 2) / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
  have hlim :
      Filter.Tendsto (fun x : ℝ => 2 - x) (nhds 0)
        (nhds ((fun x : ℝ => 2 - x) 0)) := by
    exact
      (continuousAt_const.sub continuousAt_id :
        ContinuousAt (fun x : ℝ => 2 - x) 0)
  simp only [sub_zero] at hlim
  have hlim' :
      Filter.Tendsto (fun x : ℝ => 2 - x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) :=
    hlim.mono_left inf_le_left
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp [hx0]

/-- Exercise 650_1, gap 2. -/
theorem gap2 :
    Asymptotics.IsEquivalent (nhdsWithin 0 (Set.Ioi 0))
      (fun x : ℝ => 2 * x - x ^ 2) (fun x => 2 * x) := by
  change Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
    (fun x : ℝ => (2 * x - x ^ 2) - 2 * x) (fun x => 2 * x)
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have h2c : 0 < 2 * c := by linarith
  have hlt_nhds : ∀ᶠ x : ℝ in nhds 0, x < 2 * c :=
    Iio_mem_nhds h2c
  have hlt : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x < 2 * c :=
    hlt_nhds.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hlt] with x hx hxc
  have hxpos : 0 < x := hx
  have hleft : (2 * x - x ^ 2) - 2 * x ≤ 0 := by
    nlinarith [sq_nonneg x]
  have hright : 0 < 2 * x := mul_pos (by norm_num) hxpos
  have hcx : 0 ≤ 2 * c - x := by linarith
  have hprod : 0 ≤ x * (2 * c - x) :=
    mul_nonneg (le_of_lt hxpos) hcx
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonpos hleft, abs_of_pos hright]
  nlinarith

/-- Exercise 650_1, gap 3. -/
theorem gap3 :
    Asymptotics.IsEquivalent (nhdsWithin 0 (Set.Ioi 0))
      (fun x : ℝ => 2 * x - x ^ 2) (fun x => 2 * x) := by
  exact gap2

end ProofGap.Exercise650_1
