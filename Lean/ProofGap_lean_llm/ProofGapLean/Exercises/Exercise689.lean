import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise689

noncomputable section

def y (x : ℝ) : ℝ := (x ^ 2 - 1) / (x ^ 3 - 3 * x + 2)
def SingularPoint (f : ℝ → ℝ) (a : ℝ) : Prop := ¬ ContinuousAt f a

/-- Exercise 689, gap 1; remove the unrelated free
`SingularPoint(y,x)` guard and state the polynomial factorization globally. -/
private theorem abs_div_sub_tendsto_atTop
    (a : ℝ) (f : ℝ → ℝ) (hf : ContinuousAt f a) (hfa : f a ≠ 0) :
    Filter.Tendsto (fun x => |f x / (x - a)|)
      (nhdsWithin a ({a} : Set ℝ)ᶜ) atTop := by
  refine Filter.tendsto_atTop.2 (fun b => ?_)
  let B : ℝ := |b| + 1
  let c : ℝ := |f a|
  have hB : 0 < B := by
    dsimp [B]
    linarith [abs_nonneg b]
  have hc : 0 < c := by
    dsimp [c]
    exact abs_pos.mpr hfa
  have hhalf : c / 2 < |f a| := by
    dsimp [c]
    linarith
  have hnum_nhds : ∀ᶠ x in nhds a, c / 2 < |f x| :=
    hf.abs.tendsto.eventually (Ioi_mem_nhds hhalf)
  have hnum :
      ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, c / 2 < |f x| := by
    exact (show nhdsWithin a ({a} : Set ℝ)ᶜ ≤ nhds a from inf_le_left) hnum_nhds
  let r : ℝ := c / (2 * B)
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos hc (mul_pos (by norm_num) hB)
  have hball :
      ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, x ∈ Metric.ball a r := by
    exact (show nhdsWithin a ({a} : Set ℝ)ᶜ ≤ nhds a from inf_le_left)
      (Metric.ball_mem_nhds a hr)
  filter_upwards [hnum, hball, self_mem_nhdsWithin] with x hfx hxball hxmem
  have hxa : x ≠ a := by
    simpa using hxmem
  have hA : 0 < |x - a| := abs_pos.mpr (sub_ne_zero.mpr hxa)
  have hAr : |x - a| < r := by
    simpa [Real.dist_eq] using hxball
  have hbB : b < B := by
    dsimp [B]
    linarith [le_abs_self b]
  have hBr : B * r = c / 2 := by
    dsimp [r]
    field_simp [ne_of_gt hB]
  have hBA : B * |x - a| < c / 2 := by
    calc
      B * |x - a| < B * r := mul_lt_mul_of_pos_left hAr hB
      _ = c / 2 := hBr
  have hbA : b * |x - a| < B * |x - a| :=
    mul_lt_mul_of_pos_right hbB hA
  rw [abs_div]
  apply (le_div_iff₀ hA).2
  exact (lt_trans hbA (lt_trans hBA hfx)).le

private theorem not_continuousAt_of_abs_tendsto_atTop
    (f : ℝ → ℝ) (a : ℝ)
    (h : Filter.Tendsto (fun x => |f x|)
      (nhdsWithin a ({a} : Set ℝ)ᶜ) atTop) :
    ¬ ContinuousAt f a := by
  intro hf
  let M : ℝ := |f a| + 1
  have hbound : |f a| < M := by
    dsimp [M]
    linarith
  have hsmall_nhds : ∀ᶠ x in nhds a, |f x| < M :=
    hf.abs.tendsto.eventually (Iio_mem_nhds hbound)
  have hsmall :
      ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, |f x| < M := by
    exact (show nhdsWithin a ({a} : Set ℝ)ᶜ ≤ nhds a from inf_le_left) hsmall_nhds
  have hlarge :
      ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, M ≤ |f x| :=
    (Filter.tendsto_atTop.1 h) M
  rcases (hsmall.and hlarge).exists with ⟨x, hxsmall, hxlarge⟩
  exact (not_lt_of_ge hxlarge) hxsmall

theorem gap1 (x : ℝ) :
    (x ^ 2 - 1) / (x ^ 3 - 3 * x + 2) =
      ((x - 1) * (x + 1)) / ((x - 1) ^ 2 * (x + 2)) := by
  congr 1 <;> ring

/-- Exercise 689, gap 2; the two-sided signed limit at `1`
does not equal `+∞`, so record the correct divergence in absolute value. -/
theorem gap2 :
    Filter.Tendsto (fun x => |y x|)
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) atTop := by
  have hy (x : ℝ) :
      y x = ((x + 1) / (x + 2)) / (x - 1) := by
    by_cases h1 : x = 1
    · subst x
      norm_num [y]
    by_cases h2 : x = -2
    · subst x
      norm_num [y]
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr h1
    have hx2 : x + 2 ≠ 0 := by
      intro h
      apply h2
      linarith
    rw [y, gap1 x]
    field_simp [hx1, hx2] <;> ring
  have hf : ContinuousAt (fun x : ℝ => (x + 1) / (x + 2)) 1 := by
    exact (continuousAt_id.add continuousAt_const).div
      (continuousAt_id.add continuousAt_const) (by norm_num)
  have hfa : ((1 : ℝ) + 1) / (1 + 2) ≠ 0 := by
    norm_num
  have ht := abs_div_sub_tendsto_atTop
    (a := (1 : ℝ)) (f := fun x : ℝ => (x + 1) / (x + 2)) hf hfa
  simpa only [hy] using ht

/-- Exercise 689, gap 3; likewise, the one-sided signed
limits at `-2` have opposite signs, while the absolute value tends to `+∞`. -/
theorem gap3 :
    Filter.Tendsto (fun x => |y x|)
      (nhdsWithin (-2) ({-2} : Set ℝ)ᶜ) atTop := by
  have hy (x : ℝ) :
      y x = ((x + 1) / (x - 1)) / (x - (-2)) := by
    by_cases h1 : x = 1
    · subst x
      norm_num [y]
    by_cases h2 : x = -2
    · subst x
      norm_num [y]
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr h1
    have hx2 : x + 2 ≠ 0 := by
      intro h
      apply h2
      linarith
    rw [y, gap1 x]
    field_simp [hx1, hx2] <;> ring
  have hf : ContinuousAt (fun x : ℝ => (x + 1) / (x - 1)) (-2) := by
    exact (continuousAt_id.add continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) (by norm_num)
  have hfa : (((-2 : ℝ) + 1) / ((-2) - 1)) ≠ 0 := by
    norm_num
  have ht := abs_div_sub_tendsto_atTop
    (a := (-2 : ℝ)) (f := fun x : ℝ => (x + 1) / (x - 1)) hf hfa
  simpa only [hy] using ht

/-- Exercise 689, gap 4; bind the actual singular point. -/
theorem gap4 : SingularPoint y 1 := by
  unfold SingularPoint
  exact not_continuousAt_of_abs_tendsto_atTop
    (f := y) (a := (1 : ℝ)) gap2

/-- Exercise 689, gap 5; bind the actual singular point. -/
theorem gap5 : SingularPoint y (-2) := by
  unfold SingularPoint
  exact not_continuousAt_of_abs_tendsto_atTop
    (f := y) (a := (-2 : ℝ)) gap3

/-- Exercise 689, gap 6. -/
theorem gap6 (x : ℝ) (hx : x ∈ ({1, -2} : Set ℝ)) :
    SingularPoint y x := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact gap4
  · exact gap5

end

end ProofGap.Exercise689
