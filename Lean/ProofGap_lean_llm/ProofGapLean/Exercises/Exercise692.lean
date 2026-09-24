import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise692

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.sqrt ((1 - Real.cos (Real.pi * x)) / (4 - x ^ 2))

def transformed (x : ℝ) : ℝ :=
  Real.sqrt
    ((2 * Real.pi * (Real.sin ((Real.pi / 2) * (2 - x))) ^ 2) /
      (((Real.pi / 2) * (2 - x)) * 2 * (2 + x)))

/-- A singular point of the original partial formula is a zero of its
denominator.  This avoids treating Lean's totalized `0 / 0 = 0` as part of
the intended domain. -/
def SingularPoint (_f : ℝ → ℝ) (a : ℝ) : Prop := 4 - a ^ 2 = 0

/-- Exercise 692, gap 1; formulate equality of the two
limits rather than an implication guarded by a free singular point. -/
theorem gap1 (L : ℝ) :
    Filter.Tendsto y (nhds 2) (nhds L) ↔
      Filter.Tendsto transformed (nhds 2) (nhds L) := by
  have hfun : y = transformed := by
    funext x
    unfold y transformed
    apply congrArg Real.sqrt
    have hcos : Real.cos (Real.pi * x) =
        1 - 2 * (Real.sin ((Real.pi / 2) * (2 - x))) ^ 2 := by
      calc
        Real.cos (Real.pi * x) =
            Real.cos (2 * Real.pi - Real.pi * (2 - x)) := by
              congr 1
              ring
        _ = Real.cos (Real.pi * (2 - x)) := by
              rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
              ring
        _ = 1 - 2 * (Real.sin ((Real.pi / 2) * (2 - x))) ^ 2 := by
              rw [show Real.pi * (2 - x) =
                2 * ((Real.pi / 2) * (2 - x)) by ring]
              rw [Real.cos_two_mul]
              nlinarith [Real.sin_sq_add_cos_sq
                ((Real.pi / 2) * (2 - x))]
    rw [hcos]
    have hden : 4 - x ^ 2 = (2 - x) * (2 + x) := by ring
    have htransden :
        ((Real.pi / 2) * (2 - x)) * 2 * (2 + x) =
          Real.pi * ((2 - x) * (2 + x)) := by
      ring
    rw [hden, htransden]
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    by_cases hd : (2 - x) * (2 + x) = 0
    · simp [hd]
    · field_simp [hd, hpi]
      ring
  rw [hfun]

/-- Exercise 692, gap 2. -/
theorem gap2 :
    Filter.Tendsto transformed (nhds 2) (nhds 0) := by
  unfold transformed
  let u : ℝ → ℝ := fun x => (Real.pi / 2) * (2 - x)
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hcpos : 0 < Real.pi ^ 2 + 1 := by positivity
  have hepspos : 0 < ε ^ 2 := by nlinarith
  let δ : ℝ := min 1 (ε ^ 2 / (Real.pi ^ 2 + 1))
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hepspos hcpos)
  filter_upwards [Metric.ball_mem_nhds (2 : ℝ) hδpos] with x hx
  have hdist : dist x 2 < δ := by
    simpa [Metric.mem_ball] using hx
  have habsδ : |x - 2| < ε ^ 2 / (Real.pi ^ 2 + 1) := by
    have hdist' : |x - 2| < δ := by
      simpa [Real.dist_eq] using hdist
    exact lt_of_lt_of_le hdist' (min_le_right _ _)
  have habs1 : |x - 2| < 1 := by
    have hdist' : |x - 2| < δ := by
      simpa [Real.dist_eq] using hdist
    exact lt_of_lt_of_le hdist' (min_le_left _ _)
  have hxrange := abs_lt.mp habs1
  have hxlow : 1 < x := by linarith
  have hxden : 0 < 2 + x := by linarith
  have hpiabs : Real.pi ^ 2 * |x - 2| < ε ^ 2 := by
    have hle : Real.pi ^ 2 * |x - 2| ≤
        (Real.pi ^ 2 + 1) * |x - 2| := by
      nlinarith [abs_nonneg (x - 2)]
    have hlt := mul_lt_mul_of_pos_left habsδ hcpos
    have heq :
        (Real.pi ^ 2 + 1) *
            (ε ^ 2 / (Real.pi ^ 2 + 1)) = ε ^ 2 := by
      field_simp [ne_of_gt hcpos]
    calc
      Real.pi ^ 2 * |x - 2| ≤
          (Real.pi ^ 2 + 1) * |x - 2| := hle
      _ < (Real.pi ^ 2 + 1) *
          (ε ^ 2 / (Real.pi ^ 2 + 1)) := hlt
      _ = ε ^ 2 := heq
  change dist
    (Real.sqrt
      ((2 * Real.pi * (Real.sin (u x)) ^ 2) /
        (u x * 2 * (2 + x)))) 0 < ε
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  by_cases hleft : x < 2
  · have hu_pos : 0 < u x := by
      dsimp [u]
      exact mul_pos (div_pos Real.pi_pos (by norm_num))
        (sub_pos.mpr hleft)
    have hsin_abs : |Real.sin (u x)| ≤ |u x| := by
      exact Real.abs_sin_le_abs
    rw [abs_of_pos hu_pos] at hsin_abs
    have hsin_upper : Real.sin (u x) ≤ u x :=
      (le_abs_self (Real.sin (u x))).trans hsin_abs
    have hsin_lower : -(u x) ≤ Real.sin (u x) := by
      calc
        -(u x) ≤ -|Real.sin (u x)| := neg_le_neg hsin_abs
        _ ≤ Real.sin (u x) := neg_abs_le _
    have hprod :
        0 ≤ (u x - Real.sin (u x)) * (u x + Real.sin (u x)) := by
      exact mul_nonneg (sub_nonneg.mpr hsin_upper) (by linarith)
    have hsin_sq : (Real.sin (u x)) ^ 2 ≤ (u x) ^ 2 := by
      nlinarith
    have hsdiv : (Real.sin (u x)) ^ 2 / u x ≤ u x := by
      apply (div_le_iff₀ hu_pos).2
      simpa [pow_two] using hsin_sq
    have hsqdiv_nonneg :
        0 ≤ (Real.sin (u x)) ^ 2 / u x :=
      div_nonneg (sq_nonneg _) (le_of_lt hu_pos)
    have hq_nonneg :
        0 ≤ Real.pi * ((Real.sin (u x)) ^ 2 / u x) :=
      mul_nonneg (le_of_lt Real.pi_pos) hsqdiv_nonneg
    have hq_le :
        Real.pi * ((Real.sin (u x)) ^ 2 / u x) ≤
          Real.pi * u x :=
      mul_le_mul_of_nonneg_left hsdiv (le_of_lt Real.pi_pos)
    have hdiv_le :
        (Real.pi * ((Real.sin (u x)) ^ 2 / u x)) / (2 + x) ≤
          Real.pi * ((Real.sin (u x)) ^ 2 / u x) := by
      apply (div_le_iff₀ hxden).2
      have hxone : 0 ≤ 1 + x := by linarith
      nlinarith [mul_nonneg hq_nonneg hxone]
    have hrewrite :
        (2 * Real.pi * (Real.sin (u x)) ^ 2) /
            (u x * 2 * (2 + x)) =
          (Real.pi * ((Real.sin (u x)) ^ 2 / u x)) / (2 + x) := by
      field_simp [ne_of_gt hu_pos, ne_of_gt hxden] <;> ring
    have harg_le :
        (2 * Real.pi * (Real.sin (u x)) ^ 2) /
            (u x * 2 * (2 + x)) ≤ Real.pi * u x := by
      rw [hrewrite]
      exact hdiv_le.trans hq_le
    have habseq : |x - 2| = 2 - x := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    have hpu_le : Real.pi * u x ≤ Real.pi ^ 2 * |x - 2| := by
      rw [habseq]
      have hterm : 0 ≤ Real.pi ^ 2 * (2 - x) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      dsimp [u]
      nlinarith
    have harg_lt :
        (2 * Real.pi * (Real.sin (u x)) ^ 2) /
            (u x * 2 * (2 + x)) < ε ^ 2 :=
      lt_of_le_of_lt (harg_le.trans hpu_le) hpiabs
    have hden_pos : 0 < u x * 2 * (2 + x) := by positivity
    have harg_nonneg :
        0 ≤ (2 * Real.pi * (Real.sin (u x)) ^ 2) /
          (u x * 2 * (2 + x)) := by
      exact div_nonneg (by positivity) (le_of_lt hden_pos)
    have hsqrt_sq := Real.sq_sqrt harg_nonneg
    nlinarith [Real.sqrt_nonneg
      ((2 * Real.pi * (Real.sin (u x)) ^ 2) /
        (u x * 2 * (2 + x)))]
  · have hu_nonpos : u x ≤ 0 := by
      dsimp [u]
      have hxge : 2 ≤ x := le_of_not_gt hleft
      nlinarith [Real.pi_pos]
    have hden_nonpos : u x * 2 * (2 + x) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hu_nonpos (by norm_num))
        (le_of_lt hxden)
    have harg_nonpos :
        (2 * Real.pi * (Real.sin (u x)) ^ 2) /
            (u x * 2 * (2 + x)) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by positivity) hden_nonpos
    rw [Real.sqrt_eq_zero_of_nonpos harg_nonpos]
    exact hε

/-- Exercise 692, gap 3. -/
theorem gap3 :
    Filter.Tendsto y (nhds 2) (nhds 0) := by
  rw [gap1 0]
  exact gap2

/-- Exercise 692, gap 4. -/
theorem gap4 :
    Filter.Tendsto y (nhds (-2)) (nhds 0) := by
  have hr0 := (continuousAt_id.neg :
    ContinuousAt (fun x : ℝ => -x) (-2))
  change Filter.Tendsto (fun x : ℝ => -x)
    (nhds (-2)) (nhds (-(-2))) at hr0
  norm_num at hr0
  have heven : y ∘ (fun x : ℝ => -x) = y := by
    funext x
    unfold Function.comp y
    apply congrArg Real.sqrt
    rw [show Real.pi * -x = -(Real.pi * x) by ring, Real.cos_neg]
    congr 1
    ring
  have h := gap3.comp hr0
  rw [heven] at h
  exact h

/-- Exercise 692, gap 5; bind the actual singular point. -/
theorem gap5 : SingularPoint y 2 := by
  unfold SingularPoint
  norm_num

/-- Exercise 692, gap 6; bind the actual singular point. -/
theorem gap6 : SingularPoint y (-2) := by
  unfold SingularPoint
  norm_num

/-- Exercise 692, gap 7; bind the two limit values
independently. -/
theorem gap7 :
    (∃ L : ℝ, Filter.Tendsto y (nhds 2) (nhds L)) ∧
    (∃ L : ℝ, Filter.Tendsto y (nhds (-2)) (nhds L)) := by
  constructor
  · exact ⟨0, gap3⟩
  · exact ⟨0, gap4⟩

/-- Exercise 692, gap 8. -/
theorem gap8 (x : ℝ) (hx : x ∈ ({2, -2} : Set ℝ)) :
    SingularPoint y x := by
  rcases hx with (rfl | rfl)
  · exact gap5
  · exact gap6

end

end ProofGap.Exercise692
