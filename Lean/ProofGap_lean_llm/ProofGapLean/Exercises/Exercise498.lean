import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise498

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def original (x : ℝ) : ℝ :=
  (1 - cot x ^ 3) / (2 - cot x - cot x ^ 3)
def sineCosine (x : ℝ) : ℝ :=
  (Real.sin x ^ 3 - Real.cos x ^ 3) /
    (2 * Real.sin x ^ 3 - Real.sin x ^ 2 * Real.cos x - Real.cos x ^ 3)
def cancelled (x : ℝ) : ℝ :=
  (Real.sin x ^ 2 + Real.sin x * Real.cos x + Real.cos x ^ 2) /
    (2 * Real.sin x ^ 2 + Real.sin x * Real.cos x + Real.cos x ^ 2)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 498, gap 1. -/
private theorem eventually_trig_regular :
    ∀ᶠ x : ℝ in nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ,
      Real.sin x ≠ 0 ∧ Real.sin x ≠ Real.cos x := by
  have hnear :
      Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhds (Real.pi / 4) :=
    Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hnear' :
      ∀ᶠ x : ℝ in nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Filter.Eventually.filter_mono inf_le_left hnear
  filter_upwards [hnear', self_mem_nhdsWithin] with x hx hmem
  have hxa : x ≠ Real.pi / 4 := by
    simpa using hmem
  have hx0 : 0 < x := hx.1
  have hxpi : x < Real.pi := by
    linarith [hx.2, Real.pi_pos]
  have hsinpos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  constructor
  · exact ne_of_gt hsinpos
  · intro heq
    have hsinDiff : Real.sin (x - Real.pi / 4) = 0 := by
      rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four, heq]
      ring
    have hdiff : x - Real.pi / 4 = 0 := by
      by_contra hne
      rcases lt_trichotomy (x - Real.pi / 4) 0 with hneg | hzero | hpos
      · have hposNeg :
            0 < Real.sin (-(x - Real.pi / 4)) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith)
            (by linarith [hx0, Real.pi_pos])
        have hzNeg : Real.sin (-(x - Real.pi / 4)) = 0 := by
          rw [Real.sin_neg, hsinDiff]
          norm_num
        exact (ne_of_gt hposNeg) hzNeg
      · exact hne hzero
      · exact
          (ne_of_gt
            (Real.sin_pos_of_pos_of_lt_pi hpos
              (by linarith [hx.2, Real.pi_pos])))
            hsinDiff
    apply hxa
    linarith

theorem gap1 (L : ℝ) :
    HasLimitAt original (Real.pi / 4) L ↔
      HasLimitAt sineCosine (Real.pi / 4) L := by
  unfold HasLimitAt
  have heq :
      original =ᶠ[nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ]
        sineCosine := by
    filter_upwards [eventually_trig_regular] with x hx
    have hs : Real.sin x ≠ 0 := hx.1
    unfold original sineCosine cot
    have hnum :
        1 - (Real.cos x / Real.sin x) ^ 3 =
          (Real.sin x ^ 3 - Real.cos x ^ 3) / Real.sin x ^ 3 := by
      field_simp [hs]
    have hden :
        2 - Real.cos x / Real.sin x - (Real.cos x / Real.sin x) ^ 3 =
          (2 * Real.sin x ^ 3 - Real.sin x ^ 2 * Real.cos x -
              Real.cos x ^ 3) /
            Real.sin x ^ 3 := by
      field_simp [hs]
    rw [hnum, hden]
    by_cases hq :
        2 * Real.sin x ^ 3 - Real.sin x ^ 2 * Real.cos x -
            Real.cos x ^ 3 = 0
    · simp [hq]
    · field_simp [hs, hq]
  exact Filter.tendsto_congr' heq

/-- Exercise 498, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAt sineCosine (Real.pi / 4) L ↔
      HasLimitAt cancelled (Real.pi / 4) L := by
  unfold HasLimitAt
  have heq :
      sineCosine =ᶠ[nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ]
        cancelled := by
    filter_upwards [eventually_trig_regular] with x hx
    have hsc : Real.sin x ≠ Real.cos x := hx.2
    have hd : Real.sin x - Real.cos x ≠ 0 := sub_ne_zero.mpr hsc
    unfold sineCosine cancelled
    have hnum :
        Real.sin x ^ 3 - Real.cos x ^ 3 =
          (Real.sin x - Real.cos x) *
            (Real.sin x ^ 2 + Real.sin x * Real.cos x +
              Real.cos x ^ 2) := by
      ring
    have hden :
        2 * Real.sin x ^ 3 - Real.sin x ^ 2 * Real.cos x -
            Real.cos x ^ 3 =
          (Real.sin x - Real.cos x) *
            (2 * Real.sin x ^ 2 + Real.sin x * Real.cos x +
              Real.cos x ^ 2) := by
      ring
    rw [hnum, hden]
    by_cases hq :
        2 * Real.sin x ^ 2 + Real.sin x * Real.cos x +
            Real.cos x ^ 2 = 0
    · simp [hq]
    · field_simp [hd, hq]
  exact Filter.tendsto_congr' heq

/-- Exercise 498, gap 3. -/
theorem gap3 : HasLimitAt cancelled (Real.pi / 4) (3 / 4) := by
  unfold HasLimitAt
  have hden :
      2 * Real.sin (Real.pi / 4) ^ 2 +
          Real.sin (Real.pi / 4) * Real.cos (Real.pi / 4) +
          Real.cos (Real.pi / 4) ^ 2 ≠ 0 := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hr : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  have hsin :
      ContinuousAt (fun x : ℝ => Real.sin x) (Real.pi / 4) :=
    Real.continuous_sin.continuousAt
  have hcos :
      ContinuousAt (fun x : ℝ => Real.cos x) (Real.pi / 4) :=
    Real.continuous_cos.continuousAt
  have hcont : ContinuousAt cancelled (Real.pi / 4) := by
    unfold cancelled
    exact
      (((hsin.pow 2).add (hsin.mul hcos)).add (hcos.pow 2)).div
        (((continuousAt_const.mul (hsin.pow 2)).add (hsin.mul hcos)).add
          (hcos.pow 2))
        hden
  have hval : cancelled (Real.pi / 4) = (3 / 4 : ℝ) := by
    unfold cancelled
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hr : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hhalf : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
      nlinarith
    have hprod :
        (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) := by
      simpa [pow_two] using hhalf
    rw [hhalf, hprod]
    norm_num
  rw [← hval]
  exact hcont.tendsto.mono_left inf_le_left

/-- Exercise 498, gap 4. -/
theorem gap4 : HasLimitAt original (Real.pi / 4) (3 / 4) := by
  exact (gap1 (3 / 4)).2 ((gap2 (3 / 4)).2 gap3)

end

end ProofGap.Exercise498
