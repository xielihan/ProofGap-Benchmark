import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise488

noncomputable section

def original (a x : ℝ) : ℝ :=
  (Real.sin (a + 2 * x) - 2 * Real.sin (a + x) + Real.sin a) / x ^ 2
def differenceForm (a x : ℝ) : ℝ :=
  (Real.sin (a + 2 * x) - Real.sin (a + x) -
    (Real.sin (a + x) - Real.sin a)) / x ^ 2
def expanded (a x : ℝ) : ℝ :=
  (2 * Real.cos (a + 3 * x / 2) * Real.sin (x / 2) -
    2 * Real.cos (a + x / 2) * Real.sin (x / 2)) / x ^ 2
def factored (a x : ℝ) : ℝ :=
  2 * Real.sin (x / 2) *
    (Real.cos (a + 3 * x / 2) - Real.cos (a + x / 2)) / x ^ 2
def normalized (a x : ℝ) : ℝ :=
  -(Real.sin (x / 2) / (x / 2)) ^ 2 * Real.sin (a + x)
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 488, gap 1. -/
private theorem factored_eq_normalized (a x : ℝ) :
    factored a x = normalized a x := by
  by_cases hx : x = 0
  · subst x
    simp [factored, normalized]
  · unfold factored normalized
    have hsum :
        ((a + 3 * x / 2) + (a + x / 2)) / 2 = a + x := by
      ring
    have hdiff :
        ((a + 3 * x / 2) - (a + x / 2)) / 2 = x / 2 := by
      ring
    rw [Real.cos_sub_cos (a + 3 * x / 2) (a + x / 2), hsum, hdiff]
    field_simp [hx]

theorem gap1 (a L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (differenceForm a) L := by
  have h : original a = differenceForm a := by
    funext x
    unfold original differenceForm
    ring
  rw [h]

/-- Exercise 488, gap 2. -/
theorem gap2 (a L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (expanded a) L := by
  have h : differenceForm a = expanded a := by
    funext x
    unfold differenceForm expanded
    have h₁ : ((a + 2 * x) + (a + x)) / 2 = a + 3 * x / 2 := by ring
    have h₂ : ((a + 2 * x) - (a + x)) / 2 = x / 2 := by ring
    have h₃ : ((a + x) + a) / 2 = a + x / 2 := by ring
    have h₄ : ((a + x) - a) / 2 = x / 2 := by ring
    rw [Real.sin_sub_sin (a + 2 * x) (a + x),
      Real.sin_sub_sin (a + x) a, h₁, h₂, h₃, h₄]
    ring
  rw [gap1 a L, h]

/-- Exercise 488, gap 3. -/
theorem gap3 (a L : ℝ) :
    HasLimitAtZero (expanded a) L ↔ HasLimitAtZero (factored a) L := by
  have h : expanded a = factored a := by
    funext x
    unfold expanded factored
    ring
  rw [h]

/-- Exercise 488, gap 4. -/
theorem gap4 (a L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (factored a) L := by
  exact (gap2 a L).trans (gap3 a L)

/-- Exercise 488, gap 5. -/
theorem gap5 (a L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (normalized a) L := by
  rw [gap4 a L]
  have h : factored a = normalized a := by
    funext x
    exact factored_eq_normalized a x
  rw [h]

/-- Exercise 488, gap 6. -/
theorem gap6 (a : ℝ) : HasLimitAtZero (normalized a) (-Real.sin a) := by
  unfold HasLimitAtZero
  have hx : Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using
      (continuousAt_id.mono_left
        (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left))
  have hhalf_nhds : Filter.Tendsto (fun x : ℝ => x / 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    convert hx.div_const (2 : ℝ) using 1 <;> norm_num
  have hsinc_raw : Filter.Tendsto
      (fun x : ℝ => Real.sinc (x / 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sinc 0)) :=
    (Real.continuous_sinc.continuousAt.tendsto).comp hhalf_nhds
  have hsinc_cont : Filter.Tendsto
      (fun x : ℝ => Real.sinc (x / 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using hsinc_raw
  have heq :
      (fun x : ℝ => Real.sinc (x / 2)) =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun x : ℝ => Real.sin (x / 2) / (x / 2)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx'
    have hx0 : x ≠ 0 := by simpa using hx'
    have hxhalf : x / 2 ≠ 0 := div_ne_zero hx0 (by norm_num)
    simp [Real.sinc, hxhalf]
  have hsinc : Filter.Tendsto
      (fun x : ℝ => Real.sin (x / 2) / (x / 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hsinc_cont.congr' heq
  have harg0 : Filter.Tendsto (fun x : ℝ => a + x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (a + 0)) :=
    tendsto_const_nhds.add hx
  have harg : Filter.Tendsto (fun x : ℝ => a + x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := by
    simpa using harg0
  have hsin : Filter.Tendsto (fun x : ℝ => Real.sin (a + x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sin a)) :=
    (Real.continuous_sin.continuousAt.tendsto).comp harg
  have hsq : Filter.Tendsto
      (fun x : ℝ => (Real.sin (x / 2) / (x / 2)) ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using hsinc.pow 2
  change Filter.Tendsto
    (fun x : ℝ => -((Real.sin (x / 2) / (x / 2)) ^ 2) * Real.sin (a + x))
    (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-Real.sin a))
  simpa only [neg_mul, one_mul] using hsq.neg.mul hsin

/-- Exercise 488, gap 7. -/
theorem gap7 (a : ℝ) : HasLimitAtZero (original a) (-Real.sin a) := by
  exact (gap5 a (-Real.sin a)).mpr (gap6 a)

end

end ProofGap.Exercise488
