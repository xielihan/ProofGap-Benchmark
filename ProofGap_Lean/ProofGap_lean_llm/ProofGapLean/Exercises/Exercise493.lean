import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise493

noncomputable section

def original (x : ℝ) : ℝ :=
  (2 * Real.sin x ^ 2 + Real.sin x - 1) /
    (2 * Real.sin x ^ 2 - 3 * Real.sin x + 1)
def factored (x : ℝ) : ℝ :=
  ((2 * Real.sin x - 1) * (Real.sin x + 1)) /
    ((2 * Real.sin x - 1) * (Real.sin x - 1))
def cancelled (x : ℝ) : ℝ := (Real.sin x + 1) / (Real.sin x - 1)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 493, gap 1. -/
theorem gap1 (x : ℝ) :
    2 * Real.sin x ^ 2 + Real.sin x - 1 =
      (2 * Real.sin x - 1) * (Real.sin x + 1) := by
  ring

/-- Exercise 493, gap 2. -/
theorem gap2 (x : ℝ) :
    2 * Real.sin x ^ 2 - 3 * Real.sin x + 1 =
      (2 * Real.sin x - 1) * (Real.sin x - 1) := by
  ring

/-- Exercise 493, gap 3. -/
theorem gap3 (L : ℝ) :
    HasLimitAt original (Real.pi / 6) L ↔
      HasLimitAt factored (Real.pi / 6) L := by
  unfold HasLimitAt
  have hfun : original = factored := by
    funext x
    unfold original factored
    rw [gap1, gap2]
  rw [hfun]

/-- Exercise 493, gap 4. -/
theorem gap4 (L : ℝ) :
    HasLimitAt factored (Real.pi / 6) L ↔
      HasLimitAt cancelled (Real.pi / 6) L := by
  unfold HasLimitAt
  let a : ℝ := Real.pi / 6
  have ha_open : a ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [a]
    constructor <;> nlinarith [Real.pi_pos]
  have ha_closed : a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨le_of_lt ha_open.1, le_of_lt ha_open.2⟩
  have hinterval :
      ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    apply Filter.Eventually.filter_mono inf_le_left
    exact isOpen_Ioo.mem_nhds ha_open
  have heq :
      factored =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ] cancelled := by
    filter_upwards [hinterval, self_mem_nhdsWithin] with x hx hx_mem
    have hx_ne : x ≠ a := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx_mem
    have hx_closed : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hsin_ne : Real.sin x ≠ 1 / 2 := by
      intro hsin
      have hx_eq : x = a := by
        apply Real.strictMonoOn_sin.injOn
        · exact hx_closed
        · exact ha_closed
        · dsimp [a]
          simpa only [Real.sin_pi_div_six] using hsin
      exact hx_ne hx_eq
    have hfactor : 2 * Real.sin x - 1 ≠ 0 := by
      intro h
      apply hsin_ne
      nlinarith
    have hright : Real.pi / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · nlinarith [Real.pi_pos]
      · rfl
    have hsin_one : Real.sin x ≠ 1 := by
      have hlt := Real.strictMonoOn_sin hx_closed hright hx.2
      rw [Real.sin_pi_div_two] at hlt
      nlinarith
    have hden : Real.sin x - 1 ≠ 0 := sub_ne_zero.mpr hsin_one
    unfold factored cancelled
    field_simp [hfactor, hden]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 493, gap 5. -/
theorem gap5 : HasLimitAt cancelled (Real.pi / 6) (-3) := by
  unfold HasLimitAt
  have hden : Real.sin (Real.pi / 6) - 1 ≠ 0 := by
    rw [Real.sin_pi_div_six]
    norm_num
  have hnum_cont :
      ContinuousAt (fun x : ℝ => Real.sin x + 1) (Real.pi / 6) :=
    Real.continuous_sin.continuousAt.add continuousAt_const
  have hden_cont :
      ContinuousAt (fun x : ℝ => Real.sin x - 1) (Real.pi / 6) :=
    Real.continuous_sin.continuousAt.sub continuousAt_const
  have hcont : ContinuousAt cancelled (Real.pi / 6) := by
    unfold cancelled
    exact hnum_cont.div hden_cont hden
  have hval : cancelled (Real.pi / 6) = -3 := by
    unfold cancelled
    rw [Real.sin_pi_div_six]
    norm_num
  rw [← hval]
  exact hcont.mono_left inf_le_left

/-- Exercise 493, gap 6. -/
theorem gap6 : HasLimitAt original (Real.pi / 6) (-3) := by
  exact (gap3 (-3)).mpr ((gap4 (-3)).mpr gap5)

end

end ProofGap.Exercise493
