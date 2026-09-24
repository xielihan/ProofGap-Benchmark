import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise168

noncomputable section

def arg (x : ℝ) : ℝ := 2 * x / (1 + x ^ 2)
def domain : Set ℝ := {x | |arg x| ≤ 1}
def y (x : ℝ) : ℝ := Real.arccos (arg x)
def valueSet : Set ℝ := {t | ∃ x ∈ domain, t = y x}

/-- Source: `proof_gap/exercise_168/1.txt`. -/
theorem gap1 : ∀ x : ℝ, |arg x| ≤ 1 → x ∈ domain := by
  intro x hx
  exact hx

/-- Source: `proof_gap/exercise_168/2.txt`. -/
theorem gap2 : ∀ x : ℝ, |arg x| ≤ 1 := by
  intro x
  rw [abs_le]
  have hden : 0 < 1 + x ^ 2 := by positivity
  constructor
  · unfold arg
    apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg (x + 1)]
  · unfold arg
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg (x - 1)]

/-- Source: `proof_gap/exercise_168/3.txt`. -/
theorem gap3 : domain = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  exact gap2 x

/-- Source: `proof_gap/exercise_168/4.txt`; remove the shadowed existential y. -/
theorem gap4 : valueSet = Set.Icc 0 Real.pi := by
  ext t
  constructor
  · rintro ⟨x, hxdom, rfl⟩
    exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  · rintro ⟨ht0, htpi⟩
    let c : ℝ := Real.cos t
    let s : ℝ := Real.sqrt (1 - c ^ 2)
    let x : ℝ := c / (1 + s)
    have hrad : 0 ≤ 1 - c ^ 2 := by
      dsimp [c]
      have habs := Real.abs_cos_le_one t
      have hsq := (sq_le_sq₀ (abs_nonneg (Real.cos t)) zero_le_one).2 habs
      simpa only [sq_abs, one_pow] using sub_nonneg.mpr hsq
    have hs : s ^ 2 = 1 - c ^ 2 := by
      dsimp [s]
      exact Real.sq_sqrt hrad
    have hden : 1 + s ≠ 0 := by
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      linarith
    have harg : arg x = c := by
      unfold arg
      dsimp [x]
      field_simp [hden]
      ring_nf
      rw [hs]
      ring
    have hxdom : x ∈ domain := gap1 x (gap2 x)
    refine ⟨x, hxdom, ?_⟩
    unfold y
    rw [harg]
    dsimp [c]
    exact (Real.arccos_cos ht0 htpi).symm

end

end ProofGap.Exercise168
