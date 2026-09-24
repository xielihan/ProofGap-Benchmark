import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise402

noncomputable section

def g (x : ℝ) : ℝ := 1 / (1 - x) ^ 2

def TendsToPosInfinityAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ E > 0, ∃ δ > 0, ∀ x,
    0 < |x - a| → |x - a| < δ → E < f x

/-- Exercise 402, gap 1. -/
theorem gap1 : ∀ x E : ℝ, 0 < E →
    0 < |x - 1| → |x - 1| < 1 / Real.sqrt E →
      E < 1 / |1 - x| ^ 2 := by
  intro x E hE hx hlt
  have hsqrt : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hsqrt_sq : (Real.sqrt E) ^ 2 = E :=
    Real.sq_sqrt (le_of_lt hE)
  have hprod : |x - 1| * Real.sqrt E < 1 := by
    calc
      |x - 1| * Real.sqrt E <
          (1 / Real.sqrt E) * Real.sqrt E :=
        mul_lt_mul_of_pos_right hlt hsqrt
      _ = 1 := by
        field_simp [ne_of_gt hsqrt]
  have hprod_nonneg : 0 ≤ |x - 1| * Real.sqrt E :=
    mul_nonneg (abs_nonneg _) (le_of_lt hsqrt)
  have hplus : 0 < 1 + |x - 1| * Real.sqrt E := by
    nlinarith
  have hfactor :
      0 < (1 - |x - 1| * Real.sqrt E) *
        (1 + |x - 1| * Real.sqrt E) :=
    mul_pos (sub_pos.mpr hprod) hplus
  have hprod_sq : (|x - 1| * Real.sqrt E) ^ 2 < 1 := by
    nlinarith [hfactor]
  have habs_pos : 0 < |1 - x| := by
    rw [abs_sub_comm]
    exact hx
  apply (lt_div_iff₀ (pow_pos habs_pos 2)).2
  calc
    E * |1 - x| ^ 2 = (Real.sqrt E) ^ 2 * |1 - x| ^ 2 := by
      rw [hsqrt_sq]
    _ = (|x - 1| * Real.sqrt E) ^ 2 := by
      rw [abs_sub_comm 1 x]
      ring
    _ < 1 := hprod_sq

/-- Exercise 402, gap 2; choose the square-root scale directly instead of the false `1/E` comparison. -/
theorem gap2 : ∀ E > 0, ∃ δ > 0, δ = 1 / Real.sqrt E := by
  intro E hE
  refine ⟨1 / Real.sqrt E, ?_, rfl⟩
  exact one_div_pos.mpr (Real.sqrt_pos.2 hE)

/-- Exercise 402, gap 3. -/
theorem gap3 : ∀ x E : ℝ, 0 < E →
    0 < |x - 1| → |x - 1| < 1 / Real.sqrt E →
      E < 1 / |1 - x| ^ 2 := by
  exact gap1

/-- Exercise 402, gap 4; choose `δ` after `E`. -/
theorem gap4 : ∀ E > 0, ∃ δ > 0, ∀ x : ℝ,
    0 < |x - 1| → |x - 1| < δ → E < |g x| := by
  intro E hE
  refine ⟨1 / Real.sqrt E, one_div_pos.mpr (Real.sqrt_pos.2 hE), ?_⟩
  intro x hx hδ
  simpa only [g, abs_div, abs_one, abs_pow] using
    gap1 x E hE hx hδ

/-- Exercise 402, gap 5. -/
theorem gap5 : TendsToPosInfinityAt g 1 := by
  intro E hE
  refine ⟨1 / Real.sqrt E, one_div_pos.mpr (Real.sqrt_pos.2 hE), ?_⟩
  intro x hx hδ
  simpa only [g, sq_abs] using gap1 x E hE hx hδ

/-- Exercise 402, gap 6. -/
theorem gap6 : ∃ δ : ℝ, δ = 0.1 := by
  exact ⟨0.1, rfl⟩

/-- Exercise 402, gap 7. -/
theorem gap7 : ∃ δ : ℝ, δ = 0.01 := by
  exact ⟨0.01, rfl⟩

/-- Exercise 402, gap 8. -/
theorem gap8 : ∃ δ : ℝ, δ = 0.001 := by
  exact ⟨0.001, rfl⟩

/-- Exercise 402, gap 9. -/
theorem gap9 : ∃ δ : ℝ, δ = 0.0001 := by
  exact ⟨0.0001, rfl⟩

/-- Exercise 402, gap 10. -/
theorem gap10 : TendsToPosInfinityAt g 1 := by
  exact gap5

end

end ProofGap.Exercise402
