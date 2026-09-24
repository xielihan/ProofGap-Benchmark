import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise780

noncomputable section

def xval (t : ℝ → ℝ) (a : ℝ) : ℝ := Real.arctan (t a)
def yval (t : ℝ → ℝ) (a : ℝ) : ℝ := Real.pi / 2 - xval t a
def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def domain : Set ℝ := Set.Ioo (-Real.pi / 2) (Real.pi / 2)

theorem gap1 (t : ℝ → ℝ) : ∀ a, -Real.pi / 2 < xval t a := by
  intro a
  simpa [xval, neg_div] using (Real.neg_pi_div_two_lt_arctan (t a))
theorem gap2 (t : ℝ → ℝ) : ∀ a, xval t a < Real.pi / 2 := by
  intro a
  simpa [xval] using (Real.arctan_lt_pi_div_two (t a))
theorem gap3 (t : ℝ → ℝ) : ∀ a, 0 < yval t a := by
  intro a
  rw [yval]
  exact sub_pos.mpr (gap2 t a)
theorem gap4 (t : ℝ → ℝ) : ∀ a, yval t a < Real.pi := by
  intro a
  unfold yval
  linarith [gap1 t a]
theorem gap5 (t : ℝ → ℝ) : ∀ a, Real.tan (xval t a) = t a := by
  intro a
  unfold xval
  exact Real.tan_arctan (t a)
theorem gap6 (t : ℝ → ℝ) : ∀ a, cot (yval t a) = t a := by
  intro a
  calc
    cot (yval t a) = Real.tan (xval t a) := by
      rw [yval, cot, Real.tan_eq_sin_div_cos,
        Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    _ = t a := gap5 t a
theorem gap7 (t : ℝ → ℝ) :
    ∀ a, cot (yval t a) = Real.tan (xval t a) := by
  intro a
  calc
    cot (yval t a) = t a := gap6 t a
    _ = Real.tan (xval t a) := (gap5 t a).symm
theorem gap8 (x : ℝ) :
    Real.tan x = cot (Real.pi / 2 - x) := by
  rw [Real.tan_eq_sin_div_cos, cot,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
theorem gap9 (t : ℝ → ℝ) :
    ∀ a, cot (yval t a) = cot (Real.pi / 2 - xval t a) := by
  intro a
  rfl
theorem gap10 (t : ℝ → ℝ) (a : ℝ)
    (h₁ : -Real.pi / 2 < xval t a) (h₂ : xval t a < Real.pi / 2) :
    yval t a = Real.pi / 2 - xval t a := by
  rfl
theorem gap11 (t : ℝ → ℝ) :
    ∀ a, yval t a = Real.pi / 2 - xval t a := by
  intro a
  rfl

/-- Source gap 12 uses a domain operator for an implicitly partial inverse;
record that intended principal domain explicitly. -/
theorem gap12 : domain = Set.Ioo (-Real.pi / 2) (Real.pi / 2) := by
  rfl

end

end ProofGap.Exercise780
