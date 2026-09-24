import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise774

noncomputable section

def φ (x : ℝ) : ℝ := Real.arcsin x

theorem gap1 (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) : Real.sin (φ x) = x := by
  unfold φ
  exact Real.sin_arcsin hx.1 hx.2
theorem gap2 (x : ℝ) : Real.cos (Real.pi / 2 - φ x) = Real.sin (φ x) := by
  simp [Real.cos_sub]
theorem gap3 (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) : Real.sin (φ x) = x := by
  exact gap1 x hx
theorem gap4 (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) : Real.cos (Real.pi / 2 - φ x) = x := by
  calc
    Real.cos (Real.pi / 2 - φ x) = Real.sin (φ x) := gap2 x
    _ = x := gap3 x hx
theorem gap5 (x : ℝ) : -Real.pi / 2 ≤ φ x := by
  unfold φ
  simpa [neg_div] using Real.neg_pi_div_two_le_arcsin x
theorem gap6 (x : ℝ) : φ x ≤ Real.pi / 2 := by
  unfold φ
  exact Real.arcsin_le_pi_div_two x
theorem gap7 : -Real.pi / 2 ≤ Real.pi / 2 := by
  linarith [Real.pi_pos]
theorem gap8 (x : ℝ) : 0 ≤ Real.pi / 2 - φ x := by
  linarith [gap6 x]
theorem gap9 (x : ℝ) : Real.pi / 2 - φ x ≤ Real.pi := by
  linarith [gap5 x]
theorem gap10 : 0 ≤ Real.pi := by
  exact le_of_lt Real.pi_pos
theorem gap11 (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
    Real.pi / 2 - φ x = Real.arccos x := by
  simpa [φ] using (Real.arccos_eq_pi_div_two_sub_arcsin x).symm
theorem gap12 (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
    Real.arcsin x + Real.arccos x = Real.pi / 2 := by
  have h := gap11 x hx
  dsimp [φ] at h
  linarith
theorem gap13 (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
    Real.arcsin x + Real.arccos x = Real.pi / 2 := by
  exact gap12 x hx

end
end ProofGap.Exercise774
