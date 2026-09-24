import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise808_2

noncomputable section

def f (x : ℝ) : ℝ := Real.sqrt x
def oscSet (s : Set ℝ) (δ : ℝ) : Set ℝ :=
  {|f x - f y| | (x ∈ s) (y ∈ s) (h : |x - y| ≤ δ)}
def ω (s : Set ℝ) (δ : ℝ) : ℝ := sSup (oscSet s δ)

private theorem omega_le_of_pointwise
    (s : Set ℝ) (δ M : ℝ) (hs : s.Nonempty) (hδ : 0 ≤ δ)
    (hbound : ∀ x ∈ s, ∀ y ∈ s, |x - y| ≤ δ →
      |Real.sqrt x - Real.sqrt y| ≤ M) :
    ω s δ ≤ M := by
  unfold ω
  apply csSup_le
  · rcases hs with ⟨x, hx⟩
    refine ⟨|f x - f x|, ?_⟩
    refine ⟨x, hx, x, hx, ?_, rfl⟩
    simpa using hδ
  · intro z hz
    rcases hz with ⟨x, hx, y, hy, hxy, rfl⟩
    simpa [f] using hbound x hx y hy hxy

theorem gap1 (x₁ x₂ : ℝ) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) :
    |Real.sqrt x₁ - Real.sqrt x₂| ≤ Real.sqrt |x₁ - x₂| := by
  rw [← Real.sqrt_sq_eq_abs (Real.sqrt x₁ - Real.sqrt x₂)]
  apply Real.sqrt_le_sqrt
  rcases le_total x₁ x₂ with h₁₂ | h₂₁
  · have hsqrt : Real.sqrt x₁ ≤ Real.sqrt x₂ := Real.sqrt_le_sqrt h₁₂
    rw [abs_of_nonpos (sub_nonpos.mpr h₁₂)]
    have hprod :
        0 ≤ Real.sqrt x₁ * (Real.sqrt x₂ - Real.sqrt x₁) :=
      mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hsqrt)
    nlinarith [Real.sq_sqrt hx₁, Real.sq_sqrt hx₂]
  · have hsqrt : Real.sqrt x₂ ≤ Real.sqrt x₁ := Real.sqrt_le_sqrt h₂₁
    rw [abs_of_nonneg (sub_nonneg.mpr h₂₁)]
    have hprod :
        0 ≤ Real.sqrt x₂ * (Real.sqrt x₁ - Real.sqrt x₂) :=
      mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hsqrt)
    nlinarith [Real.sq_sqrt hx₁, Real.sq_sqrt hx₂]
theorem gap2 (δ x₁ x₂ : ℝ) (hδ : 0 ≤ δ) (h : |x₁ - x₂| ≤ δ) :
    Real.sqrt |x₁ - x₂| ≤ Real.sqrt δ := by
  exact Real.sqrt_le_sqrt h
theorem gap3 (δ x₁ x₂ : ℝ) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hδ : 0 ≤ δ) (h : |x₁ - x₂| ≤ δ) :
    |Real.sqrt x₁ - Real.sqrt x₂| ≤ Real.sqrt δ := by
  exact (gap1 x₁ x₂ hx₁ hx₂).trans (gap2 δ x₁ x₂ hδ h)
theorem gap4 (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    ω (Set.Icc 0 a) δ ≤ Real.sqrt δ := by
  refine omega_le_of_pointwise (Set.Icc 0 a) δ (Real.sqrt δ) ?_ hδ ?_
  · exact ⟨0, ⟨le_rfl, ha⟩⟩
  · intro x hx y hy hxy
    exact gap3 δ x y hx.1 hy.1 hδ hxy
theorem gap5 (a x₁ x₂ : ℝ) (ha : 0 < a) (hx₁ : a < x₁) (hx₂ : a < x₂) :
    |Real.sqrt x₁ - Real.sqrt x₂| =
      |x₁ - x₂| / (Real.sqrt x₁ + Real.sqrt x₂) := by
  have hx₁pos : 0 < x₁ := lt_trans ha hx₁
  have hx₂pos : 0 < x₂ := lt_trans ha hx₂
  have hx₁nonneg : 0 ≤ x₁ := le_of_lt hx₁pos
  have hx₂nonneg : 0 ≤ x₂ := le_of_lt hx₂pos
  have hdenpos : 0 < Real.sqrt x₁ + Real.sqrt x₂ :=
    add_pos (Real.sqrt_pos.2 hx₁pos) (Real.sqrt_pos.2 hx₂pos)
  have hden : Real.sqrt x₁ + Real.sqrt x₂ ≠ 0 := ne_of_gt hdenpos
  have hid :
      Real.sqrt x₁ - Real.sqrt x₂ =
        (x₁ - x₂) / (Real.sqrt x₁ + Real.sqrt x₂) := by
    apply (eq_div_iff hden).2
    nlinarith [Real.sq_sqrt hx₁nonneg, Real.sq_sqrt hx₂nonneg]
  rw [hid, abs_div, abs_of_pos hdenpos]
theorem gap6 (a δ x₁ x₂ : ℝ) (ha : 0 < a) (hx₁ : a < x₁) (hx₂ : a < x₂)
    (h : |x₁ - x₂| ≤ δ) :
    |x₁ - x₂| / (Real.sqrt x₁ + Real.sqrt x₂) ≤
      δ / (2 * Real.sqrt a) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hbasepos : 0 < 2 * Real.sqrt a := by
    nlinarith
  have hs₁ : Real.sqrt a ≤ Real.sqrt x₁ :=
    Real.sqrt_le_sqrt (le_of_lt hx₁)
  have hs₂ : Real.sqrt a ≤ Real.sqrt x₂ :=
    Real.sqrt_le_sqrt (le_of_lt hx₂)
  have hdenlower :
      2 * Real.sqrt a ≤ Real.sqrt x₁ + Real.sqrt x₂ := by
    nlinarith
  calc
    |x₁ - x₂| / (Real.sqrt x₁ + Real.sqrt x₂) ≤
        |x₁ - x₂| / (2 * Real.sqrt a) :=
      div_le_div_of_nonneg_left (abs_nonneg _) hbasepos hdenlower
    _ ≤ δ / (2 * Real.sqrt a) := by
      have hinv : 0 ≤ (2 * Real.sqrt a)⁻¹ :=
        inv_nonneg.mpr (le_of_lt hbasepos)
      have hmul := mul_le_mul_of_nonneg_right h hinv
      simpa [div_eq_mul_inv] using hmul
theorem gap7 (a δ x₁ x₂ : ℝ) (ha : 0 < a) (hx₁ : a < x₁) (hx₂ : a < x₂)
    (h : |x₁ - x₂| ≤ δ) :
    |Real.sqrt x₁ - Real.sqrt x₂| ≤ δ / (2 * Real.sqrt a) := by
  rw [gap5 a x₁ x₂ ha hx₁ hx₂]
  exact gap6 a δ x₁ x₂ ha hx₁ hx₂ h
theorem gap8 (a δ : ℝ) (ha : 0 < a) (hδ : 0 ≤ δ) :
    ω (Set.Ioi a) δ ≤ δ / (2 * Real.sqrt a) := by
  refine omega_le_of_pointwise (Set.Ioi a) δ
    (δ / (2 * Real.sqrt a)) ?_ hδ ?_
  · exact ⟨a + 1, by simp⟩
  · intro x hx y hy hxy
    exact gap7 a δ x y ha hx hy hxy

/-- Record the two intended Hölder/Lipschitz choices separately. -/
theorem gap9 (a δ C α : ℝ) (ha : 0 < a) (hδ : 0 ≤ δ)
    (hpair : (C = 1 ∧ α = 1 / 2) ∨
      (C = 1 / (2 * Real.sqrt a) ∧ α = 1)) :
    (C = 1 → ω (Set.Ici 0) δ ≤ Real.sqrt δ) ∧
    (C = 1 / (2 * Real.sqrt a) → ω (Set.Ioi a) δ ≤ C * δ) := by
  constructor
  · intro _
    refine omega_le_of_pointwise (Set.Ici 0) δ (Real.sqrt δ) ?_ hδ ?_
    · exact ⟨0, by simp⟩
    · intro x hx y hy hxy
      exact gap3 δ x y hx hy hδ hxy
  · intro hC
    simpa [hC, div_eq_mul_inv, mul_comm] using gap8 a δ ha hδ

end

end ProofGap.Exercise808_2
