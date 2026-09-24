import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

namespace ProofGap.Exercise1235

noncomputable section

def f (x : ℝ) : ℝ := (x - 1) * (x - 2) * (x - 3)
def c₁ : ℝ := 2 - Real.sqrt 3 / 3
def c₂ : ℝ := 2 + Real.sqrt 3 / 3

theorem gap1 : ContinuousOn f (Set.Icc 1 2) := by
  unfold f
  fun_prop
theorem gap2 : ContinuousOn f (Set.Icc 2 3) := by
  unfold f
  fun_prop
theorem gap3 : DifferentiableOn ℝ f (Set.Ioo 1 2) := by
  unfold f
  fun_prop
theorem gap4 : DifferentiableOn ℝ f (Set.Ioo 2 3) := by
  unfold f
  fun_prop
theorem gap5 : f 1 = f 2 := by
  norm_num [f]
theorem gap6 : f 2 = 0 := by
  norm_num [f]
theorem gap7 : f 2 = f 3 := by
  norm_num [f]
theorem gap8 : f 3 = 0 := by
  norm_num [f]

theorem gap9 :
    ∃ u ∈ Set.Ioo (1 : ℝ) 2, ∃ v ∈ Set.Ioo (2 : ℝ) 3,
      deriv f u = 0 ∧ deriv f v = 0 := by
  obtain ⟨u, hu, hdu⟩ :=
    exists_deriv_eq_zero (f := f) (by norm_num : (1 : ℝ) < 2) gap1 gap5
  obtain ⟨v, hv, hdv⟩ :=
    exists_deriv_eq_zero (f := f) (by norm_num : (2 : ℝ) < 3) gap2 gap7
  exact ⟨u, hu, v, hv, hdu, hdv⟩

theorem gap10 (x : ℝ) :
    deriv f x =
      (x - 2) * (x - 3) + (x - 1) * (x - 3) + (x - 1) * (x - 2) := by
  have h1 := (hasDerivAt_id x).sub_const (1 : ℝ)
  have h2 := (hasDerivAt_id x).sub_const (2 : ℝ)
  have h3 := (hasDerivAt_id x).sub_const (3 : ℝ)
  unfold f
  convert ((h1.mul h2).mul h3).deriv using 1 <;>
    simp only [id_eq, Pi.mul_apply] <;> ring

theorem gap11 (x : ℝ) :
    (x - 2) * (x - 3) + (x - 1) * (x - 3) + (x - 1) * (x - 2) =
      3 * x ^ 2 - 12 * x + 11 := by
  ring

theorem gap12 (x : ℝ) :
    deriv f x = 3 * x ^ 2 - 12 * x + 11 := by
  rw [gap10, gap11]

theorem gap13 (x : ℝ) :
    x ∈ ({c₁, c₂} : Set ℝ) ↔ deriv f x = 0 := by
  rw [gap12]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro (rfl | rfl)
    · unfold c₁
      nlinarith
    · unfold c₂
      nlinarith
  · intro h
    have hp :
        (3 * x - 6 - Real.sqrt 3) * (3 * x - 6 + Real.sqrt 3) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hp with hleft | hright
    · right
      unfold c₂
      ring_nf
      linarith
    · left
      unfold c₁
      ring_nf
      linarith

theorem gap14 : 1 < c₁ := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg 3
  unfold c₁
  nlinarith
theorem gap15 : c₁ < 2 := by
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  unfold c₁
  linarith
theorem gap16 : 2 < c₂ := by
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  unfold c₂
  linarith
theorem gap17 : c₂ < 3 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg 3
  unfold c₂
  nlinarith
theorem gap18 : deriv f c₁ = 0 := by
  exact (gap13 c₁).mp (by simp)
theorem gap19 : deriv f c₂ = 0 := by
  exact (gap13 c₂).mp (by simp)

end

end ProofGap.Exercise1235
