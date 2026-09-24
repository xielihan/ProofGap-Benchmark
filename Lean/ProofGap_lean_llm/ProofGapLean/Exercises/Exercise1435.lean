import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1435

noncomputable section

def y (x : ℝ) : ℝ := Real.sqrt (2 * x - x ^ 2)
def domain : Set ℝ := Set.Icc 0 2

theorem gap1 (x : ℝ) (h₁ : 0 < x) (h₂ : x < 2) :
    deriv y x = (1 - x) / Real.sqrt (2 * x - x ^ 2) := by
  have hprod : 0 < x * (2 - x) :=
    mul_pos h₁ (sub_pos.mpr h₂)
  have hq : 0 < 2 * x - x ^ 2 := by
    nlinarith
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    simpa using
      (HasDerivAt.mul (hasDerivAt_const x (2 : ℝ)) (hasDerivAt_id x))
  have hpow : HasDerivAt ((id : ℝ → ℝ) ^ 2) (2 * x) x := by
    simpa using HasDerivAt.pow (hasDerivAt_id x) 2
  have hfunpow :
      ((id : ℝ → ℝ) ^ 2) = (fun t : ℝ => t ^ 2) := by
    funext t
    rfl
  rw [hfunpow] at hpow
  have hg₀ :
      HasDerivAt
        ((fun t : ℝ => 2 * t) - (fun t : ℝ => t ^ 2))
        (2 - 2 * x) x :=
    HasDerivAt.sub hlin hpow
  have hfunsub :
      ((fun t : ℝ => 2 * t) - (fun t : ℝ => t ^ 2)) =
        (fun t : ℝ => 2 * t - t ^ 2) := by
    funext t
    rfl
  rw [hfunsub] at hg₀
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hg₀
  have hfun :
      (Real.sqrt ∘ (fun t : ℝ => 2 * t - t ^ 2)) = y := by
    funext t
    rfl
  rw [← hfun, hs.deriv]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hq)] <;> ring

theorem gap2 : deriv y 1 = 0 := by
  rw [gap1 1 (by norm_num) (by norm_num)]
  norm_num

theorem gap3 (x : ℝ) (h₁ : 0 < x) (h₂ : x < 1) :
    0 < deriv y x := by
  have hx2 : x < 2 := by
    nlinarith
  have hprod : 0 < x * (2 - x) :=
    mul_pos h₁ (sub_pos.mpr hx2)
  have hq : 0 < 2 * x - x ^ 2 := by
    nlinarith
  rw [gap1 x h₁ hx2]
  exact div_pos (sub_pos.mpr h₂) (Real.sqrt_pos.2 hq)

theorem gap4 (x : ℝ) (h₁ : 1 < x) (h₂ : x < 2) :
    deriv y x < 0 := by
  have hx0 : 0 < x := by
    nlinarith
  have hprod : 0 < x * (2 - x) :=
    mul_pos hx0 (sub_pos.mpr h₂)
  have hq : 0 < 2 * x - x ^ 2 := by
    nlinarith
  rw [gap1 x hx0 h₂]
  exact div_neg_of_neg_of_pos (sub_neg.mpr h₁) (Real.sqrt_pos.2 hq)

theorem gap5 : IsMaxOn y domain 1 := by
  intro x hx
  rcases hx with ⟨hx0, hx2⟩
  have hprod : 0 ≤ x * (2 - x) :=
    mul_nonneg hx0 (sub_nonneg.mpr hx2)
  have hq : 0 ≤ 2 * x - x ^ 2 := by
    nlinarith
  have hs : (Real.sqrt (2 * x - x ^ 2)) ^ 2 = 2 * x - x ^ 2 :=
    Real.sq_sqrt hq
  change Real.sqrt (2 * x - x ^ 2) ≤ Real.sqrt (2 * 1 - 1 ^ 2)
  norm_num
  nlinarith [sq_nonneg (x - 1)]

theorem gap6 : y 1 = 1 := by
  norm_num [y]

theorem gap7 (x : ℝ) : 0 ≤ y x := by
  exact Real.sqrt_nonneg (2 * x - x ^ 2)

theorem gap8 : IsMinOn y domain 0 ∧ IsMinOn y domain 2 := by
  constructor
  · intro x _
    simpa [y] using gap7 x
  · intro x _
    have hy2 : y 2 = 0 := by
      norm_num [y]
    rw [hy2]
    exact gap7 x

theorem gap9 : y 0 = 0 := by
  norm_num [y]

theorem gap10 : y 2 = 0 := by
  norm_num [y]

end
end ProofGap.Exercise1435
