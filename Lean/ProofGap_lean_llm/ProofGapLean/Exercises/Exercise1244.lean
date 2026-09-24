import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1244

noncomputable section

def y (x : ℝ) : ℝ := x ^ 3

def secantCondition (x₀ y₀ : ℝ) : Prop :=
  y₀ = x₀ ^ 3 ∧ deriv y x₀ = (8 - (-1 : ℝ)) / (2 - (-1 : ℝ))

theorem gap1 (x₀ : ℝ) :
    deriv y x₀ = 3 * x₀ ^ 2 := by
  have h :=
    ((hasDerivAt_id x₀).mul (hasDerivAt_id x₀)).mul (hasDerivAt_id x₀)
  have hy : y = (id * id * id : ℝ → ℝ) := by
    funext z
    change z ^ 3 = z * z * z
    ring
  rw [hy]
  calc
    deriv (id * id * id) x₀ =
        (1 * id x₀ + id x₀ * 1) * id x₀ + (id * id : ℝ → ℝ) x₀ * 1 := h.deriv
    _ = 3 * x₀ ^ 2 := by
      change (1 * x₀ + x₀ * 1) * x₀ + (x₀ * x₀) * 1 = 3 * x₀ ^ 2
      ring

theorem gap2 (x₀ y₀ : ℝ) :
    secantCondition x₀ y₀ ↔
      y₀ = x₀ ^ 3 ∧ 3 * x₀ ^ 2 = (8 - (-1 : ℝ)) / (2 - (-1 : ℝ)) := by
  simp only [secantCondition, gap1]

theorem gap3 :
    (8 - (-1 : ℝ)) / (2 - (-1 : ℝ)) = 3 := by
  norm_num

theorem gap4 (x₀ y₀ : ℝ) :
    secantCondition x₀ y₀ ↔ y₀ = x₀ ^ 3 ∧ 3 * x₀ ^ 2 = 3 := by
  simpa only [gap3] using (gap2 x₀ y₀)

theorem gap5 (x₀ y₀ : ℝ) :
    secantCondition x₀ y₀ ↔
      y₀ = x₀ ^ 3 ∧ (x₀ = -1 ∨ x₀ = 1) := by
  rw [gap4]
  constructor
  · rintro ⟨hy, hx⟩
    refine ⟨hy, ?_⟩
    have hfactor : (x₀ - 1) * (x₀ + 1) = 0 := by
      nlinarith [hx]
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro ⟨hy, hx⟩
    rcases hx with rfl | rfl
    · exact ⟨hy, by norm_num⟩
    · exact ⟨hy, by norm_num⟩

theorem gap6 (x₀ y₀ : ℝ) :
    secantCondition x₀ y₀ ↔
      (x₀ = -1 ∧ y₀ = -1) ∨ (x₀ = 1 ∧ y₀ = 1) := by
  rw [gap5]
  constructor
  · rintro ⟨hy, hx⟩
    rcases hx with hx | hx
    · subst x₀
      norm_num at hy
      exact Or.inl ⟨rfl, hy⟩
    · subst x₀
      norm_num at hy
      exact Or.inr ⟨rfl, hy⟩
  · rintro (h | h)
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num

theorem gap7 (x₀ y₀ : ℝ)
    (h : (x₀, y₀) ∈ ({((-1 : ℝ), (-1 : ℝ)), ((1 : ℝ), (1 : ℝ))} :
      Set (ℝ × ℝ))) :
    secantCondition x₀ y₀ := by
  apply (gap6 x₀ y₀).2
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] using h

end

end ProofGap.Exercise1244
