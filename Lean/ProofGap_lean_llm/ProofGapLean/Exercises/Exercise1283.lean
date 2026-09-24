import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1283

noncomputable section

def f (x : ℝ) : ℝ := x + Real.sin x

theorem gap1 (x : ℝ) :
    deriv f x = 1 + Real.cos x := by
  have h : HasDerivAt f (1 + Real.cos x) x := by
    simpa [f] using (hasDerivAt_id x).add (Real.hasDerivAt_sin x)
  exact h.deriv

theorem gap2 (x : ℝ) :
    0 ≤ 1 + Real.cos x := by
  nlinarith [Real.neg_one_le_cos x]

theorem gap3 (x : ℝ) :
    0 ≤ deriv f x := by
  rw [gap1]
  exact gap2 x

theorem gap4 :
    MonotoneOn f (Set.Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  change a + Real.sin a ≤ b + Real.sin b
  have hsin : Real.sin a - Real.sin b ≤ b - a := by
    calc
      Real.sin a - Real.sin b ≤ |Real.sin a - Real.sin b| := le_abs_self _
      _ ≤ |a - b| := Real.abs_sin_sub_sin_le a b
      _ = b - a := by
        rw [abs_of_nonpos (sub_nonpos.mpr hab)]
        ring
  linarith

theorem gap5 :
    deriv f (Real.pi / 2) = 1 := by
  rw [gap1, Real.cos_pi_div_two]
  norm_num

theorem gap6 :
    deriv f Real.pi = 0 := by
  rw [gap1, Real.cos_pi]
  norm_num

theorem gap7 :
    deriv f (3 * Real.pi / 2) = 1 := by
  rw [gap1]
  have harg : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by
    ring
  rw [harg, Real.cos_add, Real.cos_pi, Real.cos_pi_div_two,
    Real.sin_pi, Real.sin_pi_div_two]
  norm_num

theorem gap8 :
    ¬MonotoneOn (deriv f) (Set.Ioi (0 : ℝ)) := by
  intro h
  have hx : Real.pi / 2 ∈ Set.Ioi (0 : ℝ) := by
    change 0 < Real.pi / 2
    nlinarith [Real.pi_pos]
  have hy : Real.pi ∈ Set.Ioi (0 : ℝ) := by
    exact Real.pi_pos
  have hxy : Real.pi / 2 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hbad : deriv f (Real.pi / 2) ≤ deriv f Real.pi := h hx hy hxy
  rw [gap5, gap6] at hbad
  norm_num at hbad

theorem gap9 :
    ¬AntitoneOn (deriv f) (Set.Ioi (0 : ℝ)) := by
  intro h
  have hx : Real.pi ∈ Set.Ioi (0 : ℝ) := by
    exact Real.pi_pos
  have hy : 3 * Real.pi / 2 ∈ Set.Ioi (0 : ℝ) := by
    change 0 < 3 * Real.pi / 2
    nlinarith [Real.pi_pos]
  have hxy : Real.pi ≤ 3 * Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hbad : deriv f (3 * Real.pi / 2) ≤ deriv f Real.pi := h hx hy hxy
  rw [gap7, gap6] at hbad
  norm_num at hbad

theorem gap10 (u : ℝ → ℝ) (hu : u ∈ ({f} : Set (ℝ → ℝ))) :
    MonotoneOn u (Set.Ioi (0 : ℝ)) ∧
      ¬MonotoneOn (deriv u) (Set.Ioi (0 : ℝ)) ∧
      ¬AntitoneOn (deriv u) (Set.Ioi (0 : ℝ)) := by
  have huf : u = f := by
    simpa using hu
  subst u
  exact ⟨gap4, gap8, gap9⟩

end

end ProofGap.Exercise1283
