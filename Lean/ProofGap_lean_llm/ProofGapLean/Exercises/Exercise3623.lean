import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3623

noncomputable section

def z (p : ℝ × ℝ) : ℝ :=
  (p.1 - p.2 + 1) ^ 2

def partialX (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => g (x, p.2)) p.1

def partialY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => g (p.1, y)) p.2

def zeroLine : Set (ℝ × ℝ) :=
  {p | p.1 - p.2 + 1 = 0}

def minimumPoints : Set (ℝ × ℝ) :=
  {p | ∀ q, z p ≤ z q}

theorem gap1 :
    ∀ p : ℝ × ℝ, p ∈ zeroLine →
      partialX z p = 2 * (p.1 - p.2 + 1) ∧
      2 * (p.1 - p.2 + 1) = 0 ∧
      partialY z p = -2 * (p.1 - p.2 + 1) ∧
      -2 * (p.1 - p.2 + 1) = 0 := by
  intro p hp
  change p.1 - p.2 + 1 = 0 at hp
  have hbaseX :
      HasDerivAt (fun x : ℝ => x - p.2 + 1) 1 p.1 := by
    simpa using (((hasDerivAt_id p.1).sub_const p.2).add_const 1)
  have hx :
      HasDerivAt (fun x : ℝ => (x - p.2 + 1) ^ 2)
        (2 * (p.1 - p.2 + 1)) p.1 := by
    have hcoefX :
        (1 : ℝ) * (p.1 - p.2 + 1) + (p.1 - p.2 + 1) * 1 =
          2 * (p.1 - p.2 + 1) := by
      ring
    rw [← hcoefX]
    simpa only [pow_two] using hbaseX.mul hbaseX
  have hbaseY :
      HasDerivAt (fun y : ℝ => p.1 - y + 1) (-1) p.2 := by
    simpa using
      (((hasDerivAt_const p.2 p.1).sub (hasDerivAt_id p.2)).add_const 1)
  have hy :
      HasDerivAt (fun y : ℝ => (p.1 - y + 1) ^ 2)
        (-2 * (p.1 - p.2 + 1)) p.2 := by
    have hcoefY :
        (-1 : ℝ) * (p.1 - p.2 + 1) +
            (p.1 - p.2 + 1) * (-1) =
          -2 * (p.1 - p.2 + 1) := by
      ring
    rw [← hcoefY]
    simpa only [pow_two] using hbaseY.mul hbaseY
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold partialX
    change deriv (fun x : ℝ => (x - p.2 + 1) ^ 2) p.1 = _
    exact hx.deriv
  · simp [hp]
  · unfold partialY
    change deriv (fun y : ℝ => (p.1 - y + 1) ^ 2) p.2 = _
    exact hy.deriv
  · simp [hp]

theorem gap2 :
    ∃ p : ℝ × ℝ, p ∈ zeroLine ∧ z p = 0 := by
  refine ⟨((0 : ℝ), (1 : ℝ)), ?_, ?_⟩
  · change (0 : ℝ) - 1 + 1 = 0
    ring
  · change ((0 : ℝ) - 1 + 1) ^ 2 = 0
    ring

theorem gap3 :
    ∀ p : ℝ × ℝ, 0 ≤ z p := by
  intro p
  unfold z
  exact sq_nonneg (p.1 - p.2 + 1)

theorem gap4 :
    minimumPoints = zeroLine := by
  apply Set.ext
  intro p
  constructor
  · intro hp
    change ∀ q, z p ≤ z q at hp
    obtain ⟨q, _, hq⟩ := gap2
    have hle : z p ≤ 0 := by
      simpa [hq] using hp q
    have hz : z p = 0 := le_antisymm hle (gap3 p)
    change p.1 - p.2 + 1 = 0
    have hsq :
        (p.1 - p.2 + 1) * (p.1 - p.2 + 1) = 0 := by
      simpa [z, pow_two] using hz
    rcases mul_eq_zero.mp hsq with h | h
    · exact h
    · exact h
  · intro hp
    change p.1 - p.2 + 1 = 0 at hp
    change ∀ q, z p ≤ z q
    intro q
    simpa [z, hp] using gap3 q

theorem gap5 :
    ∃ p : ℝ × ℝ, p ∈ minimumPoints ∧ z p = 0 := by
  obtain ⟨p, hp, hz⟩ := gap2
  refine ⟨p, ?_, hz⟩
  rw [gap4]
  exact hp

end

end ProofGap.Exercise3623
