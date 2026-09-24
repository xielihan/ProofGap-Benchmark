import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise760

noncomputable section

def floorShift (x : ℝ) : ℝ := x + (Int.floor x : ℝ)

theorem gap1 (x : ℝ) :
    ∃ y, ∀ k : ℤ, (k : ℝ) ≤ x → x < k + 1 → 2 * (k : ℝ) ≤ y := by
  refine ⟨2 * x, ?_⟩
  intro k hk hk'
  linarith
theorem gap2 (x : ℝ) :
    ∃ y, ∀ k : ℤ, (k : ℝ) ≤ x → x < k + 1 → y < 2 * (k : ℝ) + 1 := by
  refine ⟨2 * x - 1, ?_⟩
  intro k hk hk'
  linarith
theorem gap3 (x : ℝ) (k : ℤ) (hk : (k : ℝ) ≤ x) (hk' : x < k + 1) :
    2 * (k : ℝ) < 2 * k + 1 := by
  linarith
theorem gap4 (x : ℝ) (k : ℤ) (hk : (k : ℝ) ≤ x) (hk' : x < k + 1) :
    Int.floor x = k := by
  rw [Int.floor_eq_iff]
  exact ⟨hk, hk'⟩
theorem gap5 (x : ℝ) :
    ∃ y, ∀ k : ℤ, (k : ℝ) ≤ x → x < k + 1 → y = x + k := by
  refine ⟨floorShift x, ?_⟩
  intro k hk hk'
  simpa [floorShift, gap4 x k hk hk']
theorem gap6 (x : ℝ) :
    ∃ y, ∀ k : ℤ, (k : ℝ) ≤ x → x < k + 1 → x = y - k := by
  refine ⟨floorShift x, ?_⟩
  intro k hk hk'
  simp [floorShift, gap4 x k hk hk']
theorem gap7 :
    Function.LeftInverse
      (fun y : ℝ => y - (Int.floor ((y + 1) / 2) : ℝ)) floorShift := by
  intro x
  dsimp [floorShift]
  have hfloor :
      Int.floor ((x + (Int.floor x : ℝ) + 1) / 2) = Int.floor x := by
    apply gap4
    · have hle : (Int.floor x : ℝ) ≤ x := Int.floor_le x
      linarith
    · have hlt : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
      linarith
  rw [hfloor]
  simp

end
end ProofGap.Exercise760
