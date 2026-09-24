import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise824

def diff (f : ℝ → ℝ) (h x : ℝ) : ℝ := f (x + h) - f x

theorem gap1 (f g : ℝ → ℝ) (x h : ℝ) :
    diff (fun z => f z + g z) h x = f (x + h) + g (x + h) - (f x + g x) := by
  rfl
theorem gap2 (f g : ℝ → ℝ) (x h : ℝ) :
    diff (fun z => f z + g z) h x =
      f (x + h) - f x + (g (x + h) - g x) := by
  unfold diff
  ring
theorem gap3 (f g : ℝ → ℝ) (x h : ℝ) :
    f (x + h) - f x + (g (x + h) - g x) = diff f h x + diff g h x := by
  unfold diff
  ring
theorem gap4 (f g : ℝ → ℝ) (x h : ℝ) :
    diff (fun z => f z + g z) h x = diff f h x + diff g h x := by
  calc
    diff (fun z => f z + g z) h x =
        f (x + h) - f x + (g (x + h) - g x) := gap2 f g x h
    _ = diff f h x + diff g h x := gap3 f g x h
theorem gap5 (f g : ℝ → ℝ) (x h : ℝ) :
    diff (fun z => f z + g z) h x = diff f h x + diff g h x := by
  exact gap4 f g x h
theorem gap6 (f g : ℝ → ℝ) (x h : ℝ) :
    diff (fun z => f z * g z) h x = f (x + h) * g (x + h) - f x * g x := by
  rfl
theorem gap7 (f g : ℝ → ℝ) (x h : ℝ) :
    diff (fun z => f z * g z) h x =
      (f (x + h) - f x) * g (x + h) + (g (x + h) - g x) * f x := by
  unfold diff
  ring
theorem gap8 (f g : ℝ → ℝ) (x h : ℝ) :
    diff (fun z => f z * g z) h x = diff f h x * g (x + h) + diff g h x * f x := by
  simpa [diff] using (gap7 f g x h)
theorem gap9 (f g : ℝ → ℝ) (x h : ℝ) :
    diff (fun z => f z * g z) h x = g (x + h) * diff f h x + f x * diff g h x := by
  calc
    diff (fun z => f z * g z) h x =
        diff f h x * g (x + h) + diff g h x * f x := gap8 f g x h
    _ = g (x + h) * diff f h x + f x * diff g h x := by ring
theorem gap10 (f g : ℝ → ℝ) (x h : ℝ) :
    diff (fun z => f z * g z) h x = f (x + h) * diff g h x + g x * diff f h x := by
  unfold diff
  ring
theorem gap11 (f g : ℝ → ℝ) (x h : ℝ) :
    diff (fun z => f z + g z) h x = diff f h x + diff g h x ∧
    diff (fun z => f z * g z) h x = g (x + h) * diff f h x + f x * diff g h x := by
  exact ⟨gap4 f g x h, gap9 f g x h⟩

end ProofGap.Exercise824
