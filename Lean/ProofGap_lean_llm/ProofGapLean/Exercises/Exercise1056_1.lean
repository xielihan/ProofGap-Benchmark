import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1056_1

def y (x : ℝ) : ℝ := 2 + x - x ^ 2

theorem gap1 (x : ℝ) :
    deriv y x = 1 - 2 * x := by
  have hconst : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 x :=
    hasDerivAt_const x 2
  have hid : HasDerivAt (fun t : ℝ => t) 1 x :=
    hasDerivAt_id x
  have hderiv :
      deriv (fun t : ℝ => 2 + t - t * t) x =
        (0 + 1) - (1 * x + x * 1) :=
    ((hconst.add hid).sub (hid.mul hid)).deriv
  have hfun :
      (fun t : ℝ => 2 + t - t ^ 2) =
        (fun t : ℝ => 2 + t - t * t) := by
    funext t
    rw [pow_two]
  change deriv (fun t : ℝ => 2 + t - t ^ 2) x = 1 - 2 * x
  rw [hfun, hderiv]
  ring

theorem gap2 (x : ℝ) :
    deriv y x = 0 ↔ x = 1 / 2 := by
  rw [gap1]
  constructor
  · intro h
    linarith
  · rintro rfl
    norm_num

theorem gap3 (x : ℝ) :
    x ∈ ({(1 / 2 : ℝ)} : Set ℝ) ↔ deriv y x = 0 := by
  simpa only [Set.mem_singleton_iff] using (gap2 x).symm

theorem gap4 (x : ℝ) (hx : x = 1 / 2) :
    y x = 2 + (1 / 2 : ℝ) - 1 / 4 := by
  subst x
  norm_num [y]

theorem gap5 :
    (2 + (1 / 2 : ℝ) - 1 / 4) = 9 / 4 := by
  norm_num

theorem gap6 (x : ℝ) :
    deriv y x = 0 ↔ (x, y x) = ((1 / 2 : ℝ), (9 / 4 : ℝ)) := by
  rw [gap2]
  constructor
  · intro hx
    apply Prod.ext
    · exact hx
    · exact (gap4 x hx).trans gap5
  · intro h
    simpa using congrArg Prod.fst h

theorem gap7 (x : ℝ)
    (hx : (x, y x) ∈ ({((1 / 2 : ℝ), (9 / 4 : ℝ))} : Set (ℝ × ℝ))) :
    y x = 2 + x - x ^ 2 ∧ deriv y x = 0 := by
  have hp : (x, y x) = ((1 / 2 : ℝ), (9 / 4 : ℝ)) := by
    simpa only [Set.mem_singleton_iff] using hx
  exact ⟨rfl, (gap6 x).2 hp⟩

end ProofGap.Exercise1056_1
