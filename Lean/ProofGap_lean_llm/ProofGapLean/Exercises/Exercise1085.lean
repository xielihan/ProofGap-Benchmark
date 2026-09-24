import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1085

noncomputable section

def y (x : ℝ) : ℝ := 1 / x
def increment (h : ℝ) : ℝ := y (1 + h) - y 1
def differentialAt (x dx : ℝ) : ℝ := deriv y x * dx

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (-(1 / x ^ 2)) x := by
  have hy : y = (id⁻¹ : ℝ → ℝ) := by
    funext z
    change 1 / z = z⁻¹
    simp [one_div]
  rw [hy]
  simpa [one_div, div_eq_mul_inv] using (hasDerivAt_id x).inv hx

theorem gap2 (x dx : ℝ) (hx : x ≠ 0) :
    differentialAt x dx = -(1 / x ^ 2) * dx := by
  unfold differentialAt
  rw [(gap1 x hx).deriv]

theorem gap3 (h : ℝ) :
    increment h = y (1 + h) - y 1 := by
  rfl

theorem gap4 (h : ℝ) (hh : 1 + h ≠ 0) :
    y (1 + h) - y 1 = 1 / (1 + h) - 1 := by
  simp [y]

theorem gap5 (h : ℝ) (hh : 1 + h ≠ 0) :
    1 / (1 + h) - 1 = -(h / (1 + h)) := by
  field_simp [hh] <;> ring

theorem gap6 (h : ℝ) (hh : 1 + h ≠ 0) :
    increment h = -(h / (1 + h)) := by
  calc
    increment h = y (1 + h) - y 1 := gap3 h
    _ = 1 / (1 + h) - 1 := gap4 h hh
    _ = -(h / (1 + h)) := gap5 h hh

theorem gap7 (h : ℝ) :
    differentialAt 1 h = deriv y 1 * h := by
  rfl

theorem gap8 (h : ℝ) :
    deriv y 1 * h = -h := by
  rw [(gap1 (1 : ℝ) (by norm_num)).deriv]
  ring

theorem gap9 (h : ℝ) :
    differentialAt 1 h = -h := by
  calc
    differentialAt 1 h = deriv y 1 * h := gap7 h
    _ = -h := gap8 h

theorem gap10 (h : ℝ) (hh : h = 1) :
    increment h = -(1 / 2 : ℝ) := by
  subst h
  calc
    increment (1 : ℝ) = -((1 : ℝ) / (1 + 1)) :=
      gap6 (1 : ℝ) (by norm_num)
    _ = -(1 / 2 : ℝ) := by norm_num

theorem gap11 (h : ℝ) (hh : h = 1) :
    differentialAt 1 h = -1 := by
  subst h
  simpa using (gap9 (1 : ℝ))

theorem gap12 (h : ℝ) (hh : h = (1 / 10 : ℝ)) :
    increment h = -(1 / 11 : ℝ) := by
  subst h
  calc
    increment (1 / 10 : ℝ) =
        -((1 / 10 : ℝ) / (1 + (1 / 10 : ℝ))) :=
      gap6 (1 / 10 : ℝ) (by norm_num)
    _ = -(1 / 11 : ℝ) := by norm_num

theorem gap13 (h : ℝ) (hh : h = (1 / 10 : ℝ)) :
    differentialAt 1 h = -(1 / 10 : ℝ) := by
  subst h
  simpa using (gap9 (1 / 10 : ℝ))

theorem gap14 (h : ℝ) (hh : h = (1 / 100 : ℝ)) :
    increment h = -(1 / 101 : ℝ) := by
  subst h
  calc
    increment (1 / 100 : ℝ) =
        -((1 / 100 : ℝ) / (1 + (1 / 100 : ℝ))) :=
      gap6 (1 / 100 : ℝ) (by norm_num)
    _ = -(1 / 101 : ℝ) := by norm_num

theorem gap15 (h : ℝ) (hh : h = (1 / 100 : ℝ)) :
    differentialAt 1 h = -(1 / 100 : ℝ) := by
  subst h
  simpa using (gap9 (1 / 100 : ℝ))

theorem gap16 :
    |(-(9901 / 1000000 : ℝ)) - (-(1 / 100 : ℝ))| <
      |(-(909 / 10000 : ℝ)) - (-(1 / 10 : ℝ))| := by
  norm_num [abs_of_nonneg]

theorem gap17 :
    |(-(909 / 10000 : ℝ)) - (-(1 / 10 : ℝ))| <
      |(-(1 / 2 : ℝ)) - (-1 : ℝ)| := by
  norm_num [abs_of_nonneg]

theorem gap18 :
    |(-(9901 / 1000000 : ℝ)) - (-(1 / 100 : ℝ))| <
      |(-(1 / 2 : ℝ)) - (-1 : ℝ)| := by
  norm_num [abs_of_nonneg]

end

end ProofGap.Exercise1085
