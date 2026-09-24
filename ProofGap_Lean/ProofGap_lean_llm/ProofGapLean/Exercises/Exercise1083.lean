import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1083

noncomputable section

def f (x : ℝ) : ℝ := x ^ 3 - 2 * x + 1
def increment (h : ℝ) : ℝ := f (1 + h) - f 1
def differential (h : ℝ) : ℝ := deriv f 1 * h

theorem gap1 (h : ℝ) :
    increment h = f (1 + h) - f 1 := by rfl

theorem gap2 (h : ℝ) :
    f (1 + h) - f 1 =
      (1 + h) ^ 3 - 2 * (1 + h) + 1 - (1 - 2 + 1) := by
  unfold f
  norm_num

theorem gap3 (h : ℝ) :
    (1 + h) ^ 3 - 2 * (1 + h) + 1 - (1 - 2 + 1) =
      h + 3 * h ^ 2 + h ^ 3 := by ring

theorem gap4 (h : ℝ) :
    increment h = h + 3 * h ^ 2 + h ^ 3 := by
  rw [gap1, gap2, gap3]

theorem gap5 (h : ℝ) :
    differential h = deriv f 1 * h := by rfl

theorem gap6 (h : ℝ) :
    deriv f 1 * h = (3 * (1 : ℝ) ^ 2 - 2) * h := by
  have hf : HasDerivAt f (3 * (1 : ℝ) ^ 2 - 2) 1 := by
    unfold f
    have hpow :
        HasDerivAt (fun x : ℝ => x ^ 3) (3 * (1 : ℝ) ^ 2) 1 := by
      convert (hasDerivAt_id (1 : ℝ)).pow 3 using 1 <;>
        simp only [id_eq] <;> ring
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).const_mul 2
    simpa only [Pi.sub_apply] using
      (HasDerivAt.sub hpow hlin).add_const 1
  rw [hf.deriv]

theorem gap7 (h : ℝ) :
    (3 * (1 : ℝ) ^ 2 - 2) * h = h := by ring

theorem gap8 (h : ℝ) : differential h = h := by
  rw [gap5, gap6, gap7]

theorem gap9 (h : ℝ) (hh : h = 1) : increment h = 5 := by
  subst h
  norm_num [gap4]

theorem gap10 (h : ℝ) (hh : h = 1) : differential h = 1 := by
  subst h
  exact gap8 1

theorem gap11 (h : ℝ) (hh : h = (1 / 10 : ℝ)) :
    increment h = (131 / 1000 : ℝ) := by
  subst h
  norm_num [gap4]

theorem gap12 (h : ℝ) (hh : h = (1 / 10 : ℝ)) :
    differential h = (1 / 10 : ℝ) := by
  subst h
  exact gap8 _

theorem gap13 (h : ℝ) (hh : h = (1 / 100 : ℝ)) :
    increment h = (10301 / 1000000 : ℝ) := by
  subst h
  norm_num [gap4]

theorem gap14 (h : ℝ) (hh : h = (1 / 100 : ℝ)) :
    differential h = (1 / 100 : ℝ) := by
  subst h
  exact gap8 _

theorem gap15 :
    |(10301 / 1000000 : ℝ) - 1 / 100| <
      |(131 / 1000 : ℝ) - 1 / 10| := by norm_num [abs_of_nonneg]

theorem gap16 :
    |(131 / 1000 : ℝ) - 1 / 10| < |(5 : ℝ) - 1| := by
  norm_num [abs_of_nonneg]

theorem gap17 :
    |(10301 / 1000000 : ℝ) - 1 / 100| < |(5 : ℝ) - 1| := by
  norm_num [abs_of_nonneg]

end

end ProofGap.Exercise1083
