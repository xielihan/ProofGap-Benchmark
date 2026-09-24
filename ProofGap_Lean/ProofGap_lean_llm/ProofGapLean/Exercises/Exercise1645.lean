import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1645

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.rpow 2 (x + 1) - Real.rpow 5 (x - 1)) / Real.rpow 10 x
def simple (x : ℝ) : ℝ :=
  2 * Real.rpow (1 / 5) x - (1 / 5) * Real.rpow (1 / 2) x
def primitive (x : ℝ) : ℝ :=
  -(2 / Real.log 5) * Real.rpow (1 / 5) x +
    (1 / (5 * Real.log 2)) * Real.rpow (1 / 2) x
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem explicit_rpow_def_of_pos
    (a y : ℝ) (ha : 0 < a) :
    Real.rpow a y = Real.exp (Real.log a * y) := by
  change a ^ y = Real.exp (Real.log a * y)
  exact Real.rpow_def_of_pos ha y

private theorem original_eq_simple (x : ℝ) : original x = simple x := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h5 : (0 : ℝ) < 5 := by norm_num
  have h10 : (0 : ℝ) < 10 := by norm_num
  have h15 : (0 : ℝ) < 1 / 5 := by norm_num
  have h12 : (0 : ℝ) < 1 / 2 := by norm_num
  have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (5 : ℝ) ≠ 0)]
  have hlog15 : Real.log (1 / 5) = -Real.log 5 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (5 : ℝ) ≠ 0)]
    norm_num
  have hlog12 : Real.log (1 / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have h25 : Real.rpow 2 x / Real.rpow 10 x = Real.rpow (1 / 5) x := by
    rw [explicit_rpow_def_of_pos 2 x h2,
      explicit_rpow_def_of_pos 10 x h10,
      explicit_rpow_def_of_pos (1 / 5) x h15]
    calc
      Real.exp (Real.log 2 * x) / Real.exp (Real.log 10 * x) =
          Real.exp (Real.log 2 * x - Real.log 10 * x) :=
        (Real.exp_sub _ _).symm
      _ = Real.exp (Real.log (1 / 5) * x) := by
        rw [hlog10, hlog15]
        congr 1
        ring
  have h510 : Real.rpow 5 x / Real.rpow 10 x = Real.rpow (1 / 2) x := by
    rw [explicit_rpow_def_of_pos 5 x h5,
      explicit_rpow_def_of_pos 10 x h10,
      explicit_rpow_def_of_pos (1 / 2) x h12]
    calc
      Real.exp (Real.log 5 * x) / Real.exp (Real.log 10 * x) =
          Real.exp (Real.log 5 * x - Real.log 10 * x) :=
        (Real.exp_sub _ _).symm
      _ = Real.exp (Real.log (1 / 2) * x) := by
        rw [hlog10, hlog12]
        congr 1
        ring
  have hp2 : Real.rpow 2 (x + 1) = Real.rpow 2 x * 2 := by
    rw [explicit_rpow_def_of_pos 2 (x + 1) h2,
      explicit_rpow_def_of_pos 2 x h2]
    calc
      Real.exp (Real.log 2 * (x + 1)) =
          Real.exp (Real.log 2 * x + Real.log 2) := by
        congr 1
        ring
      _ = Real.exp (Real.log 2 * x) * Real.exp (Real.log 2) :=
        Real.exp_add _ _
      _ = Real.exp (Real.log 2 * x) * 2 := by rw [Real.exp_log h2]
  have hp5 : Real.rpow 5 (x - 1) = Real.rpow 5 x / 5 := by
    rw [explicit_rpow_def_of_pos 5 (x - 1) h5,
      explicit_rpow_def_of_pos 5 x h5]
    calc
      Real.exp (Real.log 5 * (x - 1)) =
          Real.exp (Real.log 5 * x - Real.log 5) := by
        congr 1
        ring
      _ = Real.exp (Real.log 5 * x) / Real.exp (Real.log 5) :=
        Real.exp_sub _ _
      _ = Real.exp (Real.log 5 * x) / 5 := by rw [Real.exp_log h5]
  unfold original simple
  rw [sub_div, hp2, hp5]
  calc
    Real.rpow 2 x * 2 / Real.rpow 10 x -
        (Real.rpow 5 x / 5) / Real.rpow 10 x =
        2 * (Real.rpow 2 x / Real.rpow 10 x) -
          (1 / 5) * (Real.rpow 5 x / Real.rpow 10 x) := by ring
    _ = 2 * Real.rpow (1 / 5) x -
        (1 / 5) * Real.rpow (1 / 2) x := by rw [h25, h510]

private theorem hasDerivAt_positive_const_rpow
    (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (fun y : ℝ => Real.rpow a y)
      (Real.log a * Real.rpow a x) x := by
  have hlin : HasDerivAt (fun y : ℝ => y * Real.log a) (Real.log a) x := by
    simpa using (hasDerivAt_id x).mul_const (Real.log a)
  have hfun : (fun y : ℝ => Real.rpow a y) =
      (fun y : ℝ => Real.exp (y * Real.log a)) := by
    funext y
    simpa [mul_comm] using explicit_rpow_def_of_pos a y ha
  have hx : Real.rpow a x = Real.exp (x * Real.log a) := by
    simpa [mul_comm] using explicit_rpow_def_of_pos a x ha
  simpa only [hfun, hx, Function.comp_def, mul_comm] using
    (Real.hasDerivAt_exp (x * Real.log a)).comp x hlin

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (simple x) x := by
  have hlog5 : Real.log 5 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 5))
  have hlog2 : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hl5 : Real.log (1 / 5) = -Real.log 5 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (5 : ℝ) ≠ 0)]
    norm_num
  have hl2 : Real.log (1 / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hd :
      -(2 / Real.log 5) *
          (Real.log (1 / 5) * Real.rpow (1 / 5) x) +
        (1 / (5 * Real.log 2)) *
          (Real.log (1 / 2) * Real.rpow (1 / 2) x) = simple x := by
    unfold simple
    rw [hl5, hl2]
    field_simp [hlog5, hlog2]
    all_goals ring
  have h1 :=
    (hasDerivAt_positive_const_rpow (1 / 5) x
      (by norm_num : (0 : ℝ) < 1 / 5)).const_mul
        (-(2 / Real.log 5))
  have h2 :=
    (hasDerivAt_positive_const_rpow (1 / 2) x
      (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
        (1 / (5 * Real.log 2))
  unfold primitive
  rw [← hd]
  exact h1.add h2

theorem gap1 : Antiderivatives original = Antiderivatives simple := by
  rw [show original = simple from funext original_eq_simple]

theorem gap2 : Antiderivatives simple = PrimitiveFamily primitive := by
  ext F
  simp only [Antiderivatives, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      have hFx : HasDerivAt F (simple x) x := by
        rw [← hFderiv x]
        exact hFdiff.differentiableAt.hasDerivAt
      simpa using hFx.sub (primitive_hasDerivAt x)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hx : (fun y => F y - primitive y) x =
        (fun y => F y - primitive y) 0 :=
      is_const_of_deriv_eq_zero
        (fun y => (hzero y).differentiableAt)
        (fun y => (hzero y).deriv) x 0
    linarith
  · rintro ⟨C, hC⟩
    have hFEq : F = fun x => primitive x + C := funext hC
    rw [hFEq]
    constructor
    · exact fun x => ((primitive_hasDerivAt x).add_const C).differentiableAt
    · exact fun x => ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1645
