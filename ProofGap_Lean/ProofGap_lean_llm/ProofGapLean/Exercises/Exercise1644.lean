import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1644

noncomputable section

def original (x : ℝ) : ℝ := (Real.rpow 2 x + Real.rpow 3 x) ^ 2
def expanded (x : ℝ) : ℝ :=
  Real.rpow 4 x + 2 * Real.rpow 6 x + Real.rpow 9 x
def primitive (x : ℝ) : ℝ :=
  Real.rpow 4 x / Real.log 4 +
    2 * (Real.rpow 6 x / Real.log 6) +
    Real.rpow 9 x / Real.log 9
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem hasDerivAt_rpow_div_log
    (a x : ℝ) (ha : 0 < a) (hlog : Real.log a ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.rpow a y / Real.log a) (Real.rpow a x) x := by
  have hinner : HasDerivAt (fun y : ℝ => Real.log a * y) (Real.log a) x := by
    simpa using (hasDerivAt_id x).const_mul (Real.log a)
  have hexp :=
    (Real.hasDerivAt_exp (Real.log a * x)).comp x hinner
  have hdiv := hexp.div_const (Real.log a)
  simpa [Real.rpow_def_of_pos ha, hlog] using hdiv

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (expanded x) x := by
  have h4 := hasDerivAt_rpow_div_log (4 : ℝ) x (by norm_num)
    (ne_of_gt (Real.log_pos (by norm_num)))
  have h6 := hasDerivAt_rpow_div_log (6 : ℝ) x (by norm_num)
    (ne_of_gt (Real.log_pos (by norm_num)))
  have h9 := hasDerivAt_rpow_div_log (9 : ℝ) x (by norm_num)
    (ne_of_gt (Real.log_pos (by norm_num)))
  simpa only [primitive, expanded] using
    (h4.add (h6.const_mul 2)).add h9

theorem gap1 : Antiderivatives original = Antiderivatives expanded := by
  have hfun : original = expanded := by
    funext x
    have h4 : Real.rpow 4 x = Real.rpow 2 x * Real.rpow 2 x := by
      calc
        Real.rpow 4 x = Real.rpow ((2 : ℝ) * 2) x := by norm_num
        _ = Real.rpow 2 x * Real.rpow 2 x :=
          Real.mul_rpow (by norm_num) (by norm_num)
    have h6 : Real.rpow 6 x = Real.rpow 2 x * Real.rpow 3 x := by
      calc
        Real.rpow 6 x = Real.rpow ((2 : ℝ) * 3) x := by norm_num
        _ = Real.rpow 2 x * Real.rpow 3 x :=
          Real.mul_rpow (by norm_num) (by norm_num)
    have h9 : Real.rpow 9 x = Real.rpow 3 x * Real.rpow 3 x := by
      calc
        Real.rpow 9 x = Real.rpow ((3 : ℝ) * 3) x := by norm_num
        _ = Real.rpow 3 x * Real.rpow 3 x :=
          Real.mul_rpow (by norm_num) (by norm_num)
    unfold original expanded
    rw [h4, h6, h9]
    ring
  rw [hfun]

theorem gap2 : Antiderivatives expanded = PrimitiveFamily primitive := by
  ext F
  change (Differentiable ℝ F ∧ ∀ x, deriv F x = expanded x) ↔
    ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      convert (hFdiff x).hasDerivAt.sub (hasDerivAt_primitive x) using 1
      simp [hFderiv x]
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hconst :=
      is_const_of_deriv_eq_zero hdiff (fun y => (hzero y).deriv)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [hconst x 0]
  · rintro ⟨C, hF⟩
    have hFeq : F = fun x => primitive x + C := funext hF
    rw [hFeq]
    constructor
    · exact fun x => ((hasDerivAt_primitive x).add_const C).differentiableAt
    · intro x
      exact ((hasDerivAt_primitive x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  calc
    Antiderivatives original = Antiderivatives expanded := gap1
    _ = PrimitiveFamily primitive := gap2

end
end ProofGap.Exercise1644
