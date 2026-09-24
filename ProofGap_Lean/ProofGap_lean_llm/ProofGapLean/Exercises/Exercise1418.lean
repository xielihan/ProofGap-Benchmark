import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ProofGap.Exercise1418

noncomputable section

def y (x : ℝ) := Real.cos x + Real.cosh x

theorem gap1 (x : ℝ) :
    deriv y x = -Real.sin x + Real.sinh x := by
  unfold y
  exact ((Real.hasDerivAt_cos x).add (Real.hasDerivAt_cosh x)).deriv
theorem gap2 (x : ℝ) (hcrit : deriv y x = 0) : x = 0 := by
  rw [gap1 x] at hcrit
  have heq : Real.sinh x = Real.sin x := by
    linarith
  by_contra hx
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hsinh : |x| < Real.sinh |x| :=
    (Real.self_lt_sinh_iff).2 hxabs
  have hsin : |Real.sin x| < |x| :=
    Real.abs_sin_lt_abs hx
  have habseq : |Real.sinh x| = |Real.sin x| :=
    congrArg abs heq
  rw [Real.abs_sinh] at habseq
  linarith
theorem gap3 (x : ℝ) :
    deriv (deriv y) x = -Real.cos x + Real.cosh x := by
  have hy' : deriv y = fun z : ℝ => -Real.sin z + Real.sinh z :=
    funext gap1
  rw [hy']
  exact ((Real.hasDerivAt_sin x).neg.add
    (Real.hasDerivAt_sinh x)).deriv
theorem gap4 : deriv (deriv y) 0 = 0 := by
  rw [gap3]
  norm_num
theorem gap5 (x : ℝ) :
    deriv (deriv (deriv y)) x = Real.sin x + Real.sinh x := by
  have hy'' : deriv (deriv y) =
      fun z : ℝ => -Real.cos z + Real.cosh z :=
    funext gap3
  rw [hy'']
  simpa using
    ((Real.hasDerivAt_cos x).neg.add
      (Real.hasDerivAt_cosh x)).deriv
theorem gap6 : deriv (deriv (deriv y)) 0 = 0 := by
  rw [gap5]
  norm_num
theorem gap7 (x : ℝ) :
    deriv (deriv (deriv (deriv y))) x =
      Real.cos x + Real.cosh x := by
  have hy''' : deriv (deriv (deriv y)) =
      fun z : ℝ => Real.sin z + Real.sinh z :=
    funext gap5
  rw [hy''']
  exact ((Real.hasDerivAt_sin x).add
    (Real.hasDerivAt_sinh x)).deriv
theorem gap8 : deriv (deriv (deriv (deriv y))) 0 = 2 := by
  rw [gap7]
  norm_num
theorem gap9 : (0 : ℝ) < 2 := by
  norm_num
theorem gap10 : IsMinOn y Set.univ 0 ∧ y 0 = 2 := by
  have hcont : Continuous y := by
    unfold y
    exact Real.continuous_cos.add Real.continuous_cosh
  have hderiv_neg {x : ℝ} (hx : x < 0) : deriv y x < 0 := by
    have hsinh : Real.sinh x < x :=
      (Real.sinh_lt_self_iff).2 hx
    have hsin : x ≤ Real.sin x := by
      calc
        x = -|x| := by rw [abs_of_neg hx]; ring
        _ ≤ -|Real.sin x| := neg_le_neg Real.abs_sin_le_abs
        _ ≤ Real.sin x := neg_abs_le _
    rw [gap1]
    linarith
  have hderiv_pos {x : ℝ} (hx : 0 < x) : 0 < deriv y x := by
    have hsinh : x < Real.sinh x :=
      (Real.self_lt_sinh_iff).2 hx
    have hsin : Real.sin x ≤ x := by
      calc
        Real.sin x ≤ |Real.sin x| := le_abs_self _
        _ ≤ |x| := Real.abs_sin_le_abs
        _ = x := abs_of_pos hx
    rw [gap1]
    linarith
  have hanti : StrictAntiOn y (Set.Iic 0) := by
    apply strictAntiOn_of_deriv_neg
      (convex_Iic (0 : ℝ)) hcont.continuousOn
    intro x hx
    rw [interior_Iic] at hx
    exact hderiv_neg hx
  have hmono : StrictMonoOn y (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos
      (convex_Ici (0 : ℝ)) hcont.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    exact hderiv_pos hx
  constructor
  · rw [isMinOn_iff]
    intro x _
    by_cases hx : x ≤ 0
    · exact hanti.antitoneOn hx
        (show (0 : ℝ) ∈ Set.Iic 0 by simp) hx
    · have hx0 : 0 ≤ x := le_of_lt (lt_of_not_ge hx)
      exact hmono.monotoneOn
        (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx0 hx0
  · norm_num [y]

end
end ProofGap.Exercise1418
