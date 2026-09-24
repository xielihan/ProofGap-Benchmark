import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace ProofGap.Exercise3244_3

noncomputable section

def f (x y : ℝ) : ℝ :=
  Real.arctan ((x + y) / (1 + x * y))

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g t y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g x t) y

def linearTaylorFromPartials (x y : ℝ) : ℝ :=
  f 0 0 + partialX f 0 0 * x + partialY f 0 0 * y

def linearTaylor (x y : ℝ) : ℝ := x + y

def AgreesToFirstOrder (g p : ℝ × ℝ → ℝ) : Prop :=
  Asymptotics.IsLittleO (nhds (0, 0))
    (fun q => g q - p q)
    (fun q => ‖q‖)

private def linearPart3244 : (ℝ × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ

private lemma f_hasFDerivAt_zero3244 :
    HasFDerivAt
      (fun q : ℝ × ℝ => f q.1 q.2)
      linearPart3244 (0, 0) := by
  have hinner :
      HasFDerivAt
        (fun q : ℝ × ℝ => (q.1 + q.2) / (1 + q.1 * q.2))
        linearPart3244 (0, 0) := by
    have hx :
        HasFDerivAt (fun q : ℝ × ℝ => q.1)
          (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 0) :=
      hasFDerivAt_fst
    have hy :
        HasFDerivAt (fun q : ℝ × ℝ => q.2)
          (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) :=
      hasFDerivAt_snd
    have hnum := hx.add hy
    have hden := (hasFDerivAt_const (x := (0, 0)) (1 : ℝ)).add (hx.mul hy)
    have hden_ne :
        (((fun _ : ℝ × ℝ => (1 : ℝ)) +
          (fun q : ℝ × ℝ => q.1) * (fun q : ℝ × ℝ => q.2)) (0, 0)) ≠ 0 := by
      norm_num
    have hinv :=
      (hasFDerivAt_inv' (𝕜 := ℝ) (R := ℝ) hden_ne).comp (0, 0) hden
    have hquot := hnum.mul hinv
    simp only [div_eq_mul_inv]
    convert hquot using 1 <;>
      ext q <;> simp [linearPart3244]
  unfold f
  convert hinner.arctan using 1 <;> simp [linearPart3244]

theorem gap1 (x : ℝ) :
    partialX f x 0 = 1 / (1 + x ^ 2) := by
  rw [partialX]
  have hfun : (fun t : ℝ => f t 0) = Real.arctan := by
    funext t
    simp [f]
  rw [hfun]
  exact Real.hasDerivAt_arctan x |>.deriv

theorem gap2 :
    partialX f 0 0 = 1 := by
  rw [gap1]
  norm_num

theorem gap3 (y : ℝ) :
    partialY f 0 y = 1 / (1 + y ^ 2) := by
  rw [partialY]
  have hfun : (fun t : ℝ => f 0 t) = Real.arctan := by
    funext t
    simp [f]
  rw [hfun]
  exact Real.hasDerivAt_arctan y |>.deriv

theorem gap4 :
    partialY f 0 0 = 1 := by
  rw [gap3]
  norm_num

theorem gap5 :
    AgreesToFirstOrder
      (fun q => f q.1 q.2)
      (fun q => linearTaylorFromPartials q.1 q.2) := by
  unfold AgreesToFirstOrder
  have h := f_hasFDerivAt_zero3244.isLittleO.norm_right
  convert h using 1
  · funext q
    simp [linearTaylorFromPartials, gap2, gap4, f, linearPart3244]
  · funext q
    rw [show ((0, 0) : ℝ × ℝ) = 0 by rfl, sub_zero]

theorem gap6 (x y : ℝ) :
    linearTaylorFromPartials x y = linearTaylor x y := by
  simp [linearTaylorFromPartials, linearTaylor, f, gap2, gap4]

theorem gap7 :
    AgreesToFirstOrder
      (fun q => f q.1 q.2)
      (fun q => linearTaylor q.1 q.2) := by
  convert gap5 using 1
  funext q
  exact (gap6 q.1 q.2).symm

theorem gap8 :
    AgreesToFirstOrder
      (fun q =>
        Real.arctan ((q.1 + q.2) / (1 + q.1 * q.2)))
      (fun q => q.1 + q.2) := by
  simpa [f, linearTaylor] using gap7

end

end ProofGap.Exercise3244_3
