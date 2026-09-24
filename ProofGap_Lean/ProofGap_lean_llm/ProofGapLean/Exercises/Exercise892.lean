import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise892

noncomputable section

def numerator (x : ℝ) : ℝ := x * Real.sqrt 3 - Real.sqrt 2
def denominator (x : ℝ) : ℝ := x * Real.sqrt 3 + Real.sqrt 2

def y (x : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt 6)) *
    Real.log (numerator x / denominator x)

def logarithmicForm (x : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt 6)) *
    (Real.log |numerator x| - Real.log |denominator x|)

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt 6)) *
    (Real.sqrt 3 / numerator x - Real.sqrt 3 / denominator x)

def finalDerivative (x : ℝ) : ℝ := 1 / (3 * x ^ 2 - 2)

theorem gap1 (x : ℝ) (hnum : numerator x ≠ 0)
    (hden : denominator x ≠ 0)
    (hratio : 0 < numerator x / denominator x) :
    y x = logarithmicForm x := by
  unfold y logarithmicForm
  rw [Real.log_div hnum hden, Real.log_abs, Real.log_abs]

theorem gap2 (x : ℝ) (hnum : numerator x ≠ 0)
    (hden : denominator x ≠ 0)
    (hratio : 0 < numerator x / denominator x) :
    deriv y x = expandedDerivative x := by
  have hnumDeriv : HasDerivAt numerator (Real.sqrt 3) x := by
    simpa [numerator] using
      ((hasDerivAt_id x).mul_const (Real.sqrt 3)).sub
        (hasDerivAt_const x (Real.sqrt 2))
  have hdenDeriv : HasDerivAt denominator (Real.sqrt 3) x := by
    simpa [denominator] using
      ((hasDerivAt_id x).mul_const (Real.sqrt 3)).add
        (hasDerivAt_const x (Real.sqrt 2))
  have hquot :
      HasDerivAt (fun z : ℝ => numerator z / denominator z)
        ((Real.sqrt 3 * denominator x - Real.sqrt 3 * numerator x) /
          denominator x ^ 2) x := by
    convert hnumDeriv.div hdenDeriv hden using 1 <;> ring
  have hscaled :
      HasDerivAt y
        ((1 / (2 * Real.sqrt 6)) *
          (((Real.sqrt 3 * denominator x - Real.sqrt 3 * numerator x) /
              denominator x ^ 2) /
            (numerator x / denominator x))) x := by
    simpa only [y] using
      ((hquot.log (ne_of_gt hratio)).const_mul
        (1 / (2 * Real.sqrt 6)))
  have halgebra :
      ((Real.sqrt 3 * denominator x - Real.sqrt 3 * numerator x) /
          denominator x ^ 2) /
          (numerator x / denominator x) =
        Real.sqrt 3 / numerator x - Real.sqrt 3 / denominator x := by
    field_simp [hnum, hden] <;> ring
  rw [hscaled.deriv]
  unfold expandedDerivative
  rw [halgebra]

theorem gap3 (x : ℝ) (hnum : numerator x ≠ 0)
    (hden : denominator x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs6 : (Real.sqrt 6) ^ 2 = (6 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs6ne : Real.sqrt 6 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs23 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
    let p : ℝ := Real.sqrt 3 * Real.sqrt 2
    have hp : 0 ≤ p := by
      dsimp [p]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hp_sq : p ^ 2 = (6 : ℝ) := by
      dsimp [p]
      calc
        (Real.sqrt 3 * Real.sqrt 2) ^ 2 =
            (Real.sqrt 3) ^ 2 * (Real.sqrt 2) ^ 2 := by ring
        _ = 6 := by rw [hs3, hs2]; norm_num
    have hs6nonneg : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
    nlinarith
  have hprod :
      numerator x * denominator x = 3 * x ^ 2 - 2 := by
    simp only [numerator, denominator]
    calc
      (x * Real.sqrt 3 - Real.sqrt 2) *
          (x * Real.sqrt 3 + Real.sqrt 2) =
          x ^ 2 * (Real.sqrt 3) ^ 2 - (Real.sqrt 2) ^ 2 := by ring
      _ = 3 * x ^ 2 - 2 := by rw [hs3, hs2]; ring
  have hpoly : 3 * x ^ 2 - 2 ≠ 0 := by
    have hprodne : numerator x * denominator x ≠ 0 :=
      mul_ne_zero hnum hden
    rwa [hprod] at hprodne
  have hdiff :
      Real.sqrt 3 * denominator x - Real.sqrt 3 * numerator x =
        2 * Real.sqrt 6 := by
    calc
      Real.sqrt 3 * denominator x - Real.sqrt 3 * numerator x =
          2 * (Real.sqrt 3 * Real.sqrt 2) := by
            simp only [numerator, denominator]
            ring
      _ = 2 * Real.sqrt 6 := by rw [hs23]
  have hfrac :
      Real.sqrt 3 / numerator x - Real.sqrt 3 / denominator x =
        (Real.sqrt 3 * denominator x - Real.sqrt 3 * numerator x) /
          (numerator x * denominator x) := by
    field_simp [hnum, hden] <;> ring
  unfold expandedDerivative finalDerivative
  rw [hfrac, hdiff, hprod]
  field_simp [hs6ne, hpoly] <;> ring

theorem gap4 (x : ℝ) (hnum : numerator x ≠ 0)
    (hden : denominator x ≠ 0)
    (hratio : 0 < numerator x / denominator x) :
    deriv y x = finalDerivative x := by
  rw [gap2 x hnum hden hratio, gap3 x hnum hden]

end

end ProofGap.Exercise892
