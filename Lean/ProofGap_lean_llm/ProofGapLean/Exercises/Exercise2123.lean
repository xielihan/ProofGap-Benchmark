import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2123
noncomputable section

def t (x : ℝ) := Real.sinh (x / 2) / Real.cosh (x / 2)
def integrand (x : ℝ) := 1 / (Real.sinh x + 2 * Real.cosh x)
def pulledBack (x : ℝ) := deriv t x / (t x ^ 2 + t x + 1)
def primitiveT (x : ℝ) :=
  2 / Real.sqrt 3 * Real.arctan ((2 * t x + 1) / Real.sqrt 3)
def primitive (x : ℝ) :=
  2 / Real.sqrt 3 *
    Real.arctan ((1 + 2 * (Real.sinh (x / 2) / Real.cosh (x / 2))) / Real.sqrt 3)

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x, F x = p x + C}

theorem gap1 (x : ℝ) :
    Real.sinh x = 2 * t x / (1 - t x ^ 2) := by
  have hc : Real.cosh (x / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hden :
      1 - (Real.sinh (x / 2) / Real.cosh (x / 2)) ^ 2 =
        1 / Real.cosh (x / 2) ^ 2 := by
    field_simp [hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  have hx : x / 2 + x / 2 = x := by ring
  have hsinh :
      Real.sinh x =
        Real.sinh (x / 2) * Real.cosh (x / 2) +
          Real.cosh (x / 2) * Real.sinh (x / 2) := by
    calc
      Real.sinh x = Real.sinh (x / 2 + x / 2) := congrArg Real.sinh hx.symm
      _ = Real.sinh (x / 2) * Real.cosh (x / 2) +
          Real.cosh (x / 2) * Real.sinh (x / 2) := Real.sinh_add _ _
  unfold t
  rw [hsinh, hden]
  field_simp [hc]
  ring
theorem gap2 (x : ℝ) :
    Real.cosh x = (1 + t x ^ 2) / (1 - t x ^ 2) := by
  have hc : Real.cosh (x / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hden :
      1 - (Real.sinh (x / 2) / Real.cosh (x / 2)) ^ 2 =
        1 / Real.cosh (x / 2) ^ 2 := by
    field_simp [hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  have hx : x / 2 + x / 2 = x := by ring
  have hcosh :
      Real.cosh x =
        Real.cosh (x / 2) * Real.cosh (x / 2) +
          Real.sinh (x / 2) * Real.sinh (x / 2) := by
    calc
      Real.cosh x = Real.cosh (x / 2 + x / 2) := congrArg Real.cosh hx.symm
      _ = Real.cosh (x / 2) * Real.cosh (x / 2) +
          Real.sinh (x / 2) * Real.sinh (x / 2) := Real.cosh_add _ _
  unfold t
  rw [hcosh, hden]
  field_simp [hc]
theorem gap3 (x : ℝ) :
    x = Real.log ((1 + t x) / (1 - t x)) := by
  have hc : Real.cosh (x / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hplus :
      Real.cosh (x / 2) + Real.sinh (x / 2) = Real.exp (x / 2) := by
    simpa [add_comm] using (Real.exp_eq_cosh_add_sinh (x / 2)).symm
  have hminus :
      Real.cosh (x / 2) - Real.sinh (x / 2) = Real.exp (-(x / 2)) := by
    simpa using (Real.exp_neg_eq_cosh_sub_sinh (x / 2)).symm
  have hcm : Real.cosh (x / 2) - Real.sinh (x / 2) ≠ 0 := by
    rw [hminus]
    exact Real.exp_ne_zero _
  have hratio : (1 + t x) / (1 - t x) = Real.exp x := by
    unfold t
    calc
      (1 + Real.sinh (x / 2) / Real.cosh (x / 2)) /
          (1 - Real.sinh (x / 2) / Real.cosh (x / 2)) =
          (Real.cosh (x / 2) + Real.sinh (x / 2)) /
            (Real.cosh (x / 2) - Real.sinh (x / 2)) := by
              field_simp [hc, hcm]
      _ = Real.exp (x / 2) / Real.exp (-(x / 2)) := by rw [hplus, hminus]
      _ = Real.exp ((x / 2) - (-(x / 2))) := by rw [Real.exp_sub]
      _ = Real.exp x := by congr 1 <;> ring
  rw [hratio]
  exact (Real.log_exp x).symm
theorem gap4 (x : ℝ) :
    1 = (2 / (1 - t x ^ 2)) * deriv t x := by
  have hc : Real.cosh (x / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hs : HasDerivAt (fun y : ℝ => Real.sinh (y / 2))
      (Real.cosh (x / 2) / 2) x := by
    convert (Real.hasDerivAt_sinh (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2) using 1 <;> ring
  have hcos : HasDerivAt (fun y : ℝ => Real.cosh (y / 2))
      (Real.sinh (x / 2) / 2) x := by
    convert (Real.hasDerivAt_cosh (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2) using 1 <;> ring
  have ht : HasDerivAt t
      ((Real.cosh (x / 2) / 2 * Real.cosh (x / 2) -
          Real.sinh (x / 2) * (Real.sinh (x / 2) / 2)) /
        Real.cosh (x / 2) ^ 2) x := by
    unfold t
    exact hs.div hcos hc
  have hden : 0 < 1 - t x ^ 2 := by
    have heq :
        1 - (Real.sinh (x / 2) / Real.cosh (x / 2)) ^ 2 =
          1 / Real.cosh (x / 2) ^ 2 := by
      field_simp [hc]
      nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
    unfold t
    rw [heq]
    positivity
  have hdt : deriv t x = (1 - t x ^ 2) / 2 := by
    rw [ht.deriv]
    unfold t
    field_simp [hc]
  rw [hdt]
  field_simp [ne_of_gt hden]
theorem gap5 : Family integrand = Family pulledBack := by
  have heq : ∀ x, integrand x = pulledBack x := by
    intro x
    have hd : 1 - t x ^ 2 ≠ 0 := by
      intro hz
      have h := gap4 x
      rw [hz] at h
      norm_num at h
    have hq : 0 < t x ^ 2 + t x + 1 := by
      nlinarith [sq_nonneg (t x + 1 / 2)]
    have hder : deriv t x = (1 - t x ^ 2) / 2 := by
      have h := gap4 x
      field_simp [hd] at h
      nlinarith
    have hsum :
        2 * t x / (1 - t x ^ 2) +
            2 * ((1 + t x ^ 2) / (1 - t x ^ 2)) =
          2 * (t x ^ 2 + t x + 1) / (1 - t x ^ 2) := by
      field_simp [hd] <;> ring
    unfold integrand pulledBack
    rw [gap1 x, gap2 x, hsum, hder]
    field_simp [hd, ne_of_gt hq] <;> ring
  apply Set.ext
  intro F
  change (∀ x, HasDerivAt F (integrand x) x) ↔
    ∀ x, HasDerivAt F (pulledBack x) x
  constructor
  · intro h x
    rw [← heq x]
    exact h x
  · intro h x
    rw [heq x]
    exact h x
theorem gap6 : Family pulledBack = Translates primitiveT := by
  have hp : ∀ x, HasDerivAt primitiveT (pulledBack x) x := by
    intro x
    have hc : Real.cosh (x / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    have hs : HasDerivAt (fun y : ℝ => Real.sinh (y / 2))
        (Real.cosh (x / 2) / 2) x := by
      convert (Real.hasDerivAt_sinh (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2) using 1 <;> ring
    have hcos : HasDerivAt (fun y : ℝ => Real.cosh (y / 2))
        (Real.sinh (x / 2) / 2) x := by
      convert (Real.hasDerivAt_cosh (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2) using 1 <;> ring
    have ht0 : HasDerivAt t
        ((Real.cosh (x / 2) / 2 * Real.cosh (x / 2) -
            Real.sinh (x / 2) * (Real.sinh (x / 2) / 2)) /
          Real.cosh (x / 2) ^ 2) x := by
      unfold t
      exact hs.div hcos hc
    have ht : HasDerivAt t (deriv t x) x :=
      ht0.differentiableAt.hasDerivAt
    have hsqrt : Real.sqrt 3 ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hsqrt_sq : Real.sqrt 3 ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    have hinner :
        HasDerivAt (fun y : ℝ => (2 * t y + 1) / Real.sqrt 3)
          ((2 * deriv t x) / Real.sqrt 3) x := by
      convert ((ht.const_mul 2).add_const 1).div_const (Real.sqrt 3) using 1 <;> ring
    have hprim : HasDerivAt primitiveT
        ((2 / Real.sqrt 3) *
          ((1 / (1 + ((2 * t x + 1) / Real.sqrt 3) ^ 2)) *
            ((2 * deriv t x) / Real.sqrt 3))) x := by
      unfold primitiveT
      convert ((Real.hasDerivAt_arctan
        ((2 * t x + 1) / Real.sqrt 3)).comp x hinner).const_mul
          (2 / Real.sqrt 3) using 1 <;> ring
    have hq : 0 < t x ^ 2 + t x + 1 := by
      nlinarith [sq_nonneg (t x + 1 / 2)]
    have hq' : t x * (t x + 1) + 1 ≠ 0 := by
      intro hzero
      apply ne_of_gt hq
      nlinarith
    have hz : 0 < 1 + ((2 * t x + 1) / Real.sqrt 3) ^ 2 := by
      positivity
    have hcoeff :
        (2 / Real.sqrt 3) *
            ((1 / (1 + ((2 * t x + 1) / Real.sqrt 3) ^ 2)) *
              ((2 * deriv t x) / Real.sqrt 3)) =
          deriv t x / (t x ^ 2 + t x + 1) := by
      field_simp [hsqrt, ne_of_gt hq, hq', ne_of_gt hz]
      rw [hsqrt_sq]
      ring
    rw [hcoeff] at hprim
    simpa only [pulledBack] using hprim
  apply Set.ext
  intro F
  change (∀ x, HasDerivAt F (pulledBack x) x) ↔
    ∃ C : ℝ, ∀ x, F x = primitiveT x + C
  constructor
  · intro hF
    have hG : ∀ x, HasDerivAt (fun y => F y - primitiveT y) 0 x := by
      intro x
      simpa using (hF x).sub (hp x)
    have hdiff : Differentiable ℝ (fun y => F y - primitiveT y) :=
      fun x => (hG x).differentiableAt
    have hderiv : ∀ x, deriv (fun y => F y - primitiveT y) x = 0 :=
      fun x => (hG x).deriv
    refine ⟨F 0 - primitiveT 0, ?_⟩
    intro x
    have hcst := is_const_of_deriv_eq_zero hdiff hderiv x 0
    linarith
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => primitiveT x + C := funext hC
    rw [hfun]
    intro x
    simpa using (hp x).add_const C
theorem gap7 : Translates primitiveT = Translates primitive := by
  have hp : primitiveT = primitive := by
    funext x
    simp only [primitiveT, primitive, t, add_comm]
  rw [hp]
theorem gap8 : Family integrand = Translates primitive := by
  rw [gap5, gap6, gap7]

end
end ProofGap.Exercise2123
