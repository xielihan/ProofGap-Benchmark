import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1309

noncomputable section

def y (h x : ℝ) : ℝ :=
  h / Real.sqrt (2 * Real.pi) * Real.exp (-(h ^ 2 * x ^ 2))

private theorem hasDerivAt_exp_kernel (h x : ℝ) :
    HasDerivAt
      (fun t : ℝ => Real.exp (-(h ^ 2 * t ^ 2)))
      (Real.exp (-(h ^ 2 * x ^ 2)) * (-2 * h ^ 2 * x)) x := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := by
    simpa only [id_eq] using (hasDerivAt_id x)
  have hinner :
      HasDerivAt (fun t : ℝ => -(h ^ 2 * t ^ 2)) (-2 * h ^ 2 * x) x := by
    have hneg := ((hid.mul hid).const_mul (h ^ 2)).neg
    convert hneg using 1
    · funext t
      change -(h ^ 2 * t ^ 2) = -(h ^ 2 * (t * t))
      ring
    · ring
  exact (Real.hasDerivAt_exp _).comp x hinner

theorem gap1 (h x : ℝ) :
    deriv (y h) x =
      (-2 * h ^ 3 * x / Real.sqrt (2 * Real.pi)) *
        Real.exp (-(h ^ 2 * x ^ 2)) := by
  unfold y
  apply HasDerivAt.deriv
  convert
    (hasDerivAt_exp_kernel h x).const_mul
      (h / Real.sqrt (2 * Real.pi)) using 1 <;> ring

theorem gap2 (h x : ℝ) :
    deriv (deriv (y h)) x =
      h / Real.sqrt (2 * Real.pi) *
        Real.exp (-(h ^ 2 * x ^ 2)) *
        (4 * h ^ 4 * x ^ 2 - 2 * h ^ 2) := by
  have hderiv :
      deriv (y h) = fun t : ℝ =>
        -2 * h ^ 3 * t / Real.sqrt (2 * Real.pi) *
          Real.exp (-(h ^ 2 * t ^ 2)) := by
    funext t
    exact gap1 h t
  rw [hderiv]
  apply HasDerivAt.deriv
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := by
    simpa only [id_eq] using (hasDerivAt_id x)
  have hlinear :
      HasDerivAt
        (fun t : ℝ => -2 * h ^ 3 * t / Real.sqrt (2 * Real.pi))
        (-2 * h ^ 3 / Real.sqrt (2 * Real.pi)) x := by
    have hbase :=
      hid.const_mul (-2 * h ^ 3 / Real.sqrt (2 * Real.pi))
    convert hbase using 1
    · funext t
      ring
    · ring
  have hprod := hlinear.mul (hasDerivAt_exp_kernel h x)
  convert hprod using 1 <;>
    first
    | (funext t; ring)
    | ring

theorem gap3 (h x : ℝ) (hh : h ≠ 0)
    (hzero : deriv (deriv (y h)) x = 0) :
    x ^ 2 = 1 / (2 * h ^ 2) := by
  rw [gap2 h x] at hzero
  have htwo_pi : 0 < (2 : ℝ) * Real.pi :=
    mul_pos (by norm_num) Real.pi_pos
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 htwo_pi)
  have hfactor : 4 * h ^ 4 * x ^ 2 - 2 * h ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left
      (mul_ne_zero
        (div_ne_zero hh hsqrt)
        (ne_of_gt (Real.exp_pos (-(h ^ 2 * x ^ 2)))))
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hprod :
      (2 * h ^ 2) * (2 * h ^ 2 * x ^ 2 - 1) = 0 := by
    calc
      (2 * h ^ 2) * (2 * h ^ 2 * x ^ 2 - 1) =
          4 * h ^ 4 * x ^ 2 - 2 * h ^ 2 := by ring
      _ = 0 := hfactor
  have hinner : 2 * h ^ 2 * x ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left
      (mul_ne_zero (by norm_num) hh2)
  apply (eq_div_iff (mul_ne_zero (by norm_num) hh2)).2
  nlinarith [hinner]

theorem gap4 (h σ : ℝ) (hσ : σ ≠ 0)
    (hh : h = 1 / (σ * Real.sqrt 2)) :
    h ^ 2 = 1 / (2 * σ ^ 2) := by
  rw [hh, div_pow, one_pow, mul_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

theorem gap5 (h σ x : ℝ) (hσ : 0 < σ)
    (hh : h = 1 / (σ * Real.sqrt 2))
    (hzero : deriv (deriv (y h)) x = 0) :
    x = -σ ∨ x = σ := by
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hsqrt2 : Real.sqrt (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hh0 : h ≠ 0 := by
    rw [hh]
    exact div_ne_zero (by norm_num) (mul_ne_zero hσ0 hsqrt2)
  have hx := gap3 h x hh0 hzero
  have hh2 := gap4 h σ hσ0 hh
  rw [hh2] at hx
  have hx_sq : x ^ 2 = σ ^ 2 := by
    calc
      x ^ 2 = 1 / (2 * (1 / (2 * σ ^ 2))) := hx
      _ = σ ^ 2 := by
        field_simp [hσ0] <;> ring
  have hprod : (x - σ) * (x + σ) = 0 := by
    calc
      (x - σ) * (x + σ) = x ^ 2 - σ ^ 2 := by ring
      _ = 0 := by
        rw [hx_sq]
        exact sub_self (σ ^ 2)
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

end

end ProofGap.Exercise1309
