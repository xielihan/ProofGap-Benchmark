import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise884

noncomputable section

def y (a b x : ℝ) : ℝ :=
  Real.rpow (a / b) x * Real.rpow (b / x) a *
    Real.rpow (x / a) b

def logarithmicDerivative (a b x : ℝ) : ℝ :=
  Real.log (a / b) - a / x + b / x

private theorem explicitRpowOfPos {u v : ℝ} (hu : 0 < u) :
    Real.rpow u v = Real.exp (Real.log u * v) := by
  exact Real.rpow_def_of_pos hu v

theorem gap1 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    Real.log (y a b x) =
      x * Real.log (a / b) +
        a * (Real.log b - Real.log x) +
          b * (Real.log x - Real.log a) := by
  have hab : 0 < a / b := div_pos ha hb
  have hbx : 0 < b / x := div_pos hb hx
  have hxa : 0 < x / a := div_pos hx ha
  have h₁ : 0 < Real.rpow (a / b) x := Real.rpow_pos_of_pos hab x
  have h₂ : 0 < Real.rpow (b / x) a := Real.rpow_pos_of_pos hbx a
  have h₃ : 0 < Real.rpow (x / a) b := Real.rpow_pos_of_pos hxa b
  have hlog₁ :
      Real.log (Real.rpow (a / b) x) = x * Real.log (a / b) := by
    rw [explicitRpowOfPos hab, Real.log_exp]
    ring
  have hlog₂ :
      Real.log (Real.rpow (b / x) a) = a * Real.log (b / x) := by
    rw [explicitRpowOfPos hbx, Real.log_exp]
    ring
  have hlog₃ :
      Real.log (Real.rpow (x / a) b) = b * Real.log (x / a) := by
    rw [explicitRpowOfPos hxa, Real.log_exp]
    ring
  unfold y
  rw [Real.log_mul (mul_ne_zero h₁.ne' h₂.ne') h₃.ne',
    Real.log_mul h₁.ne' h₂.ne', hlog₁, hlog₂, hlog₃,
    Real.log_div ha.ne' hb.ne', Real.log_div hb.ne' hx.ne',
    Real.log_div hx.ne' ha.ne']

theorem gap2 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    deriv (y a b) x / y a b x = logarithmicDerivative a b x := by
  have hab : 0 < a / b := div_pos ha hb
  have hbx : 0 < b / x := div_pos hb hx
  have hxa : 0 < x / a := div_pos hx ha
  have hp₂ :
      (b / x) * Real.rpow (b / x) (a - 1) =
        Real.rpow (b / x) a := by
    simp only [explicitRpowOfPos hbx]
    rw [← Real.exp_log hbx, ← Real.exp_add]
    congr 1
    rw [Real.log_exp]
    ring
  have hp₃ :
      (x / a) * Real.rpow (x / a) (b - 1) =
        Real.rpow (x / a) b := by
    simp only [explicitRpowOfPos hxa]
    rw [← Real.exp_log hxa, ← Real.exp_add]
    congr 1
    rw [Real.log_exp]
    ring
  have hinner :
      HasDerivAt (fun t : ℝ => Real.log (a / b) * t)
        (Real.log (a / b)) x := by
    convert
      (hasDerivAt_const x (Real.log (a / b))).mul (hasDerivAt_id x)
      using 1 <;> simp [id_eq] <;> ring
  have hexp :
      HasDerivAt
        (fun t : ℝ => Real.exp (Real.log (a / b) * t))
        (Real.exp (Real.log (a / b) * x) * Real.log (a / b)) x :=
    (Real.hasDerivAt_exp _).comp x hinner
  have h₁ :
      HasDerivAt (fun t : ℝ => Real.rpow (a / b) t)
        (Real.rpow (a / b) x * Real.log (a / b)) x := by
    simpa only [explicitRpowOfPos hab] using hexp
  have hbdiv :
      HasDerivAt (fun t : ℝ => b / t) (-b / x ^ 2) x := by
    convert (hasDerivAt_const x b).div (hasDerivAt_id x) hx.ne'
      using 1 <;> simp [id_eq] <;> ring
  have houter₂ :
      HasDerivAt (fun u : ℝ => Real.rpow u a)
        (a * Real.rpow (b / x) (a - 1)) (b / x) :=
    Real.hasDerivAt_rpow_const (Or.inl hbx.ne')
  have h₂ :
      HasDerivAt (fun t : ℝ => Real.rpow (b / t) a)
        (Real.rpow (b / x) a * (-a / x)) x := by
    convert (houter₂.comp x hbdiv) using 1
    rw [← hp₂]
    field_simp [hx.ne'] <;> ring
  have hxdiv :
      HasDerivAt (fun t : ℝ => t / a) (1 / a) x := by
    simpa using (hasDerivAt_id x).div_const a
  have houter₃ :
      HasDerivAt (fun u : ℝ => Real.rpow u b)
        (b * Real.rpow (x / a) (b - 1)) (x / a) :=
    Real.hasDerivAt_rpow_const (Or.inl hxa.ne')
  have h₃ :
      HasDerivAt (fun t : ℝ => Real.rpow (t / a) b)
        (Real.rpow (x / a) b * (b / x)) x := by
    convert (houter₃.comp x hxdiv) using 1
    rw [← hp₃]
    field_simp [ha.ne', hx.ne'] <;> ring
  have hprod := (h₁.mul h₂).mul h₃
  have hn₁ : Real.rpow (a / b) x ≠ 0 :=
    (Real.rpow_pos_of_pos hab x).ne'
  have hn₂ : Real.rpow (b / x) a ≠ 0 :=
    (Real.rpow_pos_of_pos hbx a).ne'
  have hn₃ : Real.rpow (x / a) b ≠ 0 :=
    (Real.rpow_pos_of_pos hxa b).ne'
  unfold y logarithmicDerivative
  change
    deriv
        (((fun t : ℝ => Real.rpow (a / b) t) *
            (fun t : ℝ => Real.rpow (b / t) a)) *
          (fun t : ℝ => Real.rpow (t / a) b)) x /
      (Real.rpow (a / b) x * Real.rpow (b / x) a *
        Real.rpow (x / a) b) =
      Real.log (a / b) - a / x + b / x
  rw [hprod.deriv]
  simp only [Pi.mul_apply]
  field_simp [hn₁, hn₂, hn₃, hx.ne'] <;> ring

theorem gap3 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    deriv (y a b) x = y a b x * logarithmicDerivative a b x := by
  have hab : 0 < a / b := div_pos ha hb
  have hbx : 0 < b / x := div_pos hb hx
  have hxa : 0 < x / a := div_pos hx ha
  have hy : y a b x ≠ 0 := by
    unfold y
    exact mul_ne_zero
      (mul_ne_zero (Real.rpow_pos_of_pos hab x).ne'
        (Real.rpow_pos_of_pos hbx a).ne')
      (Real.rpow_pos_of_pos hxa b).ne'
  have h := (div_eq_iff hy).mp (gap2 a b x ha hb hx)
  simpa [mul_comm] using h

theorem gap4 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    y a b x * logarithmicDerivative a b x =
      Real.rpow (a / b) x * Real.rpow (b / x) a *
        Real.rpow (x / a) b * logarithmicDerivative a b x := by
  rfl

theorem gap5 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    deriv (y a b) x =
      Real.rpow (a / b) x * Real.rpow (b / x) a *
        Real.rpow (x / a) b * logarithmicDerivative a b x := by
  calc
    deriv (y a b) x = y a b x * logarithmicDerivative a b x :=
      gap3 a b x ha hb hx
    _ = Real.rpow (a / b) x * Real.rpow (b / x) a *
          Real.rpow (x / a) b * logarithmicDerivative a b x :=
      gap4 a b x ha hb hx

end

end ProofGap.Exercise884
