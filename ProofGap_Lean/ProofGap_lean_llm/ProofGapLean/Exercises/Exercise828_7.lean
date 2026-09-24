import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise828_7

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def csc (x : ℝ) : ℝ := 1 / Real.sin x
def y := cot
def Δy (x Δx : ℝ) : ℝ := y (x + Δx) - y x

private theorem neg_one_sub_cot_sq_eq_neg_csc_sq (x : ℝ)
    (hx : Real.sin x ≠ 0) :
    -1 - cot x ^ 2 = -(csc x ^ 2) := by
  unfold cot csc
  field_simp [hx] <;> nlinarith [Real.sin_sq_add_cos_sq x]

private theorem hasDerivAt_y_of_sin_ne_zero (x : ℝ)
    (hx : Real.sin x ≠ 0) :
    HasDerivAt y (-(csc x ^ 2)) x := by
  have hcos : HasDerivAt Real.cos (-Real.sin x) x :=
    Real.hasDerivAt_cos x
  have hsin : HasDerivAt Real.sin (Real.cos x) x :=
    Real.hasDerivAt_sin x
  have hcoef :
      ((-Real.sin x) * Real.sin x - Real.cos x * Real.cos x) /
          Real.sin x ^ 2 =
        -((1 / Real.sin x) ^ 2) := by
    field_simp [hx] <;> nlinarith [Real.sin_sq_add_cos_sq x]
  simpa only [y, cot, csc, hcoef] using hcos.div hsin hx

theorem gap1 (x Δx : ℝ) :
    Δy x Δx / Δx = (cot (x + Δx) - cot x) / Δx := by
  rfl
theorem gap2 (x Δx : ℝ)
    (hadd : cot (x + Δx) = (cot x * cot Δx - 1) / (cot x + cot Δx)) :
    (cot (x + Δx) - cot x) / Δx =
      (((cot x * cot Δx - 1) / (cot x + cot Δx)) - cot x) / Δx := by
  rw [hadd]
theorem gap3 (x Δx : ℝ) (hΔ : Δx ≠ 0) (hden : cot x + cot Δx ≠ 0) :
    (((cot x * cot Δx - 1) / (cot x + cot Δx)) - cot x) / Δx =
      (-1 - cot x ^ 2) / (Δx * (cot x + cot Δx)) := by
  field_simp [hΔ, hden] <;> ring
theorem gap4 (x Δx : ℝ) (hx : Real.sin x ≠ 0) :
    (-1 - cot x ^ 2) / (Δx * (cot x + cot Δx)) =
      -(csc x ^ 2) / (Δx * (cot x + cot Δx)) := by
  rw [neg_one_sub_cot_sq_eq_neg_csc_sq x hx]
theorem gap5 (x Δx : ℝ)
    (h : Δy x Δx / Δx =
      (-1 - cot x ^ 2) / (Δx * (cot x + cot Δx))) :
    Δy x Δx / Δx = -(csc x ^ 2) / (Δx * (cot x + cot Δx)) := by
  by_cases hx : Real.sin x = 0
  · have hcos : Real.cos x ≠ 0 := by
      intro hcx
      nlinarith [Real.sin_sq_add_cos_sq x]
    have hcotx : cot x = 0 := by
      simp [cot, hx]
    have hshift : cot (x + Δx) = cot Δx := by
      unfold cot
      rw [Real.cos_add, Real.sin_add, hx]
      simp only [zero_mul, sub_zero, zero_add]
      by_cases hs : Real.sin Δx = 0
      · simp [hs]
      · field_simp [hcos, hs] <;> ring
    have hh : cot Δx / Δx = -1 / (Δx * cot Δx) := by
      simpa [Δy, y, hshift, hcotx] using h
    have hz : cot Δx / Δx = 0 := by
      by_cases hdx : Δx = 0
      · simp [hdx]
      by_cases hcot : cot Δx = 0
      · simp [hcot]
      exfalso
      have hh' := hh
      field_simp [hdx, hcot] at hh'
      nlinarith [sq_nonneg (cot Δx)]
    simpa [Δy, y, hshift, hcotx, csc, hx] using hz
  · calc
      Δy x Δx / Δx =
          (-1 - cot x ^ 2) / (Δx * (cot x + cot Δx)) := h
      _ = -(csc x ^ 2) / (Δx * (cot x + cot Δx)) := by
        rw [neg_one_sub_cot_sq_eq_neg_csc_sq x hx]
theorem gap6 (x : ℝ) :
    HasDerivAt y (deriv y x) x ↔
      Filter.Tendsto (fun Δx => Δy x Δx / Δx)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (deriv y x)) := by
  simpa [Δy, div_eq_mul_inv, mul_comm] using
    (hasDerivAt_iff_tendsto_slope_zero
      (f := y) (f' := deriv y x) (x := x))
theorem gap7 (x : ℝ) (hx : Real.sin x ≠ 0) :
    Filter.Tendsto (fun Δx => Δy x Δx / Δx)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-(csc x ^ 2))) := by
  have hd := hasDerivAt_y_of_sin_ne_zero x hx
  have hderiv : deriv y x = -(csc x ^ 2) := hd.deriv
  have hd' : HasDerivAt y (deriv y x) x := by
    simpa only [hderiv] using hd
  simpa only [hderiv] using (gap6 x).mp hd'
theorem gap8 (x : ℝ) (hx : Real.sin x ≠ 0) :
    deriv y x = -(csc x ^ 2) := by
  exact (hasDerivAt_y_of_sin_ne_zero x hx).deriv
theorem gap9 (x : ℝ) : -(csc x ^ 2) = -(1 / Real.sin x ^ 2) := by
  simp [csc]
theorem gap10 (x : ℝ) (hx : Real.sin x ≠ 0) :
    deriv y x = -(1 / Real.sin x ^ 2) := by
  calc
    deriv y x = -(csc x ^ 2) := gap8 x hx
    _ = -(1 / Real.sin x ^ 2) := gap9 x

end

end ProofGap.Exercise828_7
