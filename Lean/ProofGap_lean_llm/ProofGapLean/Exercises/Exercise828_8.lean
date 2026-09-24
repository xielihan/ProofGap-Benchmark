import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise828_8

noncomputable section

def increment (x Δx : ℝ) : ℝ := Real.arcsin (x + Δx) - Real.arcsin x
def quotient (x Δx : ℝ) : ℝ := increment x Δx / Δx
def auxiliary (x Δx : ℝ) : ℝ :=
  (x + Δx) * Real.sqrt (1 - x ^ 2) -
    x * Real.sqrt (1 - (x + Δx) ^ 2)

/-- Exercise 828_8, gap 1; bind `Δy` and add `Δx≠0`. -/
private theorem tendsto_div_sin_at_zero :
    Filter.Tendsto (fun u : ℝ => u / Real.sin u)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hsin :
      Filter.Tendsto (fun u : ℝ => Real.sin u / u)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero
  simpa only [inv_div, inv_one] using
    hsin.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

theorem gap1 (Δy Δx x : ℝ) (hΔy : Δy = increment x Δx)
    (hΔx : Δx ≠ 0) :
    Δy / Δx = (Real.arcsin (x + Δx) - Real.arcsin x) / Δx := by
  rw [hΔy]
  rfl

/-- Exercise 828_8, gap 2; add a local-domain hypothesis
under which the arcsine subtraction identity is valid. -/
theorem gap2 (x Δx : ℝ)
    (hformula :
      Real.arcsin (x + Δx) - Real.arcsin x =
        Real.arcsin (auxiliary x Δx)) :
    (Real.arcsin (x + Δx) - Real.arcsin x) / Δx =
      Real.arcsin (auxiliary x Δx) / Δx := by
  rw [hformula]

/-- Exercise 828_8, gap 3; bind `Δy` and the local
subtraction identity. -/
theorem gap3 (Δy Δx x : ℝ) (hΔy : Δy = increment x Δx)
    (hformula :
      Real.arcsin (x + Δx) - Real.arcsin x =
        Real.arcsin (auxiliary x Δx)) :
    Δy / Δx = Real.arcsin (auxiliary x Δx) / Δx := by
  rw [hΔy]
  simpa [increment] using gap2 x Δx hformula

/-- Exercise 828_8, gap 4; add nonzero denominators. -/
theorem gap4 (x Δx : ℝ) (hΔx : Δx ≠ 0)
    (ht : auxiliary x Δx ≠ 0) :
    Real.arcsin (auxiliary x Δx) / Δx =
      (Real.arcsin (auxiliary x Δx) / auxiliary x Δx) *
        (auxiliary x Δx / Δx) := by
  field_simp [hΔx, ht]

/-- Exercise 828_8, gap 5; bind the previously undefined
`t` as `auxiliary x Δx`. -/
theorem gap5 (x Δx : ℝ) (hΔx : Δx ≠ 0)
    (ht : auxiliary x Δx ≠ 0)
    (hx : |x| ≤ 1) (hshift : |x + Δx| ≤ 1)
    (hformula :
      Real.arcsin (x + Δx) - Real.arcsin x =
        Real.arcsin (auxiliary x Δx))
    (hden :
      (x + Δx) * Real.sqrt (1 - x ^ 2) +
        x * Real.sqrt (1 - (x + Δx) ^ 2) ≠ 0) :
    quotient x Δx =
      (Real.arcsin (auxiliary x Δx) / auxiliary x Δx) *
      ((2 * x + Δx) /
        ((x + Δx) * Real.sqrt (1 - x ^ 2) +
          x * Real.sqrt (1 - (x + Δx) ^ 2))) := by
  rcases abs_le.mp hx with ⟨hxlo, hxhi⟩
  rcases abs_le.mp hshift with ⟨hslo, hshi⟩
  have hsx : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hss : (Real.sqrt (1 - (x + Δx) ^ 2)) ^ 2 =
      1 - (x + Δx) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hratio :
      auxiliary x Δx / Δx =
        (2 * x + Δx) /
          ((x + Δx) * Real.sqrt (1 - x ^ 2) +
            x * Real.sqrt (1 - (x + Δx) ^ 2)) := by
    unfold auxiliary
    field_simp [hΔx, hden]
    nlinarith
  rw [quotient, increment, hformula]
  calc
    Real.arcsin (auxiliary x Δx) / Δx =
        (Real.arcsin (auxiliary x Δx) / auxiliary x Δx) *
          (auxiliary x Δx / Δx) := gap4 x Δx hΔx ht
    _ = _ := by rw [hratio]

/-- Exercise 828_8, gap 6; bind `t` as a function of
`Δx` and add `|x|<1`. -/
theorem gap6 (x : ℝ) (hx : |x| < 1) :
    Filter.Tendsto (auxiliary x) (nhds 0) (nhds 0) := by
  have hcont : Continuous (auxiliary x) := by
    unfold auxiliary
    exact
      ((continuous_const.add continuous_id).mul continuous_const).sub
        (continuous_const.mul
          (Real.continuous_sqrt.comp
            (continuous_const.sub
              ((continuous_const.add continuous_id).pow 2))))
  have hzero : auxiliary x 0 = 0 := by
    simp [auxiliary]
  have hca :
      Filter.Tendsto (auxiliary x) (nhds 0) (nhds (auxiliary x 0)) :=
    hcont.continuousAt
  rw [hzero] at hca
  exact hca

/-- Exercise 828_8, gap 7; replace the unspecified
derivative limit by `Tendsto`. -/
theorem gap7 (x : ℝ) (hxneg : x ≠ -1) (hxpos : x ≠ 1) :
    Filter.Tendsto (quotient x) (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (deriv Real.arcsin x)) := by
  have hd := Real.hasDerivAt_arcsin hxneg hxpos
  have hfun :
      (fun t : ℝ => t⁻¹ * (Real.arcsin (x + t) - Real.arcsin x)) =
        quotient x := by
    funext t
    simp only [quotient, increment, div_eq_mul_inv]
    rw [mul_comm]
  rw [← hfun, hd.deriv]
  simpa only [smul_eq_mul] using hd.tendsto_slope_zero

/-- Exercise 828_8, gap 8; bind all limits and state their
product conclusion. -/
theorem gap8 (x : ℝ) (hx : |x| < 1) :
    Filter.Tendsto (quotient x) (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds ((1 / Real.sqrt (1 - x ^ 2)) * 1)) := by
  have hx' := abs_lt.mp hx
  have hxneg : x ≠ -1 := ne_of_gt hx'.1
  have hxpos : x ≠ 1 := ne_of_lt hx'.2
  have hslope :=
    (Real.hasDerivAt_arcsin hxneg hxpos).tendsto_slope_zero
  have hfun :
      (fun t : ℝ => t⁻¹ * (Real.arcsin (x + t) - Real.arcsin x)) =
        quotient x := by
    funext t
    simp only [quotient, increment, div_eq_mul_inv]
    rw [mul_comm]
  rw [← hfun]
  simpa only [smul_eq_mul, mul_one] using hslope

/-- Exercise 828_8, gap 9; make the two limit values
explicit. -/
theorem gap9 (x : ℝ) :
    (1 / Real.sqrt (1 - x ^ 2)) * (1 : ℝ) =
      1 / Real.sqrt (1 - x ^ 2) := by
  simp

/-- Exercise 828_8, gap 10; add the interior-domain
condition. -/
theorem gap10 (x : ℝ) (hx : |x| < 1) :
    HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x := by
  have hx' := abs_lt.mp hx
  have hxneg : x ≠ -1 := ne_of_gt hx'.1
  have hxpos : x ≠ 1 := ne_of_lt hx'.2
  exact Real.hasDerivAt_arcsin hxneg hxpos

/-- Exercise 828_8, gap 11; represent the substitution by
equivalence of the two punctured limits. -/
theorem gap11 :
    Filter.Tendsto (fun t : ℝ => Real.arcsin t / t)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) ↔
      Filter.Tendsto (fun u : ℝ => u / Real.sin u)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  constructor
  · intro _
    exact tendsto_div_sin_at_zero
  · intro _
    have hq := gap8 0 (by norm_num : |(0 : ℝ)| < 1)
    have hfun : quotient 0 = (fun t : ℝ => Real.arcsin t / t) := by
      funext t
      simp [quotient, increment, Real.arcsin_zero]
    rw [← hfun]
    have hvalue :
        (1 / Real.sqrt (1 - (0 : ℝ) ^ 2)) * 1 = 1 := by
      norm_num
    rw [← hvalue]
    exact hq

/-- Exercise 828_8, gap 12. -/
theorem gap12 :
    Filter.Tendsto (fun u : ℝ => u / Real.sin u)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  exact tendsto_div_sin_at_zero

/-- Exercise 828_8, gap 13. -/
theorem gap13 :
    Filter.Tendsto (fun t : ℝ => Real.arcsin t / t)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  exact gap11.mpr gap12

end

end ProofGap.Exercise828_8
