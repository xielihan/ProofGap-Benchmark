import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1761

noncomputable section

def integrand (x : ℝ) : ℝ := Real.sinh x ^ 2
def primitive (x : ℝ) : ℝ := (1 / 4 : ℝ) * Real.sinh (2 * x) - x / 2
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

theorem gap1 (x : ℝ) :
    integrand x = (Real.cosh (2 * x) - 1) / 2 := by
  unfold integrand
  rw [Real.cosh_two_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem gap2 (x : ℝ) :
    HasDerivAt primitive ((Real.cosh (2 * x) - 1) / 2) x := by
  unfold primitive
  have hinner : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hsinh :
      HasDerivAt (fun y : ℝ => Real.sinh (2 * y))
        (2 * Real.cosh (2 * x)) x := by
    convert (Real.hasDerivAt_sinh (2 * x)).comp x hinner using 1 <;> ring
  convert
    (hsinh.const_mul (1 / 4 : ℝ)).sub ((hasDerivAt_id x).div_const 2)
      using 1 <;> ring

theorem gap3 :
    Family integrand = Translates primitive := by
  ext F
  change IsAntiderivative F integrand ↔ ∃ C, ∀ x, F x = primitive x + C
  have hp : ∀ x, HasDerivAt primitive (integrand x) x := by
    intro x
    simpa only [gap1 x] using gap2 x
  constructor
  · intro hF
    let G : ℝ → ℝ := fun x => F x - primitive x
    have hG : ∀ x, HasDerivAt G 0 x := by
      intro x
      simpa [G] using (hF x).sub (hp x)
    have hd : Differentiable ℝ G := fun x => (hG x).differentiableAt
    have hGx : ∀ x, G x = G 0 := by
      intro x
      by_cases hx : x = 0
      · simpa [hx]
      · rcases lt_or_gt_of_ne hx with hlt | hgt
        · obtain ⟨c, _hc, hslope⟩ :=
            exists_deriv_eq_slope (f := G) hlt
              hd.continuous.continuousOn hd.differentiableOn
          have hcderiv : deriv G c = 0 := (hG c).deriv
          have hq : (G 0 - G x) / (0 - x) = 0 := by
            linarith
          have hden : (0 : ℝ) - x ≠ 0 := by
            linarith
          field_simp [hden] at hq
          linarith
        · obtain ⟨c, _hc, hslope⟩ :=
            exists_deriv_eq_slope (f := G) hgt
              hd.continuous.continuousOn hd.differentiableOn
          have hcderiv : deriv G c = 0 := (hG c).deriv
          have hq : (G x - G 0) / (x - 0) = 0 := by
            linarith
          have hden : x - (0 : ℝ) ≠ 0 := by
            linarith
          field_simp [hden] at hq
          linarith
    refine ⟨G 0, ?_⟩
    intro x
    have hx := hGx x
    dsimp [G] at hx ⊢
    linarith
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => primitive x + C := funext hC
    intro x
    rw [hfun]
    exact (hp x).add_const C

end

end ProofGap.Exercise1761
