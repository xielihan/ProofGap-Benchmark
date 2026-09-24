import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1905

noncomputable section

def integrand (x : ℝ) : ℝ := x ^ 3 / (x ^ 8 + 3)
def primitive (x : ℝ) : ℝ :=
  1 / (4 * Real.sqrt 3) * Real.arctan (x ^ 4 / Real.sqrt 3)
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

theorem gap1 (x : ℝ) :
    integrand x =
      (1 / 4 : ℝ) * (1 / ((x ^ 4) ^ 2 + 3)) *
        deriv (fun y : ℝ => y ^ 4) x := by
  have hd : deriv (fun y : ℝ => y ^ 4) x = 4 * x ^ 3 := by
    simpa using ((hasDerivAt_id x).pow 4).deriv
  have hp : (x ^ 4) ^ 2 = x ^ 8 := by
    ring
  unfold integrand
  rw [hd, hp]
  ring

theorem gap2 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by
    positivity
  have hs_sq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hinner :
      HasDerivAt (fun y : ℝ => y ^ 4 / Real.sqrt 3)
        (4 * x ^ 3 / Real.sqrt 3) x := by
    simpa using
      (((hasDerivAt_id x).pow 4).div_const (Real.sqrt 3))
  have hden : 1 + (x ^ 4 / Real.sqrt 3) ^ 2 ≠ 0 := by
    positivity
  have hscale :
      Real.sqrt (3 : ℝ) ^ 2 *
          (1 + (x ^ 4 / Real.sqrt 3) ^ 2) =
        x ^ 8 + 3 := by
    calc
      Real.sqrt (3 : ℝ) ^ 2 *
            (1 + (x ^ 4 / Real.sqrt 3) ^ 2) =
          Real.sqrt (3 : ℝ) ^ 2 + (x ^ 4) ^ 2 := by
            field_simp [hs]
      _ = x ^ 8 + 3 := by
        rw [hs_sq]
        ring
  have halg :
      1 / (4 * Real.sqrt 3) *
          (1 / (1 + (x ^ 4 / Real.sqrt 3) ^ 2) *
            (4 * x ^ 3 / Real.sqrt 3)) =
        x ^ 3 / (x ^ 8 + 3) := by
    calc
      1 / (4 * Real.sqrt 3) *
            (1 / (1 + (x ^ 4 / Real.sqrt 3) ^ 2) *
              (4 * x ^ 3 / Real.sqrt 3)) =
          x ^ 3 /
            (Real.sqrt (3 : ℝ) ^ 2 *
              (1 + (x ^ 4 / Real.sqrt 3) ^ 2)) := by
                field_simp [hs, hden]
      _ = x ^ 3 / (x ^ 8 + 3) := by
        rw [hscale]
  have h :=
    ((Real.hasDerivAt_arctan (x ^ 4 / Real.sqrt 3)).comp x hinner).const_mul
      (1 / (4 * Real.sqrt 3))
  simpa only [primitive, integrand, halg] using h

theorem gap3 :
    Family integrand = Translates primitive := by
  ext F
  change IsAntiderivative F integrand ↔
    ∃ C, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    let G : ℝ → ℝ := fun y => F y - primitive y
    have hG : ∀ y, HasDerivAt G 0 y := by
      intro y
      dsimp [G]
      simpa using (hF y).sub (gap2 y)
    have hGdiff : Differentiable ℝ G := fun y => (hG y).differentiableAt
    have hGzero : ∀ y, deriv G y = 0 := fun y => (hG y).deriv
    refine ⟨G 0, ?_⟩
    intro x
    have hc : G x = G 0 :=
      is_const_of_deriv_eq_zero hGdiff hGzero x 0
    dsimp [G] at hc ⊢
    linarith
  · rintro ⟨C, hC⟩
    have hfun : F = fun y => primitive y + C := funext hC
    subst F
    intro x
    simpa only [add_zero] using (gap2 x).add_const C

end

end ProofGap.Exercise1905
