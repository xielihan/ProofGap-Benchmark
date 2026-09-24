import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1185

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def θ (x : ℝ) : ℝ := x / Real.sqrt 2

def y (C₁ C₂ C₃ C₄ x : ℝ) : ℝ :=
  Real.exp (θ x) * (C₁ * Real.cos (θ x) + C₂ * Real.sin (θ x)) +
    Real.exp (-θ x) * (C₃ * Real.cos (θ x) + C₄ * Real.sin (θ x))

def firstExpanded (C₁ C₂ C₃ C₄ x : ℝ) : ℝ :=
  Real.exp (θ x) *
      (C₁ / Real.sqrt 2 * Real.cos (θ x) +
        C₂ / Real.sqrt 2 * Real.sin (θ x) -
        C₁ / Real.sqrt 2 * Real.sin (θ x) +
        C₂ / Real.sqrt 2 * Real.cos (θ x)) +
    Real.exp (-θ x) *
      (-C₃ / Real.sqrt 2 * Real.cos (θ x) -
        C₄ / Real.sqrt 2 * Real.sin (θ x) -
        C₃ / Real.sqrt 2 * Real.sin (θ x) +
        C₄ / Real.sqrt 2 * Real.cos (θ x))

def secondExpanded (C₁ C₂ C₃ C₄ x : ℝ) : ℝ :=
  Real.exp (θ x) *
      (C₁ / 2 * Real.cos (θ x) +
        C₂ / 2 * Real.sin (θ x) -
        C₁ / 2 * Real.sin (θ x) +
        C₂ / 2 * Real.cos (θ x) -
        C₁ / 2 * Real.sin (θ x) +
        C₂ / 2 * Real.cos (θ x) -
        C₁ / 2 * Real.cos (θ x) -
        C₂ / 2 * Real.sin (θ x)) +
    Real.exp (-θ x) *
      (C₃ / 2 * Real.cos (θ x) +
        C₄ / 2 * Real.sin (θ x) +
        C₃ / 2 * Real.sin (θ x) -
        C₄ / 2 * Real.cos (θ x) +
        C₃ / 2 * Real.sin (θ x) -
        C₄ / 2 * Real.cos (θ x) -
        C₃ / 2 * Real.cos (θ x) -
        C₄ / 2 * Real.sin (θ x))

def secondClosed (C₁ C₂ C₃ C₄ x : ℝ) : ℝ :=
  Real.exp (θ x) * (C₂ * Real.cos (θ x) - C₁ * Real.sin (θ x)) +
    Real.exp (-θ x) * (C₃ * Real.sin (θ x) - C₄ * Real.cos (θ x))

def fourthClosed (C₁ C₂ C₃ C₄ x : ℝ) : ℝ :=
  Real.exp (θ x) * (-C₁ * Real.cos (θ x) - C₂ * Real.sin (θ x)) +
    Real.exp (-θ x) * (-C₃ * Real.cos (θ x) - C₄ * Real.sin (θ x))

private theorem deriv_y_formula (A B C D : ℝ) :
    deriv (y A B C D) =
      y ((A + B) / Real.sqrt 2) ((B - A) / Real.sqrt 2)
        ((D - C) / Real.sqrt 2) (-(C + D) / Real.sqrt 2) := by
  funext x
  have ht : HasDerivAt θ (1 / Real.sqrt 2) x := by
    simpa [θ] using (hasDerivAt_id x).div_const (Real.sqrt 2)
  have hnt : HasDerivAt (fun z : ℝ => -θ z) (-(1 / Real.sqrt 2)) x :=
    ht.neg
  have he : HasDerivAt (fun z : ℝ => Real.exp (θ z))
      (Real.exp (θ x) * (1 / Real.sqrt 2)) x :=
    (Real.hasDerivAt_exp (θ x)).comp x ht
  have hne0 := (Real.hasDerivAt_exp (-θ x)).comp x hnt
  have hne : HasDerivAt (fun z : ℝ => Real.exp (-θ z))
      (Real.exp (-θ x) * (-(1 / Real.sqrt 2))) x := by
    simpa only [Function.comp_apply] using hne0
  have hc : HasDerivAt (fun z : ℝ => Real.cos (θ z))
      (-Real.sin (θ x) * (1 / Real.sqrt 2)) x :=
    (Real.hasDerivAt_cos (θ x)).comp x ht
  have hs : HasDerivAt (fun z : ℝ => Real.sin (θ z))
      (Real.cos (θ x) * (1 / Real.sqrt 2)) x :=
    (Real.hasDerivAt_sin (θ x)).comp x ht
  apply HasDerivAt.deriv
  unfold y
  convert
    (he.mul ((hc.const_mul A).add (hs.const_mul B))).add
      (hne.mul ((hc.const_mul C).add (hs.const_mul D))) using 1 <;>
    simp only [Pi.add_apply] <;> ring

private theorem secondClosed_as_y (A B C D : ℝ) :
    secondClosed A B C D = y B (-A) (-D) C := by
  funext x
  unfold secondClosed y
  ring

theorem gap1 (C₁ C₂ C₃ C₄ x : ℝ) :
    iterDeriv 1 (y C₁ C₂ C₃ C₄) x =
      firstExpanded C₁ C₂ C₃ C₄ x := by
  change deriv (y C₁ C₂ C₃ C₄) x = firstExpanded C₁ C₂ C₃ C₄ x
  rw [deriv_y_formula]
  unfold y firstExpanded
  ring

theorem gap2 (C₁ C₂ C₃ C₄ x : ℝ) :
    iterDeriv 2 (y C₁ C₂ C₃ C₄) x =
      secondExpanded C₁ C₂ C₃ C₄ x := by
  change deriv (deriv (y C₁ C₂ C₃ C₄)) x = secondExpanded C₁ C₂ C₃ C₄ x
  rw [deriv_y_formula, deriv_y_formula]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have ha :
      (((C₁ + C₂) / Real.sqrt 2 + (C₂ - C₁) / Real.sqrt 2) /
          Real.sqrt 2) = C₂ := by
    field_simp [hsqrt_ne] <;> ring_nf <;> simp [hsqrt_sq]
  have hb :
      (((C₂ - C₁) / Real.sqrt 2 - (C₁ + C₂) / Real.sqrt 2) /
          Real.sqrt 2) = -C₁ := by
    field_simp [hsqrt_ne] <;> ring_nf <;> simp [hsqrt_sq]
  have hc :
      ((-(C₃ + C₄) / Real.sqrt 2 - (C₄ - C₃) / Real.sqrt 2) /
          Real.sqrt 2) = -C₄ := by
    field_simp [hsqrt_ne] <;> ring_nf <;> simp [hsqrt_sq]
  have hd :
      (-((C₄ - C₃) / Real.sqrt 2 + -(C₃ + C₄) / Real.sqrt 2) /
          Real.sqrt 2) = C₃ := by
    field_simp [hsqrt_ne] <;> ring_nf <;> simp [hsqrt_sq]
  rw [ha, hb, hc, hd]
  unfold y secondExpanded
  ring

theorem gap3 (C₁ C₂ C₃ C₄ x : ℝ) :
    iterDeriv 2 (y C₁ C₂ C₃ C₄) x =
      secondClosed C₁ C₂ C₃ C₄ x := by
  calc
    iterDeriv 2 (y C₁ C₂ C₃ C₄) x =
        secondExpanded C₁ C₂ C₃ C₄ x := gap2 C₁ C₂ C₃ C₄ x
    _ = secondClosed C₁ C₂ C₃ C₄ x := by
      unfold secondExpanded secondClosed
      ring

theorem gap4 (C₁ C₂ C₃ C₄ x : ℝ) :
    iterDeriv 4 (y C₁ C₂ C₃ C₄) x =
      iterDeriv 4 (y C₁ C₂ C₃ C₄) x := by
  rfl

theorem gap5 (C₁ C₂ C₃ C₄ x : ℝ) :
    iterDeriv 4 (y C₁ C₂ C₃ C₄) x =
      fourthClosed C₁ C₂ C₃ C₄ x := by
  change deriv (deriv (deriv (deriv (y C₁ C₂ C₃ C₄)))) x =
    fourthClosed C₁ C₂ C₃ C₄ x
  have hsecond :
      deriv (deriv (y C₁ C₂ C₃ C₄)) = secondClosed C₁ C₂ C₃ C₄ := by
    funext z
    exact gap3 C₁ C₂ C₃ C₄ z
  rw [hsecond, secondClosed_as_y]
  change iterDeriv 2 (y C₂ (-C₁) (-C₄) C₃) x =
    fourthClosed C₁ C₂ C₃ C₄ x
  rw [gap3]
  unfold secondClosed fourthClosed
  ring

theorem gap6 (C₁ C₂ C₃ C₄ x : ℝ) :
    fourthClosed C₁ C₂ C₃ C₄ x = -y C₁ C₂ C₃ C₄ x := by
  unfold fourthClosed y
  ring

theorem gap7 (C₁ C₂ C₃ C₄ x : ℝ) :
    iterDeriv 4 (y C₁ C₂ C₃ C₄) x = -y C₁ C₂ C₃ C₄ x := by
  calc
    iterDeriv 4 (y C₁ C₂ C₃ C₄) x =
        fourthClosed C₁ C₂ C₃ C₄ x := gap5 C₁ C₂ C₃ C₄ x
    _ = -y C₁ C₂ C₃ C₄ x := gap6 C₁ C₂ C₃ C₄ x

theorem gap8 (C₁ C₂ C₃ C₄ x : ℝ) :
    iterDeriv 4 (y C₁ C₂ C₃ C₄) x + y C₁ C₂ C₃ C₄ x = 0 := by
  rw [gap7]
  ring

theorem gap9 (C₁ C₂ C₃ C₄ x : ℝ) :
    iterDeriv 4 (y C₁ C₂ C₃ C₄) x + y C₁ C₂ C₃ C₄ x = 0 := by
  exact gap8 C₁ C₂ C₃ C₄ x

end

end ProofGap.Exercise1185
