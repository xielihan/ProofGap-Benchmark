import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1749

noncomputable section

def original (x : ℝ) : ℝ := Real.sin x ^ 4
def squared (x : ℝ) : ℝ := ((1 - Real.cos (2 * x)) / 2) ^ 2
def expanded (x : ℝ) : ℝ :=
  (1 / 4) * (1 - 2 * Real.cos (2 * x) +
    (1 + Real.cos (4 * x)) / 2)
def reduced (x : ℝ) : ℝ :=
  (1 / 8) * (3 - 4 * Real.cos (2 * x) + Real.cos (4 * x))
def primitive (x : ℝ) : ℝ :=
  (3 / 8) * x - (1 / 4) * Real.sin (2 * x) +
    (1 / 32) * Real.sin (4 * x)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem antiderivatives_eq_of_pointwise
    (f g : ℝ → ℝ) (h : ∀ x, f x = g x) :
    Antiderivatives f = Antiderivatives g := by
  ext F
  simp only [Antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hd⟩
    exact ⟨hF, fun x => (hd x).trans (h x)⟩
  · rintro ⟨hF, hd⟩
    exact ⟨hF, fun x => (hd x).trans (h x).symm⟩

private theorem original_eq_squared (x : ℝ) : original x = squared x := by
  unfold original squared
  rw [Real.cos_two_mul]
  have hs : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  calc
    Real.sin x ^ 4 = (Real.sin x ^ 2) ^ 2 := by ring
    _ = (1 - Real.cos x ^ 2) ^ 2 := by rw [hs]
    _ = ((1 - (2 * Real.cos x ^ 2 - 1)) / 2) ^ 2 := by ring

private theorem squared_eq_expanded (x : ℝ) : squared x = expanded x := by
  have hc : Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
    calc
      Real.cos (4 * x) = Real.cos (2 * (2 * x)) := by
        congr 1
        ring
      _ = 2 * Real.cos (2 * x) ^ 2 - 1 := Real.cos_two_mul (2 * x)
  unfold squared expanded
  rw [hc]
  ring

private theorem expanded_eq_reduced (x : ℝ) : expanded x = reduced x := by
  unfold expanded reduced
  ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (reduced x) x := by
  have hlin : HasDerivAt (fun y : ℝ => (3 / 8) * y) (3 / 8) x := by
    convert (hasDerivAt_id x).const_mul (3 / 8) using 1 <;> ring
  have htwo :
      HasDerivAt (fun y : ℝ => Real.sin (2 * y))
        (2 * Real.cos (2 * x)) x := by
    convert (Real.hasDerivAt_sin (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2) using 1 <;> ring
  have hfour :
      HasDerivAt (fun y : ℝ => Real.sin (4 * y))
        (4 * Real.cos (4 * x)) x := by
    convert (Real.hasDerivAt_sin (4 * x)).comp x
      ((hasDerivAt_id x).const_mul 4) using 1 <;> ring
  unfold primitive reduced
  convert (hlin.sub (htwo.const_mul (1 / 4))).add
    (hfour.const_mul (1 / 32)) using 1 <;> ring

theorem gap1 : Antiderivatives original = Antiderivatives squared := by
  exact antiderivatives_eq_of_pointwise original squared original_eq_squared

theorem gap2 : Antiderivatives squared = Antiderivatives expanded := by
  exact antiderivatives_eq_of_pointwise squared expanded squared_eq_expanded

theorem gap3 : Antiderivatives original = Antiderivatives expanded := by
  exact gap1.trans gap2

theorem gap4 : Antiderivatives original = Antiderivatives reduced := by
  exact gap3.trans
    (antiderivatives_eq_of_pointwise expanded reduced expanded_eq_reduced)

theorem gap5 : Antiderivatives reduced = PrimitiveFamily primitive := by
  ext F
  simp only [Antiderivatives, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hz : ∀ y, HasDerivAt (fun z => F z - primitive z) 0 y := by
      intro y
      convert (hF y).hasDerivAt.sub (primitive_hasDerivAt y) using 1
      rw [hderiv y]
      ring
    have hdiff : Differentiable ℝ (fun z => F z - primitive z) :=
      fun y => (hz y).differentiableAt
    have hzero : ∀ y, deriv (fun z => F z - primitive z) y = 0 :=
      fun y => (hz y).deriv
    have hconst :
        (fun z => F z - primitive z) x =
          (fun z => F z - primitive z) 0 :=
      is_const_of_deriv_eq_zero hdiff hzero x 0
    linarith [hconst]
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => primitive x + C := funext hC
    rw [hfun]
    constructor
    · intro x
      simpa [add_comm] using
        ((primitive_hasDerivAt x).const_add C).differentiableAt
    · intro x
      simpa [add_comm] using
        ((primitive_hasDerivAt x).const_add C).deriv

theorem gap6 : Antiderivatives original = PrimitiveFamily primitive := by
  exact gap4.trans gap5

end
end ProofGap.Exercise1749
