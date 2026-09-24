import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1746

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.sin (2 * x - Real.pi / 6) * Real.cos (3 * x + Real.pi / 4)
def reduced (x : ℝ) : ℝ :=
  (1 / 2) * (Real.sin (5 * x + Real.pi / 12) -
    Real.sin (x + 5 * Real.pi / 12))
def primitive (x : ℝ) : ℝ :=
  -(1 / 10) * Real.cos (5 * x + Real.pi / 12) +
    (1 / 2) * Real.cos (x + 5 * Real.pi / 12)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem original_eq_reduced : original = reduced := by
  funext x
  unfold original reduced
  have hsum :
      (2 * x - Real.pi / 6) + (3 * x + Real.pi / 4) =
        5 * x + Real.pi / 12 := by
    ring
  have hdiff :
      (2 * x - Real.pi / 6) - (3 * x + Real.pi / 4) =
        -(x + 5 * Real.pi / 12) := by
    ring
  calc
    Real.sin (2 * x - Real.pi / 6) * Real.cos (3 * x + Real.pi / 4) =
        (1 / 2) *
          (Real.sin ((2 * x - Real.pi / 6) + (3 * x + Real.pi / 4)) +
            Real.sin ((2 * x - Real.pi / 6) - (3 * x + Real.pi / 4))) := by
      rw [Real.sin_add (2 * x - Real.pi / 6) (3 * x + Real.pi / 4),
        Real.sin_sub (2 * x - Real.pi / 6) (3 * x + Real.pi / 4)]
      ring
    _ = (1 / 2) *
        (Real.sin (5 * x + Real.pi / 12) -
          Real.sin (x + 5 * Real.pi / 12)) := by
      rw [hsum, hdiff, Real.sin_neg]
      ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (reduced x) x := by
  have hlin5 : HasDerivAt (fun y : ℝ => 5 * y + Real.pi / 12) 5 x := by
    convert ((hasDerivAt_id x).const_mul (5 : ℝ)).add_const (Real.pi / 12) using 1 <;> ring
  have hlin1 : HasDerivAt (fun y : ℝ => y + 5 * Real.pi / 12) 1 x := by
    convert (hasDerivAt_id x).add_const (5 * Real.pi / 12) using 1 <;> ring
  have hcos5 := (Real.hasDerivAt_cos (5 * x + Real.pi / 12)).comp x hlin5
  have hcos1 := (Real.hasDerivAt_cos (x + 5 * Real.pi / 12)).comp x hlin1
  unfold primitive reduced
  convert
    (hcos5.const_mul (-(1 / 10 : ℝ))).add
      (hcos1.const_mul (1 / 2 : ℝ)) using 1 <;> ring

theorem gap1 : Antiderivatives original = Antiderivatives reduced := by
  exact congrArg Antiderivatives original_eq_reduced

theorem gap2 : Antiderivatives original = PrimitiveFamily primitive := by
  ext F
  simp only [Antiderivatives, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro hF
    let G : ℝ → ℝ := fun y => F y - primitive y
    have hGhas : ∀ x, HasDerivAt G 0 x := by
      intro x
      have hx := (hF.1 x).hasDerivAt.sub (primitive_hasDerivAt x)
      rw [hF.2 x, congrFun original_eq_reduced x] at hx
      simpa [G] using hx
    have hGdiff : Differentiable ℝ G := fun x => (hGhas x).differentiableAt
    have hGder : ∀ x, deriv G x = 0 := fun x => (hGhas x).deriv
    have hconst := is_const_of_deriv_eq_zero hGdiff hGder
    refine ⟨G 0, ?_⟩
    intro x
    have hx : G x = G 0 := @hconst x 0
    dsimp [G] at hx ⊢
    calc
      F x = (F x - primitive x) + primitive x := by ring
      _ = (F 0 - primitive 0) + primitive x := by rw [hx]
      _ = primitive x + (F 0 - primitive 0) := by ring
  · rintro ⟨C, hC⟩
    have hFC : F = fun x => primitive x + C := funext hC
    subst F
    constructor
    · exact fun x => ((primitive_hasDerivAt x).add_const C).differentiableAt
    · intro x
      calc
        deriv (fun y => primitive y + C) x = reduced x :=
          ((primitive_hasDerivAt x).add_const C).deriv
        _ = original x := (congrFun original_eq_reduced x).symm

end
end ProofGap.Exercise1746
