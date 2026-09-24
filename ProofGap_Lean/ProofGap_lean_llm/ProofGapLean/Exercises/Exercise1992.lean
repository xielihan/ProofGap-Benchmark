import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1992

noncomputable section

def originalIntegrand (x : ℝ) := Real.sin x ^ 6
def powerReducedIntegrand (x : ℝ) :=
  ((1 - Real.cos (2 * x)) / 2) ^ 3
def expandedIntegrand (x : ℝ) :=
  1 - 3 * Real.cos (2 * x) +
    3 * Real.cos (2 * x) ^ 2 - Real.cos (2 * x) ^ 3
def averageCosineIntegrand (x : ℝ) :=
  (1 + Real.cos (4 * x)) / 2
def cubicCosineIntegrand (x : ℝ) :=
  (1 - Real.sin (2 * x) ^ 2) * Real.cos (2 * x)
def sineSubstitutionIntegrand (x : ℝ) :=
  (1 - Real.sin (2 * x) ^ 2) *
    deriv (fun y : ℝ => Real.sin (2 * y)) x
def primitiveExpanded (x : ℝ) :=
  5 * x / 16 - 3 / 16 * Real.sin (2 * x) +
    3 / 64 * Real.sin (4 * x) -
    1 / 16 * Real.sin (2 * x) +
    1 / 48 * Real.sin (2 * x) ^ 3
def primitiveSimplified (x : ℝ) :=
  5 * x / 16 - 1 / 4 * Real.sin (2 * x) +
    3 / 64 * Real.sin (4 * x) +
    1 / 48 * Real.sin (2 * x) ^ 3
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def ScaledExpandedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives expandedIntegrand,
    ∀ x, F x = 1 / 8 * G x}
def FirstDecompositionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives averageCosineIntegrand,
    ∃ H ∈ Antiderivatives cubicCosineIntegrand,
      ∀ x,
        F x = x / 8 - 3 / 16 * Real.sin (2 * x) +
          3 / 8 * G x - 1 / 8 * H x}
def SecondDecompositionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives sineSubstitutionIntegrand,
    ∀ x,
      F x = x / 8 - 3 / 16 * Real.sin (2 * x) +
        3 * x / 16 + 3 / 64 * Real.sin (4 * x) - 1 / 16 * G x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem original_power_eq (x : ℝ) :
    originalIntegrand x = powerReducedIntegrand x := by
  unfold originalIntegrand powerReducedIntegrand
  have hbase : (1 - Real.cos (2 * x)) / 2 = Real.sin x ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hbase]
  ring

private theorem expanded_eq_eight_power (x : ℝ) :
    expandedIntegrand x = 8 * powerReducedIntegrand x := by
  unfold expandedIntegrand powerReducedIntegrand
  ring

private theorem scaled_expanded_eq (x : ℝ) :
    originalIntegrand x = 1 / 8 * expandedIntegrand x := by
  rw [original_power_eq, expanded_eq_eight_power]
  ring

private theorem hasDerivAt_sin_two (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (2 * y))
      (2 * Real.cos (2 * x)) x := by
  convert
    (Real.hasDerivAt_sin (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2) using 1 <;> ring

private theorem hasDerivAt_sin_four (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (4 * y))
      (4 * Real.cos (4 * x)) x := by
  convert
    (Real.hasDerivAt_sin (4 * x)).comp x
      ((hasDerivAt_id x).const_mul 4) using 1 <;> ring

private def averagePrimitive (x : ℝ) :=
  x / 2 + Real.sin (4 * x) / 8

private def cubicPrimitive (x : ℝ) :=
  Real.sin (2 * x) / 2 - Real.sin (2 * x) ^ 3 / 6

private def substitutionPrimitive (x : ℝ) :=
  Real.sin (2 * x) - Real.sin (2 * x) ^ 3 / 3

private theorem hasDerivAt_averagePrimitive (x : ℝ) :
    HasDerivAt averagePrimitive (averageCosineIntegrand x) x := by
  unfold averagePrimitive averageCosineIntegrand
  convert
    ((hasDerivAt_id x).div_const 2).add
      ((hasDerivAt_sin_four x).div_const 8) using 1 <;> ring

private theorem hasDerivAt_cubicPrimitive (x : ℝ) :
    HasDerivAt cubicPrimitive (cubicCosineIntegrand x) x := by
  unfold cubicPrimitive cubicCosineIntegrand
  have h := hasDerivAt_sin_two x
  convert (h.div_const 2).sub ((h.pow 3).div_const 6) using 1 <;> ring

private theorem hasDerivAt_substitutionPrimitive (x : ℝ) :
    HasDerivAt substitutionPrimitive (sineSubstitutionIntegrand x) x := by
  have h := hasDerivAt_sin_two x
  have hd : deriv (fun y : ℝ => Real.sin (2 * y)) x =
      2 * Real.cos (2 * x) := h.deriv
  unfold substitutionPrimitive sineSubstitutionIntegrand
  rw [hd]
  convert h.sub ((h.pow 3).div_const 3) using 1 <;> ring

private theorem first_formula_eq (x : ℝ) :
    x / 8 - 3 / 16 * Real.sin (2 * x) +
        3 / 8 * averagePrimitive x - 1 / 8 * cubicPrimitive x =
      primitiveSimplified x := by
  unfold averagePrimitive cubicPrimitive primitiveSimplified
  ring

private theorem second_formula_eq (x : ℝ) :
    x / 8 - 3 / 16 * Real.sin (2 * x) +
        3 * x / 16 + 3 / 64 * Real.sin (4 * x) -
        1 / 16 * substitutionPrimitive x =
      primitiveSimplified x := by
  unfold substitutionPrimitive primitiveSimplified
  ring

private theorem first_derivative_value (x : ℝ) :
    1 / 8 - 3 / 16 * (2 * Real.cos (2 * x)) +
        3 / 8 * averageCosineIntegrand x -
        1 / 8 * cubicCosineIntegrand x =
      originalIntegrand x := by
  rw [scaled_expanded_eq]
  unfold averageCosineIntegrand cubicCosineIntegrand expandedIntegrand
  have hcos4 : Real.cos (4 * x) =
      2 * Real.cos (2 * x) ^ 2 - 1 := by
    convert Real.cos_two_mul (2 * x) using 1 <;> ring
  have hsin2 : Real.sin (2 * x) ^ 2 =
      1 - Real.cos (2 * x) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * x)]
  rw [hcos4, hsin2]
  ring

private theorem hasDerivAt_primitiveSimplified (x : ℝ) :
    HasDerivAt primitiveSimplified (originalIntegrand x) x := by
  have h :
      HasDerivAt
        (fun y : ℝ =>
          y / 8 - 3 / 16 * Real.sin (2 * y) +
            3 / 8 * averagePrimitive y - 1 / 8 * cubicPrimitive y)
        (1 / 8 - 3 / 16 * (2 * Real.cos (2 * x)) +
          3 / 8 * averageCosineIntegrand x -
          1 / 8 * cubicCosineIntegrand x) x := by
    convert
      ((((hasDerivAt_id x).div_const 8).sub
          ((hasDerivAt_sin_two x).const_mul (3 / 16))).add
          ((hasDerivAt_averagePrimitive x).const_mul (3 / 8))).sub
          ((hasDerivAt_cubicPrimitive x).const_mul (1 / 8)) using 1 <;> ring
  rw [first_derivative_value x] at h
  convert h using 1
  funext y
  exact (first_formula_eq y).symm

private theorem primitiveExpanded_eq_simplified :
    primitiveExpanded = primitiveSimplified := by
  funext x
  unfold primitiveExpanded primitiveSimplified
  ring

private theorem hasDerivAt_primitiveExpanded (x : ℝ) :
    HasDerivAt primitiveExpanded (originalIntegrand x) x := by
  rw [primitiveExpanded_eq_simplified]
  exact hasDerivAt_primitiveSimplified x

private theorem antiderivatives_eq_primitive
    {f p : ℝ → ℝ} (hp : ∀ x, HasDerivAt p (f x) x) :
    Antiderivatives f = PrimitiveFamily p := by
  ext F
  change (∀ x, HasDerivAt F (f x) x) ↔
    ∃ C : ℝ, ∀ x, F x = p x + C
  constructor
  · intro hF
    have hzero : ∀ x,
        HasDerivAt (fun y : ℝ => F y - p y) 0 x := by
      intro x
      simpa using (hF x).sub (hp x)
    have hdiff : Differentiable ℝ (fun y : ℝ => F y - p y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y : ℝ => F y - p y) x = 0 :=
      fun x => (hzero x).deriv
    have hc := is_const_of_deriv_eq_zero hdiff hderiv
    refine ⟨F 0 - p 0, ?_⟩
    intro x
    have hx : F x - p x = F 0 - p 0 := hc x 0
    linarith
  · rintro ⟨C, hF⟩
    have hfun : F = fun y => p y + C := funext hF
    rw [hfun]
    intro x
    exact (hp x).add_const C

private theorem firstFamily_eq_primitive :
    FirstDecompositionFamily = PrimitiveFamily primitiveSimplified := by
  ext F
  simp only [FirstDecompositionFamily, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, H, hH, hF⟩
    rw [antiderivatives_eq_primitive hasDerivAt_averagePrimitive] at hG
    rw [antiderivatives_eq_primitive hasDerivAt_cubicPrimitive] at hH
    rcases hG with ⟨CG, hG⟩
    rcases hH with ⟨CH, hH⟩
    refine ⟨3 / 8 * CG - 1 / 8 * CH, ?_⟩
    intro x
    calc
      F x = x / 8 - 3 / 16 * Real.sin (2 * x) +
          3 / 8 * G x - 1 / 8 * H x := hF x
      _ = (x / 8 - 3 / 16 * Real.sin (2 * x) +
          3 / 8 * averagePrimitive x - 1 / 8 * cubicPrimitive x) +
          (3 / 8 * CG - 1 / 8 * CH) := by
            rw [hG x, hH x]
            ring
      _ = primitiveSimplified x + (3 / 8 * CG - 1 / 8 * CH) := by
            rw [first_formula_eq]
  · rintro ⟨C, hF⟩
    refine ⟨fun x => averagePrimitive x + 8 / 3 * C, ?_,
      fun x => cubicPrimitive x, ?_, ?_⟩
    · intro x
      exact (hasDerivAt_averagePrimitive x).add_const (8 / 3 * C)
    · intro x
      exact hasDerivAt_cubicPrimitive x
    · intro x
      calc
        F x = primitiveSimplified x + C := hF x
        _ = (x / 8 - 3 / 16 * Real.sin (2 * x) +
            3 / 8 * averagePrimitive x - 1 / 8 * cubicPrimitive x) + C := by
              rw [first_formula_eq]
        _ = x / 8 - 3 / 16 * Real.sin (2 * x) +
            3 / 8 * (averagePrimitive x + 8 / 3 * C) -
            1 / 8 * cubicPrimitive x := by ring

private theorem secondFamily_eq_primitive :
    SecondDecompositionFamily = PrimitiveFamily primitiveSimplified := by
  ext F
  simp only [SecondDecompositionFamily, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hF⟩
    rw [antiderivatives_eq_primitive hasDerivAt_substitutionPrimitive] at hG
    rcases hG with ⟨CG, hG⟩
    refine ⟨-1 / 16 * CG, ?_⟩
    intro x
    calc
      F x = x / 8 - 3 / 16 * Real.sin (2 * x) +
          3 * x / 16 + 3 / 64 * Real.sin (4 * x) - 1 / 16 * G x := hF x
      _ = (x / 8 - 3 / 16 * Real.sin (2 * x) +
          3 * x / 16 + 3 / 64 * Real.sin (4 * x) -
          1 / 16 * substitutionPrimitive x) + (-1 / 16 * CG) := by
            rw [hG x]
            ring
      _ = primitiveSimplified x + (-1 / 16 * CG) := by
            rw [second_formula_eq]
  · rintro ⟨C, hF⟩
    refine ⟨fun x => substitutionPrimitive x - 16 * C, ?_, ?_⟩
    · intro x
      exact (hasDerivAt_substitutionPrimitive x).sub_const (16 * C)
    · intro x
      calc
        F x = primitiveSimplified x + C := hF x
        _ = (x / 8 - 3 / 16 * Real.sin (2 * x) +
            3 * x / 16 + 3 / 64 * Real.sin (4 * x) -
            1 / 16 * substitutionPrimitive x) + C := by
              rw [second_formula_eq]
        _ = x / 8 - 3 / 16 * Real.sin (2 * x) +
            3 * x / 16 + 3 / 64 * Real.sin (4 * x) -
            1 / 16 * (substitutionPrimitive x - 16 * C) := by ring

theorem gap1 :
    Antiderivatives originalIntegrand =
      Antiderivatives powerReducedIntegrand := by
  ext F
  simp only [Antiderivatives, Set.mem_setOf_eq]
  constructor <;> intro h x
  · simpa only [original_power_eq] using h x
  · simpa only [original_power_eq] using h x
theorem gap2 :
    Antiderivatives powerReducedIntegrand =
      ScaledExpandedFamily := by
  ext F
  simp only [Antiderivatives, ScaledExpandedFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => 8 * F y, ?_, ?_⟩
    · intro x
      have h := (hF x).const_mul 8
      convert h using 1
      rw [expanded_eq_eight_power]
    · intro x
      ring
  · rintro ⟨G, hG, hFG⟩
    have hfun : F = fun y => 1 / 8 * G y := funext hFG
    rw [hfun]
    intro x
    have h := (hG x).const_mul (1 / 8)
    convert h using 1
    rw [expanded_eq_eight_power]
    ring
theorem gap3 :
    Antiderivatives originalIntegrand =
      ScaledExpandedFamily := by
  exact gap1.trans gap2
theorem gap4 :
    Antiderivatives originalIntegrand =
      FirstDecompositionFamily := by
  exact
    (antiderivatives_eq_primitive hasDerivAt_primitiveSimplified).trans
      firstFamily_eq_primitive.symm
theorem gap5 :
    Antiderivatives originalIntegrand =
      SecondDecompositionFamily := by
  exact
    (antiderivatives_eq_primitive hasDerivAt_primitiveSimplified).trans
      secondFamily_eq_primitive.symm
theorem gap6 :
    Antiderivatives originalIntegrand =
      PrimitiveFamily primitiveExpanded := by
  exact antiderivatives_eq_primitive hasDerivAt_primitiveExpanded
theorem gap7 :
    Antiderivatives originalIntegrand =
      PrimitiveFamily primitiveSimplified := by
  exact antiderivatives_eq_primitive hasDerivAt_primitiveSimplified

end
end ProofGap.Exercise1992
