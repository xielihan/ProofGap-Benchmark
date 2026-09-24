import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2163

noncomputable section

def coth (x : ℝ) := Real.cosh x / Real.sinh x
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def denominator (x : ℝ) :=
  (Real.exp (x + 1) + 1) ^ 2 - (Real.exp (x - 1) + 1) ^ 2
def integrand (x : ℝ) := 1 / denominator x
def differenceProduct (x : ℝ) :=
  1 / ((Real.exp (x + 1) - Real.exp (x - 1)) *
    (Real.exp (x + 1) + Real.exp (x - 1) + 2))
def exponentialFactorization (x : ℝ) :=
  1 / (Real.exp (2 * x) *
    (Real.exp 1 - Real.exp (-1)) *
    (Real.exp 1 + Real.exp (-1) + 2 * Real.exp (-x)))
def hyperbolicFactorization (x : ℝ) :=
  1 / (Real.exp (2 * x) * 2 * Real.sinh 1 *
    (2 * Real.cosh 1 + 2 * Real.exp (-x)))
def simplified (x : ℝ) :=
  1 / (4 * Real.exp x * Real.sinh 1 *
    (1 + Real.exp x * Real.cosh 1))
def ReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives
      (fun x => 1 / Real.exp x -
        Real.cosh 1 / (1 + Real.exp x * Real.cosh 1)),
    ∀ x, F x = 1 / (4 * Real.sinh 1) * G x}
def primitive (x : ℝ) :=
  -Real.exp (-x) / (4 * Real.sinh 1) -
    coth 1 / 4 * (x - Real.log (1 + Real.exp x * Real.cosh 1))

private lemma sinh_one_pos : 0 < Real.sinh 1 := by
  rw [Real.sinh_eq]
  have h := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 1 by norm_num)
  linarith

private lemma sinh_one_ne_zero : Real.sinh 1 ≠ 0 :=
  ne_of_gt sinh_one_pos

private lemma integrand_eq_differenceProduct :
    integrand = differenceProduct := by
  funext x
  unfold integrand differenceProduct denominator
  congr 1
  ring

private lemma differenceProduct_eq_exponentialFactorization :
    differenceProduct = exponentialFactorization := by
  funext x
  unfold differenceProduct exponentialFactorization
  congr 1
  simp only [sub_eq_add_neg, Real.exp_add]
  have h2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  rw [h2]
  simp only [Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  <;> ring

private lemma exponentialFactorization_eq_hyperbolicFactorization :
    exponentialFactorization = hyperbolicFactorization := by
  funext x
  unfold exponentialFactorization hyperbolicFactorization
  congr 1
  rw [Real.sinh_eq, Real.cosh_eq]
  ring

private lemma hyperbolicFactorization_eq_simplified :
    hyperbolicFactorization = simplified := by
  funext x
  unfold hyperbolicFactorization simplified
  congr 1
  have h2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  rw [h2, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  <;> ring

private lemma simplified_eq_scaled (x : ℝ) :
    simplified x =
      1 / (4 * Real.sinh 1) *
        (1 / Real.exp x -
          Real.cosh 1 / (1 + Real.exp x * Real.cosh 1)) := by
  have hu : 1 + Real.exp x * Real.cosh 1 ≠ 0 := by
    positivity
  unfold simplified
  field_simp [Real.exp_ne_zero x, sinh_one_ne_zero, hu]
  <;> ring

private lemma primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hu_ne : 1 + Real.exp x * Real.cosh 1 ≠ 0 := by
    positivity
  have hnegexp :
      HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa using
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
  have hu :
      HasDerivAt
        (fun y : ℝ => 1 + Real.exp y * Real.cosh 1)
        (Real.exp x * Real.cosh 1) x :=
    ((Real.hasDerivAt_exp x).mul_const (Real.cosh 1)).const_add 1
  have hinner :
      HasDerivAt
        (fun y : ℝ =>
          y - Real.log (1 + Real.exp y * Real.cosh 1))
        (1 - (Real.exp x * Real.cosh 1) /
          (1 + Real.exp x * Real.cosh 1)) x :=
    (hasDerivAt_id x).sub (hu.log hu_ne)
  have hd :
      HasDerivAt primitive
        (Real.exp (-x) / (4 * Real.sinh 1) -
          coth 1 / 4 *
            (1 - (Real.exp x * Real.cosh 1) /
              (1 + Real.exp x * Real.cosh 1))) x := by
    change
      HasDerivAt
        (fun y : ℝ =>
          -Real.exp (-y) / (4 * Real.sinh 1) -
            coth 1 / 4 *
              (y - Real.log (1 + Real.exp y * Real.cosh 1)))
        (Real.exp (-x) / (4 * Real.sinh 1) -
          coth 1 / 4 *
            (1 - (Real.exp x * Real.cosh 1) /
              (1 + Real.exp x * Real.cosh 1))) x
    simpa using
      (hnegexp.neg.div_const (4 * Real.sinh 1)).sub
        (hinner.const_mul (coth 1 / 4))
  have hvalue :
      Real.exp (-x) / (4 * Real.sinh 1) -
          coth 1 / 4 *
            (1 - (Real.exp x * Real.cosh 1) /
              (1 + Real.exp x * Real.cosh 1)) =
        simplified x := by
    unfold simplified coth
    rw [Real.exp_neg]
    field_simp [sinh_one_ne_zero, hu_ne, Real.exp_ne_zero x]
    <;> ring
  have hp : HasDerivAt primitive (simplified x) x := by
    rw [← hvalue]
    exact hd
  rw [integrand_eq_differenceProduct,
    differenceProduct_eq_exponentialFactorization,
    exponentialFactorization_eq_hyperbolicFactorization,
    hyperbolicFactorization_eq_simplified]
  exact hp

theorem gap1 :
    Antiderivatives integrand =
      Antiderivatives differenceProduct := by
  rw [integrand_eq_differenceProduct]
theorem gap2 :
    Antiderivatives integrand =
      Antiderivatives exponentialFactorization := by
  rw [integrand_eq_differenceProduct,
    differenceProduct_eq_exponentialFactorization]
theorem gap3 :
    Antiderivatives integrand =
      Antiderivatives hyperbolicFactorization := by
  rw [integrand_eq_differenceProduct,
    differenceProduct_eq_exponentialFactorization,
    exponentialFactorization_eq_hyperbolicFactorization]
theorem gap4 :
    Antiderivatives integrand = Antiderivatives simplified := by
  rw [integrand_eq_differenceProduct,
    differenceProduct_eq_exponentialFactorization,
    exponentialFactorization_eq_hyperbolicFactorization,
    hyperbolicFactorization_eq_simplified]
theorem gap5 :
    Antiderivatives simplified = ReductionFamily := by
  ext F
  change
    (∀ x, HasDerivAt F (simplified x) x) ↔
      ∃ G,
        (∀ x, HasDerivAt G
          (1 / Real.exp x -
            Real.cosh 1 / (1 + Real.exp x * Real.cosh 1)) x) ∧
        ∀ x, F x = 1 / (4 * Real.sinh 1) * G x
  constructor
  · intro hF
    let G : ℝ → ℝ := fun x => 4 * Real.sinh 1 * F x
    refine ⟨G, ?_, ?_⟩
    · intro x
      have hd := (hF x).const_mul (4 * Real.sinh 1)
      have hderiv :
          4 * Real.sinh 1 * simplified x =
            1 / Real.exp x -
              Real.cosh 1 / (1 + Real.exp x * Real.cosh 1) := by
        rw [simplified_eq_scaled x]
        field_simp [sinh_one_ne_zero]
      rw [← hderiv]
      exact hd
    · intro x
      dsimp [G]
      field_simp [sinh_one_ne_zero]
  · rintro ⟨G, hG, hFG⟩
    rw [show F = fun y => 1 / (4 * Real.sinh 1) * G y from funext hFG]
    intro x
    have hd := (hG x).const_mul (1 / (4 * Real.sinh 1))
    rw [simplified_eq_scaled x]
    exact hd
theorem gap6 :
    Antiderivatives integrand = ReductionFamily := by
  exact gap4.trans gap5
theorem gap7 :
    Antiderivatives integrand = PrimitiveFamily primitive := by
  ext F
  change
    (∀ x, HasDerivAt F (integrand x) x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    have hzero : ∀ x,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa using (hF x).sub (primitive_hasDerivAt x)
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y => F y - primitive y) x = 0 :=
      fun x => (hzero x).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc := is_const_of_deriv_eq_zero hdiff hderiv x 0
    linarith
  · rintro ⟨C, hC⟩
    rw [show F = fun y => primitive y + C from funext hC]
    intro x
    exact (primitive_hasDerivAt x).add_const C

end
end ProofGap.Exercise2163
