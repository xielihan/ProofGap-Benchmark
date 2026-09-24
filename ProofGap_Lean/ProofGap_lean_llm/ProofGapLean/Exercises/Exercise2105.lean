import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2105
noncomputable section

def integrand (x : ℝ) := x * Real.arctan (x + 1)
def squareDifferential (x : ℝ) :=
  Real.arctan (x + 1) * deriv (fun y : ℝ => y ^ 2) x
def rational (x : ℝ) := x ^ 2 / (x ^ 2 + 2 * x + 2)
def splitRational (x : ℝ) := 1 - (2 * x + 2) / (x ^ 2 + 2 * x + 2)
def primitive (x : ℝ) :=
  (1 / 2 : ℝ) * x ^ 2 * Real.arctan (x + 1) -
    x / 2 + (1 / 2 : ℝ) * Real.log (x ^ 2 + 2 * x + 2)

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def HalfFamily (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f, ∀ x, F x = (1 / 2 : ℝ) * A x}
def ByPartsFamily (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f,
    ∀ x, F x =
      (1 / 2 : ℝ) * x ^ 2 * Real.arctan (x + 1) - (1 / 2 : ℝ) * A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x, F x = p x + C}

private lemma quadratic_pos (x : ℝ) : 0 < x ^ 2 + 2 * x + 2 := by
  nlinarith [sq_nonneg (x + 1)]

private lemma hasDerivAt_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  simpa using ((hasDerivAt_id x).pow 2)

private lemma square_deriv (x : ℝ) :
    deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
  exact (hasDerivAt_sq x).deriv

private lemma rational_eq_split (x : ℝ) : rational x = splitRational x := by
  have hn : x ^ 2 + 2 * x + 2 ≠ 0 := ne_of_gt (quadratic_pos x)
  unfold rational splitRational
  apply (div_eq_iff hn).2
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hn]
  ring

private lemma hasDerivAt_squareArctan (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 * Real.arctan (y + 1))
      (squareDifferential x + rational x) x := by
  have hatan :
      HasDerivAt (fun y : ℝ => Real.arctan (y + 1))
        (1 / (1 + (x + 1) ^ 2)) x := by
    simpa [Function.comp_def] using
      ((Real.hasDerivAt_arctan (x + 1)).comp x
        ((hasDerivAt_id x).add_const 1))
  have hden : 1 + (x + 1) ^ 2 = x ^ 2 + 2 * x + 2 := by
    ring
  rw [hden] at hatan
  have hmul := (hasDerivAt_sq x).mul hatan
  convert hmul using 1
  unfold squareDifferential rational
  rw [square_deriv]
  field_simp [ne_of_gt (quadratic_pos x)]

private def splitPrimitiveAux (x : ℝ) :=
  x - Real.log (x ^ 2 + 2 * x + 2)

private lemma hasDerivAt_splitPrimitiveAux (x : ℝ) :
    HasDerivAt splitPrimitiveAux (splitRational x) x := by
  have hlinear : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)
  have hpoly :
      HasDerivAt (fun y : ℝ => y ^ 2 + 2 * y + 2) (2 * x + 2) x := by
    simpa [add_assoc] using ((hasDerivAt_sq x).add hlinear).add_const 2
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (y ^ 2 + 2 * y + 2))
        ((2 * x + 2) / (x ^ 2 + 2 * x + 2)) x := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
      ((Real.hasDerivAt_log (ne_of_gt (quadratic_pos x))).comp x hpoly)
  simpa [splitPrimitiveAux, splitRational] using
    (hasDerivAt_id x).sub hlog

theorem gap1 : Family integrand = HalfFamily squareDifferential := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    refine ⟨fun x => 2 * F x, ?_, ?_⟩
    · intro x
      have hscaled := (hasDerivAt_const x (2 : ℝ)).mul (hF x)
      simpa [squareDifferential, integrand, square_deriv, mul_comm,
        mul_left_comm, mul_assoc] using hscaled
    · intro x
      ring
  · rintro ⟨A, hA, hEq⟩
    intro x
    rw [show F = fun y => (1 / 2 : ℝ) * A y by
      funext y
      exact hEq y]
    have hscaled := (hasDerivAt_const x (1 / 2 : ℝ)).mul (hA x)
    convert hscaled using 1
    unfold integrand squareDifferential
    rw [square_deriv]
    ring
theorem gap2 : HalfFamily squareDifferential = ByPartsFamily rational := by
  apply Set.ext
  intro F
  constructor
  · rintro ⟨A, hA, hF⟩
    let B : ℝ → ℝ := fun x => x ^ 2 * Real.arctan (x + 1) - A x
    refine ⟨B, ?_, ?_⟩
    · intro x
      have hder := (hasDerivAt_squareArctan x).sub (hA x)
      convert hder using 1 <;> dsimp [B] <;> ring
    · intro x
      dsimp [B]
      rw [hF x]
      ring
  · rintro ⟨B, hB, hF⟩
    let A : ℝ → ℝ := fun x => x ^ 2 * Real.arctan (x + 1) - B x
    refine ⟨A, ?_, ?_⟩
    · intro x
      have hder := (hasDerivAt_squareArctan x).sub (hB x)
      convert hder using 1 <;> dsimp [A] <;> ring
    · intro x
      dsimp [A]
      rw [hF x]
      ring
theorem gap3 : Family integrand = ByPartsFamily rational := by
  exact gap1.trans gap2
theorem gap4 : Family integrand = ByPartsFamily splitRational := by
  calc
    Family integrand = ByPartsFamily rational := gap3
    _ = ByPartsFamily splitRational := by
      rw [show rational = splitRational by
        funext x
        exact rational_eq_split x]
theorem gap5 : ByPartsFamily splitRational = Translates primitive := by
  apply Set.ext
  intro F
  constructor
  · rintro ⟨A, hA, hF⟩
    let D : ℝ := A 0 - splitPrimitiveAux 0
    refine ⟨-(1 / 2 : ℝ) * D, ?_⟩
    intro x
    have hconst :
        A x - splitPrimitiveAux x = A 0 - splitPrimitiveAux 0 :=
      is_const_of_deriv_eq_zero
        (fun z => ((hA z).sub (hasDerivAt_splitPrimitiveAux z)).differentiableAt)
        (fun z => by
          have hz := ((hA z).sub (hasDerivAt_splitPrimitiveAux z)).deriv
          simpa using hz)
        x 0
    have hAform : A x = splitPrimitiveAux x + D := by
      dsimp [D]
      linarith [hconst]
    calc
      F x = (1 / 2 : ℝ) * x ^ 2 * Real.arctan (x + 1) -
          (1 / 2 : ℝ) * A x := hF x
      _ = primitive x + (-(1 / 2 : ℝ) * D) := by
        rw [hAform]
        unfold primitive splitPrimitiveAux
        ring
  · rintro ⟨C, hF⟩
    let A : ℝ → ℝ := fun x => splitPrimitiveAux x - 2 * C
    refine ⟨A, ?_, ?_⟩
    · intro x
      simpa [A] using (hasDerivAt_splitPrimitiveAux x).sub_const (2 * C)
    · intro x
      calc
        F x = primitive x + C := hF x
        _ = (1 / 2 : ℝ) * x ^ 2 * Real.arctan (x + 1) -
            (1 / 2 : ℝ) * A x := by
          unfold primitive
          dsimp [A, splitPrimitiveAux]
          ring
theorem gap6 : Family integrand = Translates primitive := by
  exact gap4.trans gap5

end
end ProofGap.Exercise2105
