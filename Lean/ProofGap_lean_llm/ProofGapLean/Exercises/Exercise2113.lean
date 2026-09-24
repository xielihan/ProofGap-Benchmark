import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2113
noncomputable section

def integrand (x : ℝ) := x * Real.arctan x * Real.log (1 + x ^ 2)
def squareDifferential (x : ℝ) :=
  Real.arctan x * Real.log (1 + x ^ 2) * deriv (fun y : ℝ => y ^ 2) x
def firstResidual (x : ℝ) :=
  x ^ 2 * (Real.log (1 + x ^ 2) / (1 + x ^ 2) +
    2 * x * Real.arctan x / (1 + x ^ 2))
def logTerm (x : ℝ) := Real.log (1 + x ^ 2)
def logQuotient (x : ℝ) := Real.log (1 + x ^ 2) / (1 + x ^ 2)
def atanQuotient (x : ℝ) := x * Real.arctan x / (1 + x ^ 2)
def twiceSquareQuotient (x : ℝ) := 2 * x ^ 2 / (1 + x ^ 2)
def squareQuotient (x : ℝ) := x ^ 2 / (1 + x ^ 2)
def primitiveExpanded (x : ℝ) :=
  (1 / 2 : ℝ) * x ^ 2 * Real.arctan x * Real.log (1 + x ^ 2) -
    (1 / 2 : ℝ) * x * Real.log (1 + x ^ 2) + x - Real.arctan x +
    (1 / 2 : ℝ) * Real.arctan x * Real.log (1 + x ^ 2) -
    (1 / 2 : ℝ) * x ^ 2 * Real.arctan x +
    (1 / 2 : ℝ) * x - (1 / 2 : ℝ) * Real.arctan x
def primitive (x : ℝ) :=
  x - Real.arctan x +
    (((1 + x ^ 2) / 2) * Real.arctan x - x / 2) *
      (Real.log (1 + x ^ 2) - 1)

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def HalfFamily (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f, ∀ x, F x = (1 / 2 : ℝ) * A x}
def ByPartsFamily (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f, ∀ x,
    F x = (1 / 2 : ℝ) * x ^ 2 * Real.arctan x * Real.log (1 + x ^ 2) -
      (1 / 2 : ℝ) * A x}
def Stage4 :=
  {F : ℝ → ℝ | ∃ A ∈ Family logTerm, ∃ B ∈ Family logQuotient,
    ∃ C ∈ Family atanQuotient, ∃ D ∈ Family (fun x => x * Real.arctan x),
    ∀ x, F x =
      (1 / 2 : ℝ) * x ^ 2 * Real.arctan x * Real.log (1 + x ^ 2) -
      (1 / 2 : ℝ) * A x + (1 / 2 : ℝ) * B x + C x - D x}
def Stage5 :=
  {F : ℝ → ℝ | ∃ A ∈ Family twiceSquareQuotient,
    ∃ B ∈ Family (fun x => x * Real.arctan x),
    ∀ x, F x =
      (1 / 2 : ℝ) * x ^ 2 * Real.arctan x * Real.log (1 + x ^ 2) -
      (1 / 2 : ℝ) * x * Real.log (1 + x ^ 2) + (1 / 2 : ℝ) * A x +
      (1 / 2 : ℝ) * Real.arctan x * Real.log (1 + x ^ 2) - B x}
def Stage6 :=
  {F : ℝ → ℝ | ∃ A ∈ Family twiceSquareQuotient, ∃ B ∈ Family atanQuotient,
    ∃ C ∈ Family atanQuotient, ∃ D ∈ Family squareQuotient, ∀ x,
    F x =
      (1 / 2 : ℝ) * x ^ 2 * Real.arctan x * Real.log (1 + x ^ 2) -
      (1 / 2 : ℝ) * x * Real.log (1 + x ^ 2) + (1 / 2 : ℝ) * A x +
      (1 / 2 : ℝ) * Real.arctan x * Real.log (1 + x ^ 2) - B x + C x -
      (1 / 2 : ℝ) * x ^ 2 * Real.arctan x + (1 / 2 : ℝ) * D x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ K : ℝ, ∀ x, F x = p x + K}

private def boundary (x : ℝ) :=
  (1 / 2 : ℝ) * x ^ 2 * Real.arctan x * Real.log (1 + x ^ 2)

private def logPrimitive (x : ℝ) :=
  x * Real.log (1 + x ^ 2) - 2 * x + 2 * Real.arctan x

private def logQPrimitive (x : ℝ) :=
  ∫ t in (0 : ℝ)..x, logQuotient t

private def atanQPrimitive (x : ℝ) :=
  (1 / 2 : ℝ) * Real.arctan x * Real.log (1 + x ^ 2) -
    (1 / 2 : ℝ) * logQPrimitive x

private def xAtanPrimitive (x : ℝ) :=
  (1 / 2 : ℝ) * (x ^ 2 + 1) * Real.arctan x - (1 / 2 : ℝ) * x

private def twiceSquarePrimitive (x : ℝ) :=
  2 * x - 2 * Real.arctan x

private def squarePrimitive (x : ℝ) :=
  x - Real.arctan x

private def residualPrimitive (x : ℝ) :=
  2 * boundary x - 2 * primitiveExpanded x

private theorem h_atan (x : ℝ) :
    HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x := by
  simpa [one_div] using Real.hasDerivAt_arctan x

private theorem h_log (x : ℝ) :
    HasDerivAt logTerm (2 * x / (1 + x ^ 2)) x := by
  have hb : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      norm_num <;> ring
  simpa [logTerm] using hb.log (by positivity)

private theorem h_primitive (x : ℝ) :
    HasDerivAt primitiveExpanded (integrand x) x := by
  have hx := hasDerivAt_id x
  have ha := h_atan x
  have hl := h_log x
  have h1 := (((hx.pow 2).const_mul (1 / 2 : ℝ)).mul ha).mul hl
  have h2 := (hx.const_mul (1 / 2 : ℝ)).mul hl
  have h5 := (ha.const_mul (1 / 2 : ℝ)).mul hl
  have h6 := ((hx.pow 2).const_mul (1 / 2 : ℝ)).mul ha
  have h7 := hx.const_mul (1 / 2 : ℝ)
  have h8 := ha.const_mul (1 / 2 : ℝ)
  have h := (((((((h1.sub h2).add hx).sub ha).add h5).sub h6).add h7).sub h8)
  have hn : 1 + x ^ 2 ≠ 0 := by positivity
  convert h using 1 <;>
    simp [primitiveExpanded, integrand, logTerm] <;>
    field_simp [hn] <;> ring

private theorem squareDifferential_eq (x : ℝ) :
    squareDifferential x = 2 * integrand x := by
  have hs : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2) using 1 <;> norm_num <;> ring
  unfold squareDifferential integrand
  rw [hs.deriv]
  ring

private theorem h_doublePrimitive (x : ℝ) :
    HasDerivAt (fun y => 2 * primitiveExpanded y) (squareDifferential x) x := by
  convert (h_primitive x).const_mul 2 using 1
  rw [squareDifferential_eq]

private theorem h_boundary (x : ℝ) :
    HasDerivAt boundary
      (integrand x + (1 / 2 : ℝ) * firstResidual x) x := by
  have hx := hasDerivAt_id x
  have h := (((hx.pow 2).const_mul (1 / 2 : ℝ)).mul (h_atan x)).mul (h_log x)
  have hn : 1 + x ^ 2 ≠ 0 := by positivity
  convert h using 1 <;>
    simp [boundary, integrand, firstResidual, logTerm] <;>
    field_simp [hn] <;> ring

private theorem h_residualPrimitive (x : ℝ) :
    HasDerivAt residualPrimitive (firstResidual x) x := by
  have h := (h_boundary x).const_mul 2 |>.sub ((h_primitive x).const_mul 2)
  convert h using 1 <;> simp [residualPrimitive] <;> ring

private theorem continuous_logQuotient : Continuous logQuotient := by
  have hd : Continuous (fun x : ℝ => 1 + x ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  unfold logQuotient
  exact (hd.log (fun x => by positivity)).div hd (fun x => by positivity)

private theorem h_logQPrimitive (x : ℝ) :
    HasDerivAt logQPrimitive (logQuotient x) x := by
  have hm : StronglyMeasurableAtFilter logQuotient (nhds x) MeasureTheory.volume :=
    continuous_logQuotient.stronglyMeasurable.stronglyMeasurableAtFilter
  unfold logQPrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    (continuous_logQuotient.intervalIntegrable 0 x)
    hm
    continuous_logQuotient.continuousAt

private theorem h_logPrimitive (x : ℝ) :
    HasDerivAt logPrimitive (logTerm x) x := by
  have h := ((hasDerivAt_id x).mul (h_log x)).sub
    ((hasDerivAt_id x).const_mul 2) |>.add ((h_atan x).const_mul 2)
  have hn : 1 + x ^ 2 ≠ 0 := by positivity
  convert h using 1 <;>
    simp [logPrimitive, logTerm] <;>
    field_simp [hn] <;> ring

private theorem h_atanQPrimitive (x : ℝ) :
    HasDerivAt atanQPrimitive (atanQuotient x) x := by
  have h := (((h_atan x).const_mul (1 / 2 : ℝ)).mul (h_log x)).sub
    ((h_logQPrimitive x).const_mul (1 / 2 : ℝ))
  have hn : 1 + x ^ 2 ≠ 0 := by positivity
  convert h using 1 <;>
    simp [atanQPrimitive, atanQuotient, logQuotient, logTerm] <;>
    field_simp [hn] <;> ring

private theorem h_xAtanPrimitive (x : ℝ) :
    HasDerivAt xAtanPrimitive (x * Real.arctan x) x := by
  have hs : HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const 1 using 1 <;> norm_num <;> ring
  have h := ((hs.const_mul (1 / 2 : ℝ)).mul (h_atan x)).sub
    ((hasDerivAt_id x).const_mul (1 / 2 : ℝ))
  have hn : 1 + x ^ 2 ≠ 0 := by positivity
  convert h using 1 <;>
    simp [xAtanPrimitive] <;>
    field_simp [hn] <;> ring

private theorem h_twiceSquarePrimitive (x : ℝ) :
    HasDerivAt twiceSquarePrimitive (twiceSquareQuotient x) x := by
  have h := ((hasDerivAt_id x).const_mul 2).sub ((h_atan x).const_mul 2)
  have hn : 1 + x ^ 2 ≠ 0 := by positivity
  convert h using 1 <;>
    simp [twiceSquarePrimitive, twiceSquareQuotient] <;>
    field_simp [hn] <;> ring

private theorem h_squarePrimitive (x : ℝ) :
    HasDerivAt squarePrimitive (squareQuotient x) x := by
  have h := (hasDerivAt_id x).sub (h_atan x)
  have hn : 1 + x ^ 2 ≠ 0 := by positivity
  convert h using 1 <;>
    simp [squarePrimitive, squareQuotient] <;>
    field_simp [hn] <;> ring

private theorem family_eq_translates {f p : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p (f x) x) : Family f = Translates p := by
  apply Set.ext
  intro F
  change (∀ x, HasDerivAt F (f x) x) ↔ ∃ K : ℝ, ∀ x, F x = p x + K
  constructor
  · intro hF
    have hd : Differentiable ℝ (fun x : ℝ => F x - p x) := fun x =>
      (hF x).differentiableAt.sub (hp x).differentiableAt
    have hz : ∀ x, deriv (fun y => F y - p y) x = 0 := fun x => by
      simpa using ((hF x).sub (hp x)).deriv
    refine ⟨F 0 - p 0, fun x => ?_⟩
    have hc := is_const_of_deriv_eq_zero hd hz x 0
    linarith
  · rintro ⟨K, hF⟩
    have heq : F = fun y => p y + K := funext hF
    rw [heq]
    intro x
    exact (hp x).add_const K

private theorem byParts_eq :
    ByPartsFamily firstResidual = Translates primitiveExpanded := by
  apply Set.ext
  intro F
  change (∃ A ∈ Family firstResidual, ∀ x,
    F x = boundary x - (1 / 2 : ℝ) * A x) ↔
    ∃ K : ℝ, ∀ x, F x = primitiveExpanded x + K
  constructor
  · rintro ⟨A, hA, hF⟩
    rw [family_eq_translates h_residualPrimitive] at hA
    rcases hA with ⟨K, hAK⟩
    refine ⟨-(1 / 2 : ℝ) * K, fun x => ?_⟩
    rw [hF x, hAK x]
    unfold residualPrimitive
    ring
  · rintro ⟨K, hF⟩
    refine ⟨fun x => residualPrimitive x - 2 * K, ?_, ?_⟩
    · rw [family_eq_translates h_residualPrimitive]
      exact ⟨-2 * K, fun x => by simp; ring⟩
    · intro x
      rw [hF x]
      unfold residualPrimitive
      ring

private theorem stage4_eq : Stage4 = Translates primitiveExpanded := by
  apply Set.ext
  intro F
  change (∃ A ∈ Family logTerm, ∃ B ∈ Family logQuotient,
    ∃ C ∈ Family atanQuotient, ∃ D ∈ Family (fun x => x * Real.arctan x),
    ∀ x, F x = boundary x - (1 / 2 : ℝ) * A x +
      (1 / 2 : ℝ) * B x + C x - D x) ↔
    ∃ K : ℝ, ∀ x, F x = primitiveExpanded x + K
  constructor
  · rintro ⟨A, hA, B, hB, C, hC, D, hD, hF⟩
    rw [family_eq_translates h_logPrimitive] at hA
    rw [family_eq_translates h_logQPrimitive] at hB
    rw [family_eq_translates h_atanQPrimitive] at hC
    rw [family_eq_translates h_xAtanPrimitive] at hD
    rcases hA with ⟨KA, hA⟩
    rcases hB with ⟨KB, hB⟩
    rcases hC with ⟨KC, hC⟩
    rcases hD with ⟨KD, hD⟩
    refine ⟨-(1 / 2 : ℝ) * KA + (1 / 2 : ℝ) * KB + KC - KD, fun x => ?_⟩
    rw [hF x, hA x, hB x, hC x, hD x]
    unfold boundary logPrimitive atanQPrimitive xAtanPrimitive primitiveExpanded
    ring
  · rintro ⟨K, hF⟩
    refine ⟨fun x => logPrimitive x - 2 * K, ?_,
      logQPrimitive, ?_, atanQPrimitive, ?_, xAtanPrimitive, ?_, ?_⟩
    · rw [family_eq_translates h_logPrimitive]
      exact ⟨-2 * K, fun x => by simp; ring⟩
    · rw [family_eq_translates h_logQPrimitive]
      exact ⟨0, fun x => by simp⟩
    · rw [family_eq_translates h_atanQPrimitive]
      exact ⟨0, fun x => by simp⟩
    · rw [family_eq_translates h_xAtanPrimitive]
      exact ⟨0, fun x => by simp⟩
    · intro x
      rw [hF x]
      unfold boundary logPrimitive atanQPrimitive xAtanPrimitive primitiveExpanded
      ring

private theorem stage5_eq : Stage5 = Translates primitiveExpanded := by
  apply Set.ext
  intro F
  change (∃ A ∈ Family twiceSquareQuotient,
    ∃ B ∈ Family (fun x => x * Real.arctan x), ∀ x,
    F x = boundary x - (1 / 2 : ℝ) * x * Real.log (1 + x ^ 2) +
      (1 / 2 : ℝ) * A x +
      (1 / 2 : ℝ) * Real.arctan x * Real.log (1 + x ^ 2) - B x) ↔
    ∃ K : ℝ, ∀ x, F x = primitiveExpanded x + K
  constructor
  · rintro ⟨A, hA, B, hB, hF⟩
    rw [family_eq_translates h_twiceSquarePrimitive] at hA
    rw [family_eq_translates h_xAtanPrimitive] at hB
    rcases hA with ⟨KA, hA⟩
    rcases hB with ⟨KB, hB⟩
    refine ⟨(1 / 2 : ℝ) * KA - KB, fun x => ?_⟩
    rw [hF x, hA x, hB x]
    unfold boundary twiceSquarePrimitive xAtanPrimitive primitiveExpanded
    ring
  · rintro ⟨K, hF⟩
    refine ⟨fun x => twiceSquarePrimitive x + 2 * K, ?_,
      xAtanPrimitive, ?_, ?_⟩
    · rw [family_eq_translates h_twiceSquarePrimitive]
      exact ⟨2 * K, fun x => rfl⟩
    · rw [family_eq_translates h_xAtanPrimitive]
      exact ⟨0, fun x => by simp⟩
    · intro x
      rw [hF x]
      unfold boundary twiceSquarePrimitive xAtanPrimitive primitiveExpanded
      ring

private theorem stage6_eq : Stage6 = Translates primitiveExpanded := by
  apply Set.ext
  intro F
  change (∃ A ∈ Family twiceSquareQuotient, ∃ B ∈ Family atanQuotient,
    ∃ C ∈ Family atanQuotient, ∃ D ∈ Family squareQuotient, ∀ x,
    F x = boundary x - (1 / 2 : ℝ) * x * Real.log (1 + x ^ 2) +
      (1 / 2 : ℝ) * A x +
      (1 / 2 : ℝ) * Real.arctan x * Real.log (1 + x ^ 2) - B x + C x -
      (1 / 2 : ℝ) * x ^ 2 * Real.arctan x + (1 / 2 : ℝ) * D x) ↔
    ∃ K : ℝ, ∀ x, F x = primitiveExpanded x + K
  constructor
  · rintro ⟨A, hA, B, hB, C, hC, D, hD, hF⟩
    rw [family_eq_translates h_twiceSquarePrimitive] at hA
    rw [family_eq_translates h_atanQPrimitive] at hB
    rw [family_eq_translates h_atanQPrimitive] at hC
    rw [family_eq_translates h_squarePrimitive] at hD
    rcases hA with ⟨KA, hA⟩
    rcases hB with ⟨KB, hB⟩
    rcases hC with ⟨KC, hC⟩
    rcases hD with ⟨KD, hD⟩
    refine ⟨(1 / 2 : ℝ) * KA - KB + KC + (1 / 2 : ℝ) * KD, fun x => ?_⟩
    rw [hF x, hA x, hB x, hC x, hD x]
    unfold boundary twiceSquarePrimitive squarePrimitive primitiveExpanded
    ring
  · rintro ⟨K, hF⟩
    refine ⟨fun x => twiceSquarePrimitive x + 2 * K, ?_,
      atanQPrimitive, ?_, atanQPrimitive, ?_, squarePrimitive, ?_, ?_⟩
    · rw [family_eq_translates h_twiceSquarePrimitive]
      exact ⟨2 * K, fun x => rfl⟩
    · rw [family_eq_translates h_atanQPrimitive]
      exact ⟨0, fun x => by simp⟩
    · rw [family_eq_translates h_atanQPrimitive]
      exact ⟨0, fun x => by simp⟩
    · rw [family_eq_translates h_squarePrimitive]
      exact ⟨0, fun x => by simp⟩
    · intro x
      rw [hF x]
      unfold boundary twiceSquarePrimitive squarePrimitive primitiveExpanded
      ring

private theorem primitive_eq (x : ℝ) : primitiveExpanded x = primitive x := by
  unfold primitiveExpanded primitive
  ring

theorem gap1 : Family integrand = HalfFamily squareDifferential := by
  rw [family_eq_translates h_primitive]
  apply Set.ext
  intro F
  change (F ∈ Translates primitiveExpanded) ↔ F ∈ HalfFamily squareDifferential
  constructor
  · rintro ⟨K, hF⟩
    refine ⟨fun x => 2 * primitiveExpanded x + 2 * K, ?_, ?_⟩
    · rw [family_eq_translates h_doublePrimitive]
      exact ⟨2 * K, fun x => rfl⟩
    · intro x
      rw [hF x]
      ring
  · rintro ⟨A, hA, hF⟩
    rw [family_eq_translates h_doublePrimitive] at hA
    rcases hA with ⟨K, hAK⟩
    refine ⟨K / 2, fun x => ?_⟩
    rw [hF x, hAK x]
    ring
theorem gap2 : HalfFamily squareDifferential = ByPartsFamily firstResidual := by
  calc
    HalfFamily squareDifferential = Family integrand := gap1.symm
    _ = Translates primitiveExpanded := family_eq_translates h_primitive
    _ = ByPartsFamily firstResidual := byParts_eq.symm
theorem gap3 : Family integrand = ByPartsFamily firstResidual := by
  exact gap1.trans gap2
theorem gap4 : Family integrand = Stage4 := by
  calc
    Family integrand = Translates primitiveExpanded := family_eq_translates h_primitive
    _ = Stage4 := stage4_eq.symm
theorem gap5 : Family integrand = Stage5 := by
  calc
    Family integrand = Translates primitiveExpanded := family_eq_translates h_primitive
    _ = Stage5 := stage5_eq.symm
theorem gap6 : Family integrand = Stage6 := by
  calc
    Family integrand = Translates primitiveExpanded := family_eq_translates h_primitive
    _ = Stage6 := stage6_eq.symm
theorem gap7 : Family integrand = Translates primitiveExpanded := by
  exact family_eq_translates h_primitive
theorem gap8 : Family integrand = Translates primitive := by
  rw [family_eq_translates h_primitive]
  apply Set.ext
  intro F
  change (∃ K : ℝ, ∀ x, F x = primitiveExpanded x + K) ↔
    ∃ K : ℝ, ∀ x, F x = primitive x + K
  constructor
  · rintro ⟨K, hF⟩
    refine ⟨K, fun x => ?_⟩
    rw [hF x, primitive_eq]
  · rintro ⟨K, hF⟩
    refine ⟨K, fun x => ?_⟩
    rw [hF x, primitive_eq]

end
end ProofGap.Exercise2113
