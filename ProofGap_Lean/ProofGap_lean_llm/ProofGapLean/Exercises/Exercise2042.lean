import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2042
noncomputable section

def denom (a b x : ℝ) := a * Real.sin x + b * Real.cos x
def numerator (a₁ b₁ x : ℝ) := a₁ * Real.sin x + b₁ * Real.cos x
def coeffA (a b a₁ b₁ : ℝ) := (a * a₁ + b * b₁) / (a ^ 2 + b ^ 2)
def coeffB (a b a₁ b₁ : ℝ) := (a * b₁ - a₁ * b) / (a ^ 2 + b ^ 2)
def CoeffIdentity (a b a₁ b₁ A B : ℝ) : Prop :=
  ∀ x, numerator a₁ b₁ x =
    A * denom a b x + B * (a * Real.cos x - b * Real.sin x)
def integrand (a b a₁ b₁ x : ℝ) := numerator a₁ b₁ x / denom a b x
def logDeriv (a b x : ℝ) :=
  (a * Real.cos x - b * Real.sin x) / denom a b x
def primitive (a b a₁ b₁ x : ℝ) :=
  coeffA a b a₁ b₁ * x +
    coeffB a b a₁ b₁ * Real.log |denom a b x|
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def LinearFamily (U : Set ℝ) (a b a₁ b₁ : ℝ) :=
  {F : ℝ → ℝ | ∃ P ∈ Family U (fun _ => (1 : ℝ)),
    ∃ Q ∈ Family U (logDeriv a b), ∃ C₀, ∀ x ∈ U,
      F x = coeffA a b a₁ b₁ * P x + coeffB a b a₁ b₁ * Q x + C₀}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) (a b : ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, denom a b x ≠ 0

private theorem sumSq_ne_zero (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    a ^ 2 + b ^ 2 ≠ 0 := by
  intro hzero
  rcases hab with ha | hb
  · apply ha
    nlinarith [sq_nonneg a, sq_nonneg b]
  · apply hb
    nlinarith [sq_nonneg a, sq_nonneg b]

private theorem coeffIdentity_standard (a b a₁ b₁ : ℝ)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    CoeffIdentity a b a₁ b₁ (coeffA a b a₁ b₁) (coeffB a b a₁ b₁) := by
  intro x
  unfold numerator denom coeffA coeffB
  field_simp [sumSq_ne_zero a b hab]
  ring

private theorem hasDerivAt_denom (a b x : ℝ) :
    HasDerivAt (denom a b) (a * Real.cos x - b * Real.sin x) x := by
  unfold denom
  convert ((Real.hasDerivAt_sin x).const_mul a).add
    ((Real.hasDerivAt_cos x).const_mul b) using 1 <;> ring

private theorem hasDerivAt_logAbsDenom (a b x : ℝ)
    (hden : denom a b x ≠ 0) :
    HasDerivAt (fun y => Real.log |denom a b y|) (logDeriv a b x) x := by
  have h := (Real.hasDerivAt_log hden).comp x (hasDerivAt_denom a b x)
  simpa [Function.comp_def, Real.log_abs, logDeriv, div_eq_mul_inv, mul_comm] using h

private theorem hasDerivAt_primitive (a b a₁ b₁ x : ℝ)
    (hab : a ≠ 0 ∨ b ≠ 0) (hden : denom a b x ≠ 0) :
    HasDerivAt (primitive a b a₁ b₁) (integrand a b a₁ b₁ x) x := by
  have hbase :=
    ((hasDerivAt_id x).const_mul (coeffA a b a₁ b₁)).add
      ((hasDerivAt_logAbsDenom a b x hden).const_mul
        (coeffB a b a₁ b₁))
  have hval :
      integrand a b a₁ b₁ x =
        coeffA a b a₁ b₁ + coeffB a b a₁ b₁ * logDeriv a b x := by
    unfold integrand logDeriv
    rw [coeffIdentity_standard a b a₁ b₁ hab x]
    field_simp [hden]
  simpa only [primitive, id_eq, mul_one, hval] using hbase

private theorem family_eq_translates_of_hasDeriv
    (U : Set ℝ) (f p : ℝ → ℝ) (hopen : IsOpen U)
    (hconn : IsPreconnected U)
    (hp : ∀ x ∈ U, HasDerivAt p (f x) x) :
    Family U f = Translates U p := by
  ext F
  change (∀ x ∈ U, HasDerivAt F (f x) x) ↔
    ∃ C, ∀ x ∈ U, F x = p x + C
  constructor
  · intro hF
    by_cases hne : U.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      have hzero : ∀ y ∈ U, HasDerivAt (fun z => F z - p z) 0 y := by
        intro y hy
        convert (hF y hy).sub (hp y hy) using 1 <;> ring
      have hdiff : DifferentiableOn ℝ (fun z => F z - p z) U := by
        intro y hy
        exact (hzero y hy).differentiableAt.differentiableWithinAt
      have hderiv : ∀ y ∈ U, deriv (fun z => F z - p z) y = 0 := by
        intro y hy
        exact (hzero y hy).deriv
      refine ⟨F x₀ - p x₀, ?_⟩
      intro x hx
      have hc := hopen.is_const_of_deriv_eq_zero hconn hdiff hderiv hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private theorem linearFamily_eq_translates
    (U : Set ℝ) (a b a₁ b₁ : ℝ) (hopen : IsOpen U)
    (hconn : IsPreconnected U)
    (hden : ∀ x ∈ U, denom a b x ≠ 0) :
    LinearFamily U a b a₁ b₁ = Translates U (primitive a b a₁ b₁) := by
  have hOneDeriv : ∀ x ∈ U, HasDerivAt (fun y : ℝ => y) 1 x := by
    intro x hx
    simpa using hasDerivAt_id x
  have hLogDeriv : ∀ x ∈ U,
      HasDerivAt (fun y => Real.log |denom a b y|) (logDeriv a b x) x := by
    intro x hx
    exact hasDerivAt_logAbsDenom a b x (hden x hx)
  have hOneEq : Family U (fun _ => (1 : ℝ)) =
      Translates U (fun y : ℝ => y) :=
    family_eq_translates_of_hasDeriv U (fun _ => (1 : ℝ))
      (fun y : ℝ => y) hopen hconn hOneDeriv
  have hLogEq : Family U (logDeriv a b) =
      Translates U (fun y => Real.log |denom a b y|) :=
    family_eq_translates_of_hasDeriv U (logDeriv a b)
      (fun y => Real.log |denom a b y|) hopen hconn hLogDeriv
  ext F
  change
    (∃ P ∈ Family U (fun _ => (1 : ℝ)),
      ∃ Q ∈ Family U (logDeriv a b), ∃ C₀, ∀ x ∈ U,
        F x = coeffA a b a₁ b₁ * P x +
          coeffB a b a₁ b₁ * Q x + C₀) ↔
    ∃ C, ∀ x ∈ U, F x = primitive a b a₁ b₁ x + C
  constructor
  · rintro ⟨P, hP, Q, hQ, C₀, hF⟩
    rw [hOneEq] at hP
    rw [hLogEq] at hQ
    rcases hP with ⟨C₁, hP⟩
    rcases hQ with ⟨C₂, hQ⟩
    refine ⟨coeffA a b a₁ b₁ * C₁ + coeffB a b a₁ b₁ * C₂ + C₀, ?_⟩
    intro x hx
    rw [hF x hx, hP x hx, hQ x hx]
    unfold primitive
    ring
  · rintro ⟨C, hF⟩
    refine ⟨(fun x : ℝ => x), ?_,
      (fun x => Real.log |denom a b x|), ?_, C, ?_⟩
    · exact hOneDeriv
    · exact hLogDeriv
    · intro x hx
      simpa [primitive] using hF x hx

theorem gap1 (a b a₁ b₁ : ℝ) :
    coeffA a b a₁ b₁ = (a * a₁ + b * b₁) / (a ^ 2 + b ^ 2) := by
  rfl
theorem gap2 (a b a₁ b₁ : ℝ) :
    coeffB a b a₁ b₁ = (a * b₁ - a₁ * b) / (a ^ 2 + b ^ 2) := by
  rfl
theorem gap3 (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) : a ^ 2 + b ^ 2 ≠ 0 := by
  exact sumSq_ne_zero a b hab
theorem gap4 (U : Set ℝ) (a b a₁ b₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hU : Regular U a b) :
    Family U (integrand a b a₁ b₁) = LinearFamily U a b a₁ b₁ := by
  rcases hU with ⟨hopen, hconn, hden⟩
  calc
    Family U (integrand a b a₁ b₁) =
        Translates U (primitive a b a₁ b₁) :=
      family_eq_translates_of_hasDeriv U (integrand a b a₁ b₁)
        (primitive a b a₁ b₁) hopen hconn
        (fun x hx =>
          hasDerivAt_primitive a b a₁ b₁ x hab (hden x hx))
    _ = LinearFamily U a b a₁ b₁ :=
      (linearFamily_eq_translates U a b a₁ b₁ hopen hconn hden).symm
theorem gap5 (U : Set ℝ) (a b a₁ b₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hU : Regular U a b) :
    LinearFamily U a b a₁ b₁ = Translates U (primitive a b a₁ b₁) := by
  rcases hU with ⟨hopen, hconn, hden⟩
  exact linearFamily_eq_translates U a b a₁ b₁ hopen hconn hden
theorem gap6 (U : Set ℝ) (a b a₁ b₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hU : Regular U a b) :
    Family U (integrand a b a₁ b₁) =
      Translates U (primitive a b a₁ b₁) := by
  calc
    Family U (integrand a b a₁ b₁) = LinearFamily U a b a₁ b₁ :=
      gap4 U a b a₁ b₁ hab hU
    _ = Translates U (primitive a b a₁ b₁) :=
      gap5 U a b a₁ b₁ hab hU
theorem gap7 (U : Set ℝ) (a b a₁ b₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hU : Regular U a b) :
    ∃ A B, CoeffIdentity a b a₁ b₁ A B ∧
      Family U (integrand a b a₁ b₁) =
        Translates U (fun x => A * x + B * Real.log |denom a b x|) := by
  refine ⟨coeffA a b a₁ b₁, coeffB a b a₁ b₁,
    coeffIdentity_standard a b a₁ b₁ hab, ?_⟩
  change Family U (integrand a b a₁ b₁) =
    Translates U (primitive a b a₁ b₁)
  exact gap6 U a b a₁ b₁ hab hU

end
end ProofGap.Exercise2042
