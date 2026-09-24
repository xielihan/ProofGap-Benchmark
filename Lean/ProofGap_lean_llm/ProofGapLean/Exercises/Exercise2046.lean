import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2046
noncomputable section

def denom (a b c x : ℝ) := a * Real.sin x + b * Real.cos x + c
def numerator (a₁ b₁ c₁ x : ℝ) := a₁ * Real.sin x + b₁ * Real.cos x + c₁
def coeffA (a b a₁ b₁ : ℝ) := (a * a₁ + b * b₁) / (a ^ 2 + b ^ 2)
def coeffB (a b a₁ b₁ : ℝ) := (a * b₁ - a₁ * b) / (a ^ 2 + b ^ 2)
def coeffC (a b c a₁ b₁ c₁ : ℝ) :=
  (a * (a * c₁ - a₁ * c) + b * (b * c₁ - b₁ * c)) / (a ^ 2 + b ^ 2)
def CoeffIdentity (a b c a₁ b₁ c₁ A B C : ℝ) : Prop :=
  ∀ x, numerator a₁ b₁ c₁ x =
    A * denom a b c x + B * (a * Real.cos x - b * Real.sin x) + C
def integrand (a b c a₁ b₁ c₁ x : ℝ) :=
  numerator a₁ b₁ c₁ x / denom a b c x
def logDeriv (a b c x : ℝ) :=
  (a * Real.cos x - b * Real.sin x) / denom a b c x
def reciprocal (a b c x : ℝ) := 1 / denom a b c x
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def LinearFamily (U : Set ℝ) (a b c a₁ b₁ c₁ : ℝ) :=
  {F : ℝ → ℝ | ∃ P ∈ Family U (fun _ => (1 : ℝ)),
    ∃ Q ∈ Family U (logDeriv a b c), ∃ R ∈ Family U (reciprocal a b c),
    ∃ C₀, ∀ x ∈ U, F x = coeffA a b a₁ b₁ * P x +
      coeffB a b a₁ b₁ * Q x + coeffC a b c a₁ b₁ c₁ * R x + C₀}
def ReducedFamily (U : Set ℝ) (a b c a₁ b₁ c₁ : ℝ) :=
  {F : ℝ → ℝ | ∃ R ∈ Family U (reciprocal a b c), ∃ C₀,
    ∀ x ∈ U, F x = coeffA a b a₁ b₁ * x +
      coeffB a b a₁ b₁ * Real.log |denom a b c x| +
      coeffC a b c a₁ b₁ c₁ * R x + C₀}
def Regular (U : Set ℝ) (a b c : ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, denom a b c x ≠ 0

private theorem coefficient_identity
    {a b c a₁ b₁ c₁ : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    CoeffIdentity a b c a₁ b₁ c₁
      (coeffA a b a₁ b₁) (coeffB a b a₁ b₁) (coeffC a b c a₁ b₁ c₁) := by
  have hs : a ^ 2 + b ^ 2 ≠ 0 := by
    apply ne_of_gt
    rcases hab with ha | hb
    · have ha2 : 0 < a * a := mul_self_pos.mpr ha
      nlinarith [sq_nonneg b]
    · have hb2 : 0 < b * b := mul_self_pos.mpr hb
      nlinarith [sq_nonneg a]
  intro x
  unfold numerator denom coeffA coeffB coeffC
  field_simp [hs]
  ring

private theorem integrand_decomposition
    {a b c a₁ b₁ c₁ x : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    (hden : denom a b c x ≠ 0) :
    integrand a b c a₁ b₁ c₁ x =
      coeffA a b a₁ b₁ + coeffB a b a₁ b₁ * logDeriv a b c x +
        coeffC a b c a₁ b₁ c₁ * reciprocal a b c x := by
  have hid := coefficient_identity (a := a) (b := b) (c := c)
    (a₁ := a₁) (b₁ := b₁) (c₁ := c₁) hab x
  unfold integrand
  rw [div_eq_iff hden]
  rw [hid]
  unfold logDeriv reciprocal
  field_simp [hden]

private theorem hasDerivAt_log_denom
    (a b c x : ℝ) (hden : denom a b c x ≠ 0) :
    HasDerivAt (fun y => Real.log |denom a b c y|) (logDeriv a b c x) x := by
  have hd : HasDerivAt (denom a b c)
      (a * Real.cos x - b * Real.sin x) x := by
    convert ((((Real.hasDerivAt_sin x).const_mul a).add
      ((Real.hasDerivAt_cos x).const_mul b)).add
      (hasDerivAt_const x c)) using 1 <;>
      simp [denom, sub_eq_add_neg, add_assoc]
  simpa [Real.log_abs, logDeriv] using hd.log hden

private theorem same_derivative_add_const
    (U : Set ℝ) (hopen : IsOpen U) (hconn : IsPreconnected U)
    (F G f : ℝ → ℝ)
    (hF : ∀ x ∈ U, HasDerivAt F (f x) x)
    (hG : ∀ x ∈ U, HasDerivAt G (f x) x) :
    ∃ C, ∀ x ∈ U, F x = G x + C := by
  by_cases hne : U.Nonempty
  · rcases hne with ⟨x₀, hx₀⟩
    let H : ℝ → ℝ := fun x => F x - G x
    have hH : ∀ x ∈ U, HasDerivAt H 0 x := by
      intro x hx
      simpa [H] using (hF x hx).sub (hG x hx)
    have hdiff : DifferentiableOn ℝ H U := by
      intro x hx
      exact (hH x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ U, deriv H x = 0 := by
      intro x hx
      exact (hH x hx).deriv
    refine ⟨H x₀, ?_⟩
    intro x hx
    have heq : H x = H x₀ :=
      hopen.is_const_of_deriv_eq_zero hconn hdiff hzero hx hx₀
    dsimp [H] at heq ⊢
    linarith
  · refine ⟨0, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

private theorem exists_reciprocal_family
    (U : Set ℝ) (a b c : ℝ) (hU : Regular U a b c) :
    ∃ R, R ∈ Family U (reciprocal a b c) := by
  classical
  by_cases hne : U.Nonempty
  · rcases hne with ⟨x₀, hx₀⟩
    have hdencont : Continuous (denom a b c) := by
      unfold denom
      exact ((continuous_const.mul Real.continuous_sin).add
        (continuous_const.mul Real.continuous_cos)).add continuous_const
    have hrecsm : MeasureTheory.StronglyMeasurable (reciprocal a b c) := by
      unfold reciprocal
      exact (measurable_const.div hdencont.measurable).stronglyMeasurable
    have hreccont : ContinuousOn (reciprocal a b c) U := by
      intro y hy
      show ContinuousWithinAt (fun z : ℝ => 1 / denom a b c z) U y
      exact ((continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) y).div
        hdencont.continuousAt (hU.2.2 y hy)).continuousWithinAt
    let R : ℝ → ℝ := fun y => ∫ t in x₀..y, reciprocal a b c t
    refine ⟨R, ?_⟩
    intro x hx
    have hseg : Set.uIcc x₀ x ⊆ U := by
      rcases le_total x₀ x with hle | hge
      · rw [Set.uIcc_of_le hle]
        exact hU.2.1.ordConnected.out hx₀ hx
      · rw [Set.uIcc_of_ge hge]
        exact hU.2.1.ordConnected.out hx hx₀
    have hint : IntervalIntegrable (reciprocal a b c) MeasureTheory.volume x₀ x :=
      (hreccont.mono hseg).intervalIntegrable
    have hcontAt : ContinuousAt (reciprocal a b c) x :=
      (hreccont x hx).continuousAt (hU.1.mem_nhds hx)
    simpa [R] using
      (intervalIntegral.integral_hasDerivAt_right hint
        hrecsm.stronglyMeasurableAtFilter hcontAt)
  · refine ⟨fun _ => 0, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

theorem gap1 (a b a₁ b₁ : ℝ) :
    coeffA a b a₁ b₁ = (a * a₁ + b * b₁) / (a ^ 2 + b ^ 2) := by
  rfl
theorem gap2 (a b a₁ b₁ : ℝ) :
    coeffB a b a₁ b₁ = (a * b₁ - a₁ * b) / (a ^ 2 + b ^ 2) := by
  rfl
theorem gap3 (a b c a₁ b₁ c₁ : ℝ) :
    coeffC a b c a₁ b₁ c₁ =
      (a * (a * c₁ - a₁ * c) + b * (b * c₁ - b₁ * c)) / (a ^ 2 + b ^ 2) := by
  rfl
theorem gap4 (U : Set ℝ) (a b c a₁ b₁ c₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hU : Regular U a b c) :
    Family U (integrand a b c a₁ b₁ c₁) = LinearFamily U a b c a₁ b₁ c₁ := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (integrand a b c a₁ b₁ c₁ x) x at hF
    obtain ⟨R, hR⟩ := exists_reciprocal_family U a b c hU
    let G : ℝ → ℝ := fun y =>
      coeffA a b a₁ b₁ * y +
      coeffB a b a₁ b₁ * Real.log |denom a b c y| +
      coeffC a b c a₁ b₁ c₁ * R y
    have hG : ∀ x ∈ U, HasDerivAt G (integrand a b c a₁ b₁ c₁ x) x := by
      intro x hx
      have hp := (hasDerivAt_id x).const_mul (coeffA a b a₁ b₁)
      have hq := (hasDerivAt_log_denom a b c x (hU.2.2 x hx)).const_mul
        (coeffB a b a₁ b₁)
      have hr := (hR x hx).const_mul (coeffC a b c a₁ b₁ c₁)
      rw [integrand_decomposition hab (hU.2.2 x hx)]
      change HasDerivAt G _ x
      dsimp [G]
      convert (hp.add hq).add hr using 1 <;> ring
    obtain ⟨C₀, hC₀⟩ :=
      same_derivative_add_const U hU.1 hU.2.1 F G
        (integrand a b c a₁ b₁ c₁) hF hG
    change ∃ P ∈ Family U (fun _ => (1 : ℝ)),
      ∃ Q ∈ Family U (logDeriv a b c), ∃ R ∈ Family U (reciprocal a b c),
      ∃ C₀, ∀ x ∈ U, F x = coeffA a b a₁ b₁ * P x +
        coeffB a b a₁ b₁ * Q x + coeffC a b c a₁ b₁ c₁ * R x + C₀
    refine ⟨fun y => y, ?_, fun y => Real.log |denom a b c y|, ?_, R, hR, C₀, ?_⟩
    · intro x hx
      simpa using hasDerivAt_id x
    · intro x hx
      exact hasDerivAt_log_denom a b c x (hU.2.2 x hx)
    · intro x hx
      simpa [G] using hC₀ x hx
  · intro hlin
    change ∃ P ∈ Family U (fun _ => (1 : ℝ)),
      ∃ Q ∈ Family U (logDeriv a b c), ∃ R ∈ Family U (reciprocal a b c),
      ∃ C₀, ∀ x ∈ U, F x = coeffA a b a₁ b₁ * P x +
        coeffB a b a₁ b₁ * Q x + coeffC a b c a₁ b₁ c₁ * R x + C₀ at hlin
    rcases hlin with ⟨P, hP, Q, hQ, R, hR, C₀, hEq⟩
    change ∀ x ∈ U, HasDerivAt F (integrand a b c a₁ b₁ c₁ x) x
    intro x hx
    have hp := (hP x hx).const_mul (coeffA a b a₁ b₁)
    have hq := (hQ x hx).const_mul (coeffB a b a₁ b₁)
    have hr := (hR x hx).const_mul (coeffC a b c a₁ b₁ c₁)
    have hsum := ((hp.add hq).add hr).add_const C₀
    rw [integrand_decomposition hab (hU.2.2 x hx)]
    have hlocal :
        F =ᶠ[nhds x]
          (fun y => coeffA a b a₁ b₁ * P y + coeffB a b a₁ b₁ * Q y +
            coeffC a b c a₁ b₁ c₁ * R y + C₀) := by
      filter_upwards [hU.1.mem_nhds hx] with y hy
      exact hEq y hy
    simpa using hsum.congr_of_eventuallyEq hlocal
theorem gap5 (U : Set ℝ) (a b c a₁ b₁ c₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hU : Regular U a b c) :
    LinearFamily U a b c a₁ b₁ c₁ = ReducedFamily U a b c a₁ b₁ c₁ := by
  apply Set.ext
  intro F
  constructor
  · intro hlin
    change ∃ P ∈ Family U (fun _ => (1 : ℝ)),
      ∃ Q ∈ Family U (logDeriv a b c), ∃ R ∈ Family U (reciprocal a b c),
      ∃ C₀, ∀ x ∈ U, F x = coeffA a b a₁ b₁ * P x +
        coeffB a b a₁ b₁ * Q x + coeffC a b c a₁ b₁ c₁ * R x + C₀ at hlin
    rcases hlin with ⟨P, hP, Q, hQ, R, hR, C₀, hEq⟩
    have hid : ∀ x ∈ U, HasDerivAt (fun y : ℝ => y) 1 x := by
      intro x hx
      simpa using hasDerivAt_id x
    have hlog : ∀ x ∈ U,
        HasDerivAt (fun y => Real.log |denom a b c y|) (logDeriv a b c x) x := by
      intro x hx
      exact hasDerivAt_log_denom a b c x (hU.2.2 x hx)
    obtain ⟨CP, hPEq⟩ :=
      same_derivative_add_const U hU.1 hU.2.1 P (fun y : ℝ => y)
        (fun _ => (1 : ℝ)) hP hid
    obtain ⟨CQ, hQEq⟩ :=
      same_derivative_add_const U hU.1 hU.2.1 Q
        (fun y => Real.log |denom a b c y|) (logDeriv a b c) hQ hlog
    change ∃ R ∈ Family U (reciprocal a b c), ∃ C₀,
      ∀ x ∈ U, F x = coeffA a b a₁ b₁ * x +
        coeffB a b a₁ b₁ * Real.log |denom a b c x| +
        coeffC a b c a₁ b₁ c₁ * R x + C₀
    refine ⟨R, hR,
      C₀ + coeffA a b a₁ b₁ * CP + coeffB a b a₁ b₁ * CQ, ?_⟩
    intro x hx
    rw [hEq x hx, hPEq x hx, hQEq x hx]
    ring
  · intro hred
    change ∃ R ∈ Family U (reciprocal a b c), ∃ C₀,
      ∀ x ∈ U, F x = coeffA a b a₁ b₁ * x +
        coeffB a b a₁ b₁ * Real.log |denom a b c x| +
        coeffC a b c a₁ b₁ c₁ * R x + C₀ at hred
    rcases hred with ⟨R, hR, C₀, hEq⟩
    change ∃ P ∈ Family U (fun _ => (1 : ℝ)),
      ∃ Q ∈ Family U (logDeriv a b c), ∃ R ∈ Family U (reciprocal a b c),
      ∃ C₀, ∀ x ∈ U, F x = coeffA a b a₁ b₁ * P x +
        coeffB a b a₁ b₁ * Q x + coeffC a b c a₁ b₁ c₁ * R x + C₀
    refine ⟨fun y => y, ?_, fun y => Real.log |denom a b c y|, ?_, R, hR, C₀, ?_⟩
    · intro x hx
      simpa using hasDerivAt_id x
    · intro x hx
      exact hasDerivAt_log_denom a b c x (hU.2.2 x hx)
    · exact hEq
theorem gap6 (U : Set ℝ) (a b c a₁ b₁ c₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hU : Regular U a b c) :
    Family U (integrand a b c a₁ b₁ c₁) = ReducedFamily U a b c a₁ b₁ c₁ := by
  calc
    Family U (integrand a b c a₁ b₁ c₁) =
        LinearFamily U a b c a₁ b₁ c₁ := gap4 U a b c a₁ b₁ c₁ hab hU
    _ = ReducedFamily U a b c a₁ b₁ c₁ := gap5 U a b c a₁ b₁ c₁ hab hU

end
end ProofGap.Exercise2046
