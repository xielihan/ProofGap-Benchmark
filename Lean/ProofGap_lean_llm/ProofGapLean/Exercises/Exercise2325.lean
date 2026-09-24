import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

open Filter
open scoped Interval

namespace ProofGap.Exercise2325

noncomputable section

def integrand (x : ℝ) : ℝ := Real.exp (-x) / (x + 100)
def I : ℝ := ∫ x in 0..100, integrand x
def leftPart : ℝ := ∫ x in 0..50, integrand x
def rightPart : ℝ := ∫ x in 50..100, integrand x

def twoPointValue (ξ₁ ξ₂ : ℝ) : ℝ :=
  (1 - Real.exp (-50)) / (100 + ξ₁) +
    (Real.exp (-50) - Real.exp (-100)) / (100 + ξ₂)

def θ : ℝ := 2 - 200 * I

def θFunction (ξ : ℝ) : ℝ :=
  2 / (100 + ξ) * (ξ + 100 / Real.exp 100)

def powerIntegral (n : ℕ) : ℝ :=
  ∫ x in 0..1, x ^ n / (1 + x)

def meanValueSequence (ξ : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 / (1 + ξ n) * (1 / ((n + 1 : ℕ) : ℝ))

def sinePowerIntegral (n : ℕ) : ℝ :=
  ∫ x in 0..Real.pi / 2, Real.sin x ^ n

private theorem expNegIntegral (a b : ℝ) :
    (∫ x in a..b, Real.exp (-x)) = Real.exp (-a) - Real.exp (-b) := by
  have hi : IntervalIntegrable (fun x : ℝ => Real.exp (-x))
      MeasureTheory.volume a b :=
    (Real.continuous_exp.comp (continuous_neg.comp continuous_id)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (f := fun x : ℝ => -Real.exp (-x))
    (fun x _ => by
      simpa using (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).neg))
    hi
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

private theorem integrandIntervalIntegrable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable integrand MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  have hnum : ContinuousAt (fun y : ℝ => Real.exp (-y)) x :=
    (Real.continuous_exp.comp (continuous_neg.comp continuous_id)).continuousAt
  have hden : ContinuousAt (fun y : ℝ => y + 100) x :=
    continuousAt_id.add continuousAt_const
  have hd : x + 100 ≠ 0 := by nlinarith [ha, hx.1]
  simpa [integrand, div_eq_mul_inv] using
    (hnum.mul (hden.inv₀ hd)).continuousWithinAt

private theorem reciprocalWeightedMeanValue
    (c a b : ℝ) (hab : a ≤ b) (hca : 0 < c + a)
    (g : ℝ → ℝ)
    (hgcont : ContinuousOn g (Set.uIcc a b))
    (hg : ∀ x ∈ Set.Icc a b, 0 ≤ g x)
    (hG : 0 < ∫ x in a..b, g x) :
    ∃ ξ ∈ Set.Icc a b,
      (∫ x in a..b, (1 / (c + x)) * g x) =
        1 / (c + ξ) * (∫ x in a..b, g x) := by
  have hcb : 0 < c + b := by nlinarith
  have hf : ContinuousOn (fun x : ℝ => 1 / (c + x)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    have hd : c + x ≠ 0 := by nlinarith [hx.1]
    have hc : ContinuousAt (fun y : ℝ => c + y) x :=
      continuousAt_const.add continuousAt_id
    simpa [one_div] using (hc.inv₀ hd).continuousWithinAt
  have hfg : IntervalIntegrable (fun x : ℝ => (1 / (c + x)) * g x)
      MeasureTheory.volume a b :=
    (hf.mul hgcont).intervalIntegrable
  have hlower :
      1 / (c + b) * (∫ x in a..b, g x) ≤
        ∫ x in a..b, (1 / (c + x)) * g x := by
    have hlowInt : IntervalIntegrable (fun x : ℝ => (1 / (c + b)) * g x)
        MeasureTheory.volume a b := by
      have hc : ContinuousOn (fun _ : ℝ => 1 / (c + b)) (Set.uIcc a b) :=
        continuous_const.continuousOn
      exact (hc.mul hgcont).intervalIntegrable
    have hmono := intervalIntegral.integral_mono_on hab hlowInt hfg (by
      intro x hx
      have hcx : 0 < c + x := by nlinarith [hx.1]
      have hrec : 1 / (c + b) ≤ 1 / (c + x) :=
        one_div_le_one_div_of_le hcx (by nlinarith [hx.2])
      exact mul_le_mul_of_nonneg_right hrec (hg x hx))
    simpa using hmono
  have hupper :
      (∫ x in a..b, (1 / (c + x)) * g x) ≤
        1 / (c + a) * (∫ x in a..b, g x) := by
    have huppInt : IntervalIntegrable (fun x : ℝ => (1 / (c + a)) * g x)
        MeasureTheory.volume a b := by
      have hc : ContinuousOn (fun _ : ℝ => 1 / (c + a)) (Set.uIcc a b) :=
        continuous_const.continuousOn
      exact (hc.mul hgcont).intervalIntegrable
    have hmono := intervalIntegral.integral_mono_on hab hfg huppInt (by
      intro x hx
      have hrec : 1 / (c + x) ≤ 1 / (c + a) :=
        one_div_le_one_div_of_le hca (by nlinarith [hx.1])
      exact mul_le_mul_of_nonneg_right hrec (hg x hx))
    simpa using hmono
  let q : ℝ :=
    (∫ x in a..b, (1 / (c + x)) * g x) /
      (∫ x in a..b, g x)
  have hqlo : 1 / (c + b) ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ hG]
    exact hlower
  have hqhi : q ≤ 1 / (c + a) := by
    dsimp [q]
    rw [div_le_iff₀ hG]
    exact hupper
  have hqpos : 0 < q :=
    lt_of_lt_of_le (one_div_pos.mpr hcb) hqlo
  refine ⟨1 / q - c, ?_, ?_⟩
  · constructor
    · have hrec := one_div_le_one_div_of_le hqpos hqhi
      have hbound : c + a ≤ 1 / q := by
        simpa only [one_div, inv_inv] using hrec
      linarith
    · have hrec := one_div_le_one_div_of_le (one_div_pos.mpr hcb) hqlo
      have hbound : 1 / q ≤ c + b := by
        simpa only [one_div, inv_inv] using hrec
      linarith
  · have hfactor : 1 / (c + (1 / q - c)) = q := by
      rw [show c + (1 / q - c) = 1 / q by ring]
      simp only [one_div, inv_inv]
    rw [hfactor]
    dsimp [q]
    field_simp [ne_of_gt hG] <;> ring

private theorem integrandMeanValue {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) :
    ∃ ξ ∈ Set.Icc a b,
      (∫ x in a..b, integrand x) =
        1 / (100 + ξ) * (∫ x in a..b, Real.exp (-x)) := by
  have hgcont : ContinuousOn (fun x : ℝ => Real.exp (-x)) (Set.uIcc a b) :=
    (Real.continuous_exp.comp (continuous_neg.comp continuous_id)).continuousOn
  have hg : ∀ x ∈ Set.Icc a b, 0 ≤ Real.exp (-x) := by
    intro x hx
    exact (Real.exp_pos (-x)).le
  have hG : 0 < ∫ x in a..b, Real.exp (-x) := by
    rw [expNegIntegral]
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  obtain ⟨ξ, hξ, h⟩ := reciprocalWeightedMeanValue
    (c := (100 : ℝ)) (a := a) (b := b) (hab := hab.le)
    (hca := by nlinarith) (g := fun x : ℝ => Real.exp (-x))
    (hgcont := hgcont) (hg := hg) (hG := hG)
  refine ⟨ξ, hξ, ?_⟩
  simpa [integrand, div_eq_mul_inv, mul_comm, add_comm] using h

private theorem integralPowZeroOne (n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ n) = 1 / (((n + 1 : ℕ) : ℝ)) := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => y ^ (n + 1) / (((n + 1 : ℕ) : ℝ))) (x ^ n) x := by
    intro x
    convert ((hasDerivAt_id x).pow (n + 1)).div_const (((n + 1 : ℕ) : ℝ)) using 1
    field_simp [hn]
    simp
  have hi : IntervalIntegrable (fun x : ℝ => x ^ n) MeasureTheory.volume 0 1 :=
    (continuous_id.pow n).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun x : ℝ => x ^ (n + 1) / (((n + 1 : ℕ) : ℝ)))
    (fun x _ => hderiv x) hi
  simpa using h

private theorem sineIntervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.sin x ^ n) MeasureTheory.volume a b := by
  exact (Real.continuous_sin.pow n).intervalIntegrable a b

theorem gap1 :
    I = leftPart + rightPart := by
  unfold I leftPart rightPart
  exact (intervalIntegral.integral_add_adjacent_intervals
    (integrandIntervalIntegrable (a := 0) (b := 50) (by norm_num) (by norm_num))
    (integrandIntervalIntegrable (a := 50) (b := 100) (by norm_num) (by norm_num))).symm

theorem gap2 :
    ∃ ξ₁ ∈ Set.Icc (0 : ℝ) 50, ∃ ξ₂ ∈ Set.Icc (50 : ℝ) 100,
      leftPart + rightPart =
        1 / (100 + ξ₁) * (∫ x in 0..50, Real.exp (-x)) +
        1 / (100 + ξ₂) * (∫ x in 50..100, Real.exp (-x)) := by
  obtain ⟨ξ₁, hξ₁, hleft⟩ := integrandMeanValue
    (a := (0 : ℝ)) (b := 50) (by norm_num) (by norm_num)
  obtain ⟨ξ₂, hξ₂, hright⟩ := integrandMeanValue
    (a := (50 : ℝ)) (b := 100) (by norm_num) (by norm_num)
  refine ⟨ξ₁, hξ₁, ξ₂, hξ₂, ?_⟩
  unfold leftPart rightPart
  rw [hleft, hright]

theorem gap3 :
    ∃ ξ₁ ∈ Set.Icc (0 : ℝ) 50, ∃ ξ₂ ∈ Set.Icc (50 : ℝ) 100,
      I =
        1 / (100 + ξ₁) * (∫ x in 0..50, Real.exp (-x)) +
        1 / (100 + ξ₂) * (∫ x in 50..100, Real.exp (-x)) := by
  obtain ⟨ξ₁, hξ₁, ξ₂, hξ₂, h⟩ := gap2
  exact ⟨ξ₁, hξ₁, ξ₂, hξ₂, by rw [gap1, h]⟩

theorem gap4 :
    ∃ ξ₁ ∈ Set.Icc (0 : ℝ) 50, ∃ ξ₂ ∈ Set.Icc (50 : ℝ) 100,
      I = twoPointValue ξ₁ ξ₂ := by
  obtain ⟨ξ₁, hξ₁, ξ₂, hξ₂, h⟩ := gap3
  refine ⟨ξ₁, hξ₁, ξ₂, hξ₂, ?_⟩
  rw [h, expNegIntegral, expNegIntegral]
  simp only [neg_zero, Real.exp_zero]
  simp [twoPointValue, div_eq_mul_inv, mul_comm]

theorem gap5 (ξ₁ ξ₂ : ℝ) (h₁ : ξ₁ ∈ Set.Icc (0 : ℝ) 50)
    (h₂ : ξ₂ ∈ Set.Icc (50 : ℝ) 100) :
    twoPointValue ξ₁ ξ₂ ≤
      (1 - Real.exp (-50)) / (100 + ξ₁) +
        (Real.exp (-50) - Real.exp (-100)) / (100 + ξ₁) := by
  unfold twoPointValue
  have hnum : 0 ≤ Real.exp (-50) - Real.exp (-100) := by
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by norm_num))
  have hd₁ : 0 < 100 + ξ₁ := by nlinarith [h₁.1]
  have hden : 100 + ξ₁ ≤ 100 + ξ₂ := by nlinarith [h₁.2, h₂.1]
  have hq := div_le_div_of_nonneg_left hnum hd₁ hden
  linarith

theorem gap6 (ξ : ℝ) :
    (1 - Real.exp (-50)) / (100 + ξ) +
        (Real.exp (-50) - Real.exp (-100)) / (100 + ξ) =
      (1 - Real.exp (-100)) / (100 + ξ) := by
  ring

theorem gap7 (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 50) :
    (1 - Real.exp (-100)) / (100 + ξ) < (1 / 100 : ℝ) := by
  have hd : 0 < 100 + ξ := by nlinarith [hξ.1]
  have hn : 1 - Real.exp (-100) < 1 := by
    have := Real.exp_pos (-100)
    linarith
  have hfirst : (1 - Real.exp (-100)) / (100 + ξ) < 1 / (100 + ξ) :=
    (div_lt_div_iff_of_pos_right hd).2 hn
  have hden : (100 : ℝ) ≤ 100 + ξ := by nlinarith [hξ.1]
  have hsecond : 1 / (100 + ξ) ≤ (1 / 100 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hden
  exact lt_of_lt_of_le hfirst hsecond

theorem gap8 (ξ₁ ξ₂ : ℝ) (h₁ : ξ₁ ∈ Set.Icc (0 : ℝ) 50)
    (h₂ : ξ₂ ∈ Set.Icc (50 : ℝ) 100) :
    twoPointValue ξ₁ ξ₂ < (1 / 100 : ℝ) := by
  calc
    twoPointValue ξ₁ ξ₂ ≤
        (1 - Real.exp (-50)) / (100 + ξ₁) +
          (Real.exp (-50) - Real.exp (-100)) / (100 + ξ₁) := gap5 ξ₁ ξ₂ h₁ h₂
    _ = (1 - Real.exp (-100)) / (100 + ξ₁) := gap6 ξ₁
    _ < 1 / 100 := gap7 ξ₁ h₁

theorem gap9 (ξ₁ ξ₂ : ℝ) (h₁ : ξ₁ ∈ Set.Icc (0 : ℝ) 50)
    (h₂ : ξ₂ ∈ Set.Icc (50 : ℝ) 100) :
    twoPointValue ξ₁ ξ₂ >
      (1 - Real.exp (-50)) / (100 + ξ₁) := by
  unfold twoPointValue
  have hn : 0 < Real.exp (-50) - Real.exp (-100) := by
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num))
  have hd : 0 < 100 + ξ₂ := by nlinarith [h₂.1]
  have hq : 0 < (Real.exp (-50) - Real.exp (-100)) / (100 + ξ₂) :=
    div_pos hn hd
  linarith

theorem gap10 (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 50) :
    (1 - Real.exp (-50)) / (100 + ξ) ≥
      (1 - Real.exp (-50)) / 150 := by
  have hn : 0 ≤ 1 - Real.exp (-50) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  have hd : 0 < 100 + ξ := by nlinarith [hξ.1]
  have hden : 100 + ξ ≤ (150 : ℝ) := by nlinarith [hξ.2]
  exact div_le_div_of_nonneg_left hn hd hden

theorem gap11 :
    (1 - Real.exp (-50)) / 150 > (1 / 200 : ℝ) := by
  have he : (51 : ℝ) ≤ Real.exp 50 := by
    nlinarith [Real.add_one_le_exp (50 : ℝ)]
  have hen : 0 ≤ Real.exp (-50) := (Real.exp_pos (-50)).le
  have hm : 51 * Real.exp (-50) ≤ 1 := by
    calc
      51 * Real.exp (-50) ≤ Real.exp 50 * Real.exp (-50) :=
        mul_le_mul_of_nonneg_right he hen
      _ = 1 := by
        rw [← Real.exp_add]
        norm_num
  norm_num at hm ⊢
  nlinarith

theorem gap12 (ξ₁ ξ₂ : ℝ) (h₁ : ξ₁ ∈ Set.Icc (0 : ℝ) 50)
    (h₂ : ξ₂ ∈ Set.Icc (50 : ℝ) 100) :
    twoPointValue ξ₁ ξ₂ > (1 / 200 : ℝ) := by
  calc
    twoPointValue ξ₁ ξ₂ > (1 - Real.exp (-50)) / (100 + ξ₁) := gap9 ξ₁ ξ₂ h₁ h₂
    _ ≥ (1 - Real.exp (-50)) / 150 := gap10 ξ₁ h₁
    _ > 1 / 200 := gap11

theorem gap13 :
    (1 / 200 : ℝ) < I := by
  obtain ⟨ξ₁, hξ₁, ξ₂, hξ₂, hI⟩ := gap4
  rw [hI]
  exact gap12 ξ₁ ξ₂ hξ₁ hξ₂

theorem gap14 :
    I < (1 / 100 : ℝ) := by
  obtain ⟨ξ₁, hξ₁, ξ₂, hξ₂, hI⟩ := gap4
  rw [hI]
  exact gap8 ξ₁ ξ₂ hξ₁ hξ₂

theorem gap15 :
    (1 / 200 : ℝ) < (1 / 100 : ℝ) := by
  norm_num

theorem gap16 :
    I = (1 / 100 : ℝ) - (1 / 200 : ℝ) * θ := by
  unfold θ
  ring

theorem gap17 :
    0 < θ := by
  unfold θ
  nlinarith [gap14]

theorem gap18 :
    θ < 1 := by
  unfold θ
  nlinarith [gap13]

theorem gap19 :
    ∃ ξ ∈ Set.Icc (0 : ℝ) 100,
      I = 1 / (ξ + 100) * ∫ x in 0..100, Real.exp (-x) := by
  obtain ⟨ξ, hξ, hI⟩ := integrandMeanValue
    (a := (0 : ℝ)) (b := 100) (by norm_num) (by norm_num)
  refine ⟨ξ, hξ, ?_⟩
  simpa [I, add_comm] using hI

theorem gap20 (ξ : ℝ) :
    1 / (ξ + 100) * (∫ x in 0..100, Real.exp (-x)) =
      1 / (ξ + 100) * (1 - 1 / Real.exp 100) := by
  rw [expNegIntegral]
  simp only [neg_zero, Real.exp_zero]
  rw [show (-100 : ℝ) = -(100 : ℝ) by norm_num, Real.exp_neg]
  ring

theorem gap21 :
    ∃ ξ ∈ Set.Icc (0 : ℝ) 100,
      I = 1 / (ξ + 100) * (1 - 1 / Real.exp 100) := by
  obtain ⟨ξ, hξ, hI⟩ := gap19
  exact ⟨ξ, hξ, hI.trans (gap20 ξ)⟩

theorem gap22 :
    ∃ ξ ∈ Set.Icc (0 : ℝ) 100, θ = θFunction ξ := by
  obtain ⟨ξ, hξ, hI⟩ := gap21
  refine ⟨ξ, hξ, ?_⟩
  unfold θ θFunction
  rw [hI]
  have hd : ξ + 100 ≠ 0 := by nlinarith [hξ.1]
  have hd' : 100 + ξ ≠ 0 := by nlinarith [hξ.1]
  have he : Real.exp 100 ≠ 0 := ne_of_gt (Real.exp_pos 100)
  field_simp [hd, hd', he]
  ring

theorem gap23 (ξ : ℝ) :
    θFunction ξ = 2 / (100 + ξ) * (ξ + 100 / Real.exp 100) := by
  rfl

theorem gap24 :
    ∃ ξ ∈ Set.Icc (0 : ℝ) 100,
      θ = 2 / (100 + ξ) * (ξ + 100 / Real.exp 100) := by
  obtain ⟨ξ, hξ, hθ⟩ := gap22
  exact ⟨ξ, hξ, hθ.trans (gap23 ξ)⟩

theorem gap25 (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 100) :
    HasDerivAt θFunction
      (200 * (1 - Real.exp (-100)) / (100 + ξ) ^ 2) ξ := by
  have hd : 100 + ξ ≠ 0 := by nlinarith [hξ.1]
  have he : Real.exp 100 ≠ 0 := ne_of_gt (Real.exp_pos 100)
  have hraw :=
    (((hasDerivAt_const ξ (2 : ℝ)).mul
      ((hasDerivAt_id ξ).add
        (hasDerivAt_const ξ (100 / Real.exp 100)))).div
      ((hasDerivAt_const ξ (100 : ℝ)).add (hasDerivAt_id ξ)) hd)
  have hquot : HasDerivAt
      (fun x : ℝ => (2 * (x + 100 / Real.exp 100)) / (100 + x))
      ((2 * (100 + ξ) - 2 * (ξ + 100 / Real.exp 100)) /
        (100 + ξ) ^ 2) ξ := by
    convert hraw using 1 <;> simp
  have hcoeff :
      2 * (100 + ξ) - 2 * (ξ + 100 / Real.exp 100) =
        200 * (1 - Real.exp (-100)) := by
    rw [show (-100 : ℝ) = -(100 : ℝ) by norm_num, Real.exp_neg]
    field_simp [he] <;> ring
  rw [hcoeff] at hquot
  have hfun :
      (fun x : ℝ => (2 * (x + 100 / Real.exp 100)) / (100 + x)) =
        θFunction := by
    funext x
    unfold θFunction
    ring
  rw [hfun] at hquot
  exact hquot

theorem gap26 (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 100) :
    0 < 200 * (1 - Real.exp (-100)) / (100 + ξ) ^ 2 := by
  have hn : 0 < 1 - Real.exp (-100) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hd : 0 < (100 + ξ) ^ 2 := sq_pos_of_pos (by nlinarith [hξ.1])
  positivity

theorem gap27 (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 100) :
    0 < deriv θFunction ξ := by
  rw [(gap25 ξ hξ).deriv]
  exact gap26 ξ hξ

theorem gap28 :
    StrictMonoOn θFunction (Set.Icc (0 : ℝ) 100) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 100)
  · intro x hx
    exact (gap25 x hx).continuousAt.continuousWithinAt
  · intro x hx
    apply gap27 x
    rw [interior_Icc] at hx
    exact ⟨hx.1.le, hx.2.le⟩

theorem gap29 (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 100) :
    θFunction 0 ≤ θFunction ξ := by
  exact gap28.monotoneOn (by norm_num) hξ hξ.1

theorem gap30 (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 100) :
    θFunction ξ ≤ θFunction 100 := by
  exact gap28.monotoneOn hξ (by norm_num) hξ.2

theorem gap31 :
    θFunction 0 ≤ θFunction 100 := by
  exact gap29 100 (by norm_num)

theorem gap32 :
    2 / Real.exp 100 ≤ θ := by
  obtain ⟨ξ, hξ, hθ⟩ := gap22
  have hmono := gap29 ξ hξ
  rw [← hθ] at hmono
  have he : Real.exp 100 ≠ 0 := ne_of_gt (Real.exp_pos 100)
  have hzero : θFunction 0 = 2 / Real.exp 100 := by
    unfold θFunction
    field_simp [he]
    ring
  simpa [hzero] using hmono

theorem gap33 :
    θ ≤ 1 + 1 / Real.exp 100 := by
  obtain ⟨ξ, hξ, hθ⟩ := gap22
  have hmono := gap30 ξ hξ
  rw [← hθ] at hmono
  have he : Real.exp 100 ≠ 0 := ne_of_gt (Real.exp_pos 100)
  have hhundred : θFunction 100 = 1 + 1 / Real.exp 100 := by
    unfold θFunction
    field_simp [he]
    ring
  simpa [hhundred] using hmono

theorem gap34 :
    2 / Real.exp 100 ≤ 1 + 1 / Real.exp 100 := by
  have he : (1 : ℝ) ≤ Real.exp 100 := Real.one_le_exp (by norm_num)
  have hp : 0 < Real.exp 100 := Real.exp_pos 100
  have hi : 1 / Real.exp 100 ≤ (1 : ℝ) := by
    rw [div_le_one hp]
    exact he
  calc
    2 / Real.exp 100 = 2 * (1 / Real.exp 100) := by ring
    _ ≤ 1 + 1 / Real.exp 100 := by nlinarith

theorem gap35 :
    2 / Real.exp 100 ≤ θ := by
  exact gap32

theorem gap36 :
    θ < 1 := by
  exact gap18

theorem gap37 :
    2 / Real.exp 100 < (1 : ℝ) := by
  have he : (101 : ℝ) ≤ Real.exp 100 := by
    nlinarith [Real.add_one_le_exp (100 : ℝ)]
  have hp : 0 < Real.exp 100 := Real.exp_pos 100
  rw [div_lt_one hp]
  linarith

theorem gap38 :
    ∃ ξ : ℕ → ℝ,
      (∀ n, ξ n ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ n, powerIntegral n =
        1 / (1 + ξ n) * (∫ x in 0..1, x ^ n) := by
  have hpoint : ∀ n : ℕ, ∃ x ∈ Set.Icc (0 : ℝ) 1,
      powerIntegral n = 1 / (1 + x) * (∫ y in 0..1, y ^ n) := by
    intro n
    have hgcont : ContinuousOn (fun x : ℝ => x ^ n) (Set.uIcc (0 : ℝ) 1) :=
      (continuous_id.pow n).continuousOn
    have hg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x ^ n := by
      intro x hx
      exact pow_nonneg hx.1 n
    have hG : 0 < ∫ x : ℝ in 0..1, x ^ n := by
      rw [integralPowZeroOne]
      positivity
    obtain ⟨x, hx, h⟩ := reciprocalWeightedMeanValue
      (c := (1 : ℝ)) (a := 0) (b := 1)
      (hab := by norm_num) (hca := by norm_num)
      (g := fun x : ℝ => x ^ n) (hgcont := hgcont) (hg := hg) (hG := hG)
    refine ⟨x, hx, ?_⟩
    simpa [powerIntegral, div_eq_mul_inv, mul_comm] using h
  choose ξ hξ hEq using hpoint
  exact ⟨ξ, hξ, hEq⟩

theorem gap39 (ξ : ℕ → ℝ) :
    (fun n => 1 / (1 + ξ n) * (∫ x in 0..1, x ^ n)) =
      meanValueSequence ξ := by
  funext n
  unfold meanValueSequence
  rw [integralPowZeroOne]

theorem gap40 (ξ : ℕ → ℝ) (hξ : ∀ n, ξ n ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (meanValueSequence ξ) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hncast : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnlarge : 1 / ε < (n : ℝ) := lt_of_lt_of_le hN hncast
  have hnpos : 0 < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.zero_lt_succ n
  have hrec : ε * (1 / ε) = 1 := by field_simp [ne_of_gt hε]
  have hscaled : ε * (1 / ε) < ε * (n : ℝ) :=
    mul_lt_mul_of_pos_left hnlarge hε
  have hcastadd : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by norm_num
  have hsmall : 1 / (((n + 1 : ℕ) : ℝ)) < ε := by
    rw [div_lt_iff₀ hnpos, hcastadd]
    nlinarith
  have hx := hξ n
  have hden : 0 < 1 + ξ n := by nlinarith [hx.1]
  have hfac0 : 0 ≤ 1 / (1 + ξ n) := (one_div_pos.mpr hden).le
  have hfac1 : 1 / (1 + ξ n) ≤ 1 := by
    rw [div_le_one hden]
    nlinarith [hx.1]
  have hrecip0 : 0 ≤ 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
  rw [Real.dist_eq]
  unfold meanValueSequence
  have hprod0 : 0 ≤ 1 / (1 + ξ n) * (1 / (((n + 1 : ℕ) : ℝ))) :=
    mul_nonneg hfac0 hrecip0
  rw [sub_zero, abs_of_nonneg hprod0]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hfac1 hrecip0) (by simpa using hsmall)

theorem gap41 :
    Tendsto powerIntegral atTop (nhds 0) := by
  obtain ⟨ξ, hξ, hpower⟩ := gap38
  have hmean := gap40 ξ hξ
  have heq := gap39 ξ
  rw [← heq] at hmean
  exact hmean.congr' (Filter.Eventually.of_forall (fun n => (hpower n).symm))

theorem gap42 (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hεπ : ε < Real.pi / 2) :
    0 ≤ sinePowerIntegral n := by
  have hsint := sineIntervalIntegrable n 0 (Real.pi / 2)
  have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume 0 (Real.pi / 2) :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on (by positivity) hz hsint (by
    intro x hx
    exact pow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2, Real.pi_pos])) n)
  simpa [sinePowerIntegral] using hmono

theorem gap43 (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hεπ : ε < Real.pi / 2) :
    sinePowerIntegral n ≤
      (∫ x in 0..Real.pi / 2 - ε, Real.sin x ^ n) + ε := by
  let c : ℝ := Real.pi / 2 - ε
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hcle : c ≤ Real.pi / 2 := by dsimp [c]; linarith
  have hleft := sineIntervalIntegrable n 0 c
  have hright := sineIntervalIntegrable n c (Real.pi / 2)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume c (Real.pi / 2) :=
    intervalIntegrable_const
  have hbound := intervalIntegral.integral_mono_on hcle hright hone (by
    intro x hx
    have hs0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
    have hs1 : Real.sin x ≤ 1 := Real.sin_le_one x
    simpa using pow_le_one₀ hs0 hs1)
  have hconst : (∫ _x : ℝ in c..Real.pi / 2, (1 : ℝ)) = ε := by
    simp [c]
  unfold sinePowerIntegral
  rw [← hsplit]
  rw [hconst] at hbound
  linarith

theorem gap44 (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hεπ : ε < Real.pi / 2) :
    (∫ x in 0..Real.pi / 2 - ε, Real.sin x ^ n) + ε ≤
      ε + (Real.pi / 2 - ε) *
        Real.sin (Real.pi / 2 - ε) ^ n := by
  let c : ℝ := Real.pi / 2 - ε
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hcpi : c ≤ Real.pi / 2 := by dsimp [c]; linarith
  have hsint := sineIntervalIntegrable n 0 c
  have hconst : IntervalIntegrable (fun _ : ℝ => Real.sin c ^ n)
      MeasureTheory.volume 0 c := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hc0 hsint hconst (by
    intro x hx
    have hxset : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
    have hcset : c ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [hc0, hcpi, Real.pi_pos]
    have hsle : Real.sin x ≤ Real.sin c :=
      Real.strictMonoOn_sin.monotoneOn hxset hcset hx.2
    have hs0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi
      hx.1 (by linarith [hx.2, hcpi, Real.pi_pos])
    exact pow_le_pow_left₀ hs0 hsle n)
  have heval : (∫ _x : ℝ in 0..c, Real.sin c ^ n) = c * Real.sin c ^ n := by simp
  rw [heval] at hmono
  dsimp [c] at hmono ⊢
  linarith

theorem gap45 (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hεπ : ε < Real.pi / 2) :
    0 ≤ ε + (Real.pi / 2 - ε) *
      Real.sin (Real.pi / 2 - ε) ^ n := by
  have hc : 0 ≤ Real.pi / 2 - ε := by linarith
  have hs : 0 ≤ Real.sin (Real.pi / 2 - ε) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi hc
    linarith [Real.pi_pos]
  positivity

theorem gap46 (ε : ℝ) (hε : 0 < ε)
    (hεπ : ε < Real.pi / 2) :
    Tendsto
      (fun n : ℕ => (Real.pi / 2 - ε) *
        Real.sin (Real.pi / 2 - ε) ^ n)
      atTop (nhds 0) := by
  let c : ℝ := Real.pi / 2 - ε
  have hc0 : 0 < c := by dsimp [c]; linarith
  have hcpi : c < Real.pi / 2 := by dsimp [c]; linarith
  have hcset : c ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hpiset : Real.pi / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hslt : Real.sin c < 1 := by
    have h := Real.strictMonoOn_sin hcset hpiset hcpi
    simpa using h
  have hs0 : 0 ≤ Real.sin c := Real.sin_nonneg_of_nonneg_of_le_pi
    hc0.le (by linarith [Real.pi_pos])
  have habs : |Real.sin c| < 1 := by simpa [abs_of_nonneg hs0] using hslt
  have hp : Tendsto (fun n : ℕ => Real.sin c ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs
  have hm := (tendsto_const_nhds.mul hp :
    Tendsto (fun n : ℕ => c * Real.sin c ^ n) atTop (nhds (c * 0)))
  simpa [c] using hm

theorem gap47 :
    Tendsto sinePowerIntegral atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  let ε : ℝ := min (δ / 2) (Real.pi / 4)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith) (by positivity)
  have hεπ : ε < Real.pi / 2 := by
    have hle : ε ≤ Real.pi / 4 := min_le_right _ _
    linarith [Real.pi_pos]
  have hεδ : ε < δ := by
    have hle : ε ≤ δ / 2 := min_le_left _ _
    linarith
  have hlim := gap46 ε hε hεπ
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim (δ - ε) (sub_pos.mpr hεδ)
  refine ⟨N, ?_⟩
  intro n hn
  have hdist := hN n hn
  rw [Real.dist_eq, sub_zero, abs_lt] at hdist
  have hlower := gap42 n ε hε hεπ
  have hupper := le_trans (gap43 n ε hε hεπ) (gap44 n ε hε hεπ)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlower]
  linarith

end

end ProofGap.Exercise2325
