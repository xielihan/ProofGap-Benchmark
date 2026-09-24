import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1456_5

noncomputable section

def amplitude (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

def PhaseData (a b φ : ℝ) : Prop :=
  Real.cos φ = a / amplitude a b ∧
    Real.sin φ = b / amplitude a b

theorem gap1 (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ φ : ℝ, PhaseData a b φ ∧
      ∀ x : ℝ, a * Real.sin x + b * Real.cos x =
        amplitude a b * Real.sin (x + φ) := by
  let r := amplitude a b
  have hs : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · have ha2 : 0 < a ^ 2 := by positivity
      nlinarith [sq_nonneg b]
    · have hb2 : 0 < b ^ 2 := by positivity
      nlinarith [sq_nonneg a]
  have hr : 0 < r := by
    dsimp [r, amplitude]
    exact Real.sqrt_pos.2 hs
  have hrsq : r ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [r, amplitude]
    rw [Real.sq_sqrt]
    positivity
  have habsa : |a| ≤ r := by
    dsimp [r, amplitude]
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
  have ha_lower : -r ≤ a := by
    nlinarith [neg_abs_le a]
  have ha_upper : a ≤ r := by
    nlinarith [le_abs_self a]
  have hc_lower : -1 ≤ a / r := by
    apply (le_div_iff₀ hr).2
    nlinarith
  have hc_upper : a / r ≤ 1 := by
    apply (div_le_iff₀ hr).2
    nlinarith
  have hunit : (a / r) ^ 2 + (b / r) ^ 2 = 1 := by
    calc
      (a / r) ^ 2 + (b / r) ^ 2 =
          (a ^ 2 + b ^ 2) / r ^ 2 := by
            field_simp [ne_of_gt hr]
            <;> ring
      _ = 1 := by
        rw [← hrsq]
        field_simp [ne_of_gt hr]
  let θ := Real.arccos (a / r)
  have hcos : Real.cos θ = a / r := by
    dsimp [θ]
    exact Real.cos_arccos hc_lower hc_upper
  have hsinnonneg : 0 ≤ Real.sin θ := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · dsimp [θ]
      exact Real.arccos_nonneg _
    · dsimp [θ]
      exact Real.arccos_le_pi _
  have hsinsq : (Real.sin θ) ^ 2 = (b / r) ^ 2 := by
    have htrig := Real.sin_sq_add_cos_sq θ
    rw [hcos] at htrig
    nlinarith [hunit]
  have hidentity (φ : ℝ)
      (hc : Real.cos φ = a / r) (hsin : Real.sin φ = b / r)
      (x : ℝ) :
      a * Real.sin x + b * Real.cos x =
        amplitude a b * Real.sin (x + φ) := by
    change a * Real.sin x + b * Real.cos x =
      r * Real.sin (x + φ)
    rw [Real.sin_add, hc, hsin]
    field_simp [ne_of_gt hr]
    <;> ring
  by_cases hb : 0 ≤ b
  · have hbdiv : 0 ≤ b / r := div_nonneg hb (le_of_lt hr)
    have hsin : Real.sin θ = b / r := by
      nlinarith [hsinsq]
    refine ⟨θ, ?_, hidentity θ hcos hsin⟩
    show Real.cos θ = a / amplitude a b ∧
      Real.sin θ = b / amplitude a b
    change Real.cos θ = a / r ∧ Real.sin θ = b / r
    exact ⟨hcos, hsin⟩
  · have hbneg : b < 0 := lt_of_not_ge hb
    have hbdiv : b / r < 0 := div_neg_of_neg_of_pos hbneg hr
    have hsinθ : Real.sin θ = -(b / r) := by
      nlinarith [hsinsq]
    have hcosneg : Real.cos (-θ) = a / r := by
      simpa using hcos
    have hsinneg : Real.sin (-θ) = b / r := by
      rw [Real.sin_neg, hsinθ]
      ring
    refine ⟨-θ, ?_, hidentity (-θ) hcosneg hsinneg⟩
    show Real.cos (-θ) = a / amplitude a b ∧
      Real.sin (-θ) = b / amplitude a b
    change Real.cos (-θ) = a / r ∧ Real.sin (-θ) = b / r
    exact ⟨hcosneg, hsinneg⟩

theorem gap2 (a b φ : ℝ) (hφ : PhaseData a b φ) :
    Real.cos φ = a / amplitude a b := by
  unfold PhaseData at hφ
  exact hφ.1

theorem gap3 (a b φ : ℝ) (hφ : PhaseData a b φ) :
    Real.sin φ = b / amplitude a b := by
  unfold PhaseData at hφ
  exact hφ.2

theorem gap4 (a b x : ℝ) :
    |a * Real.sin x + b * Real.cos x| ≤ amplitude a b := by
  by_cases hab : a ≠ 0 ∨ b ≠ 0
  · obtain ⟨φ, hφ, hrepr⟩ := gap1 a b hab
    rw [hrepr x]
    have hamp : 0 ≤ amplitude a b := by
      exact Real.sqrt_nonneg _
    calc
      |amplitude a b * Real.sin (x + φ)| =
          amplitude a b * |Real.sin (x + φ)| := by
            rw [abs_mul, abs_of_nonneg hamp]
      _ ≤ amplitude a b * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (x + φ)) hamp
      _ = amplitude a b := by ring
  · have ha : a = 0 := by
      by_contra ha
      exact hab (Or.inl ha)
    have hb : b = 0 := by
      by_contra hb
      exact hab (Or.inr hb)
    simp [ha, hb, amplitude]

theorem gap5 (a b x : ℝ) :
    |a * Real.sin x + b * Real.cos x| ≤ amplitude a b := by
  exact gap4 a b x

end

end ProofGap.Exercise1456_5
