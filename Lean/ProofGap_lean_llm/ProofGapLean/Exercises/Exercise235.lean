import ProofGapLean.Prelude.Core
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise235

noncomputable section

def sumFn (f₁ f₂ : ℝ → ℝ) (x : ℝ) : ℝ := f₁ x + f₂ x
def productFn (f₁ f₂ : ℝ → ℝ) (x : ℝ) : ℝ := f₁ x * f₂ x
def commonPeriod (T : ℝ) (k₁ k₂ : ℕ) : ℝ :=
  (k₁ : ℝ) * (k₂ : ℝ) * T

/-- Exercise 235, gap 1. -/
private theorem periodic_values_at_commonPeriod
    (f₁ f₂ : ℝ → ℝ) (T T₁ T₂ : ℝ) (k₁ k₂ : ℕ)
    (hT₁ : T₁ = T * k₁) (hT₂ : T₂ = T * k₂)
    (hp₁ : Function.Periodic f₁ T₁)
    (hp₂ : Function.Periodic f₂ T₂) (x : ℝ) :
    f₁ (x + commonPeriod T k₁ k₂) = f₁ x ∧
      f₂ (x + commonPeriod T k₁ k₂) = f₂ x := by
  have hcommon₁ : commonPeriod T k₁ k₂ = (k₂ : ℝ) * T₁ := by
    rw [commonPeriod, hT₁]
    ring
  have hcommon₂ : commonPeriod T k₁ k₂ = (k₁ : ℝ) * T₂ := by
    rw [commonPeriod, hT₂]
    ring
  constructor
  · rw [hcommon₁]
    simpa only [nsmul_eq_mul] using hp₁.nsmul k₂ x
  · rw [hcommon₂]
    simpa only [nsmul_eq_mul] using hp₂.nsmul k₁ x

theorem gap1 (f₁ : ℝ → ℝ) (T₁ : ℝ) (k₂ : ℕ)
    (hperiod : Function.Periodic f₁ T₁) : ∀ x,
    f₁ (x + (k₂ : ℝ) * T₁) = f₁ x := by
  intro x
  simpa only [nsmul_eq_mul] using hperiod.nsmul k₂ x

/-- Exercise 235, gap 2. -/
theorem gap2 (f₂ : ℝ → ℝ) (T₂ : ℝ) (k₁ : ℕ)
    (hperiod : Function.Periodic f₂ T₂) : ∀ x,
    f₂ (x + (k₁ : ℝ) * T₂) = f₂ x := by
  intro x
  simpa only [nsmul_eq_mul] using hperiod.nsmul k₁ x

/-- Exercise 235, gap 3. -/
theorem gap3 (f₁ f₂ : ℝ → ℝ) (T : ℝ) (k₁ k₂ : ℕ) : ∀ x,
    sumFn f₁ f₂ (x + commonPeriod T k₁ k₂) =
      f₁ (x + commonPeriod T k₁ k₂) +
        f₂ (x + commonPeriod T k₁ k₂) := by
  intro x
  rfl

/-- Exercise 235, gap 4. -/
theorem gap4 (f₁ f₂ : ℝ → ℝ) (T T₁ T₂ : ℝ) (k₁ k₂ : ℕ)
    (hT₁ : T₁ = T * k₁) (hT₂ : T₂ = T * k₂)
    (hp₁ : Function.Periodic f₁ T₁)
    (hp₂ : Function.Periodic f₂ T₂) : ∀ x,
    f₁ (x + commonPeriod T k₁ k₂) +
        f₂ (x + commonPeriod T k₁ k₂) =
      f₁ x + f₂ x := by
  intro x
  rcases periodic_values_at_commonPeriod f₁ f₂ T T₁ T₂ k₁ k₂ hT₁ hT₂ hp₁ hp₂ x with
    ⟨hf₁, hf₂⟩
  rw [hf₁, hf₂]

/-- Exercise 235, gap 5. -/
theorem gap5 (f₁ f₂ : ℝ → ℝ) : ∀ x,
    f₁ x + f₂ x = sumFn f₁ f₂ x := by
  intro x
  rfl

/-- Exercise 235, gap 6. -/
theorem gap6 (f₁ f₂ : ℝ → ℝ) (T T₁ T₂ : ℝ) (k₁ k₂ : ℕ)
    (hT₁ : T₁ = T * k₁) (hT₂ : T₂ = T * k₂)
    (hp₁ : Function.Periodic f₁ T₁)
    (hp₂ : Function.Periodic f₂ T₂) : ∀ x,
    sumFn f₁ f₂ (x + commonPeriod T k₁ k₂) =
      sumFn f₁ f₂ x := by
  intro x
  simpa [sumFn] using
    (gap4 f₁ f₂ T T₁ T₂ k₁ k₂ hT₁ hT₂ hp₁ hp₂ x)

/-- Exercise 235, gap 7. -/
theorem gap7 (f₁ f₂ : ℝ → ℝ) (T : ℝ) (k₁ k₂ : ℕ) : ∀ x,
    productFn f₁ f₂ (x + commonPeriod T k₁ k₂) =
      f₁ (x + commonPeriod T k₁ k₂) *
        f₂ (x + commonPeriod T k₁ k₂) := by
  intro x
  rfl

/-- Exercise 235, gap 8. -/
theorem gap8 (f₁ f₂ : ℝ → ℝ) (T T₁ T₂ : ℝ) (k₁ k₂ : ℕ)
    (hT₁ : T₁ = T * k₁) (hT₂ : T₂ = T * k₂)
    (hp₁ : Function.Periodic f₁ T₁)
    (hp₂ : Function.Periodic f₂ T₂) : ∀ x,
    f₁ (x + commonPeriod T k₁ k₂) *
        f₂ (x + commonPeriod T k₁ k₂) =
      f₁ x * f₂ x := by
  intro x
  rcases periodic_values_at_commonPeriod f₁ f₂ T T₁ T₂ k₁ k₂ hT₁ hT₂ hp₁ hp₂ x with
    ⟨hf₁, hf₂⟩
  rw [hf₁, hf₂]

/-- Exercise 235, gap 9. -/
theorem gap9 (f₁ f₂ : ℝ → ℝ) : ∀ x,
    f₁ x * f₂ x = productFn f₁ f₂ x := by
  intro x
  rfl

/-- Exercise 235, gap 10. -/
theorem gap10 (f₁ f₂ : ℝ → ℝ) (T T₁ T₂ : ℝ) (k₁ k₂ : ℕ)
    (hT₁ : T₁ = T * k₁) (hT₂ : T₂ = T * k₂)
    (hp₁ : Function.Periodic f₁ T₁)
    (hp₂ : Function.Periodic f₂ T₂) : ∀ x,
    productFn f₁ f₂ (x + commonPeriod T k₁ k₂) =
      productFn f₁ f₂ x := by
  intro x
  simpa [productFn] using
    (gap8 f₁ f₂ T T₁ T₂ k₁ k₂ hT₁ hT₂ hp₁ hp₂ x)

/-- Exercise 235, gap 11. -/
theorem gap11 (f₁ f₂ : ℝ → ℝ) (T T₁ T₂ : ℝ) (k₁ k₂ : ℕ)
    (hT₁ : T₁ = T * k₁) (hT₂ : T₂ = T * k₂)
    (hp₁ : Function.Periodic f₁ T₁)
    (hp₂ : Function.Periodic f₂ T₂) :
    Function.Periodic (sumFn f₁ f₂) (commonPeriod T k₁ k₂) := by
  intro x
  exact gap6 f₁ f₂ T T₁ T₂ k₁ k₂ hT₁ hT₂ hp₁ hp₂ x

/-- Exercise 235, gap 12. -/
theorem gap12 (f₁ f₂ : ℝ → ℝ) (T T₁ T₂ : ℝ) (k₁ k₂ : ℕ)
    (hT₁ : T₁ = T * k₁) (hT₂ : T₂ = T * k₂)
    (hp₁ : Function.Periodic f₁ T₁)
    (hp₂ : Function.Periodic f₂ T₂) :
    Function.Periodic (productFn f₁ f₂) (commonPeriod T k₁ k₂) := by
  intro x
  exact gap10 f₁ f₂ T T₁ T₂ k₁ k₂ hT₁ hT₂ hp₁ hp₂ x

/-- Exercise 235, gap 13. -/
theorem gap13 (f₁ f₂ : ℝ → ℝ) (T T₁ T₂ : ℝ) (k₁ k₂ : ℕ)
    (hT₁ : T₁ = T * k₁) (hT₂ : T₂ = T * k₂)
    (hp₁ : Function.Periodic f₁ T₁)
    (hp₂ : Function.Periodic f₂ T₂) :
    Function.Periodic (fun x => f₁ x + f₂ x) (commonPeriod T k₁ k₂) ∧
      Function.Periodic (fun x => f₁ x * f₂ x) (commonPeriod T k₁ k₂) := by
  constructor
  · simpa only [sumFn] using
      (gap11 f₁ f₂ T T₁ T₂ k₁ k₂ hT₁ hT₂ hp₁ hp₂)
  · simpa only [productFn] using
      (gap12 f₁ f₂ T T₁ T₂ k₁ k₂ hT₁ hT₂ hp₁ hp₂)

end

end ProofGap.Exercise235
