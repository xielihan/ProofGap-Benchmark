import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2982

noncomputable section

open scoped Interval

def cosineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi, f x * Real.cos ((n : ℝ) * x)

def sineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi, f x * Real.sin ((n : ℝ) * x)

def splitCosine (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ((∫ x in -Real.pi..0, f x * Real.cos ((n : ℝ) * x)) +
      ∫ x in 0..Real.pi, f x * Real.cos ((n : ℝ) * x))

def negativeReversedCosine (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    (-(∫ x in 0..Real.pi, f x * Real.cos ((n : ℝ) * x)) -
      ∫ x in -Real.pi..0, f x * Real.cos ((n : ℝ) * x))

private theorem cosineIntegral_neg_reflect (φ ψ : ℝ → ℝ)
    (hrel : ∀ x, φ (-x) = -ψ x) (n : ℕ) (a b : ℝ) :
    (∫ x in a..b, φ x * Real.cos ((n : ℝ) * x)) =
      -(∫ x in -b..-a, ψ x * Real.cos ((n : ℝ) * x)) := by
  apply neg_injective
  simp only [neg_neg]
  rw [← intervalIntegral.integral_neg]
  calc
    (∫ x in a..b, -(φ x * Real.cos ((n : ℝ) * x))) =
        ∫ x in a..b,
          (fun y => ψ y * Real.cos ((n : ℝ) * y)) (-x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxrel : φ x = -ψ (-x) := by
        simpa only [neg_neg] using hrel (-x)
      change -(φ x * Real.cos ((n : ℝ) * x)) =
        ψ (-x) * Real.cos ((n : ℝ) * (-x))
      rw [hxrel, mul_neg, Real.cos_neg]
      ring
    _ = ∫ x in -b..-a, ψ x * Real.cos ((n : ℝ) * x) := by
      exact intervalIntegral.integral_comp_neg
        (fun x => ψ x * Real.cos ((n : ℝ) * x))

private theorem sineIntegral_neg_reflect (φ ψ : ℝ → ℝ)
    (hrel : ∀ x, φ (-x) = -ψ x) (n : ℕ) (a b : ℝ) :
    (∫ x in a..b, φ x * Real.sin ((n : ℝ) * x)) =
      ∫ x in -b..-a, ψ x * Real.sin ((n : ℝ) * x) := by
  calc
    (∫ x in a..b, φ x * Real.sin ((n : ℝ) * x)) =
        ∫ x in a..b,
          (fun y => ψ y * Real.sin ((n : ℝ) * y)) (-x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxrel : φ x = -ψ (-x) := by
        simpa only [neg_neg] using hrel (-x)
      change φ x * Real.sin ((n : ℝ) * x) =
        ψ (-x) * Real.sin ((n : ℝ) * (-x))
      rw [hxrel, mul_neg, Real.sin_neg]
      ring
    _ = ∫ x in -b..-a, ψ x * Real.sin ((n : ℝ) * x) := by
      exact intervalIntegral.integral_comp_neg
        (fun x => ψ x * Real.sin ((n : ℝ) * x))

private theorem cosineCoefficient_neg_reflect (φ ψ : ℝ → ℝ)
    (hrel : ∀ x, φ (-x) = -ψ x) (n : ℕ) :
    cosineCoefficient φ n = -cosineCoefficient ψ n := by
  unfold cosineCoefficient
  rw [cosineIntegral_neg_reflect φ ψ hrel n (-Real.pi) Real.pi]
  simp

private theorem sineCoefficient_neg_reflect (φ ψ : ℝ → ℝ)
    (hrel : ∀ x, φ (-x) = -ψ x) (n : ℕ) :
    sineCoefficient φ n = sineCoefficient ψ n := by
  unfold sineCoefficient
  rw [sineIntegral_neg_reflect φ ψ hrel n (-Real.pi) Real.pi]
  simp

private theorem cosineIntegral_split (f : ℝ → ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi) (n : ℕ) :
    (∫ x in -Real.pi..Real.pi, f x * Real.cos ((n : ℝ) * x)) =
      (∫ x in -Real.pi..0, f x * Real.cos ((n : ℝ) * x)) +
        ∫ x in 0..Real.pi, f x * Real.cos ((n : ℝ) * x) := by
  have hint : IntervalIntegrable
      (fun x => f x * Real.cos ((n : ℝ) * x)) MeasureTheory.volume
        (-Real.pi) Real.pi :=
    hf.mul_continuousOn (by fun_prop)
  symm
  apply intervalIntegral.integral_add_adjacent_intervals
  · apply hint.mono_set
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ (0 : ℝ)),
      Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    exact Set.Icc_subset_Icc_right Real.pi_pos.le
  · apply hint.mono_set
    rw [Set.uIcc_of_le Real.pi_pos.le,
      Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    exact Set.Icc_subset_Icc_left (by linarith [Real.pi_pos] : -Real.pi ≤ (0 : ℝ))

private theorem cosineCoefficient_eq_splitCosine (f : ℝ → ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi) (n : ℕ) :
    cosineCoefficient f n = splitCosine f n := by
  unfold cosineCoefficient splitCosine
  rw [cosineIntegral_split f hf n]

private theorem negativeReversedCosine_eq_neg_coefficient (f : ℝ → ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi) (n : ℕ) :
    negativeReversedCosine f n = -cosineCoefficient f n := by
  unfold negativeReversedCosine cosineCoefficient
  rw [cosineIntegral_split f hf n]
  ring

theorem gap1 (φ : ℝ → ℝ) (c : ℕ → ℝ)
    (hc : ∀ n, c n = cosineCoefficient φ n) :
    ∀ n, c n = cosineCoefficient φ n := by
  exact hc

theorem gap2 (φ : ℝ → ℝ) (s : ℕ → ℝ)
    (hs : ∀ n, s n = sineCoefficient φ n) :
    ∀ n, 1 ≤ n → s n = sineCoefficient φ n := by
  intro n hn
  exact hs n

theorem gap3 (ψ : ℝ → ℝ) (α : ℕ → ℝ)
    (hα : ∀ n, α n = cosineCoefficient ψ n) :
    ∀ n, α n = cosineCoefficient ψ n := by
  exact hα

theorem gap4 (ψ : ℝ → ℝ) (β : ℕ → ℝ)
    (hβ : ∀ n, β n = sineCoefficient ψ n) :
    ∀ n, 1 ≤ n → β n = sineCoefficient ψ n := by
  intro n hn
  exact hβ n

theorem gap5 (φ : ℝ → ℝ) (c : ℕ → ℝ)
    (hφ : IntervalIntegrable φ MeasureTheory.volume (-Real.pi) Real.pi)
    (hc : ∀ n, c n = cosineCoefficient φ n) :
    ∀ n, c n = splitCosine φ n := by
  intro n
  rw [hc n]
  exact cosineCoefficient_eq_splitCosine φ hφ n

theorem gap6 (φ ψ : ℝ → ℝ) (c : ℕ → ℝ)
    (hrel : ∀ x, φ (-x) = -ψ x)
    (hψ : IntervalIntegrable ψ MeasureTheory.volume (-Real.pi) Real.pi)
    (hc : ∀ n, c n = cosineCoefficient φ n) :
    ∀ n, c n = negativeReversedCosine ψ n := by
  intro n
  rw [hc n, cosineCoefficient_neg_reflect φ ψ hrel n]
  exact (negativeReversedCosine_eq_neg_coefficient ψ hψ n).symm

theorem gap7 (ψ : ℝ → ℝ)
    (hψ : IntervalIntegrable ψ MeasureTheory.volume (-Real.pi) Real.pi) :
    ∀ n, negativeReversedCosine ψ n = -cosineCoefficient ψ n := by
  exact negativeReversedCosine_eq_neg_coefficient ψ hψ

theorem gap8 (ψ : ℝ → ℝ) (α : ℕ → ℝ)
    (hα : ∀ n, α n = cosineCoefficient ψ n) :
    ∀ n, -cosineCoefficient ψ n = -α n := by
  intro n
  rw [hα n]

theorem gap9 (φ ψ : ℝ → ℝ) (c α : ℕ → ℝ)
    (hrel : ∀ x, φ (-x) = -ψ x)
    (hc : ∀ n, c n = cosineCoefficient φ n)
    (hα : ∀ n, α n = cosineCoefficient ψ n) :
    ∀ n, c n = -α n := by
  intro n
  rw [hc n, hα n]
  exact cosineCoefficient_neg_reflect φ ψ hrel n

theorem gap10 (φ ψ : ℝ → ℝ) (s β : ℕ → ℝ)
    (hrel : ∀ x, φ (-x) = -ψ x)
    (hs : ∀ n, s n = sineCoefficient φ n)
    (hβ : ∀ n, β n = sineCoefficient ψ n) :
    ∀ n, 1 ≤ n → s n = β n := by
  intro n hn
  rw [hs n, hβ n]
  exact sineCoefficient_neg_reflect φ ψ hrel n

theorem gap11 (φ ψ : ℝ → ℝ) (c α : ℕ → ℝ)
    (hrel : ∀ x, φ (-x) = -ψ x)
    (hc : ∀ n, c n = cosineCoefficient φ n)
    (hα : ∀ n, α n = cosineCoefficient ψ n) :
    ∀ n, c n = -α n := by
  exact gap9 φ ψ c α hrel hc hα

theorem gap12 (φ ψ : ℝ → ℝ) (s β : ℕ → ℝ)
    (hrel : ∀ x, φ (-x) = -ψ x)
    (hs : ∀ n, s n = sineCoefficient φ n)
    (hβ : ∀ n, β n = sineCoefficient ψ n) :
    ∀ n, 1 ≤ n → s n = β n := by
  exact gap10 φ ψ s β hrel hs hβ

end

end ProofGap.Exercise2982
