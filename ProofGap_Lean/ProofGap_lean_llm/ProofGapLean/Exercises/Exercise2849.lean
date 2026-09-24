import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

namespace ProofGap.Exercise2849

noncomputable section

def sineTerm (h : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * h ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)

def cosineTerm (h : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * h ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

def shiftedSineTerm (x h : ℝ) (n : ℕ) : ℝ :=
  Real.sin x * cosineTerm h n + Real.cos x * sineTerm h n

def shiftedCosineTerm (x h : ℝ) (n : ℕ) : ℝ :=
  Real.cos x * cosineTerm h n - Real.sin x * sineTerm h n

theorem gap1 :
    ∀ x h : ℝ, Real.sin (x + h) =
      Real.sin x * Real.cos h + Real.cos x * Real.sin h := by
  intro x h
  exact Real.sin_add x h

theorem gap2
    (hadd :
      ∀ x h : ℝ, Real.sin (x + h) =
        Real.sin x * Real.cos h + Real.cos x * Real.sin h) :
    ∀ x h : ℝ,
      Real.sin x * Real.cos h + Real.cos x * Real.sin h =
        Real.sin x * (∑' n, cosineTerm h n) +
          Real.cos x * (∑' n, sineTerm h n) := by
  intro x h
  have hc : HasSum (cosineTerm h) (Real.cos h) := by
    simpa [cosineTerm] using Real.hasSum_cos h
  have hs : HasSum (sineTerm h) (Real.sin h) := by
    simpa [sineTerm] using Real.hasSum_sin h
  rw [hc.tsum_eq, hs.tsum_eq]

theorem gap3
    (hadd :
      ∀ x h : ℝ, Real.sin (x + h) =
        Real.sin x * Real.cos h + Real.cos x * Real.sin h)
    (hseries :
      ∀ x h : ℝ,
        Real.sin x * Real.cos h + Real.cos x * Real.sin h =
          Real.sin x * (∑' n, cosineTerm h n) +
            Real.cos x * (∑' n, sineTerm h n)) :
    ∀ x h : ℝ, Real.sin (x + h) =
      Real.sin x * (∑' n, cosineTerm h n) +
        Real.cos x * (∑' n, sineTerm h n) := by
  intro x h
  exact (hadd x h).trans (hseries x h)

theorem gap4
    (hadd :
      ∀ x h : ℝ, Real.sin (x + h) =
        Real.sin x * Real.cos h + Real.cos x * Real.sin h)
    (hseries :
      ∀ x h : ℝ,
        Real.sin x * Real.cos h + Real.cos x * Real.sin h =
          Real.sin x * (∑' n, cosineTerm h n) +
            Real.cos x * (∑' n, sineTerm h n))
    (hcombined :
      ∀ x h : ℝ, Real.sin (x + h) =
        Real.sin x * (∑' n, cosineTerm h n) +
          Real.cos x * (∑' n, sineTerm h n)) :
    ∀ x h : ℝ, Real.sin (x + h) = ∑' n, shiftedSineTerm x h n := by
  intro x h
  have hc : HasSum (cosineTerm h) (Real.cos h) := by
    simpa [cosineTerm] using Real.hasSum_cos h
  have hs : HasSum (sineTerm h) (Real.sin h) := by
    simpa [sineTerm] using Real.hasSum_sin h
  have hshift :
      HasSum (shiftedSineTerm x h)
        (Real.sin x * Real.cos h + Real.cos x * Real.sin h) := by
    simpa [shiftedSineTerm] using
      (hc.mul_left (Real.sin x)).add (hs.mul_left (Real.cos x))
  exact (hadd x h).trans hshift.tsum_eq.symm

theorem gap5
    (hsine :
      ∀ x h : ℝ, Real.sin (x + h) = ∑' n, shiftedSineTerm x h n) :
    ∀ x h : ℝ, Real.cos (x + h) = ∑' n, shiftedCosineTerm x h n := by
  intro x h
  have hc : HasSum (cosineTerm h) (Real.cos h) := by
    simpa [cosineTerm] using Real.hasSum_cos h
  have hs : HasSum (sineTerm h) (Real.sin h) := by
    simpa [sineTerm] using Real.hasSum_sin h
  have hshift :
      HasSum (shiftedCosineTerm x h)
        (Real.cos x * Real.cos h - Real.sin x * Real.sin h) := by
    simpa [shiftedCosineTerm] using
      (hc.mul_left (Real.cos x)).sub (hs.mul_left (Real.sin x))
  exact (Real.cos_add x h).trans hshift.tsum_eq.symm

theorem gap6
    (hsine :
      ∀ x h : ℝ, Real.sin (x + h) = ∑' n, shiftedSineTerm x h n)
    (hcosine :
      ∀ x h : ℝ, Real.cos (x + h) = ∑' n, shiftedCosineTerm x h n) :
    ∀ x h : ℝ, Summable (shiftedSineTerm x h) := by
  intro x h
  have hc : HasSum (cosineTerm h) (Real.cos h) := by
    simpa [cosineTerm] using Real.hasSum_cos h
  have hs : HasSum (sineTerm h) (Real.sin h) := by
    simpa [sineTerm] using Real.hasSum_sin h
  have hshift :
      HasSum (shiftedSineTerm x h)
        (Real.sin x * Real.cos h + Real.cos x * Real.sin h) := by
    simpa [shiftedSineTerm] using
      (hc.mul_left (Real.sin x)).add (hs.mul_left (Real.cos x))
  exact hshift.summable

theorem gap7
    (hsine :
      ∀ x h : ℝ, Real.sin (x + h) = ∑' n, shiftedSineTerm x h n)
    (hcosine :
      ∀ x h : ℝ, Real.cos (x + h) = ∑' n, shiftedCosineTerm x h n)
    (hsineSummable : ∀ x h : ℝ, Summable (shiftedSineTerm x h)) :
    ∀ x h : ℝ, Summable (shiftedCosineTerm x h) := by
  intro x h
  have hc : HasSum (cosineTerm h) (Real.cos h) := by
    simpa [cosineTerm] using Real.hasSum_cos h
  have hs : HasSum (sineTerm h) (Real.sin h) := by
    simpa [sineTerm] using Real.hasSum_sin h
  have hshift :
      HasSum (shiftedCosineTerm x h)
        (Real.cos x * Real.cos h - Real.sin x * Real.sin h) := by
    simpa [shiftedCosineTerm] using
      (hc.mul_left (Real.cos x)).sub (hs.mul_left (Real.sin x))
  exact hshift.summable

end

end ProofGap.Exercise2849
