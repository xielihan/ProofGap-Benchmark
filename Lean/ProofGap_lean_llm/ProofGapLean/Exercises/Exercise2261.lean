import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2261

noncomputable section

def weightedIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, f x * Real.cos x

theorem gap1 (f : ℝ → ℝ) (hf : Continuous f) :
    weightedIntegral f 0 (2 * Real.pi) =
      weightedIntegral f 0 (Real.pi / 2) +
        weightedIntegral f (Real.pi / 2) Real.pi +
        weightedIntegral f Real.pi (3 * Real.pi / 2) +
        weightedIntegral f (3 * Real.pi / 2) (2 * Real.pi) := by
  unfold weightedIntegral
  have hcont : Continuous (fun x : ℝ => f x * Real.cos x) :=
    hf.mul Real.continuous_cos
  have hwhole :
      (∫ x in 0..2 * Real.pi, f x * Real.cos x) =
        (∫ x in 0..Real.pi, f x * Real.cos x) +
          ∫ x in Real.pi..2 * Real.pi, f x * Real.cos x := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 Real.pi)
      (hcont.intervalIntegrable Real.pi (2 * Real.pi))).symm
  have hleft :
      (∫ x in 0..Real.pi, f x * Real.cos x) =
        (∫ x in 0..Real.pi / 2, f x * Real.cos x) +
          ∫ x in Real.pi / 2..Real.pi, f x * Real.cos x := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 (Real.pi / 2))
      (hcont.intervalIntegrable (Real.pi / 2) Real.pi)).symm
  have hright :
      (∫ x in Real.pi..2 * Real.pi, f x * Real.cos x) =
        (∫ x in Real.pi..3 * Real.pi / 2, f x * Real.cos x) +
          ∫ x in 3 * Real.pi / 2..2 * Real.pi, f x * Real.cos x := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable Real.pi (3 * Real.pi / 2))
      (hcont.intervalIntegrable (3 * Real.pi / 2) (2 * Real.pi))).symm
  rw [hwhole, hleft, hright]
  simp only [add_assoc]

theorem gap2 (f : ℝ → ℝ) (hf : Continuous f) :
    weightedIntegral f 0 (2 * Real.pi) =
      (∫ t in 0..1, (f (Real.arcsin t) - f (Real.pi - Real.arcsin t))) +
      ∫ t in (-1)..0,
        (f (2 * Real.pi + Real.arcsin t) - f (Real.pi - Real.arcsin t)) := by
  let g₁ : ℝ → ℝ := fun t => f (Real.arcsin t)
  let g₂ : ℝ → ℝ := fun t => f (Real.pi - Real.arcsin t)
  let g₄ : ℝ → ℝ := fun t => f (2 * Real.pi + Real.arcsin t)
  have hg₁ : Continuous g₁ := hf.comp Real.continuous_arcsin
  have hg₂ : Continuous g₂ :=
    hf.comp (continuous_const.sub Real.continuous_arcsin)
  have hg₄ : Continuous g₄ :=
    hf.comp (continuous_const.add Real.continuous_arcsin)
  have hsubst (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) :
      (∫ x in a..b, g (Real.sin x) * Real.cos x) =
        ∫ t in Real.sin a..Real.sin b, g t := by
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt Real.sin (Real.cos x) x := by
      intro x hx
      exact Real.hasDerivAt_sin x
    simpa [mul_comm] using
      (intervalIntegral.integral_comp_mul_deriv
        (f := Real.sin) (f' := Real.cos) (g := g)
        hderiv
        Real.continuous_cos.continuousOn
        hg)
  have hpi : 0 < Real.pi := Real.pi_pos
  have h0q : 0 ≤ Real.pi / 2 := by linarith
  have hqpi : Real.pi / 2 ≤ Real.pi := by linarith
  have hpithree : Real.pi ≤ 3 * Real.pi / 2 := by linarith
  have hthreefour : 3 * Real.pi / 2 ≤ 2 * Real.pi := by linarith
  have hs3 : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
      Real.sin_add]
    simp
  have hs2 : Real.sin (2 * Real.pi) = 0 := by
    rw [show 2 * Real.pi = Real.pi + Real.pi by ring, Real.sin_add]
    simp
  have h₁ : weightedIntegral f 0 (Real.pi / 2) =
      ∫ t in 0..1, g₁ t := by
    unfold weightedIntegral
    calc
      (∫ x in 0..Real.pi / 2, f x * Real.cos x) =
          ∫ x in 0..Real.pi / 2, g₁ (Real.sin x) * Real.cos x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
          simpa [Set.uIcc_of_le h0q] using hx
        have has : Real.arcsin (Real.sin x) = x :=
          Real.arcsin_sin (by linarith [hx'.1, hpi]) hx'.2
        dsimp [g₁]
        rw [has]
      _ = ∫ t in 0..1, g₁ t := by
        simpa using hsubst g₁ hg₁ 0 (Real.pi / 2)
  have h₂ : weightedIntegral f (Real.pi / 2) Real.pi =
      -(∫ t in 0..1, g₂ t) := by
    unfold weightedIntegral
    calc
      (∫ x in Real.pi / 2..Real.pi, f x * Real.cos x) =
          ∫ x in Real.pi / 2..Real.pi, g₂ (Real.sin x) * Real.cos x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc (Real.pi / 2) Real.pi := by
          simpa [Set.uIcc_of_le hqpi] using hx
        have has : Real.arcsin (Real.sin x) = Real.pi - x := by
          have h := Real.arcsin_sin
            (x := Real.pi - x)
            (by linarith [hx'.2]) (by linarith [hx'.1])
          rwa [Real.sin_pi_sub] at h
        have harg : Real.pi - Real.arcsin (Real.sin x) = x := by
          rw [has]
          ring
        dsimp [g₂]
        rw [harg]
      _ = ∫ t in Real.sin (Real.pi / 2)..Real.sin Real.pi, g₂ t :=
        hsubst g₂ hg₂ (Real.pi / 2) Real.pi
      _ = ∫ t in (1 : ℝ)..0, g₂ t := by simp
      _ = -(∫ t in 0..1, g₂ t) := by
        rw [intervalIntegral.integral_symm]
  have h₃ : weightedIntegral f Real.pi (3 * Real.pi / 2) =
      -(∫ t in (-1)..0, g₂ t) := by
    unfold weightedIntegral
    calc
      (∫ x in Real.pi..3 * Real.pi / 2, f x * Real.cos x) =
          ∫ x in Real.pi..3 * Real.pi / 2, g₂ (Real.sin x) * Real.cos x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc Real.pi (3 * Real.pi / 2) := by
          simpa [Set.uIcc_of_le hpithree] using hx
        have has : Real.arcsin (Real.sin x) = Real.pi - x := by
          have h := Real.arcsin_sin
            (x := Real.pi - x)
            (by linarith [hx'.2]) (by linarith [hx'.1, hpi])
          rwa [Real.sin_pi_sub] at h
        have harg : Real.pi - Real.arcsin (Real.sin x) = x := by
          rw [has]
          ring
        dsimp [g₂]
        rw [harg]
      _ = ∫ t in Real.sin Real.pi..Real.sin (3 * Real.pi / 2), g₂ t :=
        hsubst g₂ hg₂ Real.pi (3 * Real.pi / 2)
      _ = ∫ t in (0 : ℝ)..(-1), g₂ t := by simp [hs3]
      _ = -(∫ t in (-1)..0, g₂ t) := by
        rw [intervalIntegral.integral_symm]
  have h₄ : weightedIntegral f (3 * Real.pi / 2) (2 * Real.pi) =
      ∫ t in (-1)..0, g₄ t := by
    unfold weightedIntegral
    calc
      (∫ x in 3 * Real.pi / 2..2 * Real.pi, f x * Real.cos x) =
          ∫ x in 3 * Real.pi / 2..2 * Real.pi,
            g₄ (Real.sin x) * Real.cos x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc (3 * Real.pi / 2) (2 * Real.pi) := by
          simpa [Set.uIcc_of_le hthreefour] using hx
        have hsin : Real.sin (x - 2 * Real.pi) = Real.sin x := by
          rw [Real.sin_sub]
          simp [hs2]
        have has : Real.arcsin (Real.sin x) = x - 2 * Real.pi := by
          have h := Real.arcsin_sin
            (x := x - 2 * Real.pi)
            (by linarith [hx'.1]) (by linarith [hx'.2, hpi])
          rwa [hsin] at h
        have harg : 2 * Real.pi + Real.arcsin (Real.sin x) = x := by
          rw [has]
          ring
        dsimp [g₄]
        rw [harg]
      _ = ∫ t in Real.sin (3 * Real.pi / 2)..Real.sin (2 * Real.pi), g₄ t :=
        hsubst g₄ hg₄ (3 * Real.pi / 2) (2 * Real.pi)
      _ = ∫ t in (-1)..0, g₄ t := by simp [hs3, hs2]
  have hsub₁ :
      (∫ t in 0..1, g₁ t - g₂ t) =
        (∫ t in 0..1, g₁ t) - ∫ t in 0..1, g₂ t := by
    exact intervalIntegral.integral_sub
      (hg₁.intervalIntegrable 0 1) (hg₂.intervalIntegrable 0 1)
  have hsub₂ :
      (∫ t in (-1)..0, g₄ t - g₂ t) =
        (∫ t in (-1)..0, g₄ t) - ∫ t in (-1)..0, g₂ t := by
    exact intervalIntegral.integral_sub
      (hg₄.intervalIntegrable (-1) 0) (hg₂.intervalIntegrable (-1) 0)
  change weightedIntegral f 0 (2 * Real.pi) =
    (∫ t in 0..1, g₁ t - g₂ t) +
      ∫ t in (-1)..0, g₄ t - g₂ t
  rw [gap1 f hf, h₁, h₂, h₃, h₄, hsub₁, hsub₂]
  ring

end

end ProofGap.Exercise2261
