import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set Real

namespace ProofGap.Exercise1878

noncomputable section

def domain : Set ℝ := Set.Ioi 2

def integrand (x : ℝ) : ℝ :=
  1 / ((x ^ 2 - 4 * x + 4) * (x ^ 2 - 4 * x + 5))

def splitIntegrand (x : ℝ) : ℝ :=
  1 / (x - 2) ^ 2 - 1 / (x ^ 2 - 4 * x + 5)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def auxiliaryFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    DifferentiableOn ℝ G domain ∧
      (∀ x ∈ domain, deriv G x = 1 / ((x - 2) ^ 2 + 1)) ∧
      (∀ x ∈ domain, F x = -1 / (x - 2) - G x)}

def primitive (x : ℝ) : ℝ := -1 / (x - 2) - Real.arctan (x - 2)

private theorem baseDerivativePair (x : ℝ) (hx : x ≠ 2) :
    HasDerivAt (fun y : ℝ => -1 / (y - 2)) (1 / (x - 2) ^ 2) x ∧
      HasDerivAt (fun y : ℝ => Real.arctan (y - 2))
        (1 / ((x - 2) ^ 2 + 1)) x := by
  constructor
  · simpa using
      (hasDerivAt_const x (-1 : ℝ)).div
        ((hasDerivAt_id x).sub_const 2) (sub_ne_zero.mpr hx)
  · simpa [Function.comp_def, add_comm] using
      (Real.hasDerivAt_arctan (x - 2)).comp x
        ((hasDerivAt_id x).sub_const 2)

private theorem quadraticDenominator (x : ℝ) :
    x ^ 2 - 4 * x + 5 = (x - 2) ^ 2 + 1 := by
  ring

private theorem intervalEqOfZeroDerivative
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hzero : ∀ x ∈ Set.Icc a b, HasDerivAt f 0 x) :
    f a = f b := by
  have hcont : ContinuousOn f (Set.Icc a b) := by
    intro x hx
    exact (hzero x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Set.Ioo a b) := by
    intro x hx
    exact (hzero x ⟨hx.1.le, hx.2.le⟩).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hcderiv⟩ :=
    exists_deriv_eq_slope (f := f) hab hcont hdiff
  have hz : deriv f c = 0 :=
    (hzero c ⟨hc.1.le, hc.2.le⟩).deriv
  rw [hz] at hcderiv
  have hbane : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  field_simp [hbane] at hcderiv
  linarith

theorem gap1 (x : ℝ) (hx : x ≠ 2) :
    integrand x =
      (x ^ 2 - 4 * x + 5 - (x ^ 2 - 4 * x + 4)) /
        ((x ^ 2 - 4 * x + 4) * (x ^ 2 - 4 * x + 5)) := by
  have hnum :
      x ^ 2 - 4 * x + 5 - (x ^ 2 - 4 * x + 4) = (1 : ℝ) := by
    ring
  unfold integrand
  rw [hnum]

theorem gap2 (x : ℝ) (hx : x ≠ 2) :
    integrand x = splitIntegrand x := by
  unfold integrand splitIntegrand
  have h₁ : x ^ 2 - 4 * x + 4 = (x - 2) ^ 2 := by
    ring
  have h₂ : x ^ 2 - 4 * x + 5 = (x - 2) ^ 2 + 1 := by
    ring
  rw [h₁, h₂]
  have hsub : x - 2 ≠ 0 := sub_ne_zero.mpr hx
  have hsq : (x - 2) ^ 2 ≠ 0 := pow_ne_zero 2 hsub
  have hadd : (x - 2) ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg (x - 2)]
  field_simp [hsq, hadd] <;> ring

theorem gap3 :
    antiderivatives integrand = antiderivatives splitIntegrand := by
  ext F
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    have hxgt : 2 < x := by
      simpa [domain] using hx
    rw [← gap2 x (ne_of_gt hxgt)]
    exact hder x hx
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    have hxgt : 2 < x := by
      simpa [domain] using hx
    rw [gap2 x (ne_of_gt hxgt)]
    exact hder x hx

theorem gap4 : antiderivatives integrand = auxiliaryFamily := by
  ext F
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨fun y => -1 / (y - 2) - F y, ?_, ?_, ?_⟩
    · intro x hx
      have hxgt : 2 < x := by
        simpa [domain] using hx
      rcases baseDerivativePair x (ne_of_gt hxgt) with ⟨hu, -⟩
      exact hu.differentiableAt.differentiableWithinAt.sub (hF x hx)
    · intro x hx
      have hxgt : 2 < x := by
        simpa [domain] using hx
      have hxmem : Set.Ioi (2 : ℝ) ∈ nhds x :=
        isOpen_Ioi.mem_nhds hxgt
      have hFat : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt hxmem
      have hFhas : HasDerivAt F (integrand x) x := by
        simpa [hder x hx] using hFat.hasDerivAt
      rcases baseDerivativePair x (ne_of_gt hxgt) with ⟨hu, -⟩
      have hval :
          1 / (x - 2) ^ 2 - integrand x =
            1 / ((x - 2) ^ 2 + 1) := by
        rw [gap2 x (ne_of_gt hxgt)]
        unfold splitIntegrand
        rw [quadraticDenominator]
        ring
      have hsub := hu.sub hFhas
      rw [hval] at hsub
      exact hsub.deriv
    · intro x hx
      ring
  · rintro ⟨G, hG, hGder, hEq⟩
    have hFhas : ∀ x ∈ domain, HasDerivAt F (integrand x) x := by
      intro x hx
      have hxgt : 2 < x := by
        simpa [domain] using hx
      have hxmem : Set.Ioi (2 : ℝ) ∈ nhds x :=
        isOpen_Ioi.mem_nhds hxgt
      have hGat : DifferentiableAt ℝ G x :=
        (hG x hx).differentiableAt hxmem
      have hGhas :
          HasDerivAt G (1 / ((x - 2) ^ 2 + 1)) x := by
        simpa [hGder x hx] using hGat.hasDerivAt
      rcases baseDerivativePair x (ne_of_gt hxgt) with ⟨hu, -⟩
      have hval :
          1 / (x - 2) ^ 2 - 1 / ((x - 2) ^ 2 + 1) = integrand x := by
        rw [gap2 x (ne_of_gt hxgt)]
        unfold splitIntegrand
        rw [quadraticDenominator]
      have hcomb := hu.sub hGhas
      rw [hval] at hcomb
      have hevent :
          F =ᶠ[nhds x] (fun y => -1 / (y - 2) - G y) := by
        filter_upwards [hxmem] with y hy
        exact hEq y (by simpa [domain] using hy)
      exact hcomb.congr_of_eventuallyEq hevent
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hFhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFhas x hx).deriv

theorem gap5 : antiderivatives integrand = primitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hF, hder⟩
    have hzero :
        ∀ x ∈ domain,
          HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      have hxgt : 2 < x := by
        simpa [domain] using hx
      have hxmem : Set.Ioi (2 : ℝ) ∈ nhds x :=
        isOpen_Ioi.mem_nhds hxgt
      have hFat : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt hxmem
      have hFhas : HasDerivAt F (integrand x) x := by
        simpa [hder x hx] using hFat.hasDerivAt
      rcases baseDerivativePair x (ne_of_gt hxgt) with ⟨hu, ha⟩
      have hval :
          1 / (x - 2) ^ 2 - 1 / ((x - 2) ^ 2 + 1) = integrand x := by
        rw [gap2 x (ne_of_gt hxgt)]
        unfold splitIntegrand
        rw [quadraticDenominator]
      have hp := hu.sub ha
      rw [hval] at hp
      have hp' : HasDerivAt primitive (integrand x) x := by
        simpa [primitive] using hp
      simpa using hFhas.sub hp'
    have hconst :
        ∀ x ∈ domain,
          F x - primitive x = F 3 - primitive 3 := by
      intro x hx
      have hxgt : 2 < x := by
        simpa [domain] using hx
      rcases lt_trichotomy x 3 with hlt | heq | hgt
      · exact intervalEqOfZeroDerivative hlt
          (fun y hy =>
            hzero y (by
              simp only [domain, mem_Ioi]
              exact lt_of_lt_of_le hxgt hy.1))
      · subst x
        rfl
      · symm
        exact intervalEqOfZeroDerivative hgt
          (fun y hy =>
            hzero y (by
              simp only [domain, mem_Ioi]
              exact lt_of_lt_of_le (by norm_num) hy.1))
    refine ⟨F 3 - primitive 3, ?_⟩
    intro x hx
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 3 - primitive 3) := by rw [hconst x hx]
  · rintro ⟨C, hEq⟩
    have hFhas : ∀ x ∈ domain, HasDerivAt F (integrand x) x := by
      intro x hx
      have hxgt : 2 < x := by
        simpa [domain] using hx
      have hxmem : Set.Ioi (2 : ℝ) ∈ nhds x :=
        isOpen_Ioi.mem_nhds hxgt
      rcases baseDerivativePair x (ne_of_gt hxgt) with ⟨hu, ha⟩
      have hval :
          1 / (x - 2) ^ 2 - 1 / ((x - 2) ^ 2 + 1) = integrand x := by
        rw [gap2 x (ne_of_gt hxgt)]
        unfold splitIntegrand
        rw [quadraticDenominator]
      have hp := hu.sub ha
      rw [hval] at hp
      have hp' : HasDerivAt primitive (integrand x) x := by
        simpa [primitive] using hp
      have hpC :
          HasDerivAt (fun y => primitive y + C) (integrand x) x :=
        hp'.add_const C
      have hevent : F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [hxmem] with y hy
        exact hEq y (by simpa [domain] using hy)
      exact hpC.congr_of_eventuallyEq hevent
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hFhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFhas x hx).deriv

end

end ProofGap.Exercise1878
