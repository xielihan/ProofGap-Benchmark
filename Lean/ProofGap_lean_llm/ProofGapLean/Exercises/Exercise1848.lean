import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set Real

namespace ProofGap.Exercise1848

noncomputable section

def domain : Set ℝ := Set.Ioi 0

def integrand (x : ℝ) : ℝ := 1 / Real.sqrt (x + x ^ 2)

def shiftedIntegrand (x : ℝ) : ℝ :=
  1 / Real.sqrt ((x + 1 / 2 : ℝ) ^ 2 - 1 / 4)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def primitive (x : ℝ) : ℝ :=
  Real.log |x + 1 / 2 + Real.sqrt (x + x ^ 2)|

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (shiftedIntegrand x) x := by
  change 0 < x at hx
  have hq : 0 < x + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hs : 0 < Real.sqrt (x + x ^ 2) := Real.sqrt_pos.2 hq
  have ha : 0 < x + 1 / 2 + Real.sqrt (x + x ^ 2) := by
    nlinarith [Real.sqrt_nonneg (x + x ^ 2)]
  have hrad : ((x + 1 / 2 : ℝ) ^ 2 - 1 / 4) = x + x ^ 2 := by
    ring
  have hinner :
      HasDerivAt (fun y : ℝ => y + y ^ 2) (1 + 2 * x) x := by
    convert (hasDerivAt_id x).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt (y + y ^ 2))
        ((1 + 2 * x) / (2 * Real.sqrt (x + x ^ 2))) x := by
    convert (Real.hasDerivAt_sqrt hq.ne').comp x hinner using 1 <;> ring
  have harg :
      HasDerivAt
        (fun y : ℝ => y + 1 / 2 + Real.sqrt (y + y ^ 2))
        (1 + (1 + 2 * x) / (2 * Real.sqrt (x + x ^ 2))) x := by
    convert ((hasDerivAt_id x).add_const (1 / 2)).add hsqrt using 1 <;> ring
  have hlog :
      HasDerivAt
        (fun y : ℝ =>
          Real.log (y + 1 / 2 + Real.sqrt (y + y ^ 2)))
        (shiftedIntegrand x) x := by
    convert harg.log ha.ne' using 1
    unfold shiftedIntegrand
    rw [hrad]
    field_simp [hs.ne', ha.ne'] <;> ring
  have hevent :
      primitive =ᶠ[nhds x]
        (fun y : ℝ =>
          Real.log (y + 1 / 2 + Real.sqrt (y + y ^ 2))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    have hybase : 0 < y + 1 / 2 := by
      exact add_pos hy (by norm_num)
    have hyarg : 0 < y + 1 / 2 + Real.sqrt (y + y ^ 2) :=
      add_pos_of_pos_of_nonneg hybase (Real.sqrt_nonneg (y + y ^ 2))
    simpa only [primitive, abs_of_pos hyarg]
  exact hlog.congr_of_eventuallyEq hevent

private theorem constant_on_Ioi_of_deriv_eq_zero
    (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi (0 : ℝ)))
    (hzero : ∀ x ∈ Set.Ioi (0 : ℝ), deriv f x = 0) :
    ∀ x ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioi (0 : ℝ), f x = f y := by
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have hsub : Set.Icc x y ⊆ Set.Ioi (0 : ℝ) := by
      intro z hz
      exact lt_of_lt_of_le hx hz.1
    have hsubo : Set.Ioo x y ⊆ Set.Ioi (0 : ℝ) := by
      intro z hz
      exact lt_trans hx hz.1
    obtain ⟨c, hc, hcder⟩ :=
      exists_deriv_eq_slope (f := f) hxy
        (hf.continuousOn.mono hsub) (hf.mono hsubo)
    rw [hzero c (hsubo hc)] at hcder
    field_simp [sub_ne_zero.mpr hxy.ne'] at hcder
    linarith
  · exact congrArg f hxy
  · have hsub : Set.Icc y x ⊆ Set.Ioi (0 : ℝ) := by
      intro z hz
      exact lt_of_lt_of_le hy hz.1
    have hsubo : Set.Ioo y x ⊆ Set.Ioi (0 : ℝ) := by
      intro z hz
      exact lt_trans hy hz.1
    obtain ⟨c, hc, hcder⟩ :=
      exists_deriv_eq_slope (f := f) hyx
        (hf.continuousOn.mono hsub) (hf.mono hsubo)
    rw [hzero c (hsubo hc)] at hcder
    field_simp [sub_ne_zero.mpr hyx.ne'] at hcder
    linarith

theorem gap1 : antiderivatives integrand = antiderivatives shiftedIntegrand := by
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧
        ∀ x ∈ domain, deriv F x = integrand x) ↔
      (DifferentiableOn ℝ F domain ∧
        ∀ x ∈ domain, deriv F x = shiftedIntegrand x)
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    have hrad : ((x + 1 / 2 : ℝ) ^ 2 - 1 / 4) = x + x ^ 2 := by
      ring
    have hpoint : integrand x = shiftedIntegrand x := by
      unfold integrand shiftedIntegrand
      rw [hrad]
    rw [hderiv x hx]
    exact hpoint
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    have hrad : ((x + 1 / 2 : ℝ) ^ 2 - 1 / 4) = x + x ^ 2 := by
      ring
    have hpoint : integrand x = shiftedIntegrand x := by
      unfold integrand shiftedIntegrand
      rw [hrad]
    rw [hderiv x hx]
    exact hpoint.symm

theorem gap2 :
    antiderivatives shiftedIntegrand = primitiveFamily primitive := by
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧
        ∀ x ∈ domain, deriv F x = shiftedIntegrand x) ↔
      ∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C
  constructor
  · rintro ⟨hF, hderiv⟩
    have hp : DifferentiableOn ℝ primitive domain := by
      intro x hx
      exact
        (primitive_hasDerivAt x hx).differentiableAt.differentiableWithinAt
    have hdiff : DifferentiableOn ℝ (fun x => F x - primitive x) domain :=
      hF.sub hp
    have hzero :
        ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFAt : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
      calc
        deriv (fun y => F y - primitive y) x =
            deriv F x - shiftedIntegrand x :=
          (hFAt.hasDerivAt.sub (primitive_hasDerivAt x hx)).deriv
        _ = 0 := by rw [hderiv x hx]; ring
    have hconst :=
      constant_on_Ioi_of_deriv_eq_zero
        (fun x => F x - primitive x)
        (by simpa [domain] using hdiff)
        (by
          intro x hx
          apply hzero x
          simpa [domain] using hx)
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have heq := hconst x (by simpa [domain] using hx) 1 (by
      show (0 : ℝ) < 1
      exact zero_lt_one)
    dsimp only at heq
    linarith
  · rintro ⟨C, hFC⟩
    have hhas : ∀ x ∈ domain, HasDerivAt F (shiftedIntegrand x) x := by
      intro x hx
      have hevent :
          F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact hFC y hy
      exact
        ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq hevent
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hhas x hx).deriv

theorem gap3 : antiderivatives integrand = primitiveFamily primitive := by
  exact gap1.trans gap2

end

end ProofGap.Exercise1848
