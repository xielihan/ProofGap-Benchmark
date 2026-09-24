import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3257

noncomputable section

def u (x y : ℝ) : ℝ :=
  x * Real.log (x * y)

def partialXOrder (n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => g t y) x

def mixedX2Y (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialXOrder 2 g x t) y

theorem gap1 :
    ∀ x y, 0 < x * y →
      partialXOrder 1 u x y = Real.log (x * y) + 1 := by
  intro x y hxy
  have hxy0 : x * y ≠ 0 := ne_of_gt hxy
  obtain ⟨hx0, hy0⟩ := mul_ne_zero_iff.mp hxy0
  have hinner : HasDerivAt (fun t : ℝ => t * y) y x := by
    simpa using (hasDerivAt_id x).mul_const y
  have hlog0 : HasDerivAt Real.log (x * y)⁻¹ (x * y) :=
    Real.hasDerivAt_log hxy0
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log (t * y)) ((x * y)⁻¹ * y) x := by
    simpa [Function.comp_def] using hlog0.comp x hinner
  have hu :
      HasDerivAt (fun t : ℝ => u t y)
        (Real.log (x * y) + x * ((x * y)⁻¹ * y)) x := by
    simpa [u] using (hasDerivAt_id x).mul hlog
  change deriv (fun t : ℝ => u t y) x = Real.log (x * y) + 1
  rw [hu.deriv]
  field_simp [hx0, hy0]

theorem gap2 :
    ∀ x y, 0 < x * y →
      partialXOrder 2 u x y = 1 / x := by
  intro x y hxy
  have hxy0 : x * y ≠ 0 := ne_of_gt hxy
  obtain ⟨hx0, hy0⟩ := mul_ne_zero_iff.mp hxy0
  have hcont : Continuous (fun z : ℝ => z * y) :=
    continuous_id.mul continuous_const
  have hopen : IsOpen {z : ℝ | 0 < z * y} :=
    isOpen_lt continuous_const hcont
  have hev : ∀ᶠ z : ℝ in nhds x, 0 < z * y :=
    hopen.mem_nhds hxy
  have heq :
      (fun z : ℝ => deriv (fun t : ℝ => u t y) z) =ᶠ[nhds x]
        (fun z : ℝ => Real.log (z * y) + 1) :=
    hev.mono (fun z hz => by
      have hz' := gap1 z y hz
      change deriv (fun t : ℝ => u t y) z = Real.log (z * y) + 1 at hz'
      exact hz')
  have hinner : HasDerivAt (fun t : ℝ => t * y) y x := by
    simpa using (hasDerivAt_id x).mul_const y
  have hlog0 : HasDerivAt Real.log (x * y)⁻¹ (x * y) :=
    Real.hasDerivAt_log hxy0
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log (t * y)) ((x * y)⁻¹ * y) x := by
    simpa [Function.comp_def] using hlog0.comp x hinner
  have hright :
      HasDerivAt (fun z : ℝ => Real.log (z * y) + 1) ((x * y)⁻¹ * y) x := by
    simpa using hlog.add_const (1 : ℝ)
  have hleft :
      HasDerivAt (fun z : ℝ => deriv (fun t : ℝ => u t y) z)
        ((x * y)⁻¹ * y) x :=
    hright.congr_of_eventuallyEq heq
  change deriv (deriv (fun t : ℝ => u t y)) x = 1 / x
  rw [hleft.deriv]
  field_simp [hx0, hy0]

theorem gap3 :
    ∀ x y, 0 < x * y →
      mixedX2Y u x y = 0 := by
  intro x y hxy
  have hcont : Continuous (fun t : ℝ => x * t) :=
    continuous_const.mul continuous_id
  have hopen : IsOpen {t : ℝ | 0 < x * t} :=
    isOpen_lt continuous_const hcont
  have hev : ∀ᶠ t : ℝ in nhds y, 0 < x * t :=
    hopen.mem_nhds hxy
  have heq :
      (fun t : ℝ => partialXOrder 2 u x t) =ᶠ[nhds y]
        (fun _ : ℝ => 1 / x) :=
    hev.mono (fun t ht => gap2 x t ht)
  have hconst : HasDerivAt (fun _ : ℝ => 1 / x) 0 y :=
    hasDerivAt_const y (1 / x)
  have hpartial :
      HasDerivAt (fun t : ℝ => partialXOrder 2 u x t) 0 y :=
    hconst.congr_of_eventuallyEq heq
  change deriv (fun t : ℝ => partialXOrder 2 u x t) y = 0
  exact hpartial.deriv

end

end ProofGap.Exercise3257
