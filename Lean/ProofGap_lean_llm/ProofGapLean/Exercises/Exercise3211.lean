import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3211

noncomputable section

open Filter
open scoped Topology

def fixedSection (f : ℝ → ℝ → ℝ) (b : ℝ) : ℝ → ℝ :=
  fun x => f x b

def partialX (f : ℝ → ℝ → ℝ) (x b : ℝ) : ℝ :=
  deriv (fixedSection f b) x

def differenceQuotient (φ : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (φ (x + h) - φ x) / h

def puncturedZero : Filter ℝ :=
  nhdsWithin (0 : ℝ) (({(0 : ℝ)} : Set ℝ)ᶜ)

theorem gap1 (f : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (b : ℝ)
    (hφ : ∀ x, φ x = f x b) :
    ∀ x, deriv (fixedSection f b) x = deriv φ x := by
  intro x
  have hfun : fixedSection f b = φ := funext fun y => (hφ y).symm
  rw [hfun]

theorem gap2 (φ : ℝ → ℝ)
    (hφ : ∀ x, DifferentiableAt ℝ φ x) :
    ∀ x, Tendsto (differenceQuotient φ x) puncturedZero
      (𝓝 (deriv φ x)) := by
  intro x
  have hslope :
      Tendsto (slope φ x)
        (nhdsWithin x (({x} : Set ℝ)ᶜ)) (𝓝 (deriv φ x)) :=
    hasDerivAt_iff_tendsto_slope.mp (hφ x).hasDerivAt
  have hcont :
      Tendsto (fun h : ℝ => x + h) (𝓝 0) (𝓝 x) := by
    simpa using
      (tendsto_const_nhds.add
        (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)))
  have hnhds :
      Tendsto (fun h : ℝ => x + h) puncturedZero (𝓝 x) := by
    apply hcont.mono_left
    rw [puncturedZero, nhdsWithin]
    exact inf_le_left
  have hne :
      ∀ᶠ h in puncturedZero, x + h ∈ (({x} : Set ℝ)ᶜ) := by
    simpa [puncturedZero] using
      (self_mem_nhdsWithin :
        ∀ᶠ h in nhdsWithin (0 : ℝ) (({(0 : ℝ)} : Set ℝ)ᶜ),
          h ∈ (({(0 : ℝ)} : Set ℝ)ᶜ))
  have hshift :
      Tendsto (fun h : ℝ => x + h) puncturedZero
        (nhdsWithin x (({x} : Set ℝ)ᶜ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hnhds, hne⟩
  apply (hslope.comp hshift).congr'
  exact Filter.Eventually.of_forall (fun h => by
    simp [differenceQuotient, slope, div_eq_mul_inv, mul_comm])

theorem gap3 (f : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (b : ℝ)
    (hφ : ∀ x, φ x = f x b) :
    ∀ x L : ℝ,
      Tendsto (differenceQuotient φ x) puncturedZero (𝓝 L) ↔
        Tendsto (differenceQuotient (fixedSection f b) x)
          puncturedZero (𝓝 L) := by
  intro x L
  have hfun : φ = fixedSection f b := funext fun y => hφ y
  rw [hfun]

theorem gap4 (f : ℝ → ℝ → ℝ) (b : ℝ)
    (hf : ∀ x, DifferentiableAt ℝ (fixedSection f b) x) :
    ∀ x, Tendsto (differenceQuotient (fixedSection f b) x)
      puncturedZero (𝓝 (partialX f x b)) := by
  intro x
  simpa [partialX] using
    (gap2 (fixedSection f b) hf x)

theorem gap5 (f : ℝ → ℝ → ℝ) :
    ∀ b x, deriv (fixedSection f b) x = partialX f x b := by
  intro b x
  rfl

theorem gap6 (f : ℝ → ℝ → ℝ) :
    ∀ x b, partialX f x b = deriv (fixedSection f b) x := by
  intro x b
  rfl

end

end ProofGap.Exercise3211
