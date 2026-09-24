import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace ProofGap.Exercise1015_1

noncomputable section

open scoped Topology

def f (x : ℝ) : ℝ := x
def g (x : ℝ) : ℝ := |x|
def F (x : ℝ) : ℝ := f x * g x

def differenceQuotient (h : ℝ) : ℝ := (F h - F 0) / h
def puncturedZero : Filter ℝ := 𝓝[({0} : Set ℝ)ᶜ] 0

theorem gap1 : DifferentiableAt ℝ f 0 := by
  unfold f
  exact (hasDerivAt_id (0 : ℝ)).differentiableAt

theorem gap2 : HasDerivAt f 1 0 := by
  simpa [f] using hasDerivAt_id (0 : ℝ)

theorem gap3 : ¬ DifferentiableAt ℝ g 0 := by
  simpa [g] using not_differentiableAt_abs_zero

theorem gap4 (x : ℝ) : F x = f x * g x := by
  rfl

theorem gap5 (x : ℝ) : f x * g x = x * |x| := by
  rfl

theorem gap6 (x : ℝ) : F x = x * |x| := by
  rw [gap4, gap5]

theorem gap7 (h : ℝ) (hh : h ≠ 0) :
    differenceQuotient h = (h * |h| - 0 * |(0 : ℝ)|) / h := by
  unfold differenceQuotient
  rw [gap6 h, gap6 0]

theorem gap8 (h : ℝ) (hh : h ≠ 0) :
    (h * |h| - 0 * |(0 : ℝ)|) / h = |h| := by
  simp only [zero_mul, sub_zero]
  field_simp [hh]

theorem gap9 : Tendsto (fun h : ℝ => |h|) puncturedZero (𝓝 0) := by
  unfold puncturedZero
  simpa only [abs_zero] using
    (continuous_abs.tendsto (0 : ℝ)).mono_left inf_le_left

theorem gap10 : Tendsto differenceQuotient puncturedZero (𝓝 0) := by
  apply gap9.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa [puncturedZero] using hh
  rw [gap7 h hh0, gap8 h hh0]

theorem gap11 : HasDerivAt F 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply gap10.congr'
  exact Filter.Eventually.of_forall (fun h => by
    simp [differenceQuotient, puncturedZero, div_eq_mul_inv, smul_eq_mul]
    ring)

theorem gap12 :
    DifferentiableAt ℝ f 0 ∧
      ¬ DifferentiableAt ℝ g 0 ∧
      (∀ x, F x = f x * g x) ∧
      DifferentiableAt ℝ F 0 := by
  exact ⟨gap1, gap3, gap4, gap11.differentiableAt⟩

end

end ProofGap.Exercise1015_1
