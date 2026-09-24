import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise1648

noncomputable section

def domain : Set ℝ := Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)
def original (x : ℝ) : ℝ := Real.sqrt (1 - Real.sin (2 * x))
def squared (x : ℝ) : ℝ := Real.sqrt ((Real.cos x - Real.sin x) ^ 2)
def signed (x : ℝ) : ℝ :=
  Real.sign (Real.cos x - Real.sin x) * (Real.cos x - Real.sin x)
def primitive (x : ℝ) : ℝ :=
  (Real.sin x + Real.cos x) * Real.sign (Real.cos x - Real.sin x)
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem cos_sub_sin_pos_on_domain {x : ℝ} (hx : x ∈ domain) :
    0 < Real.cos x - Real.sin x := by
  rw [domain, Set.mem_Ioo] at hx
  have hpi : 0 < Real.pi := Real.pi_pos
  have hxmem : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  by_cases hxneg : x < 0
  · have hzero : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    have hsin : Real.sin x < Real.sin 0 :=
      Real.strictMonoOn_sin hxmem hzero hxneg
    have hcos : 0 < Real.cos x := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith
    have hsx : Real.sin x < 0 := by
      simpa using hsin
    linarith
  · have hymem : Real.pi / 2 - x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    have hxy : x < Real.pi / 2 - x := by
      linarith
    have hsin := Real.strictMonoOn_sin hxmem hymem hxy
    rw [Real.sin_pi_div_two_sub] at hsin
    linarith

private theorem signed_eq_base_on_domain {x : ℝ} (hx : x ∈ domain) :
    signed x = Real.cos x - Real.sin x := by
  have hpos := cos_sub_sin_pos_on_domain hx
  have hneg : ¬ Real.cos x - Real.sin x < 0 := by
    linarith
  have hlt : Real.sin x < Real.cos x := by
    linarith
  have hsign : Real.sign (Real.cos x - Real.sin x) = 1 := by
    simp [Real.sign, hneg, hlt]
  rw [signed, hsign]
  simp

private theorem primitive_eq_base_on_domain {x : ℝ} (hx : x ∈ domain) :
    primitive x = Real.sin x + Real.cos x := by
  have hpos := cos_sub_sin_pos_on_domain hx
  have hneg : ¬ Real.cos x - Real.sin x < 0 := by
    linarith
  have hlt : Real.sin x < Real.cos x := by
    linarith
  have hsign : Real.sign (Real.cos x - Real.sin x) = 1 := by
    simp [Real.sign, hneg, hlt]
  rw [primitive, hsign]
  simp

private theorem base_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => Real.sin y + Real.cos y)
      (Real.cos x - Real.sin x) x := by
  simpa [sub_eq_add_neg] using
    (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)

theorem gap1 (x : ℝ) : original x = squared x := by
  unfold original squared
  apply congrArg Real.sqrt
  rw [Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem gap2 (x : ℝ) : squared x = signed x := by
  unfold squared signed
  let a : ℝ := Real.cos x - Real.sin x
  change Real.sqrt (a ^ 2) = Real.sign a * a
  rw [Real.sqrt_sq_eq_abs]
  by_cases ha : a < 0
  · simp [Real.sign, ha, abs_of_neg ha]
  · have hnonneg : 0 ≤ a := le_of_not_gt ha
    by_cases hz : a = 0
    · simp [hz]
    · have hpos : 0 < a := lt_of_le_of_ne hnonneg (Ne.symm hz)
      simp [Real.sign, ha, hpos, abs_of_nonneg hnonneg]

theorem gap3 (x : ℝ) : original x = signed x := by
  exact (gap1 x).trans (gap2 x)

theorem gap4 : AntiderivativesOn original = AntiderivativesOn squared := by
  apply congrArg AntiderivativesOn
  funext x
  exact gap1 x

theorem gap5 : AntiderivativesOn squared = AntiderivativesOn signed := by
  apply congrArg AntiderivativesOn
  funext x
  exact gap2 x

theorem gap6 : AntiderivativesOn signed = PrimitiveFamily primitive := by
  ext F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = signed x) ↔
      ∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hopen : IsOpen domain := by
      exact isOpen_Ioo
    have hsubDeriv :
        ∀ x ∈ domain,
          HasDerivAt (fun y => F y - (Real.sin y + Real.cos y)) 0 x := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (hopen.mem_nhds hx)
      have hFd : HasDerivAt F (signed x) x := by
        rw [← hFderiv x hx]
        exact hFat.hasDerivAt
      simpa [signed_eq_base_on_domain hx] using
        hFd.sub (base_hasDerivAt x)
    have hsubDiff :
        DifferentiableOn ℝ (fun y => F y - (Real.sin y + Real.cos y)) domain := by
      intro x hx
      exact (hsubDeriv x hx).differentiableAt.differentiableWithinAt
    have hsubDerivEq :
        ∀ x ∈ domain,
          deriv (fun y => F y - (Real.sin y + Real.cos y)) x = 0 := by
      intro x hx
      exact (hsubDeriv x hx).deriv
    have hzero : (0 : ℝ) ∈ domain := by
      rw [domain, Set.mem_Ioo]
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨F 0 - (Real.sin 0 + Real.cos 0), ?_⟩
    intro x hx
    have heq :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hsubDiff hsubDerivEq (x := x) (y := 0) hx hzero
    rw [primitive_eq_base_on_domain hx]
    simp only [Real.sin_zero, Real.cos_zero, zero_add] at heq ⊢
    linarith
  · rintro ⟨C, hFC⟩
    have hopen : IsOpen domain := by
      exact isOpen_Ioo
    have hlocal : ∀ x ∈ domain, HasDerivAt F (signed x) x := by
      intro x hx
      have heq :
          F =ᶠ[nhds x] fun y => (Real.sin y + Real.cos y) + C := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        rw [hFC y hy, primitive_eq_base_on_domain hy]
      have hbaseC :
          HasDerivAt (fun y => (Real.sin y + Real.cos y) + C)
            (Real.cos x - Real.sin x) x := by
        convert (base_hasDerivAt x).add (hasDerivAt_const x C) using 1 <;> simp
      rw [signed_eq_base_on_domain hx]
      exact hbaseC.congr_of_eventuallyEq heq
    constructor
    · intro x hx
      exact (hlocal x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hlocal x hx).deriv

theorem gap7 : AntiderivativesOn original = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn original = AntiderivativesOn squared := gap4
    _ = AntiderivativesOn signed := gap5
    _ = PrimitiveFamily primitive := gap6

end
end ProofGap.Exercise1648
