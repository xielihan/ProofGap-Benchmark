import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1997

noncomputable section

def branch : Set ℝ := {x | Real.cos x ≠ 0}
def originalIntegrand (x : ℝ) := Real.sin x ^ 3 / Real.cos x ^ 4
def substitutedIntegrand (x : ℝ) :=
  (1 - Real.cos x ^ 2) / Real.cos x ^ 4 * deriv Real.cos x
def primitive (x : ℝ) :=
  1 / (3 * Real.cos x ^ 3) - 1 / Real.cos x
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def NegatedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives substitutedIntegrand,
    ∀ x ∈ branch, F x = -G x}
def ComponentwisePrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ → ℝ,
    (∀ x ∈ branch, F x = primitive x + K x) ∧
    (∀ x ∈ branch, HasDerivAt K 0 x)}

private theorem isOpen_branch : IsOpen branch := by
  have hclosed : IsClosed (Real.cos ⁻¹' ({0} : Set ℝ)) :=
    isClosed_singleton.preimage Real.continuous_cos
  have heq : branch = (Real.cos ⁻¹' ({0} : Set ℝ))ᶜ := by
    ext x
    simp [branch]
  rw [heq]
  exact hclosed.isOpen_compl

private theorem original_eq_neg_substituted (x : ℝ) :
    originalIntegrand x = -substitutedIntegrand x := by
  unfold originalIntegrand substitutedIntegrand
  rw [(Real.hasDerivAt_cos x).deriv]
  rw [show 1 - Real.cos x ^ 2 = Real.sin x ^ 2 by
    nlinarith [Real.sin_sq_add_cos_sq x]]
  ring

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (originalIntegrand x) x := by
  have hcos0 : Real.cos x ≠ 0 := hx
  have hcos := Real.hasDerivAt_cos x
  have hden3 : HasDerivAt (fun y : ℝ => 3 * Real.cos y ^ 3)
      (3 * (3 * Real.cos x ^ 2 * (-Real.sin x))) x := by
    convert (hcos.pow 3).const_mul 3 using 1 <;> ring
  have hfirst := (hasDerivAt_const x (1 : ℝ)).div hden3
    (mul_ne_zero (by norm_num) (pow_ne_zero 3 hcos0))
  have hsecond := (hasDerivAt_const x (1 : ℝ)).div hcos hcos0
  have hraw := hfirst.sub hsecond
  have hcoef :
      (0 * (3 * Real.cos x ^ 3) -
          1 * (3 * (3 * Real.cos x ^ 2 * (-Real.sin x)))) /
          (3 * Real.cos x ^ 3) ^ 2 -
        (0 * Real.cos x - 1 * (-Real.sin x)) / Real.cos x ^ 2 =
      originalIntegrand x := by
    unfold originalIntegrand
    have htrig : 1 - Real.cos x ^ 2 = Real.sin x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    have hsin :
        Real.sin x - Real.cos x ^ 2 * Real.sin x = Real.sin x ^ 3 := by
      calc
        _ = Real.sin x * (1 - Real.cos x ^ 2) := by ring
        _ = Real.sin x * Real.sin x ^ 2 := by rw [htrig]
        _ = Real.sin x ^ 3 := by ring
    field_simp [hcos0]
    nlinarith
  have hfinal := hraw.congr_deriv hcoef
  apply hfinal.congr_of_eventuallyEq
  filter_upwards [] with y
  unfold primitive
  rfl

theorem gap1 :
    Antiderivatives originalIntegrand = NegatedFamily := by
  apply Set.ext
  intro F
  simp only [Antiderivatives, NegatedFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨(fun x => -F x), ?_, ?_⟩
    · intro x hx
      exact (hF x hx).neg.congr_deriv
        (by rw [original_eq_neg_substituted x]; ring)
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩ x hx
    have hd := (hG x hx).neg
    have hd' := hd.congr_deriv (original_eq_neg_substituted x).symm
    apply hd'.congr_of_eventuallyEq
    filter_upwards [isOpen_branch.mem_nhds hx] with y hy
    exact hFG y hy
theorem gap2 :
    NegatedFamily = ComponentwisePrimitiveFamily := by
  rw [← gap1]
  apply Set.ext
  intro F
  simp only [Antiderivatives, ComponentwisePrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨(fun x => F x - primitive x), ?_, ?_⟩
    · intro x hx
      ring
    · intro x hx
      have hd := (hF x hx).sub (hasDerivAt_primitive x hx)
      convert hd using 1 <;> ring
  · rintro ⟨K, hFK, hK⟩ x hx
    have hd := (hasDerivAt_primitive x hx).add (hK x hx)
    have hd' : HasDerivAt (fun y => primitive y + K y)
        (originalIntegrand x) x := by
      convert hd using 1 <;> ring
    apply hd'.congr_of_eventuallyEq
    filter_upwards [isOpen_branch.mem_nhds hx] with y hy
    exact hFK y hy
theorem gap3 :
    Antiderivatives originalIntegrand =
      ComponentwisePrimitiveFamily := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1997
