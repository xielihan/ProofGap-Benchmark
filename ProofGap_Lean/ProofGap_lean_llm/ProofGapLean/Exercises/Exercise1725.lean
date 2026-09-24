import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1725

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := (1 + x) ^ 2 / (1 + x ^ 2)
def expandedIntegrand (x : ℝ) := 1 + 2 * x / (1 + x ^ 2)
def primitive (x : ℝ) := x + Real.log (1 + x ^ 2)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (expandedIntegrand x) x := by
  have hpos : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hmul : HasDerivAt (fun y : ℝ => y * y) (x + x) x := by
    simpa [id] using (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using hmul
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using hsq.const_add 1
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2))
      (2 * x / (1 + x ^ 2)) x := by
    convert (Real.hasDerivAt_log hpos.ne').comp x hinner using 1
    field_simp
  simpa [primitive, expandedIntegrand] using (hasDerivAt_id x).add hlog

private theorem value_eq_of_hasDerivAt_zero {f : ℝ → ℝ}
    (hf : ∀ x : ℝ, HasDerivAt f 0 x) (x y : ℝ) : f x = f y := by
  exact is_const_of_deriv_eq_zero
    (fun z => (hf z).differentiableAt)
    (fun z => (hf z).deriv) x y

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn expandedIntegrand := by
  apply Set.ext
  intro F
  change (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
    (∀ x ∈ branch, HasDerivAt F (expandedIntegrand x) x)
  constructor
  · intro hF x hx
    have heq : integrand x = expandedIntegrand x := by
      unfold integrand expandedIntegrand
      have hne : 1 + x ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg x]
      field_simp [hne]
      ring
    simpa [heq] using hF x hx
  · intro hF x hx
    have heq : integrand x = expandedIntegrand x := by
      unfold integrand expandedIntegrand
      have hne : 1 + x ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg x]
      field_simp [hne]
      ring
    simpa [heq] using hF x hx
theorem gap2 :
    AntiderivativesOn expandedIntegrand = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  change (∀ x ∈ branch, HasDerivAt F (expandedIntegrand x) x) ↔
    (∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C)
  constructor
  · intro hF
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hzero : ∀ y : ℝ,
        HasDerivAt (fun z => F z - primitive z) 0 y := by
      intro y
      have hFy := hF y (by simp [branch])
      convert hFy.sub (primitive_hasDerivAt y) using 1
      ring
    have hc := value_eq_of_hasDerivAt_zero hzero x 0
    change F x - primitive x = F 0 - primitive 0 at hc
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hEq : F = fun y => primitive y + C := by
      funext y
      exact hC y (by simp [branch])
    rw [hEq]
    simpa [add_comm] using (primitive_hasDerivAt x).const_add C
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1725
