import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2121
noncomputable section

def AdmissibleBranch (U : Set ℝ) : Prop :=
  U = Set.Iio 0 ∨ U = Set.Ioi 0
def coth (x : ℝ) := Real.cosh x / Real.sinh x
def integrand (x : ℝ) := coth x ^ 2
def quotient (x : ℝ) := Real.cosh x ^ 2 / Real.sinh x ^ 2
def reduced (x : ℝ) := (1 + Real.sinh x ^ 2) / Real.sinh x ^ 2
def primitive (x : ℝ) := x - coth x

def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

theorem gap1 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Family U quotient := by
  apply Set.ext
  intro F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa [integrand, quotient, coth, div_pow] using hF x hx
  · intro hF x hx
    simpa [integrand, quotient, coth, div_pow] using hF x hx
theorem gap2 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U quotient = Family U reduced := by
  apply Set.ext
  intro F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa [quotient, reduced, Real.cosh_sq, add_comm] using hF x hx
  · intro hF x hx
    simpa [quotient, reduced, Real.cosh_sq, add_comm] using hF x hx
theorem gap3 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U reduced = Translates U primitive := by
  apply Set.ext
  intro F
  simp only [Family, Translates, Set.mem_setOf_eq]
  have hprim : ∀ x ∈ U, HasDerivAt primitive (reduced x) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rcases hU with rfl | rfl
      · exact ne_of_lt hx
      · exact ne_of_gt hx
    have hsinh : Real.sinh x ≠ 0 := by
      simpa using hx0
    have hquot :
        HasDerivAt coth
          ((Real.sinh x * Real.sinh x - Real.cosh x * Real.cosh x) /
            Real.sinh x ^ 2) x := by
      unfold coth
      exact (Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x) hsinh
    have hcosh :
        Real.cosh x * Real.cosh x = Real.sinh x * Real.sinh x + 1 := by
      simpa [pow_two] using Real.cosh_sq x
    have hval :
        1 - (Real.sinh x * Real.sinh x - Real.cosh x * Real.cosh x) /
              Real.sinh x ^ 2 = reduced x := by
      unfold reduced
      rw [hcosh]
      field_simp [hsinh]
      ring
    have hder := (hasDerivAt_id x).sub hquot
    rw [hval] at hder
    simpa [primitive] using hder
  constructor
  · intro hF
    rcases hU with rfl | rfl
    · have hdiff : DifferentiableOn ℝ (F - primitive) (Set.Iio 0) :=
        fun x hx => ((hF x hx).sub (hprim x hx)).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ Set.Iio (0 : ℝ), deriv (F - primitive) x = 0 :=
        fun x hx => by
          simpa using ((hF x hx).sub (hprim x hx)).deriv
      refine ⟨F (-1) - primitive (-1), ?_⟩
      intro x hx
      have heq :=
        isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio
          hdiff hderiv hx (show (-1 : ℝ) ∈ Set.Iio 0 by norm_num)
      change F x - primitive x = F (-1) - primitive (-1) at heq
      linarith
    · have hdiff : DifferentiableOn ℝ (F - primitive) (Set.Ioi 0) :=
        fun x hx => ((hF x hx).sub (hprim x hx)).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), deriv (F - primitive) x = 0 :=
        fun x hx => by
          simpa using ((hF x hx).sub (hprim x hx)).deriv
      refine ⟨F 1 - primitive 1, ?_⟩
      intro x hx
      have heq :=
        isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
          hdiff hderiv hx (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
      change F x - primitive x = F 1 - primitive 1 at heq
      linarith
  · rintro ⟨C, hF⟩ x hx
    have hUopen : IsOpen U := by
      rcases hU with rfl | rfl
      · exact isOpen_Iio
      · exact isOpen_Ioi
    have heq : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [hUopen.mem_nhds hx] with y hy
      exact hF y hy
    exact ((hprim x hx).add_const C).congr_of_eventuallyEq heq
theorem gap4 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitive := by
  rw [gap1 U hU, gap2 U hU, gap3 U hU]

end
end ProofGap.Exercise2121
