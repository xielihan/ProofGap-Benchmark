import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ProofGap.Exercise1651

noncomputable section

def integrand (a b x : ℝ) : ℝ := a * Real.sinh x + b * Real.cosh x
def primitive (a b x : ℝ) : ℝ := a * Real.cosh x + b * Real.sinh x
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

theorem gap1 (a b : ℝ) :
    Antiderivatives (integrand a b) = PrimitiveFamily (primitive a b) := by
  have hp (x : ℝ) :
      HasDerivAt (primitive a b) (integrand a b x) x := by
    simpa only [primitive, integrand] using
      ((Real.hasDerivAt_cosh x).const_mul a).add
        ((Real.hasDerivAt_sinh x).const_mul b)
  apply Set.ext
  intro F
  simp only [Antiderivatives, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderivF⟩
    have hh (x : ℝ) :
        HasDerivAt (fun y => F y - primitive a b y) 0 x := by
      have hFd : HasDerivAt F (integrand a b x) x := by
        simpa only [hderivF x] using (hF x).hasDerivAt
      simpa using hFd.sub (hp x)
    have hh_diff : Differentiable ℝ (fun x => F x - primitive a b x) :=
      fun x => (hh x).differentiableAt
    have hmono : Monotone (fun x => F x - primitive a b x) :=
      monotone_of_deriv_nonneg hh_diff (fun x => by rw [(hh x).deriv])
    have hanti : Antitone (fun x => F x - primitive a b x) :=
      antitone_of_deriv_nonpos hh_diff (fun x => by rw [(hh x).deriv])
    have hconst (x y : ℝ) :
        F x - primitive a b x = F y - primitive a b y := by
      rcases le_total x y with hxy | hyx
      · exact le_antisymm (hmono hxy) (hanti hxy)
      · exact le_antisymm (hanti hyx) (hmono hyx)
    refine ⟨F 0 - primitive a b 0, ?_⟩
    intro x
    calc
      F x = (F x - primitive a b x) + primitive a b x := by
        rw [sub_add_cancel]
      _ = (F 0 - primitive a b 0) + primitive a b x := by
        rw [hconst x 0]
      _ = primitive a b x + (F 0 - primitive a b 0) := add_comm _ _
  · rintro ⟨C, hC⟩
    have hFC : F = fun x => primitive a b x + C := funext hC
    constructor
    · rw [hFC]
      intro x
      exact ((hp x).add_const C).differentiableAt
    · intro x
      rw [hFC]
      simpa using ((hp x).add_const C).deriv

end
end ProofGap.Exercise1651
