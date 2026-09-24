import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1909

noncomputable section

def u (x : ℝ) : ℝ := x ^ 4
def integrand (x : ℝ) : ℝ :=
  x ^ 11 / (x ^ 8 + 3 * x ^ 4 + 2)
def substitutedIntegrand (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
    (x ^ 8 / ((x ^ 4 + 1) * (x ^ 4 + 2))) * deriv u x
def quotientRewrite (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
    (1 - (3 * x ^ 4 + 2) / ((x ^ 4 + 1) * (x ^ 4 + 2))) *
    deriv u x
def partialFractionIntegrand (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
    (1 + 1 / (x ^ 4 + 1) - 4 / (x ^ 4 + 2)) * deriv u x
def primitive (x : ℝ) : ℝ :=
  x ^ 4 / 4 +
    (1 / 4 : ℝ) * Real.log ((x ^ 4 + 1) / (x ^ 4 + 2) ^ 4)
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem deriv_u_formula (x : ℝ) : deriv u x = 4 * x ^ 3 := by
  have hu : HasDerivAt u (4 * x ^ 3) x := by
    simpa [u] using ((hasDerivAt_id x).pow 4)
  exact hu.deriv

private theorem integrand_eq_substituted (x : ℝ) :
    integrand x = substitutedIntegrand x := by
  unfold integrand substitutedIntegrand
  rw [deriv_u_formula]
  rw [show x ^ 8 + 3 * x ^ 4 + 2 = (x ^ 4 + 1) * (x ^ 4 + 2) by ring]
  ring

private theorem substituted_eq_quotient (x : ℝ) :
    substitutedIntegrand x = quotientRewrite x := by
  have h1 : x ^ 4 + 1 ≠ 0 := by positivity
  have h2 : x ^ 4 + 2 ≠ 0 := by positivity
  unfold substitutedIntegrand quotientRewrite
  rw [deriv_u_formula]
  field_simp [h1, h2]
  ring

private theorem quotient_eq_partialFraction (x : ℝ) :
    quotientRewrite x = partialFractionIntegrand x := by
  have h1 : x ^ 4 + 1 ≠ 0 := by positivity
  have h2 : x ^ 4 + 2 ≠ 0 := by positivity
  unfold quotientRewrite partialFractionIntegrand
  field_simp [h1, h2]
  ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (partialFractionIntegrand x) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    simpa using (hasDerivAt_id x).pow 4
  have h1 : x ^ 4 + 1 ≠ 0 := by positivity
  have h2 : x ^ 4 + 2 ≠ 0 := by positivity
  have hnum := hpow.add_const 1
  have hbase := hpow.add_const 2
  have hden := hbase.pow 4
  have hquot := hnum.div hden (pow_ne_zero 4 h2)
  have hlog := hquot.log (div_ne_zero h1 (pow_ne_zero 4 h2))
  have hlog' :
      HasDerivAt
        (fun y : ℝ => Real.log ((y ^ 4 + 1) / (y ^ 4 + 2) ^ 4))
        (4 * x ^ 3 / (x ^ 4 + 1) - 16 * x ^ 3 / (x ^ 4 + 2)) x := by
    convert hlog using 1 <;>
      simp only [Pi.div_apply, Pi.pow_apply]
    field_simp [h1, h2]
    ring
  unfold primitive
  convert (hpow.div_const 4).add (hlog'.const_mul (1 / 4 : ℝ)) using 1
  unfold partialFractionIntegrand
  rw [deriv_u_formula]
  field_simp [h1, h2]
  ring

theorem gap1 :
    Family integrand = Family substitutedIntegrand := by
  apply congrArg Family
  funext x
  exact integrand_eq_substituted x

theorem gap2 :
    Family substitutedIntegrand = Family quotientRewrite := by
  apply congrArg Family
  funext x
  exact substituted_eq_quotient x

theorem gap3 :
    Family integrand = Family quotientRewrite := by
  rw [gap1, gap2]

theorem gap4 :
    Family integrand = Family partialFractionIntegrand := by
  apply congrArg Family
  funext x
  calc
    integrand x = substitutedIntegrand x := integrand_eq_substituted x
    _ = quotientRewrite x := substituted_eq_quotient x
    _ = partialFractionIntegrand x := quotient_eq_partialFraction x

theorem gap5 :
    Family partialFractionIntegrand = Translates primitive := by
  apply Set.ext
  intro F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    let g : ℝ → ℝ := fun x => F x - primitive x
    have hg : ∀ x, HasDerivAt g 0 x := by
      intro x
      simpa [g] using (hF x).sub (primitive_hasDerivAt x)
    have hgdiff : Differentiable ℝ g := by
      intro x
      exact (hg x).differentiableAt
    have hgderiv : ∀ x, deriv g x = 0 := by
      intro x
      exact (hg x).deriv
    refine ⟨g 0, ?_⟩
    intro x
    have hx : g x = g 0 := by
      apply is_const_of_deriv_eq_zero hgdiff hgderiv
    dsimp [g] at hx ⊢
    linarith
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := funext hC
    intro x
    rw [hEq]
    exact (primitive_hasDerivAt x).add_const C

theorem gap6 :
    Family integrand = Translates primitive := by
  rw [gap4, gap5]

end

end ProofGap.Exercise1909
